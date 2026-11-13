/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.TriLeaves
public import AdversarialBco.Bit.HpSgd
public import AdversarialBco.Bit.NearMin

@[expose] public section

/-!
# The position theorem, the core

The core of the position theorem: rounded projected subgradient descent in the triangular chart on the box
`BX(r, a, b)` (Bit/TriLeaves.lean), from the position `(0, I)`, on independent draws. `triIter` the iterates,
`triAvg` their average, `triCore` the theorem: if the objective under the law of the draws is within `εG` of the
Gaussian objective on the box (the coupled-objective lemma) and the row (R) holds, the average is a good position
(`PgGood`) for the
body at the radius `36.4 d λ(ρ_h)`, outside an event of probability `δ`. The proof: the lemma that the box holds a
minimiser in the package's
terms (`sp_tri_min`, Bit/SelfPos.lean) gives a near minimizer `xo` in the box; the descent lemma (`hpSgd`,
Bit/HpSgd.lean)
bounds the excess objective of the average under the law of the draws, on losses truncated at `‖y‖ ≤ Md` so that
the bounds hold surely; CPL1 moves it to the Gaussian objective; NM-G (`pgGood_of_nearMin_gen`, Bit/NearMin.lean)
turns the excess into a good position.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

open AdversarialBco.Poly

variable {d : ℕ}


/-! ## The core -/

/-- The iterates of the core on the draws `y`: `x_0 = (0, I)`, `x_{t+1} = clip(x_t - s Ṽ(x_t; y_t))`. -/
noncomputable def triIter (r a b s : ℝ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → PgSp d
  | 0 => pgPack 0 1
  | t + 1 => triClip r a b (triIter r a b s Vt y t - s • Vt (triIter r a b s Vt y t) (y t))

/-- The output of the core: the average of the first `N` iterates. -/
noncomputable def triAvg (r a b s : ℝ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (N : ℕ) : PgSp d :=
  (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, triIter r a b s Vt y t

/-- Two rounded subgradients that agree on the draws give the same iterates. -/
theorem triIter_congr (r a b s : ℝ) (Vt Vt' : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (h : ∀ t x, Vt x (y t) = Vt' x (y t)) (t : ℕ) :
    triIter r a b s Vt y t = triIter r a b s Vt' y t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [triIter, ih, h]

/-- The iterate `t` depends on the draws before `t` only. -/
theorem triIter_congr_y (r a b s : ℝ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (y y' : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (h : ∀ i < t, y i = y' i) :
    triIter r a b s Vt y t = triIter r a b s Vt y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [triIter, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h t (Nat.lt_succ_self t)]

/-- The average of the first `N` iterates depends on the first `N` draws only. -/
theorem triAvg_congr_y (r a b s : ℝ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (y y' : ℕ → EuclideanSpace ℝ (Fin d)) (N : ℕ) (h : ∀ i < N, y i = y' i) :
    triAvg r a b s Vt y N = triAvg r a b s Vt y' N := by
  unfold triAvg
  congr 1
  refine Finset.sum_congr rfl fun t ht => triIter_congr_y r a b s Vt y y' t fun i hi => h i ?_
  exact lt_trans hi (Finset.mem_range.1 ht)

/-- `(0, I)` is a point of the box when `a ≤ 1 ≤ b` and `0 ≤ r`. -/
theorem tri_start_mem (r a b : ℝ) (hr : 0 ≤ r) (ha : a ≤ 1) (hb : 1 ≤ b) :
    (pgPack 0 1 : PgSp d) ∈ triBox d r a b := by
  rw [tri_box_iff]
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp [pgMu_pgPack, hr]
  · rw [pgMat_pgPack, Matrix.one_apply_ne hij.ne]
  · rw [pgMat_pgPack, Matrix.one_apply_eq]; exact ⟨ha, hb⟩
  · rw [pgMat_pgPack, Matrix.one_apply_ne hij.ne']; simp; linarith

/-- **The core theorem**, on draws `y_t` independent of law `νG` and bounded by
`Md`, with a subgradient selection `u` of the gauge of `K` and a rounded subgradient `Vt` within `β` of the exact one
`triV u` on the draws. If the objective under the law `νG` is within `εG` of the Gaussian objective on the box and the
row (R) holds, the average of the iterates is a good position for `K`, outside an event of probability `δ`. -/
theorem triCore (d : ℕ) (hd : 1 ≤ d) (ρa ρh : ℝ) (hρa : 1 ≤ ρa) (hρρ : 1.05 * ρa ≤ ρh)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρa)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hu : ∀ z z', inner ℝ (u z) z' ≤ gauge K z')
    (hu' : ∀ z, gauge K z = inner ℝ (u z) z) (hu1 : ∀ z, ‖u z‖ ≤ 1)
    (r a b : ℝ) (hr : pgKappa * ρa ≤ r) (ha0 : 0 < a) (ha : a ≤ pgTmin d ρa) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hb : pgLD ρa ≤ b)
    (νG : Measure (EuclideanSpace ℝ (Fin d))) (εG : ℝ)
    (hcpl : ∀ x ∈ triBox d r a b, |∫ y, gauge K (pgMu x + pgOp x y) ∂νG - posK K (pgMu x) (pgOp x)| ≤ εG)
    (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d) (hVt : Measurable (Function.uncurry Vt)) (Md β : ℝ)
    (hβ0 : 0 ≤ β) (hβ : ∀ x ∈ triBox d r a b, ∀ y, ‖y‖ ≤ Md → ‖Vt x y - triV u x y‖ ≤ β)
    (Gb Δ s : ℝ) (hGb0 : 0 ≤ Gb) (hGb : 1 + (Md + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ Gb ^ 2) (hΔ0 : 0 < Δ)
    (hΔ : 4 * d * r ^ 2 + d * (b - a) ^ 2 + 2 * d * (d - 1) * b ^ 2 ≤ Δ ^ 2) (hs : 0 < s) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrow : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + β * Δ +
      Gb * Δ * Real.sqrt (2 * Real.log (1 / δ) / N) + 2 * εG ≤ pgEh d ρh)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = νG) (hyM : ∀ t ω, ‖y t ω‖ ≤ Md) :
    P {ω | ¬ PgGood d K (36.4 * d * pgLam ρh) (some (triAvg r a b s Vt (fun t => y t ω) N))} ≤
      ENNReal.ofReal δ := by
  classical
  obtain ⟨hKc, hKcl, hKB, hKρ⟩ := hK
  have hκ : (0 : ℝ) < pgKappa := by unfold pgKappa; norm_num
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have hab : a ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hMd : 0 ≤ Md := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hyM 0 ω)
  have hGbpos : 0 < Gb := by nlinarith [sq_nonneg (Md + pgKappa / (Real.sqrt d * a))]
  have : IsProbabilityMeasure νG := by rw [← hlaw 0]; infer_instance
  have hνM : ∀ᵐ w ∂νG, ‖w‖ ≤ Md := by
    rw [← hlaw 0, ae_map_iff (hy 0).aemeasurable (isClosed_le continuous_norm continuous_const).measurableSet]
    exact Filter.Eventually.of_forall fun ω => hyM 0 ω
  obtain ⟨hlip, hgn⟩ := tri_gauge K hKc hKB
  set BX := triBox d r a b with hBX
  -- the truncated loss, subgradient and rounded subgradient
  set l : PgSp d → EuclideanSpace ℝ (Fin d) → ℝ := fun x w => if ‖w‖ ≤ Md then triLoss (gauge K) x w else 0
    with hl
  set V : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d := fun x w => if ‖w‖ ≤ Md then triV u x w else 0 with hV
  set Vt' : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d := fun x w => if ‖w‖ ≤ Md then Vt x w else 0 with hVt'
  have hMs : MeasurableSet {p : PgSp d × EuclideanSpace ℝ (Fin d) | ‖p.2‖ ≤ Md} :=
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const).measurableSet
  have hlm : Measurable (Function.uncurry l) :=
    Measurable.ite hMs (tri_loss_meas (gauge K) hlip.continuous) measurable_const
  have hVtm : Measurable (Function.uncurry Vt') := Measurable.ite hMs hVt measurable_const
  -- the minimiser in the box
  obtain ⟨xo, hμo, hupo, hdiago, hoffo, -, hmino⟩ := sp_tri_min d ρa hd hρa K ⟨hKc, hKcl, hKB, hKρ⟩ r a b hr ha hb
  have hxo : xo ∈ BX := (tri_box_iff r a b xo).2 ⟨hμo, hupo, hdiago, hoffo⟩
  -- the objective under `νG` on the box
  have hφ : ∀ x ∈ BX, ∫ w, l x w ∂νG =
      ∫ w, gauge K (pgMu x + pgOp x w) ∂νG - pgKappa / d * ∑ i, Real.log (pgMat x i i) := by
    intro x hx
    have hint : Integrable (fun w => gauge K (pgMu x + pgOp x w)) νG := by
      refine Integrable.of_bound ((hlip.continuous.comp (continuous_const.add (pgOp x).continuous)).aestronglyMeasurable)
        (‖pgMu x‖ + ‖pgOp x‖ * Md) ?_
      filter_upwards [hνM] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (hgn _).1]
      refine (hgn _).2.trans ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
      exact ((pgOp x).le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    have hae : (fun w => l x w) =ᵐ[νG] fun w => gauge K (pgMu x + pgOp x w) - pgKappa / d * ∑ i, Real.log (pgMat x i i) := by
      filter_upwards [hνM] with w hw
      simp only [hl, hw, ite_true, triLoss]
    rw [integral_congr_ae hae, integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  -- the objective on the box
  have hH : ∀ x ∈ BX, pgH K x = posK K (pgMu x) (pgOp x) - pgKappa / d * ∑ i, Real.log (pgMat x i i) := by
    intro x hx
    have h1 : LinearMap.det ((pgOp x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (pgMat x).det :=
      sp_det_toEuclideanCLM (pgMat x)
    unfold pgH posObj
    rw [h1, (tri_det r a b ha0 x hx).2.2]
  -- the hypotheses of the descent lemma
  have hclipm : Measurable (triClip (d := d) r a b) :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      continuous_const.max (continuous_const.min (PiLp.continuous_apply 2 _ k)))).measurable
  have ha_ : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + inner ℝ (V x w) (x' - x) ≤ l x' w := by
    intro x hx x' hx' w
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hl, hV, hw, ite_true]
      exact tri_subgrad r a b ha0 (gauge K) u hu hu' x x' hx hx' w
    · simp [hl, hV, hw]
  have hlint : ∀ x ∈ BX, Integrable (l x) νG := by
    intro x hx
    refine Integrable.of_bound (hlm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (‖pgMu x‖ + ‖pgOp x‖ * Md + |pgKappa / d * ∑ i, Real.log (pgMat x i i)|)
      (Filter.Eventually.of_forall fun w => ?_)
    have hC : 0 ≤ ‖pgMu x‖ + ‖pgOp x‖ * Md + |pgKappa / d * ∑ i, Real.log (pgMat x i i)| := by
      have := mul_nonneg (norm_nonneg (pgOp x)) hMd
      positivity
    by_cases hw : ‖w‖ ≤ Md
    · simp only [Function.comp, Function.uncurry, hl, hw, ite_true, triLoss, Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_of_nonneg (hgn _).1]
      refine (hgn _).2.trans ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
      exact ((pgOp x).le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    · simp only [Function.comp, Function.uncurry, hl, hw, ite_false, norm_zero]
      exact hC
  have hb_ : ∀ x ∈ BX, ∀ w, ‖V x w‖ ≤ Gb := by
    intro x hx w
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hV, hw, ite_true]
      exact tri_V_bound hd r a b ha0 u hu1 x hx w Md Gb hw hGb0 hGb
    · simp [hV, hw, hGb0]
  have hc_ : ∀ x ∈ BX, ∀ w, ‖Vt' x w - V x w‖ ≤ β := by
    intro x hx w
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hV, hVt', hw, ite_true]
      exact hβ x hx w hw
    · simp [hV, hVt', hw, hβ0]
  have hstart := tri_start_mem (d := d) r a b hr0 ha1 hb1
  set x : ℕ → Ω → PgSp d := fun t ω => triIter r a b s Vt' (fun t => y t ω) t with hx
  have hxBX : ∀ t ω, x t ω ∈ BX := by
    intro t ω
    cases t with
    | zero => exact hstart
    | succ t => exact tri_clip_mem r a b hr0 hab hb0 _
  have hsgd := hpSgd P νG y hy hind hlaw BX (tri_box_convex d r a b) Δ hΔ0
    (fun x hx x' hx' => tri_box_diam r a b Δ hΔ0.le hΔ x x' hx hx') (triClip r a b) hclipm
    (fun z => tri_clip_mem r a b hr0 hab hb0 z) (fun z x hx => tri_clip_nonexp r a b z x hx) l hlm V Vt' hVtm Gb β
    hGbpos ha_ hlint hb_ hc_ s hs x (pgPack 0 1) hstart (fun ω => rfl) (fun t ω => rfl) N hN xo hxo δ hδ0 hδ1
  refine le_trans (measure_mono fun ω hω => ?_) hsgd
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hle
  push Not at hle
  apply hω
  have havg : triAvg r a b s Vt (fun t => y t ω) N = (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t ω := by
    unfold triAvg
    congr 1
    refine Finset.sum_congr rfl fun t _ => triIter_congr r a b s Vt Vt' _ (fun t z => ?_) t
    simp only [hVt', hyM t ω, ite_true]
  rw [havg]
  set xb := (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t ω with hxb
  have hxbBX : xb ∈ BX := tri_avg_mem r a b N hN (fun t => x t ω) (fun t => hxBX t ω)
  have hdet : (pgMat xb).det ≠ 0 := (tri_det r a b ha0 xb hxbBX).2.1.ne'
  refine pgGood_of_nearMin_gen d ρa ρh hd hρa hρρ K ⟨hKc, hKcl, hKB, hKρ⟩ xb hdet (pgH K xo) hmino ?_
  have h1 := hcpl xb hxbBX
  have h2 := hcpl xo hxo
  rw [hφ xb hxbBX, hφ xo hxo] at hle
  rw [hH xb hxbBX, hH xo hxo]
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]


end AdversarialBco.Bit
