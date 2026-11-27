/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosSgd
public import AdversarialBco.Bit.TriCore

@[expose] public section

/-!
# UNI-POS part 2: the core of TRI-OGD with a τ-subgradient field from (SEP0)

UNI-POS (the paper's section on the position), parts 1 and 2.

* `Sep0 π y0 g a c`: the conclusion (SEP0) of Lemma SEP at the base point `y0`,
  `π z ≥ π y0 + ⟪g, z - y0⟫ - a ‖z - y0‖ - c` for every `z` (Sec. 3.3, with `a = τ √d` and
  `c = (2L + 2τ√d)(64/63) ℓ_1`).
* `sep0_norm_le`: for a `1`-Lipschitz `π`, (SEP0) gives `‖g‖ ≤ 1 + a`.
* `tri_subgrad_sep0`: with `V = triV u` (the vector `g = u(μ + L w)` and `lowtri(g wᵀ) - (κ/d) diag(1/L_ii)`, the
  form of `triV`, m1), the loss of the chart has `l(x°, w) ≥ l(x, w) + ⟪V(x, w), x° - x⟫ - a ‖z° - z‖ - c`,
  `z = μ + L w`, `z° = μ° + L° w`, on the whole box.
* `tri_z_sub_le`: `‖z° - z‖ ≤ (1 + ‖w‖) ‖x° - x‖`, so on the box with `‖w‖ ≤ M_d` the slack is at most
  `τ_s = a (1 + M_d) Δ + c` (the sup of m2, bounded through the diameter `Δ` of the box).
* `tri_V_bound_G`: `‖V‖ ≤ G_b` when `‖g‖ ≤ G_g`, `1 ≤ G_g`, `G_g² + (G_g M_d + κ/(√d a))² ≤ G_b²` (`G_up` redone, m1).
* `triCoreTau`: Theorem TRI-OGD, core, with the selection `u` of exact subgradients of `triCore` replaced by a
  selection satisfying (SEP0) on the points `μ + L w` of the box, and the rounded field `Vt` compared with `triV u`
  only at the points the procedure reaches: the iterates stay in a set `S` of positions and the draws in a set `W`
  (in the application the rational points, where the oracle is defined). The row gains `2 τ_s` and the Hoeffding
  range `G_b Δ + τ_s` (`hpSgdTau`).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

variable {d : ℕ}

/-- **(SEP0)** at the base point `y0`: `π z ≥ π y0 + ⟪g, z - y0⟫ - a ‖z - y0‖ - c` for every `z`
(UNI-SEP, with `a = τ √d` and `c = (2 L + 2 τ √d)(64/63) ℓ_1`). -/
def Sep0 (π : EuclideanSpace ℝ (Fin d) → ℝ) (y0 g : EuclideanSpace ℝ (Fin d)) (a c : ℝ) : Prop :=
  ∀ z, π y0 + inner ℝ g (z - y0) - a * ‖z - y0‖ - c ≤ π z

/-- For a `1`-Lipschitz `π`, (SEP0) bounds the vector: `‖g‖ ≤ 1 + a`. -/
theorem sep0_norm_le (π : EuclideanSpace ℝ (Fin d) → ℝ) (hπ : LipschitzWith 1 π) (y0 g : EuclideanSpace ℝ (Fin d))
    (a c : ℝ) (ha : 0 ≤ a) (h : Sep0 π y0 g a c) : ‖g‖ ≤ 1 + a := by
  by_contra hlt
  push Not at hlt
  have hg : 0 < ‖g‖ := by linarith
  set e := ‖g‖ - 1 - a with he
  have he0 : 0 < e := by rw [he]; linarith
  set t := (|c| + 1) / e with ht
  have ht0 : 0 ≤ t := by positivity
  set z := y0 + (t / ‖g‖) • g with hz
  have hzy : z - y0 = (t / ‖g‖) • g := by rw [hz]; abel
  have hn : ‖z - y0‖ = t := by
    rw [hzy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  have hi : inner ℝ g (z - y0) = t * ‖g‖ := by
    rw [hzy, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hL : π z ≤ π y0 + t := by
    have := hπ.dist_le_mul z y0
    rw [Real.dist_eq, dist_eq_norm, hn] at this
    simp only [NNReal.coe_one, one_mul] at this
    linarith [le_abs_self (π z - π y0)]
  have hS := h z
  rw [hi, hn] at hS
  have hte : t * e = |c| + 1 := by rw [ht]; field_simp
  have : t * e ≤ c := by rw [he]; nlinarith
  linarith [le_abs_self c]

/-- The loss of the chart against (SEP0): with `z = μ + L w` and `z' = μ' + L' w`,
`l(x, w) + ⟪triV u x w, x' - x⟫ ≤ l(x', w) + a ‖z' - z‖ + c` on the box. -/
theorem tri_subgrad_sep0 (r a b : ℝ) (ha : 0 < a) (π : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x x' : PgSp d) (hx : x ∈ triBox d r a b)
    (hx' : x' ∈ triBox d r a b) (y : EuclideanSpace ℝ (Fin d)) (as cs : ℝ)
    (hs : Sep0 π (pgMu x + pgOp x y) (u (pgMu x + pgOp x y)) as cs) :
    triLoss π x y + inner ℝ (triV u x y) (x' - x) ≤
      triLoss π x' y + (as * ‖(pgMu x' + pgOp x' y) - (pgMu x + pgOp x y)‖ + cs) := by
  set z := pgMu x + pgOp x y with hz
  set z' := pgMu x' + pgOp x' y with hz'
  set g := u z with hg
  have h0 := tri_subgrad r a b ha (fun v => inner ℝ g v) (fun _ => g) (fun _ _ => le_rfl) (fun _ => rfl) x x' hx hx' y
  have hV : triV (fun _ => g) x y = triV u x y := rfl
  rw [hV] at h0
  unfold triLoss at h0 ⊢
  have h1 := hs z'
  have h2 : inner ℝ g (z' - z) = inner ℝ g z' - inner ℝ g z := inner_sub_right _ _ _
  simp only at h0
  rw [← hz, ← hz'] at h0
  linarith

theorem upos_pgMu_sub (x y : PgSp d) : pgMu (x - y) = pgMu x - pgMu y := by
  ext i; simp [pgMu]

theorem upos_pgOp_sub (x y : PgSp d) : pgOp (x - y) = pgOp x - pgOp y := by
  have h : pgMat (x - y) = pgMat x - pgMat y := by ext i j; simp [pgMat]
  unfold pgOp
  rw [h, map_sub]

theorem upos_pgMu_le (v : PgSp d) : ‖pgMu v‖ ≤ ‖v‖ := by
  have h := pgSp_norm_sq v
  have h0 : 0 ≤ ∑ i, ∑ j, pgMat v i j ^ 2 := by positivity
  exact le_of_sq_le_sq (by linarith) (norm_nonneg _)

theorem upos_pgOp_le (v : PgSp d) (y : EuclideanSpace ℝ (Fin d)) : ‖pgOp v y‖ ≤ ‖v‖ * ‖y‖ := by
  have hv := pgSp_norm_sq v
  have hmu : 0 ≤ ‖pgMu v‖ ^ 2 := by positivity
  have h_sq : ‖pgOp v y‖ ^ 2 ≤ (‖v‖ * ‖y‖) ^ 2 := by
    rw [pgOp_apply]
    calc ‖WithLp.toLp 2 (pgMat v *ᵥ WithLp.ofLp y)‖ ^ 2
        = ∑ i, ((pgMat v *ᵥ WithLp.ofLp y) i) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; simp
      _ = ∑ i, (∑ j, pgMat v i j * (WithLp.ofLp y) j) ^ 2 := by
          simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ i, ((∑ j, pgMat v i j ^ 2) * (∑ j, (WithLp.ofLp y) j ^ 2)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ i, ∑ j, pgMat v i j ^ 2) * ‖y‖ ^ 2 := by
          rw [← Finset.sum_mul, EuclideanSpace.norm_sq_eq]; simp
      _ ≤ ‖v‖ ^ 2 * ‖y‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
      _ = (‖v‖ * ‖y‖) ^ 2 := by ring
  exact le_of_sq_le_sq h_sq (by positivity)

/-- `‖(μ' + L' w) - (μ + L w)‖ ≤ (1 + ‖w‖) ‖x' - x‖`. -/
theorem tri_z_sub_le (x x' : PgSp d) (y : EuclideanSpace ℝ (Fin d)) :
    ‖(pgMu x' + pgOp x' y) - (pgMu x + pgOp x y)‖ ≤ (1 + ‖y‖) * ‖x' - x‖ := by
  have e : (pgMu x' + pgOp x' y) - (pgMu x + pgOp x y) = pgMu (x' - x) + pgOp (x' - x) y := by
    rw [upos_pgMu_sub, upos_pgOp_sub, ContinuousLinearMap.sub_apply]; abel
  rw [e]
  calc ‖pgMu (x' - x) + pgOp (x' - x) y‖ ≤ ‖pgMu (x' - x)‖ + ‖pgOp (x' - x) y‖ := norm_add_le _ _
    _ ≤ ‖x' - x‖ + ‖x' - x‖ * ‖y‖ := add_le_add (upos_pgMu_le _) (upos_pgOp_le _ _)
    _ = (1 + ‖y‖) * ‖x' - x‖ := by ring

/-- The bound of the field `triV u` when the selection has `‖u(μ + L y)‖ ≤ G_g` with `1 ≤ G_g` (`G_up` redone with
`|g| ≤ 1 + τ√d`, m1). -/
theorem tri_V_bound_G (hd : 1 ≤ d) (r a b : ℝ) (ha : 0 < a)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : PgSp d) (hx : x ∈ triBox d r a b)
    (y : EuclideanSpace ℝ (Fin d)) (Gg : ℝ) (hGg : 1 ≤ Gg) (hu : ‖u (pgMu x + pgOp x y)‖ ≤ Gg) (Md Gb : ℝ)
    (hy : ‖y‖ ≤ Md) (hGb0 : 0 ≤ Gb) (hGb : Gg ^ 2 + (Gg * Md + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ Gb ^ 2) :
    ‖triV u x y‖ ≤ Gb := by
  set z := pgMu x + pgOp x y with hz
  set w := u z with hw
  have hGg0 : 0 < Gg := by linarith
  rcases (tri_box_iff r a b x).mp hx with ⟨-, -, hdiag, -⟩
  have hdiag' : ∀ i, a ≤ pgMat x i i := fun i => (hdiag i).1
  have hκ : 0 ≤ pgKappa := by unfold pgKappa; norm_num
  set u' : Fin d → ℝ := fun i => w i / Gg with hu'
  set y' : Fin d → ℝ := fun j => Gg * y j with hy'
  have hw2 : ∑ i, (w i) ^ 2 = ‖w‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; simp
  have hu'sq : ∑ i, u' i ^ 2 ≤ 1 := by
    have e : ∑ i, u' i ^ 2 = (∑ i, (w i) ^ 2) / Gg ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hu']; ring
    rw [e, hw2, div_le_one (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hu 2
  have h := sp_V_norm hd u' y' (pgMat x) pgKappa a hκ ha hdiag' hu'sq
  have hprod : ∀ i j, u' i * y' j = w i * y j := by
    intro i j; rw [hu', hy']; field_simp
  simp only [hprod] at h
  have hy'n : Real.sqrt (∑ j, y' j ^ 2) = Gg * ‖y‖ := by
    have e : ∑ j, y' j ^ 2 = Gg ^ 2 * ‖y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [hy']; simp; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hGg0.le, Real.sqrt_sq (norm_nonneg _)]
  rw [hy'n] at h
  have hsplit : ‖triV u x y‖ ^ 2 = ∑ i, (w i) ^ 2 + ∑ i, ∑ j, ((if j ≤ i then w i * y j else 0) -
      (if i = j then pgKappa / d / pgMat x i i else 0)) ^ 2 := by
    rw [pgSp_norm_sq (triV u x y)]
    dsimp [triV, pgMu, pgMat, z, w]
    simp only [EuclideanSpace.norm_sq_eq]
    simp
  have hsu : ∑ i, (w i) ^ 2 = Gg ^ 2 * ∑ i, u' i ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hu']; field_simp
  have hk0 : 0 ≤ pgKappa / (Real.sqrt d * a) := by positivity
  have hmono : (Gg * ‖y‖ + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ (Gg * Md + pgKappa / (Real.sqrt d * a)) ^ 2 := by
    have : Gg * ‖y‖ ≤ Gg * Md := mul_le_mul_of_nonneg_left hy hGg0.le
    have h0 : 0 ≤ Gg * ‖y‖ + pgKappa / (Real.sqrt d * a) := by positivity
    exact pow_le_pow_left₀ h0 (by linarith) 2
  have hsq : ‖triV u x y‖ ^ 2 ≤ Gb ^ 2 := by
    rw [hsplit, hsu]
    have hU0 : 0 ≤ ∑ i, u' i ^ 2 := by positivity
    have hG2 : 1 ≤ Gg ^ 2 := by nlinarith
    nlinarith
  exact le_of_sq_le_sq hsq hGb0

/-- **Theorem TRI-OGD, core, with a τ-subgradient field** (UNI-POS parts 1 and 2). As `triCore`, with the selection
`u` of exact subgradients replaced by a selection satisfying (SEP0) at the points `μ + L w` of the box
(`hsep`, slope `as`, offset `cs`), the bound `G_b` of `triV u` computed with `‖u‖ ≤ 1 + as` (`hGb`), the slack
`τ_s ≥ as (1 + M_d) Δ + cs` (`hτs`), and the rounded field `Vt` within `β` of `triV u` at the points the procedure
reaches: the iterates start in `S` and stay in `S` (`hS0`, `hSstep`) and the draws lie in `W` (`hyW`). If the
objective under the law `νG` is within `εG` of the Gaussian objective on the box and the row (R) with the two
`τ_s` terms holds, the average of the iterates is a good position for `K`, outside an event of probability `δ`. -/
theorem triCoreTau (d : ℕ) (hd : 1 ≤ d) (ρa ρh : ℝ) (hρa : 1 ≤ ρa) (hρρ : 1.05 * ρa ≤ ρh)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρa)
    (r a b : ℝ) (hr : pgKappa * ρa ≤ r) (ha0 : 0 < a) (ha : a ≤ pgTmin d ρa) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hb : pgLD ρa ≤ b)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (as cs Md : ℝ) (has : 0 ≤ as)
    (hsep : ∀ x ∈ triBox d r a b, ∀ w, ‖w‖ ≤ Md →
      Sep0 (gauge K) (pgMu x + pgOp x w) (u (pgMu x + pgOp x w)) as cs)
    (νG : Measure (EuclideanSpace ℝ (Fin d))) (εG : ℝ)
    (hcpl : ∀ x ∈ triBox d r a b, |∫ y, gauge K (pgMu x + pgOp x y) ∂νG - posK K (pgMu x) (pgOp x)| ≤ εG)
    (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d) (hVt : Measurable (Function.uncurry Vt)) (β : ℝ)
    (Gb Δ s τs : ℝ) (hGb0 : 0 ≤ Gb)
    (hGb : (1 + as) ^ 2 + ((1 + as) * Md + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ Gb ^ 2) (hΔ0 : 0 < Δ)
    (hΔ : 4 * d * r ^ 2 + d * (b - a) ^ 2 + 2 * d * (d - 1) * b ^ 2 ≤ Δ ^ 2) (hs : 0 < s)
    (hτs0 : 0 ≤ τs) (hτs : as * ((1 + Md) * Δ) + cs ≤ τs)
    (S : Set (PgSp d)) (W : Set (EuclideanSpace ℝ (Fin d))) (hS0 : (pgPack 0 1 : PgSp d) ∈ S)
    (hSstep : ∀ x ∈ S, ∀ w ∈ W, triClip r a b (x - s • Vt x w) ∈ S)
    (hβ : ∀ x ∈ triBox d r a b, x ∈ S → ∀ w ∈ W, ‖w‖ ≤ Md → ‖Vt x w - triV u x w‖ ≤ β)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrow : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + β * Δ +
      (Gb * Δ + τs) * Real.sqrt (2 * Real.log (1 / δ) / N) + 2 * τs + 2 * εG ≤ pgEh d ρh)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = νG) (hyM : ∀ t ω, ‖y t ω‖ ≤ Md) (hyW : ∀ t ω, y t ω ∈ W) :
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
  have hGbpos : 0 < Gb := by
    have h1 : 1 ≤ (1 + as) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((1 + as) * Md + pgKappa / (Real.sqrt d * a))]
  have : IsProbabilityMeasure νG := by rw [← hlaw 0]; infer_instance
  have hνM : ∀ᵐ w ∂νG, ‖w‖ ≤ Md := by
    rw [← hlaw 0, ae_map_iff (hy 0).aemeasurable (isClosed_le continuous_norm continuous_const).measurableSet]
    exact Filter.Eventually.of_forall fun ω => hyM 0 ω
  obtain ⟨hlip, hgn⟩ := tri_gauge K hKc hKB
  set BX := triBox d r a b with hBX
  -- the truncated loss, field and rounded field
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
  -- the hypotheses of UNI-SGD
  have hclipm : Measurable (triClip (d := d) r a b) :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      continuous_const.max (continuous_const.min (PiLp.continuous_apply 2 _ k)))).measurable
  have ha_ : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + inner ℝ (V x w) (x' - x) ≤ l x' w + τs := by
    intro x hx x' hx' w
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hl, hV, hw, ite_true]
      have h1 := tri_subgrad_sep0 r a b ha0 (gauge K) u x x' hx hx' w as cs (hsep x hx w hw)
      have h2 : ‖(pgMu x' + pgOp x' w) - (pgMu x + pgOp x w)‖ ≤ (1 + Md) * Δ :=
        (tri_z_sub_le x x' w).trans (mul_le_mul (by linarith) (tri_box_diam r a b Δ hΔ0.le hΔ x' x hx' hx)
          (norm_nonneg _) (by linarith))
      have h3 : as * ‖(pgMu x' + pgOp x' w) - (pgMu x + pgOp x w)‖ ≤ as * ((1 + Md) * Δ) :=
        mul_le_mul_of_nonneg_left h2 has
      linarith
    · simp [hl, hV, hw, hτs0]
  have hlint : ∀ x ∈ BX, Integrable (l x) νG := by
    intro x hx
    refine Integrable.of_bound (hlm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (‖pgMu x‖ + ‖pgOp x‖ * Md + |pgKappa / d * ∑ i, Real.log (pgMat x i i)|)
      (Filter.Eventually.of_forall fun w => ?_)
    have hC : 0 ≤ ‖pgMu x‖ + ‖pgOp x‖ * Md + |pgKappa / d * ∑ i, Real.log (pgMat x i i)| := by
      have := mul_nonneg (norm_nonneg (pgOp x)) hMd
      positivity
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hl, hw, ite_true, triLoss, Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_of_nonneg (hgn _).1]
      refine (hgn _).2.trans ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
      exact ((pgOp x).le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    · simp only [hl, hw, ite_false, norm_zero]
      exact hC
  have hb_ : ∀ x ∈ BX, ∀ w, ‖V x w‖ ≤ Gb := by
    intro x hx w
    by_cases hw : ‖w‖ ≤ Md
    · simp only [hV, hw, ite_true]
      have hu1 := sep0_norm_le (gauge K) hlip _ _ as cs has (hsep x hx w hw)
      exact tri_V_bound_G hd r a b ha0 u x hx w (1 + as) (by linarith) hu1 Md Gb hw hGb0 hGb
    · simp [hV, hw, hGb0]
  have hstart := tri_start_mem (d := d) r a b hr0 ha1 hb1
  set x : ℕ → Ω → PgSp d := fun t ω => triIter r a b s Vt' (fun t => y t ω) t with hx
  have hxBX : ∀ t ω, x t ω ∈ BX := by
    intro t ω
    cases t with
    | zero => exact hstart
    | succ t => exact tri_clip_mem r a b hr0 hab hb0 _
  -- the iterates stay in `S`
  have hxS : ∀ t ω, x t ω ∈ S := by
    intro t ω
    induction t with
    | zero => exact hS0
    | succ t ih =>
      show triClip r a b (x t ω - s • Vt' (x t ω) (y t ω)) ∈ S
      simp only [hVt', hyM t ω, ite_true]
      exact hSstep _ ih _ (hyW t ω)
  have hc_ : ∀ t ω, ‖Vt' (x t ω) (y t ω) - V (x t ω) (y t ω)‖ ≤ β := by
    intro t ω
    simp only [hV, hVt', hyM t ω, ite_true]
    exact hβ _ (hxBX t ω) (hxS t ω) _ (hyW t ω) (hyM t ω)
  have hsgd := hpSgdTau P νG y hy hind hlaw BX (tri_box_convex d r a b) Δ hΔ0
    (fun x hx x' hx' => tri_box_diam r a b Δ hΔ0.le hΔ x x' hx hx') (triClip r a b) hclipm
    (fun z => tri_clip_mem r a b hr0 hab hb0 z) (fun z x hx => tri_clip_nonexp r a b z x hx) l hlm V Vt' hVtm Gb β
    τs hGbpos hτs0 ha_ hlint hb_ s hs x (pgPack 0 1) hstart (fun ω => rfl) (fun t ω => rfl) hc_ N hN xo hxo δ hδ0
    hδ1
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

end AdversarialBco.UniPos
