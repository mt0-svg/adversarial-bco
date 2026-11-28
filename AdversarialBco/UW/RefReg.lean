/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetUW

@[expose] public section

/-!
# W-DET at T4U with sure ranges

`refRegOf : DetUW → RefRegUW`. The port of Theorem U's Lemma (O1-GEN) (`RunRec.det`, Bit/ShadowDet.lean) and of
`RunW.wdet` (Unified/WorldShadowRef.lean) to P° of Theorem UW:

* `RunRecW`: a run record of P° (`df2RoundGaW` at `parW d n u` with the sure ranges `b0`, `y0`); its virtual epoch
  started before round `a` is the weighted epoch at `ctxW` on the path `pathW` of its unweighted path
  (`frm_fresh`, with `mode_pathW`);
* `RunRecW.det`: at a good position, with admissible losses, `EpochOK` of every weighted virtual epoch at the
  horizon `n - a`, and the Azuma inequality at the level `δc`, the regret over the `n` rounds is at most `bRegW`;
* `pathW_congr`: the weighted epoch reads its path at the rounds `s < m` only;
* `refRegOf`: on `Case ∩ Ω_ref`, `DetUW` gives `EpochOK` of P°'s virtual epochs (`GoodU`), and the record of P° is
  P°'s run (`round_rrU`, `mode_rrU`, `refPlay_rrU`, `mean_rrU`).

The regret argument reads the modes of the epochs and the losses only: the observation, weighted or not, enters
through `EpochOK`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

/-! ## The weighted epoch reads its path before the horizon only -/

theorem modeEW_congr (c : Df2Ctx d) (b0 y0 : ℝ) (π π' : Df2Path d) (m : ℕ)
    (h : ∀ s < m, π.g s = π'.g s ∧ π.e s = π'.e s ∧ π.xi s = π'.xi s) :
    ∀ s ≤ m, modeEW c b0 y0 π s = modeEW c b0 y0 π' s
  | 0, _ => rfl
  | s + 1, hs => by
    obtain ⟨h1, h2, h3⟩ := h s (by omega)
    simp only [modeEW, modeEW_congr c b0 y0 π π' m h s (by omega), h1, h2, h3]

theorem pathW_congr (c : Df2Ctx d) (b0 y0 : ℝ) (π π' : Df2Path d) (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ s < m, π.g s = π'.g s ∧ π.e s = π'.e s ∧ π.xi s = π'.xi s) :
    c.EpochOK (pathW c b0 y0 π) m ↔ c.EpochOK (pathW c b0 y0 π') m := by
  refine ctx_epochOK_congr c _ _ m hm fun s hs => ?_
  obtain ⟨h1, h2, h3⟩ := h s hs
  refine ⟨h1, ?_, h3⟩
  show eW c b0 y0 π s = eW c b0 y0 π' s
  unfold eW
  rw [modeEW_congr c b0 y0 π π' m h s hs.le, h1, h2, h3]

/-! ## A run record of P° of Theorem UW -/

/-- A run record of P°: the horizon `n`, the reference's parameters `r`, the body `K`, the losses `f`, the position
`q`, the routine `ap t` of round `t`, the draws `xi`, the noises `nt` and the dithers `ze`. -/
structure RunRecW (d : ℕ) where
  n : ℕ
  r : RefW
  K : Set (E d)
  f : ℕ → E d → ℝ
  q : PgSp d
  ap : ℕ → ApFun d
  xi : ℕ → Fin d → ℝ
  nt : ℕ → ℝ
  ze : ℕ → ℝ

namespace RunRecW

variable (R : RunRecW d)

/-- The parameters of the learner, T4U. -/
noncomputable abbrev p : Df2OPar := parW d R.n R.r.u

/-- The positioned body `K~ ∩ B_R`. -/
abbrev Kt : Set (E d) := df2Kp R.K R.q R.p.R

/-- Round `t` of the record from the mode `m`, weighted and clipped, at the exact gauge of the positioned body. -/
noncomputable def rnd (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGaW R.p R.r.b0 R.r.y0 R.n R.K R.q (gauge R.Kt) (R.ap t) (R.f t) (R.nt t) (R.xi t) (R.ze t) m

/-- The mode before round `a + s`, started in the mode `m` before round `a`. -/
noncomputable def frm (R : RunRecW d) (a : ℕ) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (R.rnd (a + s) (frm R a m s)).2

/-- The mode before round `t`. -/
noncomputable def mode (t : ℕ) : Df2Mode d := R.frm 0 (.run (df2Init R.p d)) t

/-- The play of round `t`. -/
noncomputable def play (t : ℕ) : E d := (R.rnd t (R.mode t)).1

/-- The mean of the loss of round `t` given the past. -/
noncomputable def mean (t : ℕ) : ℝ :=
  ∫ z, R.f t (df2RoundGaW R.p R.r.b0 R.r.y0 R.n R.K R.q (gauge R.Kt) apCall (R.f t) 0 z 0 (R.mode t)).1 ∂gaussK d

/-- The positioned loss of round `t`, `g_t(y) = f_t(μ_q + T_q y)/2`. -/
noncomputable def g (t : ℕ) (y : E d) : ℝ := R.f t (pgMu R.q + pgOp R.q y) / 2

/-- The context of the virtual epoch started before round `a`. -/
noncomputable def ctxAt (a : ℕ) : Df2Ctx d := ctxW d R.n R.r R.Kt fun s => R.ap (a + s)

/-- The unweighted path of the virtual epoch started before round `a`. -/
noncomputable def pathAt (a : ℕ) : Df2Path d :=
  ⟨fun s => R.g (a + s), fun s => (R.nt (a + s) + R.ze (a + s)) / 2, fun s => R.xi (a + s)⟩

/-- The weighted path of the virtual epoch started before round `a`. -/
noncomputable def pathWAt (a : ℕ) : Df2Path d := pathW (R.ctxAt a) R.r.b0 R.r.y0 (R.pathAt a)

theorem mode_succ (t : ℕ) : R.mode (t + 1) = (R.rnd t (R.mode t)).2 := by
  show (R.rnd (0 + t) (R.frm 0 _ t)).2 = _
  rw [Nat.zero_add]
  rfl

/-- At a position where the guard centre and every play lie in `K`, the next mode of a round is that of the weighted
epoch map of the epoch started at `a`, at its round `s`. -/
theorem rnd_snd (hK0 : pgMu R.q + pgOp R.q 0 ∈ R.K)
    (hplay : ∀ X : Fin d → ℝ, pgMu R.q + pgOp R.q
      (WithLp.toLp 2 ((df2Pip R.p R.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ R.K)
    (a s : ℕ) (m : Df2Mode d) :
    (R.rnd (a + s) m).2 = (df2RoundEW (R.ctxAt a) R.r.b0 R.r.y0 ((R.ctxAt a).ap s) ((R.pathAt a).g s)
      ((R.pathAt a).e s) ((R.pathAt a).xi s) m).2 := by
  cases m with
  | off => rfl
  | guard =>
    simp only [rnd, df2RoundGaW, df2RoundEW, hK0, ↓reduceIte]
  | run st =>
    have h := hplay (st.mu + (1 - R.p.lam) • (st.A *ᵥ R.xi (a + s)))
    simp only [df2Pip] at h
    simp only [rnd, df2RoundGaW, df2RoundEW, h, ↓reduceIte]
    congr 2
    simp only [g, pathAt, ctxAt, ctxW, df2Pip]
    ring

theorem frm_add (a : ℕ) (m : Df2Mode d) (s s' : ℕ) : R.frm a m (s + s') = R.frm (a + s) (R.frm a m s) s' := by
  induction s' with
  | zero => rfl
  | succ s' ih =>
    rw [← Nat.add_assoc, frm, frm, ih, Nat.add_assoc]

theorem mode_add (a s : ℕ) : R.mode (a + s) = R.frm a (R.mode a) s := by
  unfold mode
  rw [frm_add, Nat.zero_add]

theorem frm_fresh
    (hround : ∀ a s m, (R.rnd (a + s) m).2 = (df2RoundEW (R.ctxAt a) R.r.b0 R.r.y0 ((R.ctxAt a).ap s)
      ((R.pathAt a).g s) ((R.pathAt a).e s) ((R.pathAt a).xi s) m).2)
    (a s : ℕ) : R.frm a (.run (df2Init R.p d)) s = (R.ctxAt a).mode (R.pathWAt a) s := by
  rw [pathWAt, mode_pathW]
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [frm, ih, hround]
    rfl

/-- The mean of the loss of round `t`, at a running mode, is at most twice the mean of the extension. -/
theorem mean_le (t : ℕ) (st : Df2St d) (hmode : R.mode t = .run st)
    (hplay : ∀ X : Fin d → ℝ, pgMu R.q + pgOp R.q
      (WithLp.toLp 2 ((df2Pip R.p R.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ R.K)
    (hf01 : ∀ x ∈ R.K, R.f t x ∈ Set.Icc (0 : ℝ) 1) (heps : 0 < R.p.eps) (L : ℝ)
    (hlip : ∀ x y, |df2Ext R.p R.Kt (R.g t) x - df2Ext R.p R.Kt (R.g t) y| ≤ L * ‖x - y‖) :
    R.mean t ≤
      2 * ∫ z, df2Ext R.p R.Kt (R.g t)
        (WithLp.toLp 2 st.mu + (1 - R.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z) ∂(stdGaussian (E d)) := by
  unfold mean
  rw [hmode]
  set p := R.p with hp
  set Kt := R.Kt with hKt
  set ext := df2Ext p Kt (R.g t) with hext
  set Ps := R.q with hPs
  set X : (Fin d → ℝ) → Fin d → ℝ := fun z => st.mu + (1 - p.lam) • (st.A *ᵥ z) with hX
  have hpt : ∀ z, (df2RoundGaW p R.r.b0 R.r.y0 R.n R.K Ps (gauge Kt) apCall (R.f t) 0 z 0 (.run st)).1 =
      pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z)) := by
    intro z
    have h := hplay (X z)
    simp only [df2Pip, hX] at h
    simp only [df2RoundGaW]
    split_ifs with hc
    · rfl
    · exact absurd h hc
  have hle : ∀ z, R.f t (pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z))) ≤
      2 * ext (WithLp.toLp 2 (X z)) := by
    intro z
    have hin := hplay (X z)
    have h0 := (hf01 _ hin).1
    have hpip : 1 ≤ df2Pip p Kt (WithLp.toLp 2 (X z)) := le_max_left _ _
    simp only [hext, df2Ext, g]
    rw [WithLp.toLp_smul] at hin h0 ⊢
    have h2 : 0 ≤ 2 * (df2Pip p Kt (WithLp.toLp 2 (X z)) - 1) / p.eps := by
      apply div_nonneg _ heps.le; linarith
    nlinarith
  have hcont : Continuous fun u : E d =>
      ext (WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u) := by
    have hlip' : LipschitzWith (Real.toNNReal |L|) ext := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg L)]
      exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
    exact hlip'.continuous.comp (by fun_prop : Continuous fun u : E d =>
      WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)
  have hint : Integrable (fun u : E d => ext (WithLp.toLp 2 st.mu +
      (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)) (stdGaussian (E d)) := by
    have := integrable_lip_affine ext L hlip (WithLp.toLp 2 st.mu) ((1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A)
    simpa using this
  have hXz : ∀ z, ext (WithLp.toLp 2 (X z)) = (fun u : E d => ext (WithLp.toLp 2 st.mu +
      (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)) (WithLp.toLp 2 z) := by
    intro z
    show ext _ = ext _
    congr 1
  simp_rw [hpt]
  calc _ ≤ ∫ z, 2 * ext (WithLp.toLp 2 (X z)) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => (hf01 _ (hplay _)).1) ?_
          (Filter.Eventually.of_forall hle)
        refine Integrable.const_mul ?_ 2
        simp_rw [hXz]
        exact integrable_pi_toLp _ hcont hint
    _ = _ := by
        rw [integral_const_mul]
        congr 1
        simp_rw [hXz]
        exact integral_pi_toLp _ hcont

/-- **Lemma (O1-GEN) for P° of Theorem UW**: the regret of a run record on the good event. -/
theorem det (hd : 1 ≤ d) (hn : 1 ≤ R.n) (hu : 1 ≤ R.r.u) (hKc : IsClosed R.K) (hKcv : Convex ℝ R.K)
    (hfA : ∀ t < R.n, AdmLoss R.K (R.f t)) (hq : PgGood d R.K R.p.R (some R.q)) (heps : R.p.eps ≤ 1 / 2)
    (hep : ∀ a < R.n, (R.ctxAt a).EpochOK (R.pathWAt a) (R.n - a))
    (haz : ∑ t ∈ Finset.range R.n, R.f t (R.play t) ≤
      ∑ t ∈ Finset.range R.n, R.mean t + Real.sqrt (2 * R.n * Real.log (7 / R.r.δc))) :
    regretPts R.K R.f R.play R.n ≤ bRegW d R.n R.r.u R.r.δc := by
  have hpar := parOK_parW (u := R.r.u) hd hn hu
  have heps0 : 0 < R.p.eps := hpar.eps0
  have heps1 : R.p.eps < 1 := by linarith
  have hrho : 0 ≤ R.p.rho / R.p.eta := by
    have hrw := rows_parW hd hn hu heps
    have := hrw.pos_rho; have := hrw.pos_eta
    positivity
  obtain ⟨hdet, -, -, -⟩ := good_unpack hq
  have hKt : R.Kt = posBody R.K (pgMu R.q) (pgOp R.q) := df2Kp_eq_posBody hq
  have hbody : Df2Body d R.p.R R.Kt := body_good hKc hKcv hq
  obtain ⟨hconv, hclosed, hb1', hbR', -⟩ := hbody
  have h0Kt : (0 : E d) ∈ R.Kt := hb1' (Metric.mem_closedBall_self zero_le_one)
  have hK0 : pgMu R.q + pgOp R.q 0 ∈ R.K := h0Kt.1
  have hplayKt : ∀ X : E d, (df2Pip R.p R.Kt X)⁻¹ • X ∈ R.Kt := by
    intro X
    have h := play_mem _ _ hconv hclosed hb1' heps0 heps1 X
    have h2 := hconv.smul_mem_of_zero_mem h0Kt h (t := 1 - R.p.eps) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - R.p.eps) ≠ 0), one_smul] at h2
  have hplay : ∀ X : Fin d → ℝ, pgMu R.q + pgOp R.q
      (WithLp.toLp 2 ((df2Pip R.p R.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ R.K := by
    intro X
    have h := hplayKt (WithLp.toLp 2 X)
    rw [← WithLp.toLp_smul] at h
    exact h.1
  -- the positioned losses
  have hadm : ∀ t < R.n, AdmLoss R.Kt (R.g t) := by
    intro t ht
    obtain ⟨hcv, h01⟩ := hfA t ht
    refine ⟨⟨hconv, ?_⟩, fun y hy => ?_⟩
    · intro y1 hy1 y2 hy2 a b ha hb hab
      have hx := affine_comb R.q y1 y2 a b hab
      have := hcv.2 hy1.1 hy2.1 ha hb hab
      simp only [g, smul_eq_mul] at this ⊢
      rw [hx]
      linarith
    · have := h01 _ hy.1
      simp only [g, Set.mem_Icc] at this ⊢
      constructor <;> linarith [this.1, this.2]
  have hX1 := fun t (ht : t < R.n) =>
    (sifactsUW d R.n R.r.u R.Kt (R.g t) hd hn hu heps
      ⟨hconv, hclosed, hb1', hbR', (body_good hKc hKcv hq).2.2.2.2⟩ (hadm t ht)).1
  -- the modes
  have hround := R.rnd_snd hK0 hplay
  have hfresh := R.frm_fresh hround
  have hmode0 : R.mode 0 = .run (df2Init R.p d) := rfl
  -- the regret
  unfold regretPts bRegW
  have hKne : R.K.Nonempty := ⟨_, hK0⟩
  have hlow : ∑ t ∈ Finset.range R.n, R.mean t - 2 * (R.p.rho / R.p.eta) - R.n * R.p.eps ≤
      sInf ((fun y => ∑ t ∈ Finset.range R.n, R.f t y) '' R.K) := by
    apply le_csInf (hKne.image _)
    rintro _ ⟨x, hx, rfl⟩
    -- the point `x'' = (1 - ε) S x` of `K_ε`
    have hdetU : IsUnit (pgMat R.q).det := Ne.isUnit hdet
    set y : E d := WithLp.toLp 2 ((pgMat R.q)⁻¹ *ᵥ WithLp.ofLp (x - pgMu R.q)) with hy
    have hSy : pgMu R.q + pgOp R.q y = x := by
      simp only [hy, pgOp, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetU,
        Matrix.one_mulVec, WithLp.toLp_ofLp]
      abel
    have hyKt : y ∈ R.Kt := by
      rw [hKt]
      show pgMu R.q + pgOp R.q y ∈ R.K
      rw [hSy]; exact hx
    set x'' : Fin d → ℝ := (1 - R.p.eps) • WithLp.ofLp y with hx''
    have hne1 : (1 - R.p.eps) ≠ 0 := by linarith
    have hxK : x'' ∈ df2KepsOf R.Kt R.p.eps := by
      show WithLp.toLp 2 ((1 - R.p.eps)⁻¹ • x'') ∈ R.Kt
      rw [hx'', smul_smul, inv_mul_cancel₀ hne1, one_smul, WithLp.toLp_ofLp]
      exact hyKt
    -- prop:shrink and the extension on `K_ε`
    have hpt : ∀ t < R.n, 2 * df2Ext R.p R.Kt (R.g t) (WithLp.toLp 2 x'') ≤ R.f t x + R.p.eps := by
      intro t ht
      rw [(hX1 t ht).2.2.2 x'' hxK]
      have hsm : WithLp.toLp 2 x'' = (1 - R.p.eps) • y + R.p.eps • (0 : E d) := by
        rw [hx'', WithLp.toLp_smul, WithLp.toLp_ofLp, smul_zero, add_zero]
      rw [hsm]
      have hc := (hadm t ht).1.2 hyKt h0Kt (by linarith : (0 : ℝ) ≤ 1 - R.p.eps) heps0.le (by ring)
      have hy01 := (hadm t ht).2 y hyKt
      have h001 := (hadm t ht).2 0 h0Kt
      have hfx : R.g t y = R.f t x / 2 := by simp only [g, hSy]
      have h0half : R.g t 0 ≤ 1 / 2 := by
        have := (hfA t ht).2 _ hK0
        simp only [g]; linarith [this.2]
      simp only [smul_eq_mul] at hc
      nlinarith [hy01.1, h001.1]
    -- the epochs of the run
    have hQ : ∀ k a, R.n - a = k → a ≤ R.n → R.mode a = .run (df2Init R.p d) →
        ∑ t ∈ Finset.Ico a R.n, (R.mean t - 2 * df2Ext R.p R.Kt (R.g t) (WithLp.toLp 2 x'')) ≤
          2 * (R.p.rho / R.p.eta) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k IH =>
      intro a hk ha hfa
      rcases Nat.lt_or_ge a R.n with han | han
      swap
      · obtain rfl : a = R.n := le_antisymm ha han
        simp only [Finset.Ico_self, Finset.sum_empty]
        positivity
      have hmode : ∀ s, R.mode (a + s) = (R.ctxAt a).mode (R.pathWAt a) s := fun s => by
        rw [mode_add, hfa, hfresh]
      have hstep : ∀ s, a + s < R.n → (∃ st, (R.ctxAt a).mode (R.pathWAt a) s = .run st) →
          R.mean (a + s) - 2 * df2Ext R.p R.Kt (R.g (a + s)) (WithLp.toLp 2 x'') ≤
          2 * ((R.ctxAt a).ebar (R.pathWAt a) s -
            df2Ext (R.ctxAt a).p (R.ctxAt a).Kt ((R.pathWAt a).g s) (WithLp.toLp 2 x'')) := by
        rintro s hs ⟨st, hst⟩
        have h := R.mean_le (a + s) st ((hmode s).trans hst) hplay (hfA (a + s) hs).2 heps0 _
          (hX1 (a + s) hs).2.2.1
        have hst' : (R.ctxAt a).st (R.pathWAt a) s = st := by
          simp [Df2Ctx.st, hst, Df2Mode.stOr]
        have he : (R.ctxAt a).ebar (R.pathWAt a) s =
            ∫ z, df2Ext R.p R.Kt (R.g (a + s))
              (WithLp.toLp 2 st.mu + (1 - R.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z)
              ∂(stdGaussian (E d)) := by
          rw [Df2Ctx.ebar, hst']
          rfl
        have he2 : df2Ext (R.ctxAt a).p (R.ctxAt a).Kt ((R.pathWAt a).g s) (WithLp.toLp 2 x'') =
            df2Ext R.p R.Kt (R.g (a + s)) (WithLp.toLp 2 x'') := rfl
        rw [he, he2]
        linarith
      have hrun0 : ∃ st, (R.ctxAt a).mode (R.pathWAt a) 0 = .run st := ⟨_, rfl⟩
      have hrunS : ∀ s, (R.ctxAt a).cont (R.pathWAt a) s →
          ∃ st, (R.ctxAt a).mode (R.pathWAt a) (s + 1) = .run st := by
        rintro s ⟨st, h, -⟩
        exact ⟨st, h⟩
      have hsplit : ∀ r, r < R.n - a → (∀ s < r, (R.ctxAt a).cont (R.pathWAt a) s) →
          ∑ t ∈ Finset.Ico a (a + (r + 1)), (R.mean t - 2 * df2Ext R.p R.Kt (R.g t) (WithLp.toLp 2 x'')) ≤
          2 * (R.ctxAt a).eReg (R.pathWAt a) r x'' := by
        intro r hr hcont
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Df2Ctx.eReg, Finset.mul_sum]
        refine Finset.sum_le_sum fun s hs => hstep s (by rw [Finset.mem_range] at hs; omega) ?_
        rw [Finset.mem_range] at hs
        rcases s with _ | s
        · exact hrun0
        · exact hrunS s (hcont s (by omega))
      rcases hep a han with ⟨r, hr, hcont, hfire, hreg⟩ | ⟨hcont, hreg⟩
      · have h1 := hsplit r hr hcont
        have h2 := hreg x'' hxK
        have hfa' : R.mode (a + (r + 1)) = .run (df2Init R.p d) := by
          rw [hmode]; exact hfire
        have h3 := IH (R.n - (a + (r + 1))) (by omega) (a + (r + 1)) rfl (by omega) hfa'
        rw [← Finset.sum_Ico_consecutive _ (by omega : a ≤ a + (r + 1)) (by omega : a + (r + 1) ≤ R.n)]
        linarith
      · have h1 := hsplit (R.n - a - 1) (by omega) (fun s hs => hcont s (by omega))
        have h2 := hreg x'' hxK
        have hn' : a + (R.n - a - 1 + 1) = R.n := by omega
        rw [hn'] at h1
        have : (R.ctxAt a).p.rho / (R.ctxAt a).p.eta = R.p.rho / R.p.eta := rfl
        linarith
    have h0 := hQ R.n 0 (Nat.sub_zero R.n) (Nat.zero_le R.n) hmode0
    rw [← Finset.range_eq_Ico] at h0
    have h1 : ∑ t ∈ Finset.range R.n, 2 * df2Ext R.p R.Kt (R.g t) (WithLp.toLp 2 x'') ≤
        ∑ t ∈ Finset.range R.n, (R.f t x + R.p.eps) :=
      Finset.sum_le_sum fun t ht => hpt t (Finset.mem_range.mp ht)
    rw [Finset.sum_sub_distrib] at h0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    simp only
    linarith
  linarith

end RunRecW

/-! ## P° of Theorem UW is its run record -/

section RefU

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- The run record of P° of Theorem UW on `ω`. -/
noncomputable def rrU (B : RunW d n K W) (ρ : RefW) (ω : Ω) : RunRecW d :=
  ⟨n, ρ, K, B.loss ω, B.pos ω, fun t => apAdv (B.adv t ω (modeU B ρ t ω)), fun t => W.xi t ω, fun t => W.nz t ω,
    fun t => B.zeta t ω (modeU B ρ t ω)⟩

/-- `df2RoundGaW` does not read the loss off the interior of `K` at a good position. -/
theorem roundGaW_loss_congr {K : Set (E d)} (hKconv : Convex ℝ K) {p : Df2OPar} {q : PgSp d}
    (hq : PgGood d K p.R (some q)) (heps0 : 0 < p.eps) (heps1 : p.eps < 1) (b0 y0 : ℝ) (n : ℕ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (h : ∀ y ∈ interior K, ft y = ft' y) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGaW p b0 y0 n K q (gauge (df2Kp K q p.R)) ap ft nt ξ ζ m =
      df2RoundGaW p b0 y0 n K q (gauge (df2Kp K q p.R)) ap ft' nt ξ ζ m := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    have hin := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ ξ)))
    simp only [df2Pip, ← WithLp.toLp_smul] at hin
    simp only [df2RoundGaW, h _ hin]

/-- The point of a weighted round reads neither the loss, nor the noise, nor the dither. -/
theorem roundGaW_fst (p : Df2OPar) (b0 y0 : ℝ) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (nt nt' : ℝ) (ξ : Fin d → ℝ) (ζ ζ' : ℝ) (m : Df2Mode d) :
    (df2RoundGaW p b0 y0 n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGaW p b0 y0 n K Ps ga ap ft' nt' ξ ζ' m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundGaW]
    split_ifs <;> rfl

variable {B : RunW d n K W} {ρ : RefW}

section Case

variable (hKconv : Convex ℝ K) {ω : Ω} (hq : B.Case ρ.δc ω) (heps0 : 0 < (parW d n ρ.u).eps)
  (heps1 : (parW d n ρ.u).eps < 1)
include hKconv hq heps0 heps1

theorem round_rrU {t : ℕ} (ht : t < n) (m : Df2Mode d) :
    cRoundW n ρ K (B.pos ω) (apAdv (B.adv t ω (modeU B ρ t ω))) (B.lossR t ω) (W.nz t ω) (W.xi t ω)
      (B.zeta t ω (modeU B ρ t ω)) m = (rrU B ρ ω).rnd t m := by
  classical
  have hk : kTh n ρ.δc K (B.pos ω) = df2Kp K (B.pos ω) (parW d n ρ.u).R := kTh_good hq
  have hq' : PgGood d K (parW d n ρ.u).R (some (B.pos ω)) := hq
  show df2RoundGaW (parW d n ρ.u) ρ.b0 ρ.y0 n K (B.pos ω) (gauge (kTh n ρ.δc K (B.pos ω))) _ (B.lossR t ω) _ _ _ m =
    df2RoundGaW (parW d n ρ.u) ρ.b0 ρ.y0 n K (B.pos ω) (gauge (df2Kp K (B.pos ω) (parW d n ρ.u).R)) _
      (B.loss ω t) _ _ _ m
  rw [hk]
  refine roundGaW_loss_congr hKconv hq' heps0 heps1 ρ.b0 ρ.y0 n _ _ _ (fun y hy => ?_) _ _ _ m
  simp only [RunW.lossR, ht, ↓reduceIte, fL, RunW.loss, Set.piecewise_eq_of_mem _ _ _ hy]

theorem mode_rrU : ∀ t ≤ n, modeU B ρ t ω = (rrU B ρ ω).mode t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [RunRecW.mode_succ, ← mode_rrU t (by omega), ← round_rrU hKconv hq heps0 heps1 (show t < n by omega)]
    rfl

theorem refPlay_rrU {t : ℕ} (ht : t < n) : refPlayU B ρ t ω = (rrU B ρ ω).play t := by
  show (cRoundW n ρ K (B.pos ω) _ (B.lossR t ω) _ _ _ (modeU B ρ t ω)).1 =
    ((rrU B ρ ω).rnd t ((rrU B ρ ω).mode t)).1
  rw [round_rrU hKconv hq heps0 heps1 ht, mode_rrU hKconv hq heps0 heps1 t ht.le]

theorem mean_rrU {t : ℕ} (ht : t < n) : meanU B ρ t ω = (rrU B ρ ω).mean t := by
  have hk : kTh n ρ.δc K (B.pos ω) = df2Kp K (B.pos ω) (parW d n ρ.u).R := kTh_good hq
  unfold meanU RunRecW.mean
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show B.loss ω t (df2RoundGaW (parW d n ρ.u) ρ.b0 ρ.y0 n K (B.pos ω) (gauge (kTh n ρ.δc K (B.pos ω))) apCall
      (B.lossR t ω) 0 z 0 (modeU B ρ t ω)).1 = B.loss ω t (df2RoundGaW (parW d n ρ.u) ρ.b0 ρ.y0 n K (B.pos ω)
      (gauge (df2Kp K (B.pos ω) (parW d n ρ.u).R)) apCall (B.loss ω t) 0 z 0 ((rrU B ρ ω).mode t)).1
  rw [hk, mode_rrU hKconv hq heps0 heps1 t ht.le,
    roundGaW_fst _ _ _ _ _ _ _ _ (B.lossR t ω) (B.loss ω t) 0 0 z 0 0]

end Case

/-- On `Case`, DET at T4U turns the four events with sure ranges of P°'s virtual epoch started at `a` into
`EpochOK` of the weighted epoch of the record. -/
theorem epochOK_of_goodU (hDet : DetUW) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K) {ω : Ω}
    (hq : B.Case ρ.δc ω) {a : ℕ} (ha : a < n)
    (hev : EvYW (ctxU B ρ a ω) (epU B ρ a ω) (sYW n ρ.y0 ρ.δc) (n - a) ∧
      EvLQW (ctxU B ρ a ω) (epU B ρ a ω) (b1W (parW d n ρ.u) d n ρ.u) (n - a) ∧
      EvSDFW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a) ∧
      EvDQW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a)) :
    ((rrU B ρ ω).ctxAt a).EpochOK ((rrU B ρ ω).pathWAt a) (n - a) := by
  classical
  have hd := hreg.hd
  have hRW := (rows_parW hd hreg.hn hreg.hu (by linarith [hreg.heps]))
  have hR : 1 ≤ (df2oPar d n ρ.δc).R := hRW.one_le_R
  have hmw : 1 / (df2oPar d n ρ.δc).R ≤ df2Mw d := by
    rw [show (df2oPar d n ρ.δc).R = 134 * d * Real.sqrt (Real.log (2 * d + 2)) from rfl]
    exact inv_R_le_df2Mw d hd
  have hE := hDet d n ρ (kTh n ρ.δc K (B.pos ω)) (fun s => apAdv (B.adv (a + s) ω (modeU B ρ (a + s) ω)))
    (pathU B ρ a ω) (n - a) hreg (by omega) (Nat.sub_le n a) (body_kTh hKc hKconv hR hmw _)
    (fun s => apAdv_spec hd _)
    (fun s hs => adm_gTh (f := fun t => B.F.L t (lamAtW n B.F.lam a s ω)) (a := a) (s := s) hKconv
      hKc hR hmw (B.F.adm (a + s) (by omega) _) _) hev
  have hk : kTh n ρ.δc K (B.pos ω) = df2Kp K (B.pos ω) (parW d n ρ.u).R := kTh_good hq
  have hc : ctxW d n ρ (kTh n ρ.δc K (B.pos ω)) (fun s => apAdv (B.adv (a + s) ω (modeU B ρ (a + s) ω))) =
      (rrU B ρ ω).ctxAt a := by
    rw [hk]; rfl
  rw [hc] at hE
  refine (pathW_congr ((rrU B ρ ω).ctxAt a) ρ.b0 ρ.y0 (pathU B ρ a ω) ((rrU B ρ ω).pathAt a) (n - a) (by omega)
    fun s hs => ⟨?_, rfl, rfl⟩).mp hE
  funext y
  have has : a + s < n := by omega
  have hq' : PgGood d K (df2oPar d n ρ.δc).R (some (B.pos ω)) := hq
  show gTh n ρ.δc K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω) y =
    B.F.L (a + s) (B.F.lam (a + s) ω) (pgMu (B.pos ω) + pgOp (B.pos ω) y) / 2
  simp only [gTh, hq', ↓reduceIte, lamAtW, has]

end RefU

/-- **W-DET at T4U** from DET at T4U: on `Case ∩ Ω_ref`, P°'s regret is at most `bRegW`. -/
theorem refRegOf : DetUW → RefRegUW := by
  intro hDet d n ρ K Ω _ W B hreg hKc hKconv ω hq hg
  have hd := hreg.hd
  have hn := hreg.hn
  have heps : (parW d n ρ.u).eps ≤ 1 / 2 := by linarith [hreg.heps]
  have heps0 : 0 < (parW d n ρ.u).eps := (parOK_parW (u := ρ.u) hd hn hreg.hu).eps0
  have heps1 : (parW d n ρ.u).eps < 1 := by linarith
  have hplay : ∑ t ∈ Finset.range n, B.loss ω t (refPlayU B ρ t ω) =
      ∑ t ∈ Finset.range n, (rrU B ρ ω).f t ((rrU B ρ ω).play t) :=
    Finset.sum_congr rfl fun t ht => by
      rw [refPlay_rrU hKconv hq heps0 heps1 (Finset.mem_range.mp ht)]; rfl
  have hmean : ∑ t ∈ Finset.range n, meanU B ρ t ω = ∑ t ∈ Finset.range n, (rrU B ρ ω).mean t :=
    Finset.sum_congr rfl fun t ht => mean_rrU hKconv hq heps0 heps1 (Finset.mem_range.mp ht)
  have haz := hg.2
  unfold AzU at haz
  rw [hplay, hmean] at haz
  have hq' : PgGood d K (parW d n ρ.u).R (some (B.pos ω)) := hq
  have h := (rrU B ρ ω).det hd hn hreg.hu hKc hKconv (fun t ht => B.F.adm t ht _) hq' heps
    (fun a ha => epochOK_of_goodU hDet hreg hKc hKconv hq ha (hg.1 a ha).2) haz
  unfold regretPts at h ⊢
  rw [hplay]
  exact h

end AdversarialBco.UW
