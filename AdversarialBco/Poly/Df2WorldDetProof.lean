/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetTools
public import AdversarialBco.Poly.Df2RowsProof

@[expose] public section

/-!
# Lemma 8.10 with the regret on every world

`df2WorldDet_of : Df2SIFacts → Df2WorldDet`. In the case of the
analysis the round map of D0 is the round map `df2RoundE` of the epoch context `df2zCtx` on the positioned losses
`g_t = f_t(S⁻¹ ·)/2` (`zRound_snd`), so the run of D0 from a fresh mode before round `a` is the epoch started at `a`
(`zMode_add_fresh`). On the run, the mean `df2zMean t` of the loss of round `t` is at most `2 ē_t` (`zMean_le`: the
play is `a(X) = X/pip(X)`, `g(a(X)) ≤ e(X)`, and the Gaussian of `Fin d → ℝ` is carried to that of `E d`). The
regret against `x ∈ K` is then cut along the epochs of the run (strong induction on the start rounds): each epoch
that fires has `eReg ≤ 0`, the last one `eReg ≤ ρ/η`; prop:shrink passes from `x` to `(1 - ε) S x ∈ K_ε`, and the
Azuma event passes from the losses played to their means. X1 of `Df2SIFacts` (the extension is Lipschitz) gives the
integrability of the extension under the Gaussian.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM
open scoped Matrix

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## The positioned losses and the round map of D0 -/

/-- The positioned loss of round `t`, `g_t(y) = f_t(μ_S + T_S y)/2`. -/
noncomputable def zG (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (y : E d) : ℝ :=
  w.f t (pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y) / 2

/-- The noise of the observation of round `t` of D0, `(ε_t + ζ_t)/2`. -/
noncomputable def zE (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : ℝ :=
  (w.noise t + df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) / 2

/-- The draw of round `t` of D0. -/
noncomputable def zXi (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : Fin d → ℝ :=
  df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t

/-- In the case of the analysis the next mode of D0 is that of the epoch map on the positioned data: the play of a
running mode lies in `K` and the centre of the guard lies in `K`. -/
theorem zRound_snd (n : ℕ) (r0 R0 δ : ℝ) (w : World d)
    (hK0 : pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) 0 ∈ w.K)
    (hplay : ∀ X : Fin d → ℝ, pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w)
      (WithLp.toLp 2 ((df2Pip (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ w.K)
    (t : ℕ) (m : Df2Mode d) :
    (df2zRoundAt d n r0 R0 δ w t m).2 =
      (df2RoundE (df2zCtx d n r0 R0 δ w) (zG n r0 R0 δ w t) (zE n r0 R0 δ w t) (zXi n r0 R0 δ w t) m).2 := by
  cases m with
  | off => rfl
  | guard =>
    simp only [df2zRoundAt, df2RoundGa, df2RoundE, hK0, ↓reduceIte]
  | run st =>
    have h := hplay (st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ zXi n r0 R0 δ w t))
    simp only [df2Pip, df2zCtx, df2CtxAt, zXi] at h
    simp only [df2zRoundAt, df2RoundGa, df2RoundE, h, ↓reduceIte]
    congr 1
    simp only [zG, zE, zXi, df2Pip, df2zCtx, df2CtxAt]
    ring

/-- The run of D0 read from round `a`: `df2zFrom` is additive in the number of rounds (G1). -/
theorem zFrom_add (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) (m : Df2Mode d) (s s' : ℕ) :
    df2zFrom d n r0 R0 δ w a m (s + s') = df2zFrom d n r0 R0 δ w (a + s) (df2zFrom d n r0 R0 δ w a m s) s' := by
  induction s' with
  | zero => rfl
  | succ s' ih =>
    rw [← Nat.add_assoc, df2zFrom, df2zFrom, ih, Nat.add_assoc]

/-- The mode of D0 before round `a + s` is the run from its mode before round `a`. -/
theorem zMode_add (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a s : ℕ) :
    df2zMode d n r0 R0 δ w (a + s) = df2zFrom d n r0 R0 δ w a (df2zMode d n r0 R0 δ w a) s := by
  unfold df2zMode
  rw [zFrom_add, Nat.zero_add]

/-- From a fresh mode before round `a`, the run of D0 is the epoch started at `a` (G2). -/
theorem zFrom_fresh (n : ℕ) (r0 R0 δ : ℝ) (w : World d)
    (hround : ∀ t m, (df2zRoundAt d n r0 R0 δ w t m).2 =
      (df2RoundE (df2zCtx d n r0 R0 δ w) (zG n r0 R0 δ w t) (zE n r0 R0 δ w t) (zXi n r0 R0 δ w t) m).2)
    (a s : ℕ) :
    df2zFrom d n r0 R0 δ w a (.run (df2Init (df2oPar d n δ) d)) s =
      (df2zCtx d n r0 R0 δ w).mode (df2zPath d n r0 R0 δ w a) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [df2zFrom, ih, hround]
    rfl

/-! ## The mean of the loss of a round against the extension -/

/-- The Gaussian of `Fin d → ℝ` carried to `E d`. -/
theorem integral_pi_toLp (F : E d → ℝ) (hF : Continuous F) :
    ∫ z, F (WithLp.toLp 2 z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = ∫ u, F u ∂(stdGaussian (E d)) := by
  rw [← map_pi_eq_stdGaussian, integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    hF.aestronglyMeasurable]

/-- A function with a linear growth bound composed with an affine map is integrable under the Gaussian. -/
theorem integrable_lip_affine (e : E d → ℝ) (L : ℝ) (he : ∀ x y, |e x - e y| ≤ L * ‖x - y‖) (m : E d)
    (B : E d →L[ℝ] E d) : Integrable (fun u => e (m + B u)) (stdGaussian (E d)) := by
  have hlip : LipschitzWith (Real.toNNReal |L|) e := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg L)]
    exact (he x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  have hc : Continuous fun u => e (m + B u) := hlip.continuous.comp (continuous_const.add B.continuous)
  have hg : Integrable (fun u : E d => |e m| + |L| * (‖B‖ * ‖u‖)) (stdGaussian (E d)) :=
    (integrable_const _).add ((IsGaussian.integrable_id.norm.const_mul ‖B‖).const_mul |L|)
  refine hg.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have h1 := he (m + B u) m
  simp only [add_sub_cancel_left] at h1
  rw [Real.norm_eq_abs]
  have h2 : L * ‖B u‖ ≤ |L| * (‖B‖ * ‖u‖) :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm u) (abs_nonneg L))
  have h3 := abs_sub_abs_le_abs_sub (e (m + B u)) (e m)
  linarith

/-- The Gaussian of `Fin d → ℝ` carried to `E d`, for integrability. -/
theorem integrable_pi_toLp (F : E d → ℝ) (hF : Continuous F) (hi : Integrable F (stdGaussian (E d))) :
    Integrable (fun z => F (WithLp.toLp 2 z)) (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian] at hi
  exact (integrable_map_measure hF.aestronglyMeasurable (PiLp.continuous_toLp 2 _).measurable.aemeasurable).mp hi

/-- The mean of the loss of round `t` of D0, at a running mode, is at most twice the mean `ē_t` of the extension:
the play is `μ_S + T_S a(X)` with `a(X) = X/pip(X)`, and `g(a(X)) ≤ e(X)` since `pip ≥ 1` and `g ≥ 0`. -/
theorem zMean_le (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (st : Df2St d)
    (hmode : df2zMode d n r0 R0 δ w t = .run st)
    (hplay : ∀ X : Fin d → ℝ, pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w)
      (WithLp.toLp 2 ((df2Pip (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ w.K)
    (hf01 : ∀ x ∈ w.K, w.f t x ∈ Set.Icc (0 : ℝ) 1) (heps : 0 < (df2oPar d n δ).eps) (L : ℝ)
    (hlip : ∀ x y, |df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t) x -
      df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t) y| ≤ L * ‖x - y‖) :
    df2zMean d n r0 R0 δ w t ≤
      2 * ∫ z, df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t)
        (WithLp.toLp 2 st.mu + (1 - (df2oPar d n δ).lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z)
        ∂(stdGaussian (E d)) := by
  unfold df2zMean
  rw [hmode]
  set p := df2oPar d n δ with hp
  set Kt := (df2zCtx d n r0 R0 δ w).Kt with hKt
  set ext := df2Ext p Kt (zG n r0 R0 δ w t) with hext
  set Ps := df2oPs d n r0 R0 δ w with hPs
  set X : (Fin d → ℝ) → Fin d → ℝ := fun z => st.mu + (1 - p.lam) • (st.A *ᵥ z) with hX
  have hpt : ∀ z, (df2RoundGa p n w.K Ps (gauge (df2Kp w.K Ps p.R)) apCall (w.f t) 0 z 0 (.run st)).1 =
      pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z)) := by
    intro z
    have h := hplay (X z)
    simp only [df2Pip, hKt, df2zCtx, df2CtxAt, hX] at h
    simp only [df2RoundGa]
    split_ifs with hc
    · rfl
    · exact absurd h hc
  have hle : ∀ z, w.f t (pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z))) ≤
      2 * ext (WithLp.toLp 2 (X z)) := by
    intro z
    have hin := hplay (X z)
    have h0 := (hf01 _ hin).1
    have hpip : 1 ≤ df2Pip p Kt (WithLp.toLp 2 (X z)) := le_max_left _ _
    simp only [hext, df2Ext, zG]
    rw [WithLp.toLp_smul] at hin h0 ⊢
    have h2 : 0 ≤ 2 * (df2Pip p Kt (WithLp.toLp 2 (X z)) - 1) / p.eps := by
      apply div_nonneg _ heps.le; linarith
    nlinarith
  have hcont : Continuous fun u : E d => ext (WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u) := by
    have hlip' : LipschitzWith (Real.toNNReal |L|) ext := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg L)]
      exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
    exact hlip'.continuous.comp (by fun_prop : Continuous fun u : E d => WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)
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

/-! ## The gluing -/

/-- Lemma 8.10 with the regret on every world, from X1 of `Df2SIFacts`. -/
theorem df2WorldDet_of (SI : Df2SIFacts) : Df2WorldDet := by
  intro d n r0 R0 δ K f hW w hwK hwf hcase hep haz
  obtain ⟨hd, hn, hr0, _, hδ0, hδ1, hKc, hKcv, hball, _, hfA⟩ := hW
  obtain ⟨⟨P, hPos, hdet, hb1, hbR, hMw⟩, heps⟩ := hcase
  subst hwK hwf
  have RH := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hPs : df2oPs d n r0 R0 δ w = P := by simp [df2oPs, hPos]
  rw [← hPs] at hdet hb1 hbR hMw
  have hL := RH.L_pos
  have hdR := RH.d_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have heps0 : 0 < (df2oPar d n δ).eps := by rw [RH.eps]; positivity
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hrho : 0 ≤ (df2oPar d n δ).rho / (df2oPar d n δ).eta := by
    rw [RH.rho, RH.eta]; positivity
  -- the positioned body
  have hKt : (df2zCtx d n r0 R0 δ w).Kt = posBody w.K (pgMu (df2oPs d n r0 R0 δ w)) (pgOp (df2oPs d n r0 R0 δ w)) := by
    ext y
    simp only [df2zCtx, df2CtxAt, df2Kp, posBody, Set.mem_setOf_eq]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have := hbR h
    simpa using this
  have hconv : Convex ℝ (df2zCtx d n r0 R0 δ w).Kt := by
    rw [hKt]
    intro y1 hy1 y2 hy2 a b ha hb hab
    simp only [posBody, Set.mem_setOf_eq] at hy1 hy2 ⊢
    have := hKcv hy1 hy2 ha hb hab
    convert this using 1
    rw [map_add, map_smul, map_smul]
    obtain rfl : b = 1 - a := by linarith
    module
  have hclosed : IsClosed (df2zCtx d n r0 R0 δ w).Kt := by
    rw [hKt]
    exact hKc.isClosed.preimage (continuous_const.add (pgOp _).continuous)
  have hb1' : Metric.closedBall 0 1 ⊆ (df2zCtx d n r0 R0 δ w).Kt := by rw [hKt]; exact hb1
  have hbR' : (df2zCtx d n r0 R0 δ w).Kt ⊆ Metric.closedBall 0 (df2oPar d n δ).R := by rw [hKt]; exact hbR
  have hbody : Df2Body d (df2oPar d n δ).R (df2zCtx d n r0 R0 δ w).Kt :=
    ⟨hconv, hclosed, hb1', hbR', by rw [hKt]; exact hMw⟩
  have h0Kt : (0 : E d) ∈ (df2zCtx d n r0 R0 δ w).Kt := hb1' (Metric.mem_closedBall_self zero_le_one)
  have hK0 : pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) 0 ∈ w.K := h0Kt.1
  have hplayKt : ∀ X : E d, (df2Pip (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt X)⁻¹ • X ∈
      (df2zCtx d n r0 R0 δ w).Kt := by
    intro X
    have h := play_mem _ _ hconv hclosed hb1' heps0 heps1 X
    have h2 := hconv.smul_mem_of_zero_mem h0Kt h (t := 1 - (df2oPar d n δ).eps) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - (df2oPar d n δ).eps) ≠ 0), one_smul] at h2
  have hplay : ∀ X : Fin d → ℝ, pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w)
      (WithLp.toLp 2 ((df2Pip (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ w.K := by
    intro X
    have h := hplayKt (WithLp.toLp 2 X)
    rw [← WithLp.toLp_smul] at h
    exact h.1
  -- the positioned losses
  have hadm : ∀ t < n, AdmLoss (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t) := by
    intro t ht
    obtain ⟨hcv, h01⟩ := hfA t ht
    refine ⟨⟨hconv, ?_⟩, fun y hy => ?_⟩
    · intro y1 hy1 y2 hy2 a b ha hb hab
      have hx : pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) (a • y1 + b • y2) =
          a • (pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y1) +
            b • (pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y2) := by
        rw [map_add, map_smul, map_smul]
        obtain rfl : b = 1 - a := by linarith
        module
      have := hcv.2 hy1.1 hy2.1 ha hb hab
      simp only [zG, smul_eq_mul] at this ⊢
      rw [hx]
      linarith
    · have := h01 _ hy.1
      simp only [zG, Set.mem_Icc] at this ⊢
      constructor <;> linarith [this.1, this.2]
  have hX1 := fun t (ht : t < n) =>
    (SI d n δ (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t) hd hn hδ0 hδ1 heps hbody (hadm t ht)).1
  -- the modes
  have hround := zRound_snd n r0 R0 δ w hK0 hplay
  have hfresh := zFrom_fresh n r0 R0 δ w hround
  have hmode0 : df2zMode d n r0 R0 δ w 0 = .run (df2Init (df2oPar d n δ) d) := by
    have hne : ¬ (1 / 2 < (df2oPar d n δ).eps) := not_lt.mpr heps
    simp only [df2zMode, df2zFrom, df2oMode0, hPos, hne, ↓reduceIte]
  -- the regret
  unfold regretPts
  have hKne : w.K.Nonempty := ⟨0, hball (Metric.mem_closedBall_self hr0.le)⟩
  have hlow : ∑ t ∈ Finset.range n, df2zMean d n r0 R0 δ w t -
      2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) - n * (df2oPar d n δ).eps ≤
      sInf ((fun y => ∑ t ∈ Finset.range n, w.f t y) '' w.K) := by
    apply le_csInf (hKne.image _)
    rintro _ ⟨x, hx, rfl⟩
    -- the point `x'' = (1 - ε) S x` of `K_ε`
    have hdetU : IsUnit (pgMat (df2oPs d n r0 R0 δ w)).det := Ne.isUnit hdet
    set y : E d := WithLp.toLp 2 ((pgMat (df2oPs d n r0 R0 δ w))⁻¹ *ᵥ
      WithLp.ofLp (x - pgMu (df2oPs d n r0 R0 δ w))) with hy
    have hSy : pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y = x := by
      simp only [hy, pgOp, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetU,
        Matrix.one_mulVec, WithLp.toLp_ofLp]
      abel
    have hyKt : y ∈ (df2zCtx d n r0 R0 δ w).Kt := by
      rw [hKt]
      show pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y ∈ w.K
      rw [hSy]; exact hx
    set x'' : Fin d → ℝ := (1 - (df2oPar d n δ).eps) • WithLp.ofLp y with hx''
    have hne1 : (1 - (df2oPar d n δ).eps) ≠ 0 := by linarith
    have hxK : x'' ∈ df2KepsOf (df2zCtx d n r0 R0 δ w).Kt (df2oPar d n δ).eps := by
      show WithLp.toLp 2 ((1 - (df2oPar d n δ).eps)⁻¹ • x'') ∈ (df2zCtx d n r0 R0 δ w).Kt
      rw [hx'', smul_smul, inv_mul_cancel₀ hne1, one_smul, WithLp.toLp_ofLp]
      exact hyKt
    -- prop:shrink and the extension on `K_ε`
    have hpt : ∀ t < n, 2 * df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t)
        (WithLp.toLp 2 x'') ≤ w.f t x + (df2oPar d n δ).eps := by
      intro t ht
      rw [(hX1 t ht).2.2.2 x'' hxK]
      have hsm : WithLp.toLp 2 x'' = (1 - (df2oPar d n δ).eps) • y + (df2oPar d n δ).eps • (0 : E d) := by
        rw [hx'', WithLp.toLp_smul, WithLp.toLp_ofLp, smul_zero, add_zero]
      rw [hsm]
      have hc := (hadm t ht).1.2 hyKt h0Kt (by linarith : (0 : ℝ) ≤ 1 - (df2oPar d n δ).eps) heps0.le
        (by ring)
      have hy01 := (hadm t ht).2 y hyKt
      have h001 := (hadm t ht).2 0 h0Kt
      have hfx : zG n r0 R0 δ w t y = w.f t x / 2 := by simp only [zG, hSy]
      have h0half : zG n r0 R0 δ w t 0 ≤ 1 / 2 := by
        have := (hfA t ht).2 _ hK0
        simp only [zG]; linarith [this.2]
      simp only [smul_eq_mul] at hc
      nlinarith [hy01.1, h001.1]
    -- the epochs of the run
    have hQ : ∀ k a, n - a = k → a ≤ n → df2zMode d n r0 R0 δ w a = .run (df2Init (df2oPar d n δ) d) →
        ∑ t ∈ Finset.Ico a n, (df2zMean d n r0 R0 δ w t - 2 * df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt
          (zG n r0 R0 δ w t) (WithLp.toLp 2 x'')) ≤ 2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k IH =>
      intro a hk ha hfa
      rcases Nat.lt_or_ge a n with han | han
      swap
      · obtain rfl : a = n := le_antisymm ha han
        simp only [Finset.Ico_self, Finset.sum_empty]
        positivity
      have hmode : ∀ s, df2zMode d n r0 R0 δ w (a + s) =
          (df2zCtx d n r0 R0 δ w).mode (df2zPath d n r0 R0 δ w a) s := fun s => by
        rw [zMode_add, hfa, hfresh]
      have hstep : ∀ s, a + s < n → (∃ st, (df2zCtx d n r0 R0 δ w).mode (df2zPath d n r0 R0 δ w a) s = .run st) →
          df2zMean d n r0 R0 δ w (a + s) - 2 * df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt
            (zG n r0 R0 δ w (a + s)) (WithLp.toLp 2 x'') ≤
          2 * ((df2zCtx d n r0 R0 δ w).ebar (df2zPath d n r0 R0 δ w a) s -
            df2Ext (df2zCtx d n r0 R0 δ w).p (df2zCtx d n r0 R0 δ w).Kt ((df2zPath d n r0 R0 δ w a).g s)
              (WithLp.toLp 2 x'')) := by
        rintro s hs ⟨st, hst⟩
        have h := zMean_le n r0 R0 δ w (a + s) st ((hmode s).trans hst) hplay (hfA (a + s) hs).2 heps0 _
          (hX1 (a + s) hs).2.2.1
        have hst' : (df2zCtx d n r0 R0 δ w).st (df2zPath d n r0 R0 δ w a) s = st := by
          simp [Df2Ctx.st, hst, Df2Mode.stOr]
        have he : (df2zCtx d n r0 R0 δ w).ebar (df2zPath d n r0 R0 δ w a) s =
            ∫ z, df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w (a + s))
              (WithLp.toLp 2 st.mu + (1 - (df2oPar d n δ).lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z)
              ∂(stdGaussian (E d)) := by
          rw [Df2Ctx.ebar, hst']
          rfl
        have he2 : df2Ext (df2zCtx d n r0 R0 δ w).p (df2zCtx d n r0 R0 δ w).Kt ((df2zPath d n r0 R0 δ w a).g s)
            (WithLp.toLp 2 x'') = df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w (a + s))
              (WithLp.toLp 2 x'') := rfl
        rw [he, he2]
        linarith
      have hrun0 : ∃ st, (df2zCtx d n r0 R0 δ w).mode (df2zPath d n r0 R0 δ w a) 0 = .run st := ⟨_, rfl⟩
      have hrunS : ∀ s, (df2zCtx d n r0 R0 δ w).cont (df2zPath d n r0 R0 δ w a) s →
          ∃ st, (df2zCtx d n r0 R0 δ w).mode (df2zPath d n r0 R0 δ w a) (s + 1) = .run st := by
        rintro s ⟨st, h, -⟩
        exact ⟨st, h⟩
      have hsplit : ∀ r, r < n - a → (∀ s < r, (df2zCtx d n r0 R0 δ w).cont (df2zPath d n r0 R0 δ w a) s) →
          ∑ t ∈ Finset.Ico a (a + (r + 1)), (df2zMean d n r0 R0 δ w t - 2 * df2Ext (df2oPar d n δ)
            (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t) (WithLp.toLp 2 x'')) ≤
          2 * (df2zCtx d n r0 R0 δ w).eReg (df2zPath d n r0 R0 δ w a) r x'' := by
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
        have hfa' : df2zMode d n r0 R0 δ w (a + (r + 1)) = .run (df2Init (df2oPar d n δ) d) := by
          rw [hmode]; exact hfire
        have h3 := IH (n - (a + (r + 1))) (by omega) (a + (r + 1)) rfl (by omega) hfa'
        rw [← Finset.sum_Ico_consecutive _ (by omega : a ≤ a + (r + 1)) (by omega : a + (r + 1) ≤ n)]
        linarith
      · have h1 := hsplit (n - a - 1) (by omega) (fun s hs => hcont s (by omega))
        have h2 := hreg x'' hxK
        have hn' : a + (n - a - 1 + 1) = n := by omega
        rw [hn'] at h1
        have : (df2zCtx d n r0 R0 δ w).p.rho / (df2zCtx d n r0 R0 δ w).p.eta =
          (df2oPar d n δ).rho / (df2oPar d n δ).eta := rfl
        linarith
    have h0 := hQ n 0 (Nat.sub_zero n) (Nat.zero_le n) hmode0
    rw [← Finset.range_eq_Ico] at h0
    have h1 : ∑ t ∈ Finset.range n, 2 * df2Ext (df2oPar d n δ) (df2zCtx d n r0 R0 δ w).Kt (zG n r0 R0 δ w t)
        (WithLp.toLp 2 x'') ≤ ∑ t ∈ Finset.range n, (w.f t x + (df2oPar d n δ).eps) :=
      Finset.sum_le_sum fun t ht => hpt t (Finset.mem_range.mp ht)
    rw [Finset.sum_sub_distrib] at h0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    simp only
    linarith
  have haz' := haz
  unfold Df2AzPath at haz'
  linarith

end Layer2

end AdversarialBco.Poly
