/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Smooth convex approximation

`smooth_convex`: a convex `L`-Lipschitz function on `ℝ^d` is uniformly approximated, within `ε`, by a convex
`L`-Lipschitz `C^2` function with Lipschitz gradient. Mollification by a normed bump of radius `ε / (L + 1)`; the
derivative of the convolution is the convolution with the derivative of the bump, which gives the Lipschitz constant
`L ∫ ‖Dψ‖` of the gradient. Used by the proofs of the Gaussian position lemma and of the lemmas of Procedure PG.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped Convolution in
/-- Mollification by a normed bump of radius `ε / (L + 1)`. -/
theorem AdversarialBco.Body.smooth_convex {d : ℕ} (Φ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hΦ : LipschitzWith L Φ) (hc : ConvexOn ℝ Set.univ Φ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 F ∧ ConvexOn ℝ Set.univ F ∧ LipschitzWith L F ∧
      (∃ M : ℝ≥0, LipschitzWith M (fderiv ℝ F)) ∧ ∀ x, |F x - Φ x| ≤ ε := by
  have hr : 0 < ε / ((L : ℝ) + 1) := by positivity
  set r := ε / ((L : ℝ) + 1) with hr_def
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set ψ := φ.normed volume with hψ
  have hloc : LocallyIntegrable Φ volume := hΦ.continuous.locallyIntegrable
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => φ.nonneg_normed t
  have hex : ∀ x, ConvolutionExistsAt ψ Φ x (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun x =>
    hψc.convolutionExists_left _ φ.continuous_normed hloc x
  set F := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Φ with hF
  have hFeq : F = fun x => ∫ y, Φ (x - y) * ψ y := by
    funext x
    rw [hF, convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  have hint : ∀ x, Integrable (fun y => Φ (x - y) * ψ y) := fun x => by
    have h := hex x
    unfold ConvolutionExistsAt at h
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  -- the derivative of `F` as a convolution with the derivative of the bump
  set P := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (EuclideanSpace ℝ (Fin d)) with hP
  have hψ1 : ContDiff ℝ 1 ψ := φ.contDiff_normed (n := 1)
  have hder : ∀ x, fderiv ℝ F x = (fderiv ℝ ψ ⋆[P, volume] Φ) x := fun x =>
    (hψc.hasFDerivAt_convolution_left _ hψ1 hloc x).fderiv
  have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv (by simp)
  have hdcs : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv (𝕜 := ℝ)
  have hdex : ∀ x, ConvolutionExistsAt (fderiv ℝ ψ) Φ x P volume := fun x =>
    hdcs.convolutionExists_left P hdc hloc x
  have hdi : Integrable (fun t => ‖fderiv ℝ ψ t‖) volume := hdc.norm.integrable_of_hasCompactSupport hdcs.norm
  have hA : 0 ≤ ∫ t, ‖fderiv ℝ ψ t‖ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨F, hψc.contDiff_convolution_left _ (φ.contDiff_normed (n := 2)) hloc, ?_, ?_, ?_, ?_⟩
  · rw [hFeq]
    exact AdversarialBco.convexOn_convolution Φ hc ψ (φ.nonneg_normed) hint
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, hF, convolution_def, convolution_def, ← integral_sub (hex x) (hex y)]
    calc |∫ t, ((ContinuousLinearMap.lsmul ℝ ℝ) (ψ t) (Φ (x - t)) -
            (ContinuousLinearMap.lsmul ℝ ℝ) (ψ t) (Φ (y - t)))|
        ≤ ∫ t, ψ t * (L * dist x y) := by
          refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ (Filter.Eventually.of_forall fun t => ?_))
          · exact (φ.integrable_normed).mul_const _
          · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_sub, abs_mul,
              abs_of_nonneg (hψ0 t)]
            refine mul_le_mul_of_nonneg_left ?_ (hψ0 t)
            have h := hΦ.dist_le_mul (x - t) (y - t)
            rw [Real.dist_eq, dist_sub_right] at h
            exact h
      _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]
  · have hPb : ∀ (a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : ℝ), ‖P a v‖ ≤ ‖a‖ * |v| := fun a v => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      show ‖a w * v‖ ≤ ‖a‖ * |v| * ‖w‖
      calc ‖a w * v‖ = ‖a w‖ * |v| := by rw [norm_mul, Real.norm_eq_abs v]
        _ ≤ ‖a‖ * ‖w‖ * |v| := mul_le_mul_of_nonneg_right (a.le_opNorm w) (abs_nonneg v)
        _ = ‖a‖ * |v| * ‖w‖ := by ring
    refine ⟨⟨(∫ t, ‖fderiv ℝ ψ t‖) * L, mul_nonneg hA L.2⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, hder x, hder y, convolution_def, convolution_def, ← integral_sub (hdex x) (hdex y)]
    calc ‖∫ t, (P (fderiv ℝ ψ t) (Φ (x - t)) - P (fderiv ℝ ψ t) (Φ (y - t)))‖
        ≤ ∫ t, ‖fderiv ℝ ψ t‖ * (L * dist x y) := by
          refine norm_integral_le_of_norm_le (hdi.mul_const _) (Filter.Eventually.of_forall fun t => ?_)
          rw [← (P (fderiv ℝ ψ t)).map_sub]
          refine (hPb _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          have h := hΦ.dist_le_mul (x - t) (y - t)
          rw [Real.dist_eq, dist_sub_right] at h
          exact h
      _ = _ := by
          simp only [integral_mul_const]
          exact (mul_assoc (∫ t, ‖fderiv ℝ ψ t‖) (L : ℝ) (dist x y)).symm
  · intro x
    have h := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) hΦ.continuous.aestronglyMeasurable
      (ε := ε) fun y hy => by
        refine (hΦ.dist_le_mul y x).trans ?_
        calc (L : ℝ) * dist y x ≤ L * r := mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le L.2
          _ ≤ ((L : ℝ) + 1) * r := mul_le_mul_of_nonneg_right (by linarith) hr.le
          _ = ε := by rw [hr_def]; field_simp
    rwa [Real.dist_eq] at h
