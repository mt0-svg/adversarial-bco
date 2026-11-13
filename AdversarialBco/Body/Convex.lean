/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Jensen for the Gaussian cloud, the derivative of `log |det|` and the continuity of `det`

`ec_S4` (`G(b) ≤ E G(b + S g)` for a convex Lipschitz `G`), `hasDerivAt_log_abs_det_comp` and `continuous_det_clm`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal






theorem AdversarialBco.Body.ec_S4 {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hGc : ConvexOn ℝ Set.univ G)
    (L : ℝ≥0) (hGL : LipschitzWith L G) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    G b ≤ ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hS_meas : Measurable S := S.continuous.measurable
  have hS_aemeas : AEMeasurable S (stdGaussian E) := hS_meas.aemeasurable
  let μ := (stdGaussian E).map S
  have h_prob : IsProbabilityMeasure μ :=
    ((MeasureTheory.Measure.isProbabilityMeasure_map_iff hS_aemeas).mpr inferInstance)
  have h_neg_map : (stdGaussian E).map (fun w => -w) = stdGaussian E := by
    simpa using (stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := E)))
  have h_symm : μ.map (fun w => -w) = μ := by
    dsimp [μ]
    rw [Measure.map_map measurable_neg hS_meas]
    have h_comp : (fun w => -w) ∘ S = S ∘ (fun w => -w) := by
      ext x; simp [S.map_neg]
    rw [h_comp, ← Measure.map_map hS_meas measurable_neg, h_neg_map]
  have h_int_bound : ∀ g, |G (b + S g)| ≤ (|G b| + (L : ℝ) * ‖S‖) * Real.exp (1 * ‖g‖) := by
    intro g
    have h_lip : |G (b + S g) - G b| ≤ (L : ℝ) * ‖S g‖ := by
      have := hGL.norm_sub_le (b + S g) b
      simpa [add_sub_cancel_left] using this
    have h_norm_Sg : ‖S g‖ ≤ ‖S‖ * ‖g‖ := S.le_opNorm g
    have h_exp : ‖g‖ ≤ Real.exp ‖g‖ := by
      have := Real.add_one_le_exp ‖g‖
      linarith
    have h_one_le_exp : (1 : ℝ) ≤ Real.exp ‖g‖ := by
      have h := Real.add_one_le_exp ‖g‖
      have h_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
      linarith
    have h_tri : |G (b + S g)| ≤ |G b| + |G (b + S g) - G b| := by
      calc
        |G (b + S g)| = |(G (b + S g) - G b) + G b| := by rw [sub_add_cancel]
        _ ≤ |G (b + S g) - G b| + |G b| := abs_add_le _ _
        _ = |G b| + |G (b + S g) - G b| := add_comm _ _
    have hL_nonneg : 0 ≤ (L : ℝ) := by exact L.2
    have hS_norm_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
    calc
      |G (b + S g)| ≤ |G b| + |G (b + S g) - G b| := h_tri
      _ ≤ |G b| + (L : ℝ) * ‖S g‖ := by nlinarith
      _ ≤ |G b| + (L : ℝ) * (‖S‖ * ‖g‖) := by
        have htemp : (L : ℝ) * ‖S g‖ ≤ (L : ℝ) * (‖S‖ * ‖g‖) :=
          mul_le_mul_of_nonneg_left h_norm_Sg hL_nonneg
        nlinarith
      _ = |G b| + (L : ℝ) * ‖S‖ * ‖g‖ := by ring
      _ = |G b| * 1 + (L : ℝ) * ‖S‖ * ‖g‖ := by ring
      _ ≤ |G b| * Real.exp ‖g‖ + (L : ℝ) * ‖S‖ * ‖g‖ := by
        have htemp : |G b| * 1 ≤ |G b| * Real.exp ‖g‖ :=
          mul_le_mul_of_nonneg_left h_one_le_exp (abs_nonneg _)
        nlinarith
      _ ≤ |G b| * Real.exp ‖g‖ + (L : ℝ) * ‖S‖ * Real.exp ‖g‖ := by
        have htemp : (L : ℝ) * ‖S‖ * ‖g‖ ≤ (L : ℝ) * ‖S‖ * Real.exp ‖g‖ :=
          mul_le_mul_of_nonneg_left h_exp (mul_nonneg hL_nonneg hS_norm_nonneg)
        nlinarith
      _ = (|G b| + (L : ℝ) * ‖S‖) * Real.exp ‖g‖ := by ring
      _ = (|G b| + (L : ℝ) * ‖S‖) * Real.exp (1 * ‖g‖) := by ring
  have h_cont_f : Continuous (fun g => G (b + S g)) :=
    hGL.continuous.comp ((continuous_const.add continuous_id).comp S.continuous)
  have h_cont_g : Continuous (fun w => G (b + w)) :=
    hGL.continuous.comp (continuous_const.add continuous_id)
  have h_int_std : Integrable (fun g => G (b + S g)) (stdGaussian E) := by
    refine AdversarialBco.Body.integrable_of_abs_le_exp (fun g => G (b + S g))
      h_cont_f.aestronglyMeasurable (|G b| + (L : ℝ) * ‖S‖) 1 h_int_bound
  have h_int_μ : Integrable (fun w => G (b + w)) μ := by
    have h_aestrong : AEStronglyMeasurable (fun w => G (b + w)) ((stdGaussian E).map S) :=
      h_cont_g.aestronglyMeasurable
    exact ((integrable_map_measure h_aestrong hS_aemeas).mpr h_int_std)
  have h_jensen := AdversarialBco.jensen_symm μ h_symm G hGc b h_int_μ
  have h_integral : ∫ w, G (b + w) ∂μ = ∫ g, G (b + S g) ∂(stdGaussian E) := by
    calc
      ∫ w, G (b + w) ∂μ = ∫ w, G (b + w) ∂((stdGaussian E).map S) := rfl
      _ = ∫ g, G (b + S g) ∂(stdGaussian E) := by
        rw [MeasureTheory.integral_map hS_aemeas h_cont_g.aestronglyMeasurable]
  calc
    G b ≤ ∫ w, G (b + w) ∂μ := h_jensen
    _ = ∫ g, G (b + S g) ∂(stdGaussian E) := h_integral


theorem AdversarialBco.Body.hasDerivAt_log_abs_det_comp {d : ℕ}
    (S E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) :
    (∀ᶠ t in nhds (0 : ℝ), LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) ∧
    HasDerivAt (fun t : ℝ => Real.log |LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
      (LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let S_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := S
  let E'_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := E'
  let M : Matrix (Fin d) (Fin d) ℝ := LinearMap.toMatrix b b E'_lin
  have h_detS : LinearMap.det S_lin ≠ 0 := hS
  -- Relate the goal expression to S_lin and E'_lin
  have h_coe_comp (t : ℝ) : ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      S_lin ∘ₗ ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    ext x; rfl
  have h_coe_id_smul (t : ℝ) : ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) + t • ((E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    ext x; rfl
  -- For any t, det(S ∘ (id + tE')) = det S * det(id + tE')
  have h_det_factor (t : ℝ) : LinearMap.det (S_lin ∘ₗ ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
      LinearMap.det S_lin * LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) := by
    rw [LinearMap.det_comp]
  -- The matrix of id + tE' is 1 + tM
  have h_matrix (t : ℝ) : LinearMap.toMatrix b b (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
      (1 : Matrix (Fin d) (Fin d) ℝ) + t • M := by
    rw [h_coe_id_smul t]
    have h_id : LinearMap.toMatrix b b (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 := by
      simp [LinearMap.toMatrix_id b]
    have h_add : LinearMap.toMatrix b b ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) + t • (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
        LinearMap.toMatrix b b (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) +
        t • LinearMap.toMatrix b b (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
      simp [map_add, map_smul]
    simp [M, E'_lin, map_add, map_smul, LinearMap.toMatrix_id b]
  -- det(1 + tM) is continuous in t and equals 1 at t=0
  have h_det_pos_near_zero : ∀ᶠ t in nhds (0 : ℝ), (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det > 0) := by
    have h_cont : Continuous fun t : ℝ => ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det := by
      apply Continuous.matrix_det
      continuity
    have h_zero : ((1 : Matrix (Fin d) (Fin d) ℝ) + (0 : ℝ) • M).det = 1 := by
      simp
    have h_pos : (0 : ℝ) < ((1 : Matrix (Fin d) (Fin d) ℝ) + (0 : ℝ) • M).det := by
      rw [h_zero]
      norm_num
    -- Since det(1 + tM) is continuous and positive at 0, it's positive near 0
    have h_cont_at : ContinuousAt (fun t : ℝ => ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det) 0 :=
      h_cont.continuousAt
    have h_event := h_cont_at.eventually (eventually_gt_nhds h_pos)
    exact h_event
  -- First conjunct: the determinant is eventually nonzero
  have h_first : ∀ᶠ t in nhds (0 : ℝ), LinearMap.det
      ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    filter_upwards [h_det_pos_near_zero] with t ht
    rw [h_coe_comp t, h_det_factor t]
    have h_detM_ne_zero : LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b, h_matrix t]
      linarith
    exact mul_ne_zero h_detS h_detM_ne_zero
  -- Second conjunct: the derivative
  have h_second : HasDerivAt (fun t : ℝ => Real.log |LinearMap.det
      ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
      (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
    -- Near 0, we can simplify the expression
    have h_eventually_eq : ∀ᶠ t in nhds (0 : ℝ), Real.log |LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
        Real.log |LinearMap.det S_lin| +
        Real.log (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det) := by
      filter_upwards [h_det_pos_near_zero] with t ht
      rw [h_coe_comp t, h_det_factor t]
      have h_detM_eq : LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) = ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det := by
        rw [← LinearMap.det_toMatrix b, h_matrix t]
      rw [h_detM_eq]
      have hpos : ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det > 0 := ht
      rw [abs_mul, abs_of_pos hpos]
      rw [Real.log_mul (abs_pos.mpr h_detS).ne.symm (by linarith)]
    -- Now compute the derivative using the simplified expression
    refine (HasDerivAt.congr_of_eventuallyEq (𝕜 := ℝ) (F := ℝ) ?_ h_eventually_eq)
    -- The derivative of log |det S| + log(det(1 + tM)) at 0
    have h_const : HasDerivAt (fun _ : ℝ => Real.log |LinearMap.det S_lin|) (0 : ℝ) (0 : ℝ) := by
      apply hasDerivAt_const (0 : ℝ) (Real.log |LinearMap.det S_lin|)
    -- For log(det(1 + tM)), use hasDerivAt_log_det on matrix 1
    have h_log_det : HasDerivAt (fun t : ℝ => Real.log (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det))
        (((1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * M).trace) 0 := by
      apply AdversarialBco.hasDerivAt_log_det (1 : Matrix (Fin d) (Fin d) ℝ) M
      simp
    -- ((1 : Matrix _ _ ℝ)⁻¹ * M).trace = M.trace
    have h_trace : ((1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * M).trace = M.trace := by
      simp
    -- M.trace = trace(E')
    have h_trace_M : M.trace = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) E'_lin := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b E'_lin]
    rw [h_trace, h_trace_M] at h_log_det
    -- Now combine: derivative of sum = sum of derivatives
    have h_sum := h_const.add h_log_det
    -- h_sum : HasDerivAt ((fun x => Real.log |det S_lin|) + (fun t => Real.log (1 + t • M).det)) (0 + trace E'_lin) 0
    -- Goal: HasDerivAt (fun x => Real.log |det S_lin| + Real.log (1 + x • M).det) (trace ↑E') 0
    -- The function parts are definitionally equal, so we can coerce
    have h_sum' : HasDerivAt (fun (x : ℝ) => Real.log |LinearMap.det S_lin| + Real.log (1 + x • M).det)
        ((0 : ℝ) + (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d))) E'_lin) (0 : ℝ) := h_sum
    simpa [E'_lin, add_zero] using h_sum'
  exact And.intro h_first h_second

namespace AdversarialBco.Body

/-- The determinant is continuous on the operators of `EuclideanSpace ℝ (Fin d)`. -/
theorem continuous_det_clm {d : ℕ} :
    Continuous fun S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  ContinuousLinearMap.continuous_det

end AdversarialBco.Body
