/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# The standard Gaussian of `ℝ^d`

Laws of linear forms, moments, and Stein's identity for `ψ(⟨u, g⟩) H(g)` and in radial form.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal


theorem AdversarialBco.Body.map_inner_stdGaussian {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫) = gaussianReal 0 1 := by
  have hL : (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) = ⇑(innerSL ℝ u) := by
    ext g; simp [innerSL_apply_apply]
  rw [hL]
  have hmean : (stdGaussian (EuclideanSpace ℝ (Fin d)))[innerSL ℝ u] = 0 := by
    simpa using integral_strongDual_stdGaussian (innerSL ℝ u)
  have hvar : Var[innerSL ℝ u; stdGaussian (EuclideanSpace ℝ (Fin d))] = ‖innerSL ℝ u‖ ^ 2 :=
    variance_dual_stdGaussian (innerSL ℝ u)
  have hnorm : ‖innerSL ℝ u‖ = 1 := by
    rw [innerSL_apply_norm, hu]
  rw [IsGaussian.map_eq_gaussianReal (innerSL ℝ u), hmean, hvar, hnorm]
  simp


theorem AdversarialBco.Body.integral_abs_inner {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    ∫ g, |⟪u, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ‖u‖ * Real.sqrt (2 / Real.pi) := by
  by_cases hu0 : ‖u‖ = 0
  · -- u = 0 case
    have hu : u = 0 := norm_eq_zero.mp hu0
    simp [hu]
  · -- u ≠ 0 case
    have hu_pos : 0 < ‖u‖ := by
      by_contra! h
      apply hu0
      exact le_antisymm h (norm_nonneg u)
    set u0 := (‖u‖⁻¹ : ℝ) • u with hu0_def
    have hu0_norm : ‖u0‖ = 1 := by
      rw [hu0_def, norm_smul, norm_inv, norm_norm]
      field_simp [hu0]
    have h_norm_mul_inv : ‖u‖ * (‖u‖⁻¹ : ℝ) = 1 := by field_simp [hu0]
    have h_inner_val : ∀ g, ⟪u, g⟫ = ‖u‖ * ⟪u0, g⟫ := by
      intro g
      calc
        ⟪u, g⟫ = ⟪(‖u‖ * (‖u‖⁻¹ : ℝ)) • u, g⟫ := by rw [h_norm_mul_inv, one_smul]
        _ = ⟪‖u‖ • ((‖u‖⁻¹ : ℝ) • u), g⟫ := by rw [mul_smul]
        _ = ‖u‖ * ⟪(‖u‖⁻¹ : ℝ) • u, g⟫ := by rw [real_inner_smul_left]
        _ = ‖u‖ * ⟪u0, g⟫ := by rw [hu0_def]
    have h_inner : ∀ g, |⟪u, g⟫| = ‖u‖ * |⟪u0, g⟫| := by
      intro g
      rw [h_inner_val g, abs_mul, abs_of_pos hu_pos]
    have h_meas : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u0, g⟫) :=
      (continuous_inner.comp (Continuous.prodMk continuous_const continuous_id)).measurable
    calc
      ∫ g, |⟪u, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
          ∫ g, (‖u‖ * |⟪u0, g⟫|) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_congr_ae ?_
        filter_upwards with g using h_inner g
      _ = ‖u‖ * ∫ g, |⟪u0, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [MeasureTheory.integral_const_mul]
      _ = ‖u‖ * ∫ x, |x| ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u0, g⟫)) := by
        rw [integral_map_of_stronglyMeasurable h_meas continuous_abs.stronglyMeasurable]
      _ = ‖u‖ * ∫ x, |x| ∂(gaussianReal 0 1) := by
        rw [AdversarialBco.Body.map_inner_stdGaussian u0 hu0_norm]
      _ = ‖u‖ * Real.sqrt (2 * (1 : NNReal) / Real.pi) := by
        rw [AdversarialBco.integral_abs_gaussianReal 1]
      _ = ‖u‖ * Real.sqrt (2 / Real.pi) := by simp


theorem AdversarialBco.Body.opNorm_le_integral_norm {d : ℕ}
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (2 / Real.pi) * ‖S‖ ≤ ∫ g, ‖S g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_sqrt_pos : 0 < Real.sqrt (2 / Real.pi) := by
    refine Real.sqrt_pos.mpr ?_
    have h2 : 0 < (2 : ℝ) := by norm_num
    have hpi : 0 < Real.pi := Real.pi_pos
    exact div_pos h2 hpi
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 / Real.pi) := le_of_lt h_sqrt_pos
  set S_adj := (ContinuousLinearMap.adjoint S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) with hS_adj
  have h_norm_adj : ‖S_adj‖ = ‖S‖ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (F := EuclideanSpace ℝ (Fin d))).norm_map S
  have h_int_nonneg : 0 ≤ ∫ g, ‖S g‖ ∂μ := by
    refine integral_nonneg ?_
    intro g
    exact norm_nonneg _
  have h_bound : ∀ v, ‖S_adj v‖ * Real.sqrt (2 / Real.pi) ≤ ‖v‖ * (∫ g, ‖S g‖ ∂μ) := by
    intro v
    have h_cont_inner : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪v, g⟫) :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    have h_cont_comp : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪v, S g⟫) :=
      h_cont_inner.comp (ContinuousLinearMap.continuous S)
    have h_meas : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪v, S g⟫) :=
      h_cont_comp.measurable
    have h_int_abs_inner : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => |⟪v, S g⟫|) μ := by
      have h_meas_abs : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => |⟪v, S g⟫|) :=
        h_meas.abs
      have h_ae_abs : AEStronglyMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => |⟪v, S g⟫|) μ :=
        h_meas_abs.aestronglyMeasurable
      refine AdversarialBco.Body.integrable_of_abs_le_exp (fun g => |⟪v, S g⟫|) h_ae_abs
        (‖v‖ * ‖S‖) 1 ?_
      intro g
      have h_nonneg : 0 ≤ |⟪v, S g⟫| := abs_nonneg _
      calc
        |(|⟪v, S g⟫|)| = |⟪v, S g⟫| := abs_of_nonneg h_nonneg
        _ ≤ ‖v‖ * ‖S g‖ := abs_real_inner_le_norm v (S g)
        _ ≤ ‖v‖ * (‖S‖ * ‖g‖) := by
          have hle := ContinuousLinearMap.le_opNorm S g
          have h_v_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
          nlinarith
        _ = (‖v‖ * ‖S‖) * ‖g‖ := by ring
        _ ≤ (‖v‖ * ‖S‖) * Real.exp (‖g‖) := by
          have hx : ‖g‖ ≤ Real.exp (‖g‖) := by
            have := Real.add_one_le_exp (‖g‖)
            linarith
          have h_nonneg' : 0 ≤ ‖v‖ * ‖S‖ := by
            positivity
          nlinarith
        _ = (‖v‖ * ‖S‖) * Real.exp (1 * ‖g‖) := by ring
    have h_int_norm_S : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖S g‖) μ := by
      have h_ae : AEStronglyMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖S g‖) μ :=
        (ContinuousLinearMap.continuous S).aestronglyMeasurable.norm
      refine AdversarialBco.Body.integrable_of_abs_le_exp (fun g => ‖S g‖) h_ae (‖S‖) 1 ?_
      intro g
      have hle := ContinuousLinearMap.le_opNorm S g
      have h_nonneg_S : 0 ≤ ‖S‖ := norm_nonneg _
      calc
        |‖S g‖| = ‖S g‖ := abs_of_nonneg (norm_nonneg _)
        _ ≤ ‖S‖ * ‖g‖ := hle
        _ ≤ ‖S‖ * Real.exp (‖g‖) := by
          have hx : ‖g‖ ≤ Real.exp (‖g‖) := by
            have := Real.add_one_le_exp (‖g‖)
            linarith
          nlinarith
        _ = ‖S‖ * Real.exp (1 * ‖g‖) := by ring
    have h_inner_ae : (fun (g : EuclideanSpace ℝ (Fin d)) => |⟪S_adj v, g⟫|) =ᵐ[μ] (fun g => |⟪v, S g⟫|) := by
      filter_upwards with g
      simp [hS_adj, ContinuousLinearMap.adjoint_inner_left]
    calc
      ‖S_adj v‖ * Real.sqrt (2 / Real.pi) = ∫ g, |⟪S_adj v, g⟫| ∂μ := by
        rw [AdversarialBco.Body.integral_abs_inner]
      _ = ∫ g, |⟪v, S g⟫| ∂μ := by rw [integral_congr_ae h_inner_ae]
      _ ≤ ∫ g, ‖v‖ * ‖S g‖ ∂μ := by
        refine integral_mono ?_ ?_ ?_
        · simpa using h_int_abs_inner
        · exact h_int_norm_S.const_mul (‖v‖)
        · intro g
          exact abs_real_inner_le_norm v (S g)
      _ = ‖v‖ * ∫ g, ‖S g‖ ∂μ := by rw [integral_const_mul]
  have h_op_norm : ‖S_adj‖ ≤ (∫ g, ‖S g‖ ∂μ) / Real.sqrt (2 / Real.pi) := by
    refine ContinuousLinearMap.opNorm_le_bound S_adj (div_nonneg h_int_nonneg h_sqrt_nonneg) ?_
    intro v
    have hineq := h_bound v
    calc
      ‖S_adj v‖ = (‖S_adj v‖ * Real.sqrt (2 / Real.pi)) / Real.sqrt (2 / Real.pi) := by
        field_simp [h_sqrt_pos.ne.symm]
      _ ≤ (‖v‖ * (∫ g, ‖S g‖ ∂μ)) / Real.sqrt (2 / Real.pi) :=
        div_le_div_of_nonneg_right hineq h_sqrt_nonneg
      _ = ((∫ g, ‖S g‖ ∂μ) / Real.sqrt (2 / Real.pi)) * ‖v‖ := by ring
  calc
    Real.sqrt (2 / Real.pi) * ‖S‖ = Real.sqrt (2 / Real.pi) * ‖S_adj‖ := by rw [h_norm_adj]
    _ ≤ Real.sqrt (2 / Real.pi) * ((∫ g, ‖S g‖ ∂μ) / Real.sqrt (2 / Real.pi)) := by
      refine mul_le_mul_of_nonneg_left h_op_norm h_sqrt_nonneg
    _ = ∫ g, ‖S g‖ ∂μ := by
      field_simp [h_sqrt_pos.ne.symm]


theorem AdversarialBco.Body.integral_inner_sq {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪u, g⟫ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ‖u‖ ^ 2 := by
  set X := fun (g : EuclideanSpace ℝ (Fin d)) => (innerSL ℝ u) g with hX
  have hX_inner : ∀ g, X g = ⟪u, g⟫ := by
    intro g; simp [hX, innerSL_apply_apply]
  have h_int_zero : ∫ g, X g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0 := by
    rw [hX]
    simpa using integral_strongDual_stdGaussian (innerSL ℝ u)
  have h_aemeasurable : AEMeasurable X (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hX]
    exact (Continuous.aemeasurable (innerSL ℝ u).continuous)
  have h_var_eq : Var[X; stdGaussian (EuclideanSpace ℝ (Fin d))] = ∫ g, (X g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [variance_of_integral_eq_zero h_aemeasurable h_int_zero]
  have h_var_norm : Var[X; stdGaussian (EuclideanSpace ℝ (Fin d))] = ‖innerSL ℝ u‖ ^ 2 := by
    rw [hX]
    simpa using variance_dual_stdGaussian (innerSL ℝ u)
  have h_norm : ‖innerSL ℝ u‖ = ‖u‖ := innerSL_apply_norm ℝ u
  calc
    ∫ g, ⟪u, g⟫ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ g, (X g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine integral_congr_ae ?_
      filter_upwards with g
      simp [hX_inner]
    _ = Var[X; stdGaussian (EuclideanSpace ℝ (Fin d))] := by rw [h_var_eq]
    _ = ‖innerSL ℝ u‖ ^ 2 := h_var_norm
    _ = ‖u‖ ^ 2 := by rw [h_norm]


namespace AdversarialBco.Body

/-- Stein's identity in the direction `u` for `ψ(⟨u, g⟩) H(g)`. -/
theorem stein_ramp {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (ψ ψ' : ℝ → ℝ)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (A2 B2 : ℝ) (hB2 : 0 ≤ B2)
    (hψb : ∀ t, |ψ t| ≤ A2 * Real.exp (B2 * |t|)) (hψb' : ∀ t, |ψ' t| ≤ A2 * Real.exp (B2 * |t|))
    (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (H' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hH : ∀ g, HasFDerivAt H (H' g) g)
    (A1 B1 : ℝ) (hHb : ∀ g, |H g| ≤ A1 * Real.exp (B1 * ‖g‖))
    (hHb' : ∀ g, ‖H' g‖ ≤ A1 * Real.exp (B1 * ‖g‖)) :
    ∫ g, ⟪u, g⟫ * (ψ ⟪u, g⟫ * H g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ψ ⟪u, g⟫ * H' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        ∫ g, ψ' ⟪u, g⟫ * H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have ht : ∀ g : EuclideanSpace ℝ (Fin d), |⟪u, g⟫| ≤ ‖g‖ := fun g => by
    simpa [hu] using abs_real_inner_le_norm u g
  have hA2 : 0 ≤ A2 := by
    have := (abs_nonneg _).trans (hψb 0); simpa using this
  have hA1 : 0 ≤ A1 := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans (hHb 0))
  have hprod : ∀ g, A2 * Real.exp (B2 * |⟪u, g⟫|) * (A1 * Real.exp (B1 * ‖g‖)) ≤
      A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := fun g => by
    have h1 : Real.exp (B2 * |⟪u, g⟫|) ≤ Real.exp (B2 * ‖g‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (ht g) hB2)
    calc A2 * Real.exp (B2 * |⟪u, g⟫|) * (A1 * Real.exp (B1 * ‖g‖)) ≤
          A2 * Real.exp (B2 * ‖g‖) * (A1 * Real.exp (B1 * ‖g‖)) := by
          gcongr
      _ = A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := by rw [add_mul, Real.exp_add]; ring
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hψ'm : Measurable ψ' := by
    rw [show ψ' = deriv ψ from funext fun t => (hψ t).deriv.symm]; exact measurable_deriv ψ
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun g => (hH g).continuousAt
  have hH'm : Measurable fun g => H' g u := by
    rw [show H' = fderiv ℝ H from funext fun g => (hH g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ H u
  have hΦ : ∀ g, HasFDerivAt (fun g => ψ ⟪u, g⟫ * H g)
      (ψ ⟪u, g⟫ • H' g + H g • (ψ' ⟪u, g⟫ • innerSL ℝ u)) g := fun g => by
    have h1 : HasFDerivAt (fun g : EuclideanSpace ℝ (Fin d) => ψ ⟪u, g⟫) (ψ' ⟪u, g⟫ • innerSL ℝ u) g :=
      (hψ _).comp_hasFDerivAt g ((innerSL ℝ u).hasFDerivAt)
    exact h1.mul (hH g)
  have hb : ∀ g, |ψ ⟪u, g⟫ * H g| ≤ 2 * A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := fun g => by
    rw [abs_mul]
    have h0 : 0 ≤ A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := mul_nonneg (mul_nonneg hA2 hA1) (Real.exp_pos _).le
    calc |ψ ⟪u, g⟫| * |H g| ≤ A2 * Real.exp (B2 * |⟪u, g⟫|) * (A1 * Real.exp (B1 * ‖g‖)) :=
          mul_le_mul (hψb _) (hHb g) (abs_nonneg _) ((abs_nonneg _).trans (hψb _))
      _ ≤ A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := hprod g
      _ ≤ 2 * A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := by linarith
  have hb' : ∀ g, ‖ψ ⟪u, g⟫ • H' g + H g • (ψ' ⟪u, g⟫ • innerSL ℝ u)‖ ≤
      2 * A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := fun g => by
    have hi : ‖innerSL ℝ u‖ = 1 := by rw [innerSL_apply_norm, hu]
    calc ‖ψ ⟪u, g⟫ • H' g + H g • (ψ' ⟪u, g⟫ • innerSL ℝ u)‖ ≤
          ‖ψ ⟪u, g⟫ • H' g‖ + ‖H g • (ψ' ⟪u, g⟫ • innerSL ℝ u)‖ := norm_add_le _ _
      _ = |ψ ⟪u, g⟫| * ‖H' g‖ + |H g| * |ψ' ⟪u, g⟫| := by
          rw [norm_smul, norm_smul, norm_smul, hi, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
      _ ≤ A2 * Real.exp (B2 * |⟪u, g⟫|) * (A1 * Real.exp (B1 * ‖g‖)) +
            A1 * Real.exp (B1 * ‖g‖) * (A2 * Real.exp (B2 * |⟪u, g⟫|)) :=
          add_le_add (mul_le_mul (hψb _) (hHb' g) (norm_nonneg _) ((abs_nonneg _).trans (hψb _)))
            (mul_le_mul (hHb g) (hψb' _) (abs_nonneg _) ((abs_nonneg _).trans (hHb g)))
      _ ≤ 2 * A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := by nlinarith [hprod g]
  have key := stein_dir _ _ hΦ _ _ hb hb' u
  have hΦ'u : ∀ g, (ψ ⟪u, g⟫ • H' g + H g • (ψ' ⟪u, g⟫ • innerSL ℝ u)) u =
      ψ ⟪u, g⟫ * H' g u + ψ' ⟪u, g⟫ * H g := fun g => by
    simp only [_root_.add_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
      real_inner_self_eq_norm_sq, hu]
    ring
  simp only [hΦ'u] at key
  have i1 : Integrable (fun g => ψ ⟪u, g⟫ * H' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integrable_of_abs_le_exp _ ((hψc.comp hinner).measurable.mul hH'm).aestronglyMeasurable
      (A2 * A1) (B1 + B2) fun g => ?_
    rw [abs_mul]
    refine le_trans ?_ (hprod g)
    refine mul_le_mul (hψb _) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hψb _))
    rw [← Real.norm_eq_abs]
    exact ((H' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hHb' g)
  have i2 : Integrable (fun g => ψ' ⟪u, g⟫ * H g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integrable_of_abs_le_exp _ ((hψ'm.comp hinner.measurable).mul hHc.measurable).aestronglyMeasurable
      (A2 * A1) (B1 + B2) fun g => ?_
    rw [abs_mul]
    exact le_trans (mul_le_mul (hψb' _) (hHb g) (abs_nonneg _) ((abs_nonneg _).trans (hψb' _))) (hprod g)
  rw [key, integral_add i1 i2]

/-- Integrability of `ψ(⟨u, g⟩) K(g)` for functions of exponential growth. -/
theorem integrable_ramp {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (ψ : ℝ → ℝ) (hψm : Measurable ψ)
    (A2 B2 : ℝ) (hB2 : 0 ≤ B2) (hψb : ∀ t, |ψ t| ≤ A2 * Real.exp (B2 * |t|))
    (K : EuclideanSpace ℝ (Fin d) → ℝ) (hKm : AEStronglyMeasurable K (stdGaussian (EuclideanSpace ℝ (Fin d))))
    (A1 B1 : ℝ) (hKb : ∀ g, |K g| ≤ A1 * Real.exp (B1 * ‖g‖)) :
    Integrable (fun g => ψ ⟪u, g⟫ * K g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have ht : ∀ g : EuclideanSpace ℝ (Fin d), |⟪u, g⟫| ≤ ‖g‖ := fun g => by
    simpa [hu] using abs_real_inner_le_norm u g
  have hA2 : 0 ≤ A2 := by
    have := (abs_nonneg _).trans (hψb 0); simpa using this
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  refine integrable_of_abs_le_exp _ (((hψm.comp hinner.measurable).aestronglyMeasurable).mul hKm) (A2 * A1)
    (B1 + B2) fun g => ?_
  rw [abs_mul]
  have h1 : Real.exp (B2 * |⟪u, g⟫|) ≤ Real.exp (B2 * ‖g‖) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (ht g) hB2)
  calc |ψ ⟪u, g⟫| * |K g| ≤ A2 * Real.exp (B2 * ‖g‖) * (A1 * Real.exp (B1 * ‖g‖)) :=
        mul_le_mul ((hψb _).trans (mul_le_mul_of_nonneg_left h1 hA2)) (hKb g) (abs_nonneg _)
          (mul_nonneg hA2 (Real.exp_pos _).le)
    _ = A2 * A1 * Real.exp ((B1 + B2) * ‖g‖) := by rw [add_mul, Real.exp_add]; ring

/-- A linear form in the coordinates of the standard basis. -/
theorem apply_eq_sum_inner {d : ℕ} (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (g : EuclideanSpace ℝ (Fin d)) :
    ℓ g = ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * ℓ (EuclideanSpace.single i 1) := by
  have hg : (∑ i, g i • EuclideanSpace.single i (1 : ℝ)) = g := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr g
    simpa using this
  calc ℓ g = ℓ (∑ i, g i • EuclideanSpace.single i (1 : ℝ)) := by rw [hg]
    _ = ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * ℓ (EuclideanSpace.single i 1) := by
        rw [map_sum]; simp [map_smul, EuclideanSpace.inner_single_left]

/-- The radial form of Stein's identity: `E ⟨∇H(g), g⟩ = E[H(g) (|g|^2 - d)]`. -/
theorem stein_radial {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (H' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hH : ∀ g, HasFDerivAt H (H' g) g)
    (A B : ℝ) (hb : ∀ g, |H g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖H' g‖ ≤ A * Real.exp (B * ‖g‖)) :
    ∫ g, H' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, H g * (‖g‖ ^ 2 - (d : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set e : Fin d → EuclideanSpace ℝ (Fin d) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hu : ∀ i, ‖e i‖ = 1 := fun i => by simp [he]
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun g => (hH g).continuousAt
  have hH'm : ∀ v, Measurable fun g => H' g v := fun v => by
    rw [show H' = fderiv ℝ H from funext fun g => (hH g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ H v
  have hid : ∀ t : ℝ, |t| ≤ 1 * Real.exp (1 * |t|) := fun t => by
    rw [one_mul, one_mul]; linarith [Real.add_one_le_exp |t|]
  have hone : ∀ t : ℝ, |(1 : ℝ)| ≤ 1 * Real.exp (1 * |t|) := fun t => by
    rw [abs_one, one_mul]; exact Real.one_le_exp (by positivity)
  have hst : ∀ i, ∫ g, ⟪e i, g⟫ * (⟪e i, g⟫ * H g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ⟪e i, g⟫ * H' g (e i) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        ∫ g, H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := fun i => by
    have := stein_ramp (e i) (hu i) (fun t => t) (fun _ => 1) (fun t => hasDerivAt_id t) 1 1 zero_le_one hid hone
      H H' hH A B hb hb'
    simpa using this
  have iH : Integrable H (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_of_abs_le_exp _ hHc.aestronglyMeasurable _ _ hb
  have iA : ∀ i, Integrable (fun g => ⟪e i, g⟫ * H' g (e i)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun i =>
    integrable_ramp (e i) (hu i) (fun t => t) measurable_id 1 1 zero_le_one hid (fun g => H' g (e i))
      (hH'm (e i)).aestronglyMeasurable A B fun g => by
        rw [← Real.norm_eq_abs]; exact ((H' g).le_opNorm _).trans (by rw [hu i, mul_one]; exact hb' g)
  have iB : ∀ i, Integrable (fun g => ⟪e i, g⟫ * (⟪e i, g⟫ * H g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun i => (integrable_ramp (e i) (hu i) (fun t => t * t) (measurable_id.mul measurable_id) 2 2 zero_le_two
      (fun t => by
        rw [abs_mul, ← sq]
        have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
        have h2 : Real.exp |t| ≤ Real.exp (2 * |t|) := Real.exp_le_exp.2 (by linarith [abs_nonneg t])
        nlinarith [abs_nonneg t])
      H hHc.aestronglyMeasurable A B hb).congr (Filter.Eventually.of_forall fun g => by simp only; ring)
  have hsq : ∀ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ 2 = ∑ i, ⟪e i, g⟫ * ⟪e i, g⟫ := fun g => by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [he, EuclideanSpace.inner_single_left, sq]
  have e1 : (fun g => H' g g) = fun g => ∑ i, ⟪e i, g⟫ * H' g (e i) := funext fun g => apply_eq_sum_inner (H' g) g
  have e2 : (fun g => H g * (‖g‖ ^ 2 - (d : ℝ))) =
      fun g => (∑ i, ⟪e i, g⟫ * (⟪e i, g⟫ * H g)) - (d : ℝ) * H g := by
    funext g; rw [hsq, mul_sub, Finset.mul_sum]; congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  rw [e1, e2, integral_sub (integrable_finset_sum _ fun i _ => iB i) (iH.const_mul _),
    integral_finset_sum _ fun i _ => iA i, integral_finset_sum _ fun i _ => iB i, integral_const_mul]
  simp only [hst, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end AdversarialBco.Body


theorem AdversarialBco.Body.gauss_moments (d : ℕ) :
    ∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) ∧
      ∫ g, (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 2 * (d : ℝ) + 1 := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hμ : IsProbabilityMeasure μ := by infer_instance
  have h_norm_sq_le_two_exp (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 ≤ 2 * Real.exp (‖x‖) := by
    have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have h := Real.two_mul_le_exp (x := ‖x‖ / 2)
    have h' : ‖x‖ ≤ Real.exp (‖x‖ / 2) := by linarith
    have h_sq : ‖x‖ ^ 2 ≤ (Real.exp (‖x‖ / 2)) ^ 2 := by
      nlinarith [Real.exp_nonneg (‖x‖ / 2)]
    have h_exp_sq : (Real.exp (‖x‖ / 2)) ^ 2 = Real.exp (‖x‖) := by
      calc
        (Real.exp (‖x‖ / 2)) ^ 2 = Real.exp (‖x‖ / 2) * Real.exp (‖x‖ / 2) := by ring
        _ = Real.exp (‖x‖ / 2 + ‖x‖ / 2) := by rw [Real.exp_add]
        _ = Real.exp (‖x‖) := by ring
    rw [h_exp_sq] at h_sq
    nlinarith
  have h_bound1 (x : EuclideanSpace ℝ (Fin d)) : |(1 : ℝ)| ≤ (1 : ℝ) * Real.exp ((0 : ℝ) * ‖x‖) := by
    simp
  have h_bound1' (x : EuclideanSpace ℝ (Fin d)) : ‖(0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ (1 : ℝ) * Real.exp ((0 : ℝ) * ‖x‖) := by
    simp
  have h_bound2 (x : EuclideanSpace ℝ (Fin d)) : |‖x‖ ^ 2 - (d : ℝ)| ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖) := by
    have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    by_cases h : (d : ℝ) ≤ ‖x‖ ^ 2
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      -- goal: ‖x‖ ^ 2 - (d : ℝ) ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖)
      have hle : ‖x‖ ^ 2 ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖) := by
        have : ‖x‖ ^ 2 ≤ 2 * Real.exp (‖x‖) := h_norm_sq_le_two_exp x
        have h_exp_eq : Real.exp (‖x‖) = Real.exp ((1 : ℝ) * ‖x‖) := by simp
        rw [h_exp_eq] at this
        nlinarith
      linarith
    · have hsub : ‖x‖ ^ 2 - (d : ℝ) < 0 := sub_neg.mpr (not_le.mp h)
      rw [abs_of_neg hsub]
      -- goal: -(‖x‖ ^ 2 - (d : ℝ)) ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖)
      -- i.e., (d : ℝ) - ‖x‖ ^ 2 ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖)
      have h_exp_pos : 1 ≤ Real.exp (‖x‖) := Real.one_le_exp hx_nonneg
      have h_nonneg_sq : 0 ≤ ‖x‖ ^ 2 := pow_two_nonneg _
      have : (d : ℝ) - ‖x‖ ^ 2 ≤ (d : ℝ) := by linarith
      have hd_le : (d : ℝ) ≤ (d : ℝ) * Real.exp (‖x‖) := by
        have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        have : (d : ℝ) * 1 ≤ (d : ℝ) * Real.exp (‖x‖) :=
          mul_le_mul_of_nonneg_left h_exp_pos hd_nonneg
        simpa [mul_one] using this
      have h_exp_eq : Real.exp (‖x‖) = Real.exp ((1 : ℝ) * ‖x‖) := by simp
      rw [h_exp_eq] at hd_le
      nlinarith
  have h_bound2' (x : EuclideanSpace ℝ (Fin d)) : ‖(2 : ℝ) • (innerSL ℝ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x‖ ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖) := by
    have h_norm_inner : ‖(innerSL ℝ) x‖ = ‖x‖ := innerSL_apply_norm (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) x
    calc
      ‖(2 : ℝ) • (innerSL ℝ) x‖ = ‖(2 : ℝ)‖ * ‖(innerSL ℝ) x‖ := by rw [norm_smul]
      _ = 2 * ‖(innerSL ℝ) x‖ := by simp
      _ = 2 * ‖x‖ := by rw [h_norm_inner]
      _ ≤ 2 * Real.exp (‖x‖) := by
        have hx : ‖x‖ ≤ Real.exp (‖x‖) := by
          have h := Real.two_mul_le_exp (x := ‖x‖)
          -- h : 2 * ‖x‖ ≤ Real.exp (‖x‖)
          -- We need ‖x‖ ≤ Real.exp (‖x‖)
          -- Since ‖x‖ ≥ 0, we have 2*‖x‖ ≥ ‖x‖, so ‖x‖ ≤ 2*‖x‖ ≤ exp(‖x‖)
          have hx_nonneg' : 0 ≤ ‖x‖ := norm_nonneg _
          linarith
        nlinarith
      _ = 2 * Real.exp ((1 : ℝ) * ‖x‖) := by simp
      _ ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖x‖) := by
        have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        have h_exp_nonneg : 0 ≤ Real.exp ((1 : ℝ) * ‖x‖) := Real.exp_nonneg _
        nlinarith
  -- First application of stein_radial: ∫ ‖g‖^2 = d
  have h_stein1 := AdversarialBco.Body.stein_radial (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ))
    (fun (_ : EuclideanSpace ℝ (Fin d)) => (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (fun g => hasFDerivAt_const (1 : ℝ) g) (1 : ℝ) (0 : ℝ)
    h_bound1 h_bound1'
  have h_int_norm_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) μ := by
    refine integrable_of_abs_le_exp (fun g => ‖g‖ ^ 2) ?_ ((d : ℝ) + 2) 1 ?_
    · -- AEStronglyMeasurable
      exact ((continuous_norm.pow 2).aestronglyMeasurable (μ := μ))
    · -- bound
      intro g
      have h_sq_bound : ‖g‖ ^ 2 ≤ ((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖g‖) := by
        have : ‖g‖ ^ 2 ≤ 2 * Real.exp (‖g‖) := h_norm_sq_le_two_exp g
        have h_exp_eq : Real.exp (‖g‖) = Real.exp ((1 : ℝ) * ‖g‖) := by simp
        rw [h_exp_eq] at this
        nlinarith
      have h_nonneg : 0 ≤ ‖g‖ ^ 2 := pow_two_nonneg _
      simpa [abs_of_nonneg h_nonneg] using h_sq_bound
  have h_moment1 : ∫ g, ‖g‖ ^ 2 ∂μ = (d : ℝ) := by
    have h_right : (∫ g, (1 : ℝ) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ) = (∫ g, ‖g‖ ^ 2 ∂μ) - (d : ℝ) := by
      calc
        (∫ g, (1 : ℝ) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ) = (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ) := by simp
        _ = (∫ g, ‖g‖ ^ 2 ∂μ) - (∫ g, (d : ℝ) ∂μ) := integral_sub h_int_norm_sq (integrable_const _)
        _ = (∫ g, ‖g‖ ^ 2 ∂μ) - (d : ℝ) := by simp
    have h_left_zero : (∫ g, ((fun (_ : EuclideanSpace ℝ (Fin d)) => (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) g g) ∂μ) = (0 : ℝ) := by
      simp
    have h_eq := h_stein1.trans h_right
    rw [h_left_zero] at h_eq
    linarith
  -- Second application of stein_radial: ∫ (‖g‖^2 - d)^2 = 2d
  have h_stein2 := AdversarialBco.Body.stein_radial (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 - (d : ℝ))
    (fun g => (2 : ℝ) • (innerSL ℝ) g) (fun g => by
      have h := (hasStrictFDerivAt_norm_sq g).hasFDerivAt
      -- h : HasFDerivAt (fun x => ‖x‖ ^ 2) ((2 : ℕ) • (innerSL ℝ) g) g
      -- Convert (2 : ℕ) • to (2 : ℝ) •
      simpa [two_smul] using h.sub_const (d : ℝ))
    ((d : ℝ) + 2) (1 : ℝ) h_bound2 h_bound2'
  have h_int_norm_sq_sub_d_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 2 - (d : ℝ)) ^ 2) μ := by
    refine integrable_of_abs_le_exp (fun g => (‖g‖ ^ 2 - (d : ℝ)) ^ 2) ?_ (((d : ℝ) + 2) ^ 2) 2 ?_
    · -- AEStronglyMeasurable
      exact (((continuous_norm.pow 2).sub continuous_const).pow 2).aestronglyMeasurable
    · -- bound
      intro g
      have h_abs := h_bound2 g
      rw [abs_pow]
      have h_sq : |‖g‖ ^ 2 - (d : ℝ)| ^ 2 ≤ (((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 := by
        gcongr
      have h_exp_sq : (Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 = Real.exp (2 * ((1 : ℝ) * ‖g‖)) := by
        calc
          (Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 = Real.exp ((1 : ℝ) * ‖g‖) * Real.exp ((1 : ℝ) * ‖g‖) := by ring
          _ = Real.exp (((1 : ℝ) * ‖g‖) + ((1 : ℝ) * ‖g‖)) := by rw [Real.exp_add]
          _ = Real.exp (2 * ((1 : ℝ) * ‖g‖)) := by ring
      have h_goal : (((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 = ((d : ℝ) + 2) ^ 2 * Real.exp (2 * ‖g‖) := by
        calc
          (((d : ℝ) + 2) * Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 = ((d : ℝ) + 2) ^ 2 * (Real.exp ((1 : ℝ) * ‖g‖)) ^ 2 := by ring
          _ = ((d : ℝ) + 2) ^ 2 * Real.exp (2 * ((1 : ℝ) * ‖g‖)) := by rw [h_exp_sq]
          _ = ((d : ℝ) + 2) ^ 2 * Real.exp (2 * ‖g‖) := by ring
      rw [h_goal] at h_sq
      exact h_sq
  have h_moment2 : ∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ = 2 * (d : ℝ) := by
    have h_simp_left : (∫ g, ((2 : ℝ) • (innerSL ℝ) g) g ∂μ) = (∫ g, 2 * ‖g‖ ^ 2 ∂μ) := by
      simp
    have h_simp_right : (∫ g, (‖g‖ ^ 2 - (d : ℝ)) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ) = (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ) := by
      simp [sq]
    rw [h_simp_left, h_simp_right] at h_stein2
    -- h_stein2 : (∫ g, 2 * ‖g‖ ^ 2 ∂μ) = (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ)
    have h_left : (∫ g, (2 : ℝ) * ‖g‖ ^ 2 ∂μ) = 2 * (∫ g, ‖g‖ ^ 2 ∂μ) := integral_const_mul _ _
    rw [h_left, h_moment1] at h_stein2
    -- h_stein2 : 2 * (d : ℝ) = (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ)
    rw [eq_comm] at h_stein2
    exact h_stein2
  -- Third part: expand (‖g‖^2 - d - 1)^2 = (‖g‖^2 - d)^2 - 2*(‖g‖^2 - d) + 1
  have h_int_norm_sq_sub_d : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 2 - (d : ℝ))) μ :=
    h_int_norm_sq.sub (integrable_const _)
  have h_int_diff : ∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ = 0 := by
    rw [integral_sub h_int_norm_sq (integrable_const _), h_moment1]
    simp
  have h_int_one : ∫ g, (1 : ℝ) ∂μ = (1 : ℝ) := by simp
  have h_expand (g : EuclideanSpace ℝ (Fin d)) : (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 = (‖g‖ ^ 2 - (d : ℝ)) ^ 2 - 2 * (‖g‖ ^ 2 - (d : ℝ)) + 1 := by
    ring
  -- Now compute ∫ ((‖g‖^2 - d)^2 - 2*(‖g‖^2 - d) + 1)
  have h_int_all : ∫ g, (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 ∂μ = ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) ^ 2 - 2 * (‖g‖ ^ 2 - (d : ℝ)) + 1) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with g
    rw [h_expand g]
  rw [h_int_all]
  have h_int_all2 : ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) ^ 2 - 2 * (‖g‖ ^ 2 - (d : ℝ)) + 1) ∂μ =
      (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ) - 2 * (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ) + (∫ g, (1 : ℝ) ∂μ) := by
    calc
      ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) ^ 2 - 2 * (‖g‖ ^ 2 - (d : ℝ)) + 1) ∂μ
          = (∫ g, ((‖g‖ ^ 2 - (d : ℝ)) ^ 2 - 2 * (‖g‖ ^ 2 - (d : ℝ))) ∂μ) + (∫ g, (1 : ℝ) ∂μ) := by
        rw [integral_add ?_ (integrable_const _)]
        exact h_int_norm_sq_sub_d_sq.sub (h_int_norm_sq_sub_d.const_mul 2)
      _ = ((∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ) - (∫ g, 2 * (‖g‖ ^ 2 - (d : ℝ)) ∂μ)) + (∫ g, (1 : ℝ) ∂μ) := by
        rw [integral_sub h_int_norm_sq_sub_d_sq (h_int_norm_sq_sub_d.const_mul 2)]
      _ = ((∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ) - 2 * (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ)) + (∫ g, (1 : ℝ) ∂μ) := by
        have h : (∫ g, (2 : ℝ) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ) = (2 : ℝ) * (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ) :=
          integral_const_mul (2 : ℝ) (fun g => (‖g‖ ^ 2 - (d : ℝ)))
        rw [h]
      _ = (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ^ 2 ∂μ) - 2 * (∫ g, (‖g‖ ^ 2 - (d : ℝ)) ∂μ) + (∫ g, (1 : ℝ) ∂μ) := by ring
  refine ⟨h_moment1, ?_⟩
  rw [h_int_all2, h_moment2, h_int_diff, h_int_one]
  ring
