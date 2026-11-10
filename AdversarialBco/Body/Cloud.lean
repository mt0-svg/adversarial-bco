/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# The entropic objective: bounds, continuity, and the arithmetic of the moved components

`abs_det_le`, `integral_cloud_lipschitz`, `entropic_lower`, `entropic_bounded` and `moved_arith`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body.abs_det_le {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
      (Nat.factorial d : ℝ) * ‖S‖ ^ d := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hdet : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      ((LinearMap.toMatrix b b) (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))).det := by
    rw [LinearMap.det_toMatrix b]
  rw [hdet]
  let A := (LinearMap.toMatrix b b (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))
  have h_entry (i j : Fin d) : |A i j| ≤ ‖S‖ := by
    dsimp [A]
    have h_toMatrix : (LinearMap.toMatrix b b (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) i j =
        (S (b j)) i := by
      simp [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]
    rw [h_toMatrix]
    have h_norm_apply : |(S (b j)) i| ≤ ‖S (b j)‖ := by
      have := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ) (S (b j)) i
      simpa [Real.norm_eq_abs] using this
    have h_opNorm : ‖S (b j)‖ ≤ ‖S‖ * ‖b j‖ := ContinuousLinearMap.le_opNorm S (b j)
    have h_basis_norm : ‖b j‖ = 1 := by
      simpa [b] using OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin d) ℝ) j
    calc
      |(S (b j)) i| ≤ ‖S (b j)‖ := h_norm_apply
      _ ≤ ‖S‖ * ‖b j‖ := h_opNorm
      _ = ‖S‖ * 1 := by rw [h_basis_norm]
      _ = ‖S‖ := by simp
  have h_det_le := Matrix.det_le (abv := AbsoluteValue.abs) (x := ‖S‖) h_entry
  have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
  rw [hcard] at h_det_le
  have h_nsmul : (Nat.factorial d : ℕ) • (‖S‖ ^ d) = (Nat.factorial d : ℝ) * ‖S‖ ^ d := by
    simpa using nsmul_eq_mul (Nat.factorial d) (‖S‖ ^ d)
  rw [h_nsmul] at h_det_le
  exact h_det_le


theorem AdversarialBco.Body.integral_cloud_lipschitz {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hG : LipschitzWith L G) (b b' : EuclideanSpace ℝ (Fin d))
    (S S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    |∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, G (b' + S' g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      L * (‖b - b'‖ + ‖S - S'‖ * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  have hL_nonneg : (0 : ℝ) ≤ L := NNReal.coe_nonneg _
  have hmeas : Continuous G := hG.continuous
  -- pointwise bound
  have h_bound : ∀ g, |G (b + S g) - G (b' + S' g)| ≤ (L : ℝ) * (‖b - b'‖ + ‖S - S'‖ * ‖g‖) := by
    intro g
    calc
      |G (b + S g) - G (b' + S' g)| = dist (G (b + S g)) (G (b' + S' g)) := by rw [Real.dist_eq]
      _ ≤ (L : ℝ) * dist (b + S g) (b' + S' g) := hG.dist_le_mul _ _
      _ = (L : ℝ) * ‖(b + S g) - (b' + S' g)‖ := by rw [dist_eq_norm]
      _ = (L : ℝ) * ‖(b - b') + (S - S') g‖ := by
        have h : b + S g - (b' + S' g) = (b - b') + (S - S') g := by
          rw [sub_apply]
          abel_nf
        rw [h]
      _ ≤ (L : ℝ) * (‖b - b'‖ + ‖(S - S') g‖) := by
        nlinarith [norm_add_le (b - b') ((S - S') g)]
      _ ≤ (L : ℝ) * (‖b - b'‖ + ‖S - S'‖ * ‖g‖) := by
        have hle : ‖(S - S') g‖ ≤ ‖S - S'‖ * ‖g‖ := ContinuousLinearMap.le_opNorm (S - S') g
        nlinarith
  -- integrability of ‖g‖ under Gaussian measure
  have h_int_norm : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖) μ := by
    have h_int_id : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) μ :=
      IsGaussian.integrable_id
    exact h_int_id.norm
  -- integrability of G(b + S g)
  have h_int_GbS : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => G (b + S g)) μ := by
    -- bound: |G(b + S g)| ≤ |G 0| + L * (‖b‖ + ‖S‖ * ‖g‖)
    have h_bound_G : ∀ g, |G (b + S g)| ≤ |G 0| + (L : ℝ) * (‖b‖ + ‖S‖ * ‖g‖) := by
      intro g
      have h_lip : |G (b + S g) - G 0| ≤ (L : ℝ) * ‖b + S g‖ := by
        have := hG.dist_le_mul (b + S g) 0
        rw [Real.dist_eq, dist_eq_norm, sub_zero] at this
        exact this
      have h_norm : ‖b + S g‖ ≤ ‖b‖ + ‖S‖ * ‖g‖ := by
        calc
          ‖b + S g‖ ≤ ‖b‖ + ‖S g‖ := norm_add_le _ _
          _ ≤ ‖b‖ + ‖S‖ * ‖g‖ := by
            nlinarith [ContinuousLinearMap.le_opNorm S g]
      calc
        |G (b + S g)| = |G 0 + (G (b + S g) - G 0)| := by ring
        _ ≤ |G 0| + |G (b + S g) - G 0| := abs_add_le _ _
        _ ≤ |G 0| + (L : ℝ) * ‖b + S g‖ := by nlinarith
        _ ≤ |G 0| + (L : ℝ) * (‖b‖ + ‖S‖ * ‖g‖) := by nlinarith
    have h_ae : AEStronglyMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => G (b + S g)) μ :=
      (hmeas.comp (continuous_const.add S.continuous)).aestronglyMeasurable
    have h_bound_int : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => |G 0| + (L : ℝ) * (‖b‖ + ‖S‖ * ‖g‖)) μ := by
      refine Integrable.add (integrable_const _) ?_
      refine Integrable.const_mul ?_ (L : ℝ)
      refine Integrable.add (integrable_const _) ?_
      refine Integrable.const_mul h_int_norm ‖S‖
    refine Integrable.mono' h_bound_int h_ae ?_
    filter_upwards with g
    simpa [Real.norm_eq_abs] using h_bound_G g
  -- integrability of G(b' + S' g)
  have h_int_Gb'S' : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => G (b' + S' g)) μ := by
    -- same proof with b', S' instead of b, S
    have h_bound_G : ∀ g, |G (b' + S' g)| ≤ |G 0| + (L : ℝ) * (‖b'‖ + ‖S'‖ * ‖g‖) := by
      intro g
      have h_lip : |G (b' + S' g) - G 0| ≤ (L : ℝ) * ‖b' + S' g‖ := by
        have := hG.dist_le_mul (b' + S' g) 0
        rw [Real.dist_eq, dist_eq_norm, sub_zero] at this
        exact this
      have h_norm : ‖b' + S' g‖ ≤ ‖b'‖ + ‖S'‖ * ‖g‖ := by
        calc
          ‖b' + S' g‖ ≤ ‖b'‖ + ‖S' g‖ := norm_add_le _ _
          _ ≤ ‖b'‖ + ‖S'‖ * ‖g‖ := by
            nlinarith [ContinuousLinearMap.le_opNorm S' g]
      calc
        |G (b' + S' g)| = |G 0 + (G (b' + S' g) - G 0)| := by ring
        _ ≤ |G 0| + |G (b' + S' g) - G 0| := abs_add_le _ _
        _ ≤ |G 0| + (L : ℝ) * ‖b' + S' g‖ := by nlinarith
        _ ≤ |G 0| + (L : ℝ) * (‖b'‖ + ‖S'‖ * ‖g‖) := by nlinarith
    have h_ae : AEStronglyMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => G (b' + S' g)) μ :=
      (hmeas.comp (continuous_const.add S'.continuous)).aestronglyMeasurable
    have h_bound_int : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => |G 0| + (L : ℝ) * (‖b'‖ + ‖S'‖ * ‖g‖)) μ := by
      refine Integrable.add (integrable_const _) ?_
      refine Integrable.const_mul ?_ (L : ℝ)
      refine Integrable.add (integrable_const _) ?_
      refine Integrable.const_mul h_int_norm ‖S'‖
    refine Integrable.mono' h_bound_int h_ae ?_
    filter_upwards with g
    simpa [Real.norm_eq_abs] using h_bound_G g
  -- main inequality
  have h_int_sub : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => G (b + S g) - G (b' + S' g)) μ :=
    h_int_GbS.sub h_int_Gb'S'
  have h_int_bound : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => (L : ℝ) * (‖b - b'‖ + ‖S - S'‖ * ‖g‖)) μ := by
    refine Integrable.const_mul ?_ (L : ℝ)
    refine Integrable.add (integrable_const _) ?_
    refine Integrable.const_mul h_int_norm ‖S - S'‖
  calc
    |∫ g, G (b + S g) ∂μ - ∫ g, G (b' + S' g) ∂μ|
        = |∫ g, (G (b + S g) - G (b' + S' g)) ∂μ| := by
      rw [integral_sub h_int_GbS h_int_Gb'S']
    _ ≤ ∫ g, |G (b + S g) - G (b' + S' g)| ∂μ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ g, (L : ℝ) * (‖b - b'‖ + ‖S - S'‖ * ‖g‖) ∂μ := by
      refine integral_mono (h_int_sub.abs) h_int_bound h_bound
    _ = (L : ℝ) * ∫ g, (‖b - b'‖ + ‖S - S'‖ * ‖g‖) ∂μ := by
      rw [integral_const_mul]
    _ = (L : ℝ) * (∫ g, ‖b - b'‖ ∂μ + ∫ g, ‖S - S'‖ * ‖g‖ ∂μ) := by
      rw [integral_add (integrable_const _) (Integrable.const_mul h_int_norm ‖S - S'‖)]
    _ = (L : ℝ) * ((μ.real Set.univ) • ‖b - b'‖ + (‖S - S'‖ * ∫ g, ‖g‖ ∂μ)) := by
      rw [integral_const, integral_const_mul]
    _ = (L : ℝ) * ((1 : ℝ) • ‖b - b'‖ + ‖S - S'‖ * ∫ g, ‖g‖ ∂μ) := by
      rw [probReal_univ]
    _ = (L : ℝ) * (‖b - b'‖ + ‖S - S'‖ * ∫ g, ‖g‖ ∂μ) := by
      simp


theorem AdversarialBco.Body.entropic_lower {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hG : LipschitzWith L G) (a a' : ℝ) (ha : 0 < a) (hcoer : ∀ x, a * ‖x‖ - a' ≤ G x)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    a * ‖b‖ - a' ≤ ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      a * (Real.sqrt (2 / Real.pi) * ‖S‖) - a' ≤ ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hγ_prob : IsProbabilityMeasure γ := by infer_instance
  have hγ_symm : γ.map (fun w => -w) = γ := by
    simpa using stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin d)))
  have hγ_int_norm : Integrable (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) γ := by
    rw [integrable_norm_iff]
    · exact IsGaussian.integrable_id
    · exact continuous_id.aestronglyMeasurable
  let μ := γ.map S
  have hS_meas : AEMeasurable S γ := S.continuous.aemeasurable
  haveI hμ_prob : IsProbabilityMeasure μ :=
    ((Measure.isProbabilityMeasure_map_iff hS_meas).2 inferInstance)
  have hμ_symm : μ.map (fun w => -w) = μ := by
    dsimp [μ]
    calc
      (γ.map S).map (fun w => -w) = γ.map ((fun w => -w) ∘ S) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
      _ = γ.map (fun g => -(S g)) := rfl
      _ = γ.map (fun g => S (-g)) := by
        refine congrArg (fun f => γ.map f) (funext fun g => ?_)
        simp [S.map_neg]
      _ = γ.map (S ∘ (fun g => -g)) := rfl
      _ = (γ.map (fun g => -g)).map S := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
      _ = γ.map S := by rw [hγ_symm]
  have hμ_int_norm : Integrable (fun w => ‖w‖) μ := by
    have h_norm_meas : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) μ :=
      continuous_norm.aestronglyMeasurable
    rw [integrable_map_measure h_norm_meas hS_meas]
    have h_bound : ∀ g, ‖S g‖ ≤ ‖S‖ * ‖g‖ := fun g => S.le_opNorm g
    have h_int_bound : Integrable (fun g => ‖S‖ * ‖g‖) γ :=
      hγ_int_norm.const_mul ‖S‖
    have h_meas : AEStronglyMeasurable (fun g => ‖S g‖) γ :=
      (continuous_norm.comp S.continuous).aestronglyMeasurable
    refine h_int_bound.mono h_meas ?_
    filter_upwards with g
    simpa using h_bound g
  rcases AdversarialBco.norm_add_symm_ge μ hμ_symm hμ_int_norm b with ⟨h_norm1, h_norm2⟩
  have h_int_norm_Sg : Integrable (fun g => ‖S g‖) γ := by
    have h_bound' : ∀ g, ‖S g‖ ≤ ‖S‖ * ‖g‖ := fun g => S.le_opNorm g
    have h_int_bound' : Integrable (fun g => ‖S‖ * ‖g‖) γ := hγ_int_norm.const_mul ‖S‖
    have h_meas : AEStronglyMeasurable (fun g => ‖S g‖) γ :=
      (continuous_norm.comp S.continuous).aestronglyMeasurable
    refine h_int_bound'.mono h_meas ?_
    filter_upwards with g
    simpa using h_bound' g
  have h_int_norm_bSw : Integrable (fun g => ‖b + S g‖) γ := by
    have h_bound : ∀ g, ‖b + S g‖ ≤ ‖b‖ + ‖S g‖ := fun g => norm_add_le b (S g)
    have h_int_bound : Integrable (fun g => ‖b‖ + ‖S g‖) γ := by
      have h1 : Integrable (fun _ => ‖b‖) γ := integrable_const _
      exact Integrable.add h1 h_int_norm_Sg
    have h_meas : AEStronglyMeasurable (fun g => ‖b + S g‖) γ := by
      have h_cont : Continuous (fun g => b + S g) := by
        continuity
      exact (continuous_norm.comp h_cont).aestronglyMeasurable
    refine h_int_bound.mono' h_meas ?_
    filter_upwards with g
    simpa using h_bound g
  have h_int_G : Integrable (fun g => G (b + S g)) γ := by
    have h_lip : LipschitzWith (L * ‖S‖₊) (fun g => G (b + S g)) :=
      AdversarialBco.lipschitzWith_comp_affine G L hG b S
    have h_bound : ∀ g, ‖G (b + S g)‖ ≤ |G b| + (L * ‖S‖₊ : ℝ) * ‖g‖ := by
      intro g
      have h := h_lip.dist_le_mul g 0
      simp only [dist_eq_norm, sub_zero] at h
      have h' : ‖G (b + S g) - G b‖ ≤ (L * ‖S‖₊ : ℝ) * ‖g‖ := by
        simpa using h
      have h_abs : ‖G (b + S g)‖ ≤ ‖G (b + S g) - G b‖ + ‖G b‖ := by
        calc
          ‖G (b + S g)‖ = ‖(G (b + S g) - G b) + G b‖ := by ring
          _ ≤ ‖G (b + S g) - G b‖ + ‖G b‖ := norm_add_le _ _
      have h_normGb : ‖G b‖ = |G b| := by simp
      rw [h_normGb] at h_abs
      refine le_trans h_abs ?_
      linarith
    have h_int_bound : Integrable (fun g => |G b| + (L * ‖S‖₊ : ℝ) * ‖g‖) γ := by
      have h1 : Integrable (fun _ => |G b|) γ := integrable_const _
      have h2 : Integrable (fun g => (L * ‖S‖₊ : ℝ) * ‖g‖) γ :=
        hγ_int_norm.const_mul (L * ‖S‖₊ : ℝ)
      exact Integrable.add h1 h2
    have h_meas : AEStronglyMeasurable (fun g => G (b + S g)) γ := by
      have h_cont : Continuous (fun g => G (b + S g)) := by
        have : Continuous G := hG.continuous
        continuity
      exact h_cont.aestronglyMeasurable
    refine h_int_bound.mono' h_meas ?_
    filter_upwards with g
    simpa using h_bound g
  have h_int_a_norm : Integrable (fun g => a * ‖b + S g‖ - a') γ := by
    have h1 : Integrable (fun g => a * ‖b + S g‖) γ :=
      h_int_norm_bSw.const_mul a
    have h2 : Integrable (fun _ => a') γ := integrable_const _
    exact Integrable.sub h1 h2
  -- first inequality via integral_map and integral_mono
  have h_first : a * ‖b‖ - a' ≤ ∫ g, G (b + S g) ∂γ := by
    have h_norm1' : ‖b‖ ≤ ∫ g, ‖b + S g‖ ∂γ := by
      calc
        ‖b‖ ≤ ∫ w, ‖b + w‖ ∂μ := h_norm1
        _ = ∫ g, ‖b + S g‖ ∂γ := by
          dsimp [μ]
          simpa using integral_map hS_meas
            ((continuous_norm.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    calc
      a * ‖b‖ - a' ≤ a * (∫ g, ‖b + S g‖ ∂γ) - a' := by
        gcongr
      _ = (∫ g, a * ‖b + S g‖ ∂γ) - a' := by
        rw [integral_const_mul a (fun g => ‖b + S g‖)]
      _ = (∫ g, a * ‖b + S g‖ ∂γ) - (∫ g, a' ∂γ) := by
        simp [integral_const]
      _ = ∫ g, (a * ‖b + S g‖ - a') ∂γ := by
        rw [integral_sub (h_int_norm_bSw.const_mul a) (integrable_const _)]
      _ ≤ ∫ g, G (b + S g) ∂γ :=
        integral_mono h_int_a_norm h_int_G (fun g => hcoer (b + S g))
  -- second inequality
  have h_second : a * (Real.sqrt (2 / Real.pi) * ‖S‖) - a' ≤ ∫ g, G (b + S g) ∂γ := by
    have h_norm2' : ∫ g, ‖S g‖ ∂γ ≤ ∫ g, ‖b + S g‖ ∂γ := by
      calc
        ∫ g, ‖S g‖ ∂γ = ∫ w, ‖w‖ ∂μ := by
          dsimp [μ]
          simpa using (integral_map hS_meas
            ((continuous_norm.comp continuous_id).aestronglyMeasurable)).symm
        _ ≤ ∫ w, ‖b + w‖ ∂μ := h_norm2
        _ = ∫ g, ‖b + S g‖ ∂γ := by
          dsimp [μ]
          simpa using integral_map hS_meas
            ((continuous_norm.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    have h_opnorm : Real.sqrt (2 / Real.pi) * ‖S‖ ≤ ∫ g, ‖S g‖ ∂γ :=
      AdversarialBco.Body.opNorm_le_integral_norm S
    have h_comb : a * (Real.sqrt (2 / Real.pi) * ‖S‖) - a' ≤ a * (∫ g, ‖b + S g‖ ∂γ) - a' := by
      gcongr
      linarith
    calc
      a * (Real.sqrt (2 / Real.pi) * ‖S‖) - a' ≤ a * (∫ g, ‖b + S g‖ ∂γ) - a' := h_comb
      _ = (∫ g, a * ‖b + S g‖ ∂γ) - a' := by
        rw [integral_const_mul a (fun g => ‖b + S g‖)]
      _ = (∫ g, a * ‖b + S g‖ ∂γ) - (∫ g, a' ∂γ) := by
        simp [integral_const]
      _ = ∫ g, (a * ‖b + S g‖ - a') ∂γ := by
        rw [integral_sub (h_int_norm_bSw.const_mul a) (integrable_const _)]
      _ ≤ ∫ g, G (b + S g) ∂γ :=
        integral_mono h_int_a_norm h_int_G (fun g => hcoer (b + S g))
  exact And.intro h_first h_second


theorem AdversarialBco.Body.entropic_bounded {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hG : LipschitzWith L G) (a a' : ℝ) (ha : 0 < a) (hcoer : ∀ x, a * ‖x‖ - a' ≤ G x) (lam : ℝ) (hlam : 0 < lam)
    (C : ℝ) :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C →
      ‖b‖ ≤ M ∧ ‖S‖ ≤ M ∧ δ ≤ |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  let h_entropic := AdversarialBco.Body.entropic_lower G L hG a a' ha hcoer
  have h_abs_det (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
      (Nat.factorial d : ℝ) * ‖S‖ ^ d :=
    AdversarialBco.Body.abs_det_le (d := d) S
  let h_bounded := AdversarialBco.bounded_of_linear_le_log
  let sqrt_term := Real.sqrt (2 / Real.pi)
  have h_sqrt_pos : 0 < sqrt_term := Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)
  let d_fact : ℝ := (Nat.factorial d : ℝ)
  have h_d_fact_pos : 0 < d_fact := by
    simpa [d_fact] using mod_cast Nat.factorial_pos d
  have h_d_fact_ne_zero : d_fact ≠ 0 := by linarith
  let δ : ℝ := Real.exp (-(C + a') / lam)
  have hδ_pos : 0 < δ := Real.exp_pos (-(C + a') / lam)
  have h_a_sqrt_pos : 0 < a * sqrt_term := mul_pos ha h_sqrt_pos
  have h_lam_d_nonneg : 0 ≤ lam * (d : ℝ) := mul_nonneg (by linarith) (by exact mod_cast Nat.zero_le d)
  -- Key inequality: for any b, S with det S ≠ 0 and the integral condition,
  -- we have a * sqrt_term * ‖S‖ - (lam * d) * max(log ‖S‖, 0) ≤ C + a' + lam * log d_fact
  have h_key_ineq (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (h_det_ne_zero : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
      (h_main : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C) :
      a * sqrt_term * ‖S‖ - (lam * (d : ℝ)) * max (Real.log ‖S‖) 0 ≤ C + a' + lam * Real.log d_fact := by
    have h_lower2 := (h_entropic b S).2
    have h_upper : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_combined : a * (Real.sqrt (2 / Real.pi) * ‖S‖) - a' ≤
        C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_abs_pos : 0 < |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_pos.mpr h_det_ne_zero
    have h_det_le : |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        d_fact * ‖S‖ ^ d := h_abs_det S
    have h_prod_pos : 0 < d_fact * ‖S‖ ^ d := lt_of_lt_of_le h_abs_pos h_det_le
    have h_norm_pow_pos : 0 < ‖S‖ ^ d := by
      by_contra! hle
      have hle' : d_fact * ‖S‖ ^ d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hle
      linarith
    have h_norm_pow_ne_zero : ‖S‖ ^ d ≠ 0 := by linarith
    have h_log_det_le : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log (d_fact * ‖S‖ ^ d) :=
      Real.log_le_log h_abs_pos h_det_le
    have h_log_prod : Real.log (d_fact * ‖S‖ ^ d) =
        Real.log d_fact + Real.log (‖S‖ ^ d) :=
      Real.log_mul h_d_fact_ne_zero h_norm_pow_ne_zero
    have h_log_pow : Real.log (‖S‖ ^ d) = (d : ℝ) * Real.log ‖S‖ :=
      Real.log_pow (x := ‖S‖) (n := d)
    have h_log_bound : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log d_fact + (d : ℝ) * Real.log ‖S‖ := by
      linarith
    have h_log_le_max : Real.log ‖S‖ ≤ max (Real.log ‖S‖) 0 := le_max_left _ _
    have h_d_nonneg : 0 ≤ (d : ℝ) := by exact mod_cast Nat.zero_le d
    have h_mul_le : (d : ℝ) * Real.log ‖S‖ ≤ (d : ℝ) * max (Real.log ‖S‖) 0 :=
      mul_le_mul_of_nonneg_left h_log_le_max h_d_nonneg
    have h_log_bound' : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log d_fact + (d : ℝ) * max (Real.log ‖S‖) 0 := by
      linarith
    nlinarith
  -- Now apply bounded_of_linear_le_log to get M_S
  rcases h_bounded (a * sqrt_term) (lam * (d : ℝ)) (C + a' + lam * Real.log d_fact)
      h_a_sqrt_pos h_lam_d_nonneg with ⟨M_S, hM_S⟩
  -- Bound for ‖S‖
  have h_bound_S (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (h_det_ne_zero : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
      (h_main : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C) :
      ‖S‖ ≤ M_S := by
    have h_norm_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
    exact hM_S ‖S‖ h_norm_nonneg (h_key_ineq b S h_det_ne_zero h_main)
  -- Bound for ‖b‖
  have h_bound_b (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (h_det_ne_zero : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
      (h_main : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C) :
      ‖b‖ ≤ (C + a' + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0)) / a := by
    have h_lower1 := (h_entropic b S).1
    have h_upper : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_combined : a * ‖b‖ - a' ≤ C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_abs_pos : 0 < |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_pos.mpr h_det_ne_zero
    have h_det_le : |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        d_fact * ‖S‖ ^ d := h_abs_det S
    have h_log_det_le : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log (d_fact * ‖S‖ ^ d) :=
      Real.log_le_log h_abs_pos h_det_le
    have h_norm_pow_ne_zero : ‖S‖ ^ d ≠ 0 := by
      by_contra! hzero
      have : |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ 0 := by
        simpa [hzero] using h_det_le
      linarith
    have h_log_prod : Real.log (d_fact * ‖S‖ ^ d) =
        Real.log d_fact + Real.log (‖S‖ ^ d) :=
      Real.log_mul h_d_fact_ne_zero h_norm_pow_ne_zero
    have h_log_pow : Real.log (‖S‖ ^ d) = (d : ℝ) * Real.log ‖S‖ :=
      Real.log_pow (x := ‖S‖) (n := d)
    have h_log_bound : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log d_fact + (d : ℝ) * Real.log ‖S‖ := by
      linarith
    have h_norm_S_le_M_S : ‖S‖ ≤ M_S := h_bound_S b S h_det_ne_zero h_main
    have h_log_norm_le_max : Real.log ‖S‖ ≤ max (Real.log M_S) 0 := by
      by_cases h_M_S_pos : 0 < M_S
      · by_cases h_norm_pos : 0 < ‖S‖
        · have h_log_le : Real.log ‖S‖ ≤ Real.log M_S :=
            Real.log_le_log h_norm_pos h_norm_S_le_M_S
          exact h_log_le.trans (le_max_left _ _)
        · have h_norm_zero : ‖S‖ = 0 := by
            have h_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
            linarith
          have h_log_zero : Real.log ‖S‖ = 0 := by
            simpa [h_norm_zero] using Real.log_zero
          rw [h_log_zero]
          exact le_max_right _ _
      · have h_norm_zero : ‖S‖ = 0 := by
          have h_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
          linarith
        have h_log_zero : Real.log ‖S‖ = 0 := by
          simpa [h_norm_zero] using Real.log_zero
        rw [h_log_zero]
        exact le_max_right _ _
    have h_log_bound' : Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0 := by
      apply le_trans h_log_bound
      gcongr
    have h_final : a * ‖b‖ - a' ≤ C + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0) :=
      calc
        a * ‖b‖ - a' ≤ C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := h_combined
        _ ≤ C + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0) := by
          gcongr
    -- Now solve for ‖b‖: a * ‖b‖ ≤ C + a' + lam * (log d_fact + d * max(log M_S, 0))
    have h_nonneg : 0 ≤ a * ‖b‖ := mul_nonneg (by linarith) (norm_nonneg _)
    have h_mul_bound : a * ‖b‖ ≤ C + a' + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0) := by
      linarith
    -- Divide both sides by a > 0
    calc
      ‖b‖ = (a * ‖b‖) / a := by field_simp [ha.ne.symm]
      _ ≤ (C + a' + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0)) / a :=
        div_le_div_of_nonneg_right h_mul_bound (by linarith)
  -- Bound for |det S|
  have h_bound_det (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (h_det_ne_zero : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
      (h_main : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C) :
      δ ≤ |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
    have h_lower1 := (h_entropic b S).1
    have h_upper : ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_combined : a * ‖b‖ - a' ≤ C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_lower_bound : -a' ≤ a * ‖b‖ - a' := by
      have h_nonneg : 0 ≤ a * ‖b‖ := mul_nonneg (by linarith) (norm_nonneg _)
      linarith
    have h_ineq : -a' ≤ C + lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      linarith
    have h_abs_pos : 0 < |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_pos.mpr h_det_ne_zero
    have h_log_div : -(C + a') / lam ≤ Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
      have h_ineq' : -(C + a') ≤ lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
        linarith
      calc
        -(C + a') / lam ≤ (lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|) / lam :=
          div_le_div_of_nonneg_right h_ineq' (by linarith)
        _ = Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
          field_simp [hlam.ne.symm]
    have h_exp_ineq : Real.exp (-(C + a') / lam) ≤ Real.exp (Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|) :=
      Real.exp_le_exp.mpr h_log_div
    have h_exp_log : Real.exp (Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|) =
        |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      Real.exp_log h_abs_pos
    rw [h_exp_log] at h_exp_ineq
    simpa [δ] using h_exp_ineq
  -- Now combine everything
  let M : ℝ := max M_S ((C + a' + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0)) / a)
  have hM_S_le_M : M_S ≤ M := le_max_left _ _
  have hM_b_le_M : (C + a' + lam * (Real.log d_fact + (d : ℝ) * max (Real.log M_S) 0)) / a ≤ M := le_max_right _ _
  refine ⟨max M 0, δ, hδ_pos, ?_⟩
  intro b S h_det_ne_zero h_main
  have hS := h_bound_S b S h_det_ne_zero h_main
  have hb := h_bound_b b S h_det_ne_zero h_main
  have hdet := h_bound_det b S h_det_ne_zero h_main
  have hS' : ‖S‖ ≤ max M 0 := le_trans hS (le_trans hM_S_le_M (le_max_left _ _))
  have hb' : ‖b‖ ≤ max M 0 := le_trans hb (le_trans hM_b_le_M (le_max_left _ _))
  exact ⟨hb', hS', hdet⟩


theorem AdversarialBco.Body.moved_arith (h η Fb Fbs Mb Mbs : ℝ) (hh : 0 < h) (hη0 : 0 ≤ η) (hη : η ≤ h / 32)
    (hmove : Fb - Fbs < -(h / 2)) (hmin : Mbs ≤ Mb + η) :
    h ^ 2 / 32 ≤ (Fb - Mb) ^ 2 + (Fbs - Mbs) ^ 2 := by
  set x := Fb - Mb with hx
  set y := Fbs - Mbs with hy
  have hx_sub_y_lt : x - y < -(15 * h / 32) := by
    have h_eq : x - y = (Fb - Fbs) - (Mb - Mbs) := by
      dsimp [x, y]
      ring
    have h_lower : Mb - Mbs ≥ -η := by
      linarith
    have h_comb : (Fb - Fbs) - (Mb - Mbs) < -(h / 2) - (-η) := by
      linarith
    have h_bound : -(h / 2) - (-η) ≤ -(15 * h / 32) := by
      nlinarith
    linarith
  have hy_sub_x_pos : 0 < y - x := by
    linarith
  have h_sq_ineq : (x - y) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by
    have h_nonneg : (x + y) ^ 2 ≥ 0 := by positivity
    nlinarith
  have h_final : h ^ 2 / 32 ≤ (15 * h / 32) ^ 2 / 2 := by
    have h_sq_nonneg : h ^ 2 ≥ 0 := by positivity
    nlinarith
  nlinarith
