/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Gauss1
public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# One-dimensional Gaussian integrals

An integral under `gaussianReal 0 1` as an integral against the density `φ`, `∫_T^∞ t φ(t) dt = φ(T)`, and the
reflection `Q(-θ) = 1 - Q(θ)`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_gaussianReal_phi (f : ℝ → ℝ) : ∫ t, f t ∂(gaussianReal 0 1) = ∫ t, f t * AdversarialBco.BodySpec.phi t := by
  have hv : (1 : ℝ≥0) ≠ 0 := by norm_num
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
  simp [AdversarialBco.BodySpec.phi, gaussianPDFReal, smul_eq_mul, mul_comm, div_eq_mul_inv]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_Ioi_mul_phi (T : ℝ) : ∫ t in Set.Ioi T, t * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.phi T := by
  let phi := AdversarialBco.BodySpec.phi
  have hcont : ContinuousWithinAt (fun (t : ℝ) => -phi t) (Set.Ici T) T := by
    have h_cont : Continuous phi := by
      unfold phi AdversarialBco.BodySpec.phi
      refine Continuous.div_const ?_ (Real.sqrt (2 * Real.pi))
      refine Real.continuous_exp.comp ?_
      continuity
    exact (h_cont.neg).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi T, HasDerivAt (fun (t : ℝ) => -phi t) (x * phi x) x := by
    intro x hx
    have h_phi_deriv : HasDerivAt phi (-(x * phi x)) x := by
      unfold phi AdversarialBco.BodySpec.phi
      have h_inner : HasDerivAt (fun (t : ℝ) => -(t^2)/2) (-x) x := by
        have hsq : HasDerivAt (fun (t : ℝ) => t^2) (2*x) x := by
          have := hasDerivAt_pow 2 x
          simpa [show ((2:ℕ) : ℝ) = (2:ℝ) by norm_num] using this
        have hdiv : HasDerivAt (fun (t : ℝ) => t^2 / 2) ((2*x)/2) x := HasDerivAt.div_const hsq 2
        have hneg' : HasDerivAt (-(fun (t : ℝ) => t^2 / 2)) (-((2*x)/2)) x := HasDerivAt.neg hdiv
        have hneg : HasDerivAt (fun (t : ℝ) => -(t^2 / 2)) (-((2*x)/2)) x := hneg'
        convert hneg using 1
        · ext t; ring
        · ring
      have h_exp : HasDerivAt (fun (t : ℝ) => Real.exp (-(t^2)/2)) (Real.exp (-(x^2)/2) * (-x)) x :=
        HasDerivAt.exp h_inner
      have h_div : HasDerivAt (fun (t : ℝ) => Real.exp (-(t^2)/2) / Real.sqrt (2 * Real.pi))
          ((Real.exp (-(x^2)/2) * (-x)) / Real.sqrt (2 * Real.pi)) x :=
        HasDerivAt.div_const h_exp (Real.sqrt (2 * Real.pi))
      convert h_div using 1
      ring
    have h_neg : HasDerivAt (fun (t : ℝ) => -phi t) (-(-(x * phi x))) x :=
      HasDerivAt.neg h_phi_deriv
    simpa [neg_neg] using h_neg
  have f'int : IntegrableOn (fun (t : ℝ) => t * phi t) (Set.Ioi T) volume := by
    unfold phi AdversarialBco.BodySpec.phi
    have h_int : Integrable (fun (x : ℝ) => x * Real.exp (-(x^2)/2)) volume := by
      have hb : 0 < (1/2 : ℝ) := by norm_num
      have h := integrable_mul_exp_neg_mul_sq hb
      have h_eq : (fun (x : ℝ) => x * Real.exp (-(1/2 : ℝ) * x ^ 2)) =
                 (fun (x : ℝ) => x * Real.exp (-(x^2)/2)) := by
        ext x; congr 1; ring
      rw [h_eq] at h
      exact h
    have h_int_on : IntegrableOn (fun (x : ℝ) => x * Real.exp (-(x^2)/2)) (Set.Ioi T) volume :=
      h_int.integrableOn
    have h_div : IntegrableOn (fun (x : ℝ) => (x * Real.exp (-(x^2)/2)) / Real.sqrt (2 * Real.pi)) (Set.Ioi T) volume :=
      h_int_on.div_const (Real.sqrt (2 * Real.pi))
    have h_eq2 : (fun (x : ℝ) => (x * Real.exp (-(x^2)/2)) / Real.sqrt (2 * Real.pi)) =
                (fun (x : ℝ) => x * (Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi))) := by
      ext x; ring
    rw [h_eq2] at h_div
    exact h_div
  have hf : Filter.Tendsto (fun (t : ℝ) => -phi t) Filter.atTop (nhds 0) := by
    unfold phi AdversarialBco.BodySpec.phi
    have h_exp : Filter.Tendsto (fun (t : ℝ) => Real.exp (-(t^2)/2)) Filter.atTop (nhds 0) := by
      have h_sq_atTop : Filter.Tendsto (fun (t : ℝ) => (t^2)/2) Filter.atTop Filter.atTop := by
        have h_pow : Filter.Tendsto (fun (t : ℝ) => t^2) Filter.atTop Filter.atTop :=
          Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
        refine Filter.Tendsto.atTop_div_const (by norm_num : 0 < (2:ℝ)) h_pow
      have h_comp := Real.tendsto_exp_neg_atTop_nhds_zero.comp h_sq_atTop
      convert h_comp using 1
      ext t
      show Real.exp (-(t^2)/2) = Real.exp (-((t^2)/2))
      congr 1
      ring
    have h_div : Filter.Tendsto (fun (t : ℝ) => Real.exp (-(t^2)/2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds (0 / Real.sqrt (2 * Real.pi))) :=
      Filter.Tendsto.div_const h_exp (Real.sqrt (2 * Real.pi))
    have h_zero_div : (0 : ℝ) / Real.sqrt (2 * Real.pi) = 0 := by norm_num
    have h_neg : Filter.Tendsto (fun (t : ℝ) => -(Real.exp (-(t^2)/2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds (-(0 / Real.sqrt (2 * Real.pi)))) :=
      Filter.Tendsto.neg h_div
    simpa [h_zero_div] using h_neg
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv f'int hf
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Qtail_neg (θ : ℝ) : AdversarialBco.BodySpec.Qtail (-θ) = 1 - AdversarialBco.BodySpec.Qtail θ := by
  have hphi_even : ∀ x : ℝ, AdversarialBco.BodySpec.phi (-x) = AdversarialBco.BodySpec.phi x := by
    intro x
    dsimp [AdversarialBco.BodySpec.phi]
    have hsq : (-x) ^ 2 = x ^ 2 := by ring
    rw [hsq]
  have hphi_int : MeasureTheory.Integrable AdversarialBco.BodySpec.phi MeasureTheory.volume := by
    have h_int : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) MeasureTheory.volume := by
      have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
      simpa [div_eq_inv_mul] using this
    have hphi_eq : AdversarialBco.BodySpec.phi = fun x => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by
      ext x; rfl
    rw [hphi_eq]
    exact h_int.div_const (Real.sqrt (2 * Real.pi))
  have hmeas : MeasurableSet (Set.Iic θ) := measurableSet_Iic
  have htotal : ∫ s, AdversarialBco.BodySpec.phi s = 1 :=
    AdversarialBco.Body2.integral_phi
  have h_add := integral_add_compl hmeas hphi_int
  have hcompl : (Set.Iic θ)ᶜ = Set.Ioi θ := by
    ext x; simp
  rw [hcompl] at h_add
  rw [htotal] at h_add
  have hIic : ∫ s in Set.Iic θ, AdversarialBco.BodySpec.phi s = 1 - ∫ s in Set.Ioi θ, AdversarialBco.BodySpec.phi s := by
    linarith
  calc
    AdversarialBco.BodySpec.Qtail (-θ) = ∫ s in Set.Ioi (-θ), AdversarialBco.BodySpec.phi s := rfl
    _ = ∫ s in Set.Ioi (-θ), AdversarialBco.BodySpec.phi (-s) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro s hs
      rw [← hphi_even s]
    _ = ∫ s in Set.Iic θ, AdversarialBco.BodySpec.phi s := by
      simp [integral_comp_neg_Ioi (-θ) AdversarialBco.BodySpec.phi, neg_neg]
    _ = 1 - ∫ s in Set.Ioi θ, AdversarialBco.BodySpec.phi s := hIic
    _ = 1 - AdversarialBco.BodySpec.Qtail θ := rfl
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

set_option maxHeartbeats 400000

end

