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
# The kernel of Lemma 3.4 and the one-dimensional Gaussian integrals around it

`k(t) = min(t_+, 1)`, the kernel `K(θ) = ∫_θ^∞ (k - κ) φ` and `W = K/φ` with `0 ≤ W ≤ 2`, `W ≥ κ M(T) (1 - φ(T)/φ)_+`
and `W' = θ W - (k - κ)`; the tail `E[|Z|; |Z| > T] = 2 φ(T)`, the reflection of a half-space integral, and the
arithmetic of the core bracket and of the scale.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec (phi Qtail kappa kappa2)

/-- `k(t) = min(t_+, 1)`. -/
noncomputable def kfun (t : ℝ) : ℝ := min (max t 0) 1

/-- The kernel `K(θ) = Cov(k(ζ), 1{ζ > θ}) = ∫_θ^∞ (k - κ) φ` of Lemma 3.4. -/
noncomputable def Kker (θ : ℝ) : ℝ := ∫ t in Set.Ioi θ, (kfun t - kappa) * phi t

end AdversarialBco.Body2

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

theorem AdversarialBco.Body2.Kker_nonpos (θ : ℝ) (hθ : θ ≤ 0) : AdversarialBco.Body2.Kker θ = AdversarialBco.BodySpec.kappa * (1 - AdversarialBco.BodySpec.Qtail θ) := by
  unfold AdversarialBco.Body2.Kker AdversarialBco.Body2.kfun AdversarialBco.BodySpec.Qtail
  have h_nonpos_phi : ∀ t ≤ 0, min (max t 0) 1 * AdversarialBco.BodySpec.phi t = 0 := by
    intro t ht
    have : max t 0 = 0 := by simp [ht]
    simp [this]
  -- phi is integrable on ℝ
  have h_int_phi : MeasureTheory.Integrable AdversarialBco.BodySpec.phi := by
    have hpos : 0 < (1/2 : ℝ) := by norm_num
    have h_int_exp : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
      integrable_exp_neg_mul_sq hpos
    have h_eq : AdversarialBco.BodySpec.phi = fun t => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2 : ℝ) * t ^ 2) := by
      ext t
      unfold AdversarialBco.BodySpec.phi
      ring_nf
    rw [h_eq]
    exact h_int_exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  -- kfun is continuous, hence AEStronglyMeasurable
  have h_kfun_ae : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => min (max t 0) 1) MeasureTheory.volume := by
    have h_cont : Continuous (fun t : ℝ => min (max t 0) 1) := by
      refine Continuous.min ?_ continuous_const
      refine Continuous.max continuous_id continuous_const
    exact h_cont.aestronglyMeasurable
  -- kfun is bounded by 1
  have h_kfun_bound : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume, ‖min (max t 0) 1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with t
    have h0 : 0 ≤ min (max t 0) 1 := by
      apply le_min
      · exact le_max_right t 0
      · norm_num
    have h1 : min (max t 0) 1 ≤ 1 := min_le_right _ _
    have : ‖min (max t 0) 1‖ = min (max t 0) 1 := abs_of_nonneg h0
    rw [this]
    exact h1
  -- kfun * phi is integrable on ℝ
  have h_int_kfun_phi : MeasureTheory.Integrable (fun t : ℝ => min (max t 0) 1 * AdversarialBco.BodySpec.phi t) := by
    have := MeasureTheory.Integrable.mul_bdd (f := AdversarialBco.BodySpec.phi) (g := fun t => min (max t 0) 1)
      h_int_phi h_kfun_ae h_kfun_bound
    simpa [mul_comm] using this
  -- kappa * phi is integrable on ℝ
  have h_int_kappa_phi : MeasureTheory.Integrable (fun t : ℝ => AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.phi t) := by
    exact h_int_phi.const_mul AdversarialBco.BodySpec.kappa
  -- integrability on the restricted measure
  have h_int_kfun_phi_μ : MeasureTheory.Integrable (fun t : ℝ => min (max t 0) 1 * AdversarialBco.BodySpec.phi t)
      (MeasureTheory.volume.restrict (Set.Ioi θ)) :=
    h_int_kfun_phi.restrict
  have h_int_kappa_phi_μ : MeasureTheory.Integrable (fun t : ℝ => AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.phi t)
      (MeasureTheory.volume.restrict (Set.Ioi θ)) :=
    h_int_kappa_phi.restrict
  calc
    ∫ t in Set.Ioi θ, (min (max t 0) 1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.phi t
        = ∫ t in Set.Ioi θ, ((min (max t 0) 1) * AdversarialBco.BodySpec.phi t - AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.phi t) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      ring
    _ = (∫ t in Set.Ioi θ, (min (max t 0) 1) * AdversarialBco.BodySpec.phi t) - (∫ t in Set.Ioi θ, AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.phi t) := by
      rw [integral_sub h_int_kfun_phi_μ h_int_kappa_phi_μ]
    _ = (∫ t in Set.Ioi θ, (min (max t 0) 1) * AdversarialBco.BodySpec.phi t) - (AdversarialBco.BodySpec.kappa * ∫ t in Set.Ioi θ, AdversarialBco.BodySpec.phi t) := by
      rw [integral_const_mul AdversarialBco.BodySpec.kappa (fun t => AdversarialBco.BodySpec.phi t)]
    _ = (∫ t, (min (max t 0) 1) * AdversarialBco.BodySpec.phi t) - (AdversarialBco.BodySpec.kappa * ∫ t in Set.Ioi θ, AdversarialBco.BodySpec.phi t) := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro t ht
      have ht' : t ≤ θ := by
        simpa [Set.mem_Ioi] using ht
      have ht_nonpos : t ≤ 0 := le_trans ht' hθ
      exact h_nonpos_phi t ht_nonpos
    _ = AdversarialBco.BodySpec.kappa - (AdversarialBco.BodySpec.kappa * ∫ t in Set.Ioi θ, AdversarialBco.BodySpec.phi t) := by
      rw [AdversarialBco.Body2.integral_min_pos_phi]
    _ = AdversarialBco.BodySpec.kappa * (1 - ∫ t in Set.Ioi θ, AdversarialBco.BodySpec.phi t) := by
      ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

set_option maxHeartbeats 400000

theorem AdversarialBco.Body2.hasDerivAt_Kker (θ : ℝ) : HasDerivAt AdversarialBco.Body2.Kker (-((AdversarialBco.Body2.kfun θ - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.phi θ)) θ := by
  -- Define f(t) = (kfun t - kappa) * phi t
  set f := fun t : ℝ => (AdversarialBco.Body2.kfun t - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.phi t with hf
  have hf_cont : Continuous f := by
    unfold f
    have hkfun_cont : Continuous AdversarialBco.Body2.kfun := by
      have : Continuous (fun t : ℝ => min (max t 0) 1) := by
        refine Continuous.min ?_ continuous_const
        refine Continuous.max continuous_id continuous_const
      exact this
    have hphi_cont : Continuous AdversarialBco.BodySpec.phi := by
      unfold AdversarialBco.BodySpec.phi
      continuity
    exact Continuous.mul (Continuous.sub hkfun_cont continuous_const) hphi_cont
  have hf_cont_at : ∀ x, ContinuousAt f x := fun x => hf_cont.continuousAt
  have hf_int : ∀ a b, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  have hf_strong_meas : ∀ x, StronglyMeasurableAtFilter f (nhds x) MeasureTheory.volume :=
    fun x => hf_cont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)
  -- phi is integrable on ℝ (Gaussian density)
  have h_int_phi : Integrable AdversarialBco.BodySpec.phi MeasureTheory.volume := by
    unfold AdversarialBco.BodySpec.phi
    have h_int_exp : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) MeasureTheory.volume := by
      have h_eq : (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) = fun t : ℝ => Real.exp (-((1/2 : ℝ)) * t ^ 2) := by
        ext t; ring
      rw [h_eq]
      exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    -- Use Integrable.div_const
    have h_temp : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)) MeasureTheory.volume :=
      h_int_exp.div_const (Real.sqrt (2 * Real.pi))
    simpa using h_temp
  have h_kfun_bdd : ∀ t, |AdversarialBco.Body2.kfun t| ≤ 1 := by
    intro t
    unfold AdversarialBco.Body2.kfun
    have h_nonneg : 0 ≤ min (max t 0) 1 := by
      refine le_min ?_ (by norm_num)
      exact le_max_right _ _
    have h_le_one : min (max t 0) 1 ≤ 1 := min_le_right _ _
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  have hf_intOn : ∀ a, IntegrableOn f (Set.Ioi a) MeasureTheory.volume := by
    intro a
    unfold f
    have h_int_phiOn : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi a) MeasureTheory.volume :=
      h_int_phi.integrableOn
    have h_meas_restrict : AEStronglyMeasurable (fun t : ℝ => AdversarialBco.Body2.kfun t - AdversarialBco.BodySpec.kappa) (MeasureTheory.volume.restrict (Set.Ioi a)) := by
      refine ((Continuous.aestronglyMeasurable ?_).sub aestronglyMeasurable_const).restrict
      unfold AdversarialBco.Body2.kfun
      continuity
    have h_bdd : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)), ‖(AdversarialBco.Body2.kfun t - AdversarialBco.BodySpec.kappa)‖ ≤ (1 + |AdversarialBco.BodySpec.kappa|) := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi a))] with t ht
      have h_kfun_le_one : |AdversarialBco.Body2.kfun t| ≤ 1 := h_kfun_bdd t
      calc
        ‖AdversarialBco.Body2.kfun t - AdversarialBco.BodySpec.kappa‖ ≤ |AdversarialBco.Body2.kfun t| + |AdversarialBco.BodySpec.kappa| :=
          norm_sub_le (AdversarialBco.Body2.kfun t) (AdversarialBco.BodySpec.kappa)
        _ ≤ 1 + |AdversarialBco.BodySpec.kappa| := by gcongr
    -- Now use Integrable.bdd_mul: integrable phi times bounded measurable (kfun - kappa) gives integrable f
    exact h_int_phiOn.bdd_mul h_meas_restrict h_bdd
  -- Key identity: Kker θ = Kker 0 - ∫_0^θ f
  have hKker_eq : ∀ θ, AdversarialBco.Body2.Kker θ = AdversarialBco.Body2.Kker 0 - (∫ t in (0 : ℝ)..θ, f t) := by
    intro θ
    unfold AdversarialBco.Body2.Kker
    have h_sub : (∫ t in Set.Ioi (0 : ℝ), f t) - (∫ t in Set.Ioi θ, f t) = (∫ t in (0 : ℝ)..θ, f t) := by
      rw [intervalIntegral.integral_Ioi_sub_Ioi' (hf_intOn 0) (hf_intOn θ)]
    linarith
  -- Now use FTC to get the derivative
  have h_deriv_aux : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, f t) (f θ) θ :=
    intervalIntegral.integral_hasDerivAt_right (hf_int 0 θ) (hf_strong_meas θ) (hf_cont_at θ)
  have h_deriv : HasDerivAt (fun u => AdversarialBco.Body2.Kker 0 - (∫ t in (0 : ℝ)..u, f t)) (-f θ) θ := by
    have h_const : HasDerivAt (fun _ : ℝ => AdversarialBco.Body2.Kker 0) 0 θ := hasDerivAt_const _ _
    have h_sub := h_const.sub h_deriv_aux
    -- h_sub : HasDerivAt ((fun _ => Kker 0) - (fun u => ∫ ...)) (0 - f θ) θ
    -- We need: HasDerivAt (fun u => Kker 0 - ∫ ...) (-f θ) θ
    -- Use `apply` with `h_sub` after rewriting
    have : (fun u : ℝ => AdversarialBco.Body2.Kker 0 - (∫ t in (0 : ℝ)..u, f t)) = ((fun _ : ℝ => AdversarialBco.Body2.Kker 0) - (fun u : ℝ => ∫ t in (0 : ℝ)..u, f t)) := by
      ext u; rfl
    rw [this]
    simpa [sub_zero] using h_sub
  -- Combine with the identity: note that h_deriv gives derivative of Kker 0 - ∫_0^u f
  -- and hKker_eq says Kker u = Kker 0 - ∫_0^u f
  have h_target : HasDerivAt (fun u => AdversarialBco.Body2.Kker u) (-f θ) θ := by
    -- From h_deriv, we know the derivative of (Kker 0 - ∫_0^u f)
    -- and from hKker_eq, Kker u = Kker 0 - ∫_0^u f
    -- So we need to rewrite the function
    have : (fun u => AdversarialBco.Body2.Kker 0 - (∫ t in (0 : ℝ)..u, f t)) = (fun u => AdversarialBco.Body2.Kker u) := by
      ext u; exact (hKker_eq u).symm
    rw [this] at h_deriv
    exact h_deriv
  simpa [hf] using h_target
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Kker_mid (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : AdversarialBco.Body2.Kker θ = AdversarialBco.BodySpec.phi θ - AdversarialBco.BodySpec.phi 1 + AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ := by
  unfold AdversarialBco.Body2.Kker AdversarialBco.Body2.kfun
  -- Goal: ∫ t in Ioi θ, (min (max t 0) 1 - κ) * φ t = φ θ - φ 1 + Q(1) - κ * Q(θ)
  have hb : 0 < (1/2 : ℝ) := by norm_num
  have h_int_t_exp : Integrable (fun t : ℝ => t * Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
    integrable_mul_exp_neg_mul_sq hb
  have h_int_exp : Integrable (fun t : ℝ => Real.exp (-(1/2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  set φ := AdversarialBco.BodySpec.phi with hφ
  set κ := AdversarialBco.BodySpec.kappa with hκ
  have hφ_eq : φ = fun t : ℝ => Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi) := rfl
  have h_int_tphi : Integrable (fun t : ℝ => t * φ t) := by
    rw [hφ_eq]
    have : (fun t : ℝ => t * (Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi))) =
      (fun t : ℝ => (t * Real.exp (-(1/2 : ℝ) * t ^ 2)) / Real.sqrt (2 * Real.pi)) := by
      ext t; ring_nf
    rw [this]
    exact h_int_t_exp.div_const (Real.sqrt (2 * Real.pi))
  have h_int_phi : Integrable φ := by
    rw [hφ_eq]
    have : (fun t : ℝ => Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)) =
      (fun t : ℝ => Real.exp (-(1/2 : ℝ) * t ^ 2) / Real.sqrt (2 * Real.pi)) := by
      ext t; ring_nf
    rw [this]
    exact h_int_exp.div_const (Real.sqrt (2 * Real.pi))
  have hk_bound : ∀ t, ‖(min (max t 0) 1 : ℝ)‖ ≤ 1 := by
    intro t
    have h_nonneg : 0 ≤ min (max t 0) 1 := by
      apply le_min ?_ (by norm_num)
      exact le_max_right _ _
    rw [Real.norm_of_nonneg h_nonneg]
    exact min_le_right _ _
  have h_int_kphi : Integrable (fun t : ℝ => (min (max t 0) 1) * φ t) := by
    have h_ae_bound : ∀ᵐ t ∂volume, ‖(min (max t 0) 1 : ℝ)‖ ≤ 1 := by
      filter_upwards [] with t
      exact hk_bound t
    have h_ae_meas : AEStronglyMeasurable (fun t : ℝ => (min (max t 0) 1 : ℝ)) volume := by
      refine (Continuous.aestronglyMeasurable ?_)
      continuity
    exact h_int_phi.bdd_mul h_ae_meas h_ae_bound
  -- Now the main computation
  let s := Set.Ioi θ
  have h_int_kphi_on : IntegrableOn (fun t : ℝ => (min (max t 0) 1) * φ t) s volume :=
    h_int_kphi.integrableOn
  have h_int_phi_on : IntegrableOn φ s volume :=
    h_int_phi.integrableOn
  have h_int_tphi_on : IntegrableOn (fun t : ℝ => t * φ t) s volume :=
    h_int_tphi.integrableOn
  have h_sub : ∫ t in s, ((min (max t 0) 1) - κ) * φ t =
      (∫ t in s, (min (max t 0) 1) * φ t) - κ * (∫ t in s, φ t) := by
    calc
      ∫ t in s, ((min (max t 0) 1) - κ) * φ t = ∫ t in s, ((min (max t 0) 1) * φ t - κ * φ t) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        ring
      _ = (∫ t in s, (min (max t 0) 1) * φ t) - (∫ t in s, κ * φ t) := by
        rw [integral_sub h_int_kphi_on (h_int_phi_on.const_mul κ)]
      _ = (∫ t in s, (min (max t 0) 1) * φ t) - κ * (∫ t in s, φ t) := by
        rw [integral_const_mul κ φ]
  have h_kphi_eq : (∫ t in s, (min (max t 0) 1) * φ t) = φ θ - φ 1 + AdversarialBco.BodySpec.Qtail 1 := by
    let s1 : Set ℝ := Set.Ioc θ 1
    let s2 : Set ℝ := Set.Ioi (1 : ℝ)
    have h_union : s = s1 ∪ s2 := by
      ext t; constructor
      · intro ht
        by_cases h : t ≤ 1
        · exact Or.inl ⟨ht, h⟩
        · have h' : 1 < t := by linarith
          exact Or.inr h'
      · intro ht
        rcases ht with (⟨ht1, _⟩ | ht2)
        · exact ht1
        · have h1t : 1 < t := ht2
          have hθt : θ < t := by linarith
          exact hθt
    have h_disjoint : Disjoint s1 s2 := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t; constructor
      · intro h; exfalso
        rcases h with ⟨⟨_, ht1⟩, ht2⟩
        have h1t : (1 : ℝ) < t := ht2
        linarith
      · intro h; exfalso; exact h
    have h_meas_s2 : MeasurableSet s2 := measurableSet_Ioi
    have h_meas_s1 : MeasurableSet s1 := measurableSet_Ioc
    have h_s2_sub_s : s2 ⊆ s := by
      intro t ht
      rw [Set.mem_Ioi] at ht ⊢
      linarith
    have h_sub_int : ∫ t in s1, t * φ t = φ θ - φ 1 := by
      have h_sdiff : s1 = s \ s2 := by
        ext t; constructor
        · intro h; rcases h with ⟨htθ, ht1⟩
          refine ⟨htθ, ?_⟩
          intro h2
          have h1t : (1 : ℝ) < t := h2
          linarith
        · intro h; rcases h with ⟨htθ, h_not_gt1⟩
          refine ⟨htθ, ?_⟩
          exact le_of_not_gt h_not_gt1
      rw [h_sdiff]
      rw [setIntegral_sdiff h_meas_s2 h_int_tphi_on h_s2_sub_s]
      rw [AdversarialBco.Body2.integral_Ioi_mul_phi θ, AdversarialBco.Body2.integral_Ioi_mul_phi 1]
    have h_s2_int : ∫ t in s2, (1 : ℝ) * φ t = AdversarialBco.BodySpec.Qtail 1 := by
      rw [AdversarialBco.BodySpec.Qtail]
      simp [s2, φ, one_mul]
    -- Compute the integral over s1 by rewriting the integrand
    have h_s1_int' : ∫ t in s1, (min (max t 0) 1) * φ t = ∫ t in s1, t * φ t := by
      refine setIntegral_congr_fun h_meas_s1 ?_
      intro t ht
      have ht_nonneg : 0 ≤ t := by rcases ht with ⟨htθ, _⟩; linarith
      have ht_le_one : t ≤ 1 := ht.2
      have h_max : max t 0 = t := max_eq_left ht_nonneg
      have h_min : min t 1 = t := min_eq_left ht_le_one
      simp [h_max, h_min]
    -- Compute the integral over s2 by rewriting the integrand
    have h_s2_int' : ∫ t in s2, (min (max t 0) 1) * φ t = ∫ t in s2, (1 : ℝ) * φ t := by
      refine setIntegral_congr_fun h_meas_s2 ?_
      intro t ht
      have ht_pos : 1 < t := ht
      have ht_nonneg : 0 ≤ t := by linarith
      have h_max : max t 0 = t := max_eq_left ht_nonneg
      have h_min : min t 1 = 1 := min_eq_right (by linarith)
      simp [h_max, h_min]
    -- Now combine using setIntegral_union
    have h_int_s1 : IntegrableOn (fun t : ℝ => (min (max t 0) 1) * φ t) s1 volume := by
      have h_int_t_on_s1 : IntegrableOn (fun t : ℝ => t * φ t) s1 volume :=
        h_int_tphi_on.mono_set (fun t ht => ht.1)
      have h_ae_eq : (fun t : ℝ => t * φ t) =ᵐ[volume.restrict s1] (fun t => (min (max t 0) 1) * φ t) := by
        filter_upwards [self_mem_ae_restrict h_meas_s1] with t ht
        have ht_nonneg : 0 ≤ t := by rcases ht with ⟨htθ, _⟩; linarith
        have ht_le_one : t ≤ 1 := ht.2
        have h_max : max t 0 = t := max_eq_left ht_nonneg
        have h_min : min t 1 = t := min_eq_left ht_le_one
        simp [h_max, h_min]
      exact h_int_t_on_s1.congr h_ae_eq
    have h_int_s2 : IntegrableOn (fun t : ℝ => (min (max t 0) 1) * φ t) s2 volume := by
      have h_int_phi_on_s2 : IntegrableOn φ s2 volume :=
        h_int_phi_on.mono_set h_s2_sub_s
      have h_int_one_s2 : IntegrableOn (fun t : ℝ => (1 : ℝ) * φ t) s2 volume :=
        h_int_phi_on_s2.const_mul (1 : ℝ)
      have h_ae_eq : (fun t : ℝ => (1 : ℝ) * φ t) =ᵐ[volume.restrict s2] (fun t => (min (max t 0) 1) * φ t) := by
        filter_upwards [self_mem_ae_restrict h_meas_s2] with t ht
        have ht_pos : 1 < t := ht
        have ht_nonneg : 0 ≤ t := by linarith
        have h_max : max t 0 = t := max_eq_left ht_nonneg
        have h_min : min t 1 = 1 := min_eq_right (by linarith)
        simp [h_max, h_min]
      exact h_int_one_s2.congr h_ae_eq
    calc
      ∫ t in s, (min (max t 0) 1) * φ t = ∫ t in s1 ∪ s2, (min (max t 0) 1) * φ t := by rw [h_union]
      _ = (∫ t in s1, (min (max t 0) 1) * φ t) + (∫ t in s2, (min (max t 0) 1) * φ t) := by
        rw [setIntegral_union h_disjoint h_meas_s2 h_int_s1 h_int_s2]
      _ = (∫ t in s1, t * φ t) + (∫ t in s2, (1 : ℝ) * φ t) := by rw [h_s1_int', h_s2_int']
      _ = (φ θ - φ 1) + AdversarialBco.BodySpec.Qtail 1 := by rw [h_sub_int, h_s2_int]
      _ = φ θ - φ 1 + AdversarialBco.BodySpec.Qtail 1 := by ring
  calc
    ∫ t in s, ((min (max t 0) 1) - κ) * φ t = (∫ t in s, (min (max t 0) 1) * φ t) - κ * (∫ t in s, φ t) := h_sub
    _ = (φ θ - φ 1 + AdversarialBco.BodySpec.Qtail 1) - κ * (∫ t in s, φ t) := by rw [h_kphi_eq]
    _ = (φ θ - φ 1 + AdversarialBco.BodySpec.Qtail 1) - κ * AdversarialBco.BodySpec.Qtail θ := by rfl
    _ = AdversarialBco.BodySpec.phi θ - AdversarialBco.BodySpec.phi 1 + AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ := by
      simp [φ, κ]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Kker_ge_one (θ : ℝ) (hθ : 1 ≤ θ) : AdversarialBco.Body2.Kker θ = (1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.Qtail θ := by
  dsimp [AdversarialBco.Body2.Kker, AdversarialBco.BodySpec.Qtail]
  have h_eq_on : Set.EqOn (fun t : ℝ => (AdversarialBco.Body2.kfun t - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.phi t)
      (fun t : ℝ => (1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.phi t) (Set.Ioi θ) := by
    intro t ht
    have ht1 : 1 < t := by
      have : θ < t := ht
      linarith
    dsimp [AdversarialBco.Body2.kfun]
    have hmax : max t 0 = t := max_eq_left (by linarith)
    have hmin : min t 1 = 1 := min_eq_right (by linarith)
    simp [hmax, hmin]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq_on]
  rw [MeasureTheory.integral_const_mul]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Kker_ge (θ : ℝ) : AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail |θ| ≤ AdversarialBco.Body2.Kker θ := by
  by_cases hθ0 : θ ≤ 0
  · -- case θ ≤ 0
    have h_abs : |θ| = -θ := abs_of_nonpos hθ0
    rw [h_abs, AdversarialBco.Body2.Qtail_neg θ, AdversarialBco.Body2.Kker_nonpos θ hθ0]
  · -- case 0 ≤ θ
    have hθ0' : 0 ≤ θ := by linarith
    by_cases hθ1 : θ ≤ 1
    · -- case 0 ≤ θ ≤ 1
      have h_abs : |θ| = θ := abs_of_nonneg hθ0'
      rw [h_abs, AdversarialBco.Body2.Kker_mid θ hθ0' hθ1]
      have h_nonneg := AdversarialBco.Body2.kernel_nonneg θ hθ0' hθ1
      linarith
    · -- case 1 ≤ θ
      have hθ1' : 1 ≤ θ := by linarith
      have h_abs : |θ| = θ := abs_of_nonneg hθ0'
      rw [h_abs, AdversarialBco.Body2.Kker_ge_one θ hθ1']
      have h_kappa_half : AdversarialBco.BodySpec.kappa ≤ 1 / 2 := by
        have ⟨_, hhi, _, _⟩ := AdversarialBco.Body2.kappa_bounds
        linarith
      have h_Qtail_nonneg : 0 ≤ AdversarialBco.BodySpec.Qtail θ := by
        refine MeasureTheory.integral_nonneg ?_
        intro s
        refine div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
      nlinarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

lemma Wfun_bounds_phi_pos (θ : ℝ) : 0 < AdversarialBco.BodySpec.phi θ := by
  refine div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr ?_)
  nlinarith [Real.pi_pos]

lemma Wfun_bounds_phi_even (θ : ℝ) : AdversarialBco.BodySpec.phi (-θ) = AdversarialBco.BodySpec.phi θ := by
  simp [AdversarialBco.BodySpec.phi]

lemma Wfun_bounds_phi_antitone_on : AntitoneOn AdversarialBco.BodySpec.phi (Set.Ici 0) := by
  intro a ha b hb hab
  dsimp [AdversarialBco.BodySpec.phi]
  have h_exp : Real.exp (-(b ^ 2) / 2) ≤ Real.exp (-(a ^ 2) / 2) := by
    rw [Real.exp_le_exp]
    have ha' : 0 ≤ a := ha
    have hb' : 0 ≤ b := hb
    have h_sq : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  exact div_le_div_of_nonneg_right h_exp h_sqrt_nonneg

lemma Wfun_bounds_Qtail_nonneg (θ : ℝ) : 0 ≤ AdversarialBco.BodySpec.Qtail θ := by
  refine setIntegral_nonneg measurableSet_Ioi (fun t _ => ?_)
  have h := Real.exp_pos (-(t ^ 2) / 2)
  have h_nonneg : 0 ≤ AdversarialBco.BodySpec.phi t := by
    dsimp [AdversarialBco.BodySpec.phi]
    positivity
  exact h_nonneg

lemma Wfun_bounds_phi_antitone_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    AdversarialBco.BodySpec.phi b ≤ AdversarialBco.BodySpec.phi a :=
  Wfun_bounds_phi_antitone_on ha hb hab

theorem AdversarialBco.Body2.Wfun_bounds (θ : ℝ) : 0 ≤ AdversarialBco.Body2.Kker θ / AdversarialBco.BodySpec.phi θ ∧ AdversarialBco.Body2.Kker θ / AdversarialBco.BodySpec.phi θ ≤ 2 := by
  have hphi_pos : 0 < AdversarialBco.BodySpec.phi θ := Wfun_bounds_phi_pos θ
  have hkappa_nonneg : 0 ≤ AdversarialBco.BodySpec.kappa := by
    rcases AdversarialBco.Body2.kappa_bounds with ⟨hlo, _, _, _⟩
    linarith
  constructor
  · -- lower bound: 0 ≤ Kker θ / phi θ
    have hKker_nonneg : 0 ≤ AdversarialBco.Body2.Kker θ := by
      have h := AdversarialBco.Body2.Kker_ge θ
      have hnonneg : 0 ≤ AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail |θ| :=
        mul_nonneg hkappa_nonneg (Wfun_bounds_Qtail_nonneg |θ|)
      linarith
    exact div_nonneg hKker_nonneg hphi_pos.le
  · -- upper bound: Kker θ / phi θ ≤ 2
    by_cases hθ0 : θ ≤ 0
    · -- case θ ≤ 0
      have hKker_eq : AdversarialBco.Body2.Kker θ = AdversarialBco.BodySpec.kappa * (1 - AdversarialBco.BodySpec.Qtail θ) :=
        AdversarialBco.Body2.Kker_nonpos θ hθ0
      have hQtail_neg : 1 - AdversarialBco.BodySpec.Qtail θ = AdversarialBco.BodySpec.Qtail (-θ) := by
        rw [← AdversarialBco.Body2.Qtail_neg θ]
      have hKker_eq' : AdversarialBco.Body2.Kker θ = AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail (-θ) := by
        rw [hKker_eq, hQtail_neg]
      have hphi_eq : AdversarialBco.BodySpec.phi θ = AdversarialBco.BodySpec.phi (-θ) := by
        rw [← Wfun_bounds_phi_even θ]
      rw [hKker_eq', hphi_eq]
      have h_negθ_nonneg : 0 ≤ -θ := by linarith
      have h_mills_anti : AdversarialBco.BodySpec.Qtail (-θ) / AdversarialBco.BodySpec.phi (-θ) ≤
          AdversarialBco.BodySpec.Qtail 0 / AdversarialBco.BodySpec.phi 0 :=
        AdversarialBco.Body2.mills_antitone (Set.mem_Ici.mpr (by norm_num))
          (Set.mem_Ici.mpr h_negθ_nonneg) h_negθ_nonneg
      have h_mills_zero : AdversarialBco.BodySpec.Qtail 0 / AdversarialBco.BodySpec.phi 0 = Real.sqrt (Real.pi / 2) :=
        AdversarialBco.Body2.mills_zero
      rw [h_mills_zero] at h_mills_anti
      have h_sqrt_le_two : Real.sqrt (Real.pi / 2) ≤ 2 := by
        have hpi : Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
        have hdiv : Real.pi / 2 ≤ 4 := by linarith
        calc
          Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hdiv
          _ = 2 := by norm_num
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
      have h_kappa_half : AdversarialBco.BodySpec.kappa ≤ 1/2 := by
        rcases AdversarialBco.Body2.kappa_bounds with ⟨_, hhi, _, _⟩
        linarith
      calc
        (AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail (-θ)) / AdversarialBco.BodySpec.phi (-θ)
            = AdversarialBco.BodySpec.kappa * (AdversarialBco.BodySpec.Qtail (-θ) / AdversarialBco.BodySpec.phi (-θ)) := by
          ring
        _ ≤ AdversarialBco.BodySpec.kappa * Real.sqrt (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left h_mills_anti hkappa_nonneg
        _ ≤ (1/2 : ℝ) * Real.sqrt (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right h_kappa_half h_sqrt_nonneg
        _ ≤ (1/2 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left h_sqrt_le_two (by norm_num)
        _ = 1 := by norm_num
        _ ≤ 2 := by norm_num
    · -- case θ > 0
      push_neg at hθ0
      by_cases hθ1 : θ ≤ 1
      · -- case 0 < θ ≤ 1
        have hKker_eq : AdversarialBco.Body2.Kker θ = AdversarialBco.BodySpec.phi θ - AdversarialBco.BodySpec.phi 1 + AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ :=
          AdversarialBco.Body2.Kker_mid θ (by linarith) hθ1
        rw [hKker_eq]
        have h_phi1_le_phiθ : AdversarialBco.BodySpec.phi 1 ≤ AdversarialBco.BodySpec.phi θ :=
          Wfun_bounds_phi_antitone_of_nonneg (by linarith) (by linarith) hθ1
        have h_Qtail1_le_phi1 : AdversarialBco.BodySpec.Qtail 1 ≤ AdversarialBco.BodySpec.phi 1 := by
          have h := AdversarialBco.Body2.Qtail_le_phi_div 1 (by norm_num)
          simpa [div_one] using h
        have h_Qtail1_le_phiθ : AdversarialBco.BodySpec.Qtail 1 ≤ AdversarialBco.BodySpec.phi θ := by
          linarith
        calc
          (AdversarialBco.BodySpec.phi θ - AdversarialBco.BodySpec.phi 1 + AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ) / AdversarialBco.BodySpec.phi θ
              = 1 - (AdversarialBco.BodySpec.phi 1 / AdversarialBco.BodySpec.phi θ) + (AdversarialBco.BodySpec.Qtail 1 / AdversarialBco.BodySpec.phi θ) - (AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ / AdversarialBco.BodySpec.phi θ) := by
            field_simp [hphi_pos.ne.symm]
          _ ≤ 1 + (AdversarialBco.BodySpec.Qtail 1 / AdversarialBco.BodySpec.phi θ) := by
            have h_nonpos : -(AdversarialBco.BodySpec.phi 1 / AdversarialBco.BodySpec.phi θ) - (AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ / AdversarialBco.BodySpec.phi θ) ≤ 0 := by
              have h1 : 0 ≤ AdversarialBco.BodySpec.phi 1 / AdversarialBco.BodySpec.phi θ :=
                div_nonneg (Wfun_bounds_phi_pos 1).le hphi_pos.le
              have h2 : 0 ≤ AdversarialBco.BodySpec.kappa * AdversarialBco.BodySpec.Qtail θ / AdversarialBco.BodySpec.phi θ :=
                div_nonneg (mul_nonneg hkappa_nonneg (Wfun_bounds_Qtail_nonneg θ)) hphi_pos.le
              linarith
            linarith
          _ ≤ 1 + (AdversarialBco.BodySpec.phi θ / AdversarialBco.BodySpec.phi θ) := by
            have hdiv : AdversarialBco.BodySpec.Qtail 1 / AdversarialBco.BodySpec.phi θ ≤
                AdversarialBco.BodySpec.phi θ / AdversarialBco.BodySpec.phi θ :=
              (div_le_div_iff_of_pos_right hphi_pos).mpr h_Qtail1_le_phiθ
            linarith
          _ = 1 + 1 := by
            field_simp [hphi_pos.ne.symm]
          _ = 2 := by norm_num
      · -- case θ > 1
        push_neg at hθ1
        have hKker_eq : AdversarialBco.Body2.Kker θ = (1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.Qtail θ :=
          AdversarialBco.Body2.Kker_ge_one θ (by linarith)
        rw [hKker_eq]
        have h_Qt_le_phi : AdversarialBco.BodySpec.Qtail θ ≤ AdversarialBco.BodySpec.phi θ := by
          have h := AdversarialBco.Body2.Qtail_le_phi_div θ hθ0
          -- h : Qtail θ ≤ phi θ / θ
          have hdiv : AdversarialBco.BodySpec.phi θ / θ ≤ AdversarialBco.BodySpec.phi θ :=
            div_le_self hphi_pos.le hθ1.le
          linarith
        have h_kappa_le_one : 1 - AdversarialBco.BodySpec.kappa ≤ 1 := by
          rcases AdversarialBco.Body2.kappa_bounds with ⟨_, hhi, _, _⟩
          linarith
        have hQtail_nonneg : 0 ≤ AdversarialBco.BodySpec.Qtail θ := Wfun_bounds_Qtail_nonneg θ
        have h_mul : (1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.Qtail θ ≤ 1 * AdversarialBco.BodySpec.Qtail θ := by
          nlinarith
        calc
          ((1 - AdversarialBco.BodySpec.kappa) * AdversarialBco.BodySpec.Qtail θ) / AdversarialBco.BodySpec.phi θ
              ≤ (1 * AdversarialBco.BodySpec.Qtail θ) / AdversarialBco.BodySpec.phi θ :=
            div_le_div_of_nonneg_right h_mul hphi_pos.le
          _ = AdversarialBco.BodySpec.Qtail θ / AdversarialBco.BodySpec.phi θ := by simp
          _ ≤ AdversarialBco.BodySpec.phi θ / AdversarialBco.BodySpec.phi θ :=
            (div_le_div_iff_of_pos_right hphi_pos).mpr h_Qt_le_phi
          _ = 1 := by field_simp [hphi_pos.ne.symm]
          _ ≤ 2 := by norm_num
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec

lemma Wfun_ge_phi_pos (t : ℝ) : 0 < phi t := by
  dsimp [phi]
  have h_exp : 0 < Real.exp (-(t ^ 2) / 2) := Real.exp_pos _
  have h_sqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma Wfun_ge_phi_even (t : ℝ) : phi (-t) = phi t := by
  dsimp [phi]
  have h_sq : (-t) ^ 2 = t ^ 2 := by ring
  rw [h_sq]

lemma Wfun_ge_phi_antitone_on_Ici : AntitoneOn phi (Set.Ici 0) := by
  intro a ha b hb hle
  dsimp [phi]
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  have hsq : a ^ 2 ≤ b ^ 2 := by
    nlinarith
  have h_exp : Real.exp (-(b ^ 2) / 2) ≤ Real.exp (-(a ^ 2) / 2) := by
    have : -(b ^ 2) / 2 ≤ -(a ^ 2) / 2 := by
      nlinarith
    exact Real.exp_le_exp.mpr this
  have h_denom : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  gcongr

lemma Wfun_ge_Qtail_nonneg (T : ℝ) : 0 ≤ Qtail T := by
  dsimp [Qtail]
  refine integral_nonneg ?_
  intro s
  have : 0 ≤ phi s := le_of_lt (Wfun_ge_phi_pos s)
  exact this

lemma Wfun_ge_kappa_nonneg : 0 ≤ kappa := by
  have h := AdversarialBco.Body2.kappa_bounds
  rcases h with ⟨hl, _, _, _⟩
  linarith

end AdversarialBco.Body2

open AdversarialBco.BodySpec

theorem AdversarialBco.Body2.Wfun_ge (T θ : ℝ) (hT : 0 ≤ T) : AdversarialBco.BodySpec.kappa * (AdversarialBco.BodySpec.Qtail T / AdversarialBco.BodySpec.phi T) * (1 - min 1 (AdversarialBco.BodySpec.phi T / AdversarialBco.BodySpec.phi θ)) ≤ AdversarialBco.Body2.Kker θ / AdversarialBco.BodySpec.phi θ := by
  have h_phi_pos : ∀ t, 0 < phi t := Wfun_ge_phi_pos
  have h_phi_nonneg : ∀ t, 0 ≤ phi t := fun t => le_of_lt (h_phi_pos t)
  have h_Qtail_nonneg : ∀ T, 0 ≤ Qtail T := Wfun_ge_Qtail_nonneg
  have h_kappa_nonneg : 0 ≤ kappa := Wfun_ge_kappa_nonneg
  have h_abs_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have h_phi_abs_eq : phi (|θ|) = phi θ := by
    by_cases hθ_nonneg : 0 ≤ θ
    · rw [abs_of_nonneg hθ_nonneg]
    · rw [abs_of_neg (not_le.mp hθ_nonneg), Wfun_ge_phi_even]
  by_cases h_abs_le_T : |θ| ≤ T
  · -- case |θ| ≤ T: phi T ≤ phi |θ| = phi θ
    have hT_mem : T ∈ Set.Ici 0 := hT
    have h_abs_mem : |θ| ∈ Set.Ici 0 := h_abs_nonneg
    have h_phi_T_le_phi_abs : phi T ≤ phi (|θ|) :=
      Wfun_ge_phi_antitone_on_Ici h_abs_mem hT_mem h_abs_le_T
    have h_phi_T_le_phi_θ : phi T ≤ phi θ := by
      rwa [h_phi_abs_eq] at h_phi_T_le_phi_abs
    have h_phi_T_div_phi_θ_le_one : phi T / phi θ ≤ 1 := by
      rw [div_le_one (h_phi_pos θ)]
      exact h_phi_T_le_phi_θ
    have h_min_eq : min 1 (phi T / phi θ) = phi T / phi θ :=
      min_eq_right h_phi_T_div_phi_θ_le_one
    have h_mills : Qtail T / phi T ≤ Qtail (|θ|) / phi (|θ|) :=
      AdversarialBco.Body2.mills_antitone h_abs_mem hT_mem h_abs_le_T
    have h_mills' : Qtail T / phi T ≤ Qtail (|θ|) / phi θ := by
      rwa [h_phi_abs_eq] at h_mills
    have h_Kker_ge : kappa * Qtail (|θ|) ≤ AdversarialBco.Body2.Kker θ :=
      AdversarialBco.Body2.Kker_ge θ
    have h_aux_nonneg : 0 ≤ 1 - phi T / phi θ := by
      have : phi T / phi θ ≤ 1 := h_phi_T_div_phi_θ_le_one
      linarith
    have h_q_nonneg : 0 ≤ Qtail T / phi T := div_nonneg (h_Qtail_nonneg T) (h_phi_nonneg T)
    have h_q_abs_nonneg : 0 ≤ Qtail (|θ|) / phi θ :=
      div_nonneg (h_Qtail_nonneg (|θ|)) (h_phi_nonneg θ)
    calc
      kappa * (Qtail T / phi T) * (1 - min 1 (phi T / phi θ))
          = kappa * (Qtail T / phi T) * (1 - phi T / phi θ) := by rw [h_min_eq]
      _ ≤ kappa * (Qtail (|θ|) / phi θ) * (1 - phi T / phi θ) := by
        have h_mul : kappa * (Qtail T / phi T) ≤ kappa * (Qtail (|θ|) / phi θ) := by
          gcongr
        have h_nonneg : 0 ≤ 1 - phi T / phi θ := h_aux_nonneg
        nlinarith
      _ ≤ kappa * (Qtail (|θ|) / phi θ) := by
        have h_nonneg_prod : 0 ≤ kappa * (Qtail (|θ|) / phi θ) := by
          have : 0 ≤ Qtail (|θ|) / phi θ := div_nonneg (h_Qtail_nonneg _) (h_phi_nonneg θ)
          nlinarith
        have h_one_minus : 1 - phi T / phi θ ≤ 1 := by
          have : 0 ≤ phi T / phi θ := div_nonneg (h_phi_nonneg T) (h_phi_nonneg θ)
          linarith
        nlinarith
      _ = (kappa * Qtail (|θ|)) / phi θ := by ring
      _ ≤ AdversarialBco.Body2.Kker θ / phi θ := by
        gcongr
        exact le_of_lt (h_phi_pos θ)
  · -- case T < |θ|: min 1 (phi T / phi θ) = 1, left side = 0
    have hT_lt_abs : T < |θ| := by
      by_contra! h
      apply h_abs_le_T
      exact h
    have hT_mem : T ∈ Set.Ici 0 := hT
    have h_abs_mem : |θ| ∈ Set.Ici 0 := h_abs_nonneg
    have h_phi_abs_le_phi_T : phi (|θ|) ≤ phi T :=
      Wfun_ge_phi_antitone_on_Ici hT_mem h_abs_mem (le_of_lt hT_lt_abs)
    have h_phi_θ_le_phi_T : phi θ ≤ phi T := by
      rwa [h_phi_abs_eq] at h_phi_abs_le_phi_T
    have h_one_le_div : 1 ≤ phi T / phi θ := by
      rw [one_le_div (h_phi_pos θ)]
      exact h_phi_θ_le_phi_T
    have h_min_eq : min 1 (phi T / phi θ) = 1 :=
      min_eq_left h_one_le_div
    have h_left_zero : kappa * (Qtail T / phi T) * (1 - min 1 (phi T / phi θ)) = 0 := by
      rw [h_min_eq]
      ring
    have h_Kker_ge : kappa * Qtail (|θ|) ≤ AdversarialBco.Body2.Kker θ :=
      AdversarialBco.Body2.Kker_ge θ
    have h_Kker_nonneg : 0 ≤ AdversarialBco.Body2.Kker θ := by
      have : 0 ≤ kappa * Qtail (|θ|) := by
        nlinarith [h_kappa_nonneg, h_Qtail_nonneg (|θ|)]
      linarith
    have h_right_nonneg : 0 ≤ AdversarialBco.Body2.Kker θ / phi θ :=
      div_nonneg h_Kker_nonneg (h_phi_nonneg θ)
    rw [h_left_zero]
    exact h_right_nonneg
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

lemma hasDerivAt_Wfun_hasDerivAt_phi (θ : ℝ) : HasDerivAt AdversarialBco.BodySpec.phi (-θ * AdversarialBco.BodySpec.phi θ) θ := by
  dsimp [AdversarialBco.BodySpec.phi]
  have h_sqrt_pos : Real.sqrt (2 * Real.pi) > 0 :=
    Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
  have h_sqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by linarith
  have h_sq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * θ) θ := by
    simpa using hasDerivAt_pow 2 θ
  have h_sq_div_two : HasDerivAt (fun t : ℝ => t ^ 2 / 2) θ θ := by
    have := HasDerivAt.const_mul ((1 : ℝ) / 2) h_sq
    -- this: HasDerivAt (fun t => (1/2) * (t^2)) ((1/2) * (2*θ)) θ
    -- goal: HasDerivAt (fun t => t^2/2) θ θ
    -- (1/2) * (t^2) = t^2/2 by ring, (1/2)*(2*θ) = θ by ring
    convert this using 1
    · ext t; ring
    · ring
  have h_neg_sq_div_two : HasDerivAt (fun t : ℝ => -(t ^ 2) / 2) (-θ) θ := by
    have := HasDerivAt.neg h_sq_div_two
    -- this: HasDerivAt (fun t => -(t^2/2)) (-θ) θ
    -- goal: HasDerivAt (fun t => -(t^2)/2) (-θ) θ
    -- -(t^2/2) = -(t^2)/2 by neg_div
    convert this using 1
    ext t; simp [neg_div]
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) (Real.exp (-(θ ^ 2) / 2) * (-θ)) θ := by
    have := HasDerivAt.exp h_neg_sq_div_two
    -- this: HasDerivAt (fun t => Real.exp (-(t^2)/2)) (Real.exp (-(θ^2)/2) * (-θ)) θ
    -- goal: same
    -- The function in this is Real.exp ((-(t^2)/2)) which is definitionally Real.exp (-(t^2)/2)
    -- So they match
    exact this
  have h_div := HasDerivAt.div h_exp (hasDerivAt_const θ (Real.sqrt (2 * Real.pi))) h_sqrt_ne
  convert h_div using 1
  · rfl
  · have h_sq_sqrt : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by nlinarith [Real.pi_pos])
    field_simp [h_sqrt_ne]
    ring

theorem AdversarialBco.Body2.hasDerivAt_Wfun (θ : ℝ) : HasDerivAt (fun t => AdversarialBco.Body2.Kker t / AdversarialBco.BodySpec.phi t) (θ * (AdversarialBco.Body2.Kker θ / AdversarialBco.BodySpec.phi θ) - (AdversarialBco.Body2.kfun θ - AdversarialBco.BodySpec.kappa)) θ := by
  have h_phi_ne : AdversarialBco.BodySpec.phi θ ≠ 0 := by
    dsimp [AdversarialBco.BodySpec.phi]
    have h_exp_pos : Real.exp (-(θ ^ 2) / 2) > 0 := Real.exp_pos _
    have h_sqrt_pos : Real.sqrt (2 * Real.pi) > 0 :=
      Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
    positivity
  have h_Kker := AdversarialBco.Body2.hasDerivAt_Kker θ
  have h_phi := hasDerivAt_Wfun_hasDerivAt_phi θ
  have h_div := HasDerivAt.div h_Kker h_phi h_phi_ne
  convert h_div using 1
  field_simp [h_phi_ne]
  ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
open Set

theorem AdversarialBco.Body2.integral_abs_tail (T : ℝ) (hT : 0 ≤ T) : ∫ t, (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t = 2 * AdversarialBco.BodySpec.phi T := by
  have hphi_even (t : ℝ) : AdversarialBco.BodySpec.phi (-t) = AdversarialBco.BodySpec.phi t := by
    unfold AdversarialBco.BodySpec.phi
    simp [sq, mul_comm]
  have hphi_nonneg (t : ℝ) : 0 ≤ AdversarialBco.BodySpec.phi t := by
    unfold AdversarialBco.BodySpec.phi
    positivity
  -- integrability of |t| * phi t
  have h_int_abs : Integrable (fun (t : ℝ) => |t| * AdversarialBco.BodySpec.phi t) volume := by
    unfold AdversarialBco.BodySpec.phi
    have h_int : Integrable (fun (t : ℝ) => t * Real.exp (-(t ^ 2) / 2)) volume := by
      have := integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have h_abs : Integrable (fun (t : ℝ) => |t * Real.exp (-(t ^ 2) / 2)|) volume :=
      h_int.abs
    have h_eq : (fun (t : ℝ) => |t| * Real.exp (-(t ^ 2) / 2)) = (fun (t : ℝ) => |t * Real.exp (-(t ^ 2) / 2)|) := by
      ext t; simp [abs_mul]
    have h_target : Integrable (fun (t : ℝ) => |t| * (Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi))) volume := by
      have : (fun (t : ℝ) => |t| * (Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi))) =
          (fun (t : ℝ) => (|t| * Real.exp (-(t ^ 2) / 2)) / Real.sqrt (2 * Real.pi)) := by
        ext t; ring
      rw [this]
      rw [← h_eq] at h_abs
      exact h_abs.div_const (Real.sqrt (2 * Real.pi))
    exact h_target
  -- integrability of the integrand
  have h_int : Integrable (fun (t : ℝ) => (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t) volume := by
    apply h_int_abs.mono' ?_ ?_
    · -- AEStronglyMeasurable
      refine ((Measurable.ite ?_ measurable_abs measurable_const).mul ?_).aestronglyMeasurable
      · exact measurableSet_lt (measurable_const : Measurable (fun (_ : ℝ) => T)) measurable_abs
      · unfold AdversarialBco.BodySpec.phi
        refine Measurable.div ?_ ?_
        · refine Real.measurable_exp.comp ?_
          refine Measurable.div ?_ ?_
          · refine Measurable.neg ?_
            have h : Measurable (fun (x : ℝ) => x ^ 2) := by
              have hh : Measurable (fun (x : ℝ) => (2 : ℕ)) := measurable_const
              exact measurable_id.pow hh
            exact h
          · exact measurable_const
        · exact measurable_const
    · filter_upwards with t
      by_cases h : T < |t|
      · have h_nonneg : 0 ≤ |t| * AdversarialBco.BodySpec.phi t :=
          mul_nonneg (abs_nonneg _) (hphi_nonneg t)
        have h_eq : (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t = |t| * AdversarialBco.BodySpec.phi t := by
          simp [h]
        have h_norm : ‖(if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t‖ = |t| * AdversarialBco.BodySpec.phi t := by
          rw [h_eq]
          exact abs_of_nonneg h_nonneg
        rw [h_norm]
      · have h_nonneg : 0 ≤ |t| * AdversarialBco.BodySpec.phi t :=
          mul_nonneg (abs_nonneg _) (hphi_nonneg t)
        simp [h, h_nonneg]
  have h_int_on (s : Set ℝ) : IntegrableOn (fun (t : ℝ) => (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t) s volume :=
    h_int.integrableOn
  -- split ℝ into Ioi 0 and Iic 0
  have h_split : Set.Ioi (0 : ℝ) ∪ Set.Iic (0 : ℝ) = Set.univ := by
    ext x; simp
  have h_disjoint : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iic (0 : ℝ)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x; simp
  have h_meas_Iic : MeasurableSet (Set.Iic (0 : ℝ)) := measurableSet_Iic
  -- compute integral over Ioi 0
  have h_pos : ∫ t in Set.Ioi (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.phi T := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t
          = ∫ t in Set.Ioi (0 : ℝ), (if T < t then t else 0) * AdversarialBco.BodySpec.phi t := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        have ht' : 0 < t := ht
        simp [abs_of_pos ht']
      _ = ∫ t in Set.Ioi (0 : ℝ), (Set.indicator (Set.Ioi T) id t) * AdversarialBco.BodySpec.phi t := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        have ht' : 0 < t := ht
        by_cases hTt : T < t
        · simp [Set.indicator, hTt]
        · simp [Set.indicator, hTt]
      _ = ∫ t in Set.Ioi (0 : ℝ), Set.indicator (Set.Ioi T) (fun x => x * AdversarialBco.BodySpec.phi x) t := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        by_cases hTt : T < t
        · simp [Set.indicator, hTt]
        · simp [Set.indicator, hTt]
      _ = ∫ t in (Set.Ioi (0 : ℝ) ∩ Set.Ioi T), t * AdversarialBco.BodySpec.phi t := by
        rw [setIntegral_indicator measurableSet_Ioi]
      _ = ∫ t in Set.Ioi T, t * AdversarialBco.BodySpec.phi t := by
        have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioi T = Set.Ioi T := by
          ext x; constructor
          · exact fun h => h.2
          · intro hx
            have hxT : T < x := hx
            have hx0 : (0 : ℝ) < x := by linarith
            exact ⟨hx0, hxT⟩
        rw [h_inter]
      _ = AdversarialBco.BodySpec.phi T :=
        AdversarialBco.Body2.integral_Ioi_mul_phi T
  -- compute integral over Iic 0
  have h_neg : ∫ t in Set.Iic (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.phi T := by
    set f := (fun (u : ℝ) => (if T < u then u else 0) * AdversarialBco.BodySpec.phi u) with hf
    have h_on_Iic : ∀ t ∈ Set.Iic (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t = f (-t) := by
      intro t ht
      have ht' : t ≤ 0 := ht
      have h_abs : |t| = -t := abs_of_nonpos ht'
      have h_phi : AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.phi (-t) := by
        rw [hphi_even]
      dsimp [f]
      rw [h_abs, h_phi]
    calc
      ∫ t in Set.Iic (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t
          = ∫ t in Set.Iic (0 : ℝ), f (-t) := by
        refine setIntegral_congr_ae measurableSet_Iic ?_
        filter_upwards with t ht
        exact h_on_Iic t ht
      _ = ∫ t in Set.Ioi (-(0 : ℝ)), f t := by rw [integral_comp_neg_Iic 0 f]
      _ = ∫ t in Set.Ioi (0 : ℝ), f t := by simp
      _ = ∫ t in Set.Ioi (0 : ℝ), (if T < t then t else 0) * AdversarialBco.BodySpec.phi t := rfl
      _ = ∫ t in Set.Ioi (0 : ℝ), (Set.indicator (Set.Ioi T) id t) * AdversarialBco.BodySpec.phi t := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        have ht' : 0 < t := ht
        by_cases hTt : T < t
        · simp [Set.indicator, hTt]
        · simp [Set.indicator, hTt]
      _ = ∫ t in Set.Ioi (0 : ℝ), Set.indicator (Set.Ioi T) (fun x => x * AdversarialBco.BodySpec.phi x) t := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        filter_upwards with t ht
        by_cases hTt : T < t
        · simp [Set.indicator, hTt]
        · simp [Set.indicator, hTt]
      _ = ∫ t in (Set.Ioi (0 : ℝ) ∩ Set.Ioi T), t * AdversarialBco.BodySpec.phi t := by
        rw [setIntegral_indicator measurableSet_Ioi]
      _ = ∫ t in Set.Ioi T, t * AdversarialBco.BodySpec.phi t := by
        have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioi T = Set.Ioi T := by
          ext x; constructor
          · exact fun h => h.2
          · intro hx
            have hxT : T < x := hx
            have hx0 : (0 : ℝ) < x := by linarith
            exact ⟨hx0, hxT⟩
        rw [h_inter]
      _ = AdversarialBco.BodySpec.phi T :=
        AdversarialBco.Body2.integral_Ioi_mul_phi T
  -- combine using setIntegral_union
  calc
    ∫ t, (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t
        = ∫ t in Set.univ, (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t := by simp
    _ = ∫ t in (Set.Ioi (0 : ℝ) ∪ Set.Iic (0 : ℝ)), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t := by rw [h_split]
    _ = (∫ t in Set.Ioi (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t)
        + (∫ t in Set.Iic (0 : ℝ), (if T < |t| then |t| else 0) * AdversarialBco.BodySpec.phi t) := by
      rw [setIntegral_union h_disjoint h_meas_Iic (h_int_on _) (h_int_on _)]
    _ = AdversarialBco.BodySpec.phi T + AdversarialBco.BodySpec.phi T := by rw [h_pos, h_neg]
    _ = 2 * AdversarialBco.BodySpec.phi T := by ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_half_reflect {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d)))) (hsym : ∀ g, f (g - (2 * ⟪u, g⟫) • u) = f g) : ∫ g, (if 0 < ⟪u, g⟫ then f g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 1 / 2 * ∫ g, f g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let μ := stdGaussian E
  -- The reflection ρ across the hyperplane orthogonal to u
  let ρ : E ≃ₗᵢ[ℝ] E := (ℝ ∙ u)ᗮ.reflection
  have hρ_eq : ∀ g, ρ g = g - (2 * ⟪u, g⟫) • u := by
    intro g
    calc
      ρ g = ((ℝ ∙ u)ᗮ).reflection g := rfl
      _ = -((ℝ ∙ u).reflection g) := by rw [Submodule.reflection_orthogonal_apply]
      _ = -(2 • ((ℝ ∙ u).starProjection g) - g) := by rw [Submodule.reflection_apply]
      _ = g - 2 • ((ℝ ∙ u).starProjection g) := by
        abel
      _ = g - 2 • (⟪u, g⟫ • u) := by
        rw [Submodule.starProjection_unit_singleton (𝕜 := ℝ) hu g]
      _ = g - (2 * ⟪u, g⟫) • u := by
        norm_num
        rw [← smul_smul]
        exact (Nat.cast_smul_eq_nsmul (R := ℝ) (n := 2) (b := ⟪u, g⟫ • u)).symm
  have hρ_inner : ∀ g, ⟪u, ρ g⟫ = -⟪u, g⟫ := by
    intro g
    rw [hρ_eq g]
    calc
      ⟪u, g - (2 * ⟪u, g⟫) • u⟫ = ⟪u, g⟫ - ⟪u, (2 * ⟪u, g⟫) • u⟫ := by rw [inner_sub_right]
      _ = ⟪u, g⟫ - (2 * ⟪u, g⟫) * ⟪u, u⟫ := by simp [inner_smul_right]
      _ = ⟪u, g⟫ - (2 * ⟪u, g⟫) * (‖u‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪u, g⟫ - (2 * ⟪u, g⟫) * 1 := by rw [hu, one_pow]
      _ = ⟪u, g⟫ - 2 * ⟪u, g⟫ := by ring
      _ = -⟪u, g⟫ := by ring
  have hρ_symm : ∀ g, f (ρ g) = f g := by
    intro g
    rw [hρ_eq g]
    exact hsym g
  -- The reflection preserves the standard Gaussian measure
  have hμ_map : μ.map ρ = μ := by
    simpa [μ] using stdGaussian_map ρ
  -- Change of variables: ∫ g(g) ∂μ = ∫ g(ρ g) ∂μ
  have h_integral_map : ∀ (g : E → ℝ), ∫ x, g x ∂μ = ∫ x, g (ρ x) ∂μ := by
    intro g
    calc
      ∫ x, g x ∂μ = ∫ x, g x ∂(μ.map ρ) := by rw [hμ_map]
      _ = ∫ x, g (ρ x) ∂μ := by
        simpa [LinearIsometryEquiv.coe_toMeasurableEquiv] using
          MeasureTheory.integral_map_equiv ρ.toMeasurableEquiv g
  -- The set {g | ⟪u, g⟫ = 0} has measure zero
  have h_null : μ {g | ⟪u, g⟫ = 0} = 0 := by
    have h_map : μ.map (fun g => ⟪u, g⟫) = gaussianReal 0 1 := AdversarialBco.Body.map_inner_stdGaussian u hu
    have h_singleton : (gaussianReal 0 1 : Measure ℝ) {0} = 0 := by
      have h_noAtoms : NoAtoms (gaussianReal (0 : ℝ) 1) :=
        ProbabilityTheory.noAtoms_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
      exact h_noAtoms.measure_singleton 0
    have h_meas : Measurable fun g : E => ⟪u, g⟫ :=
      (measurable_const.inner (measurable_id (α := E)))
    have h_set_eq : {g | ⟪u, g⟫ = 0} = (fun g => ⟪u, g⟫) ⁻¹' {0} := by
      ext g; simp
    calc
      μ {g | ⟪u, g⟫ = 0} = μ ((fun g => ⟪u, g⟫) ⁻¹' {0}) := by rw [h_set_eq]
      _ = (μ.map (fun g => ⟪u, g⟫)) {0} := by
        rw [MeasureTheory.Measure.map_apply h_meas (measurableSet_singleton 0)]
      _ = (gaussianReal 0 1) {0} := by rw [h_map]
      _ = 0 := h_singleton
  -- Define the three regions
  let s_pos : Set E := {g | 0 < ⟪u, g⟫}
  let s_zero : Set E := {g | ⟪u, g⟫ = 0}
  let s_neg : Set E := {g | ⟪u, g⟫ < 0}
  have hm_pos : MeasurableSet s_pos := by
    have h_meas_inner : Measurable fun g : E => ⟪u, g⟫ :=
      (measurable_const.inner (measurable_id (α := E)))
    exact measurableSet_lt measurable_const h_meas_inner
  have hm_zero : MeasurableSet s_zero := by
    have h_meas_inner : Measurable fun g : E => ⟪u, g⟫ :=
      (measurable_const.inner (measurable_id (α := E)))
    exact h_meas_inner (measurableSet_singleton 0)
  have hm_neg : MeasurableSet s_neg := by
    have h_meas_inner : Measurable fun g : E => ⟪u, g⟫ :=
      (measurable_const.inner (measurable_id (α := E)))
    exact measurableSet_lt h_meas_inner measurable_const
  have hn_pos : NullMeasurableSet s_pos μ := hm_pos.nullMeasurableSet
  have hn_zero : NullMeasurableSet s_zero μ := hm_zero.nullMeasurableSet
  have hn_neg : NullMeasurableSet s_neg μ := hm_neg.nullMeasurableSet
  -- f equals the sum of its restrictions to the three regions
  have h_partition : ∀ g, f g = (s_pos.indicator f) g + (s_zero.indicator f) g + (s_neg.indicator f) g := by
    intro g
    dsimp [s_pos, s_zero, s_neg]
    by_cases hpos : 0 < ⟪u, g⟫
    · have hne : ⟪u, g⟫ ≠ 0 := by linarith
      have hnlt : ¬ ⟪u, g⟫ < 0 := by linarith
      simp [hpos, hne, hnlt]
    · by_cases hzero : ⟪u, g⟫ = 0
      · simp [hzero]
      · have hneg : ⟪u, g⟫ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
        simp [hpos, hzero, hneg]
  -- Integrability of the restricted functions
  have h_int_pos : Integrable (s_pos.indicator f) μ := hf.indicator₀ hn_pos
  have h_int_zero : Integrable (s_zero.indicator f) μ := hf.indicator₀ hn_zero
  have h_int_neg : Integrable (s_neg.indicator f) μ := hf.indicator₀ hn_neg
  -- Total integral = sum of the three restricted integrals
  have h_total : ∫ g, f g ∂μ = (∫ g, (s_pos.indicator f) g ∂μ) + (∫ g, (s_zero.indicator f) g ∂μ) + (∫ g, (s_neg.indicator f) g ∂μ) := by
    have hsum1 : ∫ g, ((s_pos.indicator f) + (s_zero.indicator f)) g ∂μ = (∫ g, (s_pos.indicator f) g ∂μ) + (∫ g, (s_zero.indicator f) g ∂μ) :=
      integral_add h_int_pos h_int_zero
    calc
      ∫ g, f g ∂μ = ∫ g, ((s_pos.indicator f) g + (s_zero.indicator f) g + (s_neg.indicator f) g) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        exact h_partition g
      _ = ∫ g, (((s_pos.indicator f) + (s_zero.indicator f)) g + (s_neg.indicator f) g) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [Pi.add_apply, add_assoc]
      _ = ∫ g, ((s_pos.indicator f) + (s_zero.indicator f)) g ∂μ + ∫ g, (s_neg.indicator f) g ∂μ := by
        rw [integral_add (h_int_pos.add h_int_zero) h_int_neg]
      _ = ((∫ g, (s_pos.indicator f) g ∂μ) + (∫ g, (s_zero.indicator f) g ∂μ)) + ∫ g, (s_neg.indicator f) g ∂μ := by
        rw [hsum1]
      _ = (∫ g, (s_pos.indicator f) g ∂μ) + (∫ g, (s_zero.indicator f) g ∂μ) + (∫ g, (s_neg.indicator f) g ∂μ) := by ring
  -- The middle integral is zero because the set has measure zero
  have h_mid_zero : ∫ g, (s_zero.indicator f) g ∂μ = 0 := by
    rw [integral_indicator₀ hn_zero]
    exact MeasureTheory.setIntegral_measure_zero f h_null
  -- Therefore total = pos + neg
  have h_total' : ∫ g, f g ∂μ = (∫ g, (s_pos.indicator f) g ∂μ) + (∫ g, (s_neg.indicator f) g ∂μ) := by
    rw [h_total, h_mid_zero, add_zero]
  -- Key equality: pos = neg by symmetry (change of variables)
  have h_eq : (∫ g, (s_pos.indicator f) g ∂μ) = (∫ g, (s_neg.indicator f) g ∂μ) := by
    calc
      (∫ g, (s_pos.indicator f) g ∂μ) = (∫ g, (s_pos.indicator f) (ρ g) ∂μ) := by
        simpa using (h_integral_map (s_pos.indicator f))
      _ = (∫ g, (if g ∈ s_neg then f (ρ g) else 0) ∂μ) := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [Set.indicator, s_pos, s_neg, hρ_inner g]
      _ = (∫ g, (if g ∈ s_neg then f g else 0) ∂μ) := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [hρ_symm g]
      _ = (∫ g, (s_neg.indicator f) g ∂μ) := by
        simp [Set.indicator, s_neg]
  -- Now combine: total = pos + neg = pos + pos = 2 * pos
  rw [h_eq] at h_total'
  have h_result : (∫ g, (s_pos.indicator f) g ∂μ) = 1/2 * ∫ g, f g ∂μ := by
    linarith
  -- But the LHS of the goal is exactly ∫ g, (s_pos.indicator f) g ∂μ
  simpa [s_pos, Set.indicator] using h_result
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.core_bracket (κ d ϑ h T Mt B : ℝ) (hκ : 312 / 1000 ≤ κ) (hκ' : κ ≤ 1 / 2) (hd : 1 ≤ d) (hϑ : 0 < ϑ) (hh : 0 < h) (hT : 0 ≤ T) (hM : 1 / (1 + T) ≤ Mt) (hB : (κ / 2 - 1 / 16) * h / ϑ + κ * Mt * h / (32 * d) ≤ B) : κ / 32 * h / ((1 + T) * d) ≤ min 1 (ϑ / Real.sqrt d) * B := by
  have hd_pos : 0 < d := by linarith
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have h_one_plus_T_pos : 0 < 1 + T := by linarith
  have hκ_nonneg : 0 ≤ κ := by linarith
  have h_κ_half_sub_sixteenth_nonneg : 0 ≤ κ / 2 - 1 / 16 := by nlinarith
  have h_κ_32_nonneg : 0 ≤ κ / 32 := div_nonneg hκ_nonneg (by norm_num)
  have h_num_nonneg : 0 ≤ κ / 32 * h := mul_nonneg h_κ_32_nonneg (by linarith)
  have h_sqrt_le_d : Real.sqrt d ≤ d := by
    calc
      Real.sqrt d ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = d := Real.sqrt_sq (by linarith)
  set ω := min 1 (ϑ / Real.sqrt d) with hω_def
  have hω_nonneg : 0 ≤ ω := by
    rw [hω_def]
    exact le_min (by norm_num) (div_nonneg (by linarith) (by linarith))
  by_cases hϑ_le_sqrt_d : ϑ ≤ Real.sqrt d
  · -- case ϑ ≤ √d, so ω = ϑ/√d
    have h_ϑ_div_sqrt_d_le_one : ϑ / Real.sqrt d ≤ 1 := by
      exact (div_le_one hsqrt_pos).mpr hϑ_le_sqrt_d
    have hω_eq : ω = ϑ / Real.sqrt d := by
      rw [hω_def]
      exact min_eq_right h_ϑ_div_sqrt_d_le_one
    rw [hω_eq]
    -- Goal: κ/32 * h / ((1+T)*d) ≤ (ϑ/√d) * B
    have h1 : κ / 32 * h / ((1 + T) * d) ≤ κ / 32 * h / d :=
      div_le_div_of_nonneg_left h_num_nonneg hd_pos (by nlinarith)
    have h2 : κ / 32 * h / d ≤ (κ / 2 - 1 / 16) * h / d := by
      have hnum : κ / 32 * h ≤ (κ / 2 - 1 / 16) * h := by
        have : κ / 32 ≤ κ / 2 - 1 / 16 := by nlinarith
        nlinarith
      gcongr
    have h3 : (κ / 2 - 1 / 16) * h / d ≤ (κ / 2 - 1 / 16) * h / Real.sqrt d := by
      have hnum_nonneg' : 0 ≤ (κ / 2 - 1 / 16) * h :=
        mul_nonneg h_κ_half_sub_sixteenth_nonneg (by linarith)
      exact div_le_div_of_nonneg_left hnum_nonneg' hsqrt_pos h_sqrt_le_d
    have h4 : (κ / 2 - 1 / 16) * h / Real.sqrt d ≤ (ϑ / Real.sqrt d) * B := by
      have h_eq : (κ / 2 - 1 / 16) * h / Real.sqrt d = (ϑ / Real.sqrt d) * ((κ / 2 - 1 / 16) * h / ϑ) := by
        field_simp [hϑ.ne.symm, hsqrt_pos.ne.symm]
      rw [h_eq]
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) (by linarith))
      -- Need: (κ/2 - 1/16) * h / ϑ ≤ B
      have h_term_nonneg : 0 ≤ κ * Mt * h / (32 * d) := by
        refine div_nonneg ?_ (by nlinarith)
        refine mul_nonneg (mul_nonneg hκ_nonneg ?_) (by linarith)
        have : 0 ≤ Mt := by
          have : 0 < 1 / (1 + T) := div_pos (by norm_num) h_one_plus_T_pos
          linarith
        exact this
      linarith
    calc
      κ / 32 * h / ((1 + T) * d) ≤ κ / 32 * h / d := h1
      _ ≤ (κ / 2 - 1 / 16) * h / d := h2
      _ ≤ (κ / 2 - 1 / 16) * h / Real.sqrt d := h3
      _ ≤ (ϑ / Real.sqrt d) * B := h4
  · -- case √d < ϑ, so ω = 1
    have h_one_lt_ϑ_div_sqrt_d : 1 < ϑ / Real.sqrt d := by
      refine (one_lt_div hsqrt_pos).mpr ?_
      linarith
    have hω_eq : ω = 1 := by
      rw [hω_def]
      exact min_eq_left (by linarith)
    rw [hω_eq, one_mul]
    -- Goal: κ/32 * h / ((1+T)*d) ≤ B
    have h1 : κ / 32 * h / ((1 + T) * d) ≤ κ * Mt * h / (32 * d) := by
      have hM' : 1 ≤ (1 + T) * Mt := by
        calc
          1 = (1 / (1 + T)) * (1 + T) := by field_simp [h_one_plus_T_pos.ne.symm]
          _ ≤ Mt * (1 + T) := mul_le_mul_of_nonneg_right hM (by linarith)
          _ = (1 + T) * Mt := mul_comm _ _
      field_simp [hd_pos.ne.symm, h_one_plus_T_pos.ne.symm, (show (32 : ℝ) ≠ 0 from by norm_num)]
      -- Goal: 1 ≤ (1 + T) * Mt
      exact hM'
    have h2 : κ * Mt * h / (32 * d) ≤ B := by
      have h_nonneg : 0 ≤ (κ / 2 - 1 / 16) * h / ϑ := by
        refine div_nonneg (mul_nonneg h_κ_half_sub_sixteenth_nonneg (by linarith)) (by linarith)
      linarith
    calc
      κ / 32 * h / ((1 + T) * d) ≤ κ * Mt * h / (32 * d) := h1
      _ ≤ B := h2
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.phiT_tail (L h d : ℝ) (hL : 0 ≤ L) (hh : 0 < h) (hd : 1 ≤ d) : 2 * L * AdversarialBco.BodySpec.phi (Real.sqrt (2 * AdversarialBco.BodySpec.lnp (26 * d * L / h))) ≤ h / (32 * d) := by
  rcases hL.eq_or_lt with (rfl | hLpos)
  · have hpos : 0 ≤ h / (32 * d) := by positivity
    simpa using hpos
  · set P := AdversarialBco.BodySpec.phi (Real.sqrt (2 * AdversarialBco.BodySpec.lnp (26 * d * L / h))) with hP
    have hypos : 0 < 26 * d * L / h := by positivity
    have hbound := AdversarialBco.Body2.phi_T_le (26 * d * L / h) hypos
    have hkey : L * P ≤ h / (64 * d) := by
      calc
        L * P = ((26 * d * L / h) * P) * (h / (26 * d)) := by
          field_simp
        _ ≤ (26/64) * (h / (26 * d)) := by
          apply mul_le_mul_of_nonneg_right hbound
          positivity
        _ = h / (64 * d) := by ring
    calc
      2 * L * P = 2 * (L * P) := by ring
      _ ≤ 2 * (h / (64 * d)) := by gcongr
      _ = h / (32 * d) := by ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

lemma scale_arith_cauchy_schwarz_two (a b x y : ℝ) : (a*x + b*y)^2 ≤ (a^2 + b^2)*(x^2 + y^2) := by
  have h : (a*y - b*x)^2 ≥ 0 := by positivity
  nlinarith

theorem AdversarialBco.Body2.scale_arith (Λ μg μm h d T VG Vg Vb Vbg Vs : ℝ) (hΛ : Λ ≤ μg + μm) (hμg : 0 ≤ μg) (hμm : 0 ≤ μm) (hh : 0 < h) (hd : 1 ≤ d) (hT : 0 ≤ T) (hVg : 0 ≤ Vg) (hVbg : 0 ≤ Vbg) (hVs : 0 ≤ Vs) (hVgG : Vg ≤ VG) (hVbgb : Vbg ≤ Vb) (hcore : Real.sqrt μg * h ≤ 32 / AdversarialBco.BodySpec.kappa * (1 + T) * d * (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d))) (hmoved : μm * h ^ 2 / 8 ≤ Vb + Vs) : Λ * h ^ 2 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
  rcases AdversarialBco.Body2.kappa_bounds with ⟨hκ_lo, hκ_hi, hκ2_lo, hκ2_hi⟩
  have hκ_pos : 0 < AdversarialBco.BodySpec.kappa := by linarith
  have hκ2_nonneg : 0 ≤ 3 + 2 * AdversarialBco.BodySpec.kappa2 := by nlinarith
  have hsqrt_d_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
  have h_one_T_nonneg : 0 ≤ 1 + T := by linarith
  have h_sq_d_ge_one : 1 ≤ d ^ 2 := by
    nlinarith
  have h_sq_one_T_ge_one : 1 ≤ (1 + T) ^ 2 := by
    nlinarith
  have hKS_nonneg : 0 ≤ AdversarialBco.BodySpec.KS := by
    unfold AdversarialBco.BodySpec.KS
    positivity
  -- prove KS ≥ 16
  have hKS16 : 16 ≤ AdversarialBco.BodySpec.KS := by
    unfold AdversarialBco.BodySpec.KS
    have h_sq_bound : AdversarialBco.BodySpec.kappa ^ 2 ≤ 128 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) := by
      have h1 : AdversarialBco.BodySpec.kappa ^ 2 ≤ ((319/1000 : ℝ)) ^ 2 := by nlinarith
      have h2 : ((319/1000 : ℝ)) ^ 2 ≤ 128 * (13/4 + 2 * (596/1000 : ℝ)) := by norm_num
      have h3 : 128 * (13/4 + 2 * (596/1000 : ℝ)) ≤ 128 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) := by nlinarith
      linarith
    have hpos_sq : 0 < AdversarialBco.BodySpec.kappa ^ 2 := by positivity
    have h_mul : 16 * AdversarialBco.BodySpec.kappa ^ 2 ≤ 2048 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) := by
      nlinarith
    have h_div : 16 ≤ 2048 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) / (AdversarialBco.BodySpec.kappa ^ 2) := by
      field_simp [hpos_sq.ne.symm]
      nlinarith
    have h_eq : 2048 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) / (AdversarialBco.BodySpec.kappa ^ 2) =
      2 * (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) := by
      field_simp [hκ_pos.ne.symm]
      ring
    rw [h_eq] at h_div
    exact h_div
  by_cases hΛ_nonpos : Λ ≤ 0
  · -- Λ ≤ 0: trivial
    have hRHS_nonneg : 0 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
      have h_T_nonneg : 0 ≤ (1 + T) ^ 2 := pow_two_nonneg _
      have h_d_nonneg : 0 ≤ d ^ 2 := pow_two_nonneg _
      have h_sum_nonneg : 0 ≤ VG + Vb + Vs := by linarith
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg hKS_nonneg h_T_nonneg
        · exact h_d_nonneg
      · exact h_sum_nonneg
    nlinarith
  · -- Λ > 0
    have hΛ_pos : 0 < Λ := by linarith
    have h_half : Λ / 2 ≤ μg ∨ Λ / 2 ≤ μm := by
      by_contra! h
      rcases h with ⟨hμg_lt, hμm_lt⟩
      have hsum : μg + μm < Λ := by linarith
      linarith
    rcases h_half with (hμg_half | hμm_half)
    · -- case μg ≥ Λ/2
      have h_mul : Λ * h ^ 2 ≤ 2 * μg * h ^ 2 := by
        nlinarith
      have h_sq_core : μg * h ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2) := by
        have h_nonneg_left : 0 ≤ Real.sqrt μg * h := by positivity
        have h_nonneg_right : 0 ≤ 32 / AdversarialBco.BodySpec.kappa * (1 + T) * d * (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) := by
          positivity
        have h_sq : (Real.sqrt μg * h) ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa * (1 + T) * d * (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d))) ^ 2 := by
          simpa [sq] using mul_le_mul hcore hcore h_nonneg_left h_nonneg_right
        have h_left_sq : (Real.sqrt μg * h) ^ 2 = μg * h ^ 2 := by
          calc
            (Real.sqrt μg * h) ^ 2 = (Real.sqrt μg) ^ 2 * h ^ 2 := by ring
            _ = μg * h ^ 2 := by rw [Real.sq_sqrt hμg]
        have h_right_sq : (32 / AdversarialBco.BodySpec.kappa * (1 + T) * d * (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d))) ^ 2 =
          (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2) := by
          ring
        rw [h_left_sq, h_right_sq] at h_sq
        exact h_sq
      have h_cauchy : (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2 ≤
        ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2)) ^ 2 + (1 / (2 * Real.sqrt d)) ^ 2) * ((Real.sqrt Vg) ^ 2 + (Real.sqrt Vbg) ^ 2) := by
        have := scale_arith_cauchy_schwarz_two (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2)) (1 / (2 * Real.sqrt d)) (Real.sqrt Vg) (Real.sqrt Vbg)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      have h_sq_sqrt_Vg : (Real.sqrt Vg) ^ 2 = Vg := Real.sq_sqrt hVg
      have h_sq_sqrt_Vbg : (Real.sqrt Vbg) ^ 2 = Vbg := Real.sq_sqrt hVbg
      have h_sq_sqrt_kappa2 : (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2)) ^ 2 = 3 + 2 * AdversarialBco.BodySpec.kappa2 :=
        Real.sq_sqrt hκ2_nonneg
      have h_bound_d : (1 / (2 * Real.sqrt d)) ^ 2 ≤ (1/4 : ℝ) := by
        have h_sqrt_d_ge_one : 1 ≤ Real.sqrt d := by
          calc
            1 = Real.sqrt 1 := by norm_num
            _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
        have hpos1 : 0 < 2 * Real.sqrt d := by positivity
        have hpos2 : 0 < (2 : ℝ) := by norm_num
        have h : 1 / (2 * Real.sqrt d) ≤ 1/2 := by
          apply (one_div_le_one_div hpos1 hpos2).mpr
          linarith
        have h_sq : (1 / (2 * Real.sqrt d)) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
          have h_nonneg : 0 ≤ 1 / (2 * Real.sqrt d) := by positivity
          have h_half_nonneg : 0 ≤ (1/2 : ℝ) := by norm_num
          calc
            (1 / (2 * Real.sqrt d)) ^ 2 = (1 / (2 * Real.sqrt d)) * (1 / (2 * Real.sqrt d)) := by ring
            _ ≤ (1/2 : ℝ) * (1/2 : ℝ) := mul_le_mul h h h_nonneg h_half_nonneg
            _ = (1/2 : ℝ) ^ 2 := by ring
        have h_half_sq : (1/2 : ℝ) ^ 2 = (1/4 : ℝ) := by norm_num
        rw [h_half_sq] at h_sq
        exact h_sq
      have h_cauchy_simplified : (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2 ≤
        (13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb) := by
        have h_mul_bound : ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2)) ^ 2 + (1 / (2 * Real.sqrt d)) ^ 2) * ((Real.sqrt Vg) ^ 2 + (Real.sqrt Vbg) ^ 2) ≤
          (13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb) := by
          have h_left : (Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2)) ^ 2 + (1 / (2 * Real.sqrt d)) ^ 2 ≤ 13/4 + 2 * AdversarialBco.BodySpec.kappa2 := by
            rw [h_sq_sqrt_kappa2]
            have h_temp : (3 + 2 * AdversarialBco.BodySpec.kappa2) + (1 / (2 * Real.sqrt d)) ^ 2 ≤ (3 + 2 * AdversarialBco.BodySpec.kappa2) + (1/4 : ℝ) := by
              linarith
            have h_eq : (3 + 2 * AdversarialBco.BodySpec.kappa2) + (1/4 : ℝ) = 13/4 + 2 * AdversarialBco.BodySpec.kappa2 := by ring
            rw [h_eq] at h_temp
            exact h_temp
          have h_right : (Real.sqrt Vg) ^ 2 + (Real.sqrt Vbg) ^ 2 ≤ VG + Vb := by
            rw [h_sq_sqrt_Vg, h_sq_sqrt_Vbg]
            have h_sum : Vg + Vbg ≤ VG + Vb := by linarith
            exact h_sum
          have h_nonneg_left' : 0 ≤ 13/4 + 2 * AdversarialBco.BodySpec.kappa2 := by positivity
          have h_nonneg_right : 0 ≤ (Real.sqrt Vg) ^ 2 + (Real.sqrt Vbg) ^ 2 := by positivity
          exact mul_le_mul h_left h_right h_nonneg_right h_nonneg_left'
        linarith
      have h_main : μg * h ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb)) := by
        have h_nonneg_B : 0 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 := by positivity
        have h_intermediate : μg * h ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2) := h_sq_core
        have h_mul : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((Real.sqrt (3 + 2 * AdversarialBco.BodySpec.kappa2) * Real.sqrt Vg + Real.sqrt Vbg / (2 * Real.sqrt d)) ^ 2) ≤
          (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb)) :=
          mul_le_mul_of_nonneg_left h_cauchy_simplified h_nonneg_B
        exact le_trans h_intermediate h_mul
      have h_KS_expr : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2) = AdversarialBco.BodySpec.KS / 2 := by
        unfold AdversarialBco.BodySpec.KS
        field_simp [hκ_pos.ne.symm]
      have h_final : 2 * μg * h ^ 2 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
        have h_T_nonneg : 0 ≤ (1 + T) ^ 2 := pow_two_nonneg _
        have h_d_nonneg : 0 ≤ d ^ 2 := pow_two_nonneg _
        have h_sum_nonneg : 0 ≤ VG + Vb + Vs := by linarith
        have h_factor : 2 * μg * h ^ 2 ≤ 2 * ((32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb))) := by
          linarith
        have h_eq2 : 2 * ((32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb))) =
          (AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2) * (VG + Vb) := by
          calc
            2 * ((32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * ((13/4 + 2 * AdversarialBco.BodySpec.kappa2) * (VG + Vb))) =
              2 * ((32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13/4 + 2 * AdversarialBco.BodySpec.kappa2)) * (1 + T) ^ 2 * d ^ 2 * (VG + Vb) := by ring
            _ = 2 * (AdversarialBco.BodySpec.KS / 2) * (1 + T) ^ 2 * d ^ 2 * (VG + Vb) := by rw [h_KS_expr]
            _ = (AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2) * (VG + Vb) := by ring
        rw [h_eq2] at h_factor
        have h_final2 : (AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2) * (VG + Vb) ≤
          AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
          have h_prod_nonneg : 0 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 := by
            positivity
          have h_Vb_le : VG + Vb ≤ VG + Vb + Vs := by linarith
          exact mul_le_mul_of_nonneg_left h_Vb_le h_prod_nonneg
        linarith
      linarith
    · -- case μm ≥ Λ/2
      have h_mul : Λ * h ^ 2 ≤ 2 * μm * h ^ 2 := by
        have h_ineq : Λ ≤ 2 * μm := by linarith
        have h_sq_nonneg : 0 ≤ h ^ 2 := pow_two_nonneg _
        exact mul_le_mul_of_nonneg_right h_ineq h_sq_nonneg
      have h_moved' : 2 * μm * h ^ 2 ≤ 16 * (Vb + Vs) := by
        have : μm * h ^ 2 ≤ 8 * (Vb + Vs) := by linarith
        linarith
      have h_Vb_Vs_le : Vb + Vs ≤ VG + Vb + Vs := by
        have hVG_nonneg : 0 ≤ VG := by linarith
        linarith
      have h_final : 16 * (Vb + Vs) ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
        have h_prod : 16 * (Vb + Vs) ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (Vb + Vs) := by
          have h_nonneg : 0 ≤ Vb + Vs := by linarith
          have h_factor : 16 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 := by
            have h_T_nonneg : 0 ≤ (1 + T) ^ 2 := pow_two_nonneg _
            have h_d_nonneg : 0 ≤ d ^ 2 := pow_two_nonneg _
            have h1 : 16 * 1 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 :=
              mul_le_mul hKS16 h_sq_one_T_ge_one (by positivity) (by linarith)
            have h2 : (16 * 1) * 1 ≤ (AdversarialBco.BodySpec.KS * (1 + T) ^ 2) * d ^ 2 :=
              mul_le_mul h1 h_sq_d_ge_one (by norm_num) (by
                have : 0 ≤ AdversarialBco.BodySpec.KS := hKS_nonneg
                have : 0 ≤ (1 + T) ^ 2 := h_T_nonneg
                positivity)
            simpa [mul_assoc] using h2
          exact mul_le_mul_of_nonneg_right h_factor h_nonneg
        have h_le : AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (Vb + Vs) ≤
          AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
          have h_factor_nonneg : 0 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 := by
            positivity
          exact mul_le_mul_of_nonneg_left h_Vb_Vs_le h_factor_nonneg
        linarith
      have h_intermediate : Λ * h ^ 2 ≤ 16 * (Vb + Vs) := by
        linarith
      linarith
end
