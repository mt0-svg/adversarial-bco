/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBody

@[expose] public section

/-! Gaussian constants: the density, the tail, Mills ratio bounds, kappa, kappa2, K_S, C_0. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_phi_Ioi_zero : ∫ s in Set.Ioi (0 : ℝ), AdversarialBco.BodySpec.phi s = 1 / 2 := by
  unfold AdversarialBco.BodySpec.phi
  have h := integral_gaussian_Ioi (1/2 : ℝ)
  have hnum : (∫ s in Set.Ioi (0 : ℝ), Real.exp (-((1/2 : ℝ) * s ^ 2))) = Real.sqrt (Real.pi / (1/2 : ℝ)) / 2 := by
    simpa [neg_mul] using h
  have h_simplify : Real.sqrt (Real.pi / (1/2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    have hpos : Real.pi > 0 := Real.pi_pos
    field_simp [hpos.ne.symm]
  calc
    ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi))
        = (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
      rw [MeasureTheory.integral_div]
    _ = (∫ s in Set.Ioi (0 : ℝ), Real.exp (-((1/2 : ℝ) * s ^ 2))) / Real.sqrt (2 * Real.pi) := by
      refine congrArg (· / Real.sqrt (2 * Real.pi)) ?_
      refine integral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      ring_nf
    _ = (Real.sqrt (Real.pi / (1/2 : ℝ)) / 2) / Real.sqrt (2 * Real.pi) := by
      rw [hnum]
    _ = (Real.sqrt (2 * Real.pi) / 2) / Real.sqrt (2 * Real.pi) := by
      rw [h_simplify]
    _ = 1/2 := by
      have hsqrtpos : Real.sqrt (2 * Real.pi) > 0 := Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
      field_simp [hsqrtpos.ne']
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_phi : ∫ s, AdversarialBco.BodySpec.phi s = 1 := by
  unfold AdversarialBco.BodySpec.phi
  calc
    ∫ s, Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi)
        = (∫ s, Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
      rw [MeasureTheory.integral_div]
    _ = (∫ s, Real.exp (-((1 : ℝ) / 2) * s ^ 2)) / Real.sqrt (2 * Real.pi) := by
      refine congrArg (· / Real.sqrt (2 * Real.pi)) ?_
      refine integral_congr_ae ?_
      filter_upwards with s
      field_simp
    _ = (Real.sqrt (Real.pi / ((1 : ℝ) / 2))) / Real.sqrt (2 * Real.pi) := by
      rw [integral_gaussian (1 / 2)]
    _ = 1 := by
      field_simp
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Qtail_eq_sub (T : ℝ) : AdversarialBco.BodySpec.Qtail T = 1 / 2 - ∫ s in (0 : ℝ)..T, AdversarialBco.BodySpec.phi s := by
  have h_int_gaussian : ∫ s in Set.Ioi (0 : ℝ), AdversarialBco.BodySpec.phi s = 1/2 := by
    have hpos : Real.sqrt (2 * Real.pi) > 0 := Real.sqrt_pos.mpr (by
      have : (0 : ℝ) < Real.pi := Real.pi_pos
      nlinarith)
    have h_eq_exp : (fun s : ℝ => Real.exp (-(s ^ 2) / 2)) = (fun s : ℝ => Real.exp (-((1/2 : ℝ)) * s ^ 2)) := by
      ext s : 1
      ring
    calc
      ∫ s in Set.Ioi (0 : ℝ), AdversarialBco.BodySpec.phi s
          = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi)) := rfl
      _ = (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
        rw [integral_div]
      _ = (∫ s in Set.Ioi (0 : ℝ), Real.exp (-((1/2 : ℝ)) * s ^ 2)) / Real.sqrt (2 * Real.pi) := by
        rw [h_eq_exp]
      _ = (Real.sqrt (Real.pi / (1/2 : ℝ)) / 2) / Real.sqrt (2 * Real.pi) := by
        rw [integral_gaussian_Ioi (1/2)]
      _ = 1/2 := by
        field_simp [hpos.ne.symm]
  have h_int_all : Integrable (fun s : ℝ => Real.exp (-(s ^ 2) / 2)) volume := by
    have h := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num : (0 : ℝ) < (1/2 : ℝ))
    -- h : Integrable (fun x => Real.exp (-(1/2) * x ^ 2)) volume
    -- need: Integrable (fun s => Real.exp (-(s ^ 2) / 2)) volume
    have h_eq : (fun s : ℝ => Real.exp (-(s ^ 2) / 2)) = (fun s : ℝ => Real.exp (-((1/2 : ℝ)) * s ^ 2)) := by
      ext s : 1
      ring
    rw [h_eq]
    exact h
  have h_int_phi : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi (0 : ℝ)) volume := by
    have h_phi_eq : AdversarialBco.BodySpec.phi = fun s => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(s ^ 2) / 2) := by
      ext s
      dsimp [AdversarialBco.BodySpec.phi]
      ring
    rw [h_phi_eq]
    exact (h_int_all.integrableOn.const_mul _)
  have h_int_phi_T : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi T) volume := by
    have h_phi_eq : AdversarialBco.BodySpec.phi = fun s => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(s ^ 2) / 2) := by
      ext s
      dsimp [AdversarialBco.BodySpec.phi]
      ring
    rw [h_phi_eq]
    exact (h_int_all.integrableOn.const_mul _)
  have h_split : (∫ s in (0 : ℝ)..T, AdversarialBco.BodySpec.phi s) + AdversarialBco.BodySpec.Qtail T = ∫ s in Set.Ioi (0 : ℝ), AdversarialBco.BodySpec.phi s := by
    dsimp [AdversarialBco.BodySpec.Qtail]
    have h := intervalIntegral.integral_interval_add_Ioi h_int_phi h_int_phi_T
    simpa [add_comm] using h
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.hasDerivAt_Qtail (T : ℝ) : HasDerivAt AdversarialBco.BodySpec.Qtail (-AdversarialBco.BodySpec.phi T) T := by
  set φ := AdversarialBco.BodySpec.phi
  have hφ_cont : Continuous φ := by
    unfold φ AdversarialBco.BodySpec.phi
    fun_prop
  have hφ_contAt : ContinuousAt φ T := hφ_cont.continuousAt
  have hφ_int : IntervalIntegrable φ volume 0 T :=
    hφ_cont.intervalIntegrable 0 T
  have hφ_strong : StronglyMeasurableAtFilter φ (nhds T) volume :=
    hφ_cont.stronglyMeasurableAtFilter volume (nhds T)
  -- integrability of φ on Ioi for any point
  have hφ_intOn_Ioi (t : ℝ) : IntegrableOn φ (Set.Ioi t) volume := by
    have h_int : Integrable φ volume := by
      have h_eq : φ = ProbabilityTheory.gaussianPDFReal 0 1 := by
        ext x
        simp [φ, AdversarialBco.BodySpec.phi, ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_one,
          mul_comm, mul_left_comm, div_eq_mul_inv]
      rw [h_eq]
      exact ProbabilityTheory.integrable_gaussianPDFReal 0 1
    exact h_int.integrableOn
  have hφ_intOn_Ioi0 : IntegrableOn φ (Set.Ioi (0 : ℝ)) volume := hφ_intOn_Ioi 0
  -- key identity: Qtail = const - integral from 0 to t
  have hQtail_eq : AdversarialBco.BodySpec.Qtail = fun (t : ℝ) =>
      (∫ s in Set.Ioi (0 : ℝ), φ s) - (∫ s in (0 : ℝ)..t, φ s) := by
    ext t
    dsimp [AdversarialBco.BodySpec.Qtail]
    have h := intervalIntegral.integral_interval_add_Ioi (hφ_intOn_Ioi 0) (hφ_intOn_Ioi t)
    linarith [h]
  rw [hQtail_eq]
  have h_const : HasDerivAt (fun _ : ℝ => ∫ s in Set.Ioi (0 : ℝ), φ s) 0 T :=
    hasDerivAt_const T _
  have h_ftc : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, φ s) (φ T) T :=
    intervalIntegral.integral_hasDerivAt_right hφ_int hφ_strong hφ_contAt
  have h_sub : HasDerivAt (fun u : ℝ => (∫ s in Set.Ioi (0 : ℝ), φ s) - (∫ s in (0 : ℝ)..u, φ s))
      (0 - φ T) T :=
    HasDerivAt.sub h_const h_ftc
  simpa [sub_zero] using h_sub
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open Set
open intervalIntegral

lemma integral_exp_bounds_exp_neg_upper_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : Real.exp (-x) ≤ 1 - x + x^2/2 := by
  have hsum : Summable fun n : ℕ => x ^ n / (n.factorial : ℝ) := by
    simpa using Real.summable_pow_div_factorial x
  have h_anti : Antitone fun n : ℕ => x ^ n / (n.factorial : ℝ) := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hx_le_np1 : x ≤ (n : ℝ) + 1 := by
      have hx1' : x ≤ (1 : ℝ) := by linarith
      have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith
      nlinarith
    have hpos_fact : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpos_np1 : (n : ℝ) + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hpos_np1' : 0 < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_nonneg_div : 0 ≤ x ^ n / (n.factorial : ℝ) :=
      div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
    calc
      x ^ (n+1) / ((n+1).factorial : ℝ) = (x ^ n * x) / (((n.factorial : ℝ) * ((n:ℝ)+1))) := by
        simp [pow_succ, Nat.factorial_succ, mul_comm]
      _ = (x ^ n / (n.factorial : ℝ)) * (x / ((n:ℝ)+1)) := by
        field_simp [hpos_fact, hpos_np1]
      _ ≤ (x ^ n / (n.factorial : ℝ)) * 1 := by
        apply mul_le_mul_of_nonneg_left ?_ h_nonneg_div
        exact (div_le_one hpos_np1').mpr hx_le_np1
      _ = x ^ n / (n.factorial : ℝ) := by simp
  have h_exp_tsum : Real.exp (-x) = ∑' n : ℕ, ((-1 : ℝ) ^ n * (x ^ n / (n.factorial : ℝ))) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
    refine tsum_congr (fun n => ?_)
    simp [div_eq_mul_inv, smul_eq_mul]
    have h_pow : (-x) ^ n = (-1 : ℝ) ^ n * x ^ n := by
      induction' n with k ih
      · simp
      · simp [pow_succ, mul_assoc, ih]
    calc
      ((n.factorial : ℝ)⁻¹) * (-x) ^ n = ((n.factorial : ℝ)⁻¹) * ((-1 : ℝ) ^ n * x ^ n) := by rw [h_pow]
      _ = (-1 : ℝ) ^ n * (x ^ n * ((n.factorial : ℝ)⁻¹)) := by ring
  have h_bound := alternating_series_error_bound (fun n : ℕ => x ^ n / (n.factorial : ℝ)) h_anti hsum 2
  have h_sum_range : (∑ i ∈ Finset.range 2, ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ)))) = 1 - x := by
    simp [Finset.sum_range_succ]
    ring
  have h_f2 : x ^ 2 / ((2 : ℕ).factorial : ℝ) = x^2/2 := by norm_num
  rw [← h_exp_tsum, h_sum_range, h_f2] at h_bound
  have h_abs := abs_le.mp h_bound
  rcases h_abs with ⟨h_low, h_high⟩
  linarith

lemma integral_exp_bounds_exp_neg_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 1 - x + x^2/2 - x^3/6 ≤ Real.exp (-x) := by
  have hsum : Summable fun n : ℕ => x ^ n / (n.factorial : ℝ) := by
    simpa using Real.summable_pow_div_factorial x
  have h_anti : Antitone fun n : ℕ => x ^ n / (n.factorial : ℝ) := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hx_le_np1 : x ≤ (n : ℝ) + 1 := by
      have hx1' : x ≤ (1 : ℝ) := by linarith
      have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith
      nlinarith
    have hpos_fact : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpos_np1 : (n : ℝ) + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hpos_np1' : 0 < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_nonneg_div : 0 ≤ x ^ n / (n.factorial : ℝ) :=
      div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
    calc
      x ^ (n+1) / ((n+1).factorial : ℝ) = (x ^ n * x) / (((n.factorial : ℝ) * ((n:ℝ)+1))) := by
        simp [pow_succ, Nat.factorial_succ, mul_comm]
      _ = (x ^ n / (n.factorial : ℝ)) * (x / ((n:ℝ)+1)) := by
        field_simp [hpos_fact, hpos_np1]
      _ ≤ (x ^ n / (n.factorial : ℝ)) * 1 := by
        apply mul_le_mul_of_nonneg_left ?_ h_nonneg_div
        exact (div_le_one hpos_np1').mpr hx_le_np1
      _ = x ^ n / (n.factorial : ℝ) := by simp
  have h_exp_tsum : Real.exp (-x) = ∑' n : ℕ, ((-1 : ℝ) ^ n * (x ^ n / (n.factorial : ℝ))) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
    refine tsum_congr (fun n => ?_)
    simp [div_eq_mul_inv, smul_eq_mul]
    have h_pow : (-x) ^ n = (-1 : ℝ) ^ n * x ^ n := by
      induction' n with k ih
      · simp
      · simp [pow_succ, mul_assoc, ih]
    calc
      ((n.factorial : ℝ)⁻¹) * (-x) ^ n = ((n.factorial : ℝ)⁻¹) * ((-1 : ℝ) ^ n * x ^ n) := by rw [h_pow]
      _ = (-1 : ℝ) ^ n * (x ^ n * ((n.factorial : ℝ)⁻¹)) := by ring
  have h_bound := alternating_series_error_bound (fun n : ℕ => x ^ n / (n.factorial : ℝ)) h_anti hsum 3
  have h_sum_range : (∑ i ∈ Finset.range 3, ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ)))) = 1 - x + x^2/2 := by
    simp [Finset.sum_range_succ]
    ring
  have h_f3 : x ^ 3 / ((3 : ℕ).factorial : ℝ) = x^3/6 := by norm_num
  rw [← h_exp_tsum, h_sum_range, h_f3] at h_bound
  have h_abs := abs_le.mp h_bound
  rcases h_abs with ⟨h_low, h_high⟩
  linarith

theorem AdversarialBco.Body2.integral_exp_bounds : (85 / 100 : ℝ) ≤ ∫ t in (0 : ℝ)..1, Real.exp (-(t ^ 2) / 2) ∧ ∫ t in (0 : ℝ)..1, Real.exp (-(t ^ 2) / 2) ≤ 86 / 100 := by
  let I := ∫ t in (0 : ℝ)..1, Real.exp (-(t ^ 2) / 2)
  -- For t ∈ [0,1], we have t^2/2 ∈ [0, 1/2]
  have h_bound_poly_lower (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 - (t ^ 2 / 2) + (t ^ 2 / 2) ^ 2 / 2 - (t ^ 2 / 2) ^ 3 / 6 ≤ Real.exp (-(t ^ 2) / 2) := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hx0 : 0 ≤ t ^ 2 / 2 := div_nonneg (pow_two_nonneg t) (by norm_num)
    have hx1 : t ^ 2 / 2 ≤ 1/2 := by
      have : t ^ 2 ≤ 1 := by
        nlinarith
      nlinarith
    have h := integral_exp_bounds_exp_neg_lower_bound hx0 hx1
    -- h: 1 - (t^2/2) + (t^2/2)^2/2 - (t^2/2)^3/6 ≤ Real.exp (-(t^2/2))
    -- We need: ... ≤ Real.exp (-(t^2)/2)
    -- Note: -(t^2/2) = -(t^2)/2 by ring
    simpa [show (-(t ^ 2 / 2) : ℝ) = (-(t ^ 2) / 2) by ring] using h
  have h_bound_poly_upper (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Real.exp (-(t ^ 2) / 2) ≤ 1 - (t ^ 2 / 2) + (t ^ 2 / 2) ^ 2 / 2 := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hx0 : 0 ≤ t ^ 2 / 2 := div_nonneg (pow_two_nonneg t) (by norm_num)
    have hx1 : t ^ 2 / 2 ≤ 1/2 := by
      have : t ^ 2 ≤ 1 := by
        nlinarith
      nlinarith
    have h := integral_exp_bounds_exp_neg_upper_bound hx0 hx1
    -- h: Real.exp (-(t^2/2)) ≤ 1 - (t^2/2) + (t^2/2)^2/2
    -- We need: Real.exp (-(t^2)/2) ≤ ...
    simpa [show (-(t ^ 2 / 2) : ℝ) = (-(t ^ 2) / 2) by ring] using h
  -- Simplify the polynomial bounds
  have h_poly_lower (t : ℝ) : 1 - (t ^ 2 / 2) + (t ^ 2 / 2) ^ 2 / 2 - (t ^ 2 / 2) ^ 3 / 6 = 1 - t^2/2 + t^4/8 - t^6/48 := by
    ring
  have h_poly_upper (t : ℝ) : 1 - (t ^ 2 / 2) + (t ^ 2 / 2) ^ 2 / 2 = 1 - t^2/2 + t^4/8 := by
    ring
  -- Now integrate the bounds
  have h_int_lower : ∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8 - t^6/48) ≤ I := by
    have h_int_poly : IntervalIntegrable (fun t => 1 - t^2/2 + t^4/8 - t^6/48) volume 0 1 := by
      -- (1 - t^2/2 + t^4/8) - t^6/48
      refine IntervalIntegrable.sub ?_ ?_
      · -- 1 - t^2/2 + t^4/8 = (1 - t^2/2) + t^4/8
        refine IntervalIntegrable.add ?_ ?_
        · -- 1 - t^2/2 = 1 + (-t^2/2)
          refine IntervalIntegrable.add intervalIntegrable_const ?_
          have : (fun t : ℝ => -(t ^ 2 / 2)) = (fun t => (-1/2) * t ^ 2) := by ext t; ring
          rw [this]
          exact IntervalIntegrable.const_mul (intervalIntegrable_pow 2) (-1/2)
        · have : (fun t : ℝ => t ^ 4 / 8) = (fun t => (1/8) * t ^ 4) := by ext t; ring
          rw [this]
          exact IntervalIntegrable.const_mul (intervalIntegrable_pow 4) (1/8)
      · have : (fun t : ℝ => t ^ 6 / 48) = (fun t => (1/48) * t ^ 6) := by ext t; ring
        rw [this]
        exact IntervalIntegrable.const_mul (intervalIntegrable_pow 6) (1/48)
    have h_int_exp : IntervalIntegrable (fun t => Real.exp (-(t ^ 2) / 2)) volume 0 1 := by
      apply Continuous.intervalIntegrable (μ := volume)
      continuity
    have h_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t^2/2 + t^4/8 - t^6/48) ≤ Real.exp (-(t ^ 2) / 2) := by
      intro t ht
      have := h_bound_poly_lower t ht
      simpa [h_poly_lower t] using this
    exact intervalIntegral.integral_mono_on (by norm_num) h_int_poly h_int_exp h_bound
  have h_int_upper : I ≤ ∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8) := by
    have h_int_poly : IntervalIntegrable (fun t => 1 - t^2/2 + t^4/8) volume 0 1 := by
      -- 1 - t^2/2 + t^4/8 = (1 - t^2/2) + t^4/8
      refine IntervalIntegrable.add ?_ ?_
      · -- 1 - t^2/2
        refine IntervalIntegrable.add intervalIntegrable_const ?_
        have : (fun t : ℝ => -(t ^ 2 / 2)) = (fun t => (-1/2) * t ^ 2) := by ext t; ring
        rw [this]
        exact IntervalIntegrable.const_mul (intervalIntegrable_pow 2) (-1/2)
      · have : (fun t : ℝ => t ^ 4 / 8) = (fun t => (1/8) * t ^ 4) := by ext t; ring
        rw [this]
        exact IntervalIntegrable.const_mul (intervalIntegrable_pow 4) (1/8)
    have h_int_exp : IntervalIntegrable (fun t => Real.exp (-(t ^ 2) / 2)) volume 0 1 := by
      apply Continuous.intervalIntegrable (μ := volume)
      continuity
    have h_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(t ^ 2) / 2) ≤ (1 - t^2/2 + t^4/8) := by
      intro t ht
      have := h_bound_poly_upper t ht
      simpa [h_poly_upper t] using this
    exact intervalIntegral.integral_mono_on (by norm_num) h_int_exp h_int_poly h_bound
  -- Compute the polynomial integrals
  have h_int_lower_val : ∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8 - t^6/48) = 1437/1680 := by
    have h_pow2 : ∫ t in (0 : ℝ)..1, t^2 = 1/3 := by rw [integral_pow 2]; norm_num
    have h_pow4 : ∫ t in (0 : ℝ)..1, t^4 = 1/5 := by rw [integral_pow 4]; norm_num
    have h_pow6 : ∫ t in (0 : ℝ)..1, t^6 = 1/7 := by rw [integral_pow 6]; norm_num
    have hc1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have hc2 : IntervalIntegrable (fun t : ℝ => t^2) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have hc3 : IntervalIntegrable (fun t : ℝ => t^4) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have hc4 : IntervalIntegrable (fun t : ℝ => t^6) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have h_eq_integrand : (fun t : ℝ => 1 - t^2/2 + t^4/8 - t^6/48) = (fun t => ((1 - t^2/2 + t^4/8) - t^6/48)) := by
      ext t; ring
    rw [h_eq_integrand]
    have h_sub1 : ∫ t in (0 : ℝ)..1, ((1 - t^2/2 + t^4/8) - t^6/48) =
        (∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8)) - (∫ t in (0 : ℝ)..1, t^6/48) := by
      rw [integral_sub (by
        have : IntervalIntegrable (fun t : ℝ => 1 - t^2/2) MeasureTheory.volume 0 1 :=
          hc1.sub (hc2.div_const 2)
        exact this.add (hc3.div_const 8)
      ) (hc4.div_const 48)]
    rw [h_sub1]
    have h_add1 : ∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8) =
        (∫ t in (0 : ℝ)..1, (1 - t^2/2)) + (∫ t in (0 : ℝ)..1, t^4/8) := by
      rw [integral_add (hc1.sub (hc2.div_const 2)) (hc3.div_const 8)]
    rw [h_add1]
    have h_sub2 : ∫ t in (0 : ℝ)..1, (1 - t^2/2) = (∫ t in (0 : ℝ)..1, (1 : ℝ)) - (∫ t in (0 : ℝ)..1, t^2/2) := by
      rw [integral_sub hc1 (hc2.div_const 2)]
    rw [h_sub2]
    have h_simp : (∫ t in (0 : ℝ)..1, (1 : ℝ)) - (∫ t in (0 : ℝ)..1, t^2/2) + (∫ t in (0 : ℝ)..1, t^4/8) - (∫ t in (0 : ℝ)..1, t^6/48) =
        (1 : ℝ) - ((1/3) / 2) + ((1/5) / 8) - ((1/7) / 48) := by
      simp [intervalIntegral.integral_div, intervalIntegral.integral_const, h_pow2, h_pow4, h_pow6]
    rw [h_simp]
    norm_num
  have h_int_upper_val : ∫ t in (0 : ℝ)..1, (1 - t^2/2 + t^4/8) = 103/120 := by
    have h_pow2 : ∫ t in (0 : ℝ)..1, t^2 = 1/3 := by rw [integral_pow 2]; norm_num
    have h_pow4 : ∫ t in (0 : ℝ)..1, t^4 = 1/5 := by rw [integral_pow 4]; norm_num
    have hc1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have hc2 : IntervalIntegrable (fun t : ℝ => t^2) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have hc3 : IntervalIntegrable (fun t : ℝ => t^4) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by continuity) _ _
    have h_eq_integrand : (fun t : ℝ => 1 - t^2/2 + t^4/8) = (fun t => ((1 - t^2/2) + t^4/8)) := by
      ext t; ring
    rw [h_eq_integrand]
    have h_add1 : ∫ t in (0 : ℝ)..1, ((1 - t^2/2) + t^4/8) =
        (∫ t in (0 : ℝ)..1, (1 - t^2/2)) + (∫ t in (0 : ℝ)..1, t^4/8) := by
      rw [integral_add (hc1.sub (hc2.div_const 2)) (hc3.div_const 8)]
    rw [h_add1]
    have h_sub1 : ∫ t in (0 : ℝ)..1, (1 - t^2/2) = (∫ t in (0 : ℝ)..1, (1 : ℝ)) - (∫ t in (0 : ℝ)..1, t^2/2) := by
      rw [integral_sub hc1 (hc2.div_const 2)]
    rw [h_sub1]
    have h_simp : (∫ t in (0 : ℝ)..1, (1 : ℝ)) - (∫ t in (0 : ℝ)..1, t^2/2) + (∫ t in (0 : ℝ)..1, t^4/8) =
        (1 : ℝ) - ((1/3) / 2) + ((1/5) / 8) := by
      simp [intervalIntegral.integral_div, intervalIntegral.integral_const, h_pow2, h_pow4]
    rw [h_simp]
    norm_num
  -- Compare with 0.85 and 0.86
  have h_lower : (85/100 : ℝ) ≤ 1437/1680 := by norm_num
  have h_upper : 103/120 ≤ (86/100 : ℝ) := by norm_num
  rw [h_int_lower_val] at h_int_lower
  rw [h_int_upper_val] at h_int_upper
  have h_left : (85/100 : ℝ) ≤ I := by linarith
  have h_right : I ≤ (86/100 : ℝ) := by linarith
  exact And.intro h_left h_right
end


section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.sqrt_two_pi_bounds : (2506 / 1000 : ℝ) ≤ Real.sqrt (2 * Real.pi) ∧ Real.sqrt (2 * Real.pi) ≤ 2507 / 1000 := by
  have h_lower : (2506 / 1000 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have h_sq : ((2506 : ℝ) / 1000) ^ 2 ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_d4]
    have h_nonneg : 0 ≤ (2506 : ℝ) / 1000 := by norm_num
    calc
      (2506 / 1000 : ℝ) = Real.sqrt (((2506 : ℝ) / 1000) ^ 2) := by
        rw [Real.sqrt_sq h_nonneg]
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt h_sq
  have h_upper : Real.sqrt (2 * Real.pi) ≤ (2507 : ℝ) / 1000 := by
    have h_sq : 2 * Real.pi ≤ ((2507 : ℝ) / 1000) ^ 2 := by
      nlinarith [Real.pi_lt_d4]
    have h_nonneg : 0 ≤ (2507 : ℝ) / 1000 := by norm_num
    calc
      Real.sqrt (2 * Real.pi) ≤ Real.sqrt (((2507 : ℝ) / 1000) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = (2507 : ℝ) / 1000 := by rw [Real.sqrt_sq h_nonneg]
  exact And.intro h_lower h_upper
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.exp_neg_half_bounds : (606 / 1000 : ℝ) ≤ Real.exp (-(1 / 2)) ∧ Real.exp (-(1 / 2)) ≤ 607 / 1000 := by
  have hx : |-(1 / 2 : ℝ)| ≤ 1 := by norm_num
  have hn : 0 < 6 := by norm_num
  have hbound := Real.exp_bound hx hn
  have hsum : (∑ m ∈ Finset.range 6, (-(1 / 2 : ℝ)) ^ m / (m.factorial : ℝ)) = (2329 / 3840 : ℝ) := by
    norm_num
  rw [hsum] at hbound
  norm_num at hbound
  have hlow : (606 / 1000 : ℝ) ≤ (2329 / 3840 : ℝ) - (7 / 276480 : ℝ) := by norm_num
  have hhigh : (2329 / 3840 : ℝ) + (7 / 276480 : ℝ) ≤ (607 / 1000 : ℝ) := by norm_num
  rcases (abs_sub_le_iff.mp hbound) with ⟨h1, h2⟩
  have hleft : (606 / 1000 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    linarith
  have hright : Real.exp (-(1 / 2)) ≤ (607 / 1000 : ℝ) := by
    linarith
  exact And.intro hleft hright
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.Qtail_one_bounds : (156 / 1000 : ℝ) ≤ AdversarialBco.BodySpec.Qtail 1 ∧ AdversarialBco.BodySpec.Qtail 1 ≤ 161 / 1000 := by
  have hQ := AdversarialBco.Body2.Qtail_eq_sub 1
  rw [hQ]
  have hE := AdversarialBco.Body2.integral_exp_bounds
  rcases hE with ⟨hE_low, hE_high⟩
  have hS := AdversarialBco.Body2.sqrt_two_pi_bounds
  rcases hS with ⟨hS_low, hS_high⟩
  have hS_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
  have h_int_phi_eq : ∫ s in (0 : ℝ)..(1 : ℝ), AdversarialBco.BodySpec.phi s =
      (∫ s in (0 : ℝ)..(1 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
    unfold AdversarialBco.BodySpec.phi
    rw [intervalIntegral.integral_div]
  rw [h_int_phi_eq]
  have h_low : (156 / 1000 : ℝ) ≤ 1/2 - (∫ s in (0 : ℝ)..(1 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
    have h_div_le : (∫ s in (0 : ℝ)..(1 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) ≤ 344 / 1000 := by
      apply (div_le_iff₀ hS_pos).mpr
      apply le_trans hE_high
      nlinarith
    nlinarith
  have h_high : 1/2 - (∫ s in (0 : ℝ)..(1 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) ≤ 161 / 1000 := by
    have h_div_ge : 339 / 1000 ≤ (∫ s in (0 : ℝ)..(1 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
      apply (le_div_iff₀ hS_pos).mpr
      apply le_trans ?_ hE_low
      nlinarith
    nlinarith
  exact And.intro h_low h_high
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.kappa_bounds : (312 / 1000 : ℝ) ≤ AdversarialBco.BodySpec.kappa ∧ AdversarialBco.BodySpec.kappa ≤ 319 / 1000 ∧ (596 / 1000 : ℝ) ≤ AdversarialBco.BodySpec.kappa2 ∧ AdversarialBco.BodySpec.kappa2 ≤ 603 / 1000 := by
  rcases AdversarialBco.Body2.Qtail_one_bounds with ⟨hQl, hQu⟩
  rcases AdversarialBco.Body2.sqrt_two_pi_bounds with ⟨hSl, hSu⟩
  rcases AdversarialBco.Body2.exp_neg_half_bounds with ⟨he, eu⟩
  have hpos_sqrt : 0 < Real.sqrt (2 * Real.pi) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hphi0_lower : (1000 / 2507 : ℝ) ≤ AdversarialBco.BodySpec.phi 0 := by
    rw [AdversarialBco.BodySpec.phi]
    have hpos_denom : (0 : ℝ) < 2507/1000 := by norm_num
    calc
      (1000 / 2507 : ℝ) = 1 / (2507/1000) := by norm_num
      _ ≤ 1 / Real.sqrt (2 * Real.pi) := by
        refine (one_div_le_one_div ?_ hpos_sqrt).mpr hSu
        norm_num
      _ = Real.exp (-(0 ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by simp [Real.exp_zero]
  have hphi0_upper : AdversarialBco.BodySpec.phi 0 ≤ (1000 / 2506 : ℝ) := by
    rw [AdversarialBco.BodySpec.phi]
    calc
      Real.exp (-(0 ^ 2) / 2) / Real.sqrt (2 * Real.pi) = 1 / Real.sqrt (2 * Real.pi) := by
        simp [Real.exp_zero]
      _ ≤ 1 / (2506/1000) := by
        refine (one_div_le_one_div hpos_sqrt ?_).mpr hSl
        norm_num
      _ = (1000 / 2506 : ℝ) := by norm_num
  have hphi1_lower : (606 / 2507 : ℝ) ≤ AdversarialBco.BodySpec.phi 1 := by
    rw [AdversarialBco.BodySpec.phi]
    have h1 : (606 / 1000 : ℝ) / (2507/1000 : ℝ) ≤ (606 / 1000 : ℝ) / Real.sqrt (2 * Real.pi) := by
      refine div_le_div_of_nonneg_left (a := 606/1000) (b := 2507/1000) (c := Real.sqrt (2 * Real.pi))
        (by norm_num) hpos_sqrt hSu
    have h2 : (606 / 1000 : ℝ) / Real.sqrt (2 * Real.pi) ≤ Real.exp (-(1 ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by
      have h_exp_eq : Real.exp (-(1 ^ 2) / 2) = Real.exp (-(1 / 2)) := by norm_num
      rw [h_exp_eq]
      refine div_le_div_of_nonneg_right (a := 606/1000) (b := Real.exp (-(1/2))) (c := Real.sqrt (2 * Real.pi))
        he (by positivity)
    have h_left : (606 / 2507 : ℝ) = (606 / 1000 : ℝ) / (2507/1000 : ℝ) := by norm_num
    rw [h_left]
    linarith
  have hphi1_upper : AdversarialBco.BodySpec.phi 1 ≤ (607 / 2506 : ℝ) := by
    rw [AdversarialBco.BodySpec.phi]
    have h1 : Real.exp (-(1 ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤ Real.exp (-(1 ^ 2) / 2) / (2506/1000 : ℝ) := by
      have h_exp_eq : Real.exp (-(1 ^ 2) / 2) = Real.exp (-(1 / 2)) := by norm_num
      rw [h_exp_eq]
      refine div_le_div_of_nonneg_left (a := Real.exp (-(1/2))) (b := Real.sqrt (2 * Real.pi)) (c := 2506/1000)
        (by positivity) (by norm_num) hSl
    have h2 : Real.exp (-(1 ^ 2) / 2) / (2506/1000 : ℝ) ≤ (607 / 1000 : ℝ) / (2506/1000 : ℝ) := by
      have h_exp_eq : Real.exp (-(1 ^ 2) / 2) = Real.exp (-(1 / 2)) := by norm_num
      rw [h_exp_eq]
      refine div_le_div_of_nonneg_right (a := Real.exp (-(1/2))) (b := 607/1000) (c := 2506/1000)
        eu (by norm_num)
    have h_right : (607 / 2506 : ℝ) = (607 / 1000 : ℝ) / (2506/1000 : ℝ) := by norm_num
    rw [h_right]
    linarith
  have hkappa_lower : (312 / 1000 : ℝ) ≤ AdversarialBco.BodySpec.kappa := by
    rw [AdversarialBco.BodySpec.kappa]
    have h : (312 / 1000 : ℝ) ≤ (1000 / 2507 : ℝ) - (607 / 2506 : ℝ) + (156 / 1000 : ℝ) := by
      nlinarith
    linarith
  have hkappa_upper : AdversarialBco.BodySpec.kappa ≤ 319 / 1000 := by
    rw [AdversarialBco.BodySpec.kappa]
    have h : (1000 / 2506 : ℝ) - (606 / 2507 : ℝ) + (161 / 1000 : ℝ) ≤ (319 / 1000 : ℝ) := by
      nlinarith
    linarith
  have hkappa2_lower : (596 / 1000 : ℝ) ≤ AdversarialBco.BodySpec.kappa2 := by
    rw [AdversarialBco.BodySpec.kappa2]
    have h : (596 / 1000 : ℝ) ≤ (1 : ℝ) - (161 / 1000 : ℝ) - (607 / 2506 : ℝ) := by
      nlinarith
    linarith
  have hkappa2_upper : AdversarialBco.BodySpec.kappa2 ≤ 603 / 1000 := by
    rw [AdversarialBco.BodySpec.kappa2]
    have h : (1 : ℝ) - (156 / 1000 : ℝ) - (606 / 2507 : ℝ) ≤ (603 / 1000 : ℝ) := by
      nlinarith
    linarith
  exact ⟨hkappa_lower, hkappa_upper, hkappa2_lower, hkappa2_upper⟩
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.KS_bounds : AdversarialBco.BodySpec.KS ≤ 95000 ∧ (65 / 64 : ℝ) ^ 2 * 16 * AdversarialBco.BodySpec.KS ≤ AdversarialBco.BodySpec.KD := by
  rcases AdversarialBco.Body2.kappa_bounds with ⟨hκl, hκh, hκ2l, hκ2h⟩
  have hκpos : 0 < AdversarialBco.BodySpec.kappa := by linarith
  have hKSle93750 : AdversarialBco.BodySpec.KS ≤ 93750 := by
    unfold AdversarialBco.BodySpec.KS
    have h_div : 32 / AdversarialBco.BodySpec.kappa ≤ 32 / ((312 : ℝ) / 1000) := by
      have h_one_div : 1 / AdversarialBco.BodySpec.kappa ≤ 1 / ((312 : ℝ) / 1000) :=
        (one_div_le_one_div hκpos (by norm_num : 0 < (312 : ℝ) / 1000)).mpr hκl
      have h32pos : (0 : ℝ) ≤ 32 := by norm_num
      calc
        32 / AdversarialBco.BodySpec.kappa = 32 * (1 / AdversarialBco.BodySpec.kappa) := by ring
        _ ≤ 32 * (1 / ((312 : ℝ) / 1000)) := mul_le_mul_of_nonneg_left h_one_div h32pos
        _ = 32 / ((312 : ℝ) / 1000) := by ring
    have h_sq : (32 / AdversarialBco.BodySpec.kappa) ^ 2 ≤ (32 / ((312 : ℝ) / 1000)) ^ 2 := by
      have h_nonneg_div1 : 0 ≤ 32 / AdversarialBco.BodySpec.kappa := by positivity
      have h_nonneg_div2 : 0 ≤ 32 / ((312 : ℝ) / 1000) := by positivity
      have h_abs : |32 / AdversarialBco.BodySpec.kappa| ≤ |32 / ((312 : ℝ) / 1000)| := by
        rwa [abs_of_nonneg h_nonneg_div1, abs_of_nonneg h_nonneg_div2]
      exact (sq_le_sq.mpr h_abs)
    have h_kappa2 : 13 / 4 + 2 * AdversarialBco.BodySpec.kappa2 ≤ 13 / 4 + 2 * ((603 : ℝ) / 1000) := by
      have h2 : 2 * AdversarialBco.BodySpec.kappa2 ≤ 2 * ((603 : ℝ) / 1000) :=
        mul_le_mul_of_nonneg_left hκ2h (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h_nonneg_sq : 0 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 := by positivity
    have h_nonneg_sum : 0 ≤ 13 / 4 + 2 * AdversarialBco.BodySpec.kappa2 := by
      nlinarith [hκ2l]
    have h_mul : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) ≤
        (32 / ((312 : ℝ) / 1000)) ^ 2 * (13 / 4 + 2 * ((603 : ℝ) / 1000)) :=
      mul_le_mul h_sq h_kappa2 h_nonneg_sum (by positivity : 0 ≤ (32 / ((312 : ℝ) / 1000)) ^ 2)
    have h_two_pos : (0 : ℝ) ≤ 2 := by norm_num
    have h_final : 2 * ((32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2)) ≤
        2 * ((32 / ((312 : ℝ) / 1000)) ^ 2 * (13 / 4 + 2 * ((603 : ℝ) / 1000))) :=
      mul_le_mul_of_nonneg_left h_mul h_two_pos
    -- Now compute the RHS with norm_num
    have h_rhs : 2 * ((32 / ((312 : ℝ) / 1000)) ^ 2 * (13 / 4 + 2 * ((603 : ℝ) / 1000))) ≤ 93750 := by
      norm_num
    linarith
  have hKSle95000 : AdversarialBco.BodySpec.KS ≤ 95000 := by linarith
  have h_second : (65 / 64 : ℝ) ^ 2 * 16 * AdversarialBco.BodySpec.KS ≤ AdversarialBco.BodySpec.KD := by
    have hpos : 0 ≤ (65 / 64 : ℝ) ^ 2 * 16 := by positivity
    have h_mul : (65 / 64 : ℝ) ^ 2 * 16 * AdversarialBco.BodySpec.KS ≤ (65 / 64 : ℝ) ^ 2 * 16 * 93750 :=
      mul_le_mul_of_nonneg_left hKSle93750 hpos
    have h_rhs : (65 / 64 : ℝ) ^ 2 * 16 * 93750 ≤ AdversarialBco.BodySpec.KD := by
      unfold AdversarialBco.BodySpec.KD
      norm_num
    linarith
  exact ⟨hKSle95000, h_second⟩
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.C0_bound : 4 * AdversarialBco.BodySpec.KD * ((2 + 4 * Real.log (52 * Real.sqrt (Real.pi / 2) * (17 / 16) * (1 + 10 ^ 8))) / Real.log 2 + 48) ≤ 1200000000 := by
  have hKD : 4 * AdversarialBco.BodySpec.KD = 6400000 := by
    dsimp [AdversarialBco.BodySpec.KD]
    norm_num
  rw [hKD]
  set C := 52 * Real.sqrt (Real.pi / 2) * (17 / 16) * (1 + 10 ^ 8) with hC
  have hC_pos : 0 < C := by
    dsimp [C]
    have h_sqrt_pos : 0 < Real.sqrt (Real.pi / 2) :=
      Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
    positivity
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have h_log2_gt_69 : (0.69 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have h_sqrt_bound : Real.sqrt (Real.pi / 2) ≤ 1.26 := by
    have h_sq : Real.pi / 2 < (1.26 : ℝ)^2 := by
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      nlinarith
    calc
      Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((1.26 : ℝ)^2) := Real.sqrt_le_sqrt (le_of_lt h_sq)
      _ = 1.26 := Real.sqrt_sq (by norm_num : 0 ≤ (1.26 : ℝ))
  have hC_bound : C ≤ 7 * 10 ^ 9 := by
    dsimp [C]
    have h1 : 52 * Real.sqrt (Real.pi / 2) * (17 / 16) * (1 + 10 ^ 8) ≤
             52 * (1.26 : ℝ) * (17 / 16) * (1 + 10 ^ 8) := by
      nlinarith
    have h2 : 52 * (1.26 : ℝ) * (17 / 16) * (1 + 10 ^ 8) ≤ 7 * 10 ^ 9 := by
      norm_num
    linarith
  have h_logC_bound : Real.log C ≤ 23 := by
    rw [Real.log_le_iff_le_exp hC_pos]
    have h_exp23 : Real.exp (23 : ℝ) = (Real.exp 1) ^ (23 : ℕ) := by
      calc
        Real.exp (23 : ℝ) = Real.exp ((23 : ℕ) * (1 : ℝ)) := by norm_num
        _ = (Real.exp (1 : ℝ)) ^ (23 : ℕ) := Real.exp_nat_mul (1 : ℝ) (23 : ℕ)
    rw [h_exp23]
    have h_exp1_ge : (2.7 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    have h_pow : (2.7 : ℝ) ^ (23 : ℕ) ≤ (Real.exp 1) ^ (23 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h_exp1_ge (23 : ℕ)
    have h_8_3e9 : (8.3 : ℝ) * 10 ^ 9 ≤ (2.7 : ℝ) ^ (23 : ℕ) := by
      norm_num
    have h_7e9_8_3e9 : (7 : ℝ) * 10 ^ 9 ≤ (8.3 : ℝ) * 10 ^ 9 := by
      norm_num
    linarith
  have h_num_bound : (2 : ℝ) + 4 * Real.log C ≤ 94 := by
    linarith
  have h_div_bound1 : ((2 : ℝ) + 4 * Real.log C) / Real.log 2 ≤ 94 / Real.log 2 :=
    div_le_div_of_nonneg_right h_num_bound (by linarith)
  have h_div_bound2 : 94 / Real.log 2 < 94 / (0.69 : ℝ) := by
    refine div_lt_div_of_pos_left (by norm_num) (by norm_num) h_log2_gt_69
  have h_final : ((2 : ℝ) + 4 * Real.log C) / Real.log 2 + 48 < 187.5 := by
    linarith
  have h_target : 6400000 * (((2 : ℝ) + 4 * Real.log C) / Real.log 2 + 48) ≤ 1200000000 := by
    nlinarith
  -- 6400000 * 187.5 = 1200000000
  simpa [hC] using h_target
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open Real
open Set
open Filter

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec

/-- The derivative of the Gaussian density: `φ'(t) = -t * φ(t)`. -/
lemma Qtail_le_phi_div_hasDerivAt_phi (t : ℝ) : HasDerivAt phi (-t * phi t) t := by
  have h_gaussian : HasDerivAt (fun u => Real.exp (-(u ^ 2) / 2)) (-t * Real.exp (-(t ^ 2) / 2)) t := by
    have h_f : HasDerivAt (fun u => -(u ^ 2) / 2) (-t) t := by
      have h_sq : HasDerivAt (fun u => u ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      simpa [div_eq_mul_inv, mul_comm, mul_assoc] using h_sq.neg.div_const 2
    have h_exp : HasDerivAt Real.exp (Real.exp (-(t ^ 2) / 2)) (-(t ^ 2) / 2) :=
      Real.hasDerivAt_exp _
    have h_comp := HasDerivAt.comp t h_exp h_f
    have h_eq : (Real.exp ∘ (fun u => -(u ^ 2) / 2)) = (fun u => Real.exp (-(u ^ 2) / 2)) := rfl
    rw [h_eq] at h_comp
    simpa [mul_comm] using h_comp
  have h_const : HasDerivAt (fun x => x * ((Real.sqrt (2 * π))⁻¹)) ((Real.sqrt (2 * π))⁻¹)
      (Real.exp (-(t ^ 2) / 2)) := by
    have h_id : HasDerivAt (fun x : ℝ => x) 1 (Real.exp (-(t ^ 2) / 2)) := hasDerivAt_id _
    simpa [one_mul] using h_id.mul_const ((Real.sqrt (2 * π))⁻¹)
  have h_comp := HasDerivAt.comp t h_const h_gaussian
  unfold phi
  have h_eq : ((fun x => x * ((Real.sqrt (2 * π))⁻¹)) ∘ (fun u => Real.exp (-(u ^ 2) / 2))) =
      (fun u => (Real.exp (-(u ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹)) := rfl
  rw [h_eq] at h_comp
  simpa [div_eq_mul_inv, mul_comm, mul_assoc, neg_mul] using h_comp

/-- The Gaussian density tends to 0 at +∞. -/
lemma Qtail_le_phi_div_tendsto_phi_atTop : Tendsto phi atTop (nhds 0) := by
  have h_sq : Tendsto (fun (t : ℝ) => t ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have h_neg_sq : Tendsto (fun (t : ℝ) => -(t ^ 2)) atTop atBot := by
    exact Filter.tendsto_neg_atTop_atBot.comp h_sq
  have h_inner : Tendsto (fun (t : ℝ) => -(t ^ 2) / 2) atTop atBot :=
    h_neg_sq.atBot_div_const (by norm_num : 0 < (2 : ℝ))
  have h_exp : Tendsto (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_inner
  have h_mul : Tendsto (fun (t : ℝ) => (Real.exp (-(t ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹)) atTop (nhds 0) := by
    simpa using h_exp.mul_const ((Real.sqrt (2 * π))⁻¹)
  unfold phi
  simpa [div_eq_mul_inv] using h_mul

/-- `t * φ(t)` is integrable on `Ioi T` for any real `T`. -/
lemma Qtail_le_phi_div_integrableOn_Ioi_mul_phi (T : ℝ) : IntegrableOn (fun u => u * phi u) (Ioi T) volume := by
  have h_pos : IntegrableOn (fun u => u * Real.exp (-(1/2 : ℝ) * u ^ 2)) (Ioi 0) volume := by
    simpa [pow_one] using
      integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num : 0 < (1/2 : ℝ))
        (s := 1) (by norm_num : (-1 : ℝ) < 1)
  have h_pos' : IntegrableOn (fun u => u * Real.exp (-(u ^ 2) / 2)) (Ioi 0) volume := by
    simpa [div_eq_mul_inv, mul_comm] using h_pos
  by_cases hT : T ≤ 0
  · -- T ≤ 0: Ioi T = Ioi 0 ∪ Ioc T 0
    have h_union : Ioi T = Ioi (0 : ℝ) ∪ Ioc T 0 := by
      ext x; constructor
      · intro hx
        by_cases hx0 : x < 0
        · exact Or.inr ⟨hx, hx0.le⟩
        · by_cases hx0' : 0 < x
          · exact Or.inl hx0'
          · -- x = 0
            have hx_eq0 : x = 0 := by linarith
            rw [hx_eq0]
            have hT0 : T < 0 := by
              rw [hx_eq0] at hx
              exact hx
            exact Or.inr ⟨hT0, le_refl 0⟩
      · intro hx; rcases hx with hx0 | ⟨hx1, hx2⟩
        · exact Set.mem_Ioi.mpr (hT.trans_lt hx0)
        · exact Set.mem_Ioi.mpr hx1
    rw [h_union]
    have h_int_on_Ioc : IntegrableOn (fun u => u * Real.exp (-(u ^ 2) / 2)) (Ioc T 0) volume := by
      have h_cont : Continuous (fun u : ℝ => u * Real.exp (-(u ^ 2) / 2)) := by
        refine Continuous.mul continuous_id ?_
        refine Real.continuous_exp.comp ?_
        refine Continuous.div ?_ ?_ ?_
        · exact Continuous.neg (continuous_pow 2)
        · exact continuous_const
        · intro x; norm_num
      exact h_cont.integrableOn_Ioc
    have h_union_int : IntegrableOn (fun u => u * Real.exp (-(u ^ 2) / 2)) (Ioi (0 : ℝ) ∪ Ioc T 0) volume :=
      h_pos'.union h_int_on_Ioc
    -- Convert to u * phi u by multiplying by constant
    have h_mul_int : Integrable (fun u => (u * Real.exp (-(u ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹))
        (volume.restrict (Ioi (0 : ℝ) ∪ Ioc T 0)) :=
      Integrable.mul_const h_union_int ((Real.sqrt (2 * π))⁻¹)
    have h_ae : (fun u => (u * Real.exp (-(u ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹)) =ᵐ[volume.restrict (Ioi (0 : ℝ) ∪ Ioc T 0)]
               (fun u => u * phi u) :=
      ae_of_all _ (fun u => by simp [phi, div_eq_mul_inv, mul_comm, mul_assoc])
    have h_mul_int' : IntegrableOn (fun u => u * phi u) (Ioi (0 : ℝ) ∪ Ioc T 0) volume :=
      h_mul_int.congr h_ae
    exact h_mul_int'
  · -- T > 0: Ioi T ⊆ Ioi 0
    have h_sub : Ioi T ⊆ Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by linarith)
    have h_restricted : IntegrableOn (fun u => u * Real.exp (-(u ^ 2) / 2)) (Ioi T) volume :=
      h_pos'.mono_set h_sub
    -- Multiply by constant factor to get u * phi u
    have h_mul_int : Integrable (fun u => (u * Real.exp (-(u ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹))
        (volume.restrict (Ioi T)) :=
      Integrable.mul_const h_restricted ((Real.sqrt (2 * π))⁻¹)
    have h_ae : (fun u => (u * Real.exp (-(u ^ 2) / 2)) * ((Real.sqrt (2 * π))⁻¹)) =ᵐ[volume.restrict (Ioi T)]
               (fun u => u * phi u) :=
      ae_of_all _ (fun u => by simp [phi, div_eq_mul_inv, mul_comm, mul_assoc])
    have h_mul_int' : IntegrableOn (fun u => u * phi u) (Ioi T) volume :=
      h_mul_int.congr h_ae
    exact h_mul_int'

/-- FTC: `∫_T^∞ t * φ(t) dt = φ(T)`. -/
lemma Qtail_le_phi_div_integral_Ioi_mul_phi (T : ℝ) : ∫ t in Ioi T, t * phi t = phi T := by
  have h_deriv (x : ℝ) (hx : x ∈ Ici T) : HasDerivAt (-phi) (x * phi x) x := by
    have hx' := Qtail_le_phi_div_hasDerivAt_phi x
    simpa [neg_mul, neg_neg] using hx'.neg
  have h_int : IntegrableOn (fun u => u * phi u) (Ioi T) volume := Qtail_le_phi_div_integrableOn_Ioi_mul_phi T
  have h_tendsto : Tendsto (fun u => -phi u) atTop (nhds 0) := by
    simpa using Qtail_le_phi_div_tendsto_phi_atTop.neg
  have h_eq := integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv h_int h_tendsto
  simpa using h_eq

end AdversarialBco.Body2

theorem AdversarialBco.Body2.Qtail_le_phi_div (T : ℝ) (hT : 0 < T) :
    AdversarialBco.BodySpec.Qtail T ≤ AdversarialBco.BodySpec.phi T / T := by
  dsimp [AdversarialBco.BodySpec.Qtail]
  calc
    ∫ s in Ioi T, AdversarialBco.BodySpec.phi s
        ≤ ∫ s in Ioi T, (s / T) * AdversarialBco.BodySpec.phi s := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
      · -- integrability of φ on Ioi T
        have h_int_phi : IntegrableOn AdversarialBco.BodySpec.phi (Ioi T) volume := by
          have h_base : IntegrableOn (fun u => Real.exp (-(1/2 : ℝ) * u ^ 2)) (Ioi 0) volume := by
            simpa [pow_zero] using
              integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num : 0 < (1/2 : ℝ))
                (s := 0) (by norm_num : (-1 : ℝ) < 0)
          have h_sub : Ioi T ⊆ Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by linarith)
          have h_restricted : IntegrableOn (fun u => Real.exp (-(1/2 : ℝ) * u ^ 2)) (Ioi T) volume :=
            h_base.mono_set h_sub
          have h_mul_int : Integrable (fun u => (Real.exp (-(1/2 : ℝ) * u ^ 2)) * ((Real.sqrt (2 * π))⁻¹))
              (volume.restrict (Ioi T)) :=
            Integrable.mul_const h_restricted ((Real.sqrt (2 * π))⁻¹)
          have h_ae : (fun u => (Real.exp (-(1/2 : ℝ) * u ^ 2)) * ((Real.sqrt (2 * π))⁻¹)) =ᵐ[volume.restrict (Ioi T)]
                     AdversarialBco.BodySpec.phi :=
            ae_of_all _ (fun u => by simp [AdversarialBco.BodySpec.phi, div_eq_mul_inv, mul_comm])
          have h_mul_int' : IntegrableOn AdversarialBco.BodySpec.phi (Ioi T) volume :=
            h_mul_int.congr h_ae
          exact h_mul_int'
        exact h_int_phi
      · -- integrability of (s/T) * φ(s) on Ioi T
        have h_int_mul : IntegrableOn (fun u => u * AdversarialBco.BodySpec.phi u) (Ioi T) volume :=
          AdversarialBco.Body2.Qtail_le_phi_div_integrableOn_Ioi_mul_phi T
        have h_mul_int : Integrable (fun u => (u * AdversarialBco.BodySpec.phi u) * (T⁻¹))
            (volume.restrict (Ioi T)) :=
          Integrable.mul_const h_int_mul (T⁻¹)
        have h_ae : (fun u => (u * AdversarialBco.BodySpec.phi u) * (T⁻¹)) =ᵐ[volume.restrict (Ioi T)]
                   (fun u => (u / T) * AdversarialBco.BodySpec.phi u) :=
          ae_of_all _ (fun u => by ring)
        have h_mul_int' : IntegrableOn (fun u => (u / T) * AdversarialBco.BodySpec.phi u) (Ioi T) volume :=
          h_mul_int.congr h_ae
        exact h_mul_int'
      · intro s hs
        have hsT : T < s := hs
        have h_phi_pos : 0 < AdversarialBco.BodySpec.phi s := by
          dsimp [AdversarialBco.BodySpec.phi]
          positivity
        have h_ratio : 1 ≤ s / T :=
          (one_le_div hT).mpr hsT.le
        nlinarith
    _ = (∫ s in Ioi T, s * AdversarialBco.BodySpec.phi s) / T := by
      calc
        ∫ s in Ioi T, (s / T) * AdversarialBco.BodySpec.phi s
            = ∫ s in Ioi T, (s * AdversarialBco.BodySpec.phi s) / T := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          ring
        _ = (∫ s in Ioi T, s * AdversarialBco.BodySpec.phi s) / T := by
          rw [integral_div (μ := volume.restrict (Ioi T)) T (fun s => s * AdversarialBco.BodySpec.phi s)]
    _ = AdversarialBco.BodySpec.phi T / T := by
      rw [AdversarialBco.Body2.Qtail_le_phi_div_integral_Ioi_mul_phi T]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.mills_lower (T : ℝ) (hT : 0 ≤ T) : AdversarialBco.BodySpec.phi T / (1 + T) ≤ AdversarialBco.BodySpec.Qtail T := by
  set v := fun t : ℝ => AdversarialBco.BodySpec.Qtail t - AdversarialBco.BodySpec.phi t / (1 + t) with hv_def
  have h_deriv_phi : ∀ t : ℝ, HasDerivAt AdversarialBco.BodySpec.phi (-(t * AdversarialBco.BodySpec.phi t)) t := by
    intro t
    have h_exp : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (-(t * Real.exp (-(t ^ 2) / 2))) t := by
      have h_inner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-t) t := by
        have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h_neg_sq : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-(2 * t)) t := h_sq.neg
        have h_div : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-(2 * t) / 2) t := h_neg_sq.div_const 2
        simpa [div_eq_inv_mul, mul_comm] using h_div
      have h_exp_deriv : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Real.exp (-(t ^ 2) / 2) * (-t)) t :=
        HasDerivAt.exp h_inner
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_exp_deriv
    have h_div : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)) (-(t * Real.exp (-(t ^ 2) / 2)) / Real.sqrt (2 * Real.pi)) t :=
      h_exp.div_const (Real.sqrt (2 * Real.pi))
    have h_phi_eq : (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)) = AdversarialBco.BodySpec.phi := by
      ext x; rfl
    rw [h_phi_eq] at h_div
    have h_simp : -(t * Real.exp (-(t ^ 2) / 2)) / Real.sqrt (2 * Real.pi) = -(t * AdversarialBco.BodySpec.phi t) := by
      dsimp [AdversarialBco.BodySpec.phi]
      ring
    rw [h_simp] at h_div
    exact h_div
  have h_deriv_v : ∀ t : ℝ, t ≠ -1 → HasDerivAt v (-t * AdversarialBco.BodySpec.phi t / (1 + t) ^ 2) t := by
    intro t ht_ne
    have h_Qtail : HasDerivAt AdversarialBco.BodySpec.Qtail (-AdversarialBco.BodySpec.phi t) t :=
      AdversarialBco.Body2.hasDerivAt_Qtail t
    have h_one_add : HasDerivAt (fun x : ℝ => 1 + x) 1 t := by
      simpa [add_comm] using (hasDerivAt_id t).const_add 1
    have h_denom_ne_zero : (1 + t) ≠ 0 := by
      intro hzero
      apply ht_ne
      linarith
    have h_phi_div : HasDerivAt (fun x : ℝ => AdversarialBco.BodySpec.phi x / (1 + x))
        (((-(t * AdversarialBco.BodySpec.phi t)) * (1 + t) - AdversarialBco.BodySpec.phi t * 1) / (1 + t) ^ 2) t :=
      HasDerivAt.fun_div (h_deriv_phi t) h_one_add h_denom_ne_zero
    have h_deriv : HasDerivAt v ((-AdversarialBco.BodySpec.phi t) - (((-(t * AdversarialBco.BodySpec.phi t)) * (1 + t) - AdversarialBco.BodySpec.phi t * 1) / (1 + t) ^ 2)) t :=
      HasDerivAt.sub h_Qtail h_phi_div
    have h_simplify : (-AdversarialBco.BodySpec.phi t) - (((-(t * AdversarialBco.BodySpec.phi t)) * (1 + t) - AdversarialBco.BodySpec.phi t * 1) / (1 + t) ^ 2) = -t * AdversarialBco.BodySpec.phi t / (1 + t) ^ 2 := by
      dsimp [AdversarialBco.BodySpec.phi]
      field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 from Real.sqrt_pos.mpr (by positivity) |>.ne']
      ring_nf
    rw [h_simplify] at h_deriv
    exact h_deriv
  have h_nonneg_phi : ∀ t : ℝ, 0 ≤ AdversarialBco.BodySpec.phi t := by
    intro t
    dsimp [AdversarialBco.BodySpec.phi]
    have h_exp_nonneg : 0 ≤ Real.exp (-(t ^ 2) / 2) := Real.exp_pos _ |>.le
    have h_sqrt_pos : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    exact div_nonneg h_exp_nonneg h_sqrt_pos
  have h_deriv_nonpos : ∀ t : ℝ, 0 ≤ t → -t * AdversarialBco.BodySpec.phi t / (1 + t) ^ 2 ≤ 0 := by
    intro t ht
    have h_num_nonpos : -t * AdversarialBco.BodySpec.phi t ≤ 0 := by
      have : 0 ≤ t * AdversarialBco.BodySpec.phi t := mul_nonneg ht (h_nonneg_phi t)
      linarith
    have h_denom_nonneg : 0 ≤ (1 + t) ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos h_denom_nonneg
  have h_v_nonneg : 0 ≤ v T := by
    have h_decreasing : ∀ S : ℝ, T ≤ S → v S ≤ v T := by
      intro S hTS
      by_cases h_eq : S = T
      · subst h_eq; rfl
      · have h_lt : T < S := by
          by_contra! h
          exact h_eq (by linarith)
        have h_cont : ContinuousOn v (Set.Icc T S) := by
          have h_diff : DifferentiableOn ℝ v (Set.Icc T S) := by
            intro x hx
            rcases Set.mem_Icc.1 hx with ⟨hx1, hx2⟩
            have hx_ne : x ≠ -1 := by linarith
            exact (h_deriv_v x hx_ne).differentiableAt.differentiableWithinAt
          exact h_diff.continuousOn
        have h_diff_on : DifferentiableOn ℝ v (Set.Ioo T S) := by
          intro x hx
          rcases Set.mem_Ioo.1 hx with ⟨hx1, hx2⟩
          have hx_ne : x ≠ -1 := by linarith
          exact (h_deriv_v x hx_ne).differentiableAt.differentiableWithinAt
        have h_mvt : ∃ c ∈ Set.Ioo T S, deriv v c = (v S - v T) / (S - T) :=
          exists_deriv_eq_slope v h_lt h_cont h_diff_on
        rcases h_mvt with ⟨c, hc, h_eq_deriv⟩
        have hc_nonneg : 0 ≤ c := by
          rcases Set.mem_Ioo.1 hc with ⟨hc1, hc2⟩
          linarith
        have hc_ne : c ≠ -1 := by linarith
        have h_deriv_c : deriv v c = -c * AdversarialBco.BodySpec.phi c / (1 + c) ^ 2 :=
          (h_deriv_v c hc_ne).deriv
        rw [h_deriv_c] at h_eq_deriv
        have h_num_nonpos : -c * AdversarialBco.BodySpec.phi c ≤ 0 := by
          have : 0 ≤ c * AdversarialBco.BodySpec.phi c := mul_nonneg hc_nonneg (h_nonneg_phi c)
          linarith
        have h_denom_nonneg : 0 ≤ (1 + c) ^ 2 := by positivity
        have h_deriv_nonpos_c : -c * AdversarialBco.BodySpec.phi c / (1 + c) ^ 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h_num_nonpos h_denom_nonneg
        have h_denom_pos : 0 < S - T := by linarith
        have h_div_nonpos : (v S - v T) / (S - T) ≤ 0 := by
          rw [← h_eq_deriv]
          exact h_deriv_nonpos_c
        have h_nonpos : v S - v T ≤ 0 := by
          have := div_nonpos_iff.mp h_div_nonpos
          rcases this with (⟨hpos, hneg⟩ | ⟨hneg', hpos'⟩)
          · linarith
          · exact hneg'
        linarith
    have h_phi_int : MeasureTheory.IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by
      have h_int : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) MeasureTheory.volume := by
        have : (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) = (fun x : ℝ => Real.exp (-((1/2 : ℝ)) * x ^ 2)) := by
          ext x; ring_nf
        rw [this]
        exact integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))
      have h_int' : MeasureTheory.Integrable (AdversarialBco.BodySpec.phi) MeasureTheory.volume :=
        h_int.div_const (Real.sqrt (2 * Real.pi))
      exact h_int'.integrableOn
    have h_tendsto_v : Filter.Tendsto v Filter.atTop (nhds 0) := by
      have h_Qtail_tendsto : Filter.Tendsto AdversarialBco.BodySpec.Qtail Filter.atTop (nhds 0) := by
        have h_anti : Antitone fun (t : ℝ) => Set.Ioi t := by
          intro a b h
          exact Set.Ioi_subset_Ioi h
        have h_meas : ∀ (t : ℝ), MeasurableSet (Set.Ioi t) := fun t => measurableSet_Ioi
        have h_inter : ⋂ (t : ℝ), Set.Ioi t = ∅ := by
          ext x
          simp [Set.mem_iInter, Set.mem_Ioi]
          exact ⟨x, le_refl x⟩
        have h_intble : ∃ (t : ℝ), MeasureTheory.IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi t) MeasureTheory.volume := by
          refine ⟨0, h_phi_int⟩
        have h_tendsto_set : Filter.Tendsto (fun t : ℝ => ∫ (s : ℝ) in Set.Ioi t, AdversarialBco.BodySpec.phi s) Filter.atTop
            (nhds (∫ (s : ℝ) in ⋂ (t : ℝ), Set.Ioi t, AdversarialBco.BodySpec.phi s)) :=
          MeasureTheory.tendsto_setIntegral_of_antitone h_meas h_anti h_intble
        have h_empty_int : (∫ (s : ℝ) in (∅ : Set ℝ), AdversarialBco.BodySpec.phi s) = (0 : ℝ) :=
          MeasureTheory.setIntegral_empty
        have h_qtail_eq : AdversarialBco.BodySpec.Qtail = (fun t : ℝ => ∫ (s : ℝ) in Set.Ioi t, AdversarialBco.BodySpec.phi s) := by
          ext t; rfl
        rw [h_qtail_eq]
        simpa [h_inter, h_empty_int] using h_tendsto_set
      have h_phi_div_tendsto : Filter.Tendsto (fun t : ℝ => AdversarialBco.BodySpec.phi t / (1 + t)) Filter.atTop (nhds 0) := by
        have h_phi_tendsto : Filter.Tendsto AdversarialBco.BodySpec.phi Filter.atTop (nhds 0) := by
          unfold AdversarialBco.BodySpec.phi
          have h_num : Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) Filter.atTop (nhds 0) := by
            have h_sq_tendsto : Filter.Tendsto (fun t : ℝ => -(t ^ 2) / 2) Filter.atTop Filter.atBot := by
              have h_neg_sq : Filter.Tendsto (fun t : ℝ => -(t ^ 2)) Filter.atTop Filter.atBot := by
                have h_sq : Filter.Tendsto (fun t : ℝ => t ^ 2) Filter.atTop Filter.atTop :=
                  Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
                simpa using Filter.tendsto_neg_atTop_atBot.comp h_sq
              exact Filter.Tendsto.atBot_div_const (by norm_num : 0 < (2 : ℝ)) h_neg_sq
            exact Real.tendsto_exp_atBot.comp h_sq_tendsto
          have h_denom : Filter.Tendsto (fun _ : ℝ => Real.sqrt (2 * Real.pi)) Filter.atTop (nhds (Real.sqrt (2 * Real.pi))) :=
            tendsto_const_nhds
          have h_sqrt_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
            Real.sqrt_pos.mpr (by positivity) |>.ne'
          have h_div : Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds (0 / Real.sqrt (2 * Real.pi))) :=
            Filter.Tendsto.div h_num h_denom h_sqrt_ne_zero
          simpa [zero_div] using h_div
        have h_denom_tendsto : Filter.Tendsto (fun t : ℝ => 1 + t) Filter.atTop Filter.atTop := by
          simpa [add_comm] using Filter.tendsto_atTop_add_const_right (α := ℝ) Filter.atTop 1 Filter.tendsto_id
        exact Filter.Tendsto.div_atTop h_phi_tendsto h_denom_tendsto
      have h_v_tendsto : Filter.Tendsto v Filter.atTop (nhds (0 - 0)) :=
        Filter.Tendsto.sub h_Qtail_tendsto h_phi_div_tendsto
      simpa [sub_self] using h_v_tendsto
    have h_eventually : ∀ᶠ (S : ℝ) in Filter.atTop, v S ≤ v T := by
      refine Filter.eventually_atTop.mpr ⟨T, fun S hS => h_decreasing S hS⟩
    exact le_of_tendsto h_tendsto_v h_eventually
  dsimp [v] at h_v_nonneg
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open Set
open Real

-- Helper: derivative of the Gaussian density phi
theorem AdversarialBco.Body2.mills_antitone_hasDerivAt_phi (t : ℝ) : HasDerivAt AdversarialBco.BodySpec.phi (-t * AdversarialBco.BodySpec.phi t) t := by
  unfold AdversarialBco.BodySpec.phi
  have h_exp : HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2)) (Real.exp (-(t ^ 2) / 2) * (-t)) t := by
    have h_inner : HasDerivAt (fun t => -(t ^ 2) / 2) (-t) t := by
      have h_sq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h_neg_sq : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-(2 * t)) t := h_sq.neg
      have h_div_two : HasDerivAt (fun t : ℝ => -(t ^ 2) / 2) (-(2 * t) / 2) t := by
        simpa using h_neg_sq.div_const 2
      have : -(2 * t) / 2 = -t := by ring
      simpa [this] using h_div_two
    have h_exp_at : HasDerivAt Real.exp (Real.exp (-(t ^ 2) / 2)) (-(t ^ 2) / 2) := by
      simpa using Real.hasDerivAt_exp (-(t ^ 2) / 2)
    exact HasDerivAt.comp t h_exp_at h_inner
  have h_mul : HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2) * (Real.sqrt (2 * Real.pi))⁻¹)
      (Real.exp (-(t ^ 2) / 2) * (-t) * (Real.sqrt (2 * Real.pi))⁻¹) t := by
    simpa using h_exp.mul_const (Real.sqrt (2 * Real.pi))⁻¹
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_mul

lemma AdversarialBco.Body2.mills_antitone_phi_pos (t : ℝ) : AdversarialBco.BodySpec.phi t > 0 := by
  unfold AdversarialBco.BodySpec.phi
  refine div_pos (Real.exp_pos _) ?_
  positivity

lemma AdversarialBco.Body2.mills_antitone_phi_ne_zero (t : ℝ) : AdversarialBco.BodySpec.phi t ≠ 0 := by
  linarith [AdversarialBco.Body2.mills_antitone_phi_pos t]

lemma AdversarialBco.Body2.mills_antitone_continuous_Qtail : Continuous AdversarialBco.BodySpec.Qtail := by
  have h_diff : Differentiable ℝ AdversarialBco.BodySpec.Qtail := by
    intro t
    exact (AdversarialBco.Body2.hasDerivAt_Qtail t).differentiableAt
  exact h_diff.continuous

lemma AdversarialBco.Body2.mills_antitone_continuous_phi : Continuous AdversarialBco.BodySpec.phi := by
  unfold AdversarialBco.BodySpec.phi
  refine Continuous.div ?_ ?_ ?_
  · refine Real.continuous_exp.comp ?_
    continuity
  · continuity
  · intro t
    positivity

theorem AdversarialBco.Body2.mills_antitone : AntitoneOn (fun T => AdversarialBco.BodySpec.Qtail T / AdversarialBco.BodySpec.phi T) (Set.Ici 0) := by
  let f := fun T : ℝ => AdversarialBco.BodySpec.Qtail T / AdversarialBco.BodySpec.phi T
  let f' := fun T : ℝ => -1 + T * f T
  have h_interior : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  have h_deriv : ∀ x ∈ interior (Set.Ici (0 : ℝ)), HasDerivWithinAt f (f' x) (interior (Set.Ici (0 : ℝ))) x := by
    intro x hx
    rw [h_interior] at hx
    have hx_pos : 0 < x := hx
    have h_Qtail : HasDerivAt AdversarialBco.BodySpec.Qtail (-AdversarialBco.BodySpec.phi x) x := hasDerivAt_Qtail x
    have h_phi : HasDerivAt AdversarialBco.BodySpec.phi (-x * AdversarialBco.BodySpec.phi x) x := AdversarialBco.Body2.mills_antitone_hasDerivAt_phi x
    have h_div := HasDerivAt.div h_Qtail h_phi (AdversarialBco.Body2.mills_antitone_phi_ne_zero x)
    have h_deriv_eq : (((-(AdversarialBco.BodySpec.phi x * AdversarialBco.BodySpec.phi x) +
        AdversarialBco.BodySpec.Qtail x * (x * AdversarialBco.BodySpec.phi x)) / (AdversarialBco.BodySpec.phi x) ^ 2)) =
        f' x := by
      dsimp [f, f']
      field_simp [AdversarialBco.Body2.mills_antitone_phi_ne_zero x]
    have h_hasDeriv : HasDerivAt f (f' x) x := by
      have h_temp : HasDerivAt (AdversarialBco.BodySpec.Qtail / AdversarialBco.BodySpec.phi) (f' x) x := by
        simpa [h_deriv_eq] using h_div
      exact h_temp
    rw [h_interior]
    exact h_hasDeriv.hasDerivWithinAt
  have h_nonpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), f' x ≤ 0 := by
    intro x hx
    rw [h_interior] at hx
    have hx_pos : 0 < x := hx
    dsimp [f']
    have h_bound : AdversarialBco.BodySpec.Qtail x / AdversarialBco.BodySpec.phi x ≤ 1 / x := by
      have h := Qtail_le_phi_div x hx_pos
      have h_div := div_le_div_of_nonneg_right h (le_of_lt (AdversarialBco.Body2.mills_antitone_phi_pos x))
      have h_simp : (AdversarialBco.BodySpec.phi x / x) / AdversarialBco.BodySpec.phi x = 1 / x := by
        field_simp [ne_of_gt hx_pos, AdversarialBco.Body2.mills_antitone_phi_ne_zero x]
      calc
        AdversarialBco.BodySpec.Qtail x / AdversarialBco.BodySpec.phi x ≤
            (AdversarialBco.BodySpec.phi x / x) / AdversarialBco.BodySpec.phi x := h_div
        _ = 1 / x := h_simp
    have h_mul : x * (AdversarialBco.BodySpec.Qtail x / AdversarialBco.BodySpec.phi x) ≤ 1 := by
      have h_mul' := mul_le_mul_of_nonneg_left h_bound (le_of_lt hx_pos)
      have h_simp' : x * x⁻¹ = 1 := by field_simp [ne_of_gt hx_pos]
      simpa [h_simp'] using h_mul'
    linarith
  have h_cont : ContinuousOn f (Set.Ici (0 : ℝ)) := by
    have h_cont_num : ContinuousOn AdversarialBco.BodySpec.Qtail (Set.Ici 0) :=
      AdversarialBco.Body2.mills_antitone_continuous_Qtail.continuousOn
    have h_cont_denom : ContinuousOn AdversarialBco.BodySpec.phi (Set.Ici 0) :=
      AdversarialBco.Body2.mills_antitone_continuous_phi.continuousOn
    have h_denom_pos : ∀ t ∈ Set.Ici (0 : ℝ), AdversarialBco.BodySpec.phi t ≠ 0 := by
      intro t ht
      exact AdversarialBco.Body2.mills_antitone_phi_ne_zero t
    exact h_cont_num.div h_cont_denom h_denom_pos
  have h_conv : Convex ℝ (Set.Ici (0 : ℝ)) := convex_Ici 0
  exact antitoneOn_of_hasDerivWithinAt_nonpos h_conv h_cont h_deriv h_nonpos
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.mills_zero : AdversarialBco.BodySpec.Qtail 0 / AdversarialBco.BodySpec.phi 0 = Real.sqrt (Real.pi / 2) := by
  have hQtail : AdversarialBco.BodySpec.Qtail 0 = 1/2 :=
    AdversarialBco.Body2.integral_phi_Ioi_zero
  have hphi0 : AdversarialBco.BodySpec.phi 0 = 1 / Real.sqrt (2 * Real.pi) := by
    simp [AdversarialBco.BodySpec.phi]
  rw [hQtail, hphi0]
  field_simp
  have hpos_left : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hpos_right : 0 ≤ 2 * Real.sqrt (Real.pi / 2) := by positivity
  have hsq_eq : (Real.sqrt (2 * Real.pi)) ^ 2 = (2 * Real.sqrt (Real.pi / 2)) ^ 2 := by
    calc
      (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
      _ = 4 * (Real.pi / 2) := by ring
      _ = 4 * ((Real.sqrt (Real.pi / 2)) ^ 2) := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ Real.pi / 2)]
      _ = (2 * Real.sqrt (Real.pi / 2)) ^ 2 := by ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with h | h
  · exact h
  · have hpos : Real.sqrt (2 * Real.pi) > 0 :=
      Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)
    have hnonpos : 2 * Real.sqrt (Real.pi / 2) ≥ 0 := by positivity
    linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_min_pos_phi : ∫ t, min (max t 0) 1 * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.kappa := by
  set f := fun (t : ℝ) => min (max t 0) 1 * AdversarialBco.BodySpec.phi t with hf
  have hphi_int : Integrable AdversarialBco.BodySpec.phi := by
    have hphi_eq : AdversarialBco.BodySpec.phi = fun t => ProbabilityTheory.gaussianPDFReal (0 : ℝ) 1 t := by
      ext t
      dsimp [AdversarialBco.BodySpec.phi, ProbabilityTheory.gaussianPDFReal]
      ring_nf
    rw [hphi_eq]
    exact ProbabilityTheory.integrable_gaussianPDFReal (0 : ℝ) 1
  have hg_cont : Continuous (fun t : ℝ => min (max t 0) 1) := by
    refine Continuous.min ?_ continuous_const
    refine Continuous.max continuous_id continuous_const
  have hg_ae_meas : AEStronglyMeasurable (fun t : ℝ => min (max t 0) 1) :=
    hg_cont.aestronglyMeasurable
  have hg_bdd : ∀ᵐ t ∂(volume : Measure ℝ), ‖min (max t 0) 1‖ ≤ (1 : ℝ) := by
    filter_upwards with t
    have h0 : 0 ≤ min (max t 0) 1 := by
      apply le_min ?_ (by norm_num)
      exact le_max_right t 0
    have h1 : min (max t 0) 1 ≤ 1 := min_le_right _ _
    simp [abs_of_nonneg h0, Real.norm_eq_abs, h1]
  have hf_int : Integrable f := by
    have := hphi_int.mul_bdd hg_ae_meas hg_bdd
    simpa [f, mul_comm] using this
  have hf_intOn_Iic : IntegrableOn f (Set.Iic (0 : ℝ)) :=
    hf_int.integrableOn
  have hf_intOn_Ioi : IntegrableOn f (Set.Ioi (0 : ℝ)) :=
    hf_int.integrableOn
  -- Split ℝ into Iic 0 and Ioi 0
  have h_split0 : (∫ t in Set.Iic (0 : ℝ), f t) + (∫ t in Set.Ioi (0 : ℝ), f t) = ∫ t, f t := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hf_intOn_Iic hf_intOn_Ioi]
  -- On Iic 0, f = 0
  have h_on_Iic : ∀ t ∈ Set.Iic (0 : ℝ), f t = 0 := by
    intro t ht
    dsimp [f]
    have ht' : t ≤ 0 := ht
    have h_max : max t 0 = 0 := max_eq_right ht'
    have h_min : min 0 1 = (0 : ℝ) := by norm_num
    calc
      min (max t 0) 1 * AdversarialBco.BodySpec.phi t = min 0 1 * AdversarialBco.BodySpec.phi t := by rw [h_max]
      _ = 0 * AdversarialBco.BodySpec.phi t := by rw [h_min]
      _ = 0 := by ring
  have h_int_Iic : (∫ t in Set.Iic (0 : ℝ), f t) = 0 := by
    rw [MeasureTheory.setIntegral_congr_ae (measurableSet_Iic) (by
      filter_upwards with t ht
      exact h_on_Iic t ht)]
    simp
  -- Split Ioi 0 into (0,1] and (1,∞)
  have h_int_01 : IntervalIntegrable f volume (0 : ℝ) 1 := by
    have h_cont : Continuous f := by
      dsimp [f]
      refine Continuous.mul ?_ ?_
      · refine Continuous.min ?_ continuous_const
        refine Continuous.max continuous_id continuous_const
      · unfold AdversarialBco.BodySpec.phi
        continuity
    exact h_cont.intervalIntegrable _ _
  have h_int_Ioi1 : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    hf_int.integrableOn
  have h_split1 : (∫ t in (0 : ℝ)..(1 : ℝ), f t) + (∫ t in Set.Ioi (1 : ℝ), f t) = (∫ t in Set.Ioi (0 : ℝ), f t) := by
    rw [← intervalIntegral.integral_interval_add_Ioi' h_int_01 h_int_Ioi1]
  -- On (0,1], f(t) = t * phi(t)
  have h_on_01 : ∀ t, t ∈ Set.Ioo (0 : ℝ) 1 → f t = t * AdversarialBco.BodySpec.phi t := by
    intro t ht
    dsimp [f]
    rcases ht with ⟨ht0, ht1⟩
    have h_max : max t 0 = t := max_eq_left (by linarith)
    have h_min : min t 1 = t := min_eq_left (by linarith)
    rw [h_max, h_min]
  -- On (1,∞), f(t) = phi(t)
  have h_on_Ioi1 : ∀ t ∈ Set.Ioi (1 : ℝ), f t = AdversarialBco.BodySpec.phi t := by
    intro t ht
    dsimp [f]
    have ht' : 1 < t := ht
    have h_max : max t 0 = t := max_eq_left (by linarith)
    have h_min : min t 1 = 1 := min_eq_right (by linarith)
    rw [h_max, h_min, one_mul]
  -- Derivative of phi: phi'(t) = -t * phi(t)
  have h_deriv : ∀ t : ℝ, HasDerivAt AdversarialBco.BodySpec.phi (-(t * AdversarialBco.BodySpec.phi t)) t := by
    intro t
    have h_phi_expr : AdversarialBco.BodySpec.phi = fun (x : ℝ) => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi) := rfl
    rw [h_phi_expr]
    -- Use the chain rule: derivative of exp(-x^2/2) is exp(-x^2/2) * (-x)
    have h_inner : HasDerivAt (fun (x : ℝ) => -(x ^ 2) / 2) (-t) t := by
      have h_sq : HasDerivAt (fun (x : ℝ) => x ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h_neg_sq : HasDerivAt (fun (x : ℝ) => -(x ^ 2)) (-(2 * t)) t :=
        h_sq.neg
      have h_div : HasDerivAt (fun (x : ℝ) => -(x ^ 2) / 2) (-(2 * t) / 2) t :=
        h_neg_sq.div_const 2
      -- Simplify -(2*t)/2 = -t
      have h_simp : -(2 * t) / 2 = -t := by ring
      rw [h_simp] at h_div
      exact h_div
    have h_exp : HasDerivAt Real.exp (Real.exp (-(t ^ 2) / 2)) (-(t ^ 2) / 2) :=
      Real.hasDerivAt_exp (x := -(t ^ 2) / 2)
    have h_comp : HasDerivAt (Real.exp ∘ (fun (x : ℝ) => -(x ^ 2) / 2)) (Real.exp (-(t ^ 2) / 2) * (-t)) t :=
      HasDerivAt.comp t h_exp h_inner
    have h_div_const : HasDerivAt (fun (x : ℝ) => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
      ((Real.exp (-(t ^ 2) / 2) * (-t)) / Real.sqrt (2 * Real.pi)) t :=
      h_comp.div_const (Real.sqrt (2 * Real.pi))
    -- Now simplify the derivative expression
    have h_simp' : (Real.exp (-(t ^ 2) / 2) * (-t)) / Real.sqrt (2 * Real.pi) = -(t * (Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi))) := by
      ring
    rw [h_simp'] at h_div_const
    exact h_div_const
  -- Compute ∫_0^1 t * phi(t) dt = phi(0) - phi(1) using FTC
  have h_int_01_tphi : (∫ t in (0 : ℝ)..(1 : ℝ), t * AdversarialBco.BodySpec.phi t) = AdversarialBco.BodySpec.phi 0 - AdversarialBco.BodySpec.phi 1 := by
    have h_deriv_neg : ∀ x ∈ Set.uIcc (0 : ℝ) (1 : ℝ), HasDerivAt (-AdversarialBco.BodySpec.phi) (x * AdversarialBco.BodySpec.phi x) x := by
      intro x hx
      have h := h_deriv x
      have h_neg : HasDerivAt (-AdversarialBco.BodySpec.phi) (-(-(x * AdversarialBco.BodySpec.phi x))) x :=
        h.neg
      have h_simp : -(-(x * AdversarialBco.BodySpec.phi x)) = x * AdversarialBco.BodySpec.phi x := by ring
      rw [h_simp] at h_neg
      exact h_neg
    have h_int : IntervalIntegrable (fun t => t * AdversarialBco.BodySpec.phi t) volume (0 : ℝ) 1 := by
      have h_cont : Continuous (fun t : ℝ => t * AdversarialBco.BodySpec.phi t) := by
        unfold AdversarialBco.BodySpec.phi
        continuity
      exact h_cont.intervalIntegrable _ _
    have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv_neg h_int
    -- h_ftc : ∫_0^1 (x * phi x) dx = (-phi) 1 - (-phi) 0
    -- (-phi) 1 - (-phi) 0 = -phi 1 + phi 0 = phi 0 - phi 1
    have h_simp_ftc : (-AdversarialBco.BodySpec.phi) 1 - (-AdversarialBco.BodySpec.phi) 0 = AdversarialBco.BodySpec.phi 0 - AdversarialBco.BodySpec.phi 1 := by
      simp [sub_eq_add_neg, add_comm]
    rw [h_simp_ftc] at h_ftc
    exact h_ftc
  -- Now assemble everything using a direct calculation
  have h_total : ∫ t, f t = AdversarialBco.BodySpec.kappa := by
    calc
      ∫ t, f t = (∫ t in Set.Iic (0 : ℝ), f t) + (∫ t in Set.Ioi (0 : ℝ), f t) := by rw [← h_split0]
      _ = 0 + (∫ t in Set.Ioi (0 : ℝ), f t) := by rw [h_int_Iic]
      _ = (∫ t in Set.Ioi (0 : ℝ), f t) := by simp
      _ = (∫ t in (0 : ℝ)..(1 : ℝ), f t) + (∫ t in Set.Ioi (1 : ℝ), f t) := by rw [← h_split1]
      _ = (∫ t in (0 : ℝ)..(1 : ℝ), t * AdversarialBco.BodySpec.phi t) + (∫ t in Set.Ioi (1 : ℝ), f t) := by
        have h_left : (∫ t in (0 : ℝ)..(1 : ℝ), f t) = (∫ t in (0 : ℝ)..(1 : ℝ), t * AdversarialBco.BodySpec.phi t) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with t ht
          -- ht : t ∈ Set.uIoc 0 1
          rcases Set.mem_uIoc.mp ht with (⟨ht0, ht1⟩ | ⟨ht1', ht0'⟩)
          · -- case: 0 < t ∧ t ≤ 1
            by_cases h0 : t = 0
            · subst t; simp [f]
            · by_cases h1 : t = 1
              · subst t; simp [f]
              · have hpos : 0 < t := ht0
                have hlt1 : t < 1 := by
                  apply lt_of_le_of_ne ht1 h1
                exact h_on_01 t ⟨hpos, hlt1⟩
          · -- case: 1 < t ∧ t ≤ 0 (impossible since 0 < 1)
            linarith
        rw [h_left]
      _ = (∫ t in (0 : ℝ)..(1 : ℝ), t * AdversarialBco.BodySpec.phi t) + (∫ t in Set.Ioi (1 : ℝ), AdversarialBco.BodySpec.phi t) := by
        have h_right : (∫ t in Set.Ioi (1 : ℝ), f t) = (∫ t in Set.Ioi (1 : ℝ), AdversarialBco.BodySpec.phi t) := by
          refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
          filter_upwards with t ht
          exact h_on_Ioi1 t ht
        rw [h_right]
      _ = (AdversarialBco.BodySpec.phi 0 - AdversarialBco.BodySpec.phi 1) + AdversarialBco.BodySpec.Qtail 1 := by
        rw [h_int_01_tphi, AdversarialBco.BodySpec.Qtail]
      _ = AdversarialBco.BodySpec.kappa := by
        rfl
  simpa [f] using h_total
end


section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
open Set

open Real

namespace AdversarialBco.Body2

lemma kernel_nonneg_Qtail_zero : BodySpec.Qtail 0 = 1/2 := by
  dsimp [BodySpec.Qtail, BodySpec.phi]
  have h_int : (∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2)) = Real.sqrt (2 * Real.pi) / 2 := by
    calc
      (∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2))
          = (∫ s in Ioi (0 : ℝ), Real.exp ((-(1/2 : ℝ)) * s ^ 2)) := by
        refine setIntegral_congr_ae measurableSet_Ioi ?_
        refine ae_of_all volume (fun s hs => ?_)
        rw [show -(s ^ 2) / 2 = (-(1/2 : ℝ)) * s ^ 2 by ring]
      _ = Real.sqrt (Real.pi / ((1 : ℝ)/2)) / 2 := by rw [integral_gaussian_Ioi]
      _ = Real.sqrt (2 * Real.pi) / 2 := by
        rw [show Real.pi / ((1 : ℝ)/2) = 2 * Real.pi by field_simp]
  calc
    ∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi)
        = (∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
      rw [integral_div]
    _ = (Real.sqrt (2 * Real.pi) / 2) / Real.sqrt (2 * Real.pi) := by rw [h_int]
    _ = 1/2 := by
      field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 from
        (Real.sqrt_pos.mpr (by positivity)).ne']

lemma kernel_nonneg_phi_pos (t : ℝ) : 0 < BodySpec.phi t := by
  dsimp [BodySpec.phi]
  refine div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

lemma kernel_nonneg_hasDerivAt_phi (t : ℝ) : HasDerivAt BodySpec.phi (-t * BodySpec.phi t) t := by
  have h_sq : HasDerivAt (fun (t : ℝ) => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h_inner : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-t) t := by
    have h_neg : HasDerivAt (fun (t : ℝ) => -(t ^ 2)) (-(2 * t)) t :=
      HasDerivAt.neg h_sq
    have h_div : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-(2 * t) / 2) t :=
      HasDerivAt.div_const h_neg 2
    have : -(2 * t) / 2 = -t := by ring
    rw [this] at h_div
    exact h_div
  have h_exp : HasDerivAt (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2))
      (Real.exp (-(t ^ 2) / 2) * (-t)) t := by
    simpa [mul_comm] using HasDerivAt.exp h_inner
  have h_div : HasDerivAt (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2) * ((Real.sqrt (2 * Real.pi))⁻¹))
      ((Real.exp (-(t ^ 2) / 2) * (-t)) * ((Real.sqrt (2 * Real.pi))⁻¹)) t :=
    HasDerivAt.mul_const h_exp ((Real.sqrt (2 * Real.pi))⁻¹)
  have h_body : BodySpec.phi = (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2) * ((Real.sqrt (2 * Real.pi))⁻¹)) := by
    ext s; rw [BodySpec.phi, div_eq_mul_inv]
  have h_deriv : (-t * BodySpec.phi t) = ((Real.exp (-(t ^ 2) / 2) * (-t)) * ((Real.sqrt (2 * Real.pi))⁻¹)) := by
    rw [BodySpec.phi]
    ring
  simpa [h_body, h_deriv, mul_comm, mul_left_comm, mul_assoc] using h_div

lemma kernel_nonneg_kappa_pos : 0 < BodySpec.kappa := by
  have h := kappa_bounds
  rcases h with ⟨hkl, hkr, _, _⟩
  linarith

lemma kernel_nonneg_kappa_lt_half : BodySpec.kappa < 1/2 := by
  have h := kappa_bounds
  rcases h with ⟨_, _, _, _⟩
  linarith

lemma kernel_nonneg_continuous_phi : Continuous BodySpec.phi := by
  have h_diff : Differentiable ℝ BodySpec.phi := by
    intro x
    exact (kernel_nonneg_hasDerivAt_phi x).differentiableAt
  exact h_diff.continuous

lemma kernel_nonneg_continuous_Qtail : Continuous BodySpec.Qtail := by
  have h_diff : Differentiable ℝ BodySpec.Qtail := by
    intro x
    exact (hasDerivAt_Qtail x).differentiableAt
  exact h_diff.continuous

lemma kernel_nonneg_Qtail_nonneg (t : ℝ) : 0 ≤ BodySpec.Qtail t := by
  dsimp [BodySpec.Qtail]
  refine integral_nonneg (fun s => ?_)
  have hpos : 0 ≤ BodySpec.phi s := by linarith [kernel_nonneg_phi_pos s]
  exact hpos

theorem kernel_nonneg (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 ≤ BodySpec.phi θ - BodySpec.phi 1 + BodySpec.Qtail 1 - 2 * BodySpec.kappa * BodySpec.Qtail θ := by
  set g := fun (x : ℝ) => BodySpec.phi x - BodySpec.phi 1 + BodySpec.Qtail 1 - 2 * BodySpec.kappa * BodySpec.Qtail x with hg
  have hderiv_g (x : ℝ) : HasDerivAt g (BodySpec.phi x * (2 * BodySpec.kappa - x)) x := by
    dsimp [g]
    have h1 : HasDerivAt BodySpec.phi (-x * BodySpec.phi x) x := kernel_nonneg_hasDerivAt_phi x
    have h2 : HasDerivAt (fun _ : ℝ => BodySpec.phi 1) 0 x := hasDerivAt_const x _
    have h3 : HasDerivAt (fun _ : ℝ => BodySpec.Qtail 1) 0 x := hasDerivAt_const x _
    have h4 : HasDerivAt (fun (x : ℝ) => 2 * BodySpec.kappa * BodySpec.Qtail x)
        (2 * BodySpec.kappa * (-BodySpec.phi x)) x :=
      HasDerivAt.const_mul (2 * BodySpec.kappa) (hasDerivAt_Qtail x)
    have hcombined : HasDerivAt (fun x : ℝ => BodySpec.phi x - BodySpec.phi 1 + BodySpec.Qtail 1 - 2 * BodySpec.kappa * BodySpec.Qtail x)
        ((-x * BodySpec.phi x) - 0 + 0 - (2 * BodySpec.kappa * (-BodySpec.phi x))) x :=
      ((h1.sub h2).add h3).sub h4
    have hderiv_eq : (-x * BodySpec.phi x) - 0 + 0 - (2 * BodySpec.kappa * (-BodySpec.phi x)) =
        BodySpec.phi x * (2 * BodySpec.kappa - x) := by ring
    -- hcombined's derivative simplifies to -(x*phi) + 2*kappa*phi
    have hcombined' : HasDerivAt (fun x : ℝ => BodySpec.phi x - BodySpec.phi 1 + BodySpec.Qtail 1 - 2 * BodySpec.kappa * BodySpec.Qtail x)
        (-(x * BodySpec.phi x) + 2 * BodySpec.kappa * BodySpec.phi x) x := by
      simpa [show (-x * BodySpec.phi x) - 0 + 0 - (2 * BodySpec.kappa * (-BodySpec.phi x)) =
        -(x * BodySpec.phi x) + 2 * BodySpec.kappa * BodySpec.phi x by ring] using hcombined
    have hgoal_eq : (-(x * BodySpec.phi x) + 2 * BodySpec.kappa * BodySpec.phi x) =
        BodySpec.phi x * (2 * BodySpec.kappa - x) := by ring
    simpa [hgoal_eq] using hcombined'
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [kernel_nonneg_Qtail_zero]
    dsimp [BodySpec.kappa]
    ring
  have hg1 : 0 ≤ g 1 := by
    dsimp [g]
    have hk : BodySpec.kappa < 1/2 := kernel_nonneg_kappa_lt_half
    have hQ1 : 0 ≤ BodySpec.Qtail 1 := kernel_nonneg_Qtail_nonneg 1
    have : 0 ≤ 1 - 2 * BodySpec.kappa := by linarith
    nlinarith
  by_cases hθk : θ ≤ 2 * BodySpec.kappa
  · -- θ ∈ [0, 2*kappa], g is non-decreasing
    have hk_nonneg : 0 ≤ BodySpec.kappa := by linarith [kernel_nonneg_kappa_pos]
    have h_mono : MonotoneOn g (Icc (0 : ℝ) (2 * BodySpec.kappa)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      · -- ContinuousOn
        have hg_cont : Continuous g := by
          dsimp [g]
          have h1 : Continuous (fun x => BodySpec.phi x - BodySpec.phi 1) :=
            Continuous.sub kernel_nonneg_continuous_phi continuous_const
          have h2 : Continuous (fun x => (BodySpec.phi x - BodySpec.phi 1) + BodySpec.Qtail 1) :=
            Continuous.add h1 continuous_const
          have h3 : Continuous (fun x => 2 * BodySpec.kappa * BodySpec.Qtail x) :=
            Continuous.mul continuous_const kernel_nonneg_continuous_Qtail
          exact Continuous.sub h2 h3
        exact hg_cont.continuousOn
      · -- HasDerivWithinAt on interior
        intro x hx
        exact (hderiv_g x).hasDerivWithinAt
      · -- Nonnegative derivative on interior
        intro x hx
        rw [interior_Icc] at hx
        rcases hx with ⟨hx1, hx2⟩
        have hpos : 0 ≤ BodySpec.phi x * (2 * BodySpec.kappa - x) := by
          have hphi_pos : 0 < BodySpec.phi x := kernel_nonneg_phi_pos x
          have h_nonneg : 0 ≤ 2 * BodySpec.kappa - x := by linarith
          nlinarith
        exact hpos
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * BodySpec.kappa) := by
      refine ⟨by norm_num, ?_⟩
      nlinarith
    have hθmem : θ ∈ Icc (0 : ℝ) (2 * BodySpec.kappa) := by
      refine ⟨h0, hθk⟩
    have hle := h_mono h0mem hθmem (by linarith)
    linarith
  · -- θ ∈ [2*kappa, 1], g is non-increasing
    have hk1 : 2 * BodySpec.kappa ≤ 1 := by
      have hk : BodySpec.kappa < 1/2 := kernel_nonneg_kappa_lt_half
      linarith
    have h_anti : AntitoneOn g (Icc (2 * BodySpec.kappa) (1 : ℝ)) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      · -- ContinuousOn
        have hg_cont : Continuous g := by
          dsimp [g]
          have h1 : Continuous (fun x => BodySpec.phi x - BodySpec.phi 1) :=
            Continuous.sub kernel_nonneg_continuous_phi continuous_const
          have h2 : Continuous (fun x => (BodySpec.phi x - BodySpec.phi 1) + BodySpec.Qtail 1) :=
            Continuous.add h1 continuous_const
          have h3 : Continuous (fun x => 2 * BodySpec.kappa * BodySpec.Qtail x) :=
            Continuous.mul continuous_const kernel_nonneg_continuous_Qtail
          exact Continuous.sub h2 h3
        exact hg_cont.continuousOn
      · -- HasDerivWithinAt on interior
        intro x hx
        exact (hderiv_g x).hasDerivWithinAt
      · -- Nonpositive derivative on interior
        intro x hx
        rw [interior_Icc] at hx
        rcases hx with ⟨hx1, hx2⟩
        have hnonpos : BodySpec.phi x * (2 * BodySpec.kappa - x) ≤ 0 := by
          have hphi_pos : 0 < BodySpec.phi x := kernel_nonneg_phi_pos x
          have h_nonpos : 2 * BodySpec.kappa - x ≤ 0 := by linarith
          nlinarith
        exact hnonpos
    have h1mem : (1 : ℝ) ∈ Icc (2 * BodySpec.kappa) (1 : ℝ) := by
      refine ⟨hk1, le_refl _⟩
    have hθmem : θ ∈ Icc (2 * BodySpec.kappa) (1 : ℝ) := by
      refine ⟨by linarith, h1⟩
    have hle := h_anti hθmem h1mem (by linarith)
    linarith

end AdversarialBco.Body2
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.phi_T_le (y : ℝ) (hy : 0 < y) : y * AdversarialBco.BodySpec.phi (Real.sqrt (2 * AdversarialBco.BodySpec.lnp y)) ≤ 26 / 64 := by
  have hlnp_nonneg : 0 ≤ AdversarialBco.BodySpec.lnp y := le_max_right _ _
  have hsqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hT_sq : (Real.sqrt (2 * AdversarialBco.BodySpec.lnp y)) ^ 2 = 2 * AdversarialBco.BodySpec.lnp y :=
    Real.sq_sqrt (by nlinarith)
  have hphi_eq : y * AdversarialBco.BodySpec.phi (Real.sqrt (2 * AdversarialBco.BodySpec.lnp y)) =
      (y * Real.exp (-(AdversarialBco.BodySpec.lnp y))) / Real.sqrt (2 * Real.pi) := by
    dsimp [AdversarialBco.BodySpec.phi]
    calc
      y * (Real.exp (-((Real.sqrt (2 * AdversarialBco.BodySpec.lnp y)) ^ 2) / 2) / Real.sqrt (2 * Real.pi))
          = y * (Real.exp (-((2 * AdversarialBco.BodySpec.lnp y)) / 2) / Real.sqrt (2 * Real.pi)) := by rw [hT_sq]
      _ = y * (Real.exp (-(AdversarialBco.BodySpec.lnp y)) / Real.sqrt (2 * Real.pi)) := by ring
      _ = (y * Real.exp (-(AdversarialBco.BodySpec.lnp y))) / Real.sqrt (2 * Real.pi) := by ring
  rw [hphi_eq]
  have hy_exp_le_one : y * Real.exp (-(AdversarialBco.BodySpec.lnp y)) ≤ 1 := by
    dsimp [AdversarialBco.BodySpec.lnp]
    by_cases hlog_nonneg : 0 ≤ Real.log y
    · rw [max_eq_left hlog_nonneg]
      rw [Real.exp_neg, Real.exp_log hy]
      field_simp [ne_of_gt hy]
      exact le_refl 1
    · rw [max_eq_right (by linarith)]
      simp
      by_contra! hgt
      have hlog_nonneg' : 0 ≤ Real.log y := Real.log_nonneg (by linarith : 1 ≤ y)
      linarith
  have h_one_div_sqrt_le : 1 / Real.sqrt (2 * Real.pi) ≤ 26 / 64 := by
    have hπgt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    have h_sq : (64 : ℝ) ^ 2 ≤ (26 * Real.sqrt (2 * Real.pi)) ^ 2 := by
      calc
        (64 : ℝ) ^ 2 = (4096 : ℝ) := by norm_num
        _ = 8 * (512 : ℝ) := by ring
        _ ≤ 8 * (169 * Real.pi) := by
          nlinarith
        _ = 1352 * Real.pi := by ring
        _ = (26 ^ 2) * (2 * Real.pi) := by ring
        _ = (26 * Real.sqrt (2 * Real.pi)) ^ 2 := by
          calc
            (26 ^ 2) * (2 * Real.pi) = 676 * (2 * Real.pi) := by norm_num
            _ = 1352 * Real.pi := by ring
            _ = (26 * Real.sqrt (2 * Real.pi)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
              ring
    have h_nonneg_26sqrt : 0 ≤ 26 * Real.sqrt (2 * Real.pi) := by positivity
    have h_ineq : (64 : ℝ) ≤ 26 * Real.sqrt (2 * Real.pi) := by
      nlinarith
    field_simp [ne_of_gt hsqrt_two_pi_pos, show (64 : ℝ) ≠ 0 from by norm_num]
    nlinarith
  have h_div_le : (y * Real.exp (-(AdversarialBco.BodySpec.lnp y))) / Real.sqrt (2 * Real.pi) ≤ 1 / Real.sqrt (2 * Real.pi) := by
    refine div_le_div_of_nonneg_right hy_exp_le_one (by positivity : 0 ≤ Real.sqrt (2 * Real.pi))
  linarith
end
