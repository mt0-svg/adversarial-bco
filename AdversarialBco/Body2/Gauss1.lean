/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBody

@[expose] public section

/-! Gaussian constants: the density `φ` and the tail `Q`, `0.156 ≤ Q(1) ≤ 0.161` (with
`0.85 ≤ ∫_0^1 e^{-t²/2} dt ≤ 0.86` and `2.506 ≤ (2π)^{1/2} ≤ 2.507`), the Mills ratio bound `Q(T) ≤ φ(T)/T` for
`T > 0`, and `φ' = -t φ`. -/

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

end


