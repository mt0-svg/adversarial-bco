/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.SrcTools
public import AdversarialBco.Poly.FreedmanProof
public import AdversarialBco.Poly.CoverProof

@[expose] public section

/-!
# Probabilistic tools: proofs

One theorem per `Prop` of `AdversarialBco/Poly/SrcTools.lean`, named after it in lower camel case (`gaussTailT1`,
`gaussTailT2`, `noiseTail`, `lemmaU`), and the leaves they are assembled from: the Gaussian tails and moments
(`gauss_tail_T1`, `gauss_moment_even`, `gauss_tail_T1'`), the moment generating function of a chi-square variable
(`chi2_mgf`), the tail of the noise (`noise_tail`), the truncation `E[Y Z] ≤ T E[Y] + E[Y²]^{1/2} E[Z² 1{Z > T}]^{1/2}`
(`lemmaTR1_main`), and Lemma U (`lemmaU_main`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## Leaves -/

theorem AdversarialBco.Poly.gauss_tail_T1 (b : ℝ) (hb : 0 ≤ b) :
    gaussianReal 0 1 (Set.Ici b) ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2) := by
  have hv : (1 : NNReal) ≠ 0 := by norm_num
  -- Express the measure as a lintegral
  rw [gaussianReal_apply 0 hv (Set.Ici b)]
  -- Goal: ∫⁻ x in Set.Ici b, gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2)
  -- Step 1: Translate the domain from Ici b to Ici 0
  have h_trans : (∫⁻ x in Set.Ici b, gaussianPDF 0 1 x) = (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 (b + x)) := by
    have h_meas : MeasurableSet (Set.Ici b) := measurableSet_Ici
    rw [← lintegral_indicator h_meas (gaussianPDF 0 1)]
    rw [← lintegral_indicator (measurableSet_Ici (a := (0 : ℝ))) (fun x => gaussianPDF 0 1 (b + x))]
    rw [← lintegral_add_right_eq_self (fun x => (Set.Ici b).indicator (gaussianPDF 0 1) x) b]
    refine lintegral_congr (fun x => ?_)
    simp [Set.indicator, Set.mem_Ici, add_comm]
  rw [h_trans]
  -- Goal: ∫⁻ x in Set.Ici 0, gaussianPDF 0 1 (b + x) ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2)
  -- Step 2: Pointwise inequality on the PDF
  have h_pdf_ineq (x : ℝ) (hx : x ∈ Set.Ici 0) : gaussianPDF 0 1 (b + x) ≤ gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) := by
    have h_def := gaussianPDF_def 0 1
    simp_rw [h_def]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_def' := gaussianPDFReal_def 0 1
    simp_rw [h_def']
    simp only [NNReal.coe_one, sub_zero, mul_one]
    have h_expand : -(b + x) ^ 2 / 2 = (-b ^ 2 / 2) + (-b * x) + (-x ^ 2 / 2) := by ring
    rw [h_expand, Real.exp_add, Real.exp_add]
    simpa [mul_assoc] using show ((√(2 * Real.pi))⁻¹ * (Real.exp (-b ^ 2 / 2) * (Real.exp (-b * x) * Real.exp (-x ^ 2 / 2)))) ≤
        ((√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) * Real.exp (-b ^ 2 / 2) from by
      have hL : (√(2 * Real.pi))⁻¹ * (Real.exp (-b ^ 2 / 2) * (Real.exp (-b * x) * Real.exp (-x ^ 2 / 2))) =
          ((√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2)) * Real.exp (-b * x) := by ring
      have hR : ((√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) * Real.exp (-b ^ 2 / 2) =
          (√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by ring
      rw [hL, hR]
      have hA : 0 ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by positivity
      have hC : Real.exp (-b * x) ≤ 1 := by
        rw [← Real.exp_zero]
        refine Real.exp_le_exp.mpr ?_
        have : -b * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
        exact this
      calc
        ((√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2)) * Real.exp (-b * x)
            ≤ ((√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2)) * 1 := by gcongr
        _ = (√(2 * Real.pi))⁻¹ * Real.exp (-b ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by ring
  -- Apply setLIntegral_mono' to use the pointwise inequality
  have h_meas_Ici0 : MeasurableSet (Set.Ici (0 : ℝ)) := measurableSet_Ici
  have h_mono : (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 (b + x)) ≤ (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (-b ^ 2 / 2))) := by
    refine setLIntegral_mono' h_meas_Ici0 (fun x hx => ?_)
    exact h_pdf_ineq x hx
  -- Step 3: Pull out the constant factor
  have h_const : (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (-b ^ 2 / 2))) =
      ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) * (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 x) := by
    rw [lintegral_mul_const _ (measurable_gaussianPDF 0 1), mul_comm]
  rw [h_const] at h_mono
  -- Step 4: Compute P(g ≥ 0) = 1/2
  have h_half : (∫⁻ x in Set.Ici 0, gaussianPDF 0 1 x) = ENNReal.ofReal (1/2) := by
    rw [← gaussianReal_apply 0 hv (Set.Ici 0)]
    -- Need to show: gaussianReal 0 1 (Set.Ici 0) = ENNReal.ofReal (1/2)
    set g := gaussianReal 0 1 (Set.Ici 0) with hg
    have h_symm : g = gaussianReal 0 1 (Set.Iic 0) := by
      have h_map : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
        simpa using gaussianReal_map_neg (μ := 0) (v := 1)
      calc
        g = gaussianReal 0 1 (Set.Ici 0) := rfl
        _ = ((gaussianReal 0 1).map (fun x => -x)) (Set.Ici 0) := by rw [h_map]
        _ = gaussianReal 0 1 ((fun x => -x) ⁻¹' Set.Ici 0) := by rw [Measure.map_apply (by fun_prop) (measurableSet_Ici)]
        _ = gaussianReal 0 1 (Set.Iic 0) := by simp
    have h_sum : g + gaussianReal 0 1 (Set.Iic 0) = 1 := by
      have h_cover : Set.Ici (0 : ℝ) ∪ Set.Iic (0 : ℝ) = Set.univ := by
        ext x; simp
      have h_inter : Set.Ici (0 : ℝ) ∩ Set.Iic (0 : ℝ) = {(0 : ℝ)} := by
        ext x; simp; exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => by subst h; exact ⟨le_refl 0, le_refl 0⟩⟩
      have h_singleton_null : gaussianReal 0 1 ({(0 : ℝ)} : Set ℝ) = 0 := by
        have h_null : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
        exact measure_singleton 0
      have h_meas_Ici : MeasurableSet (Set.Ici (0 : ℝ)) := measurableSet_Ici
      rw [← measure_union_add_inter' h_meas_Ici (Set.Iic 0)]
      rw [h_cover, h_inter, h_singleton_null]
      simp
    rw [← h_symm] at h_sum
    -- h_sum: g + g = 1
    have h_finite : g ≠ ∞ := measure_ne_top _ _
    have h_toReal : g.toReal = (1/2 : ℝ) := by
      have h_sum_toReal : (g + g).toReal = (1 : ENNReal).toReal := by rw [h_sum]
      rw [ENNReal.toReal_add h_finite h_finite, ENNReal.toReal_one] at h_sum_toReal
      linarith
    rw [← ENNReal.ofReal_toReal h_finite, h_toReal]
  rw [h_half] at h_mono
  -- Now h_mono: ∫⁻ x in Set.Ici 0, gaussianPDF 0 1 (b + x) ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) * ENNReal.ofReal (1/2)
  -- We need: ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2)
  -- Note: ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b)
  -- And Real.exp (-b^2/2) * (1/2) = Real.exp (-b^2/2) / 2
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-b ^ 2 / 2))] at h_mono
  -- h_mono: ... ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) * (1/2))
  -- Real.exp (-b^2/2) * (1/2) = Real.exp (-b^2/2) / 2
  have h_eq : Real.exp (-b ^ 2 / 2) * (1/2 : ℝ) = Real.exp (-b ^ 2 / 2) / 2 := by ring
  rw [h_eq] at h_mono
  exact h_mono

theorem AdversarialBco.Poly.gauss_tail_T1_abs (b : ℝ) (hb : 0 ≤ b) :
    gaussianReal 0 1 {x | b ≤ |x|} ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) := by
  have h_symm : gaussianReal 0 1 (Set.Iic (-b)) = gaussianReal 0 1 (Set.Ici b) := by
    calc
      gaussianReal 0 1 (Set.Iic (-b)) = gaussianReal 0 1 ((fun x => -x) ⁻¹' (Set.Ici b)) := by
        congr
        ext x
        simp
      _ = (Measure.map (fun x => -x) (gaussianReal 0 1)) (Set.Ici b) := by
        rw [MeasureTheory.Measure.map_apply measurable_neg measurableSet_Ici]
      _ = gaussianReal 0 1 (Set.Ici b) := by
        rw [ProbabilityTheory.gaussianReal_map_neg]
        simp
  have h_union : {x | b ≤ |x|} = Set.Ici b ∪ Set.Iic (-b) := by
    ext x
    simp [le_abs, Set.mem_Ici, Set.mem_Iic, Set.mem_union, le_neg]
  rw [h_union]
  have h_bound : gaussianReal 0 1 (Set.Ici b) ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2) :=
    AdversarialBco.Poly.gauss_tail_T1 b hb
  have h_exp_nonneg : 0 ≤ Real.exp (-b ^ 2 / 2) / 2 := by
    have : 0 ≤ Real.exp (-b ^ 2 / 2) := Real.exp_nonneg _
    nlinarith
  have h_add : (Real.exp (-b ^ 2 / 2) / 2) + (Real.exp (-b ^ 2 / 2) / 2) = Real.exp (-b ^ 2 / 2) := by ring
  calc
    gaussianReal 0 1 (Set.Ici b ∪ Set.Iic (-b)) ≤ gaussianReal 0 1 (Set.Ici b) + gaussianReal 0 1 (Set.Iic (-b)) :=
      MeasureTheory.measure_union_le _ _
    _ = gaussianReal 0 1 (Set.Ici b) + gaussianReal 0 1 (Set.Ici b) := by rw [h_symm]
    _ ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2) + ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2) :=
      add_le_add h_bound h_bound
    _ = ENNReal.ofReal ((Real.exp (-b ^ 2 / 2) / 2) + (Real.exp (-b ^ 2 / 2) / 2)) := by
      rw [ENNReal.ofReal_add h_exp_nonneg h_exp_nonneg]
    _ = ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) := by rw [h_add]

theorem AdversarialBco.Poly.gauss_moment_even (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) = ((2 * k - 1).doubleFactorial : ℝ) := by
  -- Key identity: (1/2)^(-(k + 1/2)) * (√Real.pi / 2^k) = √(2π)
  have h_key (k : ℕ) : ((1/2 : ℝ) ^ (-((k : ℝ) + 1/2)) * ((√Real.pi) / ((2 : ℝ) ^ (k : ℕ)))) = √(2 * Real.pi) := by
    have h1 : (1/2 : ℝ) ^ (-((k : ℝ) + 1/2)) = (2 : ℝ) ^ ((k : ℝ) + 1/2) := by
      calc
        (1/2 : ℝ) ^ (-((k : ℝ) + 1/2)) = ((2 : ℝ)⁻¹) ^ (-((k : ℝ) + 1/2)) := by norm_num
        _ = ((2 : ℝ) ^ (-1 : ℝ)) ^ (-((k : ℝ) + 1/2)) := by norm_num
        _ = (2 : ℝ) ^ ((-1 : ℝ) * (-((k : ℝ) + 1/2))) := by
          rw [Real.rpow_mul (show 0 ≤ (2 : ℝ) from by norm_num) (-1 : ℝ) (-((k : ℝ) + 1/2))]
        _ = (2 : ℝ) ^ ((k : ℝ) + 1/2) := by ring_nf
    rw [h1]
    have h2 : (2 : ℝ) ^ ((k : ℝ) + 1/2) = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1/2 : ℝ) := by
      rw [Real.rpow_add (show 0 < (2 : ℝ) from by norm_num) (k : ℝ) (1/2 : ℝ)]
    rw [h2]
    have h3 : (2 : ℝ) ^ (1/2 : ℝ) = √2 := by
      rw [Real.sqrt_eq_rpow]
    rw [h3]
    rw [← Real.rpow_natCast (2 : ℝ) k]
    have h_pos : (2 : ℝ) ^ (k : ℝ) > 0 := by
      apply Real.rpow_pos_of_pos; norm_num
    field_simp [h_pos.ne']
    rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) from by norm_num) Real.pi]

  have h_one_ne_zero : (1 : NNReal) ≠ 0 := by norm_num
  rw [integral_gaussianReal_eq_integral_smul h_one_ne_zero]
  rw [gaussianPDFReal_def 0 1]
  simp_rw [smul_eq_mul]
  simp
  -- Goal: ∫ x, (√Real.pi)⁻¹ * (√2)⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ (2 * k) = (2k-1)!!
  -- Factor out the constant (√Real.pi)⁻¹ * (√2)⁻¹ = (√(2π))⁻¹
  -- We need to rewrite inside the integral
  have h_factor : (fun (x : ℝ) => (√Real.pi)⁻¹ * (√2)⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ (2 * k)) =
      (fun (x : ℝ) => ((√Real.pi)⁻¹ * (√2)⁻¹) * (Real.exp (-x ^ 2 / 2) * x ^ (2 * k))) := by
    ext x; ring
  rw [h_factor]
  rw [integral_const_mul ((√Real.pi)⁻¹ * (√2)⁻¹)]
  -- Goal: (√Real.pi)⁻¹ * (√2)⁻¹ * ∫ x, Real.exp (-x ^ 2 / 2) * x ^ (2 * k) = (2k-1)!!

  -- Convert x^(2*k) to Real.rpow for compatibility
  -- We need to rewrite inside the integral
  have h_pow_eq : (fun (x : ℝ) => Real.exp (-x ^ 2 / 2) * x ^ (2 * k)) =
      (fun (x : ℝ) => Real.exp (-x ^ 2 / 2) * x ^ ((2 * k : ℕ) : ℝ)) := by
    ext x; rw [Real.rpow_natCast]
  rw [h_pow_eq]

  -- Now: (√(2π))⁻¹ * ∫ x, exp(-x^2/2) * x^((2k : ℝ)) = (2k-1)!!
  -- Let f(x) = exp(-x^2/2) * x^((2k : ℝ)). f is even: f(-x) = f(x)
  -- So ∫_ℝ f = 2 * ∫_{Ioi 0} f

  set f := (fun (x : ℝ) => Real.exp (-x ^ 2 / 2) * x ^ ((2 * k : ℕ) : ℝ)) with hf

  -- Lemma: f(|x|) = f(x) (since |x|^(2k) = x^(2k) and |x|^2 = x^2)
  have h_abs_eq : ∀ x, f |x| = f x := by
    intro x
    dsimp [f]
    have h_pow : |x| ^ ((2 * k : ℕ) : ℝ) = x ^ ((2 * k : ℕ) : ℝ) := by
      calc
        |x| ^ ((2 * k : ℕ) : ℝ) = (|x| ^ (2 : ℝ)) ^ (k : ℝ) := by
          rw [← Real.rpow_mul (abs_nonneg x) (2 : ℝ) (k : ℝ)]
          simp [Nat.cast_mul, mul_comm]
        _ = (x ^ (2 : ℝ)) ^ (k : ℝ) := by simp
        _ = x ^ ((2 * k : ℕ) : ℝ) := by
          calc
            (x ^ (2 : ℝ)) ^ (k : ℝ) = ((x ^ (2 : ℝ)) ^ (k : ℕ)) := by norm_cast
            _ = ((x ^ 2) ^ (k : ℕ)) := by simp
            _ = (x ^ (2 * k : ℕ)) := by rw [pow_mul]
            _ = x ^ ((2 * k : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    have h_sq : |x| ^ 2 = x ^ 2 := by simp
    -- Now rewrite using these equalities
    rw [h_pow]
    -- Need to rewrite |x|^2 to x^2 in the exp
    -- exp(-|x|^2/2) = exp(-x^2/2)
    simp [h_sq]

  -- Now use integral_comp_abs: ∫ x, f(|x|) = 2 * ∫ x in Ioi 0, f x
  -- Since f(|x|) = f(x), we have ∫ x, f(x) = 2 * ∫ x in Ioi 0, f(x)
  have h_int_full : ∫ x, f x = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
    calc
      ∫ x, f x = ∫ x, f |x| := by
        refine integral_congr_ae ?_
        filter_upwards [] with x
        rw [h_abs_eq x]
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by rw [integral_comp_abs]

  -- Now compute ∫ x in Ioi 0, f x using integral_rpow_mul_exp_neg_mul_rpow
  have h_int_Ioi : ∫ x in Set.Ioi (0 : ℝ), f x =
      ((1/2 : ℝ) ^ (-((2 * (k : ℝ)) + 1) / 2) * (1/2 : ℝ) * Real.Gamma (((2 * (k : ℝ)) + 1) / 2)) := by
    dsimp [f]
    have h_exp : (fun (x : ℝ) => Real.exp (-x ^ 2 / 2) * x ^ ((2 * k : ℕ) : ℝ)) =
        (fun (x : ℝ) => x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ (2 : ℝ))) := by
      ext x
      have h_exp_arg : -x ^ 2 / 2 = -(1/2 : ℝ) * x ^ (2 : ℝ) := by
        field_simp; simp
      rw [h_exp_arg, mul_comm]
    rw [h_exp]
    have hp : 0 < (2 : ℝ) := by norm_num
    have hq : -1 < ((2 * k : ℕ) : ℝ) := by
      have : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have h : (0 : ℝ) ≤ (2 * k : ℕ) := Nat.cast_nonneg _
      nlinarith
    have hb : 0 < (1/2 : ℝ) := by norm_num
    rw [integral_rpow_mul_exp_neg_mul_rpow hp hq hb]
    simp [Nat.cast_mul]

  -- Combine everything
  rw [h_int_full, h_int_Ioi]
  -- Goal: (√Real.pi)⁻¹ * (√2)⁻¹ * (2 * ((1/2)^(-(2k+1)/2) * (1/2) * Gamma((2k+1)/2))) = (2k-1)!!
  -- Simplify: 2 * (1/2) = 1
  ring_nf
  -- Goal: (√Real.pi)⁻¹ * (√2)⁻¹ * ((1/2)^(-(k + 1/2)) * Gamma(k + 1/2)) = (2k-1)!!
  -- But ring_nf rewrites -(k+1/2) as -1/2 - k and k+1/2 as 1/2 + k
  -- Also (2*k-1) as k*2-1
  -- Let's rewrite back to the expected form
  have h_exp1 : (-1/2 : ℝ) - (k : ℝ) = -((k : ℝ) + 1/2) := by ring
  have h_exp2 : (1/2 : ℝ) + (k : ℝ) = (k : ℝ) + 1/2 := by ring
  rw [h_exp1, h_exp2]
  -- Also fix the double factorial cast
  have h_df : ((k * 2 - 1).doubleFactorial : ℝ) = ((2 * k - 1).doubleFactorial : ℝ) := by
    simp [mul_comm]
  rw [h_df]

  -- Goal: (√Real.pi)⁻¹ * (√2)⁻¹ * ((1/2)^(-(k + 1/2)) * Gamma(k + 1/2)) = (2k-1)!!

  -- Use Real.Gamma_nat_add_half
  have hG := Real.Gamma_nat_add_half k
  -- hG: Gamma(k + 1/2) = (2k-1)!! * √Real.pi / 2^k
  rw [hG]
  -- Goal: (√Real.pi)⁻¹ * (√2)⁻¹ * ((1/2)^(-(k + 1/2)) * ((2k-1)!! * √Real.pi / 2^k)) = (2k-1)!!

  have h_temp := h_key k
  -- h_temp: (1/2)^(-(k + 1/2)) * (√Real.pi / 2^k) = √(2π)

  calc
    (√Real.pi)⁻¹ * (√2)⁻¹ * ((1/2 : ℝ) ^ (-((k : ℝ) + 1/2))) * (((2 * k - 1).doubleFactorial : ℝ) * √Real.pi / ((2 : ℝ) ^ (k : ℕ)))
        = ((√Real.pi)⁻¹ * (√2)⁻¹) * (((1/2 : ℝ) ^ (-((k : ℝ) + 1/2))) * (((2 * k - 1).doubleFactorial : ℝ) * √Real.pi / ((2 : ℝ) ^ (k : ℕ)))) := by ring
    _ = ((2 * k - 1).doubleFactorial : ℝ) * (((1/2 : ℝ) ^ (-((k : ℝ) + 1/2))) * (√Real.pi / ((2 : ℝ) ^ (k : ℕ)))) * ((√Real.pi)⁻¹ * (√2)⁻¹) := by ring
    _ = ((2 * k - 1).doubleFactorial : ℝ) * (√(2 * Real.pi)) * ((√Real.pi)⁻¹ * (√2)⁻¹) := by rw [h_temp]
    _ = ((2 * k - 1).doubleFactorial : ℝ) * ((√Real.pi)⁻¹ * (√2)⁻¹ * √(2 * Real.pi)) := by ring
    _ = ((2 * k - 1).doubleFactorial : ℝ) * 1 := by
      rw [show (√Real.pi)⁻¹ * (√2)⁻¹ * √(2 * Real.pi) = 1 by
        field_simp [show √Real.pi ≠ 0 from by positivity, show √2 ≠ 0 from by positivity, show √(2 * Real.pi) ≠ 0 from by positivity]
        rw [show √(2 * Real.pi) = √2 * √Real.pi by
          rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) from by norm_num) Real.pi, mul_comm]]
        ring]
    _ = ((2 * k - 1).doubleFactorial : ℝ) := by simp

theorem AdversarialBco.Poly.gauss_tail_T1' (k : ℕ) (b : ℝ) (_hk : 1 ≤ k) (hb : 0 ≤ b) :
    ∫ x, {x : ℝ | b < |x|}.indicator (fun x => x ^ (2 * k)) x ∂(gaussianReal 0 1) ≤
      Real.sqrt ((4 * k - 1).doubleFactorial) * Real.exp (-b ^ 2 / 4) := by
  set γ := gaussianReal 0 1 with hγ
  set A := {x : ℝ | b < |x|} with hA
  set f := fun x : ℝ => x ^ (2 * k) with hf
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    have h_abs_meas : Measurable (abs : ℝ → ℝ) := continuous_abs.measurable
    have h_Ioi_meas : MeasurableSet (Set.Ioi b) := measurableSet_Ioi
    exact h_abs_meas h_Ioi_meas
  have hf_nonneg : 0 ≤ᵐ[γ] f := by
    refine MeasureTheory.ae_of_all γ (fun x => ?_)
    dsimp [f]
    have h_even : Even (2 * k) := ⟨k, by ring⟩
    exact h_even.pow_nonneg x
  have h_indicator_nonneg : 0 ≤ᵐ[γ] A.indicator (fun _ => (1 : ℝ)) := by
    refine MeasureTheory.ae_of_all γ (fun x => ?_)
    exact Set.indicator_nonneg (fun _ _ => by norm_num) x
  have h_indicator_eq : A.indicator f = f * A.indicator (fun _ => (1 : ℝ)) := by
    ext x
    simp [Set.indicator]
  -- Cauchy-Schwarz (Holder with p = q = 2)
  have h_holder : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf_ae : MeasureTheory.AEStronglyMeasurable f γ :=
    (continuous_pow (2 * k)).aestronglyMeasurable
  -- MemLp for indicator (bounded function on finite measure)
  have h_indicator_memLp : MeasureTheory.MemLp (A.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal (2 : ℝ)) γ := by
    have h_const_memLp : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) γ :=
      MeasureTheory.memLp_const (c := (1 : ℝ)) (p := ENNReal.ofReal (2 : ℝ))
    exact h_const_memLp.indicator hA_meas
  -- MemLp for f: need Integrable (f^2) γ
  -- Use gauss_moment_even to show the integral is nonzero, hence integrable
  have h_f_sq_int : MeasureTheory.Integrable (fun x => f x ^ 2) γ := by
    dsimp [f]
    -- f x ^ 2 = (x^(2*k))^2 = x^(4*k)
    -- Use gauss_moment_even (2*k) which gives ∫ x^(4k) = (4k-1)!! > 0
    have h_moment := AdversarialBco.Poly.gauss_moment_even (2 * k)
    have h_moment_simp : ∫ x, x ^ (4 * k) ∂γ = ((4 * k - 1).doubleFactorial : ℝ) := by
      rw [hγ]
      simpa [show (2 * (2 * k) : ℕ) = 4 * k by ring] using h_moment
    have h_int_ne_zero : ∫ x, x ^ (4 * k) ∂γ ≠ 0 := by
      rw [h_moment_simp]
      have h_pos : 0 < ((4 * k - 1).doubleFactorial : ℝ) := by
        positivity
      linarith
    -- Need to relate ∫ (x^(2*k))^2 to ∫ x^(4*k)
    -- But we can avoid this by using the integral_congr_ae approach
    -- Actually, we need Integrable (fun x => (x^(2*k))^2) γ
    -- Since (x^(2*k))^2 = x^(4*k), and we know x^(4*k) is integrable
    -- We can use the equality to transfer integrability
    have h_eq : (fun x : ℝ => (x ^ (2 * k)) ^ 2) = fun x => x ^ (4 * k) := by
      ext x
      ring_nf
    rw [h_eq]
    exact MeasureTheory.Integrable.of_integral_ne_zero h_int_ne_zero
  have h_f_memLp : MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) γ := by
    have hp_eq : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    rw [hp_eq]
    rw [MeasureTheory.memLp_two_iff_integrable_sq hf_ae]
    exact h_f_sq_int
  -- Apply Cauchy-Schwarz
  have h_cauchy_schwarz : ∫ x, f x * A.indicator (fun _ => (1 : ℝ)) x ∂γ ≤
      (∫ x, f x ^ (2 : ℝ) ∂γ) ^ (1 / (2 : ℝ)) * (∫ x, (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂γ) ^ (1 / (2 : ℝ)) := by
    refine MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg h_holder hf_nonneg h_indicator_nonneg h_f_memLp h_indicator_memLp
  -- The goal is ∫ A.indicator f ≤ target
  -- Using h_indicator_eq, rewrite the goal to ∫ f * indicator ≤ target
  -- Then apply h_cauchy_schwarz.trans
  have h_goal_eq : (∫ x, A.indicator f x ∂γ) = (∫ x, f x * A.indicator (fun _ => (1 : ℝ)) x ∂γ) := by
    rw [h_indicator_eq]
    rfl
  rw [h_goal_eq]
  -- Now the goal is: ∫ f * indicator ≤ target
  -- h_cauchy_schwarz: ∫ f * indicator ≤ (∫ f^2)^(1/2) * (∫ indicator^2)^(1/2)
  -- So we apply transitivity
  refine h_cauchy_schwarz.trans ?_
  -- Simplify: (∫ f^2)^(1/2) = √(∫ f^2)
  have h_sqrt_f : (∫ x, f x ^ (2 : ℝ) ∂γ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, f x ^ (2 : ℝ) ∂γ) := by
    rw [Real.sqrt_eq_rpow]
  have h_sqrt_ind : (∫ x, (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂γ) ^ (1 / (2 : ℝ)) =
      Real.sqrt (∫ x, (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂γ) := by
    rw [Real.sqrt_eq_rpow]
  rw [h_sqrt_f, h_sqrt_ind]
  -- Compute ∫ f^2 = (4k-1)!! by gauss_moment_even at 2k
  have h_int_f_sq : (∫ x, f x ^ (2 : ℝ) ∂γ) = ((4 * k - 1).doubleFactorial : ℝ) := by
    dsimp [f]
    have h_moment : ∫ x, x ^ (2 * (2 * k)) ∂(gaussianReal 0 1) = ((2 * (2 * k) - 1).doubleFactorial : ℝ) :=
      AdversarialBco.Poly.gauss_moment_even (2 * k)
    calc
      ∫ x, (x ^ (2 * k)) ^ (2 : ℝ) ∂γ = ∫ x, (x ^ (2 * k)) ^ 2 ∂γ := by norm_num
      _ = ∫ x, x ^ (4 * k) ∂γ := by
        refine integral_congr_ae ?_
        filter_upwards [] with x
        ring_nf
      _ = ∫ x, x ^ (2 * (2 * k)) ∂γ := by ring
      _ = ∫ x, x ^ (2 * (2 * k)) ∂(gaussianReal 0 1) := by rw [hγ]
      _ = ((2 * (2 * k) - 1).doubleFactorial : ℝ) := h_moment
      _ = ((4 * k - 1).doubleFactorial : ℝ) := by ring
  rw [h_int_f_sq]
  -- Compute ∫ indicator^2 = ∫ indicator = γ.real A
  have h_int_indicator_sq : (∫ x, (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂γ) = γ.real A := by
    -- indicator^2 = indicator (since 1^2 = 1)
    have h_indicator_sq_eq : (fun x : ℝ => (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ)) = A.indicator (fun _ => (1 : ℝ)) := by
      ext x
      simp [Set.indicator]
    rw [h_indicator_sq_eq]
    -- ∫ indicator 1 = γ.real A
    exact MeasureTheory.integral_indicator_one hA_meas
  rw [h_int_indicator_sq]
  -- From gauss_tail_T1_abs: γ A ≤ ENNReal.ofReal (exp(-b^2/2))
  have h_tail_bound : γ A ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) := by
    have h_subset : A ⊆ {x | b ≤ |x|} := by
      intro x hx
      dsimp [A] at hx
      exact le_of_lt hx
    have h_measure_mono : γ A ≤ γ {x | b ≤ |x|} := measure_mono h_subset
    have h_tail_abs : γ {x | b ≤ |x|} ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) :=
      AdversarialBco.Poly.gauss_tail_T1_abs b hb
    exact le_trans h_measure_mono h_tail_abs
  -- Convert to real: γ.real A ≤ exp(-b^2/2)
  have h_real_bound : γ.real A ≤ Real.exp (-b ^ 2 / 2) := by
    rw [MeasureTheory.measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) h_tail_bound
  -- Now: √(γ.real A) ≤ √(exp(-b^2/2)) = exp(-b^2/4)
  have h_sqrt_bound : Real.sqrt (γ.real A) ≤ Real.sqrt (Real.exp (-b ^ 2 / 2)) :=
    Real.sqrt_le_sqrt h_real_bound
  have h_sqrt_exp : Real.sqrt (Real.exp (-b ^ 2 / 2)) = Real.exp (-b ^ 2 / 4) := by
    calc
      Real.sqrt (Real.exp (-b ^ 2 / 2)) = Real.exp ((-b ^ 2 / 2) / 2) := by rw [← Real.exp_half]
      _ = Real.exp (-b ^ 2 / 4) := by ring
  rw [h_sqrt_exp] at h_sqrt_bound
  -- Now we have: √(γ.real A) ≤ exp(-b^2/4)
  -- Multiply both sides by √((4k-1)!!) (which is ≥ 0)
  have h_nonneg_sqrt : 0 ≤ Real.sqrt ((4 * k - 1).doubleFactorial : ℝ) := Real.sqrt_nonneg _
  nlinarith

theorem AdversarialBco.Poly.gauss_mgf_sq (a : ℝ) (ha : a < 1 / 2) :
    ∫ x, Real.exp (a * x ^ 2) ∂(gaussianReal 0 1) = 1 / Real.sqrt (1 - 2 * a) := by
  have hb_pos : 0 < 1/2 - a := by linarith
  have h_one_ne_zero : (1 : NNReal) ≠ 0 := by norm_num
  have hpos : 0 < 1 - 2 * a := by linarith
  calc
    ∫ x, Real.exp (a * x ^ 2) ∂(gaussianReal 0 1)
        = ∫ x, gaussianPDFReal 0 1 x • Real.exp (a * x ^ 2) := by
      rw [integral_gaussianReal_eq_integral_smul h_one_ne_zero]
    _ = ∫ x, ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) • Real.exp (a * x ^ 2) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [gaussianPDFReal_def 0 1]
      simp [sub_zero]
    _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-(x ^ 2) / 2) * Real.exp (a * x ^ 2)) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      simp [smul_eq_mul, mul_assoc]
    _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((a - 1/2) * x ^ 2) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [← Real.exp_add]
      ring_nf
    _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2 - a) * x ^ 2) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring_nf
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, Real.exp (-(1/2 - a) * x ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2 - a)) := by
      rw [integral_gaussian (1/2 - a)]
    _ = 1 / Real.sqrt (1 - 2 * a) := by
      have hsqrt_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      calc
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2 - a))
            = Real.sqrt (Real.pi / (1/2 - a)) / Real.sqrt (2 * Real.pi) := by
          field_simp [hsqrt_ne_zero]
        _ = Real.sqrt ((Real.pi / (1/2 - a)) / (2 * Real.pi)) := by
          rw [Real.sqrt_div (by positivity : 0 ≤ Real.pi / (1/2 - a)) _]
        _ = Real.sqrt (1 / (2 * (1/2 - a))) := by
          field_simp
        _ = Real.sqrt (1 / (1 - 2 * a)) := by
          ring_nf
        _ = Real.sqrt 1 / Real.sqrt (1 - 2 * a) := by
          rw [Real.sqrt_div (show 0 ≤ (1 : ℝ) from by norm_num) _]
        _ = 1 / Real.sqrt (1 - 2 * a) := by norm_num


theorem AdversarialBco.Poly.chi2_mgf (d : ℕ) (a : ℝ) (ha : a < 1 / 2) :
    ∫ W, Real.exp (a * ‖W‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (1 / Real.sqrt (1 - 2 * a)) ^ d := by
  calc
    ∫ W, Real.exp (a * ‖W‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ W, Real.exp (a * ‖W‖ ^ 2) ∂((Measure.pi fun _ : Fin d => gaussianReal 0 1).map (WithLp.toLp 2)) := by
      rw [← map_pi_eq_stdGaussian]
    _ = ∫ x : Fin d → ℝ, Real.exp (a * ‖(WithLp.toLp 2) x‖ ^ 2) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
      simpa [MeasurableEquiv.coe_toLp] using integral_map_equiv (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
        (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (fun (W : EuclideanSpace ℝ (Fin d)) => Real.exp (a * ‖W‖ ^ 2))
    _ = ∫ x : Fin d → ℝ, Real.exp (a * (∑ i, (x i) ^ 2)) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
      refine integral_congr_ae ?_
      refine ae_of_all _ ?_
      intro x
      simp only
      rw [EuclideanSpace.real_norm_sq_eq]
    _ = ∫ x : Fin d → ℝ, (∏ i : Fin d, Real.exp (a * (x i) ^ 2)) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
      refine integral_congr_ae ?_
      refine ae_of_all _ ?_
      intro x
      simp only
      rw [Finset.mul_sum, Real.exp_sum]
    _ = ∏ i : Fin d, ∫ x, Real.exp (a * x ^ 2) ∂(gaussianReal 0 1) := by
      rw [integral_fintype_prod_eq_prod (fun (i : Fin d) (t : ℝ) => Real.exp (a * t ^ 2))]
    _ = ∏ i : Fin d, (1 / Real.sqrt (1 - 2 * a)) := by
      simp_rw [AdversarialBco.Poly.gauss_mgf_sq a ha]
    _ = (1 / Real.sqrt (1 - 2 * a)) ^ d := by
      simp

theorem AdversarialBco.Poly.chi2_mgf_le_two (d : ℕ) (hd : 1 ≤ d) :
    (1 / Real.sqrt (1 - 2 * (3 / (8 * d)))) ^ d ≤ 2 := by
  -- Let x = 3/(4d); then 1 - 2*(3/(8*d)) = 1 - x
  set x := (3 : ℝ) / (4 * (d : ℝ)) with hx_def
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.one_pos.trans_le hd
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hxpos : 0 < x := by
    dsimp [x]
    refine div_pos (by norm_num) (by nlinarith)
  have hxle : x ≤ 3/4 := by
    dsimp [x]
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h4pos : (0 : ℝ) < 4 := by norm_num
    have h4le : (4 : ℝ) ≤ 4 * (d : ℝ) := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num) h4pos h4le
  have h_one_minus_x_pos : 0 < 1 - x := by linarith
  have h_one_minus_x_nonneg : 0 ≤ 1 - x := by linarith
  -- Bernoulli inequality: (1 - x)^d ≥ 1 - d*x = 1/4
  have h_bern : (1 - x)^(d : ℕ) ≥ 1/4 := by
    have hnegx : (-2 : ℝ) ≤ -x := by linarith
    have h_bern_raw := one_add_mul_le_pow hnegx (d : ℕ)
    -- h_bern_raw : 1 + (d : ℝ) * (-x) ≤ (1 + (-x))^(d : ℕ)
    have h_left : 1 + (d : ℝ) * (-x) = (1/4 : ℝ) := by
      dsimp [x]
      field_simp [hd_ne_zero]
      ring
    have h_right : (1 + (-x))^(d : ℕ) = (1 - x)^(d : ℕ) := by ring
    rw [h_left, h_right] at h_bern_raw
    exact h_bern_raw
  -- Let s = Real.sqrt (1 - x)
  set s := Real.sqrt (1 - x) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - x := Real.sq_sqrt h_one_minus_x_nonneg
  -- Key: (1/s)^d = 1/(s^d)
  have h_pow_div : (1 / s)^(d : ℕ) = 1 / (s^(d : ℕ)) :=
    one_div_pow s (d : ℕ)
  -- Need: 1/(s^d) ≤ 2, i.e., s^d ≥ 1/2
  -- We know (s^d)^2 = (s^2)^d = (1-x)^d ≥ 1/4 = (1/2)^2
  -- Since s^d ≥ 0, we get s^d ≥ 1/2
  have h_sd_sq_ge : (s^(d : ℕ))^2 ≥ ((1/2 : ℝ)^2) := by
    calc
      (s^(d : ℕ))^2 = (s^(d : ℕ)) * (s^(d : ℕ)) := by ring
      _ = s^((d : ℕ) + (d : ℕ)) := by rw [pow_add]
      _ = s^(2 * (d : ℕ)) := by ring
      _ = (s^2)^(d : ℕ) := by rw [pow_mul]
      _ = (1 - x)^(d : ℕ) := by rw [hs_sq]
      _ ≥ (1/4 : ℝ) := h_bern
      _ = ((1/2 : ℝ)^2) := by norm_num
  have h_sd_nonneg : 0 ≤ s^(d : ℕ) := pow_nonneg hs_nonneg _
  -- From (s^d)^2 ≥ (1/2)^2 and s^d ≥ 0, 1/2 ≥ 0, we get s^d ≥ 1/2
  have h_sd_ge_half : s^(d : ℕ) ≥ 1/2 := by
    have h_abs := (sq_le_sq.mp h_sd_sq_ge)
    -- h_abs : |1/2| ≤ |s^(d : ℕ)|
    have h_abs_half : |(1/2 : ℝ)| = 1/2 := abs_of_pos (by norm_num : 0 < (1/2 : ℝ))
    have h_abs_sd : |s^(d : ℕ)| = s^(d : ℕ) := abs_of_nonneg h_sd_nonneg
    rw [h_abs_half, h_abs_sd] at h_abs
    exact h_abs
  -- Rewrite the goal using x
  have h_goal_eq : (1 / Real.sqrt (1 - 2 * (3 / (8 * (d : ℝ))))) ^ (d : ℕ) = (1 / s) ^ (d : ℕ) := by
    dsimp [s, x]
    have h_inner : 1 - 2 * (3 / (8 * (d : ℝ))) = 1 - x := by
      dsimp [x]
      ring
    rw [h_inner]
  rw [h_goal_eq, h_pow_div]
  have h_pos : 0 < s^(d : ℕ) := by
    have hs_pos : 0 < s := Real.sqrt_pos.mpr h_one_minus_x_pos
    exact pow_pos hs_pos _
  -- 1/(s^d) ≤ 2 because s^d ≥ 1/2
  have h_one_div_half : (1 : ℝ) / (1/2 : ℝ) = 2 := by norm_num
  have h_temp := (one_div_le_one_div h_pos (by norm_num : 0 < (1/2 : ℝ))).mpr h_sd_ge_half
  -- h_temp : 1 / (s ^ d) ≤ 1 / (1/2)
  simpa [h_one_div_half] using h_temp

theorem AdversarialBco.Poly.gauss_tail_T2 (d : ℕ) (t : ℝ) (hd : 1 ≤ d) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-(3 * t / (8 * d)))) := by
  -- Let a = 3/(8d); then 0 < a ≤ 3/8 < 1/2 since d ≥ 1.
  set a := (3 : ℝ) / ((8 : ℝ) * (d : ℝ)) with ha_def
  have ha_pos : 0 < a := by
    refine div_pos (by norm_num) ?_
    have hd' : (0 : ℝ) < d := by
      have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    nlinarith
  have ha_lt_half : a < 1/2 := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hineq : (8 : ℝ) * (1 : ℝ) ≤ (8 : ℝ) * (d : ℝ) := by nlinarith
    calc
      a = (3 : ℝ) / ((8 : ℝ) * (d : ℝ)) := rfl
      _ ≤ (3 : ℝ) / ((8 : ℝ) * (1 : ℝ)) := by
        gcongr
      _ = 3/8 := by ring
      _ < 1/2 := by norm_num
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  -- The function f(W) = exp(a * ‖W‖²) is nonnegative.
  set f := fun (W : EuclideanSpace ℝ (Fin d)) => Real.exp (a * ‖W‖ ^ 2) with hf_def
  have hf_nonneg : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (Fin d))] f := by
    refine ae_of_all _ (fun W => ?_)
    exact Real.exp_pos _ |>.le
  -- f is integrable: its integral equals a positive real number (by chi2_mgf).
  have hf_int : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_int_eq : ∫ W, f W ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (1 / Real.sqrt (1 - 2 * a)) ^ d :=
      chi2_mgf d a ha_lt_half
    have h_pos : 0 < (1 / Real.sqrt (1 - 2 * a)) ^ d := by
      have h_sqrt_pos : 0 < Real.sqrt (1 - 2 * a) := Real.sqrt_pos.mpr (by nlinarith)
      have h_base_pos : 0 < 1 / Real.sqrt (1 - 2 * a) := div_pos (by norm_num) h_sqrt_pos
      exact pow_pos h_base_pos d
    have h_int_ne_zero : ∫ W, f W ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ 0 := by
      rw [h_int_eq]
      exact ne_of_gt h_pos
    exact Integrable.of_integral_ne_zero h_int_ne_zero
  -- Apply Markov's inequality with ε = exp(a*t).
  set ε := Real.exp (a * t) with hε_def
  have hε_pos : 0 < ε := Real.exp_pos _
  have h_markov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε
  -- h_markov : ε * μ.real {x | ε ≤ f x} ≤ ∫ f
  -- Note that ε ≤ f x ↔ exp(a*t) ≤ exp(a * ‖x‖²) ↔ a*t ≤ a * ‖x‖² ↔ t ≤ ‖x‖² (since a > 0).
  have h_set_eq : {W | ε ≤ f W} = {W | t ≤ ‖W‖ ^ 2} := by
    ext W
    simp [hf_def, hε_def, Real.exp_le_exp]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have h_int_val : ∫ W, f W ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (1 / Real.sqrt (1 - 2 * a)) ^ d :=
    chi2_mgf d a ha_lt_half
  have h_int_le_two : (1 / Real.sqrt (1 - 2 * a)) ^ d ≤ 2 := chi2_mgf_le_two d hd
  -- Combine: ε * μ.real {t ≤ ‖W‖²} ≤ (1/√(1-2a))^d ≤ 2
  rw [h_set_eq, h_int_val] at h_markov
  have h_bound : ε * (stdGaussian (EuclideanSpace ℝ (Fin d))).real {W | t ≤ ‖W‖ ^ 2} ≤ 2 := by
    linarith
  -- Therefore μ.real {t ≤ ‖W‖²} ≤ 2 / ε = 2 * exp(-a*t)
  have h_measReal_le : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {W | t ≤ ‖W‖ ^ 2} ≤
      2 * Real.exp (-(a * t)) := by
    calc
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real {W | t ≤ ‖W‖ ^ 2} =
          (ε * (stdGaussian (EuclideanSpace ℝ (Fin d))).real {W | t ≤ ‖W‖ ^ 2}) / ε := by
        field_simp [ne_of_gt hε_pos]
      _ ≤ 2 / ε := div_le_div_of_nonneg_right h_bound (by positivity)
      _ = 2 * (1 / ε) := by ring
      _ = 2 * Real.exp (-(a * t)) := by
        rw [hε_def, Real.exp_neg, div_eq_mul_inv, one_mul]
  -- Now convert from measureReal to ENNReal measure.
  have h_meas_ne_top : stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} ≠ ⊤ :=
    measure_ne_top _ _
  -- First prove the inequality with a, then substitute back
  have h_goal : (stdGaussian (EuclideanSpace ℝ (Fin d))) {W | t ≤ ‖W‖ ^ 2} ≤
      ENNReal.ofReal (2 * Real.exp (-(a * t))) := by
    rw [ENNReal.le_ofReal_iff_toReal_le h_meas_ne_top (by positivity)]
    rw [← measureReal_def]
    exact h_measReal_le
  -- Now substitute back a = 3/(8d)
  rw [ha_def] at h_goal
  -- Simplify the expression
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_inv_mul] using h_goal

theorem AdversarialBco.Poly.noise_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → ℝ) (_hε : AEMeasurable ε μ) (hi : Integrable (fun ω => Real.exp (ε ω ^ 2)) μ)
    (h2 : ∫ ω, Real.exp (ε ω ^ 2) ∂μ ≤ 2) (b : ℝ) (hb : 0 ≤ b) :
    μ {ω | b ≤ |ε ω|} ≤ ENNReal.ofReal (2 * Real.exp (-b ^ 2)) := by
  set f := fun ω => Real.exp (ε ω ^ 2) with hf
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [] with ω
    exact Real.exp_nonneg _
  have hf_int : Integrable f μ := hi
  set c := Real.exp (b ^ 2) with hc
  have hc_pos : 0 < c := Real.exp_pos (b ^ 2)
  have h_subset : {ω | b ≤ |ε ω|} ⊆ {ω | c ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h_sq : b ^ 2 ≤ (ε ω) ^ 2 := by
      have h1 : -|ε ω| ≤ b := by
        have h_abs_nonneg : 0 ≤ |ε ω| := abs_nonneg _
        linarith
      calc
        b ^ 2 ≤ |ε ω| ^ 2 := sq_le_sq' h1 hω
        _ = (ε ω) ^ 2 := by simp
    dsimp [c, f]
    exact Real.exp_le_exp.mpr h_sq
  have h_meas_le : μ {ω | b ≤ |ε ω|} ≤ μ {ω | c ≤ f ω} :=
    MeasureTheory.measure_mono h_subset
  have h_fin : μ {ω | c ≤ f ω} ≠ ∞ := MeasureTheory.measure_ne_top μ _
  have h_markov : c * μ.real {ω | c ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int c
  have h_bound : μ.real {ω | c ≤ f ω} ≤ 2 / c := by
    rw [le_div_iff₀ hc_pos]
    simpa [mul_comm] using h_markov.trans h2
  have h_div_eq : 2 / c = 2 * Real.exp (-b ^ 2) := by
    dsimp [c]
    rw [div_eq_mul_inv, Real.exp_neg]
  calc
    μ {ω | b ≤ |ε ω|} ≤ μ {ω | c ≤ f ω} := h_meas_le
    _ = ENNReal.ofReal (μ.real {ω | c ≤ f ω}) := by
      rw [← ENNReal.ofReal_toReal h_fin, measureReal_def]
    _ ≤ ENNReal.ofReal (2 / c) := ENNReal.ofReal_le_ofReal h_bound
    _ = ENNReal.ofReal (2 * Real.exp (-b ^ 2)) := by rw [h_div_eq]

theorem AdversarialBco.Poly.lemmaTR1_main {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y Z : Ω → ℝ) (T : ℝ) (hY : ∀ ω, 0 ≤ Y ω) (hZ : ∀ ω, 0 ≤ Z ω) (hT : 0 ≤ T) (hY2 : MemLp Y 2 μ)
    (hZ2 : MemLp Z 2 μ) :
    ∫ ω, Y ω * Z ω ∂μ ≤ T * ∫ ω, Y ω ∂μ +
      Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) * Real.sqrt (∫ ω, {ω | T < Z ω}.indicator (fun ω => Z ω ^ 2) ω ∂μ) := by
  have hY_ae : 0 ≤ᵐ[μ] Y := ae_of_all μ hY
  have hZ_ae : 0 ≤ᵐ[μ] Z := ae_of_all μ hZ
  have hY_int : Integrable Y μ := hY2.integrable (by norm_num : 1 ≤ (2 : ENNReal))
  have hZ_int : Integrable Z μ := hZ2.integrable (by norm_num : 1 ≤ (2 : ENNReal))
  have hY_sq_int : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ := hZ2.integrable_sq
  have hY_ae_meas : AEStronglyMeasurable Y μ := hY2.aestronglyMeasurable
  have hZ_ae_meas : AEStronglyMeasurable Z μ := hZ2.aestronglyMeasurable
  set s := {ω | T < Z ω} with hs
  have h_set_nullMeasurable : NullMeasurableSet s μ :=
    (aestronglyMeasurable_const (b := T)).nullMeasurableSet_lt hZ_ae_meas
  have h_indicator_ae_meas : AEStronglyMeasurable (s.indicator Z) μ :=
    hZ_ae_meas.indicator₀ h_set_nullMeasurable
  have h_indicator_nonneg : 0 ≤ᵐ[μ] (s.indicator Z) := by
    refine ae_of_all μ (fun ω => ?_)
    exact Set.indicator_nonneg (fun a _ => hZ a) _
  -- MemLp for the indicator using the bound |indicator Z| ≤ |Z|
  have h_indicator_memLp : MemLp (s.indicator Z) 2 μ := by
    refine MemLp.mono hZ2 h_indicator_ae_meas ?_
    refine ae_of_all μ (fun ω => ?_)
    have hZ_nonneg : 0 ≤ Z ω := hZ ω
    have hind_le_Z : s.indicator Z ω ≤ Z ω := Set.indicator_le_self' (fun x _ => hZ x) ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun a _ => hZ a) _),
      abs_of_nonneg hZ_nonneg]
    exact hind_le_Z
  have h_indicator_sq_eq : (fun ω => (s.indicator Z ω) ^ 2) = s.indicator (fun ω => Z ω ^ 2) := by
    ext ω
    by_cases h : ω ∈ s
    · simp [h, s]
    · simp [h]
  have h_indicator_sq_int : Integrable (fun ω => (s.indicator Z ω) ^ 2) μ := by
    rw [h_indicator_sq_eq]
    exact hZ_sq_int.indicator₀ h_set_nullMeasurable
  -- pointwise inequality: Y * Z ≤ T * Y + Y * (indicator Z)
  have h_pointwise : ∀ ω, Y ω * Z ω ≤ T * Y ω + Y ω * (s.indicator Z ω) := by
    intro ω
    by_cases h : T < Z ω
    · have hpos : 0 ≤ T * Y ω := mul_nonneg hT (hY ω)
      have hmem : ω ∈ s := by rwa [hs]
      have hind_eq : s.indicator Z ω = Z ω := (Set.indicator_of_mem hmem Z)
      rw [hind_eq]
      nlinarith
    · have hle : Z ω ≤ T := by linarith
      have hind_le : s.indicator Z ω ≤ Z ω := Set.indicator_le_self' (fun x _ => hZ x) ω
      have hle2 : Y ω * Z ω ≤ T * Y ω :=
        calc
          Y ω * Z ω ≤ Y ω * T := mul_le_mul_of_nonneg_left hle (hY ω)
          _ = T * Y ω := mul_comm _ _
      have hle3 : T * Y ω ≤ T * Y ω + Y ω * (s.indicator Z ω) := by
        have h_nonneg : 0 ≤ Y ω * (s.indicator Z ω) :=
          mul_nonneg (hY ω) (Set.indicator_nonneg (fun a _ => hZ a) _)
        nlinarith
      nlinarith
  have hYZ_int : Integrable (fun ω => Y ω * Z ω) μ := hY2.integrable_mul hZ2
  have hTY_int : Integrable (fun ω => T * Y ω) μ := by
    simpa [mul_comm] using hY_int.mul_const T
  have hYind_int : Integrable (fun ω => Y ω * (s.indicator Z ω)) μ := by
    refine Integrable.mono hYZ_int (hY_ae_meas.mul h_indicator_ae_meas) ?_
    refine ae_of_all μ (fun ω => ?_)
    have hY_nonneg : 0 ≤ Y ω := hY ω
    have hZ_nonneg : 0 ≤ Z ω := hZ ω
    have hind_le_Z : s.indicator Z ω ≤ Z ω := Set.indicator_le_self' (fun x _ => hZ x) ω
    have h_nonneg_prod : 0 ≤ Y ω * Z ω := mul_nonneg hY_nonneg hZ_nonneg
    have h_nonneg_ind : 0 ≤ Y ω * (s.indicator Z ω) :=
      mul_nonneg hY_nonneg (Set.indicator_nonneg (fun a _ => hZ a) _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nonneg_prod, abs_of_nonneg h_nonneg_ind]
    exact mul_le_mul_of_nonneg_left hind_le_Z hY_nonneg
  -- integrate the pointwise inequality
  have h_int_ineq : ∫ ω, Y ω * Z ω ∂μ ≤ T * ∫ ω, Y ω ∂μ + ∫ ω, Y ω * (s.indicator Z ω) ∂μ := by
    calc
      ∫ ω, Y ω * Z ω ∂μ ≤ ∫ ω, (T * Y ω + Y ω * (s.indicator Z ω)) ∂μ :=
        integral_mono_ae hYZ_int (hTY_int.add hYind_int) (ae_of_all μ h_pointwise)
      _ = (∫ ω, T * Y ω ∂μ) + (∫ ω, Y ω * (s.indicator Z ω) ∂μ) := by
        rw [integral_add hTY_int hYind_int]
      _ = T * (∫ ω, Y ω ∂μ) + (∫ ω, Y ω * (s.indicator Z ω) ∂μ) := by
        rw [integral_const_mul T Y]
  -- Cauchy-Schwarz inequality for the second term
  have h_cauchy : ∫ ω, Y ω * (s.indicator Z ω) ∂μ ≤
      Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) * Real.sqrt (∫ ω, (s.indicator Z ω) ^ 2 ∂μ) := by
    have h_memLp_Y : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY2
    have h_memLp_ind : MemLp (s.indicator Z) (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using h_indicator_memLp
    have h_cs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hY_ae h_indicator_nonneg h_memLp_Y h_memLp_ind
    -- h_cs : ∫ Y * (indicator Z) ≤ (∫ Y^2)^(1/2) * (∫ (indicator Z)^2)^(1/2)
    simpa [Real.sqrt_eq_rpow] using h_cs
  -- relate (indicator Z)^2 to indicator (Z^2)
  have h_sqrt_ind_sq : Real.sqrt (∫ ω, (s.indicator Z ω) ^ 2 ∂μ) =
      Real.sqrt (∫ ω, s.indicator (fun ω => Z ω ^ 2) ω ∂μ) := by
    rw [h_indicator_sq_eq]
  rw [h_sqrt_ind_sq] at h_cauchy
  -- combine
  linarith

theorem AdversarialBco.Poly.lemmaU_main {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {ι : Type*} (C : Finset ι) (Z : ι → ℕ → Ω → ℝ)
    (hZm : ∀ c ∈ C, ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z c t)) (hZi : ∀ c ∈ C, ∀ t, Integrable (Z c t) μ)
    (hZ2 : ∀ c ∈ C, ∀ t, Integrable (fun ω => Z c t ω ^ 2) μ) (hZ0 : ∀ c ∈ C, ∀ t, μ[Z c t | ℱ t] =ᵐ[μ] 0)
    (n : ℕ) (κ δ : ℝ) (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
      AdversarialBco.Poly.fkBound μ ℱ (Z c) κ (n * C.card) δ t ω < |∑ s ∈ Finset.range t, Z c s ω|} ≤
      ENNReal.ofReal δ := by
  by_cases hC : C = ∅
  · subst hC; simp
  have hC_nonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC
  by_cases hn : n = 0
  · subst hn; simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  set N := n * C.card with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]
    exact mul_pos hn_pos (Finset.card_pos.mpr hC_nonempty)
  have hN_pos' : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  set δ₁ := δ / (N : ℝ) with hδ₁_def
  have hδ₁_pos : 0 < δ₁ := div_pos hδ0 hN_pos'
  have hδ₁_le_one : δ₁ ≤ 1 := by
    rw [hδ₁_def]
    refine (div_le_one hN_pos').mpr ?_
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt hN_pos
    linarith
  set E := fun (c : ι) (t : ℕ) (ω : Ω) =>
    AdversarialBco.Poly.fkBound μ ℱ (Z c) κ (n * C.card) δ t ω < |∑ s ∈ Finset.range t, Z c s ω| with hE_def
  set S := {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n, E c t ω} with hS_def
  set T := ⋃ p ∈ (C ×ˢ Finset.Icc 1 n), E p.1 p.2 with hT_def
  have hST : S ⊆ T := by
    intro ω hω
    rw [hS_def, Set.mem_ofPred_eq] at hω
    rcases hω with ⟨c, hc, t, ht, hω'⟩
    rw [hT_def]
    refine Set.mem_iUnion.mpr ⟨(c, t), ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hc, ht⟩, hω'⟩
  have hμT : μ T ≤ ENNReal.ofReal δ := by
    rw [hT_def]
    have h_union : μ (⋃ p ∈ (C ×ˢ Finset.Icc 1 n), E p.1 p.2) ≤
        ((C ×ˢ Finset.Icc 1 n).card : ENNReal) * ENNReal.ofReal δ₁ := by
      refine AdversarialBco.Poly.union_bound_finset μ (C ×ˢ Finset.Icc 1 n) (fun p => E p.1 p.2)
        (ENNReal.ofReal δ₁) ?_
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rcases p with ⟨c, t⟩
      have h_fk := AdversarialBco.Poly.freedmanFK μ ℱ (Z c)
        (hZm c hp1) (hZi c hp1) (hZ2 c hp1)
        (fun _ => t) (MeasureTheory.isStoppingTime_const ℱ t)
        n (by
          intro ω
          have ht_le_n : t ≤ n := (Finset.mem_Icc.mp hp2).2
          exact ht_le_n)
        (by
          intro s
          have h_drift := hZ0 c hp1 s
          filter_upwards [h_drift] with ω h_eq
          intro _h_lt
          exact h_eq)
        κ δ₁ hκ hδ₁_pos hδ₁_le_one
      -- h_fk gives an inequality for the FreedmanFK event; we need to relate it to E c t
      -- The two events differ only in the log term: 4*max/δ₁ vs 4*N*max/δ
      -- Since δ₁ = δ/N, these are equal by algebra
      have h_fk' : μ {ω | E c t ω} ≤ ENNReal.ofReal δ₁ := by
        have h_eq_set : {ω | E c t ω} = {ω |
            3 * Real.sqrt (AdversarialBco.Poly.predVar μ ℱ (Z c) t ω *
              Real.log (4 * max (AdversarialBco.Poly.absMax (fun t ω => κ * Z c t ω) t ω)
                (κ * Real.sqrt (AdversarialBco.Poly.predVar μ ℱ (Z c) t ω)) / δ₁))
            + 2 * (AdversarialBco.Poly.absMax (fun t ω => κ * Z c t ω) t ω / κ) *
              Real.log (4 * max (AdversarialBco.Poly.absMax (fun t ω => κ * Z c t ω) t ω)
                (κ * Real.sqrt (AdversarialBco.Poly.predVar μ ℱ (Z c) t ω)) / δ₁)
            < |∑ s ∈ Finset.range t, Z c s ω|} := by
          ext ω
          dsimp [E, hE_def, AdversarialBco.Poly.fkBound]
          rw [hδ₁_def, hN_def, Nat.cast_mul]
          have hn_ne_zero : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne.symm
          have hcard_ne_zero : (C.card : ℝ) ≠ 0 := by
            exact mod_cast (Finset.card_pos.mpr hC_nonempty).ne.symm
          field_simp [hn_ne_zero, hcard_ne_zero]
        rw [h_eq_set]
        exact h_fk
      exact h_fk'
    have h_card : ((C ×ˢ Finset.Icc 1 n).card : ENNReal) = (N : ENNReal) := by
      rw [Finset.card_product, Nat.card_Icc]
      have h_sub : n + 1 - 1 = n := by omega
      rw [h_sub, hN_def, mul_comm]
    have h_mul : (N : ENNReal) * ENNReal.ofReal δ₁ = ENNReal.ofReal δ := by
      rw [hδ₁_def]
      have h_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast hN_pos.le
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul h_nonneg]
      field_simp [show (N : ℝ) ≠ 0 from by exact_mod_cast hN_pos.ne.symm]
    rw [h_card, h_mul] at h_union
    exact h_union
  have hμS : μ S ≤ μ T := measure_mono hST
  rw [hS_def] at hμS
  exact hμS.trans hμT

namespace AdversarialBco.Poly

universe u

/-! ## Assemblies -/

theorem gaussTailT1 : GaussTailT1 := fun b hb => ⟨gauss_tail_T1 b hb, gauss_tail_T1_abs b hb⟩

theorem gaussTailT2 : GaussTailT2 := fun d t hd => gauss_tail_T2 d t hd

theorem noiseTail : NoiseTail.{u} := fun μ _ ε hε hi h2 b hb => noise_tail μ ε hε hi h2 b hb

theorem lemmaU : LemmaU.{u} := fun μ _ ℱ _ C Z hZm hZi hZ2 hZ0 n κ δ hκ hδ0 hδ1 =>
  lemmaU_main μ ℱ C Z hZm hZi hZ2 hZ0 n κ δ hκ hδ0 hδ1

end AdversarialBco.Poly
