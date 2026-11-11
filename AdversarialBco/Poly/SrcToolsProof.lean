/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.SrcTools
public import AdversarialBco.Poly.FreedmanProof
public import AdversarialBco.Poly.CoverProof
public import AdversarialBco.Poly.TruncProof

@[expose] public section

/-!
# The probabilistic tools of the decay-free route: proofs

One theorem per `Prop` of `AdversarialBco/Poly/SrcTools.lean`, named after it in lower camel case, and the leaves they
are assembled from.
`cond_cauchy_schwarz` comes from the quadratic `E[(U - qV)² | m] ≥ 0` at every rational `q` and
`quad_disc_of_rat` (`AdversarialBco/Poly/TruncProof.lean`), and `lemmaTR2_cond`, which is `lemmaTR1_cond` at `Y²`,
`Z²`, `T²` (for `Z, T ≥ 0`, `T² < Z²` iff `T < Z`).
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

theorem AdversarialBco.Poly.cond_cauchy_schwarz {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (U V : Ω → ℝ) (hU : MemLp U 2 μ)
    (hV : MemLp V 2 μ) :
    ∀ᵐ ω ∂μ, μ[fun ω => U ω * V ω | m] ω ≤
      Real.sqrt (μ[fun ω => U ω ^ 2 | m] ω) * Real.sqrt (μ[fun ω => V ω ^ 2 | m] ω) := by
  have hUU : Integrable (fun ω => U ω ^ 2) μ := hU.integrable_sq
  have hVV : Integrable (fun ω => V ω ^ 2) μ := hV.integrable_sq
  have hUV : Integrable (fun ω => U ω * V ω) μ := hU.integrable_mul hV
  have h_quad (q : ℚ) : ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω => U ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[fun ω => U ω * V ω | m] ω
      + (q : ℝ) ^ 2 * μ[fun ω => V ω ^ 2 | m] ω := by
    have h_nonneg : 0 ≤ᵐ[μ] μ[fun ω => (U ω - (q : ℝ) * V ω) ^ 2 | m] :=
      condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
    have h_i2 : Integrable (fun ω => (-2 * (q : ℝ)) * (U ω * V ω)) μ := hUV.const_mul _
    have h_i3 : Integrable (fun ω => (q : ℝ) ^ 2 * V ω ^ 2) μ := hVV.const_mul _
    have h_eq : (fun ω => (U ω - (q : ℝ) * V ω) ^ 2) =
        (fun ω => U ω ^ 2) + ((fun ω => (-2 * (q : ℝ)) * (U ω * V ω)) + fun ω => (q : ℝ) ^ 2 * V ω ^ 2) := by
      ext ω; simp only [Pi.add_apply]; ring
    have h_add := condExp_add hUU (h_i2.add h_i3) m
    have h_add2 := condExp_add h_i2 h_i3 m
    have h_s2 : μ[fun ω => (-2 * (q : ℝ)) * (U ω * V ω) | m] =ᵐ[μ] fun ω => (-2 * (q : ℝ)) * μ[fun ω => U ω * V ω | m] ω :=
      condExp_smul (μ := μ) (-2 * (q : ℝ)) (fun ω => U ω * V ω) m
    have h_s3 : μ[fun ω => (q : ℝ) ^ 2 * V ω ^ 2 | m] =ᵐ[μ] fun ω => (q : ℝ) ^ 2 * μ[fun ω => V ω ^ 2 | m] ω :=
      condExp_smul (μ := μ) ((q : ℝ) ^ 2) (fun ω => V ω ^ 2) m
    rw [h_eq] at h_nonneg
    filter_upwards [h_nonneg, h_add, h_add2, h_s2, h_s3] with ω h0 h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.add_apply] at h0
    rw [h3, h4, Pi.zero_apply] at h0
    linarith
  have h_all : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 ≤ μ[fun ω => U ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[fun ω => U ω * V ω | m] ω
      + (q : ℝ) ^ 2 * μ[fun ω => V ω ^ 2 | m] ω := ae_all_iff.mpr h_quad
  have hU0 : 0 ≤ᵐ[μ] μ[fun ω => U ω ^ 2 | m] := condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
  have hV0 : 0 ≤ᵐ[μ] μ[fun ω => V ω ^ 2 | m] := condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
  filter_upwards [h_all, hU0, hV0] with ω hq hu hv
  have hd := AdversarialBco.Poly.quad_disc_of_rat _ _ _ hv hq
  calc μ[fun ω => U ω * V ω | m] ω ≤ |μ[fun ω => U ω * V ω | m] ω| := le_abs_self _
    _ = Real.sqrt ((μ[fun ω => U ω * V ω | m] ω) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (μ[fun ω => U ω ^ 2 | m] ω * μ[fun ω => V ω ^ 2 | m] ω) := Real.sqrt_le_sqrt hd
    _ = _ := Real.sqrt_mul hu _

theorem AdversarialBco.Poly.lemmaTR2_main {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y Z : Ω → ℝ) (T : ℝ) (hY : ∀ ω, 0 ≤ Y ω) (hZ : ∀ ω, 0 ≤ Z ω) (hT : 0 ≤ T) (hY4 : MemLp Y 4 μ)
    (hZ4 : MemLp Z 4 μ) :
    ∫ ω, Y ω ^ 2 * Z ω ^ 2 ∂μ ≤ T ^ 2 * ∫ ω, Y ω ^ 2 ∂μ +
      Real.sqrt (∫ ω, Y ω ^ 4 ∂μ) * Real.sqrt (∫ ω, {ω | T < Z ω}.indicator (fun ω => Z ω ^ 4) ω ∂μ) := by
  -- get AEStronglyMeasurable versions
  have hY_ae : AEStronglyMeasurable Y μ := hY4.aestronglyMeasurable
  have hZ_ae : AEStronglyMeasurable Z μ := hZ4.aestronglyMeasurable
  -- the set s = {Z > T} is null-measurable
  let s : Set Ω := {ω | T < Z ω}
  have hs_nullMeasurable : NullMeasurableSet s μ :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hZ_ae
  -- integrability of Y^4 and Z^4
  have hY4_int : Integrable (fun ω => Y ω ^ 4) μ := by
    have h := hY4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have h_eq : (fun ω => ‖Y ω‖ ^ 4) = (fun ω => Y ω ^ 4) := by
      ext ω; simp [hY ω]
    rwa [h_eq] at h
  have hZ4_int : Integrable (fun ω => Z ω ^ 4) μ := by
    have h := hZ4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have h_eq : (fun ω => ‖Z ω‖ ^ 4) = (fun ω => Z ω ^ 4) := by
      ext ω; simp [hZ ω]
    rwa [h_eq] at h
  -- Y^2 is in L^2 (via memLp_two_iff_integrable_sq)
  have hYsq_ae : AEStronglyMeasurable (fun ω => Y ω ^ 2) μ :=
    hY_ae.pow 2
  have hYsq_memLp : MemLp (fun ω => Y ω ^ 2) (ENNReal.ofReal 2) μ := by
    have h : MemLp (fun ω => Y ω ^ 2) 2 μ := by
      rw [memLp_two_iff_integrable_sq hYsq_ae]
      have : (fun ω => (Y ω ^ 2) ^ 2) = (fun ω => Y ω ^ 4) := by
        ext ω; ring
      rw [this]
      exact hY4_int
    simpa using h
  -- Z^2 is in L^2
  have hZsq_ae : AEStronglyMeasurable (fun ω => Z ω ^ 2) μ :=
    hZ_ae.pow 2
  have hZsq_memLp : MemLp (fun ω => Z ω ^ 2) (ENNReal.ofReal 2) μ := by
    have h : MemLp (fun ω => Z ω ^ 2) 2 μ := by
      rw [memLp_two_iff_integrable_sq hZsq_ae]
      have : (fun ω => (Z ω ^ 2) ^ 2) = (fun ω => Z ω ^ 4) := by
        ext ω; ring
      rw [this]
      exact hZ4_int
    simpa using h
  -- the indicator of Z^2 on s is in L^2
  have h_indicator_ae : AEStronglyMeasurable (s.indicator (fun ω => Z ω ^ 2)) μ :=
    hZsq_ae.indicator₀ hs_nullMeasurable
  have h_indicator_memLp : MemLp (s.indicator (fun ω => Z ω ^ 2)) (ENNReal.ofReal 2) μ := by
    have h : MemLp (s.indicator (fun ω => Z ω ^ 2)) 2 μ := by
      rw [memLp_two_iff_integrable_sq h_indicator_ae]
      have h_eq : (fun ω => (s.indicator (fun ω => Z ω ^ 2) ω) ^ 2) = s.indicator (fun ω => Z ω ^ 4) := by
        ext ω
        by_cases h : ω ∈ s
        · rw [Set.indicator_of_mem h]
          have hT : T < Z ω := by simpa [s] using h
          rw [Set.indicator_of_mem (by simpa [s] using hT)]
          ring
        · rw [Set.indicator_apply]
          simp [h]
      rw [h_eq]
      exact hZ4_int.indicator₀ hs_nullMeasurable
    simpa using h
  -- nonnegativity conditions for Cauchy-Schwarz
  have hYsq_nonneg : 0 ≤ᵐ[μ] (fun ω => Y ω ^ 2) :=
    ae_of_all μ (fun ω => pow_two_nonneg (Y ω))
  have h_indicator_nonneg : 0 ≤ᵐ[μ] (s.indicator (fun ω => Z ω ^ 2)) := by
    have hZsq_nonneg_ae : ∀ ω, 0 ≤ Z ω ^ 2 := by
      intro ω; exact pow_two_nonneg (Z ω)
    have h_pointwise : ∀ ω, 0 ≤ s.indicator (fun ω => Z ω ^ 2) ω :=
      Set.indicator_nonneg (fun ω hω => hZsq_nonneg_ae ω)
    exact ae_of_all μ h_pointwise
  -- pointwise inequality
  have h_pointwise : ∀ ω, Y ω ^ 2 * Z ω ^ 2 ≤ T ^ 2 * Y ω ^ 2 + Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω := by
    intro ω
    by_cases h : Z ω ≤ T
    · -- then indicator is 0, and Z^2 ≤ T^2
      have h_indicator : s.indicator (fun ω => Z ω ^ 2) ω = 0 := by
        rw [Set.indicator_apply]
        simp [s, h]
      have hZsq_le_Tsq : Z ω ^ 2 ≤ T ^ 2 := by
        have hZω_nonneg : 0 ≤ Z ω := hZ ω
        nlinarith
      rw [h_indicator]
      nlinarith
    · -- then Z ω > T, indicator = Z^2
      have h_indicator : s.indicator (fun ω => Z ω ^ 2) ω = Z ω ^ 2 := by
        rw [Set.indicator_apply]
        simp [s, h]
      rw [h_indicator]
      nlinarith
  -- HolderTriple instance for ENNReal.ofReal 2
  have : (ENNReal.ofReal 2).HolderTriple (ENNReal.ofReal 2) 1 := by
    have h : ENNReal.ofReal 2 = (2 : ENNReal) := by norm_num
    rw [h]
    infer_instance
  -- integrability for integral_mono
  have h_int_Y2Z2 : Integrable (fun ω => Y ω ^ 2 * Z ω ^ 2) μ :=
    hYsq_memLp.integrable_mul hZsq_memLp
  have h_int_T2Y2 : Integrable (fun ω => T ^ 2 * Y ω ^ 2) μ := by
    have : MemLp (fun ω => T ^ 2 * Y ω ^ 2) (ENNReal.ofReal 2) μ :=
      hYsq_memLp.const_mul (T ^ 2)
    have h_one_le : (1 : ENNReal) ≤ ENNReal.ofReal 2 := by
      norm_num
    exact this.integrable h_one_le
  have h_int_cross : Integrable (fun ω => Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω) μ :=
    hYsq_memLp.integrable_mul h_indicator_memLp
  have h_int_sum : Integrable (fun ω => T ^ 2 * Y ω ^ 2 + Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω) μ :=
    h_int_T2Y2.add h_int_cross
  -- integrate the pointwise inequality
  have h_int_ineq : ∫ ω, Y ω ^ 2 * Z ω ^ 2 ∂μ ≤ ∫ ω, T ^ 2 * Y ω ^ 2 + Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω ∂μ :=
    integral_mono h_int_Y2Z2 h_int_sum h_pointwise
  -- split the integral
  have h_int_split : ∫ ω, T ^ 2 * Y ω ^ 2 + Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω ∂μ =
      T ^ 2 * ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω ∂μ := by
    rw [integral_add h_int_T2Y2 h_int_cross, integral_const_mul (T ^ 2) (fun ω => Y ω ^ 2)]
  rw [h_int_split] at h_int_ineq
  -- apply Cauchy-Schwarz to the cross term
  have h_cauchy : ∫ ω, Y ω ^ 2 * (s.indicator (fun ω => Z ω ^ 2)) ω ∂μ ≤
      Real.sqrt (∫ ω, (Y ω ^ 2) ^ 2 ∂μ) * Real.sqrt (∫ ω, (s.indicator (fun ω => Z ω ^ 2) ω) ^ 2 ∂μ) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hYsq_nonneg h_indicator_nonneg
      hYsq_memLp h_indicator_memLp
    -- h : ∫ f*g ≤ (∫ f^(2:ℝ))^(1/2) * (∫ g^(2:ℝ))^(1/2)
    -- goal : ∫ f*g ≤ Real.sqrt (∫ f^2) * Real.sqrt (∫ g^2)
    -- Note: (Y^2)^(2:ℝ) = (Y^2)^2 and Real.sqrt x = x^(1/2)
    have h1 : (fun ω => (Y ω ^ 2) ^ (2 : ℝ)) = (fun ω => (Y ω ^ 2) ^ 2) := by
      ext ω; norm_num
    have h2 : (fun ω => (s.indicator (fun ω => Z ω ^ 2) ω) ^ (2 : ℝ)) = (fun ω => (s.indicator (fun ω => Z ω ^ 2) ω) ^ 2) := by
      ext ω; norm_num
    -- rewrite the exponents
    rw [h1, h2] at h
    -- now h : ∫ f*g ≤ (∫ f^2)^(1/2) * (∫ g^2)^(1/2)
    -- Real.sqrt_eq_rpow : Real.sqrt x = x ^ (1/2)
    -- So we need to rewrite ^(1/2) to Real.sqrt
    simpa [Real.sqrt_eq_rpow] using h
  -- relate (Y^2)^2 to Y^4 and (indicator Z^2)^2 to indicator Z^4
  have h_sq1 : (fun ω => (Y ω ^ 2) ^ 2) = (fun ω => Y ω ^ 4) := by
    ext ω; ring
  have h_sq2 : (fun ω => (s.indicator (fun ω => Z ω ^ 2) ω) ^ 2) = s.indicator (fun ω => Z ω ^ 4) := by
    ext ω
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h]
      have hT : T < Z ω := by simpa [s] using h
      rw [Set.indicator_of_mem (by simpa [s] using hT)]
      ring
    · rw [Set.indicator_apply]
      simp [h]
  rw [h_sq1, h_sq2] at h_cauchy
  -- combine everything
  linarith

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

theorem AdversarialBco.Poly.lemmaTR1_cond {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (Y Z : Ω → ℝ) (T : ℝ) (hY : ∀ ω, 0 ≤ Y ω)
    (hZ : ∀ ω, 0 ≤ Z ω) (hT : 0 ≤ T) (hY2 : MemLp Y 2 μ) (hZ2 : MemLp Z 2 μ) :
    ∀ᵐ ω ∂μ, μ[fun ω => Y ω * Z ω | m] ω ≤ T * μ[Y | m] ω +
      Real.sqrt (μ[fun ω => Y ω ^ 2 | m] ω) *
        Real.sqrt (μ[{ω | T < Z ω}.indicator (fun ω => Z ω ^ 2) | m] ω) := by
  -- integrability facts from MemLp
  have hY_int : Integrable Y μ := hY2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hZ_int : Integrable Z μ := hZ2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hYsq_int : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have hZsq_int : Integrable (fun ω => Z ω ^ 2) μ := hZ2.integrable_sq
  have hYZ_int : Integrable (fun ω => Y ω * Z ω) μ := hY2.integrable_mul hZ2
  -- define A = {ω | T < Z ω} and V = indicator A Z
  let A : Set Ω := {ω | T < Z ω}
  set V := A.indicator Z with hV_def
  have hA_nullMeasurable : @NullMeasurableSet Ω m0 A μ := by
    have hZ_aemeasurable : AEMeasurable[m0] Z μ := hZ2.aestronglyMeasurable.aemeasurable
    have hT_aemeasurable : AEMeasurable[m0] (fun _ : Ω => T) μ := by
      apply aemeasurable_const
    exact nullMeasurableSet_lt hT_aemeasurable hZ_aemeasurable
  have hV_memLp : MemLp V 2 μ := by
    have h_ae : AEStronglyMeasurable[m0] V μ :=
      hZ2.aestronglyMeasurable.indicator₀ hA_nullMeasurable
    have h_bound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ Z ω := by
      filter_upwards with ω
      dsimp [V]
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        rw [abs_of_nonneg (hZ ω)]
      · rw [Set.indicator_apply]
        simp [h]
        exact hZ ω
    exact hZ2.mono' h_ae h_bound
  have hYV_int : Integrable (fun ω => Y ω * V ω) μ := hY2.integrable_mul hV_memLp
  -- pointwise inequality: Y * Z ≤ T * Y + Y * V
  have h_pointwise : ∀ ω, Y ω * Z ω ≤ T * Y ω + Y ω * V ω := by
    intro ω
    dsimp [V, A]
    by_cases h : T < Z ω
    · simp [h]
      nlinarith [hY ω, hZ ω, hT]
    · simp [h]
      nlinarith [hY ω, hZ ω, hT]
  -- apply conditional expectation monotonicity
  have hTY_int : Integrable (fun ω => T * Y ω) μ := hY_int.smul (T : ℝ)
  have hTYV_int : Integrable (fun ω => T * Y ω + Y ω * V ω) μ := hTY_int.add hYV_int
  have h_cond_ineq : μ[fun ω => Y ω * Z ω | m] ≤ᵐ[μ] μ[fun ω => T * Y ω + Y ω * V ω | m] :=
    condExp_mono hYZ_int hTYV_int (by
      filter_upwards with ω
      exact h_pointwise ω)
  -- split the RHS using condExp_add and condExp_smul
  have h_split : μ[fun ω => T * Y ω + Y ω * V ω | m] =ᵐ[μ]
      (fun ω => T * μ[Y | m] ω) + μ[fun ω => Y ω * V ω | m] := by
    calc
      μ[fun ω => T * Y ω + Y ω * V ω | m] =ᵐ[μ] μ[fun ω => T * Y ω | m] + μ[fun ω => Y ω * V ω | m] :=
        condExp_add hTY_int hYV_int m
      _ =ᵐ[μ] (fun ω => T * μ[Y | m] ω) + μ[fun ω => Y ω * V ω | m] := by
        have h := condExp_smul (μ := μ) (m₀ := m0) (T : ℝ) Y m
        exact h.add (by rfl)
  -- apply Cauchy-Schwarz to the second term
  have h_cauchy : μ[fun ω => Y ω * V ω | m] ≤ᵐ[μ]
      (fun ω => Real.sqrt (μ[fun ω => Y ω ^ 2 | m] ω) *
        Real.sqrt (μ[fun ω => V ω ^ 2 | m] ω)) := by
    have h_cs := AdversarialBco.Poly.cond_cauchy_schwarz μ m hm Y V hY2 hV_memLp
    filter_upwards [h_cs] with ω h
    exact h
  -- relate V^2 to indicator A (Z^2)
  have h_Vsq_eq : (fun ω => V ω ^ 2) =ᵐ[μ] (fun ω => (A.indicator fun ω => Z ω ^ 2) ω) := by
    filter_upwards with ω
    dsimp [V, A]
    by_cases h : T < Z ω
    · simp [h]
    · simp [h]
  have h_cond_Vsq : μ[fun ω => V ω ^ 2 | m] =ᵐ[μ] μ[A.indicator fun ω => Z ω ^ 2 | m] :=
    condExp_congr_ae h_Vsq_eq
  -- combine everything
  filter_upwards [h_cond_ineq, h_split, h_cauchy, h_cond_Vsq] with ω h_ineq h_split' h_cauchy' h_Vsq
  have h_mid : μ[fun ω => Y ω * Z ω | m] ω ≤ T * μ[Y | m] ω + μ[fun ω => Y ω * V ω | m] ω := by
    calc
      μ[fun ω => Y ω * Z ω | m] ω ≤ μ[fun ω => T * Y ω + Y ω * V ω | m] ω := h_ineq
      _ = ((fun ω => T * μ[Y | m] ω) + μ[fun ω => Y ω * V ω | m]) ω := by rw [h_split']
      _ = T * μ[Y | m] ω + μ[fun ω => Y ω * V ω | m] ω := rfl
  calc
    μ[fun ω => Y ω * Z ω | m] ω ≤ T * μ[Y | m] ω + μ[fun ω => Y ω * V ω | m] ω := h_mid
    _ ≤ T * μ[Y | m] ω +
        Real.sqrt (μ[fun ω => Y ω ^ 2 | m] ω) * Real.sqrt (μ[fun ω => V ω ^ 2 | m] ω) := by
      nlinarith
    _ = T * μ[Y | m] ω +
        Real.sqrt (μ[fun ω => Y ω ^ 2 | m] ω) * Real.sqrt (μ[A.indicator fun ω => Z ω ^ 2 | m] ω) := by
      rw [h_Vsq]

theorem AdversarialBco.Poly.lemmaTR2_cond {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (Y Z : Ω → ℝ) (T : ℝ) (hY : ∀ ω, 0 ≤ Y ω)
    (hZ : ∀ ω, 0 ≤ Z ω) (hT : 0 ≤ T) (hY4 : MemLp Y 4 μ) (hZ4 : MemLp Z 4 μ) :
    ∀ᵐ ω ∂μ, μ[fun ω => Y ω ^ 2 * Z ω ^ 2 | m] ω ≤ T ^ 2 * μ[fun ω => Y ω ^ 2 | m] ω +
      Real.sqrt (μ[fun ω => Y ω ^ 4 | m] ω) *
        Real.sqrt (μ[{ω | T < Z ω}.indicator (fun ω => Z ω ^ 4) | m] ω) := by
  have hsq : ∀ X : Ω → ℝ, MemLp X 4 μ → MemLp (fun ω => X ω ^ 2) 2 μ := by
    intro X hX
    rw [memLp_two_iff_integrable_sq (f := fun ω => X ω ^ 2) (hX.aestronglyMeasurable.pow 2)]
    have h := hX.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    refine h.congr (ae_of_all μ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  have h1 := AdversarialBco.Poly.lemmaTR1_cond μ m hm (fun ω => Y ω ^ 2) (fun ω => Z ω ^ 2) (T ^ 2)
    (fun ω => sq_nonneg _) (fun ω => sq_nonneg _) (sq_nonneg _) (hsq Y hY4) (hsq Z hZ4)
  have hY4eq : (fun ω => (Y ω ^ 2) ^ 2) = fun ω => Y ω ^ 4 := by ext ω; ring
  have hZ4eq : {ω | T ^ 2 < Z ω ^ 2}.indicator (fun ω => (Z ω ^ 2) ^ 2) =
      {ω | T < Z ω}.indicator (fun ω => Z ω ^ 4) := by
    ext ω
    have hiff : T ^ 2 < Z ω ^ 2 ↔ T < Z ω := pow_lt_pow_iff_left₀ hT (hZ ω) two_ne_zero
    by_cases h : T < Z ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | T ^ 2 < Z ω ^ 2} from hiff.mpr h),
        Set.indicator_of_mem (show ω ∈ {ω | T < Z ω} from h)]
      ring
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | T ^ 2 < Z ω ^ 2} from fun h' => h (hiff.mp h')),
        Set.indicator_of_notMem (show ω ∉ {ω | T < Z ω} from h)]
  simp only [hY4eq, hZ4eq] at h1
  exact h1

theorem AdversarialBco.Poly.one_le_absMax {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    1 ≤ AdversarialBco.Poly.absMax X k ω := by
  rw [AdversarialBco.Poly.absMax]
  rw [Finset.le_fold_max]
  left
  exact le_refl 1

theorem AdversarialBco.Poly.absMax_le {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (B : ℝ) (hB : 1 ≤ B)
    (h : ∀ s < k, |X s ω| ≤ B) : AdversarialBco.Poly.absMax X k ω ≤ B := by
  dsimp [AdversarialBco.Poly.absMax]
  rw [Finset.fold_max_le]
  refine ⟨hB, ?_⟩
  intro x hx
  have hx' : x < k := Finset.mem_range.1 hx
  exact h x hx'

theorem AdversarialBco.Poly.fkBound_caps {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (N δ Vbar Rbar : ℝ) (t : ℕ) (ω : Ω) (hN : 1 ≤ N) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hV0 : 0 ≤ Vbar) (hR : 0 < Rbar) (hV : AdversarialBco.Poly.predVar μ ℱ X t ω ≤ Vbar)
    (hX : ∀ s < t, |X s ω| ≤ Rbar) :
    AdversarialBco.Poly.fkBound μ ℱ X (1 / Rbar) N δ t ω ≤
      3 * Real.sqrt (Vbar * (Real.log (4 * N / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)))) +
        2 * Rbar * (Real.log (4 * N / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar))) := by
  set κ := 1 / Rbar with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact div_pos (by norm_num) hR
  have hκnonneg : 0 ≤ κ := hκpos.le
  set V := AdversarialBco.Poly.predVar μ ℱ X t ω with hVdef
  set A := AdversarialBco.Poly.absMax (fun s ω => κ * X s ω) t ω with hAdef
  set M := max A (κ * Real.sqrt V) with hMdef
  set l := Real.log (4 * N * M / δ) with hldef
  set lbar := Real.log (4 * N / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)) with hlbardef
  have hA_one_le : 1 ≤ A :=
    AdversarialBco.Poly.one_le_absMax (fun s ω => κ * X s ω) t ω
  have hA_le_one : A ≤ 1 := by
    refine AdversarialBco.Poly.absMax_le (fun s ω => κ * X s ω) t ω 1 (by norm_num) ?_
    intro s hs
    have hXs := hX s hs
    rw [abs_mul, abs_of_nonneg hκnonneg, hκdef]
    calc
      (1 / Rbar) * |X s ω| ≤ (1 / Rbar) * Rbar := by gcongr
      _ = 1 := by field_simp [hR.ne.symm]
  have hA_eq_one : A = 1 := by linarith
  have hA_div_κ_eq_Rbar : A / κ = Rbar := by
    rw [hA_eq_one, hκdef]
    field_simp [hR.ne.symm]
  have hM_ge_one : 1 ≤ M := by
    rw [hMdef]
    exact le_trans hA_one_le (le_max_left _ _)
  have hM_pos : 0 < M := by linarith
  have hM_le_target : M ≤ max 1 (Real.sqrt Vbar / Rbar) := by
    rw [hMdef, hA_eq_one, hκdef]
    -- Goal: max 1 ((1/Rbar) * √V) ≤ max 1 (√Vbar / Rbar)
    have h_sqrtV_le_sqrtVbar : Real.sqrt V ≤ Real.sqrt Vbar := Real.sqrt_le_sqrt hV
    have h_mul : (1 / Rbar) * Real.sqrt V ≤ Real.sqrt Vbar / Rbar := by
      calc
        (1 / Rbar) * Real.sqrt V ≤ (1 / Rbar) * Real.sqrt Vbar := by gcongr
        _ = Real.sqrt Vbar / Rbar := by ring
    exact max_le_max (by rfl) h_mul
  have hpos_4N_div_δ : 0 < 4 * N / δ := by
    have h4Npos : 0 < 4 * N := by nlinarith
    exact div_pos h4Npos hδ0
  have hpos_factor1 : 4 * N / δ ≠ 0 := by linarith
  have hpos_factor2 : M ≠ 0 := by linarith
  have hl_nonneg : 0 ≤ l := by
    rw [hldef]
    refine Real.log_nonneg ?_
    have hpos_4NM : 0 < 4 * N * M := by positivity
    have hineq : 1 ≤ 4 * N * M / δ := by
      have h_one_div_δ_ge_one : 1 ≤ 1 / δ := by
        field_simp [hδ0.ne.symm]
        linarith
      have hNM_ge_one : 1 ≤ N * M := by
        nlinarith
      have h_4NM_ge_one : 1 ≤ 4 * N * M := by nlinarith
      calc
        1 ≤ 4 * N * M := h_4NM_ge_one
        _ = (4 * N * M) * 1 := by ring
        _ ≤ (4 * N * M) * (1 / δ) := mul_le_mul_of_nonneg_left h_one_div_δ_ge_one (by positivity)
        _ = 4 * N * M / δ := by ring
    exact hineq
  have hl_le_lbar : l ≤ lbar := by
    rw [hldef, hlbardef]
    have h_eq : 4 * N * M / δ = (4 * N / δ) * M := by ring
    rw [h_eq]
    rw [Real.log_mul hpos_factor1 hpos_factor2]
    have h_logM_le : Real.log M ≤ Real.log (max 1 (Real.sqrt Vbar / Rbar)) :=
      Real.log_le_log hM_pos hM_le_target
    gcongr
  have h_sqrt_ineq : Real.sqrt (V * l) ≤ Real.sqrt (Vbar * lbar) := by
    apply Real.sqrt_le_sqrt
    calc
      V * l ≤ Vbar * l := mul_le_mul_of_nonneg_right hV hl_nonneg
      _ ≤ Vbar * lbar := mul_le_mul_of_nonneg_left hl_le_lbar hV0
  have h_mul_ineq : 2 * Rbar * l ≤ 2 * Rbar * lbar :=
    mul_le_mul_of_nonneg_left hl_le_lbar (by linarith)
  -- Unfold fkBound and the abbreviations, then combine using the inequalities
  simpa [AdversarialBco.Poly.fkBound, V, A, M, l, lbar, hA_div_κ_eq_Rbar] using
    add_le_add (by gcongr) h_mul_ineq

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

theorem AdversarialBco.Poly.lemmaUCaps_main {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {ι : Type*} (C : Finset ι) (Z : ι → ℕ → Ω → ℝ)
    (hZm : ∀ c ∈ C, ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z c t)) (hZi : ∀ c ∈ C, ∀ t, Integrable (Z c t) μ)
    (hZ2 : ∀ c ∈ C, ∀ t, Integrable (fun ω => Z c t ω ^ 2) μ) (hZ0 : ∀ c ∈ C, ∀ t, μ[Z c t | ℱ t] =ᵐ[μ] 0)
    (n : ℕ) (Vbar Rbar δ : ℝ) (hV0 : 0 ≤ Vbar) (hR : 0 < Rbar) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
      AdversarialBco.Poly.predVar μ ℱ (Z c) t ω ≤ Vbar ∧ (∀ s < t, |Z c s ω| ≤ Rbar) ∧
      3 * Real.sqrt (Vbar * (Real.log (4 * n * C.card / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)))) +
        2 * Rbar * (Real.log (4 * n * C.card / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)))
        < |∑ s ∈ Finset.range t, Z c s ω|} ≤ ENNReal.ofReal δ := by
  have hκ : 0 < 1 / Rbar := one_div_pos.mpr hR
  refine (measure_mono ?_).trans (AdversarialBco.Poly.lemmaU_main μ ℱ C Z hZm hZi hZ2 hZ0 n (1 / Rbar) δ hκ hδ0 hδ1)
  intro ω hω
  rcases hω with ⟨c, hc, t, ht, hV, hX, h_bound⟩
  have ht_mem := Finset.mem_Icc.mp ht
  rcases ht_mem with ⟨ht1, ht2⟩
  have hcard : 1 ≤ C.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨c, hc⟩)
  have hN : 1 ≤ (n : ℝ) * (C.card : ℝ) := by
    have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact mod_cast ht1
    have hcard' : (1 : ℝ) ≤ (C.card : ℝ) := by exact mod_cast hcard
    have ht2' : (t : ℝ) ≤ (n : ℝ) := by exact mod_cast ht2
    nlinarith
  have h_fkBound := AdversarialBco.Poly.fkBound_caps μ ℱ (Z c) ((n : ℝ) * (C.card : ℝ)) δ Vbar Rbar t ω hN hδ0 hδ1 hV0 hR hV hX
  have h_lt : fkBound μ ℱ (Z c) (1 / Rbar) ((n : ℝ) * (C.card : ℝ)) δ t ω < |∑ s ∈ Finset.range t, Z c s ω| := by
    calc
      fkBound μ ℱ (Z c) (1 / Rbar) ((n : ℝ) * (C.card : ℝ)) δ t ω ≤
        3 * Real.sqrt (Vbar * (Real.log (4 * ((n : ℝ) * (C.card : ℝ)) / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)))) +
          2 * Rbar * (Real.log (4 * ((n : ℝ) * (C.card : ℝ)) / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar))) := h_fkBound
      _ = 3 * Real.sqrt (Vbar * (Real.log (4 * n * C.card / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar)))) +
          2 * Rbar * (Real.log (4 * n * C.card / δ) + Real.log (max 1 (Real.sqrt Vbar / Rbar))) := by simp [mul_assoc]
      _ < |∑ s ∈ Finset.range t, Z c s ω| := h_bound
  refine ⟨c, hc, t, ht, ?_⟩
  simpa [Nat.cast_mul] using h_lt

namespace AdversarialBco.Poly

universe u

/-! ## Assemblies -/

theorem gaussTailT1 : GaussTailT1 := fun b hb => ⟨gauss_tail_T1 b hb, gauss_tail_T1_abs b hb⟩

theorem gaussTailT1' : GaussTailT1' := fun k b hk hb => gauss_tail_T1' k b hk hb

theorem gaussTailT2 : GaussTailT2 := fun d t hd => gauss_tail_T2 d t hd

theorem noiseTail : NoiseTail.{u} := fun μ _ ε hε hi h2 b hb => noise_tail μ ε hε hi h2 b hb

theorem condCauchySchwarz : CondCauchySchwarz.{u} := fun μ _ m hm U V hU hV =>
  cond_cauchy_schwarz μ m hm U V hU hV

theorem lemmaTR2 : LemmaTR2.{u} := fun μ _ Y Z T hY hZ hT hY4 hZ4 => lemmaTR2_main μ Y Z T hY hZ hT hY4 hZ4

theorem lemmaTR1 : LemmaTR1.{u} := fun μ _ Y Z T hY hZ hT hY2 hZ2 => lemmaTR1_main μ Y Z T hY hZ hT hY2 hZ2

theorem lemmaTR2Cond : LemmaTR2Cond.{u} := fun μ _ m hm Y Z T hY hZ hT hY4 hZ4 =>
  lemmaTR2_cond μ m hm Y Z T hY hZ hT hY4 hZ4

theorem lemmaTR1Cond : LemmaTR1Cond.{u} := fun μ _ m hm Y Z T hY hZ hT hY2 hZ2 =>
  lemmaTR1_cond μ m hm Y Z T hY hZ hT hY2 hZ2

theorem lemmaU : LemmaU.{u} := fun μ _ ℱ _ C Z hZm hZi hZ2 hZ0 n κ δ hκ hδ0 hδ1 =>
  lemmaU_main μ ℱ C Z hZm hZi hZ2 hZ0 n κ δ hκ hδ0 hδ1

theorem lemmaUCaps : LemmaUCaps.{u} := fun μ _ ℱ _ C Z hZm hZi hZ2 hZ0 n Vbar Rbar δ hV0 hR hδ0 hδ1 =>
  lemmaUCaps_main μ ℱ C Z hZm hZi hZ2 hZ0 n Vbar Rbar δ hV0 hR hδ0 hδ1

end AdversarialBco.Poly
