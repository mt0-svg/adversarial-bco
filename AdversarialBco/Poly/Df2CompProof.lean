/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2RowsProof
public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# The arithmetic of the measure clause

With `B = 2 ρ/η + n ε + (2 n log(7/δ_e))^{1/2}`, the bound on the regret of D0 on the case of the analysis: the
confidence of an epoch against the scale, `0 < log(1/δ_e) ≤ 25 log(2dn/δ)` (`log_inv_de_le`); the threshold
`B + 1 ≤ 10^22 d^{3/2} n^{1/2} log^5(2 d n/δ)` (`comp_thresh`); and `0 < δ₁ ≤ δ/3` (`par_δ1_pos`, `par_δ1_le`).
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Leaves -/

/-- The confidence of an epoch against the scale `log(2dn/δ)`: `0 < log(1/δ_e) ≤ 25 log(2dn/δ)`. -/
theorem log_inv_de_le (d n δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (1 / (4 * min (δ / 3) (Real.exp (-14) / (d * n) ^ 3) / (5 * n))) ∧
      Real.log (1 / (4 * min (δ / 3) (Real.exp (-14) / (d * n) ^ 3) / (5 * n))) ≤
        25 * Real.log (2 * d * n / δ) := by
  set x := d * n with hx
  have hx1 : 1 ≤ x := by nlinarith
  set E := Real.exp 14 with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hEm : Real.exp (-14) = 1 / E := by rw [Real.exp_neg, hE, one_div]
  have hn0 : 0 < n := by linarith
  set q := δ / (3 * E * x ^ 3) with hq
  have hq0 : 0 < q := by positivity
  have hd1 : q ≤ min (δ / 3) (Real.exp (-14) / x ^ 3) := by
    refine le_min ?_ ?_
    · rw [hq]
      apply div_le_div_of_nonneg_left hδ0.le (by norm_num)
      have : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1
      nlinarith
    · rw [hq, hEm, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hEx : 0 < E * x ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hδ1.le hEx.le]
  set δ1 := min (δ / 3) (Real.exp (-14) / x ^ 3) with hδ1def
  have hδ1pos : 0 < δ1 := lt_of_lt_of_le hq0 hd1
  set δe := 4 * δ1 / (5 * n) with hδe
  have hδepos : 0 < δe := by positivity
  have hδ1le : δ1 ≤ δ / 3 := min_le_left _ _
  have hδelt : δe < 1 := by
    rw [hδe, div_lt_one (by positivity)]
    nlinarith
  have hpos : 0 < Real.log (1 / δe) := by
    apply Real.log_pos
    rw [one_div]; exact one_lt_inv₀ hδepos |>.mpr hδelt
  refine ⟨hpos, ?_⟩
  have hΛ : 2 * d * n / δ = 2 * x / δ := by rw [hx]; ring
  rw [hΛ]
  have hz : 2 ≤ 2 * x / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hlog2 : 2 / 3 ≤ Real.log (2 * x / δ) := by
    have h2 : 2 / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith [Real.log_le_log (by norm_num) hz]
  -- `1/δe ≤ E (2x/δ)^4`
  have hkey : 1 / δe ≤ E * (2 * x / δ) ^ 4 := by
    rw [div_le_iff₀ hδepos]
    have h1 : 4 * q / (5 * n) ≤ δe := by
      rw [hδe]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 1 ≤ E * (2 * x / δ) ^ 4 * (4 * q / (5 * n)) := by
      rw [hq]
      have e : E * (2 * x / δ) ^ 4 * (4 * (δ / (3 * E * x ^ 3)) / (5 * n)) = 64 * x / (15 * n * δ ^ 3) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ0.le hδ1.le
      have hxn : n ≤ x := by rw [hx]; nlinarith
      nlinarith
    calc (1 : ℝ) ≤ E * (2 * x / δ) ^ 4 * (4 * q / (5 * n)) := h2
      _ ≤ E * (2 * x / δ) ^ 4 * δe := by gcongr
  have hl := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) (by positivity), hE, Real.log_exp, Real.log_pow] at hl
  push_cast at hl
  linarith

theorem comp_thresh (p : Df2OPar) (d n : ℕ) (δ : ℝ) (H : RowHyp p d n) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (h1 : p.δ1 = min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)) (he : p.δe = 4 * p.δ1 / (5 * n)) :
    2 * (p.rho / p.eta) + n * p.eps + Real.sqrt (2 * n * Real.log (7 / p.δe)) + 1 ≤
      10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  obtain ⟨-, hle⟩ := log_inv_de_le d n δ hd1 hn1 hδ0 hδ1
  have hLΛ : p.Le ≤ 900 * Real.log (2 * d * n / δ) := by
    rw [H.Le, he, h1]; linarith
  have hde := H.de_pos
  have hlog7 : Real.log (7 / p.δe) ≤ 6 + p.Le / 36 := by
    rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity), H.Le]
    have : Real.log 7 ≤ 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hd32 : (d : ℝ) ^ (3 / 2 : ℝ) = d * Real.sqrt d := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [H.rho, H.eta, H.eps, hd32]
  set Λ := Real.log (2 * d * n / δ)
  set L := p.Le with hLdef
  have hL : (504 : ℝ) ≤ L := H.L504
  set s := Real.sqrt d with hs
  set t := Real.sqrt n with ht
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hd1
  have ht1 : 1 ≤ t := Real.one_le_sqrt.mpr hn1
  have hss : s ^ 2 = d := Real.sq_sqrt (by linarith)
  have htt : t ^ 2 = n := Real.sq_sqrt (by linarith)
  have hL4 : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL1 : 1 ≤ L ^ 5 := one_le_pow₀ (by linarith)
  have hds : 1 ≤ d * s := by nlinarith
  have hP : 0 ≤ d * s * t := by positivity
  -- the four terms
  have hT1 : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) ≤ 2900 * (d * s) * L ^ 5 * t := by
    have e : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) = 2900 * (d * s) * L ^ 4 * t := by
      have hs0 : s ≠ 0 := by positivity
      field_simp
      rw [← hss]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ 2900 * (d * s))
    nlinarith
  have hT2 : (n : ℝ) * (20 * 725 * (d * s) * L ^ 5 / t) = 14500 * (d * s) * L ^ 5 * t := by
    have ht0 : t ≠ 0 := by positivity
    field_simp
    rw [← htt]; ring
  have hT3 : Real.sqrt (2 * n * Real.log (7 / p.δe)) ≤ (d * s) * L ^ 5 * t := by
    have h2 : 2 * n * Real.log (7 / p.δe) ≤ (L * t) ^ 2 := by
      rw [mul_pow, htt]
      have : 2 * Real.log (7 / p.δe) ≤ L ^ 2 := by nlinarith
      nlinarith
    calc Real.sqrt (2 * n * Real.log (7 / p.δe)) ≤ Real.sqrt ((L * t) ^ 2) := Real.sqrt_le_sqrt h2
      _ = L * t := Real.sqrt_sq (by positivity)
      _ ≤ (d * s) * L ^ 5 * t := by
        have hLL : L ≤ L ^ 5 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have : L ≤ (d * s) * L ^ 5 := le_trans hLL (le_mul_of_one_le_left (by positivity) hds)
        nlinarith
  have hT4 : (1 : ℝ) ≤ (d * s) * L ^ 5 * t := by
    have : 1 ≤ (d * s) * L ^ 5 := one_le_mul_of_one_le_of_one_le hds hL1
    nlinarith
  have hsum : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) + n * (20 * 725 * (d * s) * L ^ 5 / t) +
      Real.sqrt (2 * n * Real.log (7 / p.δe)) + 1 ≤ 17402 * (d * s * t) * L ^ 5 := by
    rw [hT2]; nlinarith
  have hL5 : L ^ 5 ≤ (900 * Λ) ^ 5 := pow_le_pow_left₀ (by linarith) hLΛ 5
  calc _ ≤ 17402 * (d * s * t) * L ^ 5 := hsum
    _ ≤ 17402 * (d * s * t) * (900 * Λ) ^ 5 := by gcongr
    _ = 17402 * 900 ^ 5 * ((d * s * t) * Λ ^ 5) := by ring
    _ ≤ 10 ^ 22 * ((d * s * t) * Λ ^ 5) := by
      gcongr
      · have : 0 ≤ Λ := by linarith
        positivity
      · norm_num
    _ = 10 ^ 22 * (d * s) * t * Λ ^ 5 := by ring

/-! ## The parameters -/

theorem par_δ1_pos (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) : 0 < (df2oPar d n δ).δ1 := by
  have hdn : (0 : ℝ) < (d : ℝ) * n := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  show 0 < min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)
  exact lt_min (by positivity) (by positivity)

theorem par_δ1_le (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).δ1 ≤ δ / 3 := min_le_left _ _

end Layer2

end AdversarialBco.Poly
