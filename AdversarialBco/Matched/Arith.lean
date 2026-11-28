/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The arithmetic of the matched minimax theorem

Pure real arithmetic, read by Matched/Lower.lean and Matched/Sanity.lean:

* `three_halves_half`, `rpow_three_halves_mul`: `2.1·10^-8 (x/2)^{3/2} ≥ 7.42·10^-9 x^{3/2}`, the constant of
  clause (a) of `TheoremLowerUDProgQ` at the failures `1/2` and `(1 - δ)/2`;
* `range_half`: the two range hypotheses of that clause at the failure `1/2` hold for every `d ≥ 4·10^6`;
* `small_ell`: `d (n ℓ)^{1/2} ≤ 0.004 d^{3/2} n^{1/2}` for `ℓ < 60` and `d ≥ 4·10^6`;
* `matched_combine`: the constant `7·10^-9` of the matched clause from `7.42·10^-9` and `8·10^-6`;
* `one_le_sqrt_log`, `log_one_div_half_pow`, `growG_arith`, `matched_window_arith`, `exceeds_flat_arith`: the facts of
  the witnesses.
-/

namespace AdversarialBco.Matched

/-- `(1/2)^{3/2} = (1/2) (1/2)^{1/2} ≥ 0.35335`. -/
theorem half_rpow_ge : (7067 / 20000 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by
  have h : (1 / 2 : ℝ) ^ (3 / 2 : ℝ) = (1 / 2) * Real.sqrt (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h]
  have hs : (7067 / 10000 : ℝ) ≤ Real.sqrt (1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  linarith

/-- `7.42·10^-9 ≤ 2.1·10^-8 (1/2)^{3/2} = 7.4246·10^-9`. -/
theorem three_halves_half : (742 / 10 ^ 11 : ℝ) ≤ 21 / 10 ^ 9 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by
  have := half_rpow_ge
  nlinarith

/-- `7.42·10^-9 x^{3/2} ≤ 2.1·10^-8 (x/2)^{3/2}` for `x ≥ 0`. -/
theorem rpow_three_halves_mul (x : ℝ) (hx : 0 ≤ x) :
    742 / 10 ^ 11 * x ^ (3 / 2 : ℝ) ≤ 21 / 10 ^ 9 * (x / 2) ^ (3 / 2 : ℝ) := by
  rw [div_eq_mul_one_div x 2, Real.mul_rpow hx (by norm_num)]
  have h1 := three_halves_half
  have h2 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx _
  nlinarith

/-- `log x ≤ 14.3 + x / (4·10^6)` for `x ≥ 4·10^6` (`log (4·10^6) ≤ 15.3` from `e > 2.7182818283`, then
`log y ≤ y - 1`), from Mathlib alone. -/
theorem log_le_ripe' (dd : ℝ) (hd : 4000000 ≤ dd) : Real.log dd ≤ 143 / 10 + dd / 4000000 := by
  have h0 : (0 : ℝ) < 4000000 := by norm_num
  have hl : Real.log 4000000 ≤ 153 / 10 := by
    rw [Real.log_le_iff_le_exp h0]
    have he : (2.7182818283 : ℝ) ^ 15 ≤ Real.exp 15 := by
      rw [show (15 : ℝ) = (15 : ℕ) by norm_num, ← Real.exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 15
    have h3 : (1 : ℝ) + 3 / 10 ≤ Real.exp (3 / 10) := by
      have := Real.add_one_le_exp (3 / 10 : ℝ); linarith
    have : Real.exp (153 / 10) = Real.exp 15 * Real.exp (3 / 10) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    have hpos : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ 15 := by positivity
    nlinarith
  have hr : Real.log (dd / 4000000) ≤ dd / 4000000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hr
  linarith

/-- The range hypotheses of clause (a) of `TheoremLowerUDProgQ` at the failure `1/2`, for every `d ≥ 4·10^6`. -/
theorem range_half (d : ℕ) (hd : 4000000 ≤ d) :
    1024 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := log_le_ripe' d hd'
  have hq : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by have := half_rpow_ge; linarith
  rw [min_self]
  refine ⟨by linarith, ?_⟩
  have : (1 / 4 : ℝ) * d ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * d := mul_le_mul_of_nonneg_right hq (by positivity)
  linarith

/-- `x^{3/2} = x √x` for `x ≥ 0`. -/
theorem rpow_three_halves_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- Below `ℓ = 60` the growing term is at most `0.004` times the flat one: `d √(n ℓ) ≤ 0.004 d^{3/2} √n`. -/
theorem small_ell (d n : ℕ) (ℓ : ℝ) (hd : 4000000 ≤ d) (hℓ : ℓ < 60) :
    (d : ℝ) * Real.sqrt (n * ℓ) ≤ 4 / 1000 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n) := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  rw [rpow_three_halves_eq _ (by positivity), Real.sqrt_mul (by positivity)]
  have hsd : (2000 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hsl : Real.sqrt ℓ ≤ 8 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hdn : 0 ≤ (d : ℝ) * Real.sqrt n := by positivity
  have h1 : (d : ℝ) * (Real.sqrt n * Real.sqrt ℓ) ≤ (d : ℝ) * Real.sqrt n * 8 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hsl hdn
  have h2 : (d : ℝ) * Real.sqrt n * 8 ≤ 4 / 1000 * ((d : ℝ) * Real.sqrt d * Real.sqrt n) := by
    have := mul_le_mul_of_nonneg_left hsd hdn
    nlinarith
  linarith

/-- The constant of the matched clause: from `V ≥ 7.42·10^-9 Λ / log d` always and
`V ≥ 8·10^-6 Y / (log d √log n)` for `ℓ ≥ 60`, with `Y ≤ 0.004 Λ` for `ℓ < 60`:
`V ≥ 7·10^-9 (Λ / log d + Y / (log d √log n))` (`7/7.42 + 7·10^-9/8·10^-6 = 0.94427 ≤ 1`;
`7·10^-9 · 1.004 ≤ 7.42·10^-9`). -/
theorem matched_combine {Lam Y ld sl V ℓ : ℝ} (hLam : 0 ≤ Lam) (hY : 0 ≤ Y) (hld : 0 < ld)
    (hsl : 1 ≤ sl) (h1 : 742 / 10 ^ 11 * Lam / ld ≤ V) (h2 : 60 ≤ ℓ → 8 / 10 ^ 6 * Y / (ld * sl) ≤ V)
    (h3 : ℓ < 60 → Y ≤ 4 / 1000 * Lam) :
    7 / 10 ^ 9 * (Lam / ld + Y / (ld * sl)) ≤ V := by
  have hls : 0 < ld * sl := by positivity
  have hu0 : 0 ≤ Lam / ld := div_nonneg hLam hld.le
  have hw0 : 0 ≤ Y / (ld * sl) := div_nonneg hY hls.le
  have e1 : 742 / 10 ^ 11 * Lam / ld = 742 / 10 ^ 11 * (Lam / ld) := mul_div_assoc _ _ _
  rw [e1] at h1
  rcases le_or_gt 60 ℓ with hl | hl
  · have h2' := h2 hl
    rw [mul_div_assoc] at h2'
    nlinarith
  · have hY' := h3 hl
    have hw1 : Y / (ld * sl) ≤ Y / ld := div_le_div_of_nonneg_left hY hld (by nlinarith)
    have hw2 : Y / ld ≤ 4 / 1000 * Lam / ld := div_le_div_of_nonneg_right hY' hld.le
    rw [mul_div_assoc] at hw2
    nlinarith

/-- `(log n)^{1/2} ≥ 1` for `n ≥ d^10`, `d ≥ 4·10^6`. -/
theorem one_le_sqrt_log (d n : ℕ) (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) : 1 ≤ Real.sqrt (Real.log n) := by
  have hdn : d ≤ n := le_trans (Nat.le_self_pow (by norm_num) d) hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have h1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt h1

/-- `log (1 / 2^{-m}) = m log 2`. -/
theorem log_one_div_half_pow (m : ℕ) : Real.log (1 / (1 / 2 : ℝ) ^ m) = m * Real.log 2 := by
  rw [one_div_pow, one_div_one_div, Real.log_pow]

/-- At `d = 4·10^6`, `n = d^10`, `log (1/δ) = d^4 log 2`: the range of `TheoremGrowG` and of the matched clause. -/
theorem growG_arith :
    60 ≤ (4000000 : ℝ) ^ 4 * Real.log 2 ∧
      (4000000 : ℝ) ^ 6 * ((4000000 : ℝ) ^ 4 * Real.log 2) ≤ (4000000 : ℝ) ^ 10 ∧
      (4000000 : ℝ) ^ 4 * Real.log 2 ≤ (4000000 : ℝ) ^ 10 / (4000000 : ℝ) ^ 6 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [show (4000000 : ℝ) ^ 10 / (4000000 : ℝ) ^ 6 = (4000000 : ℝ) ^ 4 by norm_num]
  nlinarith

/-- `0 < 2^{-m} < 1/2` for `m ≥ 2`. -/
theorem matched_window_arith (m : ℕ) (hm : 2 ≤ m) : (0 : ℝ) < (1 / 2 : ℝ) ^ m ∧ (1 / 2 : ℝ) ^ m < 1 / 2 := by
  refine ⟨by positivity, ?_⟩
  calc (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ < 1 / 2 := by norm_num

/-- At `d = 4·10^6`, `n = d^10`, `log (1/δ) = d^4 log 2`, the bound of the matched clause exceeds `10^8` times the
flat bound `7.42·10^-9 d^{3/2} n^{1/2} / log d`; its `δ` term alone does. -/
theorem exceeds_flat_arith :
    10 ^ 8 * (742 / 10 ^ 11 * (4000000 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 : ℝ) ^ 10) / Real.log 4000000) <
      7 / 10 ^ 9 * ((4000000 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 : ℝ) ^ 10) / Real.log 4000000 +
        4000000 * Real.sqrt ((4000000 : ℝ) ^ 10 * ((4000000 : ℝ) ^ 4 * Real.log 2)) /
          (Real.log 4000000 * Real.sqrt (Real.log ((4000000 : ℝ) ^ 10)))) := by
  have hD0 : (0 : ℝ) < 4000000 := by norm_num
  have hsD : Real.sqrt (4000000 : ℝ) = 2000 := by
    rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h32 : (4000000 : ℝ) ^ (3 / 2 : ℝ) = 4000000 * 2000 := by rw [rpow_three_halves_eq _ hD0.le, hsD]
  have h10 : Real.sqrt ((4000000 : ℝ) ^ 10) = (4000000 : ℝ) ^ 5 := by
    rw [show (4000000 : ℝ) ^ 10 = ((4000000 : ℝ) ^ 5) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have h14 : Real.sqrt ((4000000 : ℝ) ^ 10 * ((4000000 : ℝ) ^ 4 * Real.log 2)) =
      (4000000 : ℝ) ^ 7 * Real.sqrt (Real.log 2) := by
    rw [show (4000000 : ℝ) ^ 10 * ((4000000 : ℝ) ^ 4 * Real.log 2) = ((4000000 : ℝ) ^ 7) ^ 2 * Real.log 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hs2 : (83 / 100 : ℝ) ≤ Real.sqrt (Real.log 2) :=
    Real.le_sqrt_of_sq_le (by have := Real.log_two_gt_d9; linarith)
  have hL : 15 ≤ Real.log (4000000 : ℝ) := by
    rw [Real.le_log_iff_exp_le hD0]
    rw [show (15 : ℝ) = (15 : ℕ) by norm_num, ← Real.exp_one_pow]
    calc Real.exp 1 ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 15
      _ ≤ 4000000 := by norm_num
  have hLu : Real.log (4000000 : ℝ) ≤ 153 / 10 := by
    have := log_le_ripe' 4000000 le_rfl; norm_num at this ⊢; linarith
  have hLn : Real.log ((4000000 : ℝ) ^ 10) = 10 * Real.log 4000000 := by rw [Real.log_pow]; norm_num
  have hS : Real.sqrt (Real.log ((4000000 : ℝ) ^ 10)) ≤ 13 := by
    rw [hLn, Real.sqrt_le_left (by norm_num)]; linarith
  have hS0 : 0 < Real.sqrt (Real.log ((4000000 : ℝ) ^ 10)) := Real.sqrt_pos.2 (by rw [hLn]; linarith)
  rw [h32, h10, h14]
  set L := Real.log (4000000 : ℝ) with hLdef
  set S := Real.sqrt (Real.log ((4000000 : ℝ) ^ 10)) with hSdef
  set s2 := Real.sqrt (Real.log 2) with hs2def
  have hL0 : 0 < L := by linarith
  have hT1 : 0 ≤ 7 / 10 ^ 9 * (4000000 * 2000 * (4000000 : ℝ) ^ 5 / L) := by positivity
  have key0 : 10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5) * S <
      7 / 10 ^ 9 * (4000000 * ((4000000 : ℝ) ^ 7 * s2)) := by
    nlinarith
  have key : 10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5 / L) <
      7 / 10 ^ 9 * (4000000 * ((4000000 : ℝ) ^ 7 * s2) / (L * S)) := by
    rw [show 10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5 / L) =
          10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5) / L by ring,
      show 7 / 10 ^ 9 * (4000000 * ((4000000 : ℝ) ^ 7 * s2) / (L * S)) =
          7 / 10 ^ 9 * (4000000 * ((4000000 : ℝ) ^ 7 * s2)) / (L * S) by ring,
      div_lt_div_iff₀ hL0 (by positivity)]
    calc 10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5) * (L * S) =
          (10 ^ 8 * (742 / 10 ^ 11 * (4000000 * 2000) * (4000000 : ℝ) ^ 5) * S) * L := by ring
      _ < 7 / 10 ^ 9 * (4000000 * ((4000000 : ℝ) ^ 7 * s2)) * L := mul_lt_mul_of_pos_right key0 hL0
  rw [mul_add]
  linarith

end AdversarialBco.Matched
