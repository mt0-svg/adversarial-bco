/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUW

@[expose] public section

/-!
# Theorem U from Theorem UW

`theoremUnified_of_UW : TheoremUW → TheoremUnified`. The two statements are the same text except the threshold of the
probability and mean clauses: with `Λ = d^{3/2} √n`, `l = log(2 d n)`, `L = log(2 d n / δ)` and UW's constant `C`,
UW's threshold `C (Λ l^5 + d √(n log(2/δ)) l^{9/2})` is at most `2 max(C, 0) Λ L^5`, Theorem U's threshold at the
constant `2 max(C, 0)`. For `d, n ≥ 1` and `0 < δ < 1`: `0 ≤ l ≤ L`, `0 ≤ log(2/δ) ≤ L`, `d ≤ d^{3/2}` and
`L^{1/2} L^{9/2} = L^5` (`thrUW_le`); the program, the cost constants and the windows are UW's.
-/

open MeasureTheory

namespace AdversarialBco.UW

open BitRAM BitRAMO Unified

/-- The bracket of UW's threshold is nonnegative. -/
theorem thrUW_nonneg {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) :
    0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
      d * Real.sqrt (n * Real.log (2 / δ)) * Real.log (2 * d * n) ^ (9 / 2 : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2 * d * n) := Real.log_nonneg (by nlinarith)
  exact add_nonneg
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _)) (pow_nonneg hl 5))
    (mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.rpow_nonneg hl _))

/-- **UW's threshold against Theorem U's**: `Λ l^5 + d √(n log(2/δ)) l^{9/2} ≤ 2 Λ L^5`. -/
theorem thrUW_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
        d * Real.sqrt (n * Real.log (2 / δ)) * Real.log (2 * d * n) ^ (9 / 2 : ℝ) ≤
      2 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (2 : ℝ) ≤ 2 * d * n := by nlinarith
  have hl0 : 0 ≤ Real.log (2 * d * n) := Real.log_nonneg (by linarith)
  have hlL : Real.log (2 * d * n) ≤ Real.log (2 * d * n / δ) :=
    Real.log_le_log (by linarith) (by rw [le_div_iff₀ h0]; nlinarith)
  have hmL : Real.log (2 / δ) ≤ Real.log (2 * d * n / δ) :=
    Real.log_le_log (div_pos two_pos h0) (div_le_div_of_nonneg_right hx h0.le)
  have hL0 : 0 ≤ Real.log (2 * d * n / δ) := hl0.trans hlL
  have hd32 : (d : ℝ) ≤ (d : ℝ) ^ (3 / 2 : ℝ) :=
    calc (d : ℝ) = (d : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)
  have hsq : Real.sqrt (n * Real.log (2 / δ)) ≤ Real.sqrt n * Real.sqrt (Real.log (2 * d * n / δ)) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmL (Nat.cast_nonneg _))
  have h92 : Real.log (2 * d * n) ^ (9 / 2 : ℝ) ≤ Real.log (2 * d * n / δ) ^ (9 / 2 : ℝ) :=
    Real.rpow_le_rpow hl0 hlL (by norm_num)
  have h5 : Real.sqrt (Real.log (2 * d * n / δ)) * Real.log (2 * d * n / δ) ^ (9 / 2 : ℝ) =
      Real.log (2 * d * n / δ) ^ 5 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hL0 (by norm_num),
      show (1 / 2 : ℝ) + 9 / 2 = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hA : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have t1 : (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 ≤
      (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hlL 5) (mul_nonneg hA hsn)
  have t2 : (d : ℝ) * Real.sqrt (n * Real.log (2 / δ)) * Real.log (2 * d * n) ^ (9 / 2 : ℝ) ≤
      (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 :=
    calc (d : ℝ) * Real.sqrt (n * Real.log (2 / δ)) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)
        ≤ (d : ℝ) ^ (3 / 2 : ℝ) * (Real.sqrt n * Real.sqrt (Real.log (2 * d * n / δ))) *
            Real.log (2 * d * n / δ) ^ (9 / 2 : ℝ) :=
          mul_le_mul (mul_le_mul hd32 hsq (Real.sqrt_nonneg _) hA) h92 (Real.rpow_nonneg hl0 _)
            (mul_nonneg hA (mul_nonneg hsn (Real.sqrt_nonneg _)))
      _ = (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n *
            (Real.sqrt (Real.log (2 * d * n / δ)) * Real.log (2 * d * n / δ) ^ (9 / 2 : ℝ)) := by ring
      _ = _ := by rw [h5]
  linarith

/-- **Theorem U from Theorem UW**, at the constant `2 max(C, 0)` with UW's program, cost constants and windows. -/
theorem theoremUnified_of_UW (h : TheoremUW) : TheoremUnified := by
  obtain ⟨P, C, C', k, D, D', hU⟩ := h
  refine ⟨P, 2 * max C 0, C', k, D, D', fun d hd n hn δ r0 R0 h0 h1 hr0 hr a K hKc hKv hb1 hb2 orc horc => ?_⟩
  obtain ⟨hi, hii⟩ := hU d hd n hn δ r0 R0 h0 h1 hr0 hr a K hKc hKv hb1 hb2 orc horc
  refine ⟨hi, fun Ω _ μ coin loss noise hN => ?_⟩
  obtain ⟨hm, hint, hp, he⟩ := hii Ω μ coin loss noise hN
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast h1
  have hthr : C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
        d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) ≤
      2 * max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 :=
    calc _ ≤ max C 0 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
          d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (thrUW_nonneg hd hn _)
      _ ≤ max C 0 * (2 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5)) :=
          mul_le_mul_of_nonneg_left (thrUW_le hd hn hδ0 hδ1) (le_max_right _ _)
      _ = _ := by ring
  exact ⟨hm, hint, le_trans (measure_mono fun ω hω => lt_of_le_of_lt hthr hω) hp,
    he.trans (add_le_add hthr le_rfl)⟩

end AdversarialBco.UW
