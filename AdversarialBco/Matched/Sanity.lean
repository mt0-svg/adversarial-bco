/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Matched.Arith
public import AdversarialBco.StatementMatched
public import AdversarialBco.UnifiedLower.Sanity

@[expose] public section

/-!
# Sanity checks of StatementMatched.lean (`TheoremGrowG`, `TheoremGrowGProg`, `TheoremMinimaxMatched`)

The witnesses of the arithmetic hypotheses added by StatementMatched.lean, next to `lowerU_hyps_satisfiable` and
`progU_hyps_satisfiable` of UnifiedLower/Sanity.lean (the structural hypotheses) and `minimaxQ_high_hyps_satisfiable`
of LowerDeltaQ/Sanity.lean (the clause for `δ ≥ 1/2`).

* `growG_hyps_satisfiable`: the hypotheses of `TheoremGrowG` and `TheoremGrowGProg` (`δ > 0`, `d ≥ 4·10^6`,
  `log (1/δ) ≥ 60`, `n ≥ d^6 log (1/δ)`) hold at `d = 4·10^6`, `n = d^10`, `δ = 2^{-d^4}`, where
  `log (1/δ) = d^4 log 2` is close to the top `n / d^6 = d^4` of the range.
* `matched_hyps_satisfiable`: the hypotheses of the matched clause of `TheoremMinimaxMatched` (`d ≥ 4·10^6`,
  `n ≥ d^10`, the rational `δ < 1/2`, `log (1/δ) ≤ n / d^6`) hold at the same point, with `log (1/δ) ≥ 60`, so that the
  proof reads `TheoremGrowGProg` there, together with an input of `TheoremUnified`'s class: the unit ball about the
  rational centre `0` with a weak membership oracle.
* `growGProg_matched_hyps_satisfiable`: every hypothesis of `TheoremGrowGProg` (the program, `MachineOK`, the
  budget, the windows, `δ' = δ`) and of the matched clause holds together at that point.
* `matched_exceeds_flat`: at that point the lower bound of the matched clause is more than `10^8` times the bound
  `7.42·10^-9 d^{3/2} n^{1/2} / log d` of `TheoremMinimaxQ` (about `5.1·10^8` times).

They use `log 2 > 0.6931471803` (`Real.log_two_gt_d9`), `e < 2.7182818286` and exact rational arithmetic
(Matched/Arith.lean).
-/

namespace AdversarialBco.Matched.MatchedSanity

open BitRAM BitRAMO

/-- The hypotheses of `TheoremGrowG` and `TheoremGrowGProg` hold together at `d = 4·10^6`, `n = d^10`,
`δ = 2^{-d^4}`. -/
theorem growG_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ 4000000 ≤ d ∧ 60 ≤ Real.log (1 / δ) ∧
      (d : ℝ) ^ 6 * Real.log (1 / δ) ≤ n := by
  obtain ⟨h60, hn, -⟩ := growG_arith
  refine ⟨4000000, 4000000 ^ 10, (1 / 2 : ℝ) ^ (4000000 ^ 4), by norm_num, Nat.one_le_pow _ _ (by norm_num),
    by positivity, le_rfl, ?_, ?_⟩
  · rw [log_one_div_half_pow, Nat.cast_pow, Nat.cast_ofNat]; exact h60
  · rw [log_one_div_half_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]; exact hn

/-- The hypotheses of the matched clause of `TheoremMinimaxMatched` hold together at `d = 4·10^6`, `n = d^10` and the
rational `δ = 2^{-d^4}`, with `log (1/δ) ≥ 60`, and the closed unit ball about the rational centre `0`, compact,
convex, with a weak membership oracle. -/
theorem matched_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℚ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ (δ : ℝ) < 1 / 2 ∧
      Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6 ∧ 60 ≤ Real.log (1 / (δ : ℝ)) ∧
      IsCompact (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      ∃ orc : (Fin d → ℚ) → ℕ → Bool,
        BitRAMO.WeakMemOracle (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) orc := by
  obtain ⟨hc, hv, -, -, ⟨orc, ho, -⟩, -⟩ :=
    UnifiedLower.LowerSanity.progU_hyps_satisfiable 4000000 (4000000 ^ 10) ((1 / 2 : ℚ) ^ (4000000 ^ 4))
  obtain ⟨h60, -, hw⟩ := growG_arith
  obtain ⟨hpos, hhalf⟩ := matched_window_arith (4000000 ^ 4) (Nat.le_self_pow (by norm_num) _ |>.trans' (by norm_num))
  have hcast : (((1 / 2 : ℚ) ^ (4000000 ^ 4) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ (4000000 ^ 4) := by
    rw [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hq0 : (0 : ℚ) < (1 / 2 : ℚ) ^ (4000000 ^ 4) := by positivity
  have hq1 : (1 / 2 : ℚ) ^ (4000000 ^ 4) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by positivity)
  refine ⟨4000000, 4000000 ^ 10, (1 / 2 : ℚ) ^ (4000000 ^ 4), by norm_num, Nat.one_le_pow _ _ (by norm_num), hq0,
    hq1, le_rfl, le_rfl, ?_, ?_, ?_, hc, hv, orc, ho⟩
  · rw [hcast]; exact hhalf
  · rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]; exact hw
  · rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_ofNat]; exact h60

/-- At the point of `matched_hyps_satisfiable`, the lower bound of the matched clause of `TheoremMinimaxMatched` is
more than `10^8` times the bound `7.42·10^-9 d^{3/2} n^{1/2} / log d` of `TheoremMinimaxQ`. -/
theorem matched_exceeds_flat :
    10 ^ 8 * (742 / 10 ^ 11 * ((4000000 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 ^ 10 : ℕ) : ℝ) /
        Real.log ((4000000 : ℕ) : ℝ)) <
      7 / 10 ^ 9 * (((4000000 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 ^ 10 : ℕ) : ℝ) /
          Real.log ((4000000 : ℕ) : ℝ) +
        ((4000000 : ℕ) : ℝ) * Real.sqrt (((4000000 ^ 10 : ℕ) : ℝ) *
            Real.log (1 / (((1 / 2 : ℚ) ^ (4000000 ^ 4) : ℚ) : ℝ))) /
          (Real.log ((4000000 : ℕ) : ℝ) * Real.sqrt (Real.log ((4000000 ^ 10 : ℕ) : ℝ)))) := by
  have hcast : (((1 / 2 : ℚ) ^ (4000000 ^ 4) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ (4000000 ^ 4) := by
    rw [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  exact exceeds_flat_arith

open Unified UnifiedLower in
/-- Every hypothesis of `TheoremGrowGProg` and of the matched clause of `TheoremMinimaxMatched` holds at one point:
`d = 4·10^6`, `n = d^10`, the rational `δ = δ' = 2^{-d^4}`, the closed unit ball about the rational centre `0`
(`r0 = R0 = 1`) with a weak membership oracle, and the three-instruction program of `progU_hyps_satisfiable`, which
meets `MachineOK` with the windows `D = D' = 0` and some budget `B`. -/
theorem growGProg_matched_hyps_satisfiable :
    ∃ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (P : List InstrO)
      (B : ℝ) (D D' : ℕ → ℕ),
      1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 0 < r0 ∧ r0 ≤ R0 ∧ IsCompact K ∧ Convex ℝ K ∧
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K ∧ K ⊆ Metric.closedBall (toE a) (R0 : ℝ) ∧
      WeakMemOracle K orc ∧ MachineOK P K orc (initU d n δ r0 R0 a) n B D D' ∧
      (0 : ℝ) < δ ∧ 4000000 ≤ d ∧ 60 ≤ Real.log (1 / (δ : ℝ)) ∧ (d : ℝ) ^ 6 * Real.log (1 / (δ : ℝ)) ≤ n ∧
      d ^ 10 ≤ n ∧ (δ : ℝ) < 1 / 2 ∧ Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6 := by
  obtain ⟨hc, hv, hb1, hb2, ⟨orc, ho, -⟩, hM⟩ :=
    UnifiedLower.LowerSanity.progU_hyps_satisfiable 4000000 (4000000 ^ 10) ((1 / 2 : ℚ) ^ (4000000 ^ 4))
  obtain ⟨B, hB⟩ := hM orc
  obtain ⟨h60, hn, hw⟩ := growG_arith
  obtain ⟨-, hhalf⟩ := matched_window_arith (4000000 ^ 4) (Nat.le_self_pow (by norm_num) _ |>.trans' (by norm_num))
  have hcast : (((1 / 2 : ℚ) ^ (4000000 ^ 4) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ (4000000 ^ 4) := by
    rw [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hq0 : (0 : ℚ) < (1 / 2 : ℚ) ^ (4000000 ^ 4) := by positivity
  have hq1 : (1 / 2 : ℚ) ^ (4000000 ^ 4) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by positivity)
  refine ⟨4000000, 4000000 ^ 10, (1 / 2 : ℚ) ^ (4000000 ^ 4), 1, 1, 0, _, orc, _, B, fun _ => 0, fun _ => 0,
    by norm_num, Nat.one_le_pow _ _ (by norm_num), hq0, hq1, zero_lt_one, le_rfl, hc, hv, hb1, hb2, ho, hB,
    Rat.cast_pos.2 hq0, le_rfl, ?_, ?_, le_rfl, ?_, ?_⟩
  · rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_ofNat]; exact h60
  · rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]; exact hn
  · rw [hcast]; exact hhalf
  · rw [hcast, log_one_div_half_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]; exact hw

end AdversarialBco.Matched.MatchedSanity
