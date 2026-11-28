/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementMinimaxQ
public import AdversarialBco.Minimax.Sanity
public import AdversarialBco.Conj1LowerPolyD.Sanity

@[expose] public section

/-!
# Sanity checks of StatementMinimaxQ.lean (`TheoremLowerUDQ`, `TheoremLowerUDProgQ`, `TheoremMinimaxQ`)

The witnesses stated in the challenge next to the theorems and certified by Comparator with them, together with
`lowerU_hyps_satisfiable` and `progU_hyps_satisfiable` of UnifiedLower/Sanity.lean (the structural hypotheses) and
`payoffs_bounded`, `meanPosOf_tail_eq_integral` of Minimax/Sanity.lean (the payoffs).

* `lowerUDQ_a_hyps_satisfiable`: the hypotheses of clause (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ`, with
  the two range hypotheses `1024 k₀ ≤ min(δ, 1/2) d` and `10 k₀ ≤ min(δ, 1/2)^{3/2} d`, `k₀ = 120 log d + 68`, hold at
  `d = 10^7`, `n = d^10`, `δ = 1/2`.
* `lowerUDQ_a_small_hyps_satisfiable`: the same at `d = 10^8`, `n = d^10` and `δ = 1/20 < 1/2`, where both range
  hypotheses depend on `δ`.
* `minimaxQ_high_hyps_satisfiable`: the hypotheses of the last clause of `TheoremMinimaxQ` (`δ ≥ 1/2` and the two range
  hypotheses at `(1 - δ)/2`) hold at `d = 10^8`, `n = d^10`, the rational `δ = 1/2`, together with an input of
  `TheoremUnified`'s class: the unit ball about the rational centre `0` with a weak membership oracle.
* `boundDQ_facts`, `zeroStrat_fails_of_nonemptyDQ`: the witnesses of
  `TheoremConj1LowerPolyD` (Conj1LowerPolyD/Sanity.lean) at the constant `3.71·10^-9` of `TheoremConj1LowerPolyDQ`: the
  bound is positive and at most `n / 2` on the regime, and the zero strategy of the class fails it against every
  learner; with `constLearner_mem_of_mem` (the class of learners is not empty) they are those of that statement.

The first three proofs use `e > 2.7182818283` (`Real.exp_one_gt_d9`), `x^2 ≤ x^{3/2}` on `(0, 1]` and exact rational
arithmetic.
-/

namespace AdversarialBco.LowerDeltaQ.Sanity

open BitRAM BitRAMO

/-- `x^2 ≤ x^{3/2}` on `(0, 1]`. -/
theorem sq_le_rpow_three_halves (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) : x ^ 2 ≤ x ^ (3 / 2 : ℝ) := by
  have := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show (3 / 2 : ℝ) ≤ 2 by norm_num)
  simpa using this

/-- The hypotheses of clause (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ` hold together at `d = 10^7`,
`n = d^10`, `δ = 1/2`. -/
theorem lowerUDQ_a_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧
      1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d := by
  refine ⟨10 ^ 7, (10 ^ 7) ^ 10, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, ?_⟩
  have hl : Real.log ((10 ^ 7 : ℕ) : ℝ) < 17 := by
    have := Minimax.MinimaxSanity.log_lt_of_lt_pow ((10 ^ 7 : ℕ) : ℝ) (by positivity) 17 (by norm_num) (by norm_num)
    exact_mod_cast this
  have hr := sq_le_rpow_three_halves (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [min_self]
  push_cast at hl ⊢
  constructor
  · nlinarith
  · nlinarith

/-- The hypotheses of clause (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ` hold together at `d = 10^8`,
`n = d^10` and a failure probability `δ = 1/20` below `1/2`. -/
theorem lowerUDQ_a_small_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 / 2 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧
      1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d := by
  refine ⟨10 ^ 8, (10 ^ 8) ^ 10, 1 / 20, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, ?_⟩
  have hl : Real.log ((10 ^ 8 : ℕ) : ℝ) < 19 := by
    have := Minimax.MinimaxSanity.log_lt_of_lt_pow ((10 ^ 8 : ℕ) : ℝ) (by positivity) 19 (by norm_num) (by norm_num)
    exact_mod_cast this
  have hm : min (1 / 20 : ℝ) (1 / 2) = 1 / 20 := min_eq_left (by norm_num)
  have hr := sq_le_rpow_three_halves (1 / 20 : ℝ) (by norm_num) (by norm_num)
  rw [hm]
  push_cast at hl ⊢
  constructor
  · nlinarith
  · nlinarith

/-- The hypotheses of the last clause of `TheoremMinimaxQ` hold together at `d = 10^8`, `n = d^10` and the rational
`δ = 1/2`, with the closed unit ball about the rational centre `0`, compact, convex, with a weak membership oracle. -/
theorem minimaxQ_high_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℚ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ 1 / 2 ≤ (δ : ℝ) ∧
      1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d ∧
      10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d ∧
      IsCompact (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      ∃ orc : (Fin d → ℚ) → ℕ → Bool,
        BitRAMO.WeakMemOracle (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) orc := by
  obtain ⟨hc, hv, -, -, ⟨orc, ho, -⟩, -⟩ :=
    UnifiedLower.LowerSanity.progU_hyps_satisfiable (10 ^ 8) ((10 ^ 8) ^ 10) (1 / 2)
  refine ⟨10 ^ 8, (10 ^ 8) ^ 10, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl,
    by norm_num, ?_, ?_, hc, hv, orc, ho⟩
  all_goals
    have hl : Real.log ((10 ^ 8 : ℕ) : ℝ) < 19 := by
      have := Minimax.MinimaxSanity.log_lt_of_lt_pow ((10 ^ 8 : ℕ) : ℝ) (by positivity) 19 (by norm_num) (by norm_num)
      exact_mod_cast this
    have hq : (1 - ((1 / 2 : ℚ) : ℝ)) / 2 = 1 / 4 := by push_cast; norm_num
    have hr := sq_le_rpow_three_halves (1 / 4 : ℝ) (by norm_num) (by norm_num)
    rw [hq]
    push_cast at hl ⊢
    nlinarith

open MeasureTheory RealRAM in
/-- The bound of `TheoremConj1LowerPolyDQ` is positive and at most `n / 2` on its regime. -/
theorem boundDQ_facts {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) :
    0 < 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ∧
      371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ n / 2 := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : ((d : ℝ) ^ 10) ≤ n := by exact_mod_cast hn
  have hlog := Lower.Sanity.log_ge_one hd
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have h32 : (d : ℝ) ^ (3 / 2 : ℝ) ≤ (d : ℝ) ^ 5 := by
    calc (d : ℝ) ^ (3 / 2 : ℝ) ≤ (d : ℝ) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
      _ = (d : ℝ) ^ 5 := by norm_cast
  have h5 : (d : ℝ) ^ 5 ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc ((d : ℝ) ^ 5) ^ 2 = (d : ℝ) ^ 10 := by ring
      _ ≤ (n : ℝ) := hn'
  have hs : 0 < Real.sqrt n := lt_of_lt_of_le (by positivity) h5
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
  have h1 : 0 < (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpos : 0 < 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by positivity
  refine ⟨div_pos hpos (by linarith), ?_⟩
  calc 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d
      ≤ 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := div_le_self hpos.le hlog
    _ ≤ 371 / 10 ^ 11 * Real.sqrt n * Real.sqrt n := by
        have := mul_le_mul_of_nonneg_right (h32.trans h5) hs.le
        nlinarith
    _ = 371 / 10 ^ 11 * n := by rw [mul_assoc, hsq]
    _ ≤ n / 2 := by
        have : (0 : ℝ) ≤ n := by positivity
        linarith

open MeasureTheory RealRAM in
/-- On every nonempty convex body, the zero strategy is in the class and fails the bound of `TheoremConj1LowerPolyDQ`
against every learner. -/
theorem zeroStrat_fails_of_nonemptyDQ {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : K.Nonempty) (hKc : Convex ℝ K) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pol : Lower.Learner Ω d) :
    (fun _ _ _ _ => 0 : Strategy d) ∈ Lower.StratsLip K n ∧
      ¬ 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, Lower.regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n ∂μ := by
  refine ⟨Lower.Sanity.zeroStrat_mem hKc n, ?_⟩
  have h0 : (fun ω => Lower.regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n) = fun _ => 0 :=
    funext fun ω => Lower.Sanity.regretAd_zero hK _ n
  rw [h0, integral_zero]
  exact not_le.2 (boundDQ_facts hd hn).1

end AdversarialBco.LowerDeltaQ.Sanity
