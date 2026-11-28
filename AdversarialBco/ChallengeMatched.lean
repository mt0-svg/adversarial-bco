/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-matched.json: AdversarialBco/StatementMatched.lean verbatim over the eleventh and
-- twelfth modules, Theorem UW, its three theorems, the reduction and seven non-vacuity witnesses, each proved by
-- `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are
-- expected.
module

public import AdversarialBco.ChallengeBase.StatementMinimaxQ
public import AdversarialBco.ChallengeBase.StatementUW

@[expose] public section

/-!
# Statement: the lower bound that grows with `log (1/δ)`, and the minimax theorem matched in `δ` (release v2.4)

Three claims over the statements StatementMinimaxQ.lean (the game, the values, the lower
bound with `δ` stopped on the bowl) and StatementUW.lean (the upper bound with `log (1/δ)` entering once), imported
unchanged; nothing is redefined:

* `TheoremGrowG`: Theorem GROW in its Gaussian form, for every learner on every
  body of `BodyU`: the `(1 - δ)`-quantile of the regret grows as `d (n log (1/δ))^{1/2}`;
* `TheoremGrowGProg`: the same for the programs of the oracle machine, in the objects of `TheoremUnified`, as
  `TheoremLowerUDProgQ` is for `TheoremLowerUDQ`;
* `TheoremMinimaxMatched`: the minimax values of the game of `TheoremMinimaxQ`, with the upper bounds of `TheoremUW`
  and the lower bounds of `TheoremLowerUDProgQ` and `TheoremGrowGProg`, so that the quantile value is bounded on both
  sides by `d^{3/2} n^{1/2} + d (n log (1/δ))^{1/2}` up to factors polylogarithmic in `d` and `n`.

## The growing lower bound (`TheoremGrowG`, `TheoremGrowGProg`)

On every body of `BodyU` and for every measurable randomised learner, for `d ≥ 4·10^6`, `log (1/δ) ≥ 60` and
`n ≥ d^6 log (1/δ)`: a strategy of `StratsLowU K n r0` against which the regret is measurable, nonnegative at every
seed, and at least `8·10^-6 d (n log (1/δ))^{1/2} / (log d (log n)^{1/2})` with probability strictly more than `δ`.
The strict inequality is written `∃ p, ENNReal.ofReal δ < p ∧ LowerProbNN … p` with the frozen `LowerProbNN`
(`ProgProbNN` for the programs); it is what the strict tail of the quantile asks. The strategy is the static dent of
Theorem GROW, no genie, with the tip drawn from the uniform law on the `2^d` vertices of `[-a, a]^d`,
`a = 1/(2 √d)`, which lie on the sphere of radius `1/2`, and with the
clamped Gaussian noise of Theorem LU, fixed in advance; the proof is a change of measure by the product of the
Gaussian round ratios, Jensen and Cauchy-Schwarz, the singular part of the clamp paid under the null world. Under the
slope condition of the dent after the affine placement of the body (checked at `R0 = d (120 log d + 68)`), its losses
lie in `[1/8, 3/4]` on `K`, so the strategy is one of Theorem LU's
class `StratsLowU`, and the regret is nonnegative on every run.
`TheoremGrowGProg` asks the same of every program that meets `MachineOK` on an input of `TheoremUnified`'s class: a
strategy in closed loop with the program, zero noise, on the program's coin space, an environment of `TheoremUnified`
with the program's windows. Its failure probability `δ'` is a real parameter apart from the confidence `δ` that the
program reads; at `δ' = δ` it is the form "with probability more than `δ`" that the quantile value reads.

## The minimax claim (`TheoremMinimaxMatched`)

The game, the learners, the payoffs and the values are those of StatementMinimax.lean (`Learners`, `LearnersB`,
`payoffs`, `valMean`, `valQuant`, `valMeanB`, `valQuantB`; their docstring applies unchanged). With
`Λ = d^{3/2} n^{1/2}` (here without the `1 / log d` of StatementMinimaxQ.lean),
`U_W = C (Λ log^5 (2 d n) + d (n log (2/δ))^{1/2} log^{9/2} (2 d n))` and `B = C' (d log (2 d n / δ) S)^k`, there are
constants `C`, `C'`, `k` such that for every input of `TheoremUnified`'s class:

* (attained) some learner within cost and space `B` (in `LearnersB B`) has every mean payoff at most `U_W + n δ` and
  every quantile payoff at most `U_W`, against every environment with its windows;
* (upper) `V⁺(G) ≤ V⁺_B(G) ≤ U_W + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U_W`;
* (lower, every `d` and `n`) `n^{1/2} / (4 √3) ≤ V⁺(G)`;
* (lower, `d ≥ 4·10^6` and `n ≥ d^10`) `3.71·10^-9 Λ / log d ≤ V⁺(G)`;
* (matched, `d ≥ 4·10^6`, `n ≥ d^10`, `δ < 1/2` and `log (1/δ) ≤ n / d^6`)
  `7·10^-9 (Λ / log d + d (n log (1/δ))^{1/2} / (log d (log n)^{1/2})) ≤ V_δ(G)`;
* (lower, `δ ≥ 1/2`) `7.42·10^-9 (1 - δ)^{3/2} Λ / log d ≤ V_δ(G)` under `((1 - δ)/2) d ≥ 1024 k₀` and
  `((1 - δ)/2)^{3/2} d ≥ 10 k₀`, `k₀ = 120 log d + 68`, the clause of `TheoremMinimaxQ` unchanged.

The matched clause asks `δ < 1/2`: its flat term comes from Theorem LU-DQ at the failure `1/2`, a probability `1/2`
that exceeds `δ` only there. For `δ ≥ 1/2` the last clause applies.

So on `d ≥ 4·10^6`, `n ≥ d^10`, `δ < 1/2`, `log (1/δ) ≤ n / d^6`, the quantile value lies between
`7·10^-9 (Λ / log d + d (n log (1/δ))^{1/2} / (log d (log n)^{1/2}))` and
`√2 C (Λ + d (n log (1/δ))^{1/2}) log^5 (2 d n)` (`log (2/δ) ≤ 2 log (1/δ)` for `δ ≤ 1/2`): the two sides agree in
`δ`, and differ by at most the factor `(√2 C / 7·10^-9) log^5 (2 d n) log d (log n)^{1/2}`, which does not depend on
`δ`. Inside the range the matched clause is at least the bound `7.42·10^-9 Λ / log d` of `TheoremMinimaxQ` up to the
factor `7 / 7.42`.

**The constant `7·10^-9`.** Write `X = Λ / log d`, `Y = d (n log (1/δ))^{1/2} / (log d (log n)^{1/2})`. Clause (a) of
`TheoremLowerUDProgQ` at the failure `1/2` (both range hypotheses hold for every `d ≥ 4·10^6`) gives every learner an
environment with `P(Reg_n ≥ 7.42·10^-9 Λ / log d) ≥ 1/2 > δ`, since
`2.1·10^-8 (1/2)^{3/2} = 7.4246·10^-9 ≥ 7.42·10^-9`; so `V_δ ≥ a X` with `a = 7.42·10^-9`. If `log (1/δ) ≥ 60`,
`TheoremGrowGProg` at `δ' = δ` gives `V_δ ≥ b Y` with `b = 8·10^-6` (its range `n ≥ d^6 log (1/δ)` is the hypothesis
`log (1/δ) ≤ n / d^6`); then `7·10^-9 (X + Y) ≤ (7·10^-9 / a) a X + (7·10^-9 / b) b Y ≤ (0.94340 + 0.000875) V_δ ≤ V_δ`.
If `log (1/δ) < 60`, `Y ≤ d (n log (1/δ))^{1/2} / log d < (60/d)^{1/2} X ≤ 0.003873 X` for `d ≥ 4·10^6`
(`(log n)^{1/2} ≥ 1`), so `7·10^-9 (X + Y) ≤ 7.0272·10^-9 X ≤ a X ≤ V_δ`. The mean bound `3.71·10^-9 Λ / log d` is the
probability `1/2` of the same clause (a) read through the tail, `n^{1/2} / (4 √3)` is clause (c) of
`TheoremLowerUDProgQ`, and the clause for `δ ≥ 1/2` is clause (a) at the failure `(1 - δ)/2`, with probability
`(1 + δ)/2 > δ`, as in `TheoremMinimaxQ`.

## What is not claimed

* An identity between the minimax value and the maximin value (`inf sup = sup inf`): the theorem bounds the minimax
  values from both sides.
* The polylogarithmic factors in `d` and `n` are not claimed optimal; the constants are not claimed optimal.
* The rate for `d < 4·10^6` or `n < d^10`, as in StatementUnifiedLower.lean; for every `d` and `n` the mean value is
  bounded below at the rate `n^{1/2}` only.
* The noisy game: the lower bounds use the noise `0`, which `TheoremUnified`'s class contains.

## Non-vacuity (AdversarialBco/Matched/Sanity.lean)

The structural hypotheses are those of the v2.3 theorems, satisfiable by `lowerU_hyps_satisfiable` and
`progU_hyps_satisfiable` (UnifiedLower/Sanity.lean); the hypotheses of the clause for `δ ≥ 1/2` are those of
`TheoremMinimaxQ` (`minimaxQ_high_hyps_satisfiable`). The arithmetic hypotheses added here have content:

* `growG_hyps_satisfiable`: the hypotheses of `TheoremGrowG` and `TheoremGrowGProg` (`log (1/δ) ≥ 60`,
  `n ≥ d^6 log (1/δ)`) hold at `d = 4·10^6`, `n = d^10`, `δ = 2^{-d^4}`, where `log (1/δ) = d^4 log 2` is close to the
  top `n / d^6 = d^4` of the range;
* `matched_hyps_satisfiable`: the hypotheses of the matched clause hold at the same `d`, `n` and the rational
  `δ = 2^{-d^4} < 1/2`, with `log (1/δ) ≥ 60`, so that `TheoremGrowGProg` is read, together with an input of
  `TheoremUnified`'s class: the unit ball about the rational centre `0` with a weak membership oracle;
* `growGProg_matched_hyps_satisfiable`: every hypothesis of `TheoremGrowGProg` (at `δ' = δ`) and of the matched clause
  holds at once at that point, with the unit ball about `0`, its exact membership oracle, and the program of three
  instructions that plays the centre in every round, which meets `MachineOK` with the windows `D = D' = 0`;
* `matched_exceeds_flat`: at that point the lower bound of the matched clause is more than `10^8` times the bound
  `7.42·10^-9 Λ / log d` of `TheoremMinimaxQ`, so the clause says more than the flat bound.

The Comparator configuration config-matched.json certifies `UW.theoremUW`, `Grow.theoremGrowG`,
`Grow.theoremGrowGProg`, `Matched.theoremMinimaxMatched`, the reduction `Matched.theoremMinimaxMatched_of` and the
seven witnesses.

## Junk values

`log d > 0` for `d ≥ 4·10^6`; `log n > 0` for `n ≥ d^10` and for `n ≥ 60 d^6`, so `(log n)^{1/2} > 0` and no
denominator is `0`. `log (1/δ)` is that of a positive number for `δ > 0` (`Real.log` takes `|x|`, so the hypothesis
`0 < δ` is written out); `log (1/δ) ≥ 60` and `δ > 0` give `δ < 1`. `log (2 d n) > 0` and `log (2/δ) > 0` as in
StatementUW.lean. Every power `x ^ (3 / 2 : ℝ)` and `x ^ (9 / 2 : ℝ)` is `Real.rpow` at a base `x > 0`. The junk values
of the values (`sSup`, `sInf` on empty or unbounded sets) are excluded as in StatementMinimax.lean: the claim asserts
a learner of `LearnersB B` with every payoff bounded and `V⁺(G) ≥ n^{1/2} / (4 √3) > 0`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open Lower UnifiedLower Minimax in
/-- **Theorem GROW, Gaussian form (Route G).** For every `d, n ≥ 1`, every compact convex `K` with
`B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, `0 < r0 ≤ R0`, every measurable randomised learner on `K`, and every `δ > 0` with
`d ≥ 4·10^6`, `log (1/δ) ≥ 60` and `n ≥ d^6 log (1/δ)`: a strategy of `StratsLowU K n r0` against which the regret is
measurable, nonnegative, and at least `8·10^-6 d (n log (1/δ))^{1/2} / (log d (log n)^{1/2})` with probability more
than `δ`. -/
def TheoremGrowG : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol →
    ∀ δ : ℝ, 0 < δ → 4000000 ≤ d → 60 ≤ Real.log (1 / δ) → (d : ℝ) ^ 6 * Real.log (1 / δ) ≤ n →
      ∃ p : ENNReal, ENNReal.ofReal δ < p ∧
        LowerProbNN K n r0 μ pol
          (8 / 10 ^ 6 * d * Real.sqrt (n * Real.log (1 / δ)) / (Real.log d * Real.sqrt (Real.log n))) p

open BitRAM BitRAMO Unified UnifiedLower Minimax in
/-- **Theorem GROW, Gaussian form, for the programs of the oracle machine, in the objects of `TheoremUnified`.** For
every program `P`, every input of `TheoremUnified`'s class and every weak membership oracle of `K`, if `P` meets
`MachineOK` with some bound `B` and windows `D`, `D'`, then for every `δ' > 0` with `d ≥ 4·10^6`, `log (1/δ') ≥ 60`
and `n ≥ d^6 log (1/δ')`: a strategy of `StratsLowU K n r0` in closed loop with `P` with the noise `0`, an environment
of `TheoremUnified` with the windows `D`, `D'` on the program's coin space, against which the regret `regretU` of `P`
is measurable, nonnegative, and at least `8·10^-6 d (n log (1/δ'))^{1/2} / (log d (log n)^{1/2})` with probability
more than `δ'`; the failure probability `δ'` is a real parameter, apart from the confidence `δ` that the program
reads. -/
def TheoremGrowGProg : Prop :=
  ∀ (P : List InstrO) (d : ℕ), 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
  ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
  ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
  ∀ (B : ℝ) (D D' : ℕ → ℕ), MachineOK P K orc (initU d n δ r0 R0 a) n B D D' →
  ∀ δ' : ℝ, 0 < δ' → 4000000 ≤ d → 60 ≤ Real.log (1 / δ') → (d : ℝ) ^ 6 * Real.log (1 / δ') ≤ n →
    ∃ p : ENNReal, ENNReal.ofReal δ' < p ∧
      ProgProbNN P K orc (initU d n δ r0 R0 a) n r0 D D'
        (8 / 10 ^ 6 * d * Real.sqrt (n * Real.log (1 / δ')) / (Real.log d * Real.sqrt (Real.log n))) p

open BitRAM BitRAMO Unified Minimax in
/-- **Theorem MM matched in `δ`.** Constants `C, C', k` such that, for every input of `TheoremUnified`'s class with
every weak membership oracle, with `Λ = d^{3/2} √n`, `U_W = C (Λ log^5(2dn) + d √(n log(2/δ)) log^{9/2}(2dn))` and
`B = C' (d log(2dn/δ) S)^k`: some learner within cost and space `B` has every mean payoff at most `U_W + n δ` and
every quantile payoff at most `U_W`; `V⁺(G) ≤ V⁺_B(G) ≤ U_W + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U_W`;
`√n / (4 √3) ≤ V⁺(G)`; and, if `d ≥ 4·10^6` and `n ≥ d^10`: `3.71·10^-9 Λ / log d ≤ V⁺(G)`,
`7·10^-9 (Λ / log d + d √(n log(1/δ)) / (log d √(log n))) ≤ V_δ(G)` for `δ < 1/2` with `log(1/δ) ≤ n / d^6`, and
`7.42·10^-9 (1 - δ)^{3/2} Λ / log d ≤ V_δ(G)` for `δ ≥ 1/2` with `((1 - δ)/2) d ≥ 1024 k₀` and
`((1 - δ)/2)^{3/2} d ≥ 10 k₀`, `k₀ = 120 log d + 68`. The minimax values are bounded from both sides; no identity
between the minimax and the maximin values is claimed. -/
def TheoremMinimaxMatched : Prop :=
  ∃ (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∃ ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k),
        (∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ,
          v ≤ C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
              d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) + n * (δ : ℝ)) ∧
        ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf (δ : ℝ)) ℓ,
          v ≤ C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
              d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ))) ∧
      valMean d n δ r0 R0 a K orc ≤
        valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
      valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ≤
        C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
            d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) + n * (δ : ℝ) ∧
      valQuant d n δ r0 R0 a K orc δ ≤
        valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ∧
      valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ≤
        C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
            d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) ∧
      Real.sqrt n / (4 * Real.sqrt 3) ≤ valMean d n δ r0 R0 a K orc ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valMean d n δ r0 R0 a K orc ∧
        ((δ : ℝ) < 1 / 2 → Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6 →
          7 / 10 ^ 9 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d +
              d * Real.sqrt (n * Real.log (1 / (δ : ℝ))) / (Real.log d * Real.sqrt (Real.log n))) ≤
            valQuant d n δ r0 R0 a K orc δ) ∧
        (1 / 2 ≤ (δ : ℝ) → 1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d →
          10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d →
          742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
            valQuant d n δ r0 R0 a K orc δ))

namespace UW

/-- **Theorem UW** (`TheoremUW`). -/
theorem theoremUW : TheoremUW := by
  sorry

end UW

namespace Grow

/-- **Route G** (`TheoremGrowG`). -/
theorem theoremGrowG : TheoremGrowG := by
  sorry

/-- **Route G for the programs of the oracle machine, in the objects of `TheoremUnified`** (`TheoremGrowGProg`). -/
theorem theoremGrowGProg : TheoremGrowGProg := by
  sorry

end Grow

namespace Matched

/-- **Theorem MM matched in `δ`** (`TheoremMinimaxMatched`). -/
theorem theoremMinimaxMatched : TheoremMinimaxMatched := by
  sorry

/-- **The matched minimax theorem from `TheoremUW`, `TheoremLowerUDProgQ` and `TheoremGrowGProg`.** -/
theorem theoremMinimaxMatched_of (hU : TheoremUW) (hLD : TheoremLowerUDProgQ) (hG : TheoremGrowGProg) :
    TheoremMinimaxMatched := by
  sorry

end Matched

namespace Matched.MatchedSanity

open BitRAM BitRAMO

/-- The hypotheses of `TheoremGrowG` and `TheoremGrowGProg` hold together at `d = 4·10^6`, `n = d^10`,
`δ = 2^{-d^4}`. -/
theorem growG_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ 4000000 ≤ d ∧ 60 ≤ Real.log (1 / δ) ∧
      (d : ℝ) ^ 6 * Real.log (1 / δ) ≤ n := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end Matched.MatchedSanity

namespace LowerDeltaQ.Sanity

open BitRAM BitRAMO

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
  sorry

end LowerDeltaQ.Sanity

namespace UnifiedLower.LowerSanity

open BitRAM BitRAMO Unified
open RealRAM (Strategy Strats regretPts)
open Lower (Learner IsLearnerAd regretAd)

/-- The hypotheses of `TheoremLowerU` hold for every `d` and `n`: the closed unit ball about `0` (`r0 = R0 = 1`) and
the constant learner `0` on `Unit` with the Dirac measure. -/
theorem lowerU_hyps_satisfiable (d n : ℕ) :
    BodyU (Metric.closedBall (0 : E d) 1) 0 1 1 ∧ IsProbabilityMeasure (Measure.dirac ()) ∧
      IsLearnerAd (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0 : Learner Unit d) := by
  sorry

/-- The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ`: the closed unit ball about the rational
centre `0` (`r0 = R0 = 1`) is compact and convex, has an exact membership oracle, which is a weak membership oracle;
and for every oracle the program `M (-1) := -2`, `play (-1)`, `jmp 1`, which plays the point `0` in every round and
reads no coin, meets `MachineOK` on the input with some cost bound `B` and the windows `D = D' = 0`. -/
theorem progU_hyps_satisfiable (d n : ℕ) (δ : ℚ) :
    IsCompact (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      ∀ orc : (Fin d → ℚ) → ℕ → Bool, ∃ B : ℝ,
        MachineOK [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)]
          (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc (initU d n δ 1 1 0) n B (fun _ => 0) (fun _ => 0) := by
  sorry

end UnifiedLower.LowerSanity

end AdversarialBco
