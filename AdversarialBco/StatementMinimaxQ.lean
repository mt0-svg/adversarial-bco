/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementMinimax
public import AdversarialBco.StatementConj1LowerPolyD

@[expose] public section

/-!
# Statement: the lower bound with `δ` stopped on the bowl, and the minimax theorem at its constants (release v2.4)

Four claims over the statements
StatementMinimax.lean and StatementConj1LowerPolyD.lean (imported unchanged; nothing is redefined: the game, the values,
`LowerProbNN`, `ProgProbNN` and the polytopes are theirs), with the constants of the lower bound with `δ` stopped on the
bowl (Theorem LU-DQ and its corollaries):

* `TheoremLowerUDQ`: `TheoremLowerUD` with the range and the threshold of Theorem LU-DQ in clause (a) and the mean
  `3.71·10^-9` in clause (b);
* `TheoremLowerUDProgQ`: the same for the programs of the oracle machine, in the objects of `TheoremUnified`, as
  `TheoremLowerUDProg` is for `TheoremLowerUD`;
* `TheoremMinimaxQ`: `TheoremMinimax` with the lower bounds read from `TheoremLowerUDProgQ`;
* `TheoremConj1LowerPolyDQ`: `TheoremConj1LowerPolyD` at `3.71·10^-9`.

`TheoremMinimaxQ` bounds the minimax values from both sides: each value is an infimum over the learners of a supremum
over the environments, and the theorem places it between two explicit functions of `d`, `n` and `δ`. It is not an
identity `inf sup = sup inf` between the minimax and the maximin values, which is not claimed.

## The lower bound with `δ` (`TheoremLowerUDQ`, `TheoremLowerUDProgQ`)

With `Λ = d^{3/2} n^{1/2} / log d`, `k₀ = 120 log d + 68` and `δ₀ = min(δ, 1/2)`, on every body of `BodyU` and for
every measurable randomised learner:

* (a) for `0 < δ < 1`, `d ≥ 4·10^6`, `n ≥ d^10`, `δ₀ d ≥ 1024 k₀` and `δ₀^{3/2} d ≥ 10 k₀`, a strategy of
  `StratsLowU K n r0` against which the regret is measurable, nonnegative at every seed, and at least
  `2.1·10^-8 δ₀^{3/2} Λ` with probability at least `1 - δ` (`LowerProbNN`);
* (b) for `d ≥ 4·10^6` and `n ≥ d^10`, a strategy of the class against which the regret is integrable with mean at
  least `3.71·10^-9 Λ` (`LowerMean`);
* (c) clause (c) of `TheoremLowerU`, unchanged.

At `δ = 1/2` both range conditions of (a) hold for every `d ≥ 4·10^6`, and the threshold of (a) is
`2.1·10^-8 · 2^{-3/2} Λ = 7.4246·10^-9 Λ`. The constant `3.71·10^-9` of every mean bound here is half of it rounded
down (`1/2` times the threshold reached with probability `1/2` by a nonnegative regret): the expectation form is
derived from the probability form. `TheoremLowerUDProgQ` asks the same of every
program that meets `MachineOK` on an input of `TheoremUnified`'s class, with `ProgProbNN` and `ProgMean`: a strategy in
closed loop with the program, zero noise, on the program's coin space, an environment of `TheoremUnified` with the
program's windows. Its failure probability `δ'` is a real parameter apart from the confidence `δ` that the program
reads; at `δ' = δ` it is the form "with probability `1 - δ`" of `TheoremUnified`.

## The game (`ProgWin`, `Learners`, `LearnersB`, `payoffs`)

The game `G` is the input `(d, n, δ, r0, R0, a)` of `TheoremUnified` with a body `K` and a weak membership oracle `orc`
of `K`.

* A learner is a program `P` of the oracle machine with two coin windows `D`, `D'` (`ProgWin`) that meets, on the input
  `initU d n δ r0 R0 a`, three of the machine clauses of `TheoremUnified` (`MachineOK` of StatementUnifiedLower.lean,
  the hypothesis of `TheoremLowerUProg`): on every world whose losses are admissible on `K` in the rounds `t < n`, every
  round within some cost `B`, the plays of the rounds `t < n` in `K`, and the coin windows `D`, `D'`. These are the
  learners of `Learners`. `LearnersB B` asks clause (i) of `TheoremUnified` with the bound `B`: cost `B` per round,
  space `B`, plays in `K`, the windows; so `LearnersB B ⊆ Learners`.
* An adversary of the learner `(P, D, D')` is an environment of clause (ii) of `TheoremUnified` with its windows: a
  probability space `(Ω, μ)`, any `Ω : Type`, with the program's coins, the losses and the noises, a `NoisyAdv` with
  the windows `D`, `D'`. The learner's choice of windows is part of its move: `D'` is pinned by the coin clause (the
  number of coins read when round `t` is played), and `D t` is at least the number read when round `t - 1` is played;
  a larger `D t` only enlarges the class of adversaries.
* The payoff is a function of the tail of the regret (`tailU`): `u ↦ μ {Reg_n > u}`, with `Reg_n = regretU`, the
  regret of `TheoremUnified`. Two payoffs: the `(1 - δ')`-quantile `quantileOf δ' T = inf {u | T u ≤ δ'}` and the mean
  of the positive part `meanPosOf T = ∫_0^∞ T u du`.

The quantile value is the minimax `(1 - δ)`th quantile of Ma, Verchand and Samworth (High-probability minimax lower
bounds, arXiv 2406.13447), the infimum of the `r ∈ [0, ∞)` with `P{L ≤ r} ≥ 1 - δ`, the same set as `P(L > r) ≤ δ`;
Bongole, Zamani, Oechtering and Skoglund (Minimax quantile lower bounds for interactive statistical decision making with
privacy, arXiv 2606.23096) call it the strict minimax quantile, with `r ∈ [0, ∞]`. In both the infimum over the
learners is outside the supremum over the environments, and a learner may depend on the level. Their losses are
nonnegative; the regret here can be negative, and `u` ranges over the reals. The value is the same as with `u ≥ 0`:
every learner has the environment with the constant loss `0` and the noise `0`, where its regret and its quantile are
`0`.

## The values (`value`, `valMean`, `valQuant`, `valMeanB`, `valQuantB`)

`value L pay = inf_{ℓ ∈ L} sup_{environments of ℓ} pay (tail)`, with `sInf` and `sSup` on sets of reals.

* `valMean G = V⁺(G)`: the infimum over the learners of the supremum over their environments of `E max(Reg_n, 0)`.
* `valQuant G δ' = V_{δ'}(G)`: the same with the `(1 - δ')`-quantile of `Reg_n`. In the theorem `δ' = δ`, the
  confidence that the program reads; the definition keeps them apart.
* `valMeanB G B`, `valQuantB G B δ'`: the infimum over `LearnersB B` only, the learners within cost and space `B`.

## The minimax claim (`TheoremMinimaxQ`)

There are constants `C`, `C'` and `k` such that for every input of `TheoremUnified`'s class (`d, n ≥ 1`, rationals
`0 < δ < 1`, `0 < r0 ≤ R0`, a rational centre `a`, a compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, a weak
membership oracle `orc` of `K`), with `U = C d^{3/2} n^{1/2} log^5 (2 d n / δ)`, `B = C' (d log (2 d n / δ) S)^k`,
`Λ = d^{3/2} n^{1/2} / log d` and `k₀ = 120 log d + 68`:

* (attained) some learner within cost and space `B` (in `LearnersB B`) has every mean payoff at most `U + n δ` and
  every quantile payoff at most `U`, against every environment with its windows;
* (upper) `V⁺(G) ≤ V⁺_B(G) ≤ U + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U`;
* (lower, every `d` and `n`) `n^{1/2} / (4 √3) ≤ V⁺(G)`;
* (lower, `d ≥ 4·10^6` and `n ≥ d^10`) `3.71·10^-9 Λ ≤ V⁺(G)`; `7.42·10^-9 Λ ≤ V_δ(G)` if `δ < 1/2`; and
  `7.42·10^-9 (1 - δ)^{3/2} Λ ≤ V_δ(G)` if `δ ≥ 1/2`, `((1 - δ)/2) d ≥ 1024 k₀` and `((1 - δ)/2)^{3/2} d ≥ 10 k₀`.

So for `d ≥ 4·10^6`, `n ≥ d^10` and `δ < 1/2` the two values are `d^{3/2} n^{1/2}` up to the factor
`log d · log^5 (2 d n / δ)` (and the additive `n δ` for the mean), and a learner within cost and space `B` per round
reaches them up to that factor. The lower bounds on the quantile value come from a probability strictly above `δ`:
`P(Reg_n ≥ L) ≥ 1/2 > δ` (clause (a) of `TheoremLowerUDProgQ` at the failure `1/2`), and `P(Reg_n ≥ L) ≥ (1 + δ)/2 > δ`
(clause (a) of `TheoremLowerUDProgQ` at the failure `(1 - δ)/2`); the strict inequality is what the strict tail asks.
The constant `7.42·10^-9` is `2.1·10^-8 · 2^{-3/2} = 7.4246·10^-9` rounded down: the threshold of clause (a) at the
failure `1/2`, and at the failure `(1 - δ)/2` it is
`2.1·10^-8 ((1 - δ)/2)^{3/2} Λ = 2.1·10^-8 · 2^{-3/2} (1 - δ)^{3/2} Λ`. The lower bound `3.71·10^-9 Λ` on the mean
value is the probability `1/2` of clause (a) at the failure `1/2` read through the tail; the bound `n^{1/2} / (4 √3)`
is clause (c) of `TheoremLowerUDProgQ` with `E max(Reg_n, 0) ≥ E Reg_n`.

## Why tails, and the outer measure

Both payoffs are read from the tail `u ↦ μ {Reg_n > u}`, the probability form, and the mean is its integral, the
layer cake formula `E max(X, 0) = ∫_0^∞ P(X > u) du`. When `Reg_n` is measurable, `meanPosOf` of its tail is
`∫ max(Reg_n, 0) dμ` (the layer cake formula; sanity module, `meanPosOf_tail_eq_integral`) and `quantileOf δ'` is
`inf {u | P(Reg_n ≤ u) ≥ 1 - δ'}`, the left-continuous `(1 - δ')`-quantile of `Reg_n`. Off the measurable sets `μ` is
Mathlib's outer measure, so both payoffs are defined for every learner. The theorem does not depend on that reading:
the upper bounds read only the program of `TheoremUnified`, whose regret `TheoremUnified` asserts measurable on every
environment of its class, and each lower bound reads, for each learner, one environment in which its regret is
measurable or integrable (`ProgProb`, `ProgMean`, `ProgProbNN`), a lower bound on the supremum. So both bounds hold for
every reading of `E max(Reg_n, 0)` and of the quantile that agrees with the usual one on measurable regrets. No
integral here has a junk value: `∫⁻` is defined for every function.

## What is not claimed

* An identity between the minimax value and the maximin value (`inf sup = sup inf`): the theorem bounds the minimax
  values from both sides.
* A match in `δ`: the lower bounds do not grow with `log (1/δ)` (that of (a) decreases as `min(δ, 1/2)^{3/2}`), while
  the upper bound carries `log^5 (2 d n / δ)`. The item "A lower bound that depends on `δ`" of the frozen
  StatementUnifiedLower.lean is covered by (a), in the range of (a).
* Failure probabilities below the range of (a): (a) needs `δ₀ d ≥ 1024 k₀` and `δ₀^{3/2} d ≥ 10 k₀`, that is
  `δ ≥ δ_min(d) = max(1024 k₀/d, (10 k₀/d)^{2/3})` (and `δ_min(d) ≤ 1/2` for `d ≥ 4·10^6`).
* The rate `d^{3/2} n^{1/2} / log d` for `d < 4·10^6` or `n < d^10`, as in StatementUnifiedLower.lean; for every `d`
  and `n` the mean value is bounded below at the rate `n^{1/2}` only.
* The noisy game: the lower bounds use the noise `0`, which `TheoremUnified`'s class contains.

## Non-vacuity (AdversarialBco/LowerDeltaQ/Sanity.lean)

The structural hypotheses are those of the v2.3 theorems, satisfiable by `lowerU_hyps_satisfiable` and
`progU_hyps_satisfiable` (UnifiedLower/Sanity.lean). The arithmetic hypotheses added here have content:

* (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ` needs the failure probability `δ` (`δ'` in
  `TheoremLowerUDProgQ`) at least `δ_min(d)`; `δ_min(4·10^6) ≈ 0.48441`, so at `d = 4·10^6` it holds only for
  `δ ≥ δ_min(4·10^6)`, and `δ_min(d)` decreases to `0` as `d` grows (`δ_min(10^8) = 0.02333`,
  `δ_min(10^9) = 0.002616`); witnesses `lowerUDQ_a_hyps_satisfiable` (`d = 10^7`, `n = d^10`, `δ = 1/2`) and
  `lowerUDQ_a_small_hyps_satisfiable` (`d = 10^8`, `n = d^10`, `δ = 1/20`, where both range hypotheses depend on `δ`).
* The last clause of `TheoremMinimaxQ` (`δ ≥ 1/2`) has `(1 - δ)/2 ≤ 1/4`, so it needs `d/4 ≥ 1024 k₀` (and
  `d/8 ≥ 10 k₀`, weaker), which holds exactly from `d = 8 097 148` on; at `d = 10^8` it holds for
  `δ ∈ [1/2, 0.9533]`; witness `minimaxQ_high_hyps_satisfiable` (`d = 10^8`, `n = d^10`, `δ = 1/2`, the unit ball about
  the rational centre `0` with its exact membership oracle).
* `TheoremConj1LowerPolyDQ`: the witnesses of `TheoremConj1LowerPolyD` at `3.71·10^-9`: the class of learners is not
  empty (`constLearner_mem_of_mem`, Conj1LowerPolyD/Sanity.lean), the bound is positive and at most `n / 2` on the
  regime (`boundDQ_facts`), and the zero strategy of the class fails it against every learner
  (`zeroStrat_fails_of_nonemptyDQ`).

The witnesses are proved in Lean from `e > 2.7182818283`, `x^2 ≤ x^{3/2}` on `(0, 1]` and exact rational arithmetic. The
certificates of the frozen statement apply unchanged: the payoffs of every learner form nonempty sets inside `[0, n]`
(mean) and `[-n, n]` (quantile, `δ' < 1`) (`payoffs_bounded`), and `meanPosOf` of the tail of an almost everywhere
strongly measurable function is the integral of its positive part (`meanPosOf_tail_eq_integral`). The Comparator
configuration config-minimax-q.json certifies them next to the theorems.

## Junk values

`sSup` and `sInf` on `ℝ` are `0` on a set that is empty or unbounded. Every learner of `Learners` has environments with
any windows (the constant loss with zero noise), and its regret lies in `[-n, n]` on every run (losses in `[0, 1]` on
`K`, plays in `K`), so its payoffs form a nonempty set in `[-n, n]` (in `[0, n]` for the mean; for the quantile the
level is `δ' < 1`, since at `δ' ≥ 1` every `u` qualifies). The claim asserts a learner of `LearnersB B`, which lies in
`Learners`, so every `sSup` and `sInf` in the claim is that of a nonempty bounded set; the attained clause bounds every
payoff of that learner, with no `sSup`; and the claim asserts `V⁺(G) ≥ n^{1/2} / (4 √3) > 0`, which no junk `0` meets.
`meanPosOf` takes `toReal` of an integral at most `n`. `log (2 d n / δ) > 0`; `log d > 0` for `d ≥ 4·10^6`. A negative
`C` lowers `U` and makes the upper bounds harder. `min δ (1/2)` is the minimum of two reals; `ENNReal.ofReal (1 - δ)` is
`1 - δ` for `δ < 1`. Every power `x ^ (3 / 2 : ℝ)` is `Real.rpow` at a base `x > 0` (`d ≥ 1`; `min δ (1/2) > 0` for
`δ > 0`; `1 - δ > 0` and `(1 - δ)/2 > 0` for `δ < 1`), where it is the usual `x^{3/2}`. In `LowerProbNN` and
`ProgProbNN` the measure of `{c ≤ Reg}` is asserted only next to the measurability of the regret.

## `TheoremConj1LowerPolyDQ`

`TheoremConj1LowerPolyDQ` is `TheoremConj1LowerPolyD` (AdversarialBco/StatementConj1LowerPolyD.lean, frozen for v2.4)
word for word, its docstring included, with the constant `1.4·10^-9` of the mean replaced by `3.71·10^-9`. Nothing is
redefined: the game, the learners `Learner` and their class `IsLearnerAd`, the strategy class `StratsLip` and the
regret `regretAd` are those of `TheoremConj1Lower` (StatementConj1Lower.lean), and the polytopes `polytope` and the
height bound `HeightLE` those of StatementConj1Poly.lean. The docstring of
StatementConj1LowerPoly.lean of release v2.3 (the sentence of Conjecture 1, the claim, the regime, the reading of the
adversary, the learner, the adversary and the regret, the two halves on one polytope, the junk values) applies to this
statement unchanged, with `3.71·10^-9` in place of `7·10^-9`.

The constant: clause (b) of `TheoremLowerUDQ` gives, on every body of `BodyU` and against every measurable randomised
learner, a strategy of `StratsLowU K n r0` against which the regret is integrable with mean at least
`3.71·10^-9 d^{3/2} n^{1/2} / log d`: half of the threshold `7.4246·10^-9 d^{3/2} n^{1/2} / log d`, rounded down, that
clause (a) at `δ = 1/2` reaches with probability `1/2`, the regret being nonnegative. The proof of this statement is the
cube instance of clause (b): the cube `[-1, 1]^d` is a body of `BodyU` with `a = 0`, `r0 = 1`, `R0 = √d`, and a
strategy of `StratsLowU K n 1` (losses `1/4`-Lipschitz on `ℝ^d` with values in `[1/8, 7/8]` on `K`) is in
`StratsLip K n`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open Lower UnifiedLower Minimax in
/-- **Theorem LU-DQ.** For every `d, n ≥ 1`, every compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, `0 < r0 ≤ R0`,
and every measurable randomised learner on `K`, with `Λ = d^{3/2} n^{1/2} / log d`, `k₀ = 120 log d + 68` and
`δ₀ = min(δ, 1/2)`: (a) for `0 < δ < 1`, `d ≥ 4·10^6`, `n ≥ d^10`, `δ₀ d ≥ 1024 k₀` and `δ₀^{3/2} d ≥ 10 k₀`, a
strategy of `StratsLowU K n r0` against which the regret is measurable, nonnegative, and at least `2.1·10^-8 δ₀^{3/2} Λ`
with probability at least `1 - δ`; (b) for `d ≥ 4·10^6` and `n ≥ d^10`, a strategy of the class with integrable regret
of mean at least `3.71·10^-9 Λ`; (c) a strategy of the class with mean regret at least `n^{1/2} / (4 √3)`, and one with
regret at least `n^{1/2} / (8 √3)` with probability at least `1/48`. -/
def TheoremLowerUDQ : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol →
      (∀ δ : ℝ, 0 < δ → δ < 1 → 4000000 ≤ d → d ^ 10 ≤ n →
        1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d →
        10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d →
        LowerProbNN K n r0 μ pol
          (21 / 10 ^ 9 * min δ (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)
          (ENNReal.ofReal (1 - δ))) ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        LowerMean K n r0 μ pol (371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) ∧
      LowerMean K n r0 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      LowerProb K n r0 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified UnifiedLower Minimax in
/-- **Theorem LU-DQ for the programs of the oracle machine, in the objects of `TheoremUnified`.** For every program
`P`, every input of `TheoremUnified`'s class and every weak membership oracle of `K`, if `P` meets `MachineOK` with some
bound `B` and windows `D`, `D'`, then, for each of the clauses (a), (b), (c) of `TheoremLowerUDQ`, a strategy of
`StratsLowU K n r0` in closed loop with `P` with the noise `0`, an environment of `TheoremUnified` with the windows
`D`, `D'` on the program's coin space, against which the regret `regretU` of `P` satisfies that clause; the failure
probability `δ'` of (a) is a real parameter, apart from the confidence `δ` that the program reads. -/
def TheoremLowerUDProgQ : Prop :=
  ∀ (P : List InstrO) (d : ℕ), 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
  ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
  ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
  ∀ (B : ℝ) (D D' : ℕ → ℕ), MachineOK P K orc (initU d n δ r0 R0 a) n B D D' →
    (∀ δ' : ℝ, 0 < δ' → δ' < 1 → 4000000 ≤ d → d ^ 10 ≤ n →
      1024 * (120 * Real.log d + 68) ≤ min δ' (1 / 2) * d →
      10 * (120 * Real.log d + 68) ≤ min δ' (1 / 2) ^ (3 / 2 : ℝ) * d →
      ProgProbNN P K orc (initU d n δ r0 R0 a) n r0 D D'
        (21 / 10 ^ 9 * min δ' (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)
        (ENNReal.ofReal (1 - δ'))) ∧
    (4000000 ≤ d → d ^ 10 ≤ n →
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D'
        (371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) ∧
    ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (4 * Real.sqrt 3)) ∧
    ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified Minimax in
/-- **Theorem MM at the constants of Theorem LU-DQ.** Constants `C, C', k` such that, for every input of
`TheoremUnified`'s class with every weak membership oracle, with `U = C d^{3/2} √n log(2dn/δ)^5`,
`B = C' (d log(2dn/δ) S)^k`, `Λ = d^{3/2} √n / log d` and `k₀ = 120 log d + 68`: some learner within cost and space
`B` has every mean payoff at most `U + n δ` and every quantile payoff at most `U`; `V⁺(G) ≤ V⁺_B(G) ≤ U + n δ` and
`V_δ(G) ≤ V_{δ,B}(G) ≤ U`; `√n / (4 √3) ≤ V⁺(G)`; and, if `d ≥ 4·10^6` and `n ≥ d^10`, `3.71·10^-9 Λ ≤ V⁺(G)`,
`7.42·10^-9 Λ ≤ V_δ(G)` for `δ < 1/2`, and `7.42·10^-9 (1 - δ)^{3/2} Λ ≤ V_δ(G)` for `δ ≥ 1/2` with
`((1 - δ)/2) d ≥ 1024 k₀` and `((1 - δ)/2)^{3/2} d ≥ 10 k₀`. The minimax values are bounded from both sides; no
identity between the minimax and the maximin values is claimed. -/
def TheoremMinimaxQ : Prop :=
  ∃ (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∃ ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k),
        (∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ)) ∧
        ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf (δ : ℝ)) ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5) ∧
      valMean d n δ r0 R0 a K orc ≤
        valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
      valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ) ∧
      valQuant d n δ r0 R0 a K orc δ ≤
        valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ∧
      valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 ∧
      Real.sqrt n / (4 * Real.sqrt 3) ≤ valMean d n δ r0 R0 a K orc ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valMean d n δ r0 R0 a K orc ∧
        ((δ : ℝ) < 1 / 2 →
          742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valQuant d n δ r0 R0 a K orc δ) ∧
        (1 / 2 ≤ (δ : ℝ) → 1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d →
          10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d →
          742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
            valQuant d n δ r0 R0 a K orc δ))

open Lower RealRAM in
/-- The lower half of Conjecture 1 of Bubeck, Eldan and Lee on a polytope of their class, in the non-oblivious
reading (the paper's lower bound on a polytope): for every `d ≥ 4·10^6` there is a polytope `{x : A x ≤ b}` of `ℝ^d`
with `2 d` rational rows of height `1` that contains a closed unit ball (the proof's witness is the cube `[-1, 1]^d`)
such that, for every `n ≥ d^10`, its diameter is at most `n` and every measurable randomised learner with plays in it
meets a deterministic strategy that reads the past plays, with convex `1/4`-Lipschitz losses with values in `[0, 1]` on
it, against which the regret is integrable with mean at least `3.71·10^-9 d^{3/2} n^{1/2} / log d`. Nothing is claimed
for an oblivious adversary nor for the stochastic setting. -/
def TheoremConj1LowerPolyDQ : Prop :=
  ∀ d : ℕ, 4000000 ≤ d →
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
      m = 2 * d ∧ HeightLE A b 1 ∧ (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) ∧
      ∀ n : ℕ, d ^ 10 ≤ n →
        (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) ∧
        ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
        ∀ pol : Learner Ω d, IsLearnerAd (polytope A b) n pol →
          ∃ σ ∈ StratsLip (polytope A b) n,
            Integrable (fun ω => regretAd (polytope A b) σ (fun t => pol t ω) n) μ ∧
              371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
                ∫ ω, regretAd (polytope A b) σ (fun t => pol t ω) n ∂μ

end AdversarialBco
