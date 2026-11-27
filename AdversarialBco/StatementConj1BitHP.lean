/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# Statement: Conjecture 1 of Bubeck, Eldan and Lee, first sentence, bit-cost model, high probability

Conjecture 1 of Bubeck, Eldan and Lee (arXiv 1607.03084, BEL16.tex l.86 to 88; J. ACM 68 (2021), Conjecture 1):
"There exists an algorithm such that each step takes poly(n log(T))-time (under the same assumption on K as in
Theorem 1) and which achieves E R_T = Õ(n^{1.5} √T)." The assumption of their Theorem 1 (l.82): "K is a polytope
described by poly(n) constraints whose coefficients are rational numbers with absolute values of numerators and
denominators bounded by poly(T)"; their normalisation (l.76): K contains a unit ball and has diameter at most T.
Their game (l.69 to 73): in each round the player selects `x_t ∈ K` and simultaneously an adversary selects a convex
loss `l_t : K → [0, 1]`; the feedback is `l_t(x_t)`; the player has external randomness and selects `x_t` from the
history `(x_s, l_s(x_s))_{s<t}`; `R_T = Σ_t l_t(x_t) - min_{x ∈ K} Σ_t l_t(x)`. In their letters `n` is the dimension
and `T` the horizon, here `d` and `n`.

`TheoremConj1UpperBitHP` is that sentence with time counted in bit operations, the regret bounded in expectation and
with high probability by the same program. It contains `TheoremConj1UpperBit` (StatementConj1Bit.lean: a measurable
majorant of the regret with mean at most the bound): the program, the input, the hypotheses and the three machine
clauses are its word for word, and the regret clauses are stronger (`theoremConj1UpperBit_of_hp`,
Conj1BitHP/Main.lean). The mean of the regret itself is at most the bound too, since it is at most the mean of the
positive part.

## The claim (`TheoremConj1UpperBitHP`)

There are one program `P` of the logarithmic-cost RAM of StatementBitRAM.lean, constants `C`, `C'` and an exponent
`k` such that for all `d ≥ 1`, `n ≥ 1`, `m`, `M`, every `A ∈ ℚ^{m × d}` and `b ∈ ℚ^m` whose entries have numerators
and denominators at most `M` in absolute value, whose polytope `K = {x : A x ≤ b}` contains a closed ball of radius `1`
and has diameter at most `n`, every probability space `(Θ, ρ)` of the adversary's seed and every randomised adaptive
adversary `σ` on `K` for `n` rounds (`RandAdv`), the run of `P` on the input `d, n, m, A, b` (`initBit`) satisfies,
with `L = log (2 d n)`, `B = C' (d m L log (2 M))^k`, `Reg` the regret of the run on `K` against the losses that the
adversary chose on that run, as a function of the seed `θ` and the coin sequence `cs`, and `ℙ = ρ ⊗ coinStream`:

* (machine) on every run (every seed `θ` and every coin sequence `cs`) each round `t < n`, the first included, is
  played within cost `B` of the state from which it is awaited, at every step before the play of round `n - 1` the
  cells in use have total bit length at most `B`, and every point played in a round `t < n` lies in `K`;
* (expectation) `Reg` is measurable and integrable for `ℙ`, and the mean of its positive part is at most
  `C d^{3/2} n^{1/2} L^5`: `∫ max (Reg, 0) dℙ ≤ C d^{3/2} n^{1/2} L^5`;
* (high probability) `ℙ (Reg > C d^{3/2} n^{1/2} L^5) ≤ 1/n`: with probability at least `1 - 1/n` over the seed and
  the coins, `Reg ≤ C d^{3/2} n^{1/2} L^5`.

In BEL's letters: for `m` at most a power of the dimension and `M` at most a power of the horizon, every step has a
cost, on the logarithmic-cost RAM, polynomial in `n log T`, a Turing machine simulates every step in time polynomial in
`n log T` (StatementBitRAM.lean, "Why this is a bit-cost model"), `E R_T ≤ E max (R_T, 0) ≤ C n^{3/2} T^{1/2}
log^5 (2 n T)`, which is `Õ(n^{1.5} √T)`, and `R_T ≤ C n^{3/2} T^{1/2} log^5 (2 n T)` with probability at least
`1 - 1/T`. For every `m` and `M` the cost and the space of a step are polynomial in `d`, `m`, `log n` and `log M`.

The expectation is the Bochner integral of the real function `max (Reg, 0)`; `Reg` is asserted integrable, so
`max (Reg, 0)` is integrable too and the integral is not the junk value `0` of a non-integrable function. The mean of
the regret itself follows: `∫ Reg dℙ ≤ ∫ max (Reg, 0) dℙ`. The mean of the positive part is the quantity of
`TheoremConj1UpperBit`, whose majorant `R` can be taken `max (Reg, 0)` here.

## The input (`inputMem`, `initBit`)

The polytope and the bound `M` are those of StatementConj1Poly.lean (`polytope`, `HeightLE`):
every `m` (no bound on the number of facets), every `M`, and BEL's two normalisations as hypotheses, the ball of radius
`1` centred anywhere (the centre is not given to the program) and the diameter bound written with `dist`. The program
reads integers: the cells `0`, `1`, `2` hold `d`, `n`, `m`; the entry `e = (d + 1) i + j` of the rows
`(A i 0, ..., A i (d - 1), b i)`, `i < m`, `j ≤ d`, has its numerator in lowest terms in the cell `3 + 2 e` and its
denominator in the cell `4 + 2 e`; every other cell is `0`. The program is not told `M`; the lengths of the data are
what the program pays to read. `M` stays in the statement as BEL's height bound: the cost bound is polynomial in
`log M`, and a height polynomial in the horizon makes it polynomial in `d`, `m` and `log n`.

## The game (`GameBit`, `stepBit`, `runBit`, `playedBit`)

The adversary is a strategy `σ θ` for each seed `θ` (`Strategy`, StatementConj1.lean): the loss of round `t` is
`σ θ t x o`, a function of the points `x 0, ..., x (t - 1)` played and the feedbacks `o 0, ..., o (t - 1)` of the
rounds before `t`. The game has no noise, as BEL's: the feedback of round `u` is `l_u (x_u)` exactly, rebuilt by
`obsAd σ 0`. At each step the machine runs in the world whose loss of round `t` is `lossAd (σ θ) 0 x t`, `x` the
points the state records as played; the coins are the run's coin sequence. So the loss of round `t` is fixed by the
seed and the rounds before `t`, before the point of round `t` exists: the adversary moves simultaneously with the
player, and is adaptive. `playedBit` is the point of round `t` as a point of `E d` (`0` for a round that never comes,
which the cost clause excludes for `t < n`).

## The feedback interface

The program reads the feedback `o` of the last round played through the instruction `obs`: the integer `⌊2^p o⌋`,
its first `p` binary digits (`o ∈ [0, 1]` on the plays in `K`), at a cost of `p` plus the length of the result, `p`
chosen by the program at run time, as often as it likes until its next play. Every reading is a function of
`l_t(x_t)`, so the program learns nothing BEL's player does not. The coins are read through the instruction `coins`,
a block of `k` fair coins at cost `k` (StatementBitRAM.lean).

## The adversary (`RandAdv`)

A seed `θ` is drawn from a probability measure `ρ` on any measurable space `Θ`, independently of the program's coins,
and the adversary plays the strategy `σ θ`. It reads the points and the exact feedbacks of the earlier rounds, never
the program's coins: BEL's player "has access to external randomness", and their filtration
`F_t = σ(l_1, x_1, ..., l_t, x_t, l_{t+1})` (l.656) is generated by the plays and the losses alone. The deterministic
strategies are the case `Θ = Unit`, and the oblivious sequences the strategies that read nothing. `(Θ, σ)` comes after
the program and the instance, so it may depend on `P`, `d`, `n`, `A`, `b`. What `RandAdv` asks, for every round
`t < n` and every rational history `q` of points: the loss of round `t` on that history, `lossAd (σ θ) 0 q t`, is a
convex function `K → [0, 1]` (`AdmLoss`) for every seed, and at each point `y ∈ K` it is a measurable function of the
seed. The second condition says that `l_t(y)` is a random variable for every player that plays rational points
(StatementConj1Bit.lean, "The adversary", gives the argument), which BEL's filtration presupposes.

## The regret, the expectation and the probability

The regret of a run is `regretPts K (lossAd (σ θ) 0 x) x n`, `x` the points played: `Σ_{t < n} l_t (x_t)` minus the
infimum over `K` of `Σ_{t < n} l_t`, against the losses chosen on that run (StatementConj1.lean). The infimum is BEL's
minimum when it is attained, and is at most every value, so this regret is at least `R_T`. The law is the product
`ρ ⊗ coinStream` on `Θ × (ℕ → Bool)`, the seed independent of the coins, which are fair and independent
(`coinStream`, StatementBitRAM.lean); it is a probability measure when `ρ` is. The measurability of the regret in
`(θ, cs)` is asserted, for the product of the σ-algebra of `Θ` and the product σ-algebra of the coin sequences, so the
event `{Reg > C d^{3/2} n^{1/2} L^5}` is measurable and the probability clause bounds its probability.

The confidence `1/n` is fixed by the statement: the same program, which is told `d`, `n`, `m`, `A`, `b` and nothing
else, meets the expectation clause and the probability clause at once.

## The cost clause (`CostOKBit`)

For every step `k` at which fewer than `n` rounds have been played, some later step plays one more round, and the cost
spent between the two is at most `B`. Applied at the step after the play of round `t - 1` (at step `0` for `t = 0`),
it bounds the cost of round `t` by `B`: every round, the first included, costs at most `B`, and nothing is amortised.
Since `cost` never decreases and a halted machine never plays, it also forces all `n` rounds to be played on every
run. Besides the digits of `d`, `n` and `m`, the input has at most `2 m (d + 1) (1 + log₂ M)` binary digits,
polynomially many in the quantities of `B`, so a program can read all of it within one round.

## The space clause (`SpaceOKBit`)

At every step at which fewer than `n` rounds have been played, so at every step of every round up to the play of
round `n - 1`, the cells in use (`SpaceLE`, StatementBitRAM.lean: the cells with a nonzero content, their addresses and
contents) have total bit length at most the same `B`. Together with the cost clause, it bounds the time of a Turing
machine that simulates a round by a polynomial in `d`, `m`, `log n` and `log M`. The input is in the memory and is
counted: its cells in use have total bit length at most `N (len N + len d + len n + len m + len M)` with
`N = 3 + 2 (d + 1) m` (`input_space_nat`, Conj1Bit/Sanity.lean). The points played are output and are not counted.

## Non-vacuity

The hypotheses are satisfiable in every dimension by a randomised adversary whose strategy depends on its seed
(`hyps_satisfiable_exists`, Conj1Bit/Sanity.lean), a deterministic strategy with admissible losses is a randomised
adversary on `Unit` with no measurability asked (`randAdv_unit`), and the empty program fails the cost clause
(`nil_not_costOKBit`); the Comparator configuration of this statement certifies the three next to the theorem.

## What is not claimed

A confidence `δ` chosen by the user: the probability clause is at `δ = 1/n`, and a bound `ℙ (Reg > C d^{3/2}
n^{1/2} log^5 (2 d n / δ)) ≤ δ` for every `δ` would need a program that reads `δ`. The second sentence of the
conjecture (StatementConj1Lower.lean). A noisy feedback (the conjecture's game has none). An adversary that reads the
program's coins (an adversary that reads the current draw forces regret `n/4`). Convex bodies other than the rational
polytopes of the conjecture: `TheoremConj1Upper` (StatementConj1.lean) covers them on the real RAM.

## Junk values

`log (2 d n) ≥ log 2 > 0` for `d, n ≥ 1`, and `1/n ∈ (0, 1]`. `log (2 M)`: the hypotheses force `m ≥ 1` (with no row
the polytope is the whole space, of unbounded diameter) and then `M ≥ 1` (a denominator is at least `1`), so
`log (2 M) ≥ log 2 > 0`. A negative `C'` makes `B` negative, and the cost clause then fails at step `0` (the cost never
decreases), as does the space clause (`SpaceLE s B` is false for `B < 0`), so it cannot help; a negative `C` makes the
bound negative, which only makes both regret clauses harder (the positive part has a nonnegative mean). `playedBit` is
`0` for a round that never comes, and the cost clause makes every round `t < n` come on every run. The junk values of
the machine are listed in StatementBitRAM.lean, those of the input in StatementConj1Bit.lean.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open BitRAM in
open RealRAM (Strategy lossAd regretPts polytope HeightLE) in
/-- **Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in the bit-cost model, in expectation and with high
probability.** One program `P` of the logarithmic-cost RAM with fair coins and constants `C, C', k` such that, on every
input of `TheoremConj1UpperBit` (the dimension, the horizon, the number of constraints and the rational constraints of a
polytope that contains a unit ball and has diameter at most `n`) and against every randomised adaptive adversary `σ`
with seed law `ρ`: on every seed and coin sequence `P` plays `n` rounds, each within cost
`C' (d m log(2dn) log(2M))^k` with its cells in use of total bit length within the same bound, at points of the
polytope; the regret, as a function of the seed and the coins, is measurable and integrable for `ρ ⊗ coinStream`, the
mean of its positive part is at most `C d^{3/2} √n log(2dn)^5`, and it exceeds `C d^{3/2} √n log(2dn)^5` with
probability at most `1/n`. -/
def TheoremConj1UpperBitHP : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ,
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), HeightLE A b M →
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) →
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) →
    ∀ (Θ : Type) [MeasurableSpace Θ] (ρ : Measure Θ), IsProbabilityMeasure ρ →
    ∀ σ : Θ → Strategy d, RandAdv (polytope A b) n σ →
      (∀ (θ : Θ) (cs : ℕ → Bool),
        CostOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
          SpaceOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
          ∀ t < n, playedBit P ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b) ∧
      Measurable (fun ω : Θ × (ℕ → Bool) =>
          regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
            (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n) ∧
      Integrable (fun ω : Θ × (ℕ → Bool) =>
          regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
            (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n) (ρ.prod coinStream) ∧
      ∫ ω, max (regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
            (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n) 0 ∂(ρ.prod coinStream) ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 ∧
      (ρ.prod coinStream) {ω | C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 <
          regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
            (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n} ≤ ENNReal.ofReal (1 / n)

end AdversarialBco
