/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-conj1-exp.json: AdversarialBco/StatementConj1Exp.lean verbatim over the copies of the
-- statement files it imports, and its theorems proved by `sorry` (code/formal-proof/challenges.sh). Nothing
-- imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1

@[expose] public section

/-!
# The statement of Theorem 1.1: Conjecture 1 of Bubeck, Eldan and Lee, upper half, in expectation

Conjecture 1 of Bubeck, Eldan and Lee (arXiv 1607.03084) bounds the expected regret by `Õ(d^{3/2} n^{1/2})`.
`TheoremConj1Upper` (StatementConj1.lean) bounds the regret with probability `1 - δ`, for a program that reads `δ`.
`TheoremConj1UpperExp` is its expected form, their `Õ` bound with the fifth power of the logarithm: the same program
run with `δ = 1/(n + 1)`, and an outer expectation of the positive part of the regret at most
`C d^{3/2} n^{1/2} L^5 + 1`, `L = log (2 d n (n + 1))`. It is not the bound `C d^{3/2} n^{1/2} ln^{3/2} (n diam K)` of
Corollary 1.6 of the paper and does not imply it: the power of the logarithm is `5`, not `3/2`, and `L` carries
`log d`. Everything it uses is defined in StatementConj1.lean and StatementPoly.lean, unchanged.

## The statement (`TheoremConj1UpperExp`)

There are one program `P` of the machine of StatementPoly.lean, constants `C`, `C'` and an exponent `k` such that for
all `d ≥ 1`, `n ≥ 1`, `0 < r₀ ≤ R₀`, every compact convex `K` with `closedBall 0 r₀ ⊆ K ⊆ closedBall 0 R₀`, every
strategy `σ ∈ Strats K n` and every noise law `ν` with `NoiseOK ν`, with `L = log (2 d n (n + 1))` and the program
started from `init d n r₀ R₀ (1/(n + 1))`:

* on every run the first play comes within `C' (d L (2 + log (R₀/r₀)))^k` steps, every later round within
  `C' (d L)^k` steps of the round before, and every point played is in `K`: the cost clause of `TheoremConj1Upper`
  at `δ = 1/(n + 1)`, word for word after the identity `2 d n / δ = 2 d n (n + 1)`;
* there is a measurable `R : Ω → ℝ≥0` on `Ω = (ℕ → ℝ) × (ℕ → ℝ)` (the Gaussian stream and the noise) with
  `Reg ω ≤ R ω` on every run and `∫ R d(gaussStream ⊗ ν) ≤ C d^{3/2} n^{1/2} L^5 + 1`, the regret `Reg ω` being taken
  against the losses that the strategy chose on that run, as in `TheoremConj1Upper`.

The quantifiers are those of `TheoremConj1Upper` without `δ`. A fixed sequence of `Advs K n` is a constant strategy
of the class (`constStrat_mem`, AdversarialBco/Conj1/Poly32O.lean), so the claim covers every oblivious sequence.

## The choice of `δ`

`δ = 1/(n + 1)` is in `(0, 1)` for every `n ≥ 1`, where `TheoremConj1Upper` asks `0 < δ < 1`; `δ = 1/n` would leave
`n = 1` outside. Then `2 d n / δ = 2 d n (n + 1)`, so `L ≤ log (4 d n²)` and the bound is
`C d^{3/2} n^{1/2} log^5 (4 d n²) + 1`, polylogarithmic over `d^{3/2} n^{1/2}` as in the conjecture. The cost bounds
stay polynomial in `d` and `log n`, the first also in `log (R₀/r₀)`. The term `+ 1` is `n δ < 1`: on every run the
regret is at most `n` (each loss of round `t < n` has values in `[0, 1]` on `K`, every point played is in `K`, and the
infimum over `K` of the sum of the losses is at least `0`), and the runs above the high-probability bound have outer
measure at most `δ`. The `+ 1` does not weaken the `Õ` form: for `d, n ≥ 1`, `d^{3/2} n^{1/2} L^5 ≥ (log 4)^5 > 5`,
so the bound `+ 1` is at most `(C + 1/5) d^{3/2} n^{1/2} L^5` for `C ≥ 0`.

## The expectation

The regret is not proved measurable in the run, and it need not be: a loss of the class is convex on `K` with values
in `[0, 1]`, which leaves its values on the boundary of `K` free up to convexity (on a ball, any values on the sphere
between those of the lower semicontinuous hull and `1`), so it can be a non-measurable function there, and
`TheoremConj1Upper` says nothing of where the points played fall. Two readings are therefore excluded:

* the Bochner integral of the regret, which is `0` for a function that is not integrable (a junk value);
* the `lintegral` of the regret, which for a function that is not measurable is a lower integral (the supremum of the
  integrals of the measurable simple functions below it) and can be far below what an expectation should bound.

The statement takes the upper integral instead: a measurable majorant `R` of the regret whose integral is at most the
bound `+ 1`, that is, the outer expectation of the positive part of the regret is at most the bound `+ 1`. Three
choices make it strong: `R` is real valued, so it is integrable and its Bochner integral is at most the bound `+ 1`;
`R ≥ 0`, so it bounds the positive part of the regret, not only the regret; `Reg ω ≤ R ω` holds for every `ω`. When
the regret is integrable, its expectation is at most `∫ R`, hence at most the bound `+ 1`.

## Junk values

Those of `TheoremConj1Upper`. `1 / ((n : ℝ) + 1)` is the real quotient, in `(0, 1/2]` for `n ≥ 1`; the argument of
the logarithm is a real number at least `4`, so `L ≥ log 4 > 0`. `ENNReal.ofReal` sends a negative number to `0`; a
negative `C` only lowers the bound, so it cannot make the claim easier, and `C ≥ 0` gives a bound at least `1`. `R`
takes values in `ℝ≥0`, never `∞`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace AdversarialBco

open RealRAM in
/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee in expectation, against a non-anticipating adversary: the
program of `TheoremConj1Upper` run with `δ = 1/(n + 1)` has every point played in `K`, a number of steps per round
polynomial in `d` and `log (2 d n (n + 1))`, the first round also in `log (R₀/r₀)`, and an outer expectation of the
positive part of the regret at most `C d^{3/2} n^{1/2} log^5 (2 d n (n + 1)) + 1`: a measurable `R ≥ 0` above the
regret on every run, with that integral. -/
def TheoremConj1UpperExp : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 : ℝ, 0 < r0 → r0 ≤ R0 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ σ ∈ Strats K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ,
        CostOKAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1))) n
            (C' * ((d : ℝ) * Real.log (2 * d * n * ((n : ℝ) + 1)) * (2 + Real.log (R0 / r0))) ^ k)
            (C' * ((d : ℝ) * Real.log (2 * d * n * ((n : ℝ) + 1))) ^ k) ∧
          ∀ t < n, playedAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1))) t ∈ K) ∧
      ∃ R : (ℕ → ℝ) × (ℕ → ℝ) → ℝ≥0, Measurable R ∧
        (∀ ω : (ℕ → ℝ) × (ℕ → ℝ),
          regretPts K (lossAd σ ω.2 (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1)))))
              (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1)))) n ≤ R ω) ∧
        ∫⁻ ω, (R ω : ENNReal) ∂(gaussStream.prod ν) ≤
          ENNReal.ofReal (C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n * ((n : ℝ) + 1)) ^ 5 + 1)

/-- Theorem 1.1: the theorem that the solution module `AdversarialBco.Conj1Exp.Main` proves. -/
theorem theoremConj1UpperExp : TheoremConj1UpperExp := by
  sorry

/-- Remark 1.2 implies Theorem 1.1. -/
theorem theoremConj1UpperExp_of_conj1 : TheoremConj1Upper → TheoremConj1UpperExp := by
  sorry

end AdversarialBco
