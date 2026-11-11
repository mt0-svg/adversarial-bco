/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-conj1-poly-exp.json: AdversarialBco/StatementConj1PolyExp.lean verbatim over the copies of the
-- statement files it imports, and its theorems proved by `sorry` (code/formal-proof/challenges.sh). Nothing
-- imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Poly

@[expose] public section

/-!
# The statement of Theorem 1.3 (b): Conjecture 1 of Bubeck, Eldan and Lee, upper half, on polytopes, in expectation

The upper half of Conjecture 1 of Bubeck, Eldan and Lee (arXiv 1607.03084) with the input of their Theorem 1, a
polytope given by rational constraints, and their measure of performance, the expected regret, `Õ(d^{3/2} n^{1/2})`
with the fifth power of the logarithm. It is `TheoremConj1UpperPoly` (StatementConj1Poly.lean, Theorem 1.3 (a)), which
bounds the regret with probability `1 - δ` for a program that reads `δ`, in expectation: the same program run with
`δ = 1/(n + 1)`, and an outer expectation of the positive part of the regret at most `C d^{3/2} n^{1/2} L^5 + 1`,
`L = log (2 d n (n + 1))`. It is not the bound `C d^{3/2} n^{1/2} ln^{3/2} (n diam K)` of Corollary 1.6 of the paper
and does not imply it: the power of the logarithm is `5`, not `3/2`, and `L` carries `log d`. Everything it uses is
defined in StatementConj1Poly.lean, StatementConj1.lean, StatementPoly.lean and Statement.lean, unchanged.
`TheoremConj1UpperExp` (StatementConj1Exp.lean, Theorem 1.1) is the same expected form for the membership-oracle
model of `TheoremConj1Upper`.

## The claim (`TheoremConj1UpperPolyExp`)

There are one program `P` of the machine of StatementPoly.lean with no `query` instruction, constants `C`, `C'` and an
exponent `k` such that for all `d ≥ 1`, `n ≥ 1`, `m`, `M`, every `A ∈ ℚ^{m × d}` and `b ∈ ℚ^m` whose entries have
numerators and denominators at most `M` in absolute value, whose polytope `K = {x : A x ≤ b}` contains a closed ball of
radius `1` and has diameter at most `n`, every strategy `σ ∈ Strats K n` and every noise law `ν` with `NoiseOK ν`, with
`L = log (2 d n (n + 1))` and the program started from `initPoly d n m (1/(n + 1)) A b`:

* on every run the first play comes within `C' (d m L log (2 M))^k` steps, every later round within `C' (d m L)^k`
  steps of the round before, and every point played in a round `t < n` is in `K`: the cost clause of
  `TheoremConj1UpperPoly` at `δ = 1/(n + 1)`, word for word after the identity `2 d n / δ = 2 d n (n + 1)`;
* there is a measurable `R : Ω → ℝ≥0` on `Ω = (ℕ → ℝ) × (ℕ → ℝ)` (the Gaussian stream and the noise) with
  `Reg ω ≤ R ω` on every run and `∫ R d(gaussStream ⊗ ν) ≤ C d^{3/2} n^{1/2} L^5 + 1`, the regret `Reg ω` being taken
  on `K` against the losses that the strategy chose on that run, as in `TheoremConj1UpperPoly`.

The quantifiers, the polytope input, the model (`QueryFree`) and the cost clause are those of `TheoremConj1UpperPoly`
without `δ`. A fixed sequence of `Advs K n` is a constant strategy of the class (`constStrat_mem`,
AdversarialBco/Conj1/Poly32O.lean), so the claim covers every oblivious sequence. In BEL's letters (`n` their
dimension, `T` their horizon; here `d` and `n`): every step takes a number of machine steps polynomial in `n`, `m` and
`log T`, the first also in `log (2 M)`, and the outer expectation of the positive part of the regret is at most
`C n^{3/2} T^{1/2} log^5 (4 n T^2) + 1`.

## The choice of `δ`

`δ = 1/(n + 1)` is in `(0, 1)` for every `n ≥ 1`, where `TheoremConj1UpperPoly` asks `0 < δ < 1`. The hypotheses force
`n ≥ 2` (a closed unit ball has two points at distance `2`, and `K` has diameter at most `n`), so `δ = 1/n` would be
admissible too; `1/(n + 1)` keeps the form of `TheoremConj1UpperExp` and needs no case analysis on the hypotheses.
Then `2 d n / δ = 2 d n (n + 1)`, so `L ≤ log (4 d n²)`. The term `+ 1` is `n δ < 1`: on every run the regret is at
most `n` (each loss of round `t < n` has values in `[0, 1]` on `K`, every point played in a round `t < n` is in `K`,
and the infimum over `K` of the sum of the losses is at least `0`), and the runs above the high-probability bound have
outer measure at most `δ`. The `+ 1` does not weaken the `Õ` form: for `d, n ≥ 1`,
`d^{3/2} n^{1/2} L^5 ≥ (log 4)^5 > 5`, so the bound `+ 1` is at most `(C + 1/5) d^{3/2} n^{1/2} L^5`.

## The expectation

The regret is not proved measurable in the run: that would need the measurability of the run of the existential
program in the stream and the noise, which `TheoremConj1UpperPoly` does not export, and the joint measurability of the
losses in the history and the point. A loss of the class is constrained on the boundary of `K` only by convexity and
by `[0, 1]`: its values there are not those of the interior (the loss `0` inside and `1` on the boundary is in the
class). Two readings are therefore excluded:

* the Bochner integral of the regret, which is `0` for a function that is not integrable (a junk value);
* the `lintegral` of the regret, which for a function that is not measurable is a lower integral (the supremum of the
  integrals of the measurable simple functions below it) and can be far below what an expectation should bound.

The statement takes the upper integral instead: a measurable majorant `R` of the regret whose integral is at most the
bound `+ 1`, that is, the outer expectation of the positive part of the regret is at most the bound `+ 1`. Three
choices make it strong: `R` is real valued, so it is integrable and its Bochner integral is at most the bound `+ 1`;
`R ≥ 0`, so it bounds the positive part of the regret, not only the regret; `Reg ω ≤ R ω` holds for every `ω`. When
the regret is integrable, its expectation is at most `∫ R`, hence at most the bound `+ 1`.

## Junk values

Those of `TheoremConj1UpperPoly`. `1 / ((n : ℝ) + 1)` is the real quotient, in `(0, 1/2]` for `n ≥ 1`; the argument of
the logarithm `L` is a real number at least `4`, so `L ≥ log 4 > 0`. `ENNReal.ofReal` sends a negative number to `0`; a
negative `C` only lowers the bound, so it cannot make the claim easier, and `C ≥ 0` gives a bound at least `1`. `R`
takes values in `ℝ≥0`, never `∞`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace AdversarialBco

open RealRAM in
/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee on their polytopes, in expectation, against a
non-anticipating adversary: the program of `TheoremConj1UpperPoly`, with no membership oracle, run with
`δ = 1/(n + 1)` on the rational constraints of a polytope that contains a unit ball and has diameter at most `n`, has
every point played in the polytope, a number of steps per round polynomial in `d`, `m` and `log (2 d n (n + 1))`, the
first round also in `log (2 M)`, and an outer expectation of the positive part of the regret at most
`C d^{3/2} n^{1/2} log^5 (2 d n (n + 1)) + 1`: a measurable `R ≥ 0` above the regret on every run, with that
integral. -/
def TheoremConj1UpperPolyExp : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ), QueryFree P ∧
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ,
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), HeightLE A b M →
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) →
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) →
    ∀ σ ∈ Strats (polytope A b) n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ,
        CostOKAd P ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m (1 / ((n : ℝ) + 1)) A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n * ((n : ℝ) + 1)) * Real.log (2 * M)) ^ k)
            (C' * ((d : ℝ) * m * Real.log (2 * d * n * ((n : ℝ) + 1))) ^ k) ∧
          ∀ t < n, playedAd P ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m (1 / ((n : ℝ) + 1)) A b) t ∈
            polytope A b) ∧
      ∃ R : (ℕ → ℝ) × (ℕ → ℝ) → ℝ≥0, Measurable R ∧
        (∀ ω : (ℕ → ℝ) × (ℕ → ℝ),
          regretPts (polytope A b)
              (lossAd σ ω.2 (playedAd P ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m (1 / ((n : ℝ) + 1)) A b)))
              (playedAd P ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m (1 / ((n : ℝ) + 1)) A b)) n ≤ R ω) ∧
        ∫⁻ ω, (R ω : ENNReal) ∂(gaussStream.prod ν) ≤
          ENNReal.ofReal (C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n * ((n : ℝ) + 1)) ^ 5 + 1)

/-- Theorem 1.3 (b): the theorem that the solution module `AdversarialBco.Conj1PolyExp.Main` proves. -/
theorem theoremConj1UpperPolyExp : TheoremConj1UpperPolyExp := by
  sorry

/-- Theorem 1.3 (a) implies Theorem 1.3 (b). -/
theorem theoremConj1UpperPolyExp_of_poly : TheoremConj1UpperPoly → TheoremConj1UpperPolyExp := by
  sorry

end AdversarialBco
