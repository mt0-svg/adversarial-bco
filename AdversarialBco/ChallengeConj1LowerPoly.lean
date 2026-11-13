/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-conj1-lower-poly.json: AdversarialBco/StatementConj1LowerPoly.lean verbatim over the
-- copies of the statement files it imports, its theorem and two non-vacuity witnesses, each proved by `sorry`
-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Lower
public import AdversarialBco.ChallengeBase.StatementConj1Poly

@[expose] public section

/-!
# The frozen statement of the lower bound on a polytope: Conjecture 1 of Bubeck, Eldan and Lee, lower half, on a
polytope of their class

The paper's lower bound on a polytope; its proof on paper is the cube case of the lower bound on a body between two
balls. Nothing is
redefined: the game, the learners `Learner` and their class `IsLearnerAd`, the strategy class `StratsLip` and the
regret `regretAd` are those of StatementConj1Lower.lean, and the polytopes `polytope` and the
height bound `HeightLE` those of StatementConj1Poly.lean.

## The sentence

Conjecture 1 of Bubeck, Eldan and Lee (arXiv 1607.03084, BEL16.tex l.86 to 88), after its first sentence: "Furthermore
no algorithm can achieve a better regret bound for large n and T." The assumption on K of the first sentence is that of
their Theorem 1 (l.82): "K is a polytope described by poly(n) constraints whose coefficients are rational numbers with
absolute values of numerators and denominators bounded by poly(T)"; their normalisations (l.76): K contains a unit ball
and has diameter at most T. In their letters `n` is the dimension and `T` the horizon; here `d` and `n`.

## The claim (`TheoremConj1LowerPoly`)

For every `d ≥ 4·10^6` there is a polytope `K = {x : A x ≤ b}` of `ℝ^d` given by `m = 2 d` rational rows whose entries,
in lowest terms, have numerators and denominators at most `1` in absolute value (`HeightLE A b 1`), and which contains
a closed ball of radius `1`, such that for every `n ≥ d^10` the diameter of `K` is at most `n` and every learner of
`IsLearnerAd K n` meets a strategy of `StratsLip K n` against which its regret is integrable with mean at least
`7·10^-9 d^{3/2} n^{1/2} / log d`.

The statement asserts a polytope of the class and does not name it. The witness of the proof is the cube `[-1, 1]^d`,
the rows `± e_j` with right-hand sides `1`; AdversarialBco/Conj1Poly/Sanity.lean shows that it meets every
condition of the class (`cube_height`, `cube_ball`, `cube_diam`). The polytope comes before the horizon and the
learner, so a learner that knows it is covered.

Why one polytope and not every polytope of the class: "no algorithm can achieve a better regret bound" denies an upper
bound over the class, so it says that for every algorithm the worst case of `E R_T` over the instances of the class
(bodies and adversaries) is at least of order `n^{1.5} T^{1/2}` up to logarithms; one polytope of the class on which
every learner meets such an adversary is that worst case. The upper statements (`TheoremConj1UpperBit`,
`TheoremConj1UpperBitExp`) quantify over every polytope of the class because an upper bound must hold on every instance;
a lower bound needs one.

The class conditions are those of the upper statements, in the same forms: `HeightLE A b 1` is BEL's height bound with
the polynomial `1`, `m = 2 d` their `poly(n)` constraints with the polynomial `2 d`, the closed ball of radius `1`
(centred anywhere) and the diameter bound, written with `dist` and asserted for every `n` of the regime, their two
normalisations.

## The regime

The bound holds for every `d ≥ 4·10^6` and every `n ≥ d^10`, with explicit constants. No bound of this form can hold
for `n` below about `d^3`: the regret is at most `n`, the losses taking values in `[0, 1]` on `K`. For `n` above `d^10`
it rules out every upper bound `C d^a n^{1/2} polylog(d n)` with `a < 3/2` (take `n = d^10` and `d` large), which is
the second sentence for large `n` and `T`. It leaves open a better bound confined to `d^3 ≤ n < d^10`.
The loss `log d` is a polylogarithm in `d` only, inside the `Õ` of the first sentence.

## The reading of the adversary

This is the second sentence in its non-oblivious reading. The loss of round `t` is chosen from the points played
before `t`, as BEL's game allows (BEL16 l.69: the adversary selects `l_t` with no restriction stated; the filtration of
their analysis, l.656, `F_t = σ(l_1, x_1, ..., l_t, x_t, l_{t+1})`, lets `l_{t+1}` depend on the rounds up to `t`).
Bubeck, Eldan and Lee also tie the conjecture to a setting that this statement does not cover, zeroth order
stochastic convex optimization: the abstract (l.62), "For the simpler situation of zeroth order stochastic convex
optimization this corresponds to the conjecture that the optimal query complexity is of order n^3/ε^2", and l.129,
"this might be the optimal guarantee for this problem (see Conjecture 1)". Nothing is claimed for an oblivious
adversary (a sequence fixed in advance, an open question) nor for the stochastic setting.
A lower bound against adaptive adversaries says nothing on those, so this statement is weaker than what the authors tie
the conjecture to, and every summary of it says "in the non-oblivious reading" next to "second sentence of Conjecture
1".

## The learner, the adversary, the regret

As in StatementConj1Lower.lean, whose docstring gives the details.
A learner is a seed `ω` drawn from a probability measure
`μ` on any measurable space and a play rule, jointly measurable in the seed, the past points and the past observations,
with values in `K` for the rounds `t < n`: every randomised algorithm of BEL's game whose `E R_T` is defined. A strategy
of `StratsLip K n` is deterministic, its loss of round `t` a function of the points played before `t`, convex with
values in `[0, 1]` on `K` and `1/4`-Lipschitz on `K` for every history, measurable in the history at each point of `K`;
it comes after the learner. These restrictions are on the existential side, so they strengthen the claim. `regretAd` is
BEL's `R_T` (l.73) against the losses chosen on that run, in the noiseless game, with `sInf` over `K` for the minimum
(attained here: the losses are Lipschitz on the compact `K`); the mean is over the learner's seed, which is all the
randomness of a game against a deterministic strategy. The proof's strategy is `(σ/d^{1/2})`-Lipschitz on the cube with
`σ = 1/(8 (6 log n)^{1/2})`, far inside `1/4`.

## The two halves on one polytope

`TheoremConj1UpperBit` holds on every polytope of the class, the cube included, against every strategy of its adversary
class, and a strategy of `StratsLip K n` is one of them: it is in `Strats K n` by definition, so its losses are
admissible, and a deterministic strategy with admissible losses is a randomised adaptive adversary with the seed space
`Unit` (`randAdv_unit`, AdversarialBco/Conj1Bit/Sanity.lean). On the learner side, a program of
`TheoremConj1UpperBit` is a learner of `IsLearnerAd` on the cube by an argument that this file does not prove: run
with fair coins (`Ω = ℕ → Bool`, `μ = coinStream`), after its play is redefined on the observation sequences outside
`[0, 1]^t` (a Borel set), on every observation sequence in `[0, 1]^t` it plays in `K` within its budget (the cost and
plays-in-`K` clauses of `TheoremConj1UpperBit` for the oblivious constant strategy with those values, an adversary of
`RandAdv` with the seed space `Unit`); its play is a countable decision tree on cylinder sets of the coins and on the
Borel sets `{⌊2^p o_s⌋ = j}`, hence measurable; and the redefinition changes no run against `StratsLip K n`, whose
observations lie in `[0, 1]`.

## Junk values

Those of StatementConj1Lower.lean: `Real.log d > 0` since `d ≥ 4·10^6`, `(d : ℝ) ^ (3/2 : ℝ)` is the ordinary power
since `d > 0`, and the Bochner integral of a non-integrable function is `0`, so the claim asserts integrability and the
integral is the mean. The `sInf` of `regretPts` is over the values of `Σ_{t < n} f_t` on `K`, a nonempty set (`K`
contains a ball) bounded below by `0` for a strategy of the class. `HeightLE` reads the entries in lowest terms (`Rat`
is normalised), so the bound `1` allows exactly the entries `-1`, `0`, `1`. `Fin m` with `m = 2 d` has `2 d` rows.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open Lower RealRAM in
/-- The lower half of Conjecture 1 of Bubeck, Eldan and Lee on a polytope of their class, in the non-oblivious
reading (the paper's lower bound on a polytope): for every `d ≥ 4·10^6` there is a polytope `{x : A x ≤ b}` of `ℝ^d`
with `2 d` rational rows of height `1` that contains a closed unit ball (the proof's witness is the cube `[-1, 1]^d`)
such that, for every `n ≥ d^10`, its diameter is at most `n` and every measurable randomised learner with plays in it
meets a deterministic strategy that reads the past plays, with convex `1/4`-Lipschitz losses with values in `[0, 1]` on
it, against which the regret is integrable with mean at least `7·10^-9 d^{3/2} n^{1/2} / log d`. Nothing is claimed for
an oblivious adversary nor for the stochastic setting. -/
def TheoremConj1LowerPoly : Prop :=
  ∀ d : ℕ, 4000000 ≤ d →
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
      m = 2 * d ∧ HeightLE A b 1 ∧ (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) ∧
      ∀ n : ℕ, d ^ 10 ≤ n →
        (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) ∧
        ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
        ∀ pol : Learner Ω d, IsLearnerAd (polytope A b) n pol →
          ∃ σ ∈ StratsLip (polytope A b) n,
            Integrable (fun ω => regretAd (polytope A b) σ (fun t => pol t ω) n) μ ∧
              7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
                ∫ ω, regretAd (polytope A b) σ (fun t => pol t ω) n ∂μ

/-- The lower bound on a polytope: the theorem that the solution module `AdversarialBco.Conj1LowerPoly.Main` proves. -/
theorem theoremConj1LowerPoly_holds : TheoremConj1LowerPoly := by
  sorry

namespace Lower.Sanity

open RealRAM

/-- On every body `K` with a point `c`, the constant learner that plays `c` is a learner of the class, for every `n`. -/
theorem constLearner_mem_of_mem {d : ℕ} {K : Set (E d)} {c : E d} (hc : c ∈ K) (n : ℕ) :
    IsLearnerAd (Ω := Unit) K n (fun _ _ _ _ => c) := by
  sorry

/-- On every nonempty body, the zero strategy fails the bound against every learner. -/
theorem zeroStrat_fails_of_nonempty {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : K.Nonempty) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pol : Learner Ω d) :
    ¬ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n ∂μ := by
  sorry

end Lower.Sanity

end AdversarialBco
