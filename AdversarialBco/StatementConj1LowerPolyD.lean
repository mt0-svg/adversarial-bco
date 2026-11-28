/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower
public import AdversarialBco.StatementConj1Poly

@[expose] public section

/-!
# Statement: Conjecture 1 of Bubeck, Eldan and Lee, lower half, on a polytope of their class, at `1.4·10^-9` (v2.4)

`TheoremConj1LowerPolyD` is the lower half of Conjecture 1 on a polytope
of release v2.3 (StatementConj1LowerPoly.lean, frozen for v2.1) word for word, its docstring included, with the
constant `7·10^-9` of the mean replaced by `1.4·10^-9`. Nothing is redefined: the game, the learners `Learner` and
their class `IsLearnerAd`, the strategy class `StratsLip` and the regret `regretAd` are those of `TheoremConj1Lower`
(StatementConj1Lower.lean), and the polytopes `polytope` and the height bound `HeightLE` those of
StatementConj1Poly.lean. The docstring of StatementConj1LowerPoly.lean of release v2.3 (the sentence of Conjecture 1,
the claim, the regime, the reading of the adversary, the learner, the adversary and the regret, the two halves on one
polytope, the junk values) applies to this statement unchanged, with `1.4·10^-9` in place of `7·10^-9`.

## The constant

In release v2.4 every lower bound in expectation is derived from the lower bound in probability. Clause (b) of
`TheoremLowerUD` (AdversarialBco/StatementMinimax.lean) gives, on every body of `BodyU` and against every measurable
randomised learner, a strategy of `StratsLowU K n r0` against which the regret is integrable with mean at least
`1.4·10^-9 d^{3/2} n^{1/2} / log d`: half of the threshold `2.8·10^-9 d^{3/2} n^{1/2} / log d` that clause (a) at
`δ = 1/2` reaches with probability `1/2`, the regret being nonnegative. The statement of release v2.3 has `7·10^-9`
from a separate mean argument (Theorem lowerbody), which v2.4 does not use. The proof of this statement is the cube
instance of clause (b): the cube `[-1, 1]^d` is a body of `BodyU` with `a = 0`, `r0 = 1`, `R0 = √d`, and a strategy
of `StratsLowU K n 1` (losses `1/4`-Lipschitz on `ℝ^d` with values in `[1/8, 7/8]` on `K`) is in `StratsLip K n`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open Lower RealRAM in
/-- The lower half of Conjecture 1 of Bubeck, Eldan and Lee on a polytope of their class, in the non-oblivious
reading (the paper's lower bound on a polytope): for every `d ≥ 4·10^6` there is a polytope `{x : A x ≤ b}` of `ℝ^d`
with `2 d` rational rows of height `1` that contains a closed unit ball (the proof's witness is the cube `[-1, 1]^d`)
such that, for every `n ≥ d^10`, its diameter is at most `n` and every measurable randomised learner with plays in it
meets a deterministic strategy that reads the past plays, with convex `1/4`-Lipschitz losses with values in `[0, 1]` on
it, against which the regret is integrable with mean at least `1.4·10^-9 d^{3/2} n^{1/2} / log d`. Nothing is claimed
for an oblivious adversary nor for the stochastic setting. -/
def TheoremConj1LowerPolyD : Prop :=
  ∀ d : ℕ, 4000000 ≤ d →
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
      m = 2 * d ∧ HeightLE A b 1 ∧ (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) ∧
      ∀ n : ℕ, d ^ 10 ≤ n →
        (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) ∧
        ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
        ∀ pol : Learner Ω d, IsLearnerAd (polytope A b) n pol →
          ∃ σ ∈ StratsLip (polytope A b) n,
            Integrable (fun ω => regretAd (polytope A b) σ (fun t => pol t ω) n) μ ∧
              14 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
                ∫ ω, regretAd (polytope A b) σ (fun t => pol t ω) n ∂μ

end AdversarialBco
