/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenges, third module: AdversarialBco/StatementConj1Poly.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1

@[expose] public section

/-!
# The polytopes of Bubeck, Eldan and Lee: definitions of the frozen statements

The input of Theorem 1 of Bubeck, Eldan and Lee (arXiv 1607.03084): a polytope given by rational constraints
(`polytope`) and the bound on the heights of its data (`HeightLE`), which the bit-model statement
(StatementConj1Bit.lean) and the lower bound on a polytope (StatementConj1LowerPoly.lean) use.

* `polytope A b = {x ∈ ℝ^d : ∀ i, Σ_j A i j x_j ≤ b i}`, the polytope of Bubeck, Eldan and Lee ("K is a polytope
  described by poly(n) constraints whose coefficients are rational numbers with absolute values of numerators and
  denominators bounded by poly(T)").
* `HeightLE A b M`: every entry of `A` and of `b`, in lowest terms (`Rat.num`, `Rat.den`), has a numerator and a
  denominator of absolute value at most `M`.
* Their two normalisations, hypotheses of the statements that use these definitions: `K` contains a closed ball of
  radius `1` (centred anywhere), and any two points of `K` are at distance at most `n` ("for normalization purposes we
  assume that the diameter of K is at most T"). The second is written with `dist`, since `Metric.diam` is `0` on an
  unbounded set; it makes `K` bounded.

Junk values. `HeightLE` is about the entries in lowest terms (`Rat` is normalised), so `Rat.den ≥ 1` gives `M ≥ 1` as
soon as `m ≥ 1`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace RealRAM

/-- The polytope `{x : ∀ i, Σ_j A i j x_j ≤ b i}` of `ℝ^d`. -/
def polytope {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Set (E d) :=
  {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)}

/-- Every entry of `A` and of `b`, in lowest terms, has a numerator and a denominator of absolute value at most `M`. -/
def HeightLE {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (M : ℕ) : Prop :=
  (∀ i j, (A i j).num.natAbs ≤ M ∧ (A i j).den ≤ M) ∧ ∀ i, (b i).num.natAbs ≤ M ∧ (b i).den ≤ M

end RealRAM

end AdversarialBco
