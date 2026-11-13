/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Nets of a ball: interface statement

* `ExistsNet`: the closed ball of radius `R` in `ℝ^d` has an `ε`-net of at most `(1 + 2R/ε)^d` points, inside the
  ball and `ε`-separated.

Junk values: `2 * R / ε` is read for `ε > 0`.

The statement is a `Prop`; the theorem that proves it is in `AdversarialBco/Poly/CoverProof.lean`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly

/-- A net of a ball. -/
def ExistsNet : Prop :=
  ∀ (d : ℕ) (R ε : ℝ), 0 ≤ R → 0 < ε →
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)), ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ∃ c ∈ C, dist y c ≤ ε) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d

end AdversarialBco.Poly
