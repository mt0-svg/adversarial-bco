/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Dil
public import AdversarialBco.Body.Inner

@[expose] public section

/-!
# Proposition 2.2

`AdversarialBco.body_H`: hypothesis (H)[1/n, CB d^2 log(n d D) log(2n)] on the inner body of every convex body
containing a unit ball, from its two halves: Theorem 3.1 with (3.2) on `ℝ^d`
(`AdversarialBco.Body.dilReg`, `AdversarialBco.Body.Dil`) and the transfer to the inner body
(`AdversarialBco.Body.body_H_of_dilReg`, `AdversarialBco.Body.Inner`).
-/

/-- Proposition 2.2, assembled from its two halves. -/
theorem AdversarialBco.body_H :
    ∃ CB : ℝ, 1 ≤ CB ∧ ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (AdversarialBco.E d),
    IsCompact K → Convex ℝ K → ∀ c : AdversarialBco.E d, Metric.closedBall c 1 ⊆ K → ∀ D : ℝ, Metric.diam K ≤ D →
      AdversarialBco.HypH {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} n 0 1 (1 / n)
        (CB * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n)) :=
  AdversarialBco.Body.body_H_of_dilReg AdversarialBco.Body.dilReg
