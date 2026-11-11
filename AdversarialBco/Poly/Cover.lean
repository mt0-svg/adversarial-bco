/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Covers of a ball, the union bound and the Lipschitz completion: interface statements

Interface of the covers: the deterministic steps 1, 3 (the union) and 4 of the proof of Lemma DQ: a net of a ball and its size, the union bound over a finite family, and the quadratic
difference behind the Lipschitz completion.

* `CardLeOfSeparatedBall`: an `ε`-separated finite subset of the closed ball of radius `R` in `ℝ^d` has at most
  `(1 + 2R/ε)^d` points.
* `ExistsNet`: the closed ball of radius `R` has an `ε`-net of at most `(1 + 2R/ε)^d` points, inside the ball and
  `ε`-separated.
* `LogCardNet`: for the net of radius `2d` at scale `δ³`, `d log (1 + 4d/δ³) ≤ 4.12 d log (1/δ)` when `d ≤ 1/δ` and
  `log (1/δ) ≥ 14`.
* `UnionBoundFinset`: `P (⋃_{i ∈ S} A i) ≤ |S| p` when every `P (A i) ≤ p`.
* `QuadDiff`, `QuadSumDiff`: for self-adjoint `M`, `q(y) - q(y') = ⟪M (y - y'), y + y' - 2μ⟫` with
  `q(y) = ⟪M (y - μ), y - μ⟫`, and the bound `|∑_s q_s(y) - ∑_s q_s(y')| ≤ (∑_s ‖M_s‖) ‖y - y'‖ R` when
  `‖y + y' - 2μ_s‖ ≤ R`.

Junk values: `2 * R / ε` is read for `ε > 0`, `Real.log` at `1/δ > 1` and at `1 + 4d/δ³ > 1`.

Every statement is a `Prop`; the theorems that prove them are in `AdversarialBco/Poly/CoverProof.lean`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly

/-- A separated finite subset of a ball is small. -/
def CardLeOfSeparatedBall : Prop :=
  ∀ (d : ℕ) (R ε : ℝ), 0 ≤ R → 0 < ε → ∀ C : Finset (EuclideanSpace ℝ (Fin d)),
    ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R → (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) →
    (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d

/-- A net of a ball. -/
def ExistsNet : Prop :=
  ∀ (d : ℕ) (R ε : ℝ), 0 ≤ R → 0 < ε →
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)), ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ∃ c ∈ C, dist y c ≤ ε) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d

/-- The logarithm of the size of the net of radius `2d` at scale `δ³`. -/
def LogCardNet : Prop :=
  ∀ (d : ℕ) (δ : ℝ), 1 ≤ d → 0 < δ → δ < 1 → (d : ℝ) ≤ 1 / δ → 14 ≤ Real.log (1 / δ) →
    (d : ℝ) * Real.log (1 + 2 * (2 * d) / δ ^ 3) ≤ 4.12 * d * Real.log (1 / δ)

/-- The union bound over a finite family. -/
def UnionBoundFinset : Prop :=
  ∀ (Ω ι : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι) (A : ι → Set Ω) (p : ENNReal),
    (∀ i ∈ S, P (A i) ≤ p) → P (⋃ i ∈ S, A i) ≤ S.card * p

/-- The quadratic difference of the Lipschitz completion. -/
def QuadDiff : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (M : E →L[ℝ] E),
    IsSelfAdjoint M → ∀ y y' μ : E,
    ⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫ = ⟪M (y - y'), y + y' - 2 • μ⟫ ∧
      |⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫| ≤ ‖M‖ * ‖y - y'‖ * ‖y + y' - 2 • μ‖

/-- The Lipschitz completion for a sum of quadratic forms. -/
def QuadSumDiff : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (S : Finset ι)
    (M : ι → E →L[ℝ] E), (∀ s ∈ S, IsSelfAdjoint (M s)) → ∀ (μ : ι → E) (y y' : E) (R : ℝ),
    (∀ s ∈ S, ‖y + y' - 2 • μ s‖ ≤ R) →
    |∑ s ∈ S, ⟪M s (y - μ s), y - μ s⟫ - ∑ s ∈ S, ⟪M s (y' - μ s), y' - μ s⟫| ≤
      (∑ s ∈ S, ‖M s‖) * ‖y - y'‖ * R

end AdversarialBco.Poly
