/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Lemma D.14, the restart wrapper: definitions and interface statement

Interface: Lemma D.14, deterministic and
learner-free. Rounds `1, ..., τ` carry convex functions `s u` on a convex set `Keps` and reals `σ u`;
`S t = ∑_{u ∈ [1, t]} s u`, `sReg t x = ∑_{u ∈ [1, t]} σ u - S t x`, and `xs t` minimises `S t` on `Keps`. With the
regions `Kτ1 ⊆ Kτ ⊆ Keps`, the bonus `β`, the quantity `E`, the test outcome `Fire` and the constants `A₁, A₂, A₅, κs,
κc, b`, hypotheses (W0) to (W5) and `κs ≥ A₁ + A₅`, `b ≥ A₂ + κc` give: (a) `Fire → E ≤ 0`; (b) `xs τ ∉ Kτ → Fire`;
(c) `¬ Fire → xs τ ∈ Kτ1 ∧ E ≤ A₁ + A₂`.

The statement keeps only what the proof reads: `Keps` convex (the compactness in the paper and the continuity of the `s u`
give the existence of minimisers, which is assumed here through `xs`), `Kτ` closed, `S τ` convex on `Keps` (a sum of
convex functions), `xs (τ - 1)` a minimiser of `S (τ - 1)` (for `τ = 1` the sum is empty and any point of `Keps`
minimises it), the suprema of (W4s), (W4c) written pointwise, and "a limit of points of `Keps` outside `Kτ`" as
membership in `closure (Keps \ Kτ)`. It is not the final form of the wrapper in the regret proof.

Every statement is a `Prop`; the theorems that prove them are in `WrapperProof.lean`.
-/

namespace AdversarialBco.Poly

/-- `S t x = ∑_{u ∈ [1, t]} s u x`. -/
def wrapS {E : Type*} (s : ℕ → E → ℝ) (t : ℕ) (x : E) : ℝ :=
  ∑ u ∈ Finset.Icc 1 t, s u x

/-- `sReg t x = ∑_{u ∈ [1, t]} σ u - S t x`. -/
def wrapReg {E : Type*} (s : ℕ → E → ℝ) (σ : ℕ → ℝ) (t : ℕ) (x : E) : ℝ :=
  ∑ u ∈ Finset.Icc 1 t, σ u - wrapS s t x

/-- Lemma D.14. -/
def LemmaW : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Keps Kτ Kτ1 : Set E) (τ : ℕ) (s : ℕ → E → ℝ)
    (σ : ℕ → ℝ) (xs : ℕ → E) (β : E → ℝ) (Ereg A₁ A₂ A₅ κs κc b : ℝ) (Fire : Prop),
    1 ≤ τ → Convex ℝ Keps → IsClosed Kτ → Kτ ⊆ Keps → Kτ1 ⊆ Kτ →
    ConvexOn ℝ Keps (wrapS s τ) →
    xs τ ∈ Keps → (∀ y ∈ Keps, wrapS s τ (xs τ) ≤ wrapS s τ y) →
    (∀ y ∈ Keps, wrapS s (τ - 1) (xs (τ - 1)) ≤ wrapS s (τ - 1) y) →
    (∀ y ∈ Kτ, 0 ≤ β y) →
    -- (W0)
    xs (τ - 1) ∈ Kτ →
    -- (W1)
    Ereg ≤ wrapReg s σ τ (xs τ) + A₁ →
    -- (W2)
    (∀ y ∈ Kτ, wrapReg s σ τ y ≤ A₂ - β y) →
    -- (W3)
    (∀ y ∈ Kτ, y ∈ closure (Keps \ Kτ) → b ≤ β y) → (∀ y ∈ Kτ, β y < b → y ∈ Kτ1) →
    -- (W4s), (W4c)
    (Fire → ∀ y ∈ Kτ, wrapReg s σ τ y ≤ -κs) → ((∀ y ∈ Kτ, wrapReg s σ τ y ≤ -κc) → Fire) →
    -- (W5)
    s τ (xs (τ - 1)) - s τ (xs τ) ≤ A₅ →
    A₁ + A₅ ≤ κs → A₂ + κc ≤ b →
    (Fire → Ereg ≤ 0) ∧ (xs τ ∉ Kτ → Fire) ∧ (¬ Fire → xs τ ∈ Kτ1 ∧ Ereg ≤ A₁ + A₂)

end AdversarialBco.Poly
