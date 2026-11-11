/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Freedman's inequality at a stopping time: definitions and interface statements

Interface: the scalar Freedman inequality that the learner's concentration bounds
use (the source's thm:freedman, arXiv 2402.06535), in its corrected two-sided form, and Lemma FK; the corrected constant is explained. Every statement is a
`Prop`, proved in `AdversarialBco/Poly/FreedmanProof.lean` (theorems named after the `Prop` in lower camel case,
`freedmanStopped : FreedmanStopped`).

Indexing: `X t` is the increment of round `t + 1`, `ℱ (t + 1)`-measurable and conditioned on `ℱ t`; a stopping time
`τ ≤ n` keeps the increments `X t` with `t < τ` (the rounds `1, ..., τ`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

universe u

/-- The predictable variance `Σ_{t < n} E[X_t ^ 2 | ℱ_t]`. -/
noncomputable def predVar {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, (μ[fun ω => X t ω ^ 2 | ℱ t]) ω

/-- The exponential process `exp (α Σ_{t < n} X_t - α ^ 2 Σ_{t < n} E[X_t ^ 2 | ℱ_t])`. -/
noncomputable def expProc {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (α : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (α * ∑ t ∈ Finset.range n, X t ω - α ^ 2 * predVar μ ℱ X n ω)

/-- `max 1 (max_{t < k} X_t)`, the one-sided range. -/
noncomputable def upMax {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (Finset.range k).fold max 1 (fun t => X t ω)

/-- `max 1 (max_{t < k} |X_t|)`, the two-sided range. -/
noncomputable def absMax {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (Finset.range k).fold max 1 (fun t => |X t ω|)

/-- The unnormalised one-sided bound (the source's thm:conc:unnormalised, one-sided form): for supermartingale
differences with `α X_t ≤ 1`, `Σ X_t ≥ α Σ E[X_t ^ 2 | ℱ_t] + log (1/δ)/α` has probability at most `δ`. -/
def FreedmanUnnorm : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (α : ℝ), 0 < α → (∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) → (∀ t, Integrable (X t) μ) →
    (∀ t, Integrable (fun ω => X t ω ^ 2) μ) → (∀ t, ∀ᵐ ω ∂μ, α * X t ω ≤ 1) → (∀ t, μ[X t | ℱ t] ≤ᵐ[μ] 0) →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ →
    μ {ω | α * predVar μ ℱ X n ω + Real.log (1 / δ) / α ≤ ∑ t ∈ Finset.range n, X t ω} ≤ ENNReal.ofReal δ

/-- The one-sided strengthened Freedman inequality at a fixed horizon (Zimmert and Lattimore 2022, Theorem 9):
`Σ_{t < n} X_t ≤ 3 (V l)^{1/2} + 2 U l` with probability at least `1 - δ`, `U = max(1, max_{t < n} X_t)`,
`V` the predictable variance, `l = log (2 max(U, V^{1/2})/δ)`. -/
def FreedmanOneSided : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ), (∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) → (∀ t, Integrable (X t) μ) →
    (∀ t, Integrable (fun ω => X t ω ^ 2) μ) → (∀ t, μ[X t | ℱ t] =ᵐ[μ] 0) →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X n ω *
          Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ))
        + 2 * upMax X n ω * Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ)
        < ∑ t ∈ Finset.range n, X t ω} ≤ ENNReal.ofReal δ

/-- Freedman's inequality at a stopping time, two-sided (the source's thm:freedman with the corrected constant `4`):
for `E[X_t | ℱ_t] = 0` on `{t < τ}`, `τ ≤ n` a stopping time, with probability at least `1 - δ`,
`|Σ_{t < τ} X_t| ≤ 3 (V_τ l)^{1/2} + 2 B l`, `B = max(1, max_{t < τ} |X_t|)`, `V_τ` the predictable variance up to
`τ`, `l = log (4 max(B, V_τ^{1/2})/δ)`. -/
def FreedmanStopped : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ), (∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) → (∀ t, Integrable (X t) μ) →
    (∀ t, Integrable (fun ω => X t ω ^ 2) μ) →
    ∀ (τ : Ω → ℕ), IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)) → ∀ n : ℕ, (∀ ω, τ ω ≤ n) →
    (∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[X t | ℱ t] ω = 0) →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X (τ ω) ω *
          Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ))
        + 2 * absMax X (τ ω) ω * Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ)
        < |∑ t ∈ Finset.range (τ ω), X t ω|} ≤ ENNReal.ofReal δ

/-- Lemma FK, corrected constant: `FreedmanStopped` applied to `κ X_t` and divided
by `κ`. With `B_κ = max(1, κ max_{t < τ} |X_t|)`: `|Σ_{t < τ} X_t| ≤ 3 (V_τ l)^{1/2} + 2 (B_κ/κ) l`, that is
`2 max(1/κ, max |X_t|) l`, with `l = log (4 max(B_κ, κ V_τ^{1/2})/δ)`. -/
def FreedmanFK : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ), (∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) → (∀ t, Integrable (X t) μ) →
    (∀ t, Integrable (fun ω => X t ω ^ 2) μ) →
    ∀ (τ : Ω → ℕ), IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)) → ∀ n : ℕ, (∀ ω, τ ω ≤ n) →
    (∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[X t | ℱ t] ω = 0) →
    ∀ κ δ : ℝ, 0 < κ → 0 < δ → δ ≤ 1 →
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X (τ ω) ω * Real.log (4 * max (absMax (fun t ω => κ * X t ω) (τ ω) ω)
            (κ * Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ))
        + 2 * (absMax (fun t ω => κ * X t ω) (τ ω) ω / κ) * Real.log (4 * max (absMax (fun t ω => κ * X t ω) (τ ω) ω)
            (κ * Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ)
        < |∑ t ∈ Finset.range (τ ω), X t ω|} ≤ ENNReal.ofReal δ

end AdversarialBco.Poly
