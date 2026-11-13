/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# DF2: the event Azuma

Azuma's inequality (the paper's Azuma lemma; the source's thm:azuma, arXiv 2402.06535), in the form the proof of
DF2 reads it. The event Azuma of the source (repeated at the level `δ/7` for the adversarial chapter) is, with `Z_t = f_t(X_t/π⁺(X_t))`,
`Σ_{t ≤ n} Z_t ≤ Σ_{t ≤ n} E_{t-1}[Z_t] + (2 n log(7/δ))^{1/2}`; it holds with probability at least `1 - δ/7` because
`X_t/π⁺(X_t) ∈ K_ε ⊆ K` and the losses take values in `[0, 1]`. The appendix on one epoch of the online Newton method
rereads it under the
play `p'`: the differences `Z_t - E_{t-1}[Z_t]` are martingale differences for the filtration of the run whatever the
conditional law of `X_t` is, and nothing reads the covariance. The bound is taken once over the `n` rounds of the run
at the level `δ_e/7`: a fixed
horizon, no stopping time.

Indexing as in `Freedman.lean`: `Z t` is the variable of round `t + 1`, `ℱ (t + 1)`-measurable and conditioned on
`ℱ t`, so `μ[Z t | ℱ t]` is `E_{t-1}[Z_t]` of the source. The space `Ω` is any measurable space: no standard Borel
hypothesis (Mathlib's `measure_sum_ge_le_of_hasCondSubgaussianMGF` asks one, through the conditional expectation
kernel), so the space of the run is not constrained.

* `AzumaHoeffding`: Azuma-Hoeffding for variables with values in `[a_t, b_t]` almost surely, the upper tail:
  `P(Σ_{t<n} (Z_t - E[Z_t | ℱ_t]) ≥ ε) ≤ exp(-2 ε² / Σ_{t<n} (b_t - a_t)²)` for `ε ≥ 0`.
* `Df2AzumaEvent`: the event Azuma of DF2 at the level `δ/7`, for `Z_t ∈ [0, 1]` almost surely; the bad set is written.

Junk values. In `AzumaHoeffding`, `Σ (b_t - a_t)² = 0` makes the exponent `-2 ε²/0 = 0`, so the bound reads
`≤ 1`: true, weaker than the truth. `μ[Z t | ℱ t]` is not junk: `Z t` is bounded and measurable, hence integrable.
`Df2AzumaEvent` assumes `δ > 0`, so `7/δ` is a true quotient; for `δ ≥ 7` the logarithm is at most `0`, `Real.sqrt`
of a nonpositive number is `0`, and the bound `ofReal (δ/7) ≥ 1` holds trivially. The bad set uses the strict `<`
of the complement of the source's event (with `≤` the bad set is everything at `n = 0` and the statement fails).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

universe u

/-- Azuma-Hoeffding, upper tail. `Z t` is `ℱ (t + 1)`-measurable with values in `[a t, b t]` almost surely; then for
`ε ≥ 0`, `P(Σ_{t<n} (Z_t - E[Z_t | ℱ_t]) ≥ ε) ≤ exp(-2 ε² / Σ_{t<n} (b_t - a_t)²)`. -/
def AzumaHoeffding : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ), (∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) →
    (∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) →
    ∀ (n : ℕ) (ε : ℝ), 0 ≤ ε →
    μ {ω | ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)} ≤
      ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / ∑ t ∈ Finset.range n, (b t - a t) ^ 2))

/-- The event Azuma of DF2: for `Z t`
`ℱ (t + 1)`-measurable with values in `[0, 1]` almost surely and `δ > 0`,
`Σ_{t<n} Z_t ≤ Σ_{t<n} E[Z_t | ℱ_t] + (2 n log(7/δ))^{1/2}` fails with probability at most `δ/7`. -/
def Df2AzumaEvent : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ), (∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) →
    (∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc 0 1) →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ →
    μ {ω | ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * n * Real.log (7 / δ)) <
        ∑ t ∈ Finset.range n, Z t ω} ≤ ENNReal.ofReal (δ / 7)

end AdversarialBco.Poly
