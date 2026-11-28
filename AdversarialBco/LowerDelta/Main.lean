/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDelta.Prob

@[expose] public section

/-!
# Theorem LU-D on every body of the class: the mean from the probability

`mean_of_prob`: a measurable function with values in `[0, B]` and `P(f ≥ θ) ≥ p`, `θ ≥ 0`, is integrable with
`E f ≥ θ p` (`E Reg ≥ θ P(Reg ≥ θ)` for the regret).
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

namespace AdversarialBco.LowerDelta

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Top AdversarialBco.UnifiedLower
  AdversarialBco.UnifiedLower.Body

/-- The mean from the probability: a measurable function with values in `[0, B]` and `P(f ≥ θ) ≥ p`, `θ ≥ 0`, is
integrable with `E f ≥ θ p`. -/
theorem mean_of_prob {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {B θ p : ℝ}
    (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) (hB : ∀ ω, f ω ≤ B) (hθ : 0 ≤ θ)
    (hprob : ENNReal.ofReal p ≤ μ {ω | θ ≤ f ω}) : Integrable f μ ∧ θ * p ≤ ∫ ω, f ω ∂μ := by
  have hint : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]; exact hB ω)
  refine ⟨hint, ?_⟩
  have h1 := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ h0) hint θ
  have h2 : p ≤ μ.real {ω | θ ≤ f ω} := by
    by_cases hp : p ≤ 0
    · exact hp.trans measureReal_nonneg
    · rw [Measure.real, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)]
      exact hprob
  exact (mul_le_mul_of_nonneg_left h2 hθ).trans h1

end AdversarialBco.LowerDelta
