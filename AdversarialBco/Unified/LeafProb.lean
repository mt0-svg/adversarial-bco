/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Leaves of the unified route: the noise facts

The leaves of the unified route on the noise:

* `uni_subg_tail`: the tail of a subgaussian variable, `P(|X| ≥ u) ≤ 2 e^{-u²}` from `E exp(X²) ≤ 2` (UNI-OBS).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Uni

/-- On `{u ≤ |x|}`, `exp(u²) ≤ exp(x²)`. -/
theorem uni_exp_sq_le_of_le_abs {u x : ℝ} (hu : 0 ≤ u) (h : u ≤ |x|) : Real.exp (u ^ 2) ≤ Real.exp (x ^ 2) := by
  rw [Real.exp_le_exp, ← sq_abs x]
  exact pow_le_pow_left₀ hu h 2

/-- The tail of a subgaussian variable: Markov's inequality on `exp(X²)`. -/
theorem uni_subg_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hint : Integrable (fun ω => Real.exp (X ω ^ 2)) μ)
    (h2 : ∫ ω, Real.exp (X ω ^ 2) ∂μ ≤ 2) (u : ℝ) (hu : 0 ≤ u) :
    μ {ω | u ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  have hsub : {ω | u ≤ |X ω|} ⊆ {ω | Real.exp (u ^ 2) ≤ Real.exp (X ω ^ 2)} := fun ω hω =>
    uni_exp_sq_le_of_le_abs hu hω
  have hmk : Real.exp (u ^ 2) * μ.real {ω | Real.exp (u ^ 2) ≤ Real.exp (X ω ^ 2)} ≤
      ∫ ω, Real.exp (X ω ^ 2) ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le) hint _
  have he := Real.exp_pos (u ^ 2)
  have hT : μ.real {ω | Real.exp (u ^ 2) ≤ Real.exp (X ω ^ 2)} ≤ 2 * Real.exp (-u ^ 2) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ he]
    linarith
  calc μ {ω | u ≤ |X ω|} ≤ μ {ω | Real.exp (u ^ 2) ≤ Real.exp (X ω ^ 2)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | Real.exp (u ^ 2) ≤ Real.exp (X ω ^ 2)}) :=
      (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := ENNReal.ofReal_le_ofReal hT

end AdversarialBco.Uni
