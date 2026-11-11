/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# From a high-probability bound to a measurable majorant

The argument of AdversarialBco/Conj1Exp/Main.lean, stated once for any probability space: if a function `reg` is at
most `n` everywhere and the set where it exceeds `c` has outer measure at most `δ`, with `n δ ≤ 1` and `c ≤ b`,
`0 ≤ b`, then `R = b + n 1_M`, for `M` a measurable superset of that set of the same measure (`toMeasurable`), is a
measurable majorant of `reg` with values in `ℝ≥0` and `∫⁻ R ≤ b + 1`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace AdversarialBco

namespace RealRAM

theorem exists_majorant_of_bad {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (reg : Ω → ℝ) {b c δ : ℝ} {n : ℕ} (hb : 0 ≤ b) (hcb : c ≤ b) (hnδ : (n : ℝ) * δ ≤ 1)
    (hle : ∀ ω, reg ω ≤ n) (hbad : μ {ω | c < reg ω} ≤ ENNReal.ofReal δ) :
    ∃ R : Ω → ℝ≥0, Measurable R ∧ (∀ ω, reg ω ≤ R ω) ∧ ∫⁻ ω, (R ω : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (b + 1) := by
  set B : Set Ω := {ω | c < reg ω}
  set M := toMeasurable μ B
  have hMm : MeasurableSet M := measurableSet_toMeasurable μ B
  refine ⟨fun ω => b.toNNReal + M.indicator (fun _ => (n : ℝ≥0)) ω, ?_, ?_, ?_⟩
  · exact measurable_const.add (measurable_const.indicator hMm)
  · intro ω
    by_cases hω : ω ∈ M
    · simp only [Set.indicator_of_mem hω, NNReal.coe_add, NNReal.coe_natCast, Real.coe_toNNReal _ hb]
      linarith [hle ω]
    · have hnB : ω ∉ B := fun h => hω (subset_toMeasurable μ B h)
      have : reg ω ≤ c := not_lt.1 hnB
      simp only [Set.indicator_of_notMem hω, add_zero, Real.coe_toNNReal _ hb]
      linarith
  · have hsplit : ∀ ω, ((b.toNNReal + M.indicator (fun _ => (n : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) =
        (b.toNNReal : ℝ≥0∞) + M.indicator (fun _ => ((n : ℝ≥0) : ℝ≥0∞)) ω := by
      intro ω
      rw [ENNReal.coe_add]
      by_cases hω : ω ∈ M <;> simp [hω]
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hMm,
      measure_toMeasurable, measure_univ, mul_one]
    have hn : ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal 1 := by
      calc ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal n * ENNReal.ofReal δ := by
            gcongr
            simp
        _ = ENNReal.ofReal (n * δ) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hnδ
    calc (b.toNNReal : ℝ≥0∞) + ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal b + ENNReal.ofReal 1 := by
          gcongr
          exact le_of_eq rfl
      _ = ENNReal.ofReal (b + 1) := (ENNReal.ofReal_add hb zero_le_one).symm

end RealRAM

end AdversarialBco
