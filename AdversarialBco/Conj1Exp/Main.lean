/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.Main
public import AdversarialBco.StatementConj1Exp
public import AdversarialBco.Conj1Exp.Bound

@[expose] public section

/-!
# The solution module of the Comparator challenge of `TheoremConj1UpperExp`

The two theorems of `AdversarialBco/ChallengeConj1Exp.lean` (config-conj1-exp.json):
`theoremConj1UpperExp_of_conj1 : TheoremConj1Upper → TheoremConj1UpperExp` and `theoremConj1UpperExp :
TheoremConj1UpperExp`, the first applied to `theoremConj1Upper` (AdversarialBco/Conj1/Main.lean).

The deduction, at `δ = 1/(n + 1)`, so that `2 d n / δ = 2 d n (n + 1)`:

* the regret is at most `n` on every run (`regretPts_le_of_mem`): the losses of rounds `t < n` are `AdmLoss K`, the
  points played are in `K` by the in-K clause, and the infimum over `K` of the sum of the losses is at least `0`;
* the bad set `B` of `TheoremConj1Upper` has a measurable superset `M = toMeasurable μ B` with `μ M = μ B ≤ δ`;
* `R = b⁺ + n 1_M`, with `b = max C 0 d^{3/2} n^{1/2} L^5`, is measurable, above the regret on every run (off `M` the
  regret is at most the bound of `TheoremConj1Upper`, on `M` it is at most `n`), and `∫⁻ R = b + n μ M ≤ b + n δ ≤
  b + 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace AdversarialBco

open RealRAM in
/-- `TheoremConj1Upper` at `δ = 1/(n + 1)` gives `TheoremConj1UpperExp`. -/
theorem theoremConj1UpperExp_of_conj1 : TheoremConj1Upper → TheoremConj1UpperExp := by
  rintro ⟨P, C, C', k, hP⟩
  refine ⟨P, max C 0, C', k, ?_⟩
  intro d hd n hn r0 R0 hr0 hrR K hKc hKcv hball hsub σ hσ ν hν
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hL : 2 * (d : ℝ) * n / (1 / ((n : ℝ) + 1)) = 2 * d * n * ((n : ℝ) + 1) := by
    rw [div_div_eq_mul_div, div_one]
  obtain ⟨hcost, hbad⟩ := hP d hd n hn r0 R0 (1 / ((n : ℝ) + 1)) hr0 hrR hδpos hδ1 K hKc hKcv hball hsub σ hσ ν hν
  rw [hL] at hcost hbad
  refine ⟨hcost, ?_⟩
  have : IsProbabilityMeasure ν := hν.1
  have : IsProbabilityMeasure (gaussStream : Measure (ℕ → ℝ)) := by
    unfold gaussStream; infer_instance
  set μ : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := gaussStream.prod ν
  set L : ℝ := Real.log (2 * d * n * ((n : ℝ) + 1))
  set reg : (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun ω =>
    regretPts K (lossAd σ ω.2 (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1)))))
      (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 (1 / ((n : ℝ) + 1)))) n
  set B : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {ω | C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 < reg ω}
  have hbadB : μ B ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := hbad
  set M := toMeasurable μ B
  have hMm : MeasurableSet M := measurableSet_toMeasurable μ B
  set b : ℝ := max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 with hb
  have hdn : (1 : ℝ) ≤ d * n := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) hn'
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hb0 : 0 ≤ b := by positivity
  have hCb : C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 ≤ b := by
    have : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C 0) this
    simpa [hb, mul_assoc] using this
  refine ⟨fun ω => b.toNNReal + M.indicator (fun _ => (n : ℝ≥0)) ω, ?_, ?_, ?_⟩
  · exact measurable_const.add (measurable_const.indicator hMm)
  · intro ω
    show reg ω ≤ _
    by_cases hω : ω ∈ M
    · have hle : reg ω ≤ n :=
        regretPts_le_of_mem (lossAd_adm hσ _ _) (hcost ω.1 ω.2).2
      simp only [Set.indicator_of_mem hω, NNReal.coe_add, NNReal.coe_natCast, Real.coe_toNNReal _ hb0]
      linarith
    · have hnB : ω ∉ B := fun h => hω (subset_toMeasurable μ B h)
      have hle : reg ω ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := not_lt.1 hnB
      simp only [Set.indicator_of_notMem hω, add_zero, Real.coe_toNNReal _ hb0]
      linarith
  · have hsplit : ∀ ω, ((b.toNNReal + M.indicator (fun _ => (n : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) =
        (b.toNNReal : ℝ≥0∞) + M.indicator (fun _ => ((n : ℝ≥0) : ℝ≥0∞)) ω := by
      intro ω
      rw [ENNReal.coe_add]
      by_cases hω : ω ∈ M <;> simp [hω]
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hMm,
      measure_toMeasurable, measure_univ, mul_one]
    have hnδ : ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal 1 := by
      calc ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal n * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
            gcongr
            simp
        _ = ENNReal.ofReal (n * (1 / ((n : ℝ) + 1))) := (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal 1 := by
            apply ENNReal.ofReal_le_ofReal
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    calc (b.toNNReal : ℝ≥0∞) + ((n : ℝ≥0) : ℝ≥0∞) * μ B ≤ ENNReal.ofReal b + ENNReal.ofReal 1 := by
          gcongr
          exact le_of_eq rfl
      _ = ENNReal.ofReal (b + 1) := (ENNReal.ofReal_add hb0 zero_le_one).symm

/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee in expectation, against a strategy, as stated in
StatementConj1Exp.lean. -/
theorem theoremConj1UpperExp : TheoremConj1UpperExp := theoremConj1UpperExp_of_conj1 theoremConj1Upper

end AdversarialBco
