/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Main
public import AdversarialBco.StatementConj1PolyExp
public import AdversarialBco.Conj1Exp.Bound
public import AdversarialBco.Conj1PolyExp.Majorant

@[expose] public section

/-!
# The solution module of the Comparator challenge of `TheoremConj1UpperPolyExp`

The two theorems of `AdversarialBco/ChallengeConj1PolyExp.lean` (config-conj1-poly-exp.json):
`theoremConj1UpperPolyExp_of_poly : TheoremConj1UpperPoly → TheoremConj1UpperPolyExp` and
`theoremConj1UpperPolyExp : TheoremConj1UpperPolyExp`, the first applied to `theoremConj1UpperPoly`
(AdversarialBco/Conj1Poly/Main.lean).

The deduction is that of AdversarialBco/Conj1Exp/Main.lean, at `δ = 1/(n + 1)`, so that `2 d n / δ = 2 d n (n + 1)`:
the regret is at most `n` on every run (`regretPts_le_of_mem`, Conj1Exp/Bound.lean, with the in-`K` clause), and
`exists_majorant_of_bad` (Conj1PolyExp/Majorant.lean) turns the outer-measure bound of `TheoremConj1UpperPoly` into a
measurable majorant `b⁺ + n 1_M` with `∫⁻ ≤ b⁺ + n δ ≤ b⁺ + 1`, `b = max C 0 d^{3/2} n^{1/2} L^5`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace AdversarialBco

open RealRAM in
/-- `TheoremConj1UpperPoly` at `δ = 1/(n + 1)` gives `TheoremConj1UpperPolyExp`. -/
theorem theoremConj1UpperPolyExp_of_poly : TheoremConj1UpperPoly → TheoremConj1UpperPolyExp := by
  rintro ⟨P, C, C', k, hQ, hP⟩
  refine ⟨P, max C 0, C', k, hQ, ?_⟩
  intro d hd n hn m M A b hH hball hdiam σ hσ ν hν
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hL : 2 * (d : ℝ) * n / (1 / ((n : ℝ) + 1)) = 2 * d * n * ((n : ℝ) + 1) := by
    rw [div_div_eq_mul_div, div_one]
  obtain ⟨hcost, hbad⟩ := hP d hd n hn m M (1 / ((n : ℝ) + 1)) hδpos hδ1 A b hH hball hdiam σ hσ ν hν
  rw [hL] at hcost hbad
  refine ⟨hcost, ?_⟩
  have : IsProbabilityMeasure ν := hν.1
  have : IsProbabilityMeasure (gaussStream : Measure (ℕ → ℝ)) := by
    unfold gaussStream; infer_instance
  set L : ℝ := Real.log (2 * d * n * ((n : ℝ) + 1))
  have hdn : (1 : ℝ) ≤ d * n := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) hn'
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hb0 : 0 ≤ max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := by positivity
  have hCb : C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 ≤
      max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := by
    have : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C 0) this
    simpa [mul_assoc] using this
  have hnδ : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  exact exists_majorant_of_bad (gaussStream.prod ν) _ hb0 hCb hnδ
    (fun ω => regretPts_le_of_mem (lossAd_adm hσ _ _) (hcost ω.1 ω.2).2) hbad

/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee on their polytopes, in expectation, against a strategy, as
stated in StatementConj1PolyExp.lean. -/
theorem theoremConj1UpperPolyExp : TheoremConj1UpperPolyExp :=
  theoremConj1UpperPolyExp_of_poly theoremConj1UpperPoly

end AdversarialBco
