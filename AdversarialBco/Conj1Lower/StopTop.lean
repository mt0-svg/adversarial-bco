/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.StopGame
public import AdversarialBco.Lower.R0Ext
public import AdversarialBco.Lower.Aff

@[expose] public section

/-!
# Corollary LU-P: the rate with probability

Corollary LU-P (the paper's bound with probability), on the chain of Corollary RIPE-K-B (Top.lean) with Proposition STOP
(StopGame.lean): on a convex `K` with `B(0, 1/2) ⊆ K ⊆ B(0, R0)`, `1 ≤ R0 ≤ d kRipe d`, for `d ≥ 4·10^6` and
`n ≥ d^10`, every learner of `IsLearnerAd K n` meets a strategy of `StratsLip K n` against which its regret is
measurable in the seed and at least `2.8·10^-9 d^{3/2} n^{1/2} / ln d` with probability at least `1/2`.

This file holds one step, the coupling with the clamped noise: the clamped noise changes the regret on an event of
probability at most `2/n²` (`prob_regG_clamped`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Stop

open RealRAM Bayes _root_.AdversarialBco.Lower.Top

/-! ## The regret on the crossing event, on the reals -/

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-! ## The probabilities -/

section Prob

/-- (LU-P), the coupling with the clamped noise: the regret changes on an event of probability at most `2/n²`. -/
theorem prob_regG_clamped {P : SParams} (μ : Measure Ω) [IsProbabilityMeasure μ] (pol : Learner Ω d) {n : ℕ}
    (hn : 1 < n) (θ : ℝ) :
    (gameLaw (prior d (1 / 2)) μ).real {s | θ ≤ regG (prior d (1 / 2)) P pol n s} - 2 / (n : ℝ) ^ 2 ≤
      (gameLaw (prior d (1 / 2)) μ).real
        {s | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} := by
  have hπ := isProbabilityMeasure_prior d (show (0 : ℝ) < 1 / 2 by norm_num)
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsub : {s : Sample d Ω | θ ≤ regG (prior d (1 / 2)) P pol n s} ⊆
      {s | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} ∪
        {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|} := by
    intro s hs
    by_cases hb : s ∈ {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|}
    · exact Or.inr hb
    · left
      have hc : ∀ i < n, s.2.1 i = clampZ (ellB n) s.2.1 i := fun i hi => by
        refine (clampZ_of_abs_le ?_).symm
        by_contra h
        exact hb ⟨i, hi, lt_of_not_ge h⟩
      have := regG_congr (prior d (1 / 2)) P pol n s.1 hc s.2.2
      show θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)
      have hs' : θ ≤ regG (prior d (1 / 2)) P pol n s := hs
      linarith
  have hbad := gameLaw_bad_le (prior d (1 / 2)) μ n hℓ
  have h3 : Real.exp (3 * Real.log n) = (n : ℝ) ^ 3 := by
    rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
    norm_num
  have hexp : (n : ℝ) * (2 * Real.exp (-ellB n ^ 2 / 2)) = 2 / (n : ℝ) ^ 2 := by
    have hsq : ellB n ^ 2 = 6 * Real.log n :=
      Real.sq_sqrt (by have := Real.log_nonneg hnR.le; linarith)
    rw [hsq, show -(6 * Real.log n) / 2 = -(3 * Real.log n) by ring, Real.exp_neg, h3]
    field_simp
  have h := (measureReal_mono (μ := gameLaw (prior d (1 / 2)) μ) hsub).trans (measureReal_union_le _ _)
  rw [hexp] at hbad
  linarith

end Prob

end AdversarialBco.Lower.Stop
