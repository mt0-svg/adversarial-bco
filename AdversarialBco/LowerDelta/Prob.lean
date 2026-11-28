/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDelta.Arith
public import AdversarialBco.UnifiedLower.Body

@[expose] public section

/-!
# Theorem LU-D on a body between `B(0, 1/2)` and `B(0, R0)`

The derandomisation with the bounds on every run: `derand_prob_mid_bdd` derandomises a probability bound for `regG` on a
body between `B(0, 1/2)` and `B(0, R0)`, and also exports the bounds `0 ≤ Reg_n ≤ n/2` on every seed
(`regretAd_stratOf`, `regG_nonneg`, `regG_le`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.LowerDelta

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Top AdversarialBco.Lower.Stop
  AdversarialBco.UnifiedLower.Body

/-! ## The parameters -/


variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-! ## The derandomisation with the bounds on every run -/

/-- The derandomisation of the probability bound that also exports, on every seed, `0 ≤ Reg_n ≤ n/2`: the strategy is
that of a tip of `B(0, 1/2) ⊆ K` and a clamped noise sequence, against which the regret is `regG` at every seed. -/
theorem derand_prob_mid_bdd (I : Inputs) {P : SParams} (hP : Good P d R0) {n : ℕ} (hsc : P.sc * ellB n ≤ 1 / 8)
    {K : Set (E d)} (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K)
    (hK2 : K ⊆ Metric.closedBall 0 R0) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) {θ pr : ℝ}
    (hpr : pr ≤ (gameLaw (prior d (1 / 2)) μ).real
      {s | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)}) :
    ∃ σ ∈ StratsMid K n P.L, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n ∧ regretAd K σ (fun t => pol t ω) n ≤ n / 2) ∧
      ENNReal.ofReal pr ≤ μ {ω | θ ≤ regretAd K σ (fun t => pol t ω) n} := by
  have hπ := isProbabilityMeasure_prior d (show (0 : ℝ) < 1 / 2 by norm_num)
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hm := measurable_regG hP hpolB
  have hmc : Measurable fun s : Sample d Ω => (s.1, clampZ (ellB n) s.2.1, s.2.2) :=
    measurable_fst.prodMk (((measurable_clampZ _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  set A := {s : Sample d Ω | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} with hA_def
  have hA : MeasurableSet A := measurableSet_le measurable_const (hm.comp hmc)
  have hassoc : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => ((p.1.1, p.1.2, p.2) : Sample d Ω) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hGm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) :=
    (measurable_const.indicator hA).comp hassoc
  have hGb : ∀ p : (E d × (ℕ → ℝ)) × Ω, |A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2)| ≤ 1 := fun p => by
    by_cases hp : ((p.1.1, p.1.2, p.2) : Sample d Ω) ∈ A
    · rw [Set.indicator_of_mem hp, Pi.one_apply, abs_one]
    · rw [Set.indicator_of_notMem hp, abs_zero]
      norm_num
  have hN : ((prior d (1 / 2)).prod gaussStream)
      {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} = 0 := by
    have h0 := ae_iff.1 (prior_ae_mem d (1 / 2))
    have hs : {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} =
        {θ | θ ∉ Metric.closedBall (0 : E d) (1 / 2)} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, h0, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((prior d (1 / 2)).prod gaussStream) μ hGm hGb hN
  have ha1 : a.1 ∈ Metric.closedBall (0 : E d) (1 / 2) := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ K := hK1 ha1
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hz : ∀ i, |P.sc * clampZ (ellB n) a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hP.sc_pos]
    exact (mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hP.sc_pos.le).trans hsc
  have hσ := stratOf_mid I hP hK hK2 n a.1 (clampZ (ellB n) a.2) hz
  have hmω : Measurable fun ω : Ω => regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) :=
    hm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hω : ∀ ω, regretAd K (stratOf (prior d (1 / 2)) (ruleS d P) P.sc a.1 (clampZ (ellB n) a.2))
      (fun t => pol t ω) n = regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) := fun ω =>
    regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  refine ⟨_, hσ, ?_, fun ω => ?_, ?_⟩
  · simp only [hω]
    exact hmω
  · rw [hω]
    exact ⟨regG_nonneg hP _ pol n _, regG_le I hP hpolB _⟩
  · simp only [hω]
    set B := {ω : Ω | θ ≤ regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω)} with hB_def
    have hB : MeasurableSet B := measurableSet_le measurable_const hmω
    have h1 : ∫ p, A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) ∂((prior d (1 / 2)).prod gaussStream).prod μ =
        (gameLaw (prior d (1 / 2)) μ).real A :=
      (integral_gameLaw_assoc (prior d (1 / 2)) μ (A.indicator 1)).symm.trans (integral_indicator_one hA)
    have h2 : ∫ ω, A.indicator (1 : Sample d Ω → ℝ) (a.1, a.2, ω) ∂μ = μ.real B := by
      rw [← integral_indicator_one hB]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      beta_reduce
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ((a.1, a.2, ω) : Sample d Ω) ∈ A from hω)]
        rfl
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ((a.1, a.2, ω) : Sample d Ω) ∉ A from hω)]
    have ha' : (gameLaw (prior d (1 / 2)) μ).real A ≤ μ.real B := by
      rw [← h1, ← h2]
      exact ha
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ B)]
    exact hpr.trans ha'

end AdversarialBco.LowerDelta
