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

The steps:

- at the level `x = Y - 1/2 - σ √n`, `Y = 10^-5 σ d^{3/2} (n Γ)^{1/2}/k`, Proposition STOP gives
  `q = P(C_u > x for some u ≤ n) ≥ 0.53` (`stop_rate_K`);
- on the crossing event the regret exceeds `x - σ W` with `W = Σ_{t < n} 1{C_u ≤ x for u ≤ t} Z_t`, a noise sum with
  predictable weights, so `E W² ≤ n` and Chebyshev gives `P(|W| ≥ 7 √n) ≤ 1/49` (`prob_regG_ge`);
- the clamped noise changes the regret on an event of probability at most `2/n²` (`prob_regG_clamped`);
- some tip and clamped noise sequence keep the probability over the seed (`derand_prob`, by `exists_good_point` on the
  indicator);
- `x - 7σ √n ≥ 2.8·10^-9 d^{3/2} n^{1/2}/ln d` and `0.53 - 1/49 - 2/n² ≥ 1/2` (`ripe_prob_threshold`).

The note uses the constant 10 in Chebyshev and the threshold `x - 10 σ √n` with `x = Y - 2σ - 1/8 - 1/n`; here the
constant is 7 and the threshold `Y - 1/2 - 8 σ √n` (see StopGame.lean, (F5)).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Stop

open RealRAM Bayes _root_.AdversarialBco.Lower.Top

/-! ## The regret on the crossing event, on the reals -/

section Pure

/-- At the first `u ≤ n` with `C_u > x`, the dents so far exceed `x - σ Σ_{t < n} w_t Z_t`, where `w_t = 1` when
`C_u ≤ x` for all `u ≤ t` and `0` otherwise; the dents are nonnegative, so their sum over `t < n` does too. -/
theorem crossing_lower {C D Z w : ℕ → ℝ} {x σ : ℝ} (hC : ∀ t, C (t + 1) = C t + D t + σ * Z t) (hC0 : C 0 = 0)
    {n : ℕ} (hD : ∀ t < n, 0 ≤ D t) (hw1 : ∀ t, (∀ u ≤ t, C u ≤ x) → w t = 1)
    (hw0 : ∀ t, ¬ (∀ u ≤ t, C u ≤ x) → w t = 0) (hcross : ∃ u ≤ n, x < C u) :
    x - σ * ∑ t ∈ range n, w t * Z t < ∑ t ∈ range n, D t := by
  classical
  have hex : ∃ u, u ≤ n ∧ x < C u := by
    obtain ⟨u, hu, h⟩ := hcross
    exact ⟨u, hu, h⟩
  set τ := Nat.find hex with hτ_def
  obtain ⟨hτn, hτx⟩ := Nat.find_spec hex
  have hmin : ∀ u < τ, C u ≤ x := fun u hu => by
    have := Nat.find_min hex hu
    push Not at this
    exact this (by omega)
  have hsumC : ∀ m, ∑ t ∈ range m, (D t + σ * Z t) = C m := by
    intro m
    induction m with
    | zero => simp [hC0]
    | succ m ih => rw [sum_range_succ, ih, hC m]; ring
  have hwZ : ∑ t ∈ range n, w t * Z t = ∑ t ∈ range τ, Z t := by
    rw [← sum_range_add_sum_Ico _ hτn]
    have h1 : ∀ t ∈ range τ, w t * Z t = Z t := fun t ht => by
      rw [hw1 t fun u hu => hmin u (lt_of_le_of_lt hu (mem_range.1 ht)), one_mul]
    have h2 : ∀ t ∈ Ico τ n, w t * Z t = 0 := fun t ht => by
      rw [hw0 t fun h => absurd (h τ (mem_Ico.1 ht).1) (not_le.2 hτx), zero_mul]
    rw [sum_congr rfl h1, sum_congr rfl h2, sum_const_zero, add_zero]
  have hD' : ∑ t ∈ range τ, D t ≤ ∑ t ∈ range n, D t := by
    rw [← sum_range_add_sum_Ico _ hτn]
    have : 0 ≤ ∑ t ∈ Ico τ n, D t := sum_nonneg fun t ht => hD t (mem_Ico.1 ht).2
    linarith
  have hτ : ∑ t ∈ range τ, D t = C τ - σ * ∑ t ∈ range τ, Z t := by
    rw [← hsumC τ, sum_add_distrib, mul_sum]
    ring
  rw [hwZ]
  linarith

end Pure

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-! ## The noise sum up to the first crossing -/

section Cross

/-- The rounds before the first crossing: `C_u ≤ x` for all `u ≤ t`. -/
def noCrossSet (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) : Set (Sample d Ω) :=
  {s | ∀ u ≤ t, cumO P pol u s ≤ x}

/-- The weights of the noise sum up to the first crossing. -/
noncomputable def noCrossW (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) : ℝ :=
  (noCrossSet P pol x t).indicator (fun _ => 1) s

/-- The observed cumulative before round `u ≤ t` reads the noise before round `t` only. -/
theorem cumO_congr (P : SParams) (pol : Learner Ω d) {u t : ℕ} (hu : u ≤ t) {s s' : Sample d Ω} (h1 : s.1 = s'.1)
    (h2 : ∀ i < t, s.2.1 i = s'.2.1 i) (h3 : s.2.2 = s'.2.2) : cumO P pol u s = cumO P pol u s' := by
  rw [← cumH_hist P pol hu s, ← cumH_hist P pol hu s',
    hist_congr (prior d (1 / 2)) (ruleS d P) P.sc pol t s s' h1 h2 h3]

theorem noCrossW_props {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) :
    (∀ t < n, Measurable (noCrossW P pol x t)) ∧ (∀ t < n, ∀ s, |noCrossW P pol x t s| ≤ 1) ∧
      ∀ t < n, ReadsBefore t (noCrossW P pol x t) := by
  refine ⟨fun t ht => measurable_const.indicator ?_, fun t _ s => ?_, fun t _ s s' h1 h3 h2 => ?_⟩
  · have : noCrossSet P pol x t = ⋂ u ∈ range (t + 1), {s | cumO P pol u s ≤ x} := by
      ext s
      simp only [noCrossSet, Set.mem_ofPred_eq, Set.mem_iInter, mem_range]
      exact ⟨fun h u hu => h u (by omega), fun h u hu => h u (by omega)⟩
    rw [this]
    exact Finset.measurableSet_biInter _ fun u hu =>
      measurableSet_le (measurable_cumO hP hpol (by have := mem_range.1 hu; omega)) measurable_const
  · unfold noCrossW
    by_cases hs : s ∈ noCrossSet P pol x t
    · rw [Set.indicator_of_mem hs, abs_one]
    · rw [Set.indicator_of_notMem hs, abs_zero]
      norm_num
  · have hc : s ∈ noCrossSet P pol x t ↔ s' ∈ noCrossSet P pol x t := by
      simp only [noCrossSet, Set.mem_ofPred_eq]
      exact forall₂_congr fun u hu => by rw [cumO_congr P pol hu h1 h2 h3]
    unfold noCrossW
    by_cases hs : s ∈ noCrossSet P pol x t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hc.1 hs)]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (mt hc.2 hs)]

omit [MeasurableSpace Ω] in
/-- On the crossing event, `Reg^G_n > x - σ W`. -/
theorem regG_gt_of_cross {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (x : ℝ) {n : ℕ} {s : Sample d Ω}
    (hs : s ∈ crossSet P pol x n) :
    x - P.sc * noiseSum (noCrossW P pol x) n s < regG (prior d (1 / 2)) P pol n s := by
  rw [regG_eq]
  refine crossing_lower (C := fun u => cumO P pol u s) (D := fun t => dentT P pol t s) (Z := fun t => s.2.1 t)
    (w := fun t => noCrossW P pol x t s) (fun t => by simp only [cumO, sum_range_succ, obsB_eq]; ring)
    (by simp [cumO]) (fun t _ => sig_sub_b_nonneg hP _ _ _) (fun t h => ?_) (fun t h => ?_) hs
  · exact Set.indicator_of_mem (show s ∈ noCrossSet P pol x t from h) _
  · exact Set.indicator_of_notMem (show s ∉ noCrossSet P pol x t from h) _

end Cross

/-! ## The probabilities -/

section Prob

/-- Chebyshev for a noise sum with predictable weights in `[-1, 1]`: `P(|M_n| ≥ 7 √n) ≤ 1/49`. -/
theorem cheb_noiseSum (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hn : 0 < n) (hVm : ∀ t < n, Measurable (V t))
    (hV : ∀ t < n, ∀ s, |V t s| ≤ 1) (hVr : ∀ t < n, ReadsBefore t (V t)) :
    (gameLaw π0 μ).real {s | 7 * Real.sqrt n ≤ |noiseSum V n s|} ≤ 1 / 49 := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_meas_ge_le_integral_of_nonneg (μ := gameLaw π0 μ) (f := fun s => noiseSum V n s ^ 2)
    (ae_of_all _ fun s => sq_nonneg _) (memLp_noiseSum π0 μ hVm hV).integrable_sq (49 * n)
  have h2 := noiseSum_sq_le π0 μ hVm hV hVr
  have hsub : {s | 7 * Real.sqrt n ≤ |noiseSum V n s|} ⊆ {s | 49 * (n : ℝ) ≤ noiseSum V n s ^ 2} := by
    intro s hs
    have hs' : 7 * Real.sqrt n ≤ |noiseSum V n s| := hs
    have h7 : 0 ≤ 7 * Real.sqrt n := by positivity
    have := mul_self_le_mul_self h7 hs'
    have hs7 : 7 * Real.sqrt n * (7 * Real.sqrt n) = 49 * n := by
      rw [show 7 * Real.sqrt n * (7 * Real.sqrt n) = 49 * (Real.sqrt n * Real.sqrt n) by ring,
        Real.mul_self_sqrt hnR.le]
    show 49 * (n : ℝ) ≤ noiseSum V n s ^ 2
    rw [← sq_abs, sq]
    linarith
  have h3 := measureReal_mono (μ := gameLaw π0 μ) hsub
  have h4 : 49 * (n : ℝ) * (gameLaw π0 μ).real {s | 49 * (n : ℝ) ≤ noiseSum V n s ^ 2} ≤ 49 * n * (1 / 49) := by
    linarith
  have h5 := le_of_mul_le_mul_left h4 (by positivity)
  linarith

/-- (LU-P), the crossing step: `P(Reg^G_n ≥ x - 7σ √n) ≥ q - 1/49`. -/
theorem prob_regG_ge {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    {n : ℕ} (hn : 0 < n) (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) :
    (gameLaw (prior d (1 / 2)) μ).real (crossSet P pol x n) - 1 / 49 ≤
      (gameLaw (prior d (1 / 2)) μ).real {s | x - 7 * P.sc * Real.sqrt n ≤ regG (prior d (1 / 2)) P pol n s} := by
  have hπ := isProbabilityMeasure_prior d (show (0 : ℝ) < 1 / 2 by norm_num)
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  obtain ⟨hVm, hVb, hVr⟩ := noCrossW_props hP hpol x
  have hcheb := cheb_noiseSum (prior d (1 / 2)) μ hn hVm hVb hVr
  have hsub : crossSet P pol x n ⊆ {s | x - 7 * P.sc * Real.sqrt n ≤ regG (prior d (1 / 2)) P pol n s} ∪
      {s | 7 * Real.sqrt n ≤ |noiseSum (noCrossW P pol x) n s|} := by
    intro s hs
    by_cases hM : 7 * Real.sqrt n ≤ |noiseSum (noCrossW P pol x) n s|
    · exact Or.inr hM
    · left
      have hlt := regG_gt_of_cross hP pol x hs
      have h1 : P.sc * noiseSum (noCrossW P pol x) n s ≤ P.sc * (7 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (not_le.1 hM).le) hP.sc_pos.le
      show x - 7 * P.sc * Real.sqrt n ≤ regG (prior d (1 / 2)) P pol n s
      linarith
  have h := (measureReal_mono (μ := gameLaw (prior d (1 / 2)) μ) hsub).trans (measureReal_union_le _ _)
  linarith

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

/-- (LU-P), the derandomisation: a probability over the game of the clamped regret above `θ` is kept, over the seed,
by the strategy of some tip in `B(0, 1/2)` and some clamped noise sequence. -/
theorem derand_prob (I : Inputs) {P : SParams} (hP : Good P d R0) {n : ℕ} (hsc : P.sc * ellB n ≤ 1 / 8)
    {K : Set (E d)} (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K)
    (hK2 : K ⊆ Metric.closedBall 0 R0) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) {θ pr : ℝ}
    (hpr : pr ≤ (gameLaw (prior d (1 / 2)) μ).real
      {s | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)}) :
    ∃ σ ∈ StratsLip K n, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
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
  have hσ := stratOf_mem I hP hK hK2 n a.1 (clampZ (ellB n) a.2) hz
  have he : (fun ω => regretAd K
      (stratOf (prior d (1 / 2)) (ruleS d P) P.sc a.1 (clampZ (ellB n) a.2)) (fun t => pol t ω) n) =
      fun ω => regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) :=
    funext fun ω => regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  have hmω : Measurable fun ω : Ω => regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) :=
    hm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  refine ⟨_, hσ, ?_, ?_⟩
  · rw [he]
    exact hmω
  · have hω : ∀ ω, regretAd K (stratOf (prior d (1 / 2)) (ruleS d P) P.sc a.1 (clampZ (ellB n) a.2))
        (fun t => pol t ω) n = regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) := fun ω =>
      regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
    simp only [hω]
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

end Prob

/-! ## The arithmetic of the threshold -/

section Arith

theorem log_le_ripe (dd : ℝ) (hd : 4000000 ≤ dd) : Real.log dd ≤ 143 / 10 + dd / 4000000 := by
  have hd0 : 0 < dd := by linarith
  have h1 : Real.log dd = Real.log 4000000 + Real.log (dd / 4000000) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h2 := Real.log_le_sub_one_of_pos (show 0 < dd / 4000000 by positivity)
  have h3 : Real.log 4000000 ≤ 153 / 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : Real.exp (153 / 10) = Real.exp 1 ^ 15 * Real.exp (3 / 10) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    have h4 : (2.7182818283 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 15
    have h5 : 3 / 10 + 1 ≤ Real.exp (3 / 10) := Real.add_one_le_exp _
    rw [he]
    have h6 : (0 : ℝ) ≤ Real.exp 1 ^ 15 := by positivity
    nlinarith
  linarith

/-- The threshold of Corollary LU-P: `2.8·10^-9 d^{3/2} n^{1/2} / ln d ≤ Y - 1/2 - 8σ √n` with
`Y = 10^-5 σ d^{3/2} (n Γ)^{1/2} / k` at `σ = sigB n`, `Γ = ln(n/d^5)`, `k = 120 ln d + 68`. -/
theorem ripe_prob_threshold (dd nn : ℝ) (hd : 4000000 ≤ dd) (hn : dd ^ 10 ≤ nn) :
    28 / 10 ^ 10 * (dd * Real.sqrt dd) * Real.sqrt nn / Real.log dd ≤
      1 / 10 ^ 5 * sigB nn * (dd * Real.sqrt dd) * Real.sqrt (nn * gamR dd nn) / kRipe dd - 1 / 2 -
        8 * sigB nn * Real.sqrt nn := by
  have hL := ripeB_log dd hd
  have hLu := log_le_ripe dd hd
  have hd0 : 0 < dd := by linarith
  have hd10 : (4000000 : ℝ) ^ 10 ≤ dd ^ 10 := pow_le_pow_left₀ (by norm_num) hd 10
  have hnbig : (4000000 : ℝ) ^ 10 ≤ nn := hd10.trans hn
  have hn1 : 1 < nn := lt_of_lt_of_le (by norm_num) hnbig
  have hn0 : 0 < nn := by linarith
  have hcoef := ripeB_coef nn (gamR dd nn) hn1 (ripeB_gam dd nn (by linarith) hn)
  set L := Real.log dd with hL_def
  set A := dd * Real.sqrt dd with hA_def
  set r := Real.sqrt nn with hr_def
  set σ := sigB nn with hσ_def
  have hk : kRipe dd = 120 * L + 68 := rfl
  have hk0 : 0 < kRipe dd := by rw [hk]; linarith
  have hL0 : 0 < L := by linarith
  have hsd : 2000 ≤ Real.sqrt dd := Real.le_sqrt_of_sq_le (by nlinarith)
  have hA : 2000 * dd ≤ A := by rw [hA_def]; nlinarith
  have hA0 : 0 ≤ A := by linarith
  have hr : 500 ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hr0 : 0 ≤ r := by linarith
  -- σ ≤ 1/240
  have hσ0 : 0 < σ := (ripeB_sig dd nn hd hn).1
  have hσle : σ ≤ 1 / 240 := by
    have hlogn : 10 * L ≤ Real.log nn := by
      have := Real.log_le_log (by positivity) hn
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have h30 : 30 ≤ Real.sqrt (6 * Real.log nn) := Real.le_sqrt_of_sq_le (by nlinarith)
    rw [hσ_def]
    unfold sigB
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- Y ≥ 3.608·10^-7 A r / k
  have hY : 3608 / 10 ^ 10 * A * r / kRipe dd ≤
      1 / 10 ^ 5 * σ * A * Real.sqrt (nn * gamR dd nn) / kRipe dd := by
    rw [div_le_div_iff_of_pos_right hk0]
    have := mul_le_mul_of_nonneg_left hcoef hA0
    nlinarith
  -- 2.88·10^-9 A r / L ≤ 3.608·10^-7 A r / k
  have h1 : 288 / 10 ^ 11 * A * r / L ≤ 3608 / 10 ^ 10 * A * r / kRipe dd := by
    rw [div_le_div_iff₀ hL0 hk0]
    have hc : 288 / 10 ^ 11 * kRipe dd ≤ 3608 / 10 ^ 10 * L := by rw [hk]; linarith
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hA0 hr0)
    nlinarith
  have h2 : 8 * σ * r ≤ r / 30 := by nlinarith
  have h3 : (1 : ℝ) / 2 ≤ r / 1000 := by linarith
  have h4 : 28 / 10 ^ 10 * A * r / L + (r / 30 + r / 1000) ≤ 288 / 10 ^ 11 * A * r / L := by
    have hc : L * (1 / 30 + 1 / 1000) ≤ 8 / 10 ^ 11 * A := by nlinarith
    have h5 : r * (L * (1 / 30 + 1 / 1000)) ≤ r * (8 / 10 ^ 11 * A) := mul_le_mul_of_nonneg_left hc hr0
    have e : 288 / 10 ^ 11 * A * r / L - 28 / 10 ^ 10 * A * r / L = 8 / 10 ^ 11 * A * r / L := by ring
    have h6 : r / 30 + r / 1000 ≤ 8 / 10 ^ 11 * A * r / L := by
      rw [le_div_iff₀ hL0]
      nlinarith
    linarith
  linarith

end Arith

/-! ## Corollary LU-P -/

section Top

/-- **Corollary LU-P** (the paper's bound with probability), for `1 ≤ R0 ≤ d kRipe d` (Lemma R0-EXT): on a convex `K`
with `B(0, 1/2) ⊆ K ⊆ B(0, R0)`, for `d ≥ 4·10^6` and `n ≥ d^10`, every learner of `IsLearnerAd K n` meets a strategy
of `StratsLip K n` against which its regret is measurable in the seed and at least
`2.8·10^-9 d^{3/2} n^{1/2}/log d` with probability at least `1/2`; from the statements `Inputs`. -/
theorem lowerBodyProb_of_inputs_ext (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0)
    (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsLip K n, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (1 / 2 : ℝ≥0∞) ≤ μ {ω | 28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        regretAd K σ (fun t => pol t ω) n} := by
  have hP := good_pK_ext hd hn hR1 hRk
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hdim := ripeB_dim d hdR
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hn0 : 0 < n := by omega
  have hn4 := ripeB_n d n hdR hnR
  obtain ⟨hs0, hs4⟩ := ripeB_sig d n hdR hnR
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hR0 : 0 < R0 := by linarith
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hΓ : 4 ≤ gamR d n := gamR_ge d n (by linarith) hn4
  -- the parameters of the count
  have h16 := (ripeK_params_ext hd hn hR1 hRk).2.2.2
  have hX : Real.exp 1 / 2 ≤ xCount d ((pK d n R0).w d) := by
    have := Real.exp_one_lt_d9
    exact le_trans (by linarith) h16
  have hxc : 16 ≤ xCount d ((pK d n R0).w d) := h16
  have hN : 0 < nStar d ((pK d n R0).w d) := by
    have h1 := nStar_ge_x d ((pK d n R0).w d) (by linarith)
    have hpos : 0 < xCount d ((pK d n R0).w d) / 2 := by linarith
    have h8 : 1 ≤ Real.log (xCount d ((pK d n R0).w d) / 2) := by
      rw [Real.le_log_iff_exp_le hpos]
      have := Real.exp_one_lt_d9
      linarith
    nlinarith
  -- the level and the threshold
  set Y := 1 / 10 ^ 5 * sigB n * ((d : ℝ) * Real.sqrt d) * Real.sqrt (n * gamR d n) / kRipe d with hY_def
  have hthr := ripe_prob_threshold d n hdR hnR
  rw [← hY_def] at hthr
  have hθ0 : 0 < 28 / 10 ^ 10 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d := by
    have := ripeB_log d hdR
    have : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnn
    positivity
  set x := Y - 1 / 2 - sigB n * Real.sqrt n with hx_def
  have hsq : 0 ≤ sigB n * Real.sqrt n := mul_nonneg hs0.le (Real.sqrt_nonneg _)
  have hx : 0 ≤ x := by linarith
  -- Proposition STOP and its balance
  have hfacts := stopFacts_of_good I hP hX hN μ hn0 hpolB hx
  have hYx : x + 1 / 2 + (pK d n R0).sc * Real.sqrt n = Y := by
    change x + 1 / 2 + sigB n * Real.sqrt n = Y
    rw [hx_def]
    ring
  rw [hYx] at hfacts
  have hq := stop_rate_K hd1 hs0 hR1 hn4 hdim (R2_ripe_Kext d n (sigB n) R0 hd1 hdim hs0 hR1 hRk hnR)
    (log_x_ripe_ge_Kext d n (kRipe d) R0 (by linarith) (by linarith) hnn (by linarith) hR0
      (log_R0_le_ext d n (kRipe d) R0 hd1 (by linarith) hR0 hRk hnR)) hY_def hfacts
  -- the probabilities
  have hcross := prob_regG_ge hP μ hn0 hpolB x
  set θ := 28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d with hθ_def
  have hθ : θ ≤ x - 7 * (pK d n R0).sc * Real.sqrt n := by
    change θ ≤ x - 7 * sigB n * Real.sqrt n
    rw [hθ_def, rpow_three_halves d (by linarith), hx_def]
    linarith
  have hmono : (gameLaw (prior d (1 / 2)) μ).real
      {s | x - 7 * (pK d n R0).sc * Real.sqrt n ≤ regG (prior d (1 / 2)) (pK d n R0) pol n s} ≤
      (gameLaw (prior d (1 / 2)) μ).real {s | θ ≤ regG (prior d (1 / 2)) (pK d n R0) pol n s} :=
    measureReal_mono fun s hs => le_trans hθ hs
  have hclamp := prob_regG_clamped (P := pK d n R0) μ pol hn1 θ
  have hn2 : 2 / (n : ℝ) ^ 2 ≤ 1 / 1000 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h100 : (100 : ℝ) ≤ n := by
      have : (4000000 : ℝ) ^ 10 ≤ n := (pow_le_pow_left₀ (by norm_num) hdR 10).trans hnR
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpr : (1 / 2 : ℝ) ≤ (gameLaw (prior d (1 / 2)) μ).real
      {s | θ ≤ regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} := by
    linarith
  have hsc : (pK d n R0).sc * ellB n ≤ 1 / 8 := (sigB_mul_ellB hn1).le
  obtain ⟨σ, hσ, hm, hge⟩ := derand_prob I hP hsc hK hK1 hK2 μ hpol hpr
  refine ⟨σ, hσ, hm, le_trans (le_of_eq ?_) hge⟩
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

end Top

end AdversarialBco.Lower.Stop
