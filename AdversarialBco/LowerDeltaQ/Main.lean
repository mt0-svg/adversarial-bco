/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Prob
public import AdversarialBco.LowerDelta.Main

@[expose] public section

/-!
# Theorem LU-DQ on every body of the class

The lower bound with failure probability `δ` stopped on the bowl, in the objects of
clause (b) of `TheoremLowerU` (StatementUnifiedLower.lean): every body of `BodyU`, every learner of `IsLearnerAd`,
strategies of `StratsLowU K n r0`. With `D = d^{3/2} n^{1/2}/ln d`, `k₀ = 120 ln d + 68` and `δ₀ = min(δ, 1/2)`:

* (a) `lowerU_probDeltaQ`: for `δ ∈ (0, 1)`, `d ≥ 4·10^6`, `n ≥ d^10`, (D1) `1024 k₀ ≤ δ₀ d` and
  (D3) `10 k₀ ≤ δ₀^{3/2} d`, a strategy against which the regret is measurable in the seed, nonnegative on every seed,
  and at least `2.1·10^-8 δ₀^{3/2} D` with probability at least `1 - δ`;
* (b) `lowerU_meanDeltaQ`: for `d ≥ 4·10^6`, `n ≥ d^10`, a strategy against which the regret is integrable with mean at
  least `3.71·10^-9 D`, from (a) at `δ = 1/2` through the nonnegativity (`mean_of_prob`: `E Reg ≥ θ P(Reg ≥ θ)`).

The body is put in position (Lemma POS `position_facts`, Lemma AFF
`pullStrat_mem_mid`, `regretAd_pushLearner`), on `lowerBodyProbDeltaQ_mid` at `s = δ₀^{1/2}`, so that
`δ₀^{3/2} = s³`; for `δ > 1/2` it is the instance `δ₀ = 1/2`, whose probability `1/2` is at least `1 - δ`. At
`δ₀ = 1/2` both range conditions follow from `d ≥ 2048 k₀` (`ripeB_dim`).
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

namespace AdversarialBco.LowerDeltaQ

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Top AdversarialBco.UnifiedLower
  AdversarialBco.UnifiedLower.Body AdversarialBco.LowerDelta

/-- Theorem LU-DQ at `δ₀ = s²` on every body of `BodyU`: the strategy of `lowerBodyProbDeltaQ_mid` on the position of
the body (Lemma POS), pulled back (Lemma AFF). -/
theorem lowerU_probDeltaQ_s {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {s : ℝ} (hs : 0 < s)
    (hs2 : s ^ 2 ≤ 1 / 2) (hD1 : 1024 * kRipe d ≤ s ^ 2 * d) (hD3 : 10 * kRipe d ≤ s ^ 3 * d) {K : Set (E d)}
    {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsLowU K n r0, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n ∧ regretAd K σ (fun t => pol t ω) n ≤ n / 2) ∧
      ENNReal.ofReal (1 - s ^ 2) ≤ μ {ω | 21 / 10 ^ 9 * s ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n /
        Real.log d ≤ regretAd K σ (fun t => pol t ω) n} := by
  obtain ⟨T, hKc, hK1, hK2, hT⟩ := position_facts hd hb
  obtain ⟨hR1, hRk⟩ := posR_bounds hd
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  obtain ⟨σ', hσ', hm', hbd, hprob⟩ :=
    lowerBodyProbDeltaQ_mid lowerTopInputs hd hn hKc hK1 hK2 hR1 hRk hs hs2 hD1 hD3 μ (isLearnerAd_push T hpol)
  have hr0 := hb.1
  have hsg := sigB_le n hn1
  have hs0 : 0 ≤ sigB n := by unfold sigB; positivity
  have hpull := pullStrat_mem_mid T (L := sigB n / posR d) (M := posR d / r0) (by positivity) hT hσ'
  refine ⟨pullStrat T σ', stratsMid_lowU hr0 ?_ hpull, ?_, ?_, ?_⟩
  · have hR0 : 0 < posR d := by linarith
    rw [show sigB n / posR d * (posR d / r0) = sigB n / r0 by field_simp]
    rw [div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  · simpa only [regretAd_pushLearner] using hm'
  · simpa only [regretAd_pushLearner] using hbd
  · simpa only [regretAd_pushLearner] using hprob

/-- `δ₀ = s²` and `δ₀^{3/2} = s³` at `s = δ₀^{1/2}`. -/
theorem sqrt_facts {e : ℝ} (he : 0 < e) :
    0 < Real.sqrt e ∧ Real.sqrt e ^ 2 = e ∧ Real.sqrt e ^ 3 = e ^ (3 / 2 : ℝ) := by
  have h2 : Real.sqrt e ^ 2 = e := Real.sq_sqrt he.le
  refine ⟨Real.sqrt_pos.2 he, h2, ?_⟩
  rw [rpow_three_halves e he.le, pow_succ, h2]

/-- **Theorem LU-DQ (a)**, in the objects of clause (b) of `TheoremLowerU`: for `δ ∈ (0, 1)`, `d ≥ 4·10^6`,
`n ≥ d^10`, (D1) `1024 k₀ ≤ δ₀ d` and (D3) `10 k₀ ≤ δ₀^{3/2} d` with `δ₀ = min(δ, 1/2)`, on every body of `BodyU` and
against every learner of `IsLearnerAd`, a strategy of `StratsLowU K n r0` against which the regret is measurable in the
seed, nonnegative on every seed, and at least `2.1·10^-8 δ₀^{3/2} d^{3/2} n^{1/2}/ln d` with probability at least
`1 - δ`. -/
theorem lowerU_probDeltaQ {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (hD1 : 1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d)
    (hD3 : 10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d) {K : Set (E d)} {a : E d}
    {r0 R0 : ℝ} (hb : BodyU K a r0 R0) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsLowU K n r0, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n) ∧
      ENNReal.ofReal (1 - δ) ≤ μ {ω | 21 / 10 ^ 9 * min δ (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) *
        Real.sqrt n / Real.log d ≤ regretAd K σ (fun t => pol t ω) n} := by
  have he0 : 0 < min δ (1 / 2) := lt_min hδ0 (by norm_num)
  have he1 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have heδ : min δ (1 / 2) ≤ δ := min_le_left _ _
  obtain ⟨hs, hs2, hs3⟩ := sqrt_facts he0
  obtain ⟨σ, hσ, hmeas, hbd, hprob⟩ := lowerU_probDeltaQ_s hd hn hs (by rw [hs2]; exact he1)
    (by rw [hs2]; exact hD1) (by rw [hs3]; exact hD3) hb μ hpol
  refine ⟨σ, hσ, hmeas, fun ω => (hbd ω).1, ?_⟩
  rw [hs2, hs3] at hprob
  exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hprob

/-- `(1/2)^{1/2} ≥ 0.7071`, so `(1/2)^{3/2} ≥ 0.3535`. -/
theorem sqrt_half_cube_ge : 3535 / 10000 ≤ Real.sqrt (1 / 2) ^ 3 := by
  have h : (7071 / 10000 : ℝ) ≤ Real.sqrt (1 / 2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  calc (3535 / 10000 : ℝ) ≤ (7071 / 10000) ^ 3 := by norm_num
    _ ≤ Real.sqrt (1 / 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3

/-- The range of Theorem LU-DQ at `δ₀ = 1/2` holds for every `d ≥ 4·10^6`: (D1) `1024 k₀ ≤ d/2` and (D3)
`10 k₀ ≤ (1/2)^{3/2} d`, both from `d ≥ 2048 k₀` (`ripeB_dim`). -/
theorem range_half {d : ℕ} (hd : 4000000 ≤ d) :
    1024 * kRipe d ≤ Real.sqrt (1 / 2) ^ 2 * d ∧ 10 * kRipe d ≤ Real.sqrt (1 / 2) ^ 3 * d := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdim := ripeB_dim d hdR
  have hk := (kRipe_ge d (by linarith) hdim).1
  have h3 := sqrt_half_cube_ge
  rw [Real.sq_sqrt (by norm_num)]
  constructor
  · linarith
  · have : 3535 / 10000 * (d : ℝ) ≤ Real.sqrt (1 / 2) ^ 3 * d :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    linarith

/-- **Theorem LU-DQ (b)**, the mean, in the objects of clause (a) of `TheoremLowerU`: for `d ≥ 4·10^6` and
`n ≥ d^10`, on every body of `BodyU` and against every learner of `IsLearnerAd`, a strategy of `StratsLowU K n r0`
against which the regret is integrable with mean at least `3.71·10^-9 d^{3/2} n^{1/2}/ln d`; from (a) at `δ₀ = 1/2`,
`E Reg ≥ θ P(Reg ≥ θ)` with `Reg ≥ 0` on every seed, `θ = 2.1·10^-8 (1/2)^{3/2} D ≥ 7.42·10^-9 D`. -/
theorem lowerU_meanDeltaQ {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)} {a : E d} {r0 R0 : ℝ}
    (hb : BodyU K a r0 R0) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    LowerMean K n r0 μ pol (371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hs, hs2, -⟩ := sqrt_facts (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨hD1, hD3⟩ := range_half hd
  obtain ⟨σ, hσ, hmeas, hbd, hprob⟩ := lowerU_probDeltaQ_s hd hn hs (by rw [hs2]) hD1 hD3 hb μ hpol
  have hL := ripeB_log d hdR
  have hD : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have h3 := sqrt_half_cube_ge
  have hθ : 0 ≤ 21 / 10 ^ 9 * Real.sqrt (1 / 2) ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
    positivity
  obtain ⟨hint, hmean⟩ := mean_of_prob hmeas (fun ω => (hbd ω).1) (fun ω => (hbd ω).2) hθ hprob
  refine ⟨σ, hσ, hint, le_trans ?_ hmean⟩
  rw [hs2]
  have e1 : 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
      371 / 10 ^ 11 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by ring
  have e2 : 21 / 10 ^ 9 * Real.sqrt (1 / 2) ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d * (1 - 1 / 2) =
      21 / 10 ^ 9 * Real.sqrt (1 / 2) ^ 3 / 2 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hD

end AdversarialBco.LowerDeltaQ
