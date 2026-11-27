/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Stop

@[expose] public section

/-!
# Proposition STOP: the stopped game (F1), (F4), (F5) and the structure `StopFacts`

Proposition STOP (the paper's stopped balance) at the parameters of a `Good` strategy, for plays in `B(0, R0)`,
with the stopped live events `S'_t = stopSet P pol x t` of Stop.lean:

- (F1) `stop_round`: the three inequalities of `round_bound` in mean over `S'_t ⊆ liveSet t`;
- (F4) `stop_live`: `P(S'_t) ≥ 1 - p' - q` with `p' = Σ_{t < n} P(S'_t, round t + 1 dead)` and `q` the probability that
  the observed cumulative `C_u = Σ_{i < u} (o_i - b)` exceeds `x` for some `u ≤ n`;
- (F5) `stop_regret`: `Σ_t E[D̄_t; S'_t] ≤ x + 1/2 + σ √n`. The note bounds the overshoot of the stopping round by
  `2σ + σ E max_s Z_s^+`; here the dent of the last round is bounded by its range `1/2` and `σ Z_m` by
  `σ (a/2 + Σ_{t < n} Z_t²/(2a))` with `a = √n`, mean `σ √n`;
- `stopFacts`: the fields of `StopFacts` (StopBalance.lean) from (F1) to (F5), with (F2) `stop_payment` and (F3)
  `stop_count` of Stop.lean.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Stop

open RealRAM Bayes _root_.AdversarialBco.Lower.Top

/-! ## (F5) on the reals: the stopped sum of the dents -/

section Pure

/-- The sum of the dents over the rounds before the stopping time. With `C_{t+1} = C_t + D_t + σ Z_t`, `C_0 = 0`,
`C_t ≤ x` on the stopped rounds `St t` (decreasing in `t`) and dents at most `1/2`:
`Σ_{t < n, St t} D_t ≤ x + 1/2 + σ (a/2 + Σ_{t < n} Z_t²/(2a)) - σ Σ_{t < n, St t} Z_t`. -/
theorem stopped_sum_le {St : ℕ → Prop} [DecidablePred St] (hanti : ∀ t, St (t + 1) → St t) {C D Z : ℕ → ℝ}
    {x σ a : ℝ} (hx : 0 ≤ x) (hσ : 0 ≤ σ) (ha : 0 < a) (hC0 : C 0 = 0)
    (hC : ∀ t, C (t + 1) = C t + D t + σ * Z t) (hSx : ∀ t, St t → C t ≤ x) (n : ℕ) (hD : ∀ t < n, D t ≤ 1 / 2) :
    ∑ t ∈ range n, (if St t then D t else 0) ≤
      x + 1 / 2 + σ * (a / 2 + ∑ t ∈ range n, Z t ^ 2 / (2 * a)) - σ * ∑ t ∈ range n, (if St t then Z t else 0) := by
  have hsplit : ∀ m, ∑ t ∈ range m, (if St t then D t else 0) =
      ∑ t ∈ range m, (if St t then D t + σ * Z t else 0) - σ * ∑ t ∈ range m, (if St t then Z t else 0) := by
    intro m
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  have hA : ∀ m, St m → ∑ t ∈ range m, (if St t then D t + σ * Z t else 0) = C m := by
    intro m
    induction m with
    | zero => intro _; simp [hC0]
    | succ m ih =>
      intro hm
      rw [sum_range_succ, ih (hanti m hm), ite_eq_left (hanti m hm), hC m]
      ring
  have hamgm : ∀ z : ℝ, z ≤ a / 2 + z ^ 2 / (2 * a) := fun z => by
    have h : a / 2 + z ^ 2 / (2 * a) - z = (z - a) ^ 2 / (2 * a) := by
      field_simp
      ring
    have : 0 ≤ (z - a) ^ 2 / (2 * a) := by positivity
    linarith
  have hB : ∀ m ≤ n, ∑ t ∈ range m, (if St t then D t + σ * Z t else 0) ≤
      x + 1 / 2 + σ * (a / 2 + ∑ t ∈ range m, Z t ^ 2 / (2 * a)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [range_zero, sum_empty, add_zero]
      have : 0 ≤ σ * (a / 2) := mul_nonneg hσ (by positivity)
      linarith
    | succ m ih =>
      intro hm
      have hz : 0 ≤ σ * (Z m ^ 2 / (2 * a)) := mul_nonneg hσ (by positivity)
      rw [sum_range_succ, sum_range_succ]
      by_cases hs : St m
      · rw [ite_eq_left hs, hA m hs]
        have h1 := hSx m hs
        have h2 := hD m (by omega)
        have h3 := mul_le_mul_of_nonneg_left (hamgm (Z m)) hσ
        have h4 : 0 ≤ σ * ∑ t ∈ range m, Z t ^ 2 / (2 * a) :=
          mul_nonneg hσ (sum_nonneg fun t _ => by positivity)
        nlinarith
      · rw [ite_eq_right hs, add_zero]
        have := ih (by omega)
        nlinarith
  rw [hsplit]
  linarith [hB n le_rfl]

end Pure

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-! ## (F4): the stopped live event fails only through a crossing or a dead posterior -/

section Live

/-- The crossing event: the observed cumulative exceeds `x` at some `u ≤ n`. -/
def crossSet (P : SParams) (pol : Learner Ω d) (x : ℝ) (n : ℕ) : Set (Sample d Ω) :=
  {s | ∃ u ≤ n, x < cumO P pol u s}

theorem measurable_cumO {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {u : ℕ} (hu : u ≤ n) : Measurable (cumO P pol u) := by
  have hR := ruleS_meas_prior hP
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i < n := lt_of_lt_of_le (mem_range.1 hi) hu
  have hq : Measurable (fun s : Sample d Ω => (hist (prior d (1 / 2)) (ruleS d P) P.sc pol i s,
      play pol i s.2.2 (hist (prior d (1 / 2)) (ruleS d P) P.sc pol i s), s.1)) := by
    have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc hpol' hi'.le
    have hpl := (measurable_play (α := Option Cell) (hpol' i hi')).comp
      ((measurable_snd.comp measurable_snd).prodMk hh)
    exact hh.prodMk (hpl.prodMk measurable_fst)
  have h1 := (measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc i).2.comp hq
  have h2 := (h1.add ((measurable_const (a := P.sc)).mul (measurable_noise (d := d) (Ω := Ω) i))).sub_const P.b
  exact h2

omit [MeasurableSpace Ω] in
/-- The posterior before the first round is live when `N* > 0` (Lemma COUNT (b) at the prior, whose divergence is
`0`). -/
theorem live_zero {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (pol : Learner Ω d) (s : Sample d Ω) : s ∈ liveSet P pol 0 := by
  by_contra h
  have hd' : dLive (P.w d) (covM (postT P pol 0 s)) < d / 2 := not_le.1 h
  have hR := ruleS_meas_prior hP
  obtain ⟨C, hC, hρC⟩ := dens_le_bound (prior d (1 / 2)) (ruleS d P) P.sc 0
    (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)
  have hρ : Measurable (dens (prior d (1 / 2)) (ruleS d P) P.sc 0
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)) := by
    have h' := (measurable_dens (prior d (1 / 2)) (ruleS d P) hR P.sc 0).comp
      (measurable_prodMk_left (x := hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s))
    exact h'
  have hc := count_b (by have := hP.d_pos; omega) hP.w_pos hX hρ hC hρC
    ((dens_props (prior d (1 / 2)) (ruleS d P) hR P.sc 0).2.2 _) hd'
  have h0 : klDens (prior d (1 / 2)) (dens (prior d (1 / 2)) (ruleS d P) P.sc 0
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)) = 0 := klDens_one _
  linarith

omit [MeasurableSpace Ω] in
/-- The complement of the stopped live event of round `t ≤ n` lies in the crossing event or in the union of the dead
exits `S'_{t'} ∩ (live_{t'+1})ᶜ`, `t' < n`. -/
theorem stopSet_compl_sub {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (pol : Learner Ω d) (x : ℝ) {n t : ℕ} (ht : t ≤ n) :
    (stopSet P pol x t)ᶜ ⊆
      crossSet P pol x n ∪ ⋃ t' ∈ range n, (stopSet P pol x t' ∩ (liveSet P pol (t' + 1))ᶜ) := by
  induction t with
  | zero =>
    intro s hs
    left
    rw [Set.mem_compl_iff, mem_stopSet, not_and_or] at hs
    rcases hs with h | h
    · exact absurd (live_zero hP hX hN pol s) h
    · push Not at h
      obtain ⟨u, hu, hux⟩ := h
      exact ⟨u, by omega, hux⟩
  | succ t ih =>
    intro s hs
    by_cases hst : s ∈ stopSet P pol x t
    · rw [Set.mem_compl_iff, mem_stopSet, not_and_or] at hs
      rcases hs with h | h
      · right
        exact Set.mem_iUnion₂.2 ⟨t, mem_range.2 (by omega), hst, h⟩
      · left
        push Not at h
        obtain ⟨u, hu, hux⟩ := h
        exact ⟨u, by omega, hux⟩
    · exact ih (by omega) hst

/-- (F4): `P(S'_t) ≥ 1 - p' - q` for `t ≤ n`. -/
theorem stop_live {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t ≤ n) :
    1 - ∑ t' ∈ range n, (gameLaw (prior d (1 / 2)) μ).real (stopSet P pol x t' ∩ (liveSet P pol (t' + 1))ᶜ) -
        (gameLaw (prior d (1 / 2)) μ).real (crossSet P pol x n) ≤
      (gameLaw (prior d (1 / 2)) μ).real (stopSet P pol x t) := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have h1 := probReal_compl_eq_one_sub (μ := gameLaw (prior d (1 / 2)) μ) (measurableSet_stopSet hP hpol x ht)
  have h2 := (measureReal_mono (μ := gameLaw (prior d (1 / 2)) μ) (stopSet_compl_sub hP hX hN pol x ht)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le _ _)))
  linarith

end Live

/-! ## (F5): the regret before the stopping time -/

section Regret

/-- The dent of round `t` on the stopped live event, as a function of the tip, the history and the seed. -/
noncomputable def stopDentF (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) :
    E d × Hist d (Option Cell) × Ω → ℝ :=
  {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t}.indicator fun p =>
    (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t p.2.1) (play pol t p.2.2 p.2.1) p.1 - P.b

theorem measurable_stopDentF {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} (x : ℝ) {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (stopDentF P pol x t) := by
  have hR := ruleS_meas_prior hP
  have hq : Measurable (fun p : E d × Hist d (Option Cell) × Ω => (p.2.1, play pol t p.2.2 p.2.1, p.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (((measurable_play (α := Option Cell) hpol).comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))).prodMk measurable_fst)
  have h1 := ((measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).2.comp hq).sub_const P.b
  exact h1.indicator ((measurableSet_stopH hP x t).preimage (measurable_fst.comp measurable_snd))

theorem abs_stopDentF_le (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n)
    (p : E d × Hist d (Option Cell) × Ω) : |stopDentF P pol x t p| ≤ 1 / 2 := by
  unfold stopDentF
  by_cases hp : p ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t}
  · rw [Set.indicator_of_mem hp]
    have hx : play pol t p.2.2 p.2.1 ∈ Metric.closedBall (0 : E d) R0 := (hpol t ht).2 _ _ _
    obtain ⟨h0, h1⟩ := sig_post_bounds I hP t p.2.1 hx p.1
    have := hP.rng
    rw [abs_le]
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hp, abs_zero]
    norm_num

omit [MeasurableSpace Ω] in
theorem stopDentF_sample (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) :
    stopDentF P pol x t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) =
      (stopSet P pol x t).indicator (dentT P pol t) s := by
  unfold stopDentF
  by_cases hs : s ∈ stopSet P pol x t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t} from hs)]
    rfl
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∉ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t} from hs)]

omit [MeasurableSpace Ω] in
theorem integral_stopDentF_post (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) :
    ∫ θ, stopDentF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
        ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) =
      (stopSet P pol x t).indicator (Df P pol t) s := by
  unfold stopDentF
  by_cases hs : s ∈ stopSet P pol x t
  · have hin : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∈
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t} := fun θ => hs
    simp only [Set.indicator_of_mem (hin _), Set.indicator_of_mem hs]
    rfl
  · have hout : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∉
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopH P x t} := fun θ => hs
    simp only [Set.indicator_of_notMem (hout _), Set.indicator_of_notMem hs, integral_zero]

/-- By Lemma POST, the posterior mean of the dent on `S'_t` is the dent at the tip on `S'_t`. -/
theorem setIntegral_stop_Df (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) :
    ∫ s in stopSet P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, (stopSet P pol x t).indicator (dentT P pol t) s ∂gameLaw (prior d (1 / 2)) μ := by
  have hR := ruleS_meas_prior hP
  have hpd := post_disintegrates_integral (prior d (1 / 2)) μ (ruleS d P) hR hP.sc_pos.ne'
    (fun t ht => (hpol t ht).1) ht.le (measurable_stopDentF hP x (hpol t ht).1) (abs_stopDentF_le I hP hpol x ht)
  rw [← integral_indicator (measurableSet_stopSet hP hpol x ht.le)]
  calc ∫ s, (stopSet P pol x t).indicator (Df P pol t) s ∂gameLaw (prior d (1 / 2)) μ
      = ∫ s, ∫ θ, stopDentF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
          ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
          ∂gameLaw (prior d (1 / 2)) μ :=
        integral_congr_ae (ae_of_all _ fun s => (integral_stopDentF_post P pol x t s).symm)
    _ = ∫ s, stopDentF P pol x t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
          ∂gameLaw (prior d (1 / 2)) μ := hpd.symm
    _ = _ := integral_congr_ae (ae_of_all _ fun s => stopDentF_sample P pol x t s)

theorem integrable_stopDent (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) :
    Integrable ((stopSet P pol x t).indicator (dentT P pol t)) (gameLaw (prior d (1 / 2)) μ) := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hR := ruleS_meas_prior hP
  have he : (stopSet P pol x t).indicator (dentT P pol t) =
      fun s => stopDentF P pol x t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) :=
    funext fun s => (stopDentF_sample P pol x t s).symm
  have hq : Measurable (fun s : Sample d Ω => (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)) :=
    measurable_fst.prodMk ((measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc (fun t ht => (hpol t ht).1)
      ht.le).prodMk (measurable_snd.comp measurable_snd))
  have hm := (measurable_stopDentF hP x (hpol t ht).1).comp hq
  rw [he]
  exact (integrable_const (1 / 2 : ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact abs_stopDentF_le I hP hpol x ht _)

/-- The weights of the stopped noise sum: `1_{S'_t}`. -/
noncomputable def stopW (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) : ℝ :=
  (stopSet P pol x t).indicator (fun _ => 1) s

theorem stopW_props {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) :
    (∀ t < n, Measurable (stopW P pol x t)) ∧ (∀ t < n, ∀ s, |stopW P pol x t s| ≤ 1) ∧
      ∀ t < n, ReadsBefore t (stopW P pol x t) := by
  refine ⟨fun t ht => measurable_const.indicator (measurableSet_stopSet hP hpol x ht.le), fun t _ s => ?_,
    fun t _ s s' h1 h3 h2 => ?_⟩
  · unfold stopW
    by_cases hs : s ∈ stopSet P pol x t
    · rw [Set.indicator_of_mem hs, abs_one]
    · rw [Set.indicator_of_notMem hs, abs_zero]
      norm_num
  · unfold stopW
    have hc := stopSet_congr P pol x t h1 h2 h3
    by_cases hs : s ∈ stopSet P pol x t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hc.1 hs)]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (mt hc.2 hs)]

/-- (F5) pointwise, with the weight `a`. -/
theorem stop_regret_point (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {x : ℝ} (hx : 0 ≤ x) {a : ℝ} (ha : 0 < a)
    (s : Sample d Ω) :
    ∑ t ∈ range n, (stopSet P pol x t).indicator (dentT P pol t) s ≤
      x + 1 / 2 + P.sc * a / 2 + P.sc / (2 * a) * ∑ t ∈ range n, s.2.1 t ^ 2 -
        P.sc * noiseSum (stopW P pol x) n s := by
  classical
  have h := stopped_sum_le (St := fun t => s ∈ stopSet P pol x t) (fun t h => stopSet_succ hP pol x t h)
    (C := fun u => cumO P pol u s) (D := fun t => dentT P pol t s) (Z := fun t => s.2.1 t) hx hP.sc_pos.le ha
    (by simp [cumO]) (fun t => by simp only [cumO, sum_range_succ, obsB_eq]; ring)
    (fun t h => (mem_stopSet.1 h).2 t le_rfl) n (fun t ht => by
      have hx : playT P pol t s ∈ Metric.closedBall (0 : E d) R0 := (hpol t ht).2 _ _ _
      have := (sig_post_bounds I hP t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) hx s.1).2
      have := hP.rng
      unfold dentT
      linarith)
  have e1 : ∀ t ∈ range n, (stopSet P pol x t).indicator (dentT P pol t) s =
      if s ∈ stopSet P pol x t then dentT P pol t s else 0 := fun t _ => by
    by_cases hs : s ∈ stopSet P pol x t
    · rw [Set.indicator_of_mem hs, ite_eq_left hs]
    · rw [Set.indicator_of_notMem hs, ite_eq_right hs]
  have e2 : noiseSum (stopW P pol x) n s = ∑ t ∈ range n, if s ∈ stopSet P pol x t then s.2.1 t else 0 := by
    unfold noiseSum stopW
    refine sum_congr rfl fun t _ => ?_
    by_cases hs : s ∈ stopSet P pol x t
    · rw [Set.indicator_of_mem hs, ite_eq_left hs, one_mul]
    · rw [Set.indicator_of_notMem hs, ite_eq_right hs, zero_mul]
  have e3 : P.sc * (a / 2 + ∑ t ∈ range n, s.2.1 t ^ 2 / (2 * a)) =
      P.sc * a / 2 + P.sc / (2 * a) * ∑ t ∈ range n, s.2.1 t ^ 2 := by
    rw [mul_add, mul_sum, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun t _ => by ring
  rw [sum_congr rfl e1, e2]
  linarith

/-- (F5): `Σ_t E[D̄_t; S'_t] ≤ x + 1/2 + σ √n`. -/
theorem stop_regret (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hn : 0 < n) (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {x : ℝ}
    (hx : 0 ≤ x) :
    ∑ t ∈ range n, ∫ s in stopSet P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
      x + 1 / 2 + P.sc * Real.sqrt n := by
  have hπ := isProbabilityMeasure_prior d (show (0 : ℝ) < 1 / 2 by norm_num)
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.sqrt n with ha_def
  have ha : 0 < a := Real.sqrt_pos.2 hnR
  have ha2 : a ^ 2 = n := Real.sq_sqrt hnR.le
  obtain ⟨hVm, hVb, hVr⟩ := stopW_props hP hpol x
  rw [sum_congr rfl fun t ht => setIntegral_stop_Df I hP μ hpol x (mem_range.1 ht),
    ← integral_finsetSum _ fun t ht => integrable_stopDent I hP μ hpol x (mem_range.1 ht)]
  have i1 : Integrable (fun s : Sample d Ω => ∑ t ∈ range n, s.2.1 t ^ 2) (gameLaw (prior d (1 / 2)) μ) :=
    integrable_finsetSum _ fun t _ => integrable_noise_sq (prior d (1 / 2)) μ t
  have i2 : Integrable (noiseSum (stopW P pol x) n) (gameLaw (prior d (1 / 2)) μ) :=
    (memLp_noiseSum (prior d (1 / 2)) μ hVm hVb).integrable one_le_two
  have hR : Integrable (fun s : Sample d Ω => x + 1 / 2 + P.sc * a / 2 + P.sc / (2 * a) * ∑ t ∈ range n, s.2.1 t ^ 2 -
      P.sc * noiseSum (stopW P pol x) n s) (gameLaw (prior d (1 / 2)) μ) :=
    ((integrable_const _).add (i1.const_mul _)).sub (i2.const_mul _)
  refine (integral_mono (integrable_finsetSum _ fun t ht => integrable_stopDent I hP μ hpol x (mem_range.1 ht)) hR
    fun s => stop_regret_point I hP hpol hx ha s).trans (le_of_eq ?_)
  have hKS : Integrable (fun s : Sample d Ω => x + 1 / 2 + P.sc * a / 2 + P.sc / (2 * a) * ∑ t ∈ range n, s.2.1 t ^ 2)
      (gameLaw (prior d (1 / 2)) μ) := (integrable_const _).add (i1.const_mul _)
  have hσN : Integrable (fun s : Sample d Ω => P.sc * noiseSum (stopW P pol x) n s) (gameLaw (prior d (1 / 2)) μ) :=
    i2.const_mul _
  have hS : ∫ s, ∑ t ∈ range n, s.2.1 t ^ 2 ∂gameLaw (prior d (1 / 2)) μ = n := by
    rw [integral_finsetSum _ fun t _ => integrable_noise_sq (prior d (1 / 2)) μ t]
    simp only [integral_noise_sq, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hN : ∫ s, noiseSum (stopW P pol x) n s ∂gameLaw (prior d (1 / 2)) μ = 0 :=
    integral_noiseSum (prior d (1 / 2)) μ hVm hVb hVr
  have e2 : ∫ s, (x + 1 / 2 + P.sc * a / 2 + P.sc / (2 * a) * ∑ t ∈ range n, s.2.1 t ^ 2) ∂gameLaw (prior d (1 / 2)) μ =
      x + 1 / 2 + P.sc * a / 2 + P.sc / (2 * a) * n := by
    rw [integral_add (integrable_const _) (i1.const_mul _), integral_const, probReal_univ, one_smul,
      integral_const_mul, hS]
  have e3 : ∫ s, P.sc * noiseSum (stopW P pol x) n s ∂gameLaw (prior d (1 / 2)) μ = 0 := by
    rw [integral_const_mul, hN, mul_zero]
  have e4 : P.sc / (2 * a) * n = P.sc * a / 2 := by
    rw [← ha2]
    field_simp
  rw [integral_sub hKS hσN, e2, e3, e4]
  ring

end Regret

/-! ## (F1) and the structure `StopFacts` -/

section Facts

/-- (F1): the three inequalities of `round_bound` in mean over the stopped live event `S'_t ⊆ liveSet t`. -/
theorem stop_round (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) :
    ∫ s in stopSet P pol x t, Jf P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
        (4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k *
          ∫ s in stopSet P pol x t, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ +
        P.g / (P.sc ^ 2 * priceR d P.k) * ∫ s in stopSet P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ∧
      P.g / 2 * (999 / 1000 * (gameLaw (prior d (1 / 2)) μ).real (stopSet P pol x t) -
          ∫ s in stopSet P pol x t, af P pol t s ∂gameLaw (prior d (1 / 2)) μ) ≤
        ∫ s in stopSet P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ∧
      ∫ s in stopSet P pol x t, af P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
        4 / P.k * ∫ s in stopSet P pol x t, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ := by
  have hG : IsProbabilityMeasure (gameLaw (prior d (1 / 2)) μ) := isProbabilityMeasure_gameLaw _ μ
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hR := ruleS_meas_prior hP
  have hsc : P.sc ≠ 0 := hP.sc_pos.ne'
  have hS₀ : ∀ t < n, ∀ h θ ω, |(ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t h)
      (play pol t ω h) θ| ≤ 1 := fun t ht h θ ω => abs_sig_post_le I hP t h ((hpol t ht).2 _ _ _) θ
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hB : 0 ≤ chanBK P.L R0 P.g P.sc := by unfold chanBK; positivity
  have hJi : Integrable (Jf P pol t) (gameLaw (prior d (1 / 2)) μ) :=
    I.integrable_infoRound (prior d (1 / 2)) μ (ruleS d P) hR hsc hpol' hS₀ ht
  have hPi : Integrable (Pf P pol t) (gameLaw (prior d (1 / 2)) μ) :=
    (I.ledger_game hP.d_pos (show (0 : ℝ) < 1 / 2 by norm_num) μ (ruleS d P) hR hsc hpol' hP.w_pos.ne').1 t ht
  have hai : Integrable (af P pol t) (gameLaw (prior d (1 / 2)) μ) :=
    (integrable_const (1 : ℝ)).mono' (measurable_af hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := af_mem hP pol t s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hDi : Integrable (Df P pol t) (gameLaw (prior d (1 / 2)) μ) :=
    (integrable_const (1 : ℝ)).mono' (measurable_Df hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := Df_mem I hP hpol ht s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  exact round_integral (gameLaw (prior d (1 / 2)) μ) (stopSet P pol x t) (measurableSet_stopSet hP hpol x ht.le)
    ((4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k) (P.g / (P.sc ^ 2 * priceR d P.k)) P.g P.k
    (Jf P pol t) (Pf P pol t) (af P pol t) (Df P pol t) hJi hPi hai hDi fun s hs => by
      obtain ⟨pr, H, Iann, Irest, Drest, preg, hRF⟩ := roundFacts_at I hP hpol ht (stopSet_sub_live P pol x t hs)
      exact round_bound hk hP.dim hP.g_pos.le hB hRF

/-- **Proposition STOP** at a `Good` strategy, for plays in `B(0, R0)` and a level `x ≥ 0`: the fields (F1) to (F5)
of `StopFacts`, with `p' = Σ_{t < n} P(S'_t, round t + 1 dead)`, `q = P(C_u > x for some u ≤ n)` and
`Y = x + 1/2 + σ √n`. -/
theorem stopFacts_of_good (I : Inputs) {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d} {n : ℕ} (hn : 0 < n)
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {x : ℝ} (hx : 0 ≤ x) :
    StopFacts d P.k P.g P.sc (chanBK P.L R0 P.g P.sc) (P.w d) n
      (∑ t ∈ range n, (gameLaw (prior d (1 / 2)) μ).real (stopSet P pol x t ∩ (liveSet P pol (t + 1))ᶜ))
      ((gameLaw (prior d (1 / 2)) μ).real (crossSet P pol x n)) (x + 1 / 2 + P.sc * Real.sqrt n)
      (fun t => ∫ s in stopSet P pol x t, Jf P pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in stopSet P pol x t, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in stopSet P pol x t, af P pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in stopSet P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => (gameLaw (prior d (1 / 2)) μ).real (stopSet P pol x t)) where
  round_J := fun t ht => (stop_round I hP μ hpol x ht).1
  round_floor := fun t ht => (stop_round I hP μ hpol x ht).2.1
  round_mass := fun t ht => (stop_round I hP μ hpol x ht).2.2
  live := fun t ht => by
    have := stop_live hP hX hN μ hpol x ht.le
    linarith
  payment := stop_payment hP μ hpol x
  count := stop_count I hP μ hpol x hX
  regret := stop_regret I hP μ hn hpol hx

end Facts

end AdversarialBco.Lower.Stop
