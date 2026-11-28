/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.StopTop

@[expose] public section

/-!
# Proposition Q-STOP: Proposition STOP stopped on the bowl sum

On the Gaussian game of Conj1Lower/Top.lean at the strategy `ruleS d P` with `P` good for a
body inside `B(0, R0)`. The analysis stops at the first round where the posterior is dead or the bowl sum
`Q_u = Σ_{i < u} q_i` exceeds the level `x`, with `q_i = q_{Π_i}(x_i)` the bowl of the posterior before round `i` read
at the play of round `i`; the game itself runs its `n` rounds.

* `bowlS`: the bowl of a law at a play; `bowlS_ge` (B1), `bowlS_le` (B2), `dentS_le_bowlS` (B3),
  `measurable_bowlS_dens`.
* `stopHQ`, `stopSetQ`: the stopped live event `S_t` of round `t` on histories and on the sample (Step 1): decreasing
  (`stopSetQ_succ`), inside the live event, unchanged by later rounds (`stopHQ_push`), measurable.
* (F1) `stop_round_gen`: the three inequalities of `round_bound` integrated over any measurable subset of the live
  event; (F2) `stop_paymentQ`, (F3) `stop_countQ` through `stopped_ledger` and `stopped_count` (Step 2).
* (Q1) `stopQ_regret`: `Σ_t E[D̄_t; S_t] ≤ x + ρ`, `ρ = L (R0 + 1/2) + g` (Step 3).
* (Q2) `crossQ_or_dead`: for `x < n g` every sample crosses the level or leaves through a dead posterior (Step 5).
* (Q3) `regG_ge_of_crossQ`: on a crossing, `Reg^G_n ≥ Q_{t+1}/2 - B''` (Step 6).
* `mean_gapQ`: `E B'' ≤ 2 ρ R_L/k + (3k²/(2d²)) (x + ρ)` through Lemma POST (Step 7).
* `stopQ_prob`: Proposition Q-STOP (Step 8).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.LowerDeltaQ

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Top AdversarialBco.Lower.Stop

/-! ## The bowl at the play -/

section Bowl

variable {d : ℕ} {R0 : ℝ}

/-- The bowl of the law `π` read at the play `x`: `q_π(x) = κ φ(|x - m|_M)` in the frame of `π`. -/
noncomputable def bowlS (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : ℝ :=
  bowl (frameS P d π) (meanV π) P.kappa P.k (rOne d) x

/-- (B1): the bowl is at least `κ k = g`. -/
theorem bowlS_ge {P : SParams} (hP : Good P d R0) (π : Measure (E d)) (x : E d) : P.g ≤ bowlS P d π x := by
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have h := bowl_ge (frameS P d π) (meanV π) P.kappa P.k (rOne d) hP.kappa_pos.le (rOne_nonneg d) x
  have hκk : P.kappa * P.k = P.g := by unfold SParams.kappa; field_simp
  unfold bowlS
  linarith

/-- (B3): the dent is at most the bowl. -/
theorem dentS_le_bowlS {P : SParams} (hP : Good P d R0) (π : Measure (E d)) (x θ : E d) :
    dentS P d π x θ ≤ bowlS P d π x :=
  dent_le_bowl _ _ _ _ _ hP.kappa_pos.le (by linarith [hP.k_ge]) (rOne_nonneg d) θ x

/-- (B2): with the mean of `π` in `B(0, 1/2)` and the play in `B(0, R0)`, the bowl is at most `L (R0 + 1/2) + g`
(the first step of `dent_frame_le` and the identity of `dentS_le`). -/
theorem bowlS_le {P : SParams} (hP : Good P d R0) {π : Measure (E d)} (hS : (covM π).IsHermitian)
    (hm : meanV π ∈ Metric.closedBall (0 : E d) (1 / 2)) {x : E d} (hx : x ∈ Metric.closedBall (0 : E d) R0) :
    bowlS P d π x ≤ P.L * (R0 + 1 / 2) + P.g := by
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hκ := hP.kappa_pos
  have hr := rOne_pos hP
  have h : bowl (frameA (P.w d) (covM π)) (meanV π) P.kappa P.k (rOne d) x ≤
      P.kappa * (rOne d * (‖x - meanV π‖ / P.w d) + P.k) := by
    unfold bowl
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    refine (huber_le_lin _ _ _ (norm_nonneg _)).trans ?_
    have := norm_frameA_apply_le (P.w d) (covM π) hS hP.w_pos (x - meanV π)
    nlinarith
  have hxm : ‖x - meanV π‖ ≤ R0 + 1 / 2 := by
    have h1 := mem_closedBall_zero_iff.1 hx
    have h2 := mem_closedBall_zero_iff.1 hm
    linarith [norm_sub_le x (meanV π)]
  have hκk : P.kappa * P.k = P.g := by unfold SParams.kappa; field_simp
  have key : P.kappa * (rOne d * (‖x - meanV π‖ / P.w d) + P.k) = P.L * ‖x - meanV π‖ + P.g := by
    rw [mul_add, hκk, P.w_eq d]
    field_simp [hκ.ne', hr.ne', hP.L_pos.ne']
  unfold bowlS frameS
  rw [key] at h
  nlinarith [hP.L_pos]

/-- The bowl of the frame of `π0.withDensity (g h)` is measurable in `(h, x)`. -/
theorem measurable_bowlS_dens {H : Type} [MeasurableSpace H] (P : SParams) (hw : P.w d ≠ 0) (π0 : Measure (E d))
    [SFinite π0] {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun p : H × E d => bowlS P d (π0.withDensity (g p.1)) p.2) := by
  have hhub : Measurable (huber (rOne d) P.k) := by
    unfold huber
    exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  have hcov : Measurable fun p : H × E d => covM (π0.withDensity (g p.1)) :=
    (measurable_covM_dens π0 hg hfin).comp measurable_fst
  have hmean : Measurable fun p : H × E d => meanV (π0.withDensity (g p.1)) :=
    (measurable_meanV_dens π0 hg hfin).comp measurable_fst
  have hv : Measurable fun p : H × E d => (covM (π0.withDensity (g p.1)), p.2 - meanV (π0.withDensity (g p.1))) :=
    hcov.prodMk (measurable_snd.sub hmean)
  have hA := (measurable_frameA_apply (d := d) hw).comp hv
  have h2 := (hhub.comp hA.norm).const_mul P.kappa
  exact h2

end Bowl

/-! ## The stopped live events on the bowl sum -/

section Events

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The bowl sum over the rounds before `u`, read on a history: `Σ_{i < u} q_{Π_i}(x_i)`. -/
noncomputable def cumQH (P : SParams) (h : Hist d (Option Cell)) (u : ℕ) : ℝ :=
  ∑ i ∈ range u, bowlS P d (post (prior d (1 / 2)) (ruleS d P) P.sc i h) (h.1 i)

/-- The stopped live event of round `t`, on histories: the posterior before round `t` is live and the bowl sum stayed
at most `x` up to round `t`. -/
def stopHQ (P : SParams) (x : ℝ) (t : ℕ) : Set (Hist d (Option Cell)) :=
  {h | liveS P d (post (prior d (1 / 2)) (ruleS d P) P.sc t h) ∧ ∀ u ≤ t, cumQH P h u ≤ x}

/-- The stopped live event `S_t` of round `t`, on the sample. -/
def stopSetQ (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) : Set (Sample d Ω) :=
  hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' stopHQ P x t

/-- The bowl of round `t` at the play: `q_t = q_{Π_t}(x_t)`. -/
noncomputable def qT (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  bowlS P d (postT P pol t s) (playT P pol t s)

/-- The bowl sum `Q_u = Σ_{i < u} q_i` on the sample. -/
noncomputable def cumQ (P : SParams) (pol : Learner Ω d) (u : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ i ∈ range u, qT P pol i s

omit [MeasurableSpace Ω] in
/-- The posterior of round `i ≤ t` read on the history after `t` rounds is the posterior of round `i`. -/
theorem post_hist_le {α : Type} [MeasurableSpace α] [Inhabited α] (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ)
    (pol : Learner Ω d) {i t : ℕ} (hit : i ≤ t) (s : Sample d Ω) :
    post π0 R sc i (hist π0 R sc pol t s) = post π0 R sc i (hist π0 R sc pol i s) := by
  let _ : MeasurableSpace Ω := ⊤
  unfold post
  rw [dens_congr π0 R sc i (hist π0 R sc pol t s) (hist π0 R sc pol i s) fun j hj => by
    obtain ⟨a1, a2, a3⟩ := hist_stable π0 R sc pol s (lt_of_lt_of_le hj hit)
    obtain ⟨b1, b2, b3⟩ := hist_stable π0 R sc pol s hj
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩]

omit [MeasurableSpace Ω] in
theorem cumQH_hist (P : SParams) (pol : Learner Ω d) {u t : ℕ} (hu : u ≤ t) (s : Sample d Ω) :
    cumQH P (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) u = cumQ P pol u s := by
  let _ : MeasurableSpace Ω := ⊤
  unfold cumQH cumQ qT
  refine sum_congr rfl fun i hi => ?_
  have hit : i < t := lt_of_lt_of_le (mem_range.1 hi) hu
  rw [post_hist_le _ _ _ pol hit.le s, (hist_stable _ _ _ pol s hit).1, (hist_succ_self _ _ _ pol s i).1]

omit [MeasurableSpace Ω] in
theorem mem_stopSetQ {P : SParams} {pol : Learner Ω d} {x : ℝ} {t : ℕ} {s : Sample d Ω} :
    s ∈ stopSetQ P pol x t ↔ s ∈ liveSet P pol t ∧ ∀ u ≤ t, cumQ P pol u s ≤ x := by
  unfold stopSetQ stopHQ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => (cumQH_hist P pol hu s) ▸ h2 u hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => (cumQH_hist P pol hu s).symm ▸ h2 u hu⟩

omit [MeasurableSpace Ω] in
theorem stopSetQ_sub_live (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) :
    stopSetQ P pol x t ⊆ liveSet P pol t := fun _ hs => (mem_stopSetQ.1 hs).1

omit [MeasurableSpace Ω] in
theorem stopSetQ_succ {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (x : ℝ) (t : ℕ) :
    stopSetQ P pol x (t + 1) ⊆ stopSetQ P pol x t := fun s hs => by
  obtain ⟨h1, h2⟩ := mem_stopSetQ.1 hs
  exact mem_stopSetQ.2 ⟨live_of_live_succ hP pol t h1, fun u hu => h2 u (by omega)⟩

omit [MeasurableSpace Ω] in
theorem stopSetQ_anti {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (x : ℝ) {t u : ℕ} (htu : t ≤ u) :
    stopSetQ P pol x u ⊆ stopSetQ P pol x t := by
  induction u, htu using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih => exact (stopSetQ_succ hP pol x u).trans ih

theorem measurable_bowl_post {P : SParams} (hP : Good P d R0) (t : ℕ) :
    Measurable (fun p : Hist d (Option Cell) × E d =>
      bowlS P d (post (prior d (1 / 2)) (ruleS d P) P.sc t p.1) p.2) := by
  have hR := ruleS_meas_prior hP
  have hD := dens_props (prior d (1 / 2)) (ruleS d P) hR P.sc t
  exact measurable_bowlS_dens P hP.w_pos.ne' (prior d (1 / 2)) hD.1 hD.2.1

theorem measurable_cumQH {P : SParams} (hP : Good P d R0) (u : ℕ) :
    Measurable (fun h : Hist d (Option Cell) => cumQH P h u) := by
  unfold cumQH
  refine Finset.measurable_sum _ fun i _ => ?_
  have hpl : Measurable (fun h : Hist d (Option Cell) => (h, h.1 i)) :=
    measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have h1 : Measurable ((fun p : Hist d (Option Cell) × E d =>
      bowlS P d (post (prior d (1 / 2)) (ruleS d P) P.sc i p.1) p.2) ∘ fun h : Hist d (Option Cell) => (h, h.1 i)) :=
    (measurable_bowl_post hP i).comp hpl
  exact h1

theorem measurableSet_stopHQ {P : SParams} (hP : Good P d R0) (x : ℝ) (t : ℕ) :
    MeasurableSet (stopHQ (d := d) P x t) := by
  have hR := ruleS_meas_prior hP
  have hD := dens_props (prior d (1 / 2)) (ruleS d P) hR P.sc t
  have hL := measurableSet_liveS_dens P (prior d (1 / 2)) hD.1 hD.2.1
  have hC : MeasurableSet {h : Hist d (Option Cell) | ∀ u ≤ t, cumQH P h u ≤ x} := by
    have : {h : Hist d (Option Cell) | ∀ u ≤ t, cumQH P h u ≤ x} =
        ⋂ u ∈ Finset.range (t + 1), {h | cumQH P h u ≤ x} := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      exact ⟨fun h u hu => h u (by omega), fun h u hu => h u (by omega)⟩
    rw [this]
    exact Finset.measurableSet_biInter _ fun u _ => measurableSet_le (measurable_cumQH hP u) measurable_const
  exact hL.inter hC

theorem measurableSet_stopSetQ {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t ≤ n) :
    MeasurableSet (stopSetQ P pol x t) :=
  (measurable_hist (prior d (1 / 2)) (ruleS d P) (ruleS_meas_prior hP) P.sc (fun t ht => (hpol t ht).1) ht)
    (measurableSet_stopHQ hP x t)

/-- The stopped live event of round `t` does not read the rounds from `t` on. -/
theorem stopHQ_push (P : SParams) (x : ℝ) {t u : ℕ} (htu : t ≤ u) (h : Hist d (Option Cell)) (y : E d) (o : ℝ)
    (a : Option Cell) : Hist.push h u y o a ∈ stopHQ P x t ↔ h ∈ stopHQ P x t := by
  have hpost : ∀ i ≤ t, post (prior d (1 / 2)) (ruleS d P) P.sc i (Hist.push h u y o a) =
      post (prior d (1 / 2)) (ruleS d P) P.sc i h := fun i hi => by
    unfold post
    rw [dens_congr (prior d (1 / 2)) (ruleS d P) P.sc i (Hist.push h u y o a) h fun j hj => by
      simp [Hist.push, Function.update_of_ne (by omega : j ≠ u)]]
  have hcum : ∀ v ≤ t, cumQH P (Hist.push h u y o a) v = cumQH P h v := fun v hv => by
    unfold cumQH
    refine sum_congr rfl fun i hi => ?_
    have hiv := mem_range.1 hi
    have : i ≠ u := by omega
    rw [hpost i (by omega)]
    simp [Hist.push, Function.update_of_ne this]
  unfold stopHQ
  simp only [Set.mem_ofPred_eq, hpost t le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv => (hcum v hv) ▸ h2 v hv⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv => (hcum v hv).symm ▸ h2 v hv⟩

omit [MeasurableSpace Ω] in
theorem hist_succ_mem_stopHQ (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) :
    hist (prior d (1 / 2)) (ruleS d P) P.sc pol (t + 1) s ∈ stopHQ P x t ↔ s ∈ stopSetQ P pol x t := by
  rw [hist_succ]
  exact stopHQ_push P x le_rfl _ _ _ _

omit [MeasurableSpace Ω] in
theorem stopHQ_anti {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω)
    (hs : hist (prior d (1 / 2)) (ruleS d P) P.sc pol (t + 1) s ∈ stopHQ P x (t + 1)) :
    hist (prior d (1 / 2)) (ruleS d P) P.sc pol (t + 1) s ∈ stopHQ P x t :=
  (hist_succ_mem_stopHQ P pol x t s).2 (stopSetQ_succ hP pol x t hs)

omit [MeasurableSpace Ω] in
/-- The stopped event at round `0` is the whole sample space when `N* > 0`. -/
theorem mem_stopSetQ_zero {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (pol : Learner Ω d) {x : ℝ} (hx : 0 ≤ x) (s : Sample d Ω) :
    s ∈ stopSetQ P pol x 0 :=
  mem_stopSetQ.2 ⟨live_zero hP hX hN pol s, fun u hu => by
    rw [Nat.le_zero.1 hu]
    simpa [cumQ] using hx⟩

end Events

/-! ## (F1), (F2), (F3) on the stopped events -/

section Ledger

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- (F1) on any measurable subset of the live event of round `t`: the three inequalities of `round_bound` in mean
(the proof reads only the measurability of the set and its inclusion in the live event). -/
theorem stop_round_gen (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {S : Set (Sample d Ω)}
    (hSm : MeasurableSet S) {t : ℕ} (ht : t < n) (hS : S ⊆ liveSet P pol t) :
    ∫ s in S, Jf P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
        (4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k *
          ∫ s in S, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ +
        P.g / (P.sc ^ 2 * priceR d P.k) * ∫ s in S, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ∧
      P.g / 2 * (999 / 1000 * (gameLaw (prior d (1 / 2)) μ).real S -
          ∫ s in S, af P pol t s ∂gameLaw (prior d (1 / 2)) μ) ≤
        ∫ s in S, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ∧
      ∫ s in S, af P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
        4 / P.k * ∫ s in S, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ := by
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
  exact round_integral (gameLaw (prior d (1 / 2)) μ) S hSm
    ((4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k) (P.g / (P.sc ^ 2 * priceR d P.k)) P.g P.k
    (Jf P pol t) (Pf P pol t) (af P pol t) (Df P pol t) hJi hPi hai hDi fun s hs => by
      obtain ⟨pr, H, Iann, Irest, Drest, preg, hRF⟩ := roundFacts_at I hP hpol ht (hS hs)
      exact round_bound hk hP.dim hP.g_pos.le hB hRF

/-- The payment on the preimage of a measurable set of histories is the weighted payment of the generic ledger. -/
theorem setIntegral_Pf_hist {P : SParams} (hP : Good P d R0) (μ : Measure Ω) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {S : Set (Hist d (Option Cell))} (hSm : MeasurableSet S)
    {t : ℕ} (ht : t ≤ n) :
    ∫ s in hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, payW (prior d (1 / 2)) (ruleS d P) P.sc (P.w d) S t (play pol t s.2.2)
        (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) ∂gameLaw (prior d (1 / 2)) μ := by
  have hm := (measurable_hist (prior d (1 / 2)) (ruleS d P) (ruleS_meas_prior hP) P.sc
    (fun t ht => (hpol t ht).1) ht) hSm
  rw [← integral_indicator hm]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  unfold payW
  beta_reduce
  by_cases hs : s ∈ hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s ∈ S
      from hs)]
    rfl
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s ∉ S
      from hs)]

/-- (F2) on the bowl-stopped events: `Σ_t E[P'_t; S_t] ≤ R_L`. -/
theorem stop_paymentQ {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) :
    ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Pf P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤ ledgerR d (P.w d) := by
  have hR := ruleS_meas_prior hP
  have hL := stopped_ledger hP.d_pos (show (0 : ℝ) < 1 / 2 by norm_num) μ (ruleS d P) hR hP.sc_pos.ne'
    (fun t ht => (hpol t ht).1) hP.w_pos.ne' (stopHQ P x) (measurableSet_stopHQ hP x)
    (fun t => stopHQ_push P x le_rfl) (stopHQ_anti hP pol x)
  unfold stopSetQ
  rw [sum_congr rfl fun t ht => setIntegral_Pf_hist hP μ hpol (measurableSet_stopHQ hP x t) (mem_range.1 ht).le]
  have hb : ledgerBudget d (1 / 2) (P.w d) = ledgerR d (P.w d) := rfl
  rw [← hb]
  exact hL

/-- The information on the preimage of a measurable set of histories is the weighted information of the generic
count. -/
theorem setIntegral_Jf_hist {P : SParams} (hP : Good P d R0) (μ : Measure Ω) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {S : Set (Hist d (Option Cell))} (hSm : MeasurableSet S)
    {t : ℕ} (ht : t ≤ n) :
    ∫ s in hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S, Jf P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, infoW (prior d (1 / 2)) (ruleS d P) P.sc S t (play pol t s.2.2)
        (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) ∂gameLaw (prior d (1 / 2)) μ := by
  have hm := (measurable_hist (prior d (1 / 2)) (ruleS d P) (ruleS_meas_prior hP) P.sc
    (fun t ht => (hpol t ht).1) ht) hSm
  rw [← integral_indicator hm]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  beta_reduce
  rw [infoW_hist]
  rfl

omit [MeasurableSpace Ω] in
theorem stopQ_dead_eq (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) :
    {s : Sample d Ω | hist (prior d (1 / 2)) (ruleS d P) P.sc pol (t + 1) s ∈ stopHQ P x t ∧
      dLive (P.w d) (covM (post (prior d (1 / 2)) (ruleS d P) P.sc (t + 1)
        (hist (prior d (1 / 2)) (ruleS d P) P.sc pol (t + 1) s))) < d / 2} =
      stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ := by
  ext s
  rw [Set.mem_ofPred_eq, hist_succ_mem_stopHQ, Set.mem_inter_iff, Set.mem_compl_iff]
  exact and_congr Iff.rfl (not_le (α := ℝ)).symm

/-- (F3) on the bowl-stopped events: `N* p' ≤ Σ_t E[J_t; S_t]`, `p' = Σ_{t < n} P(S_t, round t + 1 dead)`. -/
theorem stop_countQ (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ)
    (hX : Real.exp 1 / 2 ≤ xCount d (P.w d)) :
    nStar d (P.w d) * ∑ t ∈ range n,
        (gameLaw (prior d (1 / 2)) μ).real (stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ) ≤
      ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Jf P pol t s ∂gameLaw (prior d (1 / 2)) μ := by
  have hR := ruleS_meas_prior hP
  have hS₀ : ∀ t < n, ∀ h θ ω, |(ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t h)
      (play pol t ω h) θ| ≤ 1 := fun t ht h θ ω => abs_sig_post_le I hP t h ((hpol t ht).2 _ _ _) θ
  have hc := stopped_count (by have := hP.d_pos; omega) μ (ruleS d P) hR hP.sc_pos.ne' (fun t ht => (hpol t ht).1)
    hS₀ hP.w_pos hX (stopHQ P x) (measurableSet_stopHQ hP x) (fun t => stopHQ_push P x le_rfl)
    (stopHQ_anti hP pol x) (fun t s hs => hs.1)
  simp only [stopQ_dead_eq] at hc
  unfold stopSetQ
  rw [sum_congr rfl fun t ht => setIntegral_Jf_hist hP μ hpol (measurableSet_stopHQ hP x t) (mem_range.1 ht).le]
  exact hc

end Ledger

/-! ## (Q1): the overshoot and the stopped regret -/

section Pure

/-- The overshoot, on the reals: for a decreasing family of stopped rounds on which the partial sums of `q` stay at most
`x`, with `0 ≤ q t ≤ ρ`, the stopped sum is at most `x + ρ`. -/
theorem stopped_bowl_le {St : ℕ → Prop} [DecidablePred St] (hanti : ∀ t, St (t + 1) → St t) {q : ℕ → ℝ} {x ρ : ℝ}
    (hxρ : 0 ≤ x + ρ) (hSx : ∀ t, St t → ∑ i ∈ range t, q i ≤ x) (n : ℕ) (hq : ∀ t < n, q t ≤ ρ) :
    ∑ t ∈ range n, (if St t then q t else 0) ≤ x + ρ := by
  have hA : ∀ m, St m → ∑ t ∈ range m, (if St t then q t else 0) = ∑ t ∈ range m, q t := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [sum_range_succ, sum_range_succ, ih (hanti m hm), ite_eq_left (hanti m hm)]
  have hB : ∀ m ≤ n, ∑ t ∈ range m, (if St t then q t else 0) ≤ x + ρ := by
    intro m
    induction m with
    | zero => intro _; simpa using hxρ
    | succ m ih =>
      intro hm
      rw [sum_range_succ]
      by_cases hs : St m
      · rw [ite_eq_left hs, hA m hs]
        have h1 := hSx m hs
        have h2 := hq m (by omega)
        linarith
      · rw [ite_eq_right hs, add_zero]
        exact ih (by omega)
  exact hB n le_rfl

end Pure

section Regret

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- (B1) at the play: `q_t ≥ g`. -/
theorem qT_ge {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : P.g ≤ qT P pol t s :=
  bowlS_ge hP _ _

/-- (B2) at the play: `q_t ≤ ρ = L (R0 + 1/2) + g` for plays in `B(0, R0)`. -/
theorem qT_le (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {t : ℕ} (ht : t < n) (s : Sample d Ω) :
    qT P pol t s ≤ P.L * (R0 + 1 / 2) + P.g :=
  bowlS_le hP (post_cov I hP P.sc t _).1 (post_mean hP P.sc t _) ((hpol t ht).2 _ _ _)

omit [MeasurableSpace Ω] in
theorem dentT_nonneg {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) :
    0 ≤ dentT P pol t s :=
  sig_sub_b_nonneg hP _ _ _

omit [MeasurableSpace Ω] in
/-- On a live round the dent at the tip is the dent of the rule. -/
theorem dentT_live {P : SParams} {pol : Learner Ω d} {t : ℕ} {s : Sample d Ω} (hs : s ∈ liveSet P pol t) :
    dentT P pol t s = dentS P d (postT P pol t s) (playT P pol t s) s.1 := by
  have hl : liveS P d (postT P pol t s) := hs
  unfold dentT
  rw [ruleS_sig_sub, ite_eq_left hl]

omit [MeasurableSpace Ω] in
/-- (B3) at the play: on a live round, `D_t ≤ q_t`. -/
theorem dentT_le_qT {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {t : ℕ} {s : Sample d Ω}
    (hs : s ∈ liveSet P pol t) : dentT P pol t s ≤ qT P pol t s := by
  rw [dentT_live hs]
  exact dentS_le_bowlS hP _ _ _

theorem measurable_qT {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {t : ℕ} (ht : t < n) : Measurable (qT P pol t) := by
  have hR := ruleS_meas_prior hP
  have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc (fun t ht => (hpol t ht).1) ht.le
  have hpl := (measurable_play (α := Option Cell) (hpol t ht).1).comp ((measurable_snd.comp measurable_snd).prodMk hh)
  have h1 := (measurable_bowl_post hP t).comp (hh.prodMk hpl)
  exact h1

theorem measurable_dentT {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {t : ℕ} (ht : t < n) : Measurable (dentT P pol t) := by
  have hR := ruleS_meas_prior hP
  have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc (fun t ht => (hpol t ht).1) ht.le
  have hpl := (measurable_play (α := Option Cell) (hpol t ht).1).comp ((measurable_snd.comp measurable_snd).prodMk hh)
  have h1 := ((measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).2.comp
    (hh.prodMk (hpl.prodMk measurable_fst))).sub_const P.b
  exact h1

/-- (Q1), pathwise: `Σ_{t < n} q_t 1_{S_t} ≤ x + ρ`. -/
theorem stopQ_bowl_point (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) (s : Sample d Ω) :
    ∑ t ∈ range n, (stopSetQ P pol x t).indicator (qT P pol t) s ≤ x + (P.L * (R0 + 1 / 2) + P.g) := by
  classical
  have hρ : 0 ≤ P.L * (R0 + 1 / 2) + P.g := by
    have := qT_ge hP pol 0 s
    linarith [qT_le I hP hpol hn s, hP.g_pos]
  have h := stopped_bowl_le (St := fun t => s ∈ stopSetQ P pol x t) (fun t h => stopSetQ_succ hP pol x t h)
    (q := fun t => qT P pol t s) (by linarith) (fun t h => (mem_stopSetQ.1 h).2 t le_rfl) n
    (fun t ht => qT_le I hP hpol ht s)
  have e1 : ∀ t ∈ range n, (stopSetQ P pol x t).indicator (qT P pol t) s =
      if s ∈ stopSetQ P pol x t then qT P pol t s else 0 := fun t _ => by
    by_cases hs : s ∈ stopSetQ P pol x t
    · rw [Set.indicator_of_mem hs, ite_eq_left hs]
    · rw [Set.indicator_of_notMem hs, ite_eq_right hs]
  rw [sum_congr rfl e1]
  exact h

/-- The dent of round `t` on the preimage of a set of histories, as a function of the tip, the history and the
seed. -/
noncomputable def dentF (P : SParams) (pol : Learner Ω d) (S : Set (Hist d (Option Cell))) (t : ℕ) :
    E d × Hist d (Option Cell) × Ω → ℝ :=
  {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S}.indicator fun p =>
    (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t p.2.1) (play pol t p.2.2 p.2.1) p.1 - P.b

theorem measurable_dentF {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {S : Set (Hist d (Option Cell))}
    (hSm : MeasurableSet S) {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (dentF P pol S t) := by
  have hR := ruleS_meas_prior hP
  have hq : Measurable (fun p : E d × Hist d (Option Cell) × Ω => (p.2.1, play pol t p.2.2 p.2.1, p.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (((measurable_play (α := Option Cell) hpol).comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))).prodMk measurable_fst)
  have h1 := ((measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).2.comp hq).sub_const P.b
  exact h1.indicator (hSm.preimage (measurable_fst.comp measurable_snd))

theorem abs_dentF_le (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (S : Set (Hist d (Option Cell))) {t : ℕ} (ht : t < n)
    (p : E d × Hist d (Option Cell) × Ω) : |dentF P pol S t p| ≤ 1 / 2 := by
  unfold dentF
  by_cases hp : p ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S}
  · rw [Set.indicator_of_mem hp]
    have hx : play pol t p.2.2 p.2.1 ∈ Metric.closedBall (0 : E d) R0 := (hpol t ht).2 _ _ _
    obtain ⟨h0, h1⟩ := sig_post_bounds I hP t p.2.1 hx p.1
    have := hP.rng
    rw [abs_le]
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hp, abs_zero]
    norm_num

omit [MeasurableSpace Ω] in
theorem dentF_sample (P : SParams) (pol : Learner Ω d) (S : Set (Hist d (Option Cell))) (t : ℕ) (s : Sample d Ω) :
    dentF P pol S t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) =
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S).indicator (dentT P pol t) s := by
  unfold dentF
  by_cases hs : s ∈ hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S} from hs)]
    rfl
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∉ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S} from hs)]

omit [MeasurableSpace Ω] in
theorem integral_dentF_post (P : SParams) (pol : Learner Ω d) (S : Set (Hist d (Option Cell))) (t : ℕ)
    (s : Sample d Ω) :
    ∫ θ, dentF P pol S t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
        ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) =
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S).indicator (Df P pol t) s := by
  unfold dentF
  by_cases hs : s ∈ hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S
  · have hin : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∈
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S} := fun θ => hs
    simp only [Set.indicator_of_mem (hin _), Set.indicator_of_mem hs]
    rfl
  · have hout : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∉
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ S} := fun θ => hs
    simp only [Set.indicator_of_notMem (hout _), Set.indicator_of_notMem hs, integral_zero]

/-- By Lemma POST, the posterior mean of the dent on the preimage of a measurable set of histories is the dent at the
tip there. -/
theorem setIntegral_Df_hist (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {S : Set (Hist d (Option Cell))}
    (hSm : MeasurableSet S) {t : ℕ} (ht : t < n) :
    ∫ s in hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S).indicator (dentT P pol t) s
        ∂gameLaw (prior d (1 / 2)) μ := by
  have hR := ruleS_meas_prior hP
  have hpd := post_disintegrates_integral (prior d (1 / 2)) μ (ruleS d P) hR hP.sc_pos.ne'
    (fun t ht => (hpol t ht).1) ht.le (measurable_dentF hP hSm (hpol t ht).1) (abs_dentF_le I hP hpol S ht)
  have hm := (measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc (fun t ht => (hpol t ht).1) ht.le) hSm
  rw [← integral_indicator hm]
  calc ∫ s, (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t ⁻¹' S).indicator (Df P pol t) s
        ∂gameLaw (prior d (1 / 2)) μ
      = ∫ s, ∫ θ, dentF P pol S t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
          ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
          ∂gameLaw (prior d (1 / 2)) μ :=
        integral_congr_ae (ae_of_all _ fun s => (integral_dentF_post P pol S t s).symm)
    _ = ∫ s, dentF P pol S t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
          ∂gameLaw (prior d (1 / 2)) μ := hpd.symm
    _ = _ := integral_congr_ae (ae_of_all _ fun s => dentF_sample P pol S t s)

/-- A bounded measurable function times the indicator of a measurable set is integrable for the game law. -/
theorem integrable_indicator_bdd (μ : Measure Ω) [IsProbabilityMeasure μ] {π0 : Measure (E d)}
    [IsProbabilityMeasure π0] {f : Sample d Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ s, |f s| ≤ C)
    {A : Set (Sample d Ω)} (hA : MeasurableSet A) : Integrable (A.indicator f) (gameLaw π0 μ) := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  exact ((integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hC s)).indicator hA

/-- (Q1), (F5'): `Σ_t E[D̄_t; S_t] ≤ x + ρ`, with no noise term. -/
theorem stopQ_regret (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ ≤
      x + (P.L * (R0 + 1 / 2) + P.g) := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hint : ∀ t ∈ range n, Integrable ((stopSetQ P pol x t).indicator (dentT P pol t))
      (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    integrable_indicator_bdd μ (measurable_dentT hP hpol (mem_range.1 ht)) (C := 1 / 2) (fun s => by
      have h0 := dentT_nonneg hP pol t s
      have hx' : playT P pol t s ∈ Metric.closedBall (0 : E d) R0 := (hpol t (mem_range.1 ht)).2 _ _ _
      have h1 := (sig_post_bounds I hP t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) hx' s.1).2
      have := hP.rng
      rw [abs_of_nonneg h0]
      unfold dentT
      linarith) (measurableSet_stopSetQ hP hpol x (mem_range.1 ht).le)
  have e : ∀ t ∈ range n, ∫ s in stopSetQ P pol x t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, (stopSetQ P pol x t).indicator (dentT P pol t) s ∂gameLaw (prior d (1 / 2)) μ := fun t ht =>
    setIntegral_Df_hist I hP μ hpol (measurableSet_stopHQ hP x t) (mem_range.1 ht)
  rw [sum_congr rfl e, ← integral_finsetSum _ hint]
  have hpt : ∀ s, ∑ t ∈ range n, (stopSetQ P pol x t).indicator (dentT P pol t) s ≤
      x + (P.L * (R0 + 1 / 2) + P.g) := fun s => by
    refine le_trans (sum_le_sum (g := fun t => (stopSetQ P pol x t).indicator (qT P pol t) s) fun t _ => ?_)
      (stopQ_bowl_point I hP hpol hn hx s)
    by_cases hs : s ∈ stopSetQ P pol x t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      exact dentT_le_qT hP (stopSetQ_sub_live P pol x t hs)
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
  calc ∫ s, ∑ t ∈ range n, (stopSetQ P pol x t).indicator (dentT P pol t) s ∂gameLaw (prior d (1 / 2)) μ
      ≤ ∫ _s, x + (P.L * (R0 + 1 / 2) + P.g) ∂gameLaw (prior d (1 / 2)) μ :=
        integral_mono (integrable_finsetSum _ hint) (integrable_const _) hpt
    _ = x + (P.L * (R0 + 1 / 2) + P.g) := by rw [integral_const, probReal_univ, one_smul]

end Regret

/-! ## (Q2): every sample crosses the level or leaves through a dead posterior -/

section Cross

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The crossing exits: `E_× = ∪_{t < n} (S_t ∩ {Q_{t+1} > x})`. -/
def crossQ (P : SParams) (pol : Learner Ω d) (x : ℝ) (n : ℕ) : Set (Sample d Ω) :=
  ⋃ t ∈ range n, (stopSetQ P pol x t ∩ {s | x < cumQ P pol (t + 1) s})

omit [MeasurableSpace Ω] in
/-- (Q2): for `0 ≤ x < n g` every sample lies in a crossing exit or in a dead exit `S_t ∩ live_{t+1}ᶜ`, `t < n`: the
event "still in the stopped game at the end" is empty, since every round adds a bowl value `q ≥ g`. -/
theorem crossQ_or_dead {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (pol : Learner Ω d) {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hxn : x < n * P.g)
    (s : Sample d Ω) :
    s ∈ crossQ P pol x n ∪ ⋃ t ∈ range n, (stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ) := by
  by_contra hs
  rw [Set.mem_union, not_or] at hs
  obtain ⟨hc, hd⟩ := hs
  have hall : ∀ t ≤ n, s ∈ stopSetQ P pol x t := by
    intro t
    induction t with
    | zero => exact fun _ => mem_stopSetQ_zero hP hX hN pol hx s
    | succ t ih =>
      intro ht
      have hst := ih (by omega)
      have hlive : s ∈ liveSet P pol (t + 1) := by
        by_contra hl
        exact hd (Set.mem_biUnion (mem_range.2 (by omega)) ⟨hst, hl⟩)
      have hcum : cumQ P pol (t + 1) s ≤ x := by
        by_contra hcx
        exact hc (Set.mem_biUnion (mem_range.2 (by omega)) ⟨hst, not_le.1 hcx⟩)
      refine mem_stopSetQ.2 ⟨hlive, fun u hu => ?_⟩
      rcases Nat.lt_or_ge u (t + 1) with h | h
      · exact (mem_stopSetQ.1 hst).2 u (by omega)
      · rw [show u = t + 1 by omega]
        exact hcum
  have hn := (mem_stopSetQ.1 (hall n le_rfl)).2 n le_rfl
  have hge : (n : ℝ) * P.g ≤ cumQ P pol n s := by
    unfold cumQ
    calc (n : ℝ) * P.g = ∑ _i ∈ range n, P.g := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range n, qT P pol i s := sum_le_sum fun i _ => qT_ge hP pol i s
  linarith

/-- (Q2) in probability: `P(E_×) ≥ 1 - p'`, `p' = Σ_{t < n} P(S_t ∩ live_{t+1}ᶜ)`. -/
theorem prob_crossQ_ge {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d} {x : ℝ} (hx : 0 ≤ x)
    {n : ℕ} (hxn : x < n * P.g) :
    1 - ∑ t ∈ range n, (gameLaw (prior d (1 / 2)) μ).real (stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ) ≤
      (gameLaw (prior d (1 / 2)) μ).real (crossQ P pol x n) := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hsub : (Set.univ : Set (Sample d Ω)) ⊆
      crossQ P pol x n ∪ ⋃ t ∈ range n, (stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ) :=
    fun s _ => crossQ_or_dead hP hX hN pol hx hxn s
  have h := (measureReal_mono (μ := gameLaw (prior d (1 / 2)) μ) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le _ _)))
  rw [probReal_univ] at h
  linarith

end Cross

/-! ## (Q3) and the mean of `B''` -/

section Gap

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The gap of round `t`: `(q_t/2 - D_t)_+`. -/
noncomputable def gapT (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  max (qT P pol t s / 2 - dentT P pol t s) 0

/-- `B'' = Σ_{t < n} 1_{S_t} (q_t/2 - D_t)_+`. -/
noncomputable def gapSum (P : SParams) (pol : Learner Ω d) (x : ℝ) (n : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ range n, (stopSetQ P pol x t).indicator (gapT P pol t) s

omit [MeasurableSpace Ω] in
theorem gapSum_nonneg (P : SParams) (pol : Learner Ω d) (x : ℝ) (n : ℕ) (s : Sample d Ω) :
    0 ≤ gapSum P pol x n s :=
  sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) s

omit [MeasurableSpace Ω] in
/-- (Q3), pathwise: on `S_t ∩ {Q_{t+1} > x}`, `t < n`, `Reg^G_n ≥ Q_{t+1}/2 - B''`. -/
theorem regG_ge_of_crossQ {P : SParams} (hP : Good P d R0) (pol : Learner Ω d) {x : ℝ} {n t : ℕ} (ht : t < n)
    {s : Sample d Ω} (hs : s ∈ stopSetQ P pol x t) :
    cumQ P pol (t + 1) s / 2 - gapSum P pol x n s ≤ regG (prior d (1 / 2)) P pol n s := by
  rw [regG_eq]
  have hsub : range (t + 1) ⊆ range n := range_subset_range.2 (by omega)
  have h1 : ∑ i ∈ range (t + 1), dentT P pol i s ≤ ∑ i ∈ range n, dentT P pol i s :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => dentT_nonneg hP pol i s
  have h2 : ∑ i ∈ range (t + 1), (stopSetQ P pol x i).indicator (gapT P pol i) s ≤ gapSum P pol x n s :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Set.indicator_nonneg (fun s _ => le_max_right _ _) s
  have h3 : ∀ i ∈ range (t + 1), qT P pol i s / 2 - (stopSetQ P pol x i).indicator (gapT P pol i) s ≤
      dentT P pol i s := fun i hi => by
    have hsi : s ∈ stopSetQ P pol x i := stopSetQ_anti hP pol x (Nat.lt_succ_iff.1 (mem_range.1 hi)) hs
    rw [Set.indicator_of_mem hsi]
    unfold gapT
    linarith [le_max_left (qT P pol i s / 2 - dentT P pol i s) 0]
  have h4 := sum_le_sum h3
  rw [sum_sub_distrib, ← sum_div] at h4
  unfold cumQ
  linarith

/-- The gap of round `t` on the stopped event, as a function of the tip, the history and the seed. -/
noncomputable def gapF (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) : E d × Hist d (Option Cell) × Ω → ℝ :=
  {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t}.indicator fun p =>
    max (bowlS P d (post (prior d (1 / 2)) (ruleS d P) P.sc t p.2.1) (play pol t p.2.2 p.2.1) / 2 -
      ((ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t p.2.1) (play pol t p.2.2 p.2.1) p.1 - P.b)) 0

theorem measurable_gapF {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} (x : ℝ) {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (gapF P pol x t) := by
  have hR := ruleS_meas_prior hP
  have hpl : Measurable (fun p : E d × Hist d (Option Cell) × Ω => play pol t p.2.2 p.2.1) :=
    (measurable_play (α := Option Cell) hpol).comp
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hq : Measurable (fun p : E d × Hist d (Option Cell) × Ω => (p.2.1, play pol t p.2.2 p.2.1, p.1)) :=
    (measurable_fst.comp measurable_snd).prodMk (hpl.prodMk measurable_fst)
  have hsig := ((measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).2.comp hq).sub_const P.b
  have hb : Measurable ((fun p : Hist d (Option Cell) × E d =>
      bowlS P d (post (prior d (1 / 2)) (ruleS d P) P.sc t p.1) p.2) ∘
        fun p : E d × Hist d (Option Cell) × Ω => (p.2.1, play pol t p.2.2 p.2.1)) :=
    (measurable_bowl_post hP t).comp ((measurable_fst.comp measurable_snd).prodMk hpl)
  have h1 := ((hb.div_const 2).sub hsig).max (measurable_const (a := (0 : ℝ)))
  exact h1.indicator ((measurableSet_stopHQ hP x t).preimage (measurable_fst.comp measurable_snd))

theorem gapF_bounds (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n)
    (p : E d × Hist d (Option Cell) × Ω) : 0 ≤ gapF P pol x t p ∧ gapF P pol x t p ≤ 1 / 4 := by
  unfold gapF
  by_cases hp : p ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t}
  · rw [Set.indicator_of_mem hp]
    have hx : play pol t p.2.2 p.2.1 ∈ Metric.closedBall (0 : E d) R0 := (hpol t ht).2 _ _ _
    obtain ⟨h0, -⟩ := sig_post_bounds I hP t p.2.1 hx p.1
    have hq := bowlS_le hP (post_cov I hP P.sc t p.2.1).1 (post_mean hP P.sc t p.2.1) hx
    have := hP.rng
    refine ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  · rw [Set.indicator_of_notMem hp]
    norm_num

omit [MeasurableSpace Ω] in
theorem gapF_sample (P : SParams) (pol : Learner Ω d) (x : ℝ) (t : ℕ) (s : Sample d Ω) :
    gapF P pol x t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) =
      (stopSetQ P pol x t).indicator (gapT P pol t) s := by
  unfold gapF
  by_cases hs : s ∈ stopSetQ P pol x t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∈ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t} from hs)]
    rfl
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2) ∉ {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t} from hs)]

/-- Step 7, one round, inside the posterior integral: on the stopped event the posterior mean of the gap is at most
`(q_t/2) (a_t + 3k²/d²)` (the dent is at least `q/2` on the regular cell, Lemma REGULAR (iii), and the posterior mass
outside the regular cell is at most `a_t + 3k²/d²`, Lemma REST (i)). -/
theorem integral_gapF_post_le (I : Inputs) {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) (s : Sample d Ω) :
    ∫ θ, gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
        ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) ≤
      (stopSetQ P pol x t).indicator (fun s => qT P pol t s / 2 * (af P pol t s + 3 * P.k ^ 2 / (d : ℝ) ^ 2)) s := by
  by_cases hs : s ∈ stopSetQ P pol x t
  · rw [Set.indicator_of_mem hs]
    have hl : s ∈ liveSet P pol t := stopSetQ_sub_live P pol x t hs
    set π := postT P pol t s with hπ
    set xp := playT P pol t s with hxp
    have hc : RoundCtx P R0 d π xp :=
      ⟨post_isProb hP P.sc t _, post_ball _ P.sc t _, post_cov I hP P.sc t _, hl, (hpol t ht).2 _ _ _⟩
    have := hc.prob
    have hk : 0 < P.k := by linarith [hP.k_ge]
    have hDM := hc.dm hP
    set Rg := cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) xp Cell.regular with hRg
    have hRm : MeasurableSet Rg := measurableSet_cellSet _ _ _ _ _ _ _
    set q := qT P pol t s with hq_def
    have hq0 : 0 ≤ q := le_trans hP.g_pos.le (qT_ge hP pol t s)
    -- the integrand
    have hin : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∈
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t} := fun θ => hs
    have hF : ∀ θ, gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) =
        max (q / 2 - dentS P d π xp θ) 0 := fun θ => by
      unfold gapF
      rw [Set.indicator_of_mem (hin θ), ruleS_sig_sub, ite_eq_left (show liveS P d π from hl)]
      rfl
    have hpt : ∀ θ, gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ≤
        Rgᶜ.indicator (fun _ => q / 2) θ := fun θ => by
      rw [hF]
      by_cases hθ : θ ∈ Rg
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hθ)]
        obtain ⟨hT, hR1, hR2⟩ := (cellOf_regular_iff _ _ _ _ _ _ _).1 hθ
        have hh := regular_half (frameS P d π) (meanV π) P.kappa P.k d (dmS P d π) hP.kappa_pos hk hP.dim hDM
          θ xp hT hR1 hR2
        have e1 : bowl (frameS P d π) (meanV π) P.kappa P.k (5 * Real.sqrt d) xp = q := rfl
        have e2 : dent (frameS P d π) (meanV π) P.kappa P.k (5 * Real.sqrt d) θ xp = dentS P d π xp θ := rfl
        rw [e1, e2] at hh
        exact max_le (by linarith) le_rfl
      · rw [Set.indicator_of_mem (Set.mem_compl hθ)]
        have hD0 := dentS_nonneg hP π xp θ
        exact max_le (by linarith) (by linarith)
    have hmeas : Measurable fun θ => gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) :=
      (measurable_gapF hP x (hpol t ht).1).comp (measurable_id.prodMk measurable_const)
    have hint : Integrable (fun θ => gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)) π :=
      (integrable_const (1 / 4 : ℝ)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun θ => by
        obtain ⟨h0, h1⟩ := gapF_bounds I hP hpol x ht (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact h1)
    have h1 := integral_mono hint ((integrable_const (q / 2)).indicator hRm.compl) hpt
    rw [integral_indicator_const _ hRm.compl, smul_eq_mul, probReal_compl_eq_one_sub hRm] at h1
    -- the mass outside the regular cell
    have hreg := cells_reg π (frameS P d π) (meanV π) P.k d (dmS P d π) (by linarith [hP.k_ge]) hP.dim xp
    have haf : af P pol t s = 1 - massRest π (frameS P d π) (meanV π) P.k d (dmS P d π) xp := by
      unfold af massRest restSet
      rw [ans_live hl]
    have hmr : π.real Rg = massReg π (frameS P d π) (meanV π) P.k d (dmS P d π) xp := rfl
    have hfin : 1 - π.real Rg ≤ af P pol t s + 3 * P.k ^ 2 / (d : ℝ) ^ 2 := by linarith
    calc _ ≤ (1 - π.real Rg) * (q / 2) := h1
      _ ≤ (af P pol t s + 3 * P.k ^ 2 / (d : ℝ) ^ 2) * (q / 2) :=
        mul_le_mul_of_nonneg_right hfin (by linarith)
      _ = q / 2 * (af P pol t s + 3 * P.k ^ 2 / (d : ℝ) ^ 2) := by ring
  · rw [Set.indicator_of_notMem hs]
    have hout : ∀ θ : E d, (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∉
        {p : E d × Hist d (Option Cell) × Ω | p.2.1 ∈ stopHQ P x t} := fun θ => hs
    simp only [gapF, Set.indicator_of_notMem (hout _), integral_zero, le_refl]

end Gap

/-! ## The mean of `B''` and Proposition Q-STOP -/

section QStop

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

theorem measurable_gapT {P : SParams} (hP : Good P d R0) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) {t : ℕ} (ht : t < n) : Measurable (gapT P pol t) :=
  (((measurable_qT hP hpol ht).div_const 2).sub (measurable_dentT hP hpol ht)).max measurable_const

theorem integrable_gap_round (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) :
    Integrable ((stopSetQ P pol x t).indicator (gapT P pol t)) (gameLaw (prior d (1 / 2)) μ) :=
  integrable_indicator_bdd μ (measurable_gapT hP hpol ht) (C := 1 / 4) (fun s => by
    have h0 : 0 ≤ gapT P pol t s := le_max_right _ _
    have hq := qT_le I hP hpol ht s
    have hD := dentT_nonneg hP pol t s
    have := hP.rng
    rw [abs_of_nonneg h0]
    exact max_le (by linarith) (by norm_num)) (measurableSet_stopSetQ hP hpol x ht.le)

/-- Step 7, one round: `E[1_{S_t} (q_t/2 - D_t)_+] ≤ (ρ/2) E[a_t; S_t] + (3k²/(2d²)) E[1_{S_t} q_t]`, through Lemma
POST. -/
theorem mean_gap_round (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (x : ℝ) {t : ℕ} (ht : t < n) :
    ∫ s, (stopSetQ P pol x t).indicator (gapT P pol t) s ∂gameLaw (prior d (1 / 2)) μ ≤
      (P.L * (R0 + 1 / 2) + P.g) / 2 * ∫ s in stopSetQ P pol x t, af P pol t s ∂gameLaw (prior d (1 / 2)) μ +
        3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) *
          ∫ s, (stopSetQ P pol x t).indicator (qT P pol t) s ∂gameLaw (prior d (1 / 2)) μ := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hR := ruleS_meas_prior hP
  set G := gameLaw (prior d (1 / 2)) μ with hG_def
  set S := stopSetQ P pol x t with hS_def
  have hSm : MeasurableSet S := measurableSet_stopSetQ hP hpol x ht.le
  have hpd := post_disintegrates_integral (prior d (1 / 2)) μ (ruleS d P) hR hP.sc_pos.ne'
    (fun t ht => (hpol t ht).1) ht.le (measurable_gapF hP x (hpol t ht).1) (C := 1 / 4) (fun p => by
      obtain ⟨h0, h1⟩ := gapF_bounds I hP hpol x ht p
      rw [abs_of_nonneg h0]
      exact h1)
  have e1 : ∫ s, S.indicator (gapT P pol t) s ∂G =
      ∫ s, gapF P pol x t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∂G :=
    integral_congr_ae (ae_of_all _ fun s => (gapF_sample P pol x t s).symm)
  have hρ := hP.rng
  have k0 : 0 ≤ 3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) := by positivity
  -- the bound inside, as a function of the sample
  set B : Sample d Ω → ℝ := fun s => S.indicator (fun s => (P.L * (R0 + 1 / 2) + P.g) / 2 * af P pol t s +
    3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * qT P pol t s) s with hB_def
  have hBi : Integrable B G := by
    have h1 : Integrable (fun s => (P.L * (R0 + 1 / 2) + P.g) / 2 * af P pol t s +
        3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * qT P pol t s) G := by
      refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
      · exact (integrable_const (1 : ℝ)).mono' (measurable_af hP hpol ht).aestronglyMeasurable
          (ae_of_all _ fun s => by
            obtain ⟨h0, h1⟩ := af_mem hP pol t s
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
            exact h1)
      · exact (integrable_const (1 / 2 : ℝ)).mono' (measurable_qT hP hpol ht).aestronglyMeasurable
          (ae_of_all _ fun s => by
            have h0 := le_trans hP.g_pos.le (qT_ge hP pol t s)
            rw [Real.norm_eq_abs, abs_of_nonneg h0]
            linarith [qT_le I hP hpol ht s])
    exact h1.indicator hSm
  have hpt : ∀ s, ∫ θ, gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
      ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) ≤ B s := by
    intro s
    refine (integral_gapF_post_le I hP hpol x ht s).trans ?_
    simp only [hB_def]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      have h0 := af_mem hP pol t s
      have hq0 := le_trans hP.g_pos.le (qT_ge hP pol t s)
      have hq := qT_le I hP hpol ht s
      have hk2 : 0 ≤ 3 * P.k ^ 2 / (d : ℝ) ^ 2 := by positivity
      have e : 3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * qT P pol t s = qT P pol t s / 2 * (3 * P.k ^ 2 / (d : ℝ) ^ 2) := by
        field_simp
      rw [e, mul_add]
      have : qT P pol t s / 2 * af P pol t s ≤ (P.L * (R0 + 1 / 2) + P.g) / 2 * af P pol t s :=
        mul_le_mul_of_nonneg_right (by linarith) h0.1
      linarith
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
  have hnn : 0 ≤ᵐ[G] fun s => ∫ θ, gapF P pol x t (θ, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2)
      ∂post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) :=
    ae_of_all _ fun s => integral_nonneg fun θ => (gapF_bounds I hP hpol x ht _).1
  rw [e1, hpd]
  refine (integral_mono_of_nonneg hnn hBi (ae_of_all _ hpt)).trans (le_of_eq ?_)
  have hai : Integrable (af P pol t) G :=
    (integrable_const (1 : ℝ)).mono' (measurable_af hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := af_mem hP pol t s
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact h1)
  have hqi : Integrable (qT P pol t) G :=
    (integrable_const (1 / 2 : ℝ)).mono' (measurable_qT hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        have h0 := le_trans hP.g_pos.le (qT_ge hP pol t s)
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        linarith [qT_le I hP hpol ht s])
  have eB : B = fun s => (P.L * (R0 + 1 / 2) + P.g) / 2 * S.indicator (af P pol t) s +
      3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * S.indicator (qT P pol t) s := by
    funext s
    simp only [hB_def]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
      ring
  rw [eB, integral_add ((hai.indicator hSm).const_mul _) ((hqi.indicator hSm).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hSm]

/-- Step 7: `E B'' ≤ 2 ρ R_L/k + (3k²/(2d²)) (x + ρ)`. -/
theorem mean_gapQ (I : Inputs) {P : SParams} (hP : Good P d R0) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (hn : 0 < n) (hR0 : 0 ≤ R0)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ s, gapSum P pol x n s ∂gameLaw (prior d (1 / 2)) μ ≤
      2 * (P.L * (R0 + 1 / 2) + P.g) * ledgerR d (P.w d) / P.k +
        3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * (x + (P.L * (R0 + 1 / 2) + P.g)) := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  set G := gameLaw (prior d (1 / 2)) μ with hG_def
  set ρ := P.L * (R0 + 1 / 2) + P.g with hρ_def
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hρ0 : 0 ≤ ρ := by have := hP.L_pos; have := hP.g_pos; positivity
  have hc0 : 0 ≤ 3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) := by positivity
  have hqi : ∀ t ∈ range n, Integrable ((stopSetQ P pol x t).indicator (qT P pol t)) G := fun t ht =>
    integrable_indicator_bdd μ (measurable_qT hP hpol (mem_range.1 ht)) (C := ρ) (fun s => by
      have h0 := le_trans hP.g_pos.le (qT_ge hP pol t s)
      rw [abs_of_nonneg h0]
      exact qT_le I hP hpol (mem_range.1 ht) s) (measurableSet_stopSetQ hP hpol x (mem_range.1 ht).le)
  have hgi : ∀ t ∈ range n, Integrable ((stopSetQ P pol x t).indicator (gapT P pol t)) G := fun t ht =>
    integrable_gap_round I hP μ hpol x (mem_range.1 ht)
  -- the sum of the rounds
  have h1 : ∫ s, gapSum P pol x n s ∂G ≤ ρ / 2 * ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, af P pol t s ∂G +
      3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * ∑ t ∈ range n, ∫ s, (stopSetQ P pol x t).indicator (qT P pol t) s ∂G := by
    unfold gapSum
    rw [integral_finsetSum _ hgi, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun t ht => mean_gap_round I hP μ hpol x (mem_range.1 ht)
  -- the mass announced, through (F1) and (F2)
  have h2 : ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, af P pol t s ∂G ≤ 4 / P.k * ledgerR d (P.w d) := by
    calc ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, af P pol t s ∂G
        ≤ ∑ t ∈ range n, 4 / P.k * ∫ s in stopSetQ P pol x t, Pf P pol t s ∂G :=
          sum_le_sum fun t ht => (stop_round_gen I hP μ hpol (measurableSet_stopSetQ hP hpol x (mem_range.1 ht).le)
            (mem_range.1 ht) (stopSetQ_sub_live P pol x t)).2.2
      _ = 4 / P.k * ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Pf P pol t s ∂G := by rw [mul_sum]
      _ ≤ 4 / P.k * ledgerR d (P.w d) :=
          mul_le_mul_of_nonneg_left (stop_paymentQ hP μ hpol x) (by positivity)
  -- the bowl sum, through (Q1)
  have h3 : ∑ t ∈ range n, ∫ s, (stopSetQ P pol x t).indicator (qT P pol t) s ∂G ≤ x + ρ := by
    rw [← integral_finsetSum _ hqi]
    calc ∫ s, ∑ t ∈ range n, (stopSetQ P pol x t).indicator (qT P pol t) s ∂G
        ≤ ∫ _s, x + ρ ∂G := integral_mono (integrable_finsetSum _ hqi) (integrable_const _)
          fun s => stopQ_bowl_point I hP hpol hn hx s
      _ = x + ρ := by rw [integral_const, probReal_univ, one_smul]
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ρ / 2 by linarith)
  have h5 := mul_le_mul_of_nonneg_left h3 hc0
  have e : ρ / 2 * (4 / P.k * ledgerR d (P.w d)) = 2 * ρ * ledgerR d (P.w d) / P.k := by
    field_simp
    ring
  linarith


/-- **Proposition Q-STOP** at a `Good` strategy, for plays in `B(0, R0)`, `R0 ≥ 0`, a level
`0 < x < n g` and `β > 0`: with `ρ = L (R0 + 1/2) + g`, `c₁ = (4 (3 ln d + 1) + 8 B)/k`, `c₂ = g/(σ² P_R)`,
`P(Reg^G_n > (1 - β) x/2) ≥ 1 - (c₁ R_L + c₂ (x + ρ))/N* - (4 ρ R_L/k + (3k²/d²) (x + ρ))/(β x)`. -/
theorem stopQ_prob (I : Inputs) {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (hn : 0 < n) (hR0 : 0 ≤ R0) {x β : ℝ} (hx : 0 < x)
    (hxn : x < n * P.g) (hβ : 0 < β) :
    1 - ((4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k * ledgerR d (P.w d) +
        P.g / (P.sc ^ 2 * priceR d P.k) * (x + (P.L * (R0 + 1 / 2) + P.g))) / nStar d (P.w d) -
      (4 * (P.L * (R0 + 1 / 2) + P.g) * ledgerR d (P.w d) / P.k +
        3 * P.k ^ 2 / (d : ℝ) ^ 2 * (x + (P.L * (R0 + 1 / 2) + P.g))) / (β * x) ≤
      (gameLaw (prior d (1 / 2)) μ).real {s | (1 - β) * x / 2 < regG (prior d (1 / 2)) P pol n s} := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  set G := gameLaw (prior d (1 / 2)) μ with hG_def
  set ρ := P.L * (R0 + 1 / 2) + P.g with hρ_def
  set c1 := (4 * (3 * Real.log d + 1) + 8 * chanBK P.L R0 P.g P.sc) / P.k with hc1_def
  set c2 := P.g / (P.sc ^ 2 * priceR d P.k) with hc2_def
  set RL := ledgerR d (P.w d) with hRL_def
  set N := nStar d (P.w d) with hN_def
  set p' := ∑ t ∈ range n, G.real (stopSetQ P pol x t ∩ (liveSet P pol (t + 1))ᶜ) with hp'_def
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hd1 : (1 : ℝ) ≤ d := by have := hP.dim; linarith [hP.k_ge]
  have hc1 : 0 ≤ c1 := by
    have : 0 ≤ Real.log d := Real.log_nonneg hd1
    have : 0 ≤ chanBK P.L R0 P.g P.sc := by unfold chanBK; positivity
    rw [hc1_def]
    positivity
  have hc2 : 0 ≤ c2 := by
    have := priceR_nonneg (d : ℝ) P.k
    have := hP.g_pos
    rw [hc2_def]
    positivity
  -- the dead exits: `N* p' ≤ c₁ R_L + c₂ (x + ρ)`
  have hJ : ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Jf P pol t s ∂G ≤
      c1 * ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Pf P pol t s ∂G +
        c2 * ∑ t ∈ range n, ∫ s in stopSetQ P pol x t, Df P pol t s ∂G := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun t ht => (stop_round_gen I hP μ hpol (measurableSet_stopSetQ hP hpol x (mem_range.1 ht).le)
      (mem_range.1 ht) (stopSetQ_sub_live P pol x t)).1
  have hP' := mul_le_mul_of_nonneg_left (stop_paymentQ hP μ hpol x) hc1
  have hD' := mul_le_mul_of_nonneg_left (stopQ_regret I hP μ hpol hn hx.le) hc2
  have hcount := stop_countQ I hP μ hpol x hX
  rw [← hG_def] at hP' hD' hcount
  rw [← hN_def] at hcount
  rw [← hRL_def] at hP'
  rw [← hρ_def] at hD'
  have hp : p' ≤ (c1 * RL + c2 * (x + ρ)) / N := by
    rw [le_div_iff₀ hN]
    linarith
  -- the crossing
  have hcross := prob_crossQ_ge hP hX hN μ (pol := pol) hx.le hxn
  -- Markov on `B''`
  have hgi : Integrable (gapSum P pol x n) G := integrable_finsetSum _ fun t ht =>
    integrable_gap_round I hP μ hpol x (mem_range.1 ht)
  have hmean := mean_gapQ I hP μ hpol hn hR0 hx.le
  rw [← hG_def, ← hRL_def, ← hρ_def] at hmean
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (gapSum_nonneg P pol x n)) hgi (β * x / 2)
  have hbx : 0 < β * x / 2 := by positivity
  have hB : G.real {s | β * x / 2 ≤ gapSum P pol x n s} ≤
      (4 * ρ * RL / P.k + 3 * P.k ^ 2 / (d : ℝ) ^ 2 * (x + ρ)) / (β * x) := by
    rw [le_div_iff₀ (by positivity)]
    have e : (4 * ρ * RL / P.k + 3 * P.k ^ 2 / (d : ℝ) ^ 2 * (x + ρ)) =
        2 * (2 * ρ * RL / P.k + 3 * P.k ^ 2 / (2 * (d : ℝ) ^ 2) * (x + ρ)) := by
      field_simp
      ring
    rw [e]
    linarith
  -- the crossing without a large `B''` is a large regret
  have hsub : crossQ P pol x n ⊆ {s | (1 - β) * x / 2 < regG (prior d (1 / 2)) P pol n s} ∪
      {s | β * x / 2 ≤ gapSum P pol x n s} := by
    intro s hs
    obtain ⟨t, ht, hst, hxs⟩ := Set.mem_iUnion₂.1 hs
    by_cases hB' : β * x / 2 ≤ gapSum P pol x n s
    · exact Or.inr hB'
    · left
      have h := regG_ge_of_crossQ hP pol (mem_range.1 ht) hst
      have hx' : x < cumQ P pol (t + 1) s := hxs
      show (1 - β) * x / 2 < regG (prior d (1 / 2)) P pol n s
      push Not at hB'
      linarith
  have hU := (measureReal_mono (μ := G) hsub).trans (measureReal_union_le _ _)
  linarith

end QStop

end AdversarialBco.LowerDeltaQ
