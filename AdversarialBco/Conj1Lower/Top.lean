/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Info
public import AdversarialBco.Conj1Lower.CellsRound
public import AdversarialBco.Conj1Lower.Geom
public import AdversarialBco.Conj1Lower.Sanity

@[expose] public section

/-!
# The game and the top of the lower bound

Theorem 1.4 from Proposition 9.11 (Section 9 of the paper), composed from the other modules:
`TheoremConj1Lower` (StatementConj1Lower.lean) from the hypotheses `Inputs`, the statements used from Moments.lean,
Ledger.lean and Info.lean, each a copy of its statement there; Main.lean discharges every field of `Inputs` with those
theorems (`lowerTopInputs`). The other modules (Bayes, BayesRound, Cells, CellMeas, CellsRound, Dent, Frame, Geom,
Balance, RuleS, Sanity) are used directly.

* Parameters (`pB`): the strategy `S'(g, k, L, σ)` with `σ = L = sigB n`, `k = kRipe d`, `g = gRipe d n σ` and the
  offset `b = 1/4`; the prior `prior d (1/2)`; the clamp `clampZ ℓ` at `ℓ = (6 ln n)^{1/2}`, where `σ ℓ = 1/8`.
* Lemma 9.4 (`stratOf_mem`): the deterministic strategy of a tip and a clamped noise sequence is in `StratsLip`.
* The regret identity (`regretAd_stratOf`): against it, the regret is the sum of the dents at the tip (`regG`).
* The coupling (S6) (`coupling`): clamping the noise costs at most `1/n` in mean.
* The game (`gameFacts`): `GameFacts` (Balance.lean) at the parameters of Proposition 9.11, from the per-round facts
  (`roundFacts_at`) integrated over the live event of each round, the payment and the count.
* The derandomisation (`exists_good_point`) and the composition (`theoremConj1Lower_of_inputs`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace AdversarialBco.Lower.Top

open RealRAM Bayes

/-! ## The hypotheses: the statements used from Moments.lean, Ledger.lean and Info.lean -/

/-- The statements this module uses from Moments.lean, Ledger.lean and Info.lean, each the statement of the theorem
of the same name there, specialised to answers in `Option Cell` and tips in `E d` where that one is
universe-polymorphic. Main.lean discharges every field with those theorems (`lowerTopInputs`). -/
structure Inputs : Prop where
  /-- Moments.lean. -/
  secMom_posSemidef : ∀ {d : ℕ} (π : Measure (E d)) [IsFiniteMeasure π],
    Integrable (fun θ => ‖θ‖ ^ 2) π → ∀ m : E d, (secMom π m).PosSemidef
  /-- Ledger.lean. -/
  cellPay_empty : ∀ {d : ℕ} (π : Measure (E d)) (w : ℝ), cellPay w π ∅ = 0
  /-- Ledger.lean, (L3). -/
  pay_tail : ∀ {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π], Integrable (fun θ => ‖θ‖ ^ 2) π →
    ∀ {w k : ℝ}, 0 < w → 6 ≤ k → ∀ (x : E d) {c : Set (E d)}, MeasurableSet c →
      (∀ θ ∈ c, Real.sqrt (2 * k) < readT (frameA w (covM π)) (meanV π) θ x) →
      π.real c * k / 4 ≤ cellPay w π c ∧
        (∫ θ in c, readT (frameA w (covM π)) (meanV π) θ x ^ 2 ∂π) / 8 ≤ cellPay w π c
  /-- Ledger.lean, (L4). -/
  pay_inner : ∀ {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π], Integrable (fun θ => ‖θ‖ ^ 2) π →
    ∀ {w : ℝ}, 0 < w → 0 < d → (d : ℝ) / 2 ≤ dLive w (covM π) → ∀ {c : Set (E d)}, MeasurableSet c →
      (∀ θ ∈ c, ‖frameA w (covM π) (θ - meanV π)‖ ^ 2 < DM w (covM π) / 64) →
      π.real c * d / 62 ≤ cellPay w π c
  /-- Ledger.lean, (L5). -/
  pay_outer : ∀ {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π], Integrable (fun θ => ‖θ‖ ^ 2) π →
    ∀ {w : ℝ}, 0 < w → 0 < d → ∀ {c : Set (E d)}, MeasurableSet c →
      (∀ θ ∈ c, 4 * (d : ℝ) < ‖frameA w (covM π) (θ - meanV π)‖ ^ 2) → π.real c * d / 62 ≤ cellPay w π c
  /-- Ledger.lean, (L6). -/
  ledger_game : ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω], 0 < d → ∀ {r₀ : ℝ}, 0 < r₀ → ∀ (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Rule d (Option Cell)), R.Meas (prior d r₀) → ∀ {sc : ℝ}, sc ≠ 0 →
    ∀ {pol : Learner Ω d} {n : ℕ},
    (∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) → ∀ {w : ℝ},
    w ≠ 0 →
    (∀ t < n, Integrable (fun s => payAnn w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
        (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (play pol t s.2.2 (hist (prior d r₀) R sc pol t s)))) (gameLaw (prior d r₀) μ)) ∧
      ∑ t ∈ Finset.range n, ∫ s, payAnn w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
            (play pol t s.2.2 (hist (prior d r₀) R sc pol t s))) ∂gameLaw (prior d r₀) μ ≤
        ledgerBudget d r₀ w
  /-- Info.lean, Lemma 9.6 with the channel bound (S1). -/
  infoJ_chain : ∀ {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π] {c : E d → Option Cell}, Measurable c →
    ∀ {s : E d → ℝ}, Measurable s → ∀ {S₀ : ℝ}, (∀ θ, |s θ| ≤ S₀) → ∀ {sc : ℝ}, sc ≠ 0 →
    ∀ (ĉ : Option Cell → ℝ),
    infoJ π c s sc ≤ ansEntropy π c + ∑ a, (∫ θ in c ⁻¹' {a}, (s θ - ĉ a) ^ 2 ∂π) / (2 * sc ^ 2)
  /-- Info.lean. -/
  infoJ_const : ∀ {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π] (a₀ : Option Cell) (b : ℝ) {sc : ℝ},
    sc ≠ 0 → infoJ π (fun _ => a₀) (fun _ => b) sc = 0
  /-- Info.lean. -/
  integrable_infoRound : ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (π0 : Measure (E d))
    [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Rule d (Option Cell)), R.Meas π0 →
    ∀ {sc : ℝ}, sc ≠ 0 → ∀ {pol : Learner Ω d} {n : ℕ},
    (∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) → ∀ {S₀ : ℝ},
    (∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) → ∀ {t : ℕ}, t < n →
    Integrable (infoRound π0 R sc pol t) (gameLaw π0 μ)
  /-- Info.lean, Lemma 9.6 and Lemma 9.9 (b) over the game. -/
  count_game : ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω], 1 ≤ d → ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)), R.Meas (prior d (1 / 2)) → ∀ {sc : ℝ}, sc ≠ 0 → ∀ {pol : Learner Ω d} {n : ℕ},
    (∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) → ∀ {S₀ : ℝ},
    (∀ t < n, ∀ h θ ω, |R.sig (post (prior d (1 / 2)) R sc t h) (play pol t ω h) θ| ≤ S₀) → ∀ {w : ℝ},
    0 < w → Real.exp 1 / 2 ≤ xCount d w →
    nStar d w * (gameLaw (prior d (1 / 2)) μ).real
        {s | dLive w (covM (post (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s))) < d / 2} ≤
      ∑ t ∈ Finset.range n, ∫ s, infoRound (prior d (1 / 2)) R sc pol t s ∂gameLaw (prior d (1 / 2)) μ

/-! ## Parameters -/

/-- The parameters of Proposition 9.11: `g = gRipe d n σ`, `k = kRipe d`, `L = σ = sigB n`, `b = 1/4`. -/
noncomputable def pB (d n : ℕ) : SParams := ⟨gRipe d n (sigB n), kRipe d, sigB n, sigB n, 1 / 4⟩

/-- The clamp level `ℓ = (6 ln n)^{1/2}`. -/
noncomputable def ellB (n : ℕ) : ℝ := Real.sqrt (6 * Real.log n)

/-- The noise sequence clamped to `[-ℓ, ℓ]` (route (S6)). -/
noncomputable def clampZ (ℓ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ := fun i => max (-ℓ) (min ℓ (z i))

/-- What the one-round lemmas read of the parameters. -/
structure Good (P : SParams) (d : ℕ) : Prop where
  g_pos : 0 < P.g
  k_ge : 240 ≤ P.k
  L_pos : 0 < P.L
  sc_pos : 0 < P.sc
  L_le : P.L ≤ 1 / 4
  dim : 2048 * P.k ≤ d
  rng : 3 * P.L / 2 + P.g ≤ 1 / 2
  b_eq : P.b = 1 / 4

theorem good_pB {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) : Good (pB d n) d := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7, -⟩ := ripeB_params hd hn
  exact ⟨h3, h6, h1, h1, h2, h7, h5, rfl⟩

theorem Good.d_pos {P : SParams} {d : ℕ} (hP : Good P d) : 0 < d := by
  have h1 := hP.dim
  have h2 := hP.k_ge
  have : (0 : ℝ) < d := by linarith
  exact_mod_cast this

theorem Good.kappa_pos {P : SParams} {d : ℕ} (hP : Good P d) : 0 < P.kappa :=
  div_pos hP.g_pos (by linarith [hP.k_ge])

theorem Good.w_pos {P : SParams} {d : ℕ} (hP : Good P d) : 0 < P.w d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hP.d_pos
  have hκ := hP.kappa_pos
  unfold SParams.kappa at hκ
  exact div_pos (mul_pos hκ (mul_pos (by norm_num) (Real.sqrt_pos.2 hd))) hP.L_pos

theorem pB_w (d n : ℕ) : (pB d n).w d = wStar d (kRipe d) (sigB n) (gRipe d n (sigB n)) := rfl

theorem sigB_mul_ellB {n : ℕ} (hn : 1 < n) : sigB n * ellB n = 1 / 8 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h : 0 < Real.sqrt (6 * Real.log n) := Real.sqrt_pos.2 (by linarith [Real.log_pos hn'])
  unfold sigB ellB
  field_simp

theorem abs_clampZ_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (z : ℕ → ℝ) (i : ℕ) : |clampZ ℓ z i| ≤ ℓ :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clampZ_of_abs_le {ℓ : ℝ} {z : ℕ → ℝ} {i : ℕ} (h : |z i| ≤ ℓ) : clampZ ℓ z i = z i := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  simp only [clampZ, min_eq_right h2, max_eq_right h1]

theorem measurable_clampZ (ℓ : ℝ) : Measurable (clampZ ℓ) :=
  measurable_pi_iff.2 fun i => measurable_const.max (measurable_const.min (measurable_pi_apply i))

/-! ## The dent of the rule on the unit ball -/

section Dent

variable {d : ℕ}

theorem ruleS_sig (P : SParams) (π : Measure (E d)) (x θ : E d) :
    (ruleS d P).sig π x θ = P.b + if liveS P d π then dentS P d π x θ else 0 := rfl

theorem ruleS_ans (P : SParams) (π : Measure (E d)) (x θ : E d) :
    (ruleS d P).ans π x θ = if liveS P d π then ansS P d π x θ else none := rfl

theorem rOne_nonneg (d : ℕ) : 0 ≤ rOne d := by
  unfold rOne; positivity

theorem rOne_pos {P : SParams} (hP : Good P d) : 0 < rOne d :=
  mul_pos (by norm_num) (Real.sqrt_pos.2 (by exact_mod_cast hP.d_pos))

theorem dentS_nonneg {P : SParams} (hP : Good P d) (π : Measure (E d)) (x θ : E d) : 0 ≤ dentS P d π x θ :=
  dent_frame_nonneg (P.w d) P.kappa P.k (rOne d) (covM π) hP.kappa_pos.le (by linarith [hP.k_ge])
    (rOne_nonneg d) _ θ x

theorem dentS_self {P : SParams} (hP : Good P d) (π : Measure (E d)) (θ : E d) : dentS P d π θ θ = 0 :=
  dent_frame_self (P.w d) P.kappa P.k (rOne d) (covM π) hP.kappa_pos.le (by linarith [hP.k_ge])
    (rOne_nonneg d) _ θ

/-- Lemma 9.4, the range: with the mean of `π` in `B(0, 1/2)` and the play in the unit ball, the dent is at most
`3L/2 + g`. -/
theorem dentS_le {P : SParams} (hP : Good P d) {π : Measure (E d)} (hS : (covM π).IsHermitian)
    (hm : meanV π ∈ Metric.closedBall (0 : E d) (1 / 2)) {x : E d} (hx : x ∈ Metric.closedBall (0 : E d) 1)
    (θ : E d) : dentS P d π x θ ≤ 3 * P.L / 2 + P.g := by
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hκ := hP.kappa_pos
  have hr := rOne_pos hP
  have h := dent_frame_le (P.w d) P.kappa P.k (rOne d) (covM π) hS hP.w_pos hκ.le hk.le hr.le (meanV π) θ x
  have hxm : ‖x - meanV π‖ ≤ 3 / 2 := by
    have h1 := mem_closedBall_zero_iff.1 hx
    have h2 := mem_closedBall_zero_iff.1 hm
    linarith [norm_sub_le x (meanV π)]
  have hκk : P.kappa * P.k = P.g := by unfold SParams.kappa; field_simp
  have key : P.kappa * (rOne d * (‖x - meanV π‖ / P.w d) + P.k) = P.L * ‖x - meanV π‖ + P.g := by
    rw [mul_add, hκk, P.w_eq d]
    field_simp [hκ.ne', hr.ne', hP.L_pos.ne']
  unfold dentS frameS
  rw [key] at h
  nlinarith [hP.L_pos]

/-- Lemma 9.4, the Lipschitz constant `L`. -/
theorem dentS_lipschitz {P : SParams} (hP : Good P d) {π : Measure (E d)} (hS : (covM π).IsHermitian)
    (x y θ : E d) : |dentS P d π x θ - dentS P d π y θ| ≤ P.L * ‖x - y‖ := by
  have hr := rOne_pos hP
  have h := dent_frame_lipschitz (P.w d) P.kappa P.k (rOne d) (covM π) hS hP.w_pos hP.kappa_pos.le
    (by linarith [hP.k_ge]) hr.le (meanV π) θ x y
  have he : P.kappa * rOne d / P.w d = P.L := by
    rw [P.w_eq d]
    field_simp [hP.kappa_pos.ne', hr.ne', hP.L_pos.ne']
  rw [he] at h
  exact h

/-- Lemma 9.4, convexity in the play. -/
theorem dentS_convexOn {P : SParams} (hP : Good P d) (π : Measure (E d)) (θ : E d) :
    ConvexOn ℝ Set.univ (fun x => dentS P d π x θ) :=
  dent_frame_convexOn (P.w d) P.kappa P.k (rOne d) (covM π) hP.kappa_pos.le (by linarith [hP.k_ge])
    (rOne_nonneg d) _ θ

theorem sig_sub_b_nonneg {P : SParams} (hP : Good P d) (π : Measure (E d)) (x θ : E d) :
    0 ≤ (ruleS d P).sig π x θ - P.b := by
  rw [ruleS_sig]
  split_ifs
  · linarith [dentS_nonneg hP π x θ]
  · simp

theorem sig_sub_b_le {P : SParams} (hP : Good P d) {π : Measure (E d)} (hS : (covM π).IsHermitian)
    (hm : meanV π ∈ Metric.closedBall (0 : E d) (1 / 2)) {x : E d} (hx : x ∈ Metric.closedBall (0 : E d) 1)
    (θ : E d) : (ruleS d P).sig π x θ - P.b ≤ 3 * P.L / 2 + P.g := by
  rw [ruleS_sig]
  split_ifs
  · linarith [dentS_le hP hS hm hx θ]
  · linarith [hP.g_pos, hP.L_pos]

theorem sig_self {P : SParams} (hP : Good P d) (π : Measure (E d)) (θ : E d) :
    (ruleS d P).sig π θ θ = P.b := by
  rw [ruleS_sig]
  split_ifs
  · rw [dentS_self hP]; ring
  · ring

end Dent

/-! ## The posterior of the game lives on `B(0, 1/2)` -/

section Post

variable {d : ℕ}

instance prior_half_isProb : IsProbabilityMeasure (prior d (1 / 2)) :=
  isProbabilityMeasure_prior d (by norm_num)

theorem ruleS_meas_prior {P : SParams} (hP : Good P d) :
    (ruleS d P).Meas (prior d (1 / 2)) :=
  ruleS_meas P hP.w_pos.ne' hP.kappa_pos.le (by linarith [hP.k_ge]) _

theorem post_isProb {P : SParams} (hP : Good P d) (sc : ℝ) (t : ℕ) (h : Hist d (Option Cell)) :
    IsProbabilityMeasure (post (prior d (1 / 2)) (ruleS d P) sc t h) :=
  isProbabilityMeasure_post _ _ (ruleS_meas_prior hP) sc t h

theorem post_ball (R : Rule d (Option Cell)) (sc : ℝ) (t : ℕ) (h : Hist d (Option Cell)) :
    ∀ᵐ θ ∂post (prior d (1 / 2)) R sc t h, θ ∈ Metric.closedBall (0 : E d) (1 / 2) :=
  post_ae_mem _ R sc t h (prior_ae_mem d (1 / 2))

theorem post_sq {P : SParams} (hP : Good P d) (sc : ℝ) (t : ℕ) (h : Hist d (Option Cell)) :
    Integrable (fun θ => ‖θ‖ ^ 2) (post (prior d (1 / 2)) (ruleS d P) sc t h) := by
  have := post_isProb hP sc t h
  exact integrable_sq_norm_of_ae_mem _ (post_ball _ sc t h)

theorem post_mean {P : SParams} (hP : Good P d) (sc : ℝ) (t : ℕ) (h : Hist d (Option Cell)) :
    meanV (post (prior d (1 / 2)) (ruleS d P) sc t h) ∈ Metric.closedBall (0 : E d) (1 / 2) := by
  have := post_isProb hP sc t h
  exact meanV_mem_closedBall _ (post_ball _ sc t h)

theorem post_cov (I : Inputs) {P : SParams} (hP : Good P d) (sc : ℝ) (t : ℕ) (h : Hist d (Option Cell)) :
    (covM (post (prior d (1 / 2)) (ruleS d P) sc t h)).PosSemidef := by
  have := post_isProb hP sc t h
  exact I.secMom_posSemidef _ (post_sq hP sc t h) _

/-- The signal of round `t` along the plays of a learner of the class: between `b` and `b + 3L/2 + g`. -/
theorem sig_post_bounds (I : Inputs) {P : SParams} (hP : Good P d) (t : ℕ) (h : Hist d (Option Cell))
    {x : E d} (hx : x ∈ Metric.closedBall (0 : E d) 1) (θ : E d) :
    0 ≤ (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t h) x θ - P.b ∧
      (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t h) x θ - P.b ≤ 3 * P.L / 2 + P.g :=
  ⟨sig_sub_b_nonneg hP _ x θ, sig_sub_b_le hP (post_cov I hP P.sc t h).1 (post_mean hP P.sc t h) hx θ⟩

theorem abs_sig_post_le (I : Inputs) {P : SParams} (hP : Good P d) (t : ℕ) (h : Hist d (Option Cell))
    {x : E d} (hx : x ∈ Metric.closedBall (0 : E d) 1) (θ : E d) :
    |(ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t h) x θ| ≤ 1 := by
  obtain ⟨h1, h2⟩ := sig_post_bounds I hP t h hx θ
  have := hP.rng
  have := hP.b_eq
  rw [abs_le]
  constructor <;> linarith

end Post

/-! ## Lemma 9.4: the strategy of a tip and a bounded noise sequence is in `StratsLip` -/

section Legal

variable {d : ℕ}

theorem stratOf_mem (I : Inputs) {P : SParams} (hP : Good P d) (n : ℕ) (xo : E d) (z : ℕ → ℝ)
    (hz : ∀ i, |P.sc * z i| ≤ 1 / 8) :
    stratOf (prior d (1 / 2)) (ruleS d P) P.sc xo z ∈ StratsLip (Metric.closedBall (0 : E d) 1) n := by
  refine ⟨fun t _ => ⟨fun x o => ⟨?_, fun y hy => ?_⟩, fun y _ => ?_⟩, fun t _ x o o' => ⟨rfl, fun y _ y' _ => ?_⟩⟩
  · unfold stratOf
    simp only [ruleS_sig]
    split_ifs
    · have h := ((dentS_convexOn hP (post (prior d (1 / 2)) (ruleS d P) P.sc t
        (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x)) xo).subset (Set.subset_univ _)
        (convex_closedBall 0 1)).add_const (P.b + P.sc * z t)
      convert h using 1
      funext y
      simp only [Pi.add_apply]
      ring
    · exact convexOn_const _ (convex_closedBall 0 1)
  · obtain ⟨h1, h2⟩ := sig_post_bounds I hP t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x) hy xo
    obtain ⟨h3, h4⟩ := abs_le.1 (hz t)
    have := hP.rng
    have := hP.b_eq
    simp only [stratOf, Set.mem_Icc]
    constructor <;> linarith
  · exact measurable_stratOf (prior d (1 / 2)) (ruleS d P) (ruleS_meas_prior hP) P.sc xo z t y
  · have hS := (post_cov I hP P.sc t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x)).1
    simp only [stratOf, ruleS_sig, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub]
    rw [dist_eq_norm]
    split_ifs
    · have := dentS_lipschitz hP hS y y' xo
      have := hP.L_le
      nlinarith [norm_nonneg (y - y')]
    · simp only [sub_self, abs_zero]; positivity

end Legal

/-! ## The regret identity -/

section Regret

variable {d : ℕ} {Ω : Type}

/-- The regret of the Gaussian game on the sample `s = (x°, Z, ω)`: the sum of the dents at the tip. -/
noncomputable def regG (π0 : Measure (E d)) (P : SParams) (pol : Learner Ω d) (n : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ Finset.range n, ((ruleS d P).sig (post π0 (ruleS d P) P.sc t (hist π0 (ruleS d P) P.sc pol t s))
      (play pol t s.2.2 (hist π0 (ruleS d P) P.sc pol t s)) s.1 - P.b)

theorem plays_stratOf_hist (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (pol : Learner Ω d) (xo : E d)
    (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω) t =
      play pol t ω (hist π0 R sc pol t (xo, z, ω)) := by
  unfold plays play
  rw [transcript_stratOf]

theorem lossAd_stratOf_hist (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (pol : Learner Ω d)
    (xo : E d) (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    lossAd (stratOf π0 R sc xo z) (fun _ => 0) (plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω)) t =
      fun y => R.sig (post π0 R sc t (hist π0 R sc pol t (xo, z, ω))) y xo + sc * z t := by
  rw [Sanity.lossAd_plays, transcript_stratOf]
  funext y
  simp only [stratOf]
  rw [replay_hist]

/-- The regret identity of Lemma 9.4: against `stratOf`, the comparator's infimum over the ball is attained at the
tip, so the regret is the sum of the dents at the tip. -/
theorem regretAd_stratOf {P : SParams} (hP : Good P d) (π0 : Measure (E d)) (pol : Learner Ω d) (n : ℕ)
    {xo : E d} (hxo : xo ∈ Metric.closedBall (0 : E d) 1) (z : ℕ → ℝ) (ω : Ω) :
    regretAd (Metric.closedBall 0 1) (stratOf π0 (ruleS d P) P.sc xo z) (fun t => pol t ω) n =
      regG π0 P pol n (xo, z, ω) := by
  unfold regretAd regretPts
  simp only [lossAd_stratOf_hist, plays_stratOf_hist]
  have hinf : sInf ((fun y => ∑ t ∈ Finset.range n, ((ruleS d P).sig (post π0 (ruleS d P) P.sc t
      (hist π0 (ruleS d P) P.sc pol t (xo, z, ω))) y xo + P.sc * z t)) '' Metric.closedBall 0 1) =
      ∑ t ∈ Finset.range n, (P.b + P.sc * z t) := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨xo, hxo, Finset.sum_congr rfl fun t _ => ?_⟩
      rw [sig_self hP]
    · rintro _ ⟨y, -, rfl⟩
      refine Finset.sum_le_sum fun t _ => ?_
      linarith [sig_sub_b_nonneg hP (post π0 (ruleS d P) P.sc t (hist π0 (ruleS d P) P.sc pol t (xo, z, ω))) y xo]
  rw [hinf, regG, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end Regret

/-! ## The Gaussian regret: bounds, measurability, the coupling (S6) -/

section Coupling

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem regG_nonneg {P : SParams} (hP : Good P d) (π0 : Measure (E d)) (pol : Learner Ω d) (n : ℕ)
    (s : Sample d Ω) : 0 ≤ regG π0 P pol n s := by
  exact Finset.sum_nonneg fun t _ => sig_sub_b_nonneg hP _ _ _

theorem regG_le (I : Inputs) {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) (s : Sample d Ω) :
    regG (prior d (1 / 2)) P pol n s ≤ n / 2 := by
  have hb : ∀ t ∈ Finset.range n, (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)) (play pol t s.2.2 (hist (prior d (1 / 2)) (ruleS d P)
        P.sc pol t s)) s.1 - P.b ≤ 1 / 2 := fun t ht => by
    have hx : play pol t s.2.2 (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) ∈ Metric.closedBall (0 : E d) 1 :=
      (hpol t (Finset.mem_range.1 ht)).2 _ _ _
    linarith [(sig_post_bounds I hP t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) hx s.1).2, hP.rng]
  calc regG (prior d (1 / 2)) P pol n s ≤ ∑ _t ∈ Finset.range n, (1 / 2 : ℝ) := Finset.sum_le_sum hb
    _ = n / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem measurable_regG {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) : Measurable (regG (prior d (1 / 2)) P pol n) := by
  have hR := ruleS_meas_prior hP
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  refine Finset.measurable_sum _ fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc hpol' ht'.le
  exact ((measurable_rule_post _ _ hR P.sc t).2.comp (hh.prodMk
    (((measurable_play (α := Option Cell) (hpol' t ht')).comp ((measurable_snd.comp measurable_snd).prodMk hh)).prodMk
      measurable_fst))).sub measurable_const

omit [MeasurableSpace Ω] in
/-- The regret reads the noise of the rounds before `n` only. -/
theorem regG_congr (π0 : Measure (E d)) (P : SParams) (pol : Learner Ω d) (n : ℕ) (xo : E d) {z z' : ℕ → ℝ}
    (hz : ∀ i < n, z i = z' i) (ω : Ω) : regG π0 P pol n (xo, z, ω) = regG π0 P pol n (xo, z', ω) := by
  let _ : MeasurableSpace Ω := ⊤
  unfold regG
  refine Finset.sum_congr rfl fun t ht => ?_
  have h := hist_congr π0 (ruleS d P) P.sc pol t (xo, z, ω) (xo, z', ω) rfl
    (fun i hi => hz i (lt_trans hi (Finset.mem_range.1 ht))) rfl
  simp only [h]

/-- The Gaussian tail: `P(|Z| > b) ≤ 2 e^{-b²/2}`. -/
theorem gaussian_abs_tail {b : ℝ} (hb : 0 ≤ b) :
    gaussianReal 0 1 {x | b < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-b ^ 2 / 2)) := by
  have hup : (gaussianReal 0 1).real {x | b ≤ x} ≤ Real.exp (-b ^ 2 / 2) := by
    have h := measure_ge_le_exp_mul_mgf (X := fun x : ℝ => x) (μ := gaussianReal 0 1) b hb
      (integrable_exp_mul_gaussianReal b)
    rw [mgf_fun_id_gaussianReal] at h
    refine h.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hlo : (gaussianReal 0 1).real {x | x ≤ -b} ≤ Real.exp (-b ^ 2 / 2) := by
    have h := measure_le_le_exp_mul_mgf (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (-b) (neg_nonpos.2 hb)
      (integrable_exp_mul_gaussianReal (-b))
    rw [mgf_fun_id_gaussianReal] at h
    refine h.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hsub : {x : ℝ | b < |x|} ⊆ {x | b ≤ x} ∪ {x | x ≤ -b} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases le_or_gt 0 x with h | h
    · left
      rw [abs_of_nonneg h] at hx
      exact hx.le
    · right
      rw [abs_of_neg h] at hx
      show x ≤ -b
      linarith
  have he : 0 ≤ Real.exp (-b ^ 2 / 2) := (Real.exp_pos _).le
  calc gaussianReal 0 1 {x | b < |x|} ≤ gaussianReal 0 1 ({x | b ≤ x} ∪ {x | x ≤ -b}) := measure_mono hsub
    _ ≤ gaussianReal 0 1 {x | b ≤ x} + gaussianReal 0 1 {x | x ≤ -b} := measure_union_le _ _
    _ = ENNReal.ofReal ((gaussianReal 0 1).real {x | b ≤ x}) +
        ENNReal.ofReal ((gaussianReal 0 1).real {x | x ≤ -b}) := by
      rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-b ^ 2 / 2)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlo)
    _ = ENNReal.ofReal (2 * Real.exp (-b ^ 2 / 2)) := by
      rw [← ENNReal.ofReal_add he he, two_mul]

/-- Each noise of the game is a standard Gaussian. -/
theorem gameLaw_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    gameLaw π0 μ {s | s.2.1 i ∈ B} = gaussianReal 0 1 B := by
  have h1 : {s : Sample d Ω | s.2.1 i ∈ B} = Set.univ ×ˢ ({z : ℕ → ℝ | z i ∈ B} ×ˢ Set.univ) := by
    ext s
    simp
  rw [h1]
  unfold gameLaw
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, one_mul, mul_one]
  unfold gaussStream
  have h2 := Measure.map_apply (μ := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (measurable_pi_apply i) hB
  rw [Measure.infinitePi_map_eval] at h2
  rw [h2]
  rfl

/-- Some noise of the rounds before `n` is clamped with probability at most `2 n e^{-ℓ²/2}`. -/
theorem gameLaw_bad_le (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (gameLaw π0 μ).real {s | ∃ i < n, ℓ < |s.2.1 i|} ≤ n * (2 * Real.exp (-ℓ ^ 2 / 2)) := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have hB : MeasurableSet {x : ℝ | ℓ < |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hset : {s : Sample d Ω | ∃ i < n, ℓ < |s.2.1 i|} =
      ⋃ i ∈ Finset.range n, {s : Sample d Ω | s.2.1 i ∈ {x : ℝ | ℓ < |x|}} := by
    ext s
    simp
  have hm : ∀ i ∈ Finset.range n, (gameLaw π0 μ) {s : Sample d Ω | s.2.1 i ∈ {x : ℝ | ℓ < |x|}} ≤
      ENNReal.ofReal (2 * Real.exp (-ℓ ^ 2 / 2)) := fun i _ => by
    rw [gameLaw_noise π0 μ i hB]
    exact gaussian_abs_tail hℓ
  have h := (measure_biUnion_finset_le (Finset.range n) (fun i => {s : Sample d Ω | s.2.1 i ∈ {x : ℝ | ℓ < |x|}})).trans
    (Finset.sum_le_sum hm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hset] at h
  have he : 0 ≤ 2 * Real.exp (-ℓ ^ 2 / 2) := by positivity
  rw [measureReal_def]
  calc ((gameLaw π0 μ) {s | ∃ i < n, ℓ < |s.2.1 i|}).toReal
        ≤ ((n : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-ℓ ^ 2 / 2))).toReal := ENNReal.toReal_mono (by finiteness) h
    _ = n * (2 * Real.exp (-ℓ ^ 2 / 2)) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal he]

/-- The coupling (S6): the game with the clamped noise loses at most `1/n` of mean regret. -/
theorem coupling (I : Inputs) {P : SParams} (hP : Good P d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hn : 1 < n) (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) :
    ∫ s, regG (prior d (1 / 2)) P pol n s ∂gameLaw (prior d (1 / 2)) μ - 1 / n ≤
      ∫ s, regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2) ∂gameLaw (prior d (1 / 2)) μ := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm := measurable_regG hP hpol
  have hmc : Measurable fun s : Sample d Ω => (s.1, clampZ (ellB n) s.2.1, s.2.2) :=
    measurable_fst.prodMk (((measurable_clampZ _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have hbd : ∀ s, ‖regG (prior d (1 / 2)) P pol n s‖ ≤ n / 2 := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (regG_nonneg hP _ pol n s)]
    exact regG_le I hP hpol s
  have hi : Integrable (regG (prior d (1 / 2)) P pol n) (gameLaw (prior d (1 / 2)) μ) :=
    (integrable_const ((n : ℝ) / 2)).mono' hm.aestronglyMeasurable (ae_of_all _ hbd)
  have hic : Integrable (fun s => regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2))
      (gameLaw (prior d (1 / 2)) μ) :=
    (integrable_const ((n : ℝ) / 2)).mono' (hm.comp hmc).aestronglyMeasurable (ae_of_all _ fun s => hbd _)
  have hBad : MeasurableSet {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|} := by
    have : {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|} =
        ⋃ i ∈ Finset.range n, {s : Sample d Ω | ellB n < |s.2.1 i|} := by
      ext s
      simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
  have hpt : ∀ s, regG (prior d (1 / 2)) P pol n s - regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)
      ≤ {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|}.indicator (fun _ => (n : ℝ) / 2) s := by
    intro s
    by_cases hs : s ∈ {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|}
    · rw [Set.indicator_of_mem hs]
      linarith [regG_le I hP hpol s, regG_nonneg hP (prior d (1 / 2)) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)]
    · rw [Set.indicator_of_notMem hs]
      have hc : ∀ i < n, s.2.1 i = clampZ (ellB n) s.2.1 i := fun i hi => by
        refine (clampZ_of_abs_le ?_).symm
        by_contra h
        exact hs ⟨i, hi, lt_of_not_ge h⟩
      have := regG_congr (prior d (1 / 2)) P pol n s.1 hc s.2.2
      linarith
  have hbad := gameLaw_bad_le (prior d (1 / 2)) μ n hℓ
  have h3 : Real.exp (3 * Real.log n) = (n : ℝ) ^ 3 := by
    rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
    norm_num
  have hexp : (n : ℝ) / 2 * (n * (2 * Real.exp (-ellB n ^ 2 / 2))) = 1 / n := by
    have hsq : ellB n ^ 2 = 6 * Real.log n :=
      Real.sq_sqrt (by have := Real.log_nonneg hnR.le; linarith)
    rw [hsq, show -(6 * Real.log n) / 2 = -(3 * Real.log n) by ring, Real.exp_neg, h3]
    field_simp
  have hint : ∫ s, regG (prior d (1 / 2)) P pol n s ∂gameLaw (prior d (1 / 2)) μ -
      ∫ s, regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2) ∂gameLaw (prior d (1 / 2)) μ ≤
      (n : ℝ) / 2 * (gameLaw (prior d (1 / 2)) μ).real {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|} := by
    rw [← integral_sub hi hic]
    calc _ ≤ ∫ s, {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|}.indicator (fun _ => (n : ℝ) / 2) s
            ∂gameLaw (prior d (1 / 2)) μ :=
          integral_mono (hi.sub hic) ((integrable_const _).indicator hBad) hpt
      _ = _ := by rw [integral_indicator_const _ hBad, smul_eq_mul, mul_comm]
  have : (n : ℝ) / 2 * (gameLaw (prior d (1 / 2)) μ).real {s : Sample d Ω | ∃ i < n, ellB n < |s.2.1 i|} ≤
      1 / n := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hbad (by positivity)
  linarith

end Coupling

/-! ## The derandomisation -/

section Derand

/-- A function of `(a, ω)` with mean at least `B` over `ν ⊗ μ` has a point `a` off a `ν`-null set with
`∫ G(a, ·) dμ ≥ B`. -/
theorem exists_good_point {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω] (ν : Measure A)
    [IsProbabilityMeasure ν] (μ : Measure Ω) [IsProbabilityMeasure μ] {G : A × Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hC : ∀ p, |G p| ≤ C) {N : Set A} (hN : ν N = 0) :
    ∃ a, a ∉ N ∧ ∫ p, G p ∂ν.prod μ ≤ ∫ ω, G (a, ω) ∂μ := by
  have hi : Integrable G (ν.prod μ) :=
    (integrable_const C).mono' hG.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hC p)
  rw [integral_prod G hi]
  exact exists_notMem_null_integral_le hi.integral_prod_left hN

/-- The law of the game, reassociated: `(x°, Z)` first, then the seed. -/
theorem integral_gameLaw_assoc {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (π0 : Measure (E d)) [SFinite π0]
    (μ : Measure Ω) [SFinite μ] (F : Sample d Ω → ℝ) :
    ∫ s, F s ∂gameLaw π0 μ = ∫ p, F (p.1.1, p.1.2, p.2) ∂(π0.prod gaussStream).prod μ := by
  unfold gameLaw
  exact ((measurePreserving_prodAssoc π0 gaussStream μ).integral_comp' F).symm

end Derand

/-! ## One live round: `RoundFacts` at a law `π` on `B(0, 1/2)` and a play in the unit ball -/

section OneRound

theorem preimage_answer_some {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) (c : Cell) [Decidable (ripe π A m k dd DMv x c)] :
    (fun θ => answer π A m k dd DMv x θ) ⁻¹' {some c} =
      if ripe π A m k dd DMv x c then cellSet A m k dd DMv x c else ∅ := by
  ext θ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, answer_eq_some_iff]
  split_ifs with h
  · simp [cellSet, h]
  · simp [h]

/-- The answer map is measurable in the tip. -/
theorem measurable_answer_tip {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    Measurable (fun θ => answer π A m k dd DMv x θ) := by
  classical
  refine measurable_to_countable' fun a => ?_
  cases a with
  | none => exact measurableSet_restSet π A m k dd DMv x
  | some c =>
    rw [preimage_answer_some]
    split_ifs
    · exact measurableSet_cellSet A m k dd DMv x c
    · exact MeasurableSet.empty

/-- A sum over the answers splits into the ripe cells and rest, when the empty set contributes nothing. -/
theorem sum_answer {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) (F : Set V → Option Cell → ℝ)
    (hF : ∀ a, F ∅ a = 0) :
    ∑ a, F ((fun θ => answer π A m k dd DMv x θ) ⁻¹' {a}) a =
      ∑ c ∈ ripeCells π A m k dd DMv x, F (cellSet A m k dd DMv x c) (some c) +
        F (restSet π A m k dd DMv x) none := by
  classical
  rw [Fintype.sum_option, add_comm]
  congr 1
  rw [ripeCells, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [preimage_answer_some]
  split_ifs <;> simp [hF]

/-- The entropy of the answer (Info.lean) is `entAns` (CellsRound.lean). -/
theorem ansEntropy_answer {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    ansEntropy π (fun θ => answer π A m k dd DMv x θ) = entAns π A m k dd DMv x := by
  have h := sum_answer π A m k dd DMv x (fun S _ => Real.negMulLog (π.real S)) (fun _ => by simp)
  unfold ansEntropy
  rw [h, entAns]
  have e : ∀ p : ℝ, Real.negMulLog p = p * Real.log (1 / p) := fun p => by
    rw [Real.negMulLog, one_div, Real.log_inv]
    ring
  simp only [e, massRest]

variable {d : ℕ}

/-- The payment of the announced cells (Ledger.lean) is the sum over the ripe cells (CellsRound.lean). -/
theorem payAnn_answer (I : Inputs) (w : ℝ) (π : Measure (E d)) (A : E d →L[ℝ] E d) (m : E d) (k dd DMv : ℝ)
    (x : E d) :
    payAnn w π (fun θ => answer π A m k dd DMv x θ) =
      ∑ c ∈ ripeCells π A m k dd DMv x, cellPay w π (cellSet A m k dd DMv x c) := by
  classical
  unfold payAnn
  rw [ripeCells, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [preimage_answer_some]
  split_ifs
  · rfl
  · exact I.cellPay_empty π w

/-- The centre of the signal's range `[b, b + 3L/2 + g]`. -/
noncomputable def midB (P : SParams) : ℝ := P.b + (3 * P.L / 2 + P.g) / 2

/-- `p_rest` of the rule at `(π, x)`. -/
noncomputable abbrev prS (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : ℝ :=
  massRest π (frameS P d π) (meanV π) P.k d (dmS P d π) x

/-- The centring constants of the channel bound (S1): the centre of the range on the ripe cells, and on rest the
centre of the range when `p_rest < 1/2`, `b + q(x)` when `p_rest ≥ 1/2`. -/
noncomputable def cHat (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : Option Cell → ℝ
  | some _ => midB P
  | none => if 1 / 2 ≤ prS P d π x then
      P.b + bowl (frameS P d π) (meanV π) (P.g / P.k) P.k (5 * Real.sqrt d) x else midB P

/-- `Iann = ∑_{c ripe} ∫_c (s - ĉ)²/(2σ²)`. -/
noncomputable def iAnn (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : ℝ :=
  ∑ c ∈ ripeCells π (frameS P d π) (meanV π) P.k d (dmS P d π) x,
    (∫ θ in cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) x c, ((ruleS d P).sig π x θ - midB P) ^ 2 ∂π) /
      (2 * P.sc ^ 2)

/-- `Irest = ∫_{rest} (s - ĉ_rest)²/(2σ²)/p_rest`. -/
noncomputable def iRest (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : ℝ :=
  (∫ θ in restSet π (frameS P d π) (meanV π) P.k d (dmS P d π) x,
      ((ruleS d P).sig π x θ - cHat P d π x none) ^ 2 ∂π) / (2 * P.sc ^ 2) / prS P d π x

/-- The context of one live round: the law `π` of the tip on `B(0, 1/2)`, its covariance positive semidefinite, the
round live, the play in the unit ball. -/
structure RoundCtx (P : SParams) (d : ℕ) (π : Measure (E d)) (x : E d) : Prop where
  prob : IsProbabilityMeasure π
  ball : ∀ᵐ θ ∂π, θ ∈ Metric.closedBall (0 : E d) (1 / 2)
  cov : (covM π).PosSemidef
  live : liveS P d π
  play : x ∈ Metric.closedBall (0 : E d) 1

theorem RoundCtx.sq {P : SParams} {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x) :
    Integrable (fun θ => ‖θ‖ ^ 2) π := by
  have := hc.prob
  exact integrable_sq_norm_of_ae_mem π hc.ball

theorem RoundCtx.mean {P : SParams} {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x) :
    meanV π ∈ Metric.closedBall (0 : E d) (1 / 2) := by
  have := hc.prob
  exact meanV_mem_closedBall π hc.ball

theorem RoundCtx.dm {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x) :
    (d : ℝ) / 2 ≤ dmS P d π :=
  hc.live.trans (dLive_le_DM _ _ hc.cov hP.w_pos.ne')

theorem ans_live {P : SParams} {π : Measure (E d)} (hl : liveS P d π) (x : E d) :
    (ruleS d P).ans π x = fun θ => answer π (frameS P d π) (meanV π) P.k d (dmS P d π) x θ := by
  funext θ
  simp only [ruleS_ans, hl, ↓reduceIte]
  rfl

theorem sig_live {P : SParams} {π : Measure (E d)} (hl : liveS P d π) (x : E d) :
    (ruleS d P).sig π x =
      fun θ => P.b + dent (frameS P d π) (meanV π) (P.g / P.k) P.k (5 * Real.sqrt d) θ x := by
  funext θ
  simp only [ruleS_sig, hl, ↓reduceIte]
  rfl

/-- `Dbar`: the posterior mean of `sig - b` is `dentMean` on a live round. -/
theorem integral_sig_live {P : SParams} {π : Measure (E d)} (hl : liveS P d π) (x : E d) :
    ∫ θ, ((ruleS d P).sig π x θ - P.b) ∂π = dentMean π (frameS P d π) (meanV π) P.g P.k d x := by
  rw [sig_live hl]
  unfold dentMean
  congr 1
  funext θ
  ring

theorem sq_sig_sub_midB_le {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x)
    (θ : E d) : ‖((ruleS d P).sig π x θ - midB P) ^ 2‖ ≤ (3 * P.L / 2 + P.g) ^ 2 / 4 := by
  have h0 := sig_sub_b_nonneg hP π x θ
  have h1 := sig_sub_b_le hP hc.cov.1 hc.mean hc.play θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold midB
  nlinarith

theorem abs_readT_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m θ x : V) :
    |readT A m θ x| ≤ ‖A (θ - m)‖ := by
  unfold readT
  rcases (norm_nonneg (A (x - m))).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact norm_nonneg _
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h, mul_comm]
    exact abs_real_inner_le_norm _ _

/-- Lemma 9.6 with the centring constants `cHat`. -/
theorem chain_one (I : Inputs) {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d}
    (hc : RoundCtx P d π x) :
    infoJ π ((ruleS d P).ans π x) ((ruleS d P).sig π x) P.sc ≤
      entAns π (frameS P d π) (meanV π) P.k d (dmS P d π) x + iAnn P d π x + prS P d π x * iRest P d π x := by
  have := hc.prob
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hS : ∀ θ, |(ruleS d P).sig π x θ| ≤ 1 := fun θ => by
    have h0 := sig_sub_b_nonneg hP π x θ
    have h1 := sig_sub_b_le hP hc.cov.1 hc.mean hc.play θ
    have := hP.rng
    have := hP.b_eq
    rw [abs_le]
    constructor <;> linarith
  have hsm : Measurable ((ruleS d P).sig π x) := by
    rw [sig_live hc.live]
    exact measurable_const.add (measurable_dent_tip _ _ _ _ _ (div_pos hP.g_pos hk).le hk.le
      (by positivity) x)
  have h := I.infoJ_chain π (ans_live hc.live x ▸ measurable_answer_tip π _ _ _ _ _ x) hsm hS
    hP.sc_pos.ne' (cHat P d π x)
  rw [ans_live hc.live] at h ⊢
  rw [ansEntropy_answer, sum_answer π _ _ _ _ _ x
    (fun S a => (∫ θ in S, ((ruleS d P).sig π x θ - cHat P d π x a) ^ 2 ∂π) / (2 * P.sc ^ 2))
    (fun a => by simp)] at h
  refine h.trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl (add_le_add (le_of_eq (α := ℝ) rfl) ?_)
  unfold iRest
  rcases (cells_pr_nonneg π (frameS P d π) (meanV π) P.k d (dmS P d π) x).eq_or_lt with h0 | hpos
  · have hnull : π (restSet π (frameS P d π) (meanV π) P.k d (dmS P d π) x) = 0 := by
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      unfold massRest at h0
      rw [← h0, ENNReal.ofReal_zero]
    rw [Measure.restrict_eq_zero.2 hnull, integral_zero_measure, zero_div, show prS P d π x = 0 from h0.symm,
      zero_mul]
  · rw [mul_div_cancel₀ _ hpos.ne']

/-- (S1) on the ripe cells: each carries at most `B = (3L/2 + g)²/(8σ²)` nats per unit of mass. -/
theorem ann_le_one {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x) :
    iAnn P d π x ≤ chanB P.L P.g P.sc * massAnn π (frameS P d π) (meanV π) P.k d (dmS P d π) x := by
  have := hc.prob
  have hσ : 0 < 2 * P.sc ^ 2 := by have := hP.sc_pos; positivity
  unfold iAnn massAnn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hint := norm_setIntegral_le_of_norm_le_const (μ := π)
    (s := cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) x c) (measure_lt_top _ _)
    (fun θ _ => sq_sig_sub_midB_le hP hc θ)
  rw [Real.norm_eq_abs] at hint
  calc _ ≤ (3 * P.L / 2 + P.g) ^ 2 / 4 * π.real (cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) x c) /
        (2 * P.sc ^ 2) := div_le_div_of_nonneg_right ((le_abs_self _).trans hint) hσ.le
    _ = _ := by unfold chanB; field_simp; ring

/-- (S1) on rest when `p_rest < 1/2`. -/
theorem rest_le_one {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x)
    (hpr : prS P d π x < 1 / 2) : iRest P d π x ≤ chanB P.L P.g P.sc := by
  have := hc.prob
  have hσ : 0 < 2 * P.sc ^ 2 := by have := hP.sc_pos; positivity
  have hB : 0 ≤ chanB P.L P.g P.sc := by unfold chanB; positivity
  have hc0 : cHat P d π x none = midB P := by simp only [cHat, not_le.2 hpr, ↓reduceIte]
  have hint := norm_setIntegral_le_of_norm_le_const (μ := π)
    (s := restSet π (frameS P d π) (meanV π) P.k d (dmS P d π) x) (measure_lt_top _ _)
    (fun θ _ => sq_sig_sub_midB_le hP hc θ)
  rw [Real.norm_eq_abs] at hint
  rcases (cells_pr_nonneg π (frameS P d π) (meanV π) P.k d (dmS P d π) x).eq_or_lt with h0 | hpos
  · unfold iRest
    rw [show prS P d π x = 0 from h0.symm, div_zero]
    exact hB
  · unfold iRest
    rw [hc0]
    calc _ ≤ (3 * P.L / 2 + P.g) ^ 2 / 4 * prS P d π x / (2 * P.sc ^ 2) / prS P d π x := by
          gcongr
          exact (le_abs_self _).trans hint
      _ = _ := by unfold chanB; field_simp; ring

/-- Lemma 9.7 (ii) through `cells_price` when `p_rest ≥ 1/2`. -/
theorem price_one {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d} (hc : RoundCtx P d π x)
    (hpr : 1 / 2 ≤ prS P d π x) :
    iRest P d π x ≤ P.g / (P.sc ^ 2 * priceR d P.k) *
      (dentRest π (frameS P d π) (meanV π) P.g P.k d (dmS P d π) x / prS P d π x) := by
  have := hc.prob
  have hsq := hc.sq
  have hT2 : IntegrableOn (fun θ => readT (frameS P d π) (meanV π) θ x ^ 2)
      (cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) x Cell.tail) π := by
    refine Integrable.integrableOn ?_
    refine ((hsq.const_mul (2 * ‖frameS P d π‖ ^ 2)).add
      (integrable_const (2 * ‖frameS P d π‖ ^ 2 * ‖meanV π‖ ^ 2))).mono'
      (((continuous_readT_tip _ _ x).pow 2).aestronglyMeasurable) (ae_of_all _ fun θ => ?_)
    show ‖readT (frameS P d π) (meanV π) θ x ^ 2‖ ≤
      2 * ‖frameS P d π‖ ^ 2 * ‖θ‖ ^ 2 + 2 * ‖frameS P d π‖ ^ 2 * ‖meanV π‖ ^ 2
    have h1 := abs_readT_le (frameS P d π) (meanV π) θ x
    have h2 := (frameS P d π).le_opNorm (θ - meanV π)
    have h3 := norm_sub_le θ (meanV π)
    have h4 : 0 ≤ ‖frameS P d π (θ - meanV π)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h5 : ‖frameS P d π (θ - meanV π)‖ ≤ ‖frameS P d π‖ * (‖θ‖ + ‖meanV π‖) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
    have h6 : |readT (frameS P d π) (meanV π) θ x| ^ 2 ≤ (‖frameS P d π‖ * (‖θ‖ + ‖meanV π‖)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (h1.trans h5) 2
    nlinarith [h6, mul_nonneg (sq_nonneg ‖frameS P d π‖) (sq_nonneg (‖θ‖ - ‖meanV π‖))]
  have h := cells_price π (frameS P d π) (meanV π) P.g P.sc P.k d (dmS P d π) hP.g_pos hP.sc_pos
    (by linarith [hP.k_ge]) hP.dim (hc.dm hP) x hT2 hpr
  have hc0 : cHat P d π x none = P.b + bowl (frameS P d π) (meanV π) (P.g / P.k) P.k (5 * Real.sqrt d) x := by
    simp only [cHat, hpr, ↓reduceIte]
  have he : iRest P d π x = gapRest π (frameS P d π) (meanV π) P.g P.k d (dmS P d π) x /
      massRest π (frameS P d π) (meanV π) P.k d (dmS P d π) x / (2 * P.sc ^ 2) := by
    unfold iRest gapRest
    rw [div_right_comm, hc0, sig_live hc.live]
    congr 3
    funext θ
    ring
  rw [he]
  exact h

/-- Lemma LEAK through `cells_leak` and the cell payments (L3) to (L5). -/
theorem leak_one (I : Inputs) {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d}
    (hc : RoundCtx P d π x) :
    entAns π (frameS P d π) (meanV π) P.k d (dmS P d π) x ≤
        4 * (3 * Real.log d + 1) / P.k * payAnn (P.w d) π ((ruleS d P).ans π x) ∧
      massAnn π (frameS P d π) (meanV π) P.k d (dmS P d π) x ≤ 4 / P.k * payAnn (P.w d) π ((ruleS d P).ans π x) := by
  have := hc.prob
  have hsq := hc.sq
  have hw := hP.w_pos
  have hd := hP.d_pos
  rw [ans_live hc.live, payAnn_answer I]
  refine cells_leak π (frameS P d π) (meanV π) P.k d (dmS P d π) (by linarith [hP.k_ge]) hP.dim x
    (fun c => cellPay (P.w d) π (cellSet (frameS P d π) (meanV π) P.k d (dmS P d π) x c)) (fun _ => ?_) ?_
  · exact I.pay_tail π hsq hw (by linarith [hP.k_ge]) x (measurableSet_cellSet _ _ _ _ _ _ _)
      (fun θ hθ => (cellOf_tail_iff _ _ _ _ _ _ _).1 hθ)
  · rintro c (rfl | rfl) _
    · exact I.pay_outer π hsq hw hd (measurableSet_cellSet _ _ _ _ _ _ _)
        (fun θ hθ => ((cellOf_outer_iff _ _ _ _ _ _ _).1 hθ).2)
    · exact I.pay_inner π hsq hw hd hc.live (measurableSet_cellSet _ _ _ _ _ _ _)
        (fun θ hθ => ((cellOf_inner_iff _ _ _ _ _ _ _).1 hθ).2.2)

/-- All the fields of `RoundFacts` at one live round. -/
theorem roundFacts_one (I : Inputs) {P : SParams} (hP : Good P d) {π : Measure (E d)} {x : E d}
    (hc : RoundCtx P d π x) :
    RoundFacts d P.k P.g P.sc (chanB P.L P.g P.sc) (massAnn π (frameS P d π) (meanV π) P.k d (dmS P d π) x)
      (prS P d π x) (entAns π (frameS P d π) (meanV π) P.k d (dmS P d π) x) (iAnn P d π x) (iRest P d π x)
      (infoJ π ((ruleS d P).ans π x) ((ruleS d P).sig π x) P.sc) (payAnn (P.w d) π ((ruleS d P).ans π x))
      (∫ θ, ((ruleS d P).sig π x θ - P.b) ∂π)
      (dentRest π (frameS P d π) (meanV π) P.g P.k d (dmS P d π) x)
      (massReg π (frameS P d π) (meanV π) P.k d (dmS P d π) x) := by
  have := hc.prob
  have hk : 0 < P.k := by linarith [hP.k_ge]
  have hk1 : 1 ≤ P.k := by linarith [hP.k_ge]
  have hD := integral_sig_live hc.live x
  exact
    { mass := cells_mass π _ _ _ _ _ x
      a_nonneg := cells_a_nonneg π _ _ _ _ _ x
      pr_nonneg := cells_pr_nonneg π _ _ _ _ _ x
      chain := chain_one I hP hc
      ann_le := ann_le_one hP hc
      rest_le := rest_le_one hP hc
      leak := (leak_one I hP hc).1
      leak_mass := (leak_one I hP hc).2
      price := price_one hP hc
      drest_nonneg := cells_drest_nonneg π _ _ _ _ _ _ hP.g_pos.le hk.le x
      drest_le := by rw [hD]; exact cells_drest_le π _ _ _ _ _ _ hP.g_pos.le hk.le x
      floor := by rw [hD]; exact cells_floor π _ _ _ _ _ _ hP.g_pos hk hP.dim (hc.dm hP) x
      reg := cells_reg π _ _ _ _ _ hk1 hP.dim x }

end OneRound

/-! ## The game: `GameFacts` at the parameters of Proposition 9.11 -/

section Game

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The law of the tip before round `t` on the sample `s`. -/
noncomputable abbrev postT (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : Measure (E d) :=
  post (prior d (1 / 2)) (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)

/-- The play of round `t` on the sample `s`. -/
noncomputable abbrev playT (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : E d :=
  play pol t s.2.2 (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)

/-- The live event of round `t`. -/
def liveSet (P : SParams) (pol : Learner Ω d) (t : ℕ) : Set (Sample d Ω) :=
  {s | liveS P d (postT P pol t s)}

/-- `J`: the information of round `t`. -/
noncomputable def Jf (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  infoRound (prior d (1 / 2)) (ruleS d P) P.sc pol t s

/-- `P'`: the payment of the announced cells of round `t`. -/
noncomputable def Pf (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  payAnn (P.w d) (postT P pol t s) ((ruleS d P).ans (postT P pol t s) (playT P pol t s))

/-- `a`: the mass announced in round `t`. -/
noncomputable def af (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  1 - (postT P pol t s).real {θ | (ruleS d P).ans (postT P pol t s) (playT P pol t s) θ = none}

/-- `E[D | G_{t-1}, U]`: the posterior mean of the dent of round `t`. -/
noncomputable def Df (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  ∫ θ, ((ruleS d P).sig (postT P pol t s) (playT P pol t s) θ - P.b) ∂postT P pol t s

theorem measurableSet_liveSet {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) {t : ℕ} (ht : t ≤ n) :
    MeasurableSet (liveSet P pol t) := by
  have hR := ruleS_meas_prior hP
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hD := dens_props (prior d (1 / 2)) (ruleS d P) hR P.sc t
  exact (measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc hpol' ht)
    (measurableSet_liveS_dens P (prior d (1 / 2)) hD.1 hD.2.1)

omit [MeasurableSpace Ω] in
/-- A dead round stays dead: its answer and its signal are constants, so the posterior does not move. -/
theorem live_of_live_succ {P : SParams} (hP : Good P d) (pol : Learner Ω d) (t : ℕ)
    {s : Sample d Ω} (hs : s ∈ liveSet P pol (t + 1)) : s ∈ liveSet P pol t := by
  by_contra hdead
  have hd' : ¬ liveS P d (postT P pol t s) := hdead
  have := post_isProb hP P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
  have hv : noiseVar P.sc ≠ 0 := noiseVar_ne_zero hP.sc_pos.ne'
  have hpost : postT P pol (t + 1) s = postT P pol t s := by
    show post _ _ _ (t + 1) (hist _ _ _ pol (t + 1) s) = _
    rw [hist_succ, post_succ_push _ _ (ruleS_meas_prior hP)]
    refine bayesUpd_const _ (c := gaussianPDF (P.b + 0) (noiseVar P.sc) ((ruleS d P).sig (postT P pol t s)
      (playT P pol t s) s.1 + P.sc * s.2.1 t)) (fun θ => ?_) (gaussianPDF_pos _ hv _).ne' (by simp [gaussianPDF])
    have hans : (ruleS d P).ans (postT P pol t s) (playT P pol t s) = fun _ => none :=
      funext fun θ => by simp only [ruleS_ans, hd', ↓reduceIte]
    simp only [lik, hans, ruleS_sig, hd', ↓reduceIte, Set.preimage_const_of_mem (Set.mem_singleton none),
      Set.indicator_univ]
  exact hd' (hpost ▸ hs)

omit [MeasurableSpace Ω] in
theorem liveSet_anti {P : SParams} (hP : Good P d) (pol : Learner Ω d) {t u : ℕ} (htu : t ≤ u) :
    liveSet P pol u ⊆ liveSet P pol t := by
  induction u, htu using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih => exact fun s hs => ih (live_of_live_succ hP pol u hs)

omit [MeasurableSpace Ω] in
theorem Pf_dead (I : Inputs) {P : SParams} (pol : Learner Ω d) (t : ℕ) {s : Sample d Ω}
    (hs : s ∉ liveSet P pol t) : Pf P pol t s = 0 := by
  have hd' : ¬ liveS P d (postT P pol t s) := hs
  have hans : (ruleS d P).ans (postT P pol t s) (playT P pol t s) = fun _ => none :=
    funext fun θ => by simp only [ruleS_ans, hd', ↓reduceIte]
  unfold Pf payAnn
  rw [hans]
  refine Finset.sum_eq_zero fun c _ => ?_
  have he : (fun _ : E d => (none : Option Cell)) ⁻¹' {some c} = ∅ :=
    Set.preimage_const_of_notMem (by simp)
  rw [he, I.cellPay_empty]

omit [MeasurableSpace Ω] in
theorem Jf_dead (I : Inputs) {P : SParams} (hP : Good P d) (pol : Learner Ω d) (t : ℕ) {s : Sample d Ω}
    (hs : s ∉ liveSet P pol t) : Jf P pol t s = 0 := by
  have hd' : ¬ liveS P d (postT P pol t s) := hs
  have := post_isProb hP P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
  have hans : (ruleS d P).ans (postT P pol t s) (playT P pol t s) = fun _ => none :=
    funext fun θ => by simp only [ruleS_ans, hd', ↓reduceIte]
  have hsig : (ruleS d P).sig (postT P pol t s) (playT P pol t s) = fun _ => P.b + 0 :=
    funext fun θ => by simp only [ruleS_sig, hd', ↓reduceIte]
  show infoJ (postT P pol t s) ((ruleS d P).ans (postT P pol t s) (playT P pol t s))
    ((ruleS d P).sig (postT P pol t s) (playT P pol t s)) P.sc = 0
  rw [hans, hsig]
  exact I.infoJ_const _ none (P.b + 0) hP.sc_pos.ne'

omit [MeasurableSpace Ω] in
theorem Df_dead {P : SParams} (pol : Learner Ω d) (t : ℕ) {s : Sample d Ω} (hs : s ∉ liveSet P pol t) :
    Df P pol t s = 0 := by
  have h0 : ∀ θ, (ruleS d P).sig (postT P pol t s) (playT P pol t s) θ - P.b = 0 := fun θ => by
    simp [ruleS_sig, show ¬ liveS P d (postT P pol t s) from hs]
  simp only [Df, h0, integral_zero]

theorem measurable_af {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) {t : ℕ} (ht : t < n) : Measurable (af P pol t) := by
  have hR := ruleS_meas_prior hP
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc hpol' ht.le
  have hans := (measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).1
  have hpl := measurable_play (α := Option Cell) (hpol' t ht)
  have hg : Measurable fun q : Sample d Ω × E d => (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t q.1,
      play pol t q.1.2.2 (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t q.1), q.2) :=
    (hh.comp measurable_fst).prodMk ((hpl.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
      (hh.comp measurable_fst))).prodMk measurable_snd)
  have hS := (hans.comp hg) (measurableSet_singleton none)
  have hL := measurable_lintegral_post (prior d (1 / 2)) (ruleS d P) hR P.sc t hh
    ((measurable_const (a := (1 : ℝ≥0∞))).indicator hS)
  have hm := (measurable_const (a := (1 : ℝ))).sub (ENNReal.measurable_toReal.comp hL)
  convert hm using 1
  funext s
  have hθ : MeasurableSet {θ | (ruleS d P).ans (postT P pol t s) (playT P pol t s) θ = none} :=
    (hans.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) (measurableSet_singleton none)
  simp only [Pi.sub_apply, Function.comp_apply]
  unfold af
  rw [measureReal_def, ← lintegral_indicator_one hθ]
  rfl

theorem measurable_Df {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) {t : ℕ} (ht : t < n) : Measurable (Df P pol t) := by
  have hR := ruleS_meas_prior hP
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hh := measurable_hist (prior d (1 / 2)) (ruleS d P) hR P.sc hpol' ht.le
  have hsig := (measurable_rule_post (prior d (1 / 2)) (ruleS d P) hR P.sc t).2
  have hpl := measurable_play (α := Option Cell) (hpol' t ht)
  have hf : Measurable fun q : Sample d Ω × E d => ENNReal.ofReal ((ruleS d P).sig (post (prior d (1 / 2))
      (ruleS d P) P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t q.1))
      (play pol t q.1.2.2 (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t q.1)) q.2 - P.b) :=
    ENNReal.measurable_ofReal.comp ((hsig.comp ((hh.comp measurable_fst).prodMk ((hpl.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk (hh.comp measurable_fst))).prodMk
        measurable_snd))).sub measurable_const)
  have hL := measurable_lintegral_post (prior d (1 / 2)) (ruleS d P) hR P.sc t hh hf
  have heq : Df P pol t = fun s => (∫⁻ θ, ENNReal.ofReal ((ruleS d P).sig (postT P pol t s) (playT P pol t s) θ - P.b)
      ∂postT P pol t s).toReal := by
    funext s
    have := post_isProb hP P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
    have hθ : Measurable fun θ => (ruleS d P).sig (postT P pol t s) (playT P pol t s) θ - P.b :=
      (hsig.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).sub measurable_const
    unfold Df
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun θ => sig_sub_b_nonneg hP _ _ θ)
      hθ.aestronglyMeasurable
  rw [heq]
  exact ENNReal.measurable_toReal.comp hL

omit [MeasurableSpace Ω] in
theorem af_mem {P : SParams} (hP : Good P d) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) :
    0 ≤ af P pol t s ∧ af P pol t s ≤ 1 := by
  have := post_isProb hP P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
  unfold af
  constructor
  · linarith [measureReal_le_one (μ := postT P pol t s)
      (s := {θ | (ruleS d P).ans (postT P pol t s) (playT P pol t s) θ = none})]
  · linarith [measureReal_nonneg (μ := postT P pol t s)
      (s := {θ | (ruleS d P).ans (postT P pol t s) (playT P pol t s) θ = none})]

theorem Df_mem (I : Inputs) {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) {t : ℕ} (ht : t < n) (s : Sample d Ω) :
    0 ≤ Df P pol t s ∧ Df P pol t s ≤ 1 / 2 := by
  have := post_isProb hP P.sc t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s)
  have hx : playT P pol t s ∈ Metric.closedBall (0 : E d) 1 := (hpol t ht).2 _ _ _
  have hb := fun θ => sig_post_bounds I hP t (hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s) hx θ
  constructor
  · exact integral_nonneg fun θ => (hb θ).1
  · have h := norm_integral_le_of_norm_le_const (μ := postT P pol t s) (C := 1 / 2)
      (f := fun θ => (ruleS d P).sig (postT P pol t s) (playT P pol t s) θ - P.b) (ae_of_all _ fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb θ).1]
        linarith [(hb θ).2, hP.rng])
    rw [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ h)

/-- The per-round facts at a live sample of round `t`. -/
theorem roundFacts_at (I : Inputs) {P : SParams} (hP : Good P d) {pol : Learner Ω d} {n : ℕ}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) {t : ℕ} (ht : t < n) {s : Sample d Ω}
    (hs : s ∈ liveSet P pol t) :
    ∃ pr H Iann Irest Drest preg : ℝ, RoundFacts d P.k P.g P.sc (chanB P.L P.g P.sc) (af P pol t s) pr H Iann
      Irest (Jf P pol t s) (Pf P pol t s) (Df P pol t s) Drest preg := by
  have hc : RoundCtx P d (postT P pol t s) (playT P pol t s) :=
    ⟨post_isProb hP P.sc t _, post_ball _ P.sc t _, post_cov I hP P.sc t _, hs, (hpol t ht).2 _ _ _⟩
  have := hc.prob
  have hm := cells_mass (postT P pol t s) (frameS P d (postT P pol t s)) (meanV (postT P pol t s)) P.k d
    (dmS P d (postT P pol t s)) (playT P pol t s)
  have hr : af P pol t s = 1 - massRest (postT P pol t s) (frameS P d (postT P pol t s))
      (meanV (postT P pol t s)) P.k d (dmS P d (postT P pol t s)) (playT P pol t s) := by
    unfold af massRest restSet
    rw [ans_live hs]
  have haf : af P pol t s = massAnn (postT P pol t s) (frameS P d (postT P pol t s)) (meanV (postT P pol t s))
      P.k d (dmS P d (postT P pol t s)) (playT P pol t s) := by
    linarith
  have h1 := roundFacts_one I hP hc
  rw [← haf] at h1
  exact ⟨_, _, _, _, _, _, h1⟩

/-- The mean regret of the Gaussian game is the sum of the round means over the live events (Lemma 9.5). -/
theorem sum_Df_eq (I : Inputs) {P : SParams} (hP : Good P d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} {n : ℕ} (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) :
    ∑ t ∈ Finset.range n, ∫ s in liveSet P pol t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, regG (prior d (1 / 2)) P pol n s ∂gameLaw (prior d (1 / 2)) μ := by
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hR := ruleS_meas_prior hP
  let F : ℕ → E d × Hist d (Option Cell) × Ω → ℝ := fun t p =>
    (ruleS d P).sig (post (prior d (1 / 2)) (ruleS d P) P.sc t p.2.1) (play pol t p.2.2 p.2.1) p.1 - P.b
  have hFm : ∀ t < n, Measurable (F t) := fun t ht =>
    ((measurable_rule_post _ _ hR P.sc t).2.comp ((measurable_fst.comp measurable_snd).prodMk
      (((measurable_play (α := Option Cell) (hpol' t ht)).comp
        ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))).prodMk
          measurable_fst))).sub measurable_const
  have hFb : ∀ t < n, ∀ p, |F t p| ≤ 1 / 2 := fun t ht p => by
    have hx : play pol t p.2.2 p.2.1 ∈ Metric.closedBall (0 : E d) 1 := (hpol t ht).2 _ _ _
    obtain ⟨h0, h1⟩ := sig_post_bounds I hP t p.2.1 hx p.1
    have := hP.rng
    simp only [F]
    rw [abs_le]
    constructor <;> linarith
  have hFi : ∀ t < n, Integrable (fun s : Sample d Ω => F t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s,
      s.2.2)) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    (integrable_const (1 / 2 : ℝ)).mono' ((hFm t ht).comp (measurable_fst.prodMk
      ((measurable_hist _ _ hR P.sc hpol' ht.le).prodMk (measurable_snd.comp measurable_snd)))).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hFb t ht _)
  have hround : ∀ t ∈ Finset.range n, ∫ s in liveSet P pol t, Df P pol t s ∂gameLaw (prior d (1 / 2)) μ =
      ∫ s, F t (s.1, hist (prior d (1 / 2)) (ruleS d P) P.sc pol t s, s.2.2) ∂gameLaw (prior d (1 / 2)) μ := by
    intro t ht
    have ht' := Finset.mem_range.1 ht
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => Df_dead pol t hs,
      post_disintegrates_integral (prior d (1 / 2)) μ (ruleS d P) hR hP.sc_pos.ne' hpol' ht'.le (hFm t ht')
        (hFb t ht')]
    rfl
  rw [Finset.sum_congr rfl hround, ← integral_finsetSum _ fun t ht => hFi t (Finset.mem_range.1 ht)]
  rfl

/-- `GameFacts` at the parameters of Proposition 9.11. -/
theorem gameFacts (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {pol : Learner Ω d} (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) :
    GameFacts d (kRipe d) (gRipe d n (sigB n)) (sigB n) (chanB (sigB n) (gRipe d n (sigB n)) (sigB n))
      (wStar d (kRipe d) (sigB n) (gRipe d n (sigB n))) n
      ((gameLaw (prior d (1 / 2)) μ).real (liveSet (pB d n) pol n)ᶜ)
      (fun t => ∫ s in liveSet (pB d n) pol t, Jf (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pB d n) pol t, Pf (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pB d n) pol t, af (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pB d n) pol t, Df (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => (gameLaw (prior d (1 / 2)) μ).real (liveSet (pB d n) pol t)) := by
  have hP := good_pB hd hn
  have hG : IsProbabilityMeasure (gameLaw (prior d (1 / 2)) μ) := isProbabilityMeasure_gameLaw _ μ
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hR := ruleS_meas_prior hP
  have hsc : (pB d n).sc ≠ 0 := hP.sc_pos.ne'
  have hS₀ : ∀ t < n, ∀ h θ ω, |(ruleS d (pB d n)).sig (post (prior d (1 / 2)) (ruleS d (pB d n)) (pB d n).sc t h)
      (play pol t ω h) θ| ≤ 1 := fun t ht h θ ω => abs_sig_post_le I hP t h ((hpol t ht).2 _ _ _) θ
  have hk : 0 < (pB d n).k := by linarith [hP.k_ge]
  have hB : 0 ≤ chanB (pB d n).L (pB d n).g (pB d n).sc := by unfold chanB; positivity
  have hLedger := I.ledger_game hP.d_pos (show (0 : ℝ) < 1 / 2 by norm_num) μ (ruleS d (pB d n)) hR hsc hpol'
    hP.w_pos.ne'
  have hJi : ∀ t < n, Integrable (Jf (pB d n) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    I.integrable_infoRound (prior d (1 / 2)) μ (ruleS d (pB d n)) hR hsc hpol' hS₀ ht
  have hPi : ∀ t < n, Integrable (Pf (pB d n) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    hLedger.1 t ht
  have hai : ∀ t < n, Integrable (af (pB d n) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    (integrable_const (1 : ℝ)).mono' (measurable_af hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := af_mem hP pol t s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hDi : ∀ t < n, Integrable (Df (pB d n) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    (integrable_const (1 : ℝ)).mono' (measurable_Df hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := Df_mem I hP hpol ht s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hround : ∀ t < n, _ := fun t ht =>
    round_integral (gameLaw (prior d (1 / 2)) μ) (liveSet (pB d n) pol t) (measurableSet_liveSet hP hpol ht.le)
      ((4 * (3 * Real.log d + 1) + 8 * chanB (pB d n).L (pB d n).g (pB d n).sc) / (pB d n).k)
      ((pB d n).g / ((pB d n).sc ^ 2 * priceR d (pB d n).k)) (pB d n).g (pB d n).k
      (Jf (pB d n) pol t) (Pf (pB d n) pol t) (af (pB d n) pol t) (Df (pB d n) pol t)
      (hJi t ht) (hPi t ht) (hai t ht) (hDi t ht) fun s hs => by
        obtain ⟨pr, H, Iann, Irest, Drest, preg, hRF⟩ := roundFacts_at I hP hpol ht hs
        exact round_bound hk hP.dim hP.g_pos.le hB hRF
  have hlive := measurableSet_liveSet hP hpol (le_refl n)
  have hX : Real.exp 1 / 2 ≤ xCount d ((pB d n).w d) := by
    have h16 := (ripeB_params hd hn).2.2.2.2.2.2.2.1
    have := Real.exp_one_lt_three
    exact le_trans (by linarith) h16
  refine
    { round_J := fun t ht => (hround t ht).1
      round_floor := fun t ht => (hround t ht).2.1
      round_mass := fun t ht => (hround t ht).2.2
      live := fun t ht => ?_
      payment := ?_
      count := ?_ }
  · rw [probReal_compl_eq_one_sub hlive, sub_sub_cancel]
    exact measureReal_mono (liveSet_anti hP pol ht.le)
  · have he : ∀ t ∈ Finset.range n, ∫ s in liveSet (pB d n) pol t, Pf (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ =
        ∫ s, Pf (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ := fun t _ =>
      setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => Pf_dead I pol t hs
    rw [Finset.sum_congr rfl he]
    exact hLedger.2
  · have hset : {s : Sample d Ω | dLive ((pB d n).w d) (covM (post (prior d (1 / 2)) (ruleS d (pB d n)) (pB d n).sc n
        (hist (prior d (1 / 2)) (ruleS d (pB d n)) (pB d n).sc pol n s))) < d / 2} = (liveSet (pB d n) pol n)ᶜ := by
      ext s
      exact (not_le (α := ℝ)).symm
    have hJ : ∀ t ∈ Finset.range n, ∫ s in liveSet (pB d n) pol t, Jf (pB d n) pol t s ∂gameLaw (prior d (1 / 2)) μ =
        ∫ s, infoRound (prior d (1 / 2)) (ruleS d (pB d n)) (pB d n).sc pol t s ∂gameLaw (prior d (1 / 2)) μ :=
      fun t _ => setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => Jf_dead I hP pol t hs
    rw [Finset.sum_congr rfl hJ, ← hset]
    exact I.count_game (by have := hP.d_pos; omega) μ (ruleS d (pB d n)) hR hsc hpol' hS₀ hP.w_pos hX

end Game

/-! ## The composition -/

/-- `TheoremConj1Lower` from the statements `Inputs`, which Main.lean discharges (`lowerTopInputs`). -/
theorem theoremConj1Lower_of_inputs (I : Inputs) : TheoremConj1Lower := by
  intro d hd n hn Ω _ μ hμ pol hpol
  have hP := good_pB hd hn
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hbal := ripeB_balance hd hn (gameFacts I hd hn μ hpol)
    (ER := ∫ s, regG (prior d (1 / 2)) (pB d n) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2) ∂gameLaw (prior d (1 / 2)) μ)
    (by rw [sum_Df_eq I hP μ hpol]; exact coupling I hP μ hn1 hpol)
  rw [integral_gameLaw_assoc (prior d (1 / 2)) μ
    (fun s => regG (prior d (1 / 2)) (pB d n) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2))] at hbal
  have hm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω =>
      regG (prior d (1 / 2)) (pB d n) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2) :=
    (measurable_regG hP hpol).comp ((measurable_fst.comp measurable_fst).prodMk
      (((measurable_clampZ _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  have hb : ∀ p : (E d × (ℕ → ℝ)) × Ω,
      |regG (prior d (1 / 2)) (pB d n) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2)| ≤ n / 2 := fun p =>
    abs_le.2 ⟨by linarith [regG_nonneg hP (prior d (1 / 2)) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2),
      (by positivity : (0 : ℝ) ≤ n / 2)], regG_le I hP hpol _⟩
  have hN : ((prior d (1 / 2)).prod gaussStream)
      {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} = 0 := by
    have h0 := ae_iff.1 (prior_ae_mem d (1 / 2))
    have hs : {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} =
        {θ | θ ∉ Metric.closedBall (0 : E d) (1 / 2)} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, h0, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((prior d (1 / 2)).prod gaussStream) μ hm hb hN
  have ha1 : a.1 ∈ Metric.closedBall (0 : E d) (1 / 2) := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ Metric.closedBall (0 : E d) 1 := Metric.closedBall_subset_closedBall (by norm_num) ha1
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hz : ∀ i, |(pB d n).sc * clampZ (ellB n) a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hP.sc_pos, ← sigB_mul_ellB hn1]
    exact mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hP.sc_pos.le
  have hσ := stratOf_mem I hP n a.1 (clampZ (ellB n) a.2) hz
  refine ⟨_, hσ, Sanity.integrable_regretAd hσ μ hpol, ?_⟩
  have he : (fun ω => regretAd (Metric.closedBall 0 1)
      (stratOf (prior d (1 / 2)) (ruleS d (pB d n)) (pB d n).sc a.1 (clampZ (ellB n) a.2)) (fun t => pol t ω) n) =
      fun ω => regG (prior d (1 / 2)) (pB d n) pol n (a.1, clampZ (ellB n) a.2, ω) :=
    funext fun ω => regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  rw [he]
  exact hbal.trans ha

end AdversarialBco.Lower.Top
