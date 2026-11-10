/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Statement

@[expose] public section

/-!
# The learner and the minimax regret

The definitions of hypothesis (H) and of the learner of Algorithm 7.1, and the lemmas of Sections 5 to 7 and of the
appendices of the paper that the proof of Corollary 1.2 uses: the exponential weights, the per-round minimax, the
class and the net, the law of play, Theorem 7.2 for the learner (`thmC_learner`), and Corollary 1.2 from hypothesis
(H) of the inner body (`corollaryADV_of_bodyH`).
-/

open MeasureTheory ProbabilityTheory Real Matrix

/-- The Lipschitz (inf-convolution) extension of `f` from `K`: `x ↦ inf_{y ∈ K} (f y + L dist x y)`. -/
noncomputable def AdversarialBco.lipExt {F : Type*} [NormedAddCommGroup F] (K : Set F) (f : F → ℝ) (L : ℝ) (x : F) :
    ℝ :=
  sInf ((fun y => f y + L * dist x y) '' K)

/-- Hypothesis (H)[α, β] of Section 2 of the paper on the class of convex `L`-Lipschitz functions `J → [lo, hi]`:
for every finitely supported law on the class (weights `w`, functions `F`), some probability law `ρ` carried by `J`,
under which the functions are integrable, has `E_ρ Fbar - E_w min_J F ≤ α + (β E_ρ E_w (Fbar - F)^2)^{1/2}`. -/
def AdversarialBco.HypH {d : ℕ} (J : Set (AdversarialBco.E d)) (L lo hi α β : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℝ) (F : Fin k → AdversarialBco.E d → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
    (∀ i, ConvexOn ℝ J (F i) ∧ (∀ x ∈ J, ∀ y ∈ J, |F i x - F i y| ≤ L * dist x y) ∧
      ∀ x ∈ J, F i x ∈ Set.Icc lo hi) →
    ∃ ρ : Measure (AdversarialBco.E d), IsProbabilityMeasure ρ ∧ ρ Jᶜ = 0 ∧ (∀ i, Integrable (F i) ρ) ∧
      ∫ x, ∑ i, w i * F i x ∂ρ - ∑ i, w i * sInf (F i '' J) ≤
        α + √(β * ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)

/-- The history of a sequential sampler: in round `t` the draw is `σ t h x`, from the history `h` of the earlier
rounds and the `t`-th coordinate `x` of the seed. -/
def AdversarialBco.seqHist {T X : Type*} (σ : (t : ℕ) → (Fin t → T) → X → T) : (t : ℕ) → (Fin t → X) → Fin t → T
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun ω => Fin.snoc (α := fun _ => T) (AdversarialBco.seqHist σ t (Fin.init ω))
      (σ t (AdversarialBco.seqHist σ t (Fin.init ω)) (ω (Fin.last t)))

/-- The history a learner rebuilds from its seed `ω` and its observations `y`: in round `t` the draw is
`ρ t h (ω t) (y t)`, from the history `h` of the earlier rounds. -/
def AdversarialBco.obsHist {T X : Type*} (ρ : (t : ℕ) → (Fin t → T) → X → ℝ → T) :
    (t : ℕ) → (ℕ → X) → (Fin t → ℝ) → Fin t → T
  | 0 => fun _ _ => Fin.elim0
  | t + 1 => fun ω y => Fin.snoc (α := fun _ => T) (AdversarialBco.obsHist ρ t ω (Fin.init y))
      (ρ t (AdversarialBco.obsHist ρ t ω (Fin.init y)) (ω t) (y (Fin.last t)))

/-- The exponential weights along a history of the learner of Algorithm 7.1: uniform at
the start, then `q_{t+1}(z) ∝ q_t(z) exp(-η lhat_t(z))`, where `est q τ` is the estimate of the round played from the
weights `q` with outcome `τ`. -/
noncomputable def AdversarialBco.ewQ {T C : Type*} [Fintype C] (η : ℝ) (est : (C → ℝ) → T → C → ℝ) :
    (t : ℕ) → (Fin t → T) → C → ℝ
  | 0 => fun _ _ => 1 / Fintype.card C
  | t + 1 => fun h z => AdversarialBco.ewQ η est t (Fin.init h) z *
      Real.exp (-η * est (AdversarialBco.ewQ η est t (Fin.init h)) (h (Fin.last t)) z) /
      ∑ z', AdversarialBco.ewQ η est t (Fin.init h) z' *
        Real.exp (-η * est (AdversarialBco.ewQ η est t (Fin.init h)) (h (Fin.last t)) z')

theorem AdversarialBco.minimaxRegret_le_n {d : ℕ} (K : Set (AdversarialBco.E d)) (hK : K.Nonempty) (n : ℕ) :
    AdversarialBco.minimaxRegret K n ≤ n := by
  obtain ⟨c, hc⟩ := hK
  let Ω := Unit
  let μ : Measure Ω := Measure.dirac ()
  have hμ_prob : IsProbabilityMeasure μ := by infer_instance
  let pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d := fun _ _ _ => c
  have hpol_learner : IsLearner K pol := by
    refine ⟨?_, ?_⟩
    · intro t; exact measurable_const
    · intro t ω y; exact hc
  have h_int : ∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ := by
    intro f hf
    dsimp [μ]
    -- integral w.r.t. dirac is evaluation, and the integrand doesn't depend on ω
    have h_eq : (fun ω => regret K f (fun t => pol t ω) n) = fun _ => regret K f (fun t => pol t ()) n := by
      ext ω; dsimp [pol]
    rw [h_eq]
    exact MeasureTheory.integrable_const _
  set r := sSup ((fun f => expReg K μ pol f n) '' Advs K n) with hr_def
  have hr_mem : r ∈ {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d), IsLearner K pol ∧
      (∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ) ∧
      r = sSup ((fun f => expReg K μ pol f n) '' Advs K n)} := by
    refine ⟨Ω, inferInstance, μ, hμ_prob, pol, hpol_learner, h_int, ?_⟩
    rfl
  have hr_le_n : r ≤ (n : ℝ) := by
    rw [hr_def]
    by_cases h_empty : ((fun f => expReg K μ pol f n) '' Advs K n).Nonempty
    · refine csSup_le h_empty ?_
      rintro _ ⟨f, hf, rfl⟩
      dsimp [expReg, μ]
      rw [integral_dirac]
      dsimp [pol]
      -- Now: regret K f (fun t => fun _ => c) n ≤ n
      unfold regret
      have h_sum_le_n : (∑ t ∈ Finset.range n, f t c) ≤ (n : ℝ) := by
        calc
          (∑ t ∈ Finset.range n, f t c) ≤ (∑ t ∈ Finset.range n, (1 : ℝ)) :=
            Finset.sum_le_sum fun t ht => by
              have h_adm := hf t (Finset.mem_range.1 ht)
              exact (h_adm.2 c hc).2
          _ = (n : ℝ) := by simp
      have h_sInf_nonneg : 0 ≤ sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) := by
        have h_img_nonempty : ((fun x => ∑ t ∈ Finset.range n, f t x) '' K).Nonempty :=
          ⟨∑ t ∈ Finset.range n, f t c, c, hc, rfl⟩
        refine le_csInf h_img_nonempty ?_
        rintro _ ⟨x, hx, rfl⟩
        refine Finset.sum_nonneg fun t ht => ?_
        have h_adm := hf t (Finset.mem_range.1 ht)
        exact (h_adm.2 x hx).1
      linarith
    · have h_empty' : ((fun f => expReg K μ pol f n) '' Advs K n) = ∅ :=
        Set.not_nonempty_iff_eq_empty.1 h_empty
      rw [h_empty', Real.sSup_empty]
      exact Nat.cast_nonneg _
  by_cases h_bdd : BddBelow {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d), IsLearner K pol ∧
      (∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ) ∧
      r = sSup ((fun f => expReg K μ pol f n) '' Advs K n)}
  · have h_sInf_le_r : sInf {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d), IsLearner K pol ∧
        (∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ) ∧
        r = sSup ((fun f => expReg K μ pol f n) '' Advs K n)} ≤ r :=
      csInf_le h_bdd hr_mem
    unfold minimaxRegret
    linarith
  · have h_sInf : sInf {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d), IsLearner K pol ∧
        (∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ) ∧
        r = sSup ((fun f => expReg K μ pol f n) '' Advs K n)} = 0 :=
      Real.sInf_of_not_bddBelow h_bdd
    unfold minimaxRegret
    rw [h_sInf]
    exact Nat.cast_nonneg _

theorem AdversarialBco.kl_bin_ge (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  -- Define the binary relative entropy (klBerReal) and its gap
  let klBerReal (p q : ℝ) : ℝ := p * (Real.log p - Real.log q) + (1 - p) * (Real.log (1 - p) - Real.log (1 - q))
  let klBerRealGap (p q : ℝ) : ℝ := klBerReal p q - 2 * (p - q) ^ 2
  have klBerRealGap_self (p : ℝ) : klBerRealGap p p = 0 := by
    simp [klBerRealGap, klBerReal]
  have klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
    simp [klBerReal, add_comm]
  -- Derivative of klBerRealGap p in the second argument
  have hasDerivAt_klBerRealGap {p q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
      HasDerivAt (klBerRealGap p) ((q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) q := by
    have hq1' : 1 - q ≠ 0 := sub_ne_zero.2 hq1.symm
    have h1 : HasDerivAt (fun x : ℝ => p * (Real.log p - Real.log x)) (p * (-q⁻¹)) q :=
      ((hasDerivAt_log hq0).const_sub (Real.log p)).const_mul p
    have h2 : HasDerivAt (fun x : ℝ => (1 - p) * (Real.log (1 - p) - Real.log (1 - x)))
        ((1 - p) * (-(-1 / (1 - q)))) q :=
      ((((hasDerivAt_id' (x := q)).const_sub 1).log hq1').const_sub (Real.log (1 - p))).const_mul (1 - p)
    have h3 := (((hasDerivAt_id' (x := q)).const_sub p).pow 2).const_mul 2
    refine ((h1.add h2).sub h3).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp [hq0, hq1']
    ring
  -- klBerRealGap p is continuous on [p, 1) for 0 ≤ p
  have continuousOn_klBerRealGap {p : ℝ} (hp : 0 ≤ p) :
      ContinuousOn (klBerRealGap p) (Set.Ico p 1) := by
    have h1 : ContinuousOn (fun x : ℝ => p * (Real.log p - Real.log x)) (Set.Ico p 1) := by
      rcases hp.eq_or_lt with rfl | hp'
      · simp [continuousOn_const]
      · refine continuousOn_const.mul (continuousOn_const.sub ?_)
        refine (continuousOn_log.mono fun x hx => ?_)
        exact (hp'.trans_le hx.1).ne'
    have h2 : ContinuousOn (fun x : ℝ => (1 - p) * (Real.log (1 - p) - Real.log (1 - x))) (Set.Ico p 1) :=
      continuousOn_const.mul (continuousOn_const.sub
        ((continuousOn_const.sub continuousOn_id).log fun x hx => (sub_pos.2 hx.2).ne'))
    exact (h1.add h2).sub (by fun_prop)
  -- Binary Pinsker inequality when p ≤ q
  have sq_sub_le_klBerReal_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q < 1) :
      2 * (p - q) ^ 2 ≤ klBerReal p q := by
    rcases (hp.trans hpq).eq_or_lt with rfl | hq0
    · -- p = 0 case
      have hp0 : p = 0 := le_antisymm hpq hp
      subst hp0
      simp [klBerReal]
    have hmono : MonotoneOn (klBerRealGap p) (Set.Ico p 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico p 1) (continuousOn_klBerRealGap hp)
        (f' := fun x : ℝ => (x - p) * (1 - 2 * x) ^ 2 / (x * (1 - x))) (fun x hx => ?_) fun x hx => ?_
      · rw [interior_Ico] at hx ⊢
        exact (hasDerivAt_klBerRealGap (hp.trans_lt hx.1).ne' hx.2.ne).hasDerivWithinAt
      · rw [interior_Ico] at hx
        refine div_nonneg (mul_nonneg (sub_nonneg.2 hx.1.le) (sq_nonneg _))
          (mul_pos (hp.trans_lt hx.1) (sub_pos.2 hx.2)).le
    have h := hmono ⟨le_rfl, hpq.trans_lt hq1⟩ ⟨hpq, hq1⟩ hpq
    rw [klBerRealGap_self] at h
    unfold klBerRealGap at h
    linarith
  -- Relate klBerReal to the log expression in the goal
  have klBerReal_eq_log_div (p q : ℝ) (hq0 : q ≠ 0) (hq1' : 1 - q ≠ 0) :
      klBerReal p q = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
    unfold klBerReal
    by_cases hp0 : p = 0
    · subst p; simp
    · by_cases hp1 : p = 1
      · subst p; simp
      · have hp0' : p ≠ 0 := hp0
        have hp1' : 1 - p ≠ 0 := by
          intro h; apply hp1; linarith
        rw [Real.log_div hp0' hq0, Real.log_div hp1' hq1']
  -- Main inequality
  rcases le_or_gt a b with hpq | hpq
  · -- a ≤ b case
    have h := sq_sub_le_klBerReal_of_le ha0 hpq hb1
    rw [klBerReal_eq_log_div a b hb0.ne' (by linarith)] at h
    exact h
  · -- a > b case: use symmetry
    have h := sq_sub_le_klBerReal_of_le (sub_nonneg.2 ha1) (sub_le_sub_left hpq.le 1) (by linarith)
    -- h : 2 * ((1 - a) - (1 - b)) ^ 2 ≤ klBerReal (1 - a) (1 - b)
    -- (1-a)-(1-b) = b-a, so LHS is 2*(b-a)^2
    -- klBerReal (1-a) (1-b) = klBerReal a b by symmetry
    rw [show ((1 : ℝ) - a) - ((1 : ℝ) - b) = b - a by ring] at h
    rw [klBerReal_one_sub a b] at h
    -- h : 2 * (b - a) ^ 2 ≤ klBerReal a b
    rw [klBerReal_eq_log_div a b hb0.ne' (by linarith)] at h
    -- h : 2 * (b - a) ^ 2 ≤ a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))
    have hsq : (a - b) ^ 2 = (b - a) ^ 2 := by ring
    rw [hsq]
    exact h

open Set in
theorem AdversarialBco.card_le_of_separated {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Bornology.IsBounded K) (C : Finset (EuclideanSpace ℝ (Fin d))) (hCK : ↑C ⊆ K) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) :
    (C.card : ℝ) ≤ (1 + 2 * Metric.diam K / ε) ^ d := by
  -- If C is empty, the inequality is trivial since LHS = 0 and RHS ≥ 0
  by_cases hCempty : C.Nonempty
  · -- C is nonempty: pick a reference point x0
    obtain ⟨x0, hx0⟩ := hCempty
    set D := Metric.diam K with hDdef
    have hDnonneg : 0 ≤ D := Metric.diam_nonneg
    have hε2pos : 0 < ε / 2 := by linarith
    have hball01_pos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      have hpos_ennreal := Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin d))) 0
        (by norm_num : (0 : ℝ) < 1)
      have hne_top : (volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball 0 1) ≠ ⊤ :=
        ne_of_lt MeasureTheory.measure_ball_lt_top
      rw [Measure.real_def]
      exact ENNReal.toReal_pos (ne_of_gt hpos_ennreal) hne_top
    -- The balls B(x, ε/2) for x ∈ C are pairwise disjoint
    have hpairwise_disjoint : ((C : Set (EuclideanSpace ℝ (Fin d))).PairwiseDisjoint fun x => Metric.ball x (ε / 2)) := by
      intro x hx y hy hne
      have hxy := hsep x hx y hy hne
      have : (ε / 2) + (ε / 2) ≤ dist x y := by linarith
      exact Metric.ball_disjoint_ball this
    -- Each ball B(x, ε/2) is contained in B(x0, D + ε/2)
    have hball_subset : ∀ x ∈ C, Metric.ball x (ε / 2) ⊆ Metric.ball x0 (D + ε / 2) := by
      intro x hx
      have hxK : x ∈ K := hCK (by exact Finset.mem_coe.mpr hx)
      have hx0K : x0 ∈ K := hCK (by exact Finset.mem_coe.mpr hx0)
      have hdist := Metric.dist_le_diam_of_mem hK hxK hx0K
      have hineq : (ε / 2) + dist x x0 ≤ D + ε / 2 := by linarith
      exact Metric.ball_subset_ball' hineq
    -- The union is also contained
    have hunion_subset : (⋃ x ∈ C, Metric.ball x (ε / 2)) ⊆ Metric.ball x0 (D + ε / 2) := by
      rw [Set.iUnion₂_subset_iff]
      intro x hx
      exact hball_subset x hx
    -- Each ball is measurable
    have hmeasurable : ∀ x ∈ C, MeasurableSet (Metric.ball x (ε / 2)) := by
      intro x hx
      exact Metric.isOpen_ball.measurableSet
    -- Each ball has finite measure
    have hball_fin : ∀ x ∈ C, (volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball x (ε / 2)) ≠ ⊤ := by
      intro x hx
      have h_meas : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
        infer_instance
      have h_proper : ProperSpace (EuclideanSpace ℝ (Fin d)) := by
        infer_instance
      have := MeasureTheory.measure_ball_lt_top (μ := volume) (x := x) (r := ε / 2)
      exact ne_of_lt this
    -- Using measureReal_biUnion_finset for disjoint balls
    have hmeasure_union : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (⋃ x ∈ C, Metric.ball x (ε / 2)) =
        ∑ x ∈ C, (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x (ε / 2)) := by
      refine MeasureTheory.measureReal_biUnion_finset hpairwise_disjoint hmeasurable ?_
      intro x hx
      exact hball_fin x hx
    -- Formula for volume.real of a ball: μ.real (ball x r) = r^finrank * μ.real (ball 0 1)
    have hball_volume : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
        (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x r) =
        r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      intro x r hrpos
      have hrnonneg : 0 ≤ r := by linarith
      have hformula := MeasureTheory.Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin d)))
        x hrpos
      have h_nonneg_pow : 0 ≤ r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) :=
        pow_nonneg hrnonneg _
      calc
        (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x r) =
            ((volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball x r)).toReal := by rw [Measure.real_def]
        _ = (ENNReal.ofReal (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) *
            (volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball 0 1)).toReal := by rw [hformula]
        _ = (ENNReal.ofReal (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))).toReal *
            ((volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball 0 1)).toReal := by
          rw [ENNReal.toReal_mul]
        _ = (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) *
            ((volume : Measure (EuclideanSpace ℝ (Fin d))) (Metric.ball 0 1)).toReal := by
          rw [ENNReal.toReal_ofReal h_nonneg_pow]
        _ = (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) *
            (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by rw [Measure.real_def]
    -- finrank ℝ (EuclideanSpace ℝ (Fin d)) = d
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    have hball_volume' : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
        (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x r) =
        r ^ d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      intro x r hrpos
      rw [hball_volume x r hrpos, hfinrank]
    -- Apply the formula to each ball in C
    have hsum_volume : ∑ x ∈ C, (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x (ε / 2)) =
        ((ε / 2) ^ d) * (C.card : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      simp_rw [hball_volume' _ (ε / 2) hε2pos]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    -- Now combine everything
    have hmeasure_union_val : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (⋃ x ∈ C, Metric.ball x (ε / 2)) =
        ((ε / 2) ^ d) * (C.card : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      rw [hmeasure_union, hsum_volume]
    -- Volume of the big ball: μ.real (ball x0 (D + ε/2)) = (D + ε/2)^d * μ.real (ball 0 1)
    have hball_big : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x0 (D + ε / 2)) =
        (D + ε / 2) ^ d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      have hpos : 0 < D + ε / 2 := by linarith
      rw [hball_volume' x0 (D + ε / 2) hpos]
    -- By measure monotonicity
    have hmeasure_mono : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (⋃ x ∈ C, Metric.ball x (ε / 2)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball x0 (D + ε / 2)) := by
      refine MeasureTheory.measureReal_mono hunion_subset ?_
      have h_meas : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
        infer_instance
      have h_proper : ProperSpace (EuclideanSpace ℝ (Fin d)) := by
        infer_instance
      have := MeasureTheory.measure_ball_lt_top (μ := volume) (x := x0) (r := D + ε / 2)
      exact ne_of_lt this
    -- Combine all inequalities
    rw [hmeasure_union_val, hball_big] at hmeasure_mono
    -- Now hmeasure_mono: ((ε/2)^d) * (C.card : ℝ) * V ≤ (D + ε/2)^d * V  where V = volume.real (ball 0 1)
    set V := (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) with hVdef
    have hVpos : 0 < V := hball01_pos
    -- Cancel V (multiply both sides by V⁻¹)
    have hineq_div : ((ε / 2) ^ d) * (C.card : ℝ) ≤ (D + ε / 2) ^ d := by
      nlinarith
    -- Now we have: (C.card : ℝ) * (ε/2)^d ≤ (D + ε/2)^d
    -- Divide both sides by (ε/2)^d (which is positive)
    have hε2pow_pos : 0 < (ε / 2) ^ d := pow_pos hε2pos d
    have hfinal : (C.card : ℝ) ≤ ((D + ε / 2) / (ε / 2)) ^ d := by
      calc
        (C.card : ℝ) = (((ε / 2) ^ d) * (C.card : ℝ)) / ((ε / 2) ^ d) := by
          field_simp [ne_of_gt hε2pow_pos]
        _ ≤ ((D + ε / 2) ^ d) / ((ε / 2) ^ d) :=
          (div_le_div_iff_of_pos_right hε2pow_pos).mpr hineq_div
        _ = ((D + ε / 2) / (ε / 2)) ^ d := by rw [← div_pow]
    -- Simplify the RHS: ((D + ε/2) / (ε/2)) = 1 + 2*D/ε
    have hRHS : ((D + ε / 2) / (ε / 2)) ^ d = (1 + 2 * D / ε) ^ d := by
      have h_eq : (D + ε / 2) / (ε / 2) = 1 + 2 * D / ε := by
        field_simp [ne_of_gt hε]
        ring
      rw [h_eq]
    rw [hRHS] at hfinal
    -- Recall D = Metric.diam K
    rw [hDdef] at hfinal
    exact hfinal
  · -- C is empty
    have hCcard0 : C.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hCempty)
    have hnonneg : 0 ≤ (1 + 2 * Metric.diam K / ε) ^ d := by
      have hbase : 0 ≤ 1 + 2 * Metric.diam K / ε := by
        have : 0 ≤ Metric.diam K := Metric.diam_nonneg
        positivity
      exact pow_nonneg hbase d
    simp [hCcard0, hnonneg]

theorem AdversarialBco.sub_le_of_convex_bdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (f : F → ℝ) (hf : ConvexOn ℝ K f) (h01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (hr : 0 < r) (x y : F)
    (hx : Metric.closedBall x r ⊆ K) (hy : y ∈ K) :
    f x - f y ≤ ‖x - y‖ / r := by
  by_cases hxy : x = y
  · subst hxy
    simp [sub_self, norm_zero]
  · have hδ_pos : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hxy
    set δ := ‖x - y‖ with hδ_def
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    set z := x + (r / δ) • (x - y) with hz_def
    have hz_mem_ball : z ∈ Metric.closedBall x r := by
      rw [mem_closedBall_iff_norm]
      dsimp [z]
      have h : (x + (r / δ) • (x - y)) - x = (r / δ) • (x - y) := by abel
      rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hδ_pos)]
      field_simp [hδ_pos.ne']
      rw [hδ_def]
    have hx_mem_K : x ∈ K := by
      have hx_mem_ball : x ∈ Metric.closedBall x r :=
        Metric.mem_closedBall_self (le_of_lt hr)
      exact hx hx_mem_ball
    have hz_mem_K : z ∈ K := hx hz_mem_ball
    have h01z : f z ∈ Set.Icc (0 : ℝ) 1 := h01 z hz_mem_K
    have h01y : f y ∈ Set.Icc (0 : ℝ) 1 := h01 y hy
    rcases h01z with ⟨hz_low, hz_high⟩
    rcases h01y with ⟨hy_low, hy_high⟩
    set t := δ / (δ + r) with ht_def
    have ht_nonneg : 0 ≤ t := div_nonneg hδ_nonneg (by positivity)
    have h_one_minus_t_nonneg : 0 ≤ 1 - t := by
      have h_t_le_one : t ≤ 1 := by
        refine (div_le_one ?_).mpr ?_
        · positivity
        · linarith
      linarith
    have ht_add_one_minus_t : t + (1 - t) = 1 := by ring
    have h_coeff_eq1 : (r / (δ + r)) = (δ / (δ + r)) * (r / δ) := by
      field_simp [hδ_pos.ne', show δ + r ≠ 0 from by positivity]
    have h_coeff_eq2 : (r / (δ + r)) = 1 - δ / (δ + r) := by
      field_simp [show δ + r ≠ 0 from by positivity]
      ring
    have hx_eq : x = t • z + (1 - t) • y := by
      dsimp [t, z]
      calc
        x = ((δ + r) / (δ + r)) • x := by
          field_simp [show δ + r ≠ 0 from by positivity]
          simp
        _ = ((δ / (δ + r)) + (r / (δ + r))) • x := by rw [add_div]
        _ = (δ / (δ + r)) • x + (r / (δ + r)) • x := by rw [add_smul]
        _ = (δ / (δ + r)) • x + (r / (δ + r)) • ((x - y) + y) := by simp
        _ = (δ / (δ + r)) • x + ((r / (δ + r)) • (x - y) + (r / (δ + r)) • y) := by rw [smul_add]
        _ = ((δ / (δ + r)) • x + (r / (δ + r)) • (x - y)) + (r / (δ + r)) • y := by abel
        _ = ((δ / (δ + r)) • x + ((δ / (δ + r)) * (r / δ)) • (x - y)) + (r / (δ + r)) • y := by
          rw [h_coeff_eq1]
        _ = ((δ / (δ + r)) • x + (δ / (δ + r)) • ((r / δ) • (x - y))) + (r / (δ + r)) • y := by
          rw [smul_smul]
        _ = ((δ / (δ + r)) • x + (δ / (δ + r)) • ((r / δ) • (x - y))) + (1 - δ / (δ + r)) • y := by
          rw [h_coeff_eq2]
        _ = (δ / (δ + r)) • (x + (r / δ) • (x - y)) + (1 - δ / (δ + r)) • y := by rw [smul_add]
    have h_convex : f x ≤ t * f z + (1 - t) * f y := by
      rw [hx_eq]
      have h := hf.2 (x := z) (y := y) hz_mem_K hy ht_nonneg h_one_minus_t_nonneg ht_add_one_minus_t
      simpa [smul_eq_mul] using h
    have h_ineq : f x - f y ≤ t := by
      calc
        f x - f y ≤ (t * f z + (1 - t) * f y) - f y := by linarith
        _ = t * (f z - f y) := by ring
        _ ≤ t * 1 := by
          nlinarith
        _ = t := by simp
    calc
      f x - f y ≤ t := h_ineq
      _ = δ / (δ + r) := rfl
      _ ≤ δ / r :=
        div_le_div_of_nonneg_left hδ_nonneg hr (by linarith)
      _ = ‖x - y‖ / r := by rw [hδ_def]

theorem AdversarialBco.closedBall_shrink_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hK : Convex ℝ K) (c : F) (hc : Metric.closedBall c 1 ⊆ K) (x : F) (hx : x ∈ K) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    Metric.closedBall ((1 - s) • x + s • c) s ⊆ K := by
  by_cases hs0' : s = 0
  · -- s = 0 case: closedBall ((1-0)•x + 0•c) 0 = {x}
    have hball : Metric.closedBall ((1 - s) • x + s • c) s = {x} := by
      rw [hs0']
      simp [Metric.closedBall_zero]
    rw [hball]
    exact Set.singleton_subset_iff.mpr hx
  · -- s > 0 case
    have hs_pos : 0 < s := by
      by_contra! H
      -- H: s ≤ 0, but hs0: 0 ≤ s, so s = 0, contradiction
      have heq : s = 0 := le_antisymm H hs0
      exact hs0' heq
    intro z hz
    have hz_norm' : ‖((1 - s) • x + s • c) - z‖ ≤ s := by
      rwa [mem_closedBall_iff_norm'] at hz
    have hz_norm : ‖z - ((1 - s) • x + s • c)‖ ≤ s := by
      rw [norm_sub_rev]
      exact hz_norm'
    set u := s⁻¹ • (z - (1 - s) • x - s • c) with hu_def
    have hu_norm : ‖u‖ ≤ 1 := by
      rw [hu_def]
      calc
        ‖s⁻¹ • (z - (1 - s) • x - s • c)‖ = ‖s⁻¹‖ * ‖z - (1 - s) • x - s • c‖ := norm_smul _ _
        _ = |s⁻¹| * ‖z - (1 - s) • x - s • c‖ := by rw [Real.norm_eq_abs]
        _ = s⁻¹ * ‖z - (1 - s) • x - s • c‖ := by
          rw [abs_of_nonneg (inv_nonneg.mpr hs0)]
        _ ≤ s⁻¹ * s := by
          -- need ‖z - (1 - s) • x - s • c‖ ≤ s
          -- but we have ‖z - ((1 - s) • x + s • c)‖ ≤ s
          -- note: z - (1 - s) • x - s • c = z - ((1 - s) • x + s • c)
          have : z - (1 - s) • x - s • c = z - ((1 - s) • x + s • c) := by abel
          rw [this]
          exact mul_le_mul_of_nonneg_left hz_norm (inv_nonneg.mpr hs0)
        _ = 1 := by field_simp [hs0']
    have hcu : c + u ∈ Metric.closedBall c 1 := by
      rw [mem_closedBall_iff_norm']
      calc
        ‖c - (c + u)‖ = ‖-u‖ := by
          simp
        _ = ‖u‖ := norm_neg _
        _ ≤ 1 := hu_norm
    have hcuK : c + u ∈ K := hc hcu
    have hsmu_eq : s • u = z - (1 - s) • x - s • c := by
      rw [hu_def]
      simp [smul_smul, hs0']
    have hz_eq : z = (1 - s) • x + s • (c + u) := by
      calc
        z = ((1 - s) • x + s • c) + (z - (1 - s) • x - s • c) := by abel
        _ = ((1 - s) • x + s • c) + s • u := by rw [hsmu_eq]
        _ = (1 - s) • x + s • c + s • u := rfl
        _ = (1 - s) • x + s • (c + u) := by
          simp [smul_add, add_assoc]
    rw [hz_eq]
    -- Now use Convex.add_smul_mem
    have h_comb : (1 - s) • x + s • (c + u) ∈ K := by
      -- We need to write this as x + s • ((c + u) - x)
      have : (1 - s) • x + s • (c + u) = x + s • ((c + u) - x) := by
        calc
          (1 - s) • x + s • (c + u) = (x - s • x) + s • (c + u) := by
            rw [sub_smul, one_smul]
          _ = x + (s • (c + u) - s • x) := by
            abel
          _ = x + s • ((c + u) - x) := by rw [smul_sub]
      rw [this]
      refine hK.add_smul_mem hx ?_ (by
        refine ⟨by linarith, by linarith⟩)
      -- need x + ((c + u) - x) ∈ K, i.e., c + u ∈ K
      simpa [add_sub_cancel_right] using hcuK
    exact h_comb

theorem AdversarialBco.convex_comb_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (f : F → ℝ) (hf : ConvexOn ℝ K f) (h01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (x c : F) (hx : x ∈ K) (hc : c ∈ K)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    f ((1 - s) • x + s • c) ≤ f x + s := by
  have hfx := h01 x hx
  have hfc := h01 c hc
  have hfx0 : 0 ≤ f x := hfx.1
  have hfx1 : f x ≤ 1 := hfx.2
  have hfc0 : 0 ≤ f c := hfc.1
  have hfc1 : f c ≤ 1 := hfc.2
  rcases hf with ⟨hconvK, hconv⟩
  have hconv' := hconv hx hc (a := 1 - s) (b := s) (by linarith) hs0 (by ring)
  have hfinal : (1 - s) * f x + s * f c ≤ f x + s := by
    nlinarith
  -- hconv' gives: f ((1 - s) • x + s • c) ≤ (1 - s) • f x + s • f c
  -- but (1 - s) • f x = (1 - s) * f x and s • f c = s * f c since ℝ acts on ℝ by multiplication
  -- so we can rewrite
  simpa [smul_eq_mul] using hconv'.trans hfinal

theorem AdversarialBco.convexOn_infDist {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hK : Convex ℝ K) :
    ConvexOn ℝ Set.univ (fun x => Metric.infDist x K) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hadd
  rcases em (K.Nonempty) with (hKne | hKempty)
  · -- K is nonempty
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hax : Metric.infDist x K < Metric.infDist x K + ε := by linarith
    have hby : Metric.infDist y K < Metric.infDist y K + ε := by linarith
    rcases ((Metric.infDist_lt_iff hKne).mp hax) with ⟨u, hu, hxu⟩
    rcases ((Metric.infDist_lt_iff hKne).mp hby) with ⟨v, hv, hyv⟩
    have hmem : a • u + b • v ∈ segment ℝ u v := by
      rw [segment_eq_image₂]
      refine ⟨(a, b), ⟨ha.le, hb.le, hadd⟩, ?_⟩
      rfl
    have havg : a • u + b • v ∈ K :=
      hK.segment_subset hu hv hmem
    have hsub : (a • x + b • y) - (a • u + b • v) = a • (x - u) + b • (y - v) := by
      calc
        (a • x + b • y) - (a • u + b • v) = (a • x - a • u) + (b • y - b • v) := by abel
        _ = a • (x - u) + b • (y - v) := by simp [smul_sub]
    calc
      Metric.infDist (a • x + b • y) K ≤ dist (a • x + b • y) (a • u + b • v) :=
        Metric.infDist_le_dist_of_mem havg
      _ = ‖(a • x + b • y) - (a • u + b • v)‖ := by rw [dist_eq_norm]
      _ = ‖a • (x - u) + b • (y - v)‖ := by rw [hsub]
      _ ≤ ‖a • (x - u)‖ + ‖b • (y - v)‖ := norm_add_le _ _
      _ = a * ‖x - u‖ + b * ‖y - v‖ := by
        simp [norm_smul_of_nonneg ha.le, norm_smul_of_nonneg hb.le]
      _ = a * dist x u + b * dist y v := by simp [dist_eq_norm]
      _ < a * (Metric.infDist x K + ε) + b * (Metric.infDist y K + ε) := by
        nlinarith
      _ = a * Metric.infDist x K + b * Metric.infDist y K + (a + b) * ε := by ring
      _ = a * Metric.infDist x K + b * Metric.infDist y K + ε := by
        rw [hadd, one_mul]
  · -- K is empty: infDist is 0, constant function is convex
    have hKempty' : K = ∅ := (Set.not_nonempty_iff_eq_empty.mp hKempty)
    have h_empty : ∀ x, Metric.infDist x K = (0 : ℝ) := by
      intro x; simp [hKempty', Metric.infDist_empty]
    simp [h_empty]

theorem AdversarialBco.lipExt_eq {F : Type*} [NormedAddCommGroup F] (K : Set F) (f : F → ℝ) (L : ℝ)
    (hfl : ∀ x ∈ K, ∀ y ∈ K, f x ≤ f y + L * dist x y) (x : F) (hx : x ∈ K) :
    AdversarialBco.lipExt K f L x = f x := by
  have hmem : f x ∈ ((fun y => f y + L * dist x y) '' K) := by
    refine ⟨x, hx, ?_⟩
    simp [dist_self]
  have hlower : f x ∈ lowerBounds ((fun y => f y + L * dist x y) '' K) := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hfl x hx y hy
  rw [AdversarialBco.lipExt]
  exact IsLeast.csInf_eq ⟨hmem, hlower⟩

theorem AdversarialBco.lipExt_le {F : Type*} [NormedAddCommGroup F] (K : Set F) (hK : K.Nonempty) (f : F → ℝ)
    (hfb : BddBelow (f '' K)) (L : ℝ) (hL : 0 ≤ L) (x x' : F) :
    AdversarialBco.lipExt K f L x ≤ AdversarialBco.lipExt K f L x' + L * dist x x' := by
  set Sx := ((fun y => f y + L * dist x y) '' K) with hSx
  set Sx' := ((fun y => f y + L * dist x' y) '' K) with hSx'
  have hdefx : AdversarialBco.lipExt K f L x = sInf Sx := rfl
  have hdefx' : AdversarialBco.lipExt K f L x' = sInf Sx' := rfl
  have h_nonempty_Sx : Sx.Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨f y + L * dist x y, y, hy, rfl⟩
  have h_nonempty_Sx' : Sx'.Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨f y + L * dist x' y, y, hy, rfl⟩
  have h_bddBelow_Sx : BddBelow Sx := by
    rcases hfb with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hb_y : b ≤ f y := hb (Set.mem_image_of_mem f hy)
    have h_nonneg : 0 ≤ L * dist x y := mul_nonneg hL dist_nonneg
    linarith
  have h_lower : ∀ y ∈ K, AdversarialBco.lipExt K f L x ≤ f y + L * dist x y := by
    intro y hy
    rw [hdefx]
    apply csInf_le h_bddBelow_Sx
    exact ⟨y, hy, rfl⟩
  have h_bound : ∀ y ∈ K, AdversarialBco.lipExt K f L x - L * dist x x' ≤ f y + L * dist x' y := by
    intro y hy
    have h1 : AdversarialBco.lipExt K f L x ≤ f y + L * dist x y := h_lower y hy
    have h_tri : dist x y ≤ dist x' y + dist x x' := by
      calc
        dist x y ≤ dist x x' + dist x' y := dist_triangle _ _ _
        _ = dist x' y + dist x x' := add_comm _ _
    have h_mul : L * dist x y ≤ L * (dist x' y + dist x x') :=
      mul_le_mul_of_nonneg_left h_tri hL
    have h2 : f y + L * dist x y ≤ f y + L * dist x' y + L * dist x x' := by
      linarith
    linarith
  have h_lower_Sx' : AdversarialBco.lipExt K f L x - L * dist x x' ≤ AdversarialBco.lipExt K f L x' := by
    rw [hdefx']
    apply le_csInf h_nonempty_Sx'
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact h_bound y hy
  linarith

open scoped Pointwise in
theorem AdversarialBco.lipExt_convex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hKc : Convex ℝ K) (hK : K.Nonempty) (f : F → ℝ) (hf : ConvexOn ℝ K f) (hfb : BddBelow (f '' K)) (L : ℝ)
    (hL : 0 ≤ L) :
    ConvexOn ℝ Set.univ (AdversarialBco.lipExt K f L) := by
  rcases hf with ⟨_, hf'⟩
  refine ⟨convex_univ, ?_⟩
  intro x1 _ x2 _ a b ha hb hab
  dsimp [AdversarialBco.lipExt]
  set S1 := ((fun y => f y + L * dist x1 y) '' K)
  set S2 := ((fun y => f y + L * dist x2 y) '' K)
  set S := ((fun y => f y + L * dist (a • x1 + b • x2) y) '' K)
  have hS_ne : S.Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨f y + L * dist (a • x1 + b • x2) y, y, hy, rfl⟩
  have hS1_ne : S1.Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨f y + L * dist x1 y, y, hy, rfl⟩
  have hS2_ne : S2.Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨f y + L * dist x2 y, y, hy, rfl⟩
  have hS_bdd : BddBelow S := by
    rcases hfb with ⟨lb, hlb⟩
    refine ⟨lb, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hfy : lb ≤ f y := hlb (Set.mem_image_of_mem f hy)
    have hsum : lb ≤ f y + L * dist (a • x1 + b • x2) y :=
      calc
        lb ≤ f y := hfy
        _ ≤ f y + L * dist (a • x1 + b • x2) y :=
          le_add_of_nonneg_right (mul_nonneg hL dist_nonneg)
    exact hsum
  have hS1_bdd : BddBelow S1 := by
    rcases hfb with ⟨lb, hlb⟩
    refine ⟨lb, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hfy : lb ≤ f y := hlb (Set.mem_image_of_mem f hy)
    have hsum : lb ≤ f y + L * dist x1 y :=
      calc
        lb ≤ f y := hfy
        _ ≤ f y + L * dist x1 y :=
          le_add_of_nonneg_right (mul_nonneg hL dist_nonneg)
    exact hsum
  have hS2_bdd : BddBelow S2 := by
    rcases hfb with ⟨lb, hlb⟩
    refine ⟨lb, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hfy : lb ≤ f y := hlb (Set.mem_image_of_mem f hy)
    have hsum : lb ≤ f y + L * dist x2 y :=
      calc
        lb ≤ f y := hfy
        _ ≤ f y + L * dist x2 y :=
          le_add_of_nonneg_right (mul_nonneg hL dist_nonneg)
    exact hsum
  have h_dist_ineq : ∀ y1 ∈ K, ∀ y2 ∈ K,
      dist (a • x1 + b • x2) (a • y1 + b • y2) ≤ a * dist x1 y1 + b * dist x2 y2 := by
    intro y1 hy1 y2 hy2
    calc
      dist (a • x1 + b • x2) (a • y1 + b • y2) = ‖(a • x1 + b • x2) - (a • y1 + b • y2)‖ := by
        rw [dist_eq_norm]
      _ = ‖(a • x1 - a • y1) + (b • x2 - b • y2)‖ := by abel_nf
      _ = ‖a • (x1 - y1) + b • (x2 - y2)‖ := by simp [smul_sub]
      _ ≤ ‖a • (x1 - y1)‖ + ‖b • (x2 - y2)‖ := norm_add_le _ _
      _ = |a| * ‖x1 - y1‖ + |b| * ‖x2 - y2‖ := by simp [norm_smul]
      _ = a * ‖x1 - y1‖ + b * ‖x2 - y2‖ := by simp [abs_of_nonneg ha, abs_of_nonneg hb]
      _ = a * dist x1 y1 + b * dist x2 y2 := by simp [dist_eq_norm]
  have h_ineq : ∀ y1 ∈ K, ∀ y2 ∈ K,
      f (a • y1 + b • y2) + L * dist (a • x1 + b • x2) (a • y1 + b • y2) ≤
      a * (f y1 + L * dist x1 y1) + b * (f y2 + L * dist x2 y2) := by
    intro y1 hy1 y2 hy2
    have hy : a • y1 + b • y2 ∈ K := hKc hy1 hy2 ha hb hab
    have hfy : f (a • y1 + b • y2) ≤ a * f y1 + b * f y2 :=
      hf' hy1 hy2 ha hb hab
    have hdist := h_dist_ineq y1 hy1 y2 hy2
    have hLdist : L * dist (a • x1 + b • x2) (a • y1 + b • y2) ≤ L * (a * dist x1 y1 + b * dist x2 y2) :=
      mul_le_mul_of_nonneg_left hdist hL
    nlinarith
  by_cases ha0 : a = 0
  · -- a = 0, so b = 1
    have hb1 : b = 1 := by linarith
    subst ha0; subst hb1
    simp [S, S2]
  · -- a > 0
    have ha_pos : 0 < a := by
      by_contra! h
      have : a = 0 := le_antisymm h ha
      exact ha0 this
    have h_main : ∀ y2 ∈ K, sInf S ≤ a * sInf S1 + b * (f y2 + L * dist x2 y2) := by
      intro y2 hy2
      set t2 := f y2 + L * dist x2 y2
      have h_forall_t1 : ∀ t1 ∈ S1, sInf S - b * t2 ≤ a * t1 := by
        intro t1 ht1
        rcases ht1 with ⟨y1, hy1, rfl⟩
        have hS_le : sInf S ≤ f (a • y1 + b • y2) + L * dist (a • x1 + b • x2) (a • y1 + b • y2) := by
          apply csInf_le hS_bdd
          exact ⟨a • y1 + b • y2, hKc hy1 hy2 ha hb hab, rfl⟩
        have h_ineq' := h_ineq y1 hy1 y2 hy2
        nlinarith
      have h_lower : sInf S - b * t2 ≤ sInf (a • S1) := by
        apply le_csInf
        · rcases hS1_ne with ⟨t1, ht1⟩
          exact ⟨a * t1, t1, ht1, rfl⟩
        · intro z hz
          rcases hz with ⟨t1, ht1, rfl⟩
          exact h_forall_t1 t1 ht1
      have h_sInf_aS1 : sInf (a • S1) = a * sInf S1 :=
        Real.sInf_smul_of_nonneg ha S1
      rw [h_sInf_aS1] at h_lower
      nlinarith
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      subst ha1; subst hb0
      simp [S, S1]
    · have hb_pos : 0 < b := by
        by_contra! h
        have : b = 0 := le_antisymm h hb
        exact hb0 this
      have h_div : (sInf S - a * sInf S1) / b ≤ sInf S2 := by
        apply le_csInf hS2_ne
        intro t2 ht2
        rcases ht2 with ⟨y2, hy2, rfl⟩
        have h := h_main y2 hy2
        field_simp [ne_of_gt hb_pos]
        nlinarith
      have h_mul : sInf S - a * sInf S1 ≤ b * sInf S2 := by
        field_simp [ne_of_gt hb_pos] at h_div
        nlinarith
      nlinarith

open Set Filter ENNReal in
/-- `∫ t in Ioi 0, t * exp (-t^2 / (2 s^2)) = s^2`. -/
theorem AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_sq (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t ^ 2) / (2 * s ^ 2)) = s ^ 2 := by
  have hsq : 0 < s ^ 2 := pow_pos hs 2
  -- Use the known integral ∫₀^∞ x * exp(-x²) dx = 1/2
  have h_known : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x ^ 2)) = 1/2 := by
    simpa [pow_one] using integral_rpow_mul_exp_neg_rpow
      (by norm_num : 0 < (2 : ℝ)) (by norm_num : -1 < (1 : ℝ))
  -- First rescaling: u = t/s, then t = s*u, dt = s*du
  -- ∫₀^∞ t * exp(-t²/(2s²)) dt = s² * ∫₀^∞ u * exp(-u²/2) du
  have h_rescale1 : ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t ^ 2) / (2 * s ^ 2)) =
      s ^ 2 * (∫ u in Ioi (0 : ℝ), u * Real.exp (-(u ^ 2) / 2)) := by
    calc
      ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t ^ 2) / (2 * s ^ 2)) =
          ∫ t in Ioi (0 : ℝ), s * ((t / s) * Real.exp (-((t / s) ^ 2) / 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        field_simp [hs.ne']
      _ = s * (∫ t in Ioi (0 : ℝ), (t / s) * Real.exp (-((t / s) ^ 2) / 2)) := by
        rw [integral_const_mul]
      _ = s * (s • (∫ u in Ioi (0 : ℝ), u * Real.exp (-(u ^ 2) / 2))) := by
        have h_int := integral_comp_mul_left_Ioi (fun u => u * Real.exp (-(u ^ 2) / 2)) 0 (one_div_pos.mpr hs)
        simpa [div_eq_inv_mul] using congrArg (fun T => s * T) h_int
      _ = s ^ 2 * (∫ u in Ioi (0 : ℝ), u * Real.exp (-(u ^ 2) / 2)) := by
        simp [smul_eq_mul]
        ring
  -- Now compute ∫₀^∞ u * exp(-u²/2) du = 1
  -- Let g(v) = v * exp(-v²), then u * exp(-u²/2) = √2 * g(u/√2)
  have h_rescale2 : (∫ u in Ioi (0 : ℝ), u * Real.exp (-(u ^ 2) / 2)) = 1 := by
    set g := fun v : ℝ => v * Real.exp (-(v ^ 2)) with hg_def
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
    have h_inv_sqrt2 : 0 < 1 / Real.sqrt 2 := div_pos (by norm_num) hsqrt2
    have h_int := integral_comp_mul_left_Ioi g 0 h_inv_sqrt2
    simp [smul_eq_mul, div_eq_inv_mul] at h_int
    have h_rel : (fun u : ℝ => u * Real.exp (-(u ^ 2) / 2)) = fun u => Real.sqrt 2 * g (u / Real.sqrt 2) := by
      ext u
      dsimp [g]
      have h_exp_eq : -(u ^ 2) / 2 = -((u / Real.sqrt 2) ^ 2) := by
        field_simp [hsqrt2.ne']
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      calc
        u * Real.exp (-(u ^ 2) / 2) = u * Real.exp (-((u / Real.sqrt 2) ^ 2)) := by rw [h_exp_eq]
        _ = Real.sqrt 2 * ((u / Real.sqrt 2) * Real.exp (-((u / Real.sqrt 2) ^ 2))) := by
          field_simp [hsqrt2.ne']
    rw [h_rel]
    rw [integral_const_mul]
    have h_int' : (∫ a in Ioi (0 : ℝ), g (a / Real.sqrt 2)) = Real.sqrt 2 * (∫ v in Ioi (0 : ℝ), g v) := by
      simpa [div_eq_inv_mul, mul_comm] using h_int
    rw [h_int']
    have h_known_g : (∫ v in Ioi (0 : ℝ), g v) = 1/2 := by
      simpa [hg_def] using h_known
    rw [h_known_g]
    have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    nlinarith
  rw [h_rescale1, h_rescale2]
  ring

theorem AdversarialBco.lipschitzWith_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : F → ℝ)
    (L : NNReal) (hG : LipschitzWith L G) (b : F) (S : F →L[ℝ] F) :
    LipschitzWith (L * ‖S‖₊) (fun g => G (b + S g)) := by
  have hS : LipschitzWith ‖S‖₊ S := S.lipschitzWith
  have h_add : LipschitzWith 1 (fun (x : F) => b + x) :=
    (isometry_add_left b).lipschitzWith
  have h_comp : LipschitzWith ‖S‖₊ (fun g => b + S g) := by
    convert LipschitzWith.comp h_add hS using 1
    · simp
    · ext g; simp
  have h_final : LipschitzWith (L * ‖S‖₊) (fun g => G (b + S g)) :=
    LipschitzWith.comp hG h_comp
  simpa using h_final

theorem AdversarialBco.exists_maximal_separated {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d)))
    (hJ : Bornology.IsBounded J) (hne : J.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)), ↑C ⊆ J ∧ C.Nonempty ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) ∧ (∀ x ∈ J, ∃ c ∈ C, dist x c < ε) ∧
      (C.card : ℝ) ≤ (1 + 2 * Metric.diam J / ε) ^ d := by
  set N := Nat.floor ((1 + 2 * Metric.diam J / ε) ^ d) with hNdef
  let S : Set ℕ := {k | ∃ (C : Finset (EuclideanSpace ℝ (Fin d))),
    (↑C ⊆ J) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) ∧ C.card = k}
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨1, ?_⟩
    refine ⟨{x}, ?_, ?_, ?_⟩
    · simpa using hx
    · intro x' hx' y hy' hne'
      exfalso
      apply hne'
      have hx'eq := Finset.mem_singleton.mp hx'
      have hy'eq := Finset.mem_singleton.mp hy'
      simpa [hx'eq, hy'eq] using hne'
    · simp
  have hS_bdd : BddAbove S := by
    refine ⟨N, ?_⟩
    intro k hk
    rcases hk with ⟨C, hCsub, hCsep, hCcard⟩
    have hcard := AdversarialBco.card_le_of_separated J hJ C hCsub ε hε hCsep
    rw [hCcard] at hcard
    have h_lt : (k : ℝ) < (N : ℝ) + 1 := by
      have h_floor := Nat.lt_floor_add_one ((1 + 2 * Metric.diam J / ε) ^ d)
      linarith
    by_contra! h_gt
    have h_lt_nat : N < k := h_gt
    have h_succ_le : N.succ ≤ k := h_lt_nat.nat_succ_le
    have h_cast : (N.succ : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h_succ_le
    have h_cast_succ : (N.succ : ℝ) = (N : ℝ) + 1 := by simp
    rw [h_cast_succ] at h_cast
    linarith
  have h_sSup_mem : sSup S ∈ S := Nat.sSup_mem hS_nonempty hS_bdd
  rcases h_sSup_mem with ⟨C, hCsub, hCsep, hCcard⟩
  have hC_nonempty : C.Nonempty := by
    have h1 : (1 : ℕ) ∈ S := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨{x}, ?_, ?_, ?_⟩
      · simpa using hx
      · intro x' hx' y hy' hne'
        exfalso
        apply hne'
        have hx'eq := Finset.mem_singleton.mp hx'
        have hy'eq := Finset.mem_singleton.mp hy'
        exact hx'eq.trans hy'eq.symm
      · simp
    have hle : (1 : ℕ) ≤ sSup S := le_csSup hS_bdd h1
    rw [← hCcard] at hle
    have hpos : 0 < C.card := by omega
    exact Finset.card_pos.mp hpos
  have h_net : ∀ x0 ∈ J, ∃ c ∈ C, dist x0 c < ε := by
    intro x0 hx0
    by_contra h_not
    by_cases hxC : x0 ∈ C
    · by_cases hxx : ε ≤ dist x0 x0
      · rw [dist_self] at hxx
        linarith
      · have h_lt' : dist x0 x0 < ε := not_le.mp hxx
        apply h_not
        exact ⟨x0, hxC, h_lt'⟩
    · have h_insert_sep : ∀ x' ∈ insert x0 C, ∀ y ∈ insert x0 C, x' ≠ y → ε ≤ dist x' y := by
        intro x' hx' y hy' hne'
        rcases Finset.mem_insert.mp hx' with (hx'eq | hx'C)
        · rw [hx'eq]
          rcases Finset.mem_insert.mp hy' with (hy'eq | hy'C)
          · rw [hx'eq, hy'eq] at hne'
            exfalso; exact hne' rfl
          · by_cases hle : ε ≤ dist x0 y
            · exact hle
            · have h_lt' : dist x0 y < ε := not_le.mp hle
              exfalso
              apply h_not
              exact ⟨y, hy'C, h_lt'⟩
        · rcases Finset.mem_insert.mp hy' with (hy'eq | hy'C)
          · rw [hy'eq]
            by_cases hle : ε ≤ dist x0 x'
            · simpa [dist_comm] using hle
            · have h_lt' : dist x0 x' < ε := not_le.mp hle
              exfalso
              apply h_not
              exact ⟨x', hx'C, h_lt'⟩
          · exact hCsep x' hx'C y hy'C hne'
      have h_insert_sub : (↑(insert x0 C) : Set (EuclideanSpace ℝ (Fin d))) ⊆ J := by
        intro y hy
        rcases Finset.mem_insert.mp hy with (rfl | hyC)
        · exact hx0
        · exact hCsub (by simpa using hyC)
      have hx_notin_C : x0 ∉ C := hxC
      have h_insert_card : (insert x0 C).card = C.card + 1 := by
        simpa [Finset.card_insert_of_notMem hx_notin_C]
      have h_insert_in_S : (C.card + 1 : ℕ) ∈ S := by
        refine ⟨insert x0 C, h_insert_sub, h_insert_sep, ?_⟩
        simpa using h_insert_card
      have hle : (C.card + 1 : ℕ) ≤ sSup S := le_csSup hS_bdd h_insert_in_S
      rw [← hCcard] at hle
      have h_lt : C.card < C.card + 1 := by omega
      have : C.card < C.card := Nat.lt_of_lt_of_le h_lt hle
      exact Nat.lt_irrefl _ this
  have h_card_bound : (C.card : ℝ) ≤ (1 + 2 * Metric.diam J / ε) ^ d :=
    AdversarialBco.card_le_of_separated J hJ C hCsub ε hε hCsep
  refine ⟨C, hCsub, hC_nonempty, hCsep, h_net, ?_⟩
  exact h_card_bound

theorem AdversarialBco.exists_measurable_nearest {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (C : Finset X) (hC : C.Nonempty) :
    ∃ pr : X → X, Measurable pr ∧ (∀ x, pr x ∈ C) ∧ ∀ x, ∀ c ∈ C, dist x (pr x) ≤ dist x c := by
  refine Finset.Nonempty.cons_induction ?_ ?_ hC
  · intro a
    refine ⟨fun _ => a, ?_, ?_, ?_⟩
    · exact measurable_const
    · intro x; exact Finset.mem_singleton.mpr rfl
    · intro x c hc
      have hc_eq : c = a := Finset.mem_singleton.mp hc
      subst hc_eq
      exact le_refl _
  · intro a C ha hC ih
    rcases ih with ⟨prC, hprC_meas, hprC_mem, hprC_min⟩
    set pr := fun x => if dist x a ≤ dist x (prC x) then a else prC x with hpr_def
    refine ⟨pr, ?_, ?_, ?_⟩
    · dsimp [pr]
      refine Measurable.ite ?_ measurable_const hprC_meas
      refine measurableSet_le ?_ ?_
      · exact (continuous_id.dist continuous_const).measurable
      · exact Measurable.dist measurable_id hprC_meas
    · intro x
      dsimp [pr]
      by_cases h : dist x a ≤ dist x (prC x)
      · simp [h]
      · simp [h, hprC_mem x]
    · intro x c hc
      have hcases := Finset.mem_cons.mp hc
      rcases hcases with (h_eq | hc_mem_C)
      · -- h_eq : c = a, so pr x = a and goal is dist x a ≤ dist x a
        rw [h_eq]
        dsimp [pr]
        by_cases h : dist x a ≤ dist x (prC x)
        · simp [h]
        · simp [h]
          have hlt : dist x (prC x) < dist x a := lt_of_not_ge h
          exact le_of_lt hlt
      · -- hc_mem_C : c ∈ C
        dsimp [pr]
        by_cases h : dist x a ≤ dist x (prC x)
        · simp [h]
          calc
            dist x a ≤ dist x (prC x) := h
            _ ≤ dist x c := hprC_min x c hc_mem_C
        · simp [h]
          exact hprC_min x c hc_mem_C

theorem AdversarialBco.integral_comp_le_add {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (ρ : Measure X)
    [IsProbabilityMeasure ρ] (g : X → ℝ) (pr : X → X) (L ε : ℝ) (hL : 0 ≤ L) (hpr : ∀ x, dist (pr x) x ≤ ε)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) (hint : Integrable g ρ) (hint' : Integrable (fun x => g (pr x)) ρ) :
    ∫ x, g (pr x) ∂ρ ≤ ∫ x, g x ∂ρ + L * ε := by
  have hpointwise : ∀ x, g (pr x) ≤ g x + L * ε := by
    intro x
    have h : g (pr x) - g x ≤ L * ε := by
      calc
        g (pr x) - g x ≤ |g (pr x) - g x| := le_abs_self _
        _ ≤ L * dist (pr x) x := hg (pr x) x
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (hpr x) hL
    linarith
  have h_int_add : Integrable (fun x => g x + L * ε) ρ :=
    hint.add (integrable_const _)
  have h_le : ∫ x, g (pr x) ∂ρ ≤ ∫ x, (g x + L * ε) ∂ρ :=
    integral_mono hint' h_int_add hpointwise
  have huniv_real : (ρ Set.univ).toReal = (1 : ℝ) := by
    rw [measure_univ]
    simp
  have h_int_eq : ∫ x, (g x + L * ε) ∂ρ = (∫ x, g x ∂ρ) + L * ε := by
    calc
      ∫ x, (g x + L * ε) ∂ρ = (∫ x, g x ∂ρ) + (∫ x, L * ε ∂ρ) := integral_add hint (integrable_const _)
      _ = (∫ x, g x ∂ρ) + (ρ.real Set.univ • (L * ε)) := by rw [integral_const]
      _ = (∫ x, g x ∂ρ) + ((ρ Set.univ).toReal • (L * ε)) := by rw [Measure.real_def]
      _ = (∫ x, g x ∂ρ) + ((ρ Set.univ).toReal * (L * ε)) := by rw [smul_eq_mul]
      _ = (∫ x, g x ∂ρ) + ((1 : ℝ) * (L * ε)) := by rw [huniv_real]
      _ = (∫ x, g x ∂ρ) + L * ε := by ring
  linarith

open MeasureTheory in
theorem AdversarialBco.sqrt_integral_sq_add_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    √(∫ x, (f x + g x) ^ 2 ∂μ) ≤ √(∫ x, f x ^ 2 ∂μ) + √(∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ with hA_def
  set B := ∫ x, g x ^ 2 ∂μ with hB_def
  set C := ∫ x, f x * g x ∂μ with hC_def
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun x => sq_nonneg (f x))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun x => sq_nonneg (g x))
  have hf_sq_int : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hg_sq_int : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have hfg_int : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  -- integrability of 2*s*(f*g) where s = C/B
  have h2sfg_int : Integrable (fun x => 2 * (C / B) * (f x * g x)) μ :=
    hfg_int.const_mul (2 * (C / B))
  -- integrability of s^2 * g^2
  have hs2g2_int : Integrable (fun x => ((C / B) ^ 2) * g x ^ 2) μ :=
    hg_sq_int.const_mul ((C / B) ^ 2)
  -- integrability of f^2 - 2*s*f*g
  have h_diff_int : Integrable (fun x => f x ^ 2 - 2 * (C / B) * (f x * g x)) μ :=
    hf_sq_int.sub h2sfg_int
  -- Cauchy-Schwarz: C^2 ≤ A * B
  have h_cauchy_schwarz : C ^ 2 ≤ A * B := by
    by_cases hB_zero : B = 0
    · -- If B = 0, then g^2 = 0 a.e., so g = 0 a.e., so C = 0
      have hg_sq_zero : (fun x => g x ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hg_sq_int).mp hB_zero
      have hC_zero : C = 0 := by
        dsimp [C]
        have h_fg_zero : (fun x => f x * g x) =ᵐ[μ] 0 := by
          filter_upwards [hg_sq_zero] with x hx
          have hgx : g x = 0 := by
            have hsq : g x ^ 2 = 0 := hx
            nlinarith [sq_nonneg (g x)]
          simp [hgx]
        calc
          ∫ x, f x * g x ∂μ = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae h_fg_zero
          _ = 0 := by simp
      rw [hB_zero, hC_zero]
      nlinarith
    · -- B > 0
      have hB_pos : 0 < B := lt_of_le_of_ne hB_nonneg (Ne.symm hB_zero)
      set s := C / B with hs_def
      have h_nonneg : 0 ≤ ∫ x, (f x - s * g x) ^ 2 ∂μ :=
        integral_nonneg (fun x => sq_nonneg _)
      have h_expand : ∫ x, (f x - s * g x) ^ 2 ∂μ = A - 2*s*C + s^2*B := by
        calc
          ∫ x, (f x - s * g x) ^ 2 ∂μ = ∫ x, (f x ^ 2 - 2*s*(f x * g x) + s^2 * g x ^ 2) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x; ring
          _ = (∫ x, (f x ^ 2 - 2*s*(f x * g x)) ∂μ) + (∫ x, s^2 * g x ^ 2 ∂μ) := by
            rw [integral_add h_diff_int hs2g2_int]
          _ = ((∫ x, f x ^ 2 ∂μ) - (∫ x, 2*s*(f x * g x) ∂μ)) + (∫ x, s^2 * g x ^ 2 ∂μ) := by
            rw [integral_sub hf_sq_int h2sfg_int]
          _ = A - 2*s*C + s^2*B := by
            dsimp [A, B, C, s]
            simp [integral_const_mul]
      have h_ineq : 0 ≤ A - 2*s*C + s^2*B := by linarith
      -- Substitute s = C/B
      have h_subst : A - 2*(C/B)*C + ((C/B)^2)*B = A - C^2/B := by
        field_simp [hB_zero]
        ring
      rw [hs_def] at h_ineq
      rw [h_subst] at h_ineq
      -- A - C^2/B ≥ 0 → C^2 ≤ A*B
      have h_mul : C ^ 2 ≤ A * B := by
        have h_div : C ^ 2 / B ≤ A := by linarith
        have h := (div_le_iff₀' hB_pos).mp h_div
        -- h : C^2 ≤ B * A
        simpa [mul_comm] using h
      exact h_mul
  -- Now we have C^2 ≤ A*B
  -- Expand ∫ (f+g)^2 = A + 2C + B
  have h_expand_sq : ∫ x, (f x + g x) ^ 2 ∂μ = A + 2*C + B := by
    calc
      ∫ x, (f x + g x) ^ 2 ∂μ = ∫ x, (f x ^ 2 + 2*(f x * g x) + g x ^ 2) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with x; ring
      _ = (∫ x, (f x ^ 2 + 2*(f x * g x)) ∂μ) + (∫ x, g x ^ 2 ∂μ) := by
        simpa using integral_add (hf_sq_int.add (hfg_int.const_mul 2)) hg_sq_int
      _ = ((∫ x, f x ^ 2 ∂μ) + (∫ x, 2*(f x * g x) ∂μ)) + (∫ x, g x ^ 2 ∂μ) := by
        rw [integral_add hf_sq_int (hfg_int.const_mul 2)]
      _ = A + 2*C + B := by
        dsimp [A, B, C]
        simp [integral_const_mul]
  rw [h_expand_sq]
  -- Need: √(A + 2C + B) ≤ √A + √B
  by_cases hC_nonneg : 0 ≤ C
  · -- C ≥ 0, so from C^2 ≤ A*B we get C ≤ √A * √B
    have hC_le_sqrt_mul : C ≤ √A * √B := by
      have h_sq_le : C ^ 2 ≤ (√A * √B) ^ 2 := by
        calc
          C ^ 2 ≤ A * B := h_cauchy_schwarz
          _ = (√A) ^ 2 * (√B) ^ 2 := by rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
          _ = (√A * √B) ^ 2 := by ring
      have h_nonneg_sqrt_mul : 0 ≤ √A * √B :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith
    -- Now: A + 2C + B ≤ A + 2√A√B + B = (√A + √B)^2
    have h_sum_le : A + 2*C + B ≤ (√A + √B) ^ 2 := by
      calc
        A + 2*C + B ≤ A + 2*(√A * √B) + B := by nlinarith
        _ = (√A) ^ 2 + 2*(√A * √B) + (√B) ^ 2 := by rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
        _ = (√A + √B) ^ 2 := by ring
    have h_nonneg_sum : 0 ≤ √A + √B :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sqrt_le : √(A + 2*C + B) ≤ √((√A + √B) ^ 2) :=
      Real.sqrt_le_sqrt h_sum_le
    rw [Real.sqrt_sq h_nonneg_sum] at h_sqrt_le
    exact h_sqrt_le
  · -- C < 0, then A + 2C + B ≤ A + B ≤ (√A + √B)^2 since √A + √B ≥ 0
    have h_sum_le : A + 2*C + B ≤ (√A + √B) ^ 2 := by
      have h_nonpos : 2*C ≤ 0 := by linarith
      have h_nonneg_mul : 0 ≤ √A * √B :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc
        A + 2*C + B ≤ A + B := by nlinarith
        _ ≤ A + 2*(√A * √B) + B := by nlinarith
        _ = (√A) ^ 2 + 2*(√A * √B) + (√B) ^ 2 := by rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
        _ = (√A + √B) ^ 2 := by ring
    have h_nonneg_sum : 0 ≤ √A + √B :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sqrt_le : √(A + 2*C + B) ≤ √((√A + √B) ^ 2) :=
      Real.sqrt_le_sqrt h_sum_le
    rw [Real.sqrt_sq h_nonneg_sum] at h_sqrt_le
    exact h_sqrt_le

theorem AdversarialBco.var_le_sq_mean {ι : Type*} [Fintype ι] (w W : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) :
    ∑ i, w i * ((∑ j, w j * W j) - W i) ^ 2 ≤ ∑ i, w i * W i ^ 2 := by
  set m := ∑ j, w j * W j with hm
  have h_eq : ∑ i, w i * (m - W i) ^ 2 = ∑ i, w i * W i ^ 2 - m ^ 2 := by
    calc
      ∑ i, w i * (m - W i) ^ 2
          = ∑ i, w i * (m ^ 2 - 2 * m * W i + W i ^ 2) := by
            refine Finset.sum_congr rfl (λ i _ => ?_)
            ring
      _ = ∑ i, (w i * m ^ 2 - 2 * w i * m * W i + w i * W i ^ 2) := by
            refine Finset.sum_congr rfl (λ i _ => ?_)
            ring
      _ = (∑ i, w i * m ^ 2) - (∑ i, 2 * w i * m * W i) + (∑ i, w i * W i ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = m ^ 2 * (∑ i, w i) - 2 * m * (∑ i, w i * W i) + (∑ i, w i * W i ^ 2) := by
            simp [Finset.mul_sum, Finset.sum_mul, hm, mul_comm, mul_left_comm, mul_assoc]
      _ = m ^ 2 * 1 - 2 * m * m + (∑ i, w i * W i ^ 2) := by simp [hw1, hm]
      _ = (∑ i, w i * W i ^ 2) - m ^ 2 := by ring
  rw [h_eq]
  have h_sq_nonneg : 0 ≤ m ^ 2 := sq_nonneg m
  linarith

theorem AdversarialBco.sqrt_wsum_sq_add_le {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    √(∑ i, w i * (a i + b i) ^ 2) ≤ √(∑ i, w i * a i ^ 2) + √(∑ i, w i * b i ^ 2) := by
  let s : Finset ι := Finset.univ
  set f := fun i : ι => √(w i) * a i with hf
  set g := fun i : ι => √(w i) * b i with hg
  have h_cauchy := Real.sum_mul_le_sqrt_mul_sqrt s f g
  -- h_cauchy : ∑ i ∈ s, f i * g i ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2)
  have h_f_sq : ∀ i, f i ^ 2 = w i * a i ^ 2 := by
    intro i
    dsimp [f]
    calc
      (√(w i) * a i) ^ 2 = (√(w i)) ^ 2 * (a i) ^ 2 := by ring
      _ = w i * (a i) ^ 2 := by rw [Real.sq_sqrt (hw i)]
      _ = w i * a i ^ 2 := by ring
  have h_g_sq : ∀ i, g i ^ 2 = w i * b i ^ 2 := by
    intro i
    dsimp [g]
    calc
      (√(w i) * b i) ^ 2 = (√(w i)) ^ 2 * (b i) ^ 2 := by ring
      _ = w i * (b i) ^ 2 := by rw [Real.sq_sqrt (hw i)]
      _ = w i * b i ^ 2 := by ring
  have h_fg : ∀ i, f i * g i = w i * a i * b i := by
    intro i
    dsimp [f, g]
    calc
      (√(w i) * a i) * (√(w i) * b i) = ((√(w i)) ^ 2) * (a i * b i) := by ring
      _ = w i * (a i * b i) := by rw [Real.sq_sqrt (hw i)]
      _ = w i * a i * b i := by ring
  have h_expand : ∑ i ∈ s, w i * (a i + b i) ^ 2 =
      (∑ i ∈ s, w i * a i ^ 2) + 2 * (∑ i ∈ s, w i * a i * b i) + (∑ i ∈ s, w i * b i ^ 2) := by
    calc
      ∑ i ∈ s, w i * (a i + b i) ^ 2 = ∑ i ∈ s, w i * (a i ^ 2 + 2 * a i * b i + b i ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      _ = ∑ i ∈ s, (w i * a i ^ 2 + 2 * w i * a i * b i + w i * b i ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      _ = (∑ i ∈ s, w i * a i ^ 2) + (∑ i ∈ s, 2 * w i * a i * b i) + (∑ i ∈ s, w i * b i ^ 2) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ i ∈ s, w i * a i ^ 2) + 2 * (∑ i ∈ s, w i * a i * b i) + (∑ i ∈ s, w i * b i ^ 2) := by
        simp [Finset.mul_sum, mul_assoc]
  have hA : 0 ≤ ∑ i ∈ s, w i * a i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg (a i))
  have hB : 0 ≤ ∑ i ∈ s, w i * b i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg (b i))
  have h_cauchy' : ∑ i ∈ s, w i * a i * b i ≤ √(∑ i ∈ s, w i * a i ^ 2) * √(∑ i ∈ s, w i * b i ^ 2) := by
    -- rewrite h_cauchy using h_fg, h_f_sq, h_g_sq
    simpa [h_fg, h_f_sq, h_g_sq] using h_cauchy
  have h_sum_nonneg : 0 ≤ √(∑ i ∈ s, w i * a i ^ 2) + √(∑ i ∈ s, w i * b i ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_main : ∑ i ∈ s, w i * (a i + b i) ^ 2 ≤
      (√(∑ i ∈ s, w i * a i ^ 2) + √(∑ i ∈ s, w i * b i ^ 2)) ^ 2 := by
    rw [h_expand]
    have h_sq_eq : (√(∑ i ∈ s, w i * a i ^ 2) + √(∑ i ∈ s, w i * b i ^ 2)) ^ 2 =
        (∑ i ∈ s, w i * a i ^ 2) + 2 * (√(∑ i ∈ s, w i * a i ^ 2) * √(∑ i ∈ s, w i * b i ^ 2)) + (∑ i ∈ s, w i * b i ^ 2) := by
      ring_nf
      rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
    rw [h_sq_eq]
    have h_mul : 2 * (∑ i ∈ s, w i * a i * b i) ≤ 2 * (√(∑ i ∈ s, w i * a i ^ 2) * √(∑ i ∈ s, w i * b i ^ 2)) := by
      linarith
    linarith
  calc
    √(∑ i, w i * (a i + b i) ^ 2) = √(∑ i ∈ s, w i * (a i + b i) ^ 2) := by simp [s]
    _ ≤ √((√(∑ i ∈ s, w i * a i ^ 2) + √(∑ i ∈ s, w i * b i ^ 2)) ^ 2) := Real.sqrt_le_sqrt h_main
    _ = √(∑ i ∈ s, w i * a i ^ 2) + √(∑ i ∈ s, w i * b i ^ 2) := by rw [Real.sqrt_sq h_sum_nonneg]
    _ = √(∑ i, w i * a i ^ 2) + √(∑ i, w i * b i ^ 2) := by simp [s]

open MeasureTheory in
theorem AdversarialBco.sqrt_V_le {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ] {k : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (hb : ∀ i x, |f i x| ≤ 1) (pr : X → X) (hpr : Measurable pr) (δ : ℝ)
    (hδ : ∀ i x, |f i x - f i (pr x)| ≤ δ) :
    √(∫ x, ∑ i, w i * ((∑ j, w j * f j x) - f i x) ^ 2 ∂ρ) ≤
      √(∫ x, ∑ i, w i * ((∑ j, w j * f j (pr x)) - f i (pr x)) ^ 2 ∂ρ) + δ := by
  -- δ ≥ 0 because ∑ w_i = 1 implies Fin k is nonempty and X is nonempty
  have hX_nonempty : Nonempty X := by
    by_cases h : Nonempty X
    · exact h
    · exfalso
      have h_empty : IsEmpty X := not_nonempty_iff.mp h
      have huniv_empty : ρ Set.univ = 0 := by
        have h_univ_empty : Set.univ = (∅ : Set X) :=
          Set.univ_eq_empty_iff.mpr h_empty
        rw [h_univ_empty]; exact measure_empty
      have huniv_one : ρ Set.univ = 1 := measure_univ
      rw [huniv_one] at huniv_empty
      exact one_ne_zero huniv_empty
  have h_fin_nonempty : Nonempty (Fin k) := by
    by_contra! h_empty
    -- h_empty : IsEmpty (Fin k)
    have hsum0 : ∑ i, w i = 0 := by
      simpa [h_empty] using Finset.sum_empty (β := ℝ) (s := (∅ : Finset (Fin k)))
    linarith [hsum0, hw1]
  obtain ⟨i0⟩ := h_fin_nonempty
  obtain ⟨x0⟩ := hX_nonempty
  have hδ_nonneg : 0 ≤ δ := by
    have h_abs := hδ i0 x0
    have h_nonneg_abs : 0 ≤ |f i0 x0 - f i0 (pr x0)| := abs_nonneg _
    linarith
  -- define fbar y = ∑ j, w j * f j y
  set fbar := fun (y : X) => ∑ j, w j * f j y with hfbar
  have hfbar_meas : Measurable fbar := by
    dsimp [fbar]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact (hf j).const_mul (w j)
  -- bound for fbar: |fbar x| ≤ 1
  have h_fbar_bound : ∀ x, |fbar x| ≤ 1 := by
    intro x
    calc
      |fbar x| = |∑ j, w j * f j x| := rfl
      _ ≤ ∑ j, |w j * f j x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, w j * |f j x| := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hw j)]
      _ ≤ ∑ j, w j * 1 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hb j x) (hw j))
      _ = (∑ j, w j) * 1 := by simp
      _ = 1 := by rw [hw1, one_mul]
  -- pointwise inequality
  have h_pointwise : ∀ x, √(∑ i, w i * (fbar x - f i x) ^ 2) ≤ √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ := by
    intro x
    set a := fun i => fbar x - f i x with ha
    set b := fun i => fbar (pr x) - f i (pr x) with hb
    set W := fun i => f i x - f i (pr x) with hW
    have h_diff : ∀ i, a i - b i = (∑ j, w j * W j) - W i := by
      intro i
      dsimp [a, b, fbar, W]
      calc
        (∑ j, w j * f j x) - f i x - ((∑ j, w j * f j (pr x)) - f i (pr x))
            = ((∑ j, w j * f j x) - (∑ j, w j * f j (pr x))) - (f i x - f i (pr x)) := by ring
        _ = (∑ j, w j * (f j x - f j (pr x))) - (f i x - f i (pr x)) := by
          rw [← Finset.sum_sub_distrib]
          refine congrArg (· - (f i x - f i (pr x))) (Finset.sum_congr rfl (fun j _ => by rw [mul_sub]))
        _ = (∑ j, w j * W j) - W i := rfl
    -- sqrt_wsum_sq_add_le: √(∑ w_i * (b_i + (a_i - b_i))^2) ≤ √(∑ w_i * b_i^2) + √(∑ w_i * (a_i - b_i)^2)
    have h_sqrt_add : √(∑ i, w i * (a i) ^ 2) ≤ √(∑ i, w i * (b i) ^ 2) + √(∑ i, w i * ((a i - b i) ^ 2)) := by
      have := AdversarialBco.sqrt_wsum_sq_add_le w b (a - b) hw
      simpa [add_sub_cancel] using this
    -- bound the sqrt term by δ
    have h_sqrt_diff_le_δ : √(∑ i, w i * ((a i - b i) ^ 2)) ≤ δ := by
      have h_sum_le_δsq : ∑ i, w i * ((a i - b i) ^ 2) ≤ δ ^ 2 := by
        calc
          ∑ i, w i * ((a i - b i) ^ 2) = ∑ i, w i * (((∑ j, w j * W j) - W i) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [h_diff i]
          _ ≤ ∑ i, w i * (W i ^ 2) := AdversarialBco.var_le_sq_mean w W hw hw1
          _ ≤ ∑ i, w i * (δ ^ 2) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have hW_sq : W i ^ 2 ≤ δ ^ 2 := by
              have h_abs : |W i| ≤ δ := hδ i x
              have h_abs' : |W i| ≤ |δ| := by simpa [abs_of_nonneg hδ_nonneg] using h_abs
              exact (sq_le_sq.mpr h_abs')
            exact mul_le_mul_of_nonneg_left hW_sq (hw i)
          _ = (∑ i, w i) * (δ ^ 2) := by rw [Finset.sum_mul]
          _ = δ ^ 2 := by rw [hw1, one_mul]
      have h_nonneg_sum : 0 ≤ ∑ i, w i * ((a i - b i) ^ 2) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      calc
        √(∑ i, w i * ((a i - b i) ^ 2)) ≤ √(δ ^ 2) := Real.sqrt_le_sqrt h_sum_le_δsq
        _ = |δ| := Real.sqrt_sq_eq_abs _
        _ = δ := abs_of_nonneg hδ_nonneg
    linarith
  -- square both sides pointwise
  have h_sq_pointwise : ∀ x, (∑ i, w i * (fbar x - f i x) ^ 2) ≤ ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2) := by
    intro x
    have hA_nonneg : 0 ≤ √(∑ i, w i * (fbar x - f i x) ^ 2) := Real.sqrt_nonneg _
    have h_sum_nonneg : 0 ≤ ∑ i, w i * (fbar x - f i x) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    have h_sqrt_sq : (√(∑ i, w i * (fbar x - f i x) ^ 2)) ^ 2 = ∑ i, w i * (fbar x - f i x) ^ 2 :=
      Real.sq_sqrt h_sum_nonneg
    have h_pointwise' := h_pointwise x
    nlinarith
  -- measurability and integrability of the LHS integrand
  have h_meas_L : Measurable (fun (x : X) => ∑ i, w i * (fbar x - f i x) ^ 2) := by
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have h_meas_a_sq : Measurable (fun (x : X) => (fbar x - f i x) ^ 2) :=
      Measurable.pow_const (hfbar_meas.sub (hf i)) 2
    exact h_meas_a_sq.const_mul (w i)
  have h_int_L : Integrable (fun (x : X) => ∑ i, w i * (fbar x - f i x) ^ 2) ρ := by
    refine Integrable.of_bound h_meas_L.aestronglyMeasurable 4 ?_
    filter_upwards with x
    have hL_nonneg : 0 ≤ ∑ i, w i * (fbar x - f i x) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    have hL_le_4 : ∑ i, w i * (fbar x - f i x) ^ 2 ≤ 4 := by
      calc
        ∑ i, w i * (fbar x - f i x) ^ 2 ≤ ∑ i, w i * (4 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h_diff_bound : |fbar x - f i x| ≤ 2 := by
            have h_tri := abs_sub (fbar x) (f i x)
            have h1 : |fbar x| ≤ 1 := h_fbar_bound x
            have h2 : |f i x| ≤ 1 := hb i x
            linarith
          have h_sq_bound : (fbar x - f i x) ^ 2 ≤ (2 : ℝ) ^ 2 := by
            have h_abs' : |fbar x - f i x| ≤ |(2 : ℝ)| := by
              simpa [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using h_diff_bound
            exact (sq_le_sq.mpr h_abs')
          have h_sq_bound' : (fbar x - f i x) ^ 2 ≤ (4 : ℝ) := by nlinarith
          exact mul_le_mul_of_nonneg_left h_sq_bound' (hw i)
        _ = (∑ i, w i) * 4 := by rw [Finset.sum_mul]
        _ = 4 := by rw [hw1, one_mul]
    simpa [Real.norm_eq_abs, abs_of_nonneg hL_nonneg] using hL_le_4
  -- measurability of the inner sum (used in both h_meas_R and h_sqrt_add_le)
  have h_meas_inner : Measurable (fun (x : X) => ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) := by
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have h_meas_b_sq : Measurable (fun (x : X) => (fbar (pr x) - f i (pr x)) ^ 2) :=
      Measurable.pow_const ((hfbar_meas.comp hpr).sub ((hf i).comp hpr)) 2
    exact h_meas_b_sq.const_mul (w i)
  -- measurability and integrability of the RHS integrand
  have h_meas_R : Measurable (fun (x : X) => ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2)) := by
    have h_meas_sqrt : Measurable (fun (x : X) => √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2)) :=
      Measurable.sqrt h_meas_inner
    exact Measurable.pow_const (h_meas_sqrt.add_const δ) 2
  have h_int_R : Integrable (fun (x : X) => ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2)) ρ := by
    refine Integrable.of_bound h_meas_R.aestronglyMeasurable ((2 + δ) ^ 2) ?_
    filter_upwards with x
    have hB_nonneg : 0 ≤ √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) := Real.sqrt_nonneg _
    have hB_le_2 : √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) ≤ 2 := by
      have h_sum_le_4 : ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 ≤ 4 := by
        calc
          ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 ≤ ∑ i, w i * (4 : ℝ) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have h_diff_bound : |fbar (pr x) - f i (pr x)| ≤ 2 := by
              have h_tri := abs_sub (fbar (pr x)) (f i (pr x))
              have h1 : |fbar (pr x)| ≤ 1 := h_fbar_bound (pr x)
              have h2 : |f i (pr x)| ≤ 1 := hb i (pr x)
              linarith
            have h_sq_bound : (fbar (pr x) - f i (pr x)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
              have h_abs' : |fbar (pr x) - f i (pr x)| ≤ |(2 : ℝ)| := by
                simpa [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using h_diff_bound
              exact (sq_le_sq.mpr h_abs')
            have h_sq_bound' : (fbar (pr x) - f i (pr x)) ^ 2 ≤ (4 : ℝ) := by nlinarith
            exact mul_le_mul_of_nonneg_left h_sq_bound' (hw i)
          _ = (∑ i, w i) * 4 := by rw [Finset.sum_mul]
          _ = 4 := by rw [hw1, one_mul]
      have h_nonneg_sum : 0 ≤ ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      calc
        √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) ≤ √(4 : ℝ) := Real.sqrt_le_sqrt h_sum_le_4
        _ = 2 := by norm_num
    have h_nonneg_δ : 0 ≤ δ := hδ_nonneg
    have h_bound : (√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2 ≤ (2 + δ) ^ 2 := by
      have h_nonneg_sqrt : 0 ≤ √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) := Real.sqrt_nonneg _
      have h_nonneg_sum : 0 ≤ √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ := by nlinarith
      have h_le : √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ ≤ 2 + δ := by nlinarith
      have h_abs : |√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ| ≤ |2 + δ| := by
        rw [abs_of_nonneg h_nonneg_sum, abs_of_nonneg (by nlinarith)]
        exact h_le
      exact sq_le_sq.mpr h_abs
    have h_nonneg_sq : 0 ≤ (√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg_sq] using h_bound
  -- integral inequality
  have h_int_ineq : (∫ x, ∑ i, w i * (fbar x - f i x) ^ 2 ∂ρ) ≤
      (∫ x, ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2) ∂ρ) := by
    exact integral_mono h_int_L h_int_R h_sq_pointwise
  -- take sqrt of both sides
  have h_sqrt_ineq : √(∫ x, ∑ i, w i * (fbar x - f i x) ^ 2 ∂ρ) ≤
      √(∫ x, ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2) ∂ρ) :=
    Real.sqrt_le_sqrt h_int_ineq
  -- use sqrt_integral_sq_add_le: √(∫ (B + δ)^2) ≤ √(∫ B^2) + δ
  have h_sqrt_add_le : √(∫ x, ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2) ∂ρ) ≤
      √(∫ x, (∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) ∂ρ) + δ := by
    set B := fun (x : X) => √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) with hB
    have h_memLp_B : MemLp B 2 ρ := by
      have h_meas_B : Measurable B := h_meas_inner.sqrt
      have h_bound : ∀ᵐ x ∂ρ, B x ∈ Set.Icc (0 : ℝ) 2 := by
        filter_upwards with x
        have hB_nonneg : 0 ≤ B x := Real.sqrt_nonneg _
        have hB_le_2 : B x ≤ 2 := by
          have h_sum_le_4 : ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 ≤ 4 := by
            calc
              ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 ≤ ∑ i, w i * (4 : ℝ) := by
                refine Finset.sum_le_sum (fun i _ => ?_)
                have h_diff_bound : |fbar (pr x) - f i (pr x)| ≤ 2 := by
                  have h_tri := abs_sub (fbar (pr x)) (f i (pr x))
                  have h1 : |fbar (pr x)| ≤ 1 := h_fbar_bound (pr x)
                  have h2 : |f i (pr x)| ≤ 1 := hb i (pr x)
                  linarith
                have h_sq_bound : (fbar (pr x) - f i (pr x)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
                  have h_abs' : |fbar (pr x) - f i (pr x)| ≤ |(2 : ℝ)| := by
                    simpa [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using h_diff_bound
                  exact (sq_le_sq.mpr h_abs')
                have h_sq_bound' : (fbar (pr x) - f i (pr x)) ^ 2 ≤ (4 : ℝ) := by nlinarith
                exact mul_le_mul_of_nonneg_left h_sq_bound' (hw i)
              _ = (∑ i, w i) * 4 := by rw [Finset.sum_mul]
              _ = 4 := by rw [hw1, one_mul]
          have h_nonneg_sum : 0 ≤ ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 :=
            Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
          calc
            B x = √(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) := rfl
            _ ≤ √(4 : ℝ) := Real.sqrt_le_sqrt h_sum_le_4
            _ = 2 := by norm_num
        exact ⟨hB_nonneg, hB_le_2⟩
      exact MeasureTheory.memLp_of_bounded h_bound h_meas_B.aestronglyMeasurable 2
    have h_memLp_const_δ : MemLp (fun (_ : X) => δ) 2 ρ :=
      MeasureTheory.memLp_const δ
    have h := AdversarialBco.sqrt_integral_sq_add_le ρ B (fun _ => δ) h_memLp_B h_memLp_const_δ
    -- h: √(∫ (B + (fun _ => δ))^2) ≤ √(∫ B^2) + √(∫ (fun _ => δ)^2)
    -- simplify: ∫ (fun _ => δ)^2 = δ^2, so √(δ^2) = δ; and ∫ B^2 = ∫ ∑ w_i * b_i^2
    have h_B_sq_eq : (fun x => (B x) ^ 2) = (fun x => ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) := by
      ext x
      dsimp [B]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _)))]
    simpa [B, Pi.add_apply, h_B_sq_eq, Real.sqrt_sq hδ_nonneg] using h
  -- combine with ∫ B^2 = ∫ ∑ w_i * b_i^2
  have h_int_B_sq : (∫ x, (∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) ∂ρ) =
      (∫ x, ∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2 ∂ρ) := rfl
  -- final result
  calc
    √(∫ x, ∑ i, w i * ((∑ j, w j * f j x) - f i x) ^ 2 ∂ρ) = √(∫ x, ∑ i, w i * (fbar x - f i x) ^ 2 ∂ρ) := by
      simp [fbar]
    _ ≤ √(∫ x, ((√(∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) + δ) ^ 2) ∂ρ) := h_sqrt_ineq
    _ ≤ √(∫ x, (∑ i, w i * (fbar (pr x) - f i (pr x)) ^ 2) ∂ρ) + δ := h_sqrt_add_le
    _ = √(∫ x, ∑ i, w i * ((∑ j, w j * f j (pr x)) - f i (pr x)) ^ 2 ∂ρ) + δ := by simp [fbar]

open Set in
/-- The derivative of the standard Gaussian density. -/
theorem AdversarialBco.hasDerivAt_gaussianPDFReal_0_1 (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(gaussianPDFReal 0 1 x) * x) x := by
  have h_gaussian_eq : gaussianPDFReal 0 1 = fun (t : ℝ) => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
    ext t; simp [gaussianPDFReal]
  rw [h_gaussian_eq]
  -- Now compute derivative of (√(2π))⁻¹ * exp(-t^2/2)
  set c := (Real.sqrt (2 * Real.pi))⁻¹ with hc
  have h_deriv_exp : HasDerivAt (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * (-x)) x := by
    have h_inner : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-x) x := by
      have h_sq : HasDerivAt (fun (t : ℝ) => t ^ 2) (2 * x) x := by
        simpa [pow_two] using hasDerivAt_pow 2 x
      have h_neg_sq : HasDerivAt (fun (t : ℝ) => -(t ^ 2)) (-(2 * x)) x := by
        have := h_sq.neg
        -- this : HasDerivAt (-(fun t => t^2)) (-(2*x)) x
        -- we need : HasDerivAt (fun t => -(t^2)) (-(2*x)) x
        -- Note: -(fun t => t^2) = fun t => -(t^2) by definition
        -- But the types are different: HasDerivAt expects a function ℝ → ℝ
        -- Let's use `apply` with `this` after rewriting
        simpa [Pi.neg_def] using this
      have h_div : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-(2 * x) / 2) x :=
        h_neg_sq.div_const 2
      have h_simp : -(2 * x) / 2 = -x := by ring
      simpa [h_simp] using h_div
    simpa using h_inner.exp
  have h_const : HasDerivAt (fun (_ : ℝ) => c) 0 x :=
    hasDerivAt_const _ _
  have h_mul := HasDerivAt.mul h_const h_deriv_exp
  -- h_mul : HasDerivAt ((fun _ => c) * (fun t => exp(...))) (0 * exp(...) + c * (exp(...) * (-x))) x
  -- Simplify both the function and the derivative
  have h_simp_fun : ((fun (_ : ℝ) => c) * fun (t : ℝ) => Real.exp (-(t ^ 2) / 2)) =
      fun (t : ℝ) => c * Real.exp (-(t ^ 2) / 2) := rfl
  have h_simp_deriv : (0 : ℝ) * Real.exp (-(x ^ 2) / 2) + c * (Real.exp (-(x ^ 2) / 2) * (-x)) =
      -(c * (Real.exp (-(x ^ 2) / 2) * x)) := by
    ring
  -- h_mul : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (0 * exp + c * (exp * (-x))) x
  -- Goal: HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-((fun t => c * Real.exp (-t^2/2)) x) * x) x
  -- i.e., HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * Real.exp (-x^2/2) * x)) x
  -- h_mul' : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * (Real.exp (-x^2/2) * x))) x
  -- We need to rewrite the goal's derivative to match h_mul'
  have h_mul' := h_mul
  rw [h_simp_fun] at h_mul'
  rw [h_simp_deriv] at h_mul'
  -- Now h_mul' : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * (Real.exp (-x^2/2) * x))) x
  -- Goal : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * Real.exp (-x^2/2) * x)) x
  -- These differ by associativity: c * (exp * x) vs (c * exp) * x
  -- We can simpa [mul_assoc] using h_mul'
  simpa [mul_assoc] using h_mul'

open Set in
theorem AdversarialBco.gaussian_ibp_1d (H H' : ℝ → ℝ) (hH : ∀ x, HasDerivAt H (H' x) x)
    (hint1 : Integrable (fun x => x * H x) (gaussianReal 0 1)) (hint2 : Integrable H' (gaussianReal 0 1))
    (hint3 : Integrable H (gaussianReal 0 1)) :
    ∫ x, x * H x ∂(gaussianReal 0 1) = ∫ x, H' x ∂(gaussianReal 0 1) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  set φ := gaussianPDFReal 0 1 with hφ
  have hφ_deriv (x : ℝ) : HasDerivAt φ (-(φ x) * x) x := AdversarialBco.hasDerivAt_gaussianPDFReal_0_1 x
  -- Rewrite integrals using integral_gaussianReal_eq_integral_smul
  have h_int_left : ∫ x, x * H x ∂(gaussianReal 0 1) = ∫ x, φ x • (x * H x) := by
    simpa [hφ] using integral_gaussianReal_eq_integral_smul hv (f := fun x => x * H x)
  have h_int_right : ∫ x, H' x ∂(gaussianReal 0 1) = ∫ x, φ x • H' x := by
    simpa [hφ] using integral_gaussianReal_eq_integral_smul hv (f := fun x => H' x)
  rw [h_int_left, h_int_right]
  -- Convert integrability hypotheses from gaussianReal to volume with density
  rw [gaussianReal_of_var_ne_zero _ hv] at hint1 hint2 hint3
  have h_int1' : Integrable (fun x => φ x • (x * H x)) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint1
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  have h_int2' : Integrable (fun x => φ x • H' x) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint2
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  have h_int3' : Integrable (fun x => φ x • H x) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint3
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  -- Apply integration by parts: integral_mul_deriv_eq_deriv_mul_of_integrable
  -- u := H, v := φ, u' := H', v' := fun x => -(φ x) * x
  have h_parts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu := fun x hx => hH x)
    (hv := fun x hx => hφ_deriv x)
    (huv' := ?_)
    (hu'v := ?_)
    (huv := ?_)
  -- h_parts : ∫ x, H x * (-(φ x) * x) = -∫ x, H' x * φ x
  -- We need: ∫ x, φ x • (x * H x) = ∫ x, φ x • H' x
  -- Note: φ x • (x * H x) = x * H x * φ x = -(H x * (-(φ x) * x))
  -- and φ x • H' x = H' x * φ x
  -- So from h_parts: -∫ x, φ x • (x * H x) = -∫ x, φ x • H' x
  -- Cancel minus sign
  have h_eq1 : (fun x => φ x • (x * H x)) = (fun x => -(H x * (-(φ x) * x))) := by
    ext x; simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have h_eq2 : (fun x => φ x • H' x) = (fun x => H' x * φ x) := by
    ext x; simp [smul_eq_mul, mul_comm]
  rw [h_eq1, h_eq2]
  -- Goal: ∫ x, -(H x * (-(φ x) * x)) = ∫ x, H' x * φ x
  rw [integral_neg]
  -- Goal: -∫ x, H x * (-(φ x) * x) = ∫ x, H' x * φ x
  rw [h_parts]
  -- Goal: -(-∫ x, H' x * φ x) = ∫ x, H' x * φ x
  simp
  -- Now provide the integrability conditions
  · -- huv' : Integrable (H * (fun x => -(φ x) * x))
    -- Goal: Integrable (H * (fun x => -(φ x) * x))
    -- which is definitionally Integrable (fun x => H x * (-(φ x) * x))
    -- We have h_int1' : Integrable (fun x => φ x • (x * H x))
    -- Note: H x * (-(φ x) * x) = -(φ x • (x * H x)) by ring
    simpa [Pi.mul_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h_int1'.neg
  · -- hu'v : Integrable (H' * φ)
    -- Goal: Integrable (H' * φ) which is definitionally Integrable (fun x => H' x * φ x)
    -- h_int2' : Integrable (fun x => φ x • H' x) = Integrable (fun x => φ x * H' x)
    -- By commutativity, these are equal
    simpa [Pi.mul_def, smul_eq_mul, mul_comm] using h_int2'
  · -- huv : Integrable (H * φ)
    -- Goal: Integrable (H * φ) which is definitionally Integrable (fun x => H x * φ x)
    -- h_int3' : Integrable (fun x => φ x • H x) = Integrable (fun x => φ x * H x)
    -- By commutativity, these are equal
    simpa [Pi.mul_def, smul_eq_mul, mul_comm] using h_int3'

theorem AdversarialBco.convex_inner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hK : Convex ℝ K) (r : ℝ) : Convex ℝ {y | Metric.closedBall y r ⊆ K} := by
  intro x hx y hy a b ha hb hsum
  have hx' : Metric.closedBall x r ⊆ K := hx
  have hy' : Metric.closedBall y r ⊆ K := hy
  intro z hz
  set u := z - (a • x + b • y) with hu_def
  have hu_norm : ‖u‖ ≤ r := by
    rw [hu_def]
    rw [Metric.mem_closedBall] at hz
    rwa [dist_eq_norm] at hz
  have hz_eq : z = a • (x + u) + b • (y + u) := by
    calc
      z = (a • x + b • y) + u := by
        dsimp [u]
        abel
      _ = a • x + b • y + u := rfl
      _ = a • x + b • y + (1 : ℝ) • u := by simp
      _ = a • x + b • y + ((a + b) : ℝ) • u := by rw [hsum]
      _ = a • x + b • y + (a • u + b • u) := by rw [add_smul]
      _ = (a • x + a • u) + (b • y + b • u) := by abel
      _ = a • (x + u) + b • (y + u) := by simp [smul_add]
  have hxu : x + u ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [add_sub_cancel_left, hu_norm]
  have hyu : y + u ∈ Metric.closedBall y r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [add_sub_cancel_left, hu_norm]
  have hxK : x + u ∈ K := hx' hxu
  have hyK : y + u ∈ K := hy' hyu
  rw [hz_eq]
  exact hK hxK hyK ha hb hsum

open Set in
theorem AdversarialBco.isCompact_inner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hK : IsCompact K) (r : ℝ) (hr : 0 ≤ r) : IsCompact {y | Metric.closedBall y r ⊆ K} := by
  have hJ_sub_K : {y | Metric.closedBall y r ⊆ K} ⊆ K := by
    intro y hy
    have hy_self : y ∈ Metric.closedBall y r := Metric.mem_closedBall_self hr
    exact hy hy_self
  have hK_closed : IsClosed K := hK.isClosed
  have hJ_closed : IsClosed {y | Metric.closedBall y r ⊆ K} := by
    have h_eq : {y | Metric.closedBall y r ⊆ K} = ⋂ (u : F) (_ : ‖u‖ ≤ r), {y | y + u ∈ K} := by
      ext y
      constructor
      · intro hy
        rw [Set.mem_iInter₂]
        intro u hu
        have hmem : y + u ∈ Metric.closedBall y r := by
          rw [Metric.mem_closedBall', dist_eq_norm]
          simp
          exact hu
        exact hy hmem
      · intro hy
        rw [Set.mem_iInter₂] at hy
        intro z hz
        rw [Metric.mem_closedBall'] at hz
        have hnorm : ‖z - y‖ ≤ r := by
          have : dist y z = ‖y - z‖ := dist_eq_norm y z
          rw [this] at hz
          simpa [norm_sub_rev] using hz
        have hmem := hy (z - y) hnorm
        simpa [add_sub_cancel] using hmem
    rw [h_eq]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro hu
    have h_cont : Continuous (fun (y : F) => y + u) :=
      continuous_id.add continuous_const
    exact IsClosed.preimage h_cont hK_closed
  exact IsCompact.of_isClosed_subset hK hJ_closed hJ_sub_K

theorem AdversarialBco.closedBall_subset_inner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (c : F) (hc : Metric.closedBall c 1 ⊆ K) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Metric.closedBall c (1 - r) ⊆ {y | Metric.closedBall y r ⊆ K} := by
  intro y hy
  have hdist : dist y c ≤ 1 - r := hy
  have hsum : r + dist y c ≤ 1 := by
    linarith
  have hsubset : Metric.closedBall y r ⊆ Metric.closedBall c 1 :=
    Metric.closedBall_subset_closedBall' hsum
  exact Set.Subset.trans hsubset hc

theorem AdversarialBco.two_le_diam {d : ℕ} (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : Bornology.IsBounded K) (c : EuclideanSpace ℝ (Fin d)) (hc : Metric.closedBall c 1 ⊆ K) :
    2 ≤ Metric.diam K := by
  have hpos : 0 < d := by omega
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hpos⟩ (1 : ℝ)
  have he_norm : ‖e‖ = 1 := by
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1)]
  have h_add : c + e ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, he_norm]
  have h_sub : c - e ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [he_norm]
  have h_addK : c + e ∈ K := hc h_add
  have h_subK : c - e ∈ K := hc h_sub
  have h_dist : dist (c + e) (c - e) = 2 := by
    rw [dist_eq_norm]
    calc
      ‖(c + e) - (c - e)‖ = ‖((c + e) - c) + e‖ := by abel
      _ = ‖e + e‖ := by simp
      _ = ‖(2 : ℝ) • e‖ := by rw [two_smul]
      _ = |(2 : ℝ)| * ‖e‖ := norm_smul _ _
      _ = 2 * ‖e‖ := by norm_num
      _ = 2 * 1 := by rw [he_norm]
      _ = 2 := by norm_num
  have h_le : dist (c + e) (c - e) ≤ Metric.diam K :=
    Metric.dist_le_diam_of_mem hK h_addK h_subK
  linarith

theorem AdversarialBco.abs_sub_le_inner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (f : F → ℝ) (hf : ConvexOn ℝ K f) (h01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 1 ≤ n) (x y : F)
    (hx : Metric.closedBall x (1 / (n : ℝ)) ⊆ K) (hy : Metric.closedBall y (1 / (n : ℝ)) ⊆ K) :
    |f x - f y| ≤ n * ‖x - y‖ := by
  set r := 1 / (n : ℝ) with hr
  have hnpos_nat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hrpos : 0 < r := by
    rw [hr]
    exact div_pos (by norm_num) hnpos
  have h_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hx_mem : x ∈ K := hx (Metric.mem_closedBall_self h_nonneg)
  have hy_mem : y ∈ K := hy (Metric.mem_closedBall_self h_nonneg)
  have h1 : f x - f y ≤ ‖x - y‖ / r :=
    AdversarialBco.sub_le_of_convex_bdd K f hf h01 r hrpos x y hx hy_mem
  have h2 : f y - f x ≤ ‖y - x‖ / r :=
    AdversarialBco.sub_le_of_convex_bdd K f hf h01 r hrpos y x hy hx_mem
  have h_norm : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  rw [h_norm] at h2
  have h_div : ‖x - y‖ / r = (n : ℝ) * ‖x - y‖ := by
    rw [hr]
    field_simp [hnpos.ne']
  rw [h_div] at h1 h2
  exact (abs_sub_le_iff).mpr ⟨h1, h2⟩

theorem AdversarialBco.sInf_inner_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set F)
    (hK : Convex ℝ K) (c : F) (hc : Metric.closedBall c 1 ⊆ K) (n : ℕ) (hn : 1 ≤ n) (f : ℕ → F → ℝ)
    (hf : ∀ t < n, ConvexOn ℝ K (f t)) (h01 : ∀ t < n, ∀ x ∈ K, f t x ∈ Set.Icc (0 : ℝ) 1) :
    sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K}) ≤
      sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) + 1 := by
  set s := (1 : ℝ) / (n : ℝ) with hs_def
  set S := (fun x => ∑ t ∈ Finset.range n, f t x) with hS_def
  set J := {y | Metric.closedBall y s ⊆ K} with hJ_def
  have hnpos' : (n : ℝ) ≠ 0 := by
    intro hzero
    have hn0 : (n : ℕ) = 0 := by exact_mod_cast hzero
    linarith
  have hs0 : 0 ≤ s := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : s ≤ 1 := by
    have hnpos : 0 < (n : ℝ) := by linarith
    exact (div_le_one hnpos).mpr h1n
  have hc_mem_K : c ∈ K := hc (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  have hJ_sub_K : J ⊆ K := by
    intro y hy
    have hy' : y ∈ Metric.closedBall y s := Metric.mem_closedBall_self hs0
    exact hy hy'
  have hsum_le : ∀ x ∈ K, S ((1 - s) • x + s • c) ≤ S x + 1 := by
    intro x hx
    calc
      S ((1 - s) • x + s • c) = ∑ t ∈ Finset.range n, f t ((1 - s) • x + s • c) := rfl
      _ ≤ ∑ t ∈ Finset.range n, (f t x + s) := by
        refine Finset.sum_le_sum ?_
        intro t ht
        have ht_n : t < n := Finset.mem_range.1 ht
        exact convex_comb_le K (f t) (hf t ht_n) (h01 t ht_n) x c hx hc_mem_K s hs0 hs1
      _ = (∑ t ∈ Finset.range n, f t x) + (∑ _t ∈ Finset.range n, s) := by
        rw [Finset.sum_add_distrib]
      _ = S x + ((Finset.card (Finset.range n) : ℝ) * s) := by
        simp [hS_def, Finset.sum_const, nsmul_eq_mul]
      _ = S x + ((n : ℝ) * s) := by simp
      _ = S x + ((n : ℝ) * ((1 : ℝ) / (n : ℝ))) := rfl
      _ = S x + 1 := by field_simp [hnpos']
  have h_forall_x : ∀ x ∈ K, sInf (S '' J) ≤ S x + 1 := by
    intro x hx
    set y := (1 - s) • x + s • c with hy_def
    have hy_J : y ∈ J := by
      have hball : Metric.closedBall y s ⊆ K :=
        closedBall_shrink_subset K hK c hc x hx s hs0 hs1
      exact hball
    have hSy_le : S y ≤ S x + 1 := hsum_le x hx
    have hbdd : BddBelow (S '' J) := by
      refine ⟨0, ?_⟩
      rintro z ⟨z', hz', rfl⟩
      have hz'K : z' ∈ K := hJ_sub_K hz'
      refine Finset.sum_nonneg ?_
      intro t ht
      have ht_n : t < n := Finset.mem_range.1 ht
      exact (h01 t ht_n z' hz'K).1
    have hmem : S y ∈ S '' J := ⟨y, hy_J, rfl⟩
    have h_inf_le : sInf (S '' J) ≤ S y := csInf_le hbdd hmem
    linarith
  have h_lower_bound : sInf (S '' J) - 1 ≤ sInf (S '' K) := by
    refine le_csInf ?_ ?_
    · exact ⟨S c, c, hc_mem_K, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      have h := h_forall_x x hx
      linarith
  linarith

/-- The per-round minimax of Lemma 7.5, with the
learner's side `Y` convex and not compact, the adversary's side `A` compact convex, from Mathlib's Sion theorem
and a finite subcover. -/
theorem AdversarialBco.mm1 {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] (A : Set E) (hAne : A.Nonempty) (hAc : Convex ℝ A) (hAk : IsCompact A) (Y : Set F)
    (hYc : Convex ℝ Y) (Φ : F → E → ℝ) (hcont : ∀ y ∈ Y, Continuous (Φ y)) (hcave : ∀ y ∈ Y, ConcaveOn ℝ A (Φ y))
    (hYcont : ∀ a ∈ A, ContinuousOn (fun y => Φ y a) Y) (hvex : ∀ a ∈ A, ConvexOn ℝ Y (fun y => Φ y a)) (c : ℝ)
    (h : ∀ a ∈ A, ∃ y ∈ Y, Φ y a < c) : ∃ y ∈ Y, ∀ a ∈ A, Φ y a < c := by
  classical
  -- a finite subcover of `A` by the open sets `{a | Φ y a < c}`
  obtain ⟨s, hsY, hs⟩ : ∃ s : Finset F, ↑s ⊆ Y ∧ A ⊆ ⋃ y ∈ s, {a | Φ y a < c} := by
    have hcov : A ⊆ ⋃ y : Y, {a | Φ y a < c} := fun a ha => by
      obtain ⟨y, hy, hya⟩ := h a ha
      exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hya⟩
    obtain ⟨t, ht⟩ := hAk.elim_finite_subcover (fun y : Y => {a | Φ y a < c})
      (fun y => isOpen_lt (hcont y y.2) continuous_const) hcov
    refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_⟩
    · intro y hy
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hy
      obtain ⟨y', _, rfl⟩ := hy
      exact y'.2
    · intro a ha
      obtain ⟨y, hyt, hya⟩ := Set.mem_iUnion₂.1 (ht ha)
      exact Set.mem_iUnion₂.2 ⟨y, Finset.mem_map_of_mem _ hyt, hya⟩
  -- Sion on `A × Y` for `-Φ`, with the finite set `s`
  have key := Sion.exists_lt_iInf_of_lt_iInf_of_finite (X := A) (Y := Y) (f := fun a y => -Φ y a)
    hAne hAk (fun y hy => (hcont y hy).neg.lowerSemicontinuous.lowerSemicontinuousOn A)
    (fun y hy => (hcave y hy).neg.quasiconvexOn) hYc
    (fun a ha => (hYcont a ha).neg.upperSemicontinuousOn)
    (fun a ha => (hvex a ha).neg.quasiconcaveOn) hAc s.finite_toSet hsY (t := -c)
    (fun a ha => by
      obtain ⟨y, hys, hya⟩ := Set.mem_iUnion₂.1 (hs ha)
      exact ⟨y, hys, neg_lt_neg hya⟩)
  obtain ⟨y0, hy0, hy0a⟩ := key
  exact ⟨y0, hy0, fun a ha => neg_lt_neg_iff.1 (hy0a a ha)⟩

/-- The law of play of a behavioural policy on the tree of action sequences is a
probability. -/
theorem AdversarialBco.sum_prod_policy {C : Type*} [Fintype C] (pol : (t : ℕ) → (Fin t → C) → C → ℝ)
    (hsum : ∀ t h, ∑ c, pol t h c = 1) (n : ℕ) :
    ∑ a : Fin n → C, ∏ t : Fin n, pol t (fun s : Fin t => a (Fin.castLE t.2.le s)) (a t) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ => C)).sum_comp]
    simp only [Fin.snocEquiv_apply, Fintype.sum_prod_type, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last]
    have hcast : ∀ (a : Fin n → C) (t : Fin n) (s : Fin (t : ℕ)) (c : C),
        (Fin.snoc a c : Fin (n + 1) → C) (Fin.castLE (Fin.castSucc t).2.le s) = a (Fin.castLE t.2.le s) := by
      intro a t s c
      have : (Fin.castLE (Fin.castSucc t).2.le s : Fin (n + 1)) = Fin.castSucc (Fin.castLE t.2.le s) := rfl
      rw [this, Fin.snoc_castSucc]
    simp only [hcast]
    rw [Finset.sum_comm, ← ih]
    refine Fintype.sum_congr _ _ fun a => ?_
    have hlast : ∀ c : C, (fun s : Fin ((Fin.last n : Fin (n + 1)) : ℕ) =>
        (Fin.snoc a c : Fin (n + 1) → C) (Fin.castLE (Fin.last n).2.le s)) = fun s : Fin n => a s := by
      intro c; funext s
      exact Fin.snoc_castSucc (α := fun _ => C) (p := a) (x := c) s
    simp only [hlast]
    rw [← Finset.mul_sum, hsum, mul_one]
    rfl

/-- One learner with expected regret at most `B` against every admissible sequence bounds the minimax regret by `B`. -/
theorem AdversarialBco.minimaxRegret_le_of_learner {d : ℕ} (K : Set (AdversarialBco.E d)) (hK : Convex ℝ K) (n : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (pol : (t : ℕ) → Ω → (Fin t → ℝ) → AdversarialBco.E d) (hpol : AdversarialBco.IsLearner K pol)
    (hint : ∀ f ∈ AdversarialBco.Advs K n, Integrable (fun ω => AdversarialBco.regret K f (fun t => pol t ω) n) μ) (B : ℝ)
    (hB : ∀ f ∈ AdversarialBco.Advs K n, AdversarialBco.expReg K μ pol f n ≤ B) :
    AdversarialBco.minimaxRegret K n ≤ B := by
  have h0 : (fun _ _ => (0 : ℝ)) ∈ AdversarialBco.Advs K n :=
    fun t _ => ⟨convexOn_const 0 hK, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩
  -- the regret against the zero sequence is zero for every policy with values in a nonempty set
  have hreg0 : ∀ {Ω' : Type} [MeasurableSpace Ω'] (μ' : Measure Ω')
      (pol' : (t : ℕ) → Ω' → (Fin t → ℝ) → AdversarialBco.E d), K.Nonempty →
      AdversarialBco.expReg K μ' pol' (fun _ _ => 0) n = 0 := by
    intro Ω' _ μ' pol' hne
    unfold AdversarialBco.expReg AdversarialBco.regret
    have : ((fun x => ∑ t ∈ Finset.range n, (fun (_ : ℕ) (_ : AdversarialBco.E d) => (0 : ℝ)) t x) '' K) = {0} := by
      simp only [Finset.sum_const_zero]
      exact hne.image_const 0
    rw [this, csInf_singleton]
    simp
  refine csInf_le_of_le (b := sSup ((fun f => AdversarialBco.expReg K μ pol f n) '' AdversarialBco.Advs K n)) ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    rintro r ⟨Ω', _, μ', hμ', pol', hpol', -, rfl⟩
    have hne : K.Nonempty := by
      obtain ⟨ω⟩ : Nonempty Ω' := by
        by_contra hc
        rw [not_nonempty_iff] at hc
        have := hμ'.measure_univ
        simp [Set.univ_eq_empty_iff.mpr hc] at this
      exact ⟨_, hpol'.2 0 ω Fin.elim0⟩
    by_cases hbdd : BddAbove ((fun f => AdversarialBco.expReg K μ' pol' f n) '' AdversarialBco.Advs K n)
    · rw [← hreg0 μ' pol' hne]
      exact le_csSup hbdd ⟨_, h0, rfl⟩
    · rw [Real.sSup_of_not_bddAbove hbdd]
  · exact ⟨Ω, _, μ, inferInstance, pol, hpol, hint, rfl⟩
  · exact csSup_le ⟨_, ⟨_, h0, rfl⟩⟩ (by rintro r ⟨f, hf, rfl⟩; exact hB f hf)

open MeasureTheory ProbabilityTheory in
theorem AdversarialBco.gaussian_ibp_pi {d : ℕ} (i : Fin d) (H D : (Fin d → ℝ) → ℝ)
    (hH : ∀ w u, HasDerivAt (fun v => H (Function.update w i v)) (D (Function.update w i u)) u)
    (hint1 : Integrable (fun w => w i * H w) (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hint2 : Integrable D (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hint3 : Integrable H (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    ∫ w, w i * H w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      ∫ w, D w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  -- If d = 0, then i : Fin 0 is impossible
  have h_ne_zero : d ≠ 0 := by
    intro h
    have : Fin 0 := by rw [h] at i; exact i
    exact Fin.elim0 this
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h_ne_zero
  subst hk
  -- Now d = k.succ, i : Fin (k.succ)
  let μ := fun _ : Fin (k.succ) => gaussianReal 0 1
  let γ := gaussianReal 0 1
  let ν := Measure.pi fun j : Fin k => μ (i.succAbove j)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k.succ) => ℝ) i).symm
  -- e : ℝ × ((j : Fin k) → ℝ) ≃ᵐ ((j : Fin (k.succ)) → ℝ)
  have h_meas_preserve : MeasurePreserving e ((γ).prod ν) (Measure.pi μ) := by
    have h := measurePreserving_piFinSuccAbove μ i
    exact h.symm
  have h_map_eq : Measure.map e ((γ).prod ν) = Measure.pi μ := h_meas_preserve.map_eq
  -- Use integral_map_equiv to change variables
  have hL : ∫ w, w i * H w ∂(Measure.pi μ) = ∫ (p : ℝ × ((j : Fin k) → ℝ)), (e p) i * H (e p) ∂((γ).prod ν) := by
    rw [← h_map_eq, integral_map_equiv e]
  have hR : ∫ w, D w ∂(Measure.pi μ) = ∫ (p : ℝ × ((j : Fin k) → ℝ)), D (e p) ∂((γ).prod ν) := by
    rw [← h_map_eq, integral_map_equiv e]
  rw [hL, hR]
  -- Key property: (e p) i = p.1
  have h_e_i (p : ℝ × ((j : Fin k) → ℝ)) : (e p) i = p.1 := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp [Fin.insertNthEquiv_apply]
  -- Rewrite using h_e_i
  have hL' : ∫ (p : ℝ × ((j : Fin k) → ℝ)), (e p) i * H (e p) ∂((γ).prod ν) =
            ∫ (p : ℝ × ((j : Fin k) → ℝ)), p.1 * H (e p) ∂((γ).prod ν) := by
    refine integral_congr_ae ?_
    filter_upwards with p
    rw [h_e_i p]
  rw [hL']
  -- Goal: ∫ p, p.1 * H (e p) ∂(γ.prod ν) = ∫ p, D (e p) ∂(γ.prod ν)
  -- Transport integrability hypotheses through the measure-preserving map
  have hint1' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) ((γ).prod ν) := by
    have h1_map : Integrable (fun w => w i * H w) (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h1_comp := (integrable_map_equiv e (fun w => w i * H w) (μ := (γ).prod ν)).mp h1_map
    have : ((fun w => w i * H w) ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) := by
      ext p; simp [h_e_i p]
    rwa [this] at h1_comp
  have hint2' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) ((γ).prod ν) := by
    have h2_map : Integrable D (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h2_comp := (integrable_map_equiv e D (μ := (γ).prod ν)).mp h2_map
    have : (D ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) := rfl
    rwa [this] at h2_comp
  have hint3' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => H (e p)) ((γ).prod ν) := by
    have h3_map : Integrable H (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h3_comp := (integrable_map_equiv e H (μ := (γ).prod ν)).mp h3_map
    have : (H ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => H (e p)) := rfl
    rwa [this] at h3_comp
  -- Now use integral_prod and integral_integral_swap
  rw [integral_prod _ hint1', integral_prod _ hint2']
  simp
  -- Goal: ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), x * H (e (x, w')) ∂ν ∂γ =
  --       ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), D (e (x, w')) ∂ν ∂γ
  -- Now use integral_integral_swap to swap the order of integration
  have h_swap1 : ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), x * H (e (x, w')) ∂ν ∂γ =
                ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), x * H (e (x, w')) ∂γ ∂ν := by
    have h_uncurry : Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => x * H (e (x, w'))) =
                    (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) := by
      ext p; cases p; simp
    have h_int_uncurry : Integrable (Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => x * H (e (x, w')))) ((γ).prod ν) := by
      rwa [h_uncurry]
    rw [integral_integral_swap h_int_uncurry]
  have h_swap2 : ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), D (e (x, w')) ∂ν ∂γ =
                ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), D (e (x, w')) ∂γ ∂ν := by
    have h_uncurry : Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => D (e (x, w'))) =
                    (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) := by
      ext p; cases p; simp
    have h_int_uncurry : Integrable (Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => D (e (x, w')))) ((γ).prod ν) := by
      rwa [h_uncurry]
    rw [integral_integral_swap h_int_uncurry]
  rw [h_swap1, h_swap2]
  -- Goal: ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), x * H (e (x, w')) ∂γ ∂ν =
  --       ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), D (e (x, w')) ∂γ ∂ν
  -- Now apply integral_congr_ae: it suffices to show the inner integrals are equal for a.e. w'
  refine integral_congr_ae ?_
  -- Get the a.e. properties from Fubini
  have h_ae1 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => x * H (e (x, w'))) γ := by
    have h := hint1'.prod_left_ae
    simpa using h
  have h_ae2 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => D (e (x, w'))) γ := by
    have h := hint2'.prod_left_ae
    simpa using h
  have h_ae3 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => H (e (x, w'))) γ := by
    have h := hint3'.prod_left_ae
    simpa using h
  -- Intersect the a.e. sets
  filter_upwards [h_ae1, h_ae2, h_ae3] with w' h1 h2 h3
  -- For a fixed w', define:
  let H_w' := fun (x : ℝ) => H (e (x, w'))
  let D_w' := fun (x : ℝ) => D (e (x, w'))
  -- Need to show: ∫ x, x * H_w'(x) ∂γ = ∫ x, D_w'(x) ∂γ
  -- Apply gaussian_ibp_1d
  have h_deriv (x : ℝ) : HasDerivAt H_w' (D_w' x) x := by
    have h := hH (e (x, w')) x
    -- h : HasDerivAt (fun v => H (Function.update (e (x, w')) i v)) (D (Function.update (e (x, w')) i x)) x
    -- We need to rewrite using the properties of Fin.insertNth
    -- First, note that e = Fin.insertNthEquiv (fun _ => ℝ) i
    -- And Fin.insertNthEquiv_apply gives: e (x, w') = Fin.insertNth i x w'
    -- So we can work with Fin.insertNth directly
    have h_update1 (v : ℝ) : Function.update (e (x, w')) i v = e (v, w') := by
      -- Rewrite e as Fin.insertNth
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      -- Now we need: Function.update (Fin.insertNth i x w') i v = Fin.insertNth i v w'
      -- This is true by the properties of Fin.insertNth
      -- Let's prove it inline
      ext j
      by_cases hji : j = i
      · subst hji; simp [Fin.insertNth_apply_same]
      · have h := Fin.exists_succAbove_eq hji
        obtain ⟨k, hk⟩ := h
        subst hk
        simp [Fin.insertNth_apply_succAbove]
    have h_update2 : Function.update (e (x, w')) i x = e (x, w') := by
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp
    -- Now rewrite h using h_update1 and h_update2
    simpa [h_update1, h_update2, H_w', D_w'] using h
  -- Apply gaussian_ibp_1d
  exact AdversarialBco.gaussian_ibp_1d H_w' D_w' h_deriv h1 h2 h3

open Finset in
theorem AdversarialBco.sum_prod_policy_init {C : Type*} [Fintype C] (pol : (t : ℕ) → (Fin t → C) → C → ℝ)
    (hsum : ∀ t h, ∑ c, pol t h c = 1) (n : ℕ) (g : (Fin n → C) → ℝ) :
    ∑ a : Fin (n + 1) → C, (∏ t : Fin (n + 1), pol t (fun s : Fin t => a (Fin.castLE t.2.le s)) (a t)) *
        g (Fin.init a) =
      ∑ a : Fin n → C, (∏ t : Fin n, pol t (fun s : Fin t => a (Fin.castLE t.2.le s)) (a t)) * g a := by
  -- Step 1: Use Fin.snocEquiv to rewrite the sum over Fin (n+1) → C
  rw [← (Fin.snocEquiv (fun _ => C)).sum_comp]
  -- Simplify (Fin.snocEquiv ...) x to Fin.snoc x.2 x.1
  have h_snocEquiv : ∀ (x : C × (Fin n → C)), (Fin.snocEquiv (fun _ => C)) x = Fin.snoc x.2 x.1 := by
    intro x
    ext i
    simp [Fin.snocEquiv_apply]
  simp only [h_snocEquiv]
  -- Split the product sum
  rw [Fintype.sum_prod_type]
  -- Simplify Fin.init (Fin.snoc a' c) = a'
  simp only [Fin.init_snoc]
  -- Now: ∑ c, ∑ a', (∏ t : Fin (n+1), pol t (fun s => Fin.snoc a' c (Fin.castLE t.2.le s)) (Fin.snoc a' c t)) * g a' = ∑ a, (∏ t, pol t ...) * g a
  -- Step 2: For each a', prove the inner equality
  have h_inner : ∀ (a' : Fin n → C), ∑ c : C, (∏ t : Fin (n + 1), pol t (fun s : Fin t => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE t.2.le s)) ((Fin.snoc a' c : Fin (n + 1) → C) t)) =
      (∏ t : Fin n, pol t (fun s : Fin t => a' (Fin.castLE t.2.le s)) (a' t)) := by
    intro a'
    -- For each c, we have an equality of products
    have h_per_c : ∀ (c : C), (∏ t : Fin (n + 1), pol t (fun s : Fin t => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE t.2.le s)) ((Fin.snoc a' c : Fin (n + 1) → C) t)) =
        (∏ t : Fin n, pol t (fun s : Fin t => a' (Fin.castLE t.2.le s)) (a' t)) * pol n a' c := by
      intro c
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      -- Simplify the history functions
      have h_hist1 : ∀ (x : Fin n), (fun s : Fin x => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE (Fin.castSucc x).2.le s)) = (fun s : Fin x => a' (Fin.castLE x.2.le s)) := by
        intro x
        ext s
        have hcast : Fin.castLE (Fin.castSucc x).2.le s = Fin.castSucc (Fin.castLE x.2.le s) := by rfl
        rw [hcast]
        exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => C) c a' (Fin.castLE x.2.le s)
      have h_hist2 : (fun s : Fin (Fin.last n) => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE (Fin.last n).2.le s)) = a' := by
        ext s
        have hcast : Fin.castLE (Fin.last n).2.le s = Fin.castSucc s := by rfl
        rw [hcast]
        exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => C) c a' s
      rw [h_hist2]
      simp [h_hist1]
    -- Now use h_per_c to rewrite the sum
    rw [Finset.sum_congr rfl fun c _ => by rw [h_per_c c]]
    -- Factor out the product (which doesn't depend on c)
    rw [← Finset.mul_sum]
    -- Use hsum
    rw [hsum n a']
    -- Simplify 1 * x = x
    simp
  -- Step 3: Use h_inner to rewrite the LHS
  calc
    ∑ c : C, ∑ a' : Fin n → C, (∏ t : Fin (n + 1), pol t (fun s : Fin t => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE t.2.le s)) ((Fin.snoc a' c : Fin (n + 1) → C) t)) * g a'
        = ∑ a' : Fin n → C, ∑ c : C, (∏ t : Fin (n + 1), pol t (fun s : Fin t => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE t.2.le s)) ((Fin.snoc a' c : Fin (n + 1) → C) t)) * g a' := by
      rw [Finset.sum_comm]
    _ = ∑ a' : Fin n → C, (∑ c : C, (∏ t : Fin (n + 1), pol t (fun s : Fin t => (Fin.snoc a' c : Fin (n + 1) → C) (Fin.castLE t.2.le s)) ((Fin.snoc a' c : Fin (n + 1) → C) t))) * g a' := by
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.sum_mul]
    _ = ∑ a' : Fin n → C, (∏ t : Fin n, pol t (fun s : Fin t => a' (Fin.castLE t.2.le s)) (a' t)) * g a' := by
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [h_inner a']
    _ = ∑ a : Fin n → C, (∏ t : Fin n, pol t (fun s : Fin t => a (Fin.castLE t.2.le s)) (a t)) * g a := rfl

/-- The cumulative sums `F p k = ∑ j < k, p j` of the inverse distribution sampler. -/
def AdversarialBco.Sampler.F {m : ℕ} (p : Fin (m + 1) → ℝ) (k : ℕ) : ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k)) p

namespace AdversarialBco.Sampler

variable {m : ℕ}

open MeasureTheory Set Finset

-- Count of k ∈ {1,...,m} such that F p k ≤ u
noncomputable def N (p : Fin (m + 1) → ℝ) (u : ℝ) : ℕ :=
  Finset.sum (Finset.Icc 1 m) (fun k => if F p k ≤ u then 1 else 0)

lemma N_lt_succ_m (p : Fin (m + 1) → ℝ) (u : ℝ) : N p u < m + 1 := by
  have h : N p u ≤ m := by
    unfold N
    calc
      Finset.sum (Finset.Icc 1 m) (fun k => if F p k ≤ u then (1 : ℕ) else 0) ≤
          Finset.sum (Finset.Icc 1 m) (fun _ => (1 : ℕ)) :=
        Finset.sum_le_sum (fun k hk => by
          split <;> simp)
      _ = (Finset.Icc 1 m).card := by simp
      _ = m := by
        rw [Nat.card_Icc]
        omega
  exact Nat.lt_succ_of_le h

-- The sampler function
noncomputable def S (p : Fin (m + 1) → ℝ) (u : ℝ) : Fin (m + 1) :=
  ⟨N p u, N_lt_succ_m p u⟩

lemma S_eq_iff (p : Fin (m + 1) → ℝ) (u : ℝ) (i : Fin (m + 1)) : S p u = i ↔ N p u = (i : ℕ) := by
  constructor
  · intro h; simpa [S] using congrArg Fin.val h
  · intro h; ext; simpa [S, h] using rfl

-- Key lemma: monotonicity of F when p ≥ 0
lemma F_mono (p : Fin (m + 1) → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : F p k₁ ≤ F p k₂ := by
  unfold F
  -- The set of j < k₁ is a subset of the set of j < k₂
  -- Since p_j ≥ 0, the sum over the smaller set is ≤ the sum over the larger set
  have h_subset : ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k₁)) ⊆
      ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k₂)) := by
    intro j hj
    simp at hj ⊢
    exact lt_of_lt_of_le hj h
  -- Now use sum_le_sum_of_subset_of_nonneg
  refine Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun j _ hj_not => ?_)
  -- For j not in the smaller set, we need 0 ≤ p j, which is hp_nonneg
  exact hp_nonneg j

-- F p 0 = 0
@[simp]
lemma F_zero (p : Fin (m + 1) → ℝ) : F p 0 = 0 := by
  unfold F
  simp

-- F p (m+1) = 1 when p sums to 1
lemma F_succ_m (p : Fin (m + 1) → ℝ) (hp_sum : ∑ i, p i = 1) : F p (m + 1) = 1 := by
  unfold F
  have h_filter : ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < m + 1)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro j hj
    have hj_val : (j : ℕ) < m + 1 := Fin.is_lt j
    simpa using hj_val
  rw [h_filter]
  simpa using hp_sum

-- The key equivalence: N p u = i ↔ F p i ≤ u ∧ (i < m → u < F p (i+1))
-- under the conditions p ≥ 0, sum = 1, u ∈ [0,1], i ≤ m
lemma N_eq_iff {u : ℝ} {i : ℕ} (p : Fin (m + 1) → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hi : (i : ℕ) ≤ m) :
    N p u = (i : ℕ) ↔ F p (i : ℕ) ≤ u ∧ ((i : ℕ) < m → u < F p ((i : ℕ) + 1)) := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  -- Define the set of k ∈ Icc 1 m such that F p k ≤ u
  let B := (Finset.Icc 1 m).filter (fun k => F p k ≤ u)
  have hN_eq_card : N p u = B.card := by
    unfold N B
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  -- B is downward closed: if k ∈ B and 1 ≤ j ≤ k, then j ∈ B
  have hB_downward (k : ℕ) (hk : k ∈ B) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ k) : j ∈ B := by
    unfold B at hk ⊢
    simp at hk ⊢
    rcases hk with ⟨⟨hk1, hk2⟩, hkF⟩
    have hjF : F p j ≤ u := by
      -- F p j ≤ F p k ≤ u by monotonicity
      have hF : F p j ≤ F p k := F_mono p hp_nonneg hj2
      linarith
    exact ⟨⟨hj1, le_trans hj2 hk2⟩, hjF⟩
  constructor
  · intro hN
    have h_card : B.card = (i : ℕ) := by
      rw [← hN_eq_card, hN]
    have h_le : F p (i : ℕ) ≤ u := by
      by_cases hi0 : (i : ℕ) = 0
      · subst hi0; simp [F_zero, hu0]
      · have hi_pos : 1 ≤ (i : ℕ) := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi0)
        have hi_mem_Icc : (i : ℕ) ∈ Finset.Icc 1 m :=
          Finset.mem_Icc.mpr ⟨hi_pos, hi⟩
        -- If F p i > u, then i ∉ B, and by downward closure, no k ≥ i is in B
        -- So B ⊆ Icc 1 (i-1), which has card ≤ i-1 < i, contradicting card = i
        by_contra! hgt
        -- hgt: u < F p i, so i ∉ B
        have hi_not_mem_B : (i : ℕ) ∉ B := by
          unfold B
          rw [Finset.mem_filter, Finset.mem_Icc]
          intro h
          have h1 : 1 ≤ (i : ℕ) := h.1.1
          have h2 : (i : ℕ) ≤ m := h.1.2
          have hF : F p (i : ℕ) ≤ u := h.2
          have : u < u := lt_of_lt_of_le hgt hF
          exact lt_irrefl _ this
        -- All elements of B are < i
        have hB_subset : B ⊆ Finset.Icc 1 ((i : ℕ) - 1) := by
          intro k hk
          have hk_mem : k ∈ Finset.Icc 1 m := (Finset.mem_filter.mp hk).1
          rcases Finset.mem_Icc.mp hk_mem with ⟨hk1, hk2⟩
          have hk_lt_i : k < (i : ℕ) := by
            by_contra! hge
            -- k ≥ i, so by downward closure, i ∈ B, contradiction
            have : (i : ℕ) ∈ B := hB_downward k hk (i : ℕ) hi_pos hge
            exact hi_not_mem_B this
          refine Finset.mem_Icc.mpr ⟨hk1, ?_⟩
          omega
        -- Now card(B) ≤ card(Icc 1 (i-1)) = i-1 < i
        have h_card_le : B.card ≤ ((Finset.Icc 1 ((i : ℕ) - 1)).card : ℕ) :=
          Finset.card_le_card hB_subset
        have h_card_Icc : (Finset.Icc 1 ((i : ℕ) - 1)).card = (i : ℕ) - 1 := by
          rw [Nat.card_Icc]
          omega
        rw [h_card_Icc] at h_card_le
        rw [h_card] at h_card_le
        omega
    have h_lt : (i : ℕ) < m → u < F p ((i : ℕ) + 1) := by
      intro hi_lt_m
      by_contra! hge
      -- hge: F p (i+1) ≤ u, so i+1 ∈ B
      have hi_succ_mem_Icc : (i : ℕ) + 1 ∈ Finset.Icc 1 m :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hi_succ_mem_B : (i : ℕ) + 1 ∈ B := by
        unfold B; simp [hi_succ_mem_Icc, hge]
      -- Since i+1 ∈ B, by downward closure, all j ≤ i+1 are in B
      -- In particular, Icc 1 (i+1) ⊆ B
      have h_subset : Finset.Icc 1 ((i : ℕ) + 1) ⊆ B := by
        intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
        exact hB_downward ((i : ℕ) + 1) hi_succ_mem_B j hj1 hj2
      have h_card_subset : (Finset.Icc 1 ((i : ℕ) + 1)).card ≤ B.card :=
        Finset.card_le_card h_subset
      have h_card_Icc_succ : (Finset.Icc 1 ((i : ℕ) + 1)).card = (i : ℕ) + 1 := by
        rw [Nat.card_Icc]
        omega
      rw [h_card_Icc_succ] at h_card_subset
      rw [h_card] at h_card_subset
      omega
    exact ⟨h_le, h_lt⟩
  · intro ⟨h_le, h_lt⟩
    -- Need to show N p u = i, i.e., B.card = i
    -- Since F p i ≤ u, all k ≤ i are in B (by downward closure)
    -- Since i < m → u < F p (i+1), all k > i are not in B
    -- So B = Icc 1 i, and card = i
    have hB_eq : B = Finset.Icc 1 (i : ℕ) := by
      apply Finset.Subset.antisymm ?_ ?_
      · -- B ⊆ Icc 1 i
        intro k hk
        have hk_mem : k ∈ Finset.Icc 1 m := (Finset.mem_filter.mp hk).1
        rcases Finset.mem_Icc.mp hk_mem with ⟨hk1, hk2⟩
        have hk_le_i : k ≤ (i : ℕ) := by
          by_contra! hgt
          -- k > i, so k ≥ i+1
          have hk_ge_succ : (i : ℕ) + 1 ≤ k := by omega
          -- By downward closure from k, we get i+1 ∈ B
          have hi_succ_mem_B : (i : ℕ) + 1 ∈ B := hB_downward k hk ((i : ℕ) + 1) (by omega) hk_ge_succ
          -- But if i < m, then u < F p (i+1), so i+1 ∉ B
          by_cases hi_lt_m : (i : ℕ) < m
          · have h_not_mem : (i : ℕ) + 1 ∉ B := by
              unfold B
              rw [Finset.mem_filter, Finset.mem_Icc]
              intro h
              have h1 : 1 ≤ (i : ℕ) + 1 := h.1.1
              have h2 : (i : ℕ) + 1 ≤ m := h.1.2
              have hF : F p ((i : ℕ) + 1) ≤ u := h.2
              have h_lt' : u < F p ((i : ℕ) + 1) := h_lt hi_lt_m
              have : u < u := lt_of_lt_of_le h_lt' hF
              exact lt_irrefl _ this
            exact h_not_mem hi_succ_mem_B
          · -- i = m, but then i+1 > m, and k ≤ m, so k ≥ i+1 > m contradicts k ≤ m
            omega
        refine Finset.mem_Icc.mpr ⟨hk1, hk_le_i⟩
      · -- Icc 1 i ⊆ B
        intro k hk
        rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
        have hkF : F p k ≤ u := by
          -- k ≤ i, so F p k ≤ F p i ≤ u
          have hF : F p k ≤ F p (i : ℕ) := F_mono p hp_nonneg hk2
          linarith
        have hk_mem_Icc : k ∈ Finset.Icc 1 m :=
          Finset.mem_Icc.mpr ⟨hk1, le_trans hk2 hi⟩
        unfold B; simp [hk_mem_Icc, hkF]
    rw [hN_eq_card, hB_eq]
    -- card(Icc 1 i) = i
    rw [Nat.card_Icc]
    omega

-- Measurability of S
lemma S_measurable (m : ℕ) : Measurable (fun q : (Fin (m + 1) → ℝ) × ℝ => S q.1 q.2) := by
  -- For each k, the set A_k = {q | F q.1 k ≤ q.2} is closed, hence measurable
  have h_closed (k : ℕ) : IsClosed {q : (Fin (m + 1) → ℝ) × ℝ | F q.1 k ≤ q.2} := by
    have h_cont : Continuous (fun (q : (Fin (m + 1) → ℝ) × ℝ) => F q.1 k - q.2) := by
      refine Continuous.sub ?_ continuous_snd
      refine continuous_finsetSum _ (fun j hj => ?_)
      exact Continuous.comp (continuous_apply j) continuous_fst
    have h_closed_set : IsClosed {t : ℝ | t ≤ 0} := isClosed_Iic
    have h_eq : {q : (Fin (m + 1) → ℝ) × ℝ | F q.1 k ≤ q.2} = {q | F q.1 k - q.2 ≤ 0} := by
      ext q; simp
    rw [h_eq]
    exact IsClosed.preimage h_cont h_closed_set
  have hA_meas (k : ℕ) : MeasurableSet {q : (Fin (m + 1) → ℝ) × ℝ | F q.1 k ≤ q.2} :=
    (h_closed k).measurableSet
  -- Define indicator function I_k(q) = 1 if F q.1 k ≤ q.2 else 0
  let I (k : ℕ) (q : (Fin (m + 1) → ℝ) × ℝ) : ℕ :=
    if F q.1 k ≤ q.2 then 1 else 0
  have hI_meas (k : ℕ) : Measurable (I k) := by
    refine measurable_to_countable' (fun (n : ℕ) => ?_)
    -- Goal: MeasurableSet (I k ⁻¹' {n})
    by_cases hn1 : n = 1
    · subst hn1
      have h_eq : I k ⁻¹' {1} = {q : (Fin (m + 1) → ℝ) × ℝ | F q.1 k ≤ q.2} := by
        ext q; unfold I; simp
      rw [h_eq]; exact hA_meas k
    · by_cases hn0 : n = 0
      · subst hn0
        have h_eq : I k ⁻¹' {0} = {q : (Fin (m + 1) → ℝ) × ℝ | F q.1 k ≤ q.2}ᶜ := by
          ext q; unfold I; simp
        rw [h_eq]; exact (hA_meas k).compl
      · have h_empty : I k ⁻¹' {n} = ∅ := by
          ext q; unfold I
          by_cases h : F q.1 k ≤ q.2
          · simp [h]
            intro h_eq; apply hn1; symm; exact h_eq
          · simp [h]
            intro h_eq; apply hn0; symm; exact h_eq
        rw [h_empty]; exact MeasurableSet.empty
  -- N(q) = Σ_{k ∈ Icc 1 m} I_k(q)
  have hN_meas : Measurable (fun (q : (Fin (m + 1) → ℝ) × ℝ) => N q.1 q.2) := by
    -- N q = Σ k ∈ Icc 1 m, I k q
    -- This is a finite sum of measurable ℕ-valued functions
    -- Finset.measurable_fun_sum works because ℕ has MeasurableAdd₂
    -- We can write N q directly as the sum
    simpa [N, I] using Finset.measurable_fun_sum (Finset.Icc 1 m) (fun k hk => hI_meas k)
  -- S = Fin.ofNat ∘ N
  have hS_meas : Measurable (fun q : (Fin (m + 1) → ℝ) × ℝ => S q.1 q.2) := by
    -- Use measurable_to_countable' for Fin (m+1)
    refine measurable_to_countable' (fun (i : Fin (m + 1)) => ?_)
    -- Goal: MeasurableSet ((fun q => S q.1 q.2) ⁻¹' {i})
    -- This equals {q | S q.1 q.2 = i} which equals {q | N q.1 q.2 = i.val}
    have h_eq : (fun q : (Fin (m + 1) → ℝ) × ℝ => S q.1 q.2) ⁻¹' {i} =
        {q : (Fin (m + 1) → ℝ) × ℝ | N q.1 q.2 = (i : ℕ)} := by
      ext q; simp [S_eq_iff]
    rw [h_eq]
    -- Now we need MeasurableSet {q | N q.1 q.2 = i.val}
    -- This is N⁻¹'({i.val})
    -- Since N is measurable and {i.val} is measurable (singleton in ℕ)
    exact hN_meas (MeasurableSet.singleton (i : ℕ))
  exact hS_meas

-- F p (k+1) = F p k + p k when k < m+1 (i.e., k is a valid Fin index)
lemma F_succ_eq_add (p : Fin (m + 1) → ℝ) (k : ℕ) (hk : k < m + 1) : F p (k + 1) = F p k + p ⟨k, hk⟩ := by
  unfold F
  -- Goal: sum over {j | j < k+1} p j = sum over {j | j < k} p j + p ⟨k, hk⟩
  -- The set {j | j < k+1} = {j | j < k} ∪ {⟨k, hk⟩} (disjoint)
  have h_disjoint : Disjoint ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k))
      ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) = k)) := by
    rw [Finset.disjoint_filter]
    intro j hj_univ hj_lt
    -- hj_lt: (j : ℕ) < k
    -- Need to show ¬ ((j : ℕ) = k)
    omega
  have h_union : ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k + 1)) =
      ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) < k)) ∪
      ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) = k)) := by
    ext j; simp; omega
  rw [h_union, Finset.sum_union h_disjoint]
  congr 1
  -- The second filter has exactly one element: ⟨k, hk⟩
  have h_singleton : ((Finset.univ : Finset (Fin (m + 1))).filter (fun (j : Fin (m + 1)) => (j : ℕ) = k)) = {⟨k, hk⟩} := by
    ext j; constructor
    · intro h
      rw [Finset.mem_filter] at h
      rcases h with ⟨_, h_eq⟩
      -- h_eq : (j : ℕ) = k
      apply Finset.mem_singleton.mpr
      apply Fin.ext
      simpa using h_eq
    · intro h
      rw [Finset.mem_singleton] at h
      subst h
      simp
  rw [h_singleton, Finset.sum_singleton]

-- Volume of the fiber
lemma volume_fiber_eq (p : Fin (m + 1) → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (i : Fin (m + 1)) : volume (Set.Icc (0 : ℝ) 1 ∩ (S p) ⁻¹' {i}) = ENNReal.ofReal (p i) := by
  let i' := (i : ℕ)
  have hi'_le_m : i' ≤ m := by
    have := i.2
    omega
  by_cases hi'_lt_m : i' < m
  · -- i' < m: fiber = Ico (F p i') (F p (i'+1))
    have h_fiber_eq : Set.Icc (0 : ℝ) 1 ∩ (S p) ⁻¹' {i} = Set.Ico (F p i') (F p (i' + 1)) := by
      ext u
      constructor
      · intro ⟨⟨hu0, hu1⟩, huS⟩
        have hS : S p u = i := huS
        have hN : N p u = (i : ℕ) := (S_eq_iff p u i).mp hS
        have hN' : N p u = i' := by simpa [i'] using hN
        have h_cond := (N_eq_iff p hp_nonneg hp_sum ⟨hu0, hu1⟩ hi'_le_m).mp hN'
        rcases h_cond with ⟨h_le, h_lt⟩
        exact ⟨h_le, h_lt hi'_lt_m⟩
      · intro ⟨h_le, h_lt⟩
        have hu0 : 0 ≤ u := by
          have hF0 : 0 ≤ F p i' := by
            have := F_mono p hp_nonneg (Nat.zero_le i')
            rw [F_zero] at this; exact this
          linarith
        have hu1 : u ≤ 1 := by
          have hF_succ : F p (i' + 1) ≤ F p (m + 1) :=
            F_mono p hp_nonneg (by omega)
          rw [F_succ_m p hp_sum] at hF_succ
          linarith
        have hN : N p u = i' :=
          ((N_eq_iff p hp_nonneg hp_sum ⟨hu0, hu1⟩ hi'_le_m).mpr ⟨h_le, fun _ => h_lt⟩)
        have hS : S p u = i := (S_eq_iff p u i).mpr (by simpa [i'] using hN)
        exact ⟨⟨hu0, hu1⟩, hS⟩
    rw [h_fiber_eq, Real.volume_Ico]
    have h_diff : F p (i' + 1) - F p i' = p i := by
      have hk : i' < m + 1 := by omega
      rw [F_succ_eq_add p i' hk]
      -- Goal: (F p i' + p ⟨i', hk⟩) - F p i' = p i
      -- Using add_sub_cancel_left: (a + b) - a = b
      -- So the LHS simplifies to p ⟨i', hk⟩
      -- But we need to also show p ⟨i', hk⟩ = p i
      -- This is true because ⟨i', hk⟩ = i (both have value i')
      -- Let's prove this directly
      have h_eq : (⟨i', hk⟩ : Fin (m + 1)) = i := Fin.ext rfl
      -- Now compute:
      calc
        (F p i' + p ⟨i', hk⟩) - F p i' = p ⟨i', hk⟩ := by rw [add_sub_cancel_left]
        _ = p i := by rw [h_eq]
    rw [h_diff]
  · -- i' = m
    have hi'_eq_m : i' = m := by omega
    have h_fiber_eq : Set.Icc (0 : ℝ) 1 ∩ (S p) ⁻¹' {i} = Set.Icc (F p m) 1 := by
      ext u
      constructor
      · intro ⟨⟨hu0, hu1⟩, huS⟩
        have hS : S p u = i := huS
        have hN : N p u = (i : ℕ) := (S_eq_iff p u i).mp hS
        -- (i : ℕ) = i' = m
        have hN' : N p u = m := by simpa [i', hi'_eq_m] using hN
        have h_cond := (N_eq_iff p hp_nonneg hp_sum ⟨hu0, hu1⟩ (le_refl m)).mp hN'
        rcases h_cond with ⟨h_le, _⟩
        exact ⟨h_le, hu1⟩
      · intro ⟨h_le, hu1⟩
        have hu0 : 0 ≤ u := by
          have hF0 : 0 ≤ F p m := by
            have := F_mono p hp_nonneg (Nat.zero_le m)
            rw [F_zero] at this; exact this
          linarith
        have hN : N p u = m :=
          ((N_eq_iff p hp_nonneg hp_sum ⟨hu0, hu1⟩ (le_refl m)).mpr ⟨h_le, fun h => (by omega)⟩)
        have hN' : N p u = (i : ℕ) := by simpa [i', hi'_eq_m] using hN
        have hS : S p u = i := (S_eq_iff p u i).mpr hN'
        exact ⟨⟨hu0, hu1⟩, hS⟩
    rw [h_fiber_eq, Real.volume_Icc]
    have h_diff : (1 : ℝ) - F p m = p i := by
      have h := F_succ_m p hp_sum
      have hk : m < m + 1 := by omega
      rw [F_succ_eq_add p m hk] at h
      -- h: F p m + p ⟨m, hk⟩ = 1
      -- Goal: 1 - F p m = p i
      -- Since i' = (i : ℕ) = m, we have i.val = m
      -- So p i = p ⟨m, hk⟩
      have hi_val : (i : ℕ) = m := by
        dsimp [i'] at hi'_eq_m
        exact hi'_eq_m
      have hp_eq : p i = p ⟨m, hk⟩ := by
        congr
        apply Fin.ext
        simpa [hi_val]
      rw [hp_eq]
      linarith
    rw [h_diff]

end AdversarialBco.Sampler

open MeasureTheory Set Finset AdversarialBco.Sampler in
theorem AdversarialBco.exists_sampler (m : ℕ) :
    ∃ S : (Fin (m + 1) → ℝ) → ℝ → Fin (m + 1), Measurable (fun q : (Fin (m + 1) → ℝ) × ℝ => S q.1 q.2) ∧
      ∀ p : Fin (m + 1) → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        ∀ i, volume (Set.Icc (0 : ℝ) 1 ∩ S p ⁻¹' {i}) = ENNReal.ofReal (p i) := by
  refine ⟨S, ?_, ?_⟩
  · exact S_measurable m
  · intro p hp_nonneg hp_sum i
    exact volume_fiber_eq p hp_nonneg hp_sum i

open MeasureTheory in
theorem AdversarialBco.scale_layer_cake {ι : Type*} [Fintype ι] (w g : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hgb : ∀ i, g i ≤ b) :
    IntervalIntegrable (fun t => ∑ j ∈ Finset.univ.filter (fun j => t ≤ g j), w j) volume a b ∧
      ∑ i, w i * max (g i - a) 0 = ∫ t in a..b, ∑ j ∈ Finset.univ.filter (fun j => t ≤ g j), w j := by
  -- First, rewrite the sum using indicator functions
  have h_sum_eq : (fun (t : ℝ) => ∑ j ∈ Finset.univ.filter (fun j => t ≤ g j), w j) =
      (fun (t : ℝ) => ∑ j : ι, ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t) := by
    ext t
    simp [Finset.sum_filter, Set.indicator_apply, Set.mem_Iic]
  rw [h_sum_eq]
  constructor
  · -- Part 1: IntervalIntegrable of the sum
    have h_sum_fun_eq : (∑ j : ι, (fun (t : ℝ) => ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t)) =
        (fun (t : ℝ) => ∑ j : ι, ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t) := by
      ext t
      simp
    rw [← h_sum_fun_eq]
    refine IntervalIntegrable.sum (s := Finset.univ) (f := fun j t => ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t) (fun j hj => ?_)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have h_int_on : IntegrableOn (fun (_ : ℝ) => w j) (Set.Ioc a b) volume := by
      apply MeasureTheory.integrableOn_const
      · simp
      · simp
    have h_meas : MeasurableSet (Set.Iic (g j)) := measurableSet_Iic
    exact h_int_on.indicator h_meas
  · -- Part 2: integral equality
    rw [intervalIntegral.integral_finsetSum]
    · -- Now we need: ∑ j, ∫ t in a..b, (Iic (g j)).indicator (fun _ => w j) t = ∑ i, w i * max (g i - a) 0
      refine Finset.sum_congr rfl (fun j hj => ?_)
      -- hj : j ∈ Finset.univ
      have h_int_term : ∫ t in a..b, ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t = w j * max (g j - a) 0 := by
        by_cases hga : g j ≤ a
        · have hmax : max (g j - a) 0 = 0 := by
            have h : g j - a ≤ 0 := sub_nonpos.mpr hga
            exact max_eq_right h
          rw [hmax, mul_zero]
          have h_zero : ∀ᵐ t ∂ volume, t ∈ Set.uIoc a b → ((Set.Iic (g j)).indicator (fun (_ : ℝ) => w j)) t = 0 := by
            filter_upwards [] with t ht
            rw [Set.mem_uIoc] at ht
            rcases ht with (⟨ht1, ht2⟩ | ⟨ht1, ht2⟩)
            · have ht_not_le_g : ¬ (t ≤ g j) := by
                intro hle
                have : t ≤ a := le_trans hle hga
                linarith
              simp [ht_not_le_g]
            · linarith
          rw [intervalIntegral.integral_zero_ae h_zero]
        · have hag : a ≤ g j := by linarith
          have hg_in_Icc : g j ∈ Set.Icc a b := ⟨hag, hgb j⟩
          have h := intervalIntegral.integral_indicator hg_in_Icc (f := fun (_ : ℝ) => w j) (μ := volume)
          have hmax : max (g j - a) 0 = g j - a := max_eq_left (sub_nonneg.mpr hag)
          rw [hmax]
          simpa [Set.Iic, mul_comm] using h
      rw [h_int_term]
    · intro j hj
      -- need to show IntervalIntegrable for each term
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      have h_int_on : IntegrableOn (fun (_ : ℝ) => w j) (Set.Ioc a b) volume := by
        apply MeasureTheory.integrableOn_const
        · simp
        · simp
      have h_meas : MeasurableSet (Set.Iic (g j)) := measurableSet_Iic
      exact h_int_on.indicator h_meas

theorem AdversarialBco.scale_mu_le {ι : Type*} [Fintype ι] (w g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a c t : ℝ)
    (hc : 0 ≤ c) (hat : a ≤ t)
    (hall : ∀ i, a ≤ g i → g i * ∑ j ∈ Finset.univ.filter (fun j => g i ≤ g j), w j ≤ c) :
    t * ∑ j ∈ Finset.univ.filter (fun j => t ≤ g j), w j ≤ c := by
  set T := Finset.univ.filter (fun j => t ≤ g j) with hT
  by_cases hTempty : T.Nonempty
  · -- T is nonempty: take k ∈ T minimising g on T
    obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image T g hTempty
    have hkT' : t ≤ g k := by
      simpa [hT] using hkT
    have ha_le_gk : a ≤ g k := le_trans hat hkT'
    have h_filter_eq : T = Finset.univ.filter (fun j => g k ≤ g j) := by
      apply Finset.filter_congr
      intro x hx
      have hx_univ : x ∈ Finset.univ := hx
      constructor
      · intro h
        have hxT : x ∈ T := by
          dsimp [T]
          exact Finset.mem_filter.mpr ⟨hx_univ, h⟩
        exact hkmin x hxT
      · intro h
        exact le_trans hkT' h
    have h_mu_nonneg : 0 ≤ ∑ j ∈ T, w j :=
      Finset.sum_nonneg fun i _ => hw i
    by_cases ht_nonpos : t ≤ 0
    · have : t * ∑ j ∈ T, w j ≤ 0 := by
        nlinarith
      nlinarith
    · have ht_pos : 0 ≤ t := by linarith
      have h_mul : t * ∑ j ∈ T, w j ≤ g k * ∑ j ∈ T, w j := by
        nlinarith
      have h_sum_eq : ∑ j ∈ T, w j = ∑ j ∈ Finset.univ.filter (fun j => g k ≤ g j), w j := by
        rw [h_filter_eq]
      have h_target : g k * ∑ j ∈ T, w j ≤ c := by
        rw [h_sum_eq]
        exact hall k ha_le_gk
      nlinarith
  · -- T is empty
    have hTempty' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTempty
    simp [hTempty', hc]

open MeasureTheory in
theorem AdversarialBco.scale_integral_le (F : ℝ → ℝ) (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hF : IntervalIntegrable F volume a b) (hle : ∀ t ∈ Set.Icc a b, F t ≤ c / t) :
    ∫ t in a..b, F t ≤ c * Real.log (b / a) := by
  have hb : 0 < b := by linarith
  have hg : IntervalIntegrable (fun t => c / t) volume a b := by
    have h_cont : ContinuousOn (fun t : ℝ => c / t) (Set.uIcc a b) := by
      have h_ne_zero : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ha_t : a ≤ t := ht.1
        linarith
      exact (continuousOn_const.div continuousOn_id h_ne_zero)
    exact h_cont.intervalIntegrable
  calc
    ∫ t in a..b, F t ≤ ∫ t in a..b, (c / t) := by
      refine intervalIntegral.integral_mono_on hab hF hg hle
    _ = c * ∫ t in a..b, t⁻¹ := by
      simp [div_eq_mul_inv, intervalIntegral.integral_const_mul]
    _ = c * Real.log (b / a) := by rw [integral_inv_of_pos ha hb]

open Real in
theorem AdversarialBco.scale_pigeonhole {ι : Type*} [Fintype ι] (w g : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hg : ∀ i, 0 ≤ g i) (G0 gmax : ℝ) (hG0 : 0 < G0) (hgmax : ∀ i, g i ≤ gmax)
    (hmean : ∑ i, w i * g i = G0) :
    ∃ i, G0 / 2 ≤ g i ∧
      G0 / (2 * Real.log (2 * gmax / G0)) ≤ g i * ∑ j ∈ Finset.univ.filter (fun j => g i ≤ g j), w j := by
  -- define mu(t) = ∑_{j : t ≤ g j} w j for convenience
  set mu := fun (t : ℝ) => ∑ j ∈ Finset.univ.filter (fun j => t ≤ g j), w j with hmu
  -- first, G0 ≤ gmax
  have hG0le : G0 ≤ gmax := by
    calc
      G0 = ∑ i, w i * g i := by rw [hmean]
      _ ≤ ∑ i, w i * gmax :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hgmax i) (hw i))
      _ = gmax * ∑ i, w i := by simp [Finset.mul_sum, mul_comm]
      _ = gmax := by simp [hw1]
  -- define ℓ = log(2 * gmax / G0)
  set ℓ := Real.log (2 * gmax / G0) with hℓ
  have hℓpos : 0 < ℓ := by
    have h_ratio : 1 < 2 * gmax / G0 := by
      calc
        1 < 2 := by norm_num
        _ = 2 * G0 / G0 := by field_simp [hG0.ne.symm]
        _ ≤ 2 * gmax / G0 := by gcongr
    exact Real.log_pos h_ratio
  -- the set s = {i | G0/2 ≤ g i} is nonempty
  let s := Finset.filter (fun i => G0 / 2 ≤ g i) Finset.univ
  have hs : s.Nonempty := by
    by_contra! h_empty
    -- h_empty : s = ∅ (by_contra! simplifies ¬ s.Nonempty to s = ∅)
    have h_all_lt : ∀ i, g i < G0 / 2 := by
      intro i
      have h_not_le := (Finset.filter_eq_empty_iff.1 h_empty) (Finset.mem_univ i)
      linarith
    -- since ∑ w_i = 1 > 0, there exists i with w i > 0
    have h_exists_pos : ∃ i, 0 < w i := by
      by_contra! h_all_zero
      have h_sum_zero : ∑ i, w i = 0 :=
        Finset.sum_eq_zero (fun i _ => le_antisymm (h_all_zero i) (hw i))
      linarith
    rcases h_exists_pos with ⟨i_pos, hi_pos⟩
    have h_sum_lt : ∑ i, w i * g i < ∑ i, w i * (G0 / 2) := by
      refine Finset.sum_lt_sum (fun i hi => ?_) ⟨i_pos, Finset.mem_univ i_pos, ?_⟩
      · have h_g_le : g i ≤ G0 / 2 := le_of_lt (h_all_lt i)
        exact mul_le_mul_of_nonneg_left h_g_le (hw i)
      · exact mul_lt_mul_of_pos_left (h_all_lt i_pos) hi_pos
    have h_sum_eq : ∑ i, w i * (G0 / 2) = G0 / 2 := by
      calc
        ∑ i, w i * (G0 / 2) = (∑ i, w i) * (G0 / 2) := by simp [Finset.sum_mul]
        _ = 1 * (G0 / 2) := by rw [hw1]
        _ = G0 / 2 := by simp
    rw [h_sum_eq] at h_sum_lt
    linarith
  -- define c' = max_{i ∈ s} (g i * mu(g i))
  set c' := s.sup' hs (fun i => g i * mu (g i)) with hc'
  have hc'_nonneg : 0 ≤ c' := by
    rcases hs with ⟨i, hi⟩
    have h_nonneg : 0 ≤ g i * mu (g i) := by
      have h_g_nonneg : 0 ≤ g i := hg i
      have h_mu_nonneg : 0 ≤ mu (g i) := by
        dsimp [mu]
        apply Finset.sum_nonneg
        intro j _
        exact hw j
      exact mul_nonneg h_g_nonneg h_mu_nonneg
    have h_le : g i * mu (g i) ≤ c' := Finset.le_sup' (fun i => g i * mu (g i)) hi
    linarith
  -- get the layer cake decomposition
  rcases AdversarialBco.scale_layer_cake w g (G0/2) gmax (by linarith) (fun i => hgmax i) with
    ⟨h_int, h_eq⟩
  -- by contradiction: assume the conclusion is false
  by_cases h_concl : ∃ i, G0 / 2 ≤ g i ∧ G0 / (2 * ℓ) ≤ g i * mu (g i)
  · -- we are done
    rcases h_concl with ⟨i, hi_le, hi_bound⟩
    refine ⟨i, hi_le, ?_⟩
    simpa [mu] using hi_bound
  · -- h_concl is false: for all i with G0/2 ≤ g i, g i * mu(g i) < G0/(2*ℓ)
    push_neg at h_concl
    -- h_concl: ∀ i, G0/2 ≤ g i → g i * mu(g i) < G0/(2*ℓ)
    -- hence c' < G0/(2*ℓ)
    have hc'_lt : c' < G0 / (2 * ℓ) := by
      by_contra! hge
      -- hge: G0 / (2 * ℓ) ≤ c'
      rcases (Finset.le_sup'_iff hs).mp hge with ⟨i, hi, hle⟩
      have h_lt := h_concl i (by
        -- hi : i ∈ s, which means G0/2 ≤ g i
        simpa [s] using hi)
      linarith
    -- for all t ≥ G0/2, we have t * mu(t) ≤ c'
    have h_mu_bound : ∀ t, G0 / 2 ≤ t → t * mu t ≤ c' := by
      intro t ht
      apply AdversarialBco.scale_mu_le w g hw (G0/2) c' t hc'_nonneg ht
      intro i hi
      have hi_s : i ∈ s := by
        dsimp [s]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      exact Finset.le_sup' (fun i => g i * mu (g i)) hi_s
    -- from h_mu_bound, for t > 0, we get mu(t) ≤ c' / t
    have h_mu_le_div : ∀ t ∈ Set.Icc (G0/2) gmax, mu t ≤ c' / t := by
      intro t ht
      rcases ht with ⟨ht_left, ht_right⟩
      have ht_pos : 0 < t := by linarith
      have h_bound : t * mu t ≤ c' := h_mu_bound t ht_left
      calc
        mu t = (t * mu t) / t := by field_simp [ht_pos.ne.symm]
        _ ≤ c' / t := by gcongr
    -- apply scale_integral_le
    have h_integral_bound : ∫ t in (G0/2)..gmax, mu t ≤ c' * Real.log (gmax / (G0/2)) :=
      AdversarialBco.scale_integral_le mu (G0/2) gmax c' (by linarith) (by linarith) h_int h_mu_le_div
    have h_log_eq : Real.log (gmax / (G0/2)) = ℓ := by
      calc
        Real.log (gmax / (G0/2)) = Real.log ((2 * gmax) / G0) := by ring
        _ = ℓ := by rw [hℓ]
    -- c' * ℓ < G0/2
    have hc'_mul_lt : c' * ℓ < G0 / 2 := by
      calc
        c' * ℓ < (G0 / (2 * ℓ)) * ℓ := mul_lt_mul_of_pos_right hc'_lt hℓpos
        _ = G0 / 2 := by field_simp [ne_of_gt hℓpos]
    -- hence ∫ mu < G0/2
    have h_integral_lt : ∫ t in (G0/2)..gmax, mu t < G0 / 2 := by
      calc
        ∫ t in (G0/2)..gmax, mu t ≤ c' * Real.log (gmax / (G0/2)) := h_integral_bound
        _ = c' * ℓ := by rw [h_log_eq]
        _ < G0 / 2 := hc'_mul_lt
    -- lower bound: ∑ w_i * max(g_i - G0/2, 0) ≥ G0/2
    have h_identity : ∀ (a b : ℝ), a = min a b + max (a - b) 0 := by
      intro a b
      by_cases h : a ≤ b
      · have h_min : min a b = a := min_eq_left h
        have h_max : max (a - b) 0 = 0 := max_eq_right (sub_nonpos.mpr h)
        rw [h_min, h_max]
        ring
      · have h' : b ≤ a := by linarith
        have h_min : min a b = b := min_eq_right h'
        have h_max : max (a - b) 0 = a - b := max_eq_left (sub_nonneg.mpr h')
        rw [h_min, h_max]
        ring
    have h_sum_eq : ∑ i, w i * g i =
        (∑ i, w i * min (g i) (G0/2)) + (∑ i, w i * max (g i - G0/2) 0) := by
      calc
        ∑ i, w i * g i = ∑ i, w i * (min (g i) (G0/2) + max (g i - G0/2) 0) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [← h_identity (g i) (G0/2)]
        _ = ∑ i, (w i * min (g i) (G0/2) + w i * max (g i - G0/2) 0) := by
          apply Finset.sum_congr rfl (fun i hi => ?_)
          ring
        _ = (∑ i, w i * min (g i) (G0/2)) + (∑ i, w i * max (g i - G0/2) 0) :=
          Finset.sum_add_distrib
    have h_lower : G0 / 2 ≤ ∑ i, w i * max (g i - G0/2) 0 := by
      have h_total : G0 = (∑ i, w i * min (g i) (G0/2)) + (∑ i, w i * max (g i - G0/2) 0) := by
        linarith
      have h_min_le : (∑ i, w i * min (g i) (G0/2)) ≤ G0 / 2 := by
        calc
          (∑ i, w i * min (g i) (G0/2)) ≤ (∑ i, w i * (G0/2)) :=
            Finset.sum_le_sum (fun i hi =>
              mul_le_mul_of_nonneg_left (min_le_right (g i) (G0/2)) (hw i))
          _ = (G0/2) * ∑ i, w i := by simp [Finset.sum_mul, mul_comm]
          _ = G0 / 2 := by simp [hw1]
      linarith
    -- combine: G0/2 ≤ sum = integral < G0/2, contradiction
    rw [← h_eq] at h_integral_lt
    linarith

/-- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound
`L ‖c ω‖`. -/
theorem AdversarialBco.hasDerivAt_integral_affine {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure Ω) (G : F → ℝ) (G' : F → F →L[ℝ] ℝ) (L : ℝ)
    (hG : ∀ x, HasFDerivAt G (G' x) x) (hG' : ∀ x, ‖G' x‖ ≤ L) (hcont : Continuous G') (a c : Ω → F)
    (ha : AEStronglyMeasurable a μ) (hc : AEStronglyMeasurable c μ) (hca : Integrable (fun ω => ‖c ω‖) μ)
    (hGa : Integrable (fun ω => G (a ω)) μ) :
    HasDerivAt (fun t : ℝ => ∫ ω, G (a ω + t • c ω) ∂μ) (∫ ω, G' (a ω) (c ω) ∂μ) 0 := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hderiv : ∀ ω t, HasDerivAt (fun s : ℝ => G (a ω + s • c ω)) (G' (a ω + t • c ω) (c ω)) t := by
    intro ω t
    have h : HasDerivAt (fun s : ℝ => a ω + s • c ω) (c ω) t := by
      simpa using ((hasDerivAt_id t).smul_const (c ω)).const_add (a ω)
    exact (hG _).comp_hasDerivAt t h
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t ω => G (a ω + t • c ω)) (F' := fun t ω => G' (a ω + t • c ω) (c ω))
    (bound := fun ω => L * ‖c ω‖) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => hGc.comp_aestronglyMeasurable (ha.add (hc.const_smul t)))
    (by simpa using hGa)
    (by
      simp only [zero_smul, add_zero]
      exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hcont.comp_aestronglyMeasurable ha).prodMk hc))
    (Filter.Eventually.of_forall fun ω t _ =>
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hG' _) (norm_nonneg _)))
    (hca.const_mul L)
    (Filter.Eventually.of_forall fun ω t _ => hderiv ω t)
  simpa using key.2

open MeasureTheory in
theorem AdversarialBco.jensen_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure F) [IsProbabilityMeasure μ] (hsym : μ.map (fun w => -w) = μ) (G : F → ℝ)
    (hG : ConvexOn ℝ Set.univ G) (b : F) (hint : Integrable (fun w => G (b + w)) μ) :
    G b ≤ ∫ w, G (b + w) ∂μ := by
  have hmeas_neg : AEMeasurable (fun w : F => -w) μ :=
    (continuous_neg.measurable).aemeasurable
  have h_symm_int : ∫ w, G (b - w) ∂μ = ∫ w, G (b + w) ∂μ := by
    calc
      ∫ w, G (b - w) ∂μ = ∫ w, G (b + (-w)) ∂μ := by simp [sub_eq_add_neg]
      _ = ∫ w, G (b + w) ∂(μ.map (fun w => -w)) := by
        rw [integral_map hmeas_neg (by rw [hsym]; exact hint.aestronglyMeasurable)]
      _ = ∫ w, G (b + w) ∂μ := by rw [hsym]
  have h_neg_inv : μ.IsNegInvariant :=
    Measure.IsNegInvariant.mk hsym
  have h_int2 : Integrable (fun w => G (b - w)) μ := by
    have := hint.comp_neg
    simpa [sub_eq_add_neg] using this
  have h_avg_eq : ∫ w, G (b + w) ∂μ = ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ := by
    calc
      ∫ w, G (b + w) ∂μ = (∫ w, G (b + w) ∂μ + ∫ w, G (b + w) ∂μ) / 2 := by ring
      _ = (∫ w, G (b + w) ∂μ + ∫ w, G (b - w) ∂μ) / 2 := by rw [h_symm_int]
      _ = ((∫ w, G (b + w) ∂μ) + (∫ w, G (b - w) ∂μ)) / 2 := rfl
      _ = (∫ w, (G (b + w) + G (b - w)) ∂μ) / 2 := by rw [integral_add hint h_int2]
      _ = ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ := by rw [integral_div]
  have h_pointwise : ∀ w, G b ≤ (G (b + w) + G (b - w)) / 2 := by
    intro w
    have hx : b + w ∈ Set.univ := Set.mem_univ _
    have hy : b - w ∈ Set.univ := Set.mem_univ _
    have hmid : ((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w)) = b := by
      calc
        ((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w))
            = (1/2 : ℝ) • ((b + w) + (b - w)) := by rw [← smul_add]
        _ = (1/2 : ℝ) • (b + b) := by abel
        _ = (1/2 : ℝ) • ((2 : ℝ) • b) := by simp [two_smul]
        _ = b := by simp
    calc
      G b = G (((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w))) := by rw [hmid]
      _ ≤ ((1/2 : ℝ) • G (b + w) + (1/2 : ℝ) • G (b - w)) := by
        have h := hG.2 hx hy (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
          (by norm_num : (1/2 : ℝ) + (1/2 : ℝ) = 1)
        simpa [add_comm] using h
      _ = (G (b + w) + G (b - w)) / 2 := by ring
  have h_int_avg : Integrable (fun w => (G (b + w) + G (b - w)) / 2) μ := by
    have h_sum : Integrable (fun w => G (b + w) + G (b - w)) μ :=
      Integrable.add hint h_int2
    exact h_sum.div_const 2
  calc
    G b = ∫ w, G b ∂μ := by
      rw [integral_const]
      have h_measure_univ_real : μ.real Set.univ = (1 : ℝ) := by
        rw [Measure.real_def, measure_univ, ENNReal.toReal_one]
      rw [h_measure_univ_real, one_smul]
    _ ≤ ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ :=
      integral_mono (integrable_const _) h_int_avg h_pointwise
    _ = ∫ w, G (b + w) ∂μ := by rw [h_avg_eq]

theorem AdversarialBco.convexOn_ge_of_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : F → ℝ)
    (G' : F →L[ℝ] ℝ) (hG : ConvexOn ℝ Set.univ G) (x : F) (hx : HasFDerivAt G G' x) (y : F) :
    G x + G' (y - x) ≤ G y := by
  -- The affine map φ(s) = x + s • (y - x) from ℝ to F
  let φ : ℝ →ᵃ[ℝ] F := AffineMap.lineMap x y
  -- G ∘ φ is convex on ℝ
  have h_conv : ConvexOn ℝ Set.univ (G ∘ (φ : ℝ → F)) := by
    have := hG.comp_affineMap φ
    simpa [Set.preimage_univ] using this
  -- Derivative of φ at 0: φ'(0) = y - x
  have h_deriv_φ : HasDerivAt (φ : ℝ → F) (y - x) 0 := by
    have : (φ : ℝ → F) = fun s => x + s • (y - x) := by
      ext s; simp [φ, AffineMap.lineMap_apply, add_comm]
    rw [this]
    have h_add : HasDerivAt (fun (s : ℝ) => x + s • (y - x)) (0 + (y - x)) 0 := by
      refine HasDerivAt.add ?_ ?_
      · exact hasDerivAt_const (𝕜 := ℝ) (0 : ℝ) x
      · have h_smul : HasDerivAt (fun (s : ℝ) => s • (y - x)) (y - x) 0 := by
          simpa [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
        exact h_smul
    simpa [zero_add] using h_add
  -- Chain rule: (G ∘ φ)'(0) = G'(φ(0)) ∘ φ'(0) = G'(y-x)
  have h_deriv_comp : HasDerivAt (G ∘ (φ : ℝ → F)) (G' (y - x)) 0 := by
    have hx_at_φ0 : HasFDerivAt G G' ((φ : ℝ → F) 0) := by
      have : (φ : ℝ → F) 0 = x := by simp [φ]
      rw [this]
      exact hx
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hx_at_φ0 h_deriv_φ
    simpa using this
  -- Use the 1D convexity lemma: ConvexOn.le_slope_of_hasDerivAt
  have h_slope : G' (y - x) ≤ slope (G ∘ (φ : ℝ → F)) 0 1 := by
    refine ConvexOn.le_slope_of_hasDerivAt h_conv (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) h_deriv_comp
  -- slope f 0 1 = (f 1 - f 0) / (1 - 0) = G y - G x
  have h_slope_eq : slope (G ∘ (φ : ℝ → F)) 0 1 = G y - G x := by
    simp [slope, φ]
  rw [h_slope_eq] at h_slope
  -- h_slope : G' (y - x) ≤ G y - G x
  -- Rearrange to get the desired inequality
  linarith


open Set Filter in
/-- `∫ x in Ioi 0, x * exp (-x^2/(2 v)) = v` for `v > 0`. -/
theorem AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_var (v : ℝ) (hv : 0 < v) :
    ∫ x in Ioi (0 : ℝ), rexp (-x ^ 2 / (2 * v)) * x = v := by
  set F : ℝ → ℝ := fun x => -v * rexp (-x ^ 2 / (2 * v)) with hF
  set f : ℝ → ℝ := fun x => rexp (-x ^ 2 / (2 * v)) * x with hf
  have h_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (f x) x := by
    intro x hx
    dsimp [F, f]
    have h_deriv_inner : HasDerivAt (fun x : ℝ => -x ^ 2 / (2 * v)) (-x / v) x := by
      have h_neg_sq : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := by
        have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        simpa [show (fun x : ℝ => -x ^ 2) = -(fun x : ℝ => x ^ 2) by ext; simp] using HasDerivAt.neg h_sq
      have h_const_inv : HasDerivAt (fun _ : ℝ => (2 * v)⁻¹) 0 x := by
        exact hasDerivAt_const _ _
      have h_mul : HasDerivAt (fun x : ℝ => (-x ^ 2) * (2 * v)⁻¹)
          ((-(2 * x)) * (2 * v)⁻¹ + (-x ^ 2) * 0) x :=
        HasDerivAt.mul h_neg_sq h_const_inv
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_zero, hv.ne.symm] using h_mul
    have h_exp_deriv : HasDerivAt (fun x : ℝ => rexp (-x ^ 2 / (2 * v)))
        (rexp (-x ^ 2 / (2 * v)) * (-x / v)) x := by
      refine (Real.hasDerivAt_exp _).comp x h_deriv_inner
    have h_final : HasDerivAt (fun x : ℝ => -v * rexp (-x ^ 2 / (2 * v)))
        (-v * (rexp (-x ^ 2 / (2 * v)) * (-x / v))) x :=
      HasDerivAt.const_mul (-v) h_exp_deriv
    have h_simp : -v * (rexp (-x ^ 2 / (2 * v)) * (-x / v)) = rexp (-x ^ 2 / (2 * v)) * x := by
      field_simp [hv.ne.symm]
    simpa [h_simp] using h_final
  have h_cont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    dsimp [F]
    refine Continuous.continuousWithinAt ?_
    continuity
  have h_tendsto : Tendsto F atTop (nhds (0 : ℝ)) := by
    dsimp [F]
    have h_sq_tendsto : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : 2 ≠ 0)
    have h_neg_sq_tendsto : Tendsto (fun x : ℝ => -x ^ 2) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h_sq_tendsto
    have hpos : 0 < 2 * v := by nlinarith
    have h_inner : Tendsto (fun x : ℝ => -x ^ 2 / (2 * v)) atTop atBot :=
      h_neg_sq_tendsto.atBot_div_const hpos
    have h_exp : Tendsto (fun x : ℝ => rexp (-x ^ 2 / (2 * v))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_inner
    have h_mul : Tendsto (fun x : ℝ => -v * rexp (-x ^ 2 / (2 * v))) atTop (nhds (-v * 0)) :=
      tendsto_const_nhds.mul h_exp
    simpa [mul_zero] using h_mul
  have h_integrable : IntegrableOn f (Ioi (0 : ℝ)) volume := by
    dsimp [f]
    have hb : 0 < (2 * v)⁻¹ := by
      refine inv_pos.mpr ?_
      nlinarith [hv]
    have hs : -1 < (1 : ℝ) := by norm_num
    have h_int : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(2 * v)⁻¹ * x ^ 2)) (Ioi 0) volume :=
      integrableOn_rpow_mul_exp_neg_mul_sq hb hs
    simpa [rpow_one, div_eq_inv_mul, mul_comm] using h_int
  rw [integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_integrable h_tendsto]
  dsimp [F]
  simp


open Set Filter in
theorem AdversarialBco.integral_abs_gaussianReal (v : NNReal) :
    ∫ x, |x| ∂(gaussianReal 0 v) = Real.sqrt (2 * v / Real.pi) := by
  by_cases hv : (v : ℝ) = 0
  · have hv' : v = 0 := by exact_mod_cast hv
    subst hv'
    simp [gaussianReal_zero_var]
  · have hv_ne_zero : v ≠ 0 := by
      intro h; apply hv; exact_mod_cast h
    have hv_pos : 0 < (v : ℝ) := by
      by_contra! h
      have h_eq : (v : ℝ) = 0 := by linarith
      exact hv h_eq
    rw [integral_gaussianReal_eq_integral_smul hv_ne_zero]
    simp_rw [smul_eq_mul]
    rw [gaussianPDFReal_def 0 v]
    simp only [sub_zero]
    -- ∫ x, ((√(2πv))⁻¹ * rexp(-x²/(2v))) * |x|
    -- Factor out the constant (√(2πv))⁻¹
    have h_factor : (fun x : ℝ => ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * rexp (-x ^ 2 / (2 * (v : ℝ)))) * |x|) =
        (fun x : ℝ => (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|)) := by
      ext x; ring
    rw [h_factor, integral_const_mul]
    -- Now: (√(2πv))⁻¹ * ∫ x, rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|
    -- Use integral_comp_abs with f(x) = x * rexp(-x²/(2v))
    -- Then f(|x|) = |x| * rexp(-|x|²/(2v)) = |x| * rexp(-x²/(2v))
    -- And ∫_Ioi 0 f(x) dx = ∫_Ioi 0 x * rexp(-x²/(2v)) dx = v
    set f : ℝ → ℝ := fun x => rexp (-x ^ 2 / (2 * (v : ℝ))) * x with hf
    have h_abs_eq : (fun x : ℝ => rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|) = fun x => f |x| := by
      ext x
      dsimp [f]
      simp [sq_abs]
    rw [h_abs_eq, integral_comp_abs]
    -- Now: (√(2πv))⁻¹ * (2 * ∫ x in Ioi 0, f x)
    rw [hf]
    -- (√(2πv))⁻¹ * (2 * ∫ x in Ioi 0, rexp (-x ^ 2 / (2 * (v : ℝ))) * x)
    rw [AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_var (v : ℝ) hv_pos]
    -- Now: (√(2πv))⁻¹ * (2 * v) = √(2v/π)
    -- Square both sides
    have h_eq_sq : ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ))) ^ 2 = (Real.sqrt (2 * (v : ℝ) / π)) ^ 2 := by
      calc
        ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ))) ^ 2
            = (2 * (v : ℝ)) ^ 2 / ((Real.sqrt (2 * π * (v : ℝ))) ^ 2) := by ring
        _ = (4 * (v : ℝ) ^ 2) / (2 * π * (v : ℝ)) := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * π * (v : ℝ))]
          ring
        _ = 2 * (v : ℝ) / π := by
          field_simp [hv_pos.ne.symm]
          ring
        _ = (Real.sqrt (2 * (v : ℝ) / π)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (v : ℝ) / π)]
    have h_nonneg_left : 0 ≤ (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ)) := by
      positivity
    have h_nonneg_right : 0 ≤ Real.sqrt (2 * (v : ℝ) / π) := by positivity
    -- From equality of squares and nonnegativity, we get equality
    have h_eq : (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ)) = Real.sqrt (2 * (v : ℝ) / π) := by
      nlinarith
    rw [h_eq]

open Matrix Polynomial in
theorem AdversarialBco.hasDerivAt_log_det {n : Type*} [Fintype n] [DecidableEq n] (S D : Matrix n n ℝ)
    (hS : 0 < S.det) : HasDerivAt (fun t : ℝ => Real.log (S + t • D).det) (S⁻¹ * D).trace 0 := by
  set M := S⁻¹ * D with hM
  have hS_det_ne_zero : S.det ≠ 0 := by linarith
  have hS_det_unit : IsUnit S.det := IsUnit.mk0 _ hS_det_ne_zero
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det_unit
  -- S + t • D = S * (1 + t • M)
  have h_eq : ∀ t : ℝ, S + t • D = S * (1 + t • M) := by
    intro t
    calc
      S + t • D = S + t • (S * M) := by
        have hD : D = S * M := by
          calc
            D = 1 * D := by simp
            _ = (S * S⁻¹) * D := by rw [hS_mul_inv]
            _ = S * (S⁻¹ * D) := by rw [Matrix.mul_assoc]
            _ = S * M := by rw [hM]
        rw [hD]
      _ = S * 1 + S * (t • M) := by simp
      _ = S * (1 + t • M) := by rw [Matrix.mul_add, Matrix.mul_one]
  -- det(S + t • D) = det S * det(1 + t • M)
  have h_det_eq : ∀ t : ℝ, (S + t • D).det = S.det * (1 + t • M).det := by
    intro t
    rw [h_eq t, Matrix.det_mul]
  -- Key lemma: derivative of det(1 + t • M) at 0 is trace M
  have h_deriv_det_one_add : HasDerivAt (fun t : ℝ => (1 + t • M).det) (M.trace) 0 := by
    -- Use Matrix.det_one_add_smul to express det(1 + t • M) as a polynomial
    let p' := ((1 : Matrix n n (Polynomial ℝ)) + (Polynomial.X : Polynomial ℝ) • (M.map (fun r => (Polynomial.C r : Polynomial ℝ)))).det.divX.divX
    have h_formula : (fun t : ℝ => (1 + t • M).det) = (fun t => 1 + M.trace * t + (Polynomial.eval t p') * t ^ 2) := by
      ext t
      -- Matrix.det_one_add_smul gives the formula
      have h := Matrix.det_one_add_smul t M
      -- h : (1 + t • M).det = 1 + M.trace * t + Polynomial.eval t (...) * t ^ 2
      simpa [p'] using h
    rw [h_formula]
    -- Now compute derivative of 1 + M.trace * t + (eval t p') * t^2 at 0
    have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := by
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    have h_linear : HasDerivAt (fun t : ℝ => M.trace * t) (M.trace) 0 := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
      simpa [mul_comm] using HasDerivAt.const_mul (M.trace) h_id
    have h_sq : HasDerivAt (fun t : ℝ => (Polynomial.eval t p') * t ^ 2) 0 0 := by
      have hQ : HasDerivAt (fun t : ℝ => Polynomial.eval t p') (Polynomial.eval (0 : ℝ) (Polynomial.derivative p')) 0 := by
        simpa using Polynomial.hasDerivAt p' (0 : ℝ)
      have h_sq' : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have h_mul := HasDerivAt.mul hQ h_sq'
      -- h_mul : HasDerivAt ((fun t => Q(t)) * (fun t => t^2)) (Q'(0)*0^2 + Q(0)*0) 0
      -- The derivative simplifies to 0
      have h_mul' : HasDerivAt ((fun t : ℝ => Polynomial.eval t p') * fun t : ℝ => t ^ 2) 0 0 := by
        simpa [add_zero, mul_zero] using h_mul
      -- Now the function is definitionally equal to (fun t => eval t p' * t ^ 2)
      exact h_mul'
    -- Combine: derivative of 1 + M.trace * t + (eval t p') * t^2 is 0 + M.trace + 0 = M.trace
    have h_sum := (h_const.add (h_linear.add h_sq))
    -- h_sum : HasDerivAt ((fun x => 1) + ((fun t => M.trace * t) + fun t => eval t p' * t ^ 2)) (0 + (M.trace + 0)) 0
    -- The derivative simplifies to M.trace
    have h_sum' : HasDerivAt ((fun x : ℝ => (1 : ℝ)) + ((fun t : ℝ => M.trace * t) + fun t : ℝ => (Polynomial.eval t p') * t ^ 2)) (M.trace) 0 := by
      simpa [add_zero] using h_sum
    -- The function is definitionally equal to (fun t => 1 + M.trace * t + eval t p' * t ^ 2)
    -- but we need to use funext to adjust
    have h_goal : (fun t : ℝ => 1 + M.trace * t + (Polynomial.eval t p') * t ^ 2) =
      ((fun x : ℝ => (1 : ℝ)) + ((fun t : ℝ => M.trace * t) + fun t : ℝ => (Polynomial.eval t p') * t ^ 2)) := by
      funext t; simp [mul_comm, add_comm, add_left_comm, add_assoc]
    rw [h_goal]
    exact h_sum'
  -- Now we have HasDerivAt (fun t => det(1 + t • M)) (M.trace) 0
  -- Multiply by det S
  have h_deriv_detS_mul : HasDerivAt (fun t : ℝ => S.det * (1 + t • M).det) (S.det * M.trace) 0 := by
    simpa [mul_comm] using HasDerivAt.const_mul S.det h_deriv_det_one_add
  -- Now apply log
  have h_log_input : (fun t : ℝ => Real.log ((S + t • D).det)) = (fun t => Real.log (S.det * (1 + t • M).det)) := by
    ext t
    rw [h_det_eq t]
  rw [h_log_input]
  have h_log_arg_ne_zero : S.det * (1 + (0 : ℝ) • M).det ≠ 0 := by
    simp [hS_det_ne_zero]
  have h_log_deriv := HasDerivAt.log h_deriv_detS_mul h_log_arg_ne_zero
  -- h_log_deriv : HasDerivAt (fun t => Real.log (S.det * (1 + t • M).det)) ((S.det * M.trace) / (S.det * (1 + 0 • M).det)) 0
  -- Simplify: (1 + 0 • M).det = 1, so the derivative is (S.det * M.trace) / S.det = M.trace
  have h_log_deriv_simp : HasDerivAt (fun t : ℝ => Real.log (S.det * (1 + t • M).det)) (M.trace) 0 := by
    -- rewrite the derivative in h_log_deriv
    have h_deriv_simp : (S.det * M.trace) / (S.det * (1 + (0 : ℝ) • M).det) = M.trace := by
      simp [hS_det_ne_zero]
    -- Now apply this to h_log_deriv
    convert h_log_deriv using 1
    exact h_deriv_simp.symm
  -- Now rewrite back using h_log_input
  simpa [h_log_input] using h_log_deriv_simp

theorem AdversarialBco.ew_recursive {C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (hη : 0 < η) (n : ℕ)
    (ℓ : ℕ → C → ℝ) (q : ℕ → C → ℝ) (hq0 : ∀ z, q 0 z = 1 / Fintype.card C)
    (hq : ∀ t z, q (t + 1) z = q t z * Real.exp (-η * ℓ t z) / ∑ z', q t z' * Real.exp (-η * ℓ t z')) (y : C) :
    -Real.log (Fintype.card C) / η ≤
      ∑ t ∈ Finset.range n, (ℓ t y + (1 / η) * Real.log (∑ z, q t z * Real.exp (-η * ℓ t z))) := by
  -- Define W t = ∑ z, exp(-η * ∑ s ∈ range t, ℓ s z)
  set W := fun (t : ℕ) => ∑ z : C, Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z)) with hW_def
  have hW_pos : ∀ t, 0 < W t := by
    intro t
    refine Finset.sum_pos (fun z _ => Real.exp_pos _) ?_
    exact Finset.univ_nonempty
  have hW0 : W 0 = Fintype.card C := by
    simp [W, Real.exp_zero, Finset.card_univ]
  have hW_ne_zero : ∀ t, W t ≠ 0 := fun t => by linarith [hW_pos t]
  -- Prove by induction that q t z = exp(-η * ∑ s ∈ range t, ℓ s z) / W t
  have hq_closed : ∀ t z, q t z = Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z)) / W t := by
    intro t
    induction' t with t ih
    · intro z
      simp [hq0, W]
    · intro z
      rw [hq t z]
      have h_denom : (∑ z' : C, q t z' * Real.exp (-η * ℓ t z')) = W (t + 1) / W t := by
        calc
          (∑ z' : C, q t z' * Real.exp (-η * ℓ t z')) =
            (∑ z' : C, (Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z')) / W t) *
              Real.exp (-η * ℓ t z')) := by
            refine Finset.sum_congr rfl (fun z' hz' => ?_)
            rw [ih z']
          _ = (∑ z' : C, (Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z')) *
              Real.exp (-η * ℓ t z')) / W t) := by
            refine Finset.sum_congr rfl (fun z' hz' => ?_)
            ring
          _ = (∑ z' : C, Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z')) *
              Real.exp (-η * ℓ t z')) / W t := by rw [Finset.sum_div]
          _ = (∑ z' : C, Real.exp ((-η * (∑ s ∈ Finset.range t, ℓ s z')) + (-η * ℓ t z'))) / W t := by
            refine congrArg (fun x => x / W t) (Finset.sum_congr rfl (fun z' hz' => ?_))
            rw [Real.exp_add]
          _ = (∑ z' : C, Real.exp (-η * ((∑ s ∈ Finset.range t, ℓ s z') + ℓ t z'))) / W t := by
            refine congrArg (fun x => x / W t) (Finset.sum_congr rfl (fun z' hz' => ?_))
            ring
          _ = (∑ z' : C, Real.exp (-η * (∑ s ∈ Finset.range (t + 1), ℓ s z'))) / W t := by
            simp [Finset.sum_range_succ]
          _ = W (t + 1) / W t := by rfl
      rw [ih z, h_denom]
      -- Goal: (A/Wt)*B/(C/Wt) = D/C
      field_simp [hW_ne_zero t]
      -- Goal: exp(-(η*S_t z)) * exp(-(η*ℓ t z)) / W(t+1) = exp(-(η*S_{t+1} z)) / W(t+1)
      -- Combine exponentials
      rw [← Real.exp_add]
      -- Goal: exp(-(η*S_t z) + -(η*ℓ t z)) / W(t+1) = exp(-(η*S_{t+1} z)) / W(t+1)
      congr 1
      -- Goal: -(η*S_t z) + -(η*ℓ t z) = -(η*S_{t+1} z)
      simp [Finset.sum_range_succ]
      ring
  -- From the closed form, compute ∑ z, q t z * exp(-η * ℓ t z) = W (t+1) / W t
  have h_sum_eq : ∀ t, (∑ z : C, q t z * Real.exp (-η * ℓ t z)) = W (t + 1) / W t := by
    intro t
    calc
      (∑ z : C, q t z * Real.exp (-η * ℓ t z)) =
        (∑ z : C, (Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z)) / W t) * Real.exp (-η * ℓ t z)) := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [hq_closed t z]
      _ = (∑ z : C, (Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z)) * Real.exp (-η * ℓ t z)) / W t) := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        ring
      _ = (∑ z : C, Real.exp (-η * (∑ s ∈ Finset.range t, ℓ s z)) * Real.exp (-η * ℓ t z)) / W t := by
        rw [Finset.sum_div]
      _ = (∑ z : C, Real.exp (-η * ((∑ s ∈ Finset.range t, ℓ s z) + ℓ t z))) / W t := by
        refine congrArg (fun x => x / W t) (Finset.sum_congr rfl (fun z hz => ?_))
        rw [← Real.exp_add]
        ring
      _ = (∑ z : C, Real.exp (-η * (∑ s ∈ Finset.range (t + 1), ℓ s z))) / W t := by
        simp [Finset.sum_range_succ]
      _ = W (t + 1) / W t := by rfl
  -- Now the main inequality
  have h_telescope : (∑ t ∈ Finset.range n, Real.log (W (t + 1) / W t)) =
      Real.log (W n) - Real.log (W 0) := by
    induction' n with m ih
    · simp
    · rw [Finset.sum_range_succ, ih, Real.log_div (hW_pos (m + 1)).ne' (hW_pos m).ne']
      ring
  have hkey : Real.exp (-η * (∑ t ∈ Finset.range n, ℓ t y)) ≤ W n := by
    dsimp [W]
    have hmem : y ∈ (Finset.univ : Finset C) := Finset.mem_univ y
    have h_nonneg : ∀ z, 0 ≤ Real.exp (-η * (∑ t ∈ Finset.range n, ℓ t z)) := by
      intro z; exact le_of_lt (Real.exp_pos _)
    have h_single := Finset.single_le_sum (fun z hz => h_nonneg z) hmem
    simpa using h_single
  have hineq : 0 ≤ η * (∑ t ∈ Finset.range n, ℓ t y) + Real.log (W n) := by
    have hlog := Real.log_le_log (Real.exp_pos _) hkey
    rw [Real.log_exp (-η * (∑ t ∈ Finset.range n, ℓ t y))] at hlog
    linarith
  -- The key algebraic identity: rewrite the goal
  have h_main_ineq : -Real.log (Fintype.card C) / η ≤
      (∑ t ∈ Finset.range n, ℓ t y) + (1 / η) * (Real.log (W n) - Real.log (Fintype.card C)) := by
    -- Replace Fintype.card C with W 0
    rw [← hW0]
    -- Goal: -log(W 0)/η ≤ S + (1/η)*(log(W n) - log(W 0))
    -- = (S*η + log(W n) - log(W 0))/η
    have h_rhs : (∑ t ∈ Finset.range n, ℓ t y) + (1 / η) * (Real.log (W n) - Real.log (W 0)) =
        ((∑ t ∈ Finset.range n, ℓ t y) * η + Real.log (W n) - Real.log (W 0)) / η := by
      field_simp [hη.ne']
      ring
    rw [h_rhs]
    -- Goal: -log(W 0)/η ≤ (S*η + log(W n) - log(W 0))/η
    -- Multiply both sides by η > 0
    field_simp [hη.ne']
    -- Goal: -log(W 0) ≤ S*η + log(W n) - log(W 0)
    linarith
  -- Now connect h_main_ineq to the original goal using h_sum_eq and h_telescope
  calc
    -Real.log (Fintype.card C) / η ≤
        (∑ t ∈ Finset.range n, ℓ t y) + (1 / η) * (Real.log (W n) - Real.log (Fintype.card C)) :=
      h_main_ineq
    _ = (∑ t ∈ Finset.range n, ℓ t y) + (1 / η) * (Real.log (W n) - Real.log (W 0)) := by
      rw [hW0]
    _ = (∑ t ∈ Finset.range n, ℓ t y) + (1 / η) * (∑ t ∈ Finset.range n, Real.log (W (t + 1) / W t)) := by
      rw [h_telescope]
    _ = ∑ t ∈ Finset.range n, (ℓ t y + (1 / η) * Real.log (W (t + 1) / W t)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ t ∈ Finset.range n, (ℓ t y + (1 / η) * Real.log (∑ z, q t z * Real.exp (-η * ℓ t z))) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [h_sum_eq t]

theorem AdversarialBco.br_round {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z)
    (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (g : C → Bool → C → ℝ)
    (hgpos : ∀ x b, 0 < p x → ∑ z, q z * Real.exp (-η * (g x b z / p x)) ≤ 1)
    (hgzero : ∀ x b, p x = 0 → ∀ z, 0 ≤ g x b z) (f : C → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (y : C) :
    ∑ x, ∑ b : Bool, p x * (if b then f x else 1 - f x) *
        (f x - f y + g x b y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x b z / p x)))) ≤
      ∑ x, p x * f x - f y + ∑ x, ((1 - f x) * g x false y + f x * g x true y) := by
  have hηdivpos : 0 < 1 / η := by positivity
  have hf_nonneg : ∀ x, 0 ≤ f x := λ x => (hf x).1
  have hf_le_one : ∀ x, f x ≤ 1 := λ x => (hf x).2
  have h_one_minus_f_nonneg : ∀ x, 0 ≤ 1 - f x := λ x => by
    have h := hf_le_one x
    linarith
  have h_term_ineq : ∀ x, ∑ b : Bool, p x * (if b then f x else 1 - f x) *
      (f x - f y + g x b y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x b z / p x)))) ≤
      p x * (f x - f y) + ((1 - f x) * g x false y + f x * g x true y) := by
    intro x
    by_cases hpx : p x = 0
    · rw [hpx]
      have h_right_nonneg : 0 ≤ (1 - f x) * g x false y + f x * g x true y := by
        have hgfalse := hgzero x false hpx y
        have hgtrue := hgzero x true hpx y
        have h1f := hf_nonneg x
        have hf1 := hf_le_one x
        have h_nonneg_1f : 0 ≤ 1 - f x := by linarith
        have h_nonneg_f : 0 ≤ f x := h1f
        have h1 : 0 ≤ (1 - f x) * g x false y := mul_nonneg h_nonneg_1f hgfalse
        have h2 : 0 ≤ f x * g x true y := mul_nonneg h_nonneg_f hgtrue
        linarith
      simp [h_right_nonneg]
    · have hpx_pos : 0 < p x := (hp x).lt_of_ne (Ne.symm hpx)
      have hsum_expand : ∑ b : Bool, p x * (if b then f x else 1 - f x) *
          (f x - f y + g x b y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x b z / p x)))) =
          p x * (1 - f x) * (f x - f y + g x false y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x false z / p x)))) +
          p x * f x * (f x - f y + g x true y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x true z / p x)))) := by
        simp; ring
      rw [hsum_expand]
      set A := f x - f y with hA
      set wfalse := 1 - f x with hwfalse
      set wtrue := f x with hwtrue
      set Lfalse := Real.log (∑ z, q z * Real.exp (-η * (g x false z / p x))) with hLfalse
      set Ltrue := Real.log (∑ z, q z * Real.exp (-η * (g x true z / p x))) with hLtrue
      set gfalse := g x false y with hgfalse
      set gtrue := g x true y with hgtrue
      have hLfalse_nonpos : Lfalse ≤ 0 := by
        rw [hLfalse]
        apply Real.log_nonpos
        · refine Finset.sum_nonneg (λ z hz => ?_)
          have hqz := hq z
          have hexp := Real.exp_pos (-η * (g x false z / p x))
          exact mul_nonneg (by linarith) (by linarith)
        · exact hgpos x false hpx_pos
      have hLtrue_nonpos : Ltrue ≤ 0 := by
        rw [hLtrue]
        apply Real.log_nonpos
        · refine Finset.sum_nonneg (λ z hz => ?_)
          have hqz := hq z
          have hexp := Real.exp_pos (-η * (g x true z / p x))
          exact mul_nonneg (by linarith) (by linarith)
        · exact hgpos x true hpx_pos
      have h_term_false : p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) ≤ wfalse * gfalse := by
        calc
          p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) =
              p x * wfalse * (gfalse / p x) + p x * wfalse * ((1 / η) * Lfalse) := by ring
          _ = wfalse * (p x * (gfalse / p x)) + p x * wfalse * (1 / η) * Lfalse := by ring
          _ = wfalse * gfalse + p x * wfalse * (1 / η) * Lfalse := by
            rw [mul_div_cancel₀ gfalse hpx_pos.ne.symm]
          _ ≤ wfalse * gfalse := by
            have h_nonpos : p x * wfalse * (1 / η) * Lfalse ≤ 0 := by
              have h1 : 0 ≤ p x := by linarith
              have h2 : 0 ≤ wfalse := h_one_minus_f_nonneg x
              have h3 : 0 ≤ 1 / η := by linarith
              have h4 : Lfalse ≤ 0 := hLfalse_nonpos
              have hpos : 0 ≤ p x * wfalse * (1 / η) := by
                apply mul_nonneg (mul_nonneg h1 h2) h3
              exact mul_nonpos_of_nonneg_of_nonpos hpos h4
            linarith
      have h_term_true : p x * wtrue * (gtrue / p x + (1 / η) * Ltrue) ≤ wtrue * gtrue := by
        calc
          p x * wtrue * (gtrue / p x + (1 / η) * Ltrue) =
              p x * wtrue * (gtrue / p x) + p x * wtrue * ((1 / η) * Ltrue) := by ring
          _ = wtrue * (p x * (gtrue / p x)) + p x * wtrue * (1 / η) * Ltrue := by ring
          _ = wtrue * gtrue + p x * wtrue * (1 / η) * Ltrue := by
            rw [mul_div_cancel₀ gtrue hpx_pos.ne.symm]
          _ ≤ wtrue * gtrue := by
            have h_nonpos : p x * wtrue * (1 / η) * Ltrue ≤ 0 := by
              have h1 : 0 ≤ p x := by linarith
              have h2 : 0 ≤ wtrue := hf_nonneg x
              have h3 : 0 ≤ 1 / η := by linarith
              have h4 : Ltrue ≤ 0 := hLtrue_nonpos
              have hpos : 0 ≤ p x * wtrue * (1 / η) := by
                apply mul_nonneg (mul_nonneg h1 h2) h3
              exact mul_nonpos_of_nonneg_of_nonpos hpos h4
            linarith
      calc
        p x * wfalse * (A + gfalse / p x + (1 / η) * Lfalse) + p x * wtrue * (A + gtrue / p x + (1 / η) * Ltrue) =
            (p x * wfalse * A + p x * wfalse * (gfalse / p x + (1 / η) * Lfalse)) +
            (p x * wtrue * A + p x * wtrue * (gtrue / p x + (1 / η) * Ltrue)) := by ring
        _ = p x * A * (wfalse + wtrue) + (p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) + p x * wtrue * (gtrue / p x + (1 / η) * Ltrue)) := by ring
        _ = p x * A * ((1 - f x) + f x) + (p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) + p x * wtrue * (gtrue / p x + (1 / η) * Ltrue)) := by
          rw [hwfalse, hwtrue]
        _ = p x * A * 1 + (p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) + p x * wtrue * (gtrue / p x + (1 / η) * Ltrue)) := by ring
        _ = p x * A + (p x * wfalse * (gfalse / p x + (1 / η) * Lfalse) + p x * wtrue * (gtrue / p x + (1 / η) * Ltrue)) := by ring
        _ ≤ p x * A + (wfalse * gfalse + wtrue * gtrue) := by
          nlinarith
        _ = p x * (f x - f y) + ((1 - f x) * g x false y + f x * g x true y) := by
          rw [hA, hwfalse, hwtrue, hgfalse, hgtrue]
  calc
    ∑ x, ∑ b : Bool, p x * (if b then f x else 1 - f x) *
        (f x - f y + g x b y / p x + (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g x b z / p x)))) ≤
      ∑ x, (p x * (f x - f y) + ((1 - f x) * g x false y + f x * g x true y)) := by
      refine Finset.sum_le_sum (λ x hx => h_term_ineq x)
    _ = (∑ x, p x * (f x - f y)) + (∑ x, ((1 - f x) * g x false y + f x * g x true y)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ x, (p x * f x - p x * f y)) + (∑ x, ((1 - f x) * g x false y + f x * g x true y)) := by
      rw [Finset.sum_congr rfl (λ x hx => by rw [mul_sub])]
    _ = ((∑ x, p x * f x) - (∑ x, p x * f y)) + (∑ x, ((1 - f x) * g x false y + f x * g x true y)) := by
      rw [Finset.sum_sub_distrib]
    _ = ((∑ x, p x * f x) - f y) + (∑ x, ((1 - f x) * g x false y + f x * g x true y)) := by
      have h : (∑ x, p x * f y) = f y := by
        rw [← Finset.sum_mul, hp1, one_mul]
      rw [h]
    _ = ∑ x, p x * f x - f y + ∑ x, ((1 - f x) * g x false y + f x * g x true y) := rfl

theorem AdversarialBco.gibbs_lower {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q r : C → ℝ) (hq : ∀ z, 0 < q z)
    (hr : ∀ z, 0 ≤ r z) (hr1 : ∑ z, r z = 1) (e : C → ℝ) (he : ∑ z, q z * Real.exp (-η * e z) ≤ 1) :
    -(∑ z, r z * Real.log (r z / q z)) / η ≤ ∑ z, r z * e z := by
  rw [div_le_iff₀ hη]
  -- Goal: -(∑ z, r z * Real.log (r z / q z)) ≤ η * (∑ z, r z * e z)
  have hterm (z : C) : r z * Real.log ((q z * Real.exp (-η * e z)) / r z) ≤ q z * Real.exp (-η * e z) - r z := by
    by_cases hrz : r z = 0
    · rw [hrz]
      simp
      apply mul_nonneg (le_of_lt (hq z)) (le_of_lt (Real.exp_pos _))
    · have hrz_pos : 0 < r z := lt_of_le_of_ne (hr z) (Ne.symm hrz)
      have hx_pos : 0 < (q z * Real.exp (-η * e z)) / r z :=
        div_pos (mul_pos (hq z) (Real.exp_pos _)) hrz_pos
      have hlog := Real.log_le_sub_one_of_pos hx_pos
      calc
        r z * Real.log ((q z * Real.exp (-η * e z)) / r z) ≤ r z * (((q z * Real.exp (-η * e z)) / r z) - 1) := by
          nlinarith
        _ = q z * Real.exp (-η * e z) - r z := by
          field_simp [hrz]
  have hsum_le : (∑ z, r z * Real.log ((q z * Real.exp (-η * e z)) / r z)) ≤
                (∑ z, (q z * Real.exp (-η * e z) - r z)) :=
    Finset.sum_le_sum fun z _ => hterm z
  have hsum_simp : (∑ z, (q z * Real.exp (-η * e z) - r z)) = (∑ z, q z * Real.exp (-η * e z)) - (∑ z, r z) := by
    simp [Finset.sum_sub_distrib]
  have hsum_le_zero : (∑ z, r z * Real.log ((q z * Real.exp (-η * e z)) / r z)) ≤ 0 := by
    linarith
  have hidentity : (∑ z, r z * Real.log ((q z * Real.exp (-η * e z)) / r z)) =
                  -(∑ z, r z * Real.log (r z / q z)) - η * (∑ z, r z * e z) := by
    calc
      (∑ z, r z * Real.log ((q z * Real.exp (-η * e z)) / r z))
          = (∑ z, (r z * Real.log (q z / r z) - η * r z * e z)) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases hrz : r z = 0
            · rw [hrz]
              simp
            · have hqz_ne : q z ≠ 0 := (hq z).ne.symm
              have hqexp_ne : q z * Real.exp (-η * e z) ≠ 0 :=
                mul_ne_zero hqz_ne (Real.exp_ne_zero _)
              calc
                r z * Real.log ((q z * Real.exp (-η * e z)) / r z)
                    = r z * (Real.log (q z * Real.exp (-η * e z)) - Real.log (r z)) := by
                      rw [Real.log_div hqexp_ne hrz]
                _ = r z * ((Real.log (q z) + Real.log (Real.exp (-η * e z))) - Real.log (r z)) := by
                      rw [Real.log_mul hqz_ne (Real.exp_ne_zero _)]
                _ = r z * ((Real.log (q z) + (-η * e z)) - Real.log (r z)) := by rw [Real.log_exp]
                _ = r z * (Real.log (q z) - Real.log (r z) - η * e z) := by ring
                _ = r z * Real.log (q z / r z) - η * r z * e z := by
                      rw [Real.log_div hqz_ne hrz]
                      ring
      _ = (∑ z, r z * Real.log (q z / r z)) - (∑ z, η * r z * e z) := by
            simp [Finset.sum_sub_distrib]
      _ = (∑ z, r z * Real.log (q z / r z)) - η * (∑ z, r z * e z) := by
            simp [Finset.mul_sum, mul_assoc]
      _ = -(∑ z, r z * Real.log (r z / q z)) - η * (∑ z, r z * e z) := by
            have h_neg : (∑ z, r z * Real.log (q z / r z)) = -(∑ z, r z * Real.log (r z / q z)) := by
              calc
                (∑ z, r z * Real.log (q z / r z)) = (∑ z, -(r z * Real.log (r z / q z))) := by
                  refine Finset.sum_congr rfl fun z _ => ?_
                  by_cases hrz : r z = 0
                  · rw [hrz]
                    simp
                  · have hqz_ne : q z ≠ 0 := (hq z).ne.symm
                    rw [Real.log_div hqz_ne hrz, Real.log_div hrz hqz_ne]
                    ring
                _ = -(∑ z, r z * Real.log (r z / q z)) := by simp
            rw [h_neg]
  linarith

theorem AdversarialBco.gibbs_upper {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q r : C → ℝ) (hq : ∀ z, 0 < q z)
    (hq1 : ∑ z, q z = 1) (hr : ∀ z, 0 ≤ r z) (hr1 : ∑ z, r z = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : C → ℝ, ∑ z, q z * Real.exp (-η * e z) ≤ 1 ∧
      ∑ z, r z * e z ≤ -(∑ z, r z * Real.log (r z / q z)) / η + δ := by
  have hηδ_pos : 0 < η * δ := mul_pos hη hδ
  have h_one_div_η_pos : 0 < 1 / η := div_pos (by norm_num) hη
  set M := max 1 (-(Real.log (η * δ)) / η) with hM_def
  have hM_pos : 0 < M := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    have hM_ge_one : 1 ≤ M := le_max_left _ _
    linarith
  have hM_bound : Real.exp (-η * M) ≤ η * δ := by
    have h : -η * M ≤ Real.log (η * δ) := by
      have hM_ge : -(Real.log (η * δ)) / η ≤ M := le_max_right _ _
      have h' : -(Real.log (η * δ)) ≤ η * M := by
        calc
          -(Real.log (η * δ)) = (-(Real.log (η * δ)) / η) * η := by field_simp
          _ ≤ M * η := mul_le_mul_of_nonneg_right hM_ge (by linarith)
          _ = η * M := mul_comm _ _
      linarith
    have h_exp := Real.exp_le_exp_of_le h
    have h_exp_log : Real.exp (Real.log (η * δ)) = η * δ := Real.exp_log hηδ_pos
    rw [h_exp_log] at h_exp
    exact h_exp
  have h_log_bound : (1 / η) * Real.log (1 + Real.exp (-η * M)) ≤ δ := by
    have h_exp_pos : 0 < Real.exp (-η * M) := Real.exp_pos _
    have h_sum_pos : 0 < 1 + Real.exp (-η * M) := by linarith
    have h_log_le : Real.log (1 + Real.exp (-η * M)) ≤ Real.exp (-η * M) := by
      have := Real.log_le_sub_one_of_pos h_sum_pos
      linarith
    calc
      (1 / η) * Real.log (1 + Real.exp (-η * M)) ≤ (1 / η) * Real.exp (-η * M) :=
        mul_le_mul_of_nonneg_left h_log_le (by linarith [h_one_div_η_pos])
      _ ≤ (1 / η) * (η * δ) := mul_le_mul_of_nonneg_left hM_bound (by linarith [h_one_div_η_pos])
      _ = δ := by field_simp
  set u := λ z => -(1 / η) * Real.log (r z / q z) with hu_def
  set eM := λ z => if r z > 0 then min (u z) M else M with heM_def
  set e := λ z => eM z + (1 / η) * Real.log (1 + Real.exp (-η * M)) with he_def
  refine ⟨e, ?_, ?_⟩
  · -- First condition: ∑ z, q z * Real.exp (-η * e z) ≤ 1
    have hpos_sum : 0 < 1 + Real.exp (-η * M) := by
      have h := Real.exp_pos (-η * M)
      linarith
    have h_expand : ∀ z, Real.exp (-η * e z) = Real.exp (-η * eM z) * ((1 + Real.exp (-η * M))⁻¹) := by
      intro z
      dsimp [e]
      have hcalc : -η * (eM z + (1 / η) * Real.log (1 + Real.exp (-η * M))) =
          -η * eM z + (-Real.log (1 + Real.exp (-η * M))) := by
        field_simp [ne_of_gt hη]
        ring
      calc
        Real.exp (-η * (eM z + (1 / η) * Real.log (1 + Real.exp (-η * M)))) =
            Real.exp (-η * eM z + (-Real.log (1 + Real.exp (-η * M)))) := by rw [hcalc]
        _ = Real.exp (-η * eM z) * Real.exp (-Real.log (1 + Real.exp (-η * M))) := by rw [Real.exp_add]
        _ = Real.exp (-η * eM z) * (Real.exp (Real.log (1 + Real.exp (-η * M))))⁻¹ := by rw [Real.exp_neg]
        _ = Real.exp (-η * eM z) * (1 + Real.exp (-η * M))⁻¹ := by rw [Real.exp_log hpos_sum]
    have h_key : ∀ z, q z * Real.exp (-η * eM z) ≤ r z + q z * Real.exp (-η * M) := by
      intro z
      simp only [eM, u]
      by_cases hrz : r z > 0
      · simp only [hrz, ↓reduceIte]
        by_cases huz : -(1 / η) * Real.log (r z / q z) ≤ M
        · rw [min_eq_left huz]
          have h_div_pos : 0 < r z / q z := div_pos hrz (hq z)
          calc
            q z * Real.exp (-η * (-(1 / η) * Real.log (r z / q z))) = q z * Real.exp (Real.log (r z / q z)) := by
              have harg : -η * (-(1 / η) * Real.log (r z / q z)) = Real.log (r z / q z) := by
                field_simp [ne_of_gt hη]
              rw [harg]
            _ = q z * (r z / q z) := by rw [Real.exp_log h_div_pos]
            _ = r z := by field_simp [(hq z).ne.symm]
            _ ≤ r z + q z * Real.exp (-η * M) := by
              have h_nonneg : 0 ≤ q z * Real.exp (-η * M) := by
                have hq_nonneg := le_of_lt (hq z)
                have h_exp_nonneg := le_of_lt (Real.exp_pos (-η * M))
                nlinarith
              nlinarith
        · rw [min_eq_right (by linarith)]
          nlinarith
      · have hrz_le : r z ≤ 0 := not_lt.mp hrz
        have hrz0 : r z = 0 := le_antisymm hrz_le (hr z)
        simp [hrz0]
    calc
      ∑ z, q z * Real.exp (-η * e z) = ∑ z, q z * (Real.exp (-η * eM z) * ((1 + Real.exp (-η * M))⁻¹)) := by
        apply Finset.sum_congr rfl (λ z _ => by rw [h_expand z])
      _ = (∑ z, q z * Real.exp (-η * eM z)) * ((1 + Real.exp (-η * M))⁻¹) := by
        simp_rw [Finset.sum_mul, mul_assoc]
      _ ≤ (1 + Real.exp (-η * M)) * ((1 + Real.exp (-η * M))⁻¹) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc
          ∑ z, q z * Real.exp (-η * eM z) ≤ ∑ z, (r z + q z * Real.exp (-η * M)) :=
            Finset.sum_le_sum (λ z _ => h_key z)
          _ = (∑ z, r z) + (∑ z, q z * Real.exp (-η * M)) := Finset.sum_add_distrib
          _ = 1 + (∑ z, q z * Real.exp (-η * M)) := by rw [hr1]
          _ = 1 + (∑ z, q z) * Real.exp (-η * M) := by rw [Finset.sum_mul]
          _ = 1 + 1 * Real.exp (-η * M) := by rw [hq1]
          _ = 1 + Real.exp (-η * M) := by simp
      _ = 1 := by field_simp
  · -- Second condition: ∑ z, r z * e z ≤ -(∑ z, r z * Real.log (r z / q z)) / η + δ
    have h_sum_r : ∑ z, r z = 1 := hr1
    have h_val : ∀ z, r z * eM z ≤ -(r z / η) * Real.log (r z / q z) := by
      intro z
      simp only [eM, u]
      by_cases hrz : r z > 0
      · simp only [hrz, ↓reduceIte]
        have h_min_le : min (-(1 / η) * Real.log (r z / q z)) M ≤ -(1 / η) * Real.log (r z / q z) :=
          min_le_left _ _
        calc
          r z * min (-(1 / η) * Real.log (r z / q z)) M ≤ r z * (-(1 / η) * Real.log (r z / q z)) :=
            mul_le_mul_of_nonneg_left h_min_le (hr z)
          _ = -(r z / η) * Real.log (r z / q z) := by ring
      · have hrz_le : r z ≤ 0 := not_lt.mp hrz
        have hrz0 : r z = 0 := le_antisymm hrz_le (hr z)
        simp [hrz0]
    calc
      ∑ z, r z * e z = ∑ z, r z * (eM z + (1 / η) * Real.log (1 + Real.exp (-η * M))) := rfl
      _ = ∑ z, (r z * eM z + r z * ((1 / η) * Real.log (1 + Real.exp (-η * M)))) := by
        refine Finset.sum_congr rfl (λ z _ => ?_)
        ring
      _ = (∑ z, r z * eM z) + (∑ z, r z * ((1 / η) * Real.log (1 + Real.exp (-η * M)))) :=
        Finset.sum_add_distrib
      _ = (∑ z, r z * eM z) + ((∑ z, r z) * ((1 / η) * Real.log (1 + Real.exp (-η * M)))) := by
        rw [Finset.sum_mul]
      _ = (∑ z, r z * eM z) + (1 * ((1 / η) * Real.log (1 + Real.exp (-η * M)))) := by rw [h_sum_r]
      _ = (∑ z, r z * eM z) + (1 / η) * Real.log (1 + Real.exp (-η * M)) := by ring
      _ ≤ (∑ z, (-(r z / η) * Real.log (r z / q z))) + (1 / η) * Real.log (1 + Real.exp (-η * M)) := by
        have hsum := Finset.sum_le_sum (s := Finset.univ) (λ z hz => h_val z)
        gcongr
      _ = (-(1 / η)) * (∑ z, r z * Real.log (r z / q z)) + (1 / η) * Real.log (1 + Real.exp (-η * M)) := by
        have h_eq : ∑ z, (-(r z / η) * Real.log (r z / q z)) = (-(1 / η)) * (∑ z, r z * Real.log (r z / q z)) := by
          calc
            ∑ z, (-(r z / η) * Real.log (r z / q z)) = ∑ z, (-(1 / η) * (r z * Real.log (r z / q z))) := by
              refine Finset.sum_congr rfl (λ z _ => ?_)
              ring
            _ = (-(1 / η)) * (∑ z, r z * Real.log (r z / q z)) := by rw [Finset.mul_sum]
        rw [h_eq]
      _ = -(∑ z, r z * Real.log (r z / q z)) / η + (1 / η) * Real.log (1 + Real.exp (-η * M)) := by ring
      _ ≤ -(∑ z, r z * Real.log (r z / q z)) / η + δ := by
        gcongr

open scoped BigOperators in
theorem AdversarialBco.compensation {Y : Type*} [Fintype Y] (w a q : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (ha : ∀ y, a y ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ y, 0 < q y) :
    ∑ y, w y * a y * Real.log (w y * a y / ((∑ y', w y' * a y') * q y)) +
        ∑ y, w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - ∑ y', w y' * a y') * q y)) =
      ∑ y, w y * (a y * Real.log (a y / ∑ y', w y' * a y') +
          (1 - a y) * Real.log ((1 - a y) / (1 - ∑ y', w y' * a y'))) +
        ∑ y, w y * Real.log (w y / q y) := by
  set abar := ∑ y', w y' * a y' with habar
  have h_one_minus_abar : 1 - abar = ∑ y', w y' * (1 - a y') := by
    calc
      1 - abar = (∑ y', w y') - ∑ y', w y' * a y' := by rw [hw1]
      _ = ∑ y', (w y' - w y' * a y') := by rw [Finset.sum_sub_distrib]
      _ = ∑ y', w y' * (1 - a y') := by
        refine Finset.sum_congr rfl fun y' _ => ?_
        ring
  have hq_ne_zero (y : Y) : q y ≠ 0 := by linarith [hq y]
  have habar_ge (y : Y) : w y * a y ≤ abar := by
    rw [habar]
    have hpos : ∀ i ∈ (Finset.univ : Finset Y), 0 ≤ w i * a i := by
      intro i hi
      have hw' := hw i
      have ha_low := (ha i).1
      nlinarith
    exact Finset.single_le_sum hpos (Finset.mem_univ y)
  have h_one_minus_abar_ge (y : Y) : w y * (1 - a y) ≤ 1 - abar := by
    rw [h_one_minus_abar]
    have hpos : ∀ i ∈ (Finset.univ : Finset Y), 0 ≤ w i * (1 - a i) := by
      intro i hi
      have hw' := hw i
      have ha_high := (ha i).2
      nlinarith
    exact Finset.single_le_sum hpos (Finset.mem_univ y)
  have hterm (y : Y) : w y * a y * Real.log (w y * a y / (abar * q y)) +
      w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y)) =
      w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
    by_cases hwy : w y = 0
    · rw [hwy]
      simp
    · have hwypos : 0 < w y := by
        by_contra! h
        have heq : w y = 0 := le_antisymm h (hw y)
        exact hwy heq
      have hay_low : 0 ≤ a y := (ha y).1
      have hay_high : a y ≤ 1 := (ha y).2
      by_cases hay0 : a y = 0
      · -- a y = 0
        have h_one_minus_abar_pos : 0 < 1 - abar := by
          have hpos : 0 < w y * (1 - a y) := by
            rw [hay0]
            simp [hwypos]
          have hge := h_one_minus_abar_ge y
          linarith
        have h_eq : w y / ((1 - abar) * q y) = (1 / (1 - abar)) * (w y / q y) := by
          field_simp [h_one_minus_abar_pos.ne.symm, hq_ne_zero y]
        calc
          w y * a y * Real.log (w y * a y / (abar * q y)) +
              w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y))
          = w y * 0 * Real.log (w y * 0 / (abar * q y)) +
              w y * (1 - 0) * Real.log (w y * (1 - 0) / ((1 - abar) * q y)) := by rw [hay0]
          _ = w y * Real.log (w y / ((1 - abar) * q y)) := by simp
          _ = w y * Real.log ((1 / (1 - abar)) * (w y / q y)) := by rw [h_eq]
          _ = w y * (Real.log (1 / (1 - abar)) + Real.log (w y / q y)) := by
            rw [Real.log_mul (div_ne_zero (by norm_num) h_one_minus_abar_pos.ne.symm)
              (div_ne_zero hwypos.ne.symm (hq_ne_zero y))]
          _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
            rw [hay0]
            simp
      · by_cases hay1 : a y = 1
        · -- a y = 1
          have habar_pos : 0 < abar := by
            have hpos : 0 < w y * a y := by
              rw [hay1]
              simp [hwypos]
            have hge := habar_ge y
            linarith
          have h_eq : w y / (abar * q y) = (1 / abar) * (w y / q y) := by
            field_simp [habar_pos.ne.symm, hq_ne_zero y]
          calc
            w y * a y * Real.log (w y * a y / (abar * q y)) +
                w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y))
            = w y * 1 * Real.log (w y * 1 / (abar * q y)) +
                w y * (1 - 1) * Real.log (w y * (1 - 1) / ((1 - abar) * q y)) := by rw [hay1]
            _ = w y * Real.log (w y / (abar * q y)) := by simp
            _ = w y * Real.log ((1 / abar) * (w y / q y)) := by rw [h_eq]
            _ = w y * (Real.log (1 / abar) + Real.log (w y / q y)) := by
              rw [Real.log_mul (div_ne_zero (by norm_num) habar_pos.ne.symm)
                (div_ne_zero hwypos.ne.symm (hq_ne_zero y))]
            _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
              rw [hay1]
              simp
        · -- 0 < a y < 1
          have haypos : 0 < a y := by
            by_contra! h
            apply hay0
            linarith
          have haylt1 : a y < 1 := by
            by_contra! h
            apply hay1
            linarith
          have habar_pos : 0 < abar := by
            have hpos : 0 < w y * a y := mul_pos hwypos haypos
            have hge := habar_ge y
            linarith
          have h_one_minus_abar_pos : 0 < 1 - abar := by
            have hpos : 0 < w y * (1 - a y) := mul_pos hwypos (by linarith)
            have hge := h_one_minus_abar_ge y
            linarith
          -- First part: w*a*log(w*a/(abar*q)) = w*a*(log(a/abar) + log(w/q))
          have hpart1 : w y * a y * Real.log (w y * a y / (abar * q y)) =
              w y * a y * (Real.log (a y / abar) + Real.log (w y / q y)) := by
            have h_eq : w y * a y / (abar * q y) = (a y / abar) * (w y / q y) := by
              field_simp [habar_pos.ne.symm, hq_ne_zero y]
            rw [h_eq]
            rw [Real.log_mul (div_ne_zero haypos.ne.symm habar_pos.ne.symm)
              (div_ne_zero hwypos.ne.symm (hq_ne_zero y))]
          -- Second part: w*(1-a)*log(w*(1-a)/((1-abar)*q)) = w*(1-a)*(log((1-a)/(1-abar)) + log(w/q))
          have hpart2 : w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y)) =
              w y * (1 - a y) * (Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
            have h_eq : w y * (1 - a y) / ((1 - abar) * q y) = ((1 - a y) / (1 - abar)) * (w y / q y) := by
              field_simp [h_one_minus_abar_pos.ne.symm, hq_ne_zero y]
            rw [h_eq]
            rw [Real.log_mul (div_ne_zero (by linarith) h_one_minus_abar_pos.ne.symm)
              (div_ne_zero hwypos.ne.symm (hq_ne_zero y))]
          calc
            w y * a y * Real.log (w y * a y / (abar * q y)) +
                w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y))
            = w y * a y * (Real.log (a y / abar) + Real.log (w y / q y)) +
                w y * (1 - a y) * (Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
              rw [hpart1, hpart2]
            _ = w y * (a y * (Real.log (a y / abar) + Real.log (w y / q y)) +
                (1 - a y) * (Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y))) := by ring
            _ = w y * (a y * Real.log (a y / abar) + a y * Real.log (w y / q y) +
                (1 - a y) * Real.log ((1 - a y) / (1 - abar)) + (1 - a y) * Real.log (w y / q y)) := by ring
            _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) +
                (a y + (1 - a y)) * Real.log (w y / q y)) := by ring
            _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) +
                1 * Real.log (w y / q y)) := by rw [add_comm (a y) (1 - a y), sub_add_cancel]
            _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) +
                Real.log (w y / q y)) := by ring
  calc
    ∑ y, w y * a y * Real.log (w y * a y / (abar * q y)) +
        ∑ y, w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y))
    = ∑ y, (w y * a y * Real.log (w y * a y / (abar * q y)) +
        w y * (1 - a y) * Real.log (w y * (1 - a y) / ((1 - abar) * q y))) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ y, w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)) + Real.log (w y / q y)) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [hterm y]
    _ = (∑ y, w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)))) +
        (∑ y, w y * Real.log (w y / q y)) := by
      simp [Finset.sum_add_distrib, mul_add]
    _ = ∑ y, w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar))) +
        ∑ y, w y * Real.log (w y / q y) := rfl

/-- four cases on the first coordinates, convexity of the exponential. -/
theorem AdversarialBco.convex_Eq {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z) :
    Convex ℝ {su : ℝ × (C → ℝ) | (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨
      (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)} := by
  -- G is convex: a nonnegative sum of exponentials of linear functions
  have hG : ∀ (v w : C → ℝ) (l : ℝ), 0 ≤ l → l ≤ 1 →
      ∑ z, q z * Real.exp (-η * (l * v z + (1 - l) * w z)) ≤
        l * ∑ z, q z * Real.exp (-η * v z) + (1 - l) * ∑ z, q z * Real.exp (-η * w z) := by
    intro v w l hl0 hl1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have h := convexOn_exp.2 (Set.mem_univ (-η * v z)) (Set.mem_univ (-η * w z)) hl0 (by linarith : 0 ≤ 1 - l)
      (by ring)
    simp only [smul_eq_mul] at h
    have he : -η * (l * v z + (1 - l) * w z) = l * (-η * v z) + (1 - l) * (-η * w z) := by ring
    rw [he]
    nlinarith [hq z]
  -- monotonicity: a larger argument gives a smaller sum
  have hmono : ∀ v w : C → ℝ, (∀ z, w z ≤ v z) →
      ∑ z, q z * Real.exp (-η * (v z)) ≤ ∑ z, q z * Real.exp (-η * (w z)) := by
    intro v w hvw
    refine Finset.sum_le_sum fun z _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hq z).le
    nlinarith [hvw z]
  rintro ⟨s1, u1⟩ h1 ⟨s2, u2⟩ h2 a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Pi.add_apply,
    Pi.smul_apply] at h1 h2 ⊢
  rcases h1 with ⟨hs1, hE1⟩ | ⟨hs1, hu1⟩ <;> rcases h2 with ⟨hs2, hE2⟩ | ⟨hs2, hu2⟩
  · -- both positive
    left
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp only [zero_mul, zero_add, one_mul]
      exact ⟨hs2, hE2⟩
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp only [zero_mul, add_zero, one_mul]
      exact ⟨hs1, hE1⟩
    have hs : 0 < a * s1 + b * s2 := by positivity
    refine ⟨hs, ?_⟩
    set l := a * s1 / (a * s1 + b * s2) with hl
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hs]; nlinarith
    have h1l : 1 - l = b * s2 / (a * s1 + b * s2) := by rw [hl]; field_simp; ring
    have hpt : ∀ z, (a * u1 z + b * u2 z) / (a * s1 + b * s2) = l * (u1 z / s1) + (1 - l) * (u2 z / s2) := by
      intro z; rw [h1l, hl]; field_simp
    simp only [hpt]
    calc _ ≤ l * ∑ z, q z * Real.exp (-η * (u1 z / s1)) + (1 - l) * ∑ z, q z * Real.exp (-η * (u2 z / s2)) :=
          hG (fun z => u1 z / s1) (fun z => u2 z / s2) l hl0 hl1
      _ ≤ l * 1 + (1 - l) * 1 := by gcongr
      _ = 1 := by ring
  · -- s1 > 0, s2 = 0
    subst hs2
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      right; simp only [zero_mul, zero_add, mul_zero, true_and]
      intro z; exact mul_nonneg hb (hu2 z)
    left
    have hs : 0 < a * s1 + b * 0 := by simp; positivity
    refine ⟨hs, le_trans (hmono _ (fun z => u1 z / s1) fun z => ?_) hE1⟩
    rw [mul_zero, add_zero, le_div_iff₀ (by positivity)]
    have : u1 z / s1 * (a * s1) = a * u1 z := by field_simp
    rw [this]; nlinarith [hu2 z]
  · -- s1 = 0, s2 > 0
    subst hs1
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · subst hb0
      right; simp only [zero_mul, add_zero, mul_zero, true_and]
      intro z; exact mul_nonneg ha (hu1 z)
    left
    have hs : 0 < a * 0 + b * s2 := by simp; positivity
    refine ⟨hs, le_trans (hmono _ (fun z => u2 z / s2) fun z => ?_) hE2⟩
    rw [mul_zero, zero_add, le_div_iff₀ (by positivity)]
    have : u2 z / s2 * (b * s2) = b * u2 z := by field_simp
    rw [this]; nlinarith [hu1 z]
  · -- both zero
    right
    subst hs1; subst hs2
    refine ⟨by ring, fun z => ?_⟩
    exact add_nonneg (mul_nonneg ha (hu1 z)) (mul_nonneg hb (hu2 z))

theorem AdversarialBco.convex_advSet {C : Type*} [Fintype C] (P : Set (C → ℝ)) (hP : Convex ℝ P) (hne : P.Nonempty) :
    Convex ℝ {wθ : (C → ℝ) × (C → C → ℝ) | wθ.1 ∈ stdSimplex ℝ C ∧ ∀ y, ∃ f ∈ P, wθ.2 y = wθ.1 y • f} := by
  rw [convex_iff_add_mem]
  rintro ⟨w, θ⟩ ⟨hw, hθ⟩ ⟨w', θ'⟩ ⟨hw', hθ'⟩ a b ha hb hsum
  have hw_nonneg : ∀ c, 0 ≤ w c := by
    have hmem := hw
    rw [stdSimplex_eq_inter] at hmem
    exact fun c => (Set.mem_iInter.mp hmem.left) c
  have hw'_nonneg : ∀ c, 0 ≤ w' c := by
    have hmem := hw'
    rw [stdSimplex_eq_inter] at hmem
    exact fun c => (Set.mem_iInter.mp hmem.left) c
  have hw_sum : ∑ c : C, w c = 1 := by
    have hmem := hw
    rw [stdSimplex_eq_inter] at hmem
    exact hmem.right
  have hw'_sum : ∑ c : C, w' c = 1 := by
    have hmem := hw'
    rw [stdSimplex_eq_inter] at hmem
    exact hmem.right
  refine ⟨?_, ?_⟩
  · -- a•w + b•w' ∈ stdSimplex ℝ C
    rw [stdSimplex_eq_inter]
    refine ⟨?_, ?_⟩
    · -- 0 ≤ a•w + b•w' (pointwise)
      refine Set.mem_iInter.mpr fun c => ?_
      have : 0 ≤ a * w c + b * w' c := by
        nlinarith [hw_nonneg c, hw'_nonneg c, ha, hb]
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    · -- sum = 1
      calc
        ∑ c : C, (a * w c + b * w' c) = (∑ c : C, a * w c) + (∑ c : C, b * w' c) := by
          rw [Finset.sum_add_distrib]
        _ = a * (∑ c : C, w c) + b * (∑ c : C, w' c) := by
          simp [Finset.mul_sum]
        _ = a * 1 + b * 1 := by rw [hw_sum, hw'_sum]
        _ = a + b := by ring
        _ = 1 := hsum
  · -- ∀ y, ∃ f ∈ P, (a•θ + b•θ') y = (a•w + b•w') y • f
    intro y
    have hθy := hθ y
    have hθ'y := hθ' y
    rcases hθy with ⟨f, hfP, hθy_eq⟩
    rcases hθ'y with ⟨f', hf'P, hθ'y_eq⟩
    have hθy_eq' : θ y = w y • f := by simpa using hθy_eq
    have hθ'y_eq' : θ' y = w' y • f' := by simpa using hθ'y_eq
    by_cases hzero : (a • w + b • w') y = 0
    · -- w'' y = 0
      obtain ⟨f₀, hf₀P⟩ := hne
      refine ⟨f₀, hf₀P, ?_⟩
      have hsumzero : a * w y + b * w' y = 0 := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hzero
      have hwzero : a * w y = 0 := by
        nlinarith [hw_nonneg y, hw'_nonneg y, ha, hb]
      have hw'zero : b * w' y = 0 := by
        nlinarith [hw_nonneg y, hw'_nonneg y, ha, hb]
      calc
        (a • θ + b • θ') y = a • (θ y) + b • (θ' y) := rfl
        _ = a • (w y • f) + b • (w' y • f') := by rw [hθy_eq', hθ'y_eq']
        _ = (a * w y) • f + (b * w' y) • f' := by simp [smul_smul]
        _ = 0 • f + 0 • f' := by simp [hwzero, hw'zero]
        _ = (0 : C → ℝ) := by simp
        _ = 0 • f₀ := by simp
        _ = (a • w + b • w') y • f₀ := by simpa [hzero]
    · -- w'' y > 0
      have hpos : 0 < (a • w + b • w') y := by
        have hnonneg : 0 ≤ (a • w + b • w') y := by
          have : 0 ≤ a * w y + b * w' y := by
            nlinarith [hw_nonneg y, hw'_nonneg y, ha, hb]
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
        exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
      have hpos_sum : 0 < a * w y + b * w' y := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hpos
      set s := a * w y + b * w' y with hs
      have hs_ne_zero : s ≠ 0 := by linarith
      set α := a * w y / s with hα
      set β := b * w' y / s with hβ
      have hα_nonneg : 0 ≤ α :=
        div_nonneg (mul_nonneg ha (hw_nonneg y)) (by linarith)
      have hβ_nonneg : 0 ≤ β :=
        div_nonneg (mul_nonneg hb (hw'_nonneg y)) (by linarith)
      have h_sum_αβ : α + β = 1 := by
        dsimp [α, β]
        field_simp [hs_ne_zero]
        ring
      set f'' := α • f + β • f' with hf''
      have hf''P : f'' ∈ P :=
        hP hfP hf'P hα_nonneg hβ_nonneg h_sum_αβ
      have hkey : (a * w y) • f + (b * w' y) • f' = s • f'' := by
        dsimp [f'', α, β, s]
        rw [smul_add, smul_smul, smul_smul]
        have hden_ne_zero : a * w y + b * w' y ≠ 0 := by linarith
        have h1 : (a * w y + b * w' y) * (a * w y / (a * w y + b * w' y)) = a * w y := by
          field_simp [hden_ne_zero]
        have h2 : (a * w y + b * w' y) * (b * w' y / (a * w y + b * w' y)) = b * w' y := by
          field_simp [hden_ne_zero]
        simp [h1, h2]
      refine ⟨f'', hf''P, ?_⟩
      calc
        (a • θ + b • θ') y = a • (θ y) + b • (θ' y) := rfl
        _ = a • (w y • f) + b • (w' y • f') := by rw [hθy_eq', hθ'y_eq']
        _ = (a * w y) • f + (b * w' y) • f' := by simp [smul_smul]
        _ = s • f'' := hkey
        _ = (a • w + b • w') y • f'' := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]

theorem AdversarialBco.isCompact_advSet {C : Type*} [Fintype C] (P : Set (C → ℝ)) (hP : IsCompact P) :
    IsCompact {wθ : (C → ℝ) × (C → C → ℝ) | wθ.1 ∈ stdSimplex ℝ C ∧ ∀ y, ∃ f ∈ P, wθ.2 y = wθ.1 y • f} := by
  let f : (C → ℝ) × (C → C → ℝ) → (C → ℝ) × (C → C → ℝ) := fun p => (p.1, fun y => p.1 y • p.2 y)
  have h_compact_dom : IsCompact (stdSimplex ℝ C ×ˢ (Set.univ.pi fun (_ : C) => P)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ C) (isCompact_univ_pi fun _ => hP)
  have h_cont : Continuous f := by
    refine Continuous.prodMk continuous_fst ?_
    refine continuous_pi fun y => ?_
    exact ((continuous_apply (i := y) (A := fun _ => ℝ)).comp continuous_fst).smul
      ((continuous_apply (i := y) (A := fun _ => C → ℝ)).comp continuous_snd)
  have h_image_compact : IsCompact (f '' (stdSimplex ℝ C ×ˢ (Set.univ.pi fun (_ : C) => P))) :=
    IsCompact.image h_compact_dom h_cont
  have h_eq : f '' (stdSimplex ℝ C ×ˢ (Set.univ.pi fun (_ : C) => P)) =
      {wθ : (C → ℝ) × (C → C → ℝ) | wθ.1 ∈ stdSimplex ℝ C ∧ ∀ y, ∃ f ∈ P, wθ.2 y = wθ.1 y • f} := by
    ext ⟨w, G⟩
    constructor
    · rintro ⟨⟨w', F⟩, ⟨hw', hF⟩, h⟩
      have h_eq_pair : f (w', F) = (w, G) := h
      simp [f] at h_eq_pair
      rcases h_eq_pair with ⟨rfl, rfl⟩
      refine ⟨hw', ?_⟩
      intro y
      have hFy : F y ∈ P := hF y (Set.mem_univ y)
      refine ⟨F y, hFy, ?_⟩
      rfl
    · rintro ⟨hw, hG⟩
      let F : C → C → ℝ := fun y => Classical.choose (hG y)
      have hF_spec : ∀ y, F y ∈ P ∧ G y = w y • F y := fun y => Classical.choose_spec (hG y)
      refine ⟨(w, F), ⟨hw, ?_⟩, ?_⟩
      · intro x hx
        exact (hF_spec x).1
      · ext y z
        have hf_eq : f = fun p => (p.1, fun y => p.1 y • p.2 y) := rfl
        rw [hf_eq]
        simp
        rw [(hF_spec y).2]
  rw [← h_eq]
  exact h_image_compact

open Filter Set in
theorem AdversarialBco.sg_exists {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F) (L : NNReal)
    (hL : LipschitzWith L F) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ s : EuclideanSpace ℝ (Fin d), ‖s‖ ≤ L ∧ ∀ z, F x + inner ℝ s (z - x) ≤ F z := by
  let E := EuclideanSpace ℝ (Fin d)
  -- The strict epigraph U = {(z, t) | F z < t}
  let U : Set (E × ℝ) := {p | F p.1 < p.2}
  have hU_open : IsOpen U := by
    have h_cont : Continuous F := hL.continuous
    exact isOpen_lt (h_cont.comp continuous_fst) continuous_snd
  have hU_convex : Convex ℝ U := by
    have := hF.convex_strict_epigraph
    simpa [U, mem_univ] using this
  have hx_notin_U : (x, F x) ∉ U := by
    dsimp [U]
    exact lt_irrefl (F x)
  -- Apply geometric Hahn-Banach separation
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hU_convex hU_open hx_notin_U
  -- φ : StrongDual ℝ (E × ℝ), i.e., (E × ℝ) →L[ℝ] ℝ
  -- hφ : ∀ a ∈ U, φ a < φ (x, F x)
  -- Decompose φ: let ℓ = φ ∘ (inl ℝ E ℝ) and c = φ (0, 1)
  let ℓ : E →L[ℝ] ℝ := φ ∘L (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := φ (0, 1)
  have hφ_decomp : ∀ (z : E) (t : ℝ), φ (z, t) = ℓ z + c * t := by
    intro z t
    calc
      φ (z, t) = φ ((z, 0) + (0, t)) := by simp
      _ = φ (z, 0) + φ (0, t) := φ.map_add (z, 0) (0, t)
      _ = φ ((ContinuousLinearMap.inl ℝ E ℝ) z) + φ (0, t) := by simp
      _ = ℓ z + φ (0, t) := rfl
      _ = ℓ z + φ (t • (0, 1)) := by simp
      _ = ℓ z + (t • φ (0, 1)) := by rw [φ.map_smul t (0, 1)]
      _ = ℓ z + t * c := by simp [c, smul_eq_mul]
      _ = ℓ z + c * t := by ring
  -- Show c < 0
  have hc_neg : c < 0 := by
    by_contra! hc_nonneg
    -- hc_nonneg : c ≥ 0
    have hmem : (x, F x + 1) ∈ U := by
      dsimp [U]
      exact lt_add_of_pos_right (F x) (by norm_num : (0 : ℝ) < 1)
    have h := hφ (x, F x + 1) hmem
    rw [hφ_decomp x (F x + 1), hφ_decomp x (F x)] at h
    -- h : ℓ x + c * (F x + 1) < ℓ x + c * F x
    -- i.e., ℓ x + c * F x + c < ℓ x + c * F x
    -- so c < 0, contradiction with hc_nonneg : 0 ≤ c
    have hc_lt : c < 0 := by
      linarith
    have : ¬ c < 0 := by linarith
    exact this hc_lt
  -- Taking t → F z⁺ gives ℓ z + c * F z ≤ ℓ x + c * F x
  have h_ineq : ∀ (z : E), ℓ z + c * F z ≤ ℓ x + c * F x := by
    intro z
    have h_ineq' : ∀ᶠ t in nhdsWithin (F z) (Ioi (F z)), ℓ z + c * t ≤ ℓ x + c * F x := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hmem : (z, t) ∈ U := by
        dsimp [U]
        -- ht : t ∈ Ioi (F z), which means F z < t
        exact ht
      have h := hφ (z, t) hmem
      rw [hφ_decomp z t, hφ_decomp x (F x)] at h
      linarith
    have h_tendsto : Tendsto (fun t => ℓ z + c * t) (nhdsWithin (F z) (Ioi (F z))) (nhds (ℓ z + c * F z)) := by
      refine ((continuous_const.add (continuous_const.mul continuous_id))).continuousWithinAt
    exact le_of_tendsto h_tendsto h_ineq'
  -- Rearrange: ℓ (z - x) ≤ c * (F x - F z)
  -- Multiply by (-c⁻¹) > 0 to get: (-c⁻¹ • ℓ) (z - x) ≤ F z - F x
  have h_sub_ineq : ∀ (z : E), ((-c⁻¹ : ℝ) • ℓ) (z - x) ≤ F z - F x := by
    intro z
    have h := h_ineq z
    have h_sub : ℓ (z - x) ≤ c * (F x - F z) := by
      calc
        ℓ (z - x) = ℓ z - ℓ x := by simp
        _ ≤ (ℓ x + c * F x) - c * F z - ℓ x := by linarith
        _ = c * (F x - F z) := by ring
    have hc_ne : c ≠ 0 := by linarith
    have h_nonneg : 0 ≤ -c⁻¹ := by
      have h_inv_neg : c⁻¹ < 0 := inv_lt_zero.mpr hc_neg
      linarith
    calc
      ((-c⁻¹ : ℝ) • ℓ) (z - x) = (-c⁻¹ : ℝ) * ℓ (z - x) := by simp
      _ ≤ (-c⁻¹ : ℝ) * (c * (F x - F z)) := mul_le_mul_of_nonneg_left h_sub h_nonneg
      _ = ((-c⁻¹ : ℝ) * c) * (F x - F z) := by ring
      _ = (-1) * (F x - F z) := by field_simp [hc_ne]
      _ = F z - F x := by ring
  -- Riesz representation: there exists s such that ((-c⁻¹) • ℓ) w = inner ℝ s w
  let ψ : E →L[ℝ] ℝ := -c⁻¹ • ℓ
  have h_riesz : ∃ s : E, ∀ w : E, ψ w = inner ℝ s w := by
    let s := (InnerProductSpace.toDual ℝ E).symm ψ
    refine ⟨s, λ w => ?_⟩
    calc
      ψ w = ((InnerProductSpace.toDual ℝ E) s) w := by
        simp [s, ψ]
      _ = inner ℝ s w := by rw [InnerProductSpace.toDual_apply_apply]
  obtain ⟨s, hs⟩ := h_riesz
  -- Now show ‖s‖ ≤ L
  have h_norm : ‖s‖ ≤ (L : ℝ) := by
    by_cases hs_zero : s = 0
    · subst hs_zero; simp
    · have h_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs_zero
      have h_ineq_s : ψ s ≤ (L : ℝ) * ‖s‖ := by
        have h_sub := h_sub_ineq (x + s)
        -- h_sub : ψ ((x + s) - x) ≤ F (x + s) - F x
        -- (x + s) - x = s
        have h_sub_simp : ((-c⁻¹ : ℝ) • ℓ) ((x + s) - x) = ψ s := by
          dsimp [ψ]
          simp
        rw [h_sub_simp] at h_sub
        -- h_sub : ψ s ≤ F (x + s) - F x
        have h_lip : F (x + s) - F x ≤ (L : ℝ) * ‖s‖ := by
          have hle := hL.le_add_mul (x + s) x
          rw [dist_eq_norm] at hle
          have : (x + s) - x = s := by abel
          rw [this] at hle
          linarith
        have h_inner : ψ s = inner ℝ s s := hs s
        rw [h_inner] at h_sub
        have h_norm_sq : inner ℝ s s = ‖s‖ ^ 2 := real_inner_self_eq_norm_sq _
        rw [h_norm_sq] at h_sub
        -- h_sub : ‖s‖² ≤ F (x + s) - F x
        -- h_lip : F (x + s) - F x ≤ (L : ℝ) * ‖s‖
        linarith
      -- Now h_ineq_s : ψ s ≤ (L : ℝ) * ‖s‖
      -- And ψ s = inner ℝ s s = ‖s‖²
      have h_inner : ψ s = inner ℝ s s := hs s
      rw [h_inner] at h_ineq_s
      have h_norm_sq : inner ℝ s s = ‖s‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [h_norm_sq] at h_ineq_s
      -- h_ineq_s : ‖s‖² ≤ (L : ℝ) * ‖s‖
      -- Since ‖s‖ > 0, divide by ‖s‖ to get ‖s‖ ≤ L
      nlinarith
  -- Finally, combine everything
  refine ⟨s, h_norm, λ z => ?_⟩
  have h := h_sub_ineq z
  -- h : ψ (z - x) ≤ F z - F x
  rw [hs (z - x)] at h
  -- h : inner ℝ s (z - x) ≤ F z - F x
  linarith

theorem AdversarialBco.convex_PL {d : ℕ} {C : Type*} [Fintype C] (pt : C → EuclideanSpace ℝ (Fin d)) (L : ℝ) :
    Convex ℝ {v : C → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ s : C → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxIcc, s, hs_norm, hs_ineq⟩
  rcases hy with ⟨hyIcc, t, ht_norm, ht_ineq⟩
  refine ⟨?_, ?_⟩
  · intro i
    rcases hxIcc i with ⟨hx_low, hx_high⟩
    rcases hyIcc i with ⟨hy_low, hy_high⟩
    have hlow : 0 ≤ a * x i + b * y i := by nlinarith
    have hhigh : a * x i + b * y i ≤ 1 := by nlinarith
    exact ⟨hlow, hhigh⟩
  · refine ⟨a • s + b • t, ?_, ?_⟩
    · intro i
      calc
        ‖(a • s + b • t) i‖ = ‖a • (s i) + b • (t i)‖ := rfl
        _ ≤ ‖a • (s i)‖ + ‖b • (t i)‖ := norm_add_le _ _
        _ = |a| * ‖s i‖ + |b| * ‖t i‖ := by simp [norm_smul]
        _ = a * ‖s i‖ + b * ‖t i‖ := by simp [abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * L + b * L := by
          gcongr
          · exact hs_norm i
          · exact ht_norm i
        _ = (a + b) * L := by ring
        _ = 1 * L := by rw [hab]
        _ = L := by simp
    · intro i j
      calc
        (a • x + b • y) i + inner ℝ ((a • s + b • t) i) (pt j - pt i)
            = a * x i + b * y i + inner ℝ (a • (s i) + b • (t i)) (pt j - pt i) := by simp
        _ = a * x i + b * y i + (inner ℝ (a • (s i)) (pt j - pt i) + inner ℝ (b • (t i)) (pt j - pt i)) := by
          simp [inner_add_left]
        _ = a * x i + b * y i + (a * inner ℝ (s i) (pt j - pt i) + b * inner ℝ (t i) (pt j - pt i)) := by
          simp [inner_smul_left]
        _ = a * (x i + inner ℝ (s i) (pt j - pt i)) + b * (y i + inner ℝ (t i) (pt j - pt i)) := by ring
        _ ≤ a * (x j) + b * (y j) := by
          gcongr
          · exact hs_ineq i j
          · exact ht_ineq i j
        _ = (a • x + b • y) j := by simp

open Set in
theorem AdversarialBco.isCompact_PL {d : ℕ} {C : Type*} [Fintype C] (pt : C → EuclideanSpace ℝ (Fin d)) (L : ℝ) :
    IsCompact {v : C → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ s : C → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j} := by
  -- The set is the image under Prod.fst of T
  let T : Set ((C → ℝ) × (C → EuclideanSpace ℝ (Fin d))) :=
    {p | (∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, ‖p.2 i‖ ≤ L) ∧ ∀ i j, p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j}
  have hT_closed : IsClosed T := by
    -- Each condition defines a closed set; T is their intersection
    have h_v : IsClosed {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1} := by
      -- Rewrite as intersection over i of {p | 0 ≤ p.1 i ∧ p.1 i ≤ 1}
      have h_eq : {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1} =
          ⋂ i, ({p | (0 : ℝ) ≤ p.1 i} ∩ {p | p.1 i ≤ (1 : ℝ)}) := by
        ext p; simp [Set.mem_Icc, forall_and]
      rw [h_eq]
      refine isClosed_iInter (fun i => ?_)
      have h_cont_i : Continuous (fun (p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d))) => p.1 i) :=
        (continuous_apply i).comp continuous_fst
      refine IsClosed.inter (isClosed_le continuous_const h_cont_i) (isClosed_le h_cont_i continuous_const)
    have h_s : IsClosed {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, ‖p.2 i‖ ≤ L} := by
      have h_eq : {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, ‖p.2 i‖ ≤ L} =
          ⋂ i, {p | ‖p.2 i‖ ≤ L} := by
        ext p; simp
      rw [h_eq]
      refine isClosed_iInter (fun i => ?_)
      have h_cont_norm : Continuous (fun (p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d))) => ‖p.2 i‖) :=
        Continuous.norm ((continuous_apply i).comp continuous_snd)
      exact isClosed_le h_cont_norm continuous_const
    have h_ineq : IsClosed {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i j, p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j} := by
      have h_eq : {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i j, p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j} =
          ⋂ (i : C) (j : C), {p | p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j} := by
        ext p; simp
      rw [h_eq]
      refine isClosed_iInter (fun i => ?_)
      refine isClosed_iInter (fun j => ?_)
      -- p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j
      -- equivalent to p.1 i + inner ℝ (p.2 i) (pt j - pt i) - p.1 j ≤ 0
      have h_eq2 : {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j} =
          {p | p.1 i + inner ℝ (p.2 i) (pt j - pt i) - p.1 j ≤ (0 : ℝ)} := by
        ext p; simp
      rw [h_eq2]
      have h_cont : Continuous (fun (p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d))) => p.1 i + inner ℝ (p.2 i) (pt j - pt i) - p.1 j) := by
        refine Continuous.sub ?_ ?_
        · refine Continuous.add ?_ ?_
          · exact (continuous_apply i).comp continuous_fst
          · refine Continuous.inner ?_ ?_
            · exact (continuous_apply i).comp continuous_snd
            · exact continuous_const
        · exact (continuous_apply j).comp continuous_fst
      exact isClosed_le h_cont continuous_const
    have hT_eq : T = {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1} ∩
      {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i, ‖p.2 i‖ ≤ L} ∩
      {p : (C → ℝ) × (C → EuclideanSpace ℝ (Fin d)) | ∀ i j, p.1 i + inner ℝ (p.2 i) (pt j - pt i) ≤ p.1 j} := by
      ext p; simp [T, and_assoc]
    rw [hT_eq]
    exact IsClosed.inter (IsClosed.inter h_v h_s) h_ineq
  have hT_compact : IsCompact T := by
    let K : Set ((C → ℝ) × (C → EuclideanSpace ℝ (Fin d))) :=
      (Set.univ.pi fun _ : C => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : C => Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) L)
    have hK_compact : IsCompact K := by
      have h1 : IsCompact (Set.univ.pi fun _ : C => Set.Icc (0 : ℝ) 1) := by
        refine isCompact_univ_pi (fun i => ?_)
        exact isCompact_Icc
      have h2 : IsCompact (Set.univ.pi fun _ : C => Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) L) := by
        refine isCompact_univ_pi (fun i => ?_)
        exact isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) L
      exact IsCompact.prod h1 h2
    have hT_subset_K : T ⊆ K := by
      intro p hp
      rcases hp with ⟨hv, hs, hineq⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        exact hv i
      · intro i hi
        have hball : ‖p.2 i‖ ≤ L := hs i
        simpa [Metric.mem_closedBall] using hball
    exact hK_compact.of_isClosed_subset hT_closed hT_subset_K
  have h_image : {v : C → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ s : C → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j} = Prod.fst '' T := by
    ext v; constructor
    · intro hv
      rcases hv with ⟨hvIcc, s, hsL, hineq⟩
      refine ⟨(v, s), ?_, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i; exact hvIcc i
      · intro i; exact hsL i
      · intro i j; exact hineq i j
    · intro h
      rcases h with ⟨p, hp, rfl⟩
      rcases hp with ⟨hvIcc, hsL, hineq⟩
      refine ⟨?_, p.2, ?_, ?_⟩
      · intro i; exact hvIcc i
      · intro i; exact hsL i
      · intro i j; exact hineq i j
  rw [h_image]
  exact hT_compact.image continuous_fst

theorem AdversarialBco.extension_PL {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] (pt : C → EuclideanSpace ℝ (Fin d))
    (L ε : ℝ) (v : C → ℝ) (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) (s : C → EuclideanSpace ℝ (Fin d))
    (hs : ∀ i, ‖s i‖ ≤ L) (hvs : ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j)
    (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : ∀ z ∈ J, ∃ i, ‖z - pt i‖ ≤ ε) :
    let h := fun z => Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i))
    ConvexOn ℝ Set.univ h ∧ (∀ z z', |h z - h z'| ≤ L * ‖z - z'‖) ∧ (∀ j, h (pt j) = v j) ∧
      ∀ z ∈ J, h z ∈ Set.Icc (-(L * ε)) (1 + L * ε) := by
  intro h
  have h_convex : ConvexOn ℝ Set.univ h := by
    set f : C → (EuclideanSpace ℝ (Fin d) → ℝ) := fun i z => v i + inner ℝ (s i) (z - pt i) with hf
    have h_each : ∀ i, ConvexOn ℝ Set.univ (f i) := by
      intro i
      rw [convexOn_iff_forall_pos]
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hsum
      dsimp [f]
      have hinner : inner ℝ (s i) ((a • x + b • y) - pt i) = a * inner ℝ (s i) (x - pt i) + b * inner ℝ (s i) (y - pt i) := by
        calc
          inner ℝ (s i) ((a • x + b • y) - pt i) = inner ℝ (s i) ((a • x + b • y) - (a • pt i + b • pt i)) := by
            rw [show (a • x + b • y) - pt i = (a • x + b • y) - (a • pt i + b • pt i) by
              rw [← add_smul, hsum, one_smul]]
          _ = inner ℝ (s i) ((a • x - a • pt i) + (b • y - b • pt i)) := by abel
          _ = inner ℝ (s i) (a • (x - pt i) + b • (y - pt i)) := by simp [smul_sub]
          _ = inner ℝ (s i) (a • (x - pt i)) + inner ℝ (s i) (b • (y - pt i)) := by rw [inner_add_right]
          _ = a * inner ℝ (s i) (x - pt i) + b * inner ℝ (s i) (y - pt i) := by
            simp [inner_smul_right]
      have h_eq : v i + inner ℝ (s i) ((a • x + b • y) - pt i) = a • (v i + inner ℝ (s i) (x - pt i)) + b • (v i + inner ℝ (s i) (y - pt i)) := by
        calc
          v i + inner ℝ (s i) ((a • x + b • y) - pt i) = v i + (a * inner ℝ (s i) (x - pt i) + b * inner ℝ (s i) (y - pt i)) := by rw [hinner]
          _ = (a + b) * v i + a * inner ℝ (s i) (x - pt i) + b * inner ℝ (s i) (y - pt i) := by
            rw [hsum, one_mul]
            ring
          _ = a * v i + b * v i + a * inner ℝ (s i) (x - pt i) + b * inner ℝ (s i) (y - pt i) := by ring
          _ = a * (v i + inner ℝ (s i) (x - pt i)) + b * (v i + inner ℝ (s i) (y - pt i)) := by ring
          _ = a • (v i + inner ℝ (s i) (x - pt i)) + b • (v i + inner ℝ (s i) (y - pt i)) := by
            simp [smul_eq_mul]
      exact h_eq.le
    have h_sup : ConvexOn ℝ Set.univ (Finset.sup' Finset.univ Finset.univ_nonempty f) := by
      refine Finset.sup'_induction Finset.univ_nonempty f
        (fun a₁ ha₁ a₂ ha₂ => ConvexOn.sup ha₁ ha₂) (fun i hi => h_each i)
    have : h = Finset.sup' Finset.univ Finset.univ_nonempty f := by
      ext z
      simp [h, f]
    simpa [this] using h_sup
  have h_lip : ∀ z z' : EuclideanSpace ℝ (Fin d), |h z - h z'| ≤ L * ‖z - z'‖ := by
    intro z z'
    have h_bound : h z - h z' ≤ L * ‖z - z'‖ ∧ h z' - h z ≤ L * ‖z - z'‖ := by
      constructor
      · have hz_le : h z ≤ h z' + L * ‖z - z'‖ := by
          dsimp [h]
          refine Finset.sup'_le Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i)) ?_
          intro i hi
          have h_sup_le : v i + inner ℝ (s i) (z' - pt i) ≤
              Finset.univ.sup' Finset.univ_nonempty (fun j => v j + inner ℝ (s j) (z' - pt j)) := by
            apply Finset.le_sup'_of_le (fun j => v j + inner ℝ (s j) (z' - pt j)) (Finset.mem_univ i)
            rfl
          have h_inner_eq : inner ℝ (s i) (z - pt i) = inner ℝ (s i) (z' - pt i) + inner ℝ (s i) (z - z') := by
            calc
              inner ℝ (s i) (z - pt i) = inner ℝ (s i) ((z - z') + (z' - pt i)) := by
                rw [show z - pt i = (z - z') + (z' - pt i) by abel]
              _ = inner ℝ (s i) (z - z') + inner ℝ (s i) (z' - pt i) := by rw [inner_add_right]
              _ = inner ℝ (s i) (z' - pt i) + inner ℝ (s i) (z - z') := by ring
          have h_inner_le : inner ℝ (s i) (z - z') ≤ ‖s i‖ * ‖z - z'‖ := by
            have h_abs := abs_real_inner_le_norm (s i) (z - z')
            have h_le_abs := le_abs_self (inner ℝ (s i) (z - z'))
            linarith
          calc
            v i + inner ℝ (s i) (z - pt i) = v i + (inner ℝ (s i) (z' - pt i) + inner ℝ (s i) (z - z')) := by rw [h_inner_eq]
            _ = (v i + inner ℝ (s i) (z' - pt i)) + inner ℝ (s i) (z - z') := by ring
            _ ≤ (v i + inner ℝ (s i) (z' - pt i)) + ‖s i‖ * ‖z - z'‖ := by
              simpa only [add_comm, norm_sub_rev] using add_le_add_left h_inner_le (v i + inner ℝ (s i) (z' - pt i))
            _ ≤ (v i + inner ℝ (s i) (z' - pt i)) + L * ‖z - z'‖ := by
              simpa only [add_comm, norm_sub_rev] using add_le_add_left
                (mul_le_mul_of_nonneg_right (hs i) (norm_nonneg (z' - z)))
                (v i + inner ℝ (s i) (z' - pt i))
            _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun j => v j + inner ℝ (s j) (z' - pt j))) + L * ‖z - z'‖ := by
              simpa only [add_comm] using add_le_add_right h_sup_le (L * ‖z - z'‖)
        linarith
      · have hz'_le : h z' ≤ h z + L * ‖z - z'‖ := by
          dsimp [h]
          refine Finset.sup'_le Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z' - pt i)) ?_
          intro i hi
          have h_sup_le : v i + inner ℝ (s i) (z - pt i) ≤
              Finset.univ.sup' Finset.univ_nonempty (fun j => v j + inner ℝ (s j) (z - pt j)) := by
            apply Finset.le_sup'_of_le (fun j => v j + inner ℝ (s j) (z - pt j)) (Finset.mem_univ i)
            rfl
          have h_inner_eq : inner ℝ (s i) (z' - pt i) = inner ℝ (s i) (z - pt i) + inner ℝ (s i) (z' - z) := by
            calc
              inner ℝ (s i) (z' - pt i) = inner ℝ (s i) ((z' - z) + (z - pt i)) := by
                rw [show z' - pt i = (z' - z) + (z - pt i) by abel]
              _ = inner ℝ (s i) (z' - z) + inner ℝ (s i) (z - pt i) := by rw [inner_add_right]
              _ = inner ℝ (s i) (z - pt i) + inner ℝ (s i) (z' - z) := by ring
          have h_inner_le : inner ℝ (s i) (z' - z) ≤ ‖s i‖ * ‖z - z'‖ := by
            calc
              inner ℝ (s i) (z' - z) ≤ |inner ℝ (s i) (z' - z)| := le_abs_self _
              _ ≤ ‖s i‖ * ‖z' - z‖ := abs_real_inner_le_norm _ _
              _ = ‖s i‖ * ‖z - z'‖ := by rw [norm_sub_rev]
          calc
            v i + inner ℝ (s i) (z' - pt i) = v i + (inner ℝ (s i) (z - pt i) + inner ℝ (s i) (z' - z)) := by rw [h_inner_eq]
            _ = (v i + inner ℝ (s i) (z - pt i)) + inner ℝ (s i) (z' - z) := by ring
            _ ≤ (v i + inner ℝ (s i) (z - pt i)) + ‖s i‖ * ‖z - z'‖ := by
              simpa only [add_comm, norm_sub_rev] using add_le_add_left h_inner_le (v i + inner ℝ (s i) (z - pt i))
            _ ≤ (v i + inner ℝ (s i) (z - pt i)) + L * ‖z - z'‖ := by
              simpa only [add_comm, norm_sub_rev] using add_le_add_left
                (mul_le_mul_of_nonneg_right (hs i) (norm_nonneg (z' - z)))
                (v i + inner ℝ (s i) (z - pt i))
            _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun j => v j + inner ℝ (s j) (z - pt j))) + L * ‖z - z'‖ := by
              simpa only [add_comm] using add_le_add_right h_sup_le (L * ‖z - z'‖)
        linarith
    rcases h_bound with ⟨h1, h2⟩
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have h_net : ∀ j, h (pt j) = v j := by
    intro j
    dsimp [h]
    apply le_antisymm
    · refine Finset.sup'_le Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (pt j - pt i)) ?_
      intro i hi
      exact hvs i j
    · refine Finset.le_sup'_of_le (fun i => v i + inner ℝ (s i) (pt j - pt i)) (Finset.mem_univ j) ?_
      simp
  have h_range : ∀ z ∈ J, h z ∈ Set.Icc (-(L * ε)) (1 + L * ε) := by
    intro z hz
    rcases hJ z hz with ⟨i, hi⟩
    have hv_i := hv i
    have hv_low : 0 ≤ v i := hv_i.1
    have hv_high : v i ≤ 1 := hv_i.2
    have h_net_i : h (pt i) = v i := h_net i
    have h_abs := h_lip z (pt i)
    rcases abs_le.mp h_abs with ⟨h_low, h_high⟩
    -- h_low: -(L * ‖z - pt i‖) ≤ h z - h (pt i)
    -- h_high: h z - h (pt i) ≤ L * ‖z - pt i‖
    have hL_nonneg : 0 ≤ L := by
      obtain ⟨i⟩ := ‹Nonempty C›
      have h_norm_nonneg : 0 ≤ ‖s i‖ := norm_nonneg _
      have h_le := hs i
      linarith
    have h_bound : L * ‖z - pt i‖ ≤ L * ε :=
      mul_le_mul_of_nonneg_left hi hL_nonneg
    have hz_le : h z ≤ v i + L * ε := by
      linarith
    have hz_ge : -(L * ε) ≤ h z := by
      have h_diff : h (pt i) - h z ≤ L * ‖pt i - z‖ := by
        have h_abs' := h_lip (pt i) z
        rcases abs_le.mp h_abs' with ⟨hl, hr⟩
        exact hr
      have h_norm_eq : ‖pt i - z‖ = ‖z - pt i‖ := by rw [norm_sub_rev]
      have h_norm_bound : L * ‖z - pt i‖ ≤ L * ε :=
        mul_le_mul_of_nonneg_left hi hL_nonneg
      linarith
    exact ⟨by linarith, by linarith⟩
  exact ⟨h_convex, h_lip, h_net, h_range⟩

theorem AdversarialBco.PL_of_convex {d : ℕ} {C : Type*} [Fintype C] (pt : C → EuclideanSpace ℝ (Fin d))
    (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : J.Nonempty) (hpt : ∀ i, pt i ∈ J) (L : NNReal)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ J f) (hfL : LipschitzOnWith L f J)
    (h01 : ∀ x ∈ J, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s : C → EuclideanSpace ℝ (Fin d), (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, f (pt i) + inner ℝ (s i) (pt j - pt i) ≤ f (pt j) := by
  have hL_nonneg : 0 ≤ (L : ℝ) := by exact NNReal.coe_nonneg L
  have hfb : BddBelow (f '' J) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hx' := h01 x hx
    exact hx'.1
  have hfl : ∀ x ∈ J, ∀ y ∈ J, f x ≤ f y + (L : ℝ) * dist x y :=
    fun x hx y hy => LipschitzOnWith.le_add_mul hfL hx hy
  set g := AdversarialBco.lipExt J f (L : ℝ) with hg_def
  have hg_eq : ∀ x ∈ J, g x = f x := by
    intro x hx
    exact AdversarialBco.lipExt_eq J f (L : ℝ) hfl x hx
  have hg_conv : ConvexOn ℝ Set.univ g :=
    AdversarialBco.lipExt_convex J hf.1 hJ f hf hfb (L : ℝ) hL_nonneg
  have hg_lip : LipschitzWith L g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : g x ≤ g y + (L : ℝ) * dist x y := by
      simpa [g] using AdversarialBco.lipExt_le J hJ f hfb (L : ℝ) hL_nonneg x y
    have h2 : g y ≤ g x + (L : ℝ) * dist x y := by
      simpa [g, dist_comm] using AdversarialBco.lipExt_le J hJ f hfb (L : ℝ) hL_nonneg y x
    have : |g x - g y| ≤ (L : ℝ) * dist x y := by
      have hxyle : g x - g y ≤ (L : ℝ) * dist x y := by linarith
      have hyxle : g y - g x ≤ (L : ℝ) * dist x y := by linarith
      rw [abs_le]
      constructor <;> linarith
    simpa [Real.dist_eq] using this
  have h_exists : ∀ i, ∃ s : EuclideanSpace ℝ (Fin d), ‖s‖ ≤ L ∧ ∀ z, g (pt i) + inner ℝ s (z - pt i) ≤ g z := by
    intro i
    exact AdversarialBco.sg_exists g hg_conv L hg_lip (pt i)
  choose s hs using h_exists
  refine ⟨s, ?_, ?_⟩
  · intro i
    exact hs i |>.1
  · intro i j
    have h_eq_i := hg_eq (pt i) (hpt i)
    have h_eq_j := hg_eq (pt j) (hpt j)
    have h_ineq := (hs i).2 (pt j)
    rw [h_eq_i, h_eq_j] at h_ineq
    exact h_ineq


theorem AdversarialBco.omega_mix {C : Type*} [Fintype C] [DecidableEq C] (p : C → ℝ) (g : C → Bool → C → ℝ)
    (w : C → ℝ) (f : C → C → ℝ) :
    ∑ y, (w y * ∑ x, g x false y +
        ∑ x, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)) =
      ∑ y, w y * (∑ x, p x * f y x - f y y + ∑ x, ((1 - f y x) * g x false y + f y x * g x true y)) := by
  refine Finset.sum_congr rfl fun y hy => ?_
  have hinner : (∑ x : C, g x false y) + ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * f y x =
      (∑ x : C, p x * f y x) - f y y + ∑ x : C, ((1 - f y x) * g x false y + f y x * g x true y) := by
    have hsum_ite : ∑ x : C, (if x = y then 1 else 0) * f y x = f y y := by
      simp [Finset.sum_ite_eq']
    calc
      (∑ x : C, g x false y) + ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * f y x
          = (∑ x : C, g x false y) + ∑ x : C, (p x * f y x - (if x = y then 1 else 0) * f y x + g x true y * f y x - g x false y * f y x) := by
        refine congrArg (fun t => (∑ x : C, g x false y) + t) ?_
        refine Finset.sum_congr rfl fun x hx => ?_
        ring
      _ = (∑ x : C, g x false y) + (∑ x : C, p x * f y x - ∑ x : C, (if x = y then 1 else 0) * f y x + ∑ x : C, g x true y * f y x - ∑ x : C, g x false y * f y x) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ x : C, g x false y) + (∑ x : C, p x * f y x - f y y + ∑ x : C, g x true y * f y x - ∑ x : C, g x false y * f y x) := by
        rw [hsum_ite]
      _ = (∑ x : C, p x * f y x) - f y y + ((∑ x : C, g x false y) + ∑ x : C, g x true y * f y x - ∑ x : C, g x false y * f y x) := by
        ring
      _ = (∑ x : C, p x * f y x) - f y y + ∑ x : C, (g x false y + g x true y * f y x - g x false y * f y x) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ x : C, p x * f y x) - f y y + ∑ x : C, ((1 - f y x) * g x false y + f y x * g x true y) := by
        refine congrArg (fun t => (∑ x : C, p x * f y x) - f y y + t) ?_
        refine Finset.sum_congr rfl fun x hx => ?_
        ring
  calc
    w y * ∑ x : C, g x false y + ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)
        = w y * (∑ x : C, g x false y) + ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x) := rfl
    _ = w y * (∑ x : C, g x false y) + w y * ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * f y x := by
      simp [Finset.mul_sum, mul_comm, mul_assoc]
    _ = w y * ((∑ x : C, g x false y) + ∑ x : C, (p x - (if x = y then 1 else 0) + g x true y - g x false y) * f y x) := by
      ring
    _ = w y * (∑ x : C, p x * f y x - f y y + ∑ x : C, ((1 - f y x) * g x false y + f y x * g x true y)) := by
      rw [hinner]

theorem AdversarialBco.value_arith (a0 β I η : ℝ) (hβ : 0 ≤ β) (hI : 0 ≤ I) (hη : 0 < η) :
    a0 + √(β * I / 2) - I / η ≤ a0 + η * β / 8 := by
  have hβ2 : 0 ≤ β / 2 := by linarith
  set a := √(β / 2) with ha
  set s := √I with hs
  have ha_sq : a ^ 2 = β / 2 := Real.sq_sqrt hβ2
  have hs_sq : s ^ 2 = I := Real.sq_sqrt hI
  have hsqrt_mul : √(β * I / 2) = a * s := by
    calc
      √(β * I / 2) = √((β / 2) * I) := by ring_nf
      _ = √(β / 2) * √I := Real.sqrt_mul hβ2 I
      _ = a * s := rfl
  have hβ_eq : β = 2 * a ^ 2 := by linarith
  rw [hsqrt_mul, ← hs_sq, hβ_eq]
  -- goal: a0 + a * s - s^2 / η ≤ a0 + η * (2 * a^2) / 8
  have hRHS : η * (2 * a ^ 2) / 8 = η * a ^ 2 / 4 := by ring
  rw [hRHS]
  -- goal: a0 + a * s - s^2 / η ≤ a0 + η * a^2 / 4
  -- cancel a0, then multiply by η > 0
  have h_main : a * s - s ^ 2 / η ≤ η * a ^ 2 / 4 := by
    have h_ineq : a * s * η - s ^ 2 ≤ η ^ 2 * a ^ 2 / 4 := by
      have h_sq_nonneg : (a * η / 2 - s) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith
    calc
      a * s - s ^ 2 / η = (a * s * η - s ^ 2) / η := by
        field_simp [hη.ne.symm]
      _ ≤ (η ^ 2 * a ^ 2 / 4) / η :=
        div_le_div_of_nonneg_right h_ineq (by linarith)
      _ = η * a ^ 2 / 4 := by
        field_simp [hη.ne.symm]
  linarith

theorem AdversarialBco.pinsker_bern (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (h0 : b = 0 → a = 0) (h1 : b = 1 → a = 1) :
    (a - b) ^ 2 ≤ (a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))) / 2 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  by_cases hb0' : b = 0
  · subst hb0'
    have ha0' : a = 0 := h0 rfl
    subst ha0'
    simp
  · have hb0pos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb0')
    by_cases hb1' : b = 1
    · subst hb1'
      have ha1' : a = 1 := h1 rfl
      subst ha1'
      simp
    · have hb1lt : b < 1 := lt_of_le_of_ne hb1 hb1'
      have h := AdversarialBco.kl_bin_ge a b ha0 ha1 hb0pos hb1lt
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      simpa [mul_comm] using h

open MeasureTheory in
/-- `sqrt_V_le` applied to `f / M` and `δ / M`. -/
theorem AdversarialBco.sqrt_V_le_bdd {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ] {k : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (M : ℝ) (hM : 0 < M) (hb : ∀ i x, |f i x| ≤ M) (pr : X → X) (hpr : Measurable pr) (δ : ℝ)
    (hδ : ∀ i x, |f i x - f i (pr x)| ≤ δ) :
    √(∫ x, ∑ i, w i * ((∑ j, w j * f j x) - f i x) ^ 2 ∂ρ) ≤
      √(∫ x, ∑ i, w i * ((∑ j, w j * f j (pr x)) - f i (pr x)) ^ 2 ∂ρ) + δ := by
  have hM0 : M ≠ 0 := hM.ne'
  have key : ∀ g : Fin k → ℝ, ∑ i, w i * ((∑ j, w j * (g j / M)) - g i / M) ^ 2 =
      (∑ i, w i * ((∑ j, w j * g j) - g i) ^ 2) / M ^ 2 := by
    intro g
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, w j * (g j / M) = (∑ j, w j * g j) / M := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm
    rw [this]; field_simp
  have h := AdversarialBco.sqrt_V_le ρ w hw hw1 (fun i x => f i x / M) (fun i => (hf i).div_const M)
    (fun i x => by rw [abs_div, abs_of_pos hM, div_le_one hM]; exact hb i x) pr hpr (δ / M)
    (fun i x => by rw [← sub_div, abs_div, abs_of_pos hM]; exact div_le_div_of_nonneg_right (hδ i x) hM.le)
  simp only [key, integral_div] at h
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by positivity), Real.sqrt_sq hM.le] at h
  rw [← add_div, div_le_div_iff_of_pos_right hM] at h
  exact h

theorem AdversarialBco.log_card_le (m d : ℕ) (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) (hm : 1 ≤ m)
    (hmd : (m : ℝ) ≤ (1 + 4 * D / ε) ^ d) : Real.log m ≤ d * Real.log (1 + 4 * D / ε) := by
  have hm_pos : 0 < (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact mod_cast hm
    linarith
  calc
    Real.log (m : ℝ) ≤ Real.log ((1 + 4 * D / ε) ^ d) := Real.log_le_log hm_pos hmd
    _ = (d : ℝ) * Real.log (1 + 4 * D / ε) := Real.log_pow (1 + 4 * D / ε) d

theorem AdversarialBco.min_le_avg {C : Type*} [Fintype C] [Nonempty C] (a ξ : C → ℝ) (hξ : ∀ x, 0 ≤ ξ x)
    (hξ1 : ∑ x, ξ x = 1) : Finset.univ.inf' Finset.univ_nonempty a ≤ ∑ x, ξ x * a x := by
  set μ := Finset.univ.inf' Finset.univ_nonempty a with hμ
  calc
    μ = (∑ x : C, ξ x) * μ := by rw [hξ1, one_mul]
    _ = ∑ x : C, ξ x * μ := by rw [Finset.sum_mul]
    _ ≤ ∑ x : C, ξ x * a x :=
      Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (Finset.inf'_le a (Finset.mem_univ x)) (hξ x)

set_option maxHeartbeats 400000 in
open MeasureTheory in
theorem AdversarialBco.lemma_H_shift {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (L ε α β : ℝ) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hH : AdversarialBco.HypH J L 0 1 α β) :
    AdversarialBco.HypH J L (-(L * ε)) (1 + L * ε) ((1 + 2 * L * ε) * α) β := by
  set κ := 1 + 2 * L * ε with hκ_def
  have hκ_pos : 0 < κ := by nlinarith
  have hκ_one_le : 1 ≤ κ := by nlinarith
  intro k w F hw_nonneg hw_sum hF
  set T : ℝ → ℝ := fun u => (u + L * ε) / κ with hT_def
  set G : Fin k → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => T (F i x) with hG_def
  have hT_mono : Monotone T := by
    intro a b h
    dsimp [T]
    have h' : a + L * ε ≤ b + L * ε := by linarith
    exact (div_le_div_of_nonneg_right h' (by linarith))
  have hG_convex : ∀ i, ConvexOn ℝ J (G i) := by
    intro i
    rcases hF i with ⟨hF_conv, hF_lip, hF_range⟩
    have h_add : ConvexOn ℝ J (fun x => F i x + (L * ε)) :=
      hF_conv.add_const (L * ε)
    have h_smul : ConvexOn ℝ J (fun x => (1 / κ) * (F i x + (L * ε))) :=
      h_add.smul (by positivity : 0 ≤ (1 : ℝ) / κ)
    simpa [G, T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_smul
  have hG_lip : ∀ i, ∀ x ∈ J, ∀ y ∈ J, |G i x - G i y| ≤ L * dist x y := by
    intro i x hx y hy
    rcases hF i with ⟨hF_conv, hF_lip, hF_range⟩
    have h_lip : |F i x - F i y| ≤ L * dist x y := hF_lip x hx y hy
    dsimp [G, T]
    have h_eq : |(F i x + L * ε) / κ - (F i y + L * ε) / κ| = |F i x - F i y| / κ := by
      rw [← sub_div, abs_div, abs_of_pos hκ_pos]
      congr 1
      ring_nf
    rw [h_eq]
    have h_div_le : |F i x - F i y| / κ ≤ |F i x - F i y| :=
      (div_le_self (abs_nonneg _) hκ_one_le)
    linarith
  have hG_range : ∀ i, ∀ x ∈ J, G i x ∈ Set.Icc (0 : ℝ) 1 := by
    intro i x hx
    rcases hF i with ⟨hF_conv, hF_lip, hF_range⟩
    rcases hF_range x hx with ⟨hlo, hhi⟩
    dsimp [G, T]
    have h0 : 0 ≤ (F i x + L * ε) / κ := by
      have hnum : 0 ≤ F i x + L * ε := by linarith
      exact div_nonneg hnum (by linarith)
    have h1 : (F i x + L * ε) / κ ≤ 1 := by
      have hnum : F i x + L * ε ≤ κ := by dsimp [κ]; linarith
      exact (div_le_one (by linarith)).mpr hnum
    exact ⟨h0, h1⟩
  have hG_cond : ∀ i, ConvexOn ℝ J (G i) ∧ (∀ x ∈ J, ∀ y ∈ J, |G i x - G i y| ≤ L * dist x y) ∧
      ∀ x ∈ J, G i x ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact ⟨hG_convex i, hG_lip i, hG_range i⟩
  rcases hH k w G hw_nonneg hw_sum hG_cond with ⟨ρ, hρ_prob, hρ_supp, hρ_int, hρ_ineq⟩
  have hF_int : ∀ i, Integrable (F i) ρ := by
    intro i
    have h_eq : F i = (fun x => κ * G i x - L * ε) := by
      ext x; dsimp [G, T]; field_simp [hκ_pos.ne']; ring
    rw [h_eq]
    have h_int_G : Integrable (G i) ρ := hρ_int i
    exact ((h_int_G.const_mul κ).sub (integrable_const (L * ε)))
  refine ⟨ρ, hρ_prob, hρ_supp, hF_int, ?_⟩
  -- J is nonempty
  have hJ_nonempty : J.Nonempty := by
    by_contra h_empty
    have h_empty' : J = ∅ := (Set.not_nonempty_iff_eq_empty.mp h_empty)
    let w' : Fin 1 → ℝ := fun _ => 1
    let F' : Fin 1 → EuclideanSpace ℝ (Fin d) → ℝ := fun _ _ => 0
    have hw'_nonneg : ∀ i, 0 ≤ w' i := by intro i; norm_num
    have hw'_sum : ∑ i, w' i = 1 := by simp [w']
    have hF'_cond : ∀ i, ConvexOn ℝ J (F' i) ∧ (∀ x ∈ J, ∀ y ∈ J, |F' i x - F' i y| ≤ L * dist x y) ∧
        ∀ x ∈ J, F' i x ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      rw [h_empty']
      refine ⟨⟨convex_empty, ?_⟩, ?_, ?_⟩
      · intro x hx; simp at hx
      · intro x hx; simp at hx
      · intro x hx; simp at hx
    rcases hH 1 w' F' hw'_nonneg hw'_sum hF'_cond with ⟨ρ', hρ'_prob, hρ'_supp, _, _⟩
    have huniv : ρ' Set.univ = 1 := IsProbabilityMeasure.measure_univ
    have h_supp : ρ' Jᶜ = 0 := hρ'_supp
    rw [h_empty'] at h_supp
    have : ρ' Set.univ = 0 := by simpa using h_supp
    rw [this] at huniv
    exact zero_ne_one huniv
  -- sInf formula for G
  have h_sInf_G : ∀ i, sInf (G i '' J) = (sInf (F i '' J) + L * ε) / κ := by
    intro i
    -- Work with the image set directly
    have hS_nonempty : (F i '' J).Nonempty := by
      rcases hJ_nonempty with ⟨x, hx⟩
      exact ⟨F i x, x, hx, rfl⟩
    have hS_bdd : BddBelow (F i '' J) := by
      refine ⟨-(L * ε), ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rcases hF i with ⟨_, _, hF_range⟩
      rcases hF_range x hx with ⟨hlo, _⟩
      exact hlo
    set m := sInf (F i '' J) with hm_def
    have hm_le : ∀ u ∈ F i '' J, m ≤ u := fun u hu => csInf_le hS_bdd hu
    -- Use the explicit image set
    have hT_bdd_image : BddBelow (T '' (F i '' J)) := by
      rcases hS_bdd with ⟨B, hB⟩
      refine ⟨T B, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hx, rfl⟩
      have hBz : B ≤ F i x := hB (Set.mem_image_of_mem (F i) hx)
      exact hT_mono hBz
    -- Prove sInf (T '' (F i '' J)) = T m
    have h_sInf_eq : sInf (T '' (F i '' J)) = T m := by
      apply le_antisymm
      · -- sInf (T '' (F i '' J)) ≤ T m
        set b := sInf (T '' (F i '' J)) with hb_def
        have hb_lower : ∀ v ∈ T '' (F i '' J), b ≤ v := fun v hv => csInf_le hT_bdd_image hv
        have hb_le_Tu : ∀ u ∈ F i '' J, b ≤ T u := by
          intro u hu
          apply hb_lower (T u)
          exact Set.mem_image_of_mem T hu
        have h_key : κ * b - L * ε ≤ m := by
          apply le_csInf hS_nonempty
          intro u hu
          have hb_le_Tu' : b ≤ T u := hb_le_Tu u hu
          dsimp [T] at hb_le_Tu'
          -- hb_le_Tu': b ≤ (u + L * ε) / κ
          -- Multiply by κ: κ * b ≤ u + L * ε
          have h_mul : κ * b ≤ u + L * ε := by
            calc
              κ * b ≤ κ * ((u + L * ε) / κ) := mul_le_mul_of_nonneg_left hb_le_Tu' (by linarith)
              _ = u + L * ε := by field_simp [hκ_pos.ne']
          linarith
        dsimp [T]
        -- Goal: b ≤ (m + L * ε) / κ
        -- From h_key: κ * b - L * ε ≤ m → κ * b ≤ m + L * ε → b ≤ (m + L * ε) / κ
        have h_mul' : κ * b ≤ m + L * ε := by linarith
        calc
          b = (κ * b) / κ := by field_simp [hκ_pos.ne']
          _ ≤ (m + L * ε) / κ := div_le_div_of_nonneg_right h_mul' (by linarith)
      · -- T m ≤ sInf (T '' (F i '' J))
        apply le_csInf
        · rcases hS_nonempty with ⟨u, hu⟩
          refine ⟨T u, ?_⟩
          exact Set.mem_image_of_mem T hu
        · intro v hv
          rcases hv with ⟨u, hu, rfl⟩
          have hm_le_u : m ≤ u := hm_le u hu
          exact hT_mono hm_le_u
    -- Convert to the goal: G i '' J = T '' (F i '' J)
    have h_image_eq : G i '' J = T '' (F i '' J) := by
      rw [Set.image_image]
    rw [h_image_eq]
    dsimp [T, m]
    rw [h_sInf_eq]
  -- Translate the inequality from hH
  have h_sum_G_eq : (fun x => ∑ i, w i * G i x) = (fun x => (∑ i, w i * F i x + L * ε) / κ) := by
    ext x
    dsimp [G, T]
    calc
      ∑ i, w i * ((F i x + L * ε) / κ) = ∑ i, (w i * (F i x + L * ε)) / κ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i, w i * (F i x + L * ε)) / κ := by rw [Finset.sum_div]
      _ = (∑ i, (w i * F i x + w i * (L * ε))) / κ := by
        refine congrArg (fun t => t / κ) (Finset.sum_congr rfl (fun i _ => ?_))
        ring
      _ = ((∑ i, w i * F i x) + (∑ i, w i * (L * ε))) / κ := by rw [Finset.sum_add_distrib]
      _ = ((∑ i, w i * F i x) + L * ε * (∑ i, w i)) / κ := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
      _ = ((∑ i, w i * F i x) + L * ε * 1) / κ := by rw [hw_sum]
      _ = (∑ i, w i * F i x + L * ε) / κ := by ring
  have h_sq_eq : (fun x => ∑ i, w i * ((∑ j, w j * G j x) - G i x) ^ 2) =
      (fun x => (∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2) / (κ ^ 2)) := by
    ext x
    dsimp [G, T]
    have h1 : (∑ j, w j * ((F j x + L * ε) / κ)) = ((∑ j, w j * F j x) + L * ε) / κ := by
      calc
        (∑ j, w j * ((F j x + L * ε) / κ)) = (∑ j, (w j * (F j x + L * ε)) / κ) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
        _ = (∑ j, w j * (F j x + L * ε)) / κ := by rw [Finset.sum_div]
        _ = (∑ j, (w j * F j x + w j * (L * ε))) / κ := by
          refine congrArg (fun t => t / κ) (Finset.sum_congr rfl (fun j _ => ?_))
          ring
        _ = ((∑ j, w j * F j x) + (∑ j, w j * (L * ε))) / κ := by rw [Finset.sum_add_distrib]
        _ = ((∑ j, w j * F j x) + L * ε * (∑ j, w j)) / κ := by
          simp [Finset.mul_sum, mul_comm, mul_left_comm]
        _ = ((∑ j, w j * F j x) + L * ε * 1) / κ := by rw [hw_sum]
        _ = ((∑ j, w j * F j x) + L * ε) / κ := by ring
    calc
      ∑ i, w i * ((∑ j, w j * ((F j x + L * ε) / κ)) - ((F i x + L * ε) / κ)) ^ 2
          = ∑ i, w i * (((∑ j, w j * F j x + L * ε) / κ) - ((F i x + L * ε) / κ)) ^ 2 := by rw [h1]
      _ = ∑ i, w i * ((∑ j, w j * F j x - F i x) / κ) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = ∑ i, w i * ((∑ j, w j * F j x - F i x) ^ 2 / (κ ^ 2)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i, w i * ((∑ j, w j * F j x - F i x) ^ 2)) / (κ ^ 2) := by
        simp [Finset.sum_div, mul_div_assoc]
  rw [h_sum_G_eq, h_sq_eq] at hρ_ineq
  -- Simplify integrals
  have h_int_sum_G : ∫ x, (∑ i, w i * F i x + L * ε) / κ ∂ρ = (∫ x, (∑ i, w i * F i x + L * ε) ∂ρ) / κ := by
    rw [integral_div]
  have h_int_sq_G : ∫ x, (∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2) / (κ ^ 2) ∂ρ =
      (∫ x, (∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2) ∂ρ) / (κ ^ 2) := by
    rw [integral_div]
  rw [h_int_sum_G, h_int_sq_G] at hρ_ineq
  -- Compute ∫ (∑ w_i F_i + L*ε) dρ
  have h_sum_F_int : Integrable (fun x => ∑ i, w i * F i x) ρ := by
    simpa using integrable_finsetSum (Finset.univ : Finset (Fin k)) (fun i _ => (hF_int i).const_mul (w i))
  have h_int_add : ∫ x, (∑ i, w i * F i x + L * ε) ∂ρ = (∫ x, ∑ i, w i * F i x ∂ρ) + L * ε := by
    rw [integral_add h_sum_F_int (integrable_const _), integral_const]
    have huniv : ρ Set.univ = 1 := hρ_prob.measure_univ
    have hreal : ρ.real Set.univ = (1 : ℝ) := by
      rw [show ρ.real Set.univ = (ρ Set.univ).toReal from rfl, huniv]
      norm_num
    rw [hreal]
    simp
  rw [h_int_add] at hρ_ineq
  -- Rewrite sInf terms
  have h_sInf_sum : ∑ i, w i * sInf (G i '' J) = (∑ i, w i * sInf (F i '' J) + L * ε) / κ := by
    calc
      ∑ i, w i * sInf (G i '' J) = ∑ i, w i * ((sInf (F i '' J) + L * ε) / κ) := by simp_rw [h_sInf_G]
      _ = ∑ i, (w i * (sInf (F i '' J) + L * ε)) / κ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i, w i * (sInf (F i '' J) + L * ε)) / κ := by rw [Finset.sum_div]
      _ = (∑ i, (w i * sInf (F i '' J) + w i * (L * ε))) / κ := by
        refine congrArg (fun t => t / κ) (Finset.sum_congr rfl (fun i _ => ?_))
        ring
      _ = ((∑ i, w i * sInf (F i '' J)) + (∑ i, w i * (L * ε))) / κ := by rw [Finset.sum_add_distrib]
      _ = ((∑ i, w i * sInf (F i '' J)) + L * ε * (∑ i, w i)) / κ := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
      _ = ((∑ i, w i * sInf (F i '' J)) + L * ε * 1) / κ := by rw [hw_sum]
      _ = (∑ i, w i * sInf (F i '' J) + L * ε) / κ := by ring
  rw [h_sInf_sum] at hρ_ineq
  -- Simplify left side
  have h_left_simp : (∫ x, ∑ i, w i * F i x ∂ρ + L * ε) / κ - (∑ i, w i * sInf (F i '' J) + L * ε) / κ =
      ((∫ x, ∑ i, w i * F i x ∂ρ) - ∑ i, w i * sInf (F i '' J)) / κ := by
    ring
  rw [h_left_simp] at hρ_ineq
  -- Simplify right side: √(β * X / κ^2) = √(β * X) / κ
  have h_right_simp : √(β * ((∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ) / (κ ^ 2))) =
      √(β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) / κ := by
    have h_nonneg_int : 0 ≤ ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ :=
      integral_nonneg (fun x => by
        refine Finset.sum_nonneg (fun i _ => ?_)
        have hw_nonneg_i : 0 ≤ w i := hw_nonneg i
        have h_sq_nonneg : 0 ≤ ((∑ j, w j * F j x) - F i x) ^ 2 := pow_two_nonneg _
        nlinarith)
    have h_nonneg : 0 ≤ β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ) := by nlinarith
    calc
      √(β * ((∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ) / (κ ^ 2))) =
          √((β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) / (κ ^ 2)) := by ring
      _ = √(β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) / √(κ ^ 2) := by
        rw [Real.sqrt_div h_nonneg]
      _ = √(β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) / κ := by
        rw [Real.sqrt_sq (by linarith)]
  rw [h_right_simp] at hρ_ineq
  -- Final step: multiply both sides by κ
  -- hρ_ineq: A/κ ≤ α + B/κ  where A = ∫∑ w_i F_i - ∑ w_i sInf, B = √(...)
  -- Goal: A ≤ κ*α + B
  -- Multiply hρ_ineq by κ (positive)
  have h_final : (∫ x, ∑ i, w i * F i x ∂ρ) - ∑ i, w i * sInf (F i '' J) ≤
      κ * α + √(β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) := by
    set A := (∫ x, ∑ i, w i * F i x ∂ρ) - ∑ i, w i * sInf (F i '' J) with hA_def
    set B := √(β * (∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)) with hB_def
    have h_mul : A ≤ κ * α + B := by
      calc
        A = (A / κ) * κ := by field_simp [hκ_pos.ne']
        _ ≤ (α + B / κ) * κ := mul_le_mul_of_nonneg_right hρ_ineq (by linarith)
        _ = α * κ + B := by field_simp [hκ_pos.ne']
        _ = κ * α + B := by ring
    dsimp [A, B] at h_mul
    exact h_mul
  exact h_final

theorem AdversarialBco.sq_le_two_mul_add_sq_pos (x τ : ℝ) (hx : 0 ≤ x) (hτ : 0 ≤ τ) :
    x ^ 2 ≤ 2 * τ * x + max (x - τ) 0 ^ 2 := by
  by_cases h : x ≤ τ
  · -- case x ≤ τ: max (x - τ) 0 = 0, and x^2 ≤ τ*x ≤ 2*τ*x
    have hmax : max (x - τ) 0 = 0 := by
      rw [max_eq_right (sub_nonpos.mpr h)]
    rw [hmax]
    simp
    nlinarith
  · -- case τ < x: max (x - τ) 0 = x - τ, let u = x - τ
    have hmax : max (x - τ) 0 = x - τ := by
      rw [max_eq_left (sub_nonneg.mpr (by linarith))]
    rw [hmax]
    nlinarith

open MeasureTheory Set in
theorem AdversarialBco.integral_sq_le_of_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (G : ℝ → ℝ)
    (hG : ∀ t, 0 < t → μ.real {ω | t ≤ X ω} ≤ G t)
    (hGint : IntegrableOn (fun t => 2 * t * G t) (Set.Ioi 0)) :
    ∫ ω, X ω ^ 2 ∂μ ≤ ∫ t in Set.Ioi 0, 2 * t * G t := by
  by_cases h_int : Integrable (fun ω => X ω ^ 2) μ
  · -- integrable case: use layer cake formula and change of variables
    have h_nn : 0 ≤ᵐ[μ] (fun ω => X ω ^ 2) := by
      filter_upwards with ω using pow_nonneg (hX0 ω) 2
    have h_layer := h_int.integral_eq_integral_meas_le h_nn
    -- h_layer: ∫ ω, X ω ^ 2 ∂μ = ∫ t in Set.Ioi 0, μ.real {a | t ≤ X a ^ 2}

    -- Change of variables: ∫_{t>0} μ.real {t ≤ X^2} = ∫_{t>0} 2*t * μ.real {t ≤ X}
    have h_change : ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t ≤ X ω ^ 2} =
                  ∫ t in Set.Ioi (0 : ℝ), 2 * t * μ.real {ω | t ≤ X ω} := by
      have hp : 0 < (2 : ℝ) := by norm_num
      have h_eq := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => μ.real {ω | y ≤ X ω ^ 2}) hp
      -- h_eq: ∫ x in Ioi 0, (2*x) • μ.real {x^2 ≤ X^2} = ∫ y in Ioi 0, μ.real {y ≤ X^2}
      have h_set (x : ℝ) (hx : 0 < x) : μ.real {ω | x ^ 2 ≤ (X ω) ^ 2} = μ.real {ω | x ≤ X ω} := by
        have h_set_eq : {ω | x ^ 2 ≤ (X ω) ^ 2} = {ω | x ≤ X ω} := by
          ext ω; simp [sq]
          constructor
          · intro h; exact (mul_self_le_mul_self_iff (le_of_lt hx) (hX0 ω)).mpr h
          · intro h; exact (mul_self_le_mul_self_iff (le_of_lt hx) (hX0 ω)).mp h
        rw [h_set_eq]
      calc
        ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | t ≤ X ω ^ 2} =
            ∫ t in Set.Ioi (0 : ℝ), (2 * t) * μ.real {ω | t ^ 2 ≤ (X ω) ^ 2} := by
          rw [← h_eq]
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          have ht_pos : 0 < t := ht
          simp [h_set t ht_pos, show ((2 : ℝ) - 1 : ℝ) = (1 : ℝ) by norm_num]
        _ = ∫ t in Set.Ioi (0 : ℝ), 2 * t * μ.real {ω | t ≤ X ω} := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          have ht_pos : 0 < t := ht
          simp [h_set t ht_pos]

    rw [h_layer, h_change]

    -- Now need: ∫ t in Ioi 0, 2*t * μ.real {t ≤ X} ≤ ∫ t in Ioi 0, 2*t * G t
    have h_int_left : IntegrableOn (fun t => 2 * t * μ.real {ω | t ≤ X ω}) (Set.Ioi (0 : ℝ)) := by
      have h_dom : IntegrableOn (fun t => 2 * t * G t) (Set.Ioi (0 : ℝ)) := hGint
      have h_meas_ae : AEStronglyMeasurable (fun t : ℝ => 2 * t * μ.real {ω | t ≤ X ω})
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have h_meas_μ : Measurable (fun t : ℝ => μ.real {ω | t ≤ X ω}) := by
          refine Measurable.ennreal_toReal ?_
          refine Antitone.measurable (fun t₁ t₂ h => ?_)
          refine measure_mono (fun a ha => ?_)
          exact le_trans h ha
        have h_cont : Continuous (fun t : ℝ => 2 * t) := by continuity
        have h_meas_prod : Measurable (fun t : ℝ => 2 * t * μ.real {ω | t ≤ X ω}) :=
          h_cont.measurable.mul h_meas_μ
        exact h_meas_prod.aestronglyMeasurable
      have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          ‖2 * t * μ.real {ω | t ≤ X ω}‖ ≤ 2 * t * G t := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := ht
        have hμ_nonneg : 0 ≤ μ.real {ω | t ≤ X ω} := measureReal_nonneg
        have hG_bound : μ.real {ω | t ≤ X ω} ≤ G t := hG t ht_pos
        have h_nonneg_prod : 0 ≤ 2 * t * μ.real {ω | t ≤ X ω} := by nlinarith
        have h_abs : ‖2 * t * μ.real {ω | t ≤ X ω}‖ = 2 * t * μ.real {ω | t ≤ X ω} := by
          rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_prod]
        rw [h_abs]
        nlinarith
      exact h_dom.mono' h_meas_ae h_bound

    have h_meas_set : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
    have h_pointwise : ∀ t ∈ Set.Ioi (0 : ℝ), 2 * t * μ.real {ω | t ≤ X ω} ≤ 2 * t * G t := by
      intro t ht
      have ht_pos : 0 < t := ht
      have hμ_nonneg : 0 ≤ μ.real {ω | t ≤ X ω} := measureReal_nonneg
      have hG_bound : μ.real {ω | t ≤ X ω} ≤ G t := hG t ht_pos
      nlinarith

    exact setIntegral_mono_on h_int_left hGint h_meas_set h_pointwise

  · -- non-integrable case: LHS = 0, RHS ≥ 0
    have h_left : ∫ ω, X ω ^ 2 ∂μ = 0 := integral_undef h_int
    have h_right : 0 ≤ ∫ t in Set.Ioi 0, 2 * t * G t := by
      refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
      have ht_pos : 0 < t := ht
      have hG_nonneg : 0 ≤ G t := by
        have hμ_nonneg : 0 ≤ μ.real {ω | t ≤ X ω} := measureReal_nonneg
        have h_bound := hG t ht_pos
        linarith
      nlinarith
    linarith

open MeasureTheory Set Real in
theorem AdversarialBco.gauss_tail_integral_le (s r0 : ℝ) (hs : 0 < s) (hr0 : 0 ≤ r0) :
    IntegrableOn (fun t => 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2))) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) ≤
        2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by
  have hs_sq_pos : 0 < s ^ 2 := pow_pos hs 2
  have h_denom_pos : 0 < 2 * s ^ 2 := by nlinarith
  have hb_pos : 0 < (1 : ℝ) / (2 * s ^ 2) := div_pos (by norm_num) h_denom_pos
  have h_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  -- key inequality: (r0 + t)^2 ≥ r0^2 + t^2 for t ≥ 0, r0 ≥ 0
  have h_sq_ineq : ∀ t, 0 ≤ t → (r0 + t) ^ 2 ≥ r0 ^ 2 + t ^ 2 := by
    intro t ht
    nlinarith
  -- pointwise bound
  have h_bound : ∀ t, t ∈ Set.Ioi (0 : ℝ) →
      2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) ≤
      (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) * (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
    intro t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht
    have h_sq : (r0 + t) ^ 2 ≥ r0 ^ 2 + t ^ 2 := h_sq_ineq t ht_nonneg
    have h_div : -(r0 + t) ^ 2 / (2 * s ^ 2) ≤ -(r0 ^ 2 + t ^ 2) / (2 * s ^ 2) := by
      have h_neg : -(r0 + t) ^ 2 ≤ -(r0 ^ 2 + t ^ 2) := by linarith
      exact div_le_div_of_nonneg_right h_neg (by nlinarith)
    have h_exp : Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) ≤ Real.exp (-(r0 ^ 2 + t ^ 2) / (2 * s ^ 2)) :=
      Real.exp_le_exp.mpr h_div
    have h_exp_add : Real.exp (-(r0 ^ 2 + t ^ 2) / (2 * s ^ 2)) =
        Real.exp (-r0 ^ 2 / (2 * s ^ 2)) * Real.exp (-(t ^ 2) / (2 * s ^ 2)) := by
      calc
        Real.exp (-(r0 ^ 2 + t ^ 2) / (2 * s ^ 2)) =
            Real.exp ((-r0 ^ 2) / (2 * s ^ 2) + (-(t ^ 2)) / (2 * s ^ 2)) := by ring
        _ = Real.exp ((-r0 ^ 2) / (2 * s ^ 2)) * Real.exp ((-(t ^ 2)) / (2 * s ^ 2)) := by
          rw [Real.exp_add]
        _ = Real.exp (-r0 ^ 2 / (2 * s ^ 2)) * Real.exp (-(t ^ 2) / (2 * s ^ 2)) := by ring
    calc
      2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) ≤
          2 * t * Real.exp (-(r0 ^ 2 + t ^ 2) / (2 * s ^ 2)) := by
        nlinarith
      _ = 2 * t * (Real.exp (-r0 ^ 2 / (2 * s ^ 2)) * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
        rw [h_exp_add]
      _ = (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) * (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by ring
  -- integrability of the comparison function on Ioi 0
  have h_int_comp : IntegrableOn (fun t => t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) (Set.Ioi 0) := by
    have h_int : Integrable (fun t : ℝ => t * Real.exp (-((1 : ℝ) / (2 * s ^ 2)) * t ^ 2)) :=
      integrable_mul_exp_neg_mul_sq hb_pos
    have h_eq : (fun t : ℝ => t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) =
        (fun t : ℝ => t * Real.exp (-((1 : ℝ) / (2 * s ^ 2)) * t ^ 2)) := by
      ext t
      congr 1
      ring
    rw [h_eq]
    exact h_int.integrableOn
  -- integrability of the comparison function on Ioi 0 (scaled)
  have h_int_comp_scaled : IntegrableOn (fun t => (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
      (t * Real.exp (-(t ^ 2) / (2 * s ^ 2)))) (Set.Ioi 0) := by
    -- IntegrableOn is Integrable on the restricted measure
    -- Integrable is an And type, so we use Integrable.smul
    have h_int : Integrable (fun t : ℝ => t * Real.exp (-(t ^ 2) / (2 * s ^ 2)))
        (volume.restrict (Set.Ioi 0)) := h_int_comp
    have h_smul : Integrable (fun t : ℝ => (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
        (t * Real.exp (-(t ^ 2) / (2 * s ^ 2)))) (volume.restrict (Set.Ioi 0)) :=
      h_int.smul (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)))
    exact h_smul
  -- integrability of the target function
  have h_int_target : IntegrableOn (fun t => 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)))
      (Set.Ioi 0) := by
    have h_meas_target : AEStronglyMeasurable (fun t => 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)))
        (volume.restrict (Set.Ioi 0)) := by
      have h_cont : Continuous (fun t : ℝ => 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2))) := by
        continuity
      exact h_cont.aestronglyMeasurable
    -- Use Integrable.mono' which expects ‖target‖ ≤ comparison (real-valued)
    -- Both target and comparison are nonnegative, so norms are the values themselves
    have h_norm_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
        ‖2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2))‖ ≤
        (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) * (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
      filter_upwards [ae_restrict_mem h_meas] with t ht
      have ht_pos : 0 < t := ht
      have h_nonneg : 0 ≤ 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) := by
        positivity
      have h_comp_nonneg : 0 ≤ (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
          (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
        positivity
      have h_bound' := h_bound t ht_pos
      -- h_bound' : target ≤ comparison
      -- we need ‖target‖ ≤ comparison
      -- since target ≥ 0, ‖target‖ = target
      have h_norm_target : ‖2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2))‖ =
          2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) :=
        Real.norm_of_nonneg h_nonneg
      rw [h_norm_target]
      exact h_bound'
    exact h_int_comp_scaled.mono' h_meas_target h_norm_bound
  -- the integral inequality
  have h_int_ineq : ∫ t in Set.Ioi 0, 2 * t * Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) ≤
      ∫ t in Set.Ioi 0, (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
        (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
    refine setIntegral_mono_on h_int_target h_int_comp_scaled h_meas (fun t ht => h_bound t ht)
  -- compute the RHS integral using the dependency lemma
  have h_int_rhs : ∫ t in Set.Ioi 0, (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
      (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) = 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by
    calc
      ∫ t in Set.Ioi 0, (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
          (t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) =
          (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) *
          (∫ t in Set.Ioi 0, t * Real.exp (-(t ^ 2) / (2 * s ^ 2))) := by
        rw [integral_const_mul]
      _ = (2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))) * (s ^ 2) := by
        rw [AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_sq s hs]
      _ = 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by ring
  -- combine
  rw [h_int_rhs] at h_int_ineq
  exact And.intro h_int_target h_int_ineq

/-- from `sq_le_two_mul_add_sq_pos`, `integral_sq_le_of_tail_bound` and
`gauss_tail_integral_le`. -/
theorem AdversarialBco.integral_sq_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδm : Measurable δ) (hδ0 : ∀ ω, 0 ≤ δ ω) (hint : Integrable δ μ)
    (m s r0 : ℝ) (hm : ∫ ω, δ ω ∂μ ≤ m) (hs : 0 < s) (hr0 : 0 ≤ r0)
    (htail : ∀ r, 0 ≤ r → μ.real {ω | m + r ≤ δ ω} ≤ Real.exp (-r ^ 2 / (2 * s ^ 2))) :
    ∫ ω, δ ω ^ 2 ∂μ ≤ 2 * (m + r0) * m + 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by
  have hm0 : 0 ≤ m := le_trans (integral_nonneg hδ0) hm
  have hτ : 0 ≤ m + r0 := by linarith
  have hE : 0 ≤ 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by positivity
  by_cases hsq : Integrable (fun ω => δ ω ^ 2) μ
  swap
  · rw [integral_undef hsq]; nlinarith
  set X : Ω → ℝ := fun ω => max (δ ω - (m + r0)) 0 with hXdef
  have hXm : Measurable X := (hδm.sub_const _).max measurable_const
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_right _ _
  have hXle : ∀ ω, X ω ≤ δ ω := fun ω => max_le (by linarith) (hδ0 ω)
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := by
    refine hsq.mono' (hXm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (hX0 ω) (hXle ω) 2
  obtain ⟨hGi, hGle⟩ := AdversarialBco.gauss_tail_integral_le s r0 hs hr0
  have hXt : ∀ t, 0 < t → μ.real {ω | t ≤ X ω} ≤ Real.exp (-(r0 + t) ^ 2 / (2 * s ^ 2)) := by
    intro t ht
    have hset : {ω | t ≤ X ω} = {ω | m + (r0 + t) ≤ δ ω} := by
      ext ω; simp only [Set.mem_ofPred_eq, hXdef]
      constructor
      · intro h; rcases le_max_iff.mp h with h | h <;> linarith
      · intro h; exact le_max_of_le_left (by linarith)
    rw [hset]; exact htail _ (by linarith)
  have hX2le := AdversarialBco.integral_sq_le_of_tail_bound μ X hXm hX0 _ hXt hGi
  have hpt : ∀ ω, δ ω ^ 2 ≤ 2 * (m + r0) * δ ω + X ω ^ 2 :=
    fun ω => AdversarialBco.sq_le_two_mul_add_sq_pos (δ ω) (m + r0) (hδ0 ω) hτ
  have h1 : ∫ ω, δ ω ^ 2 ∂μ ≤ ∫ ω, (2 * (m + r0) * δ ω + X ω ^ 2) ∂μ :=
    integral_mono hsq ((hint.const_mul _).add hX2) hpt
  rw [integral_add (hint.const_mul _) hX2, integral_const_mul] at h1
  have h2 : 2 * (m + r0) * ∫ ω, δ ω ∂μ ≤ 2 * (m + r0) * m := mul_le_mul_of_nonneg_left hm (by linarith)
  linarith

open MeasureTheory in
theorem AdversarialBco.convexOn_convolution {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (hint : ∀ x, Integrable (fun y => F (x - y) * φ y)) :
    ConvexOn ℝ Set.univ (fun x => ∫ y, F (x - y) * φ y) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp at hx hy
  have hkey : ∀ z, (a • x + b • y) - z = a • (x - z) + b • (y - z) := by
    intro z
    calc
      (a • x + b • y) - z = (a • x + b • y) - (a + b) • z := by simp [hab]
      _ = (a • x + b • y) - (a • z + b • z) := by simp [add_smul]
      _ = (a • x - a • z) + (b • y - b • z) := by abel
      _ = a • (x - z) + b • (y - z) := by simp [smul_sub]
  have hpointwise : ∀ z, F ((a • x + b • y) - z) * φ z ≤ (a • F (x - z) + b • F (y - z)) * φ z := by
    intro z
    rw [hkey z]
    have hF_convex := hF.2 (Set.mem_univ (x - z)) (Set.mem_univ (y - z)) ha hb hab
    have h_nonneg := hφ z
    have h_mul := mul_le_mul_of_nonneg_right hF_convex h_nonneg
    exact h_mul
  have hleft_int : Integrable (fun z => F ((a • x + b • y) - z) * φ z) volume := hint (a • x + b • y)
  have hright_int : Integrable (fun z => (a • F (x - z) + b • F (y - z)) * φ z) volume := by
    have h1 : Integrable (fun z => F (x - z) * φ z) volume := hint x
    have h2 : Integrable (fun z => F (y - z) * φ z) volume := hint y
    have h1' : Integrable (fun z => a • (F (x - z) * φ z)) volume := (h1.smul a)
    have h2' : Integrable (fun z => b • (F (y - z) * φ z)) volume := (h2.smul b)
    have hsum : Integrable (fun z => a • (F (x - z) * φ z) + b • (F (y - z) * φ z)) volume :=
      h1'.add h2'
    simpa [smul_eq_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hright_int' : Integrable (fun z => a • (F (x - z) * φ z)) volume := (hint x).smul a
  have hright_int'' : Integrable (fun z => b • (F (y - z) * φ z)) volume := (hint y).smul b
  calc
    (∫ z, F ((a • x + b • y) - z) * φ z) ≤ (∫ z, (a • F (x - z) + b • F (y - z)) * φ z) :=
      integral_mono hleft_int hright_int hpointwise
    _ = (∫ z, a • (F (x - z) * φ z) + b • (F (y - z) * φ z)) := by
      refine integral_congr_ae ?_
      filter_upwards with z
      ring
    _ = (∫ z, a • (F (x - z) * φ z)) + (∫ z, b • (F (y - z) * φ z)) :=
      integral_add hright_int' hright_int''
    _ = a • (∫ z, F (x - z) * φ z) + b • (∫ z, F (y - z) * φ z) := by
      rw [integral_smul, integral_smul]

open MeasureTheory in
theorem AdversarialBco.norm_add_symm_ge {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun w => -w) = μ) (hint : Integrable (fun w => ‖w‖) μ) (b : EuclideanSpace ℝ (Fin d)) :
    ‖b‖ ≤ ∫ w, ‖b + w‖ ∂μ ∧ ∫ w, ‖w‖ ∂μ ≤ ∫ w, ‖b + w‖ ∂μ := by
  have hae_meas_add : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b + w‖) μ :=
    ((continuous_const.add continuous_id).norm).aestronglyMeasurable
  have hae_meas_sub : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b - w‖) μ :=
    ((continuous_const.sub continuous_id).norm).aestronglyMeasurable
  have hmeas_neg : AEMeasurable (fun w : EuclideanSpace ℝ (Fin d) => -w) μ :=
    (measurable_neg.comp measurable_id).aemeasurable
  have hae_meas_add_mapped : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b + w‖)
      (μ.map (fun w => -w)) :=
    ((continuous_const.add continuous_id).norm).aestronglyMeasurable
  have hint_add : Integrable (fun w => ‖b + w‖) μ := by
    have h_bound : ∀ᵐ w ∂μ, ‖(fun w => ‖b + w‖) w‖ ≤ (fun w => ‖b‖ + ‖w‖) w := by
      filter_upwards [] with w
      simp [norm_add_le]
    have h_int : Integrable (fun w => ‖b‖ + ‖w‖) μ :=
      (integrable_const (‖b‖)).add hint
    exact h_int.mono' hae_meas_add h_bound
  have h_symm_int : ∫ w, ‖b - w‖ ∂μ = ∫ w, ‖b + w‖ ∂μ := by
    calc
      ∫ w, ‖b - w‖ ∂μ = ∫ w, ‖b + (-w)‖ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with w
        simp [sub_eq_add_neg]
      _ = ∫ w, ‖b + w‖ ∂(μ.map (fun w => -w)) := by
        rw [integral_map hmeas_neg hae_meas_add_mapped]
      _ = ∫ w, ‖b + w‖ ∂μ := by rw [hsym]
  have h_int_neg : Integrable (fun w => ‖b - w‖) μ := by
    have h_bound : ∀ᵐ w ∂μ, ‖(fun w => ‖b - w‖) w‖ ≤ (fun w => ‖b‖ + ‖w‖) w := by
      filter_upwards [] with w
      simp [norm_sub_le]
    have h_int : Integrable (fun w => ‖b‖ + ‖w‖) μ :=
      (integrable_const (‖b‖)).add hint
    exact h_int.mono' hae_meas_sub h_bound
  have h_sum_eq : ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ = 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ = (∫ w, ‖b + w‖ ∂μ) + (∫ w, ‖b - w‖ ∂μ) :=
        integral_add hint_add h_int_neg
      _ = (∫ w, ‖b + w‖ ∂μ) + (∫ w, ‖b + w‖ ∂μ) := by rw [h_symm_int]
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by ring
  have h_pointwise_b : ∀ w, 2 * ‖b‖ ≤ ‖b + w‖ + ‖b - w‖ := by
    intro w
    calc
      2 * ‖b‖ = ‖(2 : ℝ) • b‖ := by
        simp [norm_smul]
      _ = ‖(b + w) + (b - w)‖ := by
        have h : (2 : ℝ) • b = (b + w) + (b - w) := by
          simp [two_smul, add_left_comm, add_assoc, sub_eq_add_neg]
        rw [h]
      _ ≤ ‖b + w‖ + ‖b - w‖ := norm_add_le _ _
  have h_pointwise_w : ∀ w, 2 * ‖w‖ ≤ ‖b + w‖ + ‖b - w‖ := by
    intro w
    calc
      2 * ‖w‖ = ‖(2 : ℝ) • w‖ := by
        simp [norm_smul]
      _ = ‖(b + w) - (b - w)‖ := by
        have h : (2 : ℝ) • w = (b + w) - (b - w) := by
          simp [two_smul, add_left_comm, add_assoc, sub_eq_add_neg]
        rw [h]
      _ ≤ ‖b + w‖ + ‖b - w‖ := norm_sub_le _ _
  have h_int_b : 2 * ‖b‖ ≤ 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      2 * ‖b‖ = ∫ w, (2 * ‖b‖) ∂μ := by simp [integral_const]
      _ ≤ ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ :=
        integral_mono (integrable_const _) (hint_add.add h_int_neg) h_pointwise_b
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by rw [h_sum_eq]
  have h_int_w : 2 * (∫ w, ‖w‖ ∂μ) ≤ 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      2 * (∫ w, ‖w‖ ∂μ) = ∫ w, (2 * ‖w‖) ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ :=
        integral_mono (hint.const_mul 2) (hint_add.add h_int_neg) h_pointwise_w
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by rw [h_sum_eq]
  constructor
  · linarith
  · linarith

theorem AdversarialBco.bounded_of_linear_le_log (a l C : ℝ) (ha : 0 < a) (hl : 0 ≤ l) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → a * s - l * max (Real.log s) 0 ≤ C → s ≤ M := by
  set K := max 1 (2 * l / a) with hKdef
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    have hKge1 : 1 ≤ K := le_max_left _ _
    linarith
  have hK_one : (1 : ℝ) ≤ K := le_max_left _ _
  have hK_2l_div_a : 2 * l / a ≤ K := le_max_right _ _
  have h_two_l_le_aK : 2 * l ≤ a * K := by
    calc
      2 * l = (2 * l / a) * a := by field_simp [ha.ne']
      _ ≤ K * a := by nlinarith
      _ = a * K := by ring
  have h_log_bound : ∀ s : ℝ, 0 < s → Real.log s ≤ Real.log K + s / K := by
    intro s hs
    have hsK : 0 < s / K := div_pos hs hKpos
    have hlog_div : Real.log (s / K) ≤ (s / K) - 1 := Real.log_le_sub_one_of_pos hsK
    calc
      Real.log s = Real.log (K * (s / K)) := by field_simp [hKpos.ne']
      _ = Real.log K + Real.log (s / K) := by rw [Real.log_mul hKpos.ne' hsK.ne']
      _ ≤ Real.log K + ((s / K) - 1) := by nlinarith
      _ = Real.log K + s / K - 1 := by ring
      _ ≤ Real.log K + s / K := by nlinarith
  have h_ineq : ∀ s : ℝ, 0 ≤ s → l * s / K ≤ a * s / 2 := by
    intro s hs
    have h_two_l_s_le_a_K_s : 2 * l * s ≤ a * K * s := by
      nlinarith
    have h_nonneg_2K : 0 ≤ 2 * K := by nlinarith
    calc
      l * s / K = (2 * l * s) / (2 * K) := by ring
      _ ≤ (a * K * s) / (2 * K) := div_le_div_of_nonneg_right h_two_l_s_le_a_K_s h_nonneg_2K
      _ = a * s / 2 := by field_simp [hKpos.ne']
  set M := 2 * (|C| + l * |Real.log K|) / a with hMdef
  have hM_nonneg : 0 ≤ M := by
    have hnum : 0 ≤ 2 * (|C| + l * |Real.log K|) := by
      have h1 : 0 ≤ |C| := abs_nonneg _
      have h2 : 0 ≤ |Real.log K| := abs_nonneg _
      nlinarith
    have ha' : 0 ≤ a := by linarith
    exact div_nonneg hnum ha'
  refine ⟨M, λ s hs hle => ?_⟩
  by_cases hs0 : s = 0
  · rw [hs0]
    exact hM_nonneg
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hlog : Real.log s ≤ 0
    · -- max (Real.log s) 0 = 0
      have hmax : max (Real.log s) 0 = 0 := max_eq_right hlog
      rw [hmax] at hle
      have hle' : a * s ≤ C := by linarith
      have hs_le_C_div_a : s ≤ C / a := by
        calc
          s = (a * s) / a := by field_simp [ha.ne']
          _ ≤ C / a := div_le_div_of_nonneg_right hle' (by linarith)
      have hC_le_absC : C ≤ |C| := by
        by_cases hC : 0 ≤ C
        · rw [abs_of_nonneg hC]
        · rw [abs_of_nonpos (by linarith)]
          linarith
      have h_div_le_M : C / a ≤ M := by
        calc
          C / a ≤ |C| / a := div_le_div_of_nonneg_right hC_le_absC (by linarith)
          _ ≤ 2 * (|C| + l * |Real.log K|) / a := by
            refine div_le_div_of_nonneg_right ?_ (by linarith)
            nlinarith [abs_nonneg (Real.log K), hl]
          _ = M := by rw [hMdef]
      linarith
    · -- Real.log s > 0, so max (Real.log s) 0 = Real.log s
      have hmax : max (Real.log s) 0 = Real.log s := max_eq_left (by linarith)
      rw [hmax] at hle
      have hlogK_nonneg : 0 ≤ Real.log K := Real.log_nonneg hK_one
      have h_logK_abs : Real.log K = |Real.log K| := by
        rw [abs_of_nonneg hlogK_nonneg]
      have h_ineq' : l * Real.log s ≤ l * Real.log K + a * s / 2 := by
        calc
          l * Real.log s ≤ l * (Real.log K + s / K) := by
            nlinarith [h_log_bound s hs_pos]
          _ = l * Real.log K + l * s / K := by ring
          _ ≤ l * Real.log K + a * s / 2 := by
            nlinarith [h_ineq s hs]
      have h_key : a * s / 2 ≤ C + l * Real.log K := by
        linarith
      have hC_plus_logK_le : C + l * Real.log K ≤ |C| + l * |Real.log K| := by
        have hC_le_absC : C ≤ |C| := by
          by_cases hC : 0 ≤ C
          · rw [abs_of_nonneg hC]
          · rw [abs_of_nonpos (by linarith)]
            linarith
        nlinarith
      have hpos_2diva : 0 ≤ 2 / a := div_nonneg (by norm_num) (by linarith)
      have h_mul1 : (a * s / 2) * (2 / a) ≤ (C + l * Real.log K) * (2 / a) :=
        mul_le_mul_of_nonneg_right h_key hpos_2diva
      have h_mul2 : (C + l * Real.log K) * (2 / a) ≤ (|C| + l * |Real.log K|) * (2 / a) :=
        mul_le_mul_of_nonneg_right hC_plus_logK_le hpos_2diva
      calc
        s = (a * s / 2) * (2 / a) := by field_simp [ha.ne']
        _ ≤ (C + l * Real.log K) * (2 / a) := h_mul1
        _ ≤ (|C| + l * |Real.log K|) * (2 / a) := h_mul2
        _ = 2 * (|C| + l * |Real.log K|) / a := by ring
        _ = M := by rw [hMdef]

theorem AdversarialBco.exists_min_of_compact_sublevel {X : Type*} [TopologicalSpace X] (U : Set X) (f : X → ℝ)
    (hf : ContinuousOn f U) (x0 : X) (hx0 : x0 ∈ U) (hK : IsCompact {x | x ∈ U ∧ f x ≤ f x0}) :
    ∃ x ∈ U, ∀ y ∈ U, f x ≤ f y := by
  set K := {x | x ∈ U ∧ f x ≤ f x0} with hKdef
  have hx0K : x0 ∈ K := by
    dsimp [K]
    exact ⟨hx0, le_refl _⟩
  have hK_nonempty : K.Nonempty := ⟨x0, hx0K⟩
  have hK_sub_U : K ⊆ U := by
    intro x hx
    rcases hx with ⟨hxU, _⟩
    exact hxU
  have hfK : ContinuousOn f K :=
    hf.mono hK_sub_U
  rcases IsCompact.exists_isMinOn hK hK_nonempty hfK with ⟨x, hxK, hx_min⟩
  refine ⟨x, hxK.1, ?_⟩
  intro y hy
  by_cases h : f y ≤ f x0
  · have hyK : y ∈ K := ⟨hy, h⟩
    exact hx_min hyK
  · have hfx : f x ≤ f x0 := hxK.2
    linarith

open MeasureTheory in
/-- The history after `t + 1` rounds is `h` iff the history after `t` rounds is `Fin.init h` and the last draw is `h (Fin.last t)`. -/
theorem AdversarialBco.seqHist_succ_eq_iff {T X : Type*} (σ : (t : ℕ) → (Fin t → T) → X → T) (t : ℕ) (ω : Fin (t+1) → X) (h : Fin (t+1) → T) :
  (AdversarialBco.seqHist σ (t+1) ω = h) ↔
  (AdversarialBco.seqHist σ t (Fin.init ω) = Fin.init h ∧ σ t (Fin.init h) (ω (Fin.last t)) = h (Fin.last t)) := by
  have h_snoc : h = Fin.snoc (Fin.init h) (h (Fin.last t)) := by
    ext i
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc]
    | cast i => simp [Fin.snoc_castSucc, Fin.init]
  constructor
  · intro h_eq
    have h_eq_snoc : AdversarialBco.seqHist σ (t+1) ω = Fin.snoc (Fin.init h) (h (Fin.last t)) := by
      rwa [h_snoc] at h_eq
    unfold AdversarialBco.seqHist at h_eq_snoc
    rcases (Fin.snoc_inj.mp h_eq_snoc) with ⟨h_init, h_last⟩
    refine ⟨h_init, ?_⟩
    rw [h_init] at h_last
    exact h_last
  · intro ⟨h_init, h_last⟩
    unfold AdversarialBco.seqHist
    rw [h_init]
    rw [h_last]
    rw [← h_snoc]

open MeasureTheory in
theorem AdversarialBco.measurableSet_seqHist {T X : Type*} [MeasurableSpace X] (σ : (t : ℕ) → (Fin t → T) → X → T)
    (hσ : ∀ t h τ, MeasurableSet (σ t h ⁻¹' {τ})) (t : ℕ) (h : Fin t → T) :
    MeasurableSet {ω : Fin t → X | AdversarialBco.seqHist σ t ω = h} := by
  induction' t with t ih
  · -- t = 0: Fin 0 → X is a subsingleton
    have : {ω : Fin 0 → X | AdversarialBco.seqHist σ 0 ω = h} = Set.univ := by
      ext ω
      simp [AdversarialBco.seqHist]
      exact Subsingleton.elim _ _
    rw [this]
    exact MeasurableSet.univ
  · -- t = t.succ
    have h_set_eq : {ω : Fin (t+1) → X | AdversarialBco.seqHist σ (t+1) ω = h} =
        {ω : Fin (t+1) → X | AdversarialBco.seqHist σ t (Fin.init ω) = Fin.init h} ∩
        {ω : Fin (t+1) → X | σ t (Fin.init h) (ω (Fin.last t)) = h (Fin.last t)} := by
      ext ω; simp [AdversarialBco.seqHist_succ_eq_iff σ t ω h]
    rw [h_set_eq]
    apply MeasurableSet.inter
    · -- First set: preimage under Fin.init
      have h_meas_init : Measurable (Fin.init : (Fin (t+1) → X) → (Fin t → X)) := by
        apply measurable_pi_lambda
        intro i
        simpa [Fin.init] using measurable_pi_apply (i.castSucc : Fin (t+1))
      have h_meas_target : MeasurableSet {ω' : Fin t → X | AdversarialBco.seqHist σ t ω' = Fin.init h} := ih (Fin.init h)
      -- The set is Fin.init ⁻¹' {ω' | seqHist σ t ω' = Fin.init h}
      exact h_meas_init h_meas_target
    · -- Second set: preimage under evaluation at Fin.last t
      have h_meas_eval : Measurable (fun (ω : Fin (t+1) → X) => ω (Fin.last t)) :=
        measurable_pi_apply (Fin.last t)
      have h_meas_target : MeasurableSet {x : X | σ t (Fin.init h) x = h (Fin.last t)} :=
        hσ t (Fin.init h) (h (Fin.last t))
      exact h_meas_eval h_meas_target

/-- A step of Lemma 7.9: the integral of a function of a map with finitely
many values and measurable fibres is the sum over the fibres. -/
theorem AdversarialBco.integral_comp_finite {X C : Type*} [Fintype C] [MeasurableSpace X] (ρ : Measure X)
    [IsFiniteMeasure ρ] (pr : X → C) (hpr : ∀ x, MeasurableSet (pr ⁻¹' {x})) (g : C → ℝ) :
    ∫ z, g (pr z) ∂ρ = ∑ x, ρ.real (pr ⁻¹' {x}) * g x := by
  classical
  have h : (fun z => g (pr z)) = fun z => ∑ x, (pr ⁻¹' {x}).indicator (fun _ => g x) z := by
    funext z
    rw [Finset.sum_eq_single (pr z)]
    · simp [Set.indicator]
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · simp
  rw [h, integral_finsetSum _ (fun x _ => (integrable_const (g x)).indicator (hpr x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_indicator_const _ (hpr x), smul_eq_mul]

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.pi_real_init_last {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (t : ℕ) (A : Set (Fin t → X)) (hA : MeasurableSet A) (B : Set X) (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin (t + 1) => ν).real {ω | Fin.init ω ∈ A ∧ ω (Fin.last t) ∈ B} =
      (Measure.pi fun _ : Fin t => ν).real A * ν.real B := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => X) (Fin.last t)
  have h_set_eq : {ω | (Fin.init ω : Fin t → X) ∈ A ∧ (ω (Fin.last t) : X) ∈ B} = e ⁻¹' (B ×ˢ A) := by
    ext ω
    simp [e, MeasurableEquiv.piFinSuccAbove_apply, and_comm]
  rw [h_set_eq]
  have h_mp : MeasurePreserving e (Measure.pi fun _ : Fin (t + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin t => ν)) := by
    simpa [e, Fin.succAbove_last] using measurePreserving_piFinSuccAbove (fun _ : Fin (t + 1) => ν) (Fin.last t)
  have h_null : NullMeasurableSet (B ×ˢ A) (ν.prod (Measure.pi fun _ : Fin t => ν)) :=
    (hB.prod hA).nullMeasurableSet
  rw [h_mp.measureReal_preimage h_null]
  simp [Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul, mul_comm]

open MeasureTheory in
/-- Induction on `t`; the set of
seeds with history `h` splits by `seqHist_succ_eq_iff` into a condition on `Fin.init` and one on the last seed, measured
by `pi_real_init_last`. -/
theorem AdversarialBco.measure_seqHist {T X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (σ : (t : ℕ) → (Fin t → T) → X → T) (hσ : ∀ t h τ, MeasurableSet (σ t h ⁻¹' {τ}))
    (κ : (t : ℕ) → (Fin t → T) → T → ℝ) (hκ : ∀ t h τ, ν.real (σ t h ⁻¹' {τ}) = κ t h τ) (t : ℕ) (h : Fin t → T) :
    (Measure.pi fun _ : Fin t => ν).real {ω | AdversarialBco.seqHist σ t ω = h} =
      ∏ s : Fin t, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) := by
  revert h
  induction t with
  | zero =>
    intro h
    have hset : {ω : Fin 0 → X | AdversarialBco.seqHist σ 0 ω = h} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      funext i
      exact Fin.elim0 i
    rw [hset, probReal_univ]
    simp
  | succ t ih =>
    intro h
    have hset : {ω : Fin (t + 1) → X | AdversarialBco.seqHist σ (t + 1) ω = h} =
        {ω : Fin (t + 1) → X | Fin.init ω ∈ {ω' : Fin t → X | AdversarialBco.seqHist σ t ω' = Fin.init h} ∧
          ω (Fin.last t) ∈ σ t (Fin.init h) ⁻¹' {h (Fin.last t)}} := by
      ext ω
      exact AdversarialBco.seqHist_succ_eq_iff σ t ω h
    rw [hset, AdversarialBco.pi_real_init_last ν t _ (AdversarialBco.measurableSet_seqHist σ hσ t _) _
      (hσ t _ _), ih (Fin.init h), hκ, Fin.prod_univ_castSucc]
    congr 1

open MeasureTheory in
/-- `integral_comp_finite` over the fibres of the
history, measurable by `measurableSet_seqHist`, whose laws are the products of the round kernels by `measure_seqHist`. -/
theorem AdversarialBco.integral_seqHist {T X : Type*} [Fintype T] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (σ : (t : ℕ) → (Fin t → T) → X → T)
    (hσ : ∀ t h τ, MeasurableSet (σ t h ⁻¹' {τ})) (κ : (t : ℕ) → (Fin t → T) → T → ℝ)
    (hκ : ∀ t h τ, ν.real (σ t h ⁻¹' {τ}) = κ t h τ) (t : ℕ) (G : (Fin t → T) → ℝ) :
    ∫ ω, G (AdversarialBco.seqHist σ t ω) ∂(Measure.pi fun _ : Fin t => ν) =
      ∑ h : Fin t → T, (∏ s : Fin t, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) * G h := by
  rw [AdversarialBco.integral_comp_finite _ (AdversarialBco.seqHist σ t)
    (fun h => AdversarialBco.measurableSet_seqHist σ hσ t h) G]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← AdversarialBco.measure_seqHist ν σ hσ κ hκ t h]
  rfl

open MeasureTheory in
open MeasureTheory Set in
theorem AdversarialBco.coin_sampler_law {k : ℕ} (S : (Fin k → ℝ) → ℝ → Fin k)
    (hSm : Measurable (fun q : (Fin k → ℝ) × ℝ => S q.1 q.2)) (p : Fin k → ℝ)
    (hS : ∀ i, volume (Set.Icc (0 : ℝ) 1 ∩ S p ⁻¹' {i}) = ENNReal.ofReal (p i)) (hp : ∀ i, 0 ≤ p i)
    (a : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) (b : Bool) :
    MeasurableSet {uv : ℝ × ℝ | (S p uv.1, decide (uv.2 ≤ a (S p uv.1))) = (i, b)} ∧
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).real
          {uv : ℝ × ℝ | (S p uv.1, decide (uv.2 ≤ a (S p uv.1))) = (i, b)} =
        (if b then p i * a i else p i * (1 - a i)) := by
  let U := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hSp_meas : Measurable (S p) :=
    hSm.comp (Measurable.prodMk measurable_const measurable_id)
  have h_preimage_meas : MeasurableSet (S p ⁻¹' {i}) :=
    hSp_meas (measurableSet_singleton i)
  have ha_i_low : 0 ≤ a i := (ha i).1
  have ha_i_high : a i ≤ 1 := (ha i).2
  have h_rect_eq : {uv : ℝ × ℝ | (S p uv.1, decide (uv.2 ≤ a (S p uv.1))) = (i, b)} =
      (S p ⁻¹' {i}) ×ˢ {v | decide (v ≤ a i) = b} := by
    ext uv
    constructor
    · intro h
      have h1 : S p uv.1 = i := by
        have := congr_arg Prod.fst h
        simpa using this
      have h2 : decide (uv.2 ≤ a i) = b := by
        have := congr_arg Prod.snd h
        simpa [h1] using this
      refine ⟨by simpa using h1, by simpa using h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩
      have h1' : S p uv.1 = i := by simpa using h1
      have h2' : decide (uv.2 ≤ a i) = b := by simpa using h2
      refine Prod.ext h1' ?_
      simpa [h1'] using h2'
  have hV_meas : MeasurableSet {v | decide (v ≤ a i) = b} := by
    by_cases hb : b
    · have : {v | decide (v ≤ a i) = b} = Set.Iic (a i) := by
        ext v; simp [hb]
      rw [this]
      exact measurableSet_Iic
    · have : {v | decide (v ≤ a i) = b} = Set.Ioi (a i) := by
        ext v; simp [hb, not_le]
      rw [this]
      exact measurableSet_Ioi
  have h_meas : MeasurableSet ((S p ⁻¹' {i}) ×ˢ {v | decide (v ≤ a i) = b}) :=
    MeasurableSet.prod h_preimage_meas hV_meas
  have h_meas_target : MeasurableSet {uv : ℝ × ℝ | (S p uv.1, decide (uv.2 ≤ a (S p uv.1))) = (i, b)} := by
    rw [h_rect_eq]
    exact h_meas
  have h_measure : (U.prod U).real {uv : ℝ × ℝ | (S p uv.1, decide (uv.2 ≤ a (S p uv.1))) = (i, b)} =
      (if b then p i * a i else p i * (1 - a i)) := by
    rw [h_rect_eq]
    rw [Measure.real_def, Measure.prod_prod]
    have hU_Sp : U (S p ⁻¹' {i}) = ENNReal.ofReal (p i) := by
      rw [Measure.restrict_apply h_preimage_meas, Set.inter_comm]
      exact hS i
    by_cases hb : b
    · -- b = true
      have hV_eq : {v | decide (v ≤ a i) = b} = Set.Iic (a i) := by
        ext v; simp [hb]
      have hU_V : U {v | decide (v ≤ a i) = b} = ENNReal.ofReal (a i) := by
        rw [hV_eq]
        rw [Measure.restrict_apply measurableSet_Iic]
        have h_inter : Set.Iic (a i) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (a i) := by
          ext x; constructor
          · intro ⟨hx1, hx2⟩; exact ⟨hx2.1, hx1⟩
          · intro ⟨hx1, hx2⟩; exact ⟨hx2, hx1, hx2.trans ha_i_high⟩
        rw [h_inter]
        rw [Real.volume_Icc]
        simp
      have h_goal : (if b then p i * a i else p i * (1 - a i)) = p i * a i := by
        simp [hb]
      rw [h_goal]
      rw [hU_Sp, hU_V]
      rw [ENNReal.toReal_mul]
      rw [ENNReal.toReal_ofReal (hp i)]
      rw [ENNReal.toReal_ofReal ha_i_low]
    · -- b = false
      have hV_eq : {v | decide (v ≤ a i) = b} = Set.Ioi (a i) := by
        ext v; simp [hb, not_le]
      have hU_V : U {v | decide (v ≤ a i) = b} = ENNReal.ofReal (1 - a i) := by
        rw [hV_eq]
        rw [Measure.restrict_apply measurableSet_Ioi]
        have h_inter : Set.Ioi (a i) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (a i) 1 := by
          ext x; constructor
          · intro ⟨hx1, hx2⟩; exact ⟨hx1, hx2.2⟩
          · intro ⟨hx1, hx2⟩
            have hx_gt_ai : a i < x := hx1
            have h0_le_x : 0 ≤ x := le_of_lt (ha_i_low.trans_lt hx_gt_ai)
            exact ⟨hx_gt_ai, h0_le_x, hx2⟩
        rw [h_inter]
        rw [Real.volume_Ioc]
      have h_goal : (if b then p i * a i else p i * (1 - a i)) = p i * (1 - a i) := by
        simp [hb]
      rw [h_goal]
      rw [hU_Sp, hU_V]
      rw [ENNReal.toReal_mul]
      rw [ENNReal.toReal_ofReal (hp i)]
      rw [ENNReal.toReal_ofReal (sub_nonneg.2 ha_i_high)]
  exact And.intro h_meas_target h_measure

open MeasureTheory in
open Set MeasureTheory in
theorem AdversarialBco.measurable_of_finite_fibers {α β T : Type*} [MeasurableSpace α] [MeasurableSpace β] [Finite T]
    (g : α → T) (hg : ∀ τ, MeasurableSet (g ⁻¹' {τ})) (F : T → α → β) (hF : ∀ τ, Measurable (F τ)) :
    Measurable fun a => F (g a) a := by
  intro s hs
  have h_eq : (fun a => F (g a) a) ⁻¹' s = ⋃ τ : T, g ⁻¹' {τ} ∩ (F τ) ⁻¹' s := by
    ext a; simp [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, eq_comm]
  rw [h_eq]
  refine MeasurableSet.iUnion ?_
  intro τ
  refine MeasurableSet.inter (hg τ) ?_
  exact (hF τ) hs

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.measurableSet_obsHist {T X : Type*} [MeasurableSpace X] (ρ : (t : ℕ) → (Fin t → T) → X → ℝ → T)
    (hρ : ∀ t h τ, MeasurableSet {p : X × ℝ | ρ t h p.1 p.2 = τ}) (t : ℕ) (h : Fin t → T) :
    MeasurableSet {p : (ℕ → X) × (Fin t → ℝ) | AdversarialBco.obsHist ρ t p.1 p.2 = h} := by
  induction' t with t ih
  · -- t = 0: Fin 0 → T is a subsingleton, so the set is everything
    have h_univ : {p : (ℕ → X) × (Fin 0 → ℝ) | AdversarialBco.obsHist ρ 0 p.1 p.2 = h} = Set.univ := by
      ext p
      simp [AdversarialBco.obsHist]
      -- Goal: Fin.elim0 = h
      -- Any two functions from Fin 0 are equal
      ext i
      exact Fin.elim0 i
    rw [h_univ]
    exact MeasurableSet.univ
  · -- t → t+1
    have h_eq : {p : (ℕ → X) × (Fin (t+1) → ℝ) | AdversarialBco.obsHist ρ (t+1) p.1 p.2 = h} =
        {p | AdversarialBco.obsHist ρ t p.1 (Fin.init p.2) = Fin.init h} ∩
        {p | ρ t (Fin.init h) (p.1 t) (p.2 (Fin.last t)) = h (Fin.last t)} := by
      ext p
      constructor
      · intro hp
        have h_obs : AdversarialBco.obsHist ρ (t+1) p.1 p.2 = h := hp
        simp [AdversarialBco.obsHist] at h_obs
        -- h_obs: Fin.snoc (obsHist ρ t p.1 (Fin.init p.2)) (ρ t (obsHist ρ t p.1 (Fin.init p.2)) (p.1 t) (p.2 (Fin.last t))) = h
        -- Use Fin.snoc_init_self to rewrite RHS
        rw [← Fin.snoc_init_self h] at h_obs
        have h_inj := (Fin.snoc_inj (x := AdversarialBco.obsHist ρ t p.1 (Fin.init p.2))
          (xₙ := ρ t (AdversarialBco.obsHist ρ t p.1 (Fin.init p.2)) (p.1 t) (p.2 (Fin.last t)))
          (y := Fin.init h) (yₙ := h (Fin.last t))).mp h_obs
        rcases h_inj with ⟨h_init, h_last⟩
        have h_last' : ρ t (Fin.init h) (p.1 t) (p.2 (Fin.last t)) = h (Fin.last t) := by
          rwa [h_init] at h_last
        exact ⟨h_init, h_last'⟩
      · intro hp
        rcases hp with ⟨hp1, hp2⟩
        -- hp1: AdversarialBco.obsHist ρ t p.1 (Fin.init p.2) = Fin.init h
        -- hp2: ρ t (Fin.init h) (p.1 t) (p.2 (Fin.last t)) = h (Fin.last t)
        dsimp at hp1 hp2
        show AdversarialBco.obsHist ρ (t+1) p.1 p.2 = h
        simp [AdversarialBco.obsHist, hp1, hp2, Fin.snoc_init_self h]
    rw [h_eq]
    apply MeasurableSet.inter
    · -- first set: preimage under p ↦ (p.1, Fin.init p.2) of the IH set
      have h_meas_map : Measurable (fun (p : (ℕ → X) × (Fin (t+1) → ℝ)) => (p.1, Fin.init p.2)) := by
        refine Measurable.prodMk ?_ ?_
        · exact measurable_fst
        · -- Fin.init is measurable
          have h_fin_init_meas : Measurable (Fin.init : ((Fin (t+1) → ℝ) → (Fin t → ℝ))) := by
            refine Measurable.of_eval (fun i => ?_)
            simpa [Fin.init] using measurable_pi_apply (Fin.castSucc i)
          exact h_fin_init_meas.comp measurable_snd
      have h_meas_set : MeasurableSet {q : (ℕ → X) × (Fin t → ℝ) | AdversarialBco.obsHist ρ t q.1 q.2 = Fin.init h} := ih (Fin.init h)
      -- The set is the preimage
      have : {p | AdversarialBco.obsHist ρ t p.1 (Fin.init p.2) = Fin.init h} =
          (fun (p : (ℕ → X) × (Fin (t+1) → ℝ)) => (p.1, Fin.init p.2))⁻¹'
          {q : (ℕ → X) × (Fin t → ℝ) | AdversarialBco.obsHist ρ t q.1 q.2 = Fin.init h} := by
        ext p; simp
      rw [this]
      exact h_meas_set.preimage h_meas_map
    · -- second set: preimage under p ↦ (p.1 t, p.2 (Fin.last t)) of the hρ set
      have h_meas_map : Measurable (fun (p : (ℕ → X) × (Fin (t+1) → ℝ)) => (p.1 t, p.2 (Fin.last t))) := by
        refine Measurable.prodMk ?_ ?_
        · exact (measurable_pi_apply t).comp measurable_fst
        · exact (measurable_pi_apply (Fin.last t)).comp measurable_snd
      have h_meas_set : MeasurableSet {q : X × ℝ | ρ t (Fin.init h) q.1 q.2 = h (Fin.last t)} :=
        hρ t (Fin.init h) (h (Fin.last t))
      have : {p | ρ t (Fin.init h) (p.1 t) (p.2 (Fin.last t)) = h (Fin.last t)} =
          (fun (p : (ℕ → X) × (Fin (t+1) → ℝ)) => (p.1 t, p.2 (Fin.last t)))⁻¹'
          {q : X × ℝ | ρ t (Fin.init h) q.1 q.2 = h (Fin.last t)} := by
        ext p; simp
      rw [this]
      exact h_meas_set.preimage h_meas_map

theorem AdversarialBco.tree_sum_le {T : Type*} [Fintype T] (κ : (t : ℕ) → (Fin t → T) → T → ℝ)
    (hκ0 : ∀ t h τ, 0 ≤ κ t h τ) (hκ1 : ∀ t h, ∑ τ, κ t h τ = 1)
    (g : (t : ℕ) → (Fin (t + 1) → T) → ℝ) (c : ℕ → ℝ)
    (hg : ∀ t (h : Fin t → T), ∑ τ, κ t h τ * g t (Fin.snoc (α := fun _ => T) h τ) ≤ c t) (n : ℕ) :
    ∑ h : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin n, g t (fun i : Fin (t + 1) => h (Fin.castLE (Nat.succ_le_of_lt t.2) i)) ≤
      ∑ t ∈ Finset.range n, c t := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ]

    -- Split the summand using Fin.prod_univ_castSucc and Fin.sum_univ_castSucc
    have h_split (h : Fin (n + 1) → T) : (∏ s : Fin (n + 1), κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin (n + 1), g t (fun i : Fin (t + 1) => h (Fin.castLE (Nat.succ_le_of_lt t.2) i)) =
        ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
        ((∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i))) +
          g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i))) := by
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]

    -- Rewrite the LHS using h_split
    have h_lhs_eq : (∑ h : Fin (n + 1) → T, (∏ s : Fin (n + 1), κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin (n + 1), g t (fun i : Fin (t + 1) => h (Fin.castLE (Nat.succ_le_of_lt t.2) i))) =
        (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
          (∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i)))) +
        (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
        g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i))) := by
      simp [Finset.sum_add_distrib, h_split, mul_add]

    rw [h_lhs_eq]

    -- Define P(h) = product over Fin n * κ(last)
    let P (h : Fin (n + 1) → T) : ℝ := (∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
      κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))

    have h_P_eq (h : Fin (n + 1) → T) : P h = ∏ s : Fin (n + 1), κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) := by
      rw [Fin.prod_univ_castSucc]

    -- Define G(a) = inner sum for a : Fin n → T
    let G (a : Fin n → T) : ℝ := ∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => a (Fin.castLE (Nat.succ_le_of_lt t.2) i))

    -- Key lemma: S h = G (Fin.init h) for any h
    have h_S_eq_G (h : Fin (n + 1) → T) : (∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i))) = G (Fin.init h) := by
      dsimp [G]
      refine Finset.sum_congr rfl fun t _ => ?_
      refine congrArg (g (Fin.castSucc t)) ?_
      ext i
      simp [Fin.init]

    -- Rewrite the first sum using G
    have h_A_eq : (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
          (∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i)))) =
        ∑ h : Fin (n + 1) → T, P h * G (Fin.init h) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      -- Goal: A * S = P h * G (Fin.init h) where A = product, S = inner sum
      -- Note that P h = A, so goal is P h * S = P h * G (Fin.init h)
      -- This reduces to S = G (Fin.init h), which is h_S_eq_G h
      have h_P_eq' : P h = (∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n)) := rfl
      rw [h_P_eq']
      rw [h_S_eq_G h]

    -- Apply sum_prod_policy_init
    have h_A_eq2 : (∑ h : Fin (n + 1) → T, P h * G (Fin.init h)) =
        ∑ a : Fin n → T, (∏ t : Fin n, κ t (fun i : Fin t => a (Fin.castLE t.2.le i)) (a t)) * G a := by
      simp_rw [h_P_eq]
      rw [AdversarialBco.sum_prod_policy_init κ hκ1 n G]

    -- By IH, A ≤ ∑ t ∈ range n, c t
    have h_A_le : (∑ h : Fin (n + 1) → T, P h * G (Fin.init h)) ≤ ∑ t ∈ Finset.range n, c t := by
      rw [h_A_eq2]
      exact ih

    -- Helper lemmas about Fin.castLE
    have h_castLE_castSucc (s : Fin n) (i : Fin s) :
        Fin.castLE (Fin.castSucc s).2.le i = Fin.castSucc (Fin.castLE s.2.le i) := by
      ext; simp

    have h_castLE_last (i : Fin n) : Fin.castLE (Fin.last n).2.le i = Fin.castSucc i := by
      ext; simp

    -- Simplify P (Fin.snoc a τ)
    have h_P_snoc (a : Fin n → T) (τ : T) : P ((Fin.snoc a τ : Fin (n+1) → T)) = (∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) * κ n a τ := by
      simp only [P]
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun s _ => ?_) ?_
      · have hs : (fun i : Fin s => (Fin.snoc a τ : Fin (n+1) → T) (Fin.castLE (Fin.castSucc s).2.le i)) =
            (fun i : Fin s => a (Fin.castLE s.2.le i)) := by
          funext i
          have : (Fin.castLE (Fin.castSucc s).2.le i : Fin (n+1)) = Fin.castSucc (Fin.castLE s.2.le i) := Fin.ext rfl
          rw [this, Fin.snoc_castSucc]
        show κ s (fun i : Fin s => (Fin.snoc a τ : Fin (n+1) → T) (Fin.castLE (Fin.castSucc s).2.le i))
            ((Fin.snoc a τ : Fin (n+1) → T) (Fin.castSucc s)) = _
        rw [hs, Fin.snoc_castSucc]
      · have hl : (fun i : Fin n => (Fin.snoc a τ : Fin (n+1) → T) (Fin.castLE (Fin.last n).2.le i)) = a := by
          funext i
          have : (Fin.castLE (Fin.last n).2.le i : Fin (n+1)) = Fin.castSucc i := Fin.ext rfl
          rw [this, Fin.snoc_castSucc]
        show κ n (fun i : Fin n => (Fin.snoc a τ : Fin (n+1) → T) (Fin.castLE (Fin.last n).2.le i))
            ((Fin.snoc a τ : Fin (n+1) → T) (Fin.last n)) = _
        rw [hl, Fin.snoc_last]

    -- Simplify the last round term
    have h_last_term (h : Fin (n + 1) → T) : g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i)) = g n h := by
      have : (Fin.last n : ℕ) = n := by simp
      simp [this]

    -- Rewrite B in terms of P
    have h_B_eq : (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
        g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i))) =
        ∑ h : Fin (n + 1) → T, P h * g n h := by
      simp [P, h_last_term]

    -- Reindex B using Fin.snocEquiv
    have h_B_reindex : (∑ h : Fin (n + 1) → T, P h * g n h) =
        ∑ a : Fin n → T, ∑ τ : T, (P ((Fin.snoc a τ : Fin (n+1) → T))) * g n (Fin.snoc a τ) := by
      calc
        (∑ h : Fin (n + 1) → T, P h * g n h) =
          ∑ x : T × (Fin n → T), P ((Fin.snocEquiv (fun _ => T)) x) * g n ((Fin.snocEquiv (fun _ => T)) x) := by
          apply (Fintype.sum_equiv (Fin.snocEquiv (fun _ => T)) _ _ ?_).symm
          intro p
          rcases p with ⟨τ, a⟩
          simp [Fin.snocEquiv_apply]
        _ = ∑ a : Fin n → T, ∑ τ : T, P ((Fin.snoc a τ : Fin (n+1) → T)) * g n (Fin.snoc a τ) := by
          have h := Fintype.sum_prod_type' (f := fun (τ : T) (a : Fin n → T) => P ((Fin.snoc a τ : Fin (n+1) → T)) * g n (Fin.snoc a τ))
          calc
            ∑ x : T × (Fin n → T), P ((Fin.snocEquiv (fun _ => T)) x) * g n ((Fin.snocEquiv (fun _ => T)) x)
                = ∑ x : T × (Fin n → T), P ((Fin.snoc x.2 x.1 : Fin (n+1) → T)) * g n ((Fin.snoc x.2 x.1 : Fin (n+1) → T)) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              have h_eq : (Fin.snocEquiv (fun _ => T)) x = Fin.snoc x.2 x.1 := by
                ext y
                simpa using Fin.snocEquiv_apply (α := fun _ => T) (f := x) (x := y)
              simp [h_eq]
            _ = ∑ x : T, ∑ y : Fin n → T, P ((Fin.snoc y x : Fin (n+1) → T)) * g n ((Fin.snoc y x : Fin (n+1) → T)) := h
            _ = ∑ a : Fin n → T, ∑ τ : T, P ((Fin.snoc a τ : Fin (n+1) → T)) * g n (Fin.snoc a τ) := by
              rw [Finset.sum_comm]

    -- Now bound B
    have h_B_le : (∑ h : Fin (n + 1) → T, P h * g n h) ≤ c n := by
      rw [h_B_reindex]
      simp_rw [h_P_snoc]
      -- Now: ∑ a, ∑ τ, (∏ s, κ s (past_s a) (a s)) * κ n a τ * g n (Fin.snoc a τ)
      -- Factor out the product from the inner sum
      have h_factor (a : Fin n → T) : (∑ τ : T, (∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) * (κ n a τ * g n (Fin.snoc a τ))) =
          (∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) * (∑ τ : T, κ n a τ * g n (Fin.snoc a τ)) := by
        rw [← Finset.mul_sum]
      simp_rw [mul_assoc, h_factor]
      -- Now: ∑ a, (∏ s, κ s (past_s a) (a s)) * (∑ τ, κ n a τ * g n (Fin.snoc a τ))
      calc
        (∑ a : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) *
          (∑ τ : T, κ n a τ * g n (Fin.snoc a τ))) ≤
        (∑ a : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) * c n) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h_nonneg : 0 ≤ ∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s) := by
            refine Finset.prod_nonneg fun s _ => ?_
            apply hκ0
          nlinarith [hg n a, h_nonneg]
        _ = c n * (∑ a : Fin n → T, ∏ s : Fin n, κ s (fun i : Fin s => a (Fin.castLE s.2.le i)) (a s)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        _ = c n * 1 := by rw [AdversarialBco.sum_prod_policy κ hκ1 n]
        _ = c n := by simp

    -- Now combine A and B
    have h_total : ((∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
          (∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i)))) +
        (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
        g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i)))) ≤
        (∑ t ∈ Finset.range n, c t) + c n := by
      have h_first : (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
          (∑ t : Fin n, g (Fin.castSucc t) (fun i : Fin (Fin.castSucc t + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc t).2) i)))) ≤ ∑ t ∈ Finset.range n, c t := by
        rw [h_A_eq]
        exact h_A_le
      have h_second : (∑ h : Fin (n + 1) → T, ((∏ s : Fin n, κ (Fin.castSucc s) (fun i : Fin (Fin.castSucc s) => h (Fin.castLE (Fin.castSucc s).2.le i)) (h (Fin.castSucc s))) *
          κ (Fin.last n) (fun i : Fin (Fin.last n) => h (Fin.castLE (Fin.last n).2.le i)) (h (Fin.last n))) *
        g (Fin.last n) (fun i : Fin (Fin.last n + 1) => h (Fin.castLE (Nat.succ_le_of_lt (Fin.last n).2) i))) ≤ c n := by
        rw [h_B_eq]
        exact h_B_le
      nlinarith

    exact h_total

open Real Set in
/-- The linear projection of `(p, g)` on `(p x, g x b)`. -/
def AdversarialBco.convexFq_proj {C : Type*} [Fintype C] (x : C) (b : Bool) : (C → ℝ) × (C → Bool → C → ℝ) →ₗ[ℝ] ℝ × (C → ℝ) :=
  LinearMap.prod
    ((LinearMap.proj x).comp (LinearMap.fst ℝ (C → ℝ) (C → Bool → C → ℝ)))
    ((LinearMap.proj b).comp ((LinearMap.proj x).comp (LinearMap.snd ℝ (C → ℝ) (C → Bool → C → ℝ))))

open Real Set in
theorem AdversarialBco.convex_Fq {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z) :
    Convex ℝ {pg : (C → ℝ) × (C → Bool → C → ℝ) | pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
      (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)} := by
  have h_std : Convex ℝ (stdSimplex ℝ C) := convex_stdSimplex ℝ C
  have h_std_preimage : Convex ℝ ({pg : (C → ℝ) × (C → Bool → C → ℝ) | pg.1 ∈ stdSimplex ℝ C}) :=
    h_std.linear_preimage (LinearMap.fst ℝ (C → ℝ) (C → Bool → C → ℝ))
  have h_eq : Convex ℝ {su : ℝ × (C → ℝ) |
      (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨ (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)} :=
    AdversarialBco.convex_Eq η hη q hq
  have h_preimage (x : C) (b : Bool) : Convex ℝ ((AdversarialBco.convexFq_proj x b) ⁻¹' {su : ℝ × (C → ℝ) |
      (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨ (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)}) :=
    h_eq.linear_preimage (AdversarialBco.convexFq_proj x b)
  have h_inter : Convex ℝ (⋂ x, ⋂ b, (AdversarialBco.convexFq_proj x b) ⁻¹' {su : ℝ × (C → ℝ) |
      (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨ (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)}) :=
    convex_iInter fun x => convex_iInter fun b => h_preimage x b
  have h_total : Convex ℝ ({pg : (C → ℝ) × (C → Bool → C → ℝ) | pg.1 ∈ stdSimplex ℝ C} ∩
      ⋂ x, ⋂ b, (AdversarialBco.convexFq_proj x b) ⁻¹' {su : ℝ × (C → ℝ) |
      (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨ (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)}) :=
    h_std_preimage.inter h_inter
  have h_eq_set : {pg : (C → ℝ) × (C → Bool → C → ℝ) | pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
      (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)} =
      ({pg : (C → ℝ) × (C → Bool → C → ℝ) | pg.1 ∈ stdSimplex ℝ C} ∩
        ⋂ x, ⋂ b, (AdversarialBco.convexFq_proj x b) ⁻¹' {su : ℝ × (C → ℝ) |
        (0 < su.1 ∧ ∑ z, q z * Real.exp (-η * (su.2 z / su.1)) ≤ 1) ∨ (su.1 = 0 ∧ ∀ z, 0 ≤ su.2 z)}) := by
    ext pg
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      intro i
      intro b
      have hx := h i b
      have h_eq : (AdversarialBco.convexFq_proj i b) pg = (pg.1 i, pg.2 i b) := by
        simp [AdversarialBco.convexFq_proj]
      simpa [h_eq] using hx
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      intro i
      intro b
      have hx := h i b
      have h_eq : (AdversarialBco.convexFq_proj i b) pg = (pg.1 i, pg.2 i b) := by
        simp [AdversarialBco.convexFq_proj]
      simpa [h_eq] using hx
  rw [h_eq_set]
  exact h_total

theorem AdversarialBco.phi_props {C : Type*} [Fintype C] [DecidableEq C] (A : Set ((C → ℝ) × (C → C → ℝ)))
    (hA : Convex ℝ A) (Y : Set ((C → ℝ) × (C → Bool → C → ℝ))) (hY : Convex ℝ Y) :
    (∀ pg : (C → ℝ) × (C → Bool → C → ℝ), Continuous fun wθ : (C → ℝ) × (C → C → ℝ) =>
      ∑ y, (wθ.1 y * ∑ x, pg.2 x false y +
        ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * wθ.2 y x)) ∧
    (∀ pg : (C → ℝ) × (C → Bool → C → ℝ), ConcaveOn ℝ A fun wθ : (C → ℝ) × (C → C → ℝ) =>
      ∑ y, (wθ.1 y * ∑ x, pg.2 x false y +
        ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * wθ.2 y x)) ∧
    (∀ wθ : (C → ℝ) × (C → C → ℝ), Continuous fun pg : (C → ℝ) × (C → Bool → C → ℝ) =>
      ∑ y, (wθ.1 y * ∑ x, pg.2 x false y +
        ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * wθ.2 y x)) ∧
    ∀ wθ : (C → ℝ) × (C → C → ℝ), ConvexOn ℝ Y fun pg : (C → ℝ) × (C → Bool → C → ℝ) =>
      ∑ y, (wθ.1 y * ∑ x, pg.2 x false y +
        ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * wθ.2 y x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: continuity in wθ for fixed pg
    intro pg
    refine continuous_finset_sum _ (fun y _ => ?_)
    refine Continuous.add ?_ ?_
    · refine Continuous.mul ?_ continuous_const
      exact continuous_apply y |>.comp continuous_fst
    · refine continuous_finset_sum _ (fun x _ => ?_)
      refine Continuous.mul ?_ ?_
      · exact continuous_const
      · exact continuous_apply x |>.comp (continuous_apply y |>.comp continuous_snd)
  · -- Part 2: ConcaveOn ℝ A (fun wθ => ...) for fixed pg
    intro pg
    refine ⟨hA, ?_⟩
    intro x hx y hy a b ha hb hab
    have h_eq : a • (∑ z, (x.1 z * ∑ x', pg.2 x' false z +
        ∑ x', (pg.1 x' - (if x' = z then 1 else 0) + pg.2 x' true z - pg.2 x' false z) * x.2 z x')) +
        b • (∑ z, (y.1 z * ∑ x', pg.2 x' false z +
        ∑ x', (pg.1 x' - (if x' = z then 1 else 0) + pg.2 x' true z - pg.2 x' false z) * y.2 z x')) =
        (∑ z, (((a • x + b • y).1 z) * ∑ x', pg.2 x' false z +
        ∑ x', (pg.1 x' - (if x' = z then 1 else 0) + pg.2 x' true z - pg.2 x' false z) * ((a • x + b • y).2 z x'))) := by
      rw [Finset.smul_sum, Finset.smul_sum]
      simp
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul, mul_sub, sub_mul]
      ring_nf
    exact le_of_eq h_eq
  · -- Part 3: continuity in pg for fixed wθ
    intro wθ
    refine continuous_finset_sum _ (fun y _ => ?_)
    refine Continuous.add ?_ ?_
    · refine Continuous.mul continuous_const ?_
      refine continuous_finset_sum _ (fun x _ => ?_)
      exact continuous_apply y |>.comp (continuous_apply false |>.comp (continuous_apply x |>.comp continuous_snd))
    · refine continuous_finset_sum _ (fun x _ => ?_)
      refine Continuous.mul ?_ continuous_const
      refine Continuous.sub ?_ ?_
      · refine Continuous.add ?_ ?_
        · refine Continuous.sub ?_ continuous_const
          exact continuous_apply x |>.comp continuous_fst
        · exact continuous_apply y |>.comp (continuous_apply true |>.comp (continuous_apply x |>.comp continuous_snd))
      · exact continuous_apply y |>.comp (continuous_apply false |>.comp (continuous_apply x |>.comp continuous_snd))
  · -- Part 4: ConvexOn ℝ Y (fun pg => ...) for fixed wθ
    intro wθ
    refine ⟨hY, ?_⟩
    intro x hx y hy a b ha hb hab
    have h_eq : a • (∑ z, (wθ.1 z * ∑ x', x.2 x' false z +
        ∑ x', (x.1 x' - (if x' = z then 1 else 0) + x.2 x' true z - x.2 x' false z) * wθ.2 z x')) +
        b • (∑ z, (wθ.1 z * ∑ x', y.2 x' false z +
        ∑ x', (y.1 x' - (if x' = z then 1 else 0) + y.2 x' true z - y.2 x' false z) * wθ.2 z x')) =
        (∑ z, (wθ.1 z * ∑ x', ((a • x + b • y).2 x' false z) +
        ∑ x', (((a • x + b • y).1 x') - (if x' = z then 1 else 0) + ((a • x + b • y).2 x' true z) - ((a • x + b • y).2 x' false z)) * wθ.2 z x')) := by
      rw [Finset.smul_sum, Finset.smul_sum]
      simp
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul, mul_sub, sub_mul]
      apply sub_eq_zero.mp
      ring_nf
      calc
        -(a * wθ.2 z z) + wθ.2 z z - wθ.2 z z * b = wθ.2 z z - a * wθ.2 z z - wθ.2 z z * b := by ring
        _ = wθ.2 z z * (1 - a - b) := by ring
        _ = wθ.2 z z * (1 - (a + b)) := by ring
        _ = wθ.2 z z * (1 - 1) := by rw [hab]
        _ = wθ.2 z z * 0 := by ring
        _ = 0 := by ring
    exact le_of_eq h_eq.symm

theorem AdversarialBco.mass_gibbs {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z)
    (hq1 : ∑ z, q z = 1) (W : C → ℝ) (hW : ∀ y, 0 ≤ W y) (M : ℝ) (hM : ∑ y, W y = M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : C → ℝ, ∑ z, q z * Real.exp (-η * e z) ≤ 1 ∧
      ∑ y, W y * e y ≤ -(∑ y, W y * Real.log (W y / (M * q y))) / η + M * δ := by
  have hM_nonneg : 0 ≤ M := by
    rw [← hM]
    exact Finset.sum_nonneg (λ i _ => hW i)
  by_cases hM0 : M = 0
  · -- Case M = 0: take e = 0
    refine ⟨λ _ => 0, ?_, ?_⟩
    · have hcalc : ∑ z, q z * Real.exp (-η * (0 : ℝ)) = 1 := by
        calc
          ∑ z, q z * Real.exp (-η * (0 : ℝ)) = ∑ z, q z * Real.exp 0 := by simp
          _ = ∑ z, q z * 1 := by simp
          _ = ∑ z, q z := by simp
          _ = 1 := hq1
      exact le_of_eq hcalc
    · have hW0 : ∀ y, W y = 0 := by
        have hsum0 : ∑ y, W y = 0 := by rw [hM, hM0]
        have h := (Finset.sum_eq_zero_iff_of_nonneg (λ i _ => hW i)).mp hsum0
        intro y
        exact h y (Finset.mem_univ y)
      simp [hW0, hM0]
  · -- Case M > 0
    have hMpos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM0)
    set r := λ y => W y / M with hr_def
    have hr_nonneg : ∀ y, 0 ≤ r y := by
      intro y
      dsimp [r]
      exact div_nonneg (hW y) hM_nonneg
    have hr_sum : ∑ y, r y = 1 := by
      dsimp [r]
      calc
        ∑ y, W y / M = (∑ y, W y) / M := by rw [Finset.sum_div]
        _ = M / M := by rw [hM]
        _ = 1 := div_self (ne_of_gt hMpos)
    rcases gibbs_upper η hη q r hq hq1 hr_nonneg hr_sum δ hδ with ⟨e, h_eq, h_ineq⟩
    refine ⟨e, h_eq, ?_⟩
    calc
      ∑ y, W y * e y = ∑ y, (M * r y) * e y := by
        dsimp [r]
        field_simp [hMpos.ne.symm]
      _ = M * ∑ y, r y * e y := by
        simp_rw [mul_assoc, Finset.mul_sum]
      _ ≤ M * (-(∑ y, r y * Real.log (r y / q y)) / η + δ) :=
        mul_le_mul_of_nonneg_left h_ineq hM_nonneg
      _ = -(M * (∑ y, r y * Real.log (r y / q y))) / η + M * δ := by ring
      _ = -(∑ y, M * (r y * Real.log (r y / q y))) / η + M * δ := by
        simp_rw [Finset.mul_sum]
      _ = -(∑ y, W y * Real.log (r y / q y)) / η + M * δ := by
        refine congrArg (λ t => -t / η + M * δ) ?_
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [r]
        field_simp [hMpos.ne.symm]
      _ = -(∑ y, W y * Real.log (W y / (M * q y))) / η + M * δ := by
        refine congrArg (λ t => -t / η + M * δ) ?_
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [r]
        ring_nf

theorem AdversarialBco.vertex_payoff_eq {C : Type*} [Fintype C] [DecidableEq C] (w : C → ℝ) (f : C → C → ℝ) (x0 : C)
    (e0 e1 : C → ℝ) :
    ∑ y, (w y * ∑ x, (if x = x0 then e0 y else 0) +
        ∑ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + (if x = x0 then e1 y else 0) -
          (if x = x0 then e0 y else 0)) * (w y * f y x)) =
      ∑ y, w y * f y x0 - ∑ y, w y * f y y + ∑ y, w y * (1 - f y x0) * e0 y + ∑ y, w y * f y x0 * e1 y := by
  have hsum_inner : ∀ y, ∑ x : C, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) +
      (if x = x0 then e1 y else 0) - (if x = x0 then e0 y else 0)) * (w y * f y x) =
      w y * f y x0 - w y * f y y + w y * e1 y * f y x0 - w y * e0 y * f y x0 := by
    intro y
    have h_distrib : ∀ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) +
        (if x = x0 then e1 y else 0) - (if x = x0 then e0 y else 0)) * (w y * f y x) =
        ((Pi.single x0 (1 : ℝ) : C → ℝ) x) * (w y * f y x) - (if x = y then 1 else 0) * (w y * f y x) +
        (if x = x0 then e1 y else 0) * (w y * f y x) - (if x = x0 then e0 y else 0) * (w y * f y x) := by
      intro x; ring
    rw [Finset.sum_congr rfl fun x hx => h_distrib x]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm, mul_left_comm, Pi.single, Function.update]
  calc
    ∑ y : C, (w y * ∑ x : C, (if x = x0 then e0 y else 0) +
        ∑ x : C, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + (if x = x0 then e1 y else 0) -
          (if x = x0 then e0 y else 0)) * (w y * f y x))
    = ∑ y : C, (w y * e0 y + (w y * f y x0 - w y * f y y + w y * e1 y * f y x0 - w y * e0 y * f y x0)) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      simp [hsum_inner y]
    _ = (∑ y : C, w y * e0 y) + (∑ y : C, (w y * f y x0 - w y * f y y + w y * e1 y * f y x0 - w y * e0 y * f y x0)) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ y : C, w y * f y x0 - ∑ y : C, w y * f y y + ∑ y : C, w y * (1 - f y x0) * e0 y + ∑ y : C, w y * f y x0 * e1 y := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm, mul_left_comm, add_comm, mul_sub]
      abel

theorem AdversarialBco.primal_vertex {C : Type*} [Fintype C] [DecidableEq C] (η : ℝ) (hη : 0 < η) (q : C → ℝ)
    (hq : ∀ z, 0 < q z) (hq1 : ∑ z, q z = 1) (w : C → ℝ) (hw : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (f : C → C → ℝ) (hf : ∀ y x, f y x ∈ Set.Icc (0 : ℝ) 1) (x0 : C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : C → Bool → C → ℝ,
      (∀ x b, (0 < (Pi.single x0 (1 : ℝ) : C → ℝ) x ∧
          ∑ z, q z * Real.exp (-η * (g x b z / (Pi.single x0 (1 : ℝ) : C → ℝ) x)) ≤ 1) ∨
        ((Pi.single x0 (1 : ℝ) : C → ℝ) x = 0 ∧ ∀ z, 0 ≤ g x b z)) ∧
      ∑ y, (w y * ∑ x, g x false y +
          ∑ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)) ≤
        ∑ y, w y * f y x0 -
          (∑ y, w y * (f y x0 * Real.log (f y x0 / ∑ y', w y' * f y' x0) +
              (1 - f y x0) * Real.log ((1 - f y x0) / (1 - ∑ y', w y' * f y' x0))) +
            ∑ y, w y * Real.log (w y / q y)) / η -
          ∑ y, w y * f y y + δ := by
  set F := ∑ y, w y * f y x0 with hF
  set W1 := fun y => w y * f y x0 with hW1
  set W0 := fun y => w y * (1 - f y x0) with hW0
  have hF_nonneg : 0 ≤ F := Finset.sum_nonneg fun y _ => mul_nonneg (hw y) (hf y x0).1
  have hW1_nonneg : ∀ y, 0 ≤ W1 y := by
    intro y
    dsimp [W1]
    exact mul_nonneg (hw y) (hf y x0).1
  have hW0_nonneg : ∀ y, 0 ≤ W0 y := by
    intro y
    dsimp [W0]
    have hfy : f y x0 ≤ 1 := (hf y x0).2
    nlinarith [hw y]
  have hW1_sum : ∑ y, W1 y = F := rfl
  have hW0_sum : ∑ y, W0 y = 1 - F := by
    dsimp [W0, F]
    calc
      ∑ y, w y * (1 - f y x0) = ∑ y, (w y * 1 - w y * f y x0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      _ = (∑ y, w y * 1) - (∑ y, w y * f y x0) := by rw [Finset.sum_sub_distrib]
      _ = (∑ y, w y) - (∑ y, w y * f y x0) := by simp
      _ = 1 - F := by rw [hw1]
  have hδ2_pos : 0 < δ / 2 := by linarith
  obtain ⟨e1, he1q, he1⟩ := AdversarialBco.mass_gibbs η hη q hq hq1 W1 hW1_nonneg F hW1_sum (δ / 2) hδ2_pos
  obtain ⟨e0, he0q, he0⟩ := AdversarialBco.mass_gibbs η hη q hq hq1 W0 hW0_nonneg (1 - F) hW0_sum (δ / 2) hδ2_pos
  set g : C → Bool → C → ℝ := fun x b z => if x = x0 then (if b then e1 z else e0 z) else 0 with hg
  have h_first : ∀ x b, (0 < (Pi.single x0 (1 : ℝ) : C → ℝ) x ∧
      ∑ z, q z * Real.exp (-η * (g x b z / (Pi.single x0 (1 : ℝ) : C → ℝ) x)) ≤ 1) ∨
      ((Pi.single x0 (1 : ℝ) : C → ℝ) x = 0 ∧ ∀ z, 0 ≤ g x b z) := by
    intro x b
    by_cases hx : x = x0
    · left
      constructor
      · rw [hx, Pi.single_eq_same]
        norm_num
      · rw [hx, Pi.single_eq_same]
        simp [g]
        by_cases hb : b
        · simpa [hb] using he1q
        · simpa [hb] using he0q
    · right
      constructor
      · rw [Pi.single_eq_of_ne hx]
      · intro z
        simp [g, hx]
  have h_second : ∑ y, (w y * ∑ x, g x false y +
      ∑ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)) ≤
      ∑ y, w y * f y x0 -
        (∑ y, w y * (f y x0 * Real.log (f y x0 / ∑ y', w y' * f y' x0) +
            (1 - f y x0) * Real.log ((1 - f y x0) / (1 - ∑ y', w y' * f y' x0))) +
          ∑ y, w y * Real.log (w y / q y)) / η -
        ∑ y, w y * f y y + δ := by
    have h_vertex := AdversarialBco.vertex_payoff_eq w f x0 e0 e1
    have hLHS : ∑ y, (w y * ∑ x, g x false y +
        ∑ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)) =
        ∑ y, w y * f y x0 - ∑ y, w y * f y y + ∑ y, w y * (1 - f y x0) * e0 y + ∑ y, w y * f y x0 * e1 y := by
      dsimp [g]
      simpa using h_vertex
    rw [hLHS]
    have h_comp := AdversarialBco.compensation w (fun y => f y x0) q hw hw1 (fun y => hf y x0) hq
    -- h_comp : ∑ y, w y * f y x0 * log(...) + ∑ y, w y * (1 - f y x0) * log(...) = I + KL
    -- where I = ∑ y, w y * (f y x0 * log(f y x0 / F) + (1 - f y x0) * log((1 - f y x0) / (1 - F)))
    -- and   KL = ∑ y, w y * log(w y / q y)
    have h_bound : ∑ y, W0 y * e0 y + ∑ y, W1 y * e1 y ≤ -(∑ y, W0 y * Real.log (W0 y / ((1 - F) * q y)) +
        ∑ y, W1 y * Real.log (W1 y / (F * q y))) / η + δ / 2 := by
      have hsum := add_le_add he0 he1
      have hRHS : (-(∑ y, W0 y * Real.log (W0 y / ((1 - F) * q y))) / η + (1 - F) * (δ / 2)) +
          (-(∑ y, W1 y * Real.log (W1 y / (F * q y))) / η + F * (δ / 2)) =
          (-(∑ y, W0 y * Real.log (W0 y / ((1 - F) * q y)) +
            ∑ y, W1 y * Real.log (W1 y / (F * q y))) / η + δ / 2) := by
        ring
      rw [hRHS] at hsum
      exact hsum
    have h_comp_eq : (∑ y, W0 y * Real.log (W0 y / ((1 - F) * q y)) +
        ∑ y, W1 y * Real.log (W1 y / (F * q y))) =
        (∑ y, w y * (f y x0 * Real.log (f y x0 / F) + (1 - f y x0) * Real.log ((1 - f y x0) / (1 - F))) +
          ∑ y, w y * Real.log (w y / q y)) := by
      dsimp [W0, W1]
      simpa [F, add_comm] using h_comp
    rw [h_comp_eq] at h_bound
    set I := ∑ y, w y * (f y x0 * Real.log (f y x0 / F) + (1 - f y x0) * Real.log ((1 - f y x0) / (1 - F))) +
      ∑ y, w y * Real.log (w y / q y) with hI
    have hA_le : ∑ y, W0 y * e0 y + ∑ y, W1 y * e1 y ≤ -(I / η) + δ := by
      apply le_trans h_bound
      have hneg : -I / η = -(I / η) := by rw [neg_div]
      rw [hneg]
      have hhalf : δ / 2 ≤ δ := by linarith
      linarith
    have h_target : ∑ y, w y * f y x0 - ∑ y, w y * f y y + ∑ y, W0 y * e0 y + ∑ y, W1 y * e1 y ≤
        ∑ y, w y * f y x0 - I / η - ∑ y, w y * f y y + δ := by
      -- Goal: (F - S1) + A ≤ (F - S1) + (-I/η + δ)
      -- which follows from hA_le : A ≤ -(I/η) + δ
      have h := add_le_add_left hA_le (∑ y, w y * f y x0 - ∑ y, w y * f y y)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_div] using h
    simpa [W0, W1, hI] using h_target
  exact ⟨g, h_first, h_second⟩

open Finset in
theorem AdversarialBco.vertex_value_le {C : Type*} [Fintype C] [Nonempty C] (fbar I : C → ℝ) (KL s a0 β η : ℝ)
    (hI : ∀ x, 0 ≤ I x) (hKL : 0 ≤ KL) (hβ : 0 ≤ β) (hη : 0 < η) (ξ : C → ℝ) (hξ : ∀ x, 0 ≤ ξ x)
    (hξ1 : ∑ x, ξ x = 1) (hconv : ∑ x, ξ x * fbar x - s ≤ a0 + √(β * (∑ x, ξ x * I x) / 2)) :
    ∃ x0, fbar x0 - (I x0 + KL) / η - s ≤ a0 + η * β / 8 := by
  set V := fun x => fbar x - (I x + KL) / η - s with hV
  obtain ⟨x0, _, hx0_min⟩ := Finset.exists_min_image (Finset.univ : Finset C) V Finset.univ_nonempty
  refine ⟨x0, ?_⟩
  have h_min : V x0 ≤ ∑ x, ξ x * V x := by
    have h_inf := AdversarialBco.min_le_avg V ξ hξ hξ1
    have h_le : V x0 ≤ Finset.univ.inf' Finset.univ_nonempty V := by
      rw [Finset.le_inf'_iff]
      exact hx0_min
    linarith
  have h_sum_eq : ∑ x, ξ x * V x = (∑ x, ξ x * fbar x - s) - (∑ x, ξ x * I x + KL) / η := by
    dsimp [V]
    calc
      ∑ x, ξ x * (fbar x - (I x + KL) / η - s)
          = ∑ x, (ξ x * fbar x - ξ x * ((I x + KL) / η) - ξ x * s) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      _ = (∑ x, ξ x * fbar x) - (∑ x, ξ x * ((I x + KL) / η)) - (∑ x, ξ x * s) := by
        simp [Finset.sum_sub_distrib]
      _ = (∑ x, ξ x * fbar x) - ((∑ x, ξ x * (I x + KL)) / η) - (∑ x, ξ x * s) := by
        simp [Finset.sum_div, mul_div_assoc]
      _ = (∑ x, ξ x * fbar x) - ((∑ x, ξ x * I x + KL * (∑ x, ξ x)) / η) - (∑ x, ξ x * s) := by
        simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_comm]
      _ = (∑ x, ξ x * fbar x) - ((∑ x, ξ x * I x + KL * 1) / η) - (∑ x, ξ x * s) := by rw [hξ1]
      _ = (∑ x, ξ x * fbar x) - ((∑ x, ξ x * I x + KL) / η) - s := by
        rw [← Finset.sum_mul, hξ1, one_mul, mul_one]
      _ = (∑ x, ξ x * fbar x - s) - (∑ x, ξ x * I x + KL) / η := by ring
  have h_sum_nonneg : 0 ≤ (∑ x, ξ x * I x + KL) / η := by
    have h_sum : 0 ≤ ∑ x, ξ x * I x :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hξ x) (hI x)
    have h_nonneg : 0 ≤ ∑ x, ξ x * I x + KL := add_nonneg h_sum hKL
    exact div_nonneg h_nonneg (by linarith)
  have h_drop_KL : (∑ x, ξ x * fbar x - s) - (∑ x, ξ x * I x + KL) / η ≤
      (∑ x, ξ x * fbar x - s) - (∑ x, ξ x * I x) / η := by
    have hsum : (∑ x, ξ x * I x) ≤ (∑ x, ξ x * I x + KL) := by linarith
    have hdiv : (∑ x, ξ x * I x) / η ≤ (∑ x, ξ x * I x + KL) / η :=
      div_le_div_of_nonneg_right hsum (by linarith)
    linarith
  have h_apply_conv : (∑ x, ξ x * fbar x - s) - (∑ x, ξ x * I x) / η ≤
      a0 + √(β * (∑ x, ξ x * I x) / 2) - (∑ x, ξ x * I x) / η := by
    linarith
  have h_final : a0 + √(β * (∑ x, ξ x * I x) / 2) - (∑ x, ξ x * I x) / η ≤ a0 + η * β / 8 :=
    AdversarialBco.value_arith a0 β (∑ x, ξ x * I x) η hβ
      (Finset.sum_nonneg fun x _ => mul_nonneg (hξ x) (hI x)) hη
  linarith

theorem AdversarialBco.round_exists {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C] (η : ℝ) (hη : 0 < η)
    (q : C → ℝ) (hq : ∀ z, 0 < q z) (P : Set (C → ℝ)) (hPc : Convex ℝ P) (hPk : IsCompact P)
    (hPne : P.Nonempty) (c : ℝ)
    (hdual : ∀ w ∈ stdSimplex ℝ C, ∀ f : C → C → ℝ, (∀ y, f y ∈ P) →
      ∃ pg : (C → ℝ) × (C → Bool → C → ℝ), (pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)) ∧
        ∑ y, (w y * ∑ x, pg.2 x false y +
          ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * (w y * f y x)) < c) :
    ∃ pg : (C → ℝ) × (C → Bool → C → ℝ), (pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)) ∧
      ∀ y, ∀ f ∈ P, ∑ x, pg.1 x * f x - f y + ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y) < c := by
  set A : Set ((C → ℝ) × (C → C → ℝ)) := {wθ | wθ.1 ∈ stdSimplex ℝ C ∧ ∀ y, ∃ f ∈ P, wθ.2 y = wθ.1 y • f} with hA
  set Y : Set ((C → ℝ) × (C → Bool → C → ℝ)) := {pg | pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
    (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)} with hY
  set Φ : (C → ℝ) × (C → Bool → C → ℝ) → ((C → ℝ) × (C → C → ℝ)) → ℝ := fun pg wθ =>
    ∑ y, (wθ.1 y * ∑ x, pg.2 x false y +
      ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * wθ.2 y x) with hΦ
  have hAne : A.Nonempty := by
    obtain ⟨y0⟩ := ‹Nonempty C›
    have h_single : Pi.single y0 (1 : ℝ) ∈ stdSimplex ℝ C := by
      simpa using single_mem_stdSimplex ℝ (i := y0)
    obtain ⟨f, hf⟩ := hPne
    let w_single : C → ℝ := Pi.single y0 1
    have hw_single : w_single ∈ stdSimplex ℝ C := h_single
    refine ⟨(w_single, fun y => w_single y • f), ?_⟩
    refine ⟨hw_single, fun y => ?_⟩
    refine ⟨f, hf, ?_⟩
    simp [w_single]
  have hAc : Convex ℝ A := convex_advSet P hPc hPne
  have hAk : IsCompact A := isCompact_advSet P hPk
  have hYc : Convex ℝ Y := convex_Fq η hη q hq
  have hprops := phi_props A hAc Y hYc
  rcases hprops with ⟨hcont_all, hcave_all, hYcont_all, hvex_all⟩
  have hcont : ∀ pg ∈ Y, Continuous (Φ pg) := by
    intro pg hpg
    dsimp [Φ]
    exact hcont_all pg
  have hcave : ∀ pg ∈ Y, ConcaveOn ℝ A (Φ pg) := by
    intro pg hpg
    dsimp [Φ]
    exact hcave_all pg
  have hYcont : ∀ a ∈ A, ContinuousOn (fun pg => Φ pg a) Y := by
    intro a ha
    dsimp [Φ]
    exact (hYcont_all a).continuousOn
  have hvex : ∀ a ∈ A, ConvexOn ℝ Y (fun pg => Φ pg a) := by
    intro a ha
    dsimp [Φ]
    exact hvex_all a
  have h : ∀ a ∈ A, ∃ y ∈ Y, Φ y a < c := by
    intro a ha
    rcases ha with ⟨ha1, ha2⟩
    let f' : C → C → ℝ := fun y => Classical.choose (ha2 y)
    have hf' : ∀ y, f' y ∈ P := fun y => (Classical.choose_spec (ha2 y)).1
    have hf'_eq : ∀ y, a.2 y = a.1 y • f' y := fun y => (Classical.choose_spec (ha2 y)).2
    rcases hdual a.1 ha1 f' hf' with ⟨pg, hpgY, hpgΦ⟩
    refine ⟨pg, hpgY, ?_⟩
    dsimp [Φ]
    have hsum_eq : (∑ y, (a.1 y * ∑ x, pg.2 x false y +
        ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * a.2 y x)) =
        ∑ y, (a.1 y * ∑ x, pg.2 x false y +
          ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * (a.1 y * f' y x)) := by
      simp [hf'_eq]
    rw [hsum_eq]
    exact hpgΦ
  have hmm1 := mm1 A hAne hAc hAk Y hYc Φ hcont hcave hYcont hvex c h
  rcases hmm1 with ⟨pg, hpgY, hpg⟩
  refine ⟨pg, hpgY, ?_⟩
  intro y f hf
  let w0 : C → ℝ := Pi.single y 1
  have hw0_std : w0 ∈ stdSimplex ℝ C := by
    simpa [w0] using single_mem_stdSimplex ℝ (i := y)
  have ha0_mem : (w0, fun y' => w0 y' • f) ∈ A := by
    refine ⟨hw0_std, fun y' => ?_⟩
    refine ⟨f, hf, ?_⟩
    simp [w0]
  have hΦa0 := hpg (w0, fun y' => w0 y' • f) ha0_mem
  dsimp [Φ] at hΦa0
  -- hΦa0 : ∑ y, (w0 y * ∑ x, pg.2 x false y + ∑ x, ((pg.1 x - if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * (w0 y * f x)) < c
  have hΦa0_eq : (∑ y', (w0 y' * ∑ x, pg.2 x false y' +
      ∑ x, (pg.1 x - (if x = y' then 1 else 0) + pg.2 x true y' - pg.2 x false y') * (w0 y' * f x))) =
      ∑ y', w0 y' * (∑ x, pg.1 x * f x - f y' + ∑ x, ((1 - f x) * pg.2 x false y' + f x * pg.2 x true y')) := by
    have := omega_mix pg.1 pg.2 w0 (fun _ x => f x)
    simpa using this
  have hΦa0_eq2 : (∑ y', w0 y' * (∑ x, pg.1 x * f x - f y' + ∑ x, ((1 - f x) * pg.2 x false y' + f x * pg.2 x true y'))) =
      (∑ x, pg.1 x * f x - f y + ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y)) := by
    simp [w0, Pi.single_apply]
  have hsum_eq : (∑ y', (w0 y' * ∑ x, pg.2 x false y' +
      ∑ x, (pg.1 x - (if x = y' then 1 else 0) + pg.2 x true y' - pg.2 x false y') * (w0 y' * f x))) =
      (∑ x, pg.1 x * f x - f y + ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y)) := by
    rw [hΦa0_eq, hΦa0_eq2]
  rw [hsum_eq] at hΦa0
  exact hΦa0

theorem AdversarialBco.pinsker_var {Y : Type*} [Fintype Y] (w a : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1)
    (ha : ∀ y, a y ∈ Set.Icc (0 : ℝ) 1) :
    ∑ y, w y * ((∑ y', w y' * a y') - a y) ^ 2 ≤
      (∑ y, w y * (a y * Real.log (a y / ∑ y', w y' * a y') +
        (1 - a y) * Real.log ((1 - a y) / (1 - ∑ y', w y' * a y')))) / 2 := by
  set abar := ∑ y', w y' * a y' with habar
  have ha_mem (y : Y) : a y ∈ Set.Icc (0 : ℝ) 1 := ha y
  have ha_lo (y : Y) : 0 ≤ a y := (ha_mem y).1
  have ha_hi (y : Y) : a y ≤ 1 := (ha_mem y).2
  have habar_nonneg : 0 ≤ abar := by
    rw [habar]
    apply Finset.sum_nonneg
    intro y' _
    exact mul_nonneg (hw y') (ha_lo y')
  have habar_le_one : abar ≤ 1 := by
    rw [habar]
    calc
      ∑ y', w y' * a y' ≤ ∑ y', w y' * 1 := by
        apply Finset.sum_le_sum
        intro y' _
        have ha_hi' := ha_hi y'
        exact mul_le_mul_of_nonneg_left ha_hi' (hw y')
      _ = ∑ y', w y' := by simp
      _ = 1 := hw1
  have habar_mem : abar ∈ Set.Icc (0 : ℝ) 1 := ⟨habar_nonneg, habar_le_one⟩
  have h_termwise (y : Y) : w y * (abar - a y) ^ 2 ≤
      w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar))) / 2 := by
    by_cases hwy : w y = 0
    · simp [hwy]
    · have hwy_pos : 0 < w y := by
        by_contra! hle
        have heq : w y = 0 := le_antisymm hle (hw y)
        exact hwy heq
      have h0 : abar = 0 → a y = 0 := by
        intro h_abar_zero
        have h_nonneg : ∀ y', 0 ≤ w y' * a y' := by
          intro y'
          exact mul_nonneg (hw y') (ha_lo y')
        have h_sum_zero : (∑ y', w y' * a y') = 0 := h_abar_zero
        have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (λ y' _ => h_nonneg y')).mp h_sum_zero
        have h_self_zero := h_all_zero y (Finset.mem_univ y)
        nlinarith
      have h1 : abar = 1 → a y = 1 := by
        intro h_abar_one
        have h_diff_nonneg : ∀ y', 0 ≤ w y' * (1 - a y') := by
          intro y'
          nlinarith [hw y', ha_hi y']
        have h_sum_w : (∑ y', w y') = 1 := hw1
        have h_sum_one : (∑ y', w y' * a y') = 1 := h_abar_one
        have h_diff_sum_zero : (∑ y', w y' * (1 - a y')) = 0 := by
          calc
            (∑ y', w y' * (1 - a y')) = (∑ y', (w y' - w y' * a y')) := by
              apply Finset.sum_congr rfl
              intro y' _
              ring
            _ = (∑ y', w y') - (∑ y', w y' * a y') := by
              rw [Finset.sum_sub_distrib]
            _ = 1 - 1 := by rw [h_sum_w, h_sum_one]
            _ = 0 := by ring
        have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (λ y' _ => h_diff_nonneg y')).mp h_diff_sum_zero
        have h_self_zero := h_all_zero y (Finset.mem_univ y)
        nlinarith
      have h_pin := pinsker_bern (a y) abar (ha_mem y) habar_mem h0 h1
      calc
        w y * (abar - a y) ^ 2 = w y * (a y - abar) ^ 2 := by ring
        _ ≤ w y * ((a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar))) / 2) :=
          mul_le_mul_of_nonneg_left h_pin (hw y)
        _ = w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar))) / 2 := by ring
  calc
    ∑ y, w y * ((∑ y', w y' * a y') - a y) ^ 2 = ∑ y, w y * (abar - a y) ^ 2 := by simp [habar]
    _ ≤ ∑ y, (w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar))) / 2) :=
      Finset.sum_le_sum (λ y _ => h_termwise y)
    _ = (∑ y, w y * (a y * Real.log (a y / abar) + (1 - a y) * Real.log ((1 - a y) / (1 - abar)))) / 2 := by
      simp [Finset.sum_div]

open Set Finset in
theorem AdversarialBco.clamp_extension_PL {d : ℕ} {C : Type*} [Fintype C] [Nonempty C]
    (pt : C → EuclideanSpace ℝ (Fin d)) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) (v : C → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) (s : C → EuclideanSpace ℝ (Fin d)) (hs : ∀ i, ‖s i‖ ≤ L)
    (hvs : ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j) (J : Set (EuclideanSpace ℝ (Fin d))) (hJc : Convex ℝ J)
    (hJ : ∀ z ∈ J, ∃ i, ‖z - pt i‖ ≤ ε) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ConvexOn ℝ J h ∧ Continuous h ∧
      (∀ z z', |h z - h z'| ≤ L * ‖z - z'‖) ∧ (∀ j, h (pt j) = v j) ∧
      ∀ z, h z ∈ Set.Icc (-(L * ε)) (1 + L * ε) := by
  let h0 := fun z => Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i))
  have h0_prop := extension_PL pt L ε v hv s hs hvs J hJ
  rcases h0_prop with ⟨h0_conv, h0_lip, h0_pt, h0_range⟩
  -- Unfold h0 in the hypotheses
  dsimp [h0] at h0_conv h0_lip h0_pt h0_range
  -- h0_conv : ConvexOn ℝ Set.univ h0
  -- h0_lip : ∀ z z', |h0 z - h0 z'| ≤ L * ‖z - z'‖
  -- h0_pt : ∀ j, h0 (pt j) = v j
  -- h0_range : ∀ z ∈ J, h0 z ∈ Set.Icc (-(L * ε)) (1 + L * ε)
  have hLε_nonneg : 0 ≤ L * ε := mul_nonneg hL hε
  have h1Lε_nonneg : 0 ≤ 1 + L * ε := by linarith
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun z => max (-(L * ε)) (min (h0 z) (1 + L * ε)) with hh
  have h_eq_on_J : ∀ z ∈ J, h z = h0 z := by
    intro z hz
    have hz_range := h0_range z hz
    rcases hz_range with ⟨hz_low, hz_high⟩
    -- hz_low : -(L * ε) ≤ (Finset.univ.sup' ...), hz_high : (Finset.univ.sup' ...) ≤ 1 + L * ε
    dsimp [h, h0]
    have h_min : min (Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i))) (1 + L * ε) =
        Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i)) :=
      min_eq_left hz_high
    have h_max : max (-(L * ε)) (Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i))) =
        Finset.univ.sup' Finset.univ_nonempty (fun i => v i + inner ℝ (s i) (z - pt i)) := by
      -- max a b = a if b ≤ a. Here hz_low : -(L*ε) ≤ sup, so max (sup) (-(L*ε)) = sup
      -- But we have max (-(L*ε)) (sup). Use commutativity.
      rw [max_comm, max_eq_left hz_low]
    rw [h_min, h_max]
  have h_conv : ConvexOn ℝ J h := by
    have h0_conv_J : ConvexOn ℝ J h0 :=
      h0_conv.subset (subset_univ _) hJc
    -- h = h0 on J
    apply h0_conv_J.congr
    intro z hz
    exact (h_eq_on_J z hz).symm
  have h_cont : Continuous h := by
    have h0_cont : Continuous h0 := by
      have h0_lip' : LipschitzWith (Real.toNNReal L) h0 :=
        LipschitzWith.of_dist_le' fun z z' => by
          rw [Real.dist_eq, dist_eq_norm]
          -- Need: |h0 z - h0 z'| ≤ (Real.toNNReal L : ℝ) * ‖z - z'‖
          -- We have: |h0 z - h0 z'| ≤ L * ‖z - z'‖
          -- Since Real.toNNReal L = L (because L ≥ 0)
          simpa [Real.coe_toNNReal L hL] using h0_lip z z'
      exact h0_lip'.continuous
    refine Continuous.max continuous_const ?_
    refine Continuous.min h0_cont continuous_const
  have h_lip : ∀ z z', |h z - h z'| ≤ L * ‖z - z'‖ := by
    intro z z'
    dsimp [h]
    -- We need: |max a (min (h0 z) c) - max a (min (h0 z') c)| ≤ L * ‖z - z'‖
    -- where a = -(L*ε), c = 1+L*ε
    -- First, |max a u - max a v| ≤ |u - v|
    -- Then |min u c - min v c| ≤ |u - v|
    -- So |max a (min x c) - max a (min y c)| ≤ |min x c - min y c| ≤ |x - y|
    -- Then use h0_lip
    have h1 : |max (-(L * ε)) (min (h0 z) (1 + L * ε)) - max (-(L * ε)) (min (h0 z') (1 + L * ε))| ≤
        |min (h0 z) (1 + L * ε) - min (h0 z') (1 + L * ε)| := by
      -- Use abs_max_sub_max_le_abs with swapped arguments
      -- max a x = max x a, so we can apply abs_max_sub_max_le_abs with a := min (h0 z) (1+L*ε), b := min (h0 z') (1+L*ε), c := -(L*ε)
      have h := abs_max_sub_max_le_abs (min (h0 z) (1 + L * ε)) (min (h0 z') (1 + L * ε)) (-(L * ε))
      -- h : |max (min (h0 z) (1+L*ε)) (-(L*ε)) - max (min (h0 z') (1+L*ε)) (-(L*ε))| ≤ |min (h0 z) (1+L*ε) - min (h0 z') (1+L*ε)|
      -- But max is commutative, so we can rewrite
      simpa [max_comm] using h
    have h2 : |min (h0 z) (1 + L * ε) - min (h0 z') (1 + L * ε)| ≤ |h0 z - h0 z'| := by
      -- Use abs_min_sub_min_le_max with appropriate arguments
      have h_min := abs_min_sub_min_le_max (h0 z) (1 + L * ε) (h0 z') (1 + L * ε)
      -- h_min : |min (h0 z) (1+L*ε) - min (h0 z') (1+L*ε)| ≤ max |h0 z - h0 z'| |(1+L*ε) - (1+L*ε)|
      -- = max |h0 z - h0 z'| 0 = |h0 z - h0 z'|
      simpa [sub_self] using h_min
    have h3 : |h0 z - h0 z'| ≤ L * ‖z - z'‖ := h0_lip z z'
    linarith
  have h_pt : ∀ j, h (pt j) = v j := by
    intro j
    have h0_pt_j : h0 (pt j) = v j := h0_pt j
    have hvj_low : 0 ≤ v j := (hv j).1
    have hvj_high : v j ≤ 1 := (hv j).2
    have hLε : 0 ≤ L * ε := mul_nonneg hL hε
    dsimp [h]
    rw [h0_pt_j]
    -- Now we need: max (-(L*ε)) (min (v j) (1+L*ε)) = v j
    have h_min : min (v j) (1 + L * ε) = v j := min_eq_left (by linarith)
    rw [h_min]
    -- max (-(L*ε)) (v j) = v j
    have h_max : max (-(L * ε)) (v j) = v j := max_eq_right (by linarith)
    rw [h_max]
  have h_range : ∀ z, h z ∈ Set.Icc (-(L * ε)) (1 + L * ε) := by
    intro z
    dsimp [h]
    constructor
    · -- -(L * ε) ≤ max (-(L * ε)) (min (h0 z) (1 + L * ε))
      exact le_max_left _ _
    · -- max (-(L * ε)) (min (h0 z) (1 + L * ε)) ≤ 1 + L * ε
      apply max_le ?_ ?_
      · -- -(L * ε) ≤ 1 + L * ε
        have hLε : 0 ≤ L * ε := mul_nonneg hL hε
        linarith
      · -- min (h0 z) (1 + L * ε) ≤ 1 + L * ε
        exact min_le_right _ _
  exact ⟨h, h_conv, h_cont, h_lip, h_pt, h_range⟩

/-- Lemma 7.9 for the coin version. The law `ρ` that (H) gives for the
clamped extensions (`clamp_extension_PL`, values in `[-L ε, 1 + L ε]`, `lemma_H_shift`), read through the
projection `pr` onto the net, is a law `ξ` on the net whose excess over the comparator values `f y y` is at most
`(1 + 2 L ε) α + L ε (1 + √β) + (β I / 2)^{1/2}`, with `I` the information of the coins: Lemma 5.2 for the
move to the net (`integral_comp_le_add`, `sqrt_V_le_bdd`) and Pinsker for each net point (`pinsker_var`). -/
theorem AdversarialBco.conv_coin {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] (J : Set (AdversarialBco.E d))
    (hJc : Convex ℝ J) (hJm : MeasurableSet J) (L ε α β : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hH : AdversarialBco.HypH J L 0 1 α β) (pt : C → AdversarialBco.E d) (hpt : ∀ x, pt x ∈ J)
    (pr : AdversarialBco.E d → C) (hprm : ∀ x, MeasurableSet (pr ⁻¹' {x})) (hpr : ∀ z ∈ J, ‖z - pt (pr z)‖ ≤ ε)
    (w : C → ℝ) (hw : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) (f : C → C → ℝ)
    (hf01 : ∀ y x, f y x ∈ Set.Icc (0 : ℝ) 1) (s : C → C → AdversarialBco.E d) (hs : ∀ y x, ‖s y x‖ ≤ L)
    (hfs : ∀ y i j, f y i + inner ℝ (s y i) (pt j - pt i) ≤ f y j) :
    ∃ ξ : C → ℝ, (∀ x, 0 ≤ ξ x) ∧ ∑ x, ξ x = 1 ∧
      ∑ x, ξ x * (∑ y, w y * f y x) - ∑ y, w y * f y y ≤
        (1 + 2 * L * ε) * α + L * ε * (1 + √β) +
          √(β * (∑ x, ξ x * ∑ y, w y * (f y x * Real.log (f y x / ∑ y', w y' * f y' x) +
              (1 - f y x) * Real.log ((1 - f y x) / (1 - ∑ y', w y' * f y' x)))) / 2) := by
  classical
  -- the clamped extensions
  have hcov : ∀ z ∈ J, ∃ i, ‖z - pt i‖ ≤ ε := fun z hz => ⟨pr z, hpr z hz⟩
  choose h hhc hhcont hhL hhpt hhr using fun y =>
    AdversarialBco.clamp_extension_PL pt L ε hL hε (f y) (hf01 y) (s y) (hs y) (hfs y) J hJc hcov
  -- reindex by Fin k
  set k := Fintype.card C
  let e : C ≃ Fin k := Fintype.equivFin C
  let w' : Fin k → ℝ := fun i => w (e.symm i)
  let F : Fin k → AdversarialBco.E d → ℝ := fun i => h (e.symm i)
  have hw' : ∀ i, 0 ≤ w' i := fun i => hw _
  have hw'1 : ∑ i, w' i = 1 := by
    rw [← hw1]; exact Equiv.sum_comp e.symm w
  have hsum : ∀ G : C → ℝ, ∑ i, w' i * G (e.symm i) = ∑ y, w y * G y := fun G =>
    Equiv.sum_comp e.symm (fun y => w y * G y)
  have hF : ∀ i, ConvexOn ℝ J (F i) ∧ (∀ x ∈ J, ∀ y ∈ J, |F i x - F i y| ≤ L * dist x y) ∧
      ∀ x ∈ J, F i x ∈ Set.Icc (-(L * ε)) (1 + L * ε) := by
    intro i
    refine ⟨hhc _, fun x _ y _ => ?_, fun x _ => hhr _ x⟩
    rw [dist_eq_norm]; exact hhL _ x y
  obtain ⟨ρ, hρ, hρJ, hρi, hineq⟩ :=
    AdversarialBco.lemma_H_shift J L ε α β hL hε hβ hH k w' F hw' hw'1 hF
  -- measurability of functions of the net index
  have hmeasC : ∀ {β' : Type} [MeasurableSpace β'] (G : C → β'), Measurable fun z => G (pr z) := by
    intro β' _ G S _
    have : (fun z => G (pr z)) ⁻¹' S = ⋃ x ∈ {x | G x ∈ S}, pr ⁻¹' {x} := by
      ext z; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun x _ => hprm x
  -- the projection onto the net, the identity off J
  let q : AdversarialBco.E d → AdversarialBco.E d := fun z => if z ∈ J then pt (pr z) else z
  have hqm : Measurable q := Measurable.piecewise hJm (hmeasC pt) measurable_id
  have hq : ∀ z, dist (q z) z ≤ ε := by
    intro z
    by_cases hz : z ∈ J
    · simp only [q, hz, ↓reduceIte]; rw [dist_eq_norm, norm_sub_rev]; exact hpr z hz
    · simp only [q, hz, ↓reduceIte, dist_self]; exact hε
  have hqae : ∀ᵐ z ∂ρ, q z = pt (pr z) := by
    refine measure_mono_null (fun z hz => ?_) hρJ
    by_contra hzJ
    have hzJ' : z ∈ J := by simpa using hzJ
    exact hz (by simp only [q, hzJ', ↓reduceIte, Set.mem_ofPred_eq])
  -- the law of the net point
  let ξ : C → ℝ := fun x => ρ.real (pr ⁻¹' {x})
  have hξ0 : ∀ x, 0 ≤ ξ x := fun x => measureReal_nonneg
  have hint_net : ∀ G : C → ℝ, ∫ z, G (pr z) ∂ρ = ∑ x, ξ x * G x := fun G =>
    AdversarialBco.integral_comp_finite ρ pr hprm G
  have hξ1 : ∑ x, ξ x = 1 := by
    have := hint_net (fun _ => 1)
    simp only [mul_one, integral_const, smul_eq_mul, probReal_univ] at this
    exact this.symm
  refine ⟨ξ, hξ0, hξ1, ?_⟩
  -- the clamped extensions: bounds, measurability, integrability
  set M : ℝ := 1 + L * ε with hM
  have hLε : 0 ≤ L * ε := mul_nonneg hL hε
  have hMpos : 0 < M := by rw [hM]; linarith
  have hhb : ∀ y z, |h y z| ≤ M := by
    intro y z
    obtain ⟨h1, h2⟩ := hhr y z
    rw [abs_le]; constructor <;> linarith
  have hhm : ∀ y, Measurable (h y) := fun y => (hhcont y).measurable
  have hhi : ∀ y, Integrable (h y) ρ := fun y =>
    Integrable.of_bound (hhm y).aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hhb y z)
  -- the mean of the extensions
  let hbar : AdversarialBco.E d → ℝ := fun z => ∑ y, w y * h y z
  have hbar_eq : ∀ z, ∑ i, w' i * F i z = hbar z := fun z => hsum (fun y => h y z)
  have hbarL : ∀ z z', |hbar z - hbar z'| ≤ L * dist z z' := by
    intro z z'
    have : hbar z - hbar z' = ∑ y, w y * (h y z - h y z') := by
      simp only [hbar, mul_sub, Finset.sum_sub_distrib]
    rw [this, dist_eq_norm]
    calc |∑ y, w y * (h y z - h y z')| ≤ ∑ y, |w y * (h y z - h y z')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, w y * (L * ‖z - z'‖) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (hw y)]
          exact mul_le_mul_of_nonneg_left (hhL y z z') (hw y)
      _ = L * ‖z - z'‖ := by rw [← Finset.sum_mul, hw1, one_mul]
  have hbarm : Measurable hbar := Finset.measurable_sum _ fun y _ => (hhm y).const_mul _
  have hbari : Integrable hbar ρ := integrable_finsetSum _ fun y _ => (hhi y).const_mul _
  have hbarqi : Integrable (fun z => hbar (q z)) ρ := by
    refine Integrable.of_bound (hbarm.comp hqm).aestronglyMeasurable M (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    calc |hbar (q z)| ≤ ∑ y, |w y * h y (q z)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, w y * M := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (hw y)]
          exact mul_le_mul_of_nonneg_left (hhb y _) (hw y)
      _ = M := by rw [← Finset.sum_mul, hw1, one_mul]
  have hmean : ∑ x, ξ x * (∑ y, w y * f y x) ≤ ∫ z, hbar z ∂ρ + L * ε := by
    have h1 := AdversarialBco.integral_comp_le_add ρ hbar q L ε hL hq hbarL hbari hbarqi
    have h2 : ∫ z, hbar (q z) ∂ρ = ∑ x, ξ x * (∑ y, w y * f y x) := by
      rw [integral_congr_ae (hqae.mono fun z hz => by rw [hz])]
      rw [hint_net (fun x => hbar (pt x))]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hbar, hhpt]
    linarith
  -- the comparator term
  have hcomp : ∑ i, w' i * sInf (F i '' J) ≤ ∑ y, w y * f y y := by
    rw [hsum (fun y => sInf (h y '' J))]
    refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hw y)
    rw [← hhpt y y]
    refine csInf_le ⟨-(L * ε), ?_⟩ ⟨pt y, hpt y, rfl⟩
    rintro _ ⟨z, _, rfl⟩
    exact (hhr y z).1
  have hint_mean : ∫ z, ∑ i, w' i * F i z ∂ρ = ∫ z, hbar z ∂ρ :=
    integral_congr_ae (Filter.Eventually.of_forall hbar_eq)
  -- the variance term
  set V : AdversarialBco.E d → ℝ := fun z => ∑ i, w' i * ((∑ j, w' j * F j z) - F i z) ^ 2 with hV
  have hFm : ∀ i, Measurable (F i) := fun i => hhm _
  have hFb : ∀ i z, |F i z| ≤ M := fun i z => hhb _ z
  have hFq : ∀ i z, |F i z - F i (q z)| ≤ L * ε := by
    intro i z
    calc |F i z - F i (q z)| ≤ L * ‖z - q z‖ := hhL _ z (q z)
      _ ≤ L * ε := by
          refine mul_le_mul_of_nonneg_left ?_ hL
          rw [← dist_eq_norm, dist_comm]; exact hq z
  have hsqrt := AdversarialBco.sqrt_V_le_bdd ρ w' hw' hw'1 F hFm M hMpos hFb q hqm (L * ε) hFq
  have hVq : ∫ z, V (q z) ∂ρ = ∑ x, ξ x * V (pt x) := by
    rw [integral_congr_ae (hqae.mono fun z hz => by rw [hz])]
    exact hint_net (fun x => V (pt x))
  have hVpt : ∀ x, V (pt x) ≤ (∑ y, w y * (f y x * Real.log (f y x / ∑ y', w y' * f y' x) +
      (1 - f y x) * Real.log ((1 - f y x) / (1 - ∑ y', w y' * f y' x)))) / 2 := by
    intro x
    have hV' : V (pt x) = ∑ y, w y * ((∑ y', w y' * f y' x) - f y x) ^ 2 := by
      simp only [hV, F, hhpt]
      rw [hsum (fun y' => f y' x)]
      exact hsum (fun y => ((∑ y', w y' * f y' x) - f y x) ^ 2)
    rw [hV']
    exact AdversarialBco.pinsker_var w (fun y => f y x) hw hw1 (fun y => hf01 y x)
  -- combination
  set S : ℝ := ∑ x, ξ x * ∑ y, w y * (f y x * Real.log (f y x / ∑ y', w y' * f y' x) +
      (1 - f y x) * Real.log ((1 - f y x) / (1 - ∑ y', w y' * f y' x))) with hS
  have hVq_le : ∫ z, V (q z) ∂ρ ≤ S / 2 := by
    rw [hVq, hS, Finset.sum_div]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hVpt x) (hξ0 x)
  have h1 : √(∫ z, V z ∂ρ) ≤ √(S / 2) + L * ε :=
    hsqrt.trans (add_le_add (Real.sqrt_le_sqrt hVq_le) le_rfl)
  have h2 : √(β * ∫ z, V z ∂ρ) ≤ √(β * S / 2) + √β * (L * ε) := by
    rw [Real.sqrt_mul hβ, mul_div_assoc, Real.sqrt_mul hβ]
    calc √β * √(∫ z, V z ∂ρ) ≤ √β * (√(S / 2) + L * ε) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = √β * √(S / 2) + √β * (L * ε) := by ring
  have h3 : L * ε * (1 + √β) = L * ε + √β * (L * ε) := by ring
  rw [h3]
  have h4 : ∫ z, ∑ i, w' i * F i z ∂ρ - ∑ i, w' i * sInf (F i '' J) ≤
      (1 + 2 * L * ε) * α + √(β * ∫ z, V z ∂ρ) := hineq
  linarith [h4, hmean, hcomp, hint_mean, h2]


theorem AdversarialBco.ewQ_pos_sum {T C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (est : (C → ℝ) → T → C → ℝ)
    (t : ℕ) (h : Fin t → T) :
    (∀ z, 0 < AdversarialBco.ewQ η est t h z) ∧ ∑ z, AdversarialBco.ewQ η est t h z = 1 := by
  induction' t with t ih
  · -- t = 0
    have card_pos : 0 < Fintype.card C := Fintype.card_pos
    have hpos_div : 0 < (1 : ℝ) / (Fintype.card C : ℝ) := by
      refine div_pos (by norm_num) (mod_cast card_pos)
    constructor
    · intro z
      simpa [AdversarialBco.ewQ] using hpos_div
    · rw [AdversarialBco.ewQ]
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · -- t + 1
    rename_i t ih
    let q := AdversarialBco.ewQ η est t (Fin.init h)
    let e (z : C) := Real.exp (-η * est q (h (Fin.last t)) z)
    have hq_pos : ∀ z, 0 < q z := fun z => (ih (Fin.init h)).1 z
    have he_pos : ∀ z, 0 < e z := fun z => Real.exp_pos _
    have hsum_pos : 0 < ∑ z : C, q z * e z := by
      refine Finset.sum_pos (fun z _ => mul_pos (hq_pos z) (he_pos z)) ?_
      exact Finset.univ_nonempty
    have hsum_ne_zero : ∑ z : C, q z * e z ≠ 0 := by linarith
    have hpos : ∀ z, 0 < q z * e z / ∑ z' : C, q z' * e z' := by
      intro z
      exact div_pos (mul_pos (hq_pos z) (he_pos z)) hsum_pos
    have hsum_eq_one : ∑ z : C, q z * e z / ∑ z' : C, q z' * e z' = 1 := by
      calc
        ∑ z : C, q z * e z / ∑ z' : C, q z' * e z' = (∑ z : C, q z * e z) / (∑ z' : C, q z' * e z') := by
          simp [Finset.sum_div]
        _ = 1 := div_self hsum_ne_zero
    constructor
    · intro z
      simpa [AdversarialBco.ewQ, q, e] using hpos z
    · simpa [AdversarialBco.ewQ, q, e] using hsum_eq_one

theorem AdversarialBco.ew_path {T C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (hη : 0 < η)
    (est : (C → ℝ) → T → C → ℝ) (n : ℕ) (h : Fin n → T) (y : C) :
    -Real.log (Fintype.card C) / η ≤
      ∑ t : Fin n, (est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
        (1 / η) * Real.log (∑ z, AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
          Real.exp (-η * est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z))) := by
  -- Helper: Q k hk z = ewQ at k with history given by h cast via proof hk
  let Q (k : ℕ) (hk : k ≤ n) (z : C) : ℝ :=
    AdversarialBco.ewQ η est k (fun i : Fin k => h (Fin.castLE hk i)) z
  -- q t z = ewQ at min t n with the truncated history
  set q := fun (t : ℕ) (z : C) =>
    if ht : t ≤ n then Q t ht z else Q n (Nat.le_refl n) z with hq_def
  -- ℓ t z = if t < n then est (q t) (h ⟨t, ht⟩) z else 0
  set ℓ := fun (t : ℕ) (z : C) =>
    if ht : t < n then est (q t) (h ⟨t, ht⟩) z else 0 with hℓ_def
  have hq0 : ∀ z, q 0 z = 1 / Fintype.card C := by
    intro z
    dsimp [q, Q]
    simp [AdversarialBco.ewQ]
  -- Lemma: Fin.castLE is independent of the proof argument
  have h_cast_eq {a b : ℕ} (h1 h2 : a ≤ b) (i : Fin a) : Fin.castLE h1 i = Fin.castLE h2 i := by
    ext; simp
  have hq : ∀ t z, q (t + 1) z = q t z * Real.exp (-η * ℓ t z) / ∑ z', q t z' * Real.exp (-η * ℓ t z') := by
    intro t z
    by_cases ht : t < n
    · have h_le_t : t ≤ n := Nat.le_of_lt ht
      have h_le_succ : t + 1 ≤ n := by omega
      have hq_t : ∀ z, q t z = Q t h_le_t z := by
        intro z; dsimp [q]; rw [dif_pos h_le_t]
      have hq_succ : ∀ z, q (t + 1) z = Q (t + 1) h_le_succ z := by
        intro z; dsimp [q]; rw [dif_pos h_le_succ]
      have hℓ_t : ∀ z, ℓ t z = est (q t) (h ⟨t, ht⟩) z := by
        intro z; dsimp [ℓ]; rw [dif_pos ht]
      rw [hq_succ z]
      dsimp [Q, AdversarialBco.ewQ]
      have h_init_eq : Fin.init (fun i : Fin (t + 1) => h (Fin.castLE h_le_succ i)) =
          fun i : Fin t => h (Fin.castLE h_le_t i) := by
        ext i
        have h_eq : Fin.castLE h_le_succ (Fin.castSucc i) = Fin.castLE h_le_t i := by
          ext; simp
        simp [Fin.init, h_eq]
      have h_last_eq : h (Fin.castLE h_le_succ (Fin.last t)) = h ⟨t, ht⟩ := by
        have h_eq : Fin.castLE h_le_succ (Fin.last t) = (⟨t, ht⟩ : Fin n) := by
          ext; simp
        rw [h_eq]
      rw [h_init_eq, h_last_eq]
      rw [hq_t z, hℓ_t z]
      have hq_t_fun : q t = Q t h_le_t := funext hq_t
      rw [hq_t_fun]
      -- Now the goal is definitionally true except for ℓ t z' vs est (Q t h_le_t) (h ⟨t, ht⟩) z' in the denominator
      -- Use simp with all hypotheses
      simp [hℓ_t, hq_t_fun, Q]
    · have h_not_lt : ¬ t < n := ht
      have hq_t : ∀ z, q t z = Q n (Nat.le_refl n) z := by
        intro z
        dsimp [q]
        by_cases h_le_t : t ≤ n
        · have h_eq : t = n := Nat.le_antisymm h_le_t (Nat.le_of_not_gt h_not_lt)
          rw [h_eq]
          rw [dif_pos (Nat.le_refl n)]
        · rw [dif_neg h_le_t]
      have hq_t_fun : q t = fun z => Q n (Nat.le_refl n) z := funext hq_t
      have hℓ_t : ∀ z, ℓ t z = 0 := by
        intro z; dsimp [ℓ]; rw [dif_neg h_not_lt]
      have hℓ_t_fun : ℓ t = fun _ => 0 := funext hℓ_t
      have hq_succ : ∀ z, q (t + 1) z = Q n (Nat.le_refl n) z := by
        intro z
        dsimp [q]
        have h_not_le_succ : ¬ t + 1 ≤ n := by omega
        rw [dif_neg h_not_le_succ]
      rw [hq_succ z, hq_t_fun, hℓ_t_fun]
      have h_sum_one : (∑ x : C, Q n (Nat.le_refl n) x) = 1 := by
        dsimp [Q]
        exact (AdversarialBco.ewQ_pos_sum η est n (fun i : Fin n => h (Fin.castLE (Nat.le_refl n) i))).2
      simp [Real.exp_zero, h_sum_one]
  have hineq := AdversarialBco.ew_recursive η hη n ℓ q hq0 hq y
  -- hineq : -Real.log (Fintype.card C) / η ≤ ∑ t ∈ Finset.range n, (ℓ t y + (1 / η) * Real.log (∑ z, q t z * Real.exp (-η * ℓ t z)))
  -- Define f : ℕ → ℝ for the target sum (zero for k ≥ n)
  let f (k : ℕ) : ℝ :=
    if hk : k < n then
      (est (AdversarialBco.ewQ η est k (fun i : Fin k => h (Fin.castLE (Nat.le_of_lt hk) i))) (h ⟨k, hk⟩) y +
       (1 / η) * Real.log (∑ z, AdversarialBco.ewQ η est k (fun i : Fin k => h (Fin.castLE (Nat.le_of_lt hk) i)) z *
         Real.exp (-η * est (AdversarialBco.ewQ η est k (fun i : Fin k => h (Fin.castLE (Nat.le_of_lt hk) i))) (h ⟨k, hk⟩) z)))
    else 0
  -- Relate the ew_recursive sum to the target sum via Fin.sum_univ_eq_sum_range
  have hsum_eq : (∑ t ∈ Finset.range n, (ℓ t y + (1 / η) * Real.log (∑ z', q t z' * Real.exp (-η * ℓ t z')))) =
      (∑ t : Fin n, f t) := by
    rw [Fin.sum_univ_eq_sum_range f n]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_lt_n : k < n := Finset.mem_range.1 hk
    dsimp [f]
    rw [dif_pos hk_lt_n]
    have h_le_k : k ≤ n := Nat.le_of_lt hk_lt_n
    dsimp [q, ℓ]
    simp [h_le_k, hk_lt_n, Q]
  -- Now combine
  have hgoal := hineq.trans_eq hsum_eq
  -- hgoal : -Real.log (Fintype.card C) / η ≤ ∑ t : Fin n, f t
  -- Relate f t to the target summand for t : Fin n
  have h_f_eq_target : (∑ t : Fin n, f t) = (∑ t : Fin n, (est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
      (1 / η) * Real.log (∑ z, AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
        Real.exp (-η * est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z)))) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    dsimp [f]
    have ht_lt_n : (t : ℕ) < n := t.2
    have h_fin_eq : (⟨(t : ℕ), ht_lt_n⟩ : Fin n) = t := by ext; simp
    simp [ht_lt_n]
  -- Now combine everything
  rw [h_f_eq_target] at hgoal
  exact hgoal

theorem AdversarialBco.br_step {C : Type*} [Fintype C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z)
    (p : C → ℝ) (g : C → Bool → C → ℝ)
    (hpg : p ∈ stdSimplex ℝ C ∧ ∀ x b, (0 < p x ∧ ∑ z, q z * Real.exp (-η * (g x b z / p x)) ≤ 1) ∨
      (p x = 0 ∧ ∀ z, 0 ≤ g x b z))
    (a : C → ℝ) (ha : ∀ x, a x ∈ Set.Icc (0 : ℝ) 1) (y : C) :
    ∑ τ : C × Bool, p τ.1 * (if τ.2 then a τ.1 else 1 - a τ.1) *
        (a τ.1 - a y + g τ.1 τ.2 y / p τ.1 +
          (1 / η) * Real.log (∑ z, q z * Real.exp (-η * (g τ.1 τ.2 z / p τ.1)))) ≤
      ∑ x, p x * a x - a y + ∑ x, ((1 - a x) * g x false y + a x * g x true y) := by
  rcases hpg with ⟨hpg_mem, hg_cases⟩
  have hpg_inter : p ∈ (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} := by
    simpa [stdSimplex_eq_inter ℝ C] using hpg_mem
  have hp_nonneg : ∀ x, 0 ≤ p x := λ x => (Set.mem_iInter.mp hpg_inter.1) x
  have hp_sum : ∑ x, p x = 1 := hpg_inter.2
  have hgpos : ∀ x b, 0 < p x → ∑ z, q z * Real.exp (-η * (g x b z / p x)) ≤ 1 := by
    intro x b hpos
    rcases hg_cases x b with (h | h)
    · exact h.2
    · exfalso; exact hpos.ne' h.1
  have hgzero : ∀ x b, p x = 0 → ∀ z, 0 ≤ g x b z := by
    intro x b hzero
    rcases hg_cases x b with (h | h)
    · exfalso; exact h.1.ne' hzero
    · exact h.2
  rw [Fintype.sum_prod_type]
  exact AdversarialBco.br_round η hη q hq p hp_nonneg hp_sum g hgpos hgzero a ha y

theorem AdversarialBco.obsHist_obs {d : ℕ} {T X : Type*} (R : (t : ℕ) → (Fin t → T) → X → ℝ → T)
    (A : (t : ℕ) → (Fin t → T) → X → AdversarialBco.E d) (f : ℕ → AdversarialBco.E d → ℝ) (ω : ℕ → X) (t : ℕ) :
    AdversarialBco.obsHist R t ω (AdversarialBco.obs f (fun s y => A s (AdversarialBco.obsHist R s ω y) (ω s)) t) =
      AdversarialBco.seqHist (fun s h u => R s h u (f s (A s h u))) t (fun i : Fin t => ω i) := by
  induction' t with t ih
  · ext i; exact Fin.elim0 i
  · set pol := fun (s : ℕ) (y : Fin s → ℝ) => A s (AdversarialBco.obsHist R s ω y) (ω s) with hpol
    set σ := fun (s : ℕ) (h : Fin s → T) (u : X) => R s h u (f s (A s h u)) with hσ
    simp only [AdversarialBco.obs, AdversarialBco.obsHist, AdversarialBco.seqHist, hpol, hσ]
    simp only [Fin.init_snoc, Fin.snoc_last]
    rw [← hpol, ← hσ]
    have h_init_eq : Fin.init (fun i : Fin (t + 1) => ω ↑i) = fun i : Fin t => ω ↑i := by
      ext i; simp [Fin.init, Fin.val_castSucc]
    simp [h_init_eq, Fin.val_last, ih]

theorem AdversarialBco.seqHist_castLE {T X : Type*} (σ : (t : ℕ) → (Fin t → T) → X → T) (n s : ℕ) (hs : s ≤ n)
    (ω : Fin n → X) :
    (fun i : Fin s => AdversarialBco.seqHist σ n ω (Fin.castLE hs i)) =
      AdversarialBco.seqHist σ s (fun i : Fin s => ω (Fin.castLE hs i)) := by
  induction' n with n ih
  · -- n = 0, so s = 0
    have hs0 : s = 0 := Nat.eq_zero_of_le_zero hs
    subst hs0
    funext i
    exact Fin.elim0 i
  · -- n = n+1
    by_cases hseq : s = n + 1
    · subst hseq
      funext i
      simp [AdversarialBco.seqHist]
    · have hs' : s ≤ n := by
        have hlt : s < n + 1 := Nat.lt_of_le_of_ne hs hseq
        exact Nat.le_of_lt_succ hlt
      funext i
      simp [AdversarialBco.seqHist]
      have hcast : (Fin.castLE hs i : Fin (n+1)) = Fin.castSucc (Fin.castLE hs' i) := by
        ext
        simp
      rw [hcast]
      rw [Fin.snoc_castSucc]
      have h_ih := ih hs' (Fin.init ω)
      calc
        seqHist σ n (Fin.init ω) (Fin.castLE hs' i)
            = (fun i => seqHist σ n (Fin.init ω) (Fin.castLE hs' i)) i := by simp
        _ = seqHist σ s (fun i => Fin.init ω (Fin.castLE hs' i)) i := by rw [h_ih]
        _ = seqHist σ s (fun i => ω (Fin.castLE hs i)) i := by
          simp [Fin.init]

theorem AdversarialBco.seqHist_apply {T X : Type*} (σ : (t : ℕ) → (Fin t → T) → X → T) (n : ℕ) (ω : Fin n → X)
    (t : Fin n) :
    AdversarialBco.seqHist σ n ω t =
      σ t (fun i : Fin t => AdversarialBco.seqHist σ n ω (Fin.castLE t.2.le i)) (ω t) := by
  let k := t.val
  have hk_lt_n : k < n := t.2
  have h_succ_le_n : k + 1 ≤ n := by omega
  -- Restrict seqHist to Fin (k+1)
  have h_restrict_succ : (fun i : Fin (k+1) => AdversarialBco.seqHist σ n ω (Fin.castLE h_succ_le_n i)) =
      AdversarialBco.seqHist σ (k+1) (fun i : Fin (k+1) => ω (Fin.castLE h_succ_le_n i)) :=
    AdversarialBco.seqHist_castLE σ n (k+1) h_succ_le_n ω
  -- Fin.castLE h_succ_le_n (Fin.last k) = t
  have h_cast_last : Fin.castLE h_succ_le_n (Fin.last k) = t := by
    apply Fin.ext
    dsimp [k]
  -- Relate Fin.castLE h_succ_le_n (Fin.castSucc i) to Fin.castLE t.2.le i
  have h_castSucc_eq : (fun i : Fin k => Fin.castLE h_succ_le_n (Fin.castSucc i)) =
      Fin.castLE t.2.le := by
    apply funext
    intro i
    apply Fin.ext
    simp [Fin.val_castLE]
  -- Relate Fin.init of the restricted ω to the restricted ω via t.2.le
  have h_init_eq : Fin.init (fun i : Fin (k+1) => ω (Fin.castLE h_succ_le_n i)) =
      (fun i : Fin k => ω (Fin.castLE t.2.le i)) := by
    ext i
    -- Fin.init f i = f (Fin.castSucc i)
    -- So LHS = ω (Fin.castLE h_succ_le_n (Fin.castSucc i))
    -- RHS = ω (Fin.castLE t.2.le i)
    -- These are equal by h_castSucc_eq
    simpa [Fin.init] using congrArg ω (congrFun h_castSucc_eq i)
  -- Relate seqHist at k via seqHist_castLE
  have h_restrict_k : (fun i : Fin k => AdversarialBco.seqHist σ n ω (Fin.castLE t.2.le i)) =
      AdversarialBco.seqHist σ k (fun i : Fin k => ω (Fin.castLE t.2.le i)) :=
    AdversarialBco.seqHist_castLE σ n k t.2.le ω
  calc
    AdversarialBco.seqHist σ n ω t
        = AdversarialBco.seqHist σ n ω (Fin.castLE h_succ_le_n (Fin.last k)) := by rw [h_cast_last]
    _ = (fun i : Fin (k+1) => AdversarialBco.seqHist σ n ω (Fin.castLE h_succ_le_n i)) (Fin.last k) := by simp
    _ = AdversarialBco.seqHist σ (k+1) (fun i : Fin (k+1) => ω (Fin.castLE h_succ_le_n i)) (Fin.last k) := by rw [h_restrict_succ]
    _ = σ k (AdversarialBco.seqHist σ k (Fin.init (fun i : Fin (k+1) => ω (Fin.castLE h_succ_le_n i))))
        (ω (Fin.castLE h_succ_le_n (Fin.last k))) := by
      simp [AdversarialBco.seqHist, Fin.snoc_last]
    _ = σ k (AdversarialBco.seqHist σ k (fun i : Fin k => ω (Fin.castLE t.2.le i)))
        (ω (Fin.castLE h_succ_le_n (Fin.last k))) := by rw [h_init_eq]
    _ = σ k (AdversarialBco.seqHist σ k (fun i : Fin k => ω (Fin.castLE t.2.le i))) (ω t) := by rw [h_cast_last]
    _ = σ k ((fun i : Fin k => AdversarialBco.seqHist σ n ω (Fin.castLE t.2.le i))) (ω t) := by rw [h_restrict_k]
    _ = σ t (fun i : Fin t => AdversarialBco.seqHist σ n ω (Fin.castLE t.2.le i)) (ω t) := by
      dsimp [k]

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.measurable_obsPolicy {T X Z Ω : Type*} [Finite T] [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace Ω] (R : (t : ℕ) → (Fin t → T) → X → ℝ → T)
    (hR : ∀ t h τ, MeasurableSet {p : X × ℝ | R t h p.1 p.2 = τ}) (A : (t : ℕ) → (Fin t → T) → X → Z)
    (hA : ∀ t h, Measurable (A t h)) (ext : Ω → ℕ → X) (hext : Measurable ext) (t : ℕ) :
    Measurable fun p : Ω × (Fin t → ℝ) => A t (AdversarialBco.obsHist R t (ext p.1) p.2) (ext p.1 t) := by
  refine AdversarialBco.measurable_of_finite_fibers (g := fun (p : Ω × (Fin t → ℝ)) => AdversarialBco.obsHist R t (ext p.1) p.2)
    (F := fun (h : Fin t → T) (p : Ω × (Fin t → ℝ)) => A t h (ext p.1 t)) ?_ ?_
  · intro h
    have h_meas : MeasurableSet {q : (ℕ → X) × (Fin t → ℝ) | AdversarialBco.obsHist R t q.1 q.2 = h} :=
      AdversarialBco.measurableSet_obsHist R hR t h
    have h_map : Measurable (fun p : Ω × (Fin t → ℝ) => (ext p.1, p.2)) :=
      (hext.comp measurable_fst).prodMk measurable_snd
    exact h_meas.preimage h_map
  · intro h
    have h_ext_t : Measurable (fun p : Ω × (Fin t → ℝ) => ext p.1 t) :=
      (measurable_pi_apply t).comp (hext.comp measurable_fst)
    exact (hA t h).comp h_ext_t

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.integrable_of_finite_fibers {α T : Type*} [MeasurableSpace α] [Finite T] (μ : Measure α)
    [IsFiniteMeasure μ] (g : α → T) (hg : ∀ τ, MeasurableSet (g ⁻¹' {τ})) (G : T → ℝ) :
    Integrable (fun a => G (g a)) μ := by
  classical
    haveI : Fintype T := Fintype.ofFinite T
    have h_int : ∀ τ, Integrable ((g ⁻¹' {τ}).indicator (fun _ => G τ)) μ := by
      intro τ
      have h_fin : μ (g ⁻¹' {τ}) ≠ ⊤ := measure_ne_top μ (g ⁻¹' {τ})
      have h_intOn : IntegrableOn (fun _ : α => G τ) (g ⁻¹' {τ}) μ :=
        integrableOn_const h_fin (by simp)
      exact h_intOn.integrable_indicator (hg τ)
    have h_eq : (fun a => G (g a)) = (fun a => ∑ τ ∈ Finset.univ, ((g ⁻¹' {τ}).indicator (fun _ => G τ)) a) := by
      ext a
      simp [Set.indicator, Finset.sum_ite_eq, Finset.mem_univ]
    rw [h_eq]
    refine integrable_finset_sum Finset.univ (fun τ hτ => ?_)
    exact h_int τ

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.measurable_extendSeed {X : Type*} [MeasurableSpace X] (n : ℕ) (x0 : X) :
    Measurable fun (ω : Fin n → X) (s : ℕ) => if hs : s < n then ω ⟨s, hs⟩ else x0 := by
  refine measurable_pi_iff.mpr ?_
  intro s
  by_cases hs : s < n
  · simp [hs]
    exact measurable_pi_apply (⟨s, hs⟩ : Fin n)
  · simp [hs]

theorem AdversarialBco.exists_net_fin {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJb : Bornology.IsBounded J)
    (hne : J.Nonempty) (D ε : ℝ) (hJD : Metric.diam J ≤ D) (hε : 0 < ε) :
    ∃ (m : ℕ) (pt : Fin (m + 1) → EuclideanSpace ℝ (Fin d)) (pr : EuclideanSpace ℝ (Fin d) → Fin (m + 1)),
      (∀ i, pt i ∈ J) ∧ (∀ i, MeasurableSet (pr ⁻¹' {i})) ∧ (∀ z ∈ J, dist z (pt (pr z)) < ε) ∧
        ((m + 1 : ℕ) : ℝ) ≤ (1 + 4 * D / ε) ^ d := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases AdversarialBco.exists_maximal_separated J hJb hne (ε / 2) hε2 with ⟨C, hCsub, hCnonempty, hCsep, hCcover, hCcard⟩
  have h_eq : 2 * Metric.diam J / (ε / 2) = 4 * Metric.diam J / ε := by
    field_simp [hε.ne.symm]
    ring
  have h_diam_nonneg : 0 ≤ Metric.diam J := Metric.diam_nonneg
  have h_div_nonneg : 0 ≤ 4 * Metric.diam J / ε := by
    have h : 0 ≤ 4 * Metric.diam J := mul_nonneg (by norm_num) h_diam_nonneg
    exact div_nonneg h (by linarith)
  have h_base_nonneg : 0 ≤ 1 + 4 * Metric.diam J / ε := by linarith
  have h_div : Metric.diam J / ε ≤ D / ε := div_le_div_of_nonneg_right hJD (by linarith)
  have h_base_le : 1 + 4 * Metric.diam J / ε ≤ 1 + 4 * D / ε := by
    have h_div' : 4 * Metric.diam J / ε ≤ 4 * D / ε := by
      calc
        4 * Metric.diam J / ε = 4 * (Metric.diam J / ε) := by ring
        _ ≤ 4 * (D / ε) := mul_le_mul_of_nonneg_left h_div (by norm_num)
        _ = 4 * D / ε := by ring
    linarith
  have h_card_le : (C.card : ℝ) ≤ (1 + 4 * D / ε) ^ d := by
    calc
      (C.card : ℝ) ≤ (1 + 2 * Metric.diam J / (ε / 2)) ^ d := hCcard
      _ = (1 + 4 * Metric.diam J / ε) ^ d := by simp [h_eq]
      _ ≤ (1 + 4 * D / ε) ^ d := pow_le_pow_left₀ h_base_nonneg h_base_le d
  set m := C.card - 1 with hm_def
  have hm : C.card = m + 1 := by
    have hpos : 0 < C.card := Finset.card_pos.mpr hCnonempty
    omega
  let e' := C.equivFin
  let e : (↥C) ≃ Fin (m + 1) := e'.trans (finCongr hm)
  let pt : Fin (m + 1) → EuclideanSpace ℝ (Fin d) := fun i => (e.symm i).val
  have hpt_mem : ∀ i, pt i ∈ J := by
    intro i
    have hmem : (e.symm i).val ∈ C := (e.symm i).property
    have : ((e.symm i).val : EuclideanSpace ℝ (Fin d)) ∈ (C : Set (EuclideanSpace ℝ (Fin d))) := by
      simpa using hmem
    exact hCsub this
  rcases AdversarialBco.exists_measurable_nearest C hCnonempty with ⟨pr0, hpr0_meas, hpr0_mem, hpr0_best⟩
  let pr : EuclideanSpace ℝ (Fin d) → Fin (m + 1) := fun z => e ⟨pr0 z, hpr0_mem z⟩
  have hpr_pt : ∀ z, pt (pr z) = pr0 z := by
    intro z
    dsimp [pr, pt]
    simp
  have hfibre_meas : ∀ i, MeasurableSet (pr ⁻¹' {i}) := by
    intro i
    have h_eq_set : pr ⁻¹' {i} = pr0 ⁻¹' {(e.symm i).val} := by
      ext z; constructor
      · intro hz
        have hz' : pr z = i := hz
        dsimp [pr] at hz'
        have h_symm : ⟨pr0 z, hpr0_mem z⟩ = e.symm i := by
          apply (e.eq_symm_apply).mpr
          exact hz'
        have h_eq_val : pr0 z = (e.symm i).val := by
          simpa using congr_arg Subtype.val h_symm
        simp [h_eq_val]
      · intro hz
        have hz' : pr0 z = (e.symm i).val := hz
        dsimp [pr]
        have h_subtype : ⟨pr0 z, hpr0_mem z⟩ = e.symm i := Subtype.ext hz'
        simpa [h_subtype] using e.apply_symm_apply i
    rw [h_eq_set]
    have h_singleton_meas : MeasurableSet ({(e.symm i).val} : Set (EuclideanSpace ℝ (Fin d))) :=
      measurableSet_singleton _
    exact hpr0_meas h_singleton_meas
  have h_cover : ∀ z ∈ J, dist z (pt (pr z)) < ε := by
    intro z hz
    rw [hpr_pt z]
    rcases hCcover z hz with ⟨c, hc, hc_dist⟩
    have h_best : dist z (pr0 z) ≤ dist z c := hpr0_best z c hc
    have h_lt : dist z (pr0 z) < ε := by linarith
    exact h_lt
  have h_card : ((m + 1 : ℕ) : ℝ) ≤ (1 + 4 * D / ε) ^ d := by
    have : ((m + 1 : ℕ) : ℝ) = (C.card : ℝ) := by
      simp [hm]
    rw [this]
    exact h_card_le
  refine ⟨m, pt, pr, hpt_mem, hfibre_meas, h_cover, h_card⟩

theorem AdversarialBco.comparator_net {d m : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hne : J.Nonempty)
    (pt : Fin (m + 1) → EuclideanSpace ℝ (Fin d)) (pr : EuclideanSpace ℝ (Fin d) → Fin (m + 1)) (ε : ℝ)
    (hcov : ∀ z ∈ J, dist z (pt (pr z)) < ε) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ t < n, ∀ x ∈ J, ∀ y ∈ J, |f t x - f t y| ≤ L * ‖x - y‖) (hpt : ∀ i, pt i ∈ J) :
    ∃ y, ∑ t ∈ Finset.range n, f t (pt y) ≤
      sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' J) + n * L * ε := by
  -- Pick y ∈ Fin (m + 1) that minimizes the cumulative loss over the net points
  obtain ⟨y, _, hy_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (m + 1)))
    (fun i => ∑ t ∈ Finset.range n, f t (pt i)) Finset.univ_nonempty
  -- The image of J under the cumulative loss is nonempty
  have h_image_nonempty : ((fun x => ∑ t ∈ Finset.range n, f t x) '' J).Nonempty :=
    hne.image (fun x => ∑ t ∈ Finset.range n, f t x)
  -- For each x ∈ J, we have ∑ f t (pt y) - n * L * ε ≤ ∑ f t x
  have h_lower_bound_on_J : ∀ x ∈ J, (∑ t ∈ Finset.range n, f t (pt y)) - (n : ℝ) * L * ε ≤
      ∑ t ∈ Finset.range n, f t x := by
    intro x hx
    set i := pr x with hi
    have hi_mem : pt i ∈ J := hpt i
    have hdist : dist x (pt i) < ε := hcov x hx
    have hnorm : ‖x - pt i‖ < ε := by
      rwa [dist_eq_norm] at hdist
    have hbound : ∀ t ∈ Finset.range n, f t (pt i) ≤ f t x + L * ε := by
      intro t ht
      have ht_n : t < n := Finset.mem_range.1 ht
      have h_abs : |f t x - f t (pt i)| ≤ L * ‖x - pt i‖ := hf t ht_n x hx (pt i) hi_mem
      have h_abs' := (abs_sub_le_iff.mp h_abs).right
      -- h_abs' : f t (pt i) - f t x ≤ L * ‖x - pt i‖
      have h_le : f t (pt i) - f t x ≤ L * ε := by
        apply le_trans h_abs' ?_
        have : ‖x - pt i‖ ≤ ε := le_of_lt hnorm
        nlinarith
      linarith
    calc
      (∑ t ∈ Finset.range n, f t (pt y)) - (n : ℝ) * L * ε
          ≤ (∑ t ∈ Finset.range n, f t (pt i)) - (n : ℝ) * L * ε := by
        -- because y minimizes the sum
        have h_sum : ∑ t ∈ Finset.range n, f t (pt y) ≤ ∑ t ∈ Finset.range n, f t (pt i) :=
          hy_min i (Finset.mem_univ i)
        nlinarith
      _ ≤ (∑ t ∈ Finset.range n, (f t x + L * ε)) - (n : ℝ) * L * ε := by
        -- using hbound for each term
        have h_sum_le : ∑ t ∈ Finset.range n, f t (pt i) ≤ ∑ t ∈ Finset.range n, (f t x + L * ε) :=
          Finset.sum_le_sum fun t ht => hbound t ht
        nlinarith
      _ = (∑ t ∈ Finset.range n, f t x) + (∑ t ∈ Finset.range n, (L * ε)) - (n : ℝ) * L * ε := by
        rw [Finset.sum_add_distrib]
      _ = (∑ t ∈ Finset.range n, f t x) + ((Finset.card (Finset.range n) : ℝ) * (L * ε)) - (n : ℝ) * L * ε := by
        simp [Finset.sum_const]
      _ = (∑ t ∈ Finset.range n, f t x) + ((n : ℝ) * (L * ε)) - (n : ℝ) * L * ε := by
        simp
      _ = ∑ t ∈ Finset.range n, f t x := by ring
  -- Convert to a lower bound on the image set
  have h_lower_bound : ∀ b ∈ ((fun x => ∑ t ∈ Finset.range n, f t x) '' J),
      (∑ t ∈ Finset.range n, f t (pt y)) - (n : ℝ) * L * ε ≤ b := by
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    exact h_lower_bound_on_J x hx
  -- Now ∑ f t (pt y) - n * L * ε is a lower bound of the image
  have h_le_csInf : (∑ t ∈ Finset.range n, f t (pt y)) - (n : ℝ) * L * ε ≤
      sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' J) :=
    le_csInf h_image_nonempty h_lower_bound
  -- Rearrange to get the desired inequality
  refine ⟨y, ?_⟩
  nlinarith

theorem AdversarialBco.PL_of_adm {d m : ℕ} (K : Set (AdversarialBco.E d)) (hK : Convex ℝ K) (n : ℕ) (hn : 1 ≤ n)
    (pt : Fin (m + 1) → AdversarialBco.E d) (hpt : ∀ i, pt i ∈ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K})
    (f : AdversarialBco.E d → ℝ) (hf : AdversarialBco.AdmLoss K f) :
    (∀ i, f (pt i) ∈ Set.Icc (0 : ℝ) 1) ∧ ∃ s : Fin (m + 1) → AdversarialBco.E d, (∀ i, ‖s i‖ ≤ n) ∧
      ∀ i j, f (pt i) + inner ℝ (s i) (pt j - pt i) ≤ f (pt j) := by
  set J := {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} with hJ_def
  have hptJ : ∀ i, pt i ∈ J := hpt
  have hJ_nonempty : J.Nonempty := ⟨pt 0, hptJ 0⟩
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact mod_cast Nat.zero_le n
  have hpos : 0 ≤ 1 / (n : ℝ) := div_nonneg (by norm_num) hn_nonneg
  have hJ_sub_K : J ⊆ K := by
    intro y hy
    have hy' : y ∈ Metric.closedBall y (1 / (n : ℝ)) := Metric.mem_closedBall_self hpos
    exact hy hy'
  have hJ_conv : Convex ℝ J := AdversarialBco.convex_inner K hK (1 / (n : ℝ))
  have hf_conv_on_J : ConvexOn ℝ J f :=
    hf.1.subset hJ_sub_K hJ_conv
  have hf_01_on_J : ∀ x ∈ J, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hf.2 x (hJ_sub_K hx)
  have hf_lip : LipschitzOnWith (n : NNReal) f J := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hbound : |f x - f y| ≤ (n : ℝ) * ‖x - y‖ :=
      AdversarialBco.abs_sub_le_inner K f hf.1 hf.2 n hn x y hx hy
    calc
      dist (f x) (f y) = |f x - f y| := Real.dist_eq _ _
      _ ≤ (n : ℝ) * ‖x - y‖ := hbound
      _ = ((n : NNReal) : ℝ) * dist x y := by
        simp [dist_eq_norm, NNReal.coe_natCast]
  rcases AdversarialBco.PL_of_convex pt J hJ_nonempty hptJ (n : NNReal) f hf_conv_on_J hf_lip hf_01_on_J with
    ⟨s, hs_norm, hs_sub⟩
  have h_first : ∀ i, f (pt i) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact hf_01_on_J (pt i) (hptJ i)
  refine ⟨h_first, ?_⟩
  refine ⟨s, ?_, hs_sub⟩
  intro i
  simpa [NNReal.coe_natCast] using hs_norm i

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.measurableSet_coinStep {k : ℕ} (S : (Fin k → ℝ) → ℝ → Fin k)
    (hSm : Measurable (fun q : (Fin k → ℝ) × ℝ => S q.1 q.2)) (p : Fin k → ℝ) (τ : Fin k × Bool) :
    MeasurableSet {uy : (ℝ × ℝ) × ℝ | (S p uy.1.1, decide (uy.1.2 ≤ max 0 (min 1 uy.2))) = τ} := by
  rcases τ with ⟨i, b⟩
  have h_eq : {uy : (ℝ × ℝ) × ℝ | (S p uy.1.1, decide (uy.1.2 ≤ max 0 (min 1 uy.2))) = (i, b)} =
      {uy | S p uy.1.1 = i} ∩ {uy | decide (uy.1.2 ≤ max 0 (min 1 uy.2)) = b} := by
    ext uy; simp [Prod.mk.injEq]
  rw [h_eq]
  refine MeasurableSet.inter ?_ ?_
  · -- {uy | S p uy.1.1 = i} is measurable
    have h_meas : Measurable (fun (uy : (ℝ × ℝ) × ℝ) => S p uy.1.1) :=
      hSm.comp (measurable_const.prodMk (measurable_fst.comp measurable_fst))
    exact h_meas (measurableSet_singleton i)
  · -- {uy | decide (uy.1.2 ≤ max 0 (min 1 uy.2)) = b} is measurable
    by_cases hb : b
    · -- b = true: the set is {uy | uy.1.2 ≤ max 0 (min 1 uy.2)}
      have h_set : {uy : (ℝ × ℝ) × ℝ | decide (uy.1.2 ≤ max 0 (min 1 uy.2)) = b} =
          {uy | uy.1.2 ≤ max 0 (min 1 uy.2)} := by
        ext uy; simp [hb]
      rw [h_set]
      exact measurableSet_le
        (measurable_snd.comp measurable_fst)
        ((measurable_const.max (measurable_const.min measurable_snd)))
    · -- b = false: the set is the complement
      have h_set : {uy : (ℝ × ℝ) × ℝ | decide (uy.1.2 ≤ max 0 (min 1 uy.2)) = b} =
          {uy | uy.1.2 ≤ max 0 (min 1 uy.2)}ᶜ := by
        ext uy; simp [hb]
      rw [h_set]
      exact (measurableSet_le
        (measurable_snd.comp measurable_fst)
        ((measurable_const.max (measurable_const.min measurable_snd)))).compl

open MeasureTheory in
open MeasureTheory in
theorem AdversarialBco.value_dual {d : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (J : Set (AdversarialBco.E d)) (hJc : Convex ℝ J) (hJm : MeasurableSet J) (L ε α β η tol : ℝ) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hβ : 0 ≤ β) (hη : 0 < η) (htol : 0 < tol) (hH : AdversarialBco.HypH J L 0 1 α β)
    (pt : C → AdversarialBco.E d) (hpt : ∀ x, pt x ∈ J) (pr : AdversarialBco.E d → C)
    (hprm : ∀ x, MeasurableSet (pr ⁻¹' {x})) (hpr : ∀ z ∈ J, ‖z - pt (pr z)‖ ≤ ε)
    (q : C → ℝ) (hq : ∀ z, 0 < q z) (hq1 : ∑ z, q z = 1) :
    ∀ w ∈ stdSimplex ℝ C, ∀ f : C → C → ℝ, (∀ y, f y ∈ {v : C → ℝ | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧
        ∃ s : C → AdversarialBco.E d, (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j}) →
      ∃ pg : (C → ℝ) × (C → Bool → C → ℝ), (pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)) ∧
        ∑ y, (w y * ∑ x, pg.2 x false y +
          ∑ x, (pg.1 x - (if x = y then 1 else 0) + pg.2 x true y - pg.2 x false y) * (w y * f y x)) <
          (1 + 2 * L * ε) * α + L * ε * (1 + √β) + η * β / 8 + tol := by
  intro w hw
  have hw_nonneg : ∀ y, 0 ≤ w y := hw.1
  have hw_sum : ∑ y, w y = 1 := hw.2
  intro f hf
  have hf01 : ∀ y x, f y x ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    exact (hf y).1
  have h_exists_s : ∀ y, ∃ s : C → AdversarialBco.E d, (∀ i, ‖s i‖ ≤ L) ∧ ∀ i j, f y i + inner ℝ (s i) (pt j - pt i) ≤ f y j := by
    intro y
    exact (hf y).2
  choose s hs hfs using h_exists_s
  rcases AdversarialBco.conv_coin J hJc hJm L ε α β hL hε hβ hH pt hpt pr hprm hpr w hw_nonneg hw_sum f hf01 s hs hfs with
    ⟨ξ, hξ_nonneg, hξ_sum, hξ_bound⟩
  set fbar := λ x => ∑ y, w y * f y x with hfbar
  set S := ∑ y, w y * f y y with hS
  set I := λ x => ∑ y, w y * (f y x * Real.log (f y x / fbar x) + (1 - f y x) * Real.log ((1 - f y x) / (1 - fbar x))) with hI
  have hI_nonneg : ∀ x, 0 ≤ I x := by
    intro x
    have hpinsker := AdversarialBco.pinsker_var w (λ y => f y x) hw_nonneg hw_sum (hf01 · x)
    have h_nonneg : 0 ≤ ∑ y, w y * ((fbar x - f y x) ^ 2) := by
      refine Finset.sum_nonneg (λ y _ => ?_)
      have hy_nonneg : 0 ≤ w y := hw_nonneg y
      have hsq_nonneg : 0 ≤ (fbar x - f y x) ^ 2 := by positivity
      positivity
    have h_eq : (∑ y, w y * ((∑ y', w y' * f y' x) - f y x) ^ 2) = ∑ y, w y * ((fbar x - f y x) ^ 2) := by
      simp [hfbar]
    rw [h_eq] at hpinsker
    have h_div : 0 ≤ I x / 2 := by linarith
    nlinarith
  set KL := ∑ y, w y * Real.log (w y / q y) with hKL
  have hKL_nonneg : 0 ≤ KL := by
    have hgibbs := AdversarialBco.gibbs_lower η hη q w hq hw_nonneg hw_sum (λ _ => 0) (by simp [hq1])
    have h' : -KL / η ≤ 0 := by simpa [hKL] using hgibbs
    have h'' : -KL ≤ 0 := by
      have htemp := mul_le_mul_of_nonneg_right h' (by linarith : 0 ≤ η)
      field_simp [hη.ne.symm] at htemp
      simpa [mul_zero] using htemp
    linarith
  set a0 := (1 + 2 * L * ε) * α + L * ε * (1 + √β) with ha0
  have hconv : ∑ x, ξ x * fbar x - S ≤ a0 + √(β * (∑ x, ξ x * I x) / 2) := by
    simpa [hfbar, hS, hI, ha0] using hξ_bound
  rcases AdversarialBco.vertex_value_le fbar I KL S a0 β η hI_nonneg hKL_nonneg hβ hη ξ hξ_nonneg hξ_sum hconv with
    ⟨x0, hx0⟩
  have hδpos : 0 < tol / 2 := by linarith
  rcases AdversarialBco.primal_vertex η hη q hq hq1 w hw_nonneg hw_sum f hf01 x0 (tol / 2) hδpos with
    ⟨g, hg_cond, hg_bound⟩
  have hp_mem : Pi.single x0 (1 : ℝ) ∈ stdSimplex ℝ C := by
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x = x0
      · simp [hx]
      · simp [hx]
    · simp
  refine ⟨(Pi.single x0 (1 : ℝ), g), ⟨hp_mem, hg_cond⟩, ?_⟩
  have hpayoff : ∑ y, (w y * ∑ x, g x false y +
      ∑ x, ((Pi.single x0 (1 : ℝ) : C → ℝ) x - (if x = y then 1 else 0) + g x true y - g x false y) * (w y * f y x)) ≤
      fbar x0 - (I x0 + KL) / η - S + tol / 2 := by
    simpa [hfbar, hS, hI] using hg_bound
  have h_lt : fbar x0 - (I x0 + KL) / η - S + tol / 2 < a0 + η * β / 8 + tol := by
    nlinarith
  have h_target : a0 + η * β / 8 + tol = (1 + 2 * L * ε) * α + L * ε * (1 + √β) + η * β / 8 + tol := by
    simp [ha0]
  rw [h_target] at h_lt
  linarith

theorem AdversarialBco.tree_sum_le_round {T : Type*} [Fintype T] (κ : (t : ℕ) → (Fin t → T) → T → ℝ)
    (hκ0 : ∀ t h τ, 0 ≤ κ t h τ) (hκ1 : ∀ t h, ∑ τ, κ t h τ = 1)
    (G : (t : ℕ) → (Fin t → T) → T → ℝ) (c : ℕ → ℝ) (n : ℕ)
    (hG : ∀ t < n, ∀ h : Fin t → T, ∑ τ, κ t h τ * G t h τ ≤ c t) :
    ∑ h : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) ≤
      ∑ t ∈ Finset.range n, c t := by
  let g : (t : ℕ) → (Fin (t + 1) → T) → ℝ := fun t h' =>
    if hlt : t < n then G t (Fin.init h') (h' (Fin.last t)) else 0
  let c' : ℕ → ℝ := fun t => if t < n then c t else 0
  have hg' : ∀ t (h : Fin t → T), ∑ τ, κ t h τ * g t (Fin.snoc (α := fun _ => T) h τ) ≤ c' t := by
    intro t h
    by_cases hlt : t < n
    · have hg_eq : ∀ τ, g t (Fin.snoc (α := fun _ => T) h τ) = G t h τ := by
        intro τ
        simp [g, hlt, Fin.init_snoc, Fin.snoc_last]
      have hsum : (∑ τ, κ t h τ * g t (Fin.snoc (α := fun _ => T) h τ)) = (∑ τ, κ t h τ * G t h τ) := by
        apply Finset.sum_congr rfl
        intro τ _
        rw [hg_eq τ]
      rw [hsum]
      simp [c', hlt, hG t hlt h]
    · have hg_eq : ∀ τ, g t (Fin.snoc (α := fun _ => T) h τ) = 0 := by
        intro τ
        simp [g, hlt]
      have hsum : (∑ τ, κ t h τ * g t (Fin.snoc (α := fun _ => T) h τ)) = 0 := by
        simp [hg_eq]
      rw [hsum]
      simp [c', hlt]
  have htree := AdversarialBco.tree_sum_le κ hκ0 hκ1 g c' hg' n
  have h_left_eq : (∑ h : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
      ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t)) =
      (∑ h : Fin n → T, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
      ∑ t : Fin n, g t (fun i : Fin (t + 1) => h (Fin.castLE (Nat.succ_le_of_lt t.2) i))) := by
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    have ht_lt_n : (t : ℕ) < n := t.2
    simp [g, ht_lt_n]
    have h_init : Fin.init (fun i : Fin (t + 1) => h (Fin.castLE (Nat.succ_le_of_lt t.2) i)) =
        (fun i : Fin t => h (Fin.castLE t.2.le i)) := by
      ext i
      simp [Fin.init, Fin.castLE]
    have h_last_val : Fin.castLE (Nat.succ_le_of_lt t.2) (Fin.last t) = t := by
      ext
      simp
    simp [h_init, h_last_val]
  have h_right_eq : (∑ t ∈ Finset.range n, c' t) = (∑ t ∈ Finset.range n, c t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have ht_mem : t < n := Finset.mem_range.1 ht
    simp [c', ht_mem]
  rw [h_left_eq]
  rw [← h_right_eq]
  exact htree

theorem AdversarialBco.thmC_tree {C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (hη : 0 < η)
    (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) (P : Set (C → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hsol : ∀ q : C → ℝ, (∀ z, 0 < q z) → ∑ z, q z = 1 → ((sol q).1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < (sol q).1 x ∧ ∑ z, q z * Real.exp (-η * ((sol q).2 x b z / (sol q).1 x)) ≤ 1) ∨
        ((sol q).1 x = 0 ∧ ∀ z, 0 ≤ (sol q).2 x b z)) ∧
      ∀ y, ∀ f ∈ P, ∑ x, (sol q).1 x * f x - f y +
        ∑ x, ((1 - f x) * (sol q).2 x false y + f x * (sol q).2 x true y) ≤ c)
    (n : ℕ) (a : ℕ → C → ℝ) (ha : ∀ t x, a t x ∈ Set.Icc (0 : ℝ) 1) (haP : ∀ t < n, a t ∈ P) (y : C) :
    ∑ h : Fin n → C × Bool,
        (∏ s : Fin n, (sol (AdversarialBco.ewQ η (fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1) s
            (fun i : Fin s => h (Fin.castLE s.2.le i)))).1 (h s).1 *
          (if (h s).2 then a s (h s).1 else 1 - a s (h s).1)) *
        ∑ t : Fin n, (a t (h t).1 - a t y) ≤
      Real.log (Fintype.card C) / η + n * c := by
  -- Introduce abbreviations for the quantities appearing in the proof
  let est := (fun (q : C → ℝ) (τ : C × Bool) (z : C) => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1)
  let Q := (fun (t : ℕ) (h : Fin t → C × Bool) (z : C) => AdversarialBco.ewQ η est t h z)
  let κ := (fun (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) =>
    (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1))
  let G := (fun (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) =>
    a t τ.1 - a t y + est (Q t h) τ y + (1 / η) * Real.log (∑ z, Q t h z * Real.exp (-η * est (Q t h) τ z)))
  -- Q t h is positive and sums to 1
  have hQ_pos_sum (t : ℕ) (h : Fin t → C × Bool) : (∀ z, 0 < Q t h z) ∧ ∑ z, Q t h z = 1 := by
    dsimp [Q]
    exact AdversarialBco.ewQ_pos_sum η est t h
  have hQ_pos (t : ℕ) (h : Fin t → C × Bool) (z : C) : 0 < Q t h z := (hQ_pos_sum t h).1 z
  have hQ_sum (t : ℕ) (h : Fin t → C × Bool) : ∑ z, Q t h z = 1 := (hQ_pos_sum t h).2
  -- The solution at Q t h is feasible
  have h_sol_Q (t : ℕ) (h : Fin t → C × Bool) :
      (sol (Q t h)).1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < (sol (Q t h)).1 x ∧ ∑ z, Q t h z * Real.exp (-η * ((sol (Q t h)).2 x b z / (sol (Q t h)).1 x)) ≤ 1) ∨
        ((sol (Q t h)).1 x = 0 ∧ ∀ z, 0 ≤ (sol (Q t h)).2 x b z) := by
    have hpos := hQ_pos t h
    have hsum := hQ_sum t h
    exact (hsol (Q t h) hpos hsum).1
  -- Step 1: κ is nonnegative
  have hκ0 (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) : 0 ≤ κ t h τ := by
    dsimp [κ]
    have hp_nonneg : 0 ≤ (sol (Q t h)).1 τ.1 := by
      have hmem := h_sol_Q t h
      rcases hmem with ⟨hstd, _⟩
      have hmem' := hstd
      -- hstd : (sol (Q t h)).1 ∈ stdSimplex ℝ C
      -- stdSimplex = {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}
      have hstd' := hstd
      rcases hstd' with ⟨hnonneg, hsum'⟩
      exact hnonneg τ.1
    have hcoeff_nonneg : 0 ≤ (if τ.2 then a t τ.1 else 1 - a t τ.1) := by
      split
      · -- τ.2 = true
        have ha_range := ha t τ.1
        rcases ha_range with ⟨hlo, hhi⟩
        exact hlo
      · -- τ.2 = false
        have ha_range := ha t τ.1
        rcases ha_range with ⟨hlo, hhi⟩
        linarith
    exact mul_nonneg hp_nonneg hcoeff_nonneg
  -- Step 1: κ sums to 1
  have hκ1 (t : ℕ) (h : Fin t → C × Bool) : ∑ τ, κ t h τ = 1 := by
    dsimp [κ]
    calc
      ∑ τ : C × Bool, (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1)
          = ∑ x : C, ∑ b : Bool, (sol (Q t h)).1 x * (if b then a t x else 1 - a t x) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : C, ((sol (Q t h)).1 x * (a t x + (1 - a t x))) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp; ring
      _ = ∑ x : C, ((sol (Q t h)).1 x * 1) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have ha_range := ha t x
        rcases ha_range with ⟨hlo, hhi⟩
        ring
      _ = ∑ x : C, (sol (Q t h)).1 x := by simp
      _ = 1 := by
        have hmem := h_sol_Q t h
        rcases hmem with ⟨hstd, _⟩
        rcases hstd with ⟨_, hsum'⟩
        exact hsum'
  -- The product of κ over all rounds sums to 1
  have h_sum_prod : ∑ h : Fin n → C × Bool, ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) = 1 := by
    -- Need to adapt sum_prod_policy to the Fin n case
    -- sum_prod_policy works for any Fintype T, and C × Bool is a Fintype
    -- But the history type is Fin t → C × Bool, which matches
    -- Actually, sum_prod_policy expects (t : ℕ) → (Fin t → T) → T → ℝ
    -- and we have κ : (t : ℕ) → (Fin t → C × Bool) → (C × Bool) → ℝ
    -- So we can apply it directly
    -- But the sum is over Fin n → C × Bool, not over all functions
    -- Let's check: sum_prod_policy κ hκ1 n gives sum over all functions Fin n → C × Bool
    -- That's exactly what we need
    exact AdversarialBco.sum_prod_policy κ hκ1 n
  -- Step 2: Path bound from ew_path
  have h_path (h : Fin n → C × Bool) : -Real.log (Fintype.card C) / η ≤
      ∑ t : Fin n, (est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
        (1 / η) * Real.log (∑ z, Q t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
          Real.exp (-η * est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z))) := by
    -- ew_path gives exactly this with est in place of the lambda
    -- Let's check the statement of ew_path
    -- ew_path η hη est n h y : -Real.log (Fintype.card C) / η ≤ ∑ t, (est (ewQ η est t ...) (h t) y + (1/η) * log(...))
    -- And Q t h' = ewQ η est t h'
    -- So we just need to rewrite
    simpa [Q] using AdversarialBco.ew_path η hη est n h y
  -- For each history h, we have:
  -- ∑ t, (a t (h t).1 - a t y) ≤ Real.log (Fintype.card C) / η + ∑ t, G t (h|t) (h t)
  have h_path_G (h : Fin n → C × Bool) : ∑ t : Fin n, (a t (h t).1 - a t y) ≤
      Real.log (Fintype.card C) / η + ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
    have hpath := h_path h
    -- hpath : -Real.log (Fintype.card C) / η ≤ ∑ t, (est (Q t (h|t)) (h t) y + (1/η) * log(...))
    -- We want: ∑ t, (a t (h t).1 - a t y) ≤ Real.log (Fintype.card C) / η + ∑ t, G t (h|t) (h t)
    -- Note: G t (h|t) (h t) = a t (h t).1 - a t y + est (Q t (h|t)) (h t) y + (1/η) * log(...)
    -- So ∑ t, G t (h|t) (h t) = ∑ t, (a t (h t).1 - a t y) + ∑ t, (est (Q t (h|t)) (h t) y + (1/η) * log(...))
    -- Thus the goal is: ∑ t, (a t (h t).1 - a t y) ≤ Real.log (Fintype.card C) / η + (∑ t, (a t (h t).1 - a t y) + ∑ t, (est + log))
    -- which simplifies to: 0 ≤ Real.log (Fintype.card C) / η + ∑ t, (est + log)
    -- which is exactly hpath (after moving terms)
    -- Let's do this algebraically
    have hG_sum (t : Fin n) : G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) =
        (a t (h t).1 - a t y) + (est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
          (1 / η) * Real.log (∑ z, Q t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
            Real.exp (-η * est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z))) := by
      dsimp [G]
      ring
    -- Rewrite the goal using hG_sum
    -- Goal: ∑ t, (a t (h t).1 - a t y) ≤ Real.log (Fintype.card C) / η + ∑ t, G t (h|t) (h t)
    -- RHS = Real.log (Fintype.card C) / η + ∑ t, ((a t (h t).1 - a t y) + (est + log))
    --     = Real.log (Fintype.card C) / η + ∑ t, (a t (h t).1 - a t y) + ∑ t, (est + log)
    -- So the inequality becomes:
    -- ∑ t, (a t (h t).1 - a t y) ≤ Real.log (Fintype.card C) / η + ∑ t, (a t (h t).1 - a t y) + ∑ t, (est + log)
    -- Cancel ∑ t, (a t (h t).1 - a t y) from both sides:
    -- 0 ≤ Real.log (Fintype.card C) / η + ∑ t, (est + log)
    -- which is hpath
    calc
      ∑ t : Fin n, (a t (h t).1 - a t y)
          = (∑ t : Fin n, (a t (h t).1 - a t y)) + 0 := by ring
      _ ≤ (∑ t : Fin n, (a t (h t).1 - a t y)) +
          (Real.log (Fintype.card C) / η +
            ∑ t : Fin n, (est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
              (1 / η) * Real.log (∑ z, Q t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
                Real.exp (-η * est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z)))) := by
        have h0 : 0 ≤ Real.log (Fintype.card C) / η +
            ∑ t : Fin n, (est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
              (1 / η) * Real.log (∑ z, Q t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
                Real.exp (-η * est (Q t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z))) := by
          have : (0 : ℝ) = Real.log (Fintype.card C) / η + (-(Real.log (Fintype.card C) / η)) := by ring
          rw [this]
          simpa [neg_div] using add_le_add_right hpath (Real.log (Fintype.card C) / η)
        nlinarith
      _ = Real.log (Fintype.card C) / η + ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
        simp_rw [hG_sum, Finset.sum_add_distrib]
        ring
  -- Step 3: Tower property using tree_sum_le_round
  have h_tower : ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
      ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) ≤
      ∑ t ∈ Finset.range n, c := by
    -- Apply tree_sum_le_round
    -- tree_sum_le_round κ hκ0 hκ1 G (fun _ => c) n hG
    -- where hG : ∀ t < n, ∀ h : Fin t → C × Bool, ∑ τ, κ t h τ * G t h τ ≤ c
    -- But wait, tree_sum_le_round expects hG of type ∀ t < n, ∀ h, ∑ τ, κ t h τ * G t h τ ≤ c t
    -- where c t is c (constant function)
    -- Actually, the last argument of tree_sum_le_round is (hG : ∀ t < n, ∀ h : Fin t → T, ∑ τ, κ t h τ * G t h τ ≤ c t)
    -- So we need to provide hG
    have hG (t : ℕ) (ht : t < n) (h : Fin t → C × Bool) : ∑ τ, κ t h τ * G t h τ ≤ c := by
      -- We need to show this using br_step
      -- br_step η hη q hq p g hpg a ha y : ...
      -- Let q := Q t h, p := (sol q).1, g := (sol q).2
      -- Then κ t h τ = p τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1)
      -- And G t h τ = a t τ.1 - a t y + g τ.1 τ.2 y / p τ.1 + (1/η) * log(...)
      -- So κ t h τ * G t h τ = p τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1) * (a t τ.1 - a t y + g τ.1 τ.2 y / p τ.1 + (1/η) * log(...))
      -- This is exactly the LHS of br_step with q = Q t h, p = (sol q).1, g = (sol q).2
      -- The RHS of br_step is ≤ c by hsol (since a t ∈ P by haP t ht)
      -- Let's set this up
      have hpos := hQ_pos t h
      have hsum := hQ_sum t h
      have hfeas_full := hsol (Q t h) hpos hsum
      rcases hfeas_full with ⟨hstd, h_or⟩
      -- hstd : (sol (Q t h)).1 ∈ stdSimplex ℝ C ∧ ∀ x b, (0 < (sol (Q t h)).1 x ∧ ...) ∨ ((sol (Q t h)).1 x = 0 ∧ ∀ z, 0 ≤ (sol (Q t h)).2 x b z)
      -- We need to provide hpg : p ∈ stdSimplex ℝ C ∧ ∀ x b, (0 < p x ∧ ...) ∨ (p x = 0 ∧ ...)
      -- This is exactly hstd
      have hbr := AdversarialBco.br_step η hη (Q t h) hpos (sol (Q t h)).1 (sol (Q t h)).2 hstd (a t) (ha t) y
      -- hbr : ∑ τ : C × Bool, (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1) *
      --   (a t τ.1 - a t y + (sol (Q t h)).2 τ.1 τ.2 y / (sol (Q t h)).1 τ.1 +
      --     (1 / η) * Real.log (∑ z, Q t h z * Real.exp (-η * ((sol (Q t h)).2 τ.1 τ.2 z / (sol (Q t h)).1 τ.1)))) ≤
      --   ∑ x, (sol (Q t h)).1 x * a t x - a t y + ∑ x, ((1 - a t x) * (sol (Q t h)).2 x false y + a t x * (sol (Q t h)).2 x true y)
      -- Now note that:
      -- κ t h τ = (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1)
      -- And G t h τ = a t τ.1 - a t y + est (Q t h) τ y + (1/η) * log(...)
      -- where est (Q t h) τ y = (sol (Q t h)).2 τ.1 τ.2 y / (sol (Q t h)).1 τ.1
      -- So κ t h τ * G t h τ = (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1) *
      --   (a t τ.1 - a t y + (sol (Q t h)).2 τ.1 τ.2 y / (sol (Q t h)).1 τ.1 + (1/η) * log(...))
      -- This matches the LHS of hbr exactly
      -- And the RHS of hbr is ≤ c by the last part of hsol (since a t ∈ P)
      have hRHS : ∑ x, (sol (Q t h)).1 x * a t x - a t y +
          ∑ x, ((1 - a t x) * (sol (Q t h)).2 x false y + a t x * (sol (Q t h)).2 x true y) ≤ c := by
        have haP_t := haP t ht
        exact (hsol (Q t h) hpos hsum).2 y (a t) haP_t
      calc
        ∑ τ, κ t h τ * G t h τ
            = ∑ τ : C × Bool, (sol (Q t h)).1 τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1) *
                (a t τ.1 - a t y + ((sol (Q t h)).2 τ.1 τ.2 y / (sol (Q t h)).1 τ.1) +
                  (1 / η) * Real.log (∑ z, Q t h z * Real.exp (-η * ((sol (Q t h)).2 τ.1 τ.2 z / (sol (Q t h)).1 τ.1)))) := by
          dsimp [κ, G, est]
        _ ≤ ∑ x, (sol (Q t h)).1 x * a t x - a t y +
            ∑ x, ((1 - a t x) * (sol (Q t h)).2 x false y + a t x * (sol (Q t h)).2 x true y) := hbr
        _ ≤ c := hRHS
    -- Now apply tree_sum_le_round
    exact AdversarialBco.tree_sum_le_round κ hκ0 hκ1 G (fun _ => c) n hG
  -- Step 4: Combine everything
  -- We have:
  -- For each h: weight h * ∑ t, (a t (h t).1 - a t y) ≤ weight h * (Real.log (Fintype.card C) / η + ∑ t, G t (h|t) (h t))
  -- where weight h = ∏ s, κ s (h|s) (h s)
  -- Summing over h:
  -- ∑ h, weight h * ∑ t, (a t (h t).1 - a t y) ≤ ∑ h, weight h * (Real.log (Fintype.card C) / η + ∑ t, G t (h|t) (h t))
  -- = Real.log (Fintype.card C) / η * ∑ h, weight h + ∑ h, weight h * ∑ t, G t (h|t) (h t)
  -- = Real.log (Fintype.card C) / η * 1 + ∑ h, weight h * ∑ t, G t (h|t) (h t)
  -- ≤ Real.log (Fintype.card C) / η + n * c
  calc
    ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin n, (a t (h t).1 - a t y)
        ≤ ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          (Real.log (Fintype.card C) / η + ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t)) := by
      refine Finset.sum_le_sum (fun h _ => ?_)
      have hpathG := h_path_G h
      have hweight_nonneg : 0 ≤ ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) :=
        Finset.prod_nonneg (fun s _ => hκ0 s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s))
      exact mul_le_mul_of_nonneg_left hpathG hweight_nonneg
    _ = (Real.log (Fintype.card C) / η) * (∑ h : Fin n → C × Bool, ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) +
        ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp [mul_comm]
    _ = (Real.log (Fintype.card C) / η) * 1 +
        ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
      rw [h_sum_prod]
    _ = Real.log (Fintype.card C) / η +
        ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by ring
    _ ≤ Real.log (Fintype.card C) / η + (∑ t ∈ Finset.range n, c) := by
      gcongr
    _ = Real.log (Fintype.card C) / η + n * c := by
      simp [Finset.sum_const, Finset.card_range]

theorem AdversarialBco.thmC_c_main (n : ℕ) (hn : 2 ≤ n) (bh CB Λ : ℝ) (hbh : 1 / 2 ≤ bh) (hCB : 1 ≤ CB)
    (hΛ : 0 < Λ) :
    1 + n * n * (1 / (n ^ 2 * √(2 * bh))) + Λ / √(8 * Λ / (n * bh)) +
        n * ((1 + 2 * n * (1 / (n ^ 2 * √(2 * bh)))) * (1 / n) +
          n * (1 / (n ^ 2 * √(2 * bh))) * (1 + √(CB * bh)) + √(8 * Λ / (n * bh)) * (CB * bh) / 8 + 1 / n) ≤
      6 + √(CB / 2) + (1 + CB) * √(n * bh * Λ / 8) := by
  -- cast n to ℝ for algebraic convenience
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hbhpos : 0 < bh := by linarith
  have h2bh_ge_one : 1 ≤ 2 * bh := by linarith
  have hΛ_nonneg : 0 ≤ Λ := by linarith
  have hCB_nonneg : 0 ≤ CB := by linarith
  have hn_bh_pos : 0 < (n : ℝ) * bh := mul_pos hnpos hbhpos
  have hn_bh_ne_zero : (n : ℝ) * bh ≠ 0 := by linarith

  -- define the key quantities from the hint
  set r := √(2 * bh) with hr_def
  set ε := 1 / (((n : ℝ) ^ 2) * r) with hε_def
  set η := √(8 * Λ / ((n : ℝ) * bh)) with hη_def
  set S := √((n : ℝ) * bh * Λ / 8) with hS_def

  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr_ge_one : 1 ≤ r := by
    calc
      1 = √(1 : ℝ) := by norm_num
      _ ≤ √(2 * bh) := Real.sqrt_le_sqrt h2bh_ge_one
      _ = r := rfl

  have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _

  -- some useful nonnegativity facts
  have h_8Λ_div_nbh_nonneg : 0 ≤ 8 * Λ / ((n : ℝ) * bh) :=
    div_nonneg (by linarith) (by linarith)
  have h_nbhΛ_div_8_nonneg : 0 ≤ (n : ℝ) * bh * Λ / 8 :=
    div_nonneg (by positivity) (by norm_num)

  -- identity: (n:ℝ)² * ε = 1/r
  have h_NNε : ((n : ℝ) * (n : ℝ)) * ε = 1 / r := by
    rw [hε_def]
    field_simp [hnpos.ne', hr_pos.ne']

  -- identity: 2*(n:ℝ)*ε = 2/((n:ℝ)*r)
  have h_2Nε : 2 * (n : ℝ) * ε = 2 / ((n : ℝ) * r) := by
    rw [hε_def]
    field_simp [hnpos.ne', hr_pos.ne']

  -- identity: (n:ℝ)²*ε*(1+√(CB*bh)) = (1+√(CB*bh))/r
  have h_NNε_mul : ((n : ℝ) * (n : ℝ)) * ε * (1 + √(CB * bh)) = (1 + √(CB * bh)) / r := by
    rw [hε_def]
    field_simp [hnpos.ne', hr_pos.ne']

  -- identity: Λ/η = S  (both nonnegative, square both sides)
  have h_Λ_η_eq_S : Λ / η = S := by
    have hpos_div : 0 ≤ Λ / η := div_nonneg hΛ_nonneg (by
      rw [hη_def]
      exact Real.sqrt_nonneg _)
    have hsq : (Λ / η) ^ 2 = S ^ 2 := by
      calc
        (Λ / η) ^ 2 = Λ ^ 2 / η ^ 2 := by ring
        _ = Λ ^ 2 / ((√(8 * Λ / ((n : ℝ) * bh))) ^ 2) := by rw [hη_def]
        _ = Λ ^ 2 / (8 * Λ / ((n : ℝ) * bh)) := by
          rw [Real.sq_sqrt h_8Λ_div_nbh_nonneg]
        _ = Λ ^ 2 * ((n : ℝ) * bh) / (8 * Λ) := by
          field_simp [hΛ.ne', hnpos.ne', hbhpos.ne']
        _ = (n : ℝ) * bh * Λ / 8 := by
          field_simp [hΛ.ne', hnpos.ne', hbhpos.ne']
        _ = (√((n : ℝ) * bh * Λ / 8)) ^ 2 := by
          rw [Real.sq_sqrt h_nbhΛ_div_8_nonneg]
        _ = S ^ 2 := by rw [hS_def]
    have h_cases := (sq_eq_sq_iff_eq_or_eq_neg (a := Λ / η) (b := S)).mp hsq
    rcases h_cases with h | h
    · exact h
    · -- Λ/η = -S, but both are ≥ 0, so both must be 0
      have h_zero : Λ / η = 0 := by linarith
      have hS_zero : S = 0 := by linarith
      rw [h_zero, hS_zero]

  -- identity: (n:ℝ)*η*(CB*bh)/8 = CB*S  (both nonnegative, square both sides)
  have h_Nη_mul : (n : ℝ) * η * (CB * bh) / 8 = CB * S := by
    have hpos_left : 0 ≤ (n : ℝ) * η * (CB * bh) / 8 := by positivity
    have hpos_right : 0 ≤ CB * S := mul_nonneg hCB_nonneg hS_nonneg
    have hsq : ((n : ℝ) * η * (CB * bh) / 8) ^ 2 = (CB * S) ^ 2 := by
      calc
        ((n : ℝ) * η * (CB * bh) / 8) ^ 2 = ((n : ℝ) * η * (CB * bh)) ^ 2 / 64 := by ring
        _ = ((n : ℝ) ^ 2) * η ^ 2 * (CB * bh) ^ 2 / 64 := by ring
        _ = ((n : ℝ) ^ 2) * ((√(8 * Λ / ((n : ℝ) * bh))) ^ 2) * (CB * bh) ^ 2 / 64 := by rw [hη_def]
        _ = ((n : ℝ) ^ 2) * (8 * Λ / ((n : ℝ) * bh)) * (CB * bh) ^ 2 / 64 := by
          rw [Real.sq_sqrt h_8Λ_div_nbh_nonneg]
        _ = (n : ℝ) * bh * Λ * CB ^ 2 / 8 := by
          field_simp [hn_bh_ne_zero]
          ring
        _ = (CB * √((n : ℝ) * bh * Λ / 8)) ^ 2 := by
          calc
            (n : ℝ) * bh * Λ * CB ^ 2 / 8 = CB ^ 2 * ((n : ℝ) * bh * Λ / 8) := by ring
            _ = (CB * √((n : ℝ) * bh * Λ / 8)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt h_nbhΛ_div_8_nonneg]
        _ = (CB * S) ^ 2 := by rw [hS_def]
    have h_cases := (sq_eq_sq_iff_eq_or_eq_neg (a := (n : ℝ) * η * (CB * bh) / 8) (b := CB * S)).mp hsq
    rcases h_cases with h | h
    · exact h
    · -- left = -(CB*S), but both are ≥ 0, so both must be 0
      have h_zero_left : (n : ℝ) * η * (CB * bh) / 8 = 0 := by linarith
      have h_zero_right : CB * S = 0 := by linarith
      rw [h_zero_left, h_zero_right]

  -- bound: (n:ℝ)²*ε ≤ 1  (since 1/r ≤ 1 because r ≥ 1)
  have h_NNε_bound : ((n : ℝ) * (n : ℝ)) * ε ≤ 1 := by
    rw [h_NNε]
    have h := (one_div_le_one_div hr_pos (by norm_num : 0 < (1 : ℝ))).mpr hr_ge_one
    simpa using h

  -- N*r ≥ 2 (since N ≥ 2 and r ≥ 1)
  have h_Nr_ge_two : 2 ≤ (n : ℝ) * r := by
    nlinarith

  -- bound: 2*(n:ℝ)*ε ≤ 1  (since 2/(N*r) ≤ 1 because N*r ≥ 2)
  have h_2Nε_bound : 2 * (n : ℝ) * ε ≤ 1 := by
    rw [h_2Nε]
    exact (div_le_one (mul_pos hnpos hr_pos)).mpr h_Nr_ge_two

  -- bound: (n:ℝ)²*ε*(1+√(CB*bh)) ≤ 1 + √(CB/2)
  have h_NNε_mul_bound : ((n : ℝ) * (n : ℝ)) * ε * (1 + √(CB * bh)) ≤ 1 + √(CB / 2) := by
    rw [h_NNε_mul]
    calc
      (1 + √(CB * bh)) / r = 1 / r + √(CB * bh) / r := by ring
      _ ≤ 1 + √(CB * bh) / r := by
        have h_one_div_r : 1 / r ≤ 1 := by
          have h := (one_div_le_one_div hr_pos (by norm_num : 0 < (1 : ℝ))).mpr hr_ge_one
          simpa using h
        nlinarith
      _ = 1 + √(CB * bh) / √(2 * bh) := by rw [hr_def]
      _ = 1 + √((CB * bh) / (2 * bh)) := by
        rw [Real.sqrt_div (mul_nonneg hCB_nonneg (by linarith)) _]
      _ = 1 + √(CB / 2) := by
        field_simp [hbhpos.ne']

  -- assemble the main inequality using the identities and bounds
  have h_main : 1 + ((n : ℝ) * (n : ℝ)) * (1 / (((n : ℝ) ^ 2) * r)) + Λ / η +
      (n : ℝ) * ((1 + 2 * (n : ℝ) * (1 / (((n : ℝ) ^ 2) * r))) * (1 / (n : ℝ)) +
        (n : ℝ) * (1 / (((n : ℝ) ^ 2) * r)) * (1 + √(CB * bh)) + η * (CB * bh) / 8 + 1 / (n : ℝ)) ≤
      6 + √(CB / 2) + (1 + CB) * S := by
    calc
      1 + ((n : ℝ) * (n : ℝ)) * (1 / (((n : ℝ) ^ 2) * r)) + Λ / η +
          (n : ℝ) * ((1 + 2 * (n : ℝ) * (1 / (((n : ℝ) ^ 2) * r))) * (1 / (n : ℝ)) +
            (n : ℝ) * (1 / (((n : ℝ) ^ 2) * r)) * (1 + √(CB * bh)) + η * (CB * bh) / 8 + 1 / (n : ℝ))
      = 1 + ((n : ℝ) * (n : ℝ)) * ε + Λ / η +
          (n : ℝ) * ((1 + 2 * (n : ℝ) * ε) * (1 / (n : ℝ)) +
            (n : ℝ) * ε * (1 + √(CB * bh)) + η * (CB * bh) / 8 + 1 / (n : ℝ)) := by
        simp [hε_def]
      _ = 3 + ((n : ℝ) * (n : ℝ)) * ε + Λ / η + 2 * (n : ℝ) * ε +
          ((n : ℝ) * (n : ℝ)) * ε * (1 + √(CB * bh)) + (n : ℝ) * η * (CB * bh) / 8 := by
        field_simp [hnpos.ne']
        ring
      _ ≤ 3 + 1 + S + 1 + (1 + √(CB / 2)) + CB * S := by
        nlinarith
      _ = 6 + √(CB / 2) + (1 + CB) * S := by ring

  -- translate back to the original statement (with n : ℕ coerced to ℝ)
  dsimp [r, ε, η, S] at h_main
  exact h_main

theorem AdversarialBco.thmC_c_logs (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hdn : d < n) (D : ℝ) (hD : 2 ≤ D) :
    1 / 2 ≤ (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) ∧
      (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) ≤ 2 * d ^ 2 * Real.log (n * D) ^ 2 ∧
      d * Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 *
          √(2 * ((d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)))))) ≤ 6 * d * Real.log (n * D) := by
  -- basic casts and inequalities
  have hN2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hD2 : (2 : ℝ) ≤ D := hD
  have hNpos : 0 < (n : ℝ) := by linarith
  have hδpos : 0 < (d : ℝ) := by linarith
  have hDpos : 0 < D := by linarith
  have hδ_le_N : (d : ℝ) ≤ (n : ℝ) := le_of_lt (by exact_mod_cast hdn)
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have h_nonneg_n : 0 ≤ (n : ℝ) := by linarith
  have h_nonneg_d : 0 ≤ (d : ℝ) := by linarith
  have h_nonneg_D : 0 ≤ D := by linarith
  have h_nonneg_2 : 0 ≤ (2 : ℝ) := by norm_num
  have h_nonneg_1 : 0 ≤ (1 : ℝ) := by norm_num
  have h_nonneg_4 : 0 ≤ (4 : ℝ) := by norm_num
  -- Part 1
  have h_part1 : (1 : ℝ) / 2 ≤ (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) := by
    -- prove (n)*(d)*D ≥ 4
    have h_NDδD_ge_4 : (4 : ℝ) ≤ (n : ℝ) * (d : ℝ) * D := by
      have h_first : (2 : ℝ) * (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) :=
        mul_le_mul hN2 hδ1 h_nonneg_1 h_nonneg_n
      have h_second : ((2 : ℝ) * (1 : ℝ)) * (2 : ℝ) ≤ ((n : ℝ) * (d : ℝ)) * D :=
        mul_le_mul h_first hD2 h_nonneg_2 (mul_nonneg h_nonneg_n h_nonneg_d)
      calc
        (4 : ℝ) = (2 : ℝ) * (1 : ℝ) * (2 : ℝ) := by norm_num
        _ ≤ (n : ℝ) * (d : ℝ) * D := h_second
    -- prove 2*n ≥ 4
    have h_2N_ge_4 : (4 : ℝ) ≤ 2 * (n : ℝ) := by
      calc
        (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by norm_num
        _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hN2 (by norm_num)
    -- log 4 > 1
    have h_log4_gt_1 : (1 : ℝ) < Real.log (4 : ℝ) := by
      have h_exp1_lt_4 : Real.exp 1 < (4 : ℝ) := by
        have h := Real.exp_one_lt_d9; linarith
      have h4pos : (0 : ℝ) < 4 := by norm_num
      rw [Real.lt_log_iff_exp_lt h4pos]
      exact h_exp1_lt_4
    -- log(N*d*D) ≥ 1
    have h_log_NDδD_ge_1 : (1 : ℝ) ≤ Real.log ((n : ℝ) * (d : ℝ) * D) := by
      have hpos : 0 < (n : ℝ) * (d : ℝ) * D := by
        have h1 : 0 < (n : ℝ) * (d : ℝ) := mul_pos hNpos hδpos
        exact mul_pos h1 hDpos
      have h_le : (4 : ℝ) ≤ (n : ℝ) * (d : ℝ) * D := h_NDδD_ge_4
      have h_log_le : Real.log (4 : ℝ) ≤ Real.log ((n : ℝ) * (d : ℝ) * D) :=
        Real.log_le_log (by norm_num) h_le
      linarith
    -- log(2*n) ≥ 1
    have h_log_2N_ge_1 : (1 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
      have hpos : 0 < 2 * (n : ℝ) := mul_pos (by norm_num) hNpos
      have h_le : (4 : ℝ) ≤ 2 * (n : ℝ) := h_2N_ge_4
      have h_log_le : Real.log (4 : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log (by norm_num) h_le
      linarith
    -- d^2 ≥ 1
    have h_δsq_ge_1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ h_nonneg_1 hδ1 2
    -- product ≥ 1
    have hprod : (1 : ℝ) ≤ (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) :=
        one_le_mul_of_one_le_of_one_le h_δsq_ge_1 h_log_NDδD_ge_1
      have h2 : (1 : ℝ) ≤ ((d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D)) * Real.log (2 * (n : ℝ)) :=
        one_le_mul_of_one_le_of_one_le h1 h_log_2N_ge_1
      simpa [mul_assoc] using h2
    linarith
  -- Part 2
  have h_part2 : (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) ≤ 2 * (d : ℝ) ^ 2 * (Real.log ((n : ℝ) * D)) ^ 2 := by
    -- N*d*D ≤ (N*D)^2
    have h_NDδD_le_ND_sq : (n : ℝ) * (d : ℝ) * D ≤ ((n : ℝ) * D) ^ 2 := by
      have h_nd_le_nn : (n : ℝ) * (d : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hδ_le_N h_nonneg_n
      have h1 : (n : ℝ) * (d : ℝ) * D ≤ (n : ℝ) ^ 2 * D :=
        mul_le_mul_of_nonneg_right (by simpa [sq] using h_nd_le_nn) h_nonneg_D
      have hD_le_DD : D ≤ D * D := by
        -- D ≥ 2 ≥ 1, so D ≤ D*D
        have hD1' : (1 : ℝ) ≤ D := by linarith
        calc
          D = D * 1 := by ring
          _ ≤ D * D := mul_le_mul_of_nonneg_left hD1' h_nonneg_D
      have h2 : (n : ℝ) ^ 2 * D ≤ ((n : ℝ) * D) ^ 2 := by
        calc
          (n : ℝ) ^ 2 * D ≤ (n : ℝ) ^ 2 * (D * D) :=
            mul_le_mul_of_nonneg_left hD_le_DD (pow_two_nonneg _)
          _ = ((n : ℝ) * D) ^ 2 := by ring
      exact le_trans h1 h2
    -- log(N*d*D) ≤ 2*log(N*D)
    have h_log_NDδD_le_2ℓ : Real.log ((n : ℝ) * (d : ℝ) * D) ≤ 2 * Real.log ((n : ℝ) * D) := by
      have hpos : 0 < (n : ℝ) * (d : ℝ) * D := by
        have h1 : 0 < (n : ℝ) * (d : ℝ) := mul_pos hNpos hδpos
        exact mul_pos h1 hDpos
      have h_le : (n : ℝ) * (d : ℝ) * D ≤ ((n : ℝ) * D) ^ 2 := h_NDδD_le_ND_sq
      have h_log_le : Real.log ((n : ℝ) * (d : ℝ) * D) ≤ Real.log (((n : ℝ) * D) ^ 2) :=
        Real.log_le_log hpos h_le
      rw [Real.log_pow, Nat.cast_ofNat] at h_log_le
      exact h_log_le
    -- 2*N ≤ N*D
    have h_2N_le_ND : 2 * (n : ℝ) ≤ (n : ℝ) * D := by
      -- 2*n ≤ n*D because 2 ≤ D and n ≥ 0
      calc
        2 * (n : ℝ) = (n : ℝ) * 2 := by ring
        _ ≤ (n : ℝ) * D := mul_le_mul_of_nonneg_left hD2 h_nonneg_n
    -- log(2*N) ≤ log(N*D)
    have h_log_2N_le_ℓ : Real.log (2 * (n : ℝ)) ≤ Real.log ((n : ℝ) * D) := by
      have hpos : 0 < 2 * (n : ℝ) := mul_pos (by norm_num) hNpos
      exact Real.log_le_log hpos h_2N_le_ND
    -- log(2*N) ≥ 0
    have h_log_2N_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
      refine Real.log_nonneg ?_
      calc
        (1 : ℝ) ≤ 2 * (1 : ℝ) := by norm_num
        _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ (n : ℝ)) (by norm_num)
    -- main calculation
    calc
      (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ))
          = ((d : ℝ) ^ 2) * (Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ))) := by ring
      _ ≤ ((d : ℝ) ^ 2) * ((2 * Real.log ((n : ℝ) * D)) * Real.log ((n : ℝ) * D)) := by
        have h_mul : Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) ≤
            (2 * Real.log ((n : ℝ) * D)) * Real.log ((n : ℝ) * D) :=
          mul_le_mul h_log_NDδD_le_2ℓ h_log_2N_le_ℓ h_log_2N_nonneg
            (mul_nonneg (by norm_num) (by
              -- 0 ≤ 2*log(N*D) because log(N*D) ≥ 0
              have h_ND_ge_1 : (1 : ℝ) ≤ (n : ℝ) * D :=
                calc
                  (1 : ℝ) ≤ (n : ℝ) := by linarith
                  _ = (n : ℝ) * 1 := by ring
                  _ ≤ (n : ℝ) * D := mul_le_mul_of_nonneg_left hD1 h_nonneg_n
              have h_log_ND_nonneg : 0 ≤ Real.log ((n : ℝ) * D) := Real.log_nonneg h_ND_ge_1
              nlinarith))
        have h_δsq_nonneg : 0 ≤ (d : ℝ) ^ 2 := pow_two_nonneg _
        nlinarith
      _ = 2 * ((d : ℝ) ^ 2) * (Real.log ((n : ℝ) * D)) ^ 2 := by ring
  -- Part 3
  set β := (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) with hβdef
  set r := Real.sqrt (2 * β) with hrdef
  have hβ_nonneg : 0 ≤ β := by
    rw [hβdef]
    have h1 : 0 ≤ (d : ℝ) ^ 2 := pow_two_nonneg _
    have h_log_NDδD_nonneg : 0 ≤ Real.log ((n : ℝ) * (d : ℝ) * D) := by
      refine Real.log_nonneg ?_
      have h_n_ge_1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have h_d_ge_1 : (1 : ℝ) ≤ (d : ℝ) := by linarith
      have h_first : (1 : ℝ) * (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) :=
        mul_le_mul h_n_ge_1 h_d_ge_1 h_nonneg_1 h_nonneg_n
      have h_second : ((1 : ℝ) * (1 : ℝ)) * (1 : ℝ) ≤ ((n : ℝ) * (d : ℝ)) * D :=
        mul_le_mul h_first hD1 h_nonneg_1 (mul_nonneg h_nonneg_n h_nonneg_d)
      simpa [mul_one] using h_second
    have h_log_2N_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
      refine Real.log_nonneg ?_
      calc
        (1 : ℝ) ≤ 2 * (1 : ℝ) := by norm_num
        _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ (n : ℝ)) (by norm_num)
    exact mul_nonneg (mul_nonneg h1 h_log_NDδD_nonneg) h_log_2N_nonneg
  have hβ_ge_half : 1 / 2 ≤ β := by
    rw [hβdef]; exact h_part1
  have hβ_le_2δsqℓsq : β ≤ 2 * ((d : ℝ) ^ 2) * (Real.log ((n : ℝ) * D)) ^ 2 := by
    rw [hβdef]; exact h_part2
  have hℓ_pos : 0 < Real.log ((n : ℝ) * D) := by
    have h_ND_ge_4 : (4 : ℝ) ≤ (n : ℝ) * D := by
      calc
        (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by norm_num
        _ ≤ (n : ℝ) * D := mul_le_mul hN2 hD2 h_nonneg_2 h_nonneg_n
    have h_ND_gt_1 : 1 < (n : ℝ) * D := by linarith
    exact Real.log_pos h_ND_gt_1
  have hℓ_nonneg : 0 ≤ Real.log ((n : ℝ) * D) := by linarith
  have hr_ge_1 : (1 : ℝ) ≤ r := by
    rw [hrdef]
    have h_sq_le : (1 : ℝ) ^ 2 ≤ 2 * β := by
      have h2β_ge_1 : (1 : ℝ) ≤ 2 * β := by linarith
      simpa [sq] using h2β_ge_1
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt (2 * β) := Real.sqrt_le_sqrt h_sq_le
      _ = r := rfl
  have hr_le_2δℓ : r ≤ 2 * (d : ℝ) * Real.log ((n : ℝ) * D) := by
    have h2β_le : 2 * β ≤ (2 * (d : ℝ) * Real.log ((n : ℝ) * D)) ^ 2 := by
      calc
        2 * β ≤ 2 * (2 * ((d : ℝ) ^ 2) * (Real.log ((n : ℝ) * D)) ^ 2) :=
          mul_le_mul_of_nonneg_left hβ_le_2δsqℓsq h_nonneg_2
        _ = 4 * ((d : ℝ) ^ 2) * ((Real.log ((n : ℝ) * D)) ^ 2) := by ring
        _ = (2 * (d : ℝ) * Real.log ((n : ℝ) * D)) ^ 2 := by ring
    have h_nonneg_2β : 0 ≤ 2 * β := mul_nonneg h_nonneg_2 hβ_nonneg
    have h_nonneg_2δℓ : 0 ≤ 2 * (d : ℝ) * Real.log ((n : ℝ) * D) := by
      have h_mul_nonneg : 0 ≤ 2 * (d : ℝ) := mul_nonneg h_nonneg_2 h_nonneg_d
      exact mul_nonneg h_mul_nonneg hℓ_nonneg
    have hr_sq_le : r ^ 2 ≤ (2 * (d : ℝ) * Real.log ((n : ℝ) * D)) ^ 2 := by
      have h : r ^ 2 = 2 * β := by rw [hrdef, Real.sq_sqrt h_nonneg_2β]
      rw [h]; exact h2β_le
    exact le_of_sq_le_sq hr_sq_le h_nonneg_2δℓ
  have h_4DN2r_ge_1 : (1 : ℝ) ≤ 4 * D * (n : ℝ) ^ 2 * r := by
    have h_one_le_4 : (1 : ℝ) ≤ 4 := by norm_num
    have h_one_le_D : (1 : ℝ) ≤ D := by linarith
    have h_one_le_N_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h1_le_n : (1 : ℝ) ≤ (n : ℝ) := by linarith
      calc
        (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ h_nonneg_1 h1_le_n 2
    have h_one_le_r : (1 : ℝ) ≤ r := hr_ge_1
    have h_nonneg_N_sq : 0 ≤ (n : ℝ) ^ 2 := pow_two_nonneg _
    have h_nonneg_4D : 0 ≤ 4 * D := mul_nonneg (by norm_num) h_nonneg_D
    have h_nonneg_4DN2 : 0 ≤ 4 * D * (n : ℝ) ^ 2 := mul_nonneg h_nonneg_4D h_nonneg_N_sq
    have h1 : (1 : ℝ) * (1 : ℝ) ≤ 4 * D :=
      mul_le_mul h_one_le_4 h_one_le_D h_nonneg_1 h_nonneg_4
    have h2 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ (4 * D) * (n : ℝ) ^ 2 :=
      mul_le_mul h1 h_one_le_N_sq h_nonneg_1 h_nonneg_4D
    have h3 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ (4 * D) * (n : ℝ) ^ 2 * r :=
      mul_le_mul h2 h_one_le_r h_nonneg_1 h_nonneg_4DN2
    simpa [mul_one] using h3
  have h_ineq1 : 1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r)) ≤ 5 * D * (n : ℝ) ^ 2 * r := by
    have h_ne_zero : (n : ℝ) ^ 2 * r ≠ 0 := by
      have hN_sq_pos : 0 < (n : ℝ) ^ 2 := pow_pos hNpos 2
      have hr_pos : 0 < r := by linarith
      exact mul_ne_zero (ne_of_gt hN_sq_pos) (ne_of_gt hr_pos)
    have h_div : 4 * D / (1 / ((n : ℝ) ^ 2 * r)) = 4 * D * ((n : ℝ) ^ 2 * r) := by
      field_simp [h_ne_zero]
    rw [h_div]
    have hN_sq_ge_4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ h_nonneg_2 hN2 2
    have h_DN2r_ge_8 : (8 : ℝ) ≤ D * (n : ℝ) ^ 2 * r := by
      have h_mul1 : (2 : ℝ) * (4 : ℝ) ≤ D * (n : ℝ) ^ 2 :=
        mul_le_mul hD2 hN_sq_ge_4 h_nonneg_4 h_nonneg_D
      have h_mul2 : ((2 : ℝ) * (4 : ℝ)) * (1 : ℝ) ≤ (D * (n : ℝ) ^ 2) * r :=
        mul_le_mul h_mul1 hr_ge_1 h_nonneg_1 (mul_nonneg h_nonneg_D (pow_two_nonneg _))
      calc
        (8 : ℝ) = ((2 : ℝ) * (4 : ℝ)) * (1 : ℝ) := by norm_num
        _ ≤ (D * (n : ℝ) ^ 2) * r := h_mul2
        _ = D * (n : ℝ) ^ 2 * r := by ring
    linarith
  have h_N2r_pos : 0 < (n : ℝ) ^ 2 * r := by
    have hN_sq_pos : 0 < (n : ℝ) ^ 2 := pow_pos hNpos 2
    have hr_pos : 0 < r := by linarith
    exact mul_pos hN_sq_pos hr_pos
  have h_pos_arg : 0 < 1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r)) := by
    have h_div_pos : 0 < 4 * D / (1 / ((n : ℝ) ^ 2 * r)) := by
      refine div_pos (mul_pos (by norm_num) hDpos) (div_pos (by norm_num) h_N2r_pos)
    have h_one_pos : 0 < (1 : ℝ) := by norm_num
    exact add_pos h_one_pos h_div_pos
  have h_r_le_2N2D : r ≤ 2 * (n : ℝ) ^ 2 * D := by
    have hℓ_le_ND : Real.log ((n : ℝ) * D) ≤ (n : ℝ) * D := by
      have hx_pos : 0 < (n : ℝ) * D := mul_pos hNpos hDpos
      have h := Real.log_le_sub_one_of_pos hx_pos
      have hsub : (n : ℝ) * D - 1 ≤ (n : ℝ) * D := by
        -- a - 1 ≤ a
        exact sub_le_self _ h_nonneg_1
      exact le_trans h hsub
    have h1 : r ≤ 2 * (d : ℝ) * Real.log ((n : ℝ) * D) := hr_le_2δℓ
    have h2 : 2 * (d : ℝ) * Real.log ((n : ℝ) * D) ≤ 2 * (n : ℝ) * ((n : ℝ) * D) := by
      have h_mul : (d : ℝ) * Real.log ((n : ℝ) * D) ≤ (n : ℝ) * ((n : ℝ) * D) :=
        mul_le_mul hδ_le_N hℓ_le_ND hℓ_nonneg h_nonneg_n
      have h2' : 2 * ((d : ℝ) * Real.log ((n : ℝ) * D)) ≤ 2 * ((n : ℝ) * ((n : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left h_mul h_nonneg_2
      simpa [mul_assoc] using h2'
    have h3 : 2 * (n : ℝ) * ((n : ℝ) * D) = 2 * (n : ℝ) ^ 2 * D := by ring
    rw [h3] at h2
    linarith
  have h_5DN2r_le_ND_pow6 : 5 * D * (n : ℝ) ^ 2 * r ≤ ((n : ℝ) * D) ^ 6 := by
    have h_ND_ge_4 : (4 : ℝ) ≤ (n : ℝ) * D := by
      calc
        (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by norm_num
        _ ≤ (n : ℝ) * D := mul_le_mul hN2 hD2 h_nonneg_2 h_nonneg_n
    calc
      5 * D * (n : ℝ) ^ 2 * r ≤ 5 * D * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 * D) := by
        have h_nonneg_5DN2 : 0 ≤ 5 * D * (n : ℝ) ^ 2 :=
          mul_nonneg (mul_nonneg (by norm_num) h_nonneg_D) (pow_two_nonneg _)
        exact mul_le_mul_of_nonneg_left h_r_le_2N2D h_nonneg_5DN2
      _ = 10 * (n : ℝ) ^ 4 * D ^ 2 := by ring
      _ ≤ ((n : ℝ) * D) ^ 2 * ((n : ℝ) * D) ^ 4 := by
        have h10 : (10 : ℝ) ≤ ((n : ℝ) * D) ^ 2 := by
          have h16 : (16 : ℝ) ≤ ((n : ℝ) * D) ^ 2 := by
            -- (n*D) ≥ 4, so (n*D)^2 ≥ 16
            have h_ND_ge_4' : (4 : ℝ) ≤ (n : ℝ) * D := h_ND_ge_4
            have h_nonneg_4' : 0 ≤ (4 : ℝ) := h_nonneg_4
            calc
              (16 : ℝ) = (4 : ℝ) ^ 2 := by norm_num
              _ ≤ ((n : ℝ) * D) ^ 2 := pow_le_pow_left₀ h_nonneg_4 h_ND_ge_4' 2
          linarith
        have h_N4D2_le_ND4 : (n : ℝ) ^ 4 * D ^ 2 ≤ ((n : ℝ) * D) ^ 4 := by
          have hD_sq_le_D_four : D ^ 2 ≤ D ^ 4 := by
            have hD1' : (1 : ℝ) ≤ D := by linarith
            have hD_sq_ge_1 : (1 : ℝ) ≤ D ^ 2 := by
              calc
                (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
                _ ≤ D ^ 2 := pow_le_pow_left₀ (by norm_num) hD1' 2
            have h_nonneg_Dsq : 0 ≤ D ^ 2 := pow_two_nonneg _
            calc
              D ^ 2 = D ^ 2 * 1 := by ring
              _ ≤ D ^ 2 * (D ^ 2) := mul_le_mul_of_nonneg_left hD_sq_ge_1 h_nonneg_Dsq
              _ = D ^ 4 := by ring
          calc
            (n : ℝ) ^ 4 * D ^ 2 ≤ (n : ℝ) ^ 4 * D ^ 4 :=
              mul_le_mul_of_nonneg_left hD_sq_le_D_four (pow_nonneg h_nonneg_n 4)
            _ = ((n : ℝ) * D) ^ 4 := by ring
        -- Now: 10*N^4*D^2 ≤ (N*D)^2 * (N*D)^4
        -- i.e., 10 * X ≤ Y^2 * Y^4 where X = N^4*D^2, Y = N*D
        -- We have: 10 ≤ Y^2 and X ≤ Y^4
        -- So 10*X ≤ Y^2 * Y^4
        have h_nonneg_10 : 0 ≤ (10 : ℝ) := by norm_num
        have h_nonneg_N4D2 : 0 ≤ (n : ℝ) ^ 4 * D ^ 2 := mul_nonneg (pow_nonneg h_nonneg_n 4) (pow_two_nonneg _)
        have h_nonneg_NDsq : 0 ≤ ((n : ℝ) * D) ^ 2 := pow_two_nonneg _
        have h_nonneg_NDfour : 0 ≤ ((n : ℝ) * D) ^ 4 := pow_nonneg (mul_nonneg h_nonneg_n h_nonneg_D) 4
        have h_mul : (10 : ℝ) * ((n : ℝ) ^ 4 * D ^ 2) ≤ ((n : ℝ) * D) ^ 2 * ((n : ℝ) * D) ^ 4 :=
          mul_le_mul h10 h_N4D2_le_ND4 h_nonneg_N4D2 h_nonneg_NDsq
        -- simplify LHS: 10 * N^4 * D^2 = 10 * (N^4 * D^2)
        -- RHS: (N*D)^2 * (N*D)^4
        simpa [mul_assoc] using h_mul
      _ = ((n : ℝ) * D) ^ 6 := by ring
  have h_log_ineq : Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r))) ≤ 6 * Real.log ((n : ℝ) * D) := by
    have h_le : 1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r)) ≤ ((n : ℝ) * D) ^ 6 :=
      le_trans h_ineq1 h_5DN2r_le_ND_pow6
    have h_pos : 0 < 1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r)) := h_pos_arg
    have h_log_le : Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r))) ≤ Real.log (((n : ℝ) * D) ^ 6) :=
      Real.log_le_log h_pos h_le
    rw [Real.log_pow, Nat.cast_ofNat] at h_log_le
    exact h_log_le
  have h_part3 : (d : ℝ) * Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r))) ≤ 6 * (d : ℝ) * Real.log ((n : ℝ) * D) := by
    have h_nonneg_d : 0 ≤ (d : ℝ) := h_nonneg_d
    have h_nonneg_log : 0 ≤ Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 * r))) := by
      refine Real.log_nonneg ?_
      -- 1 + 4*D/(...) ≥ 1
      have h_div_nonneg : 0 ≤ 4 * D / (1 / ((n : ℝ) ^ 2 * r)) :=
        div_nonneg (mul_nonneg (by norm_num) h_nonneg_D) (by positivity)
      linarith
    -- Using h_log_ineq: log(...) ≤ 6*log(N*D)
    -- Multiply both sides by d ≥ 0
    nlinarith
  -- Assemble
  have h1' : 1 / 2 ≤ (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) := by
    simpa using h_part1
  have h2' : (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) ≤ 2 * d ^ 2 * Real.log (n * D) ^ 2 := by
    simpa [Nat.cast_pow] using h_part2
  have h3' : d * Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 *
      √(2 * ((d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)))))) ≤ 6 * d * Real.log (n * D) := by
    simpa [hβdef, hrdef] using h_part3
  exact And.intro h1' (And.intro h2' h3')

theorem AdversarialBco.thmC_c_final (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (D CB bh Λ : ℝ) (hD : 2 ≤ D) (hCB : 1 ≤ CB)
    (hbh0 : 0 ≤ bh) (hbh : bh ≤ 2 * d ^ 2 * Real.log (n * D) ^ 2) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ 6 * d * Real.log (n * D)) :
    6 + √(CB / 2) + (1 + CB) * √(n * bh * Λ / 8) ≤
      (2 * (1 + CB) + 6 + √(CB / 2)) * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ) := by
  set N := (n : ℝ) with hN
  set δ := (d : ℝ) with hδ
  set ℓ := Real.log (N * D) with hℓ
  set X := δ ^ (3 / 2 : ℝ) * Real.sqrt N * ℓ ^ (3 / 2 : ℝ) with hX
  have hN2 : (2 : ℝ) ≤ N := by
    simpa [hN] using mod_cast hn
  have hδ1 : (1 : ℝ) ≤ δ := by
    simpa [hδ] using mod_cast hd
  have hδ_nonneg : 0 ≤ δ := by linarith
  have hN_nonneg : 0 ≤ N := by linarith
  have hCB_nonneg : 0 ≤ CB := by linarith
  have hND_pos : 0 < N * D := by
    have hN_pos : 0 < N := by linarith
    have hD_pos : 0 < D := by linarith
    exact mul_pos hN_pos hD_pos
  have hℓ_nonneg : 0 ≤ ℓ := Real.log_nonneg (by
    have : (1 : ℝ) ≤ N * D := by nlinarith
    exact this)
  have hℓ_ge_one : 1 ≤ ℓ := by
    rw [Real.le_log_iff_exp_le hND_pos]
    have h_exp_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h_four_le : (2.7182818286 : ℝ) ≤ N * D := by
      nlinarith
    linarith
  have hX_nonneg : 0 ≤ X := by
    rw [hX]
    have h1 : 0 ≤ δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hδ_nonneg _
    have h2 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h3 : 0 ≤ ℓ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hℓ_nonneg _
    positivity
  have hX_ge_one : 1 ≤ X := by
    rw [hX]
    have h1 : 1 ≤ δ ^ (3 / 2 : ℝ) := Real.one_le_rpow hδ1 (by norm_num : (0 : ℝ) ≤ 3/2)
    have h2 : 1 ≤ Real.sqrt N := (Real.one_le_sqrt).mpr (by linarith)
    have h3 : 1 ≤ ℓ ^ (3 / 2 : ℝ) := Real.one_le_rpow hℓ_ge_one (by norm_num : (0 : ℝ) ≤ 3/2)
    have hpos1 : 0 ≤ δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hδ_nonneg _
    have hpos2 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hpos3 : 0 ≤ ℓ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hℓ_nonneg _
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ δ ^ (3 / 2 : ℝ) * Real.sqrt N * ℓ ^ (3 / 2 : ℝ) := by gcongr
  have hδ_cube : (δ ^ (3 / 2 : ℝ)) ^ 2 = δ ^ (3 : ℝ) := by
    simpa [Real.rpow_natCast] using
      calc
        (δ ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = δ ^ ((3 / 2 : ℝ) * (2 : ℝ)) := by
          rw [(Real.rpow_mul hδ_nonneg (3/2) (2:ℝ)).symm]
        _ = δ ^ (3 : ℝ) := by norm_num
  have hℓ_cube : (ℓ ^ (3 / 2 : ℝ)) ^ 2 = ℓ ^ (3 : ℝ) := by
    simpa [Real.rpow_natCast] using
      calc
        (ℓ ^ (3 / 2 : ℝ)) ^ (2 : ℝ) = ℓ ^ ((3 / 2 : ℝ) * (2 : ℝ)) := by
          rw [(Real.rpow_mul hℓ_nonneg (3/2) (2:ℝ)).symm]
        _ = ℓ ^ (3 : ℝ) := by norm_num
  have hX_sq_eq : X ^ 2 = N * δ ^ 3 * ℓ ^ 3 := by
    calc
      X ^ 2 = (δ ^ (3 / 2 : ℝ) * Real.sqrt N * ℓ ^ (3 / 2 : ℝ)) ^ 2 := by rw [hX]
      _ = (δ ^ (3 / 2 : ℝ)) ^ 2 * (Real.sqrt N) ^ 2 * (ℓ ^ (3 / 2 : ℝ)) ^ 2 := by ring
      _ = (δ ^ (3 / 2 : ℝ)) ^ 2 * N * (ℓ ^ (3 / 2 : ℝ)) ^ 2 := by rw [Real.sq_sqrt hN_nonneg]
      _ = δ ^ (3 : ℝ) * N * ℓ ^ (3 : ℝ) := by rw [hδ_cube, hℓ_cube]
      _ = δ ^ 3 * N * ℓ ^ 3 := by simp
      _ = N * δ ^ 3 * ℓ ^ 3 := by ring
  have h_bound : N * bh * Λ / 8 ≤ (2 * X) ^ 2 := by
    calc
      N * bh * Λ / 8 ≤ N * (2 * δ ^ 2 * ℓ ^ 2) * (6 * δ * ℓ) / 8 := by
        gcongr
      _ = (3/2 : ℝ) * (N * δ ^ 3 * ℓ ^ 3) := by ring
      _ = (3/2 : ℝ) * (X ^ 2) := by rw [hX_sq_eq]
      _ ≤ 4 * (X ^ 2) := by nlinarith
      _ = (2 * X) ^ 2 := by ring
  have h_sqrt_bound : √(N * bh * Λ / 8) ≤ 2 * X := by
    calc
      √(N * bh * Λ / 8) ≤ √((2 * X) ^ 2) := Real.sqrt_le_sqrt h_bound
      _ = 2 * X := Real.sqrt_sq (by nlinarith)
  have h_nonneg_six_plus : 0 ≤ 6 + √(CB / 2) := by
    have : 0 ≤ √(CB / 2) := Real.sqrt_nonneg _
    nlinarith
  calc
    6 + √(CB / 2) + (1 + CB) * √(n * bh * Λ / 8)
        = 6 + √(CB / 2) + (1 + CB) * √(N * bh * Λ / 8) := by simp [hN]
    _ ≤ (6 + √(CB / 2)) * X + (1 + CB) * √(N * bh * Λ / 8) := by
      have h : 6 + √(CB / 2) ≤ (6 + √(CB / 2)) * X := by
        nlinarith
      nlinarith
    _ ≤ (6 + √(CB / 2)) * X + (1 + CB) * (2 * X) := by
      have htemp : (1 + CB) * √(N * bh * Λ / 8) ≤ (1 + CB) * (2 * X) :=
        mul_le_mul_of_nonneg_left h_sqrt_bound (by linarith)
      nlinarith
    _ = (2 * (1 + CB) + 6 + √(CB / 2)) * X := by ring
    _ = (2 * (1 + CB) + 6 + √(CB / 2)) * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ) := by
      simp [hN, hδ, hℓ, hX]
      ring

theorem AdversarialBco.thmC_c_large (d n : ℕ) (hn : 2 ≤ n) (hdn : n ≤ d) (D C0 : ℝ) (hD : 2 ≤ D) (hC0 : 1 ≤ C0) :
    (n : ℝ) ≤ C0 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ) := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdn' : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdn
  have hn0 : 0 ≤ (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hd0 : 0 ≤ (d : ℝ) := by linarith
  have hC0_nonneg : 0 ≤ C0 := by linarith
  -- log(N*D) ≥ 1 because N*D ≥ 4 > exp(1)
  have hprod_ge_four : (4 : ℝ) ≤ (n : ℝ) * D := by
    nlinarith
  have hexp_lt_four : Real.exp 1 < (4 : ℝ) := by
    have h := Real.exp_one_lt_d9
    linarith
  have hexp_le_prod : Real.exp 1 ≤ (n : ℝ) * D := by
    linarith
  have hlog_pos : 0 < Real.log ((n : ℝ) * D) := by
    have h_one_lt_prod : (1 : ℝ) < (n : ℝ) * D := by
      nlinarith
    exact Real.log_pos h_one_lt_prod
  have hlog_ge_one : (1 : ℝ) ≤ Real.log ((n : ℝ) * D) := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp_le_prod
    rw [Real.log_exp (1 : ℝ)] at h
    exact h
  have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) * D) := by linarith
  -- the four key inequalities
  have h_sqrt_ge_one : (1 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hn1
  have h_dpow_ge_n : (n : ℝ) ≤ (d : ℝ) ^ (3/2 : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (3/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 : ℝ) ≤ (3/2 : ℝ))
      _ ≤ (d : ℝ) ^ (3/2 : ℝ) :=
        Real.rpow_le_rpow hn0 hdn' (by norm_num : 0 ≤ (3/2 : ℝ))
  have h_log_pow_ge_one : (1 : ℝ) ≤ Real.log ((n : ℝ) * D) ^ (3/2 : ℝ) :=
    Real.one_le_rpow hlog_ge_one (by norm_num : 0 ≤ (3/2 : ℝ))
  have h_dpow_nonneg : 0 ≤ (d : ℝ) ^ (3/2 : ℝ) := Real.rpow_nonneg hd0 _
  have h_log_pow_nonneg : 0 ≤ Real.log ((n : ℝ) * D) ^ (3/2 : ℝ) :=
    Real.rpow_nonneg hlog_nonneg _
  -- Now combine: n * 1 * 1 * 1 ≤ C0 * d^(3/2) * √n * log^(3/2)
  have h_mul : (n : ℝ) * (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤
      C0 * ((d : ℝ) ^ (3/2 : ℝ)) * √(n : ℝ) * (Real.log ((n : ℝ) * D) ^ (3/2 : ℝ)) := by
    -- Step 1: n * 1 ≤ C0 * d^(3/2)
    have h1 : (n : ℝ) * (1 : ℝ) ≤ C0 * ((d : ℝ) ^ (3/2 : ℝ)) := by
      have h_temp := mul_le_mul h_dpow_ge_n hC0 (by norm_num : 0 ≤ (1 : ℝ)) h_dpow_nonneg
      simpa [mul_comm] using h_temp
    -- Step 2: (n*1) * 1 ≤ (C0*d^(3/2)) * √n
    have h2 : ((n : ℝ) * (1 : ℝ)) * (1 : ℝ) ≤ (C0 * ((d : ℝ) ^ (3/2 : ℝ))) * √(n : ℝ) := by
      have h_nonneg_mid : 0 ≤ C0 * ((d : ℝ) ^ (3/2 : ℝ)) :=
        mul_nonneg hC0_nonneg h_dpow_nonneg
      exact mul_le_mul h1 h_sqrt_ge_one (by norm_num : 0 ≤ (1 : ℝ)) h_nonneg_mid
    -- Step 3: ((n*1)*1)*1 ≤ ((C0*d^(3/2))*√n) * log^(3/2)
    have h3 : (((n : ℝ) * (1 : ℝ)) * (1 : ℝ)) * (1 : ℝ) ≤
        ((C0 * ((d : ℝ) ^ (3/2 : ℝ))) * √(n : ℝ)) * (Real.log ((n : ℝ) * D) ^ (3/2 : ℝ)) := by
      have h_nonneg_mid2 : 0 ≤ (C0 * ((d : ℝ) ^ (3/2 : ℝ))) * √(n : ℝ) :=
        mul_nonneg (mul_nonneg hC0_nonneg h_dpow_nonneg) (Real.sqrt_nonneg _)
      exact mul_le_mul h2 h_log_pow_ge_one (by norm_num : 0 ≤ (1 : ℝ)) h_nonneg_mid2
    simpa [mul_assoc] using h3
  -- Now simplify LHS: n * 1 * 1 * 1 = n
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul

theorem AdversarialBco.thmC_c_params (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (D : ℝ) (hD : 2 ≤ D) :
    0 < 1 / ((n : ℝ) ^ 2 * √(2 * ((d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)))) ∧
      1 / ((n : ℝ) ^ 2 * √(2 * ((d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)))) ≤ 1 / 4 ∧
      0 < (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) ∧
      0 < d * Real.log (1 + 4 * D / (1 / ((n : ℝ) ^ 2 *
          √(2 * ((d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)))))) := by
  set N := (n : ℝ) with hN
  set δ := (d : ℝ) with hδ
  have hNpos : 2 ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hδpos : 1 ≤ δ := by
    dsimp [δ]
    exact_mod_cast hd
  have hDpos : 2 ≤ D := hD
  -- N * δ * D ≥ 4
  have hNδD : 4 ≤ N * δ * D := by
    have hNδ : 2 ≤ N * δ := by
      nlinarith
    nlinarith
  -- 2 * N ≥ 4
  have h2N : 4 ≤ 2 * N := by
    nlinarith
  -- log 4 > 1
  have hlog4gt1 : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
    have h_exp_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h_2718_lt_4 : (2.7182818286 : ℝ) < 4 := by norm_num
    linarith
  -- log(N * δ * D) ≥ log 4 > 1
  have hlog1_gt1 : 1 < Real.log (N * δ * D) := by
    have hpos : 0 < N * δ * D := by
      nlinarith
    have hle : Real.log 4 ≤ Real.log (N * δ * D) :=
      Real.log_le_log (by norm_num : 0 < (4 : ℝ)) hNδD
    linarith
  -- log(2 * N) ≥ log 4 > 1
  have hlog2_gt1 : 1 < Real.log (2 * N) := by
    have hpos : 0 < 2 * N := by nlinarith
    have hle : Real.log 4 ≤ Real.log (2 * N) :=
      Real.log_le_log (by norm_num : 0 < (4 : ℝ)) h2N
    linarith
  -- betahat > 0
  have hbetahatpos : 0 < δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N) := by
    positivity
  -- r = √(2 * betahat) ≥ 1
  have hr : 1 ≤ √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N))) := by
    rw [Real.one_le_sqrt]
    have hsq : (1 : ℝ) ≤ δ ^ 2 := by nlinarith
    have hlog1 : (1 : ℝ) ≤ Real.log (N * δ * D) := by linarith
    have hlog2 : (1 : ℝ) ≤ Real.log (2 * N) := by linarith
    have h12 : (1 : ℝ) ≤ δ ^ 2 * Real.log (N * δ * D) :=
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ δ ^ 2 * Real.log (N * δ * D) :=
          mul_le_mul hsq hlog1 (by linarith) (by nlinarith)
    have hprod : (1 : ℝ) ≤ δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N) :=
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ (δ ^ 2 * Real.log (N * δ * D)) * Real.log (2 * N) :=
          mul_le_mul h12 hlog2 (by linarith) (by nlinarith)
    nlinarith
  -- N^2 * r > 0
  have hN2rpos : 0 < N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N))) := by
    positivity
  -- ε = 1/(N^2 * r) > 0
  have hεpos : 0 < 1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N)))) := by
    rw [one_div_pos]
    exact hN2rpos
  -- ε ≤ 1/4
  have hεle : 1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N)))) ≤ 1 / 4 := by
    refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) ?_
    nlinarith
  -- part 3: betahat > 0
  have hpart3 : 0 < δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N) := hbetahatpos
  -- part 4: d * log(1 + 4*D/ε) > 0
  have hpart4 : 0 < d * Real.log (1 + 4 * D / (1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N)))))) := by
    have hinnerpos : 0 < 4 * D / (1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N))))) := by
      positivity
    have hgt1 : 1 < 1 + 4 * D / (1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N))))) := by
      nlinarith
    have hlogpos : 0 < Real.log (1 + 4 * D / (1 / (N ^ 2 * √(2 * (δ ^ 2 * Real.log (N * δ * D) * Real.log (2 * N)))))) :=
      Real.log_pos hgt1
    have hdpos : 0 < (d : ℝ) := by
      have := Nat.one_pos.trans_le hd
      exact_mod_cast this
    positivity
  -- combine everything
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hN, hδ] using hεpos
  · simpa [hN, hδ] using hεle
  · simpa [hN, hδ] using hpart3
  · simpa [hN, hδ] using hpart4


/-- Theorem 7.2 for the learner of Algorithm 7.1, realised as a learner of the frozen
statement. The seed is a point of `(ℝ × ℝ)^n` under the product
of uniform laws on `[0, 1]^2`, one pair per round: the first coordinate draws the action from the solution of the
round's program (`exists_sampler`), the second the coin of mean the observed loss. The learner rebuilds its history
from the seed and its observations (`obsHist`), which along the play is the history of a sequential sampler
(`obsHist_obs`); the expected regret is then the finite tree sum of `thmC_tree`, with the comparator of
`comparator_net` and `sInf_inner_le`, and `log m ≤ d log (1 + 4 D / ε)` for the size `m` of the net (Lemma 7.12). -/
theorem AdversarialBco.thmC_learner {d : ℕ} (hd : 1 ≤ d) (K : Set (AdversarialBco.E d)) (hKc : IsCompact K)
    (hK : Convex ℝ K) (c : AdversarialBco.E d) (hc : Metric.closedBall c 1 ⊆ K) (n : ℕ) (hn : 2 ≤ n) (D : ℝ)
    (hD : Metric.diam K ≤ D) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hH : AdversarialBco.HypH {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} n 0 1 α β) (ε η tol : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / 4) (hη : 0 < η) (htol : 0 < tol) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (pol : (t : ℕ) → Ω → (Fin t → ℝ) → AdversarialBco.E d), AdversarialBco.IsLearner K pol ∧
        (∀ f ∈ AdversarialBco.Advs K n, Integrable (fun ω => AdversarialBco.regret K f (fun t => pol t ω) n) μ) ∧
        ∀ f ∈ AdversarialBco.Advs K n, AdversarialBco.expReg K μ pol f n ≤
          1 + n * n * ε + d * Real.log (1 + 4 * D / ε) / η +
            n * ((1 + 2 * n * ε) * α + n * ε * (1 + √β) + η * β / 8 + tol) := by
  classical
  set J : Set (AdversarialBco.E d) := {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} with hJdef
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hinv0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact hn1r
  -- the inner body
  have hJc : Convex ℝ J := AdversarialBco.convex_inner K hK _
  have hJk : IsCompact J := AdversarialBco.isCompact_inner K hKc _ hinv0
  have hJm : MeasurableSet J := hJk.isClosed.measurableSet
  have hcJ : c ∈ J := AdversarialBco.closedBall_subset_inner K c hc (1 / n) hinv0 hinv1
    (Metric.mem_closedBall_self (by linarith))
  have hJK : J ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hinv0)
  have hJD : Metric.diam J ≤ D := (Metric.diam_mono hJK hKc.isBounded).trans hD
  have hD0 : 0 ≤ D := Metric.diam_nonneg.trans hJD
  -- the net
  obtain ⟨m, pt, pr, hpt, hprm, hcov, hcard⟩ :=
    AdversarialBco.exists_net_fin J hJk.isBounded ⟨c, hcJ⟩ D ε hJD hε
  -- the class P_L on the net, L = n
  set P : Set (Fin (m + 1) → ℝ) := {v | (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ s : Fin (m + 1) → AdversarialBco.E d, (∀ i, ‖s i‖ ≤ (n : ℝ)) ∧
      ∀ i j, v i + inner ℝ (s i) (pt j - pt i) ≤ v j} with hP
  have hPc : Convex ℝ P := AdversarialBco.convex_PL pt n
  have hPk : IsCompact P := AdversarialBco.isCompact_PL pt n
  have hPne : P.Nonempty := ⟨0, fun i => by simp, 0, fun i => by simp, fun i j => by simp⟩
  -- the round value
  set Γ : ℝ := (1 + 2 * n * ε) * α + n * ε * (1 + √β) + η * β / 8 + tol with hΓ
  have hΓ0 : 0 ≤ Γ := by
    have : 0 ≤ (1 + 2 * n * ε) * α := mul_nonneg (by positivity) hα
    have : 0 ≤ (n : ℝ) * ε * (1 + √β) := by positivity
    have : 0 ≤ η * β / 8 := by positivity
    linarith
  have hround : ∀ q : Fin (m + 1) → ℝ, ∃ pg : (Fin (m + 1) → ℝ) × (Fin (m + 1) → Bool → Fin (m + 1) → ℝ),
      (∀ z, 0 < q z) → ∑ z, q z = 1 → ((pg.1 ∈ stdSimplex ℝ (Fin (m + 1)) ∧ ∀ x b,
        (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨
          (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)) ∧
        ∀ y, ∀ f ∈ P, ∑ x, pg.1 x * f x - f y +
          ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y) ≤ Γ) := by
    intro q
    by_cases hq : (∀ z, 0 < q z) ∧ ∑ z, q z = 1
    · obtain ⟨pg, hpg, hval⟩ := AdversarialBco.round_exists η hη q hq.1 P hPc hPk hPne Γ
        (AdversarialBco.value_dual J hJc hJm n ε α β η tol hnpos.le hε.le hβ hη htol hH pt hpt pr hprm
          (fun z hz => by rw [← dist_eq_norm]; exact (hcov z hz).le) q hq.1 hq.2)
      exact ⟨pg, fun _ _ => ⟨hpg, fun y f hf => (hval y f hf).le⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hq⟩
  choose sol hsol using hround
  -- the weights, the law of the action, the sampler
  set est : (Fin (m + 1) → ℝ) → Fin (m + 1) × Bool → Fin (m + 1) → ℝ :=
    fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1 with hest
  set Q := AdversarialBco.ewQ η est with hQ
  have hQps : ∀ t h, (∀ z, 0 < Q t h z) ∧ ∑ z, Q t h z = 1 := fun t h => AdversarialBco.ewQ_pos_sum η est t h
  set pS : (t : ℕ) → (Fin t → Fin (m + 1) × Bool) → Fin (m + 1) → ℝ := fun t h => (sol (Q t h)).1 with hpS
  have hpS : ∀ t h, pS t h ∈ stdSimplex ℝ (Fin (m + 1)) := fun t h =>
    ((hsol (Q t h) (hQps t h).1 (hQps t h).2).1).1
  obtain ⟨S, hSm, hS⟩ := AdversarialBco.exists_sampler m
  have hSp : ∀ t h i, volume (Set.Icc (0 : ℝ) 1 ∩ S (pS t h) ⁻¹' {i}) = ENNReal.ofReal (pS t h i) :=
    fun t h => hS (pS t h) (hpS t h).1 (hpS t h).2
  -- the learner: round map, action, seed law, seed extension, policy
  set R : (t : ℕ) → (Fin t → Fin (m + 1) × Bool) → ℝ × ℝ → ℝ → Fin (m + 1) × Bool :=
    fun t h u y => (S (pS t h) u.1, decide (u.2 ≤ max 0 (min 1 y))) with hR
  set A : (t : ℕ) → (Fin t → Fin (m + 1) × Bool) → ℝ × ℝ → AdversarialBco.E d :=
    fun t h u => pt (S (pS t h) u.1) with hA
  set ν : Measure (ℝ × ℝ) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))
    with hν
  haveI hU : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set ext : (Fin n → ℝ × ℝ) → ℕ → ℝ × ℝ := fun ω s => if hs : s < n then ω ⟨s, hs⟩ else (0, 0) with hext
  have hextm : Measurable ext := AdversarialBco.measurable_extendSeed n (0, 0)
  set pol : (t : ℕ) → (Fin n → ℝ × ℝ) → (Fin t → ℝ) → AdversarialBco.E d :=
    fun t ω y => A t (AdversarialBco.obsHist R t (ext ω) y) (ext ω t) with hpol
  have hRm : ∀ t h τ, MeasurableSet {p : (ℝ × ℝ) × ℝ | R t h p.1 p.2 = τ} := fun t h τ =>
    AdversarialBco.measurableSet_coinStep S hSm (pS t h) τ
  have hAm : ∀ t h, Measurable (A t h) := fun t h =>
    measurable_from_top.comp (hSm.comp (measurable_const.prodMk (measurable_fst)))
  refine ⟨Fin n → ℝ × ℝ, inferInstance, Measure.pi fun _ => ν, inferInstance, pol, ⟨fun t => ?_, fun t ω y => ?_⟩,
    ?_⟩
  · exact AdversarialBco.measurable_obsPolicy R hRm A hAm ext hextm t
  · exact hJK (hpt _)
  -- a fixed admissible sequence
  have key : ∀ f ∈ AdversarialBco.Advs K n,
      Integrable (fun ω => AdversarialBco.regret K f (fun t => pol t ω) n) (Measure.pi fun _ => ν) ∧
        AdversarialBco.expReg K (Measure.pi fun _ => ν) pol f n ≤
          1 + n * n * ε + d * Real.log (1 + 4 * D / ε) / η + n * Γ := by
    intro f hf
    -- the coin means on the net, clamped into [0, 1] (no change for t < n)
    set a : ℕ → Fin (m + 1) → ℝ := fun t x => max 0 (min 1 (f t (pt x))) with ha_def
    have ha01 : ∀ t x, a t x ∈ Set.Icc (0 : ℝ) 1 := fun t x =>
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    have haf : ∀ t < n, ∀ x, a t x = f t (pt x) := by
      intro t ht x
      obtain ⟨h0, h1⟩ := (hf t ht).2 (pt x) (hJK (hpt x))
      simp only [ha_def, min_eq_right h1, max_eq_right h0]
    -- the sequential sampler of the play against f
    set σ : (t : ℕ) → (Fin t → Fin (m + 1) × Bool) → ℝ × ℝ → Fin (m + 1) × Bool :=
      fun t h u => R t h u (f t (A t h u)) with hσ
    set κ : (t : ℕ) → (Fin t → Fin (m + 1) × Bool) → Fin (m + 1) × Bool → ℝ :=
      fun t h τ => pS t h τ.1 * (if τ.2 then a t τ.1 else 1 - a t τ.1) with hκ
    have hlaw : ∀ t h (τ : Fin (m + 1) × Bool),
        MeasurableSet (σ t h ⁻¹' {τ}) ∧ ν.real (σ t h ⁻¹' {τ}) = κ t h τ := by
      intro t h τ
      obtain ⟨i, b⟩ := τ
      have hc := AdversarialBco.coin_sampler_law S hSm (pS t h) (hSp t h) (hpS t h).1 (a t) (ha01 t) i b
      have hset : σ t h ⁻¹' {(i, b)} =
          {uv : ℝ × ℝ | (S (pS t h) uv.1, decide (uv.2 ≤ a t (S (pS t h) uv.1))) = (i, b)} := rfl
      rw [hset]
      refine ⟨hc.1, hc.2.trans ?_⟩
      cases b <;> simp [hκ]
    set H : (Fin n → ℝ × ℝ) → Fin n → Fin (m + 1) × Bool := AdversarialBco.seqHist σ n with hHdef
    have hHm : ∀ h, MeasurableSet (H ⁻¹' {h}) := fun h =>
      AdversarialBco.measurableSet_seqHist σ (fun t h τ => (hlaw t h τ).1) n h
    -- the loss of round t is read on the history of the sampler
    have hloss : ∀ ω (t : ℕ) (ht : t < n),
        f t (pol t ω (AdversarialBco.obs f (fun t => pol t ω) t)) = f t (pt (H ω ⟨t, ht⟩).1) := by
      intro ω t ht
      have h1 := AdversarialBco.obsHist_obs R A f (ext ω) t
      have h2 : (fun i : Fin t => ext ω i) = fun i : Fin t => ω (Fin.castLE ht.le i) := by
        funext i
        simp only [hext, show (i : ℕ) < n from lt_trans i.2 ht, ↓reduceDIte]
        rfl
      have h3 := AdversarialBco.seqHist_castLE σ n t ht.le ω
      have h4 := AdversarialBco.seqHist_apply σ n ω ⟨t, ht⟩
      have h5 : ext ω t = ω ⟨t, ht⟩ := by simp only [hext, ht, ↓reduceDIte]
      have h6 : pol t ω (AdversarialBco.obs f (fun t => pol t ω) t) =
          A t (AdversarialBco.seqHist σ t (fun i : Fin t => ω (Fin.castLE ht.le i))) (ω ⟨t, ht⟩) := by
        show A t (AdversarialBco.obsHist R t (ext ω) (AdversarialBco.obs f (fun t => pol t ω) t)) (ext ω t) = _
        rw [h1, h2, h5]
      rw [h6]
      show f t (A t _ (ω ⟨t, ht⟩)) = f t (pt (AdversarialBco.seqHist σ n ω ⟨t, ht⟩).1)
      rw [h4, ← h3]
    have hreg : ∀ ω, AdversarialBco.regret K f (fun t => pol t ω) n =
        (∑ t : Fin n, f t (pt (H ω t).1)) - sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) := by
      intro ω
      simp only [AdversarialBco.regret]
      congr 1
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun t _ => hloss ω t t.2
    set sK : ℝ := sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) with hsK
    set G : (Fin n → Fin (m + 1) × Bool) → ℝ := fun h => (∑ t : Fin n, f t (pt (h t).1)) - sK with hG
    have hregG : (fun ω => AdversarialBco.regret K f (fun t => pol t ω) n) = fun ω => G (H ω) := funext hreg
    refine ⟨?_, ?_⟩
    · rw [hregG]
      exact AdversarialBco.integrable_of_finite_fibers _ H hHm G
    -- the expected regret as a sum over the tree of histories
    have hexp : AdversarialBco.expReg K (Measure.pi fun _ => ν) pol f n =
        ∑ h : Fin n → Fin (m + 1) × Bool,
          (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) * G h := by
      simp only [AdversarialBco.expReg]
      rw [hregG]
      exact AdversarialBco.integral_seqHist ν σ (fun t h τ => (hlaw t h τ).1) κ (fun t h τ => (hlaw t h τ).2) n G
    rw [hexp]
    -- the kernels sum to one, and so do the weights of the histories
    have hκ1 : ∀ t h, ∑ τ, κ t h τ = 1 := by
      intro t h
      rw [Fintype.sum_prod_type, ← (hpS t h).2]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hκ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
      ring
    set W : (Fin n → Fin (m + 1) × Bool) → ℝ :=
      fun h => ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) with hW
    have hW1 : ∑ h, W h = 1 := AdversarialBco.sum_prod_policy κ hκ1 n
    -- the losses on the net are in P_L for t < n
    have haP : ∀ t < n, a t ∈ P := by
      intro t ht
      have ha' : a t = fun x => f t (pt x) := funext (haf t ht)
      rw [ha']
      exact AdversarialBco.PL_of_adm K hK n hn1 pt hpt (f t) (hf t ht)
    -- the comparator: a point of the net, then the inner body, then K
    have hfL : ∀ t < n, ∀ x ∈ J, ∀ y ∈ J, |f t x - f t y| ≤ (n : ℝ) * ‖x - y‖ := fun t ht x hx y hy =>
      AdversarialBco.abs_sub_le_inner K (f t) (hf t ht).1 (hf t ht).2 n hn1 x y hx hy
    obtain ⟨y, hy⟩ := AdversarialBco.comparator_net J ⟨c, hcJ⟩ pt pr ε hcov n n hnpos.le f hfL hpt
    have hJK1 : sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' J) ≤ sK + 1 :=
      AdversarialBco.sInf_inner_le K hK c hc n hn1 f (fun t ht => (hf t ht).1) (fun t ht => (hf t ht).2)
    -- Theorem 7.2 on the tree
    have htree : ∑ h, W h * ∑ t : Fin n, (a t (h t).1 - a t y) ≤
        Real.log (Fintype.card (Fin (m + 1))) / η + n * Γ :=
      AdversarialBco.thmC_tree η hη sol P Γ hΓ0 hsol n a ha01 haP y
    have hlog : Real.log (Fintype.card (Fin (m + 1))) / η ≤ d * Real.log (1 + 4 * D / ε) / η := by
      refine div_le_div_of_nonneg_right ?_ hη.le
      rw [Fintype.card_fin]
      exact AdversarialBco.log_card_le (m + 1) d D ε hD0 hε (by omega) hcard
    have hGsplit : ∀ h : Fin n → Fin (m + 1) × Bool, G h = (∑ t : Fin n, (a t (h t).1 - a t y)) +
        ((∑ t ∈ Finset.range n, f t (pt y)) - sK) := by
      intro h
      simp only [hG]
      rw [Finset.sum_range, Finset.sum_sub_distrib]
      have e1 : ∀ t : Fin n, a t (h t).1 = f t (pt (h t).1) := fun t => haf t t.2 _
      have e2 : ∀ t : Fin n, a t y = f t (pt y) := fun t => haf t t.2 _
      simp only [e1, e2]
      ring
    have hsplit : ∑ h, W h * G h = ∑ h, W h * (∑ t : Fin n, (a t (h t).1 - a t y)) +
        ((∑ t ∈ Finset.range n, f t (pt y)) - sK) * ∑ h, W h := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hGsplit h]
      ring
    show ∑ h, W h * G h ≤ _
    rw [hsplit, hW1, mul_one]
    linarith
  exact ⟨fun f hf => (key f hf).1, fun f hf => (key f hf).2⟩

/-- Corollary 1.2 of the frozen statement from the statement of `body_H` taken as a hypothesis (the proof of Corollary
1.2 in Section 7 of the paper): (H)[1/n, C_B betahat] on the inner
body; for `d < n`, `thmC_learner` with the parameters of the proof of Corollary 1.2 and `minimaxRegret_le_of_learner` give the bound
with the constant `2 (1 + C_B) + 6 + (C_B/2)^{1/2}` (`thmC_c_main`, `thmC_c_final`); for `d ≥ n`, the regret is at most
`n` (`minimaxRegret_le_n`, `thmC_c_large`). -/
theorem AdversarialBco.corollaryADV_of_bodyH
    (hbodyH : ∃ CB : ℝ, 1 ≤ CB ∧ ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (AdversarialBco.E d),
    IsCompact K → Convex ℝ K → ∀ c : AdversarialBco.E d, Metric.closedBall c 1 ⊆ K → ∀ D : ℝ, Metric.diam K ≤ D →
      AdversarialBco.HypH {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} n 0 1 (1 / n)
        (CB * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n))) :
    AdversarialBco.CorollaryADV := by
  obtain ⟨CB, hCB, hbody⟩ := hbodyH
  refine ⟨2 * (1 + CB) + 6 + √(CB / 2), fun d hd n hn K hKc hK hball => ?_⟩
  obtain ⟨c, hc⟩ := hball
  have hD2 : 2 ≤ Metric.diam K := AdversarialBco.two_le_diam hd K hKc.isBounded c hc
  have hC0 : 1 ≤ 2 * (1 + CB) + 6 + √(CB / 2) := by
    have := Real.sqrt_nonneg (CB / 2)
    linarith
  have hKne : K.Nonempty := ⟨c, hc (Metric.mem_closedBall_self zero_le_one)⟩
  rcases le_or_gt n d with hdn | hdn
  · -- d ≥ n: the regret is at most n
    exact (AdversarialBco.minimaxRegret_le_n K hKne n).trans
      (AdversarialBco.thmC_c_large d n hn hdn (Metric.diam K) _ hD2 hC0)
  -- d < n: the parameters of the proof of Corollary 1.2
  set D := Metric.diam K with hDdef
  set bh : ℝ := (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) with hbh
  obtain ⟨hε0, hε4, hbh0, hΛ0⟩ := AdversarialBco.thmC_c_params d n hd hn D hD2
  obtain ⟨hbh1, hbh2, hΛ6⟩ := AdversarialBco.thmC_c_logs d n hd hn hdn D hD2
  set ε : ℝ := 1 / ((n : ℝ) ^ 2 * √(2 * bh)) with hε
  set Λ : ℝ := d * Real.log (1 + 4 * D / ε) with hΛ
  have hnpos : (0 : ℝ) < n := by positivity
  set η : ℝ := √(8 * Λ / (n * bh)) with hη
  have hηpos : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hβ : CB * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) = CB * bh := by
    rw [hbh]
    ring
  have hβ0 : 0 ≤ CB * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) := by
    rw [hβ]
    exact mul_nonneg (by linarith) hbh0.le
  have hHyp := hbody d hd n hn K hKc hK c hc D le_rfl
  obtain ⟨Ω, _, μ, _, pol, hpol, hint, hB⟩ := AdversarialBco.thmC_learner hd K hKc hK c hc n hn D le_rfl (1 / n)
    (CB * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n)) (by positivity) hβ0 hHyp ε η (1 / n)
    hε0 hε4 hηpos (by positivity)
  have hmm := AdversarialBco.minimaxRegret_le_of_learner K hK n μ pol hpol hint _ hB
  rw [hβ] at hmm
  have hmain := AdversarialBco.thmC_c_main n hn bh CB Λ hbh1 hCB hΛ0
  have hfinal := AdversarialBco.thmC_c_final d n hd hn D CB bh Λ hD2 hCB hbh0.le hbh2 hΛ0.le hΛ6
  exact hmm.trans (hmain.trans hfinal)
