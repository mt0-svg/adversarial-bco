/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.Proc

@[expose] public section

/-!
# Theorem PG-core for Procedure PG-N

The proof of Theorem PG-core (`pgCoreThmN`) for the procedure of Conj1Arith/Proc.lean: the descent `pgDescentN C`
over the projection `pgProjR C`, the strict test `pgTestS`. The proof reads the routine only through `pgProjR_mem`,
`pgProjR_measurable` and, in the bound of the round (`pgDescentN_expect`, E1a), `pgProjR_near` with Lemma SGD-e. The
strict verdict enters through the leaves D2 of Conj1Arith/Verdict.lean; the lemmas on PG it uses are those of
Poly/PgProcBase.lean and Poly/PgProcProof.lean (`pgVerdict_sound`, `pgMin_exists`, `prod_compl_le`, `pgCoreHyps_of`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly

/-- Amplification for the strict verdict: when the basic verdict holds only on (resp. fails only on) a measurable set
`B` of Gaussian measure at most `1/4`, the amplified test `pgTestS` accepts (resp. rejects) with probability at most
`pgDp δ`. -/
theorem pgAmplifyS (hMH : MajorityHoeffding) (hHo : PgHoeffding) (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (x : PgSp d) (B : Set (ℕ → EuclideanSpace ℝ (Fin d))) (hB : MeasurableSet B)
    (hνB : (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) B ≤ ENNReal.ofReal (1 / 4))
    (_hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdictS K ρ x w}) :
    ((∀ w, pgVerdictS K ρ x w → w ∈ B) →
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        {W | pgTestS K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ)) ∧
    ((∀ w, ¬ pgVerdictS K ρ x w → w ∈ B) →
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        {W | ¬ pgTestS K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ)) := by
  classical
  set m := pgMT δ
  set ν_inner := stdGaussian (EuclideanSpace ℝ (Fin d))
  set ν' := Measure.infinitePi fun _ : ℕ => ν_inner
  have hνB' : ν' B ≤ 1 / 4 := by
    -- hνB : ν' B ≤ ENNReal.ofReal (1/4)
    -- ENNReal.ofReal (1/4) = (1/4 : ENNReal)
    simpa using hνB
  have hMHapp := hMH (ℕ → EuclideanSpace ℝ (Fin d)) ν' B hB hνB'
  have hMHapp_m := hMHapp m
  have hJpos : 0 < pgJr δ := by
    have hlog : 0 < Real.logb 2 (4 / δ) :=
      Real.logb_pos (by norm_num) (((one_lt_div (a := 4) hδ0).mpr (by linarith)))
    exact Nat.ceil_pos.mpr hlog
  have hpos_dp : 0 < pgDp δ := by
    have hJpos' : (0 : ℝ) < pgJr δ := Nat.cast_pos.mpr hJpos
    refine div_pos hδ0 (by nlinarith)
  have h_ineq : 8 * Real.log (1 / pgDp δ) ≤ (m : ℝ) := by
    have h_eq : 1 / pgDp δ = 2 * pgJr δ / δ := by
      dsimp [pgDp]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hJpos)]
    rw [h_eq]
    dsimp [m, pgMT]
    have hpos_log : 0 ≤ 8 * Real.log (2 * pgJr δ / δ) := by
      have hpos_arg : 1 < 2 * pgJr δ / δ := by
        have hJr_ge_1 : (1 : ℝ) ≤ pgJr δ := mod_cast Nat.one_le_of_lt hJpos
        have h_one_div_δ_gt_1 : 1 < 1 / δ := one_lt_one_div hδ0 hδ1
        have h_mul : (1 : ℝ) < 2 * (pgJr δ) * (1 / δ) := by
          nlinarith
        simpa [div_eq_mul_inv] using h_mul
      have hlog_pos : 0 < Real.log (2 * pgJr δ / δ) := Real.log_pos hpos_arg
      nlinarith
    have hceil : (⌈8 * Real.log (2 * pgJr δ / δ)⌉₊ : ℝ) = (pgMT δ : ℝ) := by
      dsimp [m, pgMT]
    -- Goal: a ≤ (⌈a⌉₊ : ℝ)
    -- This follows from Nat.ceil_le.mp with n := ⌈a⌉₊
    apply (Nat.ceil_le (a := 8 * Real.log (2 * pgJr δ / δ)) (n := ⌈8 * Real.log (2 * pgJr δ / δ)⌉₊)).mp
    exact le_refl _
  have hPgHo := hHo (pgDp δ) hpos_dp m h_ineq
  have h_bound_dp : ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) ≤ ENNReal.ofReal (pgDp δ) :=
    ENNReal.ofReal_le_ofReal hPgHo
  constructor
  · intro h_accept
    have h_subset : {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | pgTestS K ρ δ x W} ⊆
        {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} := by
      intro W hW
      have hmem : pgTestS K ρ δ x W := hW
      have hcard_lt : (m : ℝ) / 2 < ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card := hmem
      have hfilter_subset : ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)) ⊆
        ((Finset.range m).filter fun i => W i ∈ B) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        rcases hi with ⟨hi_range, hi_verdict⟩
        exact ⟨hi_range, h_accept (W i) hi_verdict⟩
      have hcard_le : ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card ≤
        ((Finset.range m).filter fun i => W i ∈ B).card :=
        Finset.card_le_card hfilter_subset
      have h_ineq_card : (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card := by
        have hcard_le' : (((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card : ℝ) ≤
          (((Finset.range m).filter fun i => W i ∈ B).card : ℝ) := by exact_mod_cast hcard_le
        linarith
      exact h_ineq_card
    have h_measure_le : (Measure.infinitePi fun _ : ℕ => ν') {W | pgTestS K ρ δ x W} ≤
        (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} :=
      measure_mono h_subset
    have h_bound : (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := hMHapp_m
    exact h_measure_le.trans (h_bound.trans h_bound_dp)
  · intro h_reject
    have h_subset : {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | ¬ pgTestS K ρ δ x W} ⊆
        {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} := by
      intro W hW
      have hmem : ¬ pgTestS K ρ δ x W := hW
      have h_contra : ∀ w, w ∉ B → pgVerdictS K ρ x w := by
        intro w hwB
        by_contra h_not_verdict
        apply hwB
        exact h_reject w h_not_verdict
      have hcard_not_gt : ¬ (m : ℝ) / 2 < ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card := hmem
      have hcard_le_verdict : (((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card : ℝ) ≤ (m : ℝ) / 2 := by
        by_contra h
        apply hcard_not_gt
        push_cast
        linarith
      have h_B_subset : ((Finset.range m).filter fun i => W i ∉ B) ⊆
        ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        rcases hi with ⟨hi_range, hi_not_B⟩
        exact ⟨hi_range, h_contra (W i) hi_not_B⟩
      have h_card_B_le : ((Finset.range m).filter fun i => W i ∉ B).card ≤
        ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card :=
        Finset.card_le_card h_B_subset
      have h_card_notB_le : (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) ≤ (m : ℝ) / 2 := by
        have h : ((Finset.range m).filter fun i => W i ∉ B).card ≤ ((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card :=
          h_card_B_le
        have h' : (((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card : ℝ) ≤ (m : ℝ) / 2 := hcard_le_verdict
        have h_cast : (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) ≤ (((Finset.range m).filter fun i => pgVerdictS K ρ x (W i)).card : ℝ) := by
          exact_mod_cast h
        linarith
      have h_card_B_ge : (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card := by
        have h_total : ((Finset.range m).filter fun i => W i ∈ B).card + ((Finset.range m).filter fun i => W i ∉ B).card = m := by
          rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
        have h_total' : (((Finset.range m).filter fun i => W i ∈ B).card : ℝ) + (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) = (m : ℝ) := by
          exact_mod_cast h_total
        push_cast
        linarith
      exact h_card_B_ge
    have h_measure_le : (Measure.infinitePi fun _ : ℕ => ν') {W | ¬ pgTestS K ρ δ x W} ≤
        (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} :=
      measure_mono h_subset
    have h_bound : (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := hMHapp_m
    exact h_measure_le.trans (h_bound.trans h_bound_dp)


/-- The average point of the descent lies in `pgDom d ρ`. -/
theorem pgDescentN_mem (C : ClampRoutine) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (a : ℕ → EuclideanSpace ℝ (Fin d)) : pgDescentN C K ρ a ∈ pgDom d ρ := by
  unfold pgDescentN sgdAvg
  have hN : (pgNs d ρ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (pgNs d ρ : ℝ) := by exact_mod_cast pgNs_pos d ρ hd hρ
    linarith
  have h_iter_mem : ∀ t ∈ Finset.range (pgNs d ρ),
      sgdIter (pgProjR C d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t ∈ pgDom d ρ := by
    intro t _
    cases t with
    | zero => exact pgX1_mem d ρ hd hρ
    | succ t => exact pgProjR_mem C hd hρ _
  rw [Finset.smul_sum]
  exact (pgDom_convex d ρ).sum_mem (fun _ _ => by positivity) (by simp [hN]) h_iter_mem

/-- The descent is measurable in its draws, the projection `pgProjR C` being measurable. -/
theorem pgDescentN_measurable (C : ClampRoutine) (hPT : PiTildeMeasurable) (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hK : IsClosed K) : Measurable (pgDescentN C K ρ) := by
  have h := PgMeas.sgdAvg_family_measurable (X := Unit) (pgProjR C d ρ) (pgProjR_measurable C d ρ)
    (fun _ => pgV K ρ) ((pgV_measurable hPT d K ρ hK).comp measurable_snd) (pgStepSize d ρ) (pgX1 d ρ) (pgNs d ρ)
  exact h.comp (measurable_const.prodMk measurable_id : Measurable fun a : ℕ → EuclideanSpace ℝ (Fin d) => ((), a))

/-- `pgH` at the average point of the descent is measurable in the draws. -/
theorem pgH_descN_measurable (C : ClampRoutine) (hPT : PiTildeMeasurable) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    Measurable fun a : ℕ → EuclideanSpace ℝ (Fin d) => pgH K (pgDescentN C K ρ a) := by
  have h_mem : ∀ a, pgDescentN C K ρ a ∈ pgDom d ρ := fun a => pgDescentN_mem C d ρ hd hρ K a
  have h_restrict_meas : Measurable ((pgDom d ρ).domRestrict (pgH K)) :=
    (pgH_continuousOn d ρ hd hρ K hK).domRestrict.measurable
  have h_subtype_meas : Measurable (fun a => (⟨pgDescentN C K ρ a, h_mem a⟩ : pgDom d ρ)) :=
    Measurable.subtype_mk (pgDescentN_measurable C hPT d K ρ hK.2.1) (h := h_mem)
  simpa [Set.domRestrict_eq, Function.comp_def] using h_restrict_meas.comp h_subtype_meas

/-- `pgH` at the average point of the descent is integrable in the draws (it is bounded on `pgDom d ρ`). -/
theorem pgH_descN_integrable (C : ClampRoutine) (hPT : PiTildeMeasurable) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d)
    (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    Integrable (fun a : ℕ → EuclideanSpace ℝ (Fin d) => pgH K (pgDescentN C K ρ a))
      (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rcases pgH_bdd d ρ hd hρ K hK with ⟨B, hB⟩
  refine Integrable.mono' (integrable_const B) (pgH_descN_measurable C hPT d ρ hd hρ K hK).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  simpa using hB _ (pgDescentN_mem C d ρ hd hρ K a)

open Classical in
/-- The amplified strict test is a measurable event of the point and the draws. -/
theorem pgTestS_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTestS K ρ δ p.1 p.2} := by
  have hV : ∀ i, MeasurableSet {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdictS K ρ p.1 (p.2 i)} :=
    fun i => by
      have h' := (pgVerdictS_measurableSet hPT d K ρ hK).preimage
        (f := fun p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) => (p.1, p.2 i)) (by fun_prop)
      simpa only [Set.preimage_ofPred_eq] using h'
  have h := PgMeas.count_generic_measurableSet
    (fun i (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => pgVerdictS K ρ p.1 (p.2 i)) hV
    (inst := fun i q => Classical.dec _) (pgMT δ) ((pgMT δ : ℝ) / 2)
  convert h using 2 with p
  simp only [pgTestS]

/-- With the leaves D2: at a point of `pgDom d ρ` that is not sound, the amplified strict test accepts with probability
at most `pgDp δ`. -/
theorem pgTestS_unsound (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (hns : ¬ PgSound K ρ x) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {W | pgTestS K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ) := by
  have hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j := fun v =>
    posQ_eq_sum K hK.1 hK.2.2.1 (pgMu x) (pgOp x) v v
  have hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdictS K ρ x w} := by
    have h := (pgVerdictS_measurableSet H.hPT d K ρ hK.2.1).preimage (measurable_prodMk_left (x := x))
    exact h
  refine (pgAmplifyS H.hMH H.hHo d K ρ δ hδ0 hδ1 x {w | ¬ PgAccurateS K ρ x w}
    (pgAccurateS_measurableSet H.hPT d K ρ hK.2.1 x).compl (pgNotAccurateS_le H d ρ hd hρ K hK x hx) hmeas).1 ?_
  intro w hv hacc
  exact hns (pgVerdict_sound d ρ hd K x hQ w (pgAccurate_of_pgAccurateS K ρ x w hacc) (pgVerdict_of_pgVerdictS K ρ x w hv))

/-- With the leaves D2: at a complete point of `pgDom d ρ`, the amplified strict test rejects with probability at most
`pgDp δ`. -/
theorem pgTestS_complete (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (hc : PgComplete K ρ x) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {W | ¬ pgTestS K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ) := by
  have hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j := fun v =>
    posQ_eq_sum K hK.1 hK.2.2.1 (pgMu x) (pgOp x) v v
  have hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdictS K ρ x w} := by
    have h := (pgVerdictS_measurableSet H.hPT d K ρ hK.2.1).preimage (measurable_prodMk_left (x := x))
    exact h
  refine (pgAmplifyS H.hMH H.hHo d K ρ δ hδ0 hδ1 x {w | ¬ PgAccurateS K ρ x w}
    (pgAccurateS_measurableSet H.hPT d K ρ hK.2.1 x).compl (pgNotAccurateS_le H d ρ hd hρ K hK x hx) hmeas).2 ?_
  intro w hv hacc
  exact hv (pgVerdictS_complete d ρ hd K x hQ w hacc hc)

/-- E1a: the bound of the round, with Lemma SGD-e, Lemma N, B3 and the row C1: the expectation of `pgH` at the average
point of the descent exceeds its minimum `pgH K xs` over `pgDom d ρ` by at most `pgEh d ρ / 2`. -/
theorem pgDescentN_expect (C : ClampRoutine) (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (xs : PgSp d) (hxs : xs ∈ pgDom d ρ)
    (hmin : ∀ y ∈ pgDom d ρ, pgH K xs ≤ pgH K y) :
    ∫ a, pgH K (pgDescentN C K ρ a) ∂(Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      pgH K xs + pgEh d ρ / 2 := by
  have hcpt := pgDom_isCompact d ρ
  have hcv := pgDom_convex d ρ
  have hEP : 0 ≤ pgEP d ρ := by
    have := pgEh_pos d ρ hd hρ
    unfold pgEP
    positivity
  have hS := sgdExpectE (PgSp d) (EuclideanSpace ℝ (Fin d)) (stdGaussian (EuclideanSpace ℝ (Fin d))) (pgDom d ρ)
    (pgProjR C d ρ) (pgH K) (pgGam K) (pgV K ρ) xs (pgX1 d ρ) (pgDelta d ρ) (pgStepSize d ρ) (pgG2q d ρ)
    (pgBeta d ρ) (pgEP d ρ) pgTheta (pgNs d ρ) hcpt hcv (pgH_continuousOn d ρ hd hρ K hK)
    (pgProjR_measurable C d ρ) (pgProjR_mem C hd hρ) (fun y z hz => pgProjR_near C hd hρ y z hz)
    (pgV_measurable H.hPT d K ρ hK.2.1) (pgX1_mem d ρ hd hρ) hxs hmin (pgDom_diam d ρ hd hρ)
    (pgGam_subgrad H.hD5 d ρ hd hρ K hK) (fun x hx => ⟨(pgV_integrable H.hPT H.hLB H.hD4 H.hEta d ρ hd hρ K hK x hx).1,
      (pgV_integrable H.hPT H.hLB H.hD4 H.hEta d ρ hd hρ K hK x hx).2,
      pgV_bias H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat d ρ hd hρ K hK x hx,
      pgV_second_momentN H.hPT H.hLB H.hD4 pgEtaSqN H.hFrob H.hMom d ρ hd hρ K hK x hx⟩)
    (pgStepSize_pos d ρ hd hρ) (pgNs_pos d ρ hd hρ) hEP (by norm_num [pgTheta])
  have hrow := pgRowN d ρ hd hρ
  have hS' : ∫ a, pgH K (pgDescentN C K ρ a) ∂(Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ pgH K xs + pgDelta d ρ ^ 2 / (2 * pgStepSize d ρ * pgNs d ρ) +
        (1 + pgTheta) * pgStepSize d ρ * pgG2q d ρ / 2 + pgBeta d ρ * pgDelta d ρ +
        pgEP d ρ * pgDelta d ρ / pgStepSize d ρ + pgEP d ρ ^ 2 * (1 + 1 / pgTheta) / (2 * pgStepSize d ρ) := hS
  linarith

/-- The descent ends at a complete point outside an event of Gaussian measure at most `1/2`. -/
theorem pgDescentN_good (C : ClampRoutine) (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    ∃ G : Set (ℕ → EuclideanSpace ℝ (Fin d)), MeasurableSet G ∧
      (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) Gᶜ ≤ ENNReal.ofReal (1 / 2) ∧
      ∀ a ∈ G, PgComplete K ρ (pgDescentN C K ρ a) := by
  obtain ⟨xs, hxs, hmin⟩ := pgMin_exists H.hL H.hD1 H.hD1i H.hR H.hG d ρ hd hρ K hK
  have hminD : ∀ y ∈ pgDom d ρ, pgH K xs ≤ pgH K y := fun y hy =>
    hmin (pgMu y) (pgOp y) (by rw [pgOp_det]; exact (pgDom_inv d ρ hd hρ y hy).1)
  refine ⟨{a | pgH K (pgDescentN C K ρ a) ≤ pgH K xs + pgEh d ρ},
    measurableSet_le (pgH_descN_measurable C H.hPT d ρ hd hρ K hK) measurable_const, ?_, ?_⟩
  · have hc : ∀ a, pgH K xs ≤ pgH K (pgDescentN C K ρ a) := fun a => hminD _ (pgDescentN_mem C d ρ hd hρ K a)
    have hm := markov_half (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) _
      (pgH_descN_integrable C H.hPT d ρ hd hρ K hK) (pgH K xs) (pgEh d ρ) (pgEh_pos d ρ hd hρ) hc
      (pgDescentN_expect C H d ρ hd hρ K hK xs hxs hminD)
    refine le_trans (le_of_eq ?_) hm
    congr 1
    ext a
    simp [not_le]
  · intro a ha
    exact pgCorA H.hAi H.hAii H.hAiii H.hD4 H.hPAi H.hCAi H.hCAii H.hCAiii d ρ hd hρ K hK _
      (pgDescentN_mem C d ρ hd hρ K a) (pgH K xs) hmin ha

/-- The acceptance probability of the amplified test at the average of the descent driven by `a`. -/
noncomputable def pgAccProbN (C : ClampRoutine) {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (a : ℕ → EuclideanSpace ℝ (Fin d)) : ENNReal :=
  (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
    {W | pgTestS K ρ δ (pgDescentN C K ρ a) W}

/-- A measurable superset of the failure event of `pgCoreN`: a repeat accepts whose descent has acceptance
probability at most `δ'`, or no repeat accepts. -/
def pgCoreBadN (C : ClampRoutine) {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) : Set (ℕ → PgRound d) :=
  {ω | (∃ r < pgJr δ, pgTestS K ρ δ (pgDescentN C K ρ (ω r).1) (ω r).2 ∧
      pgAccProbN C K ρ δ (ω r).1 ≤ ENNReal.ofReal (pgDp δ)) ∨
    ∀ r < pgJr δ, ¬ pgTestS K ρ δ (pgDescentN C K ρ (ω r).1) (ω r).2}

/-- Outside `pgCoreBadN`, the output of `pgCoreN` is good. -/
theorem pgCoreN_good_of_not_bad (C : ClampRoutine) (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (ω : ℕ → PgRound d)
    (hω : ω ∉ pgCoreBadN C K ρ δ) : PgGood d K (36.4 * d * pgLam ρ) (pgCoreN C d K ρ δ ω) := by
  have key : ∀ r, r < pgJr δ → pgTestS K ρ δ (pgDescentN C K ρ (ω r).1) (ω r).2 →
      PgGood d K (36.4 * d * pgLam ρ) (some (pgOut (pgDescentN C K ρ (ω r).1))) := by
    intro r hr hacc
    have hprob : ENNReal.ofReal (pgDp δ) < pgAccProbN C K ρ δ (ω r).1 := by
      by_contra h
      exact hω (Or.inl ⟨r, hr, hacc, not_lt.mp h⟩)
    have hsound : PgSound K ρ (pgDescentN C K ρ (ω r).1) := by
      by_contra hns
      exact absurd (pgTestS_unsound H d ρ δ hd hρ hδ0 hδ1 K hK _ (pgDescentN_mem C d ρ hd hρ K _) hns)
        (not_le.mpr hprob)
    exact pgSound_good H.hCaB H.hCb H.hCc H.hG H.hNM H.hConc H.hQ d ρ hd hρ K hK _
      (pgDescentN_mem C d ρ hd hρ K _) hsound
  classical
  unfold pgCoreN
  split_ifs with h
  · exact key _ (Nat.find_spec h).1 (Nat.find_spec h).2
  · exact absurd (Or.inr fun r hr hacc => h ⟨r, hr, hacc⟩) hω

/-- The event `pgCoreBadN` has measure at most `δ`. -/
theorem pgCoreBadN_measure (C : ClampRoutine) (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    pgCoreMeasure d (pgCoreBadN C K ρ δ) ≤ ENNReal.ofReal δ := by
  obtain ⟨hJ1, hJ2, hDp0, hDp1⟩ := pgJr_spec δ hδ0 hδ1
  obtain ⟨Acc, hAccdef⟩ : ∃ Acc : Set (PgRound d), Acc = {p | pgTestS K ρ δ (pgDescentN C K ρ p.1) p.2} := ⟨_, rfl⟩
  have hAcc : MeasurableSet Acc := by
    rw [hAccdef]
    have h := (pgTestS_measurableSet H.hPT d K ρ δ hK.2.1).preimage
      (((pgDescentN_measurable C H.hPT d K ρ hK.2.1).comp measurable_fst).prodMk
        measurable_snd)
    exact h
  obtain ⟨B', hB'def⟩ : ∃ B' : Set (PgRound d), B' = {p | p ∈ Acc ∧
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        (Prod.mk p.1 ⁻¹' Acc) ≤ ENNReal.ofReal (pgDp δ)} := ⟨_, rfl⟩
  have hB' : MeasurableSet B' := by
    rw [hB'def]
    exact hAcc.inter (measurableSet_le ((measurable_measure_prodMk_left hAcc).comp measurable_fst) measurable_const)
  have hB'le : pgRoundMeasure d B' ≤ ENNReal.ofReal (pgDp δ) := by
    rw [hB'def]
    exact prod_small_slices _ _ Acc hAcc _
  obtain ⟨G, hG, hGc, hGcomp⟩ := pgDescentN_good C H d ρ hd hρ K hK
  have hrej : pgRoundMeasure d Accᶜ ≤ ENNReal.ofReal ((1 + pgDp δ) / 2) := by
    refine prod_compl_le _ _ Acc hAcc G hG (pgDp δ) hDp0.le hDp1 (fun a ha => ?_) hGc
    have h := pgTestS_complete H d ρ δ hd hρ hδ0 hδ1 K hK _ (pgDescentN_mem C d ρ hd hρ K a) (hGcomp a ha)
    rw [hAccdef]
    exact h
  have hsub : pgCoreBadN C K ρ δ ⊆ {ω | ∃ r < pgJr δ, ω r ∈ B'} ∪ {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} := by
    intro ω hω
    rcases hω with ⟨r, hr, hacc, hp⟩ | hall
    · left
      refine ⟨r, hr, ?_⟩
      rw [hB'def, hAccdef]
      exact ⟨hacc, hp⟩
    · right
      intro r hr
      rw [hAccdef]
      exact hall r hr
  have h1 : pgCoreMeasure d {ω | ∃ r < pgJr δ, ω r ∈ B'} ≤ pgJr δ * ENNReal.ofReal (pgDp δ) :=
    (H.hSome (PgRound d) (pgRoundMeasure d) B' hB' (pgJr δ)).trans (by gcongr)
  have h2 : pgCoreMeasure d {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} ≤ ENNReal.ofReal ((1 + pgDp δ) / 2) ^ pgJr δ :=
    (H.hAll (PgRound d) (pgRoundMeasure d) Accᶜ hAcc.compl (pgJr δ)).le.trans (ENNReal.pow_le_pow_left hrej)
  have hfail := H.hFail δ hδ0 hδ1 (pgJr δ) hJ1 hJ2
  have hDp : pgDp δ = δ / (2 * pgJr δ) := rfl
  have hfin : (pgJr δ : ℝ) * pgDp δ + ((1 + pgDp δ) / 2) ^ pgJr δ ≤ δ := by
    rw [hDp]; linarith
  calc pgCoreMeasure d (pgCoreBadN C K ρ δ)
      ≤ pgCoreMeasure d ({ω | ∃ r < pgJr δ, ω r ∈ B'} ∪ {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ}) := measure_mono hsub
    _ ≤ pgCoreMeasure d {ω | ∃ r < pgJr δ, ω r ∈ B'} + pgCoreMeasure d {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} :=
        measure_union_le _ _
    _ ≤ pgJr δ * ENNReal.ofReal (pgDp δ) + ENNReal.ofReal ((1 + pgDp δ) / 2) ^ pgJr δ := add_le_add h1 h2
    _ = ENNReal.ofReal (pgJr δ * pgDp δ + ((1 + pgDp δ) / 2) ^ pgJr δ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hfin

/-- Theorem PG-core for PG-N under the hypotheses `PgCoreHyps`. -/
theorem pgCoreThmN_of (C : ClampRoutine) (H : PgCoreHyps) : PgCoreThmN C := by
  intro d K ρ δ hd hKc hKcl h1 hKρ hρ hδ0 hδ1
  have hK : PgBody K ρ := ⟨hKc, hKcl, h1, hKρ⟩
  refine le_trans (measure_mono ?_) (pgCoreBadN_measure C H d ρ δ hd hρ hδ0 hδ1 K hK)
  intro ω hω
  by_contra hb
  exact hω (pgCoreN_good_of_not_bad C H d ρ δ hd hρ hδ0 hδ1 K hK ω hb)


/-- E1b: Theorem PG-core for PG-N. -/
theorem pgCoreThmN (C : ClampRoutine) : PgCoreThmN C :=
  pgCoreThmN_of C (pgCoreHyps_of chebAvg sgdExpect majorityHoeffding roundsSomeHit roundsAllMiss)

end AdversarialBco.Conj1Arith
