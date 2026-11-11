/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/

module

public import AdversarialBco.Poly.Cover

@[expose] public section

/-!
# Covers of a ball, the union bound and the Lipschitz completion: proofs

Proofs of the six interface statements of `AdversarialBco/Poly/Cover.lean`. The leaves are
`card_le_of_separated_ball`, `exists_net`, `quad_diff`, `log_card_net`, `union_bound_finset` (from
`MeasureTheory.measure_biUnion_finset_le`) and `quad_sum_diff`. The assemblies close the file.
-/

open MeasureTheory
open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.card_le_of_separated_ball {d : ℕ} (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (C : Finset (EuclideanSpace ℝ (Fin d))) (hCK : ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) :
    (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d := by
  -- If C is empty, the inequality is trivial since LHS = 0 and RHS ≥ 0
  by_cases hCempty : C.Nonempty
  · -- C is nonempty: pick a reference point x0
    obtain ⟨x0, hx0⟩ := hCempty
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
    -- Each ball B(x, ε/2) is contained in B(0, R + ε/2)
    have hball_subset : ∀ x ∈ C, Metric.ball x (ε / 2) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + ε / 2) := by
      intro x hx
      have hx_mem : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := hCK (by exact Finset.mem_coe.mpr hx)
      have hx_dist : dist x 0 ≤ R := hx_mem
      refine Metric.ball_subset_ball' ?_
      nlinarith
    -- The union is also contained
    have hunion_subset : (⋃ x ∈ C, Metric.ball x (ε / 2)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + ε / 2) := by
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
    -- Volume of the big ball: μ.real (ball 0 (R + ε/2)) = (R + ε/2)^d * μ.real (ball 0 1)
    have hball_big : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + ε / 2)) =
        (R + ε / 2) ^ d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) := by
      have hpos : 0 < R + ε / 2 := by
        have : 0 ≤ R := hR
        linarith
      rw [hball_volume' (0 : EuclideanSpace ℝ (Fin d)) (R + ε / 2) hpos]
    -- By measure monotonicity
    have hmeasure_mono : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (⋃ x ∈ C, Metric.ball x (ε / 2)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + ε / 2)) := by
      refine MeasureTheory.measureReal_mono hunion_subset ?_
      have := MeasureTheory.measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R + ε / 2)
      exact ne_of_lt this
    -- Combine all inequalities
    rw [hmeasure_union_val, hball_big] at hmeasure_mono
    -- Now hmeasure_mono: ((ε/2)^d) * (C.card : ℝ) * V ≤ (R + ε/2)^d * V  where V = volume.real (ball 0 1)
    set V := (volume : Measure (EuclideanSpace ℝ (Fin d))).real (Metric.ball 0 1) with hVdef
    have hVpos : 0 < V := hball01_pos
    -- Cancel V (multiply both sides by V⁻¹)
    have hineq_div : ((ε / 2) ^ d) * (C.card : ℝ) ≤ (R + ε / 2) ^ d := by
      nlinarith
    -- Now we have: (C.card : ℝ) * (ε/2)^d ≤ (R + ε/2)^d
    -- Divide both sides by (ε/2)^d (which is positive)
    have hε2pow_pos : 0 < (ε / 2) ^ d := pow_pos hε2pos d
    have hfinal : (C.card : ℝ) ≤ ((R + ε / 2) / (ε / 2)) ^ d := by
      calc
        (C.card : ℝ) = (((ε / 2) ^ d) * (C.card : ℝ)) / ((ε / 2) ^ d) := by
          field_simp [ne_of_gt hε2pow_pos]
        _ ≤ ((R + ε / 2) ^ d) / ((ε / 2) ^ d) :=
          (div_le_div_iff_of_pos_right hε2pow_pos).mpr hineq_div
        _ = ((R + ε / 2) / (ε / 2)) ^ d := by rw [← div_pow]
    -- Simplify the RHS: ((R + ε/2) / (ε/2)) = 1 + 2*R/ε
    have hRHS : ((R + ε / 2) / (ε / 2)) ^ d = (1 + 2 * R / ε) ^ d := by
      have h_eq : (R + ε / 2) / (ε / 2) = 1 + 2 * R / ε := by
        field_simp [ne_of_gt hε]
        ring
      rw [h_eq]
    rw [hRHS] at hfinal
    exact hfinal
  · -- C is empty
    have hCcard0 : C.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hCempty)
    have hnonneg : 0 ≤ (1 + 2 * R / ε) ^ d := by
      have hbase : 0 ≤ 1 + 2 * R / ε := by
        positivity
      exact pow_nonneg hbase d
    simp [hCcard0, hnonneg]

theorem AdversarialBco.Poly.exists_net {d : ℕ} (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin d)), ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ∃ c ∈ C, dist y c ≤ ε) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d := by
  -- Define the predicate "C is admissible"
  let admissible (C : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
    ↑C ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∧
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y)
  -- The empty set is admissible
  have h_empty_admissible : admissible ∅ := by
    refine ⟨?_, ?_⟩
    · -- empty set is subset of any set
      simp
    · -- vacuously true
      intro x hx
      exfalso
      simp at hx
  -- Bound on the cardinality of admissible sets
  have h_card_bound (C : Finset (EuclideanSpace ℝ (Fin d))) (hC : admissible C) :
      (C.card : ℝ) ≤ (1 + 2 * R / ε) ^ d := by
    rcases hC with ⟨h_sub, h_sep⟩
    apply AdversarialBco.Poly.card_le_of_separated_ball R ε hR hε C h_sub
    intro x hx y hy hxy
    have h := h_sep x hx y hy hxy
    exact h.le
  -- The target value is nonnegative
  have h_target_nonneg : 0 ≤ (1 + 2 * R / ε) ^ d := by
    have h_nonneg : 0 ≤ 1 + 2 * R / ε := by
      have hR_nonneg : 0 ≤ R := hR
      have hε_pos : 0 < ε := hε
      -- 2*R/ε ≥ 0 since R ≥ 0 and ε > 0
      have h_div_nonneg : 0 ≤ 2 * R / ε := div_nonneg (by nlinarith) hε_pos.le
      nlinarith
    exact pow_nonneg h_nonneg d
  -- Let N be the floor of the bound
  let N := ⌊(1 + 2 * R / ε) ^ d⌋₊
  have hN_le : (N : ℝ) ≤ (1 + 2 * R / ε) ^ d :=
    Nat.floor_le h_target_nonneg
  have h_lt_N_add_one : (1 + 2 * R / ε) ^ d < (N : ℝ) + 1 :=
    Nat.lt_floor_add_one ((1 + 2 * R / ε) ^ d)
  -- DecidablePred instance for admissible
  have : DecidablePred (fun (k : ℕ) => ∃ C, admissible C ∧ C.card = k) := by
    -- Since Finset.card is decidable and admissible is decidable (it's a Prop with decidable parts?),
    -- we need to provide a Decidable instance
    -- Actually, admissible is a Prop, not a Bool. But we can use Classical.decPred
    classical
    exact inferInstance
  -- Let k be the greatest integer ≤ N such that there exists an admissible set of size k
  let k := Nat.findGreatest (fun k => ∃ C, admissible C ∧ C.card = k) N
  have h_exists_C : ∃ C, admissible C ∧ C.card = k := by
    -- Since admissible ∅, we have P 0, and 0 ≤ N
    have h0 : (∃ C, admissible C ∧ C.card = 0) := ⟨∅, h_empty_admissible, by simp⟩
    exact Nat.findGreatest_spec (P := fun k => ∃ C, admissible C ∧ C.card = k) (Nat.zero_le N) h0
  rcases h_exists_C with ⟨C, hC_admissible, hC_card⟩
  -- Now we need to show that C is an ε-net
  have h_net : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ∃ c ∈ C, dist y c ≤ ε := by
    intro y hy
    by_contra! h
    -- h: ∀ c ∈ C, ε < dist y c
    -- Then insert y C is admissible
    have hy_notin_C : y ∉ C := by
      intro hyC
      have hdist := h y hyC
      have hdist_self : dist y y = 0 := dist_self _
      linarith
    have h_insert_admissible : admissible (insert y C) := by
      refine ⟨?_, ?_⟩
      · -- ↑(insert y C) ⊆ closedBall 0 R
        intro z hz
        rcases Finset.mem_insert.mp hz with (rfl | hzC)
        · exact hy
        · exact hC_admissible.1 (by simpa using hzC)
      · -- distinct points are at distance > ε
        intro x hx y' hy' hne
        rcases Finset.mem_insert.mp hx with (rfl | hxC)
        · -- x = y, y' ∈ C
          rcases Finset.mem_insert.mp hy' with (rfl | hy'C)
          · exact (hne rfl).elim
          · -- x = y, y' ∈ C
            exact h y' hy'C
        · -- x ∈ C
          rcases Finset.mem_insert.mp hy' with (rfl | hy'C)
          · -- x ∈ C, y' = y
            -- h gives ε < dist y x, but we need ε < dist x y
            rw [dist_comm]
            exact h x hxC
          · -- x ∈ C, y' ∈ C
            exact hC_admissible.2 x hxC y' hy'C hne
    -- Now, card_le_of_separated_ball gives a bound on the cardinality
    have h_card_bound_insert : ((insert y C).card : ℝ) ≤ (1 + 2 * R / ε) ^ d :=
      h_card_bound (insert y C) h_insert_admissible
    -- The cardinality of insert y C is k + 1
    have h_card_insert : (insert y C).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hy_notin_C, hC_card]
    -- So (k + 1 : ℝ) ≤ (1 + 2R/ε)^d
    rw [h_card_insert] at h_card_bound_insert
    -- Now we have (k+1 : ℝ) ≤ (1+2R/ε)^d
    -- Using the floor property: (1+2R/ε)^d < N+1
    -- So k+1 < N+1, hence k < N
    -- First, note that k ≤ N (since k = Nat.findGreatest ... N)
    have hk_le_N : k ≤ N :=
      Nat.findGreatest_le (P := fun k => ∃ C, admissible C ∧ C.card = k) (n := N)
    -- Now, if k = N, then we get a contradiction with the floor property
    have hk_ne_N : k ≠ N := by
      intro hk_eq_N
      rw [hk_eq_N] at h_card_bound_insert
      -- h_card_bound_insert: ↑(N+1) ≤ (1+2R/ε)^d
      have h_cast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by simp
      rw [h_cast] at h_card_bound_insert
      -- h_card_bound_insert: (N:ℝ)+1 ≤ (1+2R/ε)^d
      -- But h_lt_N_add_one: (1+2R/ε)^d < (N:ℝ)+1
      linarith
    -- Therefore k < N
    have hk_lt_N : k < N := Nat.lt_of_le_of_ne hk_le_N hk_ne_N
    have hk_add_one_le_N : k + 1 ≤ N := by omega
    -- Now apply Nat.findGreatest_is_greatest
    have h_not_exists : ¬ (∃ C, admissible C ∧ C.card = k + 1) :=
      Nat.findGreatest_is_greatest (k := k + 1) (Nat.lt_succ_self k) hk_add_one_le_N
    -- But we have insert y C which is admissible with card = k+1
    apply h_not_exists
    exact ⟨insert y C, h_insert_admissible, h_card_insert⟩
  -- Now assemble the result
  refine ⟨C, hC_admissible.1, ?_, h_net, ?_⟩
  · -- distinct points in C are at distance > ε
    intro x hx y hy hne
    exact hC_admissible.2 x hx y hy hne
  · -- cardinality bound: (C.card : ℝ) ≤ (1+2R/ε)^d
    -- h_card_bound C hC_admissible gives exactly this
    -- But the goal is (C.card : ℝ) ≤ (1+2R/ε)^d, which is exactly h_card_bound
    -- Wait, the goal is (C.card : ℝ) ≤ (1+2R/ε)^d
    -- And h_card_bound C hC_admissible is exactly that
    -- But the goal might be different because of the binder? Let me check.
    -- Actually, the goal is (C.card : ℝ) ≤ (1+2R/ε)^d
    -- And h_card_bound C hC_admissible is exactly that
    -- So:
    exact h_card_bound C hC_admissible

theorem AdversarialBco.Poly.quad_diff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (M : E →L[ℝ] E) (hM : IsSelfAdjoint M) (y y' μ : E) :
    ⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫ = ⟪M (y - y'), y + y' - 2 • μ⟫ ∧
      |⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫| ≤ ‖M‖ * ‖y - y'‖ * ‖y + y' - 2 • μ‖ := by
  have hsymm : (M : E →ₗ[ℝ] E).IsSymmetric := hM.isSymmetric
  have hsymm_inner : ∀ x y : E, ⟪M x, y⟫ = ⟪x, M y⟫ := hsymm.apply_clm
  set a := y - μ with ha
  set b := y' - μ with hb
  have hab_sub : a - b = y - y' := by
    dsimp [a, b]
    abel
  have hab_add : a + b = y + y' - 2 • μ := by
    dsimp [a, b]
    abel
  have h_cross : ⟪M a, b⟫ = ⟪M b, a⟫ := by
    calc
      ⟪M a, b⟫ = ⟪a, M b⟫ := hsymm_inner a b
      _ = ⟪M b, a⟫ := real_inner_comm _ _
  have h_eq' : ⟪M (a - b), a + b⟫ = ⟪M a, a⟫ - ⟪M b, b⟫ := by
    calc
      ⟪M (a - b), a + b⟫ = ⟪M a - M b, a + b⟫ := by rw [M.map_sub]
      _ = ⟪M a, a + b⟫ - ⟪M b, a + b⟫ := by rw [inner_sub_left]
      _ = (⟪M a, a⟫ + ⟪M a, b⟫) - (⟪M b, a⟫ + ⟪M b, b⟫) := by rw [inner_add_right, inner_add_right]
      _ = (⟪M a, a⟫ + ⟪M a, b⟫) - (⟪M a, b⟫ + ⟪M b, b⟫) := by rw [h_cross]
      _ = ⟪M a, a⟫ - ⟪M b, b⟫ := by ring
  have h_eq : ⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫ = ⟪M (y - y'), y + y' - 2 • μ⟫ := by
    calc
      ⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫ = ⟪M a, a⟫ - ⟪M b, b⟫ := by simp [a, b]
      _ = ⟪M (a - b), a + b⟫ := by rw [h_eq']
      _ = ⟪M (y - y'), y + y' - 2 • μ⟫ := by rw [hab_sub, hab_add]
  have h_bound : |⟪M (y - μ), y - μ⟫ - ⟪M (y' - μ), y' - μ⟫| ≤ ‖M‖ * ‖y - y'‖ * ‖y + y' - 2 • μ‖ := by
    rw [h_eq]
    calc
      |⟪M (y - y'), y + y' - 2 • μ⟫| = |⟪M (a - b), a + b⟫| := by rw [hab_sub, hab_add]
      _ ≤ ‖M (a - b)‖ * ‖a + b‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖M‖ * ‖a - b‖) * ‖a + b‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm M (a - b)) (norm_nonneg _)
      _ = ‖M‖ * ‖a - b‖ * ‖a + b‖ := by ring
      _ = ‖M‖ * ‖y - y'‖ * ‖y + y' - 2 • μ‖ := by rw [hab_sub, hab_add]
  exact And.intro h_eq h_bound

theorem AdversarialBco.Poly.log_card_net (d : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hdδ : (d : ℝ) ≤ 1 / δ) (hx : 14 ≤ Real.log (1 / δ)) :
    (d : ℝ) * Real.log (1 + 2 * (2 * d) / δ ^ 3) ≤ 4.12 * d * Real.log (1 / δ) := by
  set x := Real.log (1 / δ) with hx_def
  have hx_pos : 0 < x := by linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := by
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hδ_nonneg : 0 ≤ δ := by linarith
  have hδ3_pos : 0 < δ ^ 3 := pow_pos hδ0 3
  have hδ4_pos : 0 < δ ^ 4 := pow_pos hδ0 4
  -- d * δ ≤ 1 from hdδ
  have hdδ_mul : (d : ℝ) * δ ≤ 1 := by
    calc
      (d : ℝ) * δ ≤ (1 / δ) * δ := mul_le_mul_of_nonneg_right hdδ hδ_nonneg
      _ = 1 := by field_simp [hδ0.ne.symm]
  -- Simplify 2*(2*d) = 4*d
  have h_simplify : 2 * (2 * (d : ℝ)) = 4 * (d : ℝ) := by ring
  -- Key inequality: 1 + 4d/δ^3 ≤ 5/δ^4
  have h_main_ineq : 1 + 4 * (d : ℝ) / (δ ^ 3) ≤ 5 / (δ ^ 4) := by
    have hδ4_le_one : δ ^ 4 ≤ 1 := pow_le_one₀ hδ_nonneg (by linarith) (n := 4)
    -- First: 4d/δ^3 ≤ 4/δ^4
    have h1 : 4 * (d : ℝ) / (δ ^ 3) ≤ 4 / (δ ^ 4) := by
      apply (div_le_div_iff₀ hδ3_pos hδ4_pos).mpr
      calc
        4 * (d : ℝ) * (δ ^ 4) = 4 * ((d : ℝ) * δ) * (δ ^ 3) := by ring
        _ ≤ 4 * 1 * (δ ^ 3) := by gcongr
        _ = 4 * (δ ^ 3) := by ring
    -- Second: 1 ≤ 1/δ^4
    have h2 : (1 : ℝ) ≤ 1 / (δ ^ 4) :=
      one_le_one_div hδ4_pos hδ4_le_one
    -- Combine
    have h3 : 1 + 4 * (d : ℝ) / (δ ^ 3) ≤ 1 + 4 / (δ ^ 4) := by
      gcongr
    have h4 : 1 + 4 / (δ ^ 4) ≤ 5 / (δ ^ 4) := by
      field_simp [hδ4_pos.ne.symm]
      linarith
    exact h3.trans h4
  -- Take log of both sides
  have h_pos_arg : 0 < 1 + 4 * (d : ℝ) / (δ ^ 3) := by positivity
  have h_pos_target : 0 < 5 / (δ ^ 4) := by positivity
  have h_log_ineq : Real.log (1 + 4 * (d : ℝ) / (δ ^ 3)) ≤ Real.log (5 / (δ ^ 4)) :=
    Real.log_le_log h_pos_arg h_main_ineq
  -- log(5/δ^4) = log 5 + 4*x
  have h_log_right : Real.log (5 / (δ ^ 4)) = Real.log 5 + 4 * x := by
    calc
      Real.log (5 / (δ ^ 4)) = Real.log 5 - Real.log (δ ^ 4) := by
        rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by positivity : δ ^ 4 ≠ 0)]
      _ = Real.log 5 - (4 * Real.log δ) := by rw [Real.log_pow, Nat.cast_ofNat]
      _ = Real.log 5 + 4 * (-Real.log δ) := by ring
      _ = Real.log 5 + 4 * Real.log (δ⁻¹) := by rw [Real.log_inv]
      _ = Real.log 5 + 4 * x := by
        rw [hx_def]
        simp
  -- Bound log 5 ≤ 0.12 * x
  have h_log5_bound : Real.log 5 ≤ 0.12 * x := by
    -- log 5 = 2*log 2 + log(5/4)
    have h_log5_eq : Real.log 5 = 2 * Real.log 2 + Real.log (5/4) := by
      calc
        Real.log 5 = Real.log (4 * (5/4)) := by norm_num
        _ = Real.log 4 + Real.log (5/4) := by
          rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (5/4 : ℝ) ≠ 0)]
        _ = Real.log ((2:ℝ)^2) + Real.log (5/4) := by norm_num
        _ = 2 * Real.log 2 + Real.log (5/4) := by rw [Real.log_pow, Nat.cast_ofNat]
    rw [h_log5_eq]
    have h_log2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h_log_54 : Real.log (5/4) ≤ 5/4 - 1 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (5/4 : ℝ))
    have h_sum_lt : 2 * Real.log 2 + Real.log (5/4) < 2 * 0.6931471808 + (5/4 - 1) := by
      nlinarith
    have h_bound : 2 * 0.6931471808 + (5/4 - 1) ≤ 0.12 * x := by
      have h_mid : 2 * 0.6931471808 + (5/4 - 1) ≤ 0.12 * (14 : ℝ) := by norm_num
      have h_x : 0.12 * (14 : ℝ) ≤ 0.12 * x := by
        gcongr
      linarith
    linarith
  -- Combine: log(1 + 4d/δ^3) ≤ 4.12 * x
  have h_log_final : Real.log (1 + 4 * (d : ℝ) / (δ ^ 3)) ≤ 4.12 * x := by
    calc
      Real.log (1 + 4 * (d : ℝ) / (δ ^ 3)) ≤ Real.log (5 / (δ ^ 4)) := h_log_ineq
      _ = Real.log 5 + 4 * x := h_log_right
      _ ≤ 0.12 * x + 4 * x := by gcongr
      _ = (0.12 + 4) * x := by ring
      _ = 4.12 * x := by norm_num
  -- Multiply by d ≥ 0
  calc
    (d : ℝ) * Real.log (1 + 2 * (2 * d) / δ ^ 3) = (d : ℝ) * Real.log (1 + 4 * (d : ℝ) / (δ ^ 3)) := by
      simp [h_simplify]
    _ ≤ (d : ℝ) * (4.12 * x) := by gcongr
    _ = (d : ℝ) * (4.12 * Real.log (1 / δ)) := by rw [hx_def]
    _ = 4.12 * d * Real.log (1 / δ) := by ring

theorem AdversarialBco.Poly.union_bound_finset {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι)
    (A : ι → Set Ω) (p : ENNReal) (hA : ∀ i ∈ S, P (A i) ≤ p) :
    P (⋃ i ∈ S, A i) ≤ S.card * p := by
  refine (measure_biUnion_finset_le S A).trans ?_
  have h := Finset.sum_le_card_nsmul S (fun i => P (A i)) p hA
  rwa [nsmul_eq_mul] at h

theorem AdversarialBco.Poly.quad_sum_diff {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Finset ι) (M : ι → E →L[ℝ] E) (hM : ∀ s ∈ S, IsSelfAdjoint (M s)) (μ : ι → E) (y y' : E) (R : ℝ)
    (hR : ∀ s ∈ S, ‖y + y' - 2 • μ s‖ ≤ R) :
    |∑ s ∈ S, ⟪M s (y - μ s), y - μ s⟫ - ∑ s ∈ S, ⟪M s (y' - μ s), y' - μ s⟫| ≤
      (∑ s ∈ S, ‖M s‖) * ‖y - y'‖ * R := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  exact (AdversarialBco.Poly.quad_diff (M s) (hM s hs) y y' (μ s)).2.trans
    (mul_le_mul_of_nonneg_left (hR s hs) (by positivity))

namespace AdversarialBco.Poly

/-! ## Assemblies -/

theorem cardLeOfSeparatedBall : CardLeOfSeparatedBall := fun _ R ε hR hε C hCK hsep =>
  card_le_of_separated_ball R ε hR hε C hCK hsep

theorem existsNet : ExistsNet := fun _ R ε hR hε => exists_net R ε hR hε

theorem logCardNet : LogCardNet := fun d δ hd h0 h1 hdδ hx => log_card_net d δ hd h0 h1 hdδ hx

theorem unionBoundFinset : UnionBoundFinset := fun _ _ _ P S A p hA => union_bound_finset P S A p hA

theorem quadDiff : QuadDiff := fun _ _ _ _ M hM y y' μ => quad_diff M hM y y' μ

theorem quadSumDiff : QuadSumDiff := fun _ _ _ _ _ S M hM μ y y' R hR => quad_sum_diff S M hM μ y y' R hR

end AdversarialBco.Poly
