/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/

module

public import AdversarialBco.Poly.Cover

@[expose] public section

/-!
# Nets of a ball and the union bound: proofs

Proof of the interface statement `ExistsNet` of `AdversarialBco/Poly/Cover.lean` (theorem `existsNet`), from
`card_le_of_separated_ball` and `exists_net`, and the union bound over a finite family, `union_bound_finset` (from
`MeasureTheory.measure_biUnion_finset_le`).
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

theorem AdversarialBco.Poly.union_bound_finset {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Finset ι)
    (A : ι → Set Ω) (p : ENNReal) (hA : ∀ i ∈ S, P (A i) ≤ p) :
    P (⋃ i ∈ S, A i) ≤ S.card * p := by
  refine (measure_biUnion_finset_le S A).trans ?_
  have h := Finset.sum_le_card_nsmul S (fun i => P (A i)) p hA
  rwa [nsmul_eq_mul] at h

namespace AdversarialBco.Poly

/-! ## Assemblies -/

theorem existsNet : ExistsNet := fun _ R ε hR hε => exists_net R ε hR hε

end AdversarialBco.Poly
