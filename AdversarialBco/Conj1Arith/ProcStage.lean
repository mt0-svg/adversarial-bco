/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.ProcCore
public import AdversarialBco.Conj1Arith.ProcMeas

@[expose] public section

/-!
# Theorem PG for Procedure PG-N

Theorem PG for PG-N through the stages of the growing balls, from Theorem PG-core for PG-N (`pgCoreThmN`,
Conj1Arith/ProcCore.lean) and the measurability of PG-N (`pgMeasN`, Conj1Arith/ProcMeas.lean). The stage lemmas that do
not mention the procedure (`pgStages_spec`, `pgStage_body`, `pgStage0_body`, `pgRhoStage_bounds`, `pgGood_comp`,
`pgGood_mono`) are those of PgProcProof.lean.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly

/-- Stage `i` depends only on the streams of the stages before it. -/
theorem pgStageN_dep (C : ClampRoutine) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ) (i : ℕ)
    (ω ω' : ℕ → ℕ → PgRound d) (h : ∀ j < i, ω j = ω' j) :
    pgStageN C d K r0 δ' ω i = pgStageN C d K r0 δ' ω' i := by
  induction' i with i ih
  · rfl
  · simp only [pgStageN]
    rw [ih (fun j hj => h j (by omega)), h i (by omega)]

/-- For `i ≥ 1`, stage `i` is the procedure `pgN` up to the radius `2^i r₀` at the probability `i δ'`. -/
theorem pgStageN_eq_pgN (C : ClampRoutine) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ) (hr0 : 0 < r0) (i : ℕ)
    (hi : 1 ≤ i) (ω : ℕ → ℕ → PgRound d) :
    pgStageN C d K r0 δ' ω i = pgN C d K r0 (2 ^ i * r0) (i * δ') ω := by
  have hi' : (i : ℝ) ≠ 0 := by
    intro hzero
    have : (i : ℕ) = 0 := by exact_mod_cast hzero
    linarith
  have hlog : Real.logb (2 : ℝ) ((2 : ℝ) ^ (i : ℕ)) = (i : ℝ) := by
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
    ring
  have hstages : pgStages r0 (2 ^ i * r0) = i := by
    unfold pgStages
    have hdiv : (2 ^ i * r0) / r0 = (2 : ℝ) ^ (i : ℕ) := by
      field_simp [ne_of_gt hr0]
    rw [hdiv, hlog]
    rw [Nat.ceil_natCast i]
    exact max_eq_right hi
  unfold pgN
  rw [hstages]
  field_simp [hi']

/-- The event that stage `j` is good is measurable. -/
theorem pgStageGoodN_meas (C : ClampRoutine) (hM : PgMeasN C) (hGM : PgGoodMeas) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (r0 δ' : ℝ) (hr0 : 0 < r0) (j : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 j (pgStageN C d K r0 δ' ω j)} := by
  match j with
  | 0 =>
    have hset : {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 0 (pgStageN C d K r0 δ' ω 0)} = Set.univ := by
      ext ω; simp [PgStageGood]
    rw [hset]
    exact MeasurableSet.univ
  | j+1 =>
    have hj : 1 ≤ j+1 := Nat.succ_pos j
    have hK'_closed : IsClosed (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) :=
      hKcl.inter Metric.isClosed_closedBall
    have hK'_convex : Convex ℝ (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) :=
      hKc.inter (convex_closedBall 0 (2 ^ (j+1) * r0))
    have hM_res := hM d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') hKcl
    have hGM_res := hGM d (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) (36.4 * d * pgLam (pgRhoStage d j)) (hK'_convex) hK'_closed
    rcases hM_res with ⟨hM_some, hM_getD⟩
    -- Now we need to relate the set to these measurable pieces
    -- The set is {ω | PgStageGood d K r0 (j+1) (pgStageN C d K r0 δ' ω (j+1))}
    -- = {ω | PgGood d (K ∩ closedBall 0 (2^(j+1)*r0)) (36.4*d*pgLam (pgRhoStage d j)) (pgStageN C d K r0 δ' ω (j+1))}
    -- = {ω | PgGood d (K ∩ closedBall 0 (2^(j+1)*r0)) (36.4*d*pgLam (pgRhoStage d j)) (pgN C d K r0 (2^(j+1)*r0) ((j+1)*δ') ω)}
    -- by pgStageN_eq_pgN and pgGood_iff
    have h_set_eq : {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 (j+1) (pgStageN C d K r0 δ' ω (j+1))} =
        {ω : ℕ → ℕ → PgRound d | (pgN C d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') ω).isSome} ∩
        (fun ω' => (pgN C d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') ω').getD 0) ⁻¹'
        {Q : PgSp d | PgGood d (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) (36.4 * d * pgLam (pgRhoStage d j)) (some Q)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      rw [PgStageGood, pgStageN_eq_pgN C d K r0 δ' hr0 (j+1) hj ω, pgGood_iff]
      simp only [Option.isSome, Nat.cast_succ]
    rw [h_set_eq]
    exact MeasurableSet.inter hM_some (MeasurableSet.preimage hGM_res hM_getD)

/-! ## Assemblies: Theorem PG -/

/-- A good output of stage `j` is an invertible position in which the body `K ∩ B̄(0, 2^{j+1} r₀)` is a `PgBody` at the
ratio `pgRhoStage d j`: the input of the next stage. -/
theorem pgStageN_input (C : ClampRoutine) (hGr : PgGrowing) (hConc : PgConclusion) (d : ℕ) (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K) (r0 : ℝ) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall 0 r0 ⊆ K) (δ' : ℝ) (ω : ℕ → ℕ → PgRound d) (j : ℕ) (P : PgSp d)
    (hP : pgStageN C d K r0 δ' ω j = some P) (hg : PgStageGood d K r0 j (some P)) :
    (pgMat P).det ≠ 0 ∧
      PgBody (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d j) := by
  cases j with
  | zero =>
    have hP0 : P = pgPack 0 (r0 • 1) := by
      simp only [pgStageN, Option.some.injEq] at hP
      exact hP.symm
    subst hP0
    exact pgStage0_body d K hKc hKcl r0 hr0 hK0
  | succ i =>
    obtain ⟨P', hP', hdet, h1, hR, -⟩ := hg
    cases hP'
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := hK0 (Metric.mem_closedBall_self hr0.le)
    refine ⟨hdet, pgBody_mono _ _ _ ?_ (pgStage_body d K hKc hKcl h0 r0 _ hr0 (i + 1) P hdet h1 hR)⟩
    exact (pgRhoStage_bounds hGr hConc d hd i).2.2.1

/-- Theorem PG for PG-N from Theorem PG-core for PG-N, the measurability of PG-N and the hypotheses on the stages. -/
theorem pgThmN_of (Cr : ClampRoutine) (hC : PgCoreThmN Cr) (hM : PgMeasN Cr) (hGM : PgGoodMeas) (hGr : PgGrowing) (hConc : PgConclusion) :
    PgThmN Cr := by
  intro d K r0 R0 δ hd hKc hKcl hr0 hR hK0 hKR hδ0 hδ1
  obtain ⟨hm1, hmR⟩ := pgStages_spec r0 R0 hr0 hR
  have hm0 : (0 : ℝ) < pgStages r0 R0 := by exact_mod_cast hm1
  have hδ'0 : 0 < δ / pgStages r0 R0 := div_pos hδ0 hm0
  have hδ'1 : δ / pgStages r0 R0 < 1 :=
    (div_le_self hδ0.le (by exact_mod_cast hm1)).trans_lt hδ1
  -- the event of stage `j`: good after `j` stages, not good after `j + 1`
  let C : ℕ → Set ((ℕ → ℕ → PgRound d) × (ℕ → PgRound d)) := fun j =>
    {q | PgStageGood d K r0 j (pgStageN Cr d K r0 (δ / pgStages r0 R0) q.1 j) ∧
      ¬ PgStageGood d K r0 (j + 1) (pgStageN Cr d K r0 (δ / pgStages r0 R0) (Function.update q.1 j q.2) (j + 1))}
  have hCm : ∀ j, MeasurableSet (C j) := fun j =>
    ((pgStageGoodN_meas Cr hM hGM d K hKc hKcl r0 _ hr0 j).preimage measurable_fst).inter
      ((pgStageGoodN_meas Cr hM hGM d K hKc hKcl r0 _ hr0 (j + 1)).preimage measurable_update').compl
  have hE : ∀ j, pgMeasure d {ω | (ω, ω j) ∈ C j} ≤ ENNReal.ofReal (δ / pgStages r0 R0) := by
    intro j
    refine slice_resample (pgCoreMeasure d) j (C j) (hCm j) ?_ _ ?_
    · intro ω x x'
      have hdep : pgStageN Cr d K r0 (δ / pgStages r0 R0) (Function.update ω j x') j =
          pgStageN Cr d K r0 (δ / pgStages r0 R0) ω j :=
        pgStageN_dep Cr d K r0 _ j _ _ fun k hk => Function.update_of_ne (ne_of_lt hk) _ _
      simp only [C, Set.mem_ofPred_eq, Function.update_idem, hdep]
    · intro ω
      by_cases hg : PgStageGood d K r0 j (pgStageN Cr d K r0 (δ / pgStages r0 R0) ω j)
      · obtain ⟨P, hP⟩ : ∃ P, pgStageN Cr d K r0 (δ / pgStages r0 R0) ω j = some P := by
          cases j with
          | zero => exact ⟨_, rfl⟩
          | succ i =>
            obtain ⟨P, hP, -⟩ := hg
            exact ⟨P, hP⟩
        rw [hP] at hg
        obtain ⟨hdet, hbody⟩ := pgStageN_input Cr hGr hConc d hd K hKc hKcl r0 hr0 hK0 _ ω j P hP hg
        refine le_trans (measure_mono ?_) (hC d _ (pgRhoStage d j) _ hd hbody.1 hbody.2.1 hbody.2.2.1 hbody.2.2.2
          (pgRhoStage_bounds hGr hConc d hd j).1 hδ'0 hδ'1)
        intro x hx hgood
        apply hx.2
        have hsj : pgStageN Cr d K r0 (δ / pgStages r0 R0) (Function.update ω j x) j = some P := by
          rw [pgStageN_dep Cr d K r0 _ j _ ω fun k hk => Function.update_of_ne (ne_of_lt hk) _ _]
          exact hP
        obtain ⟨P', hP', hgood'⟩ : ∃ P', pgCoreN Cr d (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P)
            (pgOp P)) (pgRhoStage d j) (δ / pgStages r0 R0) x = some P' ∧
            PgGood d (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P))
              (36.4 * d * pgLam (pgRhoStage d j)) (some P') := by
          obtain ⟨P', hP', h'⟩ := hgood
          exact ⟨P', hP', P', rfl, h'⟩
        show PgGood d (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (36.4 * d * pgLam (pgRhoStage d j))
          (pgStageN Cr d K r0 (δ / pgStages r0 R0) (Function.update ω j x) (j + 1))
        simp only [pgStageN, hsj, Option.bind_some, Function.update_self, hP', Option.map_some]
        exact pgGood_comp d _ _ P P' hdet hgood'
      · have hempty : {x | (ω, x) ∈ C j} = ∅ := by
          ext x
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [hempty, measure_empty]
        exact bot_le
  have hfinal : ∀ ω, PgStageGood d K r0 (pgStages r0 R0) (pgStageN Cr d K r0 (δ / pgStages r0 R0) ω (pgStages r0 R0)) →
      PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pgN Cr d K r0 R0 δ ω) := by
    intro ω hω
    obtain ⟨k, hk⟩ : ∃ k, pgStages r0 R0 = k + 1 := ⟨pgStages r0 R0 - 1, by omega⟩
    rw [hk] at hω
    have hKm : K ∩ Metric.closedBall 0 (2 ^ (k + 1) * r0) = K := by
      refine Set.inter_eq_left.2 (hKR.trans (Metric.closedBall_subset_closedBall ?_))
      rw [← hk]
      exact hmR
    simp only [PgStageGood, hKm] at hω
    have hpg : pgN Cr d K r0 R0 δ ω = pgStageN Cr d K r0 (δ / ((k + 1 : ℕ) : ℝ)) ω (k + 1) := by
      unfold pgN
      rw [hk]
    rw [hpg]
    exact pgGood_mono d K _ _ (pgRhoStage_bounds hGr hConc d hd k).2.2.2 _ hω
  have hcover : {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pgN Cr d K r0 R0 δ ω)} ⊆
      ⋃ j ∈ Finset.range (pgStages r0 R0), {ω | (ω, ω j) ∈ C j} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hnot
    have hall : ∀ i ≤ pgStages r0 R0, PgStageGood d K r0 i (pgStageN Cr d K r0 (δ / pgStages r0 R0) ω i) := by
      intro i hi
      induction i with
      | zero => trivial
      | succ i ih =>
        by_contra hb
        refine hnot i (by omega) ?_
        refine ⟨ih (by omega), ?_⟩
        simpa only [Function.update_eq_self] using hb
    exact hω (hfinal ω (hall _ le_rfl))
  calc pgMeasure d {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pgN Cr d K r0 R0 δ ω)}
      ≤ pgMeasure d (⋃ j ∈ Finset.range (pgStages r0 R0), {ω | (ω, ω j) ∈ C j}) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range (pgStages r0 R0), pgMeasure d {ω | (ω, ω j) ∈ C j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (pgStages r0 R0), ENNReal.ofReal (δ / pgStages r0 R0) :=
        Finset.sum_le_sum fun j _ => hE j
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- E1c: Theorem PG for PG-N. -/
theorem pgThmN (C : ClampRoutine) : PgThmN C :=
  pgThmN_of C (pgCoreThmN C) (pgMeasN C) PgMeas.pgGoodMeas pgGrowing pgConclusion

end AdversarialBco.Conj1Arith
