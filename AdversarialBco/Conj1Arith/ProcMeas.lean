/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.Proc

@[expose] public section

/-!
# The measurability of Procedure PG-N

The measurability of the outputs of Procedure PG-N (Conj1Arith/Proc.lean), over families of bodies: the strict verdict
reads `measurableSet_posDef` (Conj1Arith/Verdict.lean) through `verdictS_generic_measurableSet`, the descent reads the
routine through `pgProjR_measurable`. The generic lemmas on families, and the measurability of the gauge and of the
estimate, are those of PgMeasProof.lean (`count_generic_measurableSet`, `sgdAvg_family_measurable`,
`pgFt_family_measurable`, `pgV_family_measurable`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly AdversarialBco.Poly.PgMeas

/-- The strict verdict over a family of bodies is a measurable event when the gauge `pgFt` is jointly measurable. -/
theorem pgVerdictS_family_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hFt : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgFt (K q.1) ρ q.2.1 q.2.2)) :
    MeasurableSet {q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdictS (K q.1) ρ q.2.1 q.2.2} := by
  have h := verdictS_generic_measurableSet (fun i (q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d))) =>
      pgFt (K q.1) ρ q.2.1 (q.2.2 i))
    (fun i => hFt.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))))
    (fun i q => q.2.2 i) (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
    (pgNT d ρ) (1.075 * pgKappa) (3 / 4 * pgTaub d ρ) (5 / 8 * (pgKappa / d))
  convert h using 2 with q
  rfl

open Classical in
/-- The amplified strict test over a family of bodies is a measurable event when the strict verdict is. -/
theorem pgTestS_family_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (hVer : MeasurableSet {q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdictS (K q.1) ρ q.2.1 q.2.2}) :
    MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTestS (K q.1) ρ δ q.2.1 q.2.2} := by
  have hV : ∀ i, MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) |
      pgVerdictS (K q.1) ρ q.2.1 (q.2.2 i)} := fun i => by
    have h' := hVer.preimage (f := fun q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) => (q.1, q.2.1, q.2.2 i))
      (by fun_prop)
    simpa only [Set.preimage_ofPred_eq] using h'
  have h := count_generic_measurableSet
    (fun i (q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => pgVerdictS (K q.1) ρ q.2.1 (q.2.2 i)) hV
    (inst := fun i q => Classical.dec _)
    (pgMT δ) ((pgMT δ : ℝ) / 2)
  convert h using 2 with q
  simp only [pgTestS]

/-- The descent with the projection of `C`, over a family of bodies, is measurable when the estimate `pgV` is. -/
theorem pgDescentN_family_measurable (C : ClampRoutine) {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hV : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgV (K q.1) ρ q.2.1 q.2.2)) :
    Measurable (fun q : X × (ℕ → EuclideanSpace ℝ (Fin d)) => pgDescentN C (K q.1) ρ q.2) :=
  sgdAvg_family_measurable (pgProjR C d ρ) (pgProjR_measurable C d ρ) (fun x => pgV (K x) ρ) hV _ _ _

/-- The output of `pgCoreN` over a family of bodies (the event that it returns, and its value) is measurable when the
test and the descent are. -/
theorem pgCoreN_family_meas (C : ClampRoutine) {X : Type*} [MeasurableSpace X] {d : ℕ} (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (ρ δ : ℝ)
    (hTest : MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTestS (K q.1) ρ δ q.2.1 q.2.2})
    (hDesc : Measurable (fun q : X × (ℕ → EuclideanSpace ℝ (Fin d)) => pgDescentN C (K q.1) ρ q.2)) :
    MeasurableSet {q : X × (ℕ → PgRound d) | (pgCoreN C d (K q.1) ρ δ q.2).isSome} ∧
      Measurable (fun q : X × (ℕ → PgRound d) => (pgCoreN C d (K q.1) ρ δ q.2).getD 0) := by
  have hD : ∀ r, Measurable (fun q : X × (ℕ → PgRound d) => pgDescentN C (K q.1) ρ (q.2 r).1) := fun r =>
    measurable_comp_lam hDesc (fun q : X × (ℕ → PgRound d) => (q.1, (q.2 r).1)) (by fun_prop)
  have hA : ∀ r, MeasurableSet {q : X × (ℕ → PgRound d) |
      pgTestS (K q.1) ρ δ (pgDescentN C (K q.1) ρ (q.2 r).1) (q.2 r).2} := fun r => by
    have h' := hTest.preimage (f := fun q : X × (ℕ → PgRound d) => (q.1, pgDescentN C (K q.1) ρ (q.2 r).1, (q.2 r).2))
      (measurable_fst.prodMk ((hD r).prodMk (by fun_prop)))
    simpa only [Set.preimage_ofPred_eq] using h'
  constructor
  · have hset : {q : X × (ℕ → PgRound d) | (pgCoreN C d (K q.1) ρ δ q.2).isSome} =
        ⋃ r ∈ Finset.range (pgJr δ),
          {q : X × (ℕ → PgRound d) | pgTestS (K q.1) ρ δ (pgDescentN C (K q.1) ρ (q.2 r).1) (q.2 r).2} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
      unfold pgCoreN
      split_ifs with h
      · simpa using h
      · simpa using h
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun r _ => hA r
  · simp only [pgCoreN, apply_dite (fun o : Option (PgSp d) => o.getD 0), Option.getD_some, Option.getD_none]
    exact measurable_dite_find (pgJr δ)
      (fun r (q : X × (ℕ → PgRound d)) => pgTestS (K q.1) ρ δ (pgDescentN C (K q.1) ρ (q.2 r).1) (q.2 r).2) hA
      (fun r q => pgOut (pgDescentN C (K q.1) ρ (q.2 r).1)) (fun r => (pgOut_continuous d).measurable.comp (hD r)) 0

/-- The output of `pgCoreN` over a measurable family of bodies is measurable. -/
theorem pgCoreN_family (C : ClampRoutine) {X : Type*} [MeasurableSpace X] {d : ℕ} (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (hK : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ K p.1}) (ρ δ : ℝ) :
    MeasurableSet {q : X × (ℕ → PgRound d) | (pgCoreN C d (K q.1) ρ δ q.2).isSome} ∧
      Measurable (fun q : X × (ℕ → PgRound d) => (pgCoreN C d (K q.1) ρ δ q.2).getD 0) := by
  have hFt := pgFt_family_measurable K hK ρ
  exact pgCoreN_family_meas C K ρ δ
    (pgTestS_family_measurableSet K ρ δ (pgVerdictS_family_measurableSet K ρ hFt))
    (pgDescentN_family_measurable C K ρ (pgV_family_measurable K ρ hFt))

/-- E1d: the measurability of PG-N core. -/
theorem pgCoreMeasN (C : ClampRoutine) : PgCoreMeasN C := fun d K' ρ δ hK' =>
  pgCoreN_family C (fun P : PgSp d => posBody K' (pgMu P) (pgOp P)) (posBody_family_measurableSet K' hK') ρ δ

/-- The output of `pgStageN` at stage `i` (the event that it returns, and its value) is measurable in the stream,
given `PgCoreMeasN C`. -/
theorem pgStageN_meas (C : ClampRoutine) (hC : PgCoreMeasN C) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K)
    (r0 δ' : ℝ) (i : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → PgRound d | (pgStageN C d K r0 δ' ω i).isSome} ∧
      Measurable fun ω : ℕ → ℕ → PgRound d => (pgStageN C d K r0 δ' ω i).getD 0 := by
  induction i with
  | zero =>
    simp only [pgStageN, Option.isSome_some]
    exact ⟨MeasurableSet.univ, measurable_const⟩
  | succ i ih =>
    obtain ⟨hS, hP⟩ := ih
    have hKi : IsClosed (K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ (i + 1) * r0)) :=
      hK.inter Metric.isClosed_closedBall
    obtain ⟨hC1, hC2⟩ := hC d _ (pgRhoStage d i) δ' hKi
    have hφ : Measurable (fun ω : ℕ → ℕ → PgRound d => ((pgStageN C d K r0 δ' ω i).getD 0, ω i)) :=
      hP.prodMk (measurable_pi_apply i)
    have hstep : ∀ ω : ℕ → ℕ → PgRound d, pgStageN C d K r0 δ' ω (i + 1) = (pgStageN C d K r0 δ' ω i).bind fun P =>
        (pgCoreN C d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d i) δ'
          (ω i)).map (pgComp P) := fun ω => rfl
    have hset : {ω : ℕ → ℕ → PgRound d | (pgStageN C d K r0 δ' ω (i + 1)).isSome} =
        {ω | (pgStageN C d K r0 δ' ω i).isSome} ∩
          (fun ω : ℕ → ℕ → PgRound d => ((pgStageN C d K r0 δ' ω i).getD 0, ω i)) ⁻¹'
            {p : PgSp d × (ℕ → PgRound d) | (pgCoreN C d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0))
              (pgMu p.1) (pgOp p.1)) (pgRhoStage d i) δ' p.2).isSome} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hstep, option_bind_map_isSome,
        Bool.and_eq_true]
    have hmeas : MeasurableSet {ω : ℕ → ℕ → PgRound d | (pgStageN C d K r0 δ' ω (i + 1)).isSome} :=
      hset ▸ hS.inter (hC1.preimage hφ)
    refine ⟨hmeas, ?_⟩
    have hfun : (fun ω : ℕ → ℕ → PgRound d => (pgStageN C d K r0 δ' ω (i + 1)).getD 0) =
        fun ω => if (pgStageN C d K r0 δ' ω (i + 1)).isSome then
          pgComp ((pgStageN C d K r0 δ' ω i).getD 0)
            ((pgCoreN C d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0))
              (pgMu ((pgStageN C d K r0 δ' ω i).getD 0)) (pgOp ((pgStageN C d K r0 δ' ω i).getD 0)))
              (pgRhoStage d i) δ' (ω i)).getD 0) else 0 := by
      funext ω
      rw [hstep]
      exact option_bind_map_getD _ _ _
    rw [hfun]
    exact Measurable.ite hmeas ((pgComp_continuous d).measurable.comp (hP.prodMk (hC2.comp hφ))) measurable_const

/-- E1e: the measurability of PG-N. -/
theorem pgMeasN (C : ClampRoutine) : PgMeasN C := fun d K r0 R0 δ hK =>
  pgStageN_meas C (pgCoreMeasN C) d K hK r0 (δ / pgStages r0 R0) (pgStages r0 R0)


end AdversarialBco.Conj1Arith
