/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.Clamp
public import AdversarialBco.Conj1Arith.Verdict
public import AdversarialBco.Conj1Arith.Rows
public import AdversarialBco.Conj1Arith.SgdE

@[expose] public section

/-!
# Procedure PG-N (Theorem PG-N, leaves E1)

Procedure PG with the two changes of PG-N: the projection of each descent step is that of a clamp routine `C`
(`pgDescentN C`, over `pgProjR C`, Conj1Arith/Clamp.lean), and the third clause of the basic verdict is strict
(`pgTestS`, over `pgVerdictS`). The core, the stages and the procedure are `pgCoreN`, `pgStageN` and `pgN`; the
positions, the parameters, the estimate and the laws of the streams are those of PgProc.lean. `PgCoreThmN C` and
`PgThmN C` are Theorems PG-core and PG for this procedure, `PgCoreMeasN C` and `PgMeasN C` the measurability of its
outputs. The theorems E1 are stated for every routine: their proofs read `C` only through `pgProjR_mem`,
`pgProjR_near` and `pgProjR_measurable`, so the filler (CLAMP-NS, Conj1Arith/ClampNS.lean) does not enter them. They
are proved in Conj1Arith/ProcCore.lean (E1a, E1b), ProcMeas.lean (E1d, E1e) and ProcStage.lean (E1c).

This file holds the definitions only. Junk values: those of PgProc.lean.
-/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly

variable {d : ℕ}

/-- The average `x̄` of the descent with the clamp routine `C` on the samples `a`. -/
noncomputable def pgDescentN (C : ClampRoutine) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (a : ℕ → EuclideanSpace ℝ (Fin d)) : PgSp d :=
  sgdAvg (pgProjR C d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) (pgNs d ρ) a

open Classical in
/-- The amplified test with the strict verdict. -/
def pgTestS (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (x : PgSp d) (w : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  (pgMT δ : ℝ) / 2 < ((Finset.range (pgMT δ)).filter fun i => pgVerdictS K ρ x (w i)).card

open Classical in
/-- Procedure PG-N core. -/
noncomputable def pgCoreN (C : ClampRoutine) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (ω : ℕ → PgRound d) : Option (PgSp d) :=
  if h : ∃ r < pgJr δ, pgTestS K ρ δ (pgDescentN C K ρ (ω r).1) (ω r).2 then
    some (pgOut (pgDescentN C K ρ (ω (Nat.find h)).1))
  else none

/-- The stages of the growing balls with `pgCoreN`. -/
noncomputable def pgStageN (C : ClampRoutine) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ)
    (ω : ℕ → ℕ → PgRound d) : ℕ → Option (PgSp d)
  | 0 => some (pgPack 0 (r0 • 1))
  | i + 1 => (pgStageN C d K r0 δ' ω i).bind fun P =>
      (pgCoreN C d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d i) δ'
        (ω i)).map (pgComp P)

/-- Procedure PG-N. -/
noncomputable def pgN (C : ClampRoutine) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ)
    (ω : ℕ → ℕ → PgRound d) : Option (PgSp d) :=
  pgStageN C d K r0 (δ / pgStages r0 R0) ω (pgStages r0 R0)

/-- Theorem PG-core for PG-N. -/
def PgCoreThmN (C : ClampRoutine) : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ), 1 ≤ d → Convex ℝ K → IsClosed K →
    Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 ρ → 1 ≤ ρ → 0 < δ → δ < 1 →
    pgCoreMeasure d {ω | ¬ PgGood d K (36.4 * d * pgLam ρ) (pgCoreN C d K ρ δ ω)} ≤ ENNReal.ofReal δ

/-- Theorem PG for PG-N. -/
def PgThmN (C : ClampRoutine) : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ), 1 ≤ d → Convex ℝ K → IsClosed K →
    0 < r0 → r0 ≤ R0 → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 → 0 < δ → δ < 1 →
    pgMeasure d {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pgN C d K r0 R0 δ ω)} ≤
      ENNReal.ofReal δ

/-- The output of `pgCoreN` is measurable jointly in the position and the stream. -/
def PgCoreMeasN (C : ClampRoutine) : Prop :=
  ∀ (d : ℕ) (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ), IsClosed K' →
    MeasurableSet {p : PgSp d × (ℕ → PgRound d) |
      (pgCoreN C d (posBody K' (pgMu p.1) (pgOp p.1)) ρ δ p.2).isSome} ∧
    Measurable fun p : PgSp d × (ℕ → PgRound d) =>
      (pgCoreN C d (posBody K' (pgMu p.1) (pgOp p.1)) ρ δ p.2).getD 0

/-- The output of `pgN` is measurable in the stream. -/
def PgMeasN (C : ClampRoutine) : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ), IsClosed K →
    MeasurableSet {ω : ℕ → ℕ → PgRound d | (pgN C d K r0 R0 δ ω).isSome} ∧
    Measurable fun ω : ℕ → ℕ → PgRound d => (pgN C d K r0 R0 δ ω).getD 0

end AdversarialBco.Conj1Arith
