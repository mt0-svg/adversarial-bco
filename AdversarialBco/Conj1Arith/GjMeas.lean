/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLin

@[expose] public section

/-!
# Measurability of Gauss-Jordan elimination

Entrywise measurability of matrix-valued maps, and of `gjStep` and `gjRun` (MachPGCode.lean) in the matrix, their
divisions read with their junk value at `0`. Used by the verdict (`measurableSet_posDef`, through the pivots).
Everything here is proved.
-/

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly.PG

variable {d : ℕ}

/-- A matrix-valued map is measurable when its entries are. -/
theorem matrix_measurable_of_entries {α : Type*} [MeasurableSpace α] {F : α → Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ i j, Measurable fun x => F x i j) : Measurable F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

theorem matrix_entry_measurable {α : Type*} [MeasurableSpace α] {F : α → Matrix (Fin d) (Fin d) ℝ}
    (hF : Measurable F) (i j : Fin d) : Measurable fun x => F x i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

/-- One step of Gauss-Jordan elimination is measurable (its divisions read with their junk value at `0`). -/
theorem gjStep_measurable (k : Fin d) :
    Measurable (gjStep k : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ →
      Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) := by
  unfold gjStep
  refine Measurable.prodMk ?_ ?_ <;>
  · refine matrix_measurable_of_entries fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs <;> fun_prop

/-- `gjRun` is measurable in the matrix. -/
theorem gjRun_measurable : ∀ k, Measurable fun T : Matrix (Fin d) (Fin d) ℝ => gjRun T k
  | 0 => by simp only [gjRun]; exact measurable_id.prodMk measurable_const
  | k + 1 => by
    by_cases hk : k < d
    · simp only [gjRun, hk, dite_true]
      exact (gjStep_measurable _).comp (gjRun_measurable k)
    · simp only [gjRun, hk, dite_false]
      exact gjRun_measurable k


end AdversarialBco.Conj1Arith
