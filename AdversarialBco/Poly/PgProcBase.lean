/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProc

@[expose] public section

/-!
# Procedure PG: facts on the space `PgSp d`

The coordinates of a packed pair (`pgMu_pgPack`, `pgMat_pgPack`), the operator of a point (`pgOp_apply`), the inner
product and the norm of `PgSp d` (`pgSp_inner`, `pgSp_norm_sq`), and the continuity of `pgMu`, `pgMat` and of
`(x, v) ↦ μ + T v` (`pg_continuous`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

namespace AdversarialBco.Poly

/-! ## The space `PgSp d` -/

/-- The point of `PgSp d` packed from `μ` and `M` has mean `μ`. -/
theorem pgMu_pgPack {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    pgMu (pgPack μ M) = μ := by
  rfl

/-- The point of `PgSp d` packed from `μ` and `M` has matrix `M`. -/
theorem pgMat_pgPack {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    pgMat (pgPack μ M) = M := by
  rfl

/-- `T v = M v` in coordinates. -/
theorem pgOp_apply {d : ℕ} (x : PgSp d) (v : EuclideanSpace ℝ (Fin d)) :
    pgOp x v = WithLp.toLp 2 (pgMat x *ᵥ WithLp.ofLp v) := by
  rw [pgOp, ← Matrix.toEuclideanCLM_toLp]

/-- The inner product of `PgSp d` is the sum of the inner products of the means and of the matrices. -/
theorem pgSp_inner {d : ℕ} (x y : PgSp d) :
    ⟪x, y⟫ = ⟪pgMu x, pgMu y⟫ + ∑ i, ∑ j, pgMat x i j * pgMat y i j := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, pgMu, pgMat, RCLike.inner_apply,
    conj_trivial]
  simp [mul_comm]

/-- `|x|^2 = |μ|^2 + |M|_F^2`. -/
theorem pgSp_norm_sq {d : ℕ} (x : PgSp d) :
    ‖x‖ ^ 2 = ‖pgMu x‖ ^ 2 + ∑ i, ∑ j, pgMat x i j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, pgSp_inner]
  simp [sq]

/-- `μ`, the matrix and the affine map `(x, y) ↦ μ + T y` are continuous on `PgSp d`. -/
theorem pg_continuous (d : ℕ) :
    Continuous (fun x : PgSp d => pgMu x) ∧ Continuous (fun x : PgSp d => pgMat x) ∧
      Continuous (fun p : PgSp d × EuclideanSpace ℝ (Fin d) => pgMu p.1 + pgOp p.1 p.2) := by
  have hmu : Continuous (fun x : PgSp d => pgMu x) := by
    unfold pgMu
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (PiLp.continuous_apply 2 _ (Sum.inl i)))
  have hmat : Continuous (fun x : PgSp d => pgMat x) := by
    unfold pgMat
    exact continuous_pi fun i => continuous_pi fun j => PiLp.continuous_apply 2 _ (Sum.inr (i, j))
  refine ⟨hmu, hmat, ?_⟩
  have hop : ∀ (x : PgSp d) (v : EuclideanSpace ℝ (Fin d)),
      pgOp x v = WithLp.toLp 2 (pgMat x *ᵥ WithLp.ofLp v) := fun x v => by
    rw [pgOp, ← Matrix.toEuclideanCLM_toLp]
  simp_rw [hop]
  refine (hmu.comp continuous_fst).add ((PiLp.continuous_toLp 2 _).comp ?_)
  exact (hmat.comp continuous_fst).matrix_mulVec ((PiLp.continuous_ofLp 2 _).comp continuous_snd)


end AdversarialBco.Poly
