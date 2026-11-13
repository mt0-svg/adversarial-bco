/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgLemmas

@[expose] public section

/-!
# Procedure PG: positions, the domain and the conclusion

Definitions for Procedure PG, in the real-RAM model: exact real arithmetic, exact standard Gaussian samples, exact
membership answers.

A position is a pair `(μ, A)`, `A` invertible, standing for the affine map `S y = A⁻¹ (y - μ)`: the body in this
position is `S(K) = posBody K μ A = {y | μ + A y ∈ K}`. A membership question for `S(K)` at `y` is the question
`μ + A y ∈ K`, so no inverse is computed, and the composition of positions (`pgComp`) is continuous.

* The space `ℝ^d × Sym_d` is inside `PgSp d = EuclideanSpace ℝ (Fin d ⊕ Fin d × Fin d)`: the coordinates `inl i` hold
  `μ`, the coordinates `inr (i, j)` the entries of a matrix, so that the norm is `(|μ|² + |T|_F²)^{1/2}`.
  `pgMu`, `pgMat`, `pgOp` read `μ`, the matrix and the operator; `pgPack` writes a pair. Positions live there too.
* `pgDom d ρ`: the domain `D`, `T` self-adjoint with `t_min ≤ T ≤ t_max`, `|μ| ≤ κ ρ` (`IsPgDom`).
* `pgMw K = E π_K(g) / E|g|`, the mean width `M(K)` in the form of the rows (`l(K)/E|g|`).
* `PgGood d K R o`: the conclusion of Theorems PG-core and PG for a returned position `o = some (μ, A)`: `A`
  invertible, `B̄(0, 1) ⊆ S(K) ⊆ B̄(0, R)` and `M(S(K)) ≤ 1.27 (d + 1)^{1/2}/d`.
* `PgGoodMeas`: for a closed convex body the set of positions `Q` with `PgGood d K R (some Q)` is Borel; it is proved
  in `PgMeasProof.lean`.

Junk values: the division by `E|g|` in `pgMw` is at a positive value for `d ≥ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AdversarialBco.Poly

/-- The domain space `ℝ^d × Sym_d`, with the Frobenius norm on the matrix part. -/
abbrev PgSp (d : ℕ) := EuclideanSpace ℝ (Fin d ⊕ Fin d × Fin d)

/-- The vector part `μ`. -/
def pgMu {d : ℕ} (x : PgSp d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => x (Sum.inl i)

/-- The matrix part `T`, as a matrix. -/
def pgMat {d : ℕ} (x : PgSp d) : Matrix (Fin d) (Fin d) ℝ := fun i j => x (Sum.inr (i, j))

/-- The matrix part `T`, as an operator. -/
noncomputable def pgOp {d : ℕ} (x : PgSp d) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)

/-- The point `(μ, M)` of `PgSp d`. -/
def pgPack {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) : PgSp d :=
  WithLp.toLp 2 (Sum.elim (fun i => μ i) (fun p => M p.1 p.2))

/-- The domain `D`. -/
def pgDom (d : ℕ) (ρ : ℝ) : Set (PgSp d) :=
  {x | IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x)}

/-- The composition of positions: the body `posBody K c A` put in the position `(μ', A')` is the body of `K` in the
position `(c + A μ', A A')`. -/
noncomputable def pgComp {d : ℕ} (P P' : PgSp d) : PgSp d := pgPack (pgMu P + pgOp P (pgMu P')) (pgMat P * pgMat P')

/-- `M(K) = E π_K(g) / E|g|`. -/
noncomputable def pgMw {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
    ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The conclusion of Theorems PG-core and PG for a returned position `(μ, A)`: `A` invertible, and the body
`S(K) = posBody K μ A` has `B̄(0, 1) ⊆ S(K) ⊆ B̄(0, R)` and `M(S(K)) ≤ 1.27 (d + 1)^{1/2}/d`. -/
def PgGood (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (o : Option (PgSp d)) : Prop :=
  ∃ P, o = some P ∧ (pgMat P).det ≠ 0 ∧ Metric.closedBall 0 1 ⊆ posBody K (pgMu P) (pgOp P) ∧
    posBody K (pgMu P) (pgOp P) ⊆ Metric.closedBall 0 R ∧
    pgMw (posBody K (pgMu P) (pgOp P)) ≤ 1.27 * Real.sqrt (d + 1) / d

/-- The positions that meet the conclusion of Theorems PG-core and PG for a closed convex body form a Borel set. -/
def PgGoodMeas : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ), Convex ℝ K → IsClosed K →
    MeasurableSet {Q : PgSp d | PgGood d K R (some Q)}

end AdversarialBco.Poly
