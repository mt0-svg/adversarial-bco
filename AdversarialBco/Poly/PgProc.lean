/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgLemmas
public import AdversarialBco.Poly.PgProb

@[expose] public section

/-!
# Procedure PG: positions, the domain and the conclusion

Definitions for Procedure PG, in the real-RAM model: exact real arithmetic, exact standard Gaussian samples, exact
membership answers. The procedure itself, with the changes of PG-N, is defined in Conj1Arith/Proc.lean (`pgCoreN`,
`pgStageN`, `pgN`).

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

open Classical in
/-- A nearest point of `D`. -/
noncomputable def pgProj (d : ℕ) (ρ : ℝ) (y : PgSp d) : PgSp d :=
  if h : ∃ z ∈ pgDom d ρ, ∀ w ∈ pgDom d ρ, ‖y - z‖ ≤ ‖y - w‖ then h.choose else y

/-- `j`, the number of bisection steps: the least integer with `2^j ≥ ρ/η`. -/
noncomputable def pgJb (d : ℕ) (ρ : ℝ) : ℕ := ⌈Real.logb 2 (ρ / pgEta d ρ)⌉₊

/-- `N`, the number of descent steps. -/
noncomputable def pgNs (d : ℕ) (ρ : ℝ) : ℕ := ⌈pgNreal d ρ⌉₊

/-- The step size `s = Δ/(G N^{1/2})`. -/
noncomputable def pgStepSize (d : ℕ) (ρ : ℝ) : ℝ :=
  pgDelta d ρ / (Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ))

/-- `n_T`, the number of samples of a basic verdict. -/
noncomputable def pgNT (d : ℕ) (ρ : ℝ) : ℕ := ⌈pgNTreal d ρ⌉₊

/-- `J`, the number of repeats: the least integer with `2^J ≥ 4/δ`. -/
noncomputable def pgJr (δ : ℝ) : ℕ := ⌈Real.logb 2 (4 / δ)⌉₊

/-- `m_T`, the number of basic verdicts: the least integer above `8 log (1/δ')`, `δ' = δ/(2J)`. -/
noncomputable def pgMT (δ : ℝ) : ℕ := ⌈8 * Real.log (2 * pgJr δ / δ)⌉₊

/-- The gauge by bisection at `μ + T g`. -/
noncomputable def pgFt {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  piTilde K ρ (pgJb d ρ) (pgMu x + pgOp x g)

/-- The matrix `g gᵀ - I`. -/
def pgGG {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec (fun i => g i) (fun i => g i) - 1

/-- The estimate of Lemma E: `(T⁻¹ g F~(g), sym(T⁻¹ (g gᵀ - I)) F~(g) - (κ/d) T⁻¹)`. -/
noncomputable def pgV {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (g : EuclideanSpace ℝ (Fin d)) : PgSp d :=
  pgPack (WithLp.toLp 2 ((pgFt K ρ x g) • ((pgMat x)⁻¹ *ᵥ fun i => g i)))
    ((pgFt K ρ x g / 2) • ((pgMat x)⁻¹ * pgGG g + ((pgMat x)⁻¹ * pgGG g)ᵀ) - (pgKappa / d) • (pgMat x)⁻¹)

/-- The starting point `x_1 = (0, t_min I)`. -/
noncomputable def pgX1 (d : ℕ) (ρ : ℝ) : PgSp d := pgPack 0 (pgTmin d ρ • 1)

/-- The average `x̄` of the descent on the samples `a`. -/
noncomputable def pgDescent {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (a : ℕ → EuclideanSpace ℝ (Fin d)) :
    PgSp d :=
  sgdAvg (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) (pgNs d ρ) a

/-- The basic verdict of the test on the samples `w 0, ..., w (n_T - 1)`. -/
def pgVerdict {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  let n := pgNT d ρ
  let kh := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, pgFt K ρ x (w i)
  let bh := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, pgFt K ρ x (w i) • w i
  let Qh := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, pgFt K ρ x (w i) • pgGG (w i)
  kh ≤ 1.075 * pgKappa ∧ ‖bh‖ ≤ 3 / 4 * pgTaub d ρ ∧
    ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Qh *ᵥ v)

open Classical in
/-- The amplified test: more than `m_T/2` of the basic verdicts on the blocks `w 0, ..., w (m_T - 1)` accept. -/
def pgTest {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (x : PgSp d)
    (w : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  (pgMT δ : ℝ) / 2 < ((Finset.range (pgMT δ)).filter fun i => pgVerdict K ρ x (w i)).card

/-- A block of the stream: the samples of one descent and those of one amplified test. -/
abbrev PgRound (d : ℕ) := (ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))

/-- The law of a block: independent standard Gaussian vectors. -/
noncomputable def pgRoundMeasure (d : ℕ) : Measure (PgRound d) :=
  (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))).prod
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The law of the stream of the core of the procedure (`pgCoreN`): one independent block per repeat. -/
noncomputable def pgCoreMeasure (d : ℕ) : Measure (ℕ → PgRound d) :=
  Measure.infinitePi fun _ : ℕ => pgRoundMeasure d

/-- The position returned for an accepted point `x = (μ, T)`: `(μ, a T)`, `a = pgA = 1`. The body in this position is
`posBody K μ (a T) = (a T)⁻¹ (K - μ)`, the image of `K` by the affine map `S y = (a T)⁻¹ (y - μ)`. -/
noncomputable def pgOut {d : ℕ} (x : PgSp d) : PgSp d := pgPack (pgMu x) (pgA • pgMat x)

open Classical in
/-- Procedure PG-core: the position of the first repeat `r < J` whose test accepts, or `none`. -/
noncomputable def pgCore (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (ω : ℕ → PgRound d) :
    Option (PgSp d) :=
  if h : ∃ r < pgJr δ, pgTest K ρ δ (pgDescent K ρ (ω r).1) (ω r).2 then
    some (pgOut (pgDescent K ρ (ω (Nat.find h)).1))
  else none

/-- The composition of positions: the body `posBody K c A` put in the position `(μ', A')` is the body of `K` in the
position `(c + A μ', A A')`. -/
noncomputable def pgComp {d : ℕ} (P P' : PgSp d) : PgSp d := pgPack (pgMu P + pgOp P (pgMu P')) (pgMat P * pgMat P')

/-- The radius ratio of stage `i` of the growing balls: `ρ_1 = 2`, `ρ_{i+1} = 3 · 54 d (log (1 + ρ_i))^{1/2}`
(indexed from `0`: `pgRhoStage d 0 = ρ_1`). -/
noncomputable def pgRhoStage (d : ℕ) : ℕ → ℝ
  | 0 => 2
  | i + 1 => 3 * (54 * d * Real.sqrt (Real.log (1 + pgRhoStage d i)))

/-- The number of stages `m = max 1 ⌈log₂ (R0/r0)⌉`. -/
noncomputable def pgStages (r0 R0 : ℝ) : ℕ := max 1 ⌈Real.logb 2 (R0 / r0)⌉₊

/-- The position after stages `0, ..., i - 1` of the growing balls (stage `i + 1` of the appendix on the position is
index `i` here),
from `S_0 y = y / r0`, the position `(0, r0 I)`; `none` once a stage returns `none`. Stage `i` runs `pgCore` on the
body of `K ∩ B̄(0, 2^{i+1} r0)` in the current position, with the ratio `ρ_{i+1}` and on the stream `ω i`. -/
noncomputable def pgStage (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ) (ω : ℕ → ℕ → PgRound d) :
    ℕ → Option (PgSp d)
  | 0 => some (pgPack 0 (r0 • 1))
  | i + 1 => (pgStage d K r0 δ' ω i).bind fun P =>
      (pgCore d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d i) δ'
        (ω i)).map (pgComp P)

/-- Procedure PG: the position after the `m` stages, each at failure probability `δ/m`. -/
noncomputable def pg (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ) (ω : ℕ → ℕ → PgRound d) :
    Option (PgSp d) :=
  pgStage d K r0 (δ / pgStages r0 R0) ω (pgStages r0 R0)

/-- The law of the stream of `pg`: one independent stream of `pgCore` per stage. -/
noncomputable def pgMeasure (d : ℕ) : Measure (ℕ → ℕ → PgRound d) :=
  Measure.infinitePi fun _ : ℕ => pgCoreMeasure d

instance pgRoundMeasure_isProb (d : ℕ) : IsProbabilityMeasure (pgRoundMeasure d) := by
  unfold pgRoundMeasure; infer_instance

instance pgCoreMeasure_isProb (d : ℕ) : IsProbabilityMeasure (pgCoreMeasure d) := by
  unfold pgCoreMeasure; infer_instance

instance pgMeasure_isProb (d : ℕ) : IsProbabilityMeasure (pgMeasure d) := by
  unfold pgMeasure; infer_instance

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

/-- The output of `pgCore` on a closed body in the position `P` is measurable jointly in `P` and the stream: the
event that a position is returned, and the position returned (`0` when none is). -/
def PgCoreMeas : Prop :=
  ∀ (d : ℕ) (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ), IsClosed K' →
    MeasurableSet {p : PgSp d × (ℕ → PgRound d) |
      (pgCore d (posBody K' (pgMu p.1) (pgOp p.1)) ρ δ p.2).isSome} ∧
    Measurable fun p : PgSp d × (ℕ → PgRound d) =>
      (pgCore d (posBody K' (pgMu p.1) (pgOp p.1)) ρ δ p.2).getD 0

/-- The output of `pg` on a closed body is measurable in the stream. -/
def PgMeas : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ), IsClosed K →
    MeasurableSet {ω : ℕ → ℕ → PgRound d | (pg d K r0 R0 δ ω).isSome} ∧
    Measurable fun ω : ℕ → ℕ → PgRound d => (pg d K r0 R0 δ ω).getD 0

/-- The positions that meet the conclusion of Theorems PG-core and PG for a closed convex body form a Borel set. -/
def PgGoodMeas : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ), Convex ℝ K → IsClosed K →
    MeasurableSet {Q : PgSp d | PgGood d K R (some Q)}

/-- The theorem PG-core. -/
def PgCoreThm : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ), 1 ≤ d → Convex ℝ K → IsClosed K →
    Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 ρ → 1 ≤ ρ → 0 < δ → δ < 1 →
    pgCoreMeasure d {ω | ¬ PgGood d K (36.4 * d * pgLam ρ) (pgCore d K ρ δ ω)} ≤ ENNReal.ofReal δ

/-- The theorem of Procedure PG. -/
def PgThm : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 R0 δ : ℝ), 1 ≤ d → Convex ℝ K → IsClosed K →
    0 < r0 → r0 ≤ R0 → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 → 0 < δ → δ < 1 →
    pgMeasure d {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pg d K r0 R0 δ ω)} ≤
      ENNReal.ofReal δ

end AdversarialBco.Poly
