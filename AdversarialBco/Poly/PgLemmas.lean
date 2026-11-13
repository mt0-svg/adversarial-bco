/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PosGauss
public import AdversarialBco.Poly.PgArith

@[expose] public section

/-!
# The lemmas of the theorem of Procedure PG: definitions and interface statements

Interface of deterministic and Gaussian lemmas of the paper's appendix on the position: the symmetric form of the
Gaussian position lemma, the domain facts (D1), the concavity of `log det`, Proposition A, the Gaussian moments of
Lemma E and the pathwise bound of Lemma SGD. Notation of `AdversarialBco/Poly/PosGauss.lean`.

* `IsPgDom τ0 τ1 R μ T`: `(μ, T)` is in the domain `D` with `t_min = τ0`, `t_max = τ1` and `|μ| ≤ R`
  (`R = κ ρ` there): `T` self-adjoint with `τ0 |v|^2 ≤ ⟪T v, v⟫ ≤ τ1 |v|^2`.
* `IsInvPair T Ti`: `Ti` is the inverse of `T`.

Junk values. `Real.log` is read at `x = k/κ > 0` and at `det T > 0`. `Real.sqrt (2 / Real.pi)` is positive.

Every statement is a `Prop`; the theorems that prove them are in `AdversarialBco/Poly/PgLemmasProof.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise

namespace AdversarialBco.Poly

/-- `(μ, T)` is in the domain `D`: `T` self-adjoint with `τ0 ≤ T ≤ τ1`, and `|μ| ≤ R`. -/
def IsPgDom {d : ℕ} (τ0 τ1 R : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  IsSelfAdjoint T ∧ ‖μ‖ ≤ R ∧ ∀ v, τ0 * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ ∧ ⟪T v, v⟫ ≤ τ1 * ‖v‖ ^ 2

/-- `Ti` is the inverse of `T`. -/
def IsInvPair {d : ℕ} (T Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  T.comp Ti = ContinuousLinearMap.id ℝ _ ∧ Ti.comp T = ContinuousLinearMap.id ℝ _

/-! ## The domain -/

/-- The minimiser of the Gaussian position lemma can be taken symmetric: for invertible `A` there is a symmetric
positive definite `T`
with the same Gaussian law `T g ~ A g` and `|det T| = |det A|` (`T = (A Aᵀ)^{1/2}`). -/
def PolarSym : Prop :=
  ∀ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    ∃ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSelfAdjoint T ∧
      (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) ∧
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map T = (stdGaussian (EuclideanSpace ℝ (Fin d))).map A ∧
      |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
        |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|

/-- The Gaussian position lemma with a symmetric positive definite minimiser `T`, with the value forms `k = κ`, `b = 0`,
`Q = (κ/d) I`. -/
def LemmaLSym : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ), IsPosBody K r0 α → 0 < κ →
    ∃ (μ : EuclideanSpace ℝ (Fin d)) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      IsSelfAdjoint T ∧ (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) ∧
      (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        posObj K κ μ T ≤ posObj K κ μ' A') ∧
      posK K μ T = κ ∧ posB K μ T = 0 ∧ ∀ v w, posQ K μ T v w = κ / d * ⟪v, w⟫

/-- (D1), the bounds read from `k = κ` and `B̄(0, 1) ⊆ K ⊆ B̄(0, ρ)`: `|μ| ≤ ρ κ` and `|Aᵀ u| (2/π)^{1/2} ≤ ρ κ` for
unit `u`. -/
def D1Bounds : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), 0 < ρ → Convex ℝ K →
    Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 ρ →
    ‖μ‖ ≤ ρ * posK K μ A ∧
      ∀ u, ‖u‖ = 1 → ‖(ContinuousLinearMap.adjoint A) u‖ * Real.sqrt (2 / Real.pi) ≤ ρ * posK K μ A

/-- (D1), the lower bound on `A`: if `K' ⊆ B̄(0, R')` and `B̄(0, 1) ⊆ K`, then `|A⁻¹ u| ≤ R'` for `|u| ≤ 1`. -/
def D1Inv : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (R' : ℝ),
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    Metric.closedBall 0 1 ⊆ K → (∀ y ∈ posBody K μ A, ‖y‖ ≤ R') →
    ∀ u y : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → A y = u → ‖y‖ ≤ R'

/-- `log det` is concave on positive definite operators: `log det T' ≤ log det T + tr(T⁻¹ (T' - T))`. -/
def LogDetConcave : Prop :=
  ∀ (d : ℕ) (T T' Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    IsSelfAdjoint T → IsSelfAdjoint T' → (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) → (∀ v, v ≠ 0 → 0 < ⟪T' v, v⟫) →
    IsInvPair T Ti →
    Real.log (LinearMap.det (T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≤
      Real.log (LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) +
        LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))

/-! ## Proposition A (approximate minimisers pass the test) -/

/-- Proposition A (i): if `h(μ, A) ≤ h* + e`, then `κ (x - 1 - log x) ≤ e` for `x = k/κ`. -/
def PropAi : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), 1 ≤ d → IsPosBody K r0 α → 0 < κ →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K κ μ' A') →
    posObj K κ μ A ≤ hstar + e → 0 < posK K μ A →
    κ * (posK K μ A / κ - 1 - Real.log (posK K μ A / κ)) ≤ e

/-- Proposition A (ii): if `h(μ, A) ≤ h* + e` with `e < t^2 (κ/d)^2/(2 (c_2 L_F + κ/d))`, `0 < t < 1`, then
`Q ≥ (1 - t)(κ/d) I`. -/
def PropAii : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e t : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), 1 ≤ d → IsPosBody K r0 α → 0 < κ →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K κ μ' A') →
    posObj K κ μ A ≤ hstar + e → ∀ L : ℝ≥0, LipschitzWith L (posF K μ A) → 0 < t → t < 1 →
    e < t ^ 2 * (κ / d) ^ 2 / (2 * (pgC2 * L + κ / d)) →
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → (1 - t) * (κ / d) ≤ posQ K μ A u u

/-- Proposition A (iii): if `h(μ, A) ≤ h* + e`, then `|b|^2 ≤ 2 (2/π)^{1/2} L_F e`. -/
def PropAiii : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K κ μ' A') →
    posObj K κ μ A ≤ hstar + e → ∀ L : ℝ≥0, LipschitzWith L (posF K μ A) →
    ‖posB K μ A‖ ^ 2 ≤ 2 * Real.sqrt (2 / Real.pi) * L * e

/-! ## Lemma E and the Gaussian moments -/

/-- The chi-square moments `E|g|^4 = d (d + 2)` and `E|g|^6 = d (d + 2)(d + 4)`. -/
def GaussMoments : Prop :=
  ∀ d : ℕ, ∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) ∧
    ∫ g, ‖g‖ ^ 6 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) * (d + 4)

/-- `E|g| ≥ d/(d + 1)^{1/2}` (item 1). -/
def NormMeanLower : Prop :=
  ∀ d : ℕ, (d : ℝ) / Real.sqrt (d + 1) ≤ ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-! ## Lemma SGD, pathwise -/

/-- The pathwise bound of projected subgradient descent (the source's Theorem thm:sgd:abstract): for iterates
`x_{t+1} = Proj_D(x_t - s v_t)` with a nonexpansive projection, `∑_{t < N} ⟪v_t, x_t - x*⟫ ≤ Δ^2/(2s) + (s/2) ∑ |v_t|^2`. -/
def SgdPathwise : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (D : Set E) (proj : E → E),
    (∀ y, ∀ z ∈ D, ‖proj y - z‖ ≤ ‖y - z‖) → ∀ xs ∈ D, ∀ (s Δ : ℝ), 0 < s → ∀ (x v : ℕ → E),
    (∀ t, x (t + 1) = proj (x t - s • v t)) → ‖x 0 - xs‖ ≤ Δ → ∀ N : ℕ,
      ∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫ ≤ Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v t‖ ^ 2

end AdversarialBco.Poly
