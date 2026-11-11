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
# The lemmas of Theorem 8.3: definitions and interface statements

Interface of the first part: the deterministic and Gaussian lemmas of
Appendix F of the paper (Proposition A, Lemma B, the domain facts (D1), (D4), (D5), Lemma E, the pathwise bound of
Lemma SGD), with the relative error `η` of Lemma B free. The randomized procedure (the descent in expectation,
Lemma T, Theorems PG-core and PG) is the second part. Notation of `AdversarialBco/Poly/PosGauss.lean`.

* `bisect P lo hi j`: the interval kept after `j` steps of bisection on `[lo, hi]` for an upward-closed question `P`.
* `piTilde K ρ j x`: the gauge by bisection of Lemma B, the upper end after `j` steps on `[|x|/ρ, |x|]` with the
  question `x/s ∈ K` (asked for `s > 0`), and `piTilde K ρ j 0 = 0`.
* `IsPgDom τ0 τ1 R μ T`: `(μ, T)` is in the domain `D` with `t_min = τ0`, `t_max = τ1` and `|μ| ≤ R`
  (`R = κ ρ` there): `T` self-adjoint with `τ0 |v|^2 ≤ ⟪T v, v⟫ ≤ τ1 |v|^2`.
* `IsInvPair T Ti`: `Ti` is the inverse of `T`.
* `gstat g i j = g_i g_j - δ_ij`, the entries of `g gᵀ - I`.

Junk values. `piTilde` divides by `ρ`, by `s` and by `2^j`; the statements assume `ρ ≥ 1` and the questions are asked
for `s > 0` only. `Real.log` is read at `x = k/κ > 0` and at `det T > 0`. `Real.sqrt (2 / Real.pi)` is positive.

Every statement is a `Prop`; the theorems that prove them are in `AdversarialBco/Poly/PgLemmasProof.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise

namespace AdversarialBco.Poly

open Classical in
/-- Bisection on `[lo, hi]` for an upward-closed question `P`: after `j` steps, the interval kept; each step asks `P`
at the midpoint and keeps the half where the threshold lies. -/
noncomputable def bisect (P : ℝ → Prop) (lo hi : ℝ) : ℕ → ℝ × ℝ
  | 0 => (lo, hi)
  | j + 1 =>
    let I := bisect P lo hi j
    if P ((I.1 + I.2) / 2) then (I.1, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2, I.2)

open Classical in
/-- The gauge by bisection of Lemma B: `j` steps on `[|x|/ρ, |x|]` with the question `x/s ∈ K`, the upper end. -/
noncomputable def piTilde {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if x = 0 then 0 else (bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2

/-- `(μ, T)` is in the domain `D`: `T` self-adjoint with `τ0 ≤ T ≤ τ1`, and `|μ| ≤ R`. -/
def IsPgDom {d : ℕ} (τ0 τ1 R : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  IsSelfAdjoint T ∧ ‖μ‖ ≤ R ∧ ∀ v, τ0 * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ ∧ ⟪T v, v⟫ ≤ τ1 * ‖v‖ ^ 2

/-- `Ti` is the inverse of `T`. -/
def IsInvPair {d : ℕ} (T Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  T.comp Ti = ContinuousLinearMap.id ℝ _ ∧ Ti.comp T = ContinuousLinearMap.id ℝ _

/-- The entries of `g gᵀ - I`. -/
noncomputable def gstat {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) (i j : Fin d) : ℝ :=
  g i * g j - if i = j then 1 else 0

/-! ## Lemma B (the gauge by bisection) -/

/-- Bisection keeps the threshold: the kept interval contains `p` and has length `(hi - lo)/2^j`. -/
def BisectSpec : Prop :=
  ∀ (P : ℝ → Prop) (p lo hi : ℝ), (∀ s, P s ↔ p ≤ s) → lo ≤ p → p ≤ hi → ∀ j : ℕ,
    (bisect P lo hi j).1 ≤ p ∧ p ≤ (bisect P lo hi j).2 ∧
      (bisect P lo hi j).2 - (bisect P lo hi j).1 = (hi - lo) / 2 ^ j

/-- `B̄(0, 1) ⊆ K ⊆ B̄(0, ρ)` gives `|x|/ρ ≤ π(x) ≤ |x|`. -/
def GaugeBounds : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ), 0 < ρ → Convex ℝ K →
    Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 ρ → ∀ x, ‖x‖ / ρ ≤ gauge K x ∧ gauge K x ≤ ‖x‖

/-- Lemma B: `π ≤ π~ ≤ π + |x| 2^{-j}`, hence `π~ ≤ (1 + η) π` when `ρ 2^{-j} ≤ η`. -/
def LemmaB : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ), 1 ≤ ρ → Convex ℝ K → IsClosed K →
    Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 ρ → ∀ (j : ℕ) (η : ℝ), ρ / 2 ^ j ≤ η → ∀ x,
      gauge K x ≤ piTilde K ρ j x ∧ piTilde K ρ j x ≤ gauge K x + ‖x‖ / 2 ^ j ∧
        piTilde K ρ j x ≤ (1 + η) * gauge K x

/-- `π~` is a Borel function. -/
def PiTildeMeasurable : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ), IsClosed K → ∀ j : ℕ, Measurable (piTilde K ρ j)

/-! ## The domain -/

/-- (D4): on `D` with `B̄(0, 1) ⊆ K`, `F(y) = π(μ + T y)` is `τ1`-Lipschitz and `0 ≤ F(y) ≤ |μ| + τ1 |y|`, and
`E F(g)^2 ≤ (R + τ1 d^{1/2})^2`. -/
def D4Bounds : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (τ0 τ1 R : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), Convex ℝ K → Metric.closedBall 0 1 ⊆ K →
    0 ≤ τ0 → IsPgDom τ0 τ1 R μ T →
    LipschitzWith (Real.toNNReal τ1) (posF K μ T) ∧ (∀ y, 0 ≤ posF K μ T y ∧ posF K μ T y ≤ ‖μ‖ + τ1 * ‖y‖) ∧
      ∫ g, posF K μ T g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (R + τ1 * Real.sqrt d) ^ 2

/-- The minimiser of Lemma F.1 can be taken symmetric: for invertible `A` there is a symmetric positive definite `T`
with the same Gaussian law `T g ~ A g` and `|det T| = |det A|` (`T = (A Aᵀ)^{1/2}`). -/
def PolarSym : Prop :=
  ∀ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    ∃ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSelfAdjoint T ∧
      (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) ∧
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map T = (stdGaussian (EuclideanSpace ℝ (Fin d))).map A ∧
      |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
        |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|

/-- Lemma F.1 with a symmetric positive definite minimiser `T`, with the value forms `k = κ`, `b = 0`, `Q = (κ/d) I`. -/
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

/-- (D5): the subgradient inequality of `h` on positive definite operators, with the gradient
`(T⁻¹ b, sym(T⁻¹ Q) - (κ/d) T⁻¹)` written through its pairings. -/
def D5Subgrad : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ) (μ μ' : EuclideanSpace ℝ (Fin d))
    (T T' Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    IsSelfAdjoint T → IsSelfAdjoint T' → (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) → (∀ v, v ≠ 0 → 0 < ⟪T' v, v⟫) →
    IsInvPair T Ti → 0 ≤ κ →
    posObj K κ μ T + ⟪posB K μ T, Ti (μ' - μ)⟫ +
        ∑ i, posQ K μ T (EuclideanSpace.single i 1) (Ti ((T' - T) (EuclideanSpace.single i 1))) -
        κ / d * LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≤
      posObj K κ μ' T'

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

/-- The Gaussian curvature bound of Proposition A (ii): for a convex `L`-Lipschitz `F`, a unit `u` and `s ≥ 0`,
`E F(g + s ⟪u, g⟫ u) ≤ E F(g) + s E[(⟪u, g⟫^2 - 1) F(g)] + c_2 L s^2/2` with `c_2 = 8 φ(2^{1/2})`. -/
def CurvBound : Prop :=
  ∀ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0), LipschitzWith L F → ConvexOn ℝ Set.univ F →
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ s : ℝ, 0 ≤ s →
      ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
          s * ∫ g, (⟪u, g⟫ ^ 2 - 1) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + pgC2 * L * s ^ 2 / 2

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

/-- Lemma E (a), vector part: `|E[ε(g) g]|^2 ≤ E ε(g)^2`. -/
def VecCS : Prop :=
  ∀ (d : ℕ) (ε : EuclideanSpace ℝ (Fin d) → ℝ), MemLp ε 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) →
    ‖∫ g, ε g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖ ^ 2 ≤
      ∫ g, ε g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- Lemma E (a), matrix part: `|E[(g gᵀ - I) ε(g)]|_F^2 ≤ 2 E ε(g)^2`. -/
def MatCS : Prop :=
  ∀ (d : ℕ) (ε : EuclideanSpace ℝ (Fin d) → ℝ), MemLp ε 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) →
    ∑ i, ∑ j, (∫ g, gstat g i j * ε g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ^ 2 ≤
      2 * ∫ g, ε g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- `|g gᵀ - I|_F^2 = |g|^4 - 2 |g|^2 + d`. -/
def FrobStat : Prop :=
  ∀ (d : ℕ) (g : EuclideanSpace ℝ (Fin d)), ∑ i, ∑ j, gstat g i j ^ 2 = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + d

/-- The chi-square moments `E|g|^4 = d (d + 2)` and `E|g|^6 = d (d + 2)(d + 4)`. -/
def GaussMoments : Prop :=
  ∀ d : ℕ, ∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) ∧
    ∫ g, ‖g‖ ^ 6 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) * (d + 4)

/-- The two moments of Lemma E (b): `E[|g|^2 (1 + |g|^2)] = d (d + 3)` and
`E[(|g|^4 - 2 |g|^2 + d)(1 + |g|^2)] = d (d + 1)(d + 5)`. -/
def MomentsE : Prop :=
  ∀ d : ℕ, ∫ g, ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 3) ∧
    ∫ g, (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (d : ℝ) * (d + 1) * (d + 5)

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
