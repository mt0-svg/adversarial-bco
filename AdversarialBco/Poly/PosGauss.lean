/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBody

@[expose] public section

/-!
# Lemma F.1 and Proposition F.2: definitions and interface statements

Interface: the Gaussian l-position (Lemma F.1) and its certificate (Proposition F.2)
of Appendix F of the paper.

* `E d = EuclideanSpace ℝ (Fin d)` is written out, `γ = stdGaussian (E d)`.
* A body (`IsPosBody K r0 α`): `K` convex and compact, `B(0, r0) ⊆ K` with `r0 > 0`, and `-K ⊆ α K` with `α ≥ 0`;
  `π = gauge K`.
* For `μ ∈ E d` and `A : E d →L[ℝ] E d`: `F(y) = π(μ + A y)` (`posF`), the moments `k = E F(g)` (`posK`),
  `b = E[F(g) g]` (`posB`) and the form `Q(v, w) = E[(⟪v, g⟫ ⟪w, g⟫ - ⟪v, w⟫) F(g)]` (`posQ`), and the body
  `K' = A⁻¹(K - μ)`, written as the preimage `{y | μ + A y ∈ K}` (`posBody`), so that no inverse is needed.
* The objective of Lemma F.1, `h(μ, A) = E π(μ + A g) - (κ/d) log |det A|` (`posObj`), over every invertible `A`.
* The bathtub constant `C_α(t) = (1 + α) φ(t) + t (1 - (1 + α) Q(t))` (`bathC`), `φ` the standard Gaussian density
  and `Q(t) = ∫_t^∞ φ` (`BodySpec.phi`, `BodySpec.Qtail`). The source writes `c(α) = (1 + α) I(1/(1 + α))` and
  `q_α = I'(1/(1 + α))`; at `t = q_α` (`Q(q_α) = 1/(1 + α)`) one has `C_α(q_α) = c(α)`, and `C_α(t) ≥ c(α)` for every
  `t`. The statements below take `t` free, so that no quantile function is needed; `GaussConst` gives the `t` of
  Appendix F.

Junk values. `log |det A|` is read only for `det A ≠ 0`. `1 / (1 - k)` in `PropCc` has `k < 1`. In `PropCaBound`
the division is by `q > 0`. `Real.sqrt (2 * Real.log (1 + α))` has `α ≥ 1`, so its argument is at least `2 log 2`.

Every statement is a `Prop`; the theorems that prove them are in
`AdversarialBco/Poly/PosGaussProof.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise

namespace AdversarialBco.Poly

/-- A convex body for Lemma F.1 and Proposition F.2: convex and compact, `B(0, r0) ⊆ K` with `r0 > 0`, and `-K ⊆ α K`
with `α ≥ 0`. -/
def IsPosBody {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ 0 < r0 ∧ Metric.ball 0 r0 ⊆ K ∧ 0 ≤ α ∧ -K ⊆ α • K

/-- `F(y) = π(μ + A y)`, `π` the gauge of `K`. -/
noncomputable def posF {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  gauge K (μ + A y)

/-- `k = E F(g)`. -/
noncomputable def posK {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ g, posF K μ A g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- `b = E[F(g) g]`. -/
noncomputable def posB {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∫ g, posF K μ A g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- `Q(v, w) = E[(⟪v, g⟫ ⟪w, g⟫ - ⟪v, w⟫) F(g)]`, the form of the matrix `E[(g gᵀ - I) F(g)]`. -/
noncomputable def posQ {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (v w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * posF K μ A g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- `K' = A⁻¹(K - μ) = {y | μ + A y ∈ K}`. -/
def posBody {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | μ + A y ∈ K}

/-- The objective of Lemma F.1, `h(μ, A) = E π(μ + A g) - (κ/d) log |det A|`. -/
noncomputable def posObj {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (κ : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : ℝ :=
  posK K μ A - κ / d * Real.log |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|

/-- The bathtub constant `C_α(t) = (1 + α) φ(t) + t (1 - (1 + α) Q(t))`. -/
noncomputable def bathC (α t : ℝ) : ℝ :=
  (1 + α) * BodySpec.phi t + t * (1 - (1 + α) * BodySpec.Qtail t)

/-! ## Gaussian tools -/

/-- The standard Gaussian of `ℝ^d` is absolutely continuous with respect to Lebesgue measure. -/
def GaussAbsCont : Prop :=
  ∀ d : ℕ, stdGaussian (EuclideanSpace ℝ (Fin d)) ≪ volume

/-- Rademacher's theorem under the Gaussian: a Lipschitz function is differentiable `γ`-almost everywhere. -/
def GaussAeDiff : Prop :=
  ∀ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0), LipschitzWith L F →
    ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ F g

/-- Gaussian integration by parts for a convex Lipschitz function, once and twice: `E[⟪v, g⟫ F(g)] = E[DF(g) v]` and
`E[(⟪v, g⟫ ⟪w, g⟫ - ⟪v, w⟫) F(g)] = E[⟪v, g⟫ DF(g) w]` (`fderiv` is `0` off the points of differentiability, a null
set). -/
def IbpLip : Prop :=
  ∀ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0), LipschitzWith L F → ConvexOn ℝ Set.univ F →
    ∀ v w : EuclideanSpace ℝ (Fin d),
      ∫ g, ⟪v, g⟫ * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
          ∫ g, fderiv ℝ F g v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
        ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
          ∫ g, ⟪v, g⟫ * fderiv ℝ F g w ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The bathtub bound of Step 4 of Lemma F.1 and of Proposition F.2, at a free `t`: for a unit `u` and `h` with values in
`[-α k, k]` almost everywhere, `|E[⟪u, g⟫ h]| ≤ k C_α(t) + |t| |E h|`. -/
def BathtubBound : Prop :=
  ∀ (d : ℕ) (u : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 → ∀ (h : EuclideanSpace ℝ (Fin d) → ℝ) (α k t : ℝ),
    0 ≤ α → 0 ≤ k → AEStronglyMeasurable h (stdGaussian (EuclideanSpace ℝ (Fin d))) →
    (∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -(α * k) ≤ h g ∧ h g ≤ k) →
    |∫ g, ⟪u, g⟫ * h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      k * bathC α t + |t| * |∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|

/-- `C_α(t) ≥ 0` for `α ≥ 0`. -/
def BathCNonneg : Prop :=
  ∀ α t : ℝ, 0 ≤ α → 0 ≤ bathC α t

/-- The constants, item 3: for `α ≥ 1` and `λ = (2 log(1 + α))^{1/2}`, the point `t = q_α` has
`0 ≤ q_α ≤ λ` and `C_α(q_α) = c(α) ≤ λ`. -/
def GaussConst : Prop :=
  ∀ α : ℝ, 1 ≤ α → ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.sqrt (2 * Real.log (1 + α)) ∧
    bathC α t ≤ Real.sqrt (2 * Real.log (1 + α))

/-! ## Proposition F.2 (the certificate) -/

/-- Proposition F.2 (a), before the choice of the radius: if `Q ≥ q I` and `A y0 = -μ`, then every `y ∈ K'` has
`q |y| ≤ (1 + k) C_α(t) + |t| |b| (|y - y0| + |y0|)`. -/
def PropCa : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    ∀ (q t : ℝ) (y0 : EuclideanSpace ℝ (Fin d)), A y0 = -μ → (∀ v, q * ‖v‖ ^ 2 ≤ posQ K μ A v v) →
    ∀ y ∈ posBody K μ A, q * ‖y‖ ≤ (1 + posK K μ A) * bathC α t + |t| * ‖posB K μ A‖ * (‖y - y0‖ + ‖y0‖)

/-- Proposition F.2 (a): if `Q ≥ q I` with `q > 0` and `6 |t| |b| ≤ q`, then `K' ⊆ B(0, 2 (1 + k) C_α(t)/q)`. -/
def PropCaBound : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    ∀ q t : ℝ, 0 < q → (∀ v, q * ‖v‖ ^ 2 ≤ posQ K μ A v v) → 6 * |t| * ‖posB K μ A‖ ≤ q →
    ∀ y ∈ posBody K μ A, ‖y‖ ≤ 2 * (1 + posK K μ A) * bathC α t / q

/-- Proposition F.2 (b): if `k ≤ Q(a)`, then `B̄(0, a) ⊆ K'`. -/
def PropCb : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    ∀ a : ℝ, posK K μ A ≤ BodySpec.Qtail a → Metric.closedBall 0 a ⊆ posBody K μ A

/-- Proposition F.2 (c): if `k < 1`, then `l(K') = E π_{K'}(g) ≤ 1/(1 - k)`. -/
def PropCc : Prop :=
  ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α → posK K μ A < 1 →
    ∫ g, gauge (posBody K μ A) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 1 / (1 - posK K μ A)

/-! ## Lemma F.1 (the Gaussian l-position) -/

/-- Lemma F.1, existence and stationarity in value form: `h` has a minimiser `(μ, A)` over every invertible `A`, and
there `k = κ`, `b = 0` and `Q = (κ/d) I`. -/
def LemmaL : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ), IsPosBody K r0 α → 0 < κ →
    ∃ (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
      (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        posObj K κ μ A ≤ posObj K κ μ' A') ∧
      posK K μ A = κ ∧ posB K μ A = 0 ∧ ∀ v w, posQ K μ A v w = κ / d * ⟪v, w⟫

/-- The stationarity part of Lemma F.1 at any minimiser: if `(μ, A)` minimises `h` over every invertible `A'`, then
`k = κ`, `b = 0` and `Q = (κ/d) I`. -/
def LemmaLOfMin : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α → 0 < κ →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
    (∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      posObj K κ μ A ≤ posObj K κ μ' A') →
    posK K μ A = κ ∧ posB K μ A = 0 ∧ ∀ v w, posQ K μ A v w = κ / d * ⟪v, w⟫

/-- Lemma F.1 (a) to (c) at a point with the value forms of the minimiser (`k = κ`, `b = 0`, `Q = (κ/d) I`): `K'` lies in
`B(0, d (1 + κ) C_α(t)/κ)` for every `t`, contains `B̄(0, a)` whenever `κ ≤ Q(a)` and has `l(K') ≤ 1/(1 - κ)`. -/
def LemmaLRadii : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), IsPosBody K r0 α →
    LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 → 0 < κ → κ < 1 →
    posK K μ A = κ → posB K μ A = 0 → (∀ v w, posQ K μ A v w = κ / d * ⟪v, w⟫) →
    (∀ t : ℝ, ∀ y ∈ posBody K μ A, ‖y‖ ≤ d * (1 + κ) * bathC α t / κ) ∧
    (∀ a : ℝ, κ ≤ BodySpec.Qtail a → Metric.closedBall 0 a ⊆ posBody K μ A) ∧
    ∫ g, gauge (posBody K μ A) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 1 / (1 - κ)

end AdversarialBco.Poly
