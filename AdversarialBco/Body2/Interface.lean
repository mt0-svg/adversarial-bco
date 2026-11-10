/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBody

@[expose] public section

/-!
# The cut of Theorem 3.1 between its regular case and every family

`AdversarialBco.BodySpec.DilTheorem` (Theorem 3.1 for every family) is proved from two statements on regular
families, defined below:

* `EcReg`: Lemma 3.2 for one regular convex function (a minimiser of the entropic objective over invertible `S`
  exists, and every such minimiser has (S4) and (S3));
* `DilRegExplicit`: Theorem 3.1 with (P3) for a regular family, with the frozen constant `KS`.

`AdversarialBco/Body2/Dil2.lean` proves both (`AdversarialBco.Body2.ecReg`, `AdversarialBco.Body2.dilRegExplicit`); Appendix
D (smoothing, uniqueness, compactness, the minimiser over invertible `S` against the one over positive
definite `S`, and the limit) proves `DilRegExplicit → EcReg → DilTheorem`.

The minimiser here ranges over every invertible `S` with `log |det S|`, the setting of the proof of Lemma 3.2;
`IsEntropicGaussian` ranges over symmetric positive definite `S` with `log det S`. The two objectives take the same
value at `S` and at `(S Sᵀ)^{1/2}` (rotation invariance of the standard Gaussian).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec

/-- `(b, S)` minimises `E G(b + S Z) - lam log |det S|` over `b ∈ ℝ^d` and invertible `S`. -/
def IsMinInv {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
    ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
        ∫ z, G (b' + S' z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          lam * Real.log |LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|

/-- Lemma 3.2 for a regular convex function: for `G` convex, of class `C^2`, Lipschitz, with a Lipschitz
gradient, and coercive, and `lam > 0`, a minimiser over invertible `S` exists, and every such minimiser has (S4)
`G b ≤ E G(b + S Z)` and (S3) `E G(b + S Z) ≤ G y + lam d` for every `y`. -/
def EcReg : Prop :=
  ∀ (d : ℕ) (G : EuclideanSpace ℝ (Fin d) → ℝ) (Lp Mp : ℝ≥0) (a1 a2 lam : ℝ), ContDiff ℝ 2 G →
    ConvexOn ℝ Set.univ G → LipschitzWith Lp G → LipschitzWith Mp (fderiv ℝ G) → 0 < a1 →
    (∀ x, a1 * ‖x‖ - a2 ≤ G x) → 0 < lam →
    (∃ b S, IsMinInv G lam b S) ∧ ∀ b S, IsMinInv G lam b S →
      G b ≤ ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
        ∀ y, ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ G y + lam * d

/-- Theorem 3.1 with (P3) for a regular family (each `F c` of class `C^2`, convex, `L`-Lipschitz, with an
`Mp`-Lipschitz gradient, minimal at `xmin c`; weights `w c ≥ 0` of sum `1`; coercive mean minimal at `bstar`;
floor `Δ* > 0`): there is a scale `h ∈ [Δ*/2, gmax]`, one of the gains, such that a minimiser over invertible `S`
at temperature `h/(16 d)` exists, and every such `(b, S)` has (S4), (S3) and (P3) with
`T = (2 ln⁺(26 d L ‖S‖ / h))^{1/2}`. -/
def DilRegExplicit : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (k : ℕ) (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L Mp : ℝ≥0)
    (xmin : Fin k → EuclideanSpace ℝ (Fin d)) (a1 a2 : ℝ) (bstar : EuclideanSpace ℝ (Fin d)),
    (∀ c, 0 ≤ w c) → ∑ c, w c = 1 → (∀ c, ContDiff ℝ 2 (F c)) →
    (∀ c, ConvexOn ℝ Set.univ (F c)) → (∀ c, LipschitzWith L (F c)) → (∀ c, LipschitzWith Mp (fderiv ℝ (F c))) →
    (∀ c y, F c (xmin c) ≤ F c y) →
    0 < a1 → (∀ x, a1 * ‖x‖ - a2 ≤ mean w F x) →
    (∀ y, mean w F bstar ≤ mean w F y) →
    0 < mean w F bstar - ∑ c, w c * F c (xmin c) →
    ∃ h : ℝ, (mean w F bstar - ∑ c, w c * F c (xmin c)) / 2 ≤ h ∧ h ≤ ⨆ c, (F c bstar - F c (xmin c)) ∧
      (∃ c, h = F c bstar - F c (xmin c)) ∧
      (∃ b S, IsMinInv (mean w F) (h / (16 * d)) b S) ∧
      ∀ b S, IsMinInv (mean w F) (h / (16 * d)) b S →
        mean w F b ≤ ∫ z, mean w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
        (∀ y, ∫ z, mean w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ mean w F y + h / (16 * d) * d) ∧
        h * (mean w F bstar - ∑ c, w c * F c (xmin c)) /
            (2 * KS * (1 + Real.sqrt (2 * lnp (26 * d * L * ‖S‖ / h))) ^ 2 * (d : ℝ) ^ 2 *
              Real.log (2 * (⨆ c, (F c bstar - F c (xmin c))) / (mean w F bstar - ∑ c, w c * F c (xmin c)))) ≤
          var w F bstar + var w F b + ∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

end AdversarialBco.Body2
