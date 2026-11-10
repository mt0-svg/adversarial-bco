/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Proposition 2.2: the interface between its two halves

`AdversarialBco.body_H` is cut at Theorem 3.1 with (3.2) for a regular family:

* `DilReg`, below, is the statement of that theorem on `ℝ^d`, proved as `AdversarialBco.Body.dilReg : DilReg`
  (Lemmas 3.2 to 3.4, Proposition 3.5 at the cloud and the pigeonhole over the scales);
* the transfer to the inner body (penalised Lipschitz extension, smoothing, the diluted law mapped by the metric
  projection, choice of the penalty and of `ε`) proves `body_H` from `DilReg`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

/-- Theorem 3.1 with (3.2) for a regular family: for a family of convex `C^2` Lipschitz
functions with Lipschitz gradients and a coercive mean, gains `gain c ≤ F c bstar - F c (x c) + η` with mean `G0`,
`bstar` an `η`-minimiser of the mean, there is a scale `h ∈ [G0/2, gmax]` and a cloud `(b, S)` at temperature
`h/(16 d)` with (S3), (S4) and (3.2). -/
def AdversarialBco.Body.DilReg : Prop :=
  ∃ K1 : ℝ, 0 < K1 ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (k : ℕ) (w : Fin k → ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (Lp Mp : ℝ≥0) (a a' : ℝ) (bstar : EuclideanSpace ℝ (Fin d))
    (x : Fin k → EuclideanSpace ℝ (Fin d)) (gain : Fin k → ℝ) (η G0 gmax : ℝ),
    (∀ c, 0 ≤ w c) → ∑ c, w c = 1 → (∀ c, ContDiff ℝ 2 (F c)) → (∀ c, ConvexOn ℝ Set.univ (F c)) →
    (∀ c, LipschitzWith Lp (F c)) → (∀ c, LipschitzWith Mp (fderiv ℝ (F c))) → 0 < a →
    (∀ z, a * ‖z‖ - a' ≤ ∑ c, w c * F c z) →
    (∀ z, ∑ c, w c * F c bstar ≤ ∑ c, w c * F c z + η) →
    (∀ c, 0 ≤ gain c) → (∀ c, gain c ≤ F c bstar - F c (x c) + η) → G0 = ∑ c, w c * gain c → 0 < G0 →
    (∀ c, gain c ≤ gmax) → 0 ≤ η → η ≤ G0 / 64 →
    ∃ (h : ℝ) (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      G0 / 2 ≤ h ∧ h ≤ gmax ∧
      (∀ z, ∫ g, ∑ c, w c * F c (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∑ c, w c * F c z + h / 16) ∧
      ∑ c, w c * F c b ≤ ∫ g, ∑ c, w c * F c (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      h * G0 ≤ K1 * (1 + AdversarialBco.Body.Tfun (Lp * ‖S‖ * 16 * (d : ℝ) / h)) ^ 2 * (d : ℝ) ^ 2 *
        Real.log (2 * gmax / G0) *
          (∑ c, w c * (F c bstar - ∑ c', w c' * F c' bstar) ^ 2 +
            ∑ c, w c * (F c b - ∑ c', w c' * F c' b) ^ 2 +
            ∫ g, ∑ c, w c * (F c (b + S g) - ∑ c', w c' * F c' (b + S g)) ^ 2
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
