/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Gaussian concentration for Lipschitz functions, both tails

Gaussian concentration (the source's thm:orlicz-lip; Boucheron, Lugosi and Massart, Theorem 5.6;
Tsirelson, Ibragimov and Sudakov), proved here: for `X ~ N(b, Σ)` on `ℝ^d` and `F` `L`-Lipschitz,
`P(|F(X) - E F(X)| ≥ t) ≤ 2 exp(-t^2/(2 L^2 ‖Σ‖))`. Its two uses are lem:ons:mink (the event Pi, `F` the gauge,
`L = 1`) and the variance of the play (`F = v`, `L = 2`), both two-sided at the constant `1/2`.

* `GaussConcLip c`: the Gaussian is the law of `b + S g`, `g` standard Gaussian on `ℝ^k` (Mathlib's `stdGaussian` on
  `EuclideanSpace ℝ (Fin k)`) and `S : ℝ^k →L ℝ^d` any linear map, so `Σ = S Sᵀ` and `‖Σ‖ = ‖S‖^2`. An `L`-Lipschitz
  `F` is integrable, its upper tail about the mean is at most `exp(-c t^2/(L ‖S‖)^2)` and its two-sided tail at most
  `2 exp(-c t^2/(L ‖S‖)^2)`, for every `t ≥ 0`. The covariance enters only through the linear map: `F ∘ (b + S ·)`
  is `L ‖S‖`-Lipschitz on `ℝ^k`, so the statement on the standard Gaussian carries all of it.
* `GaussConcMatrix c`: the same two-sided bound under Mathlib's `multivariateGaussian m A` for a positive
  semidefinite matrix `A`, with `‖A‖` the operator norm of `A` on `ℝ^d` (`Matrix.toEuclideanCLM`): the source's form,
  `N(m, A)` and `‖Σ‖`, word for word.
* `GaussConcSharp`: both at the source's constant `c = 1/2`.

Junk values. If `L ‖S‖ = 0` (or `L^2 ‖A‖ = 0`) the exponent is `-(c t^2)/0 = 0` and the bounds read `≤ 1` and
`≤ 2`, which are true; the statement is then weaker than the truth, never false. The mean `∫ F` is not a junk value,
`F` being integrable (first conjunct). For `A` not positive semidefinite `multivariateGaussian m A` is not `N(m, A)`;
`GaussConcMatrix` asks `A.PosSemidef`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

/-- Gaussian concentration for Lipschitz functions with the constant `c` in the exponent, under the law
`N(b, S Sᵀ)` of `b + S g`, `g` standard Gaussian on `ℝ^k`: an `L`-Lipschitz `F` is integrable,
`P(F - E F ≥ t) ≤ exp(-c t^2/(L ‖S‖)^2)` and `P(|F - E F| ≥ t) ≤ 2 exp(-c t^2/(L ‖S‖)^2)` for `t ≥ 0`. -/
def GaussConcLip (c : ℝ) : Prop :=
  ∀ (k d : ℕ) (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : NNReal), LipschitzWith L F →
      Integrable F ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g) ∧
        ∀ t : ℝ, 0 ≤ t →
          ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g).real
              {x | t ≤ F x - ∫ y, F y ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g)} ≤
            Real.exp (-(c * t ^ 2) / ((L : ℝ) * ‖S‖) ^ 2) ∧
          ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g).real
              {x | t ≤ |F x - ∫ y, F y ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g)|} ≤
            2 * Real.exp (-(c * t ^ 2) / ((L : ℝ) * ‖S‖) ^ 2)

/-- Gaussian concentration for Lipschitz functions with the constant `c` in the exponent, under Mathlib's
`multivariateGaussian m A` for `A` positive semidefinite: `P(|F - E F| ≥ t) ≤ 2 exp(-c t^2/(L^2 ‖A‖))` for `t ≥ 0`,
`‖A‖` the operator norm of `A` on `ℝ^d`. -/
def GaussConcMatrix (c : ℝ) : Prop :=
  ∀ (d : ℕ) (m : EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ), A.PosSemidef →
    ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : NNReal), LipschitzWith L F →
      Integrable F (multivariateGaussian m A) ∧
        ∀ t : ℝ, 0 ≤ t →
          (multivariateGaussian m A).real {x | t ≤ |F x - ∫ y, F y ∂multivariateGaussian m A|} ≤
            2 * Real.exp (-(c * t ^ 2) / ((L : ℝ) ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖))

/-- The source's thm:orlicz-lip: both forms at the constant `1/2`. -/
def GaussConcSharp : Prop :=
  GaussConcLip (1 / 2) ∧ GaussConcMatrix (1 / 2)

end AdversarialBco.Poly
