/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# The facts of SI and the constant fields at a parameter record

DET reads its parameters through two objects, stated here at any record `p : Df2OPar`:

* `Df2SIAt p Kt g`, the analytic facts of SI on the body `Kt` and the loss `g` at `p`: the body of `Df2SIFacts`
  (Df2Layer2.lean) with `df2oPar d n δ` replaced by `p`.
* `Df2ParFix p`, the nine fields of `p` that DET reads as closed forms (`κ = 1/4`, `θ = 1`, `α = 1/4`, `c₁ = 8`,
  `γ = 1/100`, `κ₀ = (1 - λ)^{-2}`, `s_b = δ²/(R (R + 1))`, `L = 36 log(1/δ)`, `σ² = 1/(8 L)`), which the table of
  Theorem U (`df2oPar d n δ`, `df2ParFix_oPar`) and the table T4U of Theorem UW share.

`DetBase` (Df2DetMain.lean) holds both at the record of its context, so DET holds at either table.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.Poly

variable {d : ℕ}

/-- The analytic facts of SI at the record `p`: the body of `Df2SIFacts` with `df2oPar d n δ` replaced by `p`. -/
def Df2SIAt (p : Df2OPar) (Kt : Set (E d)) (g : E d → ℝ) : Prop :=
  (ConvexOn ℝ Set.univ (df2Ext p Kt g) ∧ (∀ x, 0 ≤ df2Ext p Kt g x) ∧
    (∀ x y, |df2Ext p Kt g x - df2Ext p Kt g y| ≤ 8 / p.eps * ‖x - y‖) ∧
    ∀ y ∈ df2KepsOf Kt p.eps, df2Ext p Kt g (WithLp.toLp 2 y) = g (WithLp.toLp 2 y)) ∧
  ∀ (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ), Df2StateOK p Kt mu A →
    (ContDiff ℝ 2 (df2SurrOf p Kt g mu A) ∧ ConvexOn ℝ Set.univ (df2SurrOf p Kt g mu A) ∧
      ∀ z, df2SurrOf p Kt g mu A z ≤ df2Ext p Kt g z) ∧
    (∀ z ∈ df2KepsOf Kt p.eps, -(10 / (p.lam * p.eps)) ≤ df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ∧
      df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ≤ 1) ∧
    ((∫ z, df2Ext p Kt g (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A z) ∂(stdGaussian (E d))) -
        df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) ≤
      2 / p.lam * (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) * (A * Aᵀ)).trace + 2 * p.δe * d / p.lam) ∧
    (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2) * df2Sq (A * Aᵀ)⁻¹ v) ∧
    (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (d / p.δe) * (v ⬝ᵥ v)) ∧
    (∀ x y : Fin d → ℝ, p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (x - y) ≤ 1 / p.Le →
      ((2 : ℝ) • df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 y) + p.δe • (A * Aᵀ)⁻¹ -
        df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 x)).PosSemidef) ∧
    (∀ y : Fin d → ℝ, p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (y - mu) ≤ 1 / p.Le →
      df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) - df2SurrOf p Kt g mu A (WithLp.toLp 2 y) ≤
        df2GradM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) ⬝ᵥ (mu - y) -
          1 / 4 * df2Sq (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu)) (y - mu) + p.δe / p.lam ^ 2)

/-- The fields of the parameter record that DET reads as closed forms. -/
structure Df2ParFix (p : Df2OPar) : Prop where
  kap : p.kap = 1 / 4
  theta : p.theta = 1
  alpha : p.alpha = 1 / 4
  c1 : p.c1 = 8
  gam : p.gam = 1 / 100
  k0 : p.k0 = ((1 - p.lam) ^ 2)⁻¹
  sb : p.sb = p.δe ^ 2 / (p.R * (p.R + 1))
  Le : p.Le = df2C0 * Real.log (1 / p.δe)
  sig2 : p.sig2 = 1 / (8 * p.Le)

/-- The table of Theorem U has the closed forms. -/
theorem df2ParFix_oPar (d n : ℕ) (δ : ℝ) : Df2ParFix (df2oPar d n δ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AdversarialBco.Poly
