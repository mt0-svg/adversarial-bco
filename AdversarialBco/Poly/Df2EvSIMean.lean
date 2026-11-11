/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIProc
public import AdversarialBco.Poly.Df2PlayProof

@[expose] public section

/-!
# The means of the increments are the derivatives of the surrogate

Lemma D.3 at `z = μ` (`lemmaUBPrime_holds`) read under `gam d` on `Fin d → ℝ`: with `X(z) = μ + (1 - λ) A z`,
`P A Aᵀ = 1` and `e` Lipschitz,

* `mean_lin`: `∫ e(X(z)) ⟨P A z, h⟩ dγ(z) = (1 - λ) ⟨s'(μ), h⟩`;
* `mean_quad`: `∫ e(X(z)) (⟨P A z, h⟩² - hᵀ P h) dγ(z) = ((1 - λ)²/λ) hᵀ s''(μ) h`,

with `s = df2Surr e μ A λ`. So `E[⟨ĝ, h⟩ | 𝒢 s] = ⟨s'(μ), h⟩` and `E[hᵀ ŝ'' h | 𝒢 s] = hᵀ s''(μ) h`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix RealInnerProductSpace

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-- The Gaussian of `Fin d → ℝ` carried to `E d`. -/
theorem integral_gam_toLp (F : E d → ℝ) (hF : Continuous F) :
    ∫ u, F u ∂(stdGaussian (E d)) = ∫ z, F (WithLp.toLp 2 z) ∂(gam d) := by
  rw [← map_pi_eq_stdGaussian, integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    hF.aestronglyMeasurable]

theorem clm_mulVec (P : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) P (WithLp.toLp 2 v) = WithLp.toLp 2 (P *ᵥ v) :=
  (df2Carriers_holds d P P v ∅).2.1

theorem pm_comp (A P : Matrix (Fin d) (Fin d) ℝ) (hPA : P * (A * Aᵀ) = 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) P).comp ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).comp
      (ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A))) = ContinuousLinearMap.id ℝ _ := by
  have h1 := (df2Carriers_holds d A A 0 ∅).2.2.2.1
  have h2 := (df2Carriers_holds d A Aᵀ 0 ∅).2.2.1
  have h3 := (df2Carriers_holds d P (A * Aᵀ) 0 ∅).2.2.1
  rw [← h1, ← h2, ← h3, hPA, map_one]
  rfl

theorem growth_of_lip (e : E d → ℝ) (K : ℝ) (he : ∀ x y, |e x - e y| ≤ K * ‖x - y‖) (y : E d) :
    |e y| ≤ (|e 0| + |K|) * (1 + ‖y‖) := by
  have h := he y 0
  rw [sub_zero] at h
  have h1 : |e y| ≤ |e 0| + K * ‖y‖ := by
    have := abs_sub_abs_le_abs_sub (e y) (e 0); linarith
  have h2 : K * ‖y‖ ≤ |K| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
  nlinarith [abs_nonneg (e 0), abs_nonneg K, norm_nonneg y]

theorem continuous_of_lip (e : E d → ℝ) (K : ℝ) (he : ∀ x y, |e x - e y| ≤ K * ‖x - y‖) : Continuous e := by
  have hlip : LipschitzWith (Real.toNNReal |K|) e := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg K)]
    exact (he x y).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
  exact hlip.continuous

/-- The point of the play: `(1 - λ)(μ + A g) + λ μ = X(z)` at `g = toLp z`. -/
theorem play_point (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (z : Fin d → ℝ) :
    (1 - lam) • (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 z)) + lam • WithLp.toLp 2 mu =
      (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ z)) : E d) := by
  rw [clm_mulVec, WithLp.toLp_add, WithLp.toLp_smul]
  module

theorem inner_dir (A P : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (z h : Fin d → ℝ) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 z)),
      (WithLp.toLp 2 h : E d)⟫ = (1 - lam) * ((P *ᵥ (A *ᵥ z)) ⬝ᵥ h) := by
  rw [clm_mulVec, ← WithLp.toLp_smul, clm_mulVec, EuclideanSpace.inner_toLp_toLp, mulVec_smul, star_trivial,
    dotProduct_smul, smul_eq_mul, dotProduct_comm]

theorem inner_P (P : Matrix (Fin d) (Fin d) ℝ) (h : Fin d → ℝ) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P (WithLp.toLp 2 h), (WithLp.toLp 2 h : E d)⟫ = df2Sq P h := by
  rw [clm_mulVec, EuclideanSpace.inner_toLp_toLp, star_trivial]; rfl

/-- Lemma D.3 at `μ`, the gradient, under `gam d`. -/
theorem mean_lin (e : E d → ℝ) (K : ℝ) (he : ∀ x y, |e x - e y| ≤ K * ‖x - y‖) (mu : Fin d → ℝ)
    (A P : Matrix (Fin d) (Fin d) ℝ) (hPA : P * (A * Aᵀ) = 1) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (h : Fin d → ℝ) :
    ∫ z, e (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ z))) * ((P *ᵥ (A *ᵥ z)) ⬝ᵥ h) ∂(gam d) =
      (1 - lam) * (df2GradM (df2Surr e (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A) lam)
        (WithLp.toLp 2 mu) ⬝ᵥ h) := by
  have hc := continuous_of_lip e K he
  have ub := lemmaUBPrime_holds d e (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) P) lam (|e 0| + |K|) hl0 hl1 hc.measurable (growth_of_lip e K he)
    (pm_comp A P hPA)
  rw [(gradM_hessM _ _ h).1, ((ub.2 (WithLp.toLp 2 mu) (WithLp.toLp 2 h) (WithLp.toLp 2 h)).1)]
  have hF : Continuous fun g : E d => ((1 - lam) ^ 2)⁻¹ *
      e ((1 - lam) • (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A g) + lam • WithLp.toLp 2 mu) *
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A g), WithLp.toLp 2 h⟫ := by
    fun_prop
  rw [integral_gam_toLp _ hF, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [play_point, inner_dir]
  have h1 : (1 - lam) ≠ 0 := by linarith
  field_simp

/-- Lemma D.3 at `μ`, the Hessian, under `gam d`. -/
theorem mean_quad (e : E d → ℝ) (K : ℝ) (he : ∀ x y, |e x - e y| ≤ K * ‖x - y‖) (mu : Fin d → ℝ)
    (A P : Matrix (Fin d) (Fin d) ℝ) (hPA : P * (A * Aᵀ) = 1) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (h : Fin d → ℝ) :
    ∫ z, e (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ z))) * (((P *ᵥ (A *ᵥ z)) ⬝ᵥ h) ^ 2 - df2Sq P h) ∂(gam d) =
      (1 - lam) ^ 2 / lam * df2Sq (df2HessM (df2Surr e (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A) lam)
        (WithLp.toLp 2 mu)) h := by
  have hc := continuous_of_lip e K he
  have ub := lemmaUBPrime_holds d e (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) P) lam (|e 0| + |K|) hl0 hl1 hc.measurable (growth_of_lip e K he)
    (pm_comp A P hPA)
  rw [(gradM_hessM _ _ h).2, ((ub.2 (WithLp.toLp 2 mu) (WithLp.toLp 2 h) (WithLp.toLp 2 h)).2)]
  have hF : Continuous fun g : E d => ((1 - lam) ^ 2)⁻¹ *
      e ((1 - lam) • (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A g) + lam • WithLp.toLp 2 mu) *
      (((1 - lam) ^ 2)⁻¹ *
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A g), WithLp.toLp 2 h⟫ *
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A g), WithLp.toLp 2 h⟫ -
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P (WithLp.toLp 2 h), WithLp.toLp 2 h⟫) := by
    fun_prop
  rw [integral_gam_toLp _ hF, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [play_point, inner_dir, inner_P]
  have h1 : (1 - lam) ≠ 0 := by linarith
  field_simp

end AdversarialBco.Poly.EvSI
