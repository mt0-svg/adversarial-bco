/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SIFactsTools

@[expose] public section

/-!
# The surrogate of a convex Lipschitz function: generic facts

For `e` convex and `K`-Lipschitz on `E = EuclideanSpace ℝ (Fin d)`, `A` invertible (inverse `S`) and `0 < λ < 1`, the
surrogate `s = df2Surr e μ A λ` of `Df2.lean`:

* `surr_contDiff`, `surr_convex`, `surr_le`, `surr_lip`, `surr_lower` (lem:basic and 8.6);
* `surr_hess_bound`: `|s''(z)(w, v)| ≤ (λ K/(1 - λ)) ‖w‖ ‖S v‖` (prop:opt:H-upper), by the Stein form
  of `LemmaUBPrime` and `stein_hess_bound`;
* `surr_mean`: `E s(μ + ρ A g') = E e(μ + A g)` when `(1 - λ)² + λ² ρ² = 1` (prop:lower);
* `surr_sc`: prop:s-sc in the split form,
  `s''(x)(v, v) ≤ 2 s''(y)(v, v) + λ K ‖v‖ ‖S v‖/((1 - λ) r) P(log 2 - ‖c‖²/2 < ⟪c, g⟫)` with `r = (1/2)^{1/2}` and
  `c = (λ/((1 - λ) r)) S (x - y)`, through the smoothed extension `smoothExt e C w = E e(w + C g)`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace AdversarialBco.Poly.SIF

variable {d : ℕ}

/-! ## Integrability -/

theorem lip_abs_le (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (y : EuclideanSpace ℝ (Fin d)) : |e y| ≤ |e 0| + K * ‖y‖ := by
  have h := he.dist_le_mul y 0
  rw [Real.dist_eq, dist_zero_right] at h
  have := abs_sub_abs_le_abs_sub (e y) (e 0)
  linarith

theorem integrable_comp_affine (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (w : EuclideanSpace ℝ (Fin d)) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => e (w + T g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hn : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 1) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    Df2Play.integrable_norm_pow_stdGaussian d 1
  refine Integrable.mono' ((integrable_const (|e 0| + K * ‖w‖)).add (hn.const_mul (K * ‖T‖))) ?_ ?_
  · exact (he.continuous.comp (continuous_const.add T.continuous)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_one]
    have h1 := lip_abs_le e K he (w + T g)
    have h2 : ‖w + T g‖ ≤ ‖w‖ + ‖T‖ * ‖g‖ := (norm_add_le _ _).trans (by gcongr; exact T.le_opNorm g)
    have hK : (0 : ℝ) ≤ K := K.2
    nlinarith

theorem integrable_norm_clm (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => ‖T g‖) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hn : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 1) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    Df2Play.integrable_norm_pow_stdGaussian d 1
  refine Integrable.mono' (hn.const_mul ‖T‖) (T.continuous.norm.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun g => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), pow_one]
  exact T.le_opNorm g

/-! ## The surrogate: smoothness, convexity, comparison with `e` -/

/-- The `X_z` of the surrogate is affine in `g`: `(1 - λ)(μ + A g) + λ z = ((1 - λ) μ + λ z) + ((1 - λ) A) g`. -/
theorem surr_point (μ z g : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (lam : ℝ) : (1 - lam) • (μ + A g) + lam • z = ((1 - lam) • μ + lam • z) + ((1 - lam) • A) g := by
  simp only [smul_apply, smul_add]
  abel

/-- `Pm = S† S` inverts `A A†` when `S` inverts `A`. -/
theorem pm_of_inv (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hAS : ∀ x, A (S x) = x)
    (hSA : ∀ x, S (A x) = x) :
    ((ContinuousLinearMap.adjoint S).comp S).comp (A.comp (ContinuousLinearMap.adjoint A)) =
      ContinuousLinearMap.id ℝ _ := by
  ext1 x
  refine ext_inner_right ℝ fun y => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.adjoint_inner_left, hSA]
  rw [hAS]

theorem lip_growth (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (y : EuclideanSpace ℝ (Fin d)) : |e y| ≤ (|e 0| + K) * (1 + ‖y‖) := by
  have h := lip_abs_le e K he y
  have hK : (0 : ℝ) ≤ K := K.2
  nlinarith [abs_nonneg (e 0), norm_nonneg y]

theorem surr_contDiff (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : EuclideanSpace ℝ (Fin d)) (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hAS : ∀ x, A (S x) = x) (hSA : ∀ x, S (A x) = x) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    ContDiff ℝ 2 (df2Surr e μ A lam) :=
  (lemmaUBPrime_holds d e μ A _ lam _ h0 h1 he.continuous.measurable (lip_growth e K he)
    (pm_of_inv A S hAS hSA)).1

/-- The Hessian of the surrogate in Stein form: with `T = (1 - λ) A`, `S_T = (1 - λ)⁻¹ S` and
`w₀ = (1 - λ) μ + λ z`, `s''(z)(w, v) = λ E[e(w₀ + T g)(⟪g, S_T v⟫ ⟪g, S_T w⟫ - ⟪S_T v, S_T w⟫)]`. -/
theorem surr_hess_eq (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : EuclideanSpace ℝ (Fin d)) (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hAS : ∀ x, A (S x) = x) (hSA : ∀ x, S (A x) = x) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (z w v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) z w v =
      lam * ∫ g, e (((1 - lam) • μ + lam • z) + ((1 - lam) • A) g) *
        (⟪g, (1 - lam)⁻¹ • S v⟫ * ⟪g, (1 - lam)⁻¹ • S w⟫ - ⟪(1 - lam)⁻¹ • S v, (1 - lam)⁻¹ • S w⟫)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h := ((lemmaUBPrime_holds d e μ A _ lam _ h0 h1 he.continuous.measurable (lip_growth e K he)
    (pm_of_inv A S hAS hSA)).2 z v w).2
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have h1l : (1 - lam) ≠ 0 := by linarith
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, map_smul, hSA,
    real_inner_smul_left, real_inner_smul_right, ← surr_point]
  rw [real_inner_comm (S v) g, real_inner_comm (S w) g]
  field_simp

theorem surr_hess_bound (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hAS : ∀ x, A (S x) = x)
    (hSA : ∀ x, S (A x) = x) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (z w v : EuclideanSpace ℝ (Fin d)) :
    |fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) z w v| ≤ lam * K / (1 - lam) * (‖w‖ * ‖S v‖) := by
  have h1l : 0 < 1 - lam := by linarith
  rw [surr_hess_eq e K he μ A S hAS hSA lam h0 h1 z w v]
  have hTS : ∀ x, ((1 - lam) • A) (((1 - lam)⁻¹ • S) x) = x := fun x => by
    simp only [smul_apply, map_smul, hAS, smul_smul, inv_mul_cancel₀ h1l.ne', one_smul]
  have hb := stein_hess_bound e K he hc ((1 - lam) • μ + lam • z) ((1 - lam) • A) ((1 - lam)⁻¹ • S) hTS v w
  rw [abs_mul, abs_of_pos h0]
  calc lam * |∫ g, _ ∂_| ≤ lam * (K * ‖w‖ * ‖(1 - lam)⁻¹ • S v‖) := mul_le_mul_of_nonneg_left hb h0.le
    _ = lam * K / (1 - lam) * (‖w‖ * ‖S v‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h1l]
      field_simp

theorem integrable_surr_term (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ z : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Integrable (fun g => e ((1 - lam) • (μ + A g) + lam • z)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  simp only [surr_point]
  exact integrable_comp_affine e K he _ _

theorem surr_convex (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ) (h0 : 0 < lam) :
    ConvexOn ℝ Set.univ (df2Surr e μ A lam) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun g => (1 - lam) • (μ + A g) with hP
  have hpt : ∀ g, e (P g + lam • (a • x + b • y)) ≤ a * e (P g + lam • x) + b * e (P g + lam • y) := by
    intro g
    have hid : a • (P g + lam • x) + b • (P g + lam • y) = P g + lam • (a • x + b • y) := by
      have : a • (P g + lam • x) + b • (P g + lam • y) = (a + b) • P g + lam • (a • x + b • y) := by module
      rw [this, hab, one_smul]
    have := hc.2 (Set.mem_univ (P g + lam • x)) (Set.mem_univ (P g + lam • y)) ha hb hab
    rw [hid, smul_eq_mul, smul_eq_mul] at this
    exact this
  have hIx := integrable_surr_term e K he μ x A lam
  have hIy := integrable_surr_term e K he μ y A lam
  have hIxy := integrable_surr_term e K he μ (a • x + b • y) A lam
  have hJ : ∫ g, e (P g + lam • (a • x + b • y)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      a * ∫ g, e (P g + lam • x) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        b * ∫ g, e (P g + lam • y) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIx.const_mul a) (hIy.const_mul b)]
    exact integral_mono hIxy ((hIx.const_mul a).add (hIy.const_mul b)) hpt
  simp only [df2Surr, smul_eq_mul]
  have hl : 0 < 1 / lam := by positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left hJ hl.le]

theorem surr_le (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (z : EuclideanSpace ℝ (Fin d)) : df2Surr e μ A lam z ≤ e z := by
  have h1l : 0 < 1 - lam := by linarith
  have hI1 : Integrable (fun g => e (μ + A g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_comp_affine e K he μ A
  have hI2 := integrable_surr_term e K he μ z A lam
  have hpt : ∀ g, e ((1 - lam) • (μ + A g) + lam • z) ≤ (1 - lam) * e (μ + A g) + lam * e z := fun g => by
    have := hc.2 (Set.mem_univ (μ + A g)) (Set.mem_univ z) h1l.le h0.le (by ring)
    simpa only [smul_eq_mul] using this
  have hJ : ∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      (1 - lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + lam * e z := by
    calc _ ≤ ∫ g, ((1 - lam) * e (μ + A g) + lam * e z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          integral_mono hI2 ((hI1.const_mul _).add (integrable_const _)) hpt
      _ = _ := by
          rw [integral_add (hI1.const_mul _) (integrable_const _), integral_const_mul, integral_const]
          simp
  simp only [df2Surr]
  have hl : 0 < 1 / lam := by positivity
  have := mul_le_mul_of_nonneg_left hJ hl.le
  have hk : 1 / lam * ((1 - lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + lam * e z) =
      (1 / lam - 1) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + e z := by
    field_simp
  linarith

theorem surr_lip (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h0 : 0 < lam) (z z' : EuclideanSpace ℝ (Fin d)) :
    |df2Surr e μ A lam z - df2Surr e μ A lam z'| ≤ K * ‖z - z'‖ := by
  have hIz := integrable_surr_term e K he μ z A lam
  have hIz' := integrable_surr_term e K he μ z' A lam
  have hpt : ∀ g, ‖e ((1 - lam) • (μ + A g) + lam • z) - e ((1 - lam) • (μ + A g) + lam • z')‖ ≤
      K * (lam * ‖z - z'‖) := fun g => by
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    refine (he.dist_le_mul _ _).trans (le_of_eq ?_)
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h0]
  have hb := norm_integral_le_of_norm_le_const (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (Filter.Eventually.of_forall hpt)
  rw [integral_sub hIz hIz'] at hb
  rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at hb
  simp only [df2Surr]
  have hK : (0 : ℝ) ≤ K := K.2
  rw [show ∀ a b c : ℝ, a + 1 / lam * b - (a + 1 / lam * c) = 1 / lam * (b - c) from fun a b c => by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / lam)]
  calc 1 / lam * |_| ≤ 1 / lam * (K * (lam * ‖z - z'‖)) := by gcongr
    _ = K * ‖z - z'‖ := by field_simp

theorem surr_lower (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e) (he0 : ∀ x, 0 ≤ e x)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h0 : 0 < lam) (z : EuclideanSpace ℝ (Fin d)) :
    -(K * (‖z - μ‖ + ∫ g, ‖A g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) ≤ df2Surr e μ A lam z := by
  have hI1 : Integrable (fun g => e (μ + A g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_comp_affine e K he μ A
  have hI2 := integrable_surr_term e K he μ z A lam
  have hIA := integrable_norm_clm A
  have hK : (0 : ℝ) ≤ K := K.2
  have hpt : ∀ g, e (μ + A g) - K * lam * (‖z - μ‖ + ‖A g‖) ≤ e ((1 - lam) • (μ + A g) + lam • z) := fun g => by
    have h := he.dist_le_mul ((1 - lam) • (μ + A g) + lam • z) (μ + A g)
    rw [Real.dist_eq, dist_eq_norm] at h
    have hv : (1 - lam) • (μ + A g) + lam • z - (μ + A g) = lam • ((z - μ) - A g) := by module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos h0] at h
    have h3 : ‖(z - μ) - A g‖ ≤ ‖z - μ‖ + ‖A g‖ := norm_sub_le _ _
    have h4 := neg_abs_le (e ((1 - lam) • (μ + A g) + lam • z) - e (μ + A g))
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hK h0.le)]
  have hJ : ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
      K * lam * (‖z - μ‖ + ∫ g, ‖A g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
      ∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h2 : Integrable (fun g => K * lam * (‖z - μ‖ + ‖A g‖)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ((integrable_const _).add hIA).const_mul _
    have hint : Integrable (fun g => e (μ + A g) - K * lam * (‖z - μ‖ + ‖A g‖))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := hI1.sub h2
    calc _ = ∫ g, (e (μ + A g) - K * lam * (‖z - μ‖ + ‖A g‖)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          rw [integral_sub hI1 h2, integral_const_mul, integral_add (integrable_const _) hIA, integral_const]
          simp
      _ ≤ _ := integral_mono hint hI2 hpt
  have hE : 0 ≤ ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integral_nonneg fun g => he0 _
  simp only [df2Surr]
  have hl : 0 < 1 / lam := by positivity
  have := mul_le_mul_of_nonneg_left hJ hl.le
  have hk : 1 / lam * (∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
      K * lam * (‖z - μ‖ + ∫ g, ‖A g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) =
      1 / lam * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        K * (‖z - μ‖ + ∫ g, ‖A g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    field_simp
  nlinarith

/-! ## The mean over a wider Gaussian (prop:lower) -/

theorem surr_lipschitzWith (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h0 : 0 < lam) : LipschitzWith K (df2Surr e μ A lam) :=
  LipschitzWith.of_dist_le_mul fun z z' => by
    rw [Real.dist_eq, dist_eq_norm]; exact surr_lip e K he μ A lam h0 z z'

/-- The growth of `u ↦ e(w + T u)`. -/
theorem lip_affine_growth (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (w : EuclideanSpace ℝ (Fin d)) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) : |e (w + T u)| ≤ (|e 0| + K * ‖w‖) + K * ‖T‖ * ‖u‖ := by
  have h1 := lip_abs_le e K he (w + T u)
  have h2 : ‖w + T u‖ ≤ ‖w‖ + ‖T‖ * ‖u‖ := (norm_add_le _ _).trans (by gcongr; exact T.le_opNorm u)
  have hK : (0 : ℝ) ≤ K := K.2
  nlinarith

theorem surr_mean (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam ρ : ℝ)
    (h0 : 0 < lam) (h1 : lam < 1) (hρ : 0 ≤ ρ) (hρ1 : (1 - lam) ^ 2 + lam ^ 2 * ρ ^ 2 = 1) :
    ∫ g', df2Surr e μ A lam (μ + ρ • A g') ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h1l : 0 < 1 - lam := by linarith
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun u => e (μ + A u) with hF
  have hFc : Continuous F := he.continuous.comp (continuous_const.add A.continuous)
  have hsplit := integral_integral_split F hFc _ _ (lip_affine_growth e K he μ A) (lam * ρ) (1 - lam)
    (by positivity) h1l.le (by nlinarith)
  set J : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun g' => ∫ g, e ((1 - lam) • (μ + A g) + lam • (μ + ρ • A g')) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    with hJ
  have hJF : ∀ g', J g' = ∫ g, F ((lam * ρ) • g' + (1 - lam) • g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro g'
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hF, map_add, map_smul]
    congr 1
    module
  set c1 := (1 - 1 / lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) with hc1
  have hs : ∀ g', df2Surr e μ A lam (μ + ρ • A g') = c1 + 1 / lam * J g' := fun g' => rfl
  have hint : Integrable (fun g' => df2Surr e μ A lam (μ + (ρ • A) g')) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_comp_affine _ K (surr_lipschitzWith e K he μ A lam h0) μ (ρ • A)
  have hJint : Integrable J (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine (hint.sub (integrable_const c1)).const_mul lam |>.congr (Filter.Eventually.of_forall fun g' => ?_)
    simp only [Pi.sub_apply, smul_apply]
    rw [hs, add_sub_cancel_left, ← mul_assoc, mul_one_div_cancel h0.ne', one_mul]
  simp only [hs]
  rw [integral_add (integrable_const _) (hJint.const_mul _), integral_const, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [show ∫ g', J g' ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) by
    simp only [hJF]; exact hsplit]
  rw [hc1]
  ring

/-! ## The smoothed extension and prop:s-sc -/

/-- `e_C(w) = E e(w + C g)`. -/
noncomputable def smoothExt (e : EuclideanSpace ℝ (Fin d) → ℝ)
    (C : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ g, e (w + C g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

theorem smoothExt_convex (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (C : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (smoothExt e C) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hpt : ∀ g, e ((a • x + b • y) + C g) ≤ a * e (x + C g) + b * e (y + C g) := by
    intro g
    have hid : a • (x + C g) + b • (y + C g) = (a • x + b • y) + C g := by
      have : a • (x + C g) + b • (y + C g) = (a • x + b • y) + (a + b) • C g := by module
      rw [this, hab, one_smul]
    have := hc.2 (Set.mem_univ (x + C g)) (Set.mem_univ (y + C g)) ha hb hab
    rwa [hid, smul_eq_mul, smul_eq_mul] at this
  have hIx := integrable_comp_affine e K he x C
  have hIy := integrable_comp_affine e K he y C
  simp only [smoothExt, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIx.const_mul a) (hIy.const_mul b)]
  exact integral_mono (integrable_comp_affine e K he _ C) ((hIx.const_mul a).add (hIy.const_mul b)) hpt

set_option synthInstance.maxHeartbeats 400000 in
theorem smoothExt_c2 (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (C SC : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hCS : ∀ x, C (SC x) = x) :
    ContDiff ℝ 2 (smoothExt e C) ∧ ∀ z w v : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fderiv ℝ (smoothExt e C)) z w v =
        ∫ g, e (z + C g) * (⟪g, SC w⟫ * ⟪g, SC v⟫ - ⟪SC w, SC v⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun y => e (C y) with hf
  have hfm : Measurable f := (he.continuous.comp C.continuous).measurable
  have hfB : ∀ y, |f y| ≤ (|e 0| + K * ‖C‖) * (1 + ‖y‖) := by
    intro y
    have h := lip_affine_growth e K he 0 C y
    simp only [zero_add, norm_zero, mul_zero, add_zero] at h
    have hK : (0 : ℝ) ≤ K := K.2
    have : (0 : ℝ) ≤ K * ‖C‖ := by positivity
    simp only [hf]
    nlinarith [abs_nonneg (e 0), norm_nonneg y]
  obtain ⟨hHc, hHd⟩ := Df2Play.gaussConv_c2 f hfm _ hfB
  set H : EuclideanSpace ℝ (Fin d) → ℝ := fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    with hH
  have hfC : ∀ z g, f (SC z + g) = e (z + C g) := fun z g => by simp only [hf, map_add, hCS]
  have heq : smoothExt e C = fun z => 0 + 1 * H (0 + SC z) := by
    funext z
    simp only [smoothExt, hH, zero_add, one_mul, hfC]
  obtain ⟨hc2, hder⟩ := Df2Play.affine_c2 H hHc SC 0 0 1
  rw [heq]
  refine ⟨hc2, fun z w v => ?_⟩
  rw [(hder z v w).2, (hHd _ _ _).2, one_mul]
  simp only [zero_add, hfC]

theorem smoothExt_hess_bound (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (C SC : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hCS : ∀ x, C (SC x) = x) (z w v : EuclideanSpace ℝ (Fin d)) :
    |fderiv ℝ (fderiv ℝ (smoothExt e C)) z w v| ≤ K * ‖v‖ * ‖SC w‖ := by
  rw [(smoothExt_c2 e K he C SC hCS).2]
  exact stein_hess_bound e K he hc z C SC hCS w v

theorem smoothExt_hess_norm (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (C SC : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hCS : ∀ x, C (SC x) = x) (z : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ (smoothExt e C)) z‖ ≤ K * ‖SC‖ := by
  have hK : (0 : ℝ) ≤ K := K.2
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs]
  calc _ ≤ K * ‖v‖ * ‖SC w‖ := smoothExt_hess_bound e K he hc C SC hCS z w v
    _ ≤ K * ‖v‖ * (‖SC‖ * ‖w‖) := by gcongr; exact SC.le_opNorm w
    _ = K * ‖SC‖ * ‖w‖ * ‖v‖ := by ring

theorem smoothExt_hess_nonneg (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (C SC : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hCS : ∀ x, C (SC x) = x) (z v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ fderiv ℝ (fderiv ℝ (smoothExt e C)) z v v := by
  have hpsd := Layer2.hess_psd (smoothExt e C) (smoothExt_c2 e K he C SC hCS).1
    (smoothExt_convex e K he hc C) z
  have h := (Layer2.gradM_hessM (smoothExt e C) z (WithLp.ofLp v)).2
  rw [WithLp.toLp_ofLp] at h
  rw [← h]
  exact Layer2.sq_nonneg_of_psd hpsd _

set_option synthInstance.maxHeartbeats 400000 in
theorem surr_sc (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hAS : ∀ x, A (S x) = x)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (x y v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) x v v ≤
      2 * fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) y v v +
        lam * K * (‖v‖ * ‖S v‖) / ((1 - lam) * Real.sqrt (1 / 2)) *
          (stdGaussian (EuclideanSpace ℝ (Fin d))).real
            {g | Real.log 2 - ‖(lam / ((1 - lam) * Real.sqrt (1 / 2))) • S (x - y)‖ ^ 2 / 2 <
              ⟪(lam / ((1 - lam) * Real.sqrt (1 / 2))) • S (x - y), g⟫} := by
  have h1l : 0 < 1 - lam := by linarith
  set r : ℝ := Real.sqrt (1 / 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hq : 0 < (1 - lam) * r := mul_pos h1l hr0
  set C : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := ((1 - lam) * r) • A with hC
  set SC : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := ((1 - lam) * r)⁻¹ • S with hSC
  have hCS : ∀ x, C (SC x) = x := fun x => by
    simp only [hC, hSC, smul_apply, map_smul, hAS, smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
  set eθ := smoothExt e C with heθ
  obtain ⟨hθc2, hθd⟩ := smoothExt_c2 e K he C SC hCS
  have hθn := smoothExt_hess_norm e K he hc C SC hCS
  -- the surrogate of `e` and that of `eθ` differ by a constant
  have hsplit : ∀ z, ∫ g, eθ ((1 - lam) • (μ + (r • A) g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro z
    set F : EuclideanSpace ℝ (Fin d) → ℝ := fun u => e (((1 - lam) • μ + lam • z) + ((1 - lam) • A) u) with hF
    have hFc : Continuous F := he.continuous.comp (continuous_const.add ((1 - lam) • A).continuous)
    have h := integral_integral_split F hFc _ _ (lip_affine_growth e K he _ _) r r hr0.le hr0.le (by rw [hr2]; norm_num)
    simp only [surr_point]
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g₁ => ?_)
    simp only [heθ, smoothExt, hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g₂ => ?_)
    simp only [hC, smul_apply, map_add, map_smul]
    congr 1
    module
  set c0 := (1 - 1 / lam) * (∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
    ∫ g, eθ (μ + (r • A) g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) with hc0
  have hfun : df2Surr e μ A lam = fun z => df2Surr eθ μ (r • A) lam z + c0 := by
    funext z
    simp only [df2Surr, hc0, hsplit]
    ring
  have hd2 : fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) = fderiv ℝ (fderiv ℝ (df2Surr eθ μ (r • A) lam)) := by
    have : fderiv ℝ (df2Surr e μ A lam) = fderiv ℝ (df2Surr eθ μ (r • A) lam) := by
      rw [hfun]; funext z; exact fderiv_add_const c0
    rw [this]
  obtain ⟨-, hPH⟩ := playHess_holds d eθ μ (r • A) lam (K * ‖SC‖) h0 h1 hθc2 hθn
  -- the Hessian as a Gaussian average of `H`
  set c : EuclideanSpace ℝ (Fin d) := (lam / ((1 - lam) * r)) • S (x - y) with hcdef
  set H : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun g => fderiv ℝ (fderiv ℝ eθ) ((1 - lam) • (μ + (r • A) g) + lam • y) v v with hH
  have hshift : ∀ g, (1 - lam) • (μ + (r • A) (c + g)) + lam • y = (1 - lam) • (μ + (r • A) g) + lam • x := by
    intro g
    have hAc : (1 - lam) • (r • A) c = lam • (x - y) := by
      simp only [hcdef, smul_apply, map_smul, hAS, smul_smul]
      congr 1
      field_simp
    rw [map_add, smul_add, smul_add, hAc]
    module
  have hx : fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) x v v =
      lam * ∫ g, H (c + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hd2, hPH x v v]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hH, hshift]
  have hy : fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) y v v =
      lam * ∫ g, H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hd2, hPH y v v]
  -- the bounds on `H`
  have hc2e : Continuous (fderiv ℝ (fderiv ℝ eθ)) :=
    (hθc2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hHc : Continuous H := by
    simp only [hH]
    exact ((hc2e.comp (by fun_prop)).clm_apply continuous_const).clm_apply continuous_const
  have hH0 : ∀ g, 0 ≤ H g := fun g => smoothExt_hess_nonneg e K he hc C SC hCS _ v
  have hH1 : ∀ g, H g ≤ K * ‖v‖ * ‖SC v‖ := fun g =>
    (le_abs_self _).trans (smoothExt_hess_bound e K he hc C SC hCS _ v v)
  have hsh := integral_shift_le H hHc.measurable _ hH0 hH1 c
  have hSCv : ‖SC v‖ = ‖S v‖ / ((1 - lam) * r) := by
    rw [hSC, smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hq]
    field_simp
  rw [hx, hy]
  calc lam * ∫ g, H (c + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      lam * (2 * ∫ g, H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        K * ‖v‖ * ‖SC v‖ * (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {g | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫}) := mul_le_mul_of_nonneg_left hsh h0.le
    _ = _ := by rw [hSCv]; ring

end AdversarialBco.Poly.SIF
