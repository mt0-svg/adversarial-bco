/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib

@[expose] public section

/-!
# Gaussian concentration for continuously differentiable functions (port)

The argument of Maurey and Pisier: for a `C^1` function `G` with `‖∇G‖ ≤ L` and a standard Gaussian vector `Z`,
`G(Z) - E G(Z)` is sub-Gaussian with variance proxy `π^2 L^2 / 4`. Used in Section 9.2 of the paper through
`AdversarialBco/Gauss/Concentration.lean`.

Ported to Lean v4.34.1 and Mathlib v4.34.1, with names moved into `AdversarialBco.Gauss` and no proof changed, from:
* github.com/RemyDegenne/Maiti2026Power at commit b9431dd9b3811779479d1ea108e51268eb7b24ce, Copyright (c) 2026
  Rémy Degenne, released under the Apache License 2.0: `Maiti2026Power/ForLMLExplore/Probability/MaureyPisier.lean`,
  `.../Probability/GaussianMGF.lean`, `.../Analysis/Calculus/QuarterCircle.lean`, `.../Analysis/Calculus/Gradient.lean`;
* github.com/TauCetiProject/TauCeti at commit e0610cce4004d628cbd9d2aafdbbb5459fe72938, Copyright (c) 2026 The Tau
  Ceti contributors, released under the Apache License 2.0: `ContDiff.gradient_right`
  (`TauCeti/Analysis/Calculus/Gradient.lean`, here `contDiff_gradient_right`) and `IsGaussian.mgf_dual`
  (`TauCeti/Probability/Distributions/Gaussian/Transforms.lean`, here `mgf_dual`).
Renamings: `ContDiff.continuous_gradient` is `continuous_gradient_of_contDiff`, and the `IsGaussian.` prefixes of
the exponential moment lemmas are dropped.
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace AdversarialBco.Gauss

section port

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped RealInnerProductSpace NNReal

/-! ### From TauCeti `Analysis/Calculus/Gradient.lean` and `Probability/Distributions/Gaussian/Transforms.lean` -/

theorem contDiff_gradient_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {m n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)

theorem mgf_dual {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] {μ : Measure E} [IsGaussian μ]
    (L : StrongDual ℝ E) (t : ℝ) (hL : AEMeasurable L μ := by fun_prop) :
    mgf L μ t = Real.exp (t * μ[L] + t ^ 2 / 2 * Var[L; μ]) := by
  rw [← mgf_id_map hL, IsGaussian.map_eq_gaussianReal L, mgf_id_gaussianReal]
  rw [Real.coe_toNNReal _ (variance_nonneg _ _)]
  ring_nf

section grad
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {L : ℝ≥0}

/-- A differentiable function with `‖∇f‖ ≤ L` is `L`-Lipschitz. -/
lemma lipschitzWith_of_norm_gradient_le (hf : Differentiable ℝ f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) : LipschitzWith L f := by
  refine lipschitzWith_of_nnnorm_fderiv_le hf fun x ↦ ?_
  rw [← toDual_gradient, LinearIsometryEquiv.nnnorm_map]
  exact_mod_cast hL x

/-- A differentiable function with `‖∇f‖ ≤ L` has linear growth. -/
lemma abs_le_of_norm_gradient_le (hf : Differentiable ℝ f) (hL : ∀ x, ‖gradient f x‖ ≤ L)
    (x : E) : |f x| ≤ |f 0| + L * ‖x‖ := by
  have h := (lipschitzWith_of_norm_gradient_le hf hL).dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  calc |f x| = |f x - f 0 + f 0| := by ring_nf
    _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
    _ ≤ L * ‖x‖ + |f 0| := by linarith
    _ = |f 0| + L * ‖x‖ := by ring

lemma abs_inner_gradient_le (hL : ∀ x, ‖gradient f x‖ ≤ L) (x v : E) :
    |⟪gradient f x, v⟫| ≤ L * ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _))

/-- The gradient of a `C¹` function is continuous. -/
lemma continuous_gradient_of_contDiff (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (contDiff_gradient_right (m := 0) hf (by simp)).continuous

end grad
section gm
section isGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]

/-- **Exponential moments of Gaussian norms**: `exp (c ‖x‖)` is integrable for every Gaussian
measure (Fernique's theorem). -/
lemma integrable_exp_mul_norm (c : ℝ) : Integrable (fun x ↦ exp (c * ‖x‖)) μ := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq μ
  refine (hint.const_mul (exp (c ^ 2 / (4 * C)))).mono'
    (continuous_const.mul continuous_norm).rexp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * C * ‖x‖ - c)]

/-- A measurable function of linear growth has integrable exponential moments under a Gaussian
measure. -/
lemma integrable_exp_of_abs_le_add_mul_norm {F : E → ℝ} (hF : AEStronglyMeasurable F μ)
    {A B : ℝ} (hFle : ∀ x, |F x| ≤ A + B * ‖x‖) (t : ℝ) :
    Integrable (fun x ↦ exp (t * F x)) μ := by
  refine ((integrable_exp_mul_norm (|t| * B)).const_mul (exp (|t| * A))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable (hF.const_mul t))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  calc t * F x ≤ |t * F x| := le_abs_self _
    _ = |t| * |F x| := abs_mul _ _
    _ ≤ |t| * (A + B * ‖x‖) := mul_le_mul_of_nonneg_left (hFle x) (abs_nonneg t)
    _ = |t| * A + |t| * B * ‖x‖ := by ring

/-- A measurable function of linear growth is integrable under a Gaussian measure. -/
lemma integrable_of_abs_le_add_mul_norm {F : E → ℝ} (hF : AEStronglyMeasurable F μ)
    {A B : ℝ} (hFle : ∀ x, |F x| ≤ A + B * ‖x‖) : Integrable F μ := by
  refine ((integrable_const A).add (IsGaussian.integrable_id.norm.const_mul B)).mono' hF
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hFle x

/-- A Gaussian measure has finite moments of all orders. -/
lemma integrable_norm_pow (n : ℕ) : Integrable (fun x ↦ ‖x‖ ^ n) μ :=
  (IsGaussian.memLp_id μ n (by simp)).integrable_norm_pow'

/-- A measurable function of quadratic growth is integrable under a Gaussian measure. -/
lemma integrable_of_abs_le_add_mul_norm_sq {F : E → ℝ} (hF : AEStronglyMeasurable F μ)
    {A B C : ℝ} (hFle : ∀ x, |F x| ≤ A + B * ‖x‖ + C * ‖x‖ ^ 2) : Integrable F μ := by
  refine (((integrable_const A).add (IsGaussian.integrable_id.norm.const_mul B)).add
    ((integrable_norm_pow 2).const_mul C)).mono' hF
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hFle x

end isGaussian

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ} {L : ℝ≥0}

/-- A `C¹` function with bounded gradient is integrable under a Gaussian measure, with all its
exponential moments. -/
lemma integrable_exp_of_norm_gradient_le {μ : Measure E} [IsGaussian μ]
    (hf : ContDiff ℝ 1 f) (hL : ∀ x, ‖gradient f x‖ ≤ L) (t : ℝ) :
    Integrable (fun x ↦ exp (t * f x)) μ :=
  integrable_exp_of_abs_le_add_mul_norm hf.continuous.aestronglyMeasurable
    (abs_le_of_norm_gradient_le (hf.differentiable one_ne_zero) hL) t

lemma integrable_of_norm_gradient_le {μ : Measure E} [IsGaussian μ]
    (hf : ContDiff ℝ 1 f) (hL : ∀ x, ‖gradient f x‖ ≤ L) : Integrable f μ :=
  integrable_of_abs_le_add_mul_norm hf.continuous.aestronglyMeasurable
    (abs_le_of_norm_gradient_le (hf.differentiable one_ne_zero) hL)

end gradient

end gm

section qc
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ}

/-- The derivative of `θ ↦ f (sin θ • u + cos θ • v)`. -/
lemma hasDerivAt_comp_quarterCircle (hf : Differentiable ℝ f) (u v : E) (θ : ℝ) :
    HasDerivAt (fun θ ↦ f (sin θ • u + cos θ • v))
      ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ θ := by
  have hγ : HasDerivAt (fun θ ↦ sin θ • u + cos θ • v) (cos θ • u + (-sin θ) • v) θ :=
    ((hasDerivAt_sin θ).smul_const u).add ((hasDerivAt_cos θ).smul_const v)
  have h := (hasGradientAt_iff_hasFDerivAt.1 (hf _).hasGradientAt).comp_hasDerivAt θ hγ
  exact h.congr_deriv (by rw [toDual_apply_apply, sub_eq_add_neg, neg_smul])

/-- **Interpolation along a quarter circle**:
`f u - f v = ∫₀^{π/2} ⟪∇f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ dθ`. -/
lemma sub_eq_integral_quarterCircle (hf : ContDiff ℝ 1 f) (u v : E) :
    f u - f v =
      ∫ θ in (0 : ℝ)..(π / 2), ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ := by
  have hcont : Continuous fun θ : ℝ ↦
      ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ :=
    ((continuous_gradient_of_contDiff hf).comp (by fun_prop)).inner (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ ↦ hasDerivAt_comp_quarterCircle (hf.differentiable one_ne_zero) u v θ)
    (hcont.intervalIntegrable _ _)]
  simp

/-- **Jensen's inequality for the uniform measure on `[0, π/2]`**: for a continuous `h`,
`exp (s ∫₀^{π/2} h) ≤ (2/π) ∫₀^{π/2} exp (π s / 2 · h θ) dθ`. -/
lemma exp_mul_integral_le_integral_exp {h : ℝ → ℝ} (hc : Continuous h) (s : ℝ) :
    exp (s * ∫ θ in (0 : ℝ)..(π / 2), h θ) ≤
      2 / π * ∫ θ in (0 : ℝ)..(π / 2), exp (π * s / 2 * h θ) := by
  have hπ : 0 < π / 2 := by positivity
  set ν : Measure ℝ := volume.restrict (Ioc 0 (π / 2)) with hν
  have hν_univ : ν.real univ = π / 2 := by
    rw [hν, measureReal_restrict_apply_univ, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hπ.le]
  have : NeZero ν := ⟨fun h0 ↦ by simp [h0] at hν_univ; linarith⟩
  have hint : ∀ g : ℝ → ℝ, Continuous g → Integrable g ν := fun g hg ↦
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hJ := ConvexOn.map_average_le (μ := ν) (f := fun θ ↦ π * s / 2 * h θ) convexOn_exp
    continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    (hint _ (by fun_prop)) (hint _ (by fun_prop))
  rw [average_eq, average_eq, hν_univ, smul_eq_mul, smul_eq_mul, integral_const_mul] at hJ
  rw [intervalIntegral.integral_of_le hπ.le, intervalIntegral.integral_of_le hπ.le]
  have h1 : (π / 2)⁻¹ * (π * s / 2 * ∫ θ, h θ ∂ν) = s * ∫ θ, h θ ∂ν := by
    field_simp
  rw [h1, inv_div] at hJ
  exact hJ

end qc
section mp
noncomputable def gaussianConcentrationConst : ℝ≥0 := ⟨π ^ 2 / 4, by positivity⟩

lemma coe_gaussianConcentrationConst : (gaussianConcentrationConst : ℝ) = π ^ 2 / 4 := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section rotation

variable {μ : Measure E} [IsGaussian μ]

/-- For a centered Gaussian measure `μ`, the law of
`(sin θ • g + cos θ • g', cos θ • g - sin θ • g')` under `μ ⊗ μ` is `μ ⊗ μ`: the integrals of
`Φ ∘ rotation θ ∘ swap` and of `Φ` coincide. -/
lemma integral_comp_rotation_swap_prod (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0) {Φ : E × E → ℝ}
    (hΦ : Continuous Φ) (θ : ℝ) :
    ∫ p, Φ (ContinuousLinearMap.rotation θ p.swap) ∂(μ.prod μ) = ∫ p, Φ p ∂(μ.prod μ) := by
  have h1 : (μ.prod μ).map Prod.swap = μ.prod μ := Measure.prod_swap
  have h2 := IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero (μ := μ) hμ θ
  calc ∫ p, Φ (ContinuousLinearMap.rotation θ p.swap) ∂(μ.prod μ)
      = ∫ q, Φ (ContinuousLinearMap.rotation θ q) ∂((μ.prod μ).map Prod.swap) :=
        (integral_map measurable_swap.aemeasurable
          (hΦ.comp (ContinuousLinearMap.rotation θ).continuous).aestronglyMeasurable).symm
    _ = ∫ q, Φ (ContinuousLinearMap.rotation θ q) ∂(μ.prod μ) := by rw [h1]
    _ = ∫ r, Φ r ∂((μ.prod μ).map (ContinuousLinearMap.rotation θ)) :=
        (integral_map (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable
          hΦ.aestronglyMeasurable).symm
    _ = ∫ r, Φ r ∂(μ.prod μ) := by rw [h2]

end rotation

section maureyPisier

variable {f : E → ℝ} {L : ℝ≥0}

/-- **MGF of the rotated gradient term**: for `(g, g') ~ μ ⊗ μ` with `μ` the standard Gaussian
measure, `∫ exp (s ⟪∇f(g), g'⟫) = ∫ exp (s² ‖∇f(g)‖² / 2) ≤ exp (s² L² / 2)`. -/
lemma integral_exp_inner_gradient_prod_stdGaussian_le (hf : ContDiff ℝ 1 f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) (s : ℝ) :
    ∫ p, exp (s * ⟪gradient f p.1, p.2⟫) ∂((stdGaussian E).prod (stdGaussian E)) ≤
      exp (s ^ 2 * L ^ 2 / 2) := by
  have hint : Integrable (fun p : E × E ↦ exp (s * ⟪gradient f p.1, p.2⟫))
      ((stdGaussian E).prod (stdGaussian E)) := by
    refine ((integrable_const (1 : ℝ)).mul_prod
      (integrable_exp_mul_norm (μ := stdGaussian E) (|s| * L))).mono'
      (continuous_const.mul (((continuous_gradient_of_contDiff hf).comp continuous_fst).inner
        continuous_snd)).rexp.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, one_mul]
    refine Real.exp_le_exp.2 ?_
    calc s * ⟪gradient f p.1, p.2⟫ ≤ |s * ⟪gradient f p.1, p.2⟫| := le_abs_self _
      _ = |s| * |⟪gradient f p.1, p.2⟫| := abs_mul _ _
      _ ≤ |s| * (L * ‖p.2‖) :=
          mul_le_mul_of_nonneg_left (abs_inner_gradient_le hL _ _) (abs_nonneg _)
      _ = |s| * L * ‖p.2‖ := by ring
  rw [integral_prod _ hint]
  have hmgf : ∀ u, ∫ v, exp (s * ⟪gradient f u, v⟫) ∂stdGaussian E =
      exp (s ^ 2 * ‖gradient f u‖ ^ 2 / 2) := fun u ↦ by
    have h : ∫ v, exp (s * ⟪gradient f u, v⟫) ∂stdGaussian E = _ :=
      mgf_dual (innerSL ℝ (gradient f u)) s
    rw [h, integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm]
    congr 1
    ring
  simp_rw [hmgf]
  calc ∫ u, exp (s ^ 2 * ‖gradient f u‖ ^ 2 / 2) ∂stdGaussian E
      ≤ ∫ _, exp (s ^ 2 * L ^ 2 / 2) ∂stdGaussian E :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ (exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun u ↦ exp_le_exp.2 (by
            gcongr
            exact hL u))
    _ = exp (s ^ 2 * L ^ 2 / 2) := by simp

/-- **Maurey–Pisier Gaussian concentration**: a `C¹` function `f` with `‖∇f‖ ≤ L` everywhere
satisfies, under the standard Gaussian measure `μ`,
`∫ exp (λ (f x - μ[f])) ∂μ ≤ exp (c_G L² λ² / 2)` with `c_G = π²/4`, i.e. `f - μ[f]` has a
sub-Gaussian moment generating function with constant `c_G L²`. -/
theorem hasSubgaussianMGF_sub_integral_stdGaussian (hf : ContDiff ℝ 1 f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian E)
      (gaussianConcentrationConst * L ^ 2) (stdGaussian E) := by
  set μ := stdGaussian E with hμ
  set m := ∫ y, f y ∂μ with hm
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hfi : Integrable f μ := integrable_of_norm_gradient_le hf hL
  have hexp : ∀ t, Integrable (fun x ↦ exp (t * f x)) μ :=
    integrable_exp_of_norm_gradient_le hf hL
  have hint_sub : ∀ t, Integrable (fun x ↦ exp (t * (f x - m))) μ := fun t ↦ by
    refine ((hexp t).const_mul (exp (-(t * m)))).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  refine ⟨hint_sub, fun t ↦ ?_⟩
  change ∫ x, exp (t * (f x - m)) ∂μ ≤ exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2)
  -- Step 1: symmetrization by Jensen's inequality in the independent copy
  have hprod_int : Integrable (fun p : E × E ↦ exp (t * (f p.1 - f p.2))) (μ.prod μ) := by
    refine ((hexp t).mul_prod (hexp (-t))).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  have step1 : ∫ x, exp (t * (f x - m)) ∂μ ≤ ∫ p, exp (t * (f p.1 - f p.2)) ∂(μ.prod μ) := by
    rw [integral_prod _ hprod_int]
    refine integral_mono (hint_sub t) hprod_int.integral_prod_left fun u ↦ ?_
    have hJ := ConvexOn.map_integral_le (μ := μ) (f := fun v ↦ t * (f u - f v)) convexOn_exp
      continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
      (((integrable_const (f u)).sub hfi).const_mul t)
      (((hexp (-t)).const_mul (exp (t * f u))).congr (Filter.Eventually.of_forall fun v ↦ by
        dsimp only [Function.comp_apply]
        rw [← Real.exp_add]
        ring_nf))
    rw [integral_const_mul, integral_sub (integrable_const _) hfi, integral_const, probReal_univ,
      one_smul] at hJ
    exact hJ
  -- Steps 2 and 3: interpolation and Jensen's inequality on the quarter circle
  set K : E × E → ℝ → ℝ := fun p θ ↦
    exp (π * t / 2 * ⟪gradient f (sin θ • p.1 + cos θ • p.2), cos θ • p.1 - sin θ • p.2⟫) with hK
  have step23 : ∀ p : E × E, exp (t * (f p.1 - f p.2)) ≤ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ :=
    fun p ↦ by
      rw [sub_eq_integral_quarterCircle hf p.1 p.2]
      exact exp_mul_integral_le_integral_exp
        (((continuous_gradient_of_contDiff hf).comp (by fun_prop)).inner (by fun_prop)) t
  -- Step 4: Fubini and rotation invariance
  set ν : Measure ℝ := volume.restrict (Ioc 0 (π / 2)) with hν
  have hK_cont : Continuous (Function.uncurry K) :=
    (continuous_const.mul (((continuous_gradient_of_contDiff hf).comp (by fun_prop)).inner (by fun_prop))).rexp
  have hK_int : Integrable (Function.uncurry K) ((μ.prod μ).prod ν) := by
    have hD : Integrable (fun p : E × E ↦
        exp (π * |t| / 2 * L * ‖p.1‖) * exp (π * |t| / 2 * L * ‖p.2‖)) (μ.prod μ) :=
      (integrable_exp_mul_norm _).mul_prod (integrable_exp_mul_norm _)
    refine (hD.mul_prod (integrable_const (1 : ℝ))).mono' hK_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q ↦ ?_)
    change ‖exp (π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
      cos q.2 • q.1.1 - sin q.2 • q.1.2⟫)‖ ≤ _
    rw [Real.norm_of_nonneg (exp_pos _).le, mul_one, ← Real.exp_add]
    refine exp_le_exp.2 ?_
    have h1 := abs_inner_gradient_le hL (sin q.2 • q.1.1 + cos q.2 • q.1.2)
      (cos q.2 • q.1.1 - sin q.2 • q.1.2)
    have h2 : ‖cos q.2 • q.1.1 - sin q.2 • q.1.2‖ ≤ ‖q.1.1‖ + ‖q.1.2‖ := by
      calc ‖cos q.2 • q.1.1 - sin q.2 • q.1.2‖
          ≤ ‖cos q.2 • q.1.1‖ + ‖sin q.2 • q.1.2‖ := norm_sub_le _ _
        _ = |cos q.2| * ‖q.1.1‖ + |sin q.2| * ‖q.1.2‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖q.1.1‖ + 1 * ‖q.1.2‖ := by
            gcongr
            exacts [abs_cos_le_one _, abs_sin_le_one _]
        _ = ‖q.1.1‖ + ‖q.1.2‖ := by ring
    have h3 : |π * t / 2| = π * |t| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_two]
    calc π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫
        ≤ |π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫| := le_abs_self _
      _ = π * |t| / 2 * |⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫| := by rw [abs_mul, h3]
      _ ≤ π * |t| / 2 * (L * (‖q.1.1‖ + ‖q.1.2‖)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 L.2)
      _ = π * |t| / 2 * L * ‖q.1.1‖ + π * |t| / 2 * L * ‖q.1.2‖ := by ring
  have hint2 : Integrable (fun p ↦ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) (μ.prod μ) := by
    simp_rw [intervalIntegral.integral_of_le hπ.le]
    exact hK_int.integral_prod_left.const_mul _
  have step4 : ∫ p, (2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) ∂(μ.prod μ) =
      2 / π * ∫ θ in (0 : ℝ)..(π / 2), ∫ p, K p θ ∂(μ.prod μ) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [intervalIntegral.integral_of_le hπ.le]
    exact integral_integral_swap hK_int
  have step_rot : ∀ θ, ∫ p, K p θ ∂(μ.prod μ) ≤ exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := fun θ ↦ by
    have h := integral_exp_inner_gradient_prod_stdGaussian_le hf hL (π * t / 2)
    rw [← integral_comp_rotation_swap_prod (μ := μ) integral_strongDual_stdGaussian
      (Φ := fun p ↦ exp (π * t / 2 * ⟪gradient f p.1, p.2⟫))
      ((continuous_const.mul (((continuous_gradient_of_contDiff hf).comp continuous_fst).inner
        continuous_snd)).rexp) θ] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    funext p
    have e1 : sin θ • p.1 + cos θ • p.2 = cos θ • p.2 + sin θ • p.1 := add_comm _ _
    have e2 : cos θ • p.1 - sin θ • p.2 = -sin θ • p.2 + cos θ • p.1 := by
      rw [neg_smul, sub_eq_add_neg, add_comm]
    simp only [hK]
    rw [e1, e2]
    rfl
  have hint_θ : IntervalIntegrable (fun θ ↦ ∫ p, K p θ ∂(μ.prod μ)) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le]
    exact hK_int.integral_prod_right
  -- Step 5: conclusion
  calc ∫ x, exp (t * (f x - m)) ∂μ
      ≤ ∫ p, exp (t * (f p.1 - f p.2)) ∂(μ.prod μ) := step1
    _ ≤ ∫ p, (2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) ∂(μ.prod μ) :=
        integral_mono hprod_int hint2 step23
    _ = 2 / π * ∫ θ in (0 : ℝ)..(π / 2), ∫ p, K p θ ∂(μ.prod μ) := step4
    _ ≤ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := by
        gcongr
        exact intervalIntegral.integral_mono_on hπ.le hint_θ intervalIntegrable_const
          fun θ _ ↦ step_rot θ
    _ = exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
          div_mul_div_comm, mul_comm (2 : ℝ) π, div_self (by positivity), one_mul]
    _ = exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2) := by
        congr 1
        rw [NNReal.coe_mul, NNReal.coe_pow, coe_gaussianConcentrationConst]
        ring

end maureyPisier

end mp

end port

end AdversarialBco.Gauss
