/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib

@[expose] public section

/-!
# Gradient bounds and integrability under Gaussian laws (port)

Lemmas of Rémy Degenne on functions with a bounded gradient and on integrability under a Gaussian measure: a
differentiable function with `‖∇f‖ ≤ L` is `L`-Lipschitz and has linear growth (`lipschitzWith_of_norm_gradient_le`,
`abs_le_of_norm_gradient_le`); `exp (c ‖x‖)` is integrable under every Gaussian measure (`integrable_exp_mul_norm`), and
so are the exponential moments of a measurable function of linear growth (`integrable_exp_of_abs_le_add_mul_norm`); a
measurable function of linear growth is integrable (`integrable_of_abs_le_add_mul_norm`), and so is a `C^1` function
with a bounded gradient (`integrable_of_norm_gradient_le`).

Ported to Lean v4.34.1 and Mathlib v4.34.1, with names moved into `AdversarialBco.Gauss` and no proof changed, from
github.com/RemyDegenne/Maiti2026Power at commit b9431dd9b3811779479d1ea108e51268eb7b24ce, Copyright (c) 2026
Rémy Degenne, released under the Apache License 2.0: `Maiti2026Power/ForLMLExplore/Probability/GaussianMGF.lean` and
`.../Analysis/Calculus/Gradient.lean`. Renaming: the `IsGaussian.` prefixes of the exponential moment lemmas are
dropped.
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace AdversarialBco.Gauss

section port

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped RealInnerProductSpace NNReal

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

end isGaussian

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ} {L : ℝ≥0}

lemma integrable_of_norm_gradient_le {μ : Measure E} [IsGaussian μ]
    (hf : ContDiff ℝ 1 f) (hL : ∀ x, ‖gradient f x‖ ≤ L) : Integrable f μ :=
  integrable_of_abs_le_add_mul_norm hf.continuous.aestronglyMeasurable
    (abs_le_of_norm_gradient_le (hf.differentiable one_ne_zero) hL)

end gradient

end gm

end port

end AdversarialBco.Gauss
