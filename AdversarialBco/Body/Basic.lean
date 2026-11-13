/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Lemmas
public import AdversarialBco.Gauss.Concentration

@[expose] public section

/-!
# Stein's identity on `ℝ^d`

Integrability under the standard Gaussian of functions of exponential growth (`integrable_of_abs_le_exp`); Stein's
identity `E[⟨v, g⟩ Φ(g)] = E[Φ'(g) v]` for a `C^1` function of exponential growth, along a coordinate
(`stein_coord`) and along a direction (`stein_dir`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body

theorem integrable_of_abs_le_exp {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : AEStronglyMeasurable f (stdGaussian (EuclideanSpace ℝ (Fin d)))) (A B : ℝ)
    (hb : ∀ g, |f g| ≤ A * Real.exp (B * ‖g‖)) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine ((AdversarialBco.Gauss.integrable_exp_mul_norm
    (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) B).const_mul A).mono' hf
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs]; exact hb g

theorem stein_coord {d : ℕ} (Φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (Φ' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hΦ : ∀ g, HasFDerivAt Φ (Φ' g) g)
    (A B : ℝ) (hb : ∀ g, |Φ g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖Φ' g‖ ≤ A * Real.exp (B * ‖g‖))
    (i : Fin d) :
    ∫ g, g i * Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, Φ' g (EuclideanSpace.single i 1) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set P := Measure.pi fun _ : Fin d => gaussianReal 0 1
  have hP : P.map (WithLp.toLp 2) = γ := map_pi_eq_stdGaussian
  have hmeas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) := by fun_prop
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun g => (hΦ g).continuousAt
  have hΦ'eq : Φ' = fderiv ℝ Φ := funext fun g => (hΦ g).fderiv.symm
  have hDm : Measurable fun g => Φ' g (EuclideanSpace.single i 1) := by
    rw [hΦ'eq]; exact measurable_fderiv_apply_const ℝ Φ _
  -- integrability on γ
  have hnorm : ∀ g : EuclideanSpace ℝ (Fin d), |g i| ≤ ‖g‖ := fun g => by
    have := EuclideanSpace.norm_eq g
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le g i
  have i1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => g i * Φ g) γ := by
    refine integrable_of_abs_le_exp _ ((by fun_prop : Continuous fun g : EuclideanSpace ℝ (Fin d) => g i).mul hΦc).aestronglyMeasurable
      A (B + 1) fun g => ?_
    rw [abs_mul]
    have h1 : |g i| ≤ Real.exp ‖g‖ := (hnorm g).trans (by linarith [Real.add_one_le_exp ‖g‖])
    have hA : 0 ≤ A * Real.exp (B * ‖g‖) := (abs_nonneg _).trans (hb g)
    calc |g i| * |Φ g| ≤ Real.exp ‖g‖ * (A * Real.exp (B * ‖g‖)) :=
          mul_le_mul h1 (hb g) (abs_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp ((B + 1) * ‖g‖) := by rw [add_mul, one_mul, Real.exp_add]; ring
  have i2 : Integrable (fun g => Φ' g (EuclideanSpace.single i 1)) γ := by
    refine integrable_of_abs_le_exp _ hDm.aestronglyMeasurable A B fun g => ?_
    rw [← Real.norm_eq_abs]
    calc ‖Φ' g (EuclideanSpace.single i 1)‖ ≤ ‖Φ' g‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (Φ' g).le_opNorm _
      _ = ‖Φ' g‖ := by simp
      _ ≤ _ := hb' g
  have i3 : Integrable Φ γ := integrable_of_abs_le_exp _ hΦc.aestronglyMeasurable A B hb
  rw [← hP] at i1 i2 i3 ⊢
  rw [integral_map hmeas.aemeasurable i1.aestronglyMeasurable,
    integral_map hmeas.aemeasurable i2.aestronglyMeasurable]
  rw [integrable_map_measure i1.aestronglyMeasurable hmeas.aemeasurable] at i1
  rw [integrable_map_measure i2.aestronglyMeasurable hmeas.aemeasurable] at i2
  rw [integrable_map_measure i3.aestronglyMeasurable hmeas.aemeasurable] at i3
  refine AdversarialBco.gaussian_ibp_pi i (fun w => Φ (WithLp.toLp 2 w))
    (fun w => Φ' (WithLp.toLp 2 w) (EuclideanSpace.single i 1)) (fun w u => ?_) i1 i2 i3
  have hline : HasDerivAt (fun v : ℝ => (WithLp.toLp 2 (Function.update w i v) : EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace.single i 1) u := by
    have heq : (fun v : ℝ => (WithLp.toLp 2 (Function.update w i v) : EuclideanSpace ℝ (Fin d))) =
        fun v => WithLp.toLp 2 (Function.update w i 0) + v • EuclideanSpace.single i 1 := by
      funext v; ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [heq]
    simpa using ((hasDerivAt_id u).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
      (WithLp.toLp 2 (Function.update w i 0) : EuclideanSpace ℝ (Fin d))
  have := (hΦ _).comp_hasDerivAt u hline
  exact this

theorem stein_dir {d : ℕ} (Φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (Φ' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hΦ : ∀ g, HasFDerivAt Φ (Φ' g) g)
    (A B : ℝ) (hb : ∀ g, |Φ g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖Φ' g‖ ≤ A * Real.exp (B * ‖g‖))
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪v, g⟫ * Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, Φ' g v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun g => (hΦ g).continuousAt
  have hΦ'eq : Φ' = fderiv ℝ Φ := funext fun g => (hΦ g).fderiv.symm
  have hnorm : ∀ g : EuclideanSpace ℝ (Fin d), ∀ i, |g i| ≤ ‖g‖ := fun g i => by
    rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le g i
  have hint1 : ∀ i, Integrable (fun g : EuclideanSpace ℝ (Fin d) => v i * (g i * Φ g)) γ := fun i => by
    refine Integrable.const_mul ?_ _
    refine integrable_of_abs_le_exp _ ((by fun_prop : Continuous fun g : EuclideanSpace ℝ (Fin d) => g i).mul hΦc).aestronglyMeasurable
      A (B + 1) fun g => ?_
    rw [abs_mul]
    have h1 : |g i| ≤ Real.exp ‖g‖ := (hnorm g i).trans (by linarith [Real.add_one_le_exp ‖g‖])
    calc |g i| * |Φ g| ≤ Real.exp ‖g‖ * (A * Real.exp (B * ‖g‖)) :=
          mul_le_mul h1 (hb g) (abs_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp ((B + 1) * ‖g‖) := by rw [add_mul, one_mul, Real.exp_add]; ring
  have hint2 : ∀ i, Integrable (fun g => v i * Φ' g (EuclideanSpace.single i 1)) γ := fun i => by
    refine Integrable.const_mul ?_ _
    refine integrable_of_abs_le_exp _ ?_ A B fun g => ?_
    · rw [hΦ'eq]; exact (measurable_fderiv_apply_const ℝ Φ _).aestronglyMeasurable
    rw [← Real.norm_eq_abs]
    calc ‖Φ' g (EuclideanSpace.single i 1)‖ ≤ ‖Φ' g‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (Φ' g).le_opNorm _
      _ = ‖Φ' g‖ := by simp
      _ ≤ _ := hb' g
  have e1 : (fun g : EuclideanSpace ℝ (Fin d) => ⟪v, g⟫ * Φ g) = fun g => ∑ i, v i * (g i * Φ g) := by
    funext g
    rw [PiLp.inner_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm, mul_left_comm]
  have e2 : (fun g => Φ' g v) = fun g => ∑ i, v i * Φ' g (EuclideanSpace.single i 1) := by
    funext g
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [e1, e2, integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, stein_coord Φ Φ' hΦ A B hb hb' i]

end AdversarialBco.Body
