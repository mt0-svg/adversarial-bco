/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Convex
public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# Lemma 3.3 for one component

Growth and integrability of the terms, the score of Lemma 3.3 and its second moment, and Lemma 3.3 `inf_one`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body


/-- Linear growth, in the exponential form, from a bounded derivative. -/
theorem abs_le_of_norm_fderiv_le {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hF : ∀ g, HasFDerivAt F (F' g) g)
    (L : ℝ) (hF' : ∀ g, ‖F' g‖ ≤ L) (g : EuclideanSpace ℝ (Fin d)) :
    |F g| ≤ (|F 0| + |L|) * Real.exp (1 * ‖g‖) ∧ ‖F' g‖ ≤ (|F 0| + |L|) * Real.exp (1 * ‖g‖) := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x _ => (hF x).hasFDerivWithinAt)
    (fun x _ => hF' x) convex_univ (Set.mem_univ 0) (Set.mem_univ g)
  rw [sub_zero, Real.norm_eq_abs] at h
  have h1 : |F g| ≤ |F 0| + L * ‖g‖ := by
    have := abs_sub_abs_le_abs_sub (F g) (F 0); linarith
  have he : ‖g‖ + 1 ≤ Real.exp ‖g‖ := Real.add_one_le_exp _
  have he1 : 1 ≤ Real.exp ‖g‖ := Real.one_le_exp (norm_nonneg g)
  rw [one_mul]
  constructor
  · nlinarith [mul_nonneg (abs_nonneg (F 0)) (sub_nonneg.2 he1), mul_nonneg (abs_nonneg L)
      (by linarith : 0 ≤ Real.exp ‖g‖ - ‖g‖), mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg g)]
  · refine (hF' g).trans ?_
    nlinarith [mul_nonneg (abs_nonneg (F 0)) (sub_nonneg.2 he1), mul_nonneg (abs_nonneg L) (sub_nonneg.2 he1),
      le_abs_self L, abs_nonneg (F 0)]

/-- `|g|^2 ≤ 2 e^{|g|}`. -/
theorem sq_le_two_exp (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 2 * Real.exp x := by
  nlinarith [Real.quadratic_le_exp_of_nonneg hx]

/-- The ramp as a function of exponential growth. -/
theorem kr_growth (t : ℝ) : |kr t| ≤ 1 * Real.exp (0 * |t|) ∧ |kr' t| ≤ 1 * Real.exp (0 * |t|) ∧
    |t * kr t| ≤ 1 * Real.exp (1 * |t|) := by
  have h := kr_mem t
  have h' := abs_kr_deriv_le t
  rw [zero_mul, Real.exp_zero, one_mul, one_mul, one_mul]
  refine ⟨by rw [abs_le]; constructor <;> linarith, h', ?_⟩
  rw [abs_mul, abs_of_nonneg h.1]
  nlinarith [Real.add_one_le_exp |t|, abs_nonneg t]

/-- The score of Lemma 3.3 integrated against a function of exponential growth, term by term. -/
theorem integral_mul_score {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R : ℝ)
    (H : EuclideanSpace ℝ (Fin d) → ℝ) (hHc : Continuous H) (A : ℝ)
    (hb : ∀ g, |H g| ≤ A * Real.exp (1 * ‖g‖)) :
    ∫ g, H g * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      1 / R * ∫ g, H g * (‖g‖ ^ 2 - (d : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, ⟪u, g⟫ * (kr ⟪u, g⟫ * H g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        ∫ g, kr' ⟪u, g⟫ * H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        1 / R * ∫ g, H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hA : 0 ≤ A := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans (hb 0))
  have hkrc : Continuous kr := continuous_iff_continuousAt.2 fun t => (hasDerivAt_kr t).continuousAt
  have hkr'm : Measurable kr' := by
    rw [show kr' = deriv kr from funext fun t => (hasDerivAt_kr t).deriv.symm]; exact measurable_deriv kr
  have iH : Integrable H (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_of_abs_le_exp _ hHc.aestronglyMeasurable _ _ hb
  have iQ : Integrable (fun g => H g * (‖g‖ ^ 2 - (d : ℝ))) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integrable_of_abs_le_exp _ (hHc.mul ((continuous_norm.pow 2).sub continuous_const)).aestronglyMeasurable
      (A * (2 + d)) 2 fun g => ?_
    have h1 : |‖g‖ ^ 2 - (d : ℝ)| ≤ (2 + d) * Real.exp ‖g‖ := by
      have := sq_le_two_exp ‖g‖ (norm_nonneg g)
      have he1 : 1 ≤ Real.exp ‖g‖ := Real.one_le_exp (norm_nonneg g)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖g‖, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    rw [abs_mul]
    calc |H g| * |‖g‖ ^ 2 - (d : ℝ)| ≤ A * Real.exp (1 * ‖g‖) * ((2 + d) * Real.exp ‖g‖) :=
          mul_le_mul (hb g) h1 (abs_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
      _ = A * (2 + d) * Real.exp (2 * ‖g‖) := by
          rw [one_mul, show (2 : ℝ) * ‖g‖ = ‖g‖ + ‖g‖ by ring, Real.exp_add]; ring
  have iT : Integrable (fun g => ⟪u, g⟫ * kr ⟪u, g⟫ * H g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu (fun t => t * kr t) (measurable_id.mul hkrc.measurable) 1 1 zero_le_one
      (fun t => (kr_growth t).2.2) H hHc.aestronglyMeasurable A 1 hb
  have iT' : Integrable (fun g => ⟪u, g⟫ * (kr ⟪u, g⟫ * H g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    iT.congr (Filter.Eventually.of_forall fun g => by simp only; ring)
  have iK : Integrable (fun g => kr' ⟪u, g⟫ * H g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu kr' hkr'm 1 0 le_rfl (fun t => (kr_growth t).2.1) H hHc.aestronglyMeasurable A 1 hb
  have i1 : Integrable (fun g => 1 / R * (H g * (‖g‖ ^ 2 - (d : ℝ))) - ⟪u, g⟫ * (kr ⟪u, g⟫ * H g))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := (iQ.const_mul _).sub iT'
  have i2 : Integrable (fun g => 1 / R * (H g * (‖g‖ ^ 2 - (d : ℝ))) - ⟪u, g⟫ * (kr ⟪u, g⟫ * H g) +
      kr' ⟪u, g⟫ * H g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := i1.add iK
  have i3 : Integrable (fun g => 1 / R * H g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := iH.const_mul _
  have i4 : Integrable (fun g => 1 / R * (H g * (‖g‖ ^ 2 - (d : ℝ)))) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    iQ.const_mul _
  have e : (fun g => H g * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R)) =
      fun g => 1 / R * (H g * (‖g‖ ^ 2 - (d : ℝ))) - ⟪u, g⟫ * (kr ⟪u, g⟫ * H g) + kr' ⟪u, g⟫ * H g -
        1 / R * H g := by
    funext g; ring
  rw [e, integral_sub i2 i3, integral_add i1 iK, integral_sub i4 iT', integral_const_mul, integral_const_mul]

/-- The integrability facts of Lemma 3.3 for a `C^1` function with a bounded derivative. -/
theorem integrable_inf_terms {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hF : ∀ g, HasFDerivAt F (F' g) g)
    (L : ℝ) (hF' : ∀ g, ‖F' g‖ ≤ L) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    Integrable F (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => F' g g) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => kr ⟪u, g⟫ * F' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hFb := fun g => (abs_le_of_norm_fderiv_le F F' hF L hF' g).1
  have hFb' := fun g => (abs_le_of_norm_fderiv_le F F' hF L hF' g).2
  have hFcont : Continuous F := continuous_iff_continuousAt.2 fun g => (hF g).continuousAt
  have hkrc : Continuous kr := continuous_iff_continuousAt.2 fun t => (hasDerivAt_kr t).continuousAt
  have hF'm : Measurable F' := by
    rw [show F' = fderiv ℝ F from funext fun g => (hF g).fderiv.symm]; exact measurable_fderiv ℝ F
  refine ⟨integrable_of_abs_le_exp _ hFcont.aestronglyMeasurable _ _ hFb, ?_, ?_⟩
  · refine integrable_of_abs_le_exp _
      ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂ aestronglyMeasurable_id
        hF'm.aestronglyMeasurable) (|F 0| + |L|) 2 fun g => ?_
    rw [← Real.norm_eq_abs]
    calc ‖F' g g‖ ≤ ‖F' g‖ * ‖g‖ := (F' g).le_opNorm g
      _ ≤ (|F 0| + |L|) * Real.exp (1 * ‖g‖) * Real.exp ‖g‖ :=
          mul_le_mul (hFb' g) (by linarith [Real.add_one_le_exp ‖g‖]) (norm_nonneg _)
            ((norm_nonneg _).trans (hFb' g))
      _ = (|F 0| + |L|) * Real.exp (2 * ‖g‖) := by
          rw [one_mul, mul_assoc, ← Real.exp_add]; ring_nf
  · exact integrable_ramp u hu kr hkrc.measurable 1 0 le_rfl (fun t => (kr_growth t).1) (fun g => F' g u)
      (hF'm.apply_continuousLinearMap u).aestronglyMeasurable (|F 0| + |L|) 1 fun g => by
        rw [← Real.norm_eq_abs]; exact ((F' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hFb' g)

/-- Lemma 3.3 for one component. -/
theorem inf_one {d : ℕ} (F G : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hF : ∀ g, HasFDerivAt F (F' g) g)
    (hG : ∀ g, HasFDerivAt G (G' g) g) (hFc : ConvexOn ℝ Set.univ F) (LF LG : ℝ) (hF' : ∀ g, ‖F' g‖ ≤ LF)
    (hG' : ∀ g, ‖G' g‖ ≤ LG) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R Γ : ℝ) (hR : 0 < R)
    (hΓ : F (R • u) ≤ F 0 - Γ) :
    Γ / (2 * R) + ∫ g, kr ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        (∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + G 0) / R ≤
      ∫ g, (F g - G g) * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + (F 0 - G 0) / R := by
  obtain ⟨iF, iFr, iFu⟩ := integrable_inf_terms F F' hF LF hF' u hu
  obtain ⟨iG, iGr, iGu⟩ := integrable_inf_terms G G' hG LG hG' u hu
  have hkrc : Continuous kr := continuous_iff_continuousAt.2 fun t => (hasDerivAt_kr t).continuousAt
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  -- `D = F - G`: Stein's identities and the score
  have hD : ∀ g, HasFDerivAt (fun g => F g - G g) (F' g - G' g) g := fun g => (hF g).sub (hG g)
  have hDb' : ∀ g, ‖F' g - G' g‖ ≤ LF + LG := fun g => (norm_sub_le _ _).trans (add_le_add (hF' g) (hG' g))
  have hDb := fun g => (abs_le_of_norm_fderiv_le _ _ hD (LF + LG) hDb' g).1
  have hDb2 := fun g => (abs_le_of_norm_fderiv_le _ _ hD (LF + LG) hDb' g).2
  have hDc : Continuous fun g => F g - G g :=
    (continuous_iff_continuousAt.2 fun g => (hF g).continuousAt).sub
      (continuous_iff_continuousAt.2 fun g => (hG g).continuousAt)
  have eD := integral_mul_score u hu R (fun g => F g - G g) hDc _ hDb
  have sD := stein_radial (fun g => F g - G g) (fun g => F' g - G' g) hD _ _ hDb hDb2
  have rD := stein_ramp u hu kr kr' hasDerivAt_kr 1 0 le_rfl (fun t => (kr_growth t).1)
    (fun t => (kr_growth t).2.1) (fun g => F g - G g) (fun g => F' g - G' g) hD _ _ hDb hDb2
  beta_reduce at eD sD rD
  have h1 : ∫ g, (F' g - G' g) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, F' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - ∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [← integral_sub iFr iGr]; rfl
  have h2 : ∫ g, kr ⟪u, g⟫ * (F' g - G' g) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, kr ⟪u, g⟫ * F' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, kr ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [← integral_sub iFu iGu]; congr 1; funext g; rw [_root_.sub_apply]; ring
  have h3 : ∫ g, (F g - G g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integral_sub iF iG
  have key : ∫ g, (F g - G g) * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      1 / R * (∫ g, F' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        (∫ g, kr ⟪u, g⟫ * F' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∫ g, kr ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        1 / R * (∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    rw [eD, ← sD, rD, h1, h2, h3]; ring
  -- the chord inequality, integrated
  have hpt : ∀ g, (F g - F 0) / R + Γ / R * kr ⟪u, g⟫ ≤ 1 / R * F' g g - kr ⟪u, g⟫ * F' g u := fun g => by
    have := grad_chord F (F' g) hFc g (hF g) u R Γ (kr ⟪u, g⟫) hR hΓ (kr_mem _).1 (kr_mem _).2
    rwa [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  have ikr : Integrable (fun g => kr ⟪u, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integrable_of_abs_le_exp _ (hkrc.comp hinner).aestronglyMeasurable 1 0 fun g => ?_
    have := (kr_growth ⟪u, g⟫).1; rwa [zero_mul, Real.exp_zero] at this ⊢
  have hF1 : Integrable (fun g => (F g - F 0) / R) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (iF.sub (integrable_const _)).div_const _
  have hk1 : Integrable (fun g => Γ / R * kr ⟪u, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) := ikr.const_mul _
  have hr1 : Integrable (fun g => 1 / R * F' g g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := iFr.const_mul _
  have hL : Integrable (fun g => (F g - F 0) / R + Γ / R * kr ⟪u, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hF1.add hk1
  have hRi : Integrable (fun g => 1 / R * F' g g - kr ⟪u, g⟫ * F' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hr1.sub iFu
  have hI := integral_mono hL hRi hpt
  have eL : ∫ g, ((F g - F 0) / R + Γ / R * kr ⟪u, g⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - F 0) / R + Γ / R * (1 / 2) := by
    rw [integral_add hF1 hk1, integral_div, integral_sub iF (integrable_const _), integral_const_mul,
      integral_kr u hu, integral_const, probReal_univ, one_smul]
  have eR : ∫ g, (1 / R * F' g g - kr ⟪u, g⟫ * F' g u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      1 / R * ∫ g, F' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, kr ⟪u, g⟫ * F' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [integral_sub hr1 iFu, integral_const_mul]
  rw [eL, eR] at hI
  rw [key]
  have hR' : R ≠ 0 := hR.ne'
  have e : ∀ a b c x y z : ℝ, 1 / R * (a - x) - (b - y) - 1 / R * (c - z) + (F 0 - G 0) / R -
      (Γ / (2 * R) + y - (x - z + G 0) / R) = (1 / R * a - b) - ((c - F 0) / R + Γ / R * (1 / 2)) := by
    intro a b c x y z; ring
  linarith [e (∫ g, F' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (∫ g, kr ⟪u, g⟫ * F' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
    (∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
    (∫ g, kr ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))]


/-- The score of Lemma 3.3 has exponential growth. -/
theorem score_bound {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin d)) :
    |(‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R| ≤
      ((3 + d) / R + 2) * Real.exp (1 * ‖g‖) := by
  have ht : |⟪u, g⟫| ≤ ‖g‖ := by simpa [hu] using abs_real_inner_le_norm u g
  have he1 : 1 ≤ Real.exp ‖g‖ := Real.one_le_exp (norm_nonneg g)
  have hq : |‖g‖ ^ 2 - (d : ℝ)| ≤ (2 + d) * Real.exp ‖g‖ := by
    have := sq_le_two_exp ‖g‖ (norm_nonneg g)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖g‖, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hk := kr_growth ⟪u, g⟫
  rw [zero_mul, Real.exp_zero, one_mul, one_mul] at hk
  rw [one_mul] at hk ⊢
  have h3 : |kr ⟪u, g⟫ * ⟪u, g⟫| ≤ Real.exp ‖g‖ := by
    rw [mul_comm]; exact hk.2.2.trans (Real.exp_le_exp.2 ht)
  have h4 : |kr' ⟪u, g⟫| ≤ Real.exp ‖g‖ := hk.2.1.trans he1
  have h5 : |(‖g‖ ^ 2 - (d : ℝ)) / R| ≤ (2 + d) * Real.exp ‖g‖ / R := by
    rw [abs_div, abs_of_pos hR]; exact div_le_div_of_nonneg_right hq hR.le
  have h6 : |1 / R| ≤ Real.exp ‖g‖ / R := by
    rw [abs_of_pos (by positivity)]; exact div_le_div_of_nonneg_right he1 hR.le
  have e : ((3 + d) / R + 2) * Real.exp ‖g‖ =
      (2 + d) * Real.exp ‖g‖ / R + Real.exp ‖g‖ + Real.exp ‖g‖ + Real.exp ‖g‖ / R := by
    field_simp; ring
  rw [e, abs_le]
  constructor
  · linarith [neg_abs_le ((‖g‖ ^ 2 - (d : ℝ)) / R), le_abs_self (kr ⟪u, g⟫ * ⟪u, g⟫),
      neg_abs_le (kr' ⟪u, g⟫), le_abs_self (1 / R)]
  · linarith [le_abs_self ((‖g‖ ^ 2 - (d : ℝ)) / R), neg_abs_le (kr ⟪u, g⟫ * ⟪u, g⟫),
      le_abs_self (kr' ⟪u, g⟫), neg_abs_le (1 / R)]

/-- The square of the score, and the score against a function of exponential growth, are integrable. -/
theorem integrable_score {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 < R)
    (H : EuclideanSpace ℝ (Fin d) → ℝ) (hHm : AEStronglyMeasurable H (stdGaussian (EuclideanSpace ℝ (Fin d))))
    (A : ℝ) (hb : ∀ g, |H g| ≤ A * Real.exp (1 * ‖g‖)) :
    Integrable (fun g => ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => H g * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hkrc : Continuous kr := continuous_iff_continuousAt.2 fun t => (hasDerivAt_kr t).continuousAt
  have hkr'm : Measurable kr' := by
    rw [show kr' = deriv kr from funext fun t => (hasDerivAt_kr t).deriv.symm]; exact measurable_deriv kr
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hm : Measurable fun g : EuclideanSpace ℝ (Fin d) =>
      (‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R :=
    (((((continuous_norm.pow 2).sub continuous_const).div_const R).measurable.sub
      ((hkrc.comp hinner).mul hinner).measurable).add (hkr'm.comp hinner.measurable)).sub measurable_const
  have hC : 0 ≤ (3 + d) / R + 2 := by positivity
  have hA : 0 ≤ A := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((abs_nonneg _).trans (hb 0))
  refine ⟨integrable_of_abs_le_exp _ (hm.pow_const 2).aestronglyMeasurable (((3 + d) / R + 2) ^ 2) 2 fun g => ?_,
    integrable_of_abs_le_exp _ (hHm.mul hm.aestronglyMeasurable) (A * ((3 + d) / R + 2)) 2 fun g => ?_⟩
  · have h := score_bound u hu R hR g
    rw [abs_pow, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + 1 * ‖g‖ by ring, Real.exp_add]
    nlinarith [abs_nonneg ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R),
      Real.exp_pos (1 * ‖g‖)]
  · have h := score_bound u hu R hR g
    rw [abs_mul, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + 1 * ‖g‖ by ring, Real.exp_add]
    calc |H g| * |(‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R| ≤
          A * Real.exp (1 * ‖g‖) * (((3 + d) / R + 2) * Real.exp (1 * ‖g‖)) :=
        mul_le_mul (hb g) h (abs_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
      _ = A * ((3 + d) / R + 2) * (Real.exp (1 * ‖g‖) * Real.exp (1 * ‖g‖)) := by ring

/-- The second moment of the score. -/
theorem score_sq_le {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 < R) :
    ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 2 * (2 * (d : ℝ) + 1) / R ^ 2 + 8 := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hI1 := (integrable_score u hu R hR (fun _ => 0) aestronglyMeasurable_const 0 (fun g => by simp)).1
  have hn4 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 4) γ := AdversarialBco.Gauss.integrable_norm_pow 4
  have hn2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) γ := AdversarialBco.Gauss.integrable_norm_pow 2
  have hq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2) γ := by
    have := (hn4.sub (hn2.const_mul (2 * ((d : ℝ) + 1)))).add (integrable_const (((d : ℝ) + 1) ^ 2))
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have ht : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 2) γ := by
    refine hn2.mono' (hinner.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have h := abs_real_inner_le_norm u g
    rw [hu, one_mul] at h
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hI2a : Integrable (fun g : EuclideanSpace ℝ (Fin d) => 2 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 + 4) γ :=
    (hq.const_mul _).add (integrable_const _)
  have hI2b : Integrable (fun g : EuclideanSpace ℝ (Fin d) => 4 * ⟪u, g⟫ ^ 2) γ := ht.const_mul _
  have hI2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) =>
      2 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 + 4 + 4 * ⟪u, g⟫ ^ 2) γ := hI2a.add hI2b
  have hpt : ∀ g : EuclideanSpace ℝ (Fin d),
      ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2 ≤
        2 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 + 4 + 4 * ⟪u, g⟫ ^ 2 := fun g => by
    set t := ⟪u, g⟫
    set a := (‖g‖ ^ 2 - (d : ℝ) - 1) / R with ha_def
    have he : (‖g‖ ^ 2 - (d : ℝ)) / R - kr t * t + kr' t - 1 / R = a + (kr' t - kr t * t) := by
      rw [ha_def]; field_simp; ring
    have ha : a ^ 2 = 1 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 := by rw [ha_def, div_pow]; ring
    obtain ⟨hk0, hk1⟩ := kr_mem t
    have hk'2 : kr' t ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (kr' t), abs_kr_deriv_le t]
    have hkt : (kr t * t) ^ 2 ≤ t ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg t, mul_le_mul hk1 hk1 hk0 zero_le_one]
    rw [he]
    have e2 : 2 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 = 2 * a ^ 2 := by rw [ha]; ring
    rw [e2]
    nlinarith [sq_nonneg (a - (kr' t - kr t * t)), sq_nonneg (kr' t + kr t * t)]
  calc ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2 ∂γ
      ≤ ∫ g, (2 / R ^ 2 * (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 + 4 + 4 * ⟪u, g⟫ ^ 2) ∂γ := integral_mono hI1 hI2 hpt
    _ = 2 / R ^ 2 * (2 * (d : ℝ) + 1) + 4 + 4 := by
      rw [integral_add hI2a hI2b, integral_add (hq.const_mul _) (integrable_const _), integral_const_mul, integral_const_mul,
        integral_const, (gauss_moments d).2, integral_inner_sq, hu]
      simp
    _ = 2 * (2 * (d : ℝ) + 1) / R ^ 2 + 8 := by ring

end AdversarialBco.Body
