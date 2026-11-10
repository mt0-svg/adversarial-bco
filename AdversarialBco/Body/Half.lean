/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# Lemma 3.4

The tail weight `zeta`, the lower bound `chi_ge_zeta`, and Lemma 3.4 `half_one`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_le_exp.2 (by linarith : -x ≤ x)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_le_exp.2 (by linarith : x ≤ -x)]

theorem exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos x]

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_le]
  constructor <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- The tail weight of Lemma 3.4, `ζ(t) = 2 e^{-T^2} cosh(T t)`, and its derivative. -/
noncomputable def zeta (T t : ℝ) : ℝ := 2 * Real.exp (-T ^ 2) * Real.cosh (T * t)

noncomputable def zeta' (T t : ℝ) : ℝ := 2 * Real.exp (-T ^ 2) * (T * Real.sinh (T * t))

theorem hasDerivAt_zeta (T t : ℝ) : HasDerivAt (zeta T) (zeta' T t) t := by
  have h := ((Real.hasDerivAt_cosh (T * t)).comp t ((hasDerivAt_id t).const_mul T)).const_mul
    (2 * Real.exp (-T ^ 2))
  unfold zeta zeta'
  convert h using 1
  all_goals first | rfl | ring

/-- The pointwise bounds on `ζ` used by Lemma 3.4. -/
theorem zeta_bounds (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ zeta T t ∧ |zeta T t| ≤ 2 * (1 + T) * Real.exp (T * |t|) ∧
      |zeta' T t| ≤ 2 * (1 + T) * Real.exp (T * |t|) ∧
      |t * zeta T t - zeta' T t| ≤ 2 * Real.exp (-T ^ 2) * ((|t| + T) * Real.cosh (T * t)) ∧
      |t * zeta T t - zeta' T t| ≤ 2 * (1 + T) * Real.exp ((T + 1) * |t|) := by
  have hc := Real.cosh_pos (T * t)
  have hs := abs_sinh_le_cosh (T * t)
  have he := Real.exp_pos (-T ^ 2)
  have he1 : Real.exp (-T ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hct : Real.cosh (T * t) ≤ Real.exp (T * |t|) := by
    have := cosh_le_exp_abs (T * t); rwa [abs_mul, abs_of_nonneg hT] at this
  have hz0 : 0 ≤ zeta T t := by unfold zeta; exact mul_nonneg (by positivity) hc.le
  have hpt : |t * zeta T t - zeta' T t| ≤ 2 * Real.exp (-T ^ 2) * ((|t| + T) * Real.cosh (T * t)) := by
    have e : t * zeta T t - zeta' T t =
        2 * Real.exp (-T ^ 2) * (t * Real.cosh (T * t) - T * Real.sinh (T * t)) := by
      unfold zeta zeta'; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-T ^ 2))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := abs_add_le (t * Real.cosh (T * t)) (-(T * Real.sinh (T * t)))
    rw [abs_neg, ← sub_eq_add_neg, abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg hT] at h1
    nlinarith [mul_le_mul_of_nonneg_left hs hT]
  refine ⟨hz0, ?_, ?_, hpt, ?_⟩
  · rw [abs_of_nonneg hz0]; unfold zeta
    calc 2 * Real.exp (-T ^ 2) * Real.cosh (T * t) ≤ 2 * 1 * Real.exp (T * |t|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he1 (by norm_num)) hct hc.le (by norm_num)
      _ ≤ 2 * (1 + T) * Real.exp (T * |t|) := by nlinarith [Real.exp_pos (T * |t|)]
  · unfold zeta'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-T ^ 2)), abs_mul, abs_of_nonneg hT]
    calc 2 * Real.exp (-T ^ 2) * (T * |Real.sinh (T * t)|) ≤ 2 * 1 * (T * Real.exp (T * |t|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he1 (by norm_num))
            (mul_le_mul_of_nonneg_left (hs.trans hct) hT) (mul_nonneg hT (abs_nonneg _)) (by norm_num)
      _ ≤ 2 * (1 + T) * Real.exp (T * |t|) := by nlinarith [Real.exp_pos (T * |t|)]
  · refine hpt.trans ?_
    have h1 : |t| + T ≤ (1 + T) * Real.exp |t| := by
      nlinarith [Real.add_one_le_exp |t|, mul_nonneg hT (sub_nonneg.2 (Real.one_le_exp (abs_nonneg t)))]
    have hn1 : 0 ≤ (|t| + T) * Real.cosh (T * t) := mul_nonneg (by linarith [abs_nonneg t]) hc.le
    calc 2 * Real.exp (-T ^ 2) * ((|t| + T) * Real.cosh (T * t)) ≤ 2 * 1 * ((|t| + T) * Real.cosh (T * t)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 (by norm_num)) hn1
      _ ≤ 2 * 1 * ((1 + T) * Real.exp |t| * Real.exp (T * |t|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hct hc.le (mul_nonneg (by linarith) (Real.exp_pos _).le))
            (by norm_num)
      _ = 2 * (1 + T) * Real.exp ((T + 1) * |t|) := by
          rw [show (T + 1) * |t| = |t| + T * |t| by ring, Real.exp_add]; ring

/-- `χ ≥ (1 - ζ)/(4 (1 + T))` everywhere: on `|t| ≤ T` from `χ ≥ 1/(4 (1 + |t|))`, beyond from `ζ ≥ 1`. -/
theorem chi_ge_zeta (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : (1 - zeta T t) / (4 * (1 + T)) ≤ chi t := by
  have hcb := chi_bounds t
  have hT1 : 0 < 4 * (1 + T) := by linarith
  have hz0 := (zeta_bounds T hT t).1
  by_cases h : |t| ≤ T
  · calc (1 - zeta T t) / (4 * (1 + T)) ≤ 1 / (4 * (1 + T)) :=
          div_le_div_of_nonneg_right (by linarith) hT1.le
      _ ≤ 1 / (4 * (1 + |t|)) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ chi t := hcb.1
  · push Not at h
    have hz : 1 ≤ zeta T t := by
      unfold zeta
      have h1 : Real.exp |T * t| ≤ 2 * Real.cosh (T * t) := exp_abs_le_two_cosh _
      have h2 : T ^ 2 ≤ |T * t| := by rw [abs_mul, abs_of_nonneg hT]; nlinarith [abs_nonneg t]
      have h3 : 1 ≤ Real.exp (-T ^ 2) * Real.exp |T * t| := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-T ^ 2)).le]
    have : (1 - zeta T t) / (4 * (1 + T)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT1.le
    exact this.trans (le_trans (by positivity) hcb.1)

/-- Lemma 3.4. -/
theorem half_one {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G1 : EuclideanSpace ℝ (Fin d) → ℝ)
    (G1' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG1 : ∀ g, HasFDerivAt G1 (G1' g) g)
    (L1 M : ℝ) (hL1 : ∀ g, |G1 g| ≤ L1) (hM : ∀ g, ‖G1' g‖ ≤ M) (hmono : ∀ g, 0 ≤ G1' g u) (lam T : ℝ)
    (hT : 0 ≤ T) (hS1 : ∫ g, G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0)
    (hS2 : ∫ g, ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam)
    (htail : 4 * (1 + T) * L1 * Real.exp (T + 1 / 2 - T ^ 2 / 2) ≤ lam / 2) :
    lam / (8 * (1 + T)) ≤ ∫ g, kr ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hL0 : 0 ≤ L1 := (abs_nonneg _).trans (hL1 0)
  have hT1 : 0 < 4 * (1 + T) := by linarith
  have ht : ∀ g : EuclideanSpace ℝ (Fin d), |⟪u, g⟫| ≤ ‖g‖ := fun g => by
    simpa [hu] using abs_real_inner_le_norm u g
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hG1c : Continuous G1 := continuous_iff_continuousAt.2 fun g => (hG1 g).continuousAt
  have hDm : Measurable fun g => G1' g u := by
    rw [show G1' = fderiv ℝ G1 from funext fun g => (hG1 g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G1 u
  have hDb : ∀ g, |G1' g u| ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [zero_mul, Real.exp_zero, mul_one, ← Real.norm_eq_abs]
    exact ((G1' g).le_opNorm u).trans (by rw [hu, mul_one]; linarith [hM g, (abs_nonneg _).trans (hL1 g)])
  have hbG : ∀ g, |G1 g| ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [zero_mul, Real.exp_zero, mul_one]; linarith [hL1 g, (norm_nonneg _).trans (hM g)]
  have hbG' : ∀ g, ‖G1' g‖ ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [zero_mul, Real.exp_zero, mul_one]; linarith [hM g, (abs_nonneg _).trans (hL1 g)]
  -- `E[D_uu G] = lam`
  have h1 : ∫ g, G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam := by
    rw [← hS2]; exact (stein_dir G1 G1' hG1 _ _ hbG hbG' u).symm
  -- `E[kr(t) G1] = E[χ(t) D_uu G]`
  have hchic : Continuous chi := continuous_iff_continuousAt.2 fun t => (hasDerivAt_chi t).continuousAt
  have hchi'm : Measurable chi' := by
    rw [show chi' = deriv chi from funext fun t => (hasDerivAt_chi t).deriv.symm]; exact measurable_deriv chi
  have hchi_abs : ∀ t, |chi t| ≤ 1 / 4 * Real.exp (0 * |t|) := fun t => by
    rw [zero_mul, Real.exp_zero, mul_one]
    have h := chi_bounds t
    rw [abs_of_nonneg (le_trans (by positivity) h.1)]; exact h.2.1
  have hchi'_abs : ∀ t, |chi' t| ≤ 1 / 4 * Real.exp (0 * |t|) := fun t => by
    rw [zero_mul, Real.exp_zero, mul_one]; exact (chi_bounds t).2.2
  have h2 := stein_ramp u hu chi chi' hasDerivAt_chi (1 / 4) 0 le_rfl hchi_abs hchi'_abs G1 G1' hG1 (L1 + M) 0
    hbG hbG'
  have iG : Integrable G1 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_of_abs_le_exp _ hG1c.aestronglyMeasurable _ _ hbG
  have iA : Integrable (fun g => ⟪u, g⟫ * chi ⟪u, g⟫ * G1 g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu (fun t => t * chi t) (measurable_id.mul hchic.measurable) (1 / 4) 1 zero_le_one
      (fun t => by
        rw [abs_mul, one_mul]
        have h := hchi_abs t
        rw [zero_mul, Real.exp_zero, mul_one] at h
        nlinarith [Real.add_one_le_exp |t|, abs_nonneg t, abs_nonneg (chi t)])
      G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have iB : Integrable (fun g => chi' ⟪u, g⟫ * G1 g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu chi' hchi'm (1 / 4) 0 le_rfl hchi'_abs G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have h2' : ∫ g, kr ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, chi ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have hkr : (fun g => kr ⟪u, g⟫ * G1 g) =
        fun g => 1 / 2 * G1 g + (⟪u, g⟫ * chi ⟪u, g⟫ * G1 g - chi' ⟪u, g⟫ * G1 g) := by
      funext g; unfold kr; ring
    have hA : (fun g => ⟪u, g⟫ * chi ⟪u, g⟫ * G1 g) = fun g => ⟪u, g⟫ * (chi ⟪u, g⟫ * G1 g) := by
      funext g; ring
    have iAB : Integrable (fun g => ⟪u, g⟫ * chi ⟪u, g⟫ * G1 g - chi' ⟪u, g⟫ * G1 g)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := iA.sub iB
    rw [hkr, integral_add (iG.const_mul _) iAB, integral_sub iA iB, integral_const_mul, hS1, hA, h2]
    ring
  -- the tail: `E[ζ(t) D_uu G] ≤ lam/2`
  have hzc : Continuous (zeta T) := continuous_iff_continuousAt.2 fun t => (hasDerivAt_zeta T t).continuousAt
  have hz'm : Measurable (zeta' T) := by
    rw [show zeta' T = deriv (zeta T) from funext fun t => (hasDerivAt_zeta T t).deriv.symm]
    exact measurable_deriv _
  have h3 := stein_ramp u hu (zeta T) (zeta' T) (hasDerivAt_zeta T) (2 * (1 + T)) T hT
    (fun t => (zeta_bounds T hT t).2.1) (fun t => (zeta_bounds T hT t).2.2.1) G1 G1' hG1 (L1 + M) 0 hbG hbG'
  have iP : Integrable (fun g => (⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu (fun t => t * zeta T t - zeta' T t) ((measurable_id.mul hzc.measurable).sub hz'm)
      (2 * (1 + T)) (T + 1) (by linarith) (fun t => (zeta_bounds T hT t).2.2.2.2) G1 hG1c.aestronglyMeasurable
      (L1 + M) 0 hbG
  have iZ' : Integrable (fun g => zeta' T ⟪u, g⟫ * G1 g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu (zeta' T) hz'm (2 * (1 + T)) T hT (fun t => (zeta_bounds T hT t).2.2.1) G1
      hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have hsum : ∫ g, (⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
      ∫ g, zeta' T ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ⟪u, g⟫ * (zeta T ⟪u, g⟫ * G1 g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [← integral_add iP iZ']; congr 1; funext g; ring
  have hfc : Continuous fun x : ℝ => (|x| + T) * Real.cosh (T * x) :=
    (continuous_abs.add continuous_const).mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have iF : Integrable (fun g => (|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integrable_of_abs_le_exp _ (hfc.comp hinner).aestronglyMeasurable (1 + T) (T + 1) fun g => ?_
    have hc := Real.cosh_pos (T * ⟪u, g⟫)
    have hct : Real.cosh (T * ⟪u, g⟫) ≤ Real.exp (T * ‖g‖) := by
      have := cosh_le_exp_abs (T * ⟪u, g⟫)
      rw [abs_mul, abs_of_nonneg hT] at this
      exact this.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (ht g) hT))
    have h1 : |⟪u, g⟫| + T ≤ (1 + T) * Real.exp ‖g‖ := by
      nlinarith [ht g, Real.add_one_le_exp ‖g‖, mul_nonneg hT (sub_nonneg.2 (Real.one_le_exp (norm_nonneg g)))]
    rw [abs_of_nonneg (mul_nonneg (by linarith [abs_nonneg ⟪u, g⟫]) hc.le)]
    calc (|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫) ≤ (1 + T) * Real.exp ‖g‖ * Real.exp (T * ‖g‖) :=
          mul_le_mul h1 hct hc.le (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = (1 + T) * Real.exp ((T + 1) * ‖g‖) := by
          rw [show (T + 1) * ‖g‖ = ‖g‖ + T * ‖g‖ by ring, Real.exp_add]; ring
  have hmap : ∫ g, (|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ x, (|x| + T) * Real.cosh (T * x) ∂(gaussianReal 0 1) := by
    rw [← map_inner_stdGaussian u hu, integral_map hinner.aemeasurable hfc.aestronglyMeasurable]
  have htailint : ∫ g, zeta T ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ lam / 2 := by
    have hsub : ∫ g, zeta T ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ g, (⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      linarith [h3, hsum]
    have hle : ∫ g, (⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, L1 * (2 * Real.exp (-T ^ 2) * ((|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫)))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine integral_mono iP ((iF.const_mul _).const_mul _) fun g => ?_
      have hp := (zeta_bounds T hT ⟪u, g⟫).2.2.2.1
      calc (⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g ≤
            |(⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫) * G1 g| := le_abs_self _
        _ = |⟪u, g⟫ * zeta T ⟪u, g⟫ - zeta' T ⟪u, g⟫| * |G1 g| := abs_mul _ _
        _ ≤ 2 * Real.exp (-T ^ 2) * ((|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫)) * L1 :=
            mul_le_mul hp (hL1 g) (abs_nonneg _) ((abs_nonneg _).trans hp)
        _ = L1 * (2 * Real.exp (-T ^ 2) * ((|⟪u, g⟫| + T) * Real.cosh (T * ⟪u, g⟫))) := mul_comm _ _
    rw [integral_const_mul, integral_const_mul, hmap] at hle
    have hexp : Real.exp (-T ^ 2) * Real.exp ((T + 1) ^ 2 / 2) = Real.exp (T + 1 / 2 - T ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsub]
    calc _ ≤ _ := hle
      _ ≤ L1 * (2 * Real.exp (-T ^ 2) * (2 * (1 + T) * Real.exp ((T + 1) ^ 2 / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_cosh_tail T hT) (by positivity)) hL0
      _ = 4 * (1 + T) * L1 * (Real.exp (-T ^ 2) * Real.exp ((T + 1) ^ 2 / 2)) := by ring
      _ = 4 * (1 + T) * L1 * Real.exp (T + 1 / 2 - T ^ 2 / 2) := by rw [hexp]
      _ ≤ lam / 2 := htail
  -- `χ ≥ (1 - ζ)/(4 (1 + T))` and `D_uu G ≥ 0`
  have iD : Integrable (fun g => G1' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_of_abs_le_exp _ hDm.aestronglyMeasurable _ _ hDb
  have iZ : Integrable (fun g => zeta T ⟪u, g⟫ * G1' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu (zeta T) hzc.measurable (2 * (1 + T)) T hT (fun t => (zeta_bounds T hT t).2.1)
      (fun g => G1' g u) hDm.aestronglyMeasurable (L1 + M) 0 hDb
  have iC : Integrable (fun g => chi ⟪u, g⟫ * G1' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_ramp u hu chi hchic.measurable (1 / 4) 0 le_rfl hchi_abs (fun g => G1' g u)
      hDm.aestronglyMeasurable (L1 + M) 0 hDb
  have hmain : ∫ g, 1 / (4 * (1 + T)) * (G1' g u - zeta T ⟪u, g⟫ * G1' g u)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, chi ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integral_mono ((iD.sub iZ).const_mul _) iC fun g => ?_
    have := mul_le_mul_of_nonneg_right (chi_ge_zeta T hT ⟪u, g⟫) (hmono g)
    calc 1 / (4 * (1 + T)) * (G1' g u - zeta T ⟪u, g⟫ * G1' g u) =
          (1 - zeta T ⟪u, g⟫) / (4 * (1 + T)) * G1' g u := by ring
      _ ≤ chi ⟪u, g⟫ * G1' g u := this
  rw [integral_const_mul, integral_sub iD iZ, h1] at hmain
  rw [h2']
  calc lam / (8 * (1 + T)) = 1 / (4 * (1 + T)) * (lam - lam / 2) := by field_simp; ring
    _ ≤ 1 / (4 * (1 + T)) * (lam - ∫ g, zeta T ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg zero_le_one hT1.le)
    _ ≤ _ := hmain

end AdversarialBco.Body
