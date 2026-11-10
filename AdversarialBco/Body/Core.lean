/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Half
public import AdversarialBco.Body.Inf

@[expose] public section

/-!
# Proposition 3.5 at the standard Gaussian

Cauchy and Schwarz, the trace of (S2), the arithmetic of one component and Proposition 3.5 `core_std`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal


theorem AdversarialBco.Body.core_arith (lam d R T X P D0 : ℝ) (hlam : 0 < lam) (hd : 1 ≤ d) (hR : 0 < R)
    (hT : 0 ≤ T) (hX : 0 ≤ X) (h1 : lam * d + lam * R / (8 * (1 + T)) ≤ P + D0)
    (h2 : P ^ 2 ≤ X * (6 * d + 8 * R ^ 2)) :
    (lam * d) ^ 2 ≤ 576 * d ^ 2 * (1 + T) ^ 2 * (X + D0 ^ 2) := by
  set A := 8 * (1 + T) with hA
  have hApos : 0 < A := by linarith
  have hA8 : 8 ≤ A := by linarith
  have hdpos : 0 < d := by linarith
  -- Clear denominator in h1: multiply by A > 0
  have h1_clear : lam * d * A + lam * R ≤ (P + D0) * A := by
    calc
      lam * d * A + lam * R = (lam * d + lam * R / A) * A := by
        field_simp [hApos.ne.symm]
      _ ≤ (P + D0) * A := mul_le_mul_of_nonneg_right h1 (by linarith)
  -- The goal: (lam*d)^2 ≤ (3*A)^2 * d^2 * (X + D0^2)
  -- Since d > 0, cancel d^2
  have hgoal' : lam ^ 2 ≤ (3 * A) ^ 2 * (X + D0 ^ 2) := by
    by_contra! h
    -- h: lam^2 > (3*A)^2 * (X + D0^2)
    set s := lam / (3 * A) with hs
    have hs_pos : 0 < s := div_pos hlam (by linarith)
    have hs_sq_gt : s ^ 2 > X + D0 ^ 2 := by
      dsimp [s]
      rw [div_pow]
      have htemp : lam ^ 2 > (X + D0 ^ 2) * (3 * A) ^ 2 := by linarith
      have h_eq : lam ^ 2 / (3 * A) ^ 2 - (X + D0 ^ 2) = (lam ^ 2 - (X + D0 ^ 2) * (3 * A) ^ 2) / (3 * A) ^ 2 := by
        field_simp [show (3 * A) ^ 2 ≠ 0 from pow_ne_zero 2 (by linarith)]
      have hpos : lam ^ 2 - (X + D0 ^ 2) * (3 * A) ^ 2 > 0 := by linarith
      have hdivpos : 0 < (lam ^ 2 - (X + D0 ^ 2) * (3 * A) ^ 2) / (3 * A) ^ 2 :=
        div_pos hpos (pow_pos (by linarith) 2)
      linarith
    have hD0_sq_nonneg : 0 ≤ D0 ^ 2 := pow_two_nonneg D0
    have hX_lt : X < s ^ 2 := by linarith
    have hD0_sq_lt : D0 ^ 2 < s ^ 2 := by linarith
    have hD0_abs_lt : |D0| < s :=
      abs_lt_of_sq_lt_sq hD0_sq_lt (by linarith)
    have hD0_lt_s : D0 < s := by
      have := abs_lt.mp hD0_abs_lt
      linarith
    -- From h1: lam*d + lam*R/A ≤ P + D0, so P ≥ lam*d + lam*R/A - D0
    have hP_lower : lam * d + lam * R / A - D0 ≤ P := by linarith
    -- Express lam in terms of s: lam = 3*A*s
    have hlam_eq : lam = 3 * A * s := by
      dsimp [s]
      field_simp [hApos.ne.symm]
    have hP_lower2 : 3 * A * s * d + 3 * s * R - s < P := by
      rw [hlam_eq] at hP_lower
      have htemp : (3 * A * s) * R / A = 3 * s * R := by
        field_simp [hApos.ne.symm]
      rw [htemp] at hP_lower
      -- hP_lower: 3*A*s*d + 3*s*R - D0 ≤ P
      -- Since D0 < s: 3*A*s*d + 3*s*R - s < 3*A*s*d + 3*s*R - D0 ≤ P
      have h_lt : 3 * A * s * d + 3 * s * R - s < 3 * A * s * d + 3 * s * R - D0 := by linarith
      linarith
    have h_nonneg : 0 ≤ 3 * A * s * d + 3 * s * R - s := by
      have h1 : 24*s ≤ 3*A*s*d := by
        have : 8 ≤ A := hA8
        have : 1 ≤ d := hd
        nlinarith
      have h2 : 0 ≤ 3*s*R := by positivity
      nlinarith
    have hP_sq_gt : P ^ 2 > s ^ 2 * ((3 * A * d + 3 * R - 1) ^ 2) := by
      have h_sq_lt : (3 * A * s * d + 3 * s * R - s) ^ 2 < P ^ 2 := by
        nlinarith
      have h_eq : (3 * A * s * d + 3 * s * R - s) ^ 2 = s ^ 2 * ((3 * A * d + 3 * R - 1) ^ 2) := by ring
      nlinarith
    have h_ineq : (3 * A * d + 3 * R - 1) ^ 2 ≥ 6 * d + 8 * R ^ 2 := by
      have h_lower : 3 * A * d + 3 * R - 1 ≥ 24 * d + 3 * R - 1 := by nlinarith
      have h_nonneg_target : 0 ≤ 24 * d + 3 * R - 1 := by linarith [hd, hR]
      have h_sq : (24 * d + 3 * R - 1) ^ 2 ≤ (3 * A * d + 3 * R - 1) ^ 2 := by
        have h_le : 24 * d + 3 * R - 1 ≤ 3 * A * d + 3 * R - 1 := by linarith
        have := mul_self_le_mul_self h_nonneg_target h_le
        simpa [pow_two] using this
      have h_target : (24 * d + 3 * R - 1) ^ 2 ≥ 6 * d + 8 * R ^ 2 := by
        have h_expanded : (24 * d + 3 * R - 1) ^ 2 - (6 * d + 8 * R ^ 2) = 576*d^2 + R^2 + 144*d*R - 54*d - 6*R + 1 := by ring
        have h_nonneg_diff : 0 ≤ 576*d^2 + R^2 + 144*d*R - 54*d - 6*R + 1 := by
          have hA : 0 ≤ 576*d^2 - 54*d := by
            have : 576*d^2 - 54*d = d*(576*d - 54) := by ring
            rw [this]
            have hd_nonneg : 0 ≤ d := by linarith
            have hpos : 0 ≤ 576*d - 54 := by linarith
            exact mul_nonneg hd_nonneg hpos
          have hB : 0 ≤ R^2 + 144*d*R - 6*R + 1 := by
            have h_dR : 144*d*R ≥ 144*R := by
              have : 144*d*R - 144*R = 144*R*(d-1) := by ring
              have h_nonneg : 0 ≤ 144*d*R - 144*R := by
                rw [this]
                have hR_nonneg : 0 ≤ 144*R := by linarith
                have hd1 : 0 ≤ d - 1 := by linarith
                exact mul_nonneg hR_nonneg hd1
              linarith
            have hpos : 0 < R^2 + 138*R + 1 := by
              have h1 : 0 < R^2 := pow_pos hR 2
              have h2 : 0 < 138*R := by linarith
              linarith
            linarith
          linarith
        linarith
      linarith
    have h_contra : P ^ 2 > X * (6 * d + 8 * R ^ 2) := by
      have hpos : 0 < 6*d + 8*R^2 := by nlinarith
      have hs_sq_gt_X : s^2 > X := by
        -- hs_sq_gt: s^2 > X + D0^2, and D0^2 ≥ 0
        have hD0_sq_nonneg : 0 ≤ D0^2 := pow_two_nonneg D0
        linarith
      have h1 : P^2 > s^2 * ((3*A*d + 3*R - 1)^2) := hP_sq_gt
      have h_ineq2 : s^2 * ((3*A*d + 3*R - 1)^2) ≥ s^2 * (6*d + 8*R^2) :=
        mul_le_mul_of_nonneg_left h_ineq (pow_two_nonneg s)
      have h3 : s^2 * (6*d + 8*R^2) > X * (6*d + 8*R^2) :=
        mul_lt_mul_of_pos_right hs_sq_gt_X hpos
      have h_mid : s^2 * (6*d + 8*R^2) < P^2 :=
        lt_of_le_of_lt h_ineq2 h1
      exact lt_trans h3 h_mid
    exact lt_irrefl _ (lt_of_lt_of_le h_contra h2)
  -- From hgoal', multiply both sides by d^2 to get the original goal
  have h_main : (lam * d) ^ 2 ≤ (3 * A) ^ 2 * d ^ 2 * (X + D0 ^ 2) := by
    have h_sq_eq : (lam * d) ^ 2 = lam ^ 2 * d ^ 2 := by ring
    have h_goal_eq' : (3 * A) ^ 2 * d ^ 2 * (X + D0 ^ 2) = ((3 * A) ^ 2 * (X + D0 ^ 2)) * d ^ 2 := by
      calc
        (3 * A) ^ 2 * d ^ 2 * (X + D0 ^ 2) = ((3 * A) ^ 2 * d ^ 2) * (X + D0 ^ 2) := rfl
        _ = (3 * A) ^ 2 * (d ^ 2 * (X + D0 ^ 2)) := by rw [mul_assoc]
        _ = (3 * A) ^ 2 * ((X + D0 ^ 2) * d ^ 2) := by rw [mul_comm (d ^ 2) (X + D0 ^ 2)]
        _ = ((3 * A) ^ 2 * (X + D0 ^ 2)) * d ^ 2 := by rw [mul_assoc]
    rw [h_sq_eq, h_goal_eq']
    exact mul_le_mul_of_nonneg_right hgoal' (pow_two_nonneg d)
  have h_goal_eq : (3 * A) ^ 2 = 576 * (1 + T) ^ 2 := by nlinarith
  rw [h_goal_eq] at h_main
  -- h_main: (lam*d)^2 ≤ (576*(1+T)^2) * d^2 * (X + D0^2)
  -- goal: (lam*d)^2 ≤ 576 * d^2 * (1+T)^2 * (X + D0^2)
  have h_reorder : (576 * (1 + T) ^ 2) * d ^ 2 * (X + D0 ^ 2) = 576 * d ^ 2 * (1 + T) ^ 2 * (X + D0 ^ 2) := by ring
  rw [h_reorder] at h_main
  exact h_main

namespace AdversarialBco.Body

/-- Cauchy and Schwarz for integrals, from the discriminant of `∫ (t f - h)^2`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f h : α → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ) (hh : Integrable (fun x => h x ^ 2) μ)
    (hfh : Integrable (fun x => f x * h x) μ) :
    (∫ x, f x * h x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, h x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, f x * h x ∂μ) * t + ∫ x, h x ^ 2 ∂μ := by
    intro t
    have i1 : Integrable (fun x => t ^ 2 * f x ^ 2 - 2 * t * (f x * h x)) μ :=
      (hf.const_mul _).sub (hfh.const_mul _)
    have e : ∫ x, (t * f x - h x) ^ 2 ∂μ =
        (∫ x, f x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, f x * h x ∂μ) * t + ∫ x, h x ^ 2 ∂μ := by
      rw [show (fun x => (t * f x - h x) ^ 2) = fun x => t ^ 2 * f x ^ 2 - 2 * t * (f x * h x) + h x ^ 2 from
        funext fun x => by ring, integral_add i1 hh, integral_sub (hf.const_mul _) (hfh.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [← e]; exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith [this]

/-- (S2) traced: `E[G'(g) g] = lam d`. -/
theorem integral_fderiv_self {d : ℕ} (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hG'm : Measurable G') (L1 : ℝ) (hb : ∀ g, ‖G' g‖ ≤ L1) (lam : ℝ)
    (hS2 : ∀ v v', ∫ g, ⟪v, g⟫ * G' g v' ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫) :
    ∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * d := by
  have e : ∀ g : EuclideanSpace ℝ (Fin d), G' g g =
      ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * G' g (EuclideanSpace.single i 1) := fun g => by
    have hg : (∑ i, g i • EuclideanSpace.single i (1 : ℝ)) = g := by
      have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr g
      simpa using this
    calc G' g g = G' g (∑ i, g i • EuclideanSpace.single i (1 : ℝ)) := by rw [hg]
      _ = ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * G' g (EuclideanSpace.single i 1) := by
          rw [map_sum]; simp [map_smul, EuclideanSpace.inner_single_left]
  have hi : ∀ i : Fin d, Integrable (fun g => ⟪EuclideanSpace.single i (1 : ℝ), g⟫ *
      G' g (EuclideanSpace.single i 1)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun i => by
    refine integrable_of_abs_le_exp _ (((continuous_const.inner continuous_id).measurable.mul
      (hG'm.apply_continuousLinearMap _)).aestronglyMeasurable) |L1| 1 fun g => ?_
    rw [abs_mul, one_mul]
    have h1 : |⟪EuclideanSpace.single i (1 : ℝ), g⟫| ≤ ‖g‖ := by
      simpa using abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) g
    have h2 : |G' g (EuclideanSpace.single i 1)| ≤ |L1| := by
      rw [← Real.norm_eq_abs]
      exact ((G' g).le_opNorm _).trans (by simpa using (hb g).trans (le_abs_self L1))
    calc |⟪EuclideanSpace.single i (1 : ℝ), g⟫| * |G' g (EuclideanSpace.single i 1)| ≤ Real.exp ‖g‖ * |L1| :=
          mul_le_mul (h1.trans (by linarith [Real.add_one_le_exp ‖g‖])) h2 (abs_nonneg _) (Real.exp_pos _).le
      _ = |L1| * Real.exp ‖g‖ := mul_comm _ _
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => hi i, Finset.sum_congr rfl fun i _ => hS2 _ _]
  simp [EuclideanSpace.inner_single_left]
  try ring

/-- Proposition 3.5 at the standard Gaussian, for some constant `K0`; the proof takes `K0 = 576`, through `core_arith`. -/
theorem core_std : ∃ K0 : ℝ, 0 < K0 ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (k : ℕ) (w : Fin k → ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ)
    (F' : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (G'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (L L1 M lam T : ℝ) (y : Fin k → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin k)),
    (∀ c, 0 ≤ w c) → (∀ c g, HasFDerivAt (F c) (F' c g) g) → (∀ c, ConvexOn ℝ Set.univ (F c)) →
    (∀ c g, ‖F' c g‖ ≤ L) → (∀ g, HasFDerivAt G (G' g) g) → (∀ g, HasFDerivAt G' (G'' g) g) →
    (∀ g, ‖G' g‖ ≤ L1) → (∀ g, ‖G'' g‖ ≤ M) → (∀ g v, 0 ≤ G'' g v v) →
    (∀ v, ∫ g, G' g v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0) →
    (∀ v v', ∫ g, ⟪v, g⟫ * G' g v' ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫) →
    G 0 ≤ ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) → 0 < lam → 0 ≤ T →
    4 * (1 + T) * L1 * Real.exp (T + 1 / 2 - T ^ 2 / 2) ≤ lam / 2 →
    (∀ c ∈ S, F c (y c) ≤ F c 0 - 4 * lam * (d : ℝ)) →
    (∑ c ∈ S, w c) * (lam * (d : ℝ)) ^ 2 ≤
      K0 * (d : ℝ) ^ 2 * (1 + T) ^ 2 *
        (∫ g, ∑ c ∈ S, w c * (F c g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
          ∑ c ∈ S, w c * (F c 0 - G 0) ^ 2) := by
  refine ⟨576, by norm_num, ?_⟩
  intro d hd k w F F' G G' G'' L L1 M lam T y S hw hF hFc hFL hG hG' hGL1 hGM hGpos hS1 hS2 hS4 hlam hT htail
    hgain
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (G'' 0)) (hGM 0)
  have hG'm : Measurable G' := by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]; exact measurable_fderiv ℝ G
  have hGsd := integral_fderiv_self G' hG'm L1 hGL1 lam hS2
  have hGcont : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hDc : ∀ c, Continuous fun g => F c g - G g := fun c =>
    (continuous_iff_continuousAt.2 fun g => (hF c g).continuousAt).sub hGcont
  have hDb1 : ∀ c g, |F c g - G g| ≤ (|F c 0 - G 0| + |L + L1|) * Real.exp (1 * ‖g‖) := by
    intro c g
    have hD : ∀ g, HasFDerivAt (fun g => F c g - G g) (F' c g - G' g) g := fun g => (hF c g).sub (hG g)
    have hDb' : ∀ g, ‖F' c g - G' g‖ ≤ L + L1 := fun g =>
      (norm_sub_le _ _).trans (add_le_add (hFL c g) (hGL1 g))
    have := (abs_le_of_norm_fderiv_le _ _ hD (L + L1) hDb' g).1
    beta_reduce at this
    exact this
  have hDsq : ∀ c, Integrable (fun g => (F c g - G g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro c
    have hD : ∀ g, HasFDerivAt (fun g => F c g - G g) (F' c g - G' g) g := fun g => (hF c g).sub (hG g)
    have hDb' : ∀ g, ‖F' c g - G' g‖ ≤ L + L1 := fun g =>
      (norm_sub_le _ _).trans (add_le_add (hFL c g) (hGL1 g))
    have hDb := fun g => (abs_le_of_norm_fderiv_le _ _ hD (L + L1) hDb' g).1
    have hDc : Continuous fun g => F c g - G g :=
      (continuous_iff_continuousAt.2 fun g => (hF c g).continuousAt).sub hGcont
    refine integrable_of_abs_le_exp _ (hDc.pow 2).aestronglyMeasurable
      ((|F c 0 - G 0| + |L + L1|) ^ 2) 2 fun g => ?_
    have := hDb g
    beta_reduce at this
    rw [abs_pow, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + 1 * ‖g‖ by ring, Real.exp_add]
    nlinarith [abs_nonneg (F c g - G g)]
  have hone : ∀ c ∈ S, (lam * d) ^ 2 ≤ 576 * d ^ 2 * (1 + T) ^ 2 *
      (∫ g, (F c g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + (F c 0 - G 0) ^ 2) := by
    intro c hc
    have hyc := hgain c hc
    have hR : 0 < ‖y c‖ := by
      rcases (norm_nonneg (y c)).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [norm_eq_zero.1 h.symm] at hyc
        nlinarith
    set R := ‖y c‖ with hRdef
    set u := R⁻¹ • y c with hudef
    have hu : ‖u‖ = 1 := by rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hR.ne']
    have hRu : R • u = y c := by rw [hudef, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    have hΓ : F c (R • u) ≤ F c 0 - 4 * lam * d := by rw [hRu]; exact hyc
    have hinf := inf_one (F c) G (F' c) G' (hF c) hG (hFc c) L L1 (hFL c) hGL1 u hu R (4 * lam * d) hR hΓ
    -- Lemma 3.4 for `G1 = D_u G`
    have hG1 : ∀ g, HasFDerivAt (fun g => G' g u) ((ContinuousLinearMap.apply ℝ ℝ u).comp (G'' g)) g :=
      fun g => (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp g (hG' g)
    have hhalf := half_one u hu (fun g => G' g u) (fun g => (ContinuousLinearMap.apply ℝ ℝ u).comp (G'' g)) hG1
      L1 M (fun g => by
        rw [← Real.norm_eq_abs]; exact ((G' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hGL1 g))
      (fun g => by
        refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun v => ?_
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
        calc ‖G'' g v u‖ ≤ ‖G'' g v‖ * ‖u‖ := (G'' g v).le_opNorm u
          _ ≤ ‖G'' g‖ * ‖v‖ * 1 := by rw [hu]; gcongr; exact (G'' g).le_opNorm v
          _ ≤ M * ‖v‖ := by rw [mul_one]; gcongr; exact hGM g)
      (fun g => by simpa using hGpos g u) lam T hT (hS1 u)
      (by rw [hS2 u u, real_inner_self_eq_norm_sq, hu]; ring) htail
    -- Cauchy and Schwarz on the score
    set X := ∫ g, (F c g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    set I := ∫ g, (F c g - G g) * ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    have hQ := score_sq_le u hu R hR
    have hCS : I ^ 2 ≤ X * ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine sq_integral_mul_le _ _ _ (hDsq c) ?_ ?_
      · exact (integrable_score u hu R hR _ (hDc c).aestronglyMeasurable _ (hDb1 c)).1
      · exact (integrable_score u hu R hR _ (hDc c).aestronglyMeasurable _ (hDb1 c)).2
    have hX0 : 0 ≤ X := integral_nonneg fun g => sq_nonneg _
    have hQ0 : 0 ≤ ∫ g, ((‖g‖ ^ 2 - (d : ℝ)) / R - kr ⟪u, g⟫ * ⟪u, g⟫ + kr' ⟪u, g⟫ - 1 / R) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := integral_nonneg fun g => sq_nonneg _
    have hP : (R * I) ^ 2 ≤ X * (6 * d + 8 * R ^ 2) := by
      have h6 : R ^ 2 * (2 * (2 * (d : ℝ) + 1) / R ^ 2 + 8) ≤ 6 * d + 8 * R ^ 2 := by
        rw [mul_add, mul_div_cancel₀ _ (by positivity : R ^ 2 ≠ 0)]; nlinarith
      calc (R * I) ^ 2 = R ^ 2 * I ^ 2 := by ring
        _ ≤ R ^ 2 * (X * (2 * (2 * (d : ℝ) + 1) / R ^ 2 + 8)) :=
            mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul_of_nonneg_left hQ hX0)) (by positivity)
        _ = X * (R ^ 2 * (2 * (2 * (d : ℝ) + 1) / R ^ 2 + 8)) := by ring
        _ ≤ X * (6 * d + 8 * R ^ 2) := mul_le_mul_of_nonneg_left h6 hX0
    have h1 : lam * d + lam * R / (8 * (1 + T)) ≤ R * I + (F c 0 - G 0) := by
      have hT1 : 0 < 8 * (1 + T) := by linarith
      have hb : (∫ g, G' g g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + G 0) / R ≤ lam * d / R := by
        rw [hGsd]; exact div_le_div_of_nonneg_right (by linarith) hR.le
      have hmain : lam * d / R + lam / (8 * (1 + T)) ≤ I + (F c 0 - G 0) / R := by
        have e : 4 * lam * d / (2 * R) = 2 * (lam * d / R) := by field_simp; ring
        linarith [hinf, hhalf, hb, e]
      have := mul_le_mul_of_nonneg_left hmain hR.le
      have e1 : R * (lam * d / R + lam / (8 * (1 + T))) = lam * d + lam * R / (8 * (1 + T)) := by
        field_simp
      have e2 : R * (I + (F c 0 - G 0) / R) = R * I + (F c 0 - G 0) := by field_simp
      linarith
    exact core_arith lam d R T X (R * I) (F c 0 - G 0) hlam hdR hR hT hX0 h1 hP
  -- the weighted sum over the good set
  have hint : ∫ g, ∑ c ∈ S, w c * (F c g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∑ c ∈ S, w c * ∫ g, (F c g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [integral_finset_sum _ fun c _ => (hDsq c).const_mul _]
    exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
  rw [hint, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun c hc => ?_
  have := mul_le_mul_of_nonneg_left (hone c hc) (hw c)
  linarith

end AdversarialBco.Body
