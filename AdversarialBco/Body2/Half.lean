/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Ibp
public import AdversarialBco.Body2.Gauss2
public import AdversarialBco.Body2.Arith
public import AdversarialBco.Body.Inf
public import AdversarialBco.Body.Convex
public import AdversarialBco.Body.Core
public import AdversarialBco.StatementBody

@[expose] public section

/-!
# Lemma 3.4 (the second-order term) in the coordinates of the standard Gaussian

`G1` plays `∂_u Fbar(b + S ·)` and `G1' g u ≥ 0` the convexity of `Fbar` in the direction
`u`. With the kernel `W = K/φ` of the paper, Stein's identity gives `E[k(Z_u) G1] = E[W(Z_u) ∂_u G1]`; the bound
`W ≥ κ M(T) (1 - φ(T)/φ)_+` and Stein's identity for `(1 - φ(T)/φ)_+` give `E[k(Z_u) G1] ≥ κ M(T) E[Z_u 1{|Z_u| < T} G1]`,
and the tail `E[|Z_u|; |Z_u| ≥ T] = 2 φ(T)` concludes, with no disintegration of the Gaussian.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec (phi Qtail kappa kappa2)

theorem phi_pos (t : ℝ) : 0 < phi t := by
  unfold phi; positivity

theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (-(t * phi t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2) / 2) (-t) t :=
    (((hasDerivAt_pow 2 t).neg).div_const 2).congr_deriv (by rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
  have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  show HasDerivAt (fun t => Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)) (-(t * phi t)) t
  convert h2 using 1
  unfold phi; ring

theorem Qtail_nonneg (t : ℝ) : 0 ≤ Qtail t :=
  setIntegral_nonneg measurableSet_Ioi fun s _ => (phi_pos s).le

theorem kfun_mem (t : ℝ) : 0 ≤ kfun t ∧ kfun t ≤ 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

theorem continuous_kfun : Continuous kfun := (continuous_id.max continuous_const).min continuous_const

/-- `φ(T)/φ(t) < 1` exactly when `|t| > T`... and `φ(t) > φ(T)` exactly when `|t| < T`, for `T ≥ 0`. -/
theorem phi_lt_iff (T t : ℝ) (hT : 0 ≤ T) : phi T < phi t ↔ |t| < T := by
  unfold phi
  rw [div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 (by positivity)), Real.exp_lt_exp]
  constructor
  · intro h
    have : t ^ 2 < T ^ 2 := by linarith
    exact abs_lt_of_sq_lt_sq this hT
  · intro h
    have : t ^ 2 < T ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 h).1 (abs_lt.1 h).2
      simpa using this
    linarith

/-- Lemma 3.4 at the standard Gaussian. -/
theorem half_std {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G1 : EuclideanSpace ℝ (Fin d) → ℝ)
    (G1' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG1 : ∀ g, HasFDerivAt G1 (G1' g) g)
    (L1 M : ℝ) (hL1 : ∀ g, |G1 g| ≤ L1) (hM : ∀ g, ‖G1' g‖ ≤ M) (hmono : ∀ g, 0 ≤ G1' g u) (lam T : ℝ)
    (hT : 0 ≤ T) (hS1 : ∫ g, G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0)
    (hS2 : ∫ g, ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam) :
    kappa * (Qtail T / phi T) * (lam - 2 * L1 * phi T) ≤
      ∫ g, kfun ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨hκ0, hκ1, -, -⟩ := kappa_bounds
  have hL0 : 0 ≤ L1 := (abs_nonneg _).trans (hL1 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hG1c : Continuous G1 := continuous_iff_continuousAt.2 fun g => (hG1 g).continuousAt
  have hDm : Measurable fun g => G1' g u := by
    rw [show G1' = fderiv ℝ G1 from funext fun g => (hG1 g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G1 u
  have hbG : ∀ g, |G1 g| ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [zero_mul, Real.exp_zero, mul_one]; linarith [hL1 g]
  have hbG' : ∀ g, ‖G1' g‖ ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [zero_mul, Real.exp_zero, mul_one]; linarith [hM g]
  have hbD : ∀ g, |G1' g u| ≤ (L1 + M) * Real.exp (0 * ‖g‖) := fun g => by
    rw [← Real.norm_eq_abs]; exact ((G1' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hbG' g)
  have hphic : Continuous phi := continuous_iff_continuousAt.2 fun t => (hasDerivAt_phi t).continuousAt
  -- Stein's identity for `W = K/φ`: `E[W(Z_u) ∂_u G1] = E[k(Z_u) G1]`
  set W : ℝ → ℝ := fun t => Kker t / phi t with hWdef
  set W' : ℝ → ℝ := fun t => t * W t - (kfun t - kappa) with hW'def
  have hW : ∀ t, HasDerivAt W (W' t) t := fun t => hasDerivAt_Wfun t
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hW'c : Continuous W' := (continuous_id.mul hWc).sub (continuous_kfun.sub continuous_const)
  have hWb2 : ∀ t, 0 ≤ W t ∧ W t ≤ 2 := fun t => Wfun_bounds t
  have hWb : ∀ t, |W t| ≤ 3 * Real.exp (1 * |t|) := fun t => by
    have h1 : (1 : ℝ) ≤ Real.exp (1 * |t|) := Real.one_le_exp (by positivity)
    rw [abs_of_nonneg (hWb2 t).1]; linarith [(hWb2 t).2]
  have hW'b : ∀ t, |W' t| ≤ 3 * Real.exp (1 * |t|) := fun t => by
    have he := Real.add_one_le_exp |t|
    have hk := kfun_mem t
    have h1 : |t * W t| ≤ |t| * 2 := by
      rw [abs_mul, abs_of_nonneg (hWb2 t).1]; exact mul_le_mul_of_nonneg_left (hWb2 t).2 (abs_nonneg _)
    have h2 : |kfun t - kappa| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |W' t| ≤ |t * W t| + |kfun t - kappa| := abs_sub_le' _ _
      _ ≤ |t| * 2 + 1 := add_le_add h1 h2
      _ ≤ 3 * Real.exp (1 * |t|) := by rw [one_mul]; nlinarith [abs_nonneg t]
  have hstein := AdversarialBco.Body.stein_ramp u hu W W' hW 3 1 zero_le_one hWb hW'b G1 G1' hG1 (L1 + M) 0
    hbG hbG'
  have iA : Integrable (fun g => ⟪u, g⟫ * (W ⟪u, g⟫ * G1 g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (AdversarialBco.Body.integrable_ramp u hu (fun t => t * W t) (continuous_id.mul hWc).measurable 2 1
      zero_le_one (fun t => by
        have he := Real.add_one_le_exp |t|
        rw [abs_mul, abs_of_nonneg (hWb2 t).1, one_mul]
        nlinarith [abs_nonneg t, (hWb2 t).1, (hWb2 t).2])
      G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG).congr (Eventually.of_forall fun g => by simp only; ring)
  have iB : Integrable (fun g => W' ⟪u, g⟫ * G1 g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu W' hW'c.measurable 3 1 zero_le_one hW'b G1
      hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have iC : Integrable (fun g => W ⟪u, g⟫ * G1' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu W hWc.measurable 3 1 zero_le_one hWb (fun g => G1' g u)
      hDm.aestronglyMeasurable (L1 + M) 0 hbD
  have iK : Integrable (fun g => kfun ⟪u, g⟫ * G1 g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu kfun continuous_kfun.measurable 1 0 le_rfl (fun t => by
      rw [zero_mul, Real.exp_zero, mul_one, abs_of_nonneg (kfun_mem t).1]; exact (kfun_mem t).2)
      G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have hWD : ∫ g, W ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, kfun ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have e1 : ∫ g, W ⟪u, g⟫ * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ g, (⟪u, g⟫ * (W ⟪u, g⟫ * G1 g) - W' ⟪u, g⟫ * G1 g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      rw [integral_sub iA iB, hstein]; ring
    have e2 : (fun g => ⟪u, g⟫ * (W ⟪u, g⟫ * G1 g) - W' ⟪u, g⟫ * G1 g) =
        fun g => kfun ⟪u, g⟫ * G1 g - kappa * G1 g := by
      funext g; simp only [hW'def]; ring
    rw [e1, e2, integral_sub iK ((AdversarialBco.Body.integrable_of_abs_le_exp _ hG1c.aestronglyMeasurable (L1 + M) 0 hbG).const_mul kappa),
      integral_const_mul, hS1, mul_zero, sub_zero]
  -- the profile `ρ = 1 - φ(T)/φ`, positive exactly on `|t| < T`
  set r : ℝ → ℝ := fun t => phi T / phi t with hrdef
  have hrpos : ∀ t, 0 < r t := fun t => div_pos (phi_pos T) (phi_pos t)
  have hr : ∀ t, HasDerivAt r (t * r t) t := fun t => by
    have := (hasDerivAt_const t (phi T)).div (hasDerivAt_phi t) (phi_pos t).ne'
    convert this using 1
    simp only [hrdef]; field_simp; ring
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun t => (hr t).continuousAt
  have hρ : ∀ t, HasDerivAt (fun t => 1 - r t) (-(t * r t)) t := fun t => (hr t).const_sub 1
  have hρ'c : Continuous fun t => -(t * r t) := (continuous_id.mul hrc).neg
  have hpos_iff : ∀ t, 0 < 1 - r t ↔ |t| < T := fun t => by
    rw [sub_pos, ← phi_lt_iff T t hT]; simp only [hrdef]
    rw [div_lt_one (phi_pos t)]
  have hρb : ∀ t, max (1 - r t) 0 ≤ (1 + T) * Real.exp (0 * |t|) := fun t => by
    rw [zero_mul, Real.exp_zero, mul_one]
    exact max_le (by linarith [hrpos t]) (by linarith)
  have hρb' : ∀ t, 0 < 1 - r t → |-(t * r t)| ≤ (1 + T) * Real.exp (0 * |t|) := fun t ht => by
    rw [zero_mul, Real.exp_zero, mul_one, abs_neg, abs_mul, abs_of_pos (hrpos t)]
    have h1 : r t < 1 := by linarith
    have h2 : |t| < T := (hpos_iff t).1 ht
    nlinarith [abs_nonneg t, hrpos t]
  have hpp := stein_posPart u hu G1 G1' hG1 (L1 + M) 0 hbG hbG' (fun t => 1 - r t) (fun t => -(t * r t)) hρ hρ'c
    (1 + T) 0 le_rfl hρb hρb'
  have hpp' : ∫ g, max (1 - r ⟪u, g⟫) 0 * G1' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ * G1 g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hpp]
    congr 1; funext g
    by_cases h : 0 < 1 - r ⟪u, g⟫
    · rw [ite_eq_left h, ite_eq_left h, max_eq_left h.le]; ring
    · rw [ite_eq_right h, ite_eq_right h, max_eq_right (not_lt.1 h)]; ring
  -- the kernel bound `W ≥ κ M(T) ρ_+`
  have hmin : ∀ x : ℝ, 1 - min 1 x = max (1 - x) 0 := fun x => by
    rcases le_total x 1 with h | h
    · rw [min_eq_right h, max_eq_left (by linarith)]
    · rw [min_eq_left h, max_eq_right (by linarith), sub_self]
  set cM := kappa * (Qtail T / phi T) with hcM
  have hcM0 : 0 ≤ cM := mul_nonneg (by linarith) (div_nonneg (Qtail_nonneg T) (phi_pos T).le)
  have hWge : ∀ t, cM * max (1 - r t) 0 ≤ W t := fun t => by
    have := Wfun_ge T t hT; rw [hmin] at this; exact this
  have iE : Integrable (fun g => max (1 - r ⟪u, g⟫) 0 * G1' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu (fun t => max (1 - r t) 0)
      ((continuous_const.sub hrc).max continuous_const).measurable (1 + T) 0 le_rfl
      (fun t => by rw [abs_of_nonneg (le_max_right _ _)]; exact hρb t)
      (fun g => G1' g u) hDm.aestronglyMeasurable (L1 + M) 0 hbD
  have hlow : cM * ∫ g, (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ * G1 g else 0)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, kfun ⟪u, g⟫ * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [← hpp', ← hWD, ← integral_const_mul]
    refine integral_mono (iE.const_mul cM) iC fun g => ?_
    simp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hWge _) (hmono g)
  -- the tail: `E[Z_u 1{|Z_u| ≥ T} G1] ≤ 2 L1 φ(T)`
  have hite1 : Measurable fun t : ℝ => if 0 < 1 - r t then t else 0 :=
    Measurable.ite (measurableSet_lt measurable_const (continuous_const.sub hrc).measurable) measurable_id
      measurable_const
  have hite2 : Measurable fun t : ℝ => if 0 < 1 - r t then 0 else t :=
    Measurable.ite (measurableSet_lt measurable_const (continuous_const.sub hrc).measurable) measurable_const
      measurable_id
  have hid : ∀ t : ℝ, |t| ≤ 1 * Real.exp (1 * |t|) := fun t => by
    rw [one_mul, one_mul]; linarith [Real.add_one_le_exp |t|]
  have iP : Integrable (fun g => (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ else 0) * G1 g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu _ hite1 1 1 zero_le_one (fun t => by
      split_ifs
      · exact hid t
      · rw [abs_zero]; positivity) G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have iN : Integrable (fun g => (if 0 < 1 - r ⟪u, g⟫ then 0 else ⟪u, g⟫) * G1 g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu _ hite2 1 1 zero_le_one (fun t => by
      split_ifs
      · rw [abs_zero]; positivity
      · exact hid t) G1 hG1c.aestronglyMeasurable (L1 + M) 0 hbG
  have hsplit : ∫ g, (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ * G1 g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      lam - ∫ g, (if 0 < 1 - r ⟪u, g⟫ then 0 else ⟪u, g⟫) * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have e : (fun g => ⟪u, g⟫ * G1 g) = fun g => (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ else 0) * G1 g +
        (if 0 < 1 - r ⟪u, g⟫ then 0 else ⟪u, g⟫) * G1 g := by
      funext g; split_ifs <;> ring
    rw [← hS2, e, integral_add iP iN, add_sub_cancel_right]
    congr 1; funext g; split_ifs <;> ring
  have htf : Measurable fun t : ℝ => if T ≤ |t| then |t| else 0 :=
    Measurable.ite (measurableSet_le measurable_const measurable_abs) measurable_abs measurable_const
  have iT : Integrable (fun g => (if T ≤ |⟪u, g⟫| then |⟪u, g⟫| else 0) * L1)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu _ htf 1 1 zero_le_one (fun t => by
      split_ifs
      · rw [abs_abs]; exact hid t
      · rw [abs_zero]; positivity) (fun _ => L1) aestronglyMeasurable_const L1 0
      (fun g => by rw [zero_mul, Real.exp_zero, mul_one, abs_of_nonneg hL0])
  have htail1 : ∫ g, (if 0 < 1 - r ⟪u, g⟫ then 0 else ⟪u, g⟫) * G1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, (if T ≤ |⟪u, g⟫| then |⟪u, g⟫| else 0) * L1 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine integral_mono iN iT fun g => ?_
    simp only
    by_cases h : 0 < 1 - r ⟪u, g⟫
    · rw [ite_eq_left h, zero_mul]
      split_ifs <;> positivity
    · have hT' : T ≤ |⟪u, g⟫| := not_lt.1 fun h' => h ((hpos_iff _).2 h')
      rw [ite_eq_right h, ite_eq_left hT']
      calc ⟪u, g⟫ * G1 g ≤ |⟪u, g⟫ * G1 g| := le_abs_self _
        _ = |⟪u, g⟫| * |G1 g| := abs_mul _ _
        _ ≤ |⟪u, g⟫| * L1 := mul_le_mul_of_nonneg_left (hL1 g) (abs_nonneg _)
  have htail2 : ∫ g, (if T ≤ |⟪u, g⟫| then |⟪u, g⟫| else 0) * L1 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      2 * L1 * phi T := by
    have hmap : ∫ g, (if T ≤ |⟪u, g⟫| then |⟪u, g⟫| else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ t, (if T ≤ |t| then |t| else 0) ∂(gaussianReal 0 1) := by
      rw [← AdversarialBco.Body.map_inner_stdGaussian u hu,
        integral_map hinner.aemeasurable htf.aestronglyMeasurable]
    have hae : ∫ t, (if T ≤ |t| then |t| else 0) * phi t = ∫ t, (if T < |t| then |t| else 0) * phi t := by
      refine integral_congr_ae ?_
      have hnull : (volume : Measure ℝ) ({T, -T} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
      have : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({T, -T} : Set ℝ) := by
        exact measure_eq_zero_iff_ae_notMem.1 hnull
      filter_upwards [this] with t ht
      have h1 : |t| ≠ T := fun h => by
        rcases abs_eq hT |>.1 h with h' | h' <;> simp [h'] at ht
      by_cases h2 : T < |t|
      · rw [ite_eq_left h2.le, ite_eq_left h2]
      · rw [ite_eq_right (fun h => h2 (lt_of_le_of_ne h (Ne.symm h1))), ite_eq_right h2]
    rw [integral_mul_const, hmap, integral_gaussianReal_phi, hae, integral_abs_tail T hT]; ring
  calc cM * (lam - 2 * L1 * phi T) ≤ cM * ∫ g, (if 0 < 1 - r ⟪u, g⟫ then ⟪u, g⟫ * G1 g else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [hsplit]; exact mul_le_mul_of_nonneg_left (by linarith [htail1, htail2]) hcM0
    _ ≤ _ := hlow

/-- An integral of a function of `⟪u, g⟫` is an integral against `N(0, 1)`. -/
theorem integral_inner_eq {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ g, f ⟪u, g⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ∫ t, f t * phi t := by
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  rw [← integral_gaussianReal_phi, ← AdversarialBco.Body.map_inner_stdGaussian u hu,
    integral_map hinner.aemeasurable hf.aestronglyMeasurable]

/-- `E k(Z_u) = κ`. -/
theorem integral_kfun_inner {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∫ g, kfun ⟪u, g⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = kappa := by
  rw [integral_inner_eq u hu kfun continuous_kfun.measurable]; exact integral_min_pos_phi

/-- `P(Z_u > 0) = 1/2`. -/
theorem integral_ind_inner {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∫ g, (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 1 / 2 := by
  rw [integral_inner_eq u hu (fun t => if 0 < t then (1 : ℝ) else 0)
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const),
    ← integral_phi_Ioi_zero, ← integral_indicator measurableSet_Ioi]
  congr 1; funext t
  simp only [Set.indicator, Set.mem_Ioi]; split_ifs <;> ring

/-- Integrability of `1{⟪u, g⟫ > 0} X(g)` for `X` of exponential growth. -/
theorem integrable_ind {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (X : EuclideanSpace ℝ (Fin d) → ℝ)
    (hX : AEStronglyMeasurable X (stdGaussian (EuclideanSpace ℝ (Fin d)))) (A B : ℝ)
    (hXb : ∀ g, |X g| ≤ A * Real.exp (B * ‖g‖)) :
    Integrable (fun g => if 0 < ⟪u, g⟫ then X g else 0) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (AdversarialBco.Body.integrable_ramp u hu (fun t => if 0 < t then (1 : ℝ) else 0)
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const) 1 0 le_rfl
    (fun t => by split_ifs <;> simp) X hX A B hXb).congr
    (Eventually.of_forall fun g => by simp only; split_ifs <;> ring)

/-- Lemma 3.3 ((3.4), combined with the same identity for the mean) at the standard Gaussian, for one
component `F` with minimiser direction `u`, depth `R` and gap `Γ`; `τ = 1/R` and `B = 1`. -/
theorem inf_std {d : ℕ} (F G : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hF : ∀ g, HasFDerivAt F (F' g) g)
    (hG : ∀ g, HasFDerivAt G (G' g) g) (hFc : ConvexOn ℝ Set.univ F) (LF LG : ℝ) (hF' : ∀ g, ‖F' g‖ ≤ LF)
    (hG' : ∀ g, ‖G' g‖ ≤ LG) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R Γ : ℝ) (hR : 0 < R)
    (hΓ : F (R • u) ≤ F 0 - Γ) :
    Γ / R * kappa + ∫ g, kfun ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        (∫ g, (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / R ≤
      ∫ g, (F g - G g) * (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - kfun ⟪u, g⟫ * ⟪u, g⟫ +
          (if ⟪u, g⟫ < 1 then 1 else 0) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        (F 0 - G 0) / (2 * R) := by
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hFc' : Continuous F := continuous_iff_continuousAt.2 fun g => (hF g).continuousAt
  have hGc' : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hFb := fun g => AdversarialBco.Body.abs_le_of_norm_fderiv_le F F' hF LF hF' g
  have hGb := fun g => AdversarialBco.Body.abs_le_of_norm_fderiv_le G G' hG LG hG' g
  set AF := |F 0| + |LF| with hAF
  set AG := |G 0| + |LG| with hAG
  have hAF0 : 0 ≤ AF := by positivity
  have hAG0 : 0 ≤ AG := by positivity
  have aF := ibp_a u hu F F' hF AF 1 (fun g => (hFb g).1) (fun g => (hFb g).2)
  have aG := ibp_a u hu G G' hG AG 1 (fun g => (hGb g).1) (fun g => (hGb g).2)
  have bF := ibp_b u hu F F' hF AF 1 (fun g => (hFb g).1) (fun g => (hFb g).2) 1 zero_le_one
  have bG := ibp_b u hu G G' hG AG 1 (fun g => (hGb g).1) (fun g => (hGb g).2) 1 zero_le_one
  -- integrability
  have hsq : ∀ (A : ℝ) (H : EuclideanSpace ℝ (Fin d) → ℝ), 0 ≤ A → (∀ g, |H g| ≤ A * Real.exp (1 * ‖g‖)) →
      ∀ g, |H g * (‖g‖ ^ 2 - (d : ℝ))| ≤ A * (1 + d) * Real.exp ((1 + 2) * ‖g‖) := fun A H hA hH g =>
    sq_exp_bound A 1 d ‖g‖ (H g) hA (Nat.cast_nonneg d) (norm_nonneg g) (hH g)
  have hnc : Continuous fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 - (d : ℝ) := by fun_prop
  have i1 := integrable_ind u hu (fun g => F g * (‖g‖ ^ 2 - (d : ℝ))) (hFc'.mul hnc).aestronglyMeasurable _ _
    (hsq AF F hAF0 fun g => (hFb g).1)
  have i2 := integrable_ind u hu (fun g => G g * (‖g‖ ^ 2 - (d : ℝ))) (hGc'.mul hnc).aestronglyMeasurable _ _
    (hsq AG G hAG0 fun g => (hGb g).1)
  have hψm : Measurable fun t : ℝ => kfun t * t - (if 0 < t ∧ t < 1 then 1 else 0) :=
    (continuous_kfun.mul continuous_id).measurable.sub (Measurable.ite
      ((measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const))
      measurable_const measurable_const)
  have hψb : ∀ t : ℝ, |kfun t * t - (if 0 < t ∧ t < 1 then 1 else 0)| ≤ 2 * Real.exp (1 * |t|) := fun t => by
    have he := Real.add_one_le_exp |t|
    have h1 : |kfun t * t| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg (kfun_mem t).1]; exact mul_le_of_le_one_left (abs_nonneg _) (kfun_mem t).2
    have h2 : |(if 0 < t ∧ t < 1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have := abs_sub_le' (kfun t * t) (if 0 < t ∧ t < 1 then (1 : ℝ) else 0)
    rw [one_mul]; nlinarith [abs_nonneg t]
  have i3 : Integrable (fun g => F g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (AdversarialBco.Body.integrable_ramp u hu _ hψm 2 1 zero_le_one hψb F hFc'.aestronglyMeasurable AF 1
      (fun g => (hFb g).1)).congr (Eventually.of_forall fun g => by simp only; ring)
  have i4 : Integrable (fun g => G g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (AdversarialBco.Body.integrable_ramp u hu _ hψm 2 1 zero_le_one hψb G hGc'.aestronglyMeasurable AG 1
      (fun g => (hGb g).1)).congr (Eventually.of_forall fun g => by simp only; ring)
  have i5 := integrable_ind u hu F hFc'.aestronglyMeasurable AF 1 (fun g => (hFb g).1)
  have i6 := integrable_ind u hu G hGc'.aestronglyMeasurable AG 1 (fun g => (hGb g).1)
  have hself : ∀ (H : EuclideanSpace ℝ (Fin d) → ℝ) (H' : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (A : ℝ), 0 ≤ A → (∀ g, ‖H' g‖ ≤ A * Real.exp (1 * ‖g‖)) →
      ∀ g, |H' g g| ≤ A * Real.exp (2 * ‖g‖) := fun H H' A hA hH g => by
    have he := Real.add_one_le_exp ‖g‖
    rw [← Real.norm_eq_abs, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + ‖g‖ by ring, Real.exp_add]
    calc ‖H' g g‖ ≤ ‖H' g‖ * ‖g‖ := (H' g).le_opNorm g
      _ ≤ (A * Real.exp (1 * ‖g‖)) * Real.exp ‖g‖ :=
          mul_le_mul (hH g) (by linarith) (norm_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by ring
  have i7 := integrable_ind u hu (fun g => G' g g) (meas_apply_self G G' hG).aestronglyMeasurable AG 2
    (hself G G' AG hAG0 fun g => (hGb g).2)
  have i7F := integrable_ind u hu (fun g => F' g g) (meas_apply_self F F' hF).aestronglyMeasurable AF 2
    (hself F F' AF hAF0 fun g => (hFb g).2)
  have iones := integrable_ind u hu (fun _ => (1 : ℝ)) aestronglyMeasurable_const 1 0
    (fun g => by simp)
  have hkm : Measurable fun g : EuclideanSpace ℝ (Fin d) => kfun ⟪u, g⟫ := (continuous_kfun.comp hinner).measurable
  have hFum : Measurable fun g => F' g u := by
    rw [show F' = fderiv ℝ F from funext fun g => (hF g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ F u
  have iKF : Integrable (fun g => kfun ⟪u, g⟫ * F' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu kfun continuous_kfun.measurable 1 0 le_rfl (fun t => by
      rw [zero_mul, Real.exp_zero, mul_one, abs_of_nonneg (kfun_mem t).1]; exact (kfun_mem t).2)
      (fun g => F' g u) hFum.aestronglyMeasurable AF 1 (fun g => by
        rw [← Real.norm_eq_abs]; exact ((F' g).le_opNorm u).trans (by rw [hu, mul_one]; exact (hFb g).2))
  have ik : Integrable (fun g => kfun ⟪u, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_of_abs_le_exp _ hkm.aestronglyMeasurable 1 0 fun g => by
      rw [zero_mul, Real.exp_zero, mul_one, abs_of_nonneg (kfun_mem _).1]; exact (kfun_mem _).2
  -- (E1): the score integral
  have hpw1 : (fun g => (F g - G g) * (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - kfun ⟪u, g⟫ * ⟪u, g⟫ +
        (if ⟪u, g⟫ < 1 then 1 else 0) else 0)) = fun g =>
      1 / R * ((if 0 < ⟪u, g⟫ then F g * (‖g‖ ^ 2 - (d : ℝ)) else 0) -
          (if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0)) -
        (F g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0) -
          G g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0)) -
        1 / R * ((if 0 < ⟪u, g⟫ then F g else 0) - (if 0 < ⟪u, g⟫ then G g else 0)) := by
    funext g
    by_cases h : 0 < ⟪u, g⟫
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h]
      by_cases h1 : ⟪u, g⟫ < 1
      · rw [ite_eq_left h1, ite_eq_left ⟨h, h1⟩]; field_simp; ring
      · rw [ite_eq_right h1, ite_eq_right (fun h' => h1 h'.2)]; field_simp; ring
    · have hk : kfun ⟪u, g⟫ = 0 := by
        unfold kfun; rw [max_eq_right (not_lt.1 h), min_eq_left zero_le_one]
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h,
        ite_eq_right (fun h' => h h'.1), hk]
      ring
  have E1 : ∫ g, (F g - G g) * (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - kfun ⟪u, g⟫ * ⟪u, g⟫ +
        (if ⟪u, g⟫ < 1 then 1 else 0) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      1 / R * ((∫ g, (if 0 < ⟪u, g⟫ then F g * (‖g‖ ^ 2 - (d : ℝ)) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        ∫ g, (if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
      ((∫ g, F g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        ∫ g, G g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
      1 / R * ((∫ g, (if 0 < ⟪u, g⟫ then F g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        ∫ g, (if 0 < ⟪u, g⟫ then G g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    rw [hpw1, integral_sub (f := fun g => 1 / R * ((if 0 < ⟪u, g⟫ then F g * (‖g‖ ^ 2 - (d : ℝ)) else 0) -
          (if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0)) -
        (F g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0) -
          G g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0)))
      (g := fun g => 1 / R * ((if 0 < ⟪u, g⟫ then F g else 0) - (if 0 < ⟪u, g⟫ then G g else 0)))
      (((i1.sub i2).const_mul _).sub (i3.sub i4)) ((i5.sub i6).const_mul _),
      integral_sub (f := fun g => 1 / R * ((if 0 < ⟪u, g⟫ then F g * (‖g‖ ^ 2 - (d : ℝ)) else 0) -
          (if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0)))
      (g := fun g => F g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0) -
          G g * (kfun ⟪u, g⟫ * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < 1 then 1 else 0))
      ((i1.sub i2).const_mul _) (i3.sub i4), integral_const_mul, integral_const_mul,
      integral_sub i1 i2, integral_sub i3 i4, integral_sub i5 i6]
  -- (E2)
  have hpw2 : (fun g => if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) = fun g =>
      ((if 0 < ⟪u, g⟫ then G' g g else 0) - (if 0 < ⟪u, g⟫ then G g else 0)) +
        G 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0) := by
    funext g; split_ifs <;> ring
  have E2 : ∫ g, (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (∫ g, (if 0 < ⟪u, g⟫ then G' g g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        (∫ g, (if 0 < ⟪u, g⟫ then G g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + G 0 * (1 / 2) := by
    rw [hpw2, integral_add (f := fun g => (if 0 < ⟪u, g⟫ then G' g g else 0) - (if 0 < ⟪u, g⟫ then G g else 0))
      (g := fun g => G 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0)) (i7.sub i6) (iones.const_mul _),
      integral_sub i7 i6, integral_const_mul, integral_ind_inner u hu]
  -- (E3): the chord inequality, integrated
  have hpt : ∀ g, 1 / R * ((if 0 < ⟪u, g⟫ then F g else 0) - F 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0)) +
      Γ / R * kfun ⟪u, g⟫ ≤ 1 / R * (if 0 < ⟪u, g⟫ then F' g g else 0) - kfun ⟪u, g⟫ * F' g u := fun g => by
    by_cases h : 0 < ⟪u, g⟫
    · have := AdversarialBco.Body.grad_chord F (F' g) hFc g (hF g) u R Γ (kfun ⟪u, g⟫) hR hΓ (kfun_mem _).1
        (kfun_mem _).2
      rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      have e : 1 / R * (F g - F 0 * 1) + Γ / R * kfun ⟪u, g⟫ = (F g - F 0) / R + Γ / R * kfun ⟪u, g⟫ := by ring
      rw [e]; exact this
    · have hk : kfun ⟪u, g⟫ = 0 := by
        unfold kfun; rw [max_eq_right (not_lt.1 h), min_eq_left zero_le_one]
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, hk]; simp
  have E3 := integral_mono
    (f := fun g => 1 / R * ((if 0 < ⟪u, g⟫ then F g else 0) - F 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0)) +
      Γ / R * kfun ⟪u, g⟫)
    (g := fun g => 1 / R * (if 0 < ⟪u, g⟫ then F' g g else 0) - kfun ⟪u, g⟫ * F' g u)
    (((i5.sub (iones.const_mul (F 0))).const_mul (1 / R)).add (ik.const_mul (Γ / R)))
    ((i7F.const_mul (1 / R)).sub iKF) hpt
  rw [integral_add (f := fun g => 1 / R * ((if 0 < ⟪u, g⟫ then F g else 0) -
      F 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0))) (g := fun g => Γ / R * kfun ⟪u, g⟫)
      ((i5.sub (iones.const_mul (F 0))).const_mul (1 / R)) (ik.const_mul (Γ / R)),
    integral_const_mul, integral_sub (f := fun g => if 0 < ⟪u, g⟫ then F g else 0)
      (g := fun g => F 0 * (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0)) i5 (iones.const_mul (F 0)),
    integral_const_mul, integral_const_mul,
    integral_ind_inner u hu, integral_kfun_inner u hu,
    integral_sub (f := fun g => 1 / R * (if 0 < ⟪u, g⟫ then F' g g else 0))
      (g := fun g => kfun ⟪u, g⟫ * F' g u) (i7F.const_mul (1 / R)) iKF, integral_const_mul] at E3
  -- assemble
  simp only [kfun] at E1 E3 ⊢
  rw [E1, E2, ← aF, ← aG, ← bF, ← bG]
  have hR' : R ≠ 0 := hR.ne'
  have e : ∀ a b c x y z : ℝ, 1 / R * (c - F 0 * (1 / 2)) + Γ / R * kappa ≤ 1 / R * a - b →
      Γ / R * kappa + y - (x - z + G 0 * (1 / 2)) / R ≤
        1 / R * (a - x) - (b - y) - 1 / R * (c - z) + (F 0 - G 0) / (2 * R) := by
    intro a b c x y z h
    have h1 : 1 / R * (a - x) - (b - y) - 1 / R * (c - z) + (F 0 - G 0) / (2 * R) -
        (Γ / R * kappa + y - (x - z + G 0 * (1 / 2)) / R) =
        (1 / R * a - b) - (1 / R * (c - F 0 * (1 / 2)) + Γ / R * kappa) := by field_simp; ring
    linarith
  exact e _ _ _ _ _ _ E3

end AdversarialBco.Body2

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_sq_phi_01 : ∫ t in (0 : ℝ)..1, t ^ 2 * AdversarialBco.BodySpec.phi t = 1 / 2 - AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.phi 1 := by
  set φ := AdversarialBco.BodySpec.phi
  have hφ_cont : Continuous φ := by
    unfold φ AdversarialBco.BodySpec.phi
    have h_num : Continuous (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2)) := by
      continuity
    have h_denom : Continuous (fun (_ : ℝ) => Real.sqrt (2 * Real.pi)) :=
      Real.continuous_sqrt.comp continuous_const
    have h_denom_ne : ∀ (t : ℝ), (fun (_ : ℝ) => Real.sqrt (2 * Real.pi)) t ≠ 0 := by
      intro t
      have hpos : Real.sqrt (2 * Real.pi) > 0 := by
        refine Real.sqrt_pos.mpr ?_
        positivity
      linarith
    exact Continuous.div h_num h_denom h_denom_ne
  have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ => -x * φ x) (t ^ 2 * φ t - φ t) t := by
    have h_neg : HasDerivAt (fun x : ℝ => -x) (-1) t := hasDerivAt_neg t
    have h_phi : HasDerivAt φ (-(t * φ t)) t := AdversarialBco.Body2.hasDerivAt_phi t
    have h_mul := HasDerivAt.mul h_neg h_phi
    -- h_mul : HasDerivAt ((fun x => -x) * φ) ((-1) * φ t + (-t) * (-(t * φ t))) t
    have h_simp_deriv : (-1 : ℝ) * φ t + (-t) * (-(t * φ t)) = t ^ 2 * φ t - φ t := by
      ring
    have h_target : HasDerivAt (fun x : ℝ => -x * φ x) (t ^ 2 * φ t - φ t) t := by
      -- h_mul : HasDerivAt ((fun x => -x) * φ) ((-1) * φ t + (-t) * (-(t * φ t))) t
      have h_fun_eq : ((fun x : ℝ => -x) * φ) = (fun x : ℝ => -x * φ x) := by
        funext x; rfl
      have h_deriv_eq : ((-1 : ℝ) * φ t + (-t) * (-(t * φ t))) = (t ^ 2 * φ t - φ t) := by ring
      -- Rewrite the goal to match h_mul
      rw [← h_fun_eq, ← h_deriv_eq]
      exact h_mul
    exact h_target
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 2 * φ x - φ x) MeasureTheory.volume 0 1 := by
    have h_cont : Continuous (fun x : ℝ => x ^ 2 * φ x - φ x) := by
      continuity
    exact h_cont.intervalIntegrable _ _
  have h_eq_sub_raw : ∫ t in (0 : ℝ)..1, (t ^ 2 * φ t - φ t) = ((-1 * φ 1) - ((-0) * φ 0)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -x * φ x)
      (f' := fun x : ℝ => x ^ 2 * φ x - φ x) (fun x hx => hderiv x) hint
  have h_int_sub : ∫ t in (0 : ℝ)..1, (t ^ 2 * φ t - φ t) = -φ 1 := by
    rw [h_eq_sub_raw]
    ring
  have h_phi_int : ∫ t in (0 : ℝ)..1, φ t = 1 / 2 - AdversarialBco.BodySpec.Qtail 1 := by
    rw [AdversarialBco.Body2.Qtail_eq_sub 1]
    ring
  calc
    ∫ t in (0 : ℝ)..1, t ^ 2 * φ t = ∫ t in (0 : ℝ)..1, ((t ^ 2 * φ t - φ t) + φ t) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      ring
    _ = (∫ t in (0 : ℝ)..1, (t ^ 2 * φ t - φ t)) + (∫ t in (0 : ℝ)..1, φ t) := by
      have h_int1 : IntervalIntegrable (fun x : ℝ => x ^ 2 * φ x - φ x) MeasureTheory.volume 0 1 := by
        have h_cont : Continuous (fun x : ℝ => x ^ 2 * φ x - φ x) := by continuity
        exact h_cont.intervalIntegrable _ _
      have h_int2 : IntervalIntegrable φ MeasureTheory.volume 0 1 :=
        hφ_cont.intervalIntegrable _ _
      rw [intervalIntegral.integral_add h_int1 h_int2]
    _ = (-φ 1) + (1 / 2 - AdversarialBco.BodySpec.Qtail 1) := by rw [h_int_sub, h_phi_int]
    _ = 1 / 2 - AdversarialBco.BodySpec.Qtail 1 - φ 1 := by ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_four_phi_01 : ∫ t in (0 : ℝ)..1, t ^ 4 * AdversarialBco.BodySpec.phi t = 3 * (1 / 2 - AdversarialBco.BodySpec.Qtail 1 - AdversarialBco.BodySpec.phi 1) - AdversarialBco.BodySpec.phi 1 := by
  set φ := AdversarialBco.BodySpec.phi
  have hφ_cont : Continuous φ := by
    unfold φ AdversarialBco.BodySpec.phi
    refine Continuous.div ?_ ?_ (fun x => ?_)
    · exact Real.continuous_exp.comp (by continuity)
    · exact continuous_const
    · have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      linarith
  have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ => -(x ^ 3) * φ x) (t ^ 4 * φ t - 3 * (t ^ 2 * φ t)) t := by
    have h1 : HasDerivAt (-(fun x : ℝ => x ^ 3)) (-(3 * t ^ 2)) t := (hasDerivAt_pow 3 t).neg
    have h2 : HasDerivAt φ (-(t * φ t)) t := AdversarialBco.Body2.hasDerivAt_phi t
    have hprod := HasDerivAt.mul h2 h1
    -- hprod : HasDerivAt (φ * (-(fun x => x^3))) ((-(t * φ t)) * (-(fun x => x^3)) t + φ t * (-(3 * t^2))) t
    -- simplify: φ * (-(x^3)) = -(x^3 * φ), and the derivative simplifies to t^4*φ - 3*t^2*φ
    have hprod' : HasDerivAt (fun x : ℝ => -(x ^ 3) * φ x) (t ^ 4 * φ t - 3 * (t ^ 2 * φ t)) t := by
      convert hprod using 1
      · ext x; simp [mul_comm]
      · simp; ring
    exact hprod'
  have hderiv_on : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => -(x ^ 3) * φ x) (x ^ 4 * φ x - 3 * (x ^ 2 * φ x)) x :=
    fun x _ => hderiv x
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 4 * φ t - 3 * (t ^ 2 * φ t)) MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    continuity
  have h_eq : (∫ t in (0 : ℝ)..1, (t ^ 4 * φ t - 3 * (t ^ 2 * φ t))) = (-(1 : ℝ) ^ 3) * φ 1 - (-(0 : ℝ) ^ 3) * φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_on hint
  have h_simp : (-(1 : ℝ) ^ 3) * φ 1 - (-(0 : ℝ) ^ 3) * φ 0 = -φ 1 := by norm_num
  rw [h_simp] at h_eq
  have h_int_sq : ∫ t in (0 : ℝ)..1, t ^ 2 * φ t = 1 / 2 - AdversarialBco.BodySpec.Qtail 1 - φ 1 :=
    AdversarialBco.Body2.integral_sq_phi_01
  calc
    ∫ t in (0 : ℝ)..1, t ^ 4 * φ t
        = (∫ t in (0 : ℝ)..1, (t ^ 4 * φ t - 3 * (t ^ 2 * φ t) + 3 * (t ^ 2 * φ t))) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      ring
    _ = (∫ t in (0 : ℝ)..1, (t ^ 4 * φ t - 3 * (t ^ 2 * φ t))) + (∫ t in (0 : ℝ)..1, 3 * (t ^ 2 * φ t)) := by
      rw [intervalIntegral.integral_add hint]
      refine Continuous.intervalIntegrable ?_ 0 1
      continuity
    _ = (∫ t in (0 : ℝ)..1, (t ^ 4 * φ t - 3 * (t ^ 2 * φ t))) + 3 * (∫ t in (0 : ℝ)..1, t ^ 2 * φ t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (-φ 1) + 3 * (∫ t in (0 : ℝ)..1, t ^ 2 * φ t) := by rw [h_eq]
    _ = (-φ 1) + 3 * (1 / 2 - AdversarialBco.BodySpec.Qtail 1 - φ 1) := by rw [h_int_sq]
    _ = 3 * (1 / 2 - AdversarialBco.BodySpec.Qtail 1 - φ 1) - φ 1 := by ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Topology
open Filter

theorem AdversarialBco.Body2.integral_sq_phi_Ioi_one : ∫ t in Set.Ioi (1 : ℝ), t ^ 2 * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.phi 1 + AdversarialBco.BodySpec.Qtail 1 := by
  set phi := AdversarialBco.BodySpec.phi with hphi
  set f := fun t : ℝ => -t * phi t with hf
  set f' := fun t : ℝ => t ^ 2 * phi t - phi t with hf'
  have hphi_deriv (t : ℝ) : HasDerivAt phi (-(t * phi t)) t :=
    AdversarialBco.Body2.hasDerivAt_phi t
  have hphi_cont : Continuous phi := by
    unfold phi AdversarialBco.BodySpec.phi
    refine Continuous.div (Real.continuous_exp.comp ?_) continuous_const (fun x => ?_)
    · exact (continuous_neg.comp (continuous_pow 2)).div_const _
    · exact Real.sqrt_pos.mpr (by
        have hpi : 0 < Real.pi := Real.pi_pos
        nlinarith) |>.ne'
  have hf_deriv (t : ℝ) : HasDerivAt f (f' t) t := by
    dsimp [f, f']
    have h_neg_id : HasDerivAt (fun x : ℝ => -x) (-1) t := by
      simpa using hasDerivAt_neg t
    have h_prod := HasDerivAt.mul h_neg_id (hphi_deriv t)
    -- h_prod: HasDerivAt ((fun x => -x) * phi) ((-1)*phi t + (-t)*(-(t*phi t))) t
    -- Goal: HasDerivAt (fun t => -t * phi t) (t^2 * phi t - phi t) t
    have h_prod_simp : HasDerivAt (fun x => -x * phi x) (-phi t + t*(t*phi t)) t := by
      convert h_prod using 1
      ring
    have h_func_eq : (fun x => -x * phi x) = (fun t => -t * phi t) := by
      ext x; ring
    have h_deriv_eq : (-phi t + t*(t*phi t)) = (t^2 * phi t - phi t) := by ring
    rw [h_func_eq, h_deriv_eq] at h_prod_simp
    exact h_prod_simp
  have hf_cont_at : ContinuousWithinAt f (Set.Ici 1) 1 := by
    rw [hf]
    refine Continuous.continuousWithinAt ?_
    refine Continuous.mul (continuous_neg.comp continuous_id) hphi_cont
  have h_int_phi : IntegrableOn phi (Set.Ioi (1 : ℝ)) := by
    have : Integrable phi := by
      unfold phi AdversarialBco.BodySpec.phi
      have h_int : Integrable (fun x : ℝ => Real.exp (-((1/2 : ℝ)) * x ^ 2)) :=
        integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))
      convert h_int.div_const (Real.sqrt (2 * Real.pi)) using 1
      ext x
      have h_exp_eq : -x ^ 2 / 2 = -((1/2 : ℝ)) * x ^ 2 := by ring
      simp [h_exp_eq]
    exact this.integrableOn
  have h_int_t2_phi : IntegrableOn (fun t => t ^ 2 * phi t) (Set.Ioi (1 : ℝ)) := by
    have : Integrable (fun t => t ^ 2 * phi t) := by
      unfold phi AdversarialBco.BodySpec.phi
      have h := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ)) (by norm_num : (-1 : ℝ) < 2)
      have h_temp := h.div_const (Real.sqrt (2 * Real.pi))
      -- h_temp: Integrable (fun x => x^2 * exp(-(1/2)*x^2) / sqrt(2π))
      -- Goal: Integrable (fun t => t^2 * (exp(-t^2/2) / sqrt(2π)))
      -- These are equal by ring
      refine h_temp.congr (Eventually.of_forall ?_)
      intro t
      simp [div_eq_mul_inv, mul_comm, mul_assoc]
    exact this.integrableOn
  have h_int_f' : IntegrableOn f' (Set.Ioi (1 : ℝ)) := by
    rw [hf']
    exact h_int_t2_phi.sub h_int_phi
  have h_tendsto_main : Tendsto (fun t : ℝ => t * Real.exp (-(t ^ 2 / 2))) atTop (𝓝 (0 : ℝ)) := by
    have h_sq_tendsto : Tendsto (fun t : ℝ => (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2))) atTop (𝓝 (0 : ℝ)) := by
      have h_comp : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop := by
        have h_sq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := by
          simpa [sq] using tendsto_mul_self_atTop
        simpa [div_eq_mul_inv] using
          ((tendsto_mul_const_atTop_of_pos (by norm_num : 0 < (1/2 : ℝ))).mpr h_sq :
            Tendsto (fun t => t ^ 2 * (1/2 : ℝ)) atTop atTop)
      have h_zero := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h_comp_tendsto := h_zero.comp h_comp
      -- h_comp_tendsto : Tendsto ((fun x => x^1 * exp(-x)) ∘ (fun t => t^2/2)) atTop (𝓝 0)
      -- Rewrite the composition to the desired form
      have h_eq : ((fun x : ℝ => x ^ 1 * Real.exp (-x)) ∘ (fun t => t ^ 2 / 2)) =
          (fun t => (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2))) := by
        ext t; simp
      rw [h_eq] at h_comp_tendsto
      exact h_comp_tendsto
    have h_nonneg : ∀ᶠ t in atTop, (0 : ℝ) ≤ t * Real.exp (-(t ^ 2 / 2)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_nonneg ht (Real.exp_pos _).le
    have h_bound : ∀ᶠ t in atTop, t * Real.exp (-(t ^ 2 / 2)) ≤ 2 * ((t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2))) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hineq : t ≤ 2 * (t ^ 2 / 2) := by
        have : 1 ≤ t := ht
        nlinarith
      nlinarith [Real.exp_pos (-(t ^ 2 / 2))]
    have h_upper_zero : Tendsto (fun t : ℝ => 2 * ((t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)))) atTop (𝓝 (0 : ℝ)) := by
      simpa [mul_assoc] using h_sq_tendsto.const_mul (2 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ h_upper_zero h_nonneg h_bound
    · exact tendsto_const_nhds
  have h_tendsto_f : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    have h_neg : Tendsto (fun t : ℝ => -t * Real.exp (-(t ^ 2 / 2))) atTop (𝓝 (0 : ℝ)) := by
      simpa using h_tendsto_main.neg
    have h_div : Tendsto (fun t : ℝ => (-t * Real.exp (-(t ^ 2 / 2))) / Real.sqrt (2 * Real.pi)) atTop (𝓝 (0 : ℝ)) := by
      simpa [div_eq_mul_inv] using h_neg.mul_const ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa [f, phi, AdversarialBco.BodySpec.phi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_div
  have h_apply : ∫ t in Set.Ioi (1 : ℝ), f' t = (0 : ℝ) - f 1 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hf_cont_at
      (fun x hx => hf_deriv x) h_int_f' h_tendsto_f
  -- Now compute the result
  dsimp [f', f] at h_apply
  -- h_apply : ∫ t in Ioi 1, (t^2 * phi t - phi t) = 0 - (-(1 * phi 1))
  -- Simplify: -(1 * phi 1) = -phi 1
  have h_simp_rhs : (-(1 : ℝ) * phi 1) = -phi 1 := by ring
  rw [h_simp_rhs] at h_apply
  -- h_apply : ∫ t in Ioi 1, (t^2 * phi t - phi t) = 0 - (-phi 1)
  -- i.e., ∫ t in Ioi 1, t^2 * phi t - ∫ t in Ioi 1, phi t = phi 1
  have h_integral_sub : (∫ t in Set.Ioi (1 : ℝ), (t ^ 2 * phi t - phi t)) =
      (∫ t in Set.Ioi (1 : ℝ), t ^ 2 * phi t) - (∫ t in Set.Ioi (1 : ℝ), phi t) :=
    integral_sub h_int_t2_phi h_int_phi
  rw [h_integral_sub] at h_apply
  -- h_apply : (∫ t in Ioi 1, t^2 * phi t) - (∫ t in Ioi 1, phi t) = 0 - (-phi 1)
  -- Simplify RHS: 0 - (-phi 1) = phi 1
  have h_rhs : (0 : ℝ) - (-phi 1) = phi 1 := by ring
  rw [h_rhs] at h_apply
  -- h_apply : (∫ t in Ioi 1, t^2 * phi t) - (∫ t in Ioi 1, phi t) = phi 1
  -- Qtail 1 = ∫ t in Ioi 1, phi t
  have h_Qtail : (∫ t in Set.Ioi (1 : ℝ), phi t) = AdversarialBco.BodySpec.Qtail 1 := by
    rw [hphi, AdversarialBco.BodySpec.Qtail]
  rw [h_Qtail] at h_apply
  -- h_apply : (∫ t in Ioi 1, t^2 * phi t) - Qtail 1 = phi 1
  -- So ∫ t in Ioi 1, t^2 * phi t = phi 1 + Qtail 1
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.integral_score_sq_phi : ∫ t in Set.Ioi (0 : ℝ), (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t = AdversarialBco.BodySpec.kappa2 := by
  have h01pos : (0 : ℝ) ≤ 1 := by norm_num
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 := by
    rw [Set.Ioc_union_Ioi_eq_Ioi h01pos]
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx1 hx2
    rcases hx1 with ⟨hx1a, hx1b⟩
    have hx2' : (1 : ℝ) < x := hx2
    linarith
  have hmeas1 : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hmeas2 : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi
  -- integrability of t^k * phi(t) on Ioi 0 for k = 0, 2, 4
  have h_phi_mul (k : ℝ) : (fun t : ℝ => t ^ k * Real.exp (-((1/2 : ℝ)) * t ^ 2)) = (fun t => Real.sqrt (2 * Real.pi) * (t ^ k * AdversarialBco.BodySpec.phi t)) := by
    ext t
    rw [AdversarialBco.BodySpec.phi]
    field_simp
  have h_int_pow (k : ℝ) (hk : -1 < k) : IntegrableOn (fun t : ℝ => t ^ k * AdversarialBco.BodySpec.phi t) (Set.Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-((1/2 : ℝ)) * t ^ 2)) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ)) hk
    rw [h_phi_mul k] at h
    have h_sqrt_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have h' := h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    refine h'.congr ?_
    filter_upwards with t
    field_simp [h_sqrt_ne_zero]
  have h_int_phi : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi (0 : ℝ)) := by
    simpa [Real.rpow_zero, mul_comm] using h_int_pow 0 (by norm_num)
  have h_int_sq : IntegrableOn (fun t : ℝ => t ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioi (0 : ℝ)) := by
    simpa [Real.rpow_natCast] using h_int_pow 2 (by norm_num)
  have h_int_four : IntegrableOn (fun t : ℝ => t ^ 4 * AdversarialBco.BodySpec.phi t) (Set.Ioi (0 : ℝ)) := by
    simpa [Real.rpow_natCast] using h_int_pow 4 (by norm_num)
  -- integrability of (t^4 - 2t^2 + 1) * phi on Ioc 0 1
  have h_int_Ioc_simp : IntegrableOn (fun t : ℝ => (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t) (Set.Ioc (0 : ℝ) 1) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ 4 * AdversarialBco.BodySpec.phi t) (Set.Ioc (0 : ℝ) 1) :=
      h_int_four.mono_set Set.Ioc_subset_Ioi_self
    have h2 : IntegrableOn (fun t : ℝ => t ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioc (0 : ℝ) 1) :=
      h_int_sq.mono_set Set.Ioc_subset_Ioi_self
    have h3 : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioc (0 : ℝ) 1) :=
      h_int_phi.mono_set Set.Ioc_subset_Ioi_self
    have h_eq : (fun t : ℝ => (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t) =
      (fun t => t ^ 4 * AdversarialBco.BodySpec.phi t) - (fun t => (2 : ℝ) * (t ^ 2 * AdversarialBco.BodySpec.phi t)) + AdversarialBco.BodySpec.phi := by
      ext t
      calc
        (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t
            = t ^ 4 * AdversarialBco.BodySpec.phi t - 2 * t ^ 2 * AdversarialBco.BodySpec.phi t + AdversarialBco.BodySpec.phi t := by ring
        _ = (t ^ 4 * AdversarialBco.BodySpec.phi t) - ((2 : ℝ) * (t ^ 2 * AdversarialBco.BodySpec.phi t)) + AdversarialBco.BodySpec.phi t := by ring
    rw [h_eq]
    exact ((h1.sub (h2.const_mul (2 : ℝ))).add h3)
  -- integrability of t^2 * phi on Ioi 1
  have h_int_Ioi_simp : IntegrableOn (fun t : ℝ => t ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioi (1 : ℝ)) :=
    h_int_sq.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  -- a.e. equality between Ioc 0 1 and Ioo 0 1
  have h_ae_eq_set : Set.Ioc (0 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have h_sub : Set.Ioc (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) 1 ⊆ {1} := by
        intro x hx
        rcases hx with ⟨⟨hx0, hx1⟩, hx_not⟩
        by_cases h : x < 1
        · exfalso; exact hx_not ⟨hx0, h⟩
        · have hx1' : x = 1 := by linarith
          exact hx1'
      have h_null : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
      exact MeasureTheory.measure_mono_null h_sub h_null
    · have h_empty : Set.Ioo (0 : ℝ) 1 \ Set.Ioc (0 : ℝ) 1 = ∅ := by
        ext x; constructor
        · intro h; exfalso; rcases h with ⟨⟨hx0, hx1⟩, hx_not⟩; exact hx_not ⟨hx0, le_of_lt hx1⟩
        · intro h; exfalso; exact h
      simp [h_empty]
  -- pointwise equality on Ioo 0 1
  have h_eq_on_Ioo : Set.EqOn (fun t : ℝ => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t)
    (fun t : ℝ => (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t) (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have h_min : min t 1 = t := min_eq_left (by linarith)
    have h_if : (if t < 1 then (1 : ℝ) else 0) = 1 := if_pos ht1
    calc
      (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t
          = (t * t - 1) ^ 2 * AdversarialBco.BodySpec.phi t := by simp [h_min, h_if]
      _ = (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t := by ring
  -- pointwise equality on Ioi 1
  have h_eq_on_Ioi : Set.EqOn (fun t : ℝ => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t)
    (fun t : ℝ => t ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    have ht1 : 1 < t := ht
    have h_min : min t 1 = 1 := min_eq_right (by linarith)
    have h_if : (if t < 1 then (1 : ℝ) else 0) = 0 := if_neg (by linarith)
    simp [h_min, h_if]
  -- transfer integrability via a.e. equality
  have h_int_orig_Ioc : IntegrableOn (fun t : ℝ => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioc (0 : ℝ) 1) := by
    -- First, get integrability on Ioo 0 1 using pointwise equality
    have h_int_orig_Ioo : IntegrableOn (fun t : ℝ => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioo (0 : ℝ) 1) :=
      (h_int_Ioc_simp.congr_set_ae h_ae_eq_set.symm).congr_fun h_eq_on_Ioo.symm measurableSet_Ioo
    -- Then transfer back to Ioc 0 1 using a.e. equality
    exact h_int_orig_Ioo.congr_set_ae h_ae_eq_set
  have h_int_orig_Ioi : IntegrableOn (fun t : ℝ => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) (Set.Ioi (1 : ℝ)) :=
    h_int_Ioi_simp.congr_fun h_eq_on_Ioi.symm measurableSet_Ioi
  -- split the integral
  rw [hsplit]
  rw [MeasureTheory.setIntegral_union hdisj hmeas2 h_int_orig_Ioc h_int_orig_Ioi]
  -- simplify integrand on Ioc 0 1
  have h_simp_Ioc : (∫ t in Set.Ioc (0 : ℝ) 1, (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) =
      (∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t) := by
    -- Rewrite both sides to Ioo using a.e. equality
    rw [MeasureTheory.setIntegral_congr_set h_ae_eq_set, MeasureTheory.setIntegral_congr_set h_ae_eq_set]
    -- Now both integrals are over Ioo 0 1
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioo ?_
    refine ae_of_all _ ?_
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have h_min : min t 1 = t := min_eq_left (by linarith)
    have h_if : (if t < 1 then (1 : ℝ) else 0) = 1 := if_pos ht1
    calc
      (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t
          = (t * t - 1) ^ 2 * AdversarialBco.BodySpec.phi t := by simp [h_min, h_if]
      _ = (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t := by ring
  -- simplify integrand on Ioi 1
  have h_simp_Ioi : (∫ t in Set.Ioi (1 : ℝ), (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) =
      (∫ t in Set.Ioi (1 : ℝ), t ^ 2 * AdversarialBco.BodySpec.phi t) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    refine ae_of_all _ ?_
    intro t ht
    have ht1 : 1 < t := ht
    have h_min : min t 1 = 1 := min_eq_right (by linarith)
    have h_if : (if t < 1 then (1 : ℝ) else 0) = 0 := if_neg (by linarith)
    simp [h_min, h_if]
  rw [h_simp_Ioc, h_simp_Ioi]
  -- convert Ioc integral to interval integral
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- now: (∫_0^1 (t^4 - 2t^2 + 1) * phi) + (∫_{t>1} t^2 * phi) = kappa2
  -- get integrability for interval integrals
  have h_int_t4 : IntervalIntegrable (fun t : ℝ => t ^ 4 * AdversarialBco.BodySpec.phi t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h_int_four.mono_set Set.Ioc_subset_Ioi_self
  have h_int_t2 : IntervalIntegrable (fun t : ℝ => t ^ 2 * AdversarialBco.BodySpec.phi t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h_int_sq.mono_set Set.Ioc_subset_Ioi_self
  have h_int_phi_int : IntervalIntegrable AdversarialBco.BodySpec.phi volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h_int_phi.mono_set Set.Ioc_subset_Ioi_self
  -- expand the integral using linearity
  have h_expand : (∫ t in (0 : ℝ)..1, (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t) =
      (∫ t in (0 : ℝ)..1, t ^ 4 * AdversarialBco.BodySpec.phi t) - 2 * (∫ t in (0 : ℝ)..1, t ^ 2 * AdversarialBco.BodySpec.phi t) + (∫ t in (0 : ℝ)..1, AdversarialBco.BodySpec.phi t) := by
    calc
      (∫ t in (0 : ℝ)..1, (t ^ 4 - 2 * t ^ 2 + 1) * AdversarialBco.BodySpec.phi t)
          = (∫ t in (0 : ℝ)..1, (t ^ 4 * AdversarialBco.BodySpec.phi t) - (2 * (t ^ 2 * AdversarialBco.BodySpec.phi t)) + AdversarialBco.BodySpec.phi t) := by
            refine intervalIntegral.integral_congr_ae ?_
            refine ae_of_all _ ?_
            intro t ht
            ring
      _ = (∫ t in (0 : ℝ)..1, (t ^ 4 * AdversarialBco.BodySpec.phi t) - (2 * (t ^ 2 * AdversarialBco.BodySpec.phi t))) + (∫ t in (0 : ℝ)..1, AdversarialBco.BodySpec.phi t) := by
            rw [intervalIntegral.integral_add]
            · exact (h_int_t4.sub (h_int_t2.const_mul (2 : ℝ)))
            · exact h_int_phi_int
      _ = ((∫ t in (0 : ℝ)..1, t ^ 4 * AdversarialBco.BodySpec.phi t) - (∫ t in (0 : ℝ)..1, 2 * (t ^ 2 * AdversarialBco.BodySpec.phi t))) + (∫ t in (0 : ℝ)..1, AdversarialBco.BodySpec.phi t) := by
            rw [intervalIntegral.integral_sub h_int_t4 (h_int_t2.const_mul (2 : ℝ))]
      _ = (∫ t in (0 : ℝ)..1, t ^ 4 * AdversarialBco.BodySpec.phi t) - 2 * (∫ t in (0 : ℝ)..1, t ^ 2 * AdversarialBco.BodySpec.phi t) + (∫ t in (0 : ℝ)..1, AdversarialBco.BodySpec.phi t) := by
            rw [intervalIntegral.integral_const_mul]
  rw [h_expand]
  -- Now use the lemmas
  rw [AdversarialBco.Body2.integral_four_phi_01, AdversarialBco.Body2.integral_sq_phi_01]
  -- We still need ∫_0^1 phi t = 1/2 - Qtail 1
  have h_int_phi_01 : (∫ t in (0 : ℝ)..1, AdversarialBco.BodySpec.phi t) = 1/2 - AdversarialBco.BodySpec.Qtail 1 := by
    rw [AdversarialBco.Body2.Qtail_eq_sub 1]
    ring
  rw [h_int_phi_01]
  -- Now we have: (3*(1/2 - Qtail 1 - phi 1) - phi 1) - 2*(1/2 - Qtail 1 - phi 1) + (1/2 - Qtail 1) + (∫ t in Ioi 1, t^2 * phi t) = kappa2
  rw [AdversarialBco.Body2.integral_sq_phi_Ioi_one]
  -- Now we have: (3*(1/2 - Qtail 1 - phi 1) - phi 1) - 2*(1/2 - Qtail 1 - phi 1) + (1/2 - Qtail 1) + (phi 1 + Qtail 1) = kappa2
  -- Expand and simplify to show LHS = 1 - Qtail 1 - phi 1 = kappa2
  unfold AdversarialBco.BodySpec.kappa2
  ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.score_tail_moment {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) : ∫ g, (if 0 < ⟪u, g⟫ then (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - if ⟪u, g⟫ < 1 then 1 else 0) ^ 2 else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = AdversarialBco.BodySpec.kappa2 := by
  let f : ℝ → ℝ := fun t => if 0 < t then (AdversarialBco.Body2.kfun t * t - if t < 1 then 1 else 0) ^ 2 else 0
  have hf : Measurable f := by
    unfold f
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    have hkfun_meas : Measurable AdversarialBco.Body2.kfun := by
      unfold AdversarialBco.Body2.kfun
      refine Measurable.min (Measurable.max measurable_id measurable_const) measurable_const
    have h_ite_meas : Measurable (fun t : ℝ => if t < 1 then (1 : ℝ) else 0) := by
      refine Measurable.ite (f := fun (_ : ℝ) => (1 : ℝ)) (g := fun (_ : ℝ) => (0 : ℝ)) measurableSet_Iio ?_ ?_
      · exact measurable_const
      · exact measurable_const
    exact (((hkfun_meas.mul measurable_id).sub h_ite_meas).pow_const (2 : ℕ))
  have hkfun_pos {t : ℝ} (ht : 0 < t) : AdversarialBco.Body2.kfun t = min t 1 := by
    unfold AdversarialBco.Body2.kfun
    rw [max_eq_left (by linarith)]
  rw [AdversarialBco.Body2.integral_inner_eq u hu f hf]
  have h_ae : (fun t => f t * AdversarialBco.BodySpec.phi t) =ᵐ[volume]
      (Set.Ioi (0 : ℝ)).indicator (fun t => (min t 1 * t - if t < 1 then 1 else 0) ^ 2 * AdversarialBco.BodySpec.phi t) := by
    refine ae_of_all volume ?_
    intro t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht]
      have ht_pos : 0 < t := ht
      dsimp [f]
      rw [hkfun_pos ht_pos]
      rw [ite_eq_left ht_pos]
    · rw [Set.indicator_apply]
      rw [ite_eq_right ht]
      have ht' : ¬ (0 < t) := ht
      dsimp [f]
      rw [ite_eq_right ht']
      simp
  rw [MeasureTheory.integral_congr_ae h_ae]
  rw [MeasureTheory.integral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
  rw [AdversarialBco.Body2.integral_score_sq_phi]
end

theorem AdversarialBco.Body2.score_half_moment {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) : ∫ g, (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (2 * (d : ℝ) + 1) / 2 := by
  have h4 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 4) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Gauss.integrable_norm_pow 4
  have h2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Gauss.integrable_norm_pow 2
  have hf : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have := (h4.sub (h2.const_mul (2 * ((d : ℝ) + 1)))).add (integrable_const (((d : ℝ) + 1) ^ 2))
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hsym : ∀ g : EuclideanSpace ℝ (Fin d),
      (‖g - (2 * ⟪u, g⟫) • u‖ ^ 2 - (d : ℝ) - 1) ^ 2 = (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 := by
    intro g
    have : ‖g - (2 * ⟪u, g⟫) • u‖ ^ 2 = ‖g‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hu,
        real_inner_comm]
      ring
    rw [this]
  rw [AdversarialBco.Body2.integral_half_reflect u hu _ hf hsym, (AdversarialBco.Body.gauss_moments d).2]
  ring

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.score_sq_std {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 < R) : Integrable (fun g => (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ + (if ⟪u, g⟫ < 1 then 1 else 0) else 0) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧ ∫ g, (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ + (if ⟪u, g⟫ < 1 then 1 else 0) else 0) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (2 * (d : ℝ) + 1) / R ^ 2 + 2 * AdversarialBco.BodySpec.kappa2 := by
  have hR_sq_pos : 0 < R ^ 2 := pow_pos hR 2
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ_def
  set t := fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫ with ht_def
  set a := fun (g : EuclideanSpace ℝ (Fin d)) => (if 0 < t g then (‖g‖ ^ 2 - (d : ℝ) - 1) / R else 0) with ha_def
  set b := fun (g : EuclideanSpace ℝ (Fin d)) => (if 0 < t g then (AdversarialBco.Body2.kfun (t g) * t g - (if t g < 1 then 1 else 0)) else 0) with hb_def
  set f := fun (g : EuclideanSpace ℝ (Fin d)) => ((if 0 < t g then ((‖g‖ ^ 2 - (d : ℝ) - 1) / R - AdversarialBco.Body2.kfun (t g) * t g + (if t g < 1 then 1 else 0)) else 0)) ^ 2 with hf_def
  have hf_eq : ∀ g, f g = (a g - b g) ^ 2 := by
    intro g
    dsimp [f, a, b, t]
    by_cases h : 0 < ⟪u, g⟫
    · simp [h]; ring
    · simp [h]
  have h_bound : ∀ g, f g ≤ 2 * (a g) ^ 2 + 2 * (b g) ^ 2 := by
    intro g
    rw [hf_eq g]
    have h := sq_nonneg (a g + b g)
    nlinarith
  -- measurability
  have h_meas_f : AEStronglyMeasurable f μ := by
    have h_meas : Measurable f := by
      dsimp [f, a, b, t]
      have h_inner : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫ :=
        Measurable.const_inner (c := u) measurable_id
      have h_norm_sq : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 2 :=
        Measurable.pow_const measurable_norm 2
      have hkfun_meas : Measurable AdversarialBco.Body2.kfun := by
        unfold AdversarialBco.Body2.kfun
        refine Measurable.min ?_ ?_
        · refine Measurable.max ?_ ?_
          · exact measurable_id
          · exact measurable_const
        · exact measurable_const
      have h_inner_expr : Measurable fun (g : EuclideanSpace ℝ (Fin d)) =>
        (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R - AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ + (if ⟪u, g⟫ < 1 then 1 else 0) else 0) := by
        refine Measurable.ite (measurableSet_lt measurable_const h_inner) ?_ ?_
        · have hA : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => ((‖g‖ ^ 2 - (d : ℝ) - 1) / R) := by
            refine Measurable.div ?_ ?_
            · refine Measurable.sub (Measurable.sub h_norm_sq measurable_const) ?_
              exact measurable_const
            · exact measurable_const
          have hB : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫) :=
            Measurable.mul (hkfun_meas.comp h_inner) h_inner
          have hC : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => (if ⟪u, g⟫ < 1 then (1 : ℝ) else (0 : ℝ)) := by
            refine Measurable.ite (measurableSet_lt h_inner measurable_const) ?_ ?_
            · exact measurable_const
            · exact measurable_const
          have hAB : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => (((‖g‖ ^ 2 - (d : ℝ) - 1) / R) - (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫)) :=
            Measurable.sub hA hB
          have hABC : Measurable fun (g : EuclideanSpace ℝ (Fin d)) => ((((‖g‖ ^ 2 - (d : ℝ) - 1) / R) - (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫)) + (if ⟪u, g⟫ < 1 then 1 else 0)) :=
            Measurable.add hAB hC
          simpa [sub_eq_add_neg, add_assoc] using hABC
        · exact measurable_const
      refine Measurable.pow_const h_inner_expr 2
    exact h_meas.aestronglyMeasurable
  -- |⟪u, g⟫| ≤ ‖g‖
  have h_inner_bound : ∀ g, |⟪u, g⟫| ≤ ‖g‖ := by
    intro g
    calc
      |⟪u, g⟫| ≤ ‖u‖ * ‖g‖ := abs_real_inner_le_norm u g
      _ = ‖g‖ := by rw [hu, one_mul]
  -- |kfun(t)| ≤ 1
  have h_kfun_bound : ∀ t : ℝ, |AdversarialBco.Body2.kfun t| ≤ 1 := by
    intro t
    have h_nonneg : 0 ≤ AdversarialBco.Body2.kfun t := by
      unfold AdversarialBco.Body2.kfun
      refine le_min ?_ (by norm_num)
      exact le_max_right _ _
    have h_le_one : AdversarialBco.Body2.kfun t ≤ 1 := by
      unfold AdversarialBco.Body2.kfun
      exact min_le_right _ _
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  -- integrability of a^2 via score_half_moment
  have h_int_half : Integrable (fun g => (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0)) μ := by
    have h_val := AdversarialBco.Body2.score_half_moment u hu
    have h_ne_zero : ∫ g, (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0) ∂μ ≠ 0 := by
      rw [h_val]
      have : (0 : ℝ) < (2 * (d : ℝ) + 1) / 2 := by
        refine div_pos ?_ (by norm_num)
        have : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    exact MeasureTheory.Integrable.of_integral_ne_zero h_ne_zero
  have h_int_a_sq : Integrable (fun g => (a g) ^ 2) μ := by
    have h_eq : (fun g => (a g) ^ 2) = (fun g => (1 / R ^ 2) * (if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0)) := by
      ext g
      dsimp [a, t]
      by_cases h : 0 < ⟪u, g⟫
      · simp [h, div_pow]
        ring
      · simp [h]
    rw [h_eq]
    exact (h_int_half.const_mul (1 / R ^ 2))
  -- integrability of b^2 via exponential bound
  have h_int_b_sq : Integrable (fun g => (b g) ^ 2) μ := by
    have h_meas : AEStronglyMeasurable (fun g => (b g) ^ 2) μ := by
      have h_meas_b : Measurable b := by
        dsimp [b, t]
        refine Measurable.ite (measurableSet_lt measurable_const (Measurable.const_inner (c := u) measurable_id)) ?_ ?_
        · refine Measurable.sub ?_ ?_
          · refine Measurable.mul ?_ (Measurable.const_inner (c := u) measurable_id)
            unfold AdversarialBco.Body2.kfun
            refine Measurable.min ?_ ?_
            · refine Measurable.max ?_ ?_
              · exact Measurable.const_inner (c := u) measurable_id
              · exact measurable_const
            · exact measurable_const
          · refine Measurable.ite (measurableSet_lt (Measurable.const_inner (c := u) measurable_id) measurable_const) ?_ ?_
            · exact measurable_const
            · exact measurable_const
        · exact measurable_const
      exact (Measurable.pow_const h_meas_b 2).aestronglyMeasurable
    set A := (6 : ℝ) with hA_def
    refine AdversarialBco.Body.integrable_of_abs_le_exp (fun g => (b g) ^ 2) h_meas A 2 ?_
    intro g
    have h_nonneg : 0 ≤ (b g) ^ 2 := pow_two_nonneg _
    rw [abs_of_nonneg h_nonneg]
    dsimp [b, t]
    by_cases h : 0 < ⟪u, g⟫
    · simp [h]
      have h_norm_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
      -- bound the inner expression
      have h_inner_bound' : |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0)| ≤ ‖g‖ + 1 := by
        have h1 : |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫| ≤ ‖g‖ := by
          calc
            |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫| = |AdversarialBco.Body2.kfun ⟪u, g⟫| * |⟪u, g⟫| := abs_mul _ _
            _ ≤ 1 * |⟪u, g⟫| := mul_le_mul_of_nonneg_right (h_kfun_bound _) (abs_nonneg _)
            _ = |⟪u, g⟫| := by simp
            _ ≤ ‖g‖ := h_inner_bound g
        have h2 : |(if ⟪u, g⟫ < 1 then (1 : ℝ) else (0 : ℝ))| ≤ (1 : ℝ) := by
          by_cases h_lt : ⟪u, g⟫ < 1
          · rw [ite_eq_left h_lt]; simp
          · rw [ite_eq_right h_lt]; simp
        have h_sub : |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0)| ≤
            |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫| + |(if ⟪u, g⟫ < 1 then 1 else 0)| := abs_sub _ _
        exact le_trans h_sub (add_le_add h1 h2)
      have h_sq_bound : (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0)) ^ 2 ≤ (‖g‖ + 1) ^ 2 := by
        have h_abs' : |AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0)| ≤ ‖g‖ + 1 := h_inner_bound'
        have h_abs_sq' : -((‖g‖ + 1) : ℝ) ≤ AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0) ∧
            AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0) ≤ ‖g‖ + 1 :=
          abs_le.mp h_abs'
        rcases h_abs_sq' with ⟨h_left, h_right⟩
        nlinarith
      have h_poly_bound : (‖g‖ + 1) ^ 2 ≤ 2 * (1 + ‖g‖ ^ 2) := by
        nlinarith [sq_nonneg (‖g‖ - 1)]
      have h_exp_bound : 2 * (1 + ‖g‖ ^ 2) ≤ 6 * Real.exp (‖g‖) := by
        have h_sq : ‖g‖ ^ 2 ≤ 2 * Real.exp (‖g‖) := by
          have hpos : 0 ≤ ‖g‖ := h_norm_nonneg
          have h := Real.pow_div_factorial_le_exp (‖g‖) hpos 2
          have h' : ‖g‖ ^ 2 / 2 ≤ Real.exp (‖g‖) := by simpa [show (Nat.factorial 2 : ℝ) = 2 by norm_num] using h
          linarith
        have h_one : (1 : ℝ) ≤ Real.exp (‖g‖) := by
          have h := Real.add_one_le_exp (‖g‖)
          -- h : ‖g‖ + 1 ≤ exp(‖g‖), so 1 ≤ exp(‖g‖) since ‖g‖ ≥ 0
          linarith
        nlinarith
      calc
        (AdversarialBco.Body2.kfun ⟪u, g⟫ * ⟪u, g⟫ - (if ⟪u, g⟫ < 1 then 1 else 0)) ^ 2 ≤ (‖g‖ + 1) ^ 2 := h_sq_bound
        _ ≤ 2 * (1 + ‖g‖ ^ 2) := h_poly_bound
        _ ≤ 6 * Real.exp (‖g‖) := h_exp_bound
        _ ≤ 6 * Real.exp (2 * ‖g‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Real.exp_le_exp.mpr ?_
          nlinarith
    · simp [h]
      positivity
  -- integrability of f
  have h_int_f : Integrable f μ := by
    have h_meas : AEStronglyMeasurable f μ := h_meas_f
    -- f ≤ 2*a^2 + 2*b^2, and both a^2, b^2 are integrable
    -- so 2*a^2 + 2*b^2 is integrable, and f is integrable by comparison
    have h_int_sum : Integrable (fun g => 2 * (a g) ^ 2 + 2 * (b g) ^ 2) μ :=
      (h_int_a_sq.const_mul 2).add (h_int_b_sq.const_mul 2)
    have h_bound_f : ∀ᵐ g ∂μ, ‖f g‖ ≤ ‖(fun g => 2 * (a g) ^ 2 + 2 * (b g) ^ 2) g‖ := by
      filter_upwards with g
      have h := h_bound g
      have h_nonneg_f : 0 ≤ f g := by
        dsimp [f]
        apply pow_two_nonneg
      have h_nonneg_sum : 0 ≤ 2 * (a g) ^ 2 + 2 * (b g) ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_f, Real.norm_eq_abs, abs_of_nonneg h_nonneg_sum]
      exact h
    exact MeasureTheory.Integrable.mono h_int_sum h_meas h_bound_f
  -- compute ∫ a^2
  have h_int_a_sq_val : ∫ g, (a g) ^ 2 ∂μ = (2 * (d : ℝ) + 1) / (2 * R ^ 2) := by
    calc
      ∫ g, (a g) ^ 2 ∂μ = ∫ g, (if 0 < t g then ((‖g‖ ^ 2 - (d : ℝ) - 1) / R) else 0) ^ 2 ∂μ := rfl
      _ = ∫ g, (if 0 < t g then (((‖g‖ ^ 2 - (d : ℝ) - 1) / R)) ^ 2 else 0) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        by_cases h : 0 < t g
        · simp [h]
        · simp [h]
      _ = ∫ g, (1 / R ^ 2) * (if 0 < t g then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        by_cases h : 0 < t g
        · simp [h, div_pow]; ring
        · simp [h]
      _ = (1 / R ^ 2) * ∫ g, (if 0 < t g then (‖g‖ ^ 2 - (d : ℝ) - 1) ^ 2 else 0) ∂μ := by
        rw [integral_const_mul]
      _ = (1 / R ^ 2) * ((2 * (d : ℝ) + 1) / 2) := by rw [AdversarialBco.Body2.score_half_moment u hu]
      _ = (2 * (d : ℝ) + 1) / (2 * R ^ 2) := by ring
  -- compute ∫ b^2
  have h_int_b_sq_val : ∫ g, (b g) ^ 2 ∂μ = AdversarialBco.BodySpec.kappa2 := by
    calc
      ∫ g, (b g) ^ 2 ∂μ = ∫ g, ((if 0 < t g then (AdversarialBco.Body2.kfun (t g) * t g - (if t g < 1 then 1 else 0)) else 0)) ^ 2 ∂μ := rfl
      _ = ∫ g, (if 0 < t g then (AdversarialBco.Body2.kfun (t g) * t g - (if t g < 1 then 1 else 0)) ^ 2 else 0) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        by_cases h : 0 < t g
        · simp [h]
        · simp [h]
      _ = AdversarialBco.BodySpec.kappa2 := by rw [AdversarialBco.Body2.score_tail_moment u hu]
  -- integrability of 2*a^2 + 2*b^2
  have h_int_sum : Integrable (fun g => 2 * (a g) ^ 2 + 2 * (b g) ^ 2) μ :=
    (h_int_a_sq.const_mul 2).add (h_int_b_sq.const_mul 2)
  -- compute ∫ (2*a^2 + 2*b^2)
  have h_int_sum_val : ∫ g, (2 * (a g) ^ 2 + 2 * (b g) ^ 2) ∂μ = (2 * (d : ℝ) + 1) / R ^ 2 + 2 * AdversarialBco.BodySpec.kappa2 := by
    calc
      ∫ g, (2 * (a g) ^ 2 + 2 * (b g) ^ 2) ∂μ = ∫ g, 2 * (a g) ^ 2 ∂μ + ∫ g, 2 * (b g) ^ 2 ∂μ := by
        rw [integral_add (h_int_a_sq.const_mul 2) (h_int_b_sq.const_mul 2)]
      _ = 2 * ∫ g, (a g) ^ 2 ∂μ + 2 * ∫ g, (b g) ^ 2 ∂μ := by simp [integral_const_mul]
      _ = 2 * ((2 * (d : ℝ) + 1) / (2 * R ^ 2)) + 2 * AdversarialBco.BodySpec.kappa2 := by rw [h_int_a_sq_val, h_int_b_sq_val]
      _ = (2 * (d : ℝ) + 1) / R ^ 2 + 2 * AdversarialBco.BodySpec.kappa2 := by ring
  -- final result
  refine ⟨h_int_f, ?_⟩
  calc
    ∫ g, f g ∂μ ≤ ∫ g, (2 * (a g) ^ 2 + 2 * (b g) ^ 2) ∂μ := integral_mono h_int_f h_int_sum h_bound
    _ = (2 * (d : ℝ) + 1) / R ^ 2 + 2 * AdversarialBco.BodySpec.kappa2 := h_int_sum_val
end


namespace AdversarialBco.Body2
open AdversarialBco.BodySpec (phi Qtail kappa kappa2)

/-- Proposition 3.5 for one component, at the standard Gaussian: `F` plays `F_c(b + S ·)`, `G` plays
`Fbar(b + S ·)`, (S1), (S2) and (S4) hold, `h = 16 lam d`, `2 L1 φ(T) ≤ h/(32 d)` and the gap of `F` at `0` is at
least `h/2`. -/
theorem core_one {d : ℕ} (hd : 1 ≤ d) (F G : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (G'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hF : ∀ g, HasFDerivAt F (F' g) g) (hG : ∀ g, HasFDerivAt G (G' g) g) (hG' : ∀ g, HasFDerivAt G' (G'' g) g)
    (hFc : ConvexOn ℝ Set.univ F) (hGc : ConvexOn ℝ Set.univ G) (L1 M : ℝ) (hF'b : ∀ g, ‖F' g‖ ≤ L1)
    (hG'b : ∀ g, ‖G' g‖ ≤ L1) (hG''b : ∀ g, ‖G'' g‖ ≤ M) (hmono : ∀ g v, 0 ≤ G'' g v v) (lam : ℝ)
    (hS1 : ∀ v, ∫ g, G' g v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0)
    (hS2 : ∀ v v', ∫ g, ⟪v, g⟫ * G' g v' ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫)
    (hS4 : G 0 ≤ ∫ g, G g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (h T : ℝ) (hh : 0 < h)
    (hlam : lam = h / (16 * d)) (hT : 0 ≤ T) (htail : 2 * L1 * phi T ≤ h / (32 * d))
    (y : EuclideanSpace ℝ (Fin d)) (hy : F y ≤ F 0 - h / 2) :
    (kappa / 32 * h / ((1 + T) * d)) ^ 2 ≤
      (3 + 2 * kappa2 + 1 / (4 * d)) *
        (∫ g, (F g - G g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + (F 0 - G 0) ^ 2) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨hκl, hκu, hκ2l, hκ2u⟩ := kappa_bounds
  -- the direction of the minimiser
  have hy0 : y ≠ 0 := by
    rintro rfl; linarith
  set R := ‖y‖ with hR_def
  have hR : 0 < R := norm_pos_iff.2 hy0
  set u : EuclideanSpace ℝ (Fin d) := R⁻¹ • y with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hR.ne']
  have hRu : R • u = y := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hΓ : F (R • u) ≤ F 0 - h / 2 := by rw [hRu]; exact hy
  have I := inf_std F G F' G' hF hG hFc L1 L1 hF'b hG'b u hu R (h / 2) hR hΓ
  -- the dilation term
  have hL1 : 0 ≤ L1 := (norm_nonneg _).trans (hG'b 0)
  have hFc' : Continuous F := continuous_iff_continuousAt.2 fun g => (hF g).continuousAt
  have hGc' : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hFb := fun g => AdversarialBco.Body.abs_le_of_norm_fderiv_le F F' hF L1 hF'b g
  have hGb := fun g => AdversarialBco.Body.abs_le_of_norm_fderiv_le G G' hG L1 hG'b g
  set AG := |G 0| + |L1| with hAG
  have hAG0 : 0 ≤ AG := by positivity
  have hself : ∀ g, |G' g g| ≤ AG * Real.exp (2 * ‖g‖) := fun g => by
    have he := Real.add_one_le_exp ‖g‖
    rw [← Real.norm_eq_abs, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + ‖g‖ by ring, Real.exp_add]
    calc ‖G' g g‖ ≤ ‖G' g‖ * ‖g‖ := (G' g).le_opNorm g
      _ ≤ (AG * Real.exp (1 * ‖g‖)) * Real.exp ‖g‖ :=
          mul_le_mul ((hGb g).2) (by linarith) (norm_nonneg _) (mul_nonneg hAG0 (Real.exp_pos _).le)
      _ = _ := by ring
  have iGs : Integrable (fun g => G' g g) γ :=
    AdversarialBco.Body.integrable_of_abs_le_exp _ (meas_apply_self G G' hG).aestronglyMeasurable AG 2 hself
  have iG : Integrable G γ :=
    AdversarialBco.Body.integrable_of_abs_le_exp _ hGc'.aestronglyMeasurable AG 1 fun g => (hGb g).1
  have iX : Integrable (fun g => G' g g - G g + G 0) γ := (iGs.sub iG).add (integrable_const _)
  have iXi : Integrable (fun g => if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) γ := by
    have := iX.indicator (measurableSet_lt (measurable_const (a := (0 : ℝ))) hinner.measurable)
    refine this.congr (Eventually.of_forall fun g => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hXnn : ∀ g, 0 ≤ G' g g - G g + G 0 := fun g => by
    have := AdversarialBco.convexOn_ge_of_hasFDerivAt G (G' g) hGc g (hG g) 0
    rw [zero_sub, map_neg] at this
    linarith
  have hG'm : Measurable G' := by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]; exact measurable_fderiv ℝ G
  have htr := AdversarialBco.Body.integral_fderiv_self G' hG'm L1 hG'b lam hS2
  have hD : ∫ g, (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ∂γ ≤ lam * d := by
    have h1 := integral_mono iXi iX fun g => by
      show (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ≤ G' g g - G g + G 0
      split_ifs
      · exact le_rfl
      · exact hXnn g
    have eX : ∫ g, (G' g g - G g + G 0) ∂γ = lam * d - ∫ g, G g ∂γ + G 0 := by
      rw [integral_add (f := fun g => G' g g - G g) (g := fun _ => G 0) (iGs.sub iG) (integrable_const _),
        integral_sub (f := fun g => G' g g) (g := G) iGs iG, integral_const, probReal_univ, one_smul, htr]
    linarith
  -- the second-order term
  have hG1 : ∀ g, HasFDerivAt (fun x => G' x u) ((G'' g).flip u) g := fun g => by
    have := (hG' g).clm_apply (hasFDerivAt_const u g)
    simpa using this
  have hL1u : ∀ g, |G' g u| ≤ L1 := fun g => by
    rw [← Real.norm_eq_abs]; exact ((G' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hG'b g)
  have hMu : ∀ g, ‖(G'' g).flip u‖ ≤ M := fun g =>
    ((G'' g).flip.le_opNorm u).trans (by rw [ContinuousLinearMap.opNorm_flip, hu, mul_one]; exact hG''b g)
  have hS2u : ∫ g, ⟪u, g⟫ * G' g u ∂γ = lam := by
    rw [hS2 u u, real_inner_self_eq_norm_sq, hu]; ring
  have H := half_std u hu (fun x => G' x u) (fun g => (G'' g).flip u) hG1 L1 M hL1u hMu
    (fun g => by simpa using hmono g u) lam T hT (hS1 u) hS2u
  -- the bracket
  have hphiT := phi_pos T
  set Mt := Qtail T / phi T with hMt
  have hMt1 : 1 / (1 + T) ≤ Mt := by
    rw [hMt, le_div_iff₀ hphiT, one_div_mul_eq_div]; exact mills_lower T hT
  have hMt0 : 0 ≤ Mt := le_trans (by positivity) hMt1
  have hlamd : lam * d = h / 16 := by rw [hlam]; field_simp
  set B := h / 2 / R * kappa + ∫ g, kfun ⟪u, g⟫ * G' g u ∂γ -
    (∫ g, (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ∂γ) / R with hB_def
  have hB : (kappa / 2 - 1 / 16) * h / R + kappa * Mt * h / (32 * d) ≤ B := by
    have e1 : (∫ g, (if 0 < ⟪u, g⟫ then G' g g - G g + G 0 else 0) ∂γ) / R ≤ h / 16 / R :=
      div_le_div_of_nonneg_right (hlamd ▸ hD) hR.le
    have e2 : kappa * Mt * h / (32 * d) ≤ ∫ g, kfun ⟪u, g⟫ * G' g u ∂γ := by
      refine le_trans ?_ H
      have hl2 : h / (32 * d) ≤ lam - 2 * L1 * phi T := by
        have : lam = 2 * (h / (32 * d)) := by rw [hlam]; ring
        linarith
      calc kappa * Mt * h / (32 * d) = kappa * Mt * (h / (32 * d)) := by ring
        _ ≤ kappa * Mt * (lam - 2 * L1 * phi T) :=
            mul_le_mul_of_nonneg_left hl2 (mul_nonneg (by linarith) hMt0)
    have e3 : (kappa / 2 - 1 / 16) * h / R = h / 2 / R * kappa - h / 16 / R := by ring
    rw [hB_def, e3]
    linarith
  have hcore := core_bracket kappa d R h T Mt B hκl (by linarith) hdR hR hh hT hMt1 hB
  -- the right side
  set ω := min 1 (R / Real.sqrt d) with hω
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hω0 : 0 ≤ ω := le_min zero_le_one (div_nonneg hR.le hsd.le)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hωR : ω ^ 2 ≤ R ^ 2 / d := by
    have : ω ≤ R / Real.sqrt d := min_le_right _ _
    calc ω ^ 2 ≤ (R / Real.sqrt d) ^ 2 := pow_le_pow_left₀ hω0 this 2
      _ = R ^ 2 / d := by rw [div_pow, Real.sq_sqrt hd0.le]
  set sc : EuclideanSpace ℝ (Fin d) → ℝ := fun g => if 0 < ⟪u, g⟫ then (‖g‖ ^ 2 - (d : ℝ) - 1) / R -
      kfun ⟪u, g⟫ * ⟪u, g⟫ + (if ⟪u, g⟫ < 1 then 1 else 0) else 0 with hsc
  obtain ⟨isc, hsc2⟩ := score_sq_std u hu R hR
  have hscm : Measurable sc := by
    refine Measurable.ite (measurableSet_lt measurable_const hinner.measurable) ?_ measurable_const
    refine Measurable.add ?_ (Measurable.ite (measurableSet_lt hinner.measurable measurable_const)
      measurable_const measurable_const)
    exact ((((continuous_norm.pow 2).sub continuous_const).sub continuous_const).div_const R).measurable.sub
      ((continuous_kfun.comp hinner).mul hinner).measurable
  have hDc : Continuous fun g => F g - G g := hFc'.sub hGc'
  have hDb : ∀ g, |F g - G g| ≤ (|F 0 - G 0| + |L1 + L1|) * Real.exp (1 * ‖g‖) := fun g => by
    have hD' : ∀ g, HasFDerivAt (fun g => F g - G g) (F' g - G' g) g := fun g => (hF g).sub (hG g)
    have hDb' : ∀ g, ‖F' g - G' g‖ ≤ L1 + L1 := fun g => (norm_sub_le _ _).trans (add_le_add (hF'b g) (hG'b g))
    have := (AdversarialBco.Body.abs_le_of_norm_fderiv_le _ _ hD' (L1 + L1) hDb' g).1
    beta_reduce at this
    exact this
  have iD2 : Integrable (fun g => (F g - G g) ^ 2) γ := by
    refine AdversarialBco.Body.integrable_of_abs_le_exp _ (hDc.pow 2).aestronglyMeasurable
      ((|F 0 - G 0| + |L1 + L1|) ^ 2) 2 fun g => ?_
    have := hDb g
    rw [abs_pow, show (2 : ℝ) * ‖g‖ = 1 * ‖g‖ + 1 * ‖g‖ by ring, Real.exp_add]
    calc |F g - G g| ^ 2 ≤ ((|F 0 - G 0| + |L1 + L1|) * Real.exp (1 * ‖g‖)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = _ := by ring
  have iDs : Integrable (fun g => (F g - G g) * sc g) γ := by
    refine ((iD2.add isc).div_const 2).mono' (hDc.aestronglyMeasurable.mul hscm.aestronglyMeasurable)
      (Eventually.of_forall fun g => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul]
    have h2 := two_mul_le_add_sq |F g - G g| |sc g|
    rw [sq_abs, sq_abs] at h2
    linarith only [h2]
  have hCS := AdversarialBco.Body.sq_integral_mul_le γ (fun g => F g - G g) sc iD2 isc iDs
  set X := ∫ g, (F g - G g) ^ 2 ∂γ with hX
  have hX0 : 0 ≤ X := integral_nonneg fun g => sq_nonneg _
  set P := ω * ∫ g, (F g - G g) * sc g ∂γ with hP
  set Q := ω * ((F 0 - G 0) / (2 * R)) with hQ
  have hPQ : min 1 (R / Real.sqrt d) * B ≤ P + Q := by
    rw [← hω, hP, hQ, ← mul_add]
    exact mul_le_mul_of_nonneg_left I hω0
  have hP2 : P ^ 2 ≤ (3 + 2 * kappa2) * X := by
    have hs0 : 0 ≤ ∫ g, sc g ^ 2 ∂γ := integral_nonneg fun g => sq_nonneg _
    have hω2 : ω ^ 2 * ∫ g, sc g ^ 2 ∂γ ≤ 3 + 2 * kappa2 := by
      have hω2' : ω ^ 2 ≤ 1 := pow_le_one₀ hω0 hω1
      calc ω ^ 2 * ∫ g, sc g ^ 2 ∂γ ≤ ω ^ 2 * ((2 * (d : ℝ) + 1) / R ^ 2 + 2 * kappa2) :=
            mul_le_mul_of_nonneg_left hsc2 (sq_nonneg _)
        _ = ω ^ 2 * (2 * (d : ℝ) + 1) / R ^ 2 + ω ^ 2 * (2 * kappa2) := by ring
        _ ≤ R ^ 2 / d * (2 * (d : ℝ) + 1) / R ^ 2 + 1 * (2 * kappa2) := by
            refine add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hωR (by linarith))
              (sq_nonneg R)) (mul_le_mul_of_nonneg_right hω2' (by linarith))
        _ = (2 * (d : ℝ) + 1) / d + 2 * kappa2 := by field_simp
        _ ≤ 3 + 2 * kappa2 := by
            have : (2 * (d : ℝ) + 1) / d ≤ 3 := by rw [div_le_iff₀ hd0]; linarith
            linarith
    calc P ^ 2 = ω ^ 2 * (∫ g, (F g - G g) * sc g ∂γ) ^ 2 := by rw [hP]; ring
      _ ≤ ω ^ 2 * (X * ∫ g, sc g ^ 2 ∂γ) := mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ = X * (ω ^ 2 * ∫ g, sc g ^ 2 ∂γ) := by ring
      _ ≤ X * (3 + 2 * kappa2) := mul_le_mul_of_nonneg_left hω2 hX0
      _ = (3 + 2 * kappa2) * X := by ring
  have hQ2 : Q ^ 2 ≤ 1 / (4 * d) * (F 0 - G 0) ^ 2 := by
    calc Q ^ 2 = ω ^ 2 * (F 0 - G 0) ^ 2 / (4 * R ^ 2) := by rw [hQ]; ring
      _ ≤ R ^ 2 / d * (F 0 - G 0) ^ 2 / (4 * R ^ 2) := by gcongr
      _ = 1 / (4 * d) * (F 0 - G 0) ^ 2 := by field_simp
  have hℓ : 0 ≤ kappa / 32 * h / ((1 + T) * d) := by
    have : 0 < kappa := by linarith
    positivity
  exact core_sq_arith _ P Q X _ _ _ (by linarith) (by positivity) hℓ (hcore.trans hPQ) hP2 hQ2

end AdversarialBco.Body2
