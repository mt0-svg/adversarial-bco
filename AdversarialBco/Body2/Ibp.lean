/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# Lemma 3.7 (integration by parts on a half space), in the coordinates of the standard Gaussian

With `x = b + S Z`, `G(z) = F(b + S z)` and `u = σ S^{-1} e` (a unit vector, `ζ = σ ⟪u, Z⟫`):
(a) is `ibp_a` and (b) is `ibp_b` (with `B = σ β`, divided by `σ`). Both come from the Stein identities of
`AdversarialBco.Body` (`stein_radial`, `stein_ramp`) applied to smooth approximations of the indicator and of the hinge,
and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2

/-- The smooth transition of Mathlib: derivative everywhere, bounded, zero outside `[0, 1]`. -/
theorem st_facts : ∃ C : ℝ, 0 ≤ C ∧ (∀ t, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t) ∧
    (∀ t, |deriv Real.smoothTransition t| ≤ C) ∧ (∀ t, t < 0 ∨ 1 < t → deriv Real.smoothTransition t = 0) ∧
    Continuous (deriv Real.smoothTransition) := by
  have hc1 : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hd : ∀ t, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t := fun t =>
    ((hc1.differentiable one_ne_zero) t).hasDerivAt
  have hcont : Continuous (deriv Real.smoothTransition) := hc1.continuous_deriv le_rfl
  have h0 : ∀ t, t < 0 ∨ 1 < t → deriv Real.smoothTransition t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
        (eventually_lt_nhds ht).mono fun s hs => Real.smoothTransition.zero_of_nonpos hs.le
      rw [this.deriv_eq, deriv_const]
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
        (eventually_gt_nhds ht).mono fun s hs => Real.smoothTransition.one_of_one_le hs.le
      rw [this.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, hd, fun t => ?_, h0, hcont⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · rw [← Real.norm_eq_abs]; exact (hC t ht).trans (le_max_left _ _)
  · have : t < 0 ∨ 1 < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht; exact ht
    rw [h0 t this, abs_zero]; exact le_max_right _ _

/-- `s(n t) → 1{t > 0}`. -/
theorem st_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => Real.smoothTransition (n * t)) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  split_ifs with ht
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have : 1 ≤ (n : ℝ) * t := by
      have h1 : (1 / t) * t = 1 := by field_simp
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact (Real.smoothTransition.one_of_one_le this).symm
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    exact (Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (not_lt.1 ht))).symm

/-- `s'(n t) (n t) → 0`, bounded by `C`. -/
theorem st_deriv_tendsto (C : ℝ) (hstb : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    (hst0 : ∀ t, t < 0 ∨ 1 < t → deriv Real.smoothTransition t = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => deriv Real.smoothTransition (n * t) * (n * t)) atTop (𝓝 0) ∧
      ∀ n : ℕ, |deriv Real.smoothTransition (n * t) * (n * t)| ≤ C := by
  refine ⟨?_, fun n => ?_⟩
  · rcases lt_trichotomy t 0 with ht | ht | ht
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) * t < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hn) ht
      rw [hst0 _ (Or.inl this), zero_mul]
    · subst ht; simp
    · obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have : 1 < (n : ℝ) * t := by
        have h1 : (1 / t) * t = 1 := by field_simp
        have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      rw [hst0 _ (Or.inr this), zero_mul]
  · by_cases h : (n : ℝ) * t < 0 ∨ 1 < (n : ℝ) * t
    · rw [hst0 _ h, zero_mul, abs_zero]; exact (abs_nonneg _).trans (hstb 0)
    · simp only [not_or, not_lt] at h
      rw [abs_mul]
      have h1 : |(n : ℝ) * t| ≤ 1 := abs_le.2 ⟨by linarith, h.2⟩
      calc |deriv Real.smoothTransition (n * t)| * |(n : ℝ) * t| ≤ C * 1 :=
            mul_le_mul (hstb _) h1 (abs_nonneg _) ((abs_nonneg _).trans (hstb 0))
        _ = C := mul_one C

/-- `g ↦ G'(g) g` is measurable for a differentiable `G`. -/
theorem meas_apply_self {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ g, HasFDerivAt G (G' g) g) :
    Measurable fun g => G' g g := by
  have hm : ∀ v, Measurable fun g => G' g v := fun v => by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G v
  have e : (fun g => G' g g) =
      fun g => ∑ i, ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * G' g (EuclideanSpace.single i 1) :=
    funext fun g => AdversarialBco.Body.apply_eq_sum_inner (G' g) g
  rw [e]
  exact Finset.measurable_sum _ fun i _ => (continuous_const.inner continuous_id).measurable.mul (hm _)

theorem lin_exp_bound (A B C x : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    |A * Real.exp (B * x) * (x + C)| ≤ A * (1 + C) * Real.exp ((B + 1) * x) := by
  have he := Real.add_one_le_exp x
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hE : 0 ≤ Real.exp (B * x) := (Real.exp_pos _).le
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA hE) (by linarith))]
  have h : x + C ≤ (1 + C) * Real.exp x := by nlinarith
  calc A * Real.exp (B * x) * (x + C) ≤ A * Real.exp (B * x) * ((1 + C) * Real.exp x) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hA hE)
    _ = A * (1 + C) * Real.exp ((B + 1) * x) := by rw [show (B + 1) * x = B * x + x by ring, Real.exp_add]; ring

theorem sq_exp_bound (A B D x y : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hx : 0 ≤ x)
    (hy : |y| ≤ A * Real.exp (B * x)) :
    |y * (x ^ 2 - D)| ≤ A * (1 + D) * Real.exp ((B + 2) * x) := by
  have he := Real.add_one_le_exp x
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hE : 0 ≤ Real.exp (B * x) := (Real.exp_pos _).le
  have hee : 1 ≤ Real.exp x * Real.exp x := by nlinarith
  have hxx : x * x ≤ Real.exp x * Real.exp x := mul_self_le_mul_self hx (by linarith)
  have h1 : |x ^ 2 - D| ≤ (1 + D) * (Real.exp x * Real.exp x) := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul]
  calc |y| * |x ^ 2 - D| ≤ A * Real.exp (B * x) * ((1 + D) * (Real.exp x * Real.exp x)) :=
        mul_le_mul hy h1 (abs_nonneg _) (mul_nonneg hA hE)
    _ = A * (1 + D) * Real.exp ((B + 2) * x) := by
        rw [show (B + 2) * x = B * x + x + x by ring, Real.exp_add, Real.exp_add]; ring

/-- Lemma 3.7 (a) in the coordinates of the standard Gaussian: for a half space `{⟪u, g⟫ > 0}` through `0`,
`E[1{⟪u,Z⟫>0} ⟪∇G(Z), Z⟫] = E[1{⟪u,Z⟫>0} G(Z) (|Z|^2 - d)]`. -/
theorem ibp_a {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ g, HasFDerivAt G (G' g) g)
    (A B : ℝ) (hb : ∀ g, |G g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖G' g‖ ≤ A * Real.exp (B * ‖g‖)) :
    ∫ g, (if 0 < ⟪u, g⟫ then G' g g else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, (if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨C, hC0, hd, hstb, hst0, -⟩ := st_facts
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans (hb 0); simpa using this
  have hs1 : ∀ t, |Real.smoothTransition t| ≤ 1 := fun t =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg t], Real.smoothTransition.le_one t⟩
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hG'm : Measurable fun g => G' g g := meas_apply_self G G' hG
  have hs'm : Measurable (deriv Real.smoothTransition) := measurable_deriv _
  have hsn : ∀ n : ℕ, Continuous fun g : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (n * ⟪u, g⟫) :=
    fun n => Real.smoothTransition.continuous.comp (continuous_const.mul hinner)
  have hψ : ∀ n : ℕ, ∀ t, HasDerivAt (fun t => Real.smoothTransition (n * t))
      (deriv Real.smoothTransition (n * t) * n) t := fun n t => by
    have h1 : HasDerivAt (fun t => (n : ℝ) * t) n t := by simpa using (hasDerivAt_id t).const_mul (n : ℝ)
    exact (hd (n * t)).comp t h1
  have hH : ∀ n : ℕ, ∀ g, HasFDerivAt (fun g => Real.smoothTransition (n * ⟪u, g⟫) * G g)
      (Real.smoothTransition (n * ⟪u, g⟫) • G' g +
        G g • ((deriv Real.smoothTransition (n * ⟪u, g⟫) * n) • innerSL ℝ u)) g := fun n g =>
    ((hψ n _).comp_hasFDerivAt g ((innerSL ℝ u).hasFDerivAt)).mul (hG g)
  have hi : ‖innerSL ℝ u‖ = 1 := by rw [innerSL_apply_norm, hu]
  have hbH : ∀ n : ℕ, ∀ g, |Real.smoothTransition (n * ⟪u, g⟫) * G g| ≤
      ((1 + C * n) * A) * Real.exp (B * ‖g‖) := fun n g => by
    rw [abs_mul]
    have h0 : 0 ≤ A * Real.exp (B * ‖g‖) := mul_nonneg hA (Real.exp_pos _).le
    have h1 : 0 ≤ C * n := mul_nonneg hC0 (Nat.cast_nonneg n)
    calc |Real.smoothTransition (n * ⟪u, g⟫)| * |G g| ≤ 1 * (A * Real.exp (B * ‖g‖)) :=
          mul_le_mul (hs1 _) (hb g) (abs_nonneg _) zero_le_one
      _ ≤ ((1 + C * n) * A) * Real.exp (B * ‖g‖) := by nlinarith
  have hbH' : ∀ n : ℕ, ∀ g, ‖Real.smoothTransition (n * ⟪u, g⟫) • G' g +
        G g • ((deriv Real.smoothTransition (n * ⟪u, g⟫) * n) • innerSL ℝ u)‖ ≤
      ((1 + C * n) * A) * Real.exp (B * ‖g‖) := fun n g => by
    have h0 : 0 ≤ A * Real.exp (B * ‖g‖) := mul_nonneg hA (Real.exp_pos _).le
    calc _ ≤ ‖Real.smoothTransition (n * ⟪u, g⟫) • G' g‖ +
          ‖G g • ((deriv Real.smoothTransition (n * ⟪u, g⟫) * n) • innerSL ℝ u)‖ := norm_add_le _ _
      _ = |Real.smoothTransition (n * ⟪u, g⟫)| * ‖G' g‖ +
          |G g| * (|deriv Real.smoothTransition (n * ⟪u, g⟫)| * n) := by
          simp only [norm_smul, hi, Real.norm_eq_abs, mul_one, abs_mul, Nat.abs_cast]
      _ ≤ 1 * (A * Real.exp (B * ‖g‖)) + (A * Real.exp (B * ‖g‖)) * (C * n) :=
          add_le_add (mul_le_mul (hs1 _) (hb' g) (norm_nonneg _) zero_le_one)
            (mul_le_mul (hb g) (mul_le_mul_of_nonneg_right (hstb _) (Nat.cast_nonneg n)) (by positivity) h0)
      _ = ((1 + C * n) * A) * Real.exp (B * ‖g‖) := by ring
  have key : ∀ n : ℕ, ∫ g, (Real.smoothTransition (n * ⟪u, g⟫) * G' g g +
        G g * (deriv Real.smoothTransition (n * ⟪u, g⟫) * (n * ⟪u, g⟫))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, Real.smoothTransition (n * ⟪u, g⟫) * (G g * (‖g‖ ^ 2 - (d : ℝ)))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := fun n => by
    have h := AdversarialBco.Body.stein_radial _ _ (hH n) _ _ (hbH n) (hbH' n)
    have e1 : ∀ g, (Real.smoothTransition (n * ⟪u, g⟫) • G' g +
        G g • ((deriv Real.smoothTransition (n * ⟪u, g⟫) * n) • innerSL ℝ u)) g =
        Real.smoothTransition (n * ⟪u, g⟫) * G' g g +
          G g * (deriv Real.smoothTransition (n * ⟪u, g⟫) * (n * ⟪u, g⟫)) := fun g => by
      simp only [_root_.add_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
      ring
    refine (integral_congr_ae (Eventually.of_forall fun g => (e1 g).symm)).trans (h.trans ?_)
    congr 1; funext g; ring
  have iL : Integrable (fun g : EuclideanSpace ℝ (Fin d) => A * Real.exp (B * ‖g‖) * (‖g‖ + C))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_of_abs_le_exp _ (by fun_prop : Continuous fun g : EuclideanSpace ℝ (Fin d) =>
      A * Real.exp (B * ‖g‖) * (‖g‖ + C)).aestronglyMeasurable (A * (1 + C)) (B + 1)
      fun g => lin_exp_bound A B C ‖g‖ hA hC0 (norm_nonneg g)
  have hL := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => Real.smoothTransition (n * ⟪u, g⟫) * G' g g +
        G g * (deriv Real.smoothTransition (n * ⟪u, g⟫) * (n * ⟪u, g⟫)))
    (f := fun g => if 0 < ⟪u, g⟫ then G' g g else 0)
    (fun g => A * Real.exp (B * ‖g‖) * (‖g‖ + C))
    (fun n => (((hsn n).measurable.mul hG'm).add (hGc.measurable.mul
      ((hs'm.comp (continuous_const.mul hinner).measurable).mul
        (continuous_const.mul hinner).measurable))).aestronglyMeasurable)
    iL
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      have h0 : 0 ≤ A * Real.exp (B * ‖g‖) := mul_nonneg hA (Real.exp_pos _).le
      have h1 : |G' g g| ≤ A * Real.exp (B * ‖g‖) * ‖g‖ := by
        rw [← Real.norm_eq_abs]
        exact ((G' g).le_opNorm g).trans (mul_le_mul_of_nonneg_right (hb' g) (norm_nonneg _))
      have h2 := (st_deriv_tendsto C hstb hst0 ⟪u, g⟫).2 n
      calc _ ≤ |Real.smoothTransition (n * ⟪u, g⟫) * G' g g| +
            |G g * (deriv Real.smoothTransition (n * ⟪u, g⟫) * (n * ⟪u, g⟫))| := abs_add_le _ _
        _ = |Real.smoothTransition (n * ⟪u, g⟫)| * |G' g g| +
            |G g| * |deriv Real.smoothTransition (n * ⟪u, g⟫) * (n * ⟪u, g⟫)| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * (A * Real.exp (B * ‖g‖) * ‖g‖) + A * Real.exp (B * ‖g‖) * C :=
            add_le_add (mul_le_mul (hs1 _) h1 (abs_nonneg _) zero_le_one)
              (mul_le_mul (hb g) h2 (abs_nonneg _) h0)
        _ = A * Real.exp (B * ‖g‖) * (‖g‖ + C) := by ring)
    (Eventually.of_forall fun g => by
      have h1 := ((st_tendsto ⟪u, g⟫).mul (tendsto_const_nhds (x := G' g g))).add
        ((tendsto_const_nhds (x := G g)).mul (st_deriv_tendsto C hstb hst0 ⟪u, g⟫).1)
      have h2 : (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0) * G' g g + G g * 0 =
          if 0 < ⟪u, g⟫ then G' g g else 0 := by
        split_ifs <;> ring
      rwa [h2] at h1)
  have iR : Integrable (fun g => G g * (‖g‖ ^ 2 - (d : ℝ))) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_of_abs_le_exp _ (hGc.mul (by fun_prop)).aestronglyMeasurable
      (A * (1 + d)) (B + 2) fun g => sq_exp_bound A B d ‖g‖ (G g) hA (Nat.cast_nonneg d) (norm_nonneg g) (hb g)
  have hR := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => Real.smoothTransition (n * ⟪u, g⟫) * (G g * (‖g‖ ^ 2 - (d : ℝ))))
    (f := fun g => if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0)
    (fun g => |G g * (‖g‖ ^ 2 - (d : ℝ))|)
    (fun n => ((hsn n).mul (hGc.mul (by fun_prop))).aestronglyMeasurable)
    iR.abs
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hs1 _))
    (Eventually.of_forall fun g => by
      have h1 := (st_tendsto ⟪u, g⟫).mul (tendsto_const_nhds (x := G g * (‖g‖ ^ 2 - (d : ℝ))))
      have h2 : (if 0 < ⟪u, g⟫ then (1 : ℝ) else 0) * (G g * (‖g‖ ^ 2 - (d : ℝ))) =
          if 0 < ⟪u, g⟫ then G g * (‖g‖ ^ 2 - (d : ℝ)) else 0 := by
        split_ifs <;> ring
      rwa [h2] at h1)
  exact tendsto_nhds_unique (hL.congr key) hR

theorem abs_sub_le' (t a : ℝ) : |t - a| ≤ |t| + |a| := by
  simpa [sub_eq_add_neg] using abs_add_le t (-a)

theorem hinge_le_exp (t a : ℝ) : |max (t - a) 0| ≤ (1 + |a|) * Real.exp (1 * |t|) := by
  have he := Real.add_one_le_exp |t|
  have he1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have h : |max (t - a) 0| ≤ |t - a| := by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have h2 := abs_sub_le' t a
  rw [one_mul]; nlinarith [abs_nonneg a]

theorem quad_le_exp (t a c : ℝ) (hc : 0 ≤ c) : |t| * |t - a| + c ≤ (1 + |a| + c) * Real.exp (2 * |t|) := by
  have he := Real.add_one_le_exp |t|
  have he1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have h2 := abs_sub_le' t a
  have h3 : |t| * |t - a| ≤ Real.exp |t| * ((1 + |a|) * Real.exp |t|) :=
    mul_le_mul (by linarith) (by nlinarith [abs_nonneg a]) (abs_nonneg _) (by positivity)
  have hee : 1 ≤ Real.exp |t| * Real.exp |t| := by nlinarith
  have h4 : c ≤ c * (Real.exp |t| * Real.exp |t|) := le_mul_of_one_le_right hc hee
  rw [show 2 * |t| = |t| + |t| by ring, Real.exp_add]
  calc |t| * |t - a| + c ≤ (1 + |a|) * (Real.exp |t| * Real.exp |t|) + c * (Real.exp |t| * Real.exp |t|) :=
        add_le_add (h3.trans_eq (by ring)) h4
    _ = (1 + |a| + c) * (Real.exp |t| * Real.exp |t|) := by ring

/-- Stein's identity for a hinge in the direction `u`:
`E[(⟪u,Z⟫ - a)_+ ∂_u G(Z)] = E[G(Z) ((⟪u,Z⟫ - a)_+ ⟪u,Z⟫ - 1{⟪u,Z⟫ > a})]`. -/
theorem stein_hinge {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ g, HasFDerivAt G (G' g) g)
    (A B : ℝ) (hb : ∀ g, |G g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖G' g‖ ≤ A * Real.exp (B * ‖g‖)) (a : ℝ) :
    ∫ g, max (⟪u, g⟫ - a) 0 * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, G g * (max (⟪u, g⟫ - a) 0 * ⟪u, g⟫ - if a < ⟪u, g⟫ then 1 else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨C, hC0, hd, hstb, hst0, hs'c⟩ := st_facts
  have hs1 : ∀ t, |Real.smoothTransition t| ≤ 1 := fun t =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg t], Real.smoothTransition.le_one t⟩
  have hsc : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hG'um : Measurable fun g => G' g u := by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G u
  have hG'u : ∀ g, |G' g u| ≤ A * Real.exp (B * ‖g‖) := fun g => by
    rw [← Real.norm_eq_abs]; exact ((G' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hb' g)
  set ψ : ℕ → ℝ → ℝ := fun n t => (t - a) * Real.smoothTransition (n * (t - a)) with hψdef
  set ψ' : ℕ → ℝ → ℝ := fun n t => Real.smoothTransition (n * (t - a)) +
    deriv Real.smoothTransition (n * (t - a)) * (n * (t - a)) with hψ'def
  have hψc : ∀ n, Continuous (ψ n) := fun n =>
    (continuous_id.sub continuous_const).mul (hsc.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  have hψ'c : ∀ n, Continuous (ψ' n) := fun n =>
    (hsc.comp (continuous_const.mul (continuous_id.sub continuous_const))).add
      ((hs'c.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
        (continuous_const.mul (continuous_id.sub continuous_const)))
  have hψd : ∀ n t, HasDerivAt (ψ n) (ψ' n t) t := fun n t => by
    have h1 : HasDerivAt (fun t : ℝ => t - a) 1 t := (hasDerivAt_id' t).sub_const a
    have h2 : HasDerivAt (fun t : ℝ => (n : ℝ) * (t - a)) n t := by simpa using h1.const_mul (n : ℝ)
    have h3 : HasDerivAt (fun t => Real.smoothTransition (n * (t - a)))
        (deriv Real.smoothTransition (n * (t - a)) * n) t := (hd _).comp t h2
    exact (h1.mul h3).congr_deriv (by simp only [hψ'def]; ring)
  have hψle : ∀ n t, |ψ n t| ≤ |t - a| := fun n t => by
    simp only [hψdef]; rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hs1 _)
  have hψ'le : ∀ n t, |ψ' n t| ≤ 1 + C := fun n t => by
    simp only [hψ'def]
    exact (abs_add_le _ _).trans (add_le_add (hs1 _) ((st_deriv_tendsto C hstb hst0 (t - a)).2 n))
  have hψb : ∀ n t, |ψ n t| ≤ (1 + |a| + C) * Real.exp (1 * |t|) := fun n t => by
    have he1 : 1 ≤ Real.exp (1 * |t|) := Real.one_le_exp (by positivity)
    have := hinge_le_exp t a
    have h2 : |t - a| ≤ (1 + |a|) * Real.exp (1 * |t|) := by
      have he := Real.add_one_le_exp |t|
      have := abs_sub_le' t a
      rw [one_mul] at he1 ⊢; nlinarith [abs_nonneg a]
    nlinarith [hψle n t, Real.exp_pos (1 * |t|)]
  have hψ'b : ∀ n t, |ψ' n t| ≤ (1 + |a| + C) * Real.exp (1 * |t|) := fun n t => by
    have he1 : 1 ≤ Real.exp (1 * |t|) := Real.one_le_exp (by positivity)
    nlinarith [hψ'le n t, abs_nonneg a]
  have key : ∀ n : ℕ, ∫ g, ψ n ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, (⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g) - ψ' n ⟪u, g⟫ * G g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      fun n => by
    have h := AdversarialBco.Body.stein_ramp u hu (ψ n) (ψ' n) (hψd n) (1 + |a| + C) 1 zero_le_one (hψb n)
      (hψ'b n) G G' hG A B hb hb'
    have i1 : Integrable (fun g => ⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (AdversarialBco.Body.integrable_ramp u hu (fun t => t * ψ n t) (continuous_id.mul (hψc n)).measurable
        (1 + |a| + 0) 2 zero_le_two (fun t => by
          rw [abs_mul]
          refine le_trans ?_ (quad_le_exp t a 0 le_rfl)
          rw [add_zero]; exact mul_le_mul_of_nonneg_left (hψle n t) (abs_nonneg _))
        G hGc.aestronglyMeasurable A B hb).congr (Eventually.of_forall fun g => by simp only; ring)
    have i2 : Integrable (fun g => ψ' n ⟪u, g⟫ * G g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      AdversarialBco.Body.integrable_ramp u hu (ψ' n) (hψ'c n).measurable (1 + |a| + C) 1 zero_le_one (hψ'b n)
        G hGc.aestronglyMeasurable A B hb
    rw [integral_sub i1 i2, h]; ring
  have iL : Integrable (fun g => |⟪u, g⟫ - a| * |G' g u|) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu (fun t => |t - a|) (continuous_id.sub continuous_const).abs.measurable
      (1 + |a|) 1 zero_le_one (fun t => by
        have he := Real.add_one_le_exp |t|
        have := abs_sub_le' t a
        rw [abs_abs, one_mul]; nlinarith [abs_nonneg a, Real.one_le_exp (abs_nonneg t)])
      (fun g => |G' g u|) hG'um.abs.aestronglyMeasurable A B (fun g => by rw [abs_abs]; exact hG'u g)
  have hL := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => ψ n ⟪u, g⟫ * G' g u)
    (f := fun g => max (⟪u, g⟫ - a) 0 * G' g u)
    (fun g => |⟪u, g⟫ - a| * |G' g u|)
    (fun n => (((hψc n).comp hinner).measurable.mul hG'um).aestronglyMeasurable)
    iL
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hψle n _) (abs_nonneg _))
    (Eventually.of_forall fun g => by
      have h1 := ((tendsto_const_nhds (x := ⟪u, g⟫ - a)).mul (st_tendsto (⟪u, g⟫ - a))).mul
        (tendsto_const_nhds (x := G' g u))
      have h2 : (⟪u, g⟫ - a) * (if 0 < ⟪u, g⟫ - a then (1 : ℝ) else 0) * G' g u = max (⟪u, g⟫ - a) 0 * G' g u := by
        split_ifs with h
        · rw [max_eq_left h.le]; ring
        · rw [max_eq_right (not_lt.1 h)]; ring
      rw [h2] at h1
      exact h1)
  have iR : Integrable (fun g => (|⟪u, g⟫| * |⟪u, g⟫ - a| + (1 + C)) * |G g|)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu (fun t => |t| * |t - a| + (1 + C))
      ((continuous_abs.mul (continuous_id.sub continuous_const).abs).add continuous_const).measurable
      (1 + |a| + (1 + C)) 2 zero_le_two (fun t => by
        rw [abs_of_nonneg (by positivity)]; exact quad_le_exp t a (1 + C) (by linarith))
      (fun g => |G g|) hGc.abs.aestronglyMeasurable A B (fun g => by rw [abs_abs]; exact hb g)
  have hR := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => ⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g) - ψ' n ⟪u, g⟫ * G g)
    (f := fun g => G g * (max (⟪u, g⟫ - a) 0 * ⟪u, g⟫ - if a < ⟪u, g⟫ then 1 else 0))
    (fun g => (|⟪u, g⟫| * |⟪u, g⟫ - a| + (1 + C)) * |G g|)
    (fun n => ((hinner.mul (((hψc n).comp hinner).mul hGc)).sub
      (((hψ'c n).comp hinner).mul hGc)).aestronglyMeasurable)
    iR
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      calc _ ≤ |⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g)| + |ψ' n ⟪u, g⟫ * G g| := abs_sub_le' _ _
        _ = |⟪u, g⟫| * |ψ n ⟪u, g⟫| * |G g| + |ψ' n ⟪u, g⟫| * |G g| := by
            rw [abs_mul, abs_mul, abs_mul (ψ' n _)]; ring
        _ ≤ |⟪u, g⟫| * |⟪u, g⟫ - a| * |G g| + (1 + C) * |G g| :=
            add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hψle n _) (abs_nonneg _))
              (abs_nonneg _)) (mul_le_mul_of_nonneg_right (hψ'le n _) (abs_nonneg _))
        _ = _ := by ring)
    (Eventually.of_forall fun g => by
      have hA := ((tendsto_const_nhds (x := ⟪u, g⟫ - a)).mul (st_tendsto (⟪u, g⟫ - a)))
      have hB := (st_tendsto (⟪u, g⟫ - a)).add (st_deriv_tendsto C hstb hst0 (⟪u, g⟫ - a)).1
      have h1 := ((tendsto_const_nhds (x := ⟪u, g⟫)).mul (hA.mul (tendsto_const_nhds (x := G g)))).sub
        (hB.mul (tendsto_const_nhds (x := G g)))
      have h2 : ⟪u, g⟫ * ((⟪u, g⟫ - a) * (if 0 < ⟪u, g⟫ - a then (1 : ℝ) else 0) * G g) -
          ((if 0 < ⟪u, g⟫ - a then (1 : ℝ) else 0) + 0) * G g =
          G g * (max (⟪u, g⟫ - a) 0 * ⟪u, g⟫ - if a < ⟪u, g⟫ then 1 else 0) := by
        by_cases h : a < ⟪u, g⟫
        · rw [ite_eq_left (sub_pos.2 h), ite_eq_left h, max_eq_left (sub_pos.2 h).le]; ring
        · rw [ite_eq_right (by linarith), ite_eq_right h, max_eq_right (by linarith)]; ring
      rw [h2] at h1
      exact h1)
  exact tendsto_nhds_unique (hL.congr key) hR

/-- Lemma 3.7 (b) in the coordinates of the standard Gaussian, for the truncated ramp `min(⟪u,Z⟫_+, β)`:
`E[min(⟪u,Z⟫_+, β) ∂_u G(Z)] = E[G(Z) (min(⟪u,Z⟫_+, β) ⟪u,Z⟫ - 1{0 < ⟪u,Z⟫ < β})]`. -/
theorem ibp_b {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ g, HasFDerivAt G (G' g) g)
    (A B : ℝ) (hb : ∀ g, |G g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖G' g‖ ≤ A * Real.exp (B * ‖g‖))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∫ g, min (max ⟪u, g⟫ 0) β * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, G g * (min (max ⟪u, g⟫ 0) β * ⟪u, g⟫ - if 0 < ⟪u, g⟫ ∧ ⟪u, g⟫ < β then 1 else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hG'um : Measurable fun g => G' g u := by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G u
  have hG'u : ∀ g, |G' g u| ≤ A * Real.exp (B * ‖g‖) := fun g => by
    rw [← Real.norm_eq_abs]; exact ((G' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hb' g)
  have iH : ∀ a : ℝ, Integrable (fun g => max (⟪u, g⟫ - a) 0 * G' g u) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun a => AdversarialBco.Body.integrable_ramp u hu (fun t => max (t - a) 0)
      ((continuous_id.sub continuous_const).max continuous_const).measurable (1 + |a|) 1 zero_le_one
      (fun t => hinge_le_exp t a) (fun g => G' g u) hG'um.aestronglyMeasurable A B hG'u
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have iR : ∀ a : ℝ, Integrable (fun g => G g * (max (⟪u, g⟫ - a) 0 * ⟪u, g⟫ - if a < ⟪u, g⟫ then 1 else 0))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun a => by
    refine Integrable.mono' (AdversarialBco.Body.integrable_ramp u hu (fun t => |t| * |t - a| + (1 + 0))
      ((continuous_abs.mul (continuous_id.sub continuous_const).abs).add continuous_const).measurable
      (1 + |a| + (1 + 0)) 2 zero_le_two (fun t => by
        rw [abs_of_nonneg (by positivity)]; exact quad_le_exp t a (1 + 0) (by norm_num))
      (fun g => |G g|) hGc.abs.aestronglyMeasurable A B (fun g => by rw [abs_abs]; exact hb g)) ?_ ?_
    · exact (hGc.measurable.mul ((((hinner.sub continuous_const).max continuous_const).mul hinner).measurable.sub
        (Measurable.ite (measurableSet_lt measurable_const hinner.measurable) measurable_const
          measurable_const))).aestronglyMeasurable
    · refine Eventually.of_forall fun g => ?_
      rw [Real.norm_eq_abs, abs_mul, mul_comm (|G g|)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h1 : |max (⟪u, g⟫ - a) 0| ≤ |⟪u, g⟫ - a| := by
        rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
      have h2 : |(if a < ⟪u, g⟫ then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      calc _ ≤ |max (⟪u, g⟫ - a) 0 * ⟪u, g⟫| + |(if a < ⟪u, g⟫ then (1 : ℝ) else 0)| := abs_sub_le' _ _
        _ ≤ |⟪u, g⟫ - a| * |⟪u, g⟫| + 1 := by rw [abs_mul]; gcongr
        _ = _ := by ring
  have hmin : ∀ t : ℝ, min (max t 0) β = max (t - 0) 0 - max (t - β) 0 := fun t => by
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, min_eq_left hβ, sub_zero, max_eq_right h, max_eq_right (by linarith)]; ring
    · rcases le_total t β with h' | h'
      · rw [max_eq_left h, min_eq_left h', sub_zero, max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, min_eq_right h', sub_zero, max_eq_left h, max_eq_left (by linarith)]; ring
  have hnull : (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | ⟪u, g⟫ = β} = 0 := by
    have h := Measure.map_apply hinner.measurable (measurableSet_singleton β)
      (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    rw [AdversarialBco.Body.map_inner_stdGaussian u hu] at h
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [measure_singleton] at h
    exact h.symm
  have hae : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), ⟪u, g⟫ ≠ β := by
    rw [ae_iff]; simpa using hnull
  calc ∫ g, min (max ⟪u, g⟫ 0) β * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ g, (max (⟪u, g⟫ - 0) 0 * G' g u - max (⟪u, g⟫ - β) 0 * G' g u)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        congr 1; funext g; rw [hmin]; ring
    _ = ∫ g, G g * (max (⟪u, g⟫ - 0) 0 * ⟪u, g⟫ - if 0 < ⟪u, g⟫ then 1 else 0)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, G g * (max (⟪u, g⟫ - β) 0 * ⟪u, g⟫ - if β < ⟪u, g⟫ then 1 else 0)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_sub (iH 0) (iH β), stein_hinge u hu G G' hG A B hb hb' 0,
          stein_hinge u hu G G' hG A B hb hb' β]
    _ = ∫ g, (G g * (max (⟪u, g⟫ - 0) 0 * ⟪u, g⟫ - if 0 < ⟪u, g⟫ then 1 else 0) -
          G g * (max (⟪u, g⟫ - β) 0 * ⟪u, g⟫ - if β < ⟪u, g⟫ then 1 else 0))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_sub (iR 0) (iR β)]
    _ = _ := by
        refine integral_congr_ae (hae.mono fun g hg => ?_)
        dsimp only
        rw [hmin]
        by_cases h0 : 0 < ⟪u, g⟫
        · by_cases hβ' : ⟪u, g⟫ < β
          · rw [ite_eq_left h0, ite_eq_right (not_lt.2 hβ'.le), ite_eq_left ⟨h0, hβ'⟩]; ring
          · have : β < ⟪u, g⟫ := lt_of_le_of_ne (not_lt.1 hβ') (Ne.symm hg)
            rw [ite_eq_left h0, ite_eq_left this, ite_eq_right (fun h => hβ' h.2)]; ring
        · rw [ite_eq_right h0, ite_eq_right (by linarith), ite_eq_right (fun h => h0 h.1)]; ring

/-- Stein's identity for the positive part of a `C^1` profile `ρ` in the direction `u`:
`E[ρ(⟪u,Z⟫)_+ ∂_u G(Z)] = E[G(Z) (ρ(⟪u,Z⟫)_+ ⟪u,Z⟫ - 1{ρ(⟪u,Z⟫) > 0} ρ'(⟪u,Z⟫))]`. Only `ρ_+` and `ρ'` on `{ρ > 0}` need
a growth bound. -/
theorem stein_posPart {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ g, HasFDerivAt G (G' g) g)
    (A B : ℝ) (hb : ∀ g, |G g| ≤ A * Real.exp (B * ‖g‖)) (hb' : ∀ g, ‖G' g‖ ≤ A * Real.exp (B * ‖g‖))
    (ρ ρ' : ℝ → ℝ) (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hρ'c : Continuous ρ') (A2 B2 : ℝ) (hB2 : 0 ≤ B2)
    (hρb : ∀ t, max (ρ t) 0 ≤ A2 * Real.exp (B2 * |t|)) (hρb' : ∀ t, 0 < ρ t → |ρ' t| ≤ A2 * Real.exp (B2 * |t|)) :
    ∫ g, max (ρ ⟪u, g⟫) 0 * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, G g * (max (ρ ⟪u, g⟫) 0 * ⟪u, g⟫ - if 0 < ρ ⟪u, g⟫ then ρ' ⟪u, g⟫ else 0)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨C, hC0, hd, hstb, hst0, hs'c⟩ := st_facts
  have hs1 : ∀ t, |Real.smoothTransition t| ≤ 1 := fun t =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg t], Real.smoothTransition.le_one t⟩
  have hsc : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  have hinner : Continuous fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ := continuous_const.inner continuous_id
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun g => (hG g).continuousAt
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun t => (hρ t).continuousAt
  have hA2 : 0 ≤ A2 := by
    have := (le_max_right (ρ 0) 0).trans (hρb 0); simpa using this
  have hG'um : Measurable fun g => G' g u := by
    rw [show G' = fderiv ℝ G from funext fun g => (hG g).fderiv.symm]
    exact measurable_fderiv_apply_const ℝ G u
  have hG'u : ∀ g, |G' g u| ≤ A * Real.exp (B * ‖g‖) := fun g => by
    rw [← Real.norm_eq_abs]; exact ((G' g).le_opNorm u).trans (by rw [hu, mul_one]; exact hb' g)
  -- the factor `s(x) + s'(x) x`: bounded by `1 + C`, zero for `x ≤ 0`
  have hfac : ∀ x : ℝ, |Real.smoothTransition x + deriv Real.smoothTransition x * x| ≤ 1 + C := fun x => by
    have h := (st_deriv_tendsto C hstb hst0 x).2 1
    simp only [Nat.cast_one, one_mul] at h
    exact (abs_add_le _ _).trans (add_le_add (hs1 _) h)
  have hfac0 : ∀ x : ℝ, x ≤ 0 → Real.smoothTransition x + deriv Real.smoothTransition x * x = 0 := fun x hx => by
    rw [Real.smoothTransition.zero_of_nonpos hx, zero_add]
    rcases hx.lt_or_eq with h | h
    · rw [hst0 x (Or.inl h), zero_mul]
    · rw [h, mul_zero]
  set ψ : ℕ → ℝ → ℝ := fun n t => ρ t * Real.smoothTransition (n * ρ t) with hψdef
  set ψ' : ℕ → ℝ → ℝ := fun n t => ρ' t * (Real.smoothTransition (n * ρ t) +
    deriv Real.smoothTransition (n * ρ t) * (n * ρ t)) with hψ'def
  have hψc : ∀ n, Continuous (ψ n) := fun n => hρc.mul (hsc.comp (continuous_const.mul hρc))
  have hψ'c : ∀ n, Continuous (ψ' n) := fun n =>
    hρ'c.mul ((hsc.comp (continuous_const.mul hρc)).add
      ((hs'c.comp (continuous_const.mul hρc)).mul (continuous_const.mul hρc)))
  have hψd : ∀ n t, HasDerivAt (ψ n) (ψ' n t) t := fun n t => by
    have h2 : HasDerivAt (fun t => (n : ℝ) * ρ t) (n * ρ' t) t := (hρ t).const_mul (n : ℝ)
    have h3 : HasDerivAt (fun t => Real.smoothTransition (n * ρ t))
        (deriv Real.smoothTransition (n * ρ t) * (n * ρ' t)) t := (hd _).comp t h2
    exact ((hρ t).mul h3).congr_deriv (by simp only [hψ'def]; ring)
  have hψle : ∀ n t, |ψ n t| ≤ max (ρ t) 0 := fun n t => by
    simp only [hψdef]
    rcases le_or_gt (ρ t) 0 with h | h
    · rw [Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h), mul_zero,
        abs_zero]
      exact le_max_right _ _
    · rw [abs_mul, abs_of_pos h, max_eq_left h.le]; exact mul_le_of_le_one_right h.le (hs1 _)
  have hψ'le : ∀ n t, |ψ' n t| ≤ (1 + C) * (if 0 < ρ t then |ρ' t| else 0) := fun n t => by
    simp only [hψ'def]
    rcases le_or_gt (ρ t) 0 with h | h
    · rw [hfac0 _ (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h), mul_zero, abs_zero,
        ite_eq_right (not_lt.2 h), mul_zero]
    · rw [ite_eq_left h, abs_mul, mul_comm (1 + C)]
      exact mul_le_mul_of_nonneg_left (hfac _) (abs_nonneg _)
  have hite : ∀ t, (if 0 < ρ t then |ρ' t| else 0) ≤ A2 * Real.exp (B2 * |t|) := fun t => by
    split_ifs with h
    · exact hρb' t h
    · exact mul_nonneg hA2 (Real.exp_pos _).le
  have hψb : ∀ n t, |ψ n t| ≤ ((1 + C) * A2) * Real.exp (B2 * |t|) := fun n t => by
    have h0 : 0 ≤ A2 * Real.exp (B2 * |t|) := mul_nonneg hA2 (Real.exp_pos _).le
    nlinarith [hψle n t, hρb t]
  have hψ'b : ∀ n t, |ψ' n t| ≤ ((1 + C) * A2) * Real.exp (B2 * |t|) := fun n t => by
    have h0 : 0 ≤ (if 0 < ρ t then |ρ' t| else 0) := by split_ifs <;> simp
    calc |ψ' n t| ≤ (1 + C) * (if 0 < ρ t then |ρ' t| else 0) := hψ'le n t
      _ ≤ (1 + C) * (A2 * Real.exp (B2 * |t|)) := mul_le_mul_of_nonneg_left (hite t) (by linarith)
      _ = _ := by ring
  have htb : ∀ n t, |t * ψ n t| ≤ ((1 + C) * A2) * Real.exp ((B2 + 1) * |t|) := fun n t => by
    have he := Real.add_one_le_exp |t|
    have h1 : |t| * max (ρ t) 0 ≤ Real.exp |t| * (A2 * Real.exp (B2 * |t|)) :=
      mul_le_mul (by linarith) (hρb t) (le_max_right _ _) (Real.exp_pos _).le
    have h2 : 0 ≤ C * A2 * Real.exp ((B2 + 1) * |t|) := by positivity
    rw [abs_mul]
    calc |t| * |ψ n t| ≤ |t| * max (ρ t) 0 := mul_le_mul_of_nonneg_left (hψle n t) (abs_nonneg _)
      _ ≤ Real.exp |t| * (A2 * Real.exp (B2 * |t|)) := h1
      _ = A2 * Real.exp ((B2 + 1) * |t|) := by rw [add_mul, one_mul, Real.exp_add]; ring
      _ ≤ ((1 + C) * A2) * Real.exp ((B2 + 1) * |t|) := by nlinarith
  have key : ∀ n : ℕ, ∫ g, ψ n ⟪u, g⟫ * G' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, (⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g) - ψ' n ⟪u, g⟫ * G g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      fun n => by
    have h := AdversarialBco.Body.stein_ramp u hu (ψ n) (ψ' n) (hψd n) ((1 + C) * A2) B2 hB2 (hψb n)
      (hψ'b n) G G' hG A B hb hb'
    have i1 : Integrable (fun g => ⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (AdversarialBco.Body.integrable_ramp u hu (fun t => t * ψ n t) (continuous_id.mul (hψc n)).measurable
        ((1 + C) * A2) (B2 + 1) (by linarith) (htb n) G hGc.aestronglyMeasurable A B hb).congr
        (Eventually.of_forall fun g => by simp only; ring)
    have i2 : Integrable (fun g => ψ' n ⟪u, g⟫ * G g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      AdversarialBco.Body.integrable_ramp u hu (ψ' n) (hψ'c n).measurable ((1 + C) * A2) B2 hB2 (hψ'b n)
        G hGc.aestronglyMeasurable A B hb
    rw [integral_sub i1 i2, h]; ring
  have hmaxc : Continuous fun t => max (ρ t) 0 := hρc.max continuous_const
  have iL : Integrable (fun g => max (ρ ⟪u, g⟫) 0 * |G' g u|) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu (fun t => max (ρ t) 0) hmaxc.measurable A2 B2 hB2
      (fun t => by rw [abs_of_nonneg (le_max_right _ _)]; exact hρb t)
      (fun g => |G' g u|) hG'um.abs.aestronglyMeasurable A B (fun g => by rw [abs_abs]; exact hG'u g)
  have hL := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => ψ n ⟪u, g⟫ * G' g u)
    (f := fun g => max (ρ ⟪u, g⟫) 0 * G' g u)
    (fun g => max (ρ ⟪u, g⟫) 0 * |G' g u|)
    (fun n => (((hψc n).comp hinner).measurable.mul hG'um).aestronglyMeasurable)
    iL
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hψle n _) (abs_nonneg _))
    (Eventually.of_forall fun g => by
      have h1 := ((tendsto_const_nhds (x := ρ ⟪u, g⟫)).mul (st_tendsto (ρ ⟪u, g⟫))).mul
        (tendsto_const_nhds (x := G' g u))
      have h2 : ρ ⟪u, g⟫ * (if 0 < ρ ⟪u, g⟫ then (1 : ℝ) else 0) * G' g u = max (ρ ⟪u, g⟫) 0 * G' g u := by
        split_ifs with h
        · rw [max_eq_left h.le]; ring
        · rw [max_eq_right (not_lt.1 h)]; ring
      rw [h2] at h1
      exact h1)
  have hitem : Measurable fun t => if 0 < ρ t then |ρ' t| else 0 :=
    Measurable.ite (measurableSet_lt measurable_const hρc.measurable) hρ'c.measurable.abs measurable_const
  have iR : Integrable (fun g => (|⟪u, g⟫| * max (ρ ⟪u, g⟫) 0 +
      (1 + C) * (if 0 < ρ ⟪u, g⟫ then |ρ' ⟪u, g⟫| else 0)) * |G g|) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Body.integrable_ramp u hu
      (fun t => |t| * max (ρ t) 0 + (1 + C) * (if 0 < ρ t then |ρ' t| else 0))
      ((continuous_abs.mul hmaxc).measurable.add (measurable_const.mul hitem))
      ((2 + C) * A2) (B2 + 1) (by linarith) (fun t => by
        have he := Real.add_one_le_exp |t|
        have h0 : 0 ≤ (if 0 < ρ t then |ρ' t| else 0) := by split_ifs <;> simp
        have hE : Real.exp (B2 * |t|) ≤ Real.exp ((B2 + 1) * |t|) :=
          Real.exp_le_exp.2 (by nlinarith [abs_nonneg t])
        have hEE : Real.exp ((B2 + 1) * |t|) = Real.exp |t| * Real.exp (B2 * |t|) := by
          rw [← Real.exp_add]; ring_nf
        have h1 : |t| * max (ρ t) 0 ≤ Real.exp |t| * (A2 * Real.exp (B2 * |t|)) :=
          mul_le_mul (by linarith) (hρb t) (le_max_right _ _) (Real.exp_pos _).le
        have h2 : (1 + C) * (if 0 < ρ t then |ρ' t| else 0) ≤ (1 + C) * (A2 * Real.exp ((B2 + 1) * |t|)) :=
          mul_le_mul_of_nonneg_left ((hite t).trans (mul_le_mul_of_nonneg_left hE hA2)) (by linarith)
        rw [abs_of_nonneg (by positivity)]
        rw [hEE] at h2 ⊢
        nlinarith [Real.exp_pos |t|, Real.exp_pos (B2 * |t|)])
      (fun g => |G g|) hGc.abs.aestronglyMeasurable A B (fun g => by rw [abs_abs]; exact hb g)
  have hR := tendsto_integral_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun (n : ℕ) g => ⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g) - ψ' n ⟪u, g⟫ * G g)
    (f := fun g => G g * (max (ρ ⟪u, g⟫) 0 * ⟪u, g⟫ - if 0 < ρ ⟪u, g⟫ then ρ' ⟪u, g⟫ else 0))
    (fun g => (|⟪u, g⟫| * max (ρ ⟪u, g⟫) 0 + (1 + C) * (if 0 < ρ ⟪u, g⟫ then |ρ' ⟪u, g⟫| else 0)) * |G g|)
    (fun n => ((hinner.mul (((hψc n).comp hinner).mul hGc)).sub
      (((hψ'c n).comp hinner).mul hGc)).aestronglyMeasurable)
    iR
    (fun n => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      calc _ ≤ |⟪u, g⟫ * (ψ n ⟪u, g⟫ * G g)| + |ψ' n ⟪u, g⟫ * G g| := abs_sub_le' _ _
        _ = |⟪u, g⟫| * |ψ n ⟪u, g⟫| * |G g| + |ψ' n ⟪u, g⟫| * |G g| := by
            rw [abs_mul, abs_mul, abs_mul (ψ' n _)]; ring
        _ ≤ |⟪u, g⟫| * max (ρ ⟪u, g⟫) 0 * |G g| +
            (1 + C) * (if 0 < ρ ⟪u, g⟫ then |ρ' ⟪u, g⟫| else 0) * |G g| :=
            add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hψle n _) (abs_nonneg _))
              (abs_nonneg _)) (mul_le_mul_of_nonneg_right (hψ'le n _) (abs_nonneg _))
        _ = _ := by ring)
    (Eventually.of_forall fun g => by
      have hA := (tendsto_const_nhds (x := ρ ⟪u, g⟫)).mul (st_tendsto (ρ ⟪u, g⟫))
      have hB := (tendsto_const_nhds (x := ρ' ⟪u, g⟫)).mul
        ((st_tendsto (ρ ⟪u, g⟫)).add (st_deriv_tendsto C hstb hst0 (ρ ⟪u, g⟫)).1)
      have h1 := ((tendsto_const_nhds (x := ⟪u, g⟫)).mul (hA.mul (tendsto_const_nhds (x := G g)))).sub
        (hB.mul (tendsto_const_nhds (x := G g)))
      have h2 : ⟪u, g⟫ * (ρ ⟪u, g⟫ * (if 0 < ρ ⟪u, g⟫ then (1 : ℝ) else 0) * G g) -
          ρ' ⟪u, g⟫ * ((if 0 < ρ ⟪u, g⟫ then (1 : ℝ) else 0) + 0) * G g =
          G g * (max (ρ ⟪u, g⟫) 0 * ⟪u, g⟫ - if 0 < ρ ⟪u, g⟫ then ρ' ⟪u, g⟫ else 0) := by
        by_cases h : 0 < ρ ⟪u, g⟫
        · rw [ite_eq_left h, ite_eq_left h, max_eq_left h.le]; ring
        · rw [ite_eq_right h, ite_eq_right h, max_eq_right (not_lt.1 h)]; ring
      rw [h2] at h1
      exact h1)
  exact tendsto_nhds_unique (hL.congr key) hR

end AdversarialBco.Body2
