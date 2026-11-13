/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2

@[expose] public section

/-!
# The play `p'` of DF2: proofs

Proofs of `PlayShift`, `LemmaUBPrime` and `PlayHess` of `AdversarialBco/Poly/Df2.lean` (the subsection on the surrogate
and its estimators
of the paper), as `playShift_holds`, `lemmaUBPrime_holds`, `playHess_holds`.

* `playShift_holds`: the shift of the play.
* `lemmaUBPrime_holds`: `e` is never differentiated. The Gaussian `stdGaussian` has the density `gdens d`
  (`stdGaussian_eq_withDensity`, by characteristic functions), so `H(u) = E f(u + g) = ∫ f(y) gdens(y - u) dy`
  (`integral_stdGaussian_shift`), and `H` is of class `C²` with the derivatives of the density under the integral
  (`gaussConv_c2`, from `contDiff_two_integral` with the domination `gauss_kernel_dom`). From `Pm ∘ A ∘ A† = id`, `A`
  has an inverse `S` with `⟪Pm (A g), v⟫ = ⟪g, S v⟫` and `⟪Pm v, w⟫ = ⟪S w, S v⟫` (`pm_inverse`); with
  `T = (1 - λ) A` and `f = e ∘ T`, the second term of the surrogate is `H(b + L z)`, `L = λ T⁻¹`, and `affine_c2` gives
  the stated gradient and Hessian.
* `playHess_holds`: `e` is `C²` with `‖D²e‖ ≤ B`, so `De` grows linearly and `e` quadratically
  (`norm_fderiv_le_of_hess`, `abs_le_of_hess`); `z ↦ e(X_z(g))` is differentiated twice under the Gaussian integral
  (`contDiff_two_integral`); `A` need not be invertible.

Instance search on `E →L[ℝ] E →L[ℝ] ℝ`: `ContinuousSub` is given explicitly in
`continuous_hessForm`, and `gaussConv_c2`, `playHess_holds` raise `synthInstance.maxHeartbeats` to 400000 for
`PseudoMetrizableSpace`.
-/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly.Df2Play

/-- The standard Gaussian density on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def gdens (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-(‖x‖ ^ 2) / 2)

/-- The inner product as a real bilinear map, `innerBL d w v = ⟪w, v⟫`. -/
noncomputable def innerBL (d : ℕ) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  innerSL ℝ

/-! ## Leaves -/

open Complex in
theorem stdGaussian_eq_withDensity (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) =
      volume.withDensity (fun x => ENNReal.ofReal (gdens d x)) := by
  have hb : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hint : Integrable (gdens d) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb 0
      (0 : EuclideanSpace ℝ (Fin d))).norm.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ ^ d)
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [gdens, zero_mul, add_zero, Complex.norm_exp]
    congr 2
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; norm_num; ring
  have hnn : ∀ x, 0 ≤ gdens d x := fun x => by unfold gdens; positivity
  have hmeas : Measurable fun x => ENNReal.ofReal (gdens d x) := by
    apply ENNReal.measurable_ofReal.comp; unfold gdens; fun_prop
  have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (gdens d x)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_apply, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d), (ENNReal.ofReal (gdens d x)).toReal • cexp (↑⟪x, t⟫ * I) =
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ d : ℂ) * cexp (-(1 / 2 : ℂ) * ‖x‖ ^ 2 + I * ⟪t, x⟫) := by
    intro x
    rw [ENNReal.toReal_ofReal (hnn x), Complex.real_smul, gdens, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc,
      ← Complex.exp_add, real_inner_comm x t]
    congr 2
    all_goals (push_cast; ring)
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb]
  have key : ((Real.sqrt (2 * Real.pi))⁻¹ ^ d : ℂ) * ((Real.pi : ℂ) / (1 / 2)) ^ ((Fintype.card (Fin d) : ℂ) / 2) = 1 := by
    have h2 : ((Real.pi : ℂ) / (1 / 2)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    have h3 : ((Fintype.card (Fin d) : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) := by rw [Fintype.card_fin]; push_cast; ring
    rw [h2, h3, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    have h4 : (2 * Real.pi) ^ ((d : ℝ) / 2) = (Real.sqrt (2 * Real.pi)) ^ d := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      ring_nf
    rw [h4, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'), Complex.ofReal_one]
  have hq : I ^ 2 * (‖t‖ : ℂ) ^ 2 / (4 * (1 / 2)) = -(‖t‖ : ℂ) ^ 2 / 2 := by rw [Complex.I_sq]; ring
  rw [hq, ← mul_assoc, key, one_mul]

theorem integral_stdGaussian_eq (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ∫ x, F x * gdens d x := by
  rw [stdGaussian_eq_withDensity d]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · -- (ENNReal.ofReal (gdens d x)).toReal = gdens d x, using positivity
    have h_nonneg : ∀ x, 0 ≤ gdens d x := by
      intro x
      unfold gdens
      have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)
      have h_base_pos : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := inv_pos.mpr h_sqrt_pos
      have h_pow_pos : 0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ d := pow_pos h_base_pos d
      have h_exp_pos : 0 < Real.exp (-(‖x‖ ^ 2) / 2) := Real.exp_pos _
      positivity
    simp [smul_eq_mul, mul_comm, ENNReal.toReal_ofReal (h_nonneg _)]
  · -- Measurable (fun x => ENNReal.ofReal (gdens d x))
    have h_cont : Continuous (gdens d) := by
      unfold gdens
      continuity
    exact (ENNReal.measurable_ofReal.comp h_cont.measurable)
  · -- ∀ᵐ x, ENNReal.ofReal (gdens d x) < ⊤
    filter_upwards with x using ENNReal.ofReal_lt_top

theorem integral_stdGaussian_shift (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    ∫ g, F (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ∫ y, F y * gdens d (y - u) := by
  calc
    ∫ g, F (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ x, F (u + x) * gdens d x := by
      rw [integral_stdGaussian_eq d (fun g => F (u + g))]
    _ = ∫ x, (fun y => F y * gdens d (y - u)) (u + x) := by
      refine integral_congr_ae ?_
      filter_upwards [] with x
      simp
    _ = ∫ y, F y * gdens d (y - u) := by
      simpa using MeasureTheory.integral_add_left_eq_self (fun y => F y * gdens d (y - u)) u

theorem integrable_one_add_norm_pow_mul_exp (d k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by
  set N := k + (d + 1) with hN
  set M : ℝ := 2 ^ N * (2 + (N.factorial : ℝ) / c ^ N) with hM
  have hbound : ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ M := by
    intro r hr
    have h1 : (1 + r) ^ N ≤ 2 ^ N * (1 + r ^ N) := by
      rcases le_total r 1 with h | h
      · calc (1 + r) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
          _ ≤ 2 ^ N * (1 + r ^ N) := le_mul_of_one_le_right (by positivity) (by
              have := pow_nonneg hr N; linarith)
      · calc (1 + r) ^ N ≤ (2 * r) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
          _ = 2 ^ N * r ^ N := mul_pow _ _ _
          _ ≤ 2 ^ N * (1 + r ^ N) := by gcongr; linarith
    have h2 : r ^ N ≤ 1 + (r ^ 2) ^ N := by
      rcases le_total r 1 with h | h
      · have := pow_le_one₀ hr h (n := N); have := pow_nonneg (sq_nonneg r) N; linarith
      · have : r ^ N ≤ (r ^ 2) ^ N := by
          rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
        linarith
    have hcN : 0 < c ^ N := pow_pos hc N
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    have h3 : (c * r ^ 2) ^ N / N.factorial ≤ Real.exp (c * r ^ 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) N
    have h4 : (r ^ 2) ^ N ≤ N.factorial / c ^ N * Real.exp (c * r ^ 2) := by
      rw [mul_pow, div_le_iff₀ hfac] at h3
      rw [div_mul_eq_mul_div, le_div_iff₀ hcN]
      nlinarith
    have hE : 1 ≤ Real.exp (c * r ^ 2) := Real.one_le_exp (by positivity)
    have hEpos : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
    have h5 : (1 + r) ^ N ≤ M * Real.exp (c * r ^ 2) := by
      have hq : 0 ≤ (N.factorial : ℝ) / c ^ N := by positivity
      calc (1 + r) ^ N ≤ 2 ^ N * (2 + N.factorial / c ^ N * Real.exp (c * r ^ 2)) := by
            have : (0 : ℝ) ≤ 2 ^ N := by positivity
            have h7 : 1 + r ^ N ≤ 2 + N.factorial / c ^ N * Real.exp (c * r ^ 2) := by linarith
            nlinarith [mul_le_mul_of_nonneg_left h7 this]
        _ ≤ 2 ^ N * (2 * Real.exp (c * r ^ 2) + N.factorial / c ^ N * Real.exp (c * r ^ 2)) := by
            gcongr; linarith
        _ = M * Real.exp (c * r ^ 2) := by rw [hM]; ring
    have h6 : Real.exp (-c * r ^ 2) * Real.exp (c * r ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ M * Real.exp (c * r ^ 2) * Real.exp (-c * r ^ 2) :=
          mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = M := by rw [mul_assoc, mul_comm (Real.exp (c * r ^ 2)), h6, mul_one]
  have hint := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume) (r := (d + 1 : ℕ))
    (by simp)
  refine (hint.const_mul M).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hr := norm_nonneg x
  have hpos : 0 < 1 + ‖x‖ := by linarith
  have hsplit : (1 + ‖x‖) ^ k = (1 + ‖x‖) ^ N * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, hN, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne'),
      mul_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsplit]
  calc (1 + ‖x‖) ^ N * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) * Real.exp (-c * ‖x‖ ^ 2)
      = (1 + ‖x‖) ^ N * Real.exp (-c * ‖x‖ ^ 2) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by ring
    _ ≤ M * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (hbound _ hr) (Real.rpow_nonneg hpos.le _)

theorem exp_neg_sq_sub_le {d : ℕ} (x u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ ≤ 1) :
    Real.exp (-(‖x - u‖ ^ 2) / 2) ≤ Real.exp (1 / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
  have h_ineq : ‖x - u‖ ^ 2 ≥ ‖x‖ ^ 2 / 2 - ‖u‖ ^ 2 := by
    set a := ‖x‖ with ha
    set b := ‖u‖ with hb
    have ha_nonneg : 0 ≤ a := norm_nonneg _
    have hb_nonneg : 0 ≤ b := norm_nonneg _
    by_cases h : b ≤ a
    · have h_sub : ‖x - u‖ ≥ a - b := by
        have := norm_sub_norm_le x u
        linarith
      have h_sq : (a - b) ^ 2 ≥ a ^ 2 / 2 - b ^ 2 := by
        have h_eq : (a - b) ^ 2 - (a ^ 2 / 2 - b ^ 2) = (a - 2 * b) ^ 2 / 2 := by
          ring
        have h_nonneg_sq : 0 ≤ (a - 2 * b) ^ 2 / 2 := by
          have : 0 ≤ (a - 2 * b) ^ 2 := pow_two_nonneg _
          positivity
        linarith
      have h_sq' : ‖x - u‖ ^ 2 ≥ (a - b) ^ 2 := by
        nlinarith
      nlinarith
    · have h_nonneg_sq : 0 ≤ ‖x - u‖ ^ 2 := pow_two_nonneg _
      have h_rhs_nonpos : a ^ 2 / 2 - b ^ 2 ≤ 0 := by
        nlinarith
      nlinarith
  have h_exp : -(‖x - u‖ ^ 2) / 2 ≤ (1 / 2 : ℝ) + (-(1 / 4) * ‖x‖ ^ 2) := by
    have h1 : -(‖x - u‖ ^ 2) / 2 ≤ -((‖x‖ ^ 2 / 2) - (‖u‖ ^ 2)) / 2 := by
      linarith
    have h2 : -((‖x‖ ^ 2 / 2) - (‖u‖ ^ 2)) / 2 = -(‖x‖ ^ 2) / 4 + (‖u‖ ^ 2) / 2 := by
      ring
    have h3 : -(‖x‖ ^ 2) / 4 + (‖u‖ ^ 2) / 2 ≤ -(‖x‖ ^ 2) / 4 + 1 / 2 := by
      have : (‖u‖ ^ 2) / 2 ≤ 1 / 2 := by
        have h_sq : ‖u‖ ^ 2 ≤ 1 := by
          have h_nonneg_u : 0 ≤ ‖u‖ := norm_nonneg _
          nlinarith
        linarith
      linarith
    have h4 : -(‖x‖ ^ 2) / 4 + 1 / 2 = (1 / 2 : ℝ) + (-(1 / 4) * ‖x‖ ^ 2) := by
      ring
    linarith
  calc
    Real.exp (-(‖x - u‖ ^ 2) / 2) ≤ Real.exp ((1 / 2 : ℝ) + (-(1 / 4) * ‖x‖ ^ 2)) :=
      Real.exp_le_exp.mpr h_exp
    _ = Real.exp (1 / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by rw [Real.exp_add]

theorem hasFDerivAt_gdens_sub {d : ℕ} (y u : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun u => gdens d (y - u)) (gdens d (y - u) • innerSL ℝ (y - u)) u := by
  have h_sub : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin d) => y - u) (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) u := by
    simpa using (hasFDerivAt_id u).const_sub y
  have h_norm_sq : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin d) => ‖y - u‖ ^ 2) (-((2 : ℝ) • innerSL ℝ (y - u))) u := by
    have := h_sub.norm_sq
    apply this.congr_fderiv
    ext w
    simp
    ring
  have h_neg_norm_div_two : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin d) => -(‖y - u‖ ^ 2) / 2) (innerSL ℝ (y - u)) u := by
    have := (h_norm_sq.neg).const_smul ((2 : ℝ)⁻¹)
    convert this using 1
    · ext x; simp [div_eq_mul_inv, smul_eq_mul, Pi.smul_apply, mul_comm]
    · simp [smul_smul]
  have h_exp : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin d) => Real.exp (-(‖y - u‖ ^ 2) / 2))
      (Real.exp (-(‖y - u‖ ^ 2) / 2) • innerSL ℝ (y - u)) u := by
    simpa using h_neg_norm_div_two.exp
  -- Now multiply by the constant c = (Real.sqrt (2 * Real.pi))⁻¹ ^ d
  simpa [gdens, smul_smul, mul_comm] using h_exp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ ^ d)

theorem hasFDerivAt_gdens_sub_smul {d : ℕ} (y u : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun u => gdens d (y - u) • innerSL ℝ (y - u))
      (gdens d (y - u) • ((innerSL ℝ (y - u)).smulRight (innerSL ℝ (y - u)) - innerBL d)) u := by
  have hf : HasFDerivAt (fun u => innerBL d (y - u)) ((innerBL d).comp (-ContinuousLinearMap.id ℝ _)) u :=
    (innerBL d).hasFDerivAt.comp u ((hasFDerivAt_id u).const_sub y)
  have h := (hasFDerivAt_gdens_sub y u).smul hf
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ContinuousLinearMap.ext fun v => ?_)
  have e1 : ∀ p q : EuclideanSpace ℝ (Fin d), (innerSL ℝ p) q = ⟪p, q⟫ := fun _ _ => rfl
  simp [innerBL, e1]
  ring

theorem contDiff_two_integral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → α → ℝ) (K₁ : E → α → (E →L[ℝ] ℝ)) (K₂ : E → α → (E →L[ℝ] E →L[ℝ] ℝ))
    (hK : ∀ z, Integrable (K z) μ) (hK₁ : ∀ z, AEStronglyMeasurable (K₁ z) μ)
    (hK₂ : ∀ z, AEStronglyMeasurable (K₂ z) μ)
    (hd₁ : ∀ a z, HasFDerivAt (fun z => K z a) (K₁ z a) z)
    (hd₂ : ∀ a z, HasFDerivAt (fun z => K₁ z a) (K₂ z a) z)
    (hc₂ : ∀ a, Continuous (fun z => K₂ z a))
    (hdom : ∀ z₀, ∃ ε > 0, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ a, ∀ z ∈ Metric.ball z₀ ε, ‖K₁ z a‖ ≤ b a ∧ ‖K₂ z a‖ ≤ b a) :
    ContDiff ℝ 2 (fun z => ∫ a, K z a ∂μ) ∧
      ∀ z v w, fderiv ℝ (fun z => ∫ a, K z a ∂μ) z v = ∫ a, K₁ z a v ∂μ ∧
        fderiv ℝ (fderiv ℝ (fun z => ∫ a, K z a ∂μ)) z w v = ∫ a, K₂ z a w v ∂μ := by
  have hI1 : ∀ z, Integrable (K₁ z) μ := fun z => by
    obtain ⟨ε, hε, b, hb, hbd⟩ := hdom z
    exact hb.mono' (hK₁ z) (Filter.Eventually.of_forall fun a => (hbd a z (Metric.mem_ball_self hε)).1)
  have hF1 : ∀ z₀, HasFDerivAt (fun z => ∫ a, K z a ∂μ) (∫ a, K₁ z₀ a ∂μ) z₀ := fun z₀ => by
    obtain ⟨ε, hε, b, hb, hbd⟩ := hdom z₀
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds z₀ hε)
      (Filter.Eventually.of_forall fun z => (hK z).aestronglyMeasurable) (hK z₀) (hK₁ z₀)
      (Filter.Eventually.of_forall fun a z hz => (hbd a z hz).1) hb
      (Filter.Eventually.of_forall fun a z _ => hd₁ a z)
  have hF2 : ∀ z₀, HasFDerivAt (fun z => ∫ a, K₁ z a ∂μ) (∫ a, K₂ z₀ a ∂μ) z₀ := fun z₀ => by
    obtain ⟨ε, hε, b, hb, hbd⟩ := hdom z₀
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds z₀ hε)
      (Filter.Eventually.of_forall fun z => hK₁ z) (hI1 z₀) (hK₂ z₀)
      (Filter.Eventually.of_forall fun a z hz => (hbd a z hz).2) hb
      (Filter.Eventually.of_forall fun a z _ => hd₂ a z)
  have hC2 : Continuous (fun z => ∫ a, K₂ z a ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro z₀
    obtain ⟨ε, hε, b, hb, hbd⟩ := hdom z₀
    exact continuousAt_of_dominated (Filter.Eventually.of_forall fun z => hK₂ z)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hε) fun z hz =>
        Filter.Eventually.of_forall fun a => (hbd a z hz).2) hb
      (Filter.Eventually.of_forall fun a => (hc₂ a).continuousAt)
  have hfd1 : fderiv ℝ (fun z => ∫ a, K z a ∂μ) = fun z => ∫ a, K₁ z a ∂μ := funext fun z => (hF1 z).fderiv
  have hfd2 : fderiv ℝ (fun z => ∫ a, K₁ z a ∂μ) = fun z => ∫ a, K₂ z a ∂μ := funext fun z => (hF2 z).fderiv
  refine ⟨?_, fun z v w => ⟨?_, ?_⟩⟩
  · have h1 : ContDiff ℝ 1 (fun z => ∫ a, K₁ z a ∂μ) := by
      rw [show (1 : WithTop ℕ∞) = ((0 : ℕ) + 1 : ℕ) by norm_num]
      exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, contDiff_zero.mpr hC2, hF2⟩
    rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) + 1 : ℕ) by norm_num]
    exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, by simpa using h1, hF1⟩
  · rw [hfd1, ContinuousLinearMap.integral_apply (hI1 z)]
  · rw [hfd1, hfd2]
    obtain ⟨ε, hε, b, hb, hbd⟩ := hdom z
    have h1 := Integrable.mono' (β := E →L[ℝ] (E →L[ℝ] ℝ)) (f := K₂ z) hb (hK₂ z)
      (Filter.Eventually.of_forall fun a => (hbd a z (Metric.mem_ball_self hε)).2)
    rw [ContinuousLinearMap.integral_apply h1, ContinuousLinearMap.integral_apply (h1.apply_continuousLinearMap w)]

theorem norm_smul_innerSL_sub_le {d : ℕ} (a : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖a • ((innerSL ℝ x).smulRight (innerSL ℝ x) - innerBL d)‖ ≤ |a| * (‖x‖ ^ 2 + 1) := by
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have happ : ((innerSL ℝ x).smulRight (innerSL ℝ x) - innerBL d) w v = ⟪x, w⟫ * ⟪x, v⟫ - ⟪w, v⟫ := by
    simp [innerBL]
    rfl
  rw [happ, Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm x w
  have h2 := abs_real_inner_le_norm x v
  have h3 := abs_real_inner_le_norm w v
  calc |⟪x, w⟫ * ⟪x, v⟫ - ⟪w, v⟫| ≤ |⟪x, w⟫| * |⟪x, v⟫| + |⟪w, v⟫| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ (‖x‖ * ‖w‖) * (‖x‖ * ‖v‖) + ‖w‖ * ‖v‖ := by gcongr
    _ = (‖x‖ ^ 2 + 1) * ‖w‖ * ‖v‖ := by ring

theorem gauss_kernel_dom {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B * (1 + ‖y‖)) (u₀ u y : EuclideanSpace ℝ (Fin d)) (hu : ‖u - u₀‖ ≤ 1) :
    |f y| * gdens d (y - u) * (‖y - u‖ ^ 2 + 1) ≤
      2 * B * (1 + ‖u₀‖) * (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (1 / 2) *
        ((1 + ‖y - u₀‖) ^ 3 * Real.exp (-(1 / 4) * ‖y - u₀‖ ^ 2)) := by
  set r := ‖y - u₀‖ with hr
  set c := (Real.sqrt (2 * Real.pi))⁻¹ ^ d with hc
  have hr_nonneg : 0 ≤ r := by rw [hr]; exact norm_nonneg _
  have hB_nonneg : 0 ≤ B := by
    have h0 := hB 0
    have h0' : |f 0| ≤ B := by
      simpa [norm_zero] using h0
    have h_abs : 0 ≤ |f 0| := abs_nonneg _
    linarith
  have h_f_bound : |f y| ≤ B * (1 + ‖u₀‖) * (1 + r) := by
    have hy := hB y
    have hy_eq : y = u₀ + (y - u₀) := by abel
    have h_tri : ‖y‖ ≤ ‖u₀‖ + r := by
      rw [hy_eq]
      calc
        ‖u₀ + (y - u₀)‖ ≤ ‖u₀‖ + ‖y - u₀‖ := norm_add_le _ _
        _ = ‖u₀‖ + r := rfl
    have h_ineq : 1 + ‖y‖ ≤ (1 + ‖u₀‖) * (1 + r) := by
      have h_nonneg_prod : 0 ≤ ‖u₀‖ * r := mul_nonneg (norm_nonneg _) hr_nonneg
      nlinarith
    calc
      |f y| ≤ B * (1 + ‖y‖) := hy
      _ ≤ B * ((1 + ‖u₀‖) * (1 + r)) := mul_le_mul_of_nonneg_left h_ineq hB_nonneg
      _ = B * (1 + ‖u₀‖) * (1 + r) := by ring
  have hc_nonneg : 0 ≤ c := by
    have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)
    have h_inv_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    exact pow_nonneg h_inv_nonneg d
  have h_gdens_bound : gdens d (y - u) ≤ c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2) := by
    have h_exp := exp_neg_sq_sub_le (y - u₀) (u - u₀) hu
    have h_sub : (y - u₀) - (u - u₀) = y - u := by abel
    calc
      gdens d (y - u) = c * Real.exp (-(‖y - u‖ ^ 2) / 2) := rfl
      _ = c * Real.exp (-(‖(y - u₀) - (u - u₀)‖ ^ 2) / 2) := by simp [h_sub]
      _ ≤ c * (Real.exp (1 / 2) * Real.exp (-(1 / 4) * ‖y - u₀‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h_exp hc_nonneg
      _ = c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2) := by ring
  have h_norm_bound : ‖y - u‖ ^ 2 + 1 ≤ 2 * (1 + r) ^ 2 := by
    have h_sub : y - u = (y - u₀) - (u - u₀) := by abel
    have h_norm_sub : ‖y - u‖ ≤ r + ‖u - u₀‖ := by
      calc
        ‖y - u‖ = ‖(y - u₀) - (u - u₀)‖ := by rw [h_sub]
        _ ≤ ‖y - u₀‖ + ‖u - u₀‖ := norm_sub_le _ _
        _ = r + ‖u - u₀‖ := rfl
    have h_norm_sub' : ‖y - u‖ ≤ r + 1 := by linarith
    have h_sq : ‖y - u‖ ^ 2 ≤ (r + 1) ^ 2 := by
      have h_norm_nonneg : 0 ≤ ‖y - u‖ := norm_nonneg _
      nlinarith
    have h_sq_bound : (r + 1) ^ 2 + 1 ≤ 2 * (1 + r) ^ 2 := by
      have h : (1 : ℝ) ≤ (1 + r) ^ 2 := by
        have h1r : 1 ≤ 1 + r := by linarith
        nlinarith
      nlinarith
    linarith
  have h_abs_nonneg : 0 ≤ |f y| := abs_nonneg _
  have h_gdens_nonneg : 0 ≤ gdens d (y - u) := by
    have h_exp_pos : 0 < Real.exp (-(‖y - u‖ ^ 2) / 2) := Real.exp_pos _
    have h_nonneg : 0 ≤ c * Real.exp (-(‖y - u‖ ^ 2) / 2) :=
      mul_nonneg hc_nonneg (by positivity)
    have h_gdens_eq : gdens d (y - u) = c * Real.exp (-(‖y - u‖ ^ 2) / 2) := by
      simp [gdens, hc]
    rw [h_gdens_eq]
    exact h_nonneg
  have h_f_bound_nonneg : 0 ≤ B * (1 + ‖u₀‖) * (1 + r) := by
    have h1 : 0 ≤ 1 + ‖u₀‖ := by linarith [norm_nonneg u₀]
    have h2 : 0 ≤ 1 + r := by linarith
    exact mul_nonneg (mul_nonneg hB_nonneg h1) h2
  have h_gdens_bound_nonneg : 0 ≤ c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2) := by
    have h1 : 0 ≤ Real.exp (1 / 2) := by positivity
    have h2 : 0 ≤ Real.exp (-(1 / 4) * r ^ 2) := by positivity
    exact mul_nonneg (mul_nonneg hc_nonneg h1) h2
  have h_norm_bound_nonneg : 0 ≤ 2 * (1 + r) ^ 2 := by
    have h : 0 ≤ (1 + r) ^ 2 := pow_two_nonneg _
    positivity
  calc
    |f y| * gdens d (y - u) * (‖y - u‖ ^ 2 + 1)
        ≤ (B * (1 + ‖u₀‖) * (1 + r)) * (c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2))
            * (2 * (1 + r) ^ 2) := by
      have h1 : |f y| * gdens d (y - u) ≤
          (B * (1 + ‖u₀‖) * (1 + r)) * (c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2)) :=
        mul_le_mul h_f_bound h_gdens_bound h_gdens_nonneg h_f_bound_nonneg
      have h2 : (|f y| * gdens d (y - u)) * (‖y - u‖ ^ 2 + 1) ≤
          ((B * (1 + ‖u₀‖) * (1 + r)) * (c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2)))
            * (2 * (1 + r) ^ 2) :=
        mul_le_mul h1 h_norm_bound (by
          have h : 0 ≤ ‖y - u‖ ^ 2 + 1 := by nlinarith [norm_nonneg (y - u)]
          exact h)
          (by
            have h : 0 ≤ (B * (1 + ‖u₀‖) * (1 + r)) * (c * Real.exp (1 / 2) * Real.exp (-(1 / 4) * r ^ 2)) :=
              mul_nonneg h_f_bound_nonneg h_gdens_bound_nonneg
            exact h)
      simpa [mul_assoc] using h2
    _ = 2 * B * (1 + ‖u₀‖) * c * Real.exp (1 / 2) * ((1 + r) ^ 3 * Real.exp (-(1 / 4) * r ^ 2)) := by
      ring

theorem affine_c2 {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ) (hH : ContDiff ℝ 2 H)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d)) (c a : ℝ) :
    ContDiff ℝ 2 (fun z => c + a * H (b + L z)) ∧
      ∀ z v w, fderiv ℝ (fun z => c + a * H (b + L z)) z v = a * fderiv ℝ H (b + L z) (L v) ∧
        fderiv ℝ (fderiv ℝ (fun z => c + a * H (b + L z))) z w v =
          a * fderiv ℝ (fderiv ℝ H) (b + L z) (L w) (L v) := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hH1 : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (m := 1) (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ H) := hH1.differentiable (by norm_num)
  have hG : ∀ z, HasFDerivAt (fun z => b + L z) L z := fun z => (L.hasFDerivAt).const_add b
  have h1 : ∀ z, HasFDerivAt (fun z => c + a * H (b + L z)) (a • (fderiv ℝ H (b + L z)).comp L) z := by
    intro z
    exact (((hd (b + L z)).hasFDerivAt.comp z (hG z)).const_mul a).const_add c
  have hf1 : fderiv ℝ (fun z => c + a * H (b + L z)) = fun z => a • (fderiv ℝ H (b + L z)).comp L :=
    funext fun z => (h1 z).fderiv
  set Φ : (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
    a • (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip L with hΦdef
  have hΦ : ∀ φ, Φ φ = a • φ.comp L := fun φ => by simp [hΦdef]
  have h2 : ∀ z, HasFDerivAt (fun z => a • (fderiv ℝ H (b + L z)).comp L)
      (Φ.comp ((fderiv ℝ (fderiv ℝ H) (b + L z)).comp L)) z := by
    intro z
    have := Φ.hasFDerivAt.comp z ((hdd (b + L z)).hasFDerivAt.comp z (hG z))
    convert this using 1
    funext z
    simp [hΦ]
  refine ⟨contDiff_const.add (contDiff_const.mul (hH.comp (contDiff_const.add L.contDiff))),
    fun z v w => ⟨?_, ?_⟩⟩
  · rw [hf1]; simp
  · rw [hf1, (h2 z).fderiv]; simp [hΦ]

theorem pm_inverse {d : ℕ} (A Pm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : Pm.comp (A.comp (ContinuousLinearMap.adjoint A)) = ContinuousLinearMap.id ℝ _) :
    ∃ S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      A.comp S = ContinuousLinearMap.id ℝ _ ∧ S.comp A = ContinuousLinearMap.id ℝ _ ∧
        (∀ g v, ⟪Pm (A g), v⟫ = ⟪g, S v⟫) ∧ (∀ v w, ⟪Pm v, w⟫ = ⟪S w, S v⟫) := by
  -- Let M = A ∘ A†
  set M := A.comp (ContinuousLinearMap.adjoint A) with hM_def
  have hPmM : Pm.comp M = ContinuousLinearMap.id ℝ _ := h
  -- Pointwise: Pm (M x) = x for all x
  have hPmM_apply : ∀ x, Pm (M x) = x := by
    intro x
    have hx := congrArg (fun f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => f x) hPmM
    simpa [ContinuousLinearMap.id_apply] using hx
  -- M is injective
  have hM_inj : Function.Injective M := by
    intro x y hxy
    calc
      x = Pm (M x) := (hPmM_apply x).symm
      _ = Pm (M y) := by rw [hxy]
      _ = y := hPmM_apply y
  -- M is self-adjoint: ⟪M x, y⟫ = ⟪x, M y⟫
  have hM_self_adjoint : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫ := by
    intro x y
    calc
      ⟪M x, y⟫ = ⟪A ((ContinuousLinearMap.adjoint A) x), y⟫ := rfl
      _ = ⟪(ContinuousLinearMap.adjoint A) x, (ContinuousLinearMap.adjoint A) y⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪x, A ((ContinuousLinearMap.adjoint A) y)⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪x, M y⟫ := rfl
  -- EuclideanSpace ℝ (Fin d) is finite-dimensional
  have h_fin : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)) := by infer_instance
  -- M is surjective (injective ↔ surjective in finite dimension)
  have hM_surj : Function.Surjective M := by
    let M_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := M.toLinearMap
    have hM_lin_inj : Function.Injective M_lin := hM_inj
    have hM_lin_surj : Function.Surjective M_lin :=
      (LinearMap.injective_iff_surjective.mp hM_lin_inj)
    intro x
    rcases hM_lin_surj x with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [M_lin] using hy
  -- M ∘ Pm = id
  have hMPm : M.comp Pm = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro x
    rcases hM_surj x with ⟨y, hy⟩
    calc
      (M.comp Pm) x = M (Pm x) := rfl
      _ = M (Pm (M y)) := by rw [hy]
      _ = M ((Pm.comp M) y) := rfl
      _ = M y := by
        have hcomp : (Pm.comp M) y = y := by
          simpa [ContinuousLinearMap.id_apply] using congrArg (fun f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => f y) hPmM
        rw [hcomp]
      _ = x := hy
  -- Pointwise: M (Pm x) = x
  have hMPm_apply : ∀ x, M (Pm x) = x := by
    intro x
    simpa [ContinuousLinearMap.id_apply] using congrArg (fun f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => f x) hMPm
  -- Pm is self-adjoint: ⟪Pm x, y⟫ = ⟪x, Pm y⟫
  have hPm_self_adjoint : ∀ x y, ⟪Pm x, y⟫ = ⟪x, Pm y⟫ := by
    intro x y
    calc
      ⟪Pm x, y⟫ = ⟪Pm x, M (Pm y)⟫ := by rw [hMPm_apply y]
      _ = ⟪M (Pm x), Pm y⟫ := by rw [hM_self_adjoint (Pm x) (Pm y)]
      _ = ⟪x, Pm y⟫ := by rw [hMPm_apply x]
  -- Define S = A† ∘ Pm
  set S := (ContinuousLinearMap.adjoint A).comp Pm with hS_def
  -- A ∘ S = id
  have hAS : A.comp S = ContinuousLinearMap.id ℝ _ := by
    calc
      A.comp S = A.comp ((ContinuousLinearMap.adjoint A).comp Pm) := rfl
      _ = (A.comp (ContinuousLinearMap.adjoint A)).comp Pm := by
        rw [ContinuousLinearMap.comp_assoc]
      _ = M.comp Pm := rfl
      _ = ContinuousLinearMap.id ℝ _ := hMPm
  -- A is injective (A ∘ S = id makes A surjective, hence injective in finite dimensions)
  have hA_inj : Function.Injective A := by
    have hA_surj : Function.Surjective A := by
      intro x
      refine ⟨S x, ?_⟩
      have hx := congrArg (fun f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => f x) hAS
      simpa [ContinuousLinearMap.id_apply] using hx
    have hA_lin_surj : Function.Surjective (A.toLinearMap) := hA_surj
    have hA_lin_inj : Function.Injective (A.toLinearMap) :=
      (LinearMap.injective_iff_surjective.mpr hA_lin_surj)
    exact hA_lin_inj
  -- S ∘ A = id
  have hSA : S.comp A = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro x
    apply hA_inj
    calc
      A ((S.comp A) x) = A (S (A x)) := rfl
      _ = (A.comp S) (A x) := rfl
      _ = (ContinuousLinearMap.id ℝ _) (A x) := by rw [hAS]
      _ = A x := by simp
  -- Inner product identity 1: ⟪Pm (A g), v⟫ = ⟪g, S v⟫
  have h_inner1 : ∀ g v, ⟪Pm (A g), v⟫ = ⟪g, S v⟫ := by
    intro g v
    calc
      ⟪Pm (A g), v⟫ = ⟪A g, Pm v⟫ := by rw [hPm_self_adjoint (A g) v]
      _ = ⟪g, (ContinuousLinearMap.adjoint A) (Pm v)⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪g, S v⟫ := rfl
  -- Inner product identity 2: ⟪Pm v, w⟫ = ⟪S w, S v⟫
  have h_inner2 : ∀ v w, ⟪Pm v, w⟫ = ⟪S w, S v⟫ := by
    intro v w
    have hcalc : ⟪S w, S v⟫ = ⟪Pm v, w⟫ := by
      calc
        ⟪S w, S v⟫ = ⟪(ContinuousLinearMap.adjoint A) (Pm w), (ContinuousLinearMap.adjoint A) (Pm v)⟫ := rfl
        _ = ⟪Pm w, A ((ContinuousLinearMap.adjoint A) (Pm v))⟫ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        _ = ⟪Pm w, (A.comp (ContinuousLinearMap.adjoint A)) (Pm v)⟫ := rfl
        _ = ⟪Pm w, M (Pm v)⟫ := rfl
        _ = ⟪Pm w, v⟫ := by rw [hMPm_apply v]
        _ = ⟪w, Pm v⟫ := by rw [hPm_self_adjoint w v]
        _ = ⟪Pm v, w⟫ := by rw [real_inner_comm]
    exact hcalc.symm
  -- Assemble the result
  refine ⟨S, hAS, hSA, h_inner1, h_inner2⟩

theorem norm_fderiv_le_of_hess {d : ℕ} (e : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ) (he : ContDiff ℝ 2 e)
    (hB : ∀ y, ‖fderiv ℝ (fderiv ℝ e) y‖ ≤ B) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ e x‖ ≤ ‖fderiv ℝ e 0‖ + B * ‖x‖ := by
  have h_contdiff_fderiv : ContDiff ℝ 1 (fderiv ℝ e) :=
    he.fderiv_right (by decide)
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ e) :=
    h_contdiff_fderiv.differentiable_one
  have h_mvt := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => h_diff_fderiv.differentiableAt)
    (fun y _ => hB y)
    convex_univ
    (Set.mem_univ 0)
    (Set.mem_univ x)
  have h_bound : ‖fderiv ℝ e x‖ - ‖fderiv ℝ e 0‖ ≤ B * ‖x‖ := by
    have h := norm_sub_norm_le (fderiv ℝ e x) (fderiv ℝ e 0)
    have h_mvt' : ‖fderiv ℝ e x - fderiv ℝ e 0‖ ≤ B * ‖x‖ := by
      simpa [sub_zero] using h_mvt
    exact le_trans h h_mvt'
  linarith

theorem abs_le_of_hess {d : ℕ} (e : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ) (he : ContDiff ℝ 2 e)
    (hB : ∀ y, ‖fderiv ℝ (fderiv ℝ e) y‖ ≤ B) (x : EuclideanSpace ℝ (Fin d)) :
    |e x| ≤ |e 0| + ‖fderiv ℝ e 0‖ * ‖x‖ + B * ‖x‖ ^ 2 := by
  have hB0 : 0 ≤ B := by
    have h0 := hB 0
    have h0' : 0 ≤ ‖fderiv ℝ (fderiv ℝ e) 0‖ := norm_nonneg (fderiv ℝ (fderiv ℝ e) 0)
    linarith
  have h_diff : Differentiable ℝ e := he.differentiable (by norm_num)
  have h_conv : Convex ℝ (segment ℝ 0 x) := convex_segment (𝕜 := ℝ) 0 x
  have h_mem0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ segment ℝ 0 x := left_mem_segment (𝕜 := ℝ) 0 x
  have h_memx : x ∈ segment ℝ 0 x := right_mem_segment (𝕜 := ℝ) 0 x
  have h_bound : ∀ y ∈ segment ℝ 0 x, ‖fderiv ℝ e y‖ ≤ ‖fderiv ℝ e 0‖ + B * ‖x‖ := by
    intro y hy
    have hy_norm : ‖y‖ ≤ ‖x‖ := by
      rcases (segment_eq_image_lineMap ℝ 0 x).subset hy with ⟨t, ht, rfl⟩
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      rw [AffineMap.lineMap_apply_module]
      simp
      rw [norm_smul, Real.norm_of_nonneg ht0]
      nlinarith [norm_nonneg x]
    have h := AdversarialBco.Poly.Df2Play.norm_fderiv_le_of_hess e B he hB y
    have h' : B * ‖y‖ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_left hy_norm hB0
    linarith
  have h_mvt : ‖e x - e 0‖ ≤ (‖fderiv ℝ e 0‖ + B * ‖x‖) * ‖x - 0‖ :=
    h_conv.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => h_diff.differentiableAt)
      h_bound
      h_mem0
      h_memx
  have h_norm_sub : ‖x - 0‖ = ‖x‖ := by simp
  rw [h_norm_sub] at h_mvt
  have h_abs_sub : |e x| - |e 0| ≤ |e x - e 0| := abs_sub_abs_le_abs_sub (e x) (e 0)
  have h_norm_abs : |e x - e 0| = ‖e x - e 0‖ := by rw [Real.norm_eq_abs]
  rw [h_norm_abs] at h_abs_sub
  have h_abs_le : |e x| ≤ |e 0| + (‖fderiv ℝ e 0‖ + B * ‖x‖) * ‖x‖ := by
    linarith
  calc
    |e x| ≤ |e 0| + (‖fderiv ℝ e 0‖ + B * ‖x‖) * ‖x‖ := h_abs_le
    _ = |e 0| + ‖fderiv ℝ e 0‖ * ‖x‖ + B * ‖x‖ * ‖x‖ := by ring
    _ = |e 0| + ‖fderiv ℝ e 0‖ * ‖x‖ + B * (‖x‖ * ‖x‖) := by ring
    _ = |e 0| + ‖fderiv ℝ e 0‖ * ‖x‖ + B * ‖x‖ ^ 2 := by ring

theorem integrable_norm_pow_stdGaussian (d k : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ k) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h_mem : MemLp id (k : ENNReal) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) (k : ENNReal) (by simp)
  exact h_mem.integrable_norm_pow'

/-! ## Small facts -/

theorem gdens_nonneg (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gdens d x := by
  unfold gdens; positivity

theorem continuous_gdens (d : ℕ) : Continuous (gdens d) := by
  unfold gdens; fun_prop

theorem innerBL_apply {d : ℕ} (w v : EuclideanSpace ℝ (Fin d)) : innerBL d w v = ⟪w, v⟫ := rfl

theorem continuous_hessForm (d : ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => (innerSL ℝ x).smulRight (innerSL ℝ x) - innerBL d) := by
  have : ContinuousSub (EuclideanSpace ℝ (Fin d) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) :=
    @IsTopologicalAddGroup.to_continuousSub (EuclideanSpace ℝ (Fin d) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommGroup.toAddGroup inferInstance
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => innerSL ℝ x) := (innerSL ℝ).continuous
  exact ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).continuous₂.comp (hc.prodMk hc)).sub continuous_const

theorem hessForm_apply {d : ℕ} (x w v : EuclideanSpace ℝ (Fin d)) :
    ((innerSL ℝ x).smulRight (innerSL ℝ x) - innerBL d) w v = ⟪x, w⟫ * ⟪x, v⟫ - ⟪w, v⟫ := by
  simp [innerBL_apply]

/-! ## The Gaussian convolution of a function of linear growth -/

set_option synthInstance.maxHeartbeats 400000 in
/-- `u ↦ E f(u + g)` is of class `C²` for `f` measurable of linear growth, with the derivatives of the Gaussian
density: gradient `E f(u + g) ⟨g, v⟩`, Hessian `E f(u + g) (⟨g, w⟩⟨g, v⟩ - ⟨w, v⟩)`. -/
theorem gaussConv_c2 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B * (1 + ‖y‖)) :
    ContDiff ℝ 2 (fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ∧
      ∀ u v w : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) u v =
            ∫ g, f (u + g) * ⟪g, v⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
          fderiv ℝ (fderiv ℝ (fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) u w v =
            ∫ g, f (u + g) * (⟪g, w⟫ * ⟪g, v⟫ - ⟪w, v⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hH : (fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = fun u => ∫ y, f y * gdens d (y - u) := by
    funext u; exact integral_stdGaussian_shift d f u
  rw [hH]
  -- the dominating function centred at `u₀`
  have hdomf : ∀ u₀ : EuclideanSpace ℝ (Fin d), Integrable (fun y : EuclideanSpace ℝ (Fin d) => 2 * B * (1 + ‖u₀‖) * (Real.sqrt (2 * Real.pi))⁻¹ ^ d *
      Real.exp (1 / 2) * ((1 + ‖y - u₀‖) ^ 3 * Real.exp (-(1 / 4) * ‖y - u₀‖ ^ 2))) := by
    intro u₀
    exact ((integrable_one_add_norm_pow_mul_exp d 3 (c := 1 / 4) (by norm_num)).comp_sub_right u₀).const_mul _
  have hcd : ∀ u : EuclideanSpace ℝ (Fin d), Continuous (fun y : EuclideanSpace ℝ (Fin d) => gdens d (y - u)) := fun u =>
    (continuous_gdens d).comp (continuous_id.sub continuous_const)
  have hci : ∀ u : EuclideanSpace ℝ (Fin d), Continuous (fun y : EuclideanSpace ℝ (Fin d) => innerSL ℝ (y - u)) := fun u =>
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  have hch : ∀ u : EuclideanSpace ℝ (Fin d), Continuous (fun y : EuclideanSpace ℝ (Fin d) => (innerSL ℝ (y - u)).smulRight (innerSL ℝ (y - u)) - innerBL d) :=
    fun u => (continuous_hessForm d).comp (continuous_id.sub continuous_const)
  have hmeas0 : ∀ u : EuclideanSpace ℝ (Fin d), AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin d) => f y * gdens d (y - u)) volume := fun u =>
    hf.aestronglyMeasurable.mul (hcd u).aestronglyMeasurable
  have key := contDiff_two_integral (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun u y => f y * gdens d (y - u))
    (fun u y => (f y * gdens d (y - u)) • innerSL ℝ (y - u))
    (fun u y => (f y * gdens d (y - u)) • ((innerSL ℝ (y - u)).smulRight (innerSL ℝ (y - u)) - innerBL d))
    (fun u => by
      refine (hdomf u).mono' (hmeas0 u) (Filter.Eventually.of_forall fun y => ?_)
      have h := gauss_kernel_dom f B hB u u y (by simp)
      have h0 := gdens_nonneg d (y - u)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      calc |f y| * gdens d (y - u) ≤ |f y| * gdens d (y - u) * (‖y - u‖ ^ 2 + 1) := by
            apply le_mul_of_one_le_right (by positivity); nlinarith [sq_nonneg ‖y - u‖]
        _ ≤ _ := h)
    (fun u => (hmeas0 u).smul (hci u).aestronglyMeasurable)
    (fun u => (hmeas0 u).smul (hch u).aestronglyMeasurable)
    (fun y u => by
      have h := (hasFDerivAt_gdens_sub y u).const_mul (f y)
      convert h using 1
      rw [smul_smul])
    (fun y u => by
      have h := (hasFDerivAt_gdens_sub_smul y u).const_smul (f y)
      convert h using 1
      · funext u; simp only [Pi.smul_apply, smul_smul]
      · rw [smul_smul])
    (fun y => by
      have hc1 : Continuous (fun u : EuclideanSpace ℝ (Fin d) => gdens d (y - u)) :=
        (continuous_gdens d).comp (continuous_const.sub continuous_id)
      have hc2 : Continuous (fun u : EuclideanSpace ℝ (Fin d) => (innerSL ℝ (y - u)).smulRight (innerSL ℝ (y - u)) - innerBL d) :=
        (continuous_hessForm d).comp (continuous_const.sub continuous_id)
      exact (continuous_const.mul hc1).smul hc2)
    (fun u₀ => by
      refine ⟨1, one_pos, _, hdomf u₀, fun y u hu => ?_⟩
      have hu' : ‖u - u₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hu).le
      have h := gauss_kernel_dom f B hB u₀ u y hu'
      have h0 := gdens_nonneg d (y - u)
      have hfg : 0 ≤ |f y| * gdens d (y - u) := by positivity
      constructor
      · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, innerSL_apply_norm]
        calc |f y| * gdens d (y - u) * ‖y - u‖ ≤ |f y| * gdens d (y - u) * (‖y - u‖ ^ 2 + 1) := by
              apply mul_le_mul_of_nonneg_left _ hfg; nlinarith [sq_nonneg (‖y - u‖ - 1)]
          _ ≤ _ := h
      · calc _ ≤ |f y * gdens d (y - u)| * (‖y - u‖ ^ 2 + 1) := norm_smul_innerSL_sub_le _ _
          _ = |f y| * gdens d (y - u) * (‖y - u‖ ^ 2 + 1) := by rw [abs_mul, abs_of_nonneg h0]
          _ ≤ _ := h)
  refine ⟨key.1, fun u v w => ⟨?_, ?_⟩⟩
  · rw [(key.2 u v w).1]
    have := integral_stdGaussian_shift d (fun y => f y * ⟪y - u, v⟫) u
    simp only [add_sub_cancel_left] at this
    rw [this]
    congr 1; funext y
    simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  · rw [(key.2 u v w).2]
    have := integral_stdGaussian_shift d (fun y => f y * (⟪y - u, w⟫ * ⟪y - u, v⟫ - ⟪w, v⟫)) u
    simp only [add_sub_cancel_left] at this
    rw [this]
    congr 1; funext y
    simp only [FunLike.coe_smul, Pi.smul_apply, hessForm_apply, smul_eq_mul]
    ring

theorem integrable_quad_stdGaussian (d : ℕ) (a b c : ℝ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => a + b * ‖g‖ + c * ‖g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h1 := (integrable_norm_pow_stdGaussian d 1).const_mul b
  simp only [pow_one] at h1
  exact ((integrable_const a).add h1).add ((integrable_norm_pow_stdGaussian d 2).const_mul c)

end AdversarialBco.Poly.Df2Play

namespace AdversarialBco.Poly

open Df2Play

/-- `PlayShift`. -/
theorem playShift_holds : PlayShift := by
  intro d e μ A lam hl0 hl1
  have hint : (fun g => e ((1 - lam) • (μ + A g) + lam • μ)) = fun g => e (μ + (1 - lam) • A g) := by
    funext g
    congr 1
    rw [smul_add, add_comm ((1 - lam) • μ), add_assoc, ← add_smul]
    simp [add_comm]
  unfold df2Surr
  rw [hint]
  have hl : lam ≠ 0 := hl0.ne'
  field_simp
  ring

theorem lemmaUBPrime_holds : LemmaUBPrime := by
  intro d e μ A Pm lam B hl0 hl1 he hB hPm
  obtain ⟨S, hAS, -, hPmA, hPmS⟩ := pm_inverse A Pm hPm
  have h1l : 0 < 1 - lam := by linarith
  have h1l' : (1 - lam) ≠ 0 := h1l.ne'
  have hl' : lam ≠ 0 := hl0.ne'
  set T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := (1 - lam) • A with hT
  set ST : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := (1 - lam)⁻¹ • S with hST
  have hAS' : ∀ x, A (S x) = x := fun x => by
    simpa using congrArg (fun F : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) => F x) hAS
  have hTS : ∀ x, T (ST x) = x := by
    intro x
    simp only [hT, hST, smul_apply, map_smul, hAS', smul_smul, inv_mul_cancel₀ h1l',
      one_smul]
  clear_value T ST
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun y => e (T y) with hf
  have hfm : Measurable f := he.comp T.continuous.measurable
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hfB : ∀ y, |f y| ≤ (B * (1 + ‖T‖)) * (1 + ‖y‖) := by
    intro y
    calc |f y| ≤ B * (1 + ‖T y‖) := hB _
      _ ≤ B * ((1 + ‖T‖) * (1 + ‖y‖)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          have := T.le_opNorm y
          nlinarith [norm_nonneg y, norm_nonneg T]
      _ = _ := by ring
  obtain ⟨hHc, hHd⟩ := gaussConv_c2 f hfm _ hfB
  set H : EuclideanSpace ℝ (Fin d) → ℝ := fun u => ∫ g, f (u + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    with hH
  set b : EuclideanSpace ℝ (Fin d) := ST ((1 - lam) • μ) with hb
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := lam • ST with hL
  have hTL : ∀ z, T (L z) = lam • z := fun z => by rw [hL, smul_apply, map_smul, hTS]
  have hX : ∀ z g, f (b + L z + g) = e ((1 - lam) • (μ + A g) + lam • z) := by
    intro z g
    show e (T (b + L z + g)) = _
    rw [map_add, map_add, hb, hTS, hTL]
    congr 1
    rw [hT, smul_apply, smul_add]
    abel
  set c0 := (1 - 1 / lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) with hc0
  have hs : df2Surr e μ A lam = fun z => c0 + 1 / lam * H (b + L z) := by
    funext z
    simp only [df2Surr, hc0, hH, hX]
  obtain ⟨hc2, hder⟩ := affine_c2 H hHc L b c0 (1 / lam)
  rw [hs]
  have hLv : ∀ v, L v = (lam * (1 - lam)⁻¹) • S v := fun v => by
    simp only [hL, hST, smul_apply, smul_smul]
  refine ⟨hc2, fun z v w => ⟨?_, ?_⟩⟩
  · rw [(hder z v w).1, (hHd _ _ w).1, ← integral_const_mul]
    congr 1; funext g
    rw [hX, hLv, real_inner_smul_right, map_smul, real_inner_smul_left, hPmA]
    field_simp
  · rw [(hder z v w).2, (hHd _ _ _).2, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext g
    rw [hX]
    simp only [hLv, real_inner_smul_right, real_inner_smul_left, map_smul, hPmA, hPmS v w]
    field_simp

set_option synthInstance.maxHeartbeats 400000 in
theorem playHess_holds : PlayHess := by
  intro d e μ A lam B hl0 hl1 he hB
  have hB0 : 0 ≤ B := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hB 0)
  have h1l : 0 < 1 - lam := by linarith
  have hd1 : Differentiable ℝ e := he.differentiable (by norm_num)
  have hfe : ContDiff ℝ 1 (fderiv ℝ e) := he.fderiv_right (m := 1) (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ e) := hfe.differentiable (by norm_num)
  have hc1e : Continuous (fderiv ℝ e) := hfe.continuous
  have hc2e : Continuous (fderiv ℝ (fderiv ℝ e)) := hfe.continuous_fderiv (by norm_num)
  set X : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun z g => (1 - lam) • (μ + A g) + lam • z with hXdef
  have hXc : ∀ z, Continuous (X z) := fun z => by simp only [hXdef]; fun_prop
  have hXcz : ∀ g, Continuous (fun z => X z g) := fun g => by simp only [hXdef]; fun_prop
  have hXd : ∀ g z, HasFDerivAt (fun z => X z g) (lam • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) z :=
    fun g z => ((hasFDerivAt_id z).const_smul lam).const_add _
  have hXn : ∀ z g, ‖X z g‖ ≤ (1 - lam) * ‖μ‖ + lam * ‖z‖ + (1 - lam) * ‖A‖ * ‖g‖ := by
    intro z g
    simp only [hXdef]
    calc ‖(1 - lam) • (μ + A g) + lam • z‖ ≤ (1 - lam) * (‖μ‖ + ‖A‖ * ‖g‖) + lam * ‖z‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos h1l]
            exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (A.le_opNorm g))) h1l.le
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
      _ = _ := by ring
  set D0 := ‖fderiv ℝ e 0‖
  have hD0 : 0 ≤ D0 := norm_nonneg _
  set q := (1 - lam) * ‖A‖ with hq
  have hq0 : 0 ≤ q := mul_nonneg h1l.le (norm_nonneg _)
  have key := contDiff_two_integral (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (fun z g => e (X z g)) (fun z g => lam • fderiv ℝ e (X z g))
    (fun z g => (lam * lam) • fderiv ℝ (fderiv ℝ e) (X z g))
    (fun z => by
      set p := (1 - lam) * ‖μ‖ + lam * ‖z‖
      have hp : 0 ≤ p := by positivity
      refine (integrable_quad_stdGaussian d (|e 0| + D0 * p + B * p ^ 2) (D0 * q + 2 * B * p * q) (B * q ^ 2)).mono'
        (he.continuous.comp (hXc z)).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
      have h1 := abs_le_of_hess e B he hB (X z g)
      have h2 := hXn z g
      have hx0 := norm_nonneg (X z g)
      have hg0 := norm_nonneg g
      have h3 : ‖X z g‖ ^ 2 ≤ (p + q * ‖g‖) ^ 2 := pow_le_pow_left₀ hx0 (by linarith) 2
      rw [Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_left h2 hD0, mul_le_mul_of_nonneg_left h3 hB0])
    (fun z => ((hc1e.comp (hXc z)).const_smul lam).aestronglyMeasurable)
    (fun z => ((hc2e.comp (hXc z)).const_smul (lam * lam)).aestronglyMeasurable)
    (fun g z => by
      have h := (hd1 (X z g)).hasFDerivAt.comp z (hXd g z)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp)
    (fun g z => by
      have h := ((hd2 (X z g)).hasFDerivAt.comp z (hXd g z)).const_smul lam
      refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ContinuousLinearMap.ext fun v => ?_)
      simp [smul_smul])
    (fun g => ((hc2e.comp (hXcz g)).const_smul (lam * lam)))
    (fun z₀ => by
      set p := (1 - lam) * ‖μ‖ + lam * (‖z₀‖ + 1)
      have hp : 0 ≤ p := by positivity
      refine ⟨1, one_pos, fun g => (lam * (D0 + B * p) + lam * lam * B) + (lam * B * q) * ‖g‖ + 0 * ‖g‖ ^ 2,
        integrable_quad_stdGaussian d _ _ _, fun g z hz => ?_⟩
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := Metric.mem_ball.mp hz
        rw [dist_eq_norm] at this
        linarith [norm_le_insert' z z₀]
      have h2 : ‖X z g‖ ≤ p + q * ‖g‖ := by
        have := hXn z g
        have : lam * ‖z‖ ≤ lam * (‖z₀‖ + 1) := mul_le_mul_of_nonneg_left hz' hl0.le
        simp only [p, hq] at *
        nlinarith
      have h1 := norm_fderiv_le_of_hess e B he hB (X z g)
      have hg0 := norm_nonneg g
      have hBq : 0 ≤ lam * B * q * ‖g‖ := by positivity
      constructor
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
        have : ‖fderiv ℝ e (X z g)‖ ≤ D0 + B * (p + q * ‖g‖) :=
          h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 hB0))
        nlinarith [mul_le_mul_of_nonneg_left this hl0.le, mul_nonneg (mul_nonneg hl0.le hl0.le) hB0]
      · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl0.le hl0.le)]
        have := mul_le_mul_of_nonneg_left (hB (X z g)) (mul_nonneg hl0.le hl0.le)
        nlinarith [mul_nonneg hl0.le (add_nonneg hD0 (mul_nonneg hB0 hp))])
  set J : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ∫ g, e (X z g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    with hJ
  set c0 := (1 - 1 / lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) with hc0
  have hs : df2Surr e μ A lam =
      fun z => c0 + 1 / lam * J (0 + ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) z) := by
    funext z
    simp only [df2Surr, hc0, hJ, hXdef, zero_add, ContinuousLinearMap.id_apply]
  obtain ⟨hc2, hder⟩ := affine_c2 J key.1 (ContinuousLinearMap.id ℝ _) 0 c0 (1 / lam)
  rw [hs]
  refine ⟨hc2, fun z v w => ?_⟩
  rw [(hder z v w).2]
  simp only [zero_add, ContinuousLinearMap.id_apply]
  rw [(key.2 z v w).2, ← integral_const_mul, ← integral_const_mul]
  congr 1; funext g
  simp only [hXdef, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

end AdversarialBco.Poly
