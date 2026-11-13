/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProc
public import AdversarialBco.StatementPoly
public import AdversarialBco.Poly.Df2Run

@[expose] public section

/-!
# Tools for Proposition G of DF2-O

Generic facts on Gaussian laws, gauges and the noise, read by `Df2PropGProof.lean` and by files of `Bit/`.

* One-dimensional Gaussian bounds, elementary, with no Pinsker inequality and no relative entropy: a scale
  `(1 + u)` costs `u` (the density of the wider law is at least `1/(1 + u)` times the other), a shift of the mean by
  `c` costs `|c|/(2 b)` (`gauss_affine_le`). PO's Lemma TV reaches `u/2^{1/2} + |m̂ - m|/(2a)` through Pinsker; the
  bound here has `u` in place of `u/2^{1/2}`, which the margin of the row `n η_g (R + 7)/ε ≤ δ₁` absorbs at
  `ε ≤ 1/2`.
* Lemma G (iii): a convex loss with values in `[0, 1]` is `(1/ε)`-Lipschitz on `(1 - ε) K'`
  (`convex_lip_eps`); the gauge facts that place the points played in the interior of the body.
* `E|ε_t| ≤ 1` under the noise hypothesis (`noise_abs_lintegral`).
* The positioned body cut by `B_R`: the gauge factor of a play (`gauge_pt_le`), `df2Kp` as a body in a position
  (`kp_eq_posBody`), convex and closed (`kp_convex_of`, `kp_closed_of`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Poly.PropG

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly

/-! ## One-dimensional Gaussian bounds -/

theorem gauss_affine_eq (a s : ℝ) (hs : s ≠ 0) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal 0 1 {z | a + s * z ∈ S} = gaussianReal a (s ^ 2).toNNReal S := by
  have hmeas_add : Measurable (fun (x : ℝ) => a + x) := by fun_prop
  have hmeas_mul : Measurable (fun (x : ℝ) => s * x) := by fun_prop
  have hmeas_affine : Measurable (fun (z : ℝ) => a + s * z) := by fun_prop
  have hmul := gaussianReal_map_const_mul (μ := 0) (v := 1) s
  have hadd := gaussianReal_map_const_add (μ := 0) (v := NNReal.mk (s ^ 2) (sq_nonneg s)) a
  calc
    gaussianReal 0 1 {z | a + s * z ∈ S}
        = ((gaussianReal 0 1).map (fun (z : ℝ) => a + s * z)) S := by
      change gaussianReal 0 1 ((fun (z : ℝ) => a + s * z) ⁻¹' S) = _
      rw [← Measure.map_apply hmeas_affine hS]
    _ = (((gaussianReal 0 1).map (fun (x : ℝ) => s * x)).map (fun (x : ℝ) => a + x)) S := by
      change ((gaussianReal 0 1).map ((fun (x : ℝ) => a + x) ∘ (fun (x : ℝ) => s * x))) S = _
      rw [← Measure.map_map hmeas_add hmeas_mul]
    _ = ((gaussianReal (s * (0 : ℝ)) (NNReal.mk (s ^ 2) (sq_nonneg s) * (1 : NNReal))).map
        (fun (x : ℝ) => a + x)) S := by rw [hmul]
    _ = ((gaussianReal 0 (NNReal.mk (s ^ 2) (sq_nonneg s))).map (fun (x : ℝ) => a + x)) S := by simp
    _ = gaussianReal (0 + a) (NNReal.mk (s ^ 2) (sq_nonneg s)) S := by rw [hadd]
    _ = gaussianReal a (NNReal.mk (s ^ 2) (sq_nonneg s)) S := by simp
    _ = gaussianReal a ((s ^ 2).toNNReal) S := by
      rw [← Real.toNNReal_of_nonneg (sq_nonneg s)]

theorem gauss_scale_le (a b c : ℝ) (hb : 0 < b) (hc : 1 ≤ c) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal a ((c * b) ^ 2).toNNReal S ≤ gaussianReal a (b ^ 2).toNNReal S + ENNReal.ofReal (1 - 1 / c) := by
  have hc0 : 0 < c := by linarith
  have hv0 : (b ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hv1 : ((c * b) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hpt : ∀ x : ℝ, ENNReal.ofReal (1 / c) * gaussianPDF a (b ^ 2).toNNReal x ≤
      gaussianPDF a ((c * b) ^ 2).toNNReal x := by
    intro x
    simp only [gaussianPDF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg _)]
    have hs : Real.sqrt (2 * Real.pi * (c * b) ^ 2) = c * Real.sqrt (2 * Real.pi * b ^ 2) := by
      rw [show 2 * Real.pi * (c * b) ^ 2 = c ^ 2 * (2 * Real.pi * b ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0.le]
    rw [hs, mul_inv, ← mul_assoc, one_div]
    have hsq : 0 < Real.sqrt (2 * Real.pi * b ^ 2) := Real.sqrt_pos.2 (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
    have : 1 ≤ c ^ 2 := by nlinarith
    nlinarith [sq_nonneg b]
  have key : ∀ T : Set ℝ, MeasurableSet T →
      ENNReal.ofReal (1 / c) * gaussianReal a (b ^ 2).toNNReal T ≤ gaussianReal a ((c * b) ^ 2).toNNReal T := by
    intro T hT
    rw [gaussianReal_apply a hv0, gaussianReal_apply a hv1, ← lintegral_const_mul _ (measurable_gaussianPDF _ _)]
    exact lintegral_mono fun x => hpt x
  have h := key Sᶜ hS.compl
  rw [prob_compl_eq_one_sub hS, prob_compl_eq_one_sub hS] at h
  rw [← ofReal_measureReal (μ := gaussianReal a (b ^ 2).toNNReal),
    ← ofReal_measureReal (μ := gaussianReal a ((c * b) ^ 2).toNNReal)] at h ⊢
  set r0 := (gaussianReal a (b ^ 2).toNNReal).real S
  set r1 := (gaussianReal a ((c * b) ^ 2).toNNReal).real S
  have hr0 : 0 ≤ r0 := measureReal_nonneg
  have hr1 : 0 ≤ r1 := measureReal_nonneg
  have hr0' : r0 ≤ 1 := measureReal_le_one
  have hr1' : r1 ≤ 1 := measureReal_le_one
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_sub _ hr1,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by linarith)] at h
  have hc1 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  rw [← ENNReal.ofReal_add hr0 (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 1 / c * r0 ≤ r0 := by nlinarith
  nlinarith

theorem gauss_pdf_le_half (a b : ℝ) (hb : 0 < b) (x : ℝ) :
    gaussianPDF a (b ^ 2).toNNReal x ≤ ENNReal.ofReal (1 / (2 * b)) := by
  simp only [gaussianPDF]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg _)]
  have h2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    calc (2 : ℝ) = Real.sqrt 4 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hs : Real.sqrt (2 * Real.pi * b ^ 2) = Real.sqrt (2 * Real.pi) * b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
  rw [hs]
  have he : Real.exp (-(x - a) ^ 2 / (2 * b ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.2 (by positivity)
  calc (Real.sqrt (2 * Real.pi) * b)⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * b ^ 2))
      ≤ (Real.sqrt (2 * Real.pi) * b)⁻¹ * 1 := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 / (2 * b) := by
      rw [mul_one, one_div]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right h2 hb.le)

theorem gauss_shift_le_of_le (a1 a0 b : ℝ) (hb : 0 < b) (ha : a0 ≤ a1) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal a1 (b ^ 2).toNNReal S ≤
      gaussianReal a0 (b ^ 2).toNNReal S + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
  set v := (b ^ 2).toNNReal with hvdef
  have hv : v ≠ 0 := by rw [hvdef, Ne, Real.toNNReal_eq_zero, not_le]; positivity
  set m := (a0 + a1) / 2
  set A : Set ℝ := Set.Ioi m
  have hA : MeasurableSet A := measurableSet_Ioi
  have hpdf : ∀ x, (x - a1) ^ 2 - (x - a0) ^ 2 = (a1 - a0) * (2 * (m - x)) := fun x => by ring
  have hle : ∀ a a' x : ℝ, (x - a) ^ 2 ≤ (x - a') ^ 2 → gaussianPDF a' v x ≤ gaussianPDF a v x := by
    intro a a' x h
    simp only [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right h (by positivity)
  -- on `A` the density of `N(a1)` dominates, off `A` the density of `N(a0)` does
  have hon : ∀ T ⊆ A, MeasurableSet T → gaussianReal a0 v T ≤ gaussianReal a1 v T := by
    intro T hTA hT
    rw [gaussianReal_apply a0 hv, gaussianReal_apply a1 hv]
    refine setLIntegral_mono (measurable_gaussianPDF _ _) fun x hx => hle a1 a0 x ?_
    have hx' : m < x := hTA hx
    nlinarith [hpdf x]
  have hoff : ∀ T, T ∩ A = ∅ → MeasurableSet T → gaussianReal a1 v T ≤ gaussianReal a0 v T := by
    intro T hTA hT
    rw [gaussianReal_apply a0 hv, gaussianReal_apply a1 hv]
    refine setLIntegral_mono (measurable_gaussianPDF _ _) fun x hx => hle a0 a1 x ?_
    have hx' : x ≤ m := by
      by_contra h
      have : x ∈ T ∩ A := ⟨hx, lt_of_not_ge h⟩
      rw [hTA] at this
      exact this
    nlinarith [hpdf x]
  -- the half-line: `N(a1)(A) ≤ N(a0)(A) + (a1 - a0)/(2b)`
  have hhalf : gaussianReal a1 v A ≤ gaussianReal a0 v A + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
    have hmap : gaussianReal a1 v A = gaussianReal a0 v (Set.Ioi (m - (a1 - a0))) := by
      have h := gaussianReal_map_add_const (μ := a0) (v := v) (a1 - a0)
      rw [show a0 + (a1 - a0) = a1 by ring] at h
      rw [← h, Measure.map_apply (measurable_add_const _) hA]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, A]
      constructor <;> intro h <;> linarith
    rw [hmap]
    have hsplit : Set.Ioi (m - (a1 - a0)) = Set.Ioc (m - (a1 - a0)) m ∪ A := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc, A]
      constructor
      · intro h
        by_cases hx : x ≤ m
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr (lt_of_not_ge hx)
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
    rw [hsplit, add_comm]
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    rw [gaussianReal_apply a0 hv]
    calc ∫⁻ x in Set.Ioc (m - (a1 - a0)) m, gaussianPDF a0 v x
        ≤ ∫⁻ _ in Set.Ioc (m - (a1 - a0)) m, ENNReal.ofReal (1 / (2 * b)) :=
          setLIntegral_mono measurable_const fun x _ => gauss_pdf_le_half a0 b hb x
      _ = ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show m - (m - (a1 - a0)) = a1 - a0 by ring]
          ring
  have h1 := hon (A \ S) Set.sdiff_subset (hA.diff hS)
  have h2 := hoff (S \ A) (by ext x; simp) (hS.diff hA)
  have eA1 := measure_inter_add_sdiff (μ := gaussianReal a1 v) A hS
  have eA0 := measure_inter_add_sdiff (μ := gaussianReal a0 v) A hS
  have eS1 := measure_inter_add_sdiff (μ := gaussianReal a1 v) S hA
  have eS0 := measure_inter_add_sdiff (μ := gaussianReal a0 v) S hA
  -- `N1(S ∩ A) ≤ N0(S ∩ A) + δ` by cancelling `N1(A \ S)`
  have hSA : gaussianReal a1 v (S ∩ A) ≤ gaussianReal a0 v (S ∩ A) + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
    refine (ENNReal.add_le_add_iff_right (measure_ne_top (gaussianReal a1 v) (A \ S))).1 ?_
    rw [Set.inter_comm S A]
    calc gaussianReal a1 v (A ∩ S) + gaussianReal a1 v (A \ S) = gaussianReal a1 v A := eA1
      _ ≤ gaussianReal a0 v A + ENNReal.ofReal ((a1 - a0) / (2 * b)) := hhalf
      _ = gaussianReal a0 v (A ∩ S) + gaussianReal a0 v (A \ S) + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
          rw [eA0]
      _ ≤ gaussianReal a0 v (A ∩ S) + gaussianReal a1 v (A \ S) + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
          gcongr
      _ = gaussianReal a0 v (A ∩ S) + ENNReal.ofReal ((a1 - a0) / (2 * b)) + gaussianReal a1 v (A \ S) := by
          ring
  calc gaussianReal a1 v S = gaussianReal a1 v (S ∩ A) + gaussianReal a1 v (S \ A) := eS1.symm
    _ ≤ gaussianReal a0 v (S ∩ A) + ENNReal.ofReal ((a1 - a0) / (2 * b)) + gaussianReal a0 v (S \ A) :=
        add_le_add hSA h2
    _ = gaussianReal a0 v S + ENNReal.ofReal ((a1 - a0) / (2 * b)) := by
        rw [← eS0]; ring

theorem gauss_shift_le (a1 a0 b : ℝ) (hb : 0 < b) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal a1 (b ^ 2).toNNReal S ≤
      gaussianReal a0 (b ^ 2).toNNReal S + ENNReal.ofReal (|a1 - a0| / (2 * b)) := by
  rcases le_total a0 a1 with ha | ha
  · rw [abs_of_nonneg (sub_nonneg.2 ha)]
    exact gauss_shift_le_of_le a1 a0 b hb ha S hS
  · have hrefl : ∀ a : ℝ, gaussianReal a (b ^ 2).toNNReal S =
        gaussianReal (-a) (b ^ 2).toNNReal (Neg.neg ⁻¹' S) := by
      intro a
      rw [← gaussianReal_map_neg, Measure.map_apply measurable_neg (measurable_neg hS)]
      congr 1
      ext x
      simp
    rw [hrefl a1, hrefl a0, abs_of_nonpos (sub_nonpos.2 ha), show -(a1 - a0) = -a1 - -a0 by ring]
    exact gauss_shift_le_of_le (-a1) (-a0) b hb (neg_le_neg ha) _ (measurable_neg hS)

theorem gauss_affine_le (a1 a0 b0 u : ℝ) (hb0 : 0 < b0) (hu : 0 ≤ u) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal 0 1 {z | a1 + (1 + u) * b0 * z ∈ S} ≤
      gaussianReal 0 1 {z | a0 + b0 * z ∈ S} + ENNReal.ofReal (u + |a1 - a0| / (2 * b0)) := by
  have hb1 : (1 + u) * b0 ≠ 0 := by positivity
  rw [gauss_affine_eq a1 _ hb1 S hS, gauss_affine_eq a0 b0 hb0.ne' S hS]
  have h1 := gauss_scale_le a1 b0 (1 + u) hb0 (by linarith) S hS
  have h2 := gauss_shift_le a1 a0 b0 hb0 S hS
  have hu' : 1 - 1 / (1 + u) ≤ u := by
    have h : 1 - u ≤ 1 / (1 + u) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  calc gaussianReal a1 (((1 + u) * b0) ^ 2).toNNReal S
      ≤ gaussianReal a1 (b0 ^ 2).toNNReal S + ENNReal.ofReal (1 - 1 / (1 + u)) := h1
    _ ≤ gaussianReal a0 (b0 ^ 2).toNNReal S + ENNReal.ofReal (|a1 - a0| / (2 * b0)) + ENNReal.ofReal u := by
        gcongr
    _ = gaussianReal a0 (b0 ^ 2).toNNReal S + ENNReal.ofReal (u + |a1 - a0| / (2 * b0)) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) hu, add_comm (|a1 - a0| / (2 * b0))]

/-! ## Lemma G and the gauge -/

theorem convex_lip_eps {d : ℕ} (K' : Set (EuclideanSpace ℝ (Fin d))) (hK' : Convex ℝ K')
    (h1 : Metric.closedBall 0 1 ⊆ K') (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ K' F)
    (hF01 : ∀ x ∈ K', F x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (a b : EuclideanSpace ℝ (Fin d)) (ha : (1 - ε)⁻¹ • a ∈ K') (hb : (1 - ε)⁻¹ • b ∈ K') :
    F b - F a ≤ ‖b - a‖ / ε := by
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K' := by
    have hball : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_self]
      norm_num
    exact h1 hball
  have ha_mem : a ∈ K' := by
    have ha_eq : a = (1 - ε) • ((1 - ε)⁻¹ • a) + ε • (0 : EuclideanSpace ℝ (Fin d)) := by
      have h_sub_ne : 1 - ε ≠ 0 := by linarith
      simp [smul_smul, mul_inv_cancel₀ h_sub_ne]
    rw [ha_eq]
    exact hK' ha h0 (by linarith) (by linarith) (by ring)
  have hb_mem : b ∈ K' := by
    have hb_eq : b = (1 - ε) • ((1 - ε)⁻¹ • b) + ε • (0 : EuclideanSpace ℝ (Fin d)) := by
      have h_sub_ne : 1 - ε ≠ 0 := by linarith
      simp [smul_smul, mul_inv_cancel₀ h_sub_ne]
    rw [hb_eq]
    exact hK' hb h0 (by linarith) (by linarith) (by ring)
  by_cases h_eq : b = a
  · rw [h_eq, sub_self]
    simp
  · have h_pos : 0 < ‖b - a‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr h_eq
    set r := ‖b - a‖ with hr_def
    have hr_pos : 0 < r := h_pos
    have hr_ne : r ≠ 0 := by linarith
    set v := r⁻¹ • (b - a) with hv_def
    have hv_norm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr_pos, ← hr_def]
      field_simp [hr_ne]
    have hv_mem : v ∈ K' := by
      have hball : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hv_norm]
      exact h1 hball
    set z := b + ε • v with hz_def
    have hz_mem : z ∈ K' := by
      rw [hz_def]
      have hz_eq : b + ε • v = (1 - ε) • ((1 - ε)⁻¹ • b) + ε • v := by
        have h_sub_ne : 1 - ε ≠ 0 := by linarith
        have h : (1 - ε) • ((1 - ε)⁻¹ • b) = b := by
          rw [smul_smul, mul_inv_cancel₀ h_sub_ne, one_smul]
        rw [h]
      rw [hz_eq]
      exact hK' hb hv_mem (by linarith) (by linarith) (by ring)
    set s := r / (r + ε) with hs_def
    have hs_nonneg : 0 ≤ s := by
      rw [hs_def]
      refine div_nonneg (by linarith) (by linarith)
    have hs_le_one : s ≤ 1 := by
      rw [hs_def]
      refine (div_le_one (by linarith)).mpr (by linarith)
    have h_comb : (1 - s) • a + s • z = b := by
      rw [hz_def, hv_def, hs_def]
      have hcoeff_a : (1 - r / (r + ε)) - (r / (r + ε)) * ε * r⁻¹ = 0 := by
        field_simp [hr_ne]
        ring
      have hcoeff_b : (r / (r + ε)) + (r / (r + ε)) * ε * r⁻¹ = 1 := by
        field_simp [hr_ne]
      have h_expr : (1 - r / (r + ε)) • a + (r / (r + ε)) • (b + ε • (r⁻¹ • (b - a))) =
          ((1 - r / (r + ε)) - (r / (r + ε)) * ε * r⁻¹) • a + ((r / (r + ε)) + (r / (r + ε)) * ε * r⁻¹) • b := by
        calc
          (1 - r / (r + ε)) • a + (r / (r + ε)) • (b + ε • (r⁻¹ • (b - a)))
              = (1 - r / (r + ε)) • a + (r / (r + ε)) • b + (r / (r + ε)) • (ε • (r⁻¹ • (b - a))) := by
            rw [smul_add, add_assoc]
          _ = (1 - r / (r + ε)) • a + (r / (r + ε)) • b + ((r / (r + ε)) * ε * r⁻¹) • (b - a) := by
            simp [smul_smul, mul_assoc]
          _ = (1 - r / (r + ε)) • a + (r / (r + ε)) • b + (((r / (r + ε)) * ε * r⁻¹) • b - ((r / (r + ε)) * ε * r⁻¹) • a) := by
            rw [smul_sub]
          _ = ((1 - r / (r + ε)) - (r / (r + ε)) * ε * r⁻¹) • a + ((r / (r + ε)) + (r / (r + ε)) * ε * r⁻¹) • b := by
            simp [add_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_smul]
      rw [h_expr, hcoeff_a, hcoeff_b]
      simp
    have h_convex : F b ≤ (1 - s) • F a + s • F z := by
      rw [← h_comb]
      refine hF.2 ha_mem hz_mem (by linarith) hs_nonneg (by ring)
    have hz_range : F z ∈ Set.Icc (0 : ℝ) 1 := hF01 z hz_mem
    have ha_range : F a ∈ Set.Icc (0 : ℝ) 1 := hF01 a ha_mem
    have h_diff : F z - F a ≤ 1 := by
      rcases hz_range with ⟨hz_low, hz_high⟩
      rcases ha_range with ⟨ha_low, ha_high⟩
      linarith
    have h_bound : F b - F a ≤ s := by
      have h_convex' : F b ≤ (1 - s) * F a + s * F z := by
        simpa [smul_eq_mul] using h_convex
      have h_mul : s * (F z - F a) ≤ s := by
        nlinarith
      linarith
    have hs_le : s ≤ ‖b - a‖ / ε := by
      rw [hs_def, hr_def]
      have hpos_sum : 0 < r + ε := by linarith
      rw [div_le_div_iff_of_pos_left hr_pos hpos_sum hε]
      linarith
    linarith

theorem gauge_smul_mem {d : ℕ} (K' : Set (EuclideanSpace ℝ (Fin d))) (hc : Convex ℝ K') (hcl : IsClosed K')
    (h1 : Metric.closedBall 0 1 ⊆ K') (ε : ℝ) (hε1 : ε < 1) (y : EuclideanSpace ℝ (Fin d))
    (hy : gauge K' y ≤ 1 - ε) : (1 - ε)⁻¹ • y ∈ K' := by
  have hεpos : 0 < 1 - ε := by linarith
  have hεinv_nonneg : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.mpr hεpos.le
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K' := by
    have hball : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      apply Metric.mem_closedBall_self
      norm_num
    exact h1 hball
  have h_abs : Absorbent ℝ K' := by
    have h_ball_abs : Absorbent ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      absorbent_ball_zero (by norm_num : 0 < (1 : ℝ))
    have h_sub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K' :=
      subset_trans Metric.ball_subset_closedBall h1
    exact h_ball_abs.mono h_sub
  have h_gauge : gauge K' ((1 - ε)⁻¹ • y) ≤ 1 := by
    calc
      gauge K' ((1 - ε)⁻¹ • y) = (1 - ε)⁻¹ • gauge K' y := gauge_smul_of_nonneg hεinv_nonneg y
      _ = (1 - ε)⁻¹ * gauge K' y := by simp
      _ ≤ (1 - ε)⁻¹ * (1 - ε) := mul_le_mul_of_nonneg_left hy hεinv_nonneg
      _ = 1 := by field_simp [hεpos.ne']
  have h_mem_closure : (1 - ε)⁻¹ • y ∈ closure K' :=
    mem_closure_of_gauge_le_one hc h0 h_abs h_gauge
  rw [hcl.closure_eq] at h_mem_closure
  exact h_mem_closure

theorem gauge_lt_one_interior {d : ℕ} (K' : Set (EuclideanSpace ℝ (Fin d))) (hc : Convex ℝ K')
    (h1 : Metric.closedBall 0 1 ⊆ K') (y : EuclideanSpace ℝ (Fin d)) (hy : gauge K' y < 1) : y ∈ interior K' := by
  have hball_mem_nhds : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) (by norm_num : (0 : ℝ) < 1)
  have hball_sub_K' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K' :=
    subset_trans Metric.ball_subset_closedBall h1
  have hK'_nhds : K' ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset hball_mem_nhds hball_sub_K'
  exact ((gauge_lt_one_iff_mem_interior hc hK'_nhds).mp hy)

theorem posBody_interior {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (P : PgSp d) (hdet : (pgMat P).det ≠ 0)
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ interior (posBody K (pgMu P) (pgOp P))) :
    pgMu P + pgOp P y ∈ interior K := by
  -- The map h(y) = pgMu P + pgOp P y is a homeomorphism when pgMat P is invertible
  -- First, get that pgMat P is invertible from hdet
  have hdet_unit : IsUnit ((pgMat P).det) := IsUnit.mk0 _ hdet
  have hA_inv : Invertible (pgMat P) := Matrix.invertibleOfIsUnitDet _ hdet_unit
  -- Matrix.toEuclideanCLM is a star algebra equivalence (hence a ring equivalence), so it preserves units
  have hA_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (pgMat P)) :=
    ((MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))).mpr (isUnit_of_invertible (pgMat P)))
  -- From IsUnit we get a ContinuousLinearEquiv via ContinuousLinearEquiv.ofUnit
  let A_equiv : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofUnit hA_unit.unit
  -- A_equiv is an open map
  have hA_open : IsOpenMap (A_equiv : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    ContinuousLinearEquiv.isOpenMap A_equiv
  -- Translation by pgMu P is also an open map
  have h_trans_open : IsOpenMap (fun (z : EuclideanSpace ℝ (Fin d)) => pgMu P + z) :=
    isOpenMap_add_left (pgMu P)
  -- The composition h(y) = pgMu P + A_equiv y is an open map
  have h_open : IsOpenMap (fun (z : EuclideanSpace ℝ (Fin d)) => pgMu P + (A_equiv z)) :=
    IsOpenMap.comp h_trans_open hA_open
  -- Note that pgOp P = A_equiv as continuous linear maps
  have hA_eq : (A_equiv : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = pgOp P := rfl
  -- We have: posBody K (pgMu P) (pgOp P) = (fun z => pgMu P + pgOp P z) ⁻¹' K
  have h_posBody_eq : posBody K (pgMu P) (pgOp P) = (fun z => pgMu P + pgOp P z) ⁻¹' K := by
    ext z
    simp [posBody]
  -- hy : y ∈ interior (posBody K (pgMu P) (pgOp P))
  -- So y ∈ interior ((fun z => pgMu P + pgOp P z) ⁻¹' K)
  rw [h_posBody_eq] at hy
  -- Since the map is open, the image of the interior is open and contained in K
  have hy_image : (fun z => pgMu P + pgOp P z) y ∈
      (fun z => pgMu P + pgOp P z) '' interior ((fun z => pgMu P + pgOp P z) ⁻¹' K) :=
    Set.mem_image_of_mem (fun z => pgMu P + pgOp P z) hy
  have h_open_image : IsOpen ((fun z => pgMu P + pgOp P z) ''
      interior ((fun z => pgMu P + pgOp P z) ⁻¹' K)) :=
    h_open _ isOpen_interior
  have h_subset_K : (fun z => pgMu P + pgOp P z) '' interior ((fun z => pgMu P + pgOp P z) ⁻¹' K) ⊆ K := by
    calc
      (fun z => pgMu P + pgOp P z) '' interior ((fun z => pgMu P + pgOp P z) ⁻¹' K) ⊆
          (fun z => pgMu P + pgOp P z) '' ((fun z => pgMu P + pgOp P z) ⁻¹' K) :=
        Set.image_mono interior_subset
      _ ⊆ K := Set.image_preimage_subset _ _
  have h_subset_interior : (fun z => pgMu P + pgOp P z) '' interior ((fun z => pgMu P + pgOp P z) ⁻¹' K) ⊆
      interior K :=
    interior_maximal h_subset_K h_open_image
  exact h_subset_interior hy_image

/-! ## The noise -/

theorem noise_abs_lintegral (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν) (t : ℕ) :
    ∫⁻ ε, ENNReal.ofReal |ε t| ∂ν ≤ 1 := by
  rcases hν with ⟨hν_prob, hν_t⟩
  rcases hν_t t with ⟨h_int, h_mean, h_bound⟩
  have h_pastNoise_le : pastNoise t ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
    have h_meas : Measurable (fun (ε : ℕ → ℝ) (i : Fin t) => ε i) := by
      refine measurable_pi_iff.mpr (fun i => ?_)
      exact measurable_pi_apply (i : ℕ)
    exact h_meas.comap_le
  have h_sigmaFinite : SigmaFinite (ν.trim h_pastNoise_le) :=
    IsFiniteMeasure.toSigmaFinite _
  have h_pointwise : ∀ ε : ℕ → ℝ, |ε t| ≤ Real.exp (ε t ^ 2) / 2 := by
    intro ε
    have h1 : 2 * |ε t| ≤ |ε t| ^ 2 + 1 := by
      have := two_mul_le_add_sq (|ε t|) 1
      simpa using this
    have h2 : |ε t| ^ 2 + 1 ≤ Real.exp (ε t ^ 2) := by
      simpa [sq_abs] using Real.add_one_le_exp (ε t ^ 2)
    linarith
  have h_exp_int : ∫ ε, Real.exp (ε t ^ 2) ∂ν ≤ 2 := by
    calc
      ∫ ε, Real.exp (ε t ^ 2) ∂ν = ∫ ε, (ν[fun ε => Real.exp (ε t ^ 2) | pastNoise t]) ε ∂ν := by
        rw [integral_condExp h_pastNoise_le]
      _ ≤ ∫ ε, (fun _ : ℕ → ℝ => (2 : ℝ)) ε ∂ν :=
        integral_mono_ae (integrable_condExp (μ := ν) (m := pastNoise t))
          (integrable_const _) h_bound
      _ = (2 : ℝ) := by
        rw [integral_const, smul_eq_mul]
        have h_real_univ : ν.real Set.univ = 1 := by
          rw [Measure.real_def, hν_prob.measure_univ]
          norm_num
        rw [h_real_univ]
        norm_num
  calc
    ∫⁻ ε, ENNReal.ofReal |ε t| ∂ν ≤ ∫⁻ ε, ENNReal.ofReal (Real.exp (ε t ^ 2) / 2) ∂ν :=
      lintegral_mono (fun ε => ENNReal.ofReal_le_ofReal (h_pointwise ε))
    _ = ENNReal.ofReal (∫ ε, (Real.exp (ε t ^ 2) / 2) ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal (h_int.div_const 2)
        (by filter_upwards with ε using by positivity : 0 ≤ᵐ[ν] fun ε => Real.exp (ε t ^ 2) / 2)]
    _ = ENNReal.ofReal ((∫ ε, Real.exp (ε t ^ 2) ∂ν) / 2) := by rw [integral_div]
    _ ≤ ENNReal.ofReal (2 / 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h_exp_int (by norm_num))
    _ = ENNReal.ofReal (1 : ℝ) := by norm_num
    _ = 1 := ENNReal.ofReal_one

/-! ## The gauge factor and the positioned body -/

section Leaves

open Classical

/-- The gauge factor `max (1, g/(1 - ε))`, `g` at least the gauge of `X`, brings `X` into `(1 - ε) K'`. -/
theorem gauge_pt_le {d : ℕ} (Kp : Set (EuclideanSpace ℝ (Fin d))) (hc : Convex ℝ Kp)
    (h1 : Metric.closedBall 0 1 ⊆ Kp) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (X : EuclideanSpace ℝ (Fin d)) (g : ℝ)
    (hg : gauge Kp X ≤ g) : gauge Kp ((max 1 (g / (1 - ε)))⁻¹ • X) ≤ 1 - ε := by
  have hm : 0 < max 1 (g / (1 - ε)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1e : 0 < 1 - ε := by linarith
  rw [gauge_smul_of_nonneg (inv_nonneg.2 hm.le), smul_eq_mul]
  have hg0 : 0 ≤ gauge Kp X := gauge_nonneg _
  rcases le_total (g / (1 - ε)) 1 with h | h
  · rw [max_eq_left h, inv_one, one_mul]
    rw [div_le_one h1e] at h
    linarith
  · rw [max_eq_right h, inv_div]
    have hg' : 0 < g := by
      by_contra hneg
      push Not at hneg
      have : g / (1 - ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg h1e.le
      linarith
    calc (1 - ε) / g * gauge Kp X ≤ (1 - ε) / g * g := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 1 - ε := by field_simp

theorem kp_eq_posBody {d : ℕ} (K : Set (E d)) (Ps : PgSp d) (R : ℝ)
    (h : posBody K (pgMu Ps) (pgOp Ps) ⊆ Metric.closedBall 0 R) : df2Kp K Ps R = posBody K (pgMu Ps) (pgOp Ps) := by
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    exact ⟨hy, mem_closedBall_zero_iff.1 (h hy)⟩

theorem kp_convex_of {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (Ps : PgSp d) (R : ℝ) : Convex ℝ (df2Kp K Ps R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have hx1 := hx.1
    have hy1 := hy.1
    have : pgMu Ps + pgOp Ps (a • x + b • y) = a • (pgMu Ps + pgOp Ps x) + b • (pgMu Ps + pgOp Ps y) := by
      rw [map_add, map_smul, map_smul, smul_add, smul_add]
      have : pgMu Ps = a • pgMu Ps + b • pgMu Ps := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      abel
    rw [this]
    exact hK hx1 hy1 ha hb hab
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = R := by rw [← add_mul, hab, one_mul]

theorem kp_closed_of {d : ℕ} (K : Set (E d)) (hK : IsClosed K) (Ps : PgSp d) (R : ℝ) : IsClosed (df2Kp K Ps R) := by
  have h1 : IsClosed {y : E d | pgMu Ps + pgOp Ps y ∈ K} :=
    hK.preimage (continuous_const.add (pgOp Ps).continuous)
  have h2 : IsClosed {y : E d | ‖y‖ ≤ R} := isClosed_le continuous_norm continuous_const
  exact h1.inter h2

end Leaves

end AdversarialBco.Poly.PropG
