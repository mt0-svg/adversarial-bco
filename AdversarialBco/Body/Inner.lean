/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Interface
public import AdversarialBco.Body.Convex
public import AdversarialBco.Body.Gauss
public import AdversarialBco.Body.Ramp
public import AdversarialBco.Body.Transfer
public import AdversarialBco.Body.Smooth

@[expose] public section

/-!
# The transfer half of Proposition 2.2

`AdversarialBco.Body.body_H_of_dilReg`: hypothesis (H)[1/n, CB d^2 log(n d D) log(2n)] on the inner body
`J = {y | closedBall y (1/n) ⊆ K}` from Theorem 3.1 with (3.2) on `ℝ^d` (`DilReg`). Route: minimisers on `J`; the point mass at a minimiser of the mean when `G0 ≤ 1/n`;
otherwise the penalised extensions `lipExt J f_c n + P infDist(·, J)` with `P = (Q (n d D)^6)^2`, smoothed at
`ε = 1/(128 n (1 + Θ))`, `DilReg` applied to the smoothed family, the diluted law
`(1 - q) δ_{b*} + (q/2) δ_b + (q/2) cloud`, `q = G0/(4h)`, mapped by the metric projection onto `J`.

The lemmas `tr_*`, then the assembly.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

/-! ## Batch b14: inner body, law, extension, smoothing -/

theorem AdversarialBco.Body.tr_dirac {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (w : Fin k → ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (bstar : EuclideanSpace ℝ (Fin d)) (hb : bstar ∈ J) (α β : ℝ)
    (hreg : ∑ i, w i * F i bstar - ∑ i, w i * sInf (F i '' J) ≤ α) :
    ∃ ρ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure ρ ∧ ρ Jᶜ = 0 ∧ (∀ i, Integrable (F i) ρ) ∧
      ∫ x, ∑ i, w i * F i x ∂ρ - ∑ i, w i * sInf (F i '' J) ≤
        α + √(β * ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ) := by
  let ρ := Measure.dirac bstar
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Measure.dirac_apply]
    simp [hb]
  · intro i
    apply MeasureTheory.integrable_dirac
    apply enorm_lt_top
  · have h_eq : (∫ x, ∑ i, w i * F i x ∂ρ) = ∑ i, w i * F i bstar := by
      simp [ρ, MeasureTheory.integral_dirac]
    have h_nonneg_sqrt : 0 ≤ √(β * ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ) :=
      Real.sqrt_nonneg _
    rw [h_eq]
    linarith

theorem AdversarialBco.Body.tr_map_proj {d : ℕ} (p : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure p]
    (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : IsClosed J)
    (pr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hpr : Continuous pr) (hprJ : ∀ x, pr x ∈ J)
    (Φ g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : Continuous g) (hgJ : ∀ y ∈ J, Φ y = g y) (B : ℝ)
    (hB : ∀ y ∈ J, |Φ y| ≤ B) :
    IsProbabilityMeasure (p.map pr) ∧ (p.map pr) Jᶜ = 0 ∧ Integrable Φ (p.map pr) ∧
      Integrable (fun x => Φ (pr x)) p ∧ ∫ y, Φ y ∂(p.map pr) = ∫ x, Φ (pr x) ∂p := by
  have hpr_meas : AEMeasurable pr p := hpr.measurable.aemeasurable
  have hJ_comp_meas : MeasurableSet Jᶜ := hJ.isOpen_compl.measurableSet
  have h_preimage_empty : pr ⁻¹' Jᶜ = ∅ := by
    ext x; simp [hprJ x]
  have h_map_prob : IsProbabilityMeasure (p.map pr) := inferInstance
  have h_map_compl_zero : (p.map pr) Jᶜ = 0 := by
    calc
      (p.map pr) Jᶜ = p (pr ⁻¹' Jᶜ) :=
        Measure.map_apply_of_aemeasurable hpr_meas hJ_comp_meas
      _ = p ∅ := by rw [h_preimage_empty]
      _ = 0 := measure_empty
  have h_ae_mem_J : ∀ᵐ y ∂(p.map pr), y ∈ J := by
    rw [ae_iff]
    have : {y | ¬ y ∈ J} = Jᶜ := by ext y; simp
    rw [this]
    exact h_map_compl_zero
  have h_ae_eq : Φ =ᵐ[p.map pr] g := by
    have h_sub : {x | Φ x ≠ g x} ⊆ Jᶜ := by
      intro x hx
      by_contra! hx_notin_Jc
      -- hx_notin_Jc : x ∉ Jᶜ, i.e., x ∈ J
      have hxJ : x ∈ J := by simpa using hx_notin_Jc
      apply hx
      exact hgJ x hxJ
    refine (ae_iff (μ := p.map pr) (p := fun x => Φ x = g x)).mpr ?_
    have : {x | ¬ (Φ x = g x)} = {x | Φ x ≠ g x} := by ext x; simp
    rw [this]
    exact measure_mono_null h_sub h_map_compl_zero
  have h_int_g : Integrable g (p.map pr) := by
    have h_bound : ∀ᵐ y ∂(p.map pr), ‖g y‖ ≤ B := by
      filter_upwards [h_ae_mem_J] with y hy
      calc
        ‖g y‖ = |g y| := by simp
        _ = |Φ y| := by rw [hgJ y hy]
        _ ≤ B := hB y hy
    have : IsFiniteMeasure (p.map pr) := by infer_instance
    exact Integrable.mono' (integrable_const B) hg.aestronglyMeasurable h_bound
  have h_int_Φ : Integrable Φ (p.map pr) :=
    h_int_g.congr h_ae_eq.symm
  have h_int_Φ_pr : Integrable (fun x => Φ (pr x)) p := by
    have h_pointwise : (fun x => Φ (pr x)) = g ∘ pr := by
      ext x
      exact hgJ (pr x) (hprJ x)
    rw [h_pointwise]
    have h_bound : ∀ᵐ x ∂p, ‖g (pr x)‖ ≤ B := by
      filter_upwards with x
      calc
        ‖g (pr x)‖ = |g (pr x)| := by simp
        _ = |Φ (pr x)| := by rw [hgJ (pr x) (hprJ x)]
        _ ≤ B := hB (pr x) (hprJ x)
    have h_cont : Continuous (g ∘ pr) := hg.comp hpr
    have h_aestrongly : AEStronglyMeasurable (g ∘ pr) p :=
      h_cont.aestronglyMeasurable
    have : IsFiniteMeasure p := by infer_instance
    exact Integrable.mono' (integrable_const B) h_aestrongly h_bound
  have h_integral_eq : ∫ y, Φ y ∂(p.map pr) = ∫ x, Φ (pr x) ∂p := by
    calc
      ∫ y, Φ y ∂(p.map pr) = ∫ y, g y ∂(p.map pr) := integral_congr_ae h_ae_eq
      _ = ∫ x, g (pr x) ∂p := integral_map hpr_meas hg.aestronglyMeasurable
      _ = ∫ x, Φ (pr x) ∂p := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [hgJ (pr x) (hprJ x)]
  exact ⟨h_map_prob, h_map_compl_zero, h_int_Φ, h_int_Φ_pr, h_integral_eq⟩

theorem AdversarialBco.Body.tr_ext {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJv : Convex ℝ J)
    (hJn : J.Nonempty) (f : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) (hf : ConvexOn ℝ J f)
    (hfl : ∀ x ∈ J, ∀ y ∈ J, |f x - f y| ≤ n * dist x y) (hf01 : ∀ x ∈ J, f x ∈ Set.Icc (0 : ℝ) 1) (P : ℝ)
    (hP : 0 ≤ P) :
    Continuous (AdversarialBco.lipExt J f n) ∧ (∀ x ∈ J, AdversarialBco.lipExt J f n x = f x) ∧
      ConvexOn ℝ Set.univ (fun x => AdversarialBco.lipExt J f n x + P * Metric.infDist x J) ∧
      LipschitzWith (Real.toNNReal (n + P)) (fun x => AdversarialBco.lipExt J f n x + P * Metric.infDist x J) := by
  have hfb : BddBelow (f '' J) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (hf01 x hx).1
  have hfl' : ∀ x ∈ J, ∀ y ∈ J, f x ≤ f y + (n : ℝ) * dist x y := by
    intro x hx y hy
    have h := hfl x hx y hy
    have hle : f x - f y ≤ |f x - f y| := le_abs_self _
    linarith
  have h_lip : LipschitzWith ((n : ℕ) : ℝ≥0) (AdversarialBco.lipExt J f (n : ℝ)) := by
    have h := AdversarialBco.Body.lipExt_lipschitz J hJn f hfb (n : ℝ≥0)
    simpa [NNReal.coe_natCast] using h
  have h_cont : Continuous (AdversarialBco.lipExt J f (n : ℝ)) :=
    h_lip.continuous
  have h_val : ∀ x ∈ J, AdversarialBco.lipExt J f (n : ℝ) x = f x := by
    intro x hx
    exact AdversarialBco.lipExt_eq J f (n : ℝ) hfl' x hx
  have h_conv_lip : ConvexOn ℝ Set.univ (AdversarialBco.lipExt J f (n : ℝ)) :=
    AdversarialBco.lipExt_convex J hJv hJn f hf hfb (n : ℝ) (Nat.cast_nonneg n)
  have h_conv_inf : ConvexOn ℝ Set.univ (fun x => Metric.infDist x J) :=
    AdversarialBco.convexOn_infDist J hJv
  have h_conv_inf' : ConvexOn ℝ Set.univ (fun x => P * Metric.infDist x J) := by
    have h := ConvexOn.smul hP h_conv_inf
    simpa [smul_eq_mul] using h
  have h_conv_total : ConvexOn ℝ Set.univ (fun x => AdversarialBco.lipExt J f (n : ℝ) x + P * Metric.infDist x J) := by
    have h := ConvexOn.add h_conv_lip h_conv_inf'
    -- h : ConvexOn ℝ Set.univ (lipExt J f (n : ℝ) + (fun x => P * Metric.infDist x J))
    -- which is definitionally ConvexOn ℝ Set.univ (fun x => lipExt J f (n : ℝ) x + P * Metric.infDist x J)
    exact h
  have h_lip_Pinf : LipschitzWith (Real.toNNReal P) (fun x => P * Metric.infDist x J) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hPcoeff : (Real.toNNReal P : ℝ) = P := Real.coe_toNNReal P hP
    rw [hPcoeff]
    have h_inf_dist : |Metric.infDist x J - Metric.infDist y J| ≤ dist x y := by
      have h1 : Metric.infDist x J - Metric.infDist y J ≤ dist x y := by
        have h := Metric.infDist_le_infDist_add_dist (s := J) (x := x) (y := y)
        linarith
      have h2 : Metric.infDist y J - Metric.infDist x J ≤ dist x y := by
        have h := Metric.infDist_le_infDist_add_dist (s := J) (x := y) (y := x)
        rw [dist_comm y x] at h
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |P * Metric.infDist x J - P * Metric.infDist y J| = |P * (Metric.infDist x J - Metric.infDist y J)| := by rw [mul_sub]
      _ = |P| * |Metric.infDist x J - Metric.infDist y J| := by rw [abs_mul]
      _ = P * |Metric.infDist x J - Metric.infDist y J| := by rw [abs_of_nonneg hP]
      _ ≤ P * dist x y := mul_le_mul_of_nonneg_left h_inf_dist hP
  have h_lip_total : LipschitzWith (((n : ℕ) : ℝ≥0) + Real.toNNReal P) (fun x => AdversarialBco.lipExt J f (n : ℝ) x + P * Metric.infDist x J) :=
    LipschitzWith.add h_lip h_lip_Pinf
  have h_nnreal_eq : Real.toNNReal ((n : ℝ) + P) = ((n : ℕ) : ℝ≥0) + Real.toNNReal P := by
    rw [Real.toNNReal_add (Nat.cast_nonneg n) hP, Real.toNNReal_natCast]
  exact ⟨h_cont, h_val, h_conv_total, by simpa [h_nnreal_eq] using h_lip_total⟩

theorem AdversarialBco.Body.tr_smooth_family {d k : ℕ} (Φ : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hΦ : ∀ c, LipschitzWith L (Φ c)) (hc : ∀ c, ConvexOn ℝ Set.univ (Φ c)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ≥0), ∀ c, ContDiff ℝ 2 (F c) ∧
      ConvexOn ℝ Set.univ (F c) ∧ LipschitzWith L (F c) ∧ LipschitzWith M (fderiv ℝ (F c)) ∧
      ∀ x, |F c x - Φ c x| ≤ ε := by
  choose F hF using fun c => AdversarialBco.Body.smooth_convex (Φ c) L (hΦ c) (hc c) ε hε
  have hF' : ∀ c, ContDiff ℝ 2 (F c) ∧ ConvexOn ℝ Set.univ (F c) ∧ LipschitzWith L (F c) ∧
      (∃ M : ℝ≥0, LipschitzWith M (fderiv ℝ (F c))) ∧ ∀ x, |F c x - Φ c x| ≤ ε := hF
  choose M hM using fun c => (hF' c).2.2.2.1
  refine ⟨F, Finset.univ.sup M, fun c => ?_⟩
  have hMc : M c ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ c)
  have h_contdiff : ContDiff ℝ 2 (F c) := (hF' c).1
  have h_convex : ConvexOn ℝ Set.univ (F c) := (hF' c).2.1
  have h_lip : LipschitzWith L (F c) := (hF' c).2.2.1
  have h_lip' : LipschitzWith (Finset.univ.sup M) (fderiv ℝ (F c)) :=
    LipschitzWith.weaken (hM c) hMc
  have h_bound : ∀ x, |F c x - Φ c x| ≤ ε := (hF' c).2.2.2.2
  exact ⟨h_contdiff, h_convex, h_lip, h_lip', h_bound⟩

theorem AdversarialBco.Body.tr_infDist_ge {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ J) (D : ℝ) (hJD : ∀ y ∈ J, dist y c ≤ D)
    (z : EuclideanSpace ℝ (Fin d)) : ‖z‖ - (‖c‖ + D) ≤ Metric.infDist z J := by
  have hJ_nonempty : J.Nonempty := ⟨c, hc⟩
  rw [Metric.le_infDist hJ_nonempty]
  intro y hy
  have hy_bound : ‖y‖ ≤ ‖c‖ + D := by
    calc
      ‖y‖ ≤ ‖y - c‖ + ‖c‖ := norm_le_norm_sub_add y c
      _ = dist y c + ‖c‖ := by rw [dist_eq_norm]
      _ ≤ D + ‖c‖ := by nlinarith [hJD y hy]
      _ = ‖c‖ + D := by ring
  have hz_bound : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := norm_le_norm_sub_add z y
  rw [dist_eq_norm]
  nlinarith

theorem AdversarialBco.Body.tr_unit_bounds (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (a : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) :
    |∑ i, w i * a i| ≤ 1 ∧ |∑ i, w i * ((∑ j, w j * a j) - a i) ^ 2| ≤ 1 := by
  have ha_low : ∀ i, 0 ≤ a i := λ i => (ha i).1
  have ha_high : ∀ i, a i ≤ 1 := λ i => (ha i).2
  set m := ∑ i : Fin k, w i * a i with hm
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    refine Finset.sum_nonneg (λ i _ => ?_)
    exact mul_nonneg (hw i) (ha_low i)
  have hm_le_one : m ≤ 1 := by
    dsimp [m]
    calc
      ∑ i : Fin k, w i * a i ≤ ∑ i : Fin k, w i := by
        refine Finset.sum_le_sum (λ i _ => ?_)
        have h := mul_le_mul_of_nonneg_left (ha_high i) (hw i)
        simpa [mul_one] using h
      _ = 1 := hw1
  have h_abs_m : |m| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h_sq_bound : ∀ i, (m - a i) ^ 2 ≤ 1 := by
    intro i
    have h_abs : |m - a i| ≤ 1 := by
      rw [abs_le]
      have hlow := ha_low i
      have hhigh := ha_high i
      constructor
      · linarith
      · linarith
    have h := abs_le.mp h_abs
    nlinarith
  have h_nonneg_sq : ∀ i, 0 ≤ (m - a i) ^ 2 := λ i => pow_two_nonneg _
  have h_summand_nonneg : ∀ i, 0 ≤ w i * (m - a i) ^ 2 := λ i =>
    mul_nonneg (hw i) (h_nonneg_sq i)
  have h_summand_le_wi : ∀ i, w i * (m - a i) ^ 2 ≤ w i := by
    intro i
    have h := h_sq_bound i
    calc
      w i * (m - a i) ^ 2 ≤ w i * 1 := mul_le_mul_of_nonneg_left h (hw i)
      _ = w i := mul_one _
  have h_sum_nonneg : 0 ≤ ∑ i : Fin k, w i * (m - a i) ^ 2 :=
    Finset.sum_nonneg (λ i _ => h_summand_nonneg i)
  have h_sum_le_one : ∑ i : Fin k, w i * (m - a i) ^ 2 ≤ 1 := by
    calc
      ∑ i : Fin k, w i * (m - a i) ^ 2 ≤ ∑ i : Fin k, w i :=
        Finset.sum_le_sum (λ i _ => h_summand_le_wi i)
      _ = 1 := hw1
  have h_abs_sum : |∑ i : Fin k, w i * (m - a i) ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hm_eq : m = ∑ j : Fin k, w j * a j := rfl
  simpa [hm, hm_eq] using And.intro h_abs_m h_abs_sum

theorem AdversarialBco.Body.tr_variance_shift (k : ℕ) (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (a b : Fin k → ℝ) (t e : ℝ) (h : ∀ c, |a c - t - b c| ≤ e) :
    ∑ c, w c * (a c - ∑ c', w c' * a c') ^ 2 ≤ 2 * ∑ c, w c * ((∑ c', w c' * b c') - b c) ^ 2 + 8 * e ^ 2 := by
  have hv := AdversarialBco.Body.variance_transfer k w hw hw1 (fun c => a c - t) b e h
  have hshift : ∑ c', w c' * (a c' - t) = (∑ c', w c' * a c') - t := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  have hl : ∑ c, w c * (a c - t - ∑ c', w c' * (a c' - t)) ^ 2 = ∑ c, w c * (a c - ∑ c', w c' * a c') ^ 2 := by
    rw [hshift]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hr : ∑ c, w c * (b c - ∑ c', w c' * b c') ^ 2 = ∑ c, w c * ((∑ c', w c' * b c') - b c) ^ 2 :=
    Finset.sum_congr rfl fun c _ => by ring
  rw [← hl, ← hr]
  exact hv

/-! ## Batch b14: the Gaussian cloud -/

theorem AdversarialBco.Body.tr_integrable_cloud {d : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hΨ : LipschitzWith L Ψ) :
    Integrable Ψ (AdversarialBco.Gauss.cloud b S) ∧ Integrable (fun x => Ψ x ^ 2) (AdversarialBco.Gauss.cloud b S) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun g => b + S g
  have hcloud : AdversarialBco.Gauss.cloud b S = μ.map T := rfl
  rw [hcloud]
  have hT_cont : Continuous T := by
    exact (continuous_const.add (S.continuous))
  have hT_meas : AEMeasurable T μ := hT_cont.aemeasurable
  have hΨ_cont : Continuous Ψ := hΨ.continuous
  have hΨ_meas : AEStronglyMeasurable Ψ (μ.map T) := hΨ_cont.aestronglyMeasurable
  have hΨsq_meas : AEStronglyMeasurable (fun x => Ψ x ^ 2) (μ.map T) := by
    have hcont_sq : Continuous (fun x => Ψ x ^ 2) := hΨ_cont.pow 2
    exact hcont_sq.aestronglyMeasurable
  -- triangle inequality for absolute value
  have h_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
    calc
      |a + b| = |a - (-b)| := by ring_nf
      _ ≤ |a| + |-b| := abs_sub _ _
      _ = |a| + |b| := by simp
  -- integrability of S under μ
  have h_int_S : Integrable S μ := by
    have h_int_id : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) μ :=
      IsGaussian.integrable_id
    exact S.integrable_comp h_int_id
  have h_int_normS : Integrable (fun g => ‖S g‖) μ := h_int_S.norm
  -- integrability of ‖S g‖^2 using the bound ‖S g‖^2 ≤ ‖S‖^2 * ‖g‖^2
  have h_int_normS_sq : Integrable (fun g => ‖S g‖ ^ 2) μ := by
    have h_bound : ∀ g, ‖S g‖ ^ 2 ≤ (‖S‖ ^ 2) * (‖g‖ ^ 2) := by
      intro g
      have hS_le : ‖S g‖ ≤ ‖S‖ * ‖g‖ := S.le_opNorm g
      have h_nonneg_S : 0 ≤ ‖S‖ := norm_nonneg _
      have h_nonneg_g : 0 ≤ ‖g‖ := norm_nonneg _
      have h_nonneg_Sg : 0 ≤ ‖S g‖ := norm_nonneg _
      have h_sq : (‖S g‖) ^ 2 ≤ (‖S‖ * ‖g‖) ^ 2 := by
        nlinarith
      nlinarith
    have h_ae_bound : ∀ᵐ g ∂μ, ‖(fun g => ‖S g‖ ^ 2) g‖ ≤ ((fun _ => (‖S‖ ^ 2) * (‖g‖ ^ 2)) g) := by
      filter_upwards with g
      have hpos : 0 ≤ ‖S g‖ ^ 2 := pow_two_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hpos] using h_bound g
    have h_int_g_sq : Integrable (fun g => ‖g‖ ^ 2) μ := by
      have h_memLp : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 2 μ :=
        IsGaussian.memLp_id μ 2 (by norm_num)
      have h_int : Integrable (fun g => ‖(id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) g‖ ^ 2) μ :=
        h_memLp.integrable_norm_pow (by norm_num)
      simpa using h_int
    have h_int_dom : Integrable (fun g => (‖S‖ ^ 2) * (‖g‖ ^ 2)) μ :=
      h_int_g_sq.const_mul (‖S‖ ^ 2)
    have h_meas : AEStronglyMeasurable (fun g => ‖S g‖ ^ 2) μ := by
      have h_cont_sq : Continuous (fun x : ℝ => x ^ 2) := by continuity
      have h_cont_normS : Continuous (fun g => ‖S g‖) :=
        continuous_norm.comp S.continuous
      exact (h_cont_sq.comp h_cont_normS).aestronglyMeasurable
    exact h_int_dom.mono' h_meas h_ae_bound
  -- the Lipschitz bound (used in both h_int1 and h_int2)
  have h_bound : ∀ g, |Ψ (T g)| ≤ |Ψ b| + (L : ℝ) * ‖S g‖ := by
    intro g
    calc
      |Ψ (T g)| = |Ψ (b + S g)| := rfl
      _ = |(Ψ (b + S g) - Ψ b) + Ψ b| := by ring_nf
      _ ≤ |Ψ (b + S g) - Ψ b| + |Ψ b| := h_abs_add _ _
      _ = dist (Ψ (b + S g)) (Ψ b) + |Ψ b| := by rw [Real.dist_eq]
      _ ≤ (L : ℝ) * dist (b + S g) b + |Ψ b| := by
        nlinarith [hΨ.dist_le_mul (b + S g) b]
      _ = (L : ℝ) * ‖(b + S g) - b‖ + |Ψ b| := by rw [dist_eq_norm]
      _ = (L : ℝ) * ‖S g‖ + |Ψ b| := by rw [add_sub_cancel_left]
      _ = |Ψ b| + (L : ℝ) * ‖S g‖ := add_comm _ _
  have h_int1 : Integrable (Ψ ∘ T) μ := by
    have h_ae_bound : ∀ᵐ g ∂μ, ‖(Ψ ∘ T) g‖ ≤ ((fun _ => |Ψ b|) g + (fun g => (L : ℝ) * ‖S g‖) g) := by
      filter_upwards with g
      have hpos : 0 ≤ |(Ψ ∘ T) g| := abs_nonneg _
      simpa [Real.norm_eq_abs, Pi.add_apply] using h_bound g
    have h_int_const : Integrable (fun _ => |Ψ b|) μ := by
      apply integrable_const
    have h_int_dom : Integrable (fun g => (L : ℝ) * ‖S g‖) μ :=
      h_int_normS.const_mul (L : ℝ)
    have h_meas : AEStronglyMeasurable (Ψ ∘ T) μ :=
      (hΨ_cont.comp hT_cont).aestronglyMeasurable
    exact (h_int_const.add h_int_dom).mono' h_meas h_ae_bound
  have h_int2 : Integrable ((Ψ ∘ T) ^ 2) μ := by
    -- bound (Ψ(T g))^2 ≤ 2 * (Ψ b)^2 + 2 * ((L : ℝ) * ‖S g‖)^2
    have h_bound_sq : ∀ g, (Ψ (T g)) ^ 2 ≤ 2 * ((Ψ b) ^ 2) + 2 * (((L : ℝ) * ‖S g‖) ^ 2) := by
      intro g
      have h_abs := h_bound g
      have h_nonneg_abs : 0 ≤ |Ψ (T g)| := abs_nonneg _
      have h_nonneg_bound : 0 ≤ |Ψ b| + (L : ℝ) * ‖S g‖ := by
        positivity
      have h_sq_abs : |Ψ (T g)| ^ 2 ≤ (|Ψ b| + (L : ℝ) * ‖S g‖) ^ 2 := by
        nlinarith
      have h_sq_abs_eq : |Ψ (T g)| ^ 2 = (Ψ (T g)) ^ 2 := sq_abs _
      have h_sq : (Ψ (T g)) ^ 2 ≤ (|Ψ b| + (L : ℝ) * ‖S g‖) ^ 2 := by
        nlinarith
      have h_expand : (|Ψ b| + (L : ℝ) * ‖S g‖) ^ 2 ≤ 2 * ((Ψ b) ^ 2) + 2 * (((L : ℝ) * ‖S g‖) ^ 2) := by
        have hx_sq : (|Ψ b|) ^ 2 = (Ψ b) ^ 2 := sq_abs _
        have h_nonneg_sq : 0 ≤ (|Ψ b| - (L : ℝ) * ‖S g‖) ^ 2 := pow_two_nonneg _
        nlinarith
      nlinarith
    have h_ae_bound : ∀ᵐ g ∂μ, ‖((Ψ ∘ T) ^ 2) g‖ ≤ ((fun _ => 2 * ((Ψ b) ^ 2)) g + (fun g => 2 * (((L : ℝ) * ‖S g‖) ^ 2)) g) := by
      filter_upwards with g
      have h_nonneg_sq : 0 ≤ (Ψ (T g)) ^ 2 := pow_two_nonneg _
      have h_norm : ‖((Ψ ∘ T) ^ 2) g‖ = |(Ψ (T g)) ^ 2| := Real.norm_eq_abs _
      have h_abs_sq : |(Ψ (T g)) ^ 2| = (Ψ (T g)) ^ 2 := abs_of_nonneg h_nonneg_sq
      simpa [h_norm, h_abs_sq, Pi.add_apply] using h_bound_sq g
    have h_int_const : Integrable (fun _ => 2 * ((Ψ b) ^ 2)) μ := by
      apply integrable_const
    have h_int_dom : Integrable (fun g => 2 * (((L : ℝ) * ‖S g‖) ^ 2)) μ := by
      have h_int : Integrable (fun g => ((L : ℝ) * ‖S g‖) ^ 2) μ := by
        simpa [mul_pow] using h_int_normS_sq.const_mul ((L : ℝ) ^ 2)
      exact h_int.const_mul 2
    have h_meas : AEStronglyMeasurable ((Ψ ∘ T) ^ 2) μ := by
      have h_cont_sq : Continuous (fun g => (Ψ (T g)) ^ 2) := hΨ_cont.pow 2 |>.comp hT_cont
      exact h_cont_sq.aestronglyMeasurable
    exact (h_int_const.add h_int_dom).mono' h_meas h_ae_bound
  exact ⟨(MeasureTheory.integrable_map_measure hΨ_meas hT_meas).mpr h_int1,
         (MeasureTheory.integrable_map_measure hΨsq_meas hT_meas).mpr h_int2⟩

theorem AdversarialBco.Body.tr_integrable_cloud_var {d k : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (w : Fin k → ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hF : ∀ c, LipschitzWith L (F c)) :
    Integrable (fun x => ∑ c, w c * F c x) (AdversarialBco.Gauss.cloud b S) ∧
      Integrable (fun x => ∑ c, w c * (F c x - ∑ c', w c' * F c' x) ^ 2) (AdversarialBco.Gauss.cloud b S) := by
  have hm : LipschitzWith ((∑ c, ‖w c‖₊) * L) (fun x => ∑ c, w c * F c x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← Finset.sum_sub_distrib]
    calc |∑ c, (w c * F c x - w c * F c y)| ≤ ∑ c, |w c * F c x - w c * F c y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, ‖w c‖ * (L * dist x y) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [← mul_sub, abs_mul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← Real.dist_eq]
        exact (hF c).dist_le_mul x y
      _ = _ := by
        simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
  refine ⟨(AdversarialBco.Body.tr_integrable_cloud b S _ _ hm).1, ?_⟩
  exact integrable_finsetSum _ fun c _ =>
    (AdversarialBco.Body.tr_integrable_cloud b S _ _ ((hF c).sub hm)).2.const_mul (w c)

theorem AdversarialBco.Body.tr_jensen_infDist {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : Convex ℝ J)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Metric.infDist b J ≤ ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  set δ := fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J with hδ
  set G := fun w : EuclideanSpace ℝ (Fin d) => δ (b + S w) with hG
  have hδ_lip : LipschitzWith 1 δ := Metric.lipschitz_infDist_pt J
  have hδ_convex : ConvexOn ℝ Set.univ δ := AdversarialBco.convexOn_infDist J hJ
  have hδ_cont : Continuous δ := Metric.continuous_infDist_pt J
  have hG_convex : ConvexOn ℝ Set.univ G := by
    let φ : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      { toFun := fun w => b + S w
        linear := S
        map_vadd' := fun x y => by
          simp [add_comm, add_left_comm, S.map_add] }
    have h := hδ_convex.comp_affineMap φ
    -- h : ConvexOn ℝ (φ ⁻¹' Set.univ) (δ ∘ φ)
    -- φ ⁻¹' Set.univ = Set.univ, and δ ∘ φ = G
    have hφ_univ : φ ⁻¹' Set.univ = Set.univ := by simp
    have hδφ_eq_G : δ ∘ φ = G := by
      ext w; simp [φ, G, δ]
    simpa [hφ_univ, hδφ_eq_G] using h
  have hsymm : μ.map (fun w => -w) = μ := by
    simpa [μ] using stdGaussian_map (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
  have h_integ_cloud : Integrable δ (AdversarialBco.Gauss.cloud b S) :=
    (AdversarialBco.Body.tr_integrable_cloud b S δ 1 hδ_lip).1
  have h_cloud_eq : AdversarialBco.Gauss.cloud b S = μ.map (fun g => b + S g) := rfl
  rw [h_cloud_eq] at h_integ_cloud
  have h_ae_meas : AEMeasurable (fun w : EuclideanSpace ℝ (Fin d) => b + S w) μ :=
    (measurable_const.add S.measurable).aemeasurable
  have h_integ_comp : Integrable (δ ∘ (fun w : EuclideanSpace ℝ (Fin d) => b + S w)) μ :=
    h_integ_cloud.comp_aemeasurable h_ae_meas
  have h_integ_μ : Integrable (fun w => G (0 + w)) μ := by
    have h_eq : (fun w => G (0 + w)) = δ ∘ (fun w => b + S w) := by
      ext w; simp [G, δ]
    rw [h_eq]
    exact h_integ_comp
  have h_jensen := AdversarialBco.jensen_symm μ hsymm G hG_convex 0 h_integ_μ
  have h_int_map : ∫ x, δ x ∂(μ.map (fun g => b + S g)) = ∫ w, δ (b + S w) ∂μ := by
    have h_meas : Measurable (fun g : EuclideanSpace ℝ (Fin d) => b + S g) :=
      measurable_const.add S.measurable
    have h_strong : StronglyMeasurable δ := hδ_cont.stronglyMeasurable
    rw [MeasureTheory.integral_map_of_stronglyMeasurable h_meas h_strong]
  calc
    Metric.infDist b J = δ b := rfl
    _ = G 0 := by simp [G, δ]
    _ ≤ ∫ w, G (0 + w) ∂μ := h_jensen
    _ = ∫ w, δ (b + S w) ∂μ := by simp [G, δ]
    _ = ∫ x, δ x ∂(μ.map (fun g => b + S g)) := by rw [h_int_map]
    _ = ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) := by simp [δ, AdversarialBco.Gauss.cloud, μ]

theorem AdversarialBco.Body.tr_opNorm_bound {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d)))
    (pr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hprJ : ∀ x, pr x ∈ J)
    (hpr : ∀ x, dist x (pr x) = Metric.infDist x J) (D : ℝ) (hJD : ∀ x ∈ J, ∀ y ∈ J, dist x y ≤ D)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (2 / Real.pi) * ‖S‖ ≤
      ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) + D + Metric.infDist b J := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hμ_prob : IsProbabilityMeasure μ := by infer_instance
  have hcloud_eq : AdversarialBco.Gauss.cloud b S = μ.map (fun g => b + S g) := rfl
  -- pointwise bound for every g
  have h_pointwise : ∀ g, ‖S g‖ ≤ Metric.infDist (b + S g) J + D + Metric.infDist b J := by
    intro g
    have hJD' := hJD (pr (b + S g)) (hprJ _) (pr b) (hprJ _)
    calc
      ‖S g‖ = ‖(b + S g) - b‖ := by simp [add_sub_cancel_left]
      _ = dist (b + S g) b := by rw [dist_eq_norm]
      _ ≤ dist (b + S g) (pr (b + S g)) + dist (pr (b + S g)) b := dist_triangle _ _ _
      _ = Metric.infDist (b + S g) J + dist (pr (b + S g)) b := by rw [hpr]
      _ ≤ Metric.infDist (b + S g) J + (dist (pr (b + S g)) (pr b) + dist (pr b) b) := by
        nlinarith [dist_triangle (pr (b + S g)) (pr b) b]
      _ = Metric.infDist (b + S g) J + dist (pr (b + S g)) (pr b) + dist (pr b) b := by ring
      _ ≤ Metric.infDist (b + S g) J + D + dist (pr b) b := by nlinarith
      _ = Metric.infDist (b + S g) J + D + Metric.infDist b J := by
        rw [← hpr b, dist_comm b (pr b)]
  -- integrability of ‖S g‖ under μ
  have h_int_norm : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖S g‖) μ := by
    have h_cloud_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖)
        (AdversarialBco.Gauss.cloud (0 : EuclideanSpace ℝ (Fin d)) S) :=
      (AdversarialBco.Body.tr_integrable_cloud (0 : EuclideanSpace ℝ (Fin d)) S (fun x => ‖x‖) 1
        lipschitzWith_one_norm).1
    have h_cloud_eq0 : AdversarialBco.Gauss.cloud (0 : EuclideanSpace ℝ (Fin d)) S = μ.map S := by
      ext x; simp [AdversarialBco.Gauss.cloud, μ]
    rw [h_cloud_eq0] at h_cloud_int
    have h_meas_S : AEMeasurable S μ := S.continuous.aemeasurable
    have h_ae_strongly : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) (μ.map S) :=
      h_cloud_int.aestronglyMeasurable
    exact ((MeasureTheory.integrable_map_measure h_ae_strongly h_meas_S).mp h_cloud_int)
  -- integrability of Metric.infDist (b + S g) J under μ
  have h_int_infDist : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => Metric.infDist (b + S g) J) μ := by
    have h_cloud_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J)
        (AdversarialBco.Gauss.cloud b S) :=
      (AdversarialBco.Body.tr_integrable_cloud b S (fun x => Metric.infDist x J) 1
        (Metric.lipschitz_infDist_pt J)).1
    rw [hcloud_eq] at h_cloud_int
    have h_meas_map : AEMeasurable (fun g => b + S g) μ :=
      ((continuous_const.add S.continuous)).aemeasurable
    have h_ae_strongly : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J)
        (μ.map (fun g => b + S g)) :=
      h_cloud_int.aestronglyMeasurable
    exact ((MeasureTheory.integrable_map_measure h_ae_strongly h_meas_map).mp h_cloud_int)
  -- integrability of the sum
  have h_int_sum : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) =>
      Metric.infDist (b + S g) J + D + Metric.infDist b J) μ := by
    have h_int_const : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => D) μ :=
      MeasureTheory.integrable_const (c := D) (μ := μ)
    have h_int_const_infDist : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => Metric.infDist b J) μ :=
      MeasureTheory.integrable_const (c := Metric.infDist b J) (μ := μ)
    have h_int_add1 : Integrable (fun g => Metric.infDist (b + S g) J + D) μ :=
      Integrable.add h_int_infDist h_int_const
    exact Integrable.add h_int_add1 h_int_const_infDist
  -- apply integral_mono
  have h_int_bound : ∫ g, ‖S g‖ ∂μ ≤ ∫ g, (Metric.infDist (b + S g) J + D + Metric.infDist b J) ∂μ :=
    MeasureTheory.integral_mono h_int_norm h_int_sum h_pointwise
  -- split the RHS integral
  have h_int_rhs : ∫ g, (Metric.infDist (b + S g) J + D + Metric.infDist b J) ∂μ =
      (∫ g, Metric.infDist (b + S g) J ∂μ) + D + Metric.infDist b J := by
    have h_int_D : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => D) μ :=
      MeasureTheory.integrable_const (c := D) (μ := μ)
    have h_int_infDist_b : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => Metric.infDist b J) μ :=
      MeasureTheory.integrable_const (c := Metric.infDist b J) (μ := μ)
    have h_int_fst : Integrable (fun g => Metric.infDist (b + S g) J + D) μ :=
      Integrable.add h_int_infDist h_int_D
    calc
      ∫ g, (Metric.infDist (b + S g) J + D + Metric.infDist b J) ∂μ =
          (∫ g, (Metric.infDist (b + S g) J + D) ∂μ) + (∫ g, Metric.infDist b J ∂μ) :=
        MeasureTheory.integral_add h_int_fst h_int_infDist_b
      _ = ((∫ g, Metric.infDist (b + S g) J ∂μ) + (∫ g, D ∂μ)) + (∫ g, Metric.infDist b J ∂μ) := by
        rw [MeasureTheory.integral_add h_int_infDist h_int_D]
      _ = ((∫ g, Metric.infDist (b + S g) J ∂μ) + D) + Metric.infDist b J := by
        rw [MeasureTheory.integral_const (c := D) (μ := μ),
          MeasureTheory.integral_const (c := Metric.infDist b J) (μ := μ),
          MeasureTheory.probReal_univ (μ := μ)]
        simp
      _ = (∫ g, Metric.infDist (b + S g) J ∂μ) + D + Metric.infDist b J := by ring
  -- convert ∫ g, Metric.infDist (b + S g) J ∂μ to ∫ x, Metric.infDist x J ∂(cloud b S)
  have h_int_cloud : ∫ g, Metric.infDist (b + S g) J ∂μ =
      ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) := by
    rw [hcloud_eq]
    have h_meas_map : AEMeasurable (fun g => b + S g) μ :=
      ((continuous_const.add S.continuous)).aemeasurable
    have h_ae_strongly : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J)
        (μ.map (fun g => b + S g)) := by
      have h_int_cloud' : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J)
          (μ.map (fun g => b + S g)) := by
        rw [← hcloud_eq]
        exact (AdversarialBco.Body.tr_integrable_cloud b S (fun x => Metric.infDist x J) 1
          (Metric.lipschitz_infDist_pt J)).1
      exact h_int_cloud'.aestronglyMeasurable
    rw [MeasureTheory.integral_map h_meas_map h_ae_strongly]
  -- put everything together
  have h_opNorm : Real.sqrt (2 / Real.pi) * ‖S‖ ≤ ∫ g, ‖S g‖ ∂μ :=
    AdversarialBco.Body.opNorm_le_integral_norm S
  calc
    Real.sqrt (2 / Real.pi) * ‖S‖ ≤ ∫ g, ‖S g‖ ∂μ := h_opNorm
    _ ≤ ∫ g, (Metric.infDist (b + S g) J + D + Metric.infDist b J) ∂μ := h_int_bound
    _ = (∫ g, Metric.infDist (b + S g) J ∂μ) + D + Metric.infDist b J := by rw [h_int_rhs]
    _ = (∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S)) + D + Metric.infDist b J := by
      rw [h_int_cloud]
    _ = ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) + D + Metric.infDist b J := rfl

theorem AdversarialBco.Body.tr_cloud_sq {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (σ : ℝ) (hσ : 0 < σ) (hS : ‖S‖ ≤ σ) (m : ℝ)
    (hm : ∫ x, Metric.infDist x J ∂(AdversarialBco.Gauss.cloud b S) ≤ m) (Y : ℝ) (hY : 1 ≤ Y) :
    ∫ x, Metric.infDist x J ^ 2 ∂(AdversarialBco.Gauss.cloud b S) ≤
      2 * (m + Real.pi * σ * Y) * m + Real.pi ^ 2 * σ ^ 2 / (4 * Y ^ 2) := by
  set δ := fun (x : EuclideanSpace ℝ (Fin d)) => Metric.infDist x J
  set ν := AdversarialBco.Gauss.cloud b S
  set c := (2 : ℝ) / (Real.pi ^ 2)
  set s := Real.pi * σ / 2
  set r0 := Real.pi * σ * Y
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hY_nonneg : 0 ≤ Y := by linarith
  have hs_pos : 0 < s := by positivity
  have hr0_nonneg : 0 ≤ r0 := by positivity
  have hδ_lip : LipschitzWith (1 : NNReal) δ := Metric.lipschitz_infDist_pt J
  have hδ_nonneg : ∀ x, 0 ≤ δ x := fun x => Metric.infDist_nonneg
  have hδ_meas : Measurable δ := (Metric.continuous_infDist_pt J).measurable
  have h_gauss := AdversarialBco.Gauss.gaussConcAt (k := d) (d := d) (b := b) (S := S) (F := δ) (L := 1) hδ_lip
  rcases h_gauss with ⟨h_int, h_tail_gauss⟩
  have h_tail : ∀ r, 0 ≤ r → ν.real {x | m + r ≤ δ x} ≤ Real.exp (-r ^ 2 / (2 * s ^ 2)) := by
    intro r hr
    by_cases hS_norm_pos : 0 < ‖S‖
    · -- case ‖S‖ > 0
      have h_int_le_m : (∫ x, δ x ∂ν) ≤ m := hm
      have h_set_subset : {x | m + r ≤ δ x} ⊆ {x | (∫ x, δ x ∂ν) + r ≤ δ x} := by
        intro x hx
        have hx' : m + r ≤ δ x := hx
        have hsum : (∫ x, δ x ∂ν) + r ≤ m + r := by
          linarith
        exact le_trans hsum hx'
      have h_measure_le : ν.real {x | m + r ≤ δ x} ≤ ν.real {x | (∫ x, δ x ∂ν) + r ≤ δ x} :=
        measureReal_mono h_set_subset
      have h_tail_bound : ν.real {x | (∫ x, δ x ∂ν) + r ≤ δ x} ≤ Real.exp (-(c * r ^ 2) / ((1 : ℝ) * ‖S‖) ^ 2) :=
        h_tail_gauss r hr
      have h_exp_le : Real.exp (-(c * r ^ 2) / ((1 : ℝ) * ‖S‖) ^ 2) ≤ Real.exp (-r ^ 2 / (2 * s ^ 2)) := by
        rw [Real.exp_le_exp]
        have hS_norm_sq_pos : 0 < ‖S‖ ^ 2 := by positivity
        by_cases hr_zero : r = 0
        · subst hr_zero; simp
        · have hr_sq_pos : 0 < r ^ 2 := by positivity
          have h_ineq : ‖S‖ ^ 2 ≤ c * (2 * s ^ 2) := by
            dsimp [c, s]
            field_simp
            nlinarith
          have h_main : r ^ 2 * ‖S‖ ^ 2 ≤ c * r ^ 2 * (2 * s ^ 2) := by
            nlinarith
          field_simp [hS_norm_sq_pos.ne', hr_sq_pos.ne']
          nlinarith
      linarith
    · -- case ‖S‖ = 0
      have h_norm_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
      have hS_zero : S = 0 := norm_eq_zero.mp (by linarith)
      have hν_dirac : ν = Measure.dirac b := by
        dsimp [ν, AdversarialBco.Gauss.cloud]
        rw [hS_zero]
        have h : (fun (g : EuclideanSpace ℝ (Fin d)) => b + (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g) = fun _ => b := by
          ext g; simp
        rw [h]
        rw [Measure.map_const]
        have hprob : (stdGaussian (EuclideanSpace ℝ (Fin d))) Set.univ = 1 := by
          have hprob' : IsProbabilityMeasure (stdGaussian (EuclideanSpace ℝ (Fin d))) := by infer_instance
          exact measure_univ
        simp [hprob]
      rw [hν_dirac]
      by_cases hr_zero : r = 0
      · subst hr_zero
        have h_exp0 : Real.exp (-0 ^ 2 / (2 * s ^ 2)) = 1 := by simp
        rw [h_exp0]
        exact measureReal_le_one
      · have hr_pos : 0 < r := by
          by_contra! h
          have : r = 0 := by linarith
          exact hr_zero this
        have h_not_mem : b ∉ {x | m + r ≤ δ x} := by
          intro hb
          have hb' : m + r ≤ δ b := hb
          have h_int_val : (∫ x, δ x ∂ν) = δ b := by
            rw [hν_dirac]
            simp
          have hδb_le_m : δ b ≤ m := by
            rw [← h_int_val]
            exact hm
          linarith
        have h_measure_zero : (Measure.dirac b).real {x | m + r ≤ δ x} = 0 := by
          simp [h_not_mem]
        rw [h_measure_zero]
        positivity
  have h_result := AdversarialBco.integral_sq_le_of_tail ν δ hδ_meas hδ_nonneg h_int m s r0 hm hs_pos hr0_nonneg h_tail
  have h_final : 2 * (m + r0) * m + 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) ≤
      2 * (m + Real.pi * σ * Y) * m + Real.pi ^ 2 * σ ^ 2 / (4 * Y ^ 2) := by
    have h_exp_bound : Real.exp (-(2 * Y ^ 2)) ≤ 1 / (2 * Y ^ 2) := by
      have h_add_one : 2 * Y ^ 2 + 1 ≤ Real.exp (2 * Y ^ 2) := Real.add_one_le_exp (2 * Y ^ 2)
      have h_pos : 0 < 2 * Y ^ 2 := by positivity
      have h_pos' : 0 < 2 * Y ^ 2 + 1 := by positivity
      have h_exp_pos : 0 < Real.exp (2 * Y ^ 2) := Real.exp_pos (2 * Y ^ 2)
      have h_inv1 : (Real.exp (2 * Y ^ 2))⁻¹ ≤ (2 * Y ^ 2 + 1)⁻¹ := by
        rw [← one_div, ← one_div]
        exact (one_div_le_one_div h_exp_pos h_pos').mpr (by linarith)
      have h_inv2 : (2 * Y ^ 2 + 1)⁻¹ ≤ (2 * Y ^ 2)⁻¹ := by
        rw [← one_div, ← one_div]
        exact (one_div_le_one_div h_pos' h_pos).mpr (by linarith)
      calc
        Real.exp (-(2 * Y ^ 2)) = (Real.exp (2 * Y ^ 2))⁻¹ := by rw [Real.exp_neg]
        _ ≤ (2 * Y ^ 2 + 1)⁻¹ := h_inv1
        _ ≤ (2 * Y ^ 2)⁻¹ := h_inv2
        _ = 1 / (2 * Y ^ 2) := by ring
    have h_pi_sq_pos : 0 < Real.pi ^ 2 := by positivity
    have h_sigma_sq_pos : 0 < σ ^ 2 := by positivity
    have h_Y_sq_pos : 0 < Y ^ 2 := by positivity
    have h_nonneg_m : 0 ≤ m := by
      have h_int_nonneg : 0 ≤ ∫ x, δ x ∂ν := integral_nonneg hδ_nonneg
      linarith
    have h_coeff : 2 * s ^ 2 = Real.pi ^ 2 * σ ^ 2 / 2 := by
      dsimp [s]; ring
    have h_exp_arg : r0 ^ 2 / (2 * s ^ 2) = 2 * Y ^ 2 := by
      dsimp [r0, s]
      field_simp [hπ_pos.ne', hσ.ne']
    have h_exp_arg' : -r0 ^ 2 / (2 * s ^ 2) = -(2 * Y ^ 2) := by
      rw [show -r0 ^ 2 / (2 * s ^ 2) = -(r0 ^ 2 / (2 * s ^ 2)) by ring, h_exp_arg]
    calc
      2 * (m + r0) * m + 2 * s ^ 2 * Real.exp (-r0 ^ 2 / (2 * s ^ 2))
          = 2 * (m + r0) * m + (Real.pi ^ 2 * σ ^ 2 / 2) * Real.exp (-r0 ^ 2 / (2 * s ^ 2)) := by rw [h_coeff]
      _ = 2 * (m + r0) * m + (Real.pi ^ 2 * σ ^ 2 / 2) * Real.exp (-(2 * Y ^ 2)) := by rw [h_exp_arg']
      _ = 2 * (m + Real.pi * σ * Y) * m + (Real.pi ^ 2 * σ ^ 2 / 2) * Real.exp (-(2 * Y ^ 2)) := by dsimp [r0]
      _ ≤ 2 * (m + Real.pi * σ * Y) * m + (Real.pi ^ 2 * σ ^ 2 / 2) * (1 / (2 * Y ^ 2)) := by
        nlinarith
      _ = 2 * (m + Real.pi * σ * Y) * m + Real.pi ^ 2 * σ ^ 2 / (4 * Y ^ 2) := by ring
  linarith

theorem AdversarialBco.Body.tr_mean_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Ψ δ : Ω → ℝ) (hΨ : Integrable Ψ ν) (hδ : Integrable δ ν) (A c0 e u : ℝ) (hA : 0 < A)
    (hlow : ∀ x, c0 + A * δ x - e ≤ Ψ x) (hup : ∫ x, Ψ x ∂ν ≤ c0 + e + u) :
    ∫ x, δ x ∂ν ≤ (u + 2 * e) / A := by
  have h_int : (∫ x, (c0 + A * δ x - e) ∂ν) ≤ (∫ x, Ψ x ∂ν) := by
    refine MeasureTheory.integral_mono ?_ ?_ ?_
    · have h1 : Integrable (fun x => A * δ x) ν := hδ.const_mul A
      have h2 : Integrable (fun _ => c0) ν := integrable_const c0
      have h3 : Integrable (fun _ => e) ν := integrable_const e
      convert (h1.add h2).sub h3 using 1
      ext x; simp [add_comm]
    · exact hΨ
    · exact hlow
  have h_sum : (∫ x, (c0 + A * δ x - e) ∂ν) = c0 + A * (∫ x, δ x ∂ν) - e := by
    have h1 : Integrable (fun x => A * δ x) ν := hδ.const_mul A
    have h2 : Integrable (fun _ => c0) ν := integrable_const c0
    have h3 : Integrable (fun _ => e) ν := integrable_const e
    have h_sum' : Integrable (fun x => c0 + A * δ x) ν := h2.add h1
    calc
      (∫ x, (c0 + A * δ x - e) ∂ν) = (∫ x, (c0 + A * δ x) ∂ν) - (∫ x, e ∂ν) := by
        rw [integral_sub h_sum' h3]
      _ = ((∫ x, c0 ∂ν) + (∫ x, A * δ x ∂ν)) - (∫ x, e ∂ν) := by
        rw [integral_add h2 h1]
      _ = (c0 + A * (∫ x, δ x ∂ν)) - e := by
        simp [integral_const, integral_const_mul]
      _ = c0 + A * (∫ x, δ x ∂ν) - e := by ring
  have h_ineq : c0 + A * (∫ x, δ x ∂ν) - e ≤ c0 + e + u := by
    linarith
  have h_final : A * (∫ x, δ x ∂ν) ≤ u + 2 * e := by
    linarith
  have h_eq : (∫ x, δ x ∂ν) = (A * (∫ x, δ x ∂ν)) / A := by
    field_simp [ne_of_gt hA]
  rw [h_eq]
  exact div_le_div_of_nonneg_right h_final (by linarith)

/-! ## Batch b14: arithmetic -/

theorem AdversarialBco.Body.tr_regret (A G0 q h ε fb Fb I1 I2 Fs : ℝ) (hf1 : fb ≤ Fb + ε) (hf2 : Fb ≤ I2)
    (hf3 : I2 ≤ Fs + h / 16) (hf4 : Fs ≤ A + ε) (hf5 : I1 ≤ I2 + ε) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hqh : q * h = G0 / 4) (hε : 0 ≤ ε) :
    (1 - q) * A + q / 2 * fb + q / 2 * I1 - (A - G0) ≤ 65 / 64 * G0 + ε := by
  have hq02 : 0 ≤ q / 2 := by linarith
  have h_fb_minus_A : fb - A ≤ h / 16 + 2 * ε := by
    linarith
  have h_I1_minus_A : I1 - A ≤ h / 16 + 2 * ε := by
    linarith
  have h1 : q / 2 * (fb - A) ≤ q / 2 * (h / 16 + 2 * ε) :=
    mul_le_mul_of_nonneg_left h_fb_minus_A hq02
  have h2 : q / 2 * (I1 - A) ≤ q / 2 * (h / 16 + 2 * ε) :=
    mul_le_mul_of_nonneg_left h_I1_minus_A hq02
  have hsum : q / 2 * (fb - A) + q / 2 * (I1 - A) ≤ q * (h / 16 + 2 * ε) := by
    linarith
  have h_main : (1 - q) * A + q / 2 * fb + q / 2 * I1 - (A - G0) ≤ G0 + q * (h / 16 + 2 * ε) := by
    nlinarith
  have h_qh : q * (h / 16 + 2 * ε) = G0 / 64 + 2 * q * ε := by
    nlinarith
  have h_qε : 2 * q * ε ≤ ε := by
    nlinarith
  nlinarith

theorem AdversarialBco.Body.tr_choice (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 1 ≤ Q ∧ 25600 * K * (176 + 8 * Real.log (257 * Q ^ 2)) ≤ Q := by
  set t := (2 : ℝ)^23 * K with ht
  have ht_pos : 0 < t := by
    have h2 : 0 < (2 : ℝ)^23 := by norm_num
    have hKpos : 0 < K := by linarith
    exact mul_pos h2 hKpos
  have hlog257 : Real.log (257 : ℝ) ≤ 256 := by
    have hpos : 0 < (257 : ℝ) := by norm_num
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
  set Q := t ^ 2 with hQ
  have hQpos : 0 < Q := pow_pos ht_pos 2
  have hQ_ge_one : 1 ≤ Q := by
    have ht_ge_one : 1 ≤ t := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ)^23 := by norm_num
      nlinarith
    nlinarith
  refine ⟨Q, hQ_ge_one, ?_⟩
  rw [hQ]
  have hlog_bound : Real.log (257 * (t ^ 2) ^ 2) ≤ 256 + 4 * (t - 1) := by
    have hpos257 : (257 : ℝ) ≠ 0 := by norm_num
    have hpos_t4 : (t ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero 2 ht_pos.ne.symm)
    calc
      Real.log (257 * (t ^ 2) ^ 2) = Real.log (257 : ℝ) + Real.log ((t ^ 2) ^ 2) := by
        rw [Real.log_mul hpos257 hpos_t4]
      _ = Real.log (257 : ℝ) + Real.log (t ^ 4) := by ring_nf
      _ = Real.log (257 : ℝ) + 4 * Real.log t := by
        rw [Real.log_pow, Nat.cast_ofNat]
      _ ≤ 256 + 4 * (t - 1) := by nlinarith
  have h_arith : 25600 * K * (176 + 8 * Real.log (257 * (t ^ 2) ^ 2)) ≤ t ^ 2 := by
    have h_mid : 176 + 8 * Real.log (257 * (t ^ 2) ^ 2) ≤ 2192 + 32 * t := by
      nlinarith
    have h_final : 25600 * K * (2192 + 32 * t) ≤ t ^ 2 := by
      dsimp [t]
      nlinarith
    nlinarith
  exact h_arith

theorem AdversarialBco.Body.tr_log_bound (Q N : ℝ) (hQ : 1 ≤ Q) (hN : 4 ≤ N) :
    72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) ≤ (176 + 8 * Real.log (257 * Q ^ 2)) * Real.log N ∧
      1 ≤ Real.log N := by
  have hNpos : 0 < N := by linarith
  have hQpos : 0 < Q := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_exp_lt_N : Real.exp 1 < N := by
    have h_exp_lt_three : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have h_one_le_logN : 1 ≤ Real.log N := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ ≤ Real.log N := Real.log_le_log h_exp_pos (by linarith)
  set L := Real.log (257 * Q ^ 2) with hL_def
  set l := Real.log N with hl_def
  have hL_nonneg : 0 ≤ L := by
    rw [hL_def]
    apply Real.log_nonneg
    nlinarith
  have hl_nonneg : 0 ≤ l := by
    rw [hl_def]
    apply Real.log_nonneg
    linarith
  have h_main : 1 + 256 * (Q * N ^ 6) ^ 2 * N ≤ 257 * Q ^ 2 * N ^ 13 := by
    have hQ2 : 1 ≤ Q ^ 2 := by
      simpa using one_le_pow₀ hQ (n := 2)
    have hN13 : 1 ≤ N ^ 13 := by
      simpa using one_le_pow₀ hN1 (n := 13)
    have hprod : 1 ≤ Q ^ 2 * N ^ 13 := by
      nlinarith
    calc
      1 + 256 * (Q * N ^ 6) ^ 2 * N = 1 + 256 * (Q ^ 2 * (N ^ 6) ^ 2) * N := by ring
      _ = 1 + 256 * (Q ^ 2 * N ^ 12) * N := by ring
      _ = 1 + 256 * Q ^ 2 * N ^ 13 := by ring
      _ ≤ (Q ^ 2 * N ^ 13) + 256 * Q ^ 2 * N ^ 13 := by nlinarith
      _ = 257 * Q ^ 2 * N ^ 13 := by ring
  have hpos_left : 0 < 1 + 256 * (Q * N ^ 6) ^ 2 * N := by nlinarith
  have hpos_right : 0 < 257 * Q ^ 2 * N ^ 13 := by
    have hQ2pos : 0 < Q ^ 2 := pow_pos hQpos 2
    have hN13pos : 0 < N ^ 13 := pow_pos hNpos 13
    nlinarith
  have h_log_bound : Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) ≤ L + 13 * l := by
    calc
      Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) ≤ Real.log (257 * Q ^ 2 * N ^ 13) :=
        Real.log_le_log hpos_left h_main
      _ = Real.log ((257 * Q ^ 2) * (N ^ 13)) := by ring
      _ = Real.log (257 * Q ^ 2) + Real.log (N ^ 13) := by
        refine Real.log_mul ?_ ?_
        · nlinarith
        · exact pow_ne_zero 13 hNpos.ne.symm
      _ = L + Real.log (N ^ 13) := by rw [hL_def]
      _ = L + (13 : ℝ) * Real.log N := by rw [Real.log_pow, Nat.cast_ofNat]
      _ = L + 13 * l := by rw [hl_def]
  have h_final : 72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) ≤ (176 + 8 * Real.log (257 * Q ^ 2)) * Real.log N := by
    calc
      72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) ≤ 72 + 8 * (L + 13 * l) := by nlinarith
      _ = 72 + 8 * L + 104 * l := by ring
      _ ≤ 72 * l + 8 * L * l + 104 * l := by
        have h1 : 72 ≤ 72 * l := by nlinarith
        have h2 : 8 * L ≤ 8 * L * l := by nlinarith
        nlinarith
      _ = (176 + 8 * L) * l := by ring
      _ = (176 + 8 * Real.log (257 * Q ^ 2)) * Real.log N := by rw [hL_def, hl_def]
  exact And.intro h_final h_one_le_logN

theorem AdversarialBco.Body.tr_P_ge (Q n d D : ℝ) (hQ : 1 ≤ Q) (hn : 2 ≤ n) (hd : 1 ≤ d) (hD : 2 ≤ D) :
    2 * n ≤ (Q * (n * d * D) ^ 6) ^ 2 ∧ 1 ≤ Q * (n * d * D) ^ 6 ∧ 4 ≤ n * d * D := by
  let N := n * d * D
  have hn0 : 0 ≤ n := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hN_nonneg : 0 ≤ N :=
    mul_nonneg (mul_nonneg hn0 hd0) hD0
  have hN_ge_four : 4 ≤ N := by
    have hdD : 2 ≤ d * D := by
      nlinarith
    nlinarith
  have hN_ge_one : 1 ≤ N := by linarith
  have hN_pow_ge_one : 1 ≤ N ^ 6 :=
    one_le_pow₀ hN_ge_one
  have hN_pow_ge_one' : ∀ k : ℕ, 1 ≤ N ^ k := by
    intro k; exact one_le_pow₀ hN_ge_one
  have hQN_ge_one : 1 ≤ Q * N ^ 6 :=
    one_le_mul_of_one_le_of_one_le hQ hN_pow_ge_one
  have hN_pow_six_ge_N : N ≤ N ^ 6 := by
    calc
      N = N * 1 := by ring
      _ ≤ N * (N ^ 5) := mul_le_mul_of_nonneg_left (hN_pow_ge_one' 5) hN_nonneg
      _ = N ^ 6 := by ring
  have hN_pow_le_QN : N ^ 6 ≤ Q * N ^ 6 := by
    have hNpow_nonneg : 0 ≤ N ^ 6 := pow_nonneg hN_nonneg 6
    nlinarith
  have hN_ge_two_n : 2 * n ≤ N := by
    have hdD_ge_two : 2 ≤ d * D := by
      nlinarith
    nlinarith
  have h_sq_ge : Q * N ^ 6 ≤ (Q * N ^ 6) ^ 2 := by
    have hpos : 0 ≤ Q * N ^ 6 := by
      have hQpos : 0 ≤ Q := by linarith
      have hNpow_nonneg : 0 ≤ N ^ 6 := pow_nonneg hN_nonneg 6
      exact mul_nonneg hQpos hNpow_nonneg
    calc
      Q * N ^ 6 = (Q * N ^ 6) * 1 := by ring
      _ ≤ (Q * N ^ 6) * (Q * N ^ 6) := mul_le_mul_of_nonneg_left hQN_ge_one hpos
      _ = (Q * N ^ 6) ^ 2 := by ring
  have h_main : 2 * n ≤ (Q * N ^ 6) ^ 2 := by
    linarith
  exact ⟨h_main, hQN_ge_one, hN_ge_four⟩

theorem AdversarialBco.Body.tr_Y_big (K Q : ℝ) (hK : 0 ≤ K) (hQ1 : 1 ≤ Q)
    (hQ : 25600 * K * (176 + 8 * Real.log (257 * Q ^ 2)) ≤ Q) (n d D : ℝ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hD : 2 ≤ D) :
    1600 * (8 * K * (72 + 8 * Real.log (1 + 256 * (Q * (n * d * D) ^ 6) ^ 2 * (n * d * D))) * d ^ 2 *
      Real.log (2 * n)) * n ^ 4 * D ^ 2 ≤ Q * (n * d * D) ^ 6 := by
  have hdD : 2 ≤ d * D := by nlinarith
  have hN4 : 4 ≤ n * d * D := by rw [mul_assoc]; nlinarith
  obtain ⟨hT, hl1⟩ := AdversarialBco.Body.tr_log_bound Q (n * d * D) hQ1 hN4
  set N := n * d * D with hN
  set L := Real.log (257 * Q ^ 2) with hL
  set T := 72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) with hTdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hlN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2n : Real.log (2 * n) ≤ 2 * n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2n0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N) := Real.log_nonneg (by
      have : 0 ≤ 256 * (Q * N ^ 6) ^ 2 * N := by positivity
      linarith)
    linarith
  have hC0 : 0 ≤ 176 + 8 * L := by linarith
  have hTN : T ≤ (176 + 8 * L) * N := hT.trans (mul_le_mul_of_nonneg_left hlN hC0)
  have hn0 : 0 < n := by linarith
  have hd0 : 0 < d := by linarith
  have hD0 : 0 < D := by linarith
  have hmono : n ^ 5 * d ^ 2 * D ^ 2 ≤ N ^ 5 := by
    rw [hN, mul_pow, mul_pow]
    have hd2 : d ^ 2 ≤ d ^ 5 := pow_le_pow_right₀ hd (by norm_num)
    have hD2 : D ^ 2 ≤ D ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1 : d ^ 2 * D ^ 2 ≤ d ^ 5 * D ^ 5 := mul_le_mul hd2 hD2 (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (pow_pos hn0 5))
    linarith [h2]
  have hK8 : 0 ≤ 8 * K := by linarith
  calc 1600 * (8 * K * T * d ^ 2 * Real.log (2 * n)) * n ^ 4 * D ^ 2
      ≤ 1600 * (8 * K * ((176 + 8 * L) * N) * d ^ 2 * (2 * n)) * n ^ 4 * D ^ 2 := by
        have h1 : 8 * K * T ≤ 8 * K * ((176 + 8 * L) * N) := mul_le_mul_of_nonneg_left hTN hK8
        have h2 : 8 * K * T * d ^ 2 ≤ 8 * K * ((176 + 8 * L) * N) * d ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h3 : 8 * K * T * d ^ 2 * Real.log (2 * n) ≤ 8 * K * ((176 + 8 * L) * N) * d ^ 2 * (2 * n) :=
          mul_le_mul h2 h2n h2n0 (by have := mul_nonneg hK8 (mul_nonneg hC0 (by linarith : (0:ℝ) ≤ N)); positivity)
        have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1600)
        have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ n ^ 4)
        exact mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = 25600 * K * (176 + 8 * L) * N * (n ^ 5 * d ^ 2 * D ^ 2) := by ring
    _ ≤ 25600 * K * (176 + 8 * L) * N * N ^ 5 := by
        apply mul_le_mul_of_nonneg_left hmono
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 25600) hK) hC0
        exact mul_nonneg this (by linarith)
    _ = 25600 * K * (176 + 8 * L) * N ^ 6 := by ring
    _ ≤ Q * N ^ 6 := mul_le_mul_of_nonneg_right hQ (by positivity)

theorem AdversarialBco.Body.tr_beta (K Q n d D : ℝ) (hK : 0 ≤ K) (hQ : 1 ≤ Q) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hD : 2 ≤ D) :
    (65 / 32) ^ 2 * (8 * K * (72 + 8 * Real.log (1 + 256 * (Q * (n * d * D) ^ 6) ^ 2 * (n * d * D))) * d ^ 2 *
      Real.log (2 * n)) ≤
      34 * K * (176 + 8 * Real.log (257 * Q ^ 2)) * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n) := by
  set N := n * d * D with hN
  have hN4 : 4 ≤ N := by
    dsimp [N]
    calc
      (4 : ℝ) = 2 * 1 * 2 := by norm_num
      _ ≤ n * d * D := by gcongr
  rcases AdversarialBco.Body.tr_log_bound Q N hQ hN4 with ⟨hT, hlogN⟩
  have hlog2n : 0 ≤ Real.log (2 * n) :=
    Real.log_nonneg (by nlinarith : 1 ≤ 2 * n)
  have hlogN_nonneg : 0 ≤ Real.log N := by linarith [hlogN]
  have hL_nonneg : 0 ≤ Real.log (257 * Q ^ 2) :=
    Real.log_nonneg (by nlinarith : 1 ≤ 257 * Q ^ 2)
  have hA : ((65 : ℝ) / 32) ^ 2 * (8 : ℝ) ≤ (34 : ℝ) := by
    nlinarith
  have h_mul : ((65 / 32) ^ 2 * 8) * K * (72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N)) * d ^ 2 * Real.log (2 * n) ≤
      ((65 / 32) ^ 2 * 8) * K * ((176 + 8 * Real.log (257 * Q ^ 2)) * Real.log N) * d ^ 2 * Real.log (2 * n) := by
    gcongr
  calc
    (65 / 32) ^ 2 * (8 * K * (72 + 8 * Real.log (1 + 256 * (Q * (n * d * D) ^ 6) ^ 2 * (n * d * D))) * d ^ 2 * Real.log (2 * n))
        = ((65 / 32) ^ 2 * 8) * K * (72 + 8 * Real.log (1 + 256 * (Q * N ^ 6) ^ 2 * N)) * d ^ 2 * Real.log (2 * n) := by
      dsimp [N]
      ring
    _ ≤ ((65 / 32) ^ 2 * 8) * K * ((176 + 8 * Real.log (257 * Q ^ 2)) * Real.log N) * d ^ 2 * Real.log (2 * n) := h_mul
    _ = ((65 / 32) ^ 2 * 8) * (K * (176 + 8 * Real.log (257 * Q ^ 2)) * d ^ 2 * Real.log N * Real.log (2 * n)) := by ring
    _ ≤ (34 : ℝ) * (K * (176 + 8 * Real.log (257 * Q ^ 2)) * d ^ 2 * Real.log N * Real.log (2 * n)) := by
      have hM : 0 ≤ K * (176 + 8 * Real.log (257 * Q ^ 2)) * d ^ 2 * Real.log N * Real.log (2 * n) := by
        positivity
      nlinarith
    _ = 34 * K * (176 + 8 * Real.log (257 * Q ^ 2)) * d ^ 2 * Real.log N * Real.log (2 * n) := by ring

theorem AdversarialBco.Body.tr_eps (n Θ : ℝ) (hn : 2 ≤ n) (hΘ : 0 ≤ Θ) :
    0 < 1 / (128 * n * (1 + Θ)) ∧ 1 / (128 * n * (1 + Θ)) ≤ 1 / (128 * n) ∧
      Θ * (16 * (1 / (128 * n * (1 + Θ))) ^ 2) ≤ 1 / (4 * n ^ 2) := by
  have hnpos : 0 < n := by linarith
  have hpos : 0 < 1 + Θ := by linarith
  have hpos_denom1 : 0 < 128 * n * (1 + Θ) := by positivity
  have hpos_denom2 : 0 < 128 * n := by positivity
  have h_denom_le : 128 * n ≤ 128 * n * (1 + Θ) := by
    have h1 : 1 ≤ 1 + Θ := by linarith
    nlinarith
  have h_one_div_le : 1 / (128 * n * (1 + Θ)) ≤ 1 / (128 * n) :=
    (one_div_le_one_div_of_le hpos_denom2 h_denom_le)
  have h_pos : 0 < 1 / (128 * n * (1 + Θ)) :=
    div_pos (by norm_num) hpos_denom1
  have h_third : Θ * (16 * (1 / (128 * n * (1 + Θ))) ^ 2) ≤ 1 / (4 * n ^ 2) := by
    have hpos_n : 0 < n := by linarith
    have hpos_1pΘ : 0 < 1 + Θ := by linarith
    have hpos_denom : 0 < 128 * n * (1 + Θ) := by positivity
    have hpos_4n2 : 0 < 4 * n ^ 2 := by positivity
    have h_sq_ne_zero : (128 * n * (1 + Θ)) ^ 2 ≠ 0 := by positivity
    calc
      Θ * (16 * (1 / (128 * n * (1 + Θ))) ^ 2)
          = Θ * (16 * (1 / ((128 * n * (1 + Θ)) ^ 2))) := by
            rw [one_div_pow]
      _ = (Θ * 16) / ((128 * n * (1 + Θ)) ^ 2) := by
            field_simp [h_sq_ne_zero]
      _ = 16 * Θ / ((128 * n * (1 + Θ)) ^ 2) := by ring
      _ ≤ 16 * (1 + Θ) / ((128 * n * (1 + Θ)) ^ 2) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith
      _ = 16 / ((128 * n) ^ 2 * (1 + Θ)) := by
            field_simp
      _ ≤ 16 / ((128 * n) ^ 2) := by
        refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
        have h1 : 1 ≤ 1 + Θ := by linarith
        nlinarith
      _ = (16 / ((128 : ℝ) ^ 2)) * (1 / (n ^ 2)) := by
            field_simp
      _ ≤ (1 / 4) * (1 / (n ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        norm_num
      _ = 1 / (4 * n ^ 2) := by
            field_simp
  exact And.intro h_pos (And.intro h_one_div_le h_third)

theorem AdversarialBco.Body.tr_m_bound (n P h ε : ℝ) (hn : 2 ≤ n) (hP : 2 * n ≤ P) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (128 * n)) :
    0 ≤ (h / 16 + 2 * ε) / (P - n) ∧ (h / 16 + 2 * ε) / (P - n) ≤ 1 / P ∧ 1 / P ≤ 1 := by
  have hnpos : 0 < n := by linarith
  have hPpos : 0 < P := by linarith
  have hP_sub_n_pos : 0 < P - n := by linarith
  have hnum_nonneg : 0 ≤ h / 16 + 2 * ε := by
    positivity
  have h1 : 0 ≤ (h / 16 + 2 * ε) / (P - n) :=
    div_nonneg hnum_nonneg (by linarith)
  have h3 : 1 / P ≤ 1 :=
    (div_le_one hPpos).mpr (by linarith)
  have hnum_bound : h / 16 + 2 * ε ≤ 1/2 := by
    have hh' : h / 16 ≤ 1/16 := by linarith
    have hε_bound : ε ≤ 1/256 := by
      have hpos : 0 < 128 * n := by positivity
      have hpos256 : (0 : ℝ) < 256 := by norm_num
      have hdiv : 1 / (128 * n) ≤ 1 / 256 := by
        rw [one_div_le_one_div hpos hpos256]
        nlinarith
      linarith
    have h2ε : 2 * ε ≤ 1/128 := by linarith
    linarith
  have h_denom_bound : P / 2 ≤ P - n := by linarith
  have hP_half_pos : 0 < P / 2 := by linarith
  have h2 : (h / 16 + 2 * ε) / (P - n) ≤ 1 / P := by
    have h_step1 : (h / 16 + 2 * ε) / (P - n) ≤ (1/2) / (P - n) :=
      div_le_div_of_nonneg_right hnum_bound (by linarith)
    have h_step2 : (1/2) / (P - n) ≤ (1/2) / (P / 2) := by
      have h_one_div : 1 / (P - n) ≤ 1 / (P / 2) := by
        rw [one_div_le_one_div hP_sub_n_pos hP_half_pos]
        exact h_denom_bound
      calc
        (1/2) / (P - n) = (1/2) * (1 / (P - n)) := by ring
        _ ≤ (1/2) * (1 / (P / 2)) := mul_le_mul_of_nonneg_left h_one_div (by norm_num)
        _ = (1/2) / (P / 2) := by ring
    have h_step3 : (1/2) / (P / 2) = 1 / P := by
      field_simp [hPpos.ne.symm]
    calc
      (h / 16 + 2 * ε) / (P - n) ≤ (1/2) / (P - n) := h_step1
      _ ≤ (1/2) / (P / 2) := h_step2
      _ = 1 / P := h_step3
  exact And.intro h1 (And.intro h2 h3)

theorem AdversarialBco.Body.tr_S_bound (s D m I δb : ℝ) (hD : 2 ≤ D) (hm : m ≤ 1) (hI : I ≤ m) (hδb : δb ≤ m)
    (h : Real.sqrt (2 / Real.pi) * s ≤ I + D + δb) : s ≤ 4 * D := by
  have hsum : I + D + δb ≤ 2 + D := by
    have hIm : I + δb ≤ 2 * m := by nlinarith
    nlinarith
  have hsqrt : (1/2 : ℝ) ≤ Real.sqrt (2 / Real.pi) := by
    have hsq : (1/2 : ℝ)^2 ≤ 2 / Real.pi := by
      have h : (1/2 : ℝ)^2 = (1/4 : ℝ) := by norm_num
      rw [h]
      field_simp [Real.pi_pos.ne.symm]
      linarith [Real.pi_le_four]
    calc
      (1/2 : ℝ) = Real.sqrt ((1/2 : ℝ)^2) := by norm_num
      _ ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_le_sqrt hsq
  by_cases hs : s ≤ 0
  · nlinarith
  · have hs' : 0 ≤ s := by linarith
    have h1 : (1/2 : ℝ) * s ≤ Real.sqrt (2 / Real.pi) * s :=
      mul_le_mul_of_nonneg_right hsqrt hs'
    have h2 : (1/2 : ℝ) * s ≤ I + D + δb := by nlinarith
    have h3 : (1/2 : ℝ) * s ≤ 2 + D := by nlinarith
    nlinarith

theorem AdversarialBco.Body.tr_r_bound (n d D P h s G0 : ℝ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hP : n ≤ P) (hs0 : 0 ≤ s)
    (hs : s ≤ 4 * D) (hG0 : 1 / n < G0) (hh : G0 / 2 ≤ h) :
    0 ≤ (n + P) * s * 16 * d / h ∧ (n + P) * s * 16 * d / h ≤ 256 * P * (n * d * D) := by
  have hn_pos : 0 < n := by linarith
  have hP_nonneg : 0 ≤ P := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hG0_pos : 0 < G0 := by
    have : 0 < 1 / n := div_pos (by norm_num) hn_pos
    linarith
  have hh_pos : 0 < h := by
    have : 0 < G0 / 2 := div_pos hG0_pos (by norm_num)
    linarith
  have h_one_lt_two_nh : 1 < 2 * n * h := by
    have h1 : 1 < n * G0 := by
      calc
        1 = (1 / n) * n := by field_simp [hn_pos.ne.symm]
        _ < G0 * n := mul_lt_mul_of_pos_right hG0 hn_pos
        _ = n * G0 := mul_comm _ _
    have hG0_le_2h : G0 ≤ 2 * h := by linarith
    have h2 : n * G0 ≤ 2 * n * h := by nlinarith
    linarith
  have h_nonneg : 0 ≤ (n + P) * s * 16 * d / h := by
    have h_num_nonneg : 0 ≤ (n + P) * s * 16 * d := by
      have hnP : 0 ≤ n + P := by nlinarith
      have h1 : 0 ≤ (n + P) * s := mul_nonneg hnP hs0
      have h2 : 0 ≤ ((n + P) * s) * 16 := mul_nonneg h1 (by norm_num)
      exact mul_nonneg h2 hd_nonneg
    exact div_nonneg h_num_nonneg (by linarith)
  have h_upper : (n + P) * s * 16 * d / h ≤ 256 * P * (n * d * D) := by
    rw [div_le_iff₀ hh_pos]
    have hD_nonneg : 0 ≤ D := by nlinarith
    have h_nP_le : n + P ≤ 2 * P := by nlinarith
    have h_2P_nonneg : 0 ≤ 2 * P := by nlinarith
    have h_4D_nonneg : 0 ≤ 4 * D := by nlinarith
    have h_prod_le : (n + P) * s ≤ (2 * P) * (4 * D) :=
      mul_le_mul h_nP_le hs hs0 h_2P_nonneg
    have h_rest_nonneg : 0 ≤ 16 * d := by nlinarith
    have h1 : (n + P) * s * 16 * d ≤ 2 * P * (4 * D) * 16 * d := by
      nlinarith
    have h_eq : 2 * P * (4 * D) * 16 * d = 128 * P * d * D := by ring
    have h_factor : 0 ≤ P * d * D := by
      have h1 : 0 ≤ P * d := mul_nonneg hP_nonneg hd_nonneg
      exact mul_nonneg h1 hD_nonneg
    have h_two_nh_ge_one : 1 ≤ 2 * n * h := by linarith
    have h2 : 128 * P * d * D ≤ 256 * P * n * d * D * h := by
      calc
        128 * P * d * D = 128 * (P * d * D) := by ring
        _ ≤ 128 * (P * d * D) * (2 * n * h) := by
          have hX : 0 ≤ 128 * (P * d * D) := by nlinarith
          nlinarith
        _ = 256 * P * n * d * D * h := by ring
    nlinarith
  exact And.intro h_nonneg h_upper

theorem AdversarialBco.Body.tr_dsq_arith (m Y D Ecl Ep δb q : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ 1 / Y ^ 2) (hY : 1 ≤ Y)
    (hD : 2 ≤ D) (hEcl0 : 0 ≤ Ecl)
    (hEcl : Ecl ≤ 2 * (m + Real.pi * (4 * D) * Y) * m + Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y ^ 2))
    (hδb0 : 0 ≤ δb) (hδb : δb ≤ m) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hEp : Ep ≤ q / 2 * δb ^ 2 + q / 2 * Ecl) :
    Ep ≤ 25 * D ^ 2 / Y := by
  have hYpos : 0 < Y := by linarith
  have hYsq_pos : 0 < Y ^ 2 := by nlinarith
  have hDpos : 0 < D := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_lt_315 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi_sq_lt_10 : Real.pi ^ 2 < 10 := by nlinarith
  have hq2 : q / 2 ≤ 1/4 := by linarith
  have hδb_sq : δb ^ 2 ≤ m ^ 2 := by nlinarith
  have hEp_bound : Ep ≤ (1/4) * m ^ 2 + (1/4) * Ecl := by nlinarith
  have hy_cube_pos : 0 < Y ^ 3 := by nlinarith
  have hy3_le : 1 / Y ^ 3 ≤ 1 := by
    have h : 1 / Y ^ 3 ≤ 1 / 1 := by
      refine ((one_div_le_one_div hy_cube_pos (by norm_num)).mpr ?_)
      nlinarith
    simpa using h
  have hy2m : Y ^ 2 * m ≤ 1 := by
    calc
      Y ^ 2 * m ≤ Y ^ 2 * (1 / Y ^ 2) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 1 := by field_simp [hYpos.ne.symm]
  have hgoal : Ep * Y ≤ 25 * D ^ 2 := by
    have h1 : Ep * Y ≤ ((1/4) * m ^ 2 + (1/4) * Ecl) * Y := by nlinarith
    have h2 : ((1/4) * m ^ 2 + (1/4) * Ecl) * Y ≤ 25 * D ^ 2 := by
      have hmY : m ^ 2 * Y ≤ 1 := by
        have hm_sq : m ^ 2 ≤ (1 / Y ^ 2) ^ 2 := by nlinarith
        calc
          m ^ 2 * Y ≤ ((1 / Y ^ 2) ^ 2) * Y := mul_le_mul_of_nonneg_right hm_sq (by linarith)
          _ = 1 / Y ^ 3 := by
            field_simp [hYpos.ne.symm]
          _ ≤ 1 := hy3_le
      have hEclY : Ecl * Y ≤ 2 + 8 * Real.pi * D + 4 * Real.pi ^ 2 * D ^ 2 := by
        have hEcl_mul_Y : Ecl * Y ≤ (2 * (m + Real.pi * (4 * D) * Y) * m + Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y ^ 2)) * Y := by
          nlinarith
        have h_expanded : (2 * (m + Real.pi * (4 * D) * Y) * m + Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y ^ 2)) * Y =
                          2 * m ^ 2 * Y + 8 * Real.pi * D * Y ^ 2 * m + Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y) := by
          field_simp [hYpos.ne.symm]
          ring
        rw [h_expanded] at hEcl_mul_Y
        have h_term1 : 2 * m ^ 2 * Y ≤ 2 := by nlinarith
        have h_term2 : 8 * Real.pi * D * Y ^ 2 * m ≤ 8 * Real.pi * D := by
          have h := mul_le_mul_of_nonneg_right hy2m (by positivity : 0 ≤ 8 * Real.pi * D)
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have h_term3 : Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y) ≤ 4 * Real.pi ^ 2 * D ^ 2 := by
          have h_eq : Real.pi ^ 2 * (4 * D) ^ 2 / (4 * Y) = (4 * Real.pi ^ 2 * D ^ 2) / Y := by ring
          rw [h_eq]
          refine div_le_self ?_ hY
          positivity
        linarith
      nlinarith
    nlinarith
  have hdiv : (Ep * Y) / Y ≤ (25 * D ^ 2) / Y :=
    div_le_div_of_nonneg_right hgoal (by linarith)
  calc
    Ep = (Ep * Y) / Y := by field_simp [hYpos.ne.symm]
    _ ≤ (25 * D ^ 2) / Y := hdiv

theorem AdversarialBco.Body.tr_Ep_small (Θ n D Y Ep : ℝ) (hΘ : 0 ≤ Θ) (hn : 2 ≤ n) (hY : 0 < Y) (hEp0 : 0 ≤ Ep)
    (hEp : Ep ≤ 25 * D ^ 2 / Y) (hbig : 1600 * Θ * n ^ 4 * D ^ 2 ≤ Y) :
    Θ * (16 * n ^ 2 * Ep) ≤ 1 / (4 * n ^ 2) := by
  have hnpos : 0 < n := by linarith
  have hn_sq_pos : 0 < n ^ 2 := pow_pos hnpos 2
  have h16n_sq_nonneg : 0 ≤ 16 * n ^ 2 := by nlinarith
  have h_mul : Θ * Ep ≤ Θ * (25 * D ^ 2 / Y) :=
    mul_le_mul_of_nonneg_left hEp hΘ
  have h_main : Θ * (16 * n ^ 2 * Ep) ≤ Θ * (16 * n ^ 2 * (25 * D ^ 2 / Y)) := by
    calc
      Θ * (16 * n ^ 2 * Ep) = (16 * n ^ 2) * (Θ * Ep) := by ring
      _ ≤ (16 * n ^ 2) * (Θ * (25 * D ^ 2 / Y)) :=
        mul_le_mul_of_nonneg_left h_mul h16n_sq_nonneg
      _ = Θ * (16 * n ^ 2 * (25 * D ^ 2 / Y)) := by ring
  have h_simp : Θ * (16 * n ^ 2 * (25 * D ^ 2 / Y)) = 400 * Θ * n ^ 2 * D ^ 2 / Y := by ring
  have h_target : 400 * Θ * n ^ 2 * D ^ 2 / Y ≤ 1 / (4 * n ^ 2) := by
    have h_denom2 : 0 < 4 * n ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hY h_denom2]
    nlinarith
  calc
    Θ * (16 * n ^ 2 * Ep) ≤ Θ * (16 * n ^ 2 * (25 * D ^ 2 / Y)) := h_main
    _ = 400 * Θ * n ^ 2 * D ^ 2 / Y := h_simp
    _ ≤ 1 / (4 * n ^ 2) := h_target

theorem AdversarialBco.Body.tr_P3 (K X h G0 q s3 EpV : ℝ) (hK : 0 ≤ K) (hX : 0 ≤ X) (hh : 0 < h) (hG0 : 0 < G0)
    (hq : q = G0 / (4 * h)) (hP3 : h * G0 ≤ K * X * s3) (hEp : q / 2 * s3 ≤ EpV) :
    G0 ^ 2 ≤ 8 * K * X * EpV := by
  have hq_nonneg : 0 ≤ q := by
    rw [hq]
    exact div_nonneg (by linarith) (by linarith)
  have hq_div2_nonneg : 0 ≤ q / 2 := div_nonneg hq_nonneg (by norm_num)
  have hKX_nonneg : 0 ≤ K * X := mul_nonneg hK hX
  have h_eq : G0 ^ 2 / 8 = (q / 2) * (h * G0) := by
    rw [hq]
    field_simp [hh.ne.symm]
    ring
  have h_chain : G0 ^ 2 / 8 ≤ K * X * EpV := by
    calc
      G0 ^ 2 / 8 = (q / 2) * (h * G0) := h_eq
      _ ≤ (q / 2) * (K * X * s3) := mul_le_mul_of_nonneg_left hP3 hq_div2_nonneg
      _ = K * X * ((q / 2) * s3) := by ring
      _ ≤ K * X * EpV := mul_le_mul_of_nonneg_left hEp hKX_nonneg
  calc
    G0 ^ 2 = (G0 ^ 2 / 8) * 8 := by field_simp
    _ ≤ (K * X * EpV) * 8 := mul_le_mul_of_nonneg_right h_chain (by norm_num)
    _ = 8 * K * X * EpV := by ring

theorem AdversarialBco.Body.tr_final (n G0 Θ VJ Ep ε reg β : ℝ) (hn : 2 ≤ n) (hG0 : 1 / n < G0) (hΘ : 0 ≤ Θ)
    (hVJ : 0 ≤ VJ) (hmain : G0 ^ 2 ≤ Θ * (2 * VJ + 16 * ε ^ 2 + 16 * n ^ 2 * Ep))
    (hε2 : Θ * (16 * ε ^ 2) ≤ 1 / (4 * n ^ 2)) (hEpb : Θ * (16 * n ^ 2 * Ep) ≤ 1 / (4 * n ^ 2))
    (hreg : reg ≤ 65 / 64 * G0 + ε) (hε : ε ≤ 1 / n) (hβ : (65 / 32) ^ 2 * Θ ≤ β) :
    reg ≤ 1 / n + √(β * VJ) := by
  have hn_pos : 0 < n := by linarith
  have h_one_div_n_pos : 0 < 1 / n := div_pos (by norm_num) hn_pos
  have hG0_nonneg : 0 ≤ G0 := by linarith
  have hG0_sq_gt_one_div_n_sq : (1 / n) ^ 2 < G0 ^ 2 :=
    pow_lt_pow_left₀ hG0 h_one_div_n_pos.le (by norm_num : 2 ≠ 0)
  have h_one_div_n_sq_eq : (1 / n) ^ 2 = 1 / (n ^ 2) := by ring
  have h_one_div_n_sq_lt_G0_sq : 1 / (n ^ 2) < G0 ^ 2 := by
    rw [← h_one_div_n_sq_eq]
    exact hG0_sq_gt_one_div_n_sq
  have h_one_div_two_n_sq_lt_G0_sq_div_two : 1 / (2 * n ^ 2) < G0 ^ 2 / 2 := by
    have h_eq : 1 / (2 * n ^ 2) = (1 / (n ^ 2)) / 2 := by ring
    rw [h_eq]
    linarith
  have h_G0_sq_lt_four_Theta_VJ : G0 ^ 2 < 4 * Θ * VJ := by
    have h_expand : Θ * (2 * VJ + 16 * ε ^ 2 + 16 * n ^ 2 * Ep) = 2 * Θ * VJ + Θ * (16 * ε ^ 2) + Θ * (16 * n ^ 2 * Ep) := by ring
    rw [h_expand] at hmain
    have h_sum : Θ * (16 * ε ^ 2) + Θ * (16 * n ^ 2 * Ep) ≤ 1 / (2 * n ^ 2) := by
      have h_add := add_le_add hε2 hEpb
      have h_eq : (1 / (4 * n ^ 2)) + (1 / (4 * n ^ 2)) = 1 / (2 * n ^ 2) := by ring
      linarith
    have h_G0_sq_le : G0 ^ 2 ≤ 2 * Θ * VJ + 1 / (2 * n ^ 2) := by linarith
    linarith
  have h_G0_sq_le_four_Theta_VJ : G0 ^ 2 ≤ 4 * Θ * VJ := by linarith
  have h_G0_le_sqrt_four : G0 ≤ √(4 * Θ * VJ) :=
    Real.le_sqrt_of_sq_le h_G0_sq_le_four_Theta_VJ
  have h_sqrt_four_Theta_VJ : √(4 * Θ * VJ) = 2 * √(Θ * VJ) := by
    calc
      √(4 * Θ * VJ) = √(4 * (Θ * VJ)) := by ring_nf
      _ = √(4 : ℝ) * √(Θ * VJ) := Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) _
      _ = 2 * √(Θ * VJ) := by norm_num
  have h_G0_le_two_sqrt : G0 ≤ 2 * √(Θ * VJ) := by
    linarith
  have h_65_64_G0_le_65_32_sqrt : (65 / 64 : ℝ) * G0 ≤ (65 / 32 : ℝ) * √(Θ * VJ) := by
    nlinarith
  have h_sqrt_term_eq : (65 / 32 : ℝ) * √(Θ * VJ) = √(((65 / 32 : ℝ) ^ 2) * (Θ * VJ)) := by
    calc
      (65 / 32 : ℝ) * √(Θ * VJ) = √(((65 / 32 : ℝ) ^ 2)) * √(Θ * VJ) := by
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (65 / 32 : ℝ))]
      _ = √(((65 / 32 : ℝ) ^ 2) * (Θ * VJ)) := by
        rw [← Real.sqrt_mul (by norm_num : 0 ≤ ((65 / 32 : ℝ) ^ 2)) _]
  have h_sqrt_term_le : √(((65 / 32 : ℝ) ^ 2) * (Θ * VJ)) ≤ √(β * VJ) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have h_65_64_G0_le_sqrt_beta_VJ : (65 / 64 : ℝ) * G0 ≤ √(β * VJ) := by
    linarith
  have h_reg_le : reg ≤ √(β * VJ) + 1 / n := by
    linarith
  rw [add_comm]
  exact h_reg_le

/-! ## The assembly -/

/-- The inner body of a convex body with diameter at most `D` containing a unit ball. -/
theorem AdversarialBco.Body.tr_inner {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : IsCompact K) (hKv : Convex ℝ K) (c : EuclideanSpace ℝ (Fin d))
    (hc : Metric.closedBall c 1 ⊆ K) (D : ℝ) (hD : Metric.diam K ≤ D) :
    IsCompact {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} ∧ Convex ℝ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} ∧
      c ∈ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} ∧
      (∀ x ∈ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K}, ∀ y ∈ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K},
        dist x y ≤ D) ∧ 2 ≤ D := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hr1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hsub : {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hr0)
  refine ⟨AdversarialBco.isCompact_inner K hKc _ hr0, AdversarialBco.convex_inner K hKv _, ?_, ?_, ?_⟩
  · apply AdversarialBco.closedBall_subset_inner K c hc _ hr0 hr1
    exact Metric.mem_closedBall_self (by linarith)
  · intro x hx y hy
    exact (Metric.dist_le_diam_of_mem hKc.isBounded (hsub hx) (hsub hy)).trans hD
  · exact (AdversarialBco.two_le_diam hd K hKc.isBounded c hc).trans hD

/-- A function continuous on a nonempty compact set has a minimiser there, and its infimum is its value there. -/
theorem AdversarialBco.Body.tr_min {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJc : IsCompact J)
    (hJn : J.Nonempty) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContinuousOn f J) :
    ∃ x ∈ J, (∀ y ∈ J, f x ≤ f y) ∧ sInf (f '' J) = f x := by
  obtain ⟨x, hx, hmin⟩ := hJc.exists_isMinOn hJn hf
  refine ⟨x, hx, fun y hy => hmin hy, ?_⟩
  exact IsLeast.csInf_eq ⟨Set.mem_image_of_mem f hx, by rintro _ ⟨y, hy, rfl⟩; exact hmin hy⟩

theorem AdversarialBco.Body.tr_wsum_le {k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (u v : Fin k → ℝ) (t : ℝ) (h : ∀ c, u c ≤ v c + t) : ∑ c, w c * u c ≤ ∑ c, w c * v c + t := by
  calc ∑ c, w c * u c ≤ ∑ c, w c * (v c + t) := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h c) (hw c)
    _ = ∑ c, w c * v c + t := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]

theorem AdversarialBco.Body.tr_integral_cloud {d : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hΨ : Continuous Ψ) :
    ∫ x, Ψ x ∂(AdversarialBco.Gauss.cloud b S) = ∫ g, Ψ (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  unfold AdversarialBco.Gauss.cloud
  rw [integral_map (by fun_prop) hΨ.aestronglyMeasurable]

theorem AdversarialBco.Body.tr_bdd_integrable {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ν] (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hΨ : Continuous Ψ) (B : ℝ) (hB : ∀ x, |Ψ x| ≤ B) :
    Integrable Ψ ν :=
  Integrable.mono' (integrable_const B) hΨ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

theorem AdversarialBco.Body.tr_integral_le_add {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (u v : EuclideanSpace ℝ (Fin d) → ℝ) (hu : Integrable u ν) (hv : Integrable v ν)
    (e : ℝ) (h : ∀ x, u x ≤ v x + e) : ∫ x, u x ∂ν ≤ ∫ x, v x ∂ν + e := by
  have h1 : ∫ x, u x ∂ν ≤ ∫ x, (v x + e) ∂ν := integral_mono hu (hv.add (integrable_const e)) h
  rwa [integral_add hv (integrable_const e), integral_const, probReal_univ, one_smul] at h1

/-- Integration of a pointwise bound `V ≤ 2 A + c1 + c2 δ2` under a probability measure. -/
theorem AdversarialBco.Body.tr_integral_bound {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (V A δ2 : EuclideanSpace ℝ (Fin d) → ℝ) (c1 c2 : ℝ) (hV : Integrable V ν)
    (hA : Integrable A ν) (hδ : Integrable δ2 ν) (h : ∀ y, V y ≤ 2 * A y + c1 + c2 * δ2 y) :
    ∫ y, V y ∂ν ≤ 2 * ∫ y, A y ∂ν + c1 + c2 * ∫ y, δ2 y ∂ν := by
  have hI1 : Integrable (fun y => 2 * A y + c1) ν := (hA.const_mul 2).add (integrable_const c1)
  have hI2 : Integrable (fun y => c2 * δ2 y) ν := hδ.const_mul c2
  calc ∫ y, V y ∂ν ≤ ∫ y, (2 * A y + c1 + c2 * δ2 y) ∂ν := integral_mono hV (hI1.add hI2) h
    _ = 2 * ∫ y, A y ∂ν + c1 + c2 * ∫ y, δ2 y ∂ν := by
      rw [integral_add hI1 hI2, integral_add (hA.const_mul 2) (integrable_const c1), integral_const_mul,
        integral_const_mul, integral_const, probReal_univ, one_smul]

/-! ## The assembly -/

/-- The transfer half of Proposition 2.2: hypothesis (H)[1/n, CB d^2 log(n d D) log(2n)] on the inner body from
Theorem 3.1 with (3.2) on `ℝ^d`. -/
theorem AdversarialBco.Body.body_H_of_dilReg (hdil : AdversarialBco.Body.DilReg) :
    ∃ CB : ℝ, 1 ≤ CB ∧ ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (AdversarialBco.E d),
    IsCompact K → Convex ℝ K → ∀ c : AdversarialBco.E d, Metric.closedBall c 1 ⊆ K → ∀ D : ℝ, Metric.diam K ≤ D →
      AdversarialBco.HypH {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} n 0 1 (1 / n)
        (CB * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n)) := by
  obtain ⟨K1, hK1, hdil⟩ := hdil
  obtain ⟨Q, hQ1, hQ⟩ := AdversarialBco.Body.tr_choice (max K1 1) (le_max_right _ _)
  have hLQ : 0 ≤ Real.log (257 * Q ^ 2) := Real.log_nonneg (by nlinarith)
  refine ⟨34 * max K1 1 * (176 + 8 * Real.log (257 * Q ^ 2)), by nlinarith [le_max_right K1 1], ?_⟩
  intro d hd n hn Kb hKbc hKbv c hc D hD
  set Kc : ℝ := max K1 1 with hKc_def
  have hKc1 : 1 ≤ Kc := le_max_right _ _
  have hK1c : K1 ≤ Kc := le_max_left _ _
  obtain ⟨hJc, hJv, hcJ, hJD, hD2⟩ := AdversarialBco.Body.tr_inner hd n hn Kb hKbc hKbv c hc D hD
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hYbig := AdversarialBco.Body.tr_Y_big Kc Q (by linarith) hQ1 hQ n d D hn2 hd1 hD2
  have hβ := AdversarialBco.Body.tr_beta Kc Q n d D (by linarith) hQ1 hn2 hd1 hD2
  obtain ⟨hP2n, hY1, hN4⟩ := AdversarialBco.Body.tr_P_ge Q n d D hQ1 hn2 hd1 hD2
  set N : ℝ := (n : ℝ) * d * D with hN_def
  set Y : ℝ := Q * N ^ 6 with hY_def
  set P : ℝ := Y ^ 2 with hP_def
  have hPn : (n : ℝ) ≤ P := by linarith
  have hP0 : 0 ≤ P := by linarith
  set Tb : ℝ := 72 + 8 * Real.log (1 + 256 * P * N) with hTb_def
  have hTb0 : 0 ≤ Tb := by
    have : 0 ≤ Real.log (1 + 256 * P * N) := Real.log_nonneg (by nlinarith)
    linarith
  have hlog2n : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  set Θ : ℝ := 8 * Kc * Tb * (d : ℝ) ^ 2 * Real.log (2 * n) with hΘ_def
  have hΘ0 : 0 ≤ Θ := by positivity
  obtain ⟨hε0, hε1, hε2⟩ := AdversarialBco.Body.tr_eps n Θ hn2 hΘ0
  set ε : ℝ := 1 / (128 * (n : ℝ) * (1 + Θ)) with hε_def
  have hε128 : ε ≤ 1 / n / 128 := by
    have : (1 : ℝ) / n / 128 = 1 / (128 * n) := by ring
    rw [this]; exact hε1
  have hn1 : (0 : ℝ) < 1 / n := by positivity
  unfold AdversarialBco.HypH
  set J : Set (EuclideanSpace ℝ (Fin d)) := {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ Kb} with hJ_def
  intro k w F hw hw1 hF
  -- the family on `J`, its extensions and its minimisers
  have hFc : ∀ i, ConvexOn ℝ J (F i) := fun i => (hF i).1
  have hFl : ∀ i, ∀ y ∈ J, ∀ z ∈ J, |F i y - F i z| ≤ n * dist y z := fun i => (hF i).2.1
  have hF01 : ∀ i, ∀ y ∈ J, F i y ∈ Set.Icc (0 : ℝ) 1 := fun i => (hF i).2.2
  have hF1 : ∀ i, ∀ y ∈ J, |F i y| ≤ 1 := fun i y hy => by
    obtain ⟨h0, h1⟩ := hF01 i y hy
    rw [abs_le]; constructor <;> linarith
  have hJn : J.Nonempty := ⟨c, hcJ⟩
  have hext := fun i => AdversarialBco.Body.tr_ext J hJv hJn (F i) n (hFc i) (hFl i) (hF01 i) P hP0
  have hGc : ∀ i, Continuous (AdversarialBco.lipExt J (F i) n) := fun i => (hext i).1
  have hGJ : ∀ i, ∀ y ∈ J, AdversarialBco.lipExt J (F i) n y = F i y := fun i => (hext i).2.1
  have hFcont : ∀ i, ContinuousOn (F i) J := fun i =>
    (hGc i).continuousOn.congr fun y hy => (hGJ i y hy).symm
  have hGbc : Continuous (fun y => ∑ i, w i * AdversarialBco.lipExt J (F i) n y) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hGc i)
  choose x hxJ hxmin hxinf using fun i => AdversarialBco.Body.tr_min J hJc hJn (F i) (hFcont i)
  have hfbcont : ContinuousOn (fun y => ∑ i, w i * F i y) J :=
    hGbc.continuousOn.congr fun y hy => Finset.sum_congr rfl fun i _ => by rw [hGJ i y hy]
  obtain ⟨bstar, hbJ, hbmin, -⟩ := AdversarialBco.Body.tr_min J hJc hJn _ hfbcont
  beta_reduce at hbmin
  set G0 : ℝ := ∑ i, w i * (F i bstar - F i (x i)) with hG0_def
  have hreg_eq : ∑ i, w i * F i bstar - ∑ i, w i * sInf (F i '' J) = G0 := by
    rw [hG0_def, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hxinf i]; ring
  have hgain0 : ∀ i, 0 ≤ F i bstar - F i (x i) := fun i => sub_nonneg.2 (hxmin i bstar hbJ)
  have hgain1 : ∀ i, F i bstar - F i (x i) ≤ 1 := fun i => by
    have h1 := hF01 i bstar hbJ
    have h2 := hF01 i (x i) (hxJ i)
    simp only [Set.mem_Icc] at h1 h2
    linarith only [h1.1, h1.2, h2.1, h2.2]
  -- small regret: the point mass at `bstar`
  by_cases hsmall : G0 ≤ 1 / n
  · exact AdversarialBco.Body.tr_dirac J k w F bstar hbJ _ _ (hreg_eq.le.trans hsmall)
  push Not at hsmall
  have hG0pos : 0 < G0 := hn1.trans hsmall
  -- smoothing of the penalised extensions, projection
  obtain ⟨F', M, hF'⟩ := AdversarialBco.Body.tr_smooth_family
    (fun i y => AdversarialBco.lipExt J (F i) n y + P * Metric.infDist y J) (Real.toNNReal (n + P))
    (fun i => (hext i).2.2.2) (fun i => (hext i).2.2.1) ε hε0
  obtain ⟨pr, hprc, hprJ, hprd, hprid⟩ := AdversarialBco.Body.exists_proj J hJc hJv hJn
  have hpw : ∀ i y, F i (pr y) + (P - n) * Metric.infDist y J - ε ≤ F' i y ∧
      F' i y ≤ F i (pr y) + (n + P) * Metric.infDist y J + ε ∧
      |F' i y - P * Metric.infDist y J - F i (pr y)| ≤ ε + n * Metric.infDist y J := by
    intro i y
    have h1 := AdversarialBco.Body.ext_bounds J (F i) n P hn0.le (hFl i) y (pr y) (hprJ y) (hprd y)
    have h2 : |F' i y - (AdversarialBco.lipExt J (F i) n y + P * Metric.infDist y J)| ≤ ε := (hF' i).2.2.2.2 y
    rw [abs_le] at h2
    exact ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2], abs_le.2 ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2]⟩⟩
  have hlow : ∀ y, ∑ i, w i * F i bstar + (P - n) * Metric.infDist y J - ε ≤ ∑ i, w i * F' i y := by
    intro y
    have h1 := AdversarialBco.Body.tr_wsum_le w hw hw1 (fun i => F i (pr y)) (fun i => F' i y)
      (-((P - n) * Metric.infDist y J - ε)) (fun i => by linarith only [(hpw i y).1])
    have h2 := hbmin (pr y) (hprJ y)
    beta_reduce at h1
    linarith only [h1, h2]
  have hupp : ∀ y, ∑ i, w i * F i (pr y) ≤ ∑ i, w i * F' i y + ε := by
    intro y
    have hδ : 0 ≤ (P - n) * Metric.infDist y J := mul_nonneg (by linarith only [hPn]) Metric.infDist_nonneg
    have h1 := AdversarialBco.Body.tr_wsum_le w hw hw1 (fun i => F i (pr y)) (fun i => F' i y)
      (-((P - n) * Metric.infDist y J - ε)) (fun i => by linarith only [(hpw i y).1])
    beta_reduce at h1
    linarith only [h1, hδ]
  have hstar : ∑ i, w i * F' i bstar ≤ ∑ i, w i * F i bstar + ε := by
    have h1 := AdversarialBco.Body.tr_wsum_le w hw hw1 (fun i => F' i bstar) (fun i => F i bstar) ε
      (fun i => by
        have h2 := (hpw i bstar).2.1
        rw [hprid bstar hbJ, Metric.infDist_zero_of_mem hbJ] at h2
        linarith only [h2])
    beta_reduce at h1
    exact h1
  have hcoer : ∀ z, (P - n) * ‖z‖ - ((P - n) * (‖c‖ + D) + ε) ≤ ∑ i, w i * F' i z := by
    intro z
    have h1 := AdversarialBco.Body.tr_infDist_ge J c hcJ D (fun y hy => hJD y hy c hcJ) z
    have h3 : 0 ≤ ∑ i, w i * F i bstar := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hF01 i bstar hbJ).1
    linarith only [hlow z, mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hPn), h3]
  have hbstarF : ∀ z, ∑ i, w i * F' i bstar ≤ ∑ i, w i * F' i z + 2 * ε := by
    intro z
    have hδ : 0 ≤ (P - n) * Metric.infDist z J := mul_nonneg (by linarith only [hPn]) Metric.infDist_nonneg
    linarith only [hlow z, hstar, hδ]
  have hgainF : ∀ i, F i bstar - F i (x i) ≤ F' i bstar - F' i (x i) + 2 * ε := by
    intro i
    have h1 := (hpw i bstar).1
    have h2 := (hpw i (x i)).2.1
    rw [hprid bstar hbJ, Metric.infDist_zero_of_mem hbJ] at h1
    rw [hprid (x i) (hxJ i), Metric.infDist_zero_of_mem (hxJ i)] at h2
    linarith only [h1, h2]
  -- Theorem 3.1 with (3.2) for the smoothed family
  obtain ⟨h, b, S, hh1, hh2, hS3, hS4, hP3⟩ := hdil d hd k w F' (Real.toNNReal (n + P)) M (P - n)
    ((P - n) * (‖c‖ + D) + ε) bstar x (fun i => F i bstar - F i (x i)) (2 * ε) G0 1 hw hw1
    (fun i => (hF' i).1) (fun i => (hF' i).2.1) (fun i => (hF' i).2.2.1) (fun i => (hF' i).2.2.2.1)
    (by linarith only [hP2n, hn2]) hcoer hbstarF hgain0 hgainF rfl hG0pos hgain1 (by linarith only [hε0])
    (by linarith only [hε128, hsmall])
  have hh0 : 0 < h := by linarith only [hh1, hG0pos]
  set q : ℝ := G0 / (4 * h) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq12 : q ≤ 1 / 2 := by rw [hq_def, div_le_iff₀ (by positivity)]; linarith only [hh1]
  have hq1 : q ≤ 1 := by linarith only [hq12]
  set cl := AdversarialBco.Gauss.cloud b S with hcl_def
  -- continuity and integrability under the cloud
  have hF'cont : ∀ i, Continuous (F' i) := fun i => (hF' i).2.2.1.continuous
  have hFbc : Continuous (fun y => ∑ i, w i * F' i y) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hF'cont i)
  set V' : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∑ i, w i * (F' i y - ∑ j, w j * F' j y) ^ 2 with hV'_def
  set VJ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∑ i, w i * ((∑ j, w j * F j y) - F i y) ^ 2 with hVJ_def
  have hV'c : Continuous V' :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (((hF'cont i).sub hFbc).pow 2)
  have hV'0 : ∀ y, 0 ≤ V' y := fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hVJ0 : ∀ y, 0 ≤ VJ y := fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  obtain ⟨hFbI, hV'I⟩ := AdversarialBco.Body.tr_integrable_cloud_var b S w F' _ (fun i => (hF' i).2.2.1)
  obtain ⟨hδI, hδ2I⟩ := AdversarialBco.Body.tr_integrable_cloud b S (fun y => Metric.infDist y J) 1
    (Metric.lipschitz_infDist_pt J)
  have hunit : ∀ y ∈ J, |∑ i, w i * F i y| ≤ 1 ∧ |VJ y| ≤ 1 := fun y hy =>
    AdversarialBco.Body.tr_unit_bounds k w hw hw1 (fun i => F i y) (fun i => hF01 i y hy)
  have hfbpr_c : Continuous (fun y => ∑ i, w i * F i (pr y)) := by
    have : (fun y => ∑ i, w i * F i (pr y)) = fun y => ∑ i, w i * AdversarialBco.lipExt J (F i) n (pr y) :=
      funext fun y => Finset.sum_congr rfl fun i _ => by rw [hGJ i _ (hprJ y)]
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hGc i).comp hprc)
  have hfbprI : Integrable (fun y => ∑ i, w i * F i (pr y)) cl :=
    AdversarialBco.Body.tr_bdd_integrable cl _ hfbpr_c 1 (fun y => (hunit (pr y) (hprJ y)).1)
  have hS3' : ∀ z, ∫ y, ∑ i, w i * F' i y ∂cl ≤ ∑ i, w i * F' i z + h / 16 := fun z => by
    rw [hcl_def, AdversarialBco.Body.tr_integral_cloud b S _ hFbc]; exact hS3 z
  have hS4' : ∑ i, w i * F' i b ≤ ∫ y, ∑ i, w i * F' i y ∂cl := by
    rw [hcl_def, AdversarialBco.Body.tr_integral_cloud b S _ hFbc]; exact hS4
  have hP3' : h * G0 ≤ K1 * (1 + AdversarialBco.Body.Tfun ((n + P) * ‖S‖ * 16 * d / h)) ^ 2 * (d : ℝ) ^ 2 *
      Real.log (2 * 1 / G0) * (V' bstar + V' b + ∫ y, V' y ∂cl) := by
    rw [hcl_def, AdversarialBco.Body.tr_integral_cloud b S _ hV'c, ← Real.coe_toNNReal (n + P) (by positivity)]
    exact hP3
  -- the cloud is close to `J`
  have hmI : ∫ y, Metric.infDist y J ∂cl ≤ (h / 16 + 2 * ε) / (P - n) :=
    AdversarialBco.Body.tr_mean_le cl (fun y => ∑ i, w i * F' i y) (fun y => Metric.infDist y J) hFbI hδI
      (P - n) (∑ i, w i * F i bstar) ε (h / 16) (by linarith only [hP2n, hn2]) hlow (by linarith only [hS3' bstar, hstar])
  obtain ⟨hm0, hmP, hP1⟩ := AdversarialBco.Body.tr_m_bound n P h ε hn2 hP2n hh0.le hh2 hε0.le hε1
  set m : ℝ := (h / 16 + 2 * ε) / (P - n) with hm_def
  have hjen := AdversarialBco.Body.tr_jensen_infDist J hJv b S
  have hopn := AdversarialBco.Body.tr_opNorm_bound J pr hprJ hprd D hJD b S
  have hSb : ‖S‖ ≤ 4 * D :=
    AdversarialBco.Body.tr_S_bound ‖S‖ D m _ _ hD2 (hmP.trans hP1) hmI (hjen.trans hmI) hopn
  have hsq := AdversarialBco.Body.tr_cloud_sq J b S (4 * D) (by linarith only [hD2]) hSb m hmI Y hY1
  -- the tail parameter and the logarithm of (3.2)
  obtain ⟨hr0, hr⟩ : 0 ≤ (n + P) * ‖S‖ * 16 * d / h ∧ (n + P) * ‖S‖ * 16 * d / h ≤ 256 * P * N :=
    AdversarialBco.Body.tr_r_bound n d D P h ‖S‖ G0 hn2 hd1 hPn (norm_nonneg _) hSb hsmall hh1
  have hT : (1 + AdversarialBco.Body.Tfun ((n + P) * ‖S‖ * 16 * d / h)) ^ 2 ≤ Tb := by
    refine (AdversarialBco.Body.one_add_Tfun_sq_le _ hr0).trans ?_
    have : Real.log (1 + (n + P) * ‖S‖ * 16 * d / h) ≤ Real.log (1 + 256 * P * N) :=
      Real.log_le_log (by linarith only [hr0]) (by linarith only [hr])
    linarith only [this, hTb_def]
  have hlogG0 : 0 ≤ Real.log (2 * 1 / G0) ∧ Real.log (2 * 1 / G0) ≤ Real.log (2 * n) := by
    have h1 : 1 < G0 * n := by rw [div_lt_iff₀ hn0] at hsmall; linarith only [hsmall]
    constructor
    · apply Real.log_nonneg; rw [le_div_iff₀ hG0pos]; linarith only [hh1, hh2]
    · apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hG0pos]; linarith only [h1]
  -- the diluted law and its image on `J`
  set p : Measure (EuclideanSpace ℝ (Fin d)) := ENNReal.ofReal (1 - q) • Measure.dirac bstar +
    ENNReal.ofReal (q / 2) • Measure.dirac b + ENNReal.ofReal (q / 2) • cl with hp_def
  have hdl : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f cl →
      IsProbabilityMeasure p ∧ Integrable f p ∧
        ∫ y, f y ∂p = (1 - q) * f bstar + q / 2 * f b + q / 2 * ∫ y, f y ∂cl :=
    fun f hf => AdversarialBco.Body.integral_diluted bstar b cl q hq0 hq1 f hf
  haveI hpP : IsProbabilityMeasure p := (hdl 0 (integrable_zero _ _ _)).1
  have hmapF := fun i => AdversarialBco.Body.tr_map_proj p J hJc.isClosed pr hprc hprJ (F i) _ (hGc i)
    (fun y hy => (hGJ i y hy).symm) 1 (hF1 i)
  have hmapM := AdversarialBco.Body.tr_map_proj p J hJc.isClosed pr hprc hprJ (fun y => ∑ i, w i * F i y) _ hGbc
    (fun y hy => Finset.sum_congr rfl fun i _ => by rw [hGJ i y hy]) 1 (fun y hy => (hunit y hy).1)
  have hGVc : Continuous (fun y => ∑ i, w i * ((∑ j, w j * AdversarialBco.lipExt J (F j) n y) -
      AdversarialBco.lipExt J (F i) n y) ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((hGbc.sub (hGc i)).pow 2)
  have hmapV := AdversarialBco.Body.tr_map_proj p J hJc.isClosed pr hprc hprJ VJ _ hGVc
    (fun y hy => by
      have hGJy : ∀ i, AdversarialBco.lipExt J (F i) n y = F i y := fun i => hGJ i y hy
      simp only [hVJ_def, hGJy]) 1 (fun y hy => (hunit y hy).2)
  refine ⟨Measure.map pr p, hmapM.1, hmapM.2.1, fun i => (hmapF i).2.2.1, ?_⟩
  have hrwM : ∫ y, ∑ i, w i * F i y ∂(Measure.map pr p) = ∫ y, ∑ i, w i * F i (pr y) ∂p := hmapM.2.2.2.2
  have hrwV : ∫ y, ∑ i, w i * ((∑ j, w j * F j y) - F i y) ^ 2 ∂(Measure.map pr p) = ∫ y, VJ (pr y) ∂p :=
    hmapV.2.2.2.2
  rw [hrwM, hrwV]
  -- regret
  have hfbdec : ∫ y, ∑ i, w i * F i (pr y) ∂p = (1 - q) * ∑ i, w i * F i bstar +
      q / 2 * ∑ i, w i * F i (pr b) + q / 2 * ∫ y, ∑ i, w i * F i (pr y) ∂cl := by
    have := (hdl _ hfbprI).2.2
    beta_reduce at this
    rw [this, hprid bstar hbJ]
  have hsInf : ∑ i, w i * sInf (F i '' J) = ∑ i, w i * F i bstar - G0 := by linarith only [hreg_eq]
  have hreg := AdversarialBco.Body.tr_regret (∑ i, w i * F i bstar) G0 q h ε (∑ i, w i * F i (pr b))
    (∑ i, w i * F' i b) (∫ y, ∑ i, w i * F i (pr y) ∂cl) (∫ y, ∑ i, w i * F' i y ∂cl)
    (∑ i, w i * F' i bstar) (hupp b) hS4' (hS3' bstar) hstar
    (AdversarialBco.Body.tr_integral_le_add cl _ _ hfbprI hFbI ε hupp) hq0 hq12
    (by rw [hq_def]; field_simp) hε0.le
  -- variance
  have hvarpt : ∀ y, V' y ≤ 2 * VJ (pr y) + 16 * ε ^ 2 + 16 * (n : ℝ) ^ 2 * Metric.infDist y J ^ 2 := by
    intro y
    have h1 : V' y ≤ 2 * VJ (pr y) + 8 * (ε + n * Metric.infDist y J) ^ 2 :=
      AdversarialBco.Body.tr_variance_shift k w hw hw1 (fun i => F' i y) (fun i => F i (pr y))
        (P * Metric.infDist y J) (ε + n * Metric.infDist y J) (fun i => (hpw i y).2.2)
    have h2 : 8 * (ε + n * Metric.infDist y J) ^ 2 ≤ 16 * ε ^ 2 + 16 * (n : ℝ) ^ 2 * Metric.infDist y J ^ 2 := by
      linarith only [sq_nonneg (ε - n * Metric.infDist y J)]
    linarith only [h1, h2]
  obtain ⟨-, hV'p, hV'dec⟩ := hdl V' hV'I
  obtain ⟨-, hδ2p, hδ2dec⟩ := hdl (fun y => Metric.infDist y J ^ 2) hδ2I
  beta_reduce at hδ2dec
  have hVJp : Integrable (fun y => VJ (pr y)) p := hmapV.2.2.2.1
  have hEpV := AdversarialBco.Body.tr_integral_bound p V' (fun y => VJ (pr y)) (fun y => Metric.infDist y J ^ 2)
    (16 * ε ^ 2) (16 * (n : ℝ) ^ 2) hV'p hVJp hδ2p hvarpt
  beta_reduce at hEpV
  have hs3 : 0 ≤ V' bstar + V' b + ∫ y, V' y ∂cl := by
    have := integral_nonneg (μ := cl) (f := V') fun y => hV'0 y
    linarith only [this, hV'0 bstar, hV'0 b]
  have hEp_s3 : q / 2 * (V' bstar + V' b + ∫ y, V' y ∂cl) ≤ ∫ y, V' y ∂p := by
    rw [hV'dec]
    linarith only [mul_le_mul_of_nonneg_right (show q / 2 ≤ 1 - q by linarith only [hq12]) (hV'0 bstar)]
  have hP3'' : h * G0 ≤ Kc * (Tb * (d : ℝ) ^ 2 * Real.log (2 * n)) * (V' bstar + V' b + ∫ y, V' y ∂cl) := by
    refine hP3'.trans ?_
    set T2 := (1 + AdversarialBco.Body.Tfun ((n + P) * ‖S‖ * 16 * d / h)) ^ 2 with hT2
    set L2 := Real.log (2 * 1 / G0) with hL2
    have hA : T2 * (d : ℝ) ^ 2 * L2 ≤ Tb * (d : ℝ) ^ 2 * Real.log (2 * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hT (by positivity)) hlogG0.2 hlogG0.1 (by positivity)
    have hA0 : 0 ≤ T2 * (d : ℝ) ^ 2 * L2 := mul_nonneg (by positivity) hlogG0.1
    calc K1 * T2 * (d : ℝ) ^ 2 * L2 * (V' bstar + V' b + ∫ y, V' y ∂cl)
        = K1 * (T2 * (d : ℝ) ^ 2 * L2) * (V' bstar + V' b + ∫ y, V' y ∂cl) := by ring
      _ ≤ Kc * (Tb * (d : ℝ) ^ 2 * Real.log (2 * n)) * (V' bstar + V' b + ∫ y, V' y ∂cl) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hK1c hA hA0 (by linarith only [hKc1])) hs3
  have hG0sq := AdversarialBco.Body.tr_P3 Kc (Tb * (d : ℝ) ^ 2 * Real.log (2 * n)) h G0 q _ _ (by linarith only [hKc1])
    (by positivity) hh0 hG0pos hq_def hP3'' hEp_s3
  have hΘeq : 8 * Kc * (Tb * (d : ℝ) ^ 2 * Real.log (2 * n)) = Θ := by rw [hΘ_def]; ring
  rw [hΘeq] at hG0sq
  have hmain : G0 ^ 2 ≤ Θ * (2 * ∫ y, VJ (pr y) ∂p + 16 * ε ^ 2 +
      16 * (n : ℝ) ^ 2 * ∫ y, Metric.infDist y J ^ 2 ∂p) :=
    hG0sq.trans (mul_le_mul_of_nonneg_left hEpV hΘ0)
  -- second moment of the distance under the diluted law
  have hEp : ∫ y, Metric.infDist y J ^ 2 ∂p ≤ 25 * D ^ 2 / Y := by
    refine AdversarialBco.Body.tr_dsq_arith m Y D _ _ (Metric.infDist b J) q hm0 hmP hY1 hD2
      (integral_nonneg fun y => sq_nonneg _) hsq Metric.infDist_nonneg (hjen.trans hmI) hq0 hq12 ?_
    rw [hδ2dec, Metric.infDist_zero_of_mem hbJ]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    exact le_rfl
  have hEpb := AdversarialBco.Body.tr_Ep_small Θ n D Y _ hΘ0 hn2 (by linarith only [hY1])
    (integral_nonneg fun y => sq_nonneg _) hEp hYbig
  refine AdversarialBco.Body.tr_final n G0 Θ _ _ ε _ _ hn2 hsmall hΘ0
    (integral_nonneg fun y => hVJ0 _) hmain hε2 hEpb ?_ (by linarith only [hε128, hn1]) hβ
  rw [hfbdec, hsInf]
  exact hreg
