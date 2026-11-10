/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Core
public import AdversarialBco.Body.Cloud
public import AdversarialBco.Body.Interface

@[expose] public section

/-!
# Lemma 3.2 and Theorem 3.1 with (3.2) for a regular family

(S3), the existence of the entropic cloud `ec_min_exists`, `ec_exists`, and `dilReg : DilReg`, the half of
Proposition 2.2 on `ℝ^d`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

/-- (S3): the cost of the cloud above every value of `G` is at most `lam d`. -/
theorem AdversarialBco.Body.ec_S3 {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hGc : ConvexOn ℝ Set.univ G) (L : ℝ≥0) (hGL : LipschitzWith L G) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS1 : ∀ w, ∫ g, G' (b + S g) w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0)
    (hS2 : ∀ v v', ∫ g, ⟪v, g⟫ * G' (b + S g) (S v') ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫)
    (z : EuclideanSpace ℝ (Fin d)) :
    ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ G z + lam * (d : ℝ) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hG'eq : G' = fderiv ℝ G := funext fun x => (hG x).fderiv.symm
  have hG'm : Measurable G' := hG'eq ▸ measurable_fderiv ℝ G
  have hG'b : ∀ x, ‖G' x‖ ≤ L := fun x => by rw [hG'eq]; exact norm_fderiv_le_of_lipschitz ℝ hGL
  have haffm : Measurable fun g : EuclideanSpace ℝ (Fin d) => b + S g :=
    (continuous_const.add S.continuous).measurable
  let H' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun g => (G' (b + S g)).comp S
  have hH'm : Measurable H' :=
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip
      S).continuous.measurable.comp (hG'm.comp haffm)
  have hH'b : ∀ g, ‖H' g‖ ≤ L * ‖S‖ := fun g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hG'b _) (norm_nonneg _))
  have htr : ∫ g, H' g g ∂γ = lam * d := AdversarialBco.Body.integral_fderiv_self H' hH'm (L * ‖S‖) hH'b lam hS2
  have hlip := AdversarialBco.lipschitzWith_comp_affine G L hGL b S
  have iG : Integrable (fun g => G (b + S g)) γ :=
    AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm hlip.continuous.aestronglyMeasurable
      (AdversarialBco.Gauss.abs_le_of_lipschitz hlip)
  have iA : Integrable (fun g => G' (b + S g) (z - b)) γ := by
    refine AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm
      ((hG'm.comp haffm).apply_continuousLinearMap (z - b)).aestronglyMeasurable (A := L * ‖z - b‖) (B := 0)
      fun g => ?_
    rw [zero_mul, add_zero, ← Real.norm_eq_abs]
    exact ((G' (b + S g)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hG'b _) (norm_nonneg _))
  have htr' : ∫ g, G' (b + S g) (S g) ∂γ = lam * d := htr
  have hBm : AEStronglyMeasurable (fun g => G' (b + S g) (S g)) γ :=
    (ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂ (μ := γ) S.continuous.aestronglyMeasurable
      (hG'm.comp haffm).aestronglyMeasurable
  have iB : Integrable (fun g => G' (b + S g) (S g)) γ := by
    refine AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm hBm (A := 0) (B := L * ‖S‖) fun g => ?_
    rw [zero_add, ← Real.norm_eq_abs]
    exact ((H' g).le_opNorm g).trans (mul_le_mul_of_nonneg_right (hH'b g) (norm_nonneg _))
  have hpt : ∀ g, G (b + S g) + G' (b + S g) (z - b) - G' (b + S g) (S g) ≤ G z := fun g => by
    have h1 := AdversarialBco.convexOn_ge_of_hasFDerivAt G (G' (b + S g)) hGc (b + S g) (hG _) z
    have e : z - (b + S g) = (z - b) - S g := by abel
    rw [e, map_sub] at h1
    linarith
  have iGA : Integrable (fun g => G (b + S g) + G' (b + S g) (z - b)) γ := iG.add iA
  have iL : Integrable (fun g => G (b + S g) + G' (b + S g) (z - b) - G' (b + S g) (S g)) γ := iGA.sub iB
  have hint := integral_mono iL (integrable_const (G z)) hpt
  rw [integral_sub iGA iB, integral_add iG iA, hS1, htr', integral_const, probReal_univ, one_smul] at hint
  linarith

namespace AdversarialBco.Body

/-! ## 3. Lemma 3.2: existence of the entropic cloud -/

/-- Existence of a minimiser of the entropic objective `E G(b + S g) - lam log |det S|` over every invertible `S`. -/
theorem ec_min_exists {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hGL : LipschitzWith L G)
    (a a' : ℝ) (ha : 0 < a) (hcoer : ∀ x, a * ‖x‖ - a' ≤ G x) (lam : ℝ) (hlam : 0 < lam) :
    ∃ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
      ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
          ∫ g, G (b' + S' g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let f : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) → ℝ := fun p =>
    ∫ g, G (p.1 + p.2 g) ∂γ -
      lam * Real.log |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|
  let U : Set (EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) :=
    {p | LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0}
  let x0 : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (0, ContinuousLinearMap.id ℝ _)
  have hx0 : x0 ∈ U := by simp [U, x0]
  obtain ⟨M, δ, hδ, hMδ⟩ := entropic_bounded G L hGL a a' ha hcoer lam hlam (f x0)
  have hIc : Continuous fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =>
      ∫ g, G (p.1 + p.2 g) ∂γ := by
    set c := ∫ g, ‖g‖ ∂γ
    have hc : 0 ≤ c := integral_nonneg fun _ => norm_nonneg _
    refine (LipschitzWith.of_dist_le_mul (K := (L * (1 + c)).toNNReal) fun p p' => ?_).continuous
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have h := integral_cloud_lipschitz G L hGL p.1 p'.1 p.2 p'.2
    have h1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
      rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
    have h2 : ‖p.2 - p'.2‖ ≤ dist p p' := by
      rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_right _ _
    calc _ ≤ (L : ℝ) * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖ * c) := h
      _ ≤ L * (dist p p' + dist p p' * c) := by gcongr
      _ = L * (1 + c) * dist p p' := by ring
  have hdc : Continuous fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =>
      LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    continuous_det_clm.comp continuous_snd
  have hfc : ContinuousOn f U := by
    refine hIc.continuousOn.sub (continuousOn_const.mul ?_)
    refine Real.continuousOn_log.comp (continuous_abs.comp hdc).continuousOn fun p hp => ?_
    simpa [U] using hp
  have hK : IsCompact {p | p ∈ U ∧ f p ≤ f x0} := by
    have heq : {p | p ∈ U ∧ f p ≤ f x0} =
        {p | δ ≤ |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|} ∩
          f ⁻¹' Set.Iic (f x0) := by
      ext p
      constructor
      · rintro ⟨hp, hle⟩
        exact ⟨(hMδ p.1 p.2 hp hle).2.2, hle⟩
      · rintro ⟨hp, hle⟩
        refine ⟨fun h0 => ?_, hle⟩
        simp only [Set.mem_ofPred_eq, h0, abs_zero] at hp
        linarith
    have hsub : {p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) |
        δ ≤ |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|} ⊆ U := by
      intro p hp h0
      simp only [Set.mem_ofPred_eq, h0, abs_zero] at hp
      linarith
    have hcl := ContinuousOn.preimage_isClosed_of_isClosed (hfc.mono hsub)
      (isClosed_le continuous_const (continuous_abs.comp hdc)) (isClosed_Iic (a := f x0))
    rw [heq]
    refine Metric.isCompact_of_isClosed_isBounded hcl ((Metric.isBounded_closedBall (x := 0) (r := M)).subset ?_)
    rintro p ⟨hp1, hp2⟩
    obtain ⟨hb, hS, -⟩ := hMδ p.1 p.2 (hsub hp1) hp2
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hb hS
  obtain ⟨p, hpU, hp⟩ := AdversarialBco.exists_min_of_compact_sublevel U f hfc x0 hx0 hK
  exact ⟨p.1, p.2, hpU, fun b' S' h => hp (b', S') h⟩

/-- Lemma 3.2 (stationarity) for a `C^1` Lipschitz coercive reference: (S1) and (S2) in the coordinates of the cloud. -/
theorem ec_exists {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hG'c : Continuous G') (L : ℝ≥0) (hGL : LipschitzWith L G) (a a' : ℝ) (ha : 0 < a)
    (hcoer : ∀ x, a * ‖x‖ - a' ≤ G x) (lam : ℝ) (hlam : 0 < lam) :
    ∃ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
      (∀ w, ∫ g, G' (b + S g) w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0) ∧
      ∀ v v', ∫ g, ⟪v, g⟫ * G' (b + S g) (S v') ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫ := by
  obtain ⟨b, S, hdet, hmin⟩ := ec_min_exists G L hGL a a' ha hcoer lam hlam
  refine ⟨b, S, hdet, fun w => ?_, fun v v' => ?_⟩
  · have := ec_first_order G G' hG hG'c L hGL lam b S hdet hmin w 0
    simpa using this
  · have := ec_first_order G G' hG hG'c L hGL lam b S hdet hmin 0 ((innerSL ℝ v).smulRight v')
    simp only [zero_add, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
      smul_eq_mul] at this
    rw [this]
    congr 1
    rw [ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
    rfl

/-! ## 5. Theorem 3.1 for a regular family, with near-minimisers -/

/-- The arithmetic closing Theorem 3.1 with (3.2). -/
theorem dil_arith (K0 d T ℓ h G0 μS μM Vs Vb EV : ℝ) (hK0 : 0 < K0) (hD : 1 ≤ d ^ 2 * (1 + T) ^ 2) (hℓ : 0 < ℓ)
    (hh : 0 < h) (hVs : 0 ≤ Vs) (hVb : 0 ≤ Vb) (hEV : 0 ≤ EV)
    (hcore : μS * (h ^ 2 / 256) ≤ K0 * d ^ 2 * (1 + T) ^ 2 * (EV + Vb)) (hmv : μM * (h ^ 2 / 32) ≤ Vb + Vs)
    (hG0 : G0 ≤ 2 * ℓ * (h * (μS + μM))) :
    h * G0 ≤ 2 * (256 * K0 + 32) * (1 + T) ^ 2 * d ^ 2 * ℓ * (Vs + Vb + EV) := by
  have e : K0 * d ^ 2 * (1 + T) ^ 2 = K0 * (d ^ 2 * (1 + T) ^ 2) := by ring
  rw [e] at hcore
  rw [show 2 * (256 * K0 + 32) * (1 + T) ^ 2 * d ^ 2 * ℓ * (Vs + Vb + EV) =
    2 * (256 * K0 + 32) * (d ^ 2 * (1 + T) ^ 2) * ℓ * (Vs + Vb + EV) by ring]
  generalize d ^ 2 * (1 + T) ^ 2 = D at hD hcore ⊢
  have h1 : h ^ 2 * (μS + μM) ≤ 256 * (K0 * D * (EV + Vb)) + 32 * (Vb + Vs) := by
    have e2 : h ^ 2 * (μS + μM) = 256 * (μS * (h ^ 2 / 256)) + 32 * (μM * (h ^ 2 / 32)) := by ring
    rw [e2]
    have e3 : K0 * D * (EV + Vb) = K0 * (D * (EV + Vb)) := by ring
    rw [e3]
    linarith
  have h2 : 256 * (K0 * D * (EV + Vb)) + 32 * (Vb + Vs) ≤ (256 * K0 + 32) * D * (Vs + Vb + EV) := by
    nlinarith [mul_nonneg (mul_nonneg hK0.le (by linarith : (0 : ℝ) ≤ D)) hVs,
      mul_nonneg (by linarith : (0 : ℝ) ≤ D) hEV, mul_le_mul_of_nonneg_right hD (add_nonneg hVb hVs)]
  calc h * G0 ≤ h * (2 * ℓ * (h * (μS + μM))) := mul_le_mul_of_nonneg_left hG0 hh.le
    _ = 2 * ℓ * (h ^ 2 * (μS + μM)) := by ring
    _ ≤ 2 * ℓ * ((256 * K0 + 32) * D * (Vs + Vb + EV)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 2 * (256 * K0 + 32) * D * ℓ * (Vs + Vb + EV) := by ring

/-- The weighted mean of a family of `C^2` functions with Lipschitz values and gradients is `C^2`, with the same
bounds on its first and second derivatives. -/
theorem mean_regular {d k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (Lp Mp : ℝ≥0) (hF2 : ∀ c, ContDiff ℝ 2 (F c))
    (hFL : ∀ c, LipschitzWith Lp (F c)) (hF'L : ∀ c, LipschitzWith Mp (fderiv ℝ (F c))) :
    ∃ (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (G'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ z, HasFDerivAt (fun z => ∑ c, w c * F c z) (G' z) z) ∧ (∀ z, HasFDerivAt G' (G'' z) z) ∧
      Continuous G' ∧ LipschitzWith Lp (fun z => ∑ c, w c * F c z) ∧ (∀ z, ‖G' z‖ ≤ Lp) ∧
      ∀ z, ‖G'' z‖ ≤ Mp := by
  have hF'b : ∀ c z, ‖fderiv ℝ (F c) z‖ ≤ Lp := fun c z => norm_fderiv_le_of_lipschitz ℝ (hFL c)
  have hd : ∀ z, HasFDerivAt (fun z => ∑ c, w c • fderiv ℝ (F c) z) (∑ c, w c • fderiv ℝ (fderiv ℝ (F c)) z) z :=
    fun z => HasFDerivAt.fun_sum fun c _ =>
      (((((hF2 c).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z).hasFDerivAt).const_smul
        (w c)
  have hG'L : LipschitzWith Mp (fun z => ∑ c, w c • fderiv ℝ (F c) z) := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ c, (w c • fderiv ℝ (F c) z - w c • fderiv ℝ (F c) z')‖ ≤
          ∑ c, ‖w c • fderiv ℝ (F c) z - w c • fderiv ℝ (F c) z'‖ := norm_sum_le _ _
      _ ≤ ∑ c, w c * (Mp * dist z z') := Finset.sum_le_sum fun c _ => by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hw c), ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left ((hF'L c).dist_le_mul z z') (hw c)
      _ = Mp * dist z z' := by rw [← Finset.sum_mul, hw1, one_mul]
  refine ⟨fun z => ∑ c, w c • fderiv ℝ (F c) z, fun z => fderiv ℝ (fun z => ∑ c, w c • fderiv ℝ (F c) z) z,
    fun z => ?_, fun z => (hd z).differentiableAt.hasFDerivAt, ?_, ?_, fun z => ?_,
    fun z => norm_fderiv_le_of_lipschitz ℝ hG'L⟩
  · exact HasFDerivAt.fun_sum fun c _ => ((((hF2 c).differentiable (by norm_num)) z).hasFDerivAt).const_mul (w c)
  · exact continuous_finsetSum _ fun c _ => ((hF2 c).continuous_fderiv (by norm_num)).const_smul (w c)
  · refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [Real.dist_eq]
    calc |∑ c, w c * F c z - ∑ c, w c * F c z'| = |∑ c, w c * (F c z - F c z')| := by
          simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ c, |w c * (F c z - F c z')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, w c * (Lp * dist z z') := Finset.sum_le_sum fun c _ => by
          rw [abs_mul, abs_of_nonneg (hw c), ← Real.dist_eq]
          exact mul_le_mul_of_nonneg_left ((hFL c).dist_le_mul z z') (hw c)
      _ = Lp * dist z z' := by rw [← Finset.sum_mul, hw1, one_mul]
  · calc ‖∑ c, w c • fderiv ℝ (F c) z‖ ≤ ∑ c, ‖w c • fderiv ℝ (F c) z‖ := norm_sum_le _ _
      _ ≤ ∑ c, w c * Lp := Finset.sum_le_sum fun c _ => by
          rw [norm_smul, Real.norm_of_nonneg (hw c)]
          exact mul_le_mul_of_nonneg_left (hF'b c z) (hw c)
      _ = Lp := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A weighted mean of convex functions with nonnegative weights is convex. -/
theorem convexOn_wsum {d k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ)
    (hFc : ∀ c, ConvexOn ℝ Set.univ (F c)) : ConvexOn ℝ Set.univ (fun z => ∑ c, w c * F c z) := by
  refine ⟨convex_univ, fun z _ z' _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have h1 := (hFc c).2 (Set.mem_univ z) (Set.mem_univ z') hs ht hst
  simp only [smul_eq_mul] at h1
  nlinarith [mul_le_mul_of_nonneg_left h1 (hw c)]

/-- A convex function stays convex after an affine change of variables `g ↦ b + S g`. -/
theorem convexOn_comp_cloud {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun g => F (b + S g)) := by
  refine ⟨convex_univ, fun g _ g' _ s t hs ht hst => ?_⟩
  have e : b + S (s • g + t • g') = s • (b + S g) + t • (b + S g') := by
    rw [map_add, map_smul, map_smul, smul_add, smul_add]
    have hb : b = s • b + t • b := by rw [← add_smul, hst, one_smul]
    nth_rewrite 1 [hb]
    abel
  simp only [e, smul_eq_mul]
  exact hF.2 (Set.mem_univ _) (Set.mem_univ _) hs ht hst

/-- The second derivative in the coordinates `g ↦ b + S g` of the cloud: it exists, is bounded and is nonnegative
on the diagonal when the function is convex. -/
theorem pullback_hess {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (G'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hG : ∀ z, HasFDerivAt G (G' z) z) (hG' : ∀ z, HasFDerivAt G' (G'' z) z) (hGc : ConvexOn ℝ Set.univ G)
    (M : ℝ) (hM : ∀ z, ‖G'' z‖ ≤ M) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ (Gs'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (M' : ℝ),
      (∀ g, HasFDerivAt (fun g => (G' (b + S g)).comp S) (Gs'' g) g) ∧ (∀ g, ‖Gs'' g‖ ≤ M') ∧
      ∀ g v, 0 ≤ Gs'' g v v := by
  let P : (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ℝ).flip S
  have haff : ∀ g, HasFDerivAt (fun g => b + S g) S g := fun g => (S.hasFDerivAt).const_add b
  refine ⟨fun g => P.comp ((G'' (b + S g)).comp S), ‖P‖ * (M * ‖S‖), fun g => ?_, fun g => ?_, fun g v => ?_⟩
  · have h1 := (hG' (b + S g)).comp g (haff g)
    exact P.hasFDerivAt.comp g h1
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))
      (norm_nonneg _))
  · exact AdversarialBco.Body.hess_nonneg_of_convex G G' G'' hG hG' hGc (b + S g) (S v)

/-- Theorem 3.1 with (3.2) for a regular family: the interface `DilReg`. -/
theorem dilReg : DilReg := by
  obtain ⟨K0, hK0, hcore⟩ := core_std
  unfold DilReg
  refine ⟨2 * (256 * K0 + 32), by positivity, ?_⟩
  intro d hd k w F Lp Mp a a' bstar x gain η G0 gmax hw hw1 hF2 hFc hFL hF'L ha hcoer hbstar hg0 hgain hG0
    hG0pos hgmax hη0 hη
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the family and its mean
  have hF' : ∀ c z, HasFDerivAt (F c) (fderiv ℝ (F c) z) z := fun c z =>
    (((hF2 c).differentiable (by norm_num)) z).hasFDerivAt
  have hF'b : ∀ c z, ‖fderiv ℝ (F c) z‖ ≤ Lp := fun c z => norm_fderiv_le_of_lipschitz ℝ (hFL c)
  obtain ⟨G', G'', hG, hG', hG'c, hGL, hG'b, hG''b⟩ := mean_regular w hw hw1 F Lp Mp hF2 hFL hF'L
  have hGc := convexOn_wsum w hw F hFc
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ∑ c, w c * F c z with hG_def
  -- the scale
  have hG0max : G0 ≤ gmax := by
    rw [hG0]
    calc ∑ c, w c * gain c ≤ ∑ c, w c * gmax :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hgmax c) (hw c)
      _ = gmax := by rw [← Finset.sum_mul, hw1, one_mul]
  obtain ⟨i, hi1, hi2⟩ := AdversarialBco.scale_pigeonhole w gain hw hw1 hg0 G0 gmax hG0pos hgmax hG0.symm
  set h := gain i with hh_def
  have hh : 0 < h := by linarith
  have hηh : η ≤ h / 32 := by linarith
  have hlog : 0 < Real.log (2 * gmax / G0) := Real.log_pos (by rw [lt_div_iff₀ hG0pos]; linarith)
  set lam := h / (16 * (d : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  have hlamd : lam * d = h / 16 := by
    rw [hlam_def]; field_simp
  -- the cloud
  obtain ⟨b, S, hdet, hS1, hS2⟩ := ec_exists G G' hG hG'c Lp hGL a a' ha hcoer lam hlam
  have hS3 : ∀ z, ∫ g, G (b + S g) ∂γ ≤ G z + h / 16 := fun z => by
    have := ec_S3 G G' hG hGc Lp hGL lam b S hS1 hS2 z
    rwa [hlamd] at this
  have hS4 : G b ≤ ∫ g, G (b + S g) ∂γ := ec_S4 G hGc Lp hGL b S
  refine ⟨h, b, S, hi1, hgmax i, hS3, hS4, ?_⟩
  -- the family in the coordinates of the cloud
  have haff : ∀ g, HasFDerivAt (fun g => b + S g) S g := fun g => (S.hasFDerivAt).const_add b
  have hFs : ∀ c g, HasFDerivAt (fun g => F c (b + S g)) ((fderiv ℝ (F c) (b + S g)).comp S) g := fun c g =>
    (hF' c (b + S g)).comp g (haff g)
  have hGs : ∀ g, HasFDerivAt (fun g => G (b + S g)) ((G' (b + S g)).comp S) g := fun g => by
    have h1 := (hG (b + S g)).comp g (haff g)
    exact h1
  obtain ⟨Gs'', M', hGs', hGs''b, hGspos⟩ := pullback_hess G G' G'' hG hG' hGc Mp hG''b b S
  have hFsc : ∀ c, ConvexOn ℝ Set.univ (fun g => F c (b + S g)) := fun c => convexOn_comp_cloud (F c) (hFc c) b S
  have hFs'b : ∀ c g, ‖(fderiv ℝ (F c) (b + S g)).comp S‖ ≤ Lp * ‖S‖ := fun c g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hF'b c _) (norm_nonneg _))
  have hGs'b : ∀ g, ‖(G' (b + S g)).comp S‖ ≤ Lp * ‖S‖ := fun g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hG'b _) (norm_nonneg _))
  have hS1' : ∀ v, ∫ g, (G' (b + S g)).comp S v ∂γ = 0 := fun v => hS1 (S v)
  have hS2' : ∀ v v', ∫ g, ⟪v, g⟫ * (G' (b + S g)).comp S v' ∂γ = lam * ⟪v, v'⟫ := fun v v' => hS2 v v'
  have hS4' : (fun g => G (b + S g)) 0 ≤ ∫ g, (fun g => G (b + S g)) g ∂γ := by
    simpa using hS4
  -- the tail parameter
  set T := Tfun (Lp * ‖S‖ * 16 * (d : ℝ) / h) with hT_def
  have hTeq : (Lp : ℝ) * ‖S‖ / lam = Lp * ‖S‖ * 16 * d / h := by
    rw [hlam_def]; field_simp
  have hT0 : 0 ≤ T := by rw [hT_def, Tfun]; positivity
  have htail : 4 * (1 + T) * (Lp * ‖S‖) * Real.exp (T + 1 / 2 - T ^ 2 / 2) ≤ lam / 2 := by
    have := tail_Tfun (Lp * ‖S‖) lam (by positivity) hlam
    rwa [hTeq] at this
  -- good and moved components
  set A := Finset.univ.filter (fun j => h ≤ gain j) with hA_def
  set Sg := A.filter (fun j => -(h / 2) ≤ F j b - F j bstar) with hSg_def
  set Mv := A.filter (fun j => ¬ -(h / 2) ≤ F j b - F j bstar) with hMv_def
  have hsurj : Function.Surjective S := by
    have hu : IsUnit (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
    exact ((Module.End.isUnit_iff _).1 hu).2
  choose y hy using fun c => hsurj (x c - b)
  have hgain' : ∀ c ∈ Sg, (fun g => F c (b + S g)) (y c) ≤ (fun g => F c (b + S g)) 0 - 4 * lam * d :=
    fun c hc => by
    simp only [hSg_def, hA_def, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [hy c, map_zero, add_zero, show b + (x c - b) = x c by abel]
    have h4 : 4 * lam * d = h / 4 := by rw [mul_assoc, hlamd]; ring
    linarith [hgain c, hc.1, hc.2]
  have hc := hcore d hd k w (fun c g => F c (b + S g)) (fun c g => (fderiv ℝ (F c) (b + S g)).comp S)
    (fun g => G (b + S g)) (fun g => (G' (b + S g)).comp S) Gs'' (Lp * ‖S‖) (Lp * ‖S‖) M' lam T y Sg hw hFs hFsc
    hFs'b hGs hGs' hGs'b hGs''b hGspos hS1' hS2'
    hS4' hlam hT0 htail hgain'
  -- integrability of the variance under the cloud
  have hint_sq : ∀ c, Integrable (fun g => (F c (b + S g) - G (b + S g)) ^ 2) γ := fun c => by
    have h3 := (AdversarialBco.lipschitzWith_comp_affine (F c) Lp (hFL c) b S).sub
      (AdversarialBco.lipschitzWith_comp_affine G Lp hGL b S)
    set K : ℝ := ((Lp * ‖S‖₊ + Lp * ‖S‖₊ : ℝ≥0) : ℝ) with hK_def
    refine AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm_sq (h3.continuous.pow 2).aestronglyMeasurable
      (A := 2 * (F c (b + S 0) - G (b + S 0)) ^ 2) (B := 0) (C := 2 * K ^ 2) fun g => ?_
    have hd := h3.dist_le_mul g 0
    rw [Real.dist_eq, dist_zero_right] at hd
    have e1 : ((F c (b + S g) - G (b + S g)) - (F c (b + S 0) - G (b + S 0))) ^ 2 ≤ (K * ‖g‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [abs_pow, sq_abs]
    nlinarith [sq_nonneg ((F c (b + S g) - G (b + S g)) - 2 * (F c (b + S 0) - G (b + S 0)))]
  have hEVint : Integrable (fun g => ∑ c, w c * (F c (b + S g) - G (b + S g)) ^ 2) γ :=
    integrable_finsetSum _ fun c _ => (hint_sq c).const_mul (w c)
  have hEVSgint : Integrable (fun g => ∑ c ∈ Sg, w c * (F c (b + S g) - G (b + S g)) ^ 2) γ :=
    integrable_finsetSum _ fun c _ => (hint_sq c).const_mul (w c)
  have hE : ∫ g, ∑ c ∈ Sg, w c * (F c (b + S g) - G (b + S g)) ^ 2 ∂γ ≤
      ∫ g, ∑ c, w c * (F c (b + S g) - G (b + S g)) ^ 2 ∂γ :=
    integral_mono hEVSgint hEVint fun g =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => mul_nonneg (hw c) (sq_nonneg _)
  have hVb : ∑ c ∈ Sg, w c * (F c (b + S 0) - G (b + S 0)) ^ 2 ≤ ∑ c, w c * (F c b - G b) ^ 2 := by
    simp only [map_zero, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => mul_nonneg (hw c) (sq_nonneg _)
  -- moved components
  have hmv : ∀ c ∈ Mv, h ^ 2 / 32 ≤ (F c b - G b) ^ 2 + (F c bstar - G bstar) ^ 2 := fun c hc => by
    simp only [hMv_def, hA_def, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hc
    exact moved_arith h η (F c b) (F c bstar) (G b) (G bstar) hh hη0 hηh hc.2 (hbstar b)
  have hMv : (∑ c ∈ Mv, w c) * (h ^ 2 / 32) ≤
      ∑ c, w c * (F c b - G b) ^ 2 + ∑ c, w c * (F c bstar - G bstar) ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    calc ∑ c ∈ Mv, w c * (h ^ 2 / 32) ≤ ∑ c ∈ Mv, (w c * (F c b - G b) ^ 2 + w c * (F c bstar - G bstar) ^ 2) :=
          Finset.sum_le_sum fun c hc => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hmv c hc) (hw c)
      _ ≤ ∑ c, (w c * (F c b - G b) ^ 2 + w c * (F c bstar - G bstar) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ =>
            add_nonneg (mul_nonneg (hw c) (sq_nonneg _)) (mul_nonneg (hw c) (sq_nonneg _))
  -- the arithmetic
  have hsplit : ∑ j ∈ A, w j = ∑ c ∈ Sg, w c + ∑ c ∈ Mv, w c :=
    (Finset.sum_filter_add_sum_filter_not A _ _).symm
  set Vs := ∑ c, w c * (F c bstar - G bstar) ^ 2 with hVs_def
  set Vb := ∑ c, w c * (F c b - G b) ^ 2 with hVb_def
  set EV := ∫ g, ∑ c, w c * (F c (b + S g) - G (b + S g)) ^ 2 ∂γ with hEV_def
  have hVs0 : 0 ≤ Vs := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hVb0 : 0 ≤ Vb := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hEV0 : 0 ≤ EV := integral_nonneg fun g => Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hD1 : 1 ≤ (d : ℝ) ^ 2 * (1 + T) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd') (one_le_pow₀ (by linarith))
  have hcore' : (∑ c ∈ Sg, w c) * (h ^ 2 / 256) ≤ K0 * (d : ℝ) ^ 2 * (1 + T) ^ 2 * (EV + Vb) := by
    have e : (lam * (d : ℝ)) ^ 2 = h ^ 2 / 256 := by rw [hlamd]; ring
    rw [← e]
    exact hc.trans (mul_le_mul_of_nonneg_left (add_le_add hE hVb) (by positivity))
  have hG0le : G0 ≤ 2 * Real.log (2 * gmax / G0) * (h * (∑ c ∈ Sg, w c + ∑ c ∈ Mv, w c)) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (2 * gmax / G0))).1 hi2
    rw [hsplit] at this
    linarith
  exact dil_arith K0 d T (Real.log (2 * gmax / G0)) h G0 (∑ c ∈ Sg, w c) (∑ c ∈ Mv, w c) Vs Vb EV hK0 hD1 hlog hh
    hVs0 hVb0 hEV0 hcore' hMv hG0le

end AdversarialBco.Body
