/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Dil
public import AdversarialBco.Body2.Interface
public import AdversarialBco.Body2.Gauss2
public import AdversarialBco.Body2.Arith
public import AdversarialBco.Body2.Half

@[expose] public section

/-!
# Lemma 3.2 and Theorem 3.1 with (P3) for a regular family, with the frozen constant `KS`

`ecReg : EcReg` and `dilRegExplicit : DilRegExplicit`
(`AdversarialBco/Body2/Interface.lean`), from the one-component core inequality `core_one`, the
stationarity of a minimiser over invertible `S` (`AdversarialBco.Body.ec_first_order`), and the pigeonhole over the
scales (`AdversarialBco.scale_pigeonhole`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec

/-- `KS > 0`. -/
theorem KS_pos : 0 < KS := by
  obtain ⟨h1, -, h3, -⟩ := kappa_bounds
  unfold KS
  have : 0 < kappa := by linarith
  have : 0 < 13 / 4 + 2 * kappa2 := by linarith
  positivity

/-- Stationarity of a minimiser over invertible `S`: (S1) and (S2) in the coordinates of the cloud. -/
theorem minInv_stationary {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hG'c : Continuous G') (L : ℝ≥0) (hGL : LipschitzWith L G) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hm : IsMinInv G lam b S) :
    (∀ v, ∫ g, G' (b + S g) v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0) ∧
      ∀ v v', ∫ g, ⟪v, g⟫ * G' (b + S g) (S v') ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = lam * ⟪v, v'⟫ := by
  obtain ⟨hdet, hmin⟩ := hm
  refine ⟨fun v => ?_, fun v v' => ?_⟩
  · have := AdversarialBco.Body.ec_first_order G G' hG hG'c L hGL lam b S hdet hmin v 0
    simpa using this
  · have := AdversarialBco.Body.ec_first_order G G' hG hG'c L hGL lam b S hdet hmin 0
      ((innerSL ℝ v).smulRight v')
    simp only [zero_add, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
      smul_eq_mul] at this
    rw [this]
    congr 1
    rw [ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
    rfl

/-- Lemma 3.2 for a regular convex function. -/
theorem ecReg : EcReg := by
  intro d G Lp Mp a1 a2 lam hG2 hGc hGL hG'L ha1 hcoer hlam
  have hG' : ∀ x, HasFDerivAt G (fderiv ℝ G x) x := fun x => ((hG2.differentiable (by norm_num)) x).hasFDerivAt
  have hG'c : Continuous (fderiv ℝ G) := hG2.continuous_fderiv (by norm_num)
  refine ⟨?_, fun b S hm => ?_⟩
  · obtain ⟨b, S, hdet, hmin⟩ := AdversarialBco.Body.ec_min_exists G Lp hGL a1 a2 ha1 hcoer lam hlam
    exact ⟨b, S, hdet, hmin⟩
  · obtain ⟨hS1, hS2⟩ := minInv_stationary G (fderiv ℝ G) hG' hG'c Lp hGL lam b S hm
    exact ⟨AdversarialBco.Body.ec_S4 G hGc Lp hGL b S,
      fun y => AdversarialBco.Body.ec_S3 G (fderiv ℝ G) hG' hGc Lp hGL lam b S hS1 hS2 y⟩

set_option maxHeartbeats 1000000 in
/-- Theorem 3.1 with (P3) for a regular family, with the constant `KS`. -/
theorem dilRegExplicit : DilRegExplicit := by
  intro d hd k w F L Mp xmin a1 a2 bstar hw hw1 hF2 hFc hFL hF'L hxmin ha1 hcoer hbstar hΔ
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  -- the gains and the scale
  set gain : Fin k → ℝ := fun c => F c bstar - F c (xmin c) with hgain_def
  set Δs := mean w F bstar - ∑ c, w c * F c (xmin c) with hΔs_def
  set gmax := ⨆ c, (F c bstar - F c (xmin c)) with hgmax_def
  have hg0 : ∀ c, 0 ≤ gain c := fun c => sub_nonneg.2 (hxmin c bstar)
  have hgmax : ∀ c, gain c ≤ gmax := fun c => le_ciSup (Set.finite_range _).bddAbove c
  have hmean : ∑ c, w c * gain c = Δs := by
    simp only [hgain_def, hΔs_def, mean, mul_sub, Finset.sum_sub_distrib]
  obtain ⟨i, hi1, hi2⟩ := AdversarialBco.scale_pigeonhole w gain hw hw1 hg0 Δs gmax hΔ hgmax hmean
  set h := gain i with hh_def
  have hh : 0 < h := by linarith
  have hΔgmax : Δs ≤ gmax := by
    rw [← hmean]
    calc ∑ c, w c * gain c ≤ ∑ c, w c * gmax :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hgmax c) (hw c)
      _ = gmax := by rw [← Finset.sum_mul, hw1, one_mul]
  have hlog : 0 < Real.log (2 * gmax / Δs) := Real.log_pos (by rw [lt_div_iff₀ hΔ]; linarith)
  set lam := h / (16 * (d : ℝ)) with hlam_def
  have hlam : 0 < lam := by positivity
  have hlamd : lam * d = h / 16 := by rw [hlam_def]; field_simp
  -- the mean
  obtain ⟨G', G'', hG, hG', hG'c, hGL, hG'b, hG''b⟩ := AdversarialBco.Body.mean_regular w hw hw1 F L Mp hF2 hFL hF'L
  have hGc := AdversarialBco.Body.convexOn_wsum w hw F hFc
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ∑ c, w c * F c z with hG_def
  have hGmean : mean w F = G := rfl
  have hF' : ∀ c z, HasFDerivAt (F c) (fderiv ℝ (F c) z) z := fun c z =>
    (((hF2 c).differentiable (by norm_num)) z).hasFDerivAt
  have hF'b : ∀ c z, ‖fderiv ℝ (F c) z‖ ≤ L := fun c z => norm_fderiv_le_of_lipschitz ℝ (hFL c)
  refine ⟨h, hi1, hgmax i, ⟨i, rfl⟩, ?_, fun b S hm => ?_⟩
  · obtain ⟨b, S, hdet, hmin⟩ := AdversarialBco.Body.ec_min_exists G L hGL a1 a2 ha1 hcoer lam hlam
    exact ⟨b, S, hdet, hmin⟩
  obtain ⟨hS1, hS2⟩ := minInv_stationary G G' hG hG'c L hGL lam b S hm
  have hS3 : ∀ z, ∫ g, G (b + S g) ∂γ ≤ G z + lam * d := fun z =>
    AdversarialBco.Body.ec_S3 G G' hG hGc L hGL lam b S hS1 hS2 z
  have hS4 : G b ≤ ∫ g, G (b + S g) ∂γ := AdversarialBco.Body.ec_S4 G hGc L hGL b S
  refine ⟨hS4, hS3, ?_⟩
  -- the family in the coordinates of the cloud
  have haff : ∀ g, HasFDerivAt (fun g => b + S g) S g := fun g => (S.hasFDerivAt).const_add b
  have hFs : ∀ c g, HasFDerivAt (fun g => F c (b + S g)) ((fderiv ℝ (F c) (b + S g)).comp S) g := fun c g =>
    (hF' c (b + S g)).comp g (haff g)
  have hGs : ∀ g, HasFDerivAt (fun g => G (b + S g)) ((G' (b + S g)).comp S) g := fun g => by
    have h1 := (hG (b + S g)).comp g (haff g)
    exact h1
  obtain ⟨Gs'', M', hGs', hGs''b, hGspos⟩ :=
    AdversarialBco.Body.pullback_hess G G' G'' hG hG' hGc Mp hG''b b S
  have hFsc : ∀ c, ConvexOn ℝ Set.univ (fun g => F c (b + S g)) := fun c =>
    AdversarialBco.Body.convexOn_comp_cloud (F c) (hFc c) b S
  have hGsc : ConvexOn ℝ Set.univ (fun g => G (b + S g)) := AdversarialBco.Body.convexOn_comp_cloud G hGc b S
  have hFs'b : ∀ c g, ‖(fderiv ℝ (F c) (b + S g)).comp S‖ ≤ L * ‖S‖ := fun c g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hF'b c _) (norm_nonneg _))
  have hGs'b : ∀ g, ‖(G' (b + S g)).comp S‖ ≤ L * ‖S‖ := fun g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hG'b _) (norm_nonneg _))
  have hS1' : ∀ v, ∫ g, (G' (b + S g)).comp S v ∂γ = 0 := fun v => hS1 (S v)
  have hS2' : ∀ v v', ∫ g, ⟪v, g⟫ * (G' (b + S g)).comp S v' ∂γ = lam * ⟪v, v'⟫ := fun v v' => hS2 v v'
  have hS4' : (fun g => G (b + S g)) 0 ≤ ∫ g, (fun g => G (b + S g)) g ∂γ := by
    simpa using hS4
  -- the tail parameter
  set T := Real.sqrt (2 * lnp (26 * d * L * ‖S‖ / h)) with hT_def
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have htail : 2 * (L * ‖S‖) * phi T ≤ h / (32 * d) := by
    have := phiT_tail (L * ‖S‖) h d (by positivity) hh hd'
    rwa [show (26 : ℝ) * d * (L * ‖S‖) / h = 26 * d * L * ‖S‖ / h by ring] at this
  -- good and moved components
  set A := Finset.univ.filter (fun j => gain i ≤ gain j) with hA_def
  set Sg := A.filter (fun j => -(h / 2) ≤ F j b - F j bstar) with hSg_def
  set Mv := A.filter (fun j => ¬ -(h / 2) ≤ F j b - F j bstar) with hMv_def
  have hsurj : Function.Surjective S := by
    have hu : IsUnit (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hm.1)
    exact ((Module.End.isUnit_iff _).1 hu).2
  choose y hy using fun c => hsurj (xmin c - b)
  set ℓ := kappa / 32 * h / ((1 + T) * d) with hℓ_def
  set C := 3 + 2 * kappa2 + 1 / (4 * (d : ℝ)) with hC_def
  have hone : ∀ c ∈ Sg, ℓ ^ 2 ≤ C * (∫ g, (F c (b + S g) - G (b + S g)) ^ 2 ∂γ + (F c b - G b) ^ 2) := by
    intro c hc
    simp only [hSg_def, hA_def, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hyc : F c (b + S (y c)) ≤ F c (b + S 0) - h / 2 := by
      rw [hy c, map_zero, add_zero, show b + (xmin c - b) = xmin c by abel]
      have : gain i ≤ F c bstar - F c (xmin c) := hc.1
      linarith [hc.2]
    have := core_one hd (fun g => F c (b + S g)) (fun g => G (b + S g)) (fun g => (fderiv ℝ (F c) (b + S g)).comp S)
      (fun g => (G' (b + S g)).comp S) Gs'' (hFs c) hGs hGs' (hFsc c) hGsc (L * ‖S‖) M' (hFs'b c) hGs'b hGs''b
      hGspos lam hS1' hS2' hS4' h T hh hlam_def hT0 htail (y c) hyc
    simpa only [map_zero, add_zero] using this
  -- integrability of the variance under the cloud
  have hint_sq : ∀ c, Integrable (fun g => (F c (b + S g) - G (b + S g)) ^ 2) γ := fun c => by
    have h3 := (AdversarialBco.lipschitzWith_comp_affine (F c) L (hFL c) b S).sub
      (AdversarialBco.lipschitzWith_comp_affine G L hGL b S)
    set K : ℝ := ((L * ‖S‖₊ + L * ‖S‖₊ : ℝ≥0) : ℝ) with hK_def
    refine AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm_sq (h3.continuous.pow 2).aestronglyMeasurable
      (A := 2 * (F c (b + S 0) - G (b + S 0)) ^ 2) (B := 0) (C := 2 * K ^ 2) fun g => ?_
    have hd := h3.dist_le_mul g 0
    rw [Real.dist_eq, dist_zero_right] at hd
    have e1 : ((F c (b + S g) - G (b + S g)) - (F c (b + S 0) - G (b + S 0))) ^ 2 ≤ (K * ‖g‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [abs_pow, sq_abs]
    nlinarith [sq_nonneg ((F c (b + S g) - G (b + S g)) - 2 * (F c (b + S 0) - G (b + S 0)))]
  set Vs := var w F bstar with hVs_def
  set Vb := var w F b with hVb_def
  set VG := ∫ z, var w F (b + S z) ∂γ with hVG_def
  have hVs0 : 0 ≤ Vs := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hVb0 : 0 ≤ Vb := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hVGeq : VG = ∑ c, w c * ∫ g, (F c (b + S g) - G (b + S g)) ^ 2 ∂γ := by
    rw [hVG_def, show (fun z => var w F (b + S z)) = fun z => ∑ c, w c * (F c (b + S z) - G (b + S z)) ^ 2 from
      rfl, integral_finsetSum _ fun c _ => (hint_sq c).const_mul (w c)]
    exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
  set Vg := ∑ c ∈ Sg, w c * ∫ g, (F c (b + S g) - G (b + S g)) ^ 2 ∂γ with hVg_def
  set Vbg := ∑ c ∈ Sg, w c * (F c b - G b) ^ 2 with hVbg_def
  have hVg0 : 0 ≤ Vg := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (integral_nonneg fun g => sq_nonneg _)
  have hVbg0 : 0 ≤ Vbg := Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  have hVgG : Vg ≤ VG := by
    rw [hVGeq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ =>
      mul_nonneg (hw c) (integral_nonneg fun g => sq_nonneg _)
  have hVbgb : Vbg ≤ Vb :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => mul_nonneg (hw c) (sq_nonneg _)
  have hcore : (∑ c ∈ Sg, w c) * ℓ ^ 2 ≤ C * (Vg + Vbg) := by
    rw [Finset.sum_mul, hVg_def, hVbg_def, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc => by
      rw [← mul_add, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hone c hc) (hw c)
  -- moved components
  have hmv : ∀ c ∈ Mv, h ^ 2 / 8 ≤ (F c b - G b) ^ 2 + (F c bstar - G bstar) ^ 2 := fun c hc => by
    simp only [hMv_def, hA_def, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hc
    have hGb : G bstar ≤ G b := hbstar b
    nlinarith [sq_nonneg ((F c b - G b) + (F c bstar - G bstar)), hc.2]
  have hMv : (∑ c ∈ Mv, w c) * h ^ 2 / 8 ≤ Vb + Vs := by
    rw [mul_div_assoc, Finset.sum_mul]
    calc ∑ c ∈ Mv, w c * (h ^ 2 / 8) ≤ ∑ c ∈ Mv, (w c * (F c b - G b) ^ 2 + w c * (F c bstar - G bstar) ^ 2) :=
          Finset.sum_le_sum fun c hc => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hmv c hc) (hw c)
      _ ≤ ∑ c, (w c * (F c b - G b) ^ 2 + w c * (F c bstar - G bstar) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ =>
            add_nonneg (mul_nonneg (hw c) (sq_nonneg _)) (mul_nonneg (hw c) (sq_nonneg _))
      _ = Vb + Vs := Finset.sum_add_distrib
  have hsplit : ∑ j ∈ A, w j = ∑ c ∈ Sg, w c + ∑ c ∈ Mv, w c :=
    (Finset.sum_filter_add_sum_filter_not A _ _).symm
  have hscale := scale_arith2 (∑ j ∈ A, w j) (∑ c ∈ Sg, w c) (∑ c ∈ Mv, w c) h d T VG Vg Vb Vbg Vs hsplit.le
    (Finset.sum_nonneg fun c _ => hw c) (Finset.sum_nonneg fun c _ => hw c) hh hd' hT0 hVg0 hVbg0 hVs0 hVgG hVbgb
    hcore hMv
  -- (P3)
  have hKS := KS_pos
  have hP : 0 < 2 * KS * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs) := by positivity
  rw [div_le_iff₀ hP]
  have hi2' : Δs ≤ 2 * Real.log (2 * gmax / Δs) * (h * ∑ j ∈ A, w j) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (2 * gmax / Δs))).1 hi2
    linarith
  calc h * Δs ≤ h * (2 * Real.log (2 * gmax / Δs) * (h * ∑ j ∈ A, w j)) := mul_le_mul_of_nonneg_left hi2' hh.le
    _ = 2 * Real.log (2 * gmax / Δs) * ((∑ j ∈ A, w j) * h ^ 2) := by ring
    _ ≤ 2 * Real.log (2 * gmax / Δs) * (KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (Vs + Vb + VG) * (2 * KS * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs)) := by ring

end AdversarialBco.Body2
