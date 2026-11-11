/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIProc

@[expose] public section

/-!
# Matrix and surrogate tools for the events LQ, S-DF and DQ

A symmetric matrix with a quadratic bound has the bilinear bound; the Hessian matrix of a `C²` function is symmetric
and is its second derivative; the surrogate is as Lipschitz as the extension, so its gradient is bounded; the
quadratic of a positive semidefinite matrix under a sum.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix RealInnerProductSpace

namespace AdversarialBco.Poly.EvSI

open Layer2

theorem bilin_le_of_quad {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (K : ℝ)
    (hK : ∀ v, |v ⬝ᵥ (M *ᵥ v)| ≤ K * (v ⬝ᵥ v)) (x y : Fin d → ℝ) :
    |x ⬝ᵥ (M *ᵥ y)| ≤ K * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) := by
  -- symmetry of the bilinear form: x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x)
  have h_symm : ∀ a b, a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := by
    intro a b
    calc
      a ⬝ᵥ (M *ᵥ b) = (Matrix.vecMul a M) ⬝ᵥ b := by rw [Matrix.dotProduct_mulVec]
      _ = (Matrix.vecMul a M.transpose) ⬝ᵥ b := by rw [hM]
      _ = (M.mulVec a) ⬝ᵥ b := by rw [Matrix.vecMul_transpose]
      _ = b ⬝ᵥ (M.mulVec a) := by rw [dotProduct_comm]
      _ = b ⬝ᵥ (M *ᵥ a) := rfl
  -- key identity: 4 * B(u,v) = Q(u+v) - Q(u-v) for all u, v
  have h_key : ∀ u v, (u + v) ⬝ᵥ (M *ᵥ (u + v)) - (u - v) ⬝ᵥ (M *ᵥ (u - v)) = 4 * (u ⬝ᵥ (M *ᵥ v)) := by
    intro u v
    simp only [mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct]
    rw [h_symm u v]
    ring_nf
  -- set a = x⬝x, b = y⬝y
  set a := x ⬝ᵥ x with ha
  set b := y ⬝ᵥ y with hb
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    simpa [dotProduct] using Finset.sum_nonneg (fun i _ => by nlinarith [sq_nonneg (x i)])
  have hb_nonneg : 0 ≤ b := by
    rw [hb]
    simpa [dotProduct] using Finset.sum_nonneg (fun i _ => by nlinarith [sq_nonneg (y i)])
  -- case split on a = 0 or b = 0
  by_cases ha0 : a = 0
  · -- then x = 0, so LHS = 0
    have hx0 : x = 0 := (dotProduct_self_eq_zero.mp ha0)
    rw [hx0]
    simp [ha0]
  by_cases hb0 : b = 0
  · -- then y = 0, so LHS = 0
    have hy0 : y = 0 := (dotProduct_self_eq_zero.mp hb0)
    rw [hy0]
    simp [hb0]
  -- now a > 0 and b > 0
  have ha_pos : 0 < a := by
    by_contra! h
    exact ha0 (le_antisymm h ha_nonneg)
  have hb_pos : 0 < b := by
    by_contra! h
    exact hb0 (le_antisymm h hb_nonneg)
  have ha_sqrt_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
  have hb_sqrt_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
  have ha_sqrt_nonneg : 0 ≤ Real.sqrt a := le_of_lt ha_sqrt_pos
  have hb_sqrt_nonneg : 0 ≤ Real.sqrt b := le_of_lt hb_sqrt_pos
  -- set s = (sqrt(b)/sqrt(a))^{1/2}, so s^2 = sqrt(b)/sqrt(a)
  set s := Real.sqrt (Real.sqrt b / Real.sqrt a) with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (div_pos hb_sqrt_pos ha_sqrt_pos)
  have hs_sq : s^2 = Real.sqrt b / Real.sqrt a := by
    rw [hs]
    exact Real.sq_sqrt (div_nonneg hb_sqrt_nonneg ha_sqrt_nonneg)
  -- apply the bound to (s • x) and (s⁻¹ • y)
  -- first compute: (s • x) ⬝ᵥ (M *ᵥ (s⁻¹ • y)) = x ⬝ᵥ (M *ᵥ y)
  have h_apply : (s • x) ⬝ᵥ (M *ᵥ (s⁻¹ • y)) = x ⬝ᵥ (M *ᵥ y) := by
    simp [dotProduct_smul, smul_dotProduct, mulVec_smul, hs_pos.ne.symm]
  -- compute the bound using the key identity
  have h_bound : |(s • x) ⬝ᵥ (M *ᵥ (s⁻¹ • y))| ≤ (K / 2) * ((s • x) ⬝ᵥ (s • x) + (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y)) := by
    let u := s • x
    let v := s⁻¹ • y
    let A := (u + v) ⬝ᵥ (M *ᵥ (u + v))
    let B := (u - v) ⬝ᵥ (M *ᵥ (u - v))
    have hkey' : A - B = 4 * (u ⬝ᵥ (M *ᵥ v)) := h_key u v
    have h_abs_sub : |4 * (u ⬝ᵥ (M *ᵥ v))| = |A - B| := by rw [hkey']
    have h_triangle : |A - B| ≤ |A| + |B| := by
      -- |A - B| = |A + (-B)| ≤ |A| + |-B| = |A| + |B|
      calc
        |A - B| = |A + (-B)| := by rw [sub_eq_add_neg]
        _ ≤ |A| + |-B| := abs_add_le _ _
        _ = |A| + |B| := by rw [abs_neg]
    have h_hK1 : |A| ≤ K * ((u + v) ⬝ᵥ (u + v)) := hK _
    have h_hK2 : |B| ≤ K * ((u - v) ⬝ᵥ (u - v)) := hK _
    have h_abs_mul : |4 * (u ⬝ᵥ (M *ᵥ v))| = 4 * |u ⬝ᵥ (M *ᵥ v)| := by
      rw [abs_mul, abs_of_pos (by norm_num : 0 < (4 : ℝ))]
    have h_parallelogram' : (u + v) ⬝ᵥ (u + v) + (u - v) ⬝ᵥ (u - v) = 2 * (u ⬝ᵥ u + v ⬝ᵥ v) := by
      simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
      ring
    have h_main : 4 * |u ⬝ᵥ (M *ᵥ v)| ≤ 2 * K * (u ⬝ᵥ u + v ⬝ᵥ v) := by
      calc
        4 * |u ⬝ᵥ (M *ᵥ v)| = |4 * (u ⬝ᵥ (M *ᵥ v))| := by rw [h_abs_mul]
        _ = |A - B| := by rw [h_abs_sub]
        _ ≤ |A| + |B| := h_triangle
        _ ≤ K * ((u + v) ⬝ᵥ (u + v)) + K * ((u - v) ⬝ᵥ (u - v)) := by nlinarith
        _ = K * ((u + v) ⬝ᵥ (u + v) + (u - v) ⬝ᵥ (u - v)) := by ring
        _ = K * (2 * (u ⬝ᵥ u + v ⬝ᵥ v)) := by rw [h_parallelogram']
        _ = 2 * K * (u ⬝ᵥ u + v ⬝ᵥ v) := by ring
    nlinarith
  -- Now simplify the RHS of the bound
  have h_simplify : (K / 2) * ((s • x) ⬝ᵥ (s • x) + (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y)) = K * (Real.sqrt a * Real.sqrt b) := by
    have h1 : (s • x) ⬝ᵥ (s • x) = s^2 * a := by
      simp [dotProduct_smul, smul_dotProduct, ha]
      ring
    have h2 : (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y) = (s⁻¹)^2 * b := by
      simp [dotProduct_smul, smul_dotProduct, hb]
      ring
    rw [h1, h2]
    have hs_inv_sq : (s⁻¹)^2 = Real.sqrt a / Real.sqrt b := by
      calc
        (s⁻¹)^2 = (s^2)⁻¹ := by ring
        _ = (Real.sqrt b / Real.sqrt a)⁻¹ := by rw [hs_sq]
        _ = Real.sqrt a / Real.sqrt b := by field_simp [ha_sqrt_pos.ne.symm, hb_sqrt_pos.ne.symm]
    rw [hs_sq, hs_inv_sq]
    -- Now: (K/2) * ( (sqrt(b)/sqrt(a))*a + (sqrt(a)/sqrt(b))*b )
    -- = (K/2) * ( sqrt(b)*sqrt(a) + sqrt(a)*sqrt(b) )
    -- = K * sqrt(a)*sqrt(b)
    have h_sq_sqrt_a : (Real.sqrt a)^2 = a := Real.sq_sqrt ha_nonneg
    have h_sq_sqrt_b : (Real.sqrt b)^2 = b := Real.sq_sqrt hb_nonneg
    calc
      (K / 2) * ((Real.sqrt b / Real.sqrt a) * a + (Real.sqrt a / Real.sqrt b) * b) =
          (K / 2) * (((Real.sqrt b)^2 * a) / (Real.sqrt a * Real.sqrt b) + ((Real.sqrt a)^2 * b) / (Real.sqrt a * Real.sqrt b)) := by
        field_simp [ha_sqrt_pos.ne.symm, hb_sqrt_pos.ne.symm]
      _ = (K / 2) * ((b * a) / (Real.sqrt a * Real.sqrt b) + (a * b) / (Real.sqrt a * Real.sqrt b)) := by
        rw [h_sq_sqrt_a, h_sq_sqrt_b]
      _ = (K / 2) * ((b * a + a * b) / (Real.sqrt a * Real.sqrt b)) := by ring
      _ = (K / 2) * ((2 * a * b) / (Real.sqrt a * Real.sqrt b)) := by ring
      _ = K * (a * b) / (Real.sqrt a * Real.sqrt b) := by ring
      _ = K * ((Real.sqrt a)^2 * (Real.sqrt b)^2) / (Real.sqrt a * Real.sqrt b) := by rw [h_sq_sqrt_a, h_sq_sqrt_b]
      _ = K * (Real.sqrt a * Real.sqrt b) := by
        field_simp [ha_sqrt_pos.ne.symm, hb_sqrt_pos.ne.symm]
  -- Combine
  calc
    |x ⬝ᵥ (M *ᵥ y)| = |(s • x) ⬝ᵥ (M *ᵥ (s⁻¹ • y))| := by rw [h_apply]
    _ ≤ (K / 2) * ((s • x) ⬝ᵥ (s • x) + (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y)) := h_bound
    _ = K * (Real.sqrt a * Real.sqrt b) := by rw [h_simplify]
    _ = K * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) := by rw [ha, hb]

theorem hessM_transpose {d : ℕ} (f : E d → ℝ) (hf : ContDiff ℝ 2 f) (z : E d) :
    (df2HessM f z)ᵀ = df2HessM f z := by
  have h_symm : IsSymmSndFDerivAt ℝ f z :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  ext i j
  simp [df2HessM, Matrix.transpose_apply]
  exact h_symm.eq (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)

theorem hessM_bilin {d : ℕ} (f : E d → ℝ) (z : E d) (x y : Fin d → ℝ) :
    x ⬝ᵥ (df2HessM f z *ᵥ y) = fderiv ℝ (fderiv ℝ f) z (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  have hsumx : WithLp.toLp 2 x = ∑ i : Fin d, x i • (EuclideanSpace.single i 1 : E d) := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (WithLp.toLp 2 x)
    rw [← h]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have hsumy : WithLp.toLp 2 y = ∑ i : Fin d, y i • (EuclideanSpace.single i 1 : E d) := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (WithLp.toLp 2 y)
    rw [← h]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have h_expand : fderiv ℝ (fderiv ℝ f) z (∑ i : Fin d, x i • EuclideanSpace.single i 1)
      (∑ i : Fin d, y i • EuclideanSpace.single i 1) =
      ∑ i : Fin d, ∑ j : Fin d, x i * y j *
        fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    calc
      fderiv ℝ (fderiv ℝ f) z (∑ i : Fin d, x i • EuclideanSpace.single i 1)
          (∑ i : Fin d, y i • EuclideanSpace.single i 1) =
          (∑ i : Fin d, (fderiv ℝ (fderiv ℝ f) z) (x i • EuclideanSpace.single i 1))
          (∑ i : Fin d, y i • EuclideanSpace.single i 1) := by
        rw [map_sum (fderiv ℝ (fderiv ℝ f) z)]
      _ = ∑ i : Fin d, ((fderiv ℝ (fderiv ℝ f) z) (x i • EuclideanSpace.single i 1))
          (∑ i : Fin d, y i • EuclideanSpace.single i 1) := by
        rw [_root_.sum_apply]
      _ = ∑ i : Fin d, (x i • (fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))
          (∑ i : Fin d, y i • EuclideanSpace.single i 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.map_smul]
      _ = ∑ i : Fin d, x i * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))
          (∑ i : Fin d, y i • EuclideanSpace.single i 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [_root_.smul_apply, smul_eq_mul]
      _ = ∑ i : Fin d, x i * (∑ j : Fin d, ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))
          (y j • EuclideanSpace.single j 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))]
      _ = ∑ i : Fin d, x i * (∑ j : Fin d, y j *
          ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine congrArg (fun t => x i * t) ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
      _ = ∑ i : Fin d, ∑ j : Fin d, x i * y j *
          ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  calc
    x ⬝ᵥ (df2HessM f z *ᵥ y) = ((Matrix.toBilin' (df2HessM f z)) x) y := by
      rw [Matrix.toBilin'_apply']
    _ = ∑ i : Fin d, ∑ j : Fin d, x i * df2HessM f z i j * y j := by
      rw [Matrix.toBilin'_apply]
    _ = ∑ i : Fin d, ∑ j : Fin d, x i * y j * df2HessM f z i j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∑ i : Fin d, ∑ j : Fin d, x i * y j *
        (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
      simp [df2HessM]
    _ = fderiv ℝ (fderiv ℝ f) z (∑ i : Fin d, x i • EuclideanSpace.single i 1)
        (∑ i : Fin d, y i • EuclideanSpace.single i 1) := by
      rw [h_expand]
    _ = fderiv ℝ (fderiv ℝ f) z (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
      rw [hsumx, hsumy]

theorem surr_lip {d : ℕ} (e : E d → ℝ) (K : ℝ) (hK : 0 ≤ K) (he : ∀ x y, |e x - e y| ≤ K * ‖x - y‖) (μ : E d)
    (A : E d →L[ℝ] E d) (lam : ℝ) (hlam : 0 < lam) (z z' : E d) :
    |df2Surr e μ A lam z - df2Surr e μ A lam z'| ≤ K * ‖z - z'‖ := by
  set ν := stdGaussian (EuclideanSpace ℝ (Fin d)) with hν
  have : IsGaussian ν := inferInstance
  have h_int_norm : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) ν :=
    IsGaussian.integrable_id.norm
  have h_int_one : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) ν :=
    integrable_const _
  have he_cont : Continuous e := by
    have hlip : LipschitzWith (Real.toNNReal K) e :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        have := he x y
        simpa [dist_eq_norm, Real.coe_toNNReal K, max_eq_left hK] using this)
    exact hlip.continuous
  have h_bound : ∀ x, |e x| ≤ |e 0| + K * ‖x‖ := by
    intro x
    have h := he x 0
    simp_rw [sub_zero] at h
    have h' : |e x| - |e 0| ≤ |e x - e 0| := by
      have := abs_sub_abs_le_abs_sub (e x) (e 0)
      linarith
    linarith
  -- integrability of e composed with an affine function of g
  have h_int_affine (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (b : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun g : EuclideanSpace ℝ (Fin d) => e (L g + b)) ν := by
    set C1 := |e 0| + K * ‖b‖ with hC1
    set C2 := K * ‖L‖ with hC2
    have h_bound' : ∀ g, |e (L g + b)| ≤ C1 + C2 * ‖g‖ := by
      intro g
      calc
        |e (L g + b)| ≤ |e 0| + K * ‖L g + b‖ := h_bound _
        _ ≤ |e 0| + K * (‖L g‖ + ‖b‖) := by gcongr; exact norm_add_le _ _
        _ ≤ |e 0| + K * (‖L‖ * ‖g‖ + ‖b‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm L g
        _ = (|e 0| + K * ‖b‖) + (K * ‖L‖) * ‖g‖ := by ring
        _ = C1 + C2 * ‖g‖ := by rw [hC1, hC2]
    have h_bound_int : Integrable (fun g => C1 + C2 * ‖g‖) ν := by
      simpa [mul_comm] using (h_int_one.const_mul C1).add (h_int_norm.const_mul C2)
    have h_meas : AEStronglyMeasurable (fun g => e (L g + b)) ν :=
      (Continuous.aestronglyMeasurable he_cont).comp_measurable
        ((L.measurable).add measurable_const)
    refine Integrable.mono' h_bound_int h_meas ?_
    filter_upwards with g
    simpa using h_bound' g
  set Lz := (1 - lam) • A with hLz
  set bz := (1 - lam) • μ + lam • z with hbz
  set bz' := (1 - lam) • μ + lam • z' with hbz'
  have h_int_z : Integrable (fun g => e (Lz g + bz)) ν := h_int_affine Lz bz
  have h_int_z' : Integrable (fun g => e (Lz g + bz')) ν := h_int_affine Lz bz'
  have h_diff_eq : df2Surr e μ A lam z - df2Surr e μ A lam z' =
      (1 / lam) * (∫ g, (e (Lz g + bz) - e (Lz g + bz')) ∂ν) := by
    dsimp [df2Surr, Lz, bz, bz', ν]
    have h_eq_int_z : (∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        (∫ g, e (Lz g + bz) ∂ν) := by
      refine MeasureTheory.integral_congr_ae (ae_of_all _ (fun g => ?_))
      simp [Lz, bz, add_comm, add_assoc, smul_add]
    have h_eq_int_z' : (∫ g, e ((1 - lam) • (μ + A g) + lam • z') ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
        (∫ g, e (Lz g + bz') ∂ν) := by
      refine MeasureTheory.integral_congr_ae (ae_of_all _ (fun g => ?_))
      simp [Lz, bz', add_comm, add_assoc, smul_add]
    rw [h_eq_int_z, h_eq_int_z', MeasureTheory.integral_sub h_int_z h_int_z']
    field_simp [hlam.ne']
    ring
  rw [h_diff_eq]
  have h_one_div_lam_pos : 0 < 1 / lam := div_pos (by norm_num) hlam
  rw [abs_mul, abs_of_pos h_one_div_lam_pos]
  have h_main : |∫ g, (e (Lz g + bz) - e (Lz g + bz')) ∂ν| ≤ K * lam * ‖z - z'‖ := by
    calc
      |∫ g, (e (Lz g + bz) - e (Lz g + bz')) ∂ν| ≤ ∫ g, ‖e (Lz g + bz) - e (Lz g + bz')‖ ∂ν := by
        simpa using MeasureTheory.norm_integral_le_integral_norm (fun g => e (Lz g + bz) - e (Lz g + bz')) (μ := ν)
      _ = ∫ g, |e (Lz g + bz) - e (Lz g + bz')| ∂ν := by simp
      _ ≤ ∫ g, K * ‖(Lz g + bz) - (Lz g + bz')‖ ∂ν := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
        · refine ae_of_all _ (fun g => abs_nonneg _)
        · have : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => K * ‖bz - bz'‖) ν :=
            integrable_const _
          simpa [sub_sub_sub_cancel_right] using this
        · refine ae_of_all _ (fun g => ?_)
          exact he (Lz g + bz) (Lz g + bz')
      _ = ∫ g, K * ‖bz - bz'‖ ∂ν := by
        refine MeasureTheory.integral_congr_ae ?_
        refine ae_of_all _ (fun g => ?_)
        have : (Lz g + bz) - (Lz g + bz') = bz - bz' := by
          abel
        simp [this]
      _ = K * ‖bz - bz'‖ := by
        rw [MeasureTheory.integral_const]
        have : IsProbabilityMeasure ν := inferInstance
        simp
      _ = K * (lam * ‖z - z'‖) := by
        rw [hbz, hbz']
        have : ((1 - lam) • μ + lam • z) - ((1 - lam) • μ + lam • z') = lam • (z - z') := by
          calc
            ((1 - lam) • μ + lam • z) - ((1 - lam) • μ + lam • z') = lam • z - lam • z' := by abel
            _ = lam • (z - z') := by rw [smul_sub]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
      _ = K * lam * ‖z - z'‖ := by ring
  calc
    (1 / lam) * |∫ g, (e (Lz g + bz) - e (Lz g + bz')) ∂ν| ≤ (1 / lam) * (K * lam * ‖z - z'‖) := by
      gcongr
    _ = K * ‖z - z'‖ := by field_simp [hlam.ne']

theorem psd_expand {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) (a b : Fin d → ℝ) (η : ℝ)
    (hη : 0 < η) : df2Sq P (a + b) ≤ (1 + η) * df2Sq P a + (1 + η⁻¹) * df2Sq P b := by
  -- Over ℝ, star is identity
  have hstar (x : Fin d → ℝ) : star x = x := star_id_of_comm
  -- PSD gives nonnegativity of the quadratic form
  have hP_nonneg (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by
    simpa [hstar x] using hP.dotProduct_mulVec_nonneg x
  -- Symmetry: a ⬝ᵥ (P *ᵥ b) = b ⬝ᵥ (P *ᵥ a) because P is Hermitian
  have h_symm (x y : Fin d → ℝ) : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
    have hP_transpose_eq : Pᵀ = P := hP.1.isSymm.eq
    calc
      x ⬝ᵥ (P *ᵥ y) = x ⬝ᵥ (Pᵀ *ᵥ y) := by rw [hP_transpose_eq]
      _ = y ⬝ᵥ (P *ᵥ x) := by rw [dotProduct_transpose_mulVec]
  -- Expand df2Sq P (a + b) = Qa + 2*B + Qb where Qa = df2Sq P a, Qb = df2Sq P b, B = b ⬝ᵥ (P *ᵥ a)
  have h_expand : df2Sq P (a + b) = df2Sq P a + 2 * (b ⬝ᵥ (P *ᵥ a)) + df2Sq P b := by
    dsimp [df2Sq]
    calc
      (a + b) ⬝ᵥ (P *ᵥ (a + b)) = (a + b) ⬝ᵥ (P *ᵥ a + P *ᵥ b) := by rw [mulVec_add]
      _ = (a + b) ⬝ᵥ (P *ᵥ a) + (a + b) ⬝ᵥ (P *ᵥ b) := by rw [dotProduct_add]
      _ = (a ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ a)) + (a ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ b)) := by
        simp [add_dotProduct]
      _ = (a ⬝ᵥ (P *ᵥ a) + a ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ a)) + b ⬝ᵥ (P *ᵥ b) := by ring
      _ = (a ⬝ᵥ (P *ᵥ a) + (a ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ a)) + b ⬝ᵥ (P *ᵥ b)) := by ring
      _ = (a ⬝ᵥ (P *ᵥ a) + (b ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ a)) + b ⬝ᵥ (P *ᵥ b)) := by
        rw [h_symm a b]
      _ = (a ⬝ᵥ (P *ᵥ a) + 2 * (b ⬝ᵥ (P *ᵥ a)) + b ⬝ᵥ (P *ᵥ b)) := by ring
      _ = df2Sq P a + 2 * (b ⬝ᵥ (P *ᵥ a)) + df2Sq P b := rfl
  rw [h_expand]
  set Qa := df2Sq P a with hQa
  set Qb := df2Sq P b with hQb
  set B := b ⬝ᵥ (P *ᵥ a) with hB
  -- Apply PSD to η • a - b
  have h_psd : 0 ≤ (η • a - b) ⬝ᵥ (P *ᵥ (η • a - b)) := hP_nonneg (η • a - b)
  -- Expand the PSD inequality
  have h_psd_expand : (η • a - b) ⬝ᵥ (P *ᵥ (η • a - b)) = η ^ 2 * Qa - 2 * η * B + Qb := by
    dsimp [Qa, Qb, B, df2Sq]
    calc
      (η • a - b) ⬝ᵥ (P *ᵥ (η • a - b)) = (η • a - b) ⬝ᵥ (P *ᵥ (η • a) - P *ᵥ b) := by rw [mulVec_sub]
      _ = (η • a - b) ⬝ᵥ (η • (P *ᵥ a) - P *ᵥ b) := by rw [mulVec_smul]
      _ = (η • a - b) ⬝ᵥ (η • (P *ᵥ a)) - (η • a - b) ⬝ᵥ (P *ᵥ b) := by rw [dotProduct_sub]
      _ = ((η • a) ⬝ᵥ (η • (P *ᵥ a)) - b ⬝ᵥ (η • (P *ᵥ a))) - ((η • a) ⬝ᵥ (P *ᵥ b) - b ⬝ᵥ (P *ᵥ b)) := by
        rw [sub_dotProduct, sub_dotProduct]
      _ = ((η • a) ⬝ᵥ (η • (P *ᵥ a)) - b ⬝ᵥ (η • (P *ᵥ a))) - (η • a) ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ b) := by ring
      _ = (η • (a ⬝ᵥ (η • (P *ᵥ a))) - η • (b ⬝ᵥ (P *ᵥ a))) - η • (a ⬝ᵥ (P *ᵥ b)) + (b ⬝ᵥ (P *ᵥ b)) := by
        simp [smul_dotProduct, dotProduct_smul]
      _ = (η * (η * (a ⬝ᵥ (P *ᵥ a))) - η * (b ⬝ᵥ (P *ᵥ a))) - η * (b ⬝ᵥ (P *ᵥ a)) + (b ⬝ᵥ (P *ᵥ b)) := by
        simp [dotProduct_smul, h_symm a b, smul_eq_mul]
      _ = η ^ 2 * (a ⬝ᵥ (P *ᵥ a)) - 2 * η * (b ⬝ᵥ (P *ᵥ a)) + (b ⬝ᵥ (P *ᵥ b)) := by ring
      _ = η ^ 2 * Qa - 2 * η * B + Qb := rfl
  rw [h_psd_expand] at h_psd
  -- Now h_psd : 0 ≤ η^2 * Qa - 2*η*B + Qb
  -- Rearranged: 2*η*B ≤ η^2 * Qa + Qb
  -- Since η > 0, divide by η: 2*B ≤ η * Qa + η⁻¹ * Qb
  have h_ineq : 2 * B ≤ η * Qa + η⁻¹ * Qb := by
    have h_temp : 2 * η * B ≤ η ^ 2 * Qa + Qb := by nlinarith
    have h_mul : η * (2 * B) ≤ η * (η * Qa + η⁻¹ * Qb) := by
      calc
        η * (2 * B) = 2 * η * B := by ring
        _ ≤ η ^ 2 * Qa + Qb := h_temp
        _ = η * (η * Qa) + Qb := by ring
        _ = η * (η * Qa) + η * (η⁻¹ * Qb) := by
          field_simp [hη.ne.symm]
        _ = η * (η * Qa + η⁻¹ * Qb) := by ring
    exact le_of_mul_le_mul_left h_mul hη
  -- Final inequality: Qa + 2*B + Qb ≤ (1+η)*Qa + (1+η⁻¹)*Qb
  nlinarith

/-- `|⟨s'(z), v⟩| ≤ K |v|` for a `K`-Lipschitz `f`. -/
theorem gradM_dot_le {d : ℕ} (f : E d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * ‖x - y‖)
    (z : E d) (v : Fin d → ℝ) : |df2GradM f z ⬝ᵥ v| ≤ K * Real.sqrt (v ⬝ᵥ v) := by
  rw [(gradM_hessM f z v).1]
  have h_norm : ‖fderiv ℝ f z‖ ≤ K :=
    norm_fderiv_le_of_lip' (𝕜 := ℝ) hK (by
      apply Filter.mem_of_superset Filter.univ_mem
      intro x _
      simpa using hf x z)
  have h_norm_sq : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq, dotProduct]
    simp [sq]
  have h_norm_eq : ‖WithLp.toLp 2 v‖ = Real.sqrt (v ⬝ᵥ v) := by
    rw [← h_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  calc
    |fderiv ℝ f z (WithLp.toLp 2 v)| = ‖fderiv ℝ f z (WithLp.toLp 2 v)‖ := by simp
    _ ≤ ‖fderiv ℝ f z‖ * ‖WithLp.toLp 2 v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖WithLp.toLp 2 v‖ := by gcongr
    _ = K * Real.sqrt (v ⬝ᵥ v) := by rw [h_norm_eq]

end AdversarialBco.Poly.EvSI
