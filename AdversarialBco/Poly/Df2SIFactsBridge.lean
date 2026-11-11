/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetTools

@[expose] public section

/-!
# From the matrices of the state to the operators of the surrogate

For `A` invertible: `toEuclideanCLM A` and `toEuclideanCLM A⁻¹` are inverse to each other, `|A⁻¹ v|² = vᵀ (A Aᵀ)⁻¹ v`,
and `A Aᵀ ≤ c` gives `|v| ≤ c^{1/2} |A⁻¹ v|` and `|A g| ≤ c^{1/2} |g|`.
-/

open scoped RealInnerProductSpace Matrix

namespace AdversarialBco.Poly.SIF

variable {d : ℕ}

/-- `‖v‖² = v ⬝ᵥ v` on `E d`. -/
theorem norm_toLp_sq (v : Fin d → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, dotProduct]
  simp only [pow_two]

/-- `A A⁻¹ = 1` on `E d`. -/
theorem clm_mul_inv (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) = x := by
  have h : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have := congrArg (fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) h
  simp only [map_mul, map_one] at this
  exact this

/-- `A⁻¹ A = 1` on `E d`. -/
theorem clm_inv_mul (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) = x := by
  have h : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have := congrArg (fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) h
  simp only [map_mul, map_one] at this
  exact this

/-- `|A⁻¹ v|² = vᵀ (A Aᵀ)⁻¹ v`. -/
theorem clm_inv_norm_sq (A : Matrix (Fin d) (Fin d) ℝ) (_hA : A.det ≠ 0) (v : Fin d → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (WithLp.toLp 2 v)‖ ^ 2 = df2Sq (A * Aᵀ)⁻¹ v := by
  have hinv : (A * Aᵀ)⁻¹ = (A⁻¹)ᵀ * A⁻¹ := by rw [Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  unfold df2Sq
  rw [Matrix.toEuclideanCLM_toLp, norm_toLp_sq, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, ← hinv, dotProduct_comm]

/-- `A Aᵀ ≤ c` gives `|Aᵀ u|² ≤ c |u|²`. -/
theorem transpose_norm_sq_le (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (h : (c • (1 : Matrix (Fin d) (Fin d) ℝ) - A * Aᵀ).PosSemidef) (u : Fin d → ℝ) :
    (Aᵀ *ᵥ u) ⬝ᵥ (Aᵀ *ᵥ u) ≤ c * (u ⬝ᵥ u) := by
  have e : (Aᵀ *ᵥ u) ⬝ᵥ (Aᵀ *ᵥ u) = df2Sq (A * Aᵀ) u := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, dotProduct_comm]
    rfl
  rw [e]
  have := Layer2.sq_le_of_psd h u
  rwa [Layer2.sq_smul, Layer2.sq_one] at this

/-- `A Aᵀ ≤ c` gives `⟪x, A y⟫ ≤ c^{1/2} |x| |y|`. -/
theorem inner_clm_le (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : (c • (1 : Matrix (Fin d) (Fin d) ℝ) - A * Aᵀ).PosSemidef) (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ ≤ Real.sqrt c * ‖x‖ * ‖y‖ := by
  have hdot : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ = ⟪WithLp.toLp 2 (Aᵀ *ᵥ WithLp.ofLp x), y⟫ := by
    rw [Matrix.inner_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have hT : ‖WithLp.toLp 2 (Aᵀ *ᵥ WithLp.ofLp x)‖ ≤ Real.sqrt c * ‖x‖ := by
    have hsq : ‖WithLp.toLp 2 (Aᵀ *ᵥ WithLp.ofLp x)‖ ^ 2 ≤ (Real.sqrt c * ‖x‖) ^ 2 := by
      rw [norm_toLp_sq, mul_pow, Real.sq_sqrt hc, ← WithLp.toLp_ofLp (p := 2) x, norm_toLp_sq, WithLp.ofLp_toLp]
      exact transpose_norm_sq_le A c h _
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  rw [hdot]
  calc _ ≤ ‖WithLp.toLp 2 (Aᵀ *ᵥ WithLp.ofLp x)‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ Real.sqrt c * ‖x‖ * ‖y‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)

/-- `A Aᵀ ≤ c` gives `|v| ≤ c^{1/2} |A⁻¹ v|`. -/
theorem clm_norm_le_inv (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (h : (c • (1 : Matrix (Fin d) (Fin d) ℝ) - A * Aᵀ).PosSemidef) (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ Real.sqrt c * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ v‖ := by
  set w := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ v with hw
  have h1 : ‖v‖ ^ 2 ≤ Real.sqrt c * ‖v‖ * ‖w‖ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [show v = Matrix.toEuclideanCLM (𝕜 := ℝ) A w from (clm_mul_inv A hA v).symm]
    have := inner_clm_le A c hc h v w
    rwa [show Matrix.toEuclideanCLM (𝕜 := ℝ) A w = v from clm_mul_inv A hA v] at this ⊢
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- `A Aᵀ ≤ c` gives `|A g| ≤ c^{1/2} |g|`. -/
theorem clm_norm_apply_le (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : (c • (1 : Matrix (Fin d) (Fin d) ℝ) - A * Aᵀ).PosSemidef) (g : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A g‖ ≤ Real.sqrt c * ‖g‖ := by
  set w := Matrix.toEuclideanCLM (𝕜 := ℝ) A g with hw
  have h1 : ‖w‖ ^ 2 ≤ Real.sqrt c * ‖w‖ * ‖g‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact inner_clm_le A c hc h w g
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

end AdversarialBco.Poly.SIF
