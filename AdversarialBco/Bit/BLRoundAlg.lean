/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundBasic

@[expose] public section

/-!
# Piece C: the algebra and the scalar bounds of one round

The factor identities of DF2's update (`An = A° N°`, `Pn An = (P° A°) N°⁻¹`), the scalar errors of E3 at BL's
square roots and quotients (`e3_scal_*`), the matrix error of the factor (`e3_mat`), the Frobenius and trace bounds
of the guard R10, the bound `|Y| ≤ Ȳ`, and the increments of E9 (`inc_b`, `inc_k`).
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open Matrix

theorem PnAn_eq {d : ℕ} (P A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hqd : q = a + c * (ξ ⬝ᵥ ξ)) (hPA : Aᵀ * (P * A) = 1) (hP : Pᵀ = P) :
    (a • P + c • vecMulVec (P *ᵥ (A *ᵥ ξ)) (P *ᵥ (A *ᵥ ξ))) *
        ((Real.sqrt a)⁻¹ • (A - (c / q / (1 + Real.sqrt (a / q))) • vecMulVec (A *ᵥ ξ) ξ)) =
      (P * A) * (Real.sqrt a • (1 : Matrix (Fin d) (Fin d) ℝ) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec ξ ξ) := by
  set w := A *ᵥ ξ with hw
  set u := P *ᵥ w with hu
  have ha' : 0 ≤ a := by linarith
  have hq' : 0 ≤ q := by linarith
  have hs_pos : Real.sqrt a > 0 := Real.sqrt_pos.mpr ha
  have ht_pos : Real.sqrt q > 0 := Real.sqrt_pos.mpr hq
  have hs_ne_zero : Real.sqrt a ≠ 0 := by linarith
  have ht_ne_zero : Real.sqrt q ≠ 0 := by linarith
  have hAw : Aᵀ *ᵥ u = ξ := by
    calc
      Aᵀ *ᵥ u = Aᵀ *ᵥ (P *ᵥ w) := rfl
      _ = Aᵀ *ᵥ (P *ᵥ (A *ᵥ ξ)) := by rw [hw]
      _ = (Aᵀ * P) *ᵥ (A *ᵥ ξ) := by rw [Matrix.mulVec_mulVec]
      _ = ((Aᵀ * P) * A) *ᵥ ξ := by rw [Matrix.mulVec_mulVec]
      _ = (Aᵀ * (P * A)) *ᵥ ξ := by rw [Matrix.mul_assoc]
      _ = 1 *ᵥ ξ := by rw [hPA]
      _ = ξ := by simp
  have h_uw : u ⬝ᵥ w = ξ ⬝ᵥ ξ := by
    calc
      u ⬝ᵥ w = u ⬝ᵥ (A *ᵥ ξ) := by rw [hw]
      _ = ξ ⬝ᵥ (Aᵀ *ᵥ u) := by rw [Matrix.dotProduct_transpose_mulVec]
      _ = ξ ⬝ᵥ ξ := by rw [hAw]
  have h_vecMulVec_u_A : vecMulVec u u * A = vecMulVec u ξ := by
    calc
      vecMulVec u u * A = vecMulVec u (u ᵥ* A) := by rw [Matrix.vecMulVec_mul]
      _ = vecMulVec u (w ᵥ* (Pᵀ * A)) := by rw [hu, Matrix.vecMul_mulVec]
      _ = vecMulVec u (w ᵥ* (P * A)) := by rw [hP]
      _ = vecMulVec u (ξ ᵥ* (Aᵀ * (P * A))) := by rw [hw, Matrix.vecMul_mulVec]
      _ = vecMulVec u (ξ ᵥ* 1) := by rw [hPA]
      _ = vecMulVec u ξ := by simp
  have h_P_vecMulVec : P * vecMulVec w ξ = vecMulVec u ξ := by
    rw [Matrix.mul_vecMulVec, hu]
  have h_PA_vecMulVec : (P * A) * vecMulVec ξ ξ = vecMulVec u ξ := by
    calc
      (P * A) * vecMulVec ξ ξ = vecMulVec ((P * A) *ᵥ ξ) ξ := by rw [Matrix.mul_vecMulVec]
      _ = vecMulVec (P *ᵥ (A *ᵥ ξ)) ξ := by rw [Matrix.mulVec_mulVec]
      _ = vecMulVec u ξ := by rw [← hw, ← hu]
  set α := (Real.sqrt a)⁻¹ with hα
  set β := c / q / (1 + Real.sqrt (a / q)) with hβ
  set ξξ := ξ ⬝ᵥ ξ with hξξ
  have hq_eq : q = a + c * ξξ := hqd
  have h_scalar : c * α - a * α * β - c * α * β * ξξ = c / (Real.sqrt a + Real.sqrt q) := by
    dsimp [α, β, ξξ]
    have h_sqrta_pos : Real.sqrt a > 0 := Real.sqrt_pos.mpr ha
    have h_sqrtq_pos : Real.sqrt q > 0 := Real.sqrt_pos.mpr hq
    have h_denom : 1 + Real.sqrt (a / q) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (a / q)]
    have h_sqrt_div : Real.sqrt (a / q) = Real.sqrt a / Real.sqrt q := Real.sqrt_div ha' q
    set s := Real.sqrt a with hs
    set t := Real.sqrt q with ht
    set r := Real.sqrt (a / q) with hr
    have h_sqrt_div' : r = s / t := h_sqrt_div
    calc
      c * s⁻¹ - a * s⁻¹ * (c / q / (1 + r)) - c * s⁻¹ * (c / q / (1 + r)) * ξξ
          = s⁻¹ * (c - a * (c / q / (1 + r)) - c * (c / q / (1 + r)) * ξξ) := by ring
      _ = s⁻¹ * (c - (c / q / (1 + r)) * (a + c * ξξ)) := by ring
      _ = s⁻¹ * (c - (c / q / (1 + r)) * q) := by rw [hqd]
      _ = s⁻¹ * (c - c / (1 + r)) := by
            field_simp [hq.ne']
      _ = s⁻¹ * c * (r / (1 + r)) := by
            field_simp [h_denom]
            ring
      _ = s⁻¹ * c * r / (1 + r) := by ring
      _ = s⁻¹ * c * (s / t) / (1 + s / t) := by rw [h_sqrt_div']
      _ = c / t / (1 + s / t) := by
            calc
              s⁻¹ * c * (s / t) / (1 + s / t) = c * (s⁻¹ * s) / t / (1 + s / t) := by ring
              _ = c * 1 / t / (1 + s / t) := by
                    field_simp [h_sqrta_pos.ne']
              _ = c / t / (1 + s / t) := by simp
      _ = c / (t * (1 + s / t)) := by
            simp [div_div]
      _ = c / (t + s) := by
            have h : t * (1 + s / t) = t + s := by
              field_simp [h_sqrtq_pos.ne']
            rw [h]
      _ = c / (s + t) := by ring
  have h_left : (a • P + c • vecMulVec u u) * ((Real.sqrt a)⁻¹ • (A - (c / q / (1 + Real.sqrt (a / q))) • vecMulVec w ξ)) =
      Real.sqrt a • (P * A) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec u ξ := by
    calc
      (a • P + c • vecMulVec u u) * (α • (A - β • vecMulVec w ξ))
          = (a • P + c • vecMulVec u u) * (α • A - α • (β • vecMulVec w ξ)) := by
            rw [smul_sub, smul_smul]
      _ = (a • P + c • vecMulVec u u) * (α • A - (α * β) • vecMulVec w ξ) := by
            rw [smul_smul, mul_comm α β]
      _ = (a • P) * (α • A - (α * β) • vecMulVec w ξ) + (c • vecMulVec u u) * (α • A - (α * β) • vecMulVec w ξ) := by
            rw [Matrix.add_mul]
      _ = ((a • P) * (α • A) - (a • P) * ((α * β) • vecMulVec w ξ)) + ((c • vecMulVec u u) * (α • A) - (c • vecMulVec u u) * ((α * β) • vecMulVec w ξ)) := by
            rw [mul_sub, mul_sub]
      _ = ((a * α) • (P * A) - (a * (α * β)) • (P * vecMulVec w ξ)) + ((c * α) • (vecMulVec u u * A) - (c * (α * β)) • (vecMulVec u u * vecMulVec w ξ)) := by
            have h1 : (a • P) * (α • A) = (a * α) • (P * A) := by
              calc
                (a • P) * (α • A) = a • (P * (α • A)) := by rw [Matrix.smul_mul]
                _ = a • (α • (P * A)) := by rw [Matrix.mul_smul]
                _ = (a * α) • (P * A) := by rw [smul_smul]
            have h2 : (a • P) * ((α * β) • vecMulVec w ξ) = (a * (α * β)) • (P * vecMulVec w ξ) := by
              calc
                (a • P) * ((α * β) • vecMulVec w ξ) = a • (P * ((α * β) • vecMulVec w ξ)) := by rw [Matrix.smul_mul]
                _ = a • ((α * β) • (P * vecMulVec w ξ)) := by rw [Matrix.mul_smul]
                _ = (a * (α * β)) • (P * vecMulVec w ξ) := by rw [smul_smul]
            have h3 : (c • vecMulVec u u) * (α • A) = (c * α) • (vecMulVec u u * A) := by
              calc
                (c • vecMulVec u u) * (α • A) = c • (vecMulVec u u * (α • A)) := by rw [Matrix.smul_mul]
                _ = c • (α • (vecMulVec u u * A)) := by rw [Matrix.mul_smul]
                _ = (c * α) • (vecMulVec u u * A) := by rw [smul_smul]
            have h4 : (c • vecMulVec u u) * ((α * β) • vecMulVec w ξ) = (c * (α * β)) • (vecMulVec u u * vecMulVec w ξ) := by
              calc
                (c • vecMulVec u u) * ((α * β) • vecMulVec w ξ) = c • (vecMulVec u u * ((α * β) • vecMulVec w ξ)) := by rw [Matrix.smul_mul]
                _ = c • ((α * β) • (vecMulVec u u * vecMulVec w ξ)) := by rw [Matrix.mul_smul]
                _ = (c * (α * β)) • (vecMulVec u u * vecMulVec w ξ) := by rw [smul_smul]
            rw [h1, h2, h3, h4]
      _ = (((a * α) • (P * A)) - ((a * α * β) • (vecMulVec u ξ))) + ((c * α) • (vecMulVec u ξ) - ((c * α * β) • ((u ⬝ᵥ w) • vecMulVec u ξ))) := by
            rw [h_P_vecMulVec, h_vecMulVec_u_A, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
            simp [mul_comm, mul_left_comm, mul_assoc, smul_smul]
      _ = (((a * α) • (P * A)) - ((a * α * β) • (vecMulVec u ξ))) + ((c * α) • (vecMulVec u ξ) - ((c * α * β * (u ⬝ᵥ w)) • vecMulVec u ξ)) := by
            rw [smul_smul]
      _ = (a * α) • (P * A) + (c * α - a * α * β - c * α * β * (u ⬝ᵥ w)) • vecMulVec u ξ := by
            simp [add_smul, add_left_comm, add_assoc, sub_eq_add_neg]
      _ = (a * α) • (P * A) + (c * α - a * α * β - c * α * β * ξξ) • vecMulVec u ξ := by rw [h_uw]
      _ = Real.sqrt a • (P * A) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec u ξ := by
            have ha_eq : a * α = Real.sqrt a := by
              dsimp [α]
              field_simp [hs_ne_zero]
              rw [Real.sq_sqrt ha']
            have h_scalar' : c * α - Real.sqrt a * β - c * α * β * ξξ = c / (Real.sqrt a + Real.sqrt q) := by
              calc
                c * α - Real.sqrt a * β - c * α * β * ξξ = c * α - a * α * β - c * α * β * ξξ := by rw [← ha_eq]
                _ = c / (Real.sqrt a + Real.sqrt q) := h_scalar
            rw [ha_eq, h_scalar']
  have h_right : (P * A) * (Real.sqrt a • (1 : Matrix (Fin d) (Fin d) ℝ) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec ξ ξ) =
      Real.sqrt a • (P * A) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec u ξ := by
    calc
      (P * A) * (Real.sqrt a • (1 : Matrix (Fin d) (Fin d) ℝ) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec ξ ξ)
          = (P * A) * (Real.sqrt a • (1 : Matrix (Fin d) (Fin d) ℝ)) + (P * A) * ((c / (Real.sqrt a + Real.sqrt q)) • vecMulVec ξ ξ) := by
            rw [Matrix.mul_add]
      _ = Real.sqrt a • ((P * A) * 1) + (c / (Real.sqrt a + Real.sqrt q)) • ((P * A) * vecMulVec ξ ξ) := by
            simp
      _ = Real.sqrt a • (P * A) + (c / (Real.sqrt a + Real.sqrt q)) • vecMulVec u ξ := by
            simp [h_PA_vecMulVec]
  rw [h_left, h_right]

theorem An_eq_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (s k : ℝ) :
    s • (A - k • vecMulVec (A *ᵥ ξ) ξ) = A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + (-(s * k)) • vecMulVec ξ ξ) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_vecMulVec]
  rw [smul_sub, smul_smul, sub_eq_add_neg, neg_smul]

theorem coef_eq (c a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    (Real.sqrt a)⁻¹ * (c / q / (1 + Real.sqrt (a / q))) =
      c / (Real.sqrt a * Real.sqrt q * (Real.sqrt a + Real.sqrt q)) := by
  have ha' : 0 ≤ a := ha.le
  have hq' : 0 ≤ q := hq.le
  have hsqrt_div : Real.sqrt (a / q) = Real.sqrt a / Real.sqrt q := Real.sqrt_div ha' q
  have hq_sq : q = Real.sqrt q ^ 2 := by rw [Real.sq_sqrt hq']
  have hsqrta_pos : Real.sqrt a > 0 := Real.sqrt_pos.mpr ha
  have hsqrtq_pos : Real.sqrt q > 0 := Real.sqrt_pos.mpr hq
  have hsqrt_sqrtq : Real.sqrt (Real.sqrt q ^ 2) = Real.sqrt q := by
    rw [Real.sqrt_sq hsqrtq_pos.le]
  rw [hsqrt_div, hq_sq, hsqrt_sqrtq]
  field_simp [hsqrta_pos.ne.symm, hsqrtq_pos.ne.symm]
  ring

theorem e3_scal_inv (c c' Δ cb X1 tp s1 : ℝ) (hc : |c| ≤ cb) (hcc : |c' - c| ≤ Δ)
    (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 1000)
    (hs1 : s1 ≤ Real.sqrt (1 / (1 - c')) ∧ Real.sqrt (1 / (1 - c')) < s1 + tp) :
    |s1 - (Real.sqrt (1 - c))⁻¹| ≤ tp + Δ := by
  rcases hs1 with ⟨hs1_le, hs1_lt⟩
  have hX1sq_nonneg : 0 ≤ X1 ^ 2 := by positivity
  have h_one_plus_X1sq_ge_one : 1 ≤ 1 + X1 ^ 2 := by linarith
  have hcb_le : cb ≤ 1 / 10 ^ 30 := by
    nlinarith
  have hΔ_le : Δ ≤ 1 / 10 ^ 30 := by
    nlinarith
  have hΔ_nonneg : 0 ≤ Δ := by
    have h_nonneg_abs : 0 ≤ |c' - c| := abs_nonneg _
    linarith
  have hc_abs_le : |c| ≤ 1 / 10 ^ 30 := by linarith
  have hc'_abs_le : |c'| ≤ 2 / 10 ^ 30 := by
    have h_triangle : |c'| ≤ |c' - c| + |c| := by
      calc
        |c'| = |(c' - c) + c| := by ring_nf
        _ ≤ |c' - c| + |c| := abs_add_le _ _
    linarith
  have hc_le : c ≤ 2 / 10 ^ 30 := by
    have hc'_le : c' ≤ 2 / 10 ^ 30 := by
      have := abs_le.mp hc'_abs_le
      linarith
    have hc_le' : c ≤ 1 / 10 ^ 30 := by
      have := abs_le.mp hc_abs_le
      linarith
    linarith
  have hc_ge : -(2 / 10 ^ 30) ≤ c := by
    have hc_ge' : -(1 / 10 ^ 30) ≤ c := by
      have := abs_le.mp hc_abs_le
      linarith
    linarith
  have hc'_le : c' ≤ 2 / 10 ^ 30 := by
    have := abs_le.mp hc'_abs_le
    linarith
  have hc'_ge : -(2 / 10 ^ 30) ≤ c' := by
    have := abs_le.mp hc'_abs_le
    linarith
  have h_one_sub_c_pos : 0 < 1 - c := by linarith
  have h_one_sub_c'_pos : 0 < 1 - c' := by linarith
  have h_one_sub_c_nonneg : 0 ≤ 1 - c := by linarith
  have h_one_sub_c'_nonneg : 0 ≤ 1 - c' := by linarith
  have h_sqrt_pos : Real.sqrt (1 - c) > 0 := Real.sqrt_pos.mpr h_one_sub_c_pos
  have h_sqrt_pos' : Real.sqrt (1 - c') > 0 := Real.sqrt_pos.mpr h_one_sub_c'_pos
  have h_sqrt_inv_eq : Real.sqrt (1 / (1 - c')) = (Real.sqrt (1 - c'))⁻¹ := by
    calc
      Real.sqrt (1 / (1 - c')) = Real.sqrt ((1 - c')⁻¹) := by norm_num
      _ = (Real.sqrt (1 - c'))⁻¹ := Real.sqrt_inv _
  have h_s1_le_inv : s1 ≤ (Real.sqrt (1 - c'))⁻¹ := by
    rw [← h_sqrt_inv_eq]
    exact hs1_le
  have h_inv_lt : (Real.sqrt (1 - c'))⁻¹ < s1 + tp := by
    rw [← h_sqrt_inv_eq]
    exact hs1_lt
  have h_first : |s1 - (Real.sqrt (1 - c'))⁻¹| ≤ tp := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_s1_le_inv)]
    linarith
  have h_sqrt_diff_eq : (Real.sqrt (1 - c'))⁻¹ - (Real.sqrt (1 - c))⁻¹ =
      (c' - c) / ((Real.sqrt (1 - c) + Real.sqrt (1 - c')) * Real.sqrt (1 - c) * Real.sqrt (1 - c')) := by
    field_simp [h_sqrt_pos.ne', h_sqrt_pos'.ne']
    nlinarith [Real.sq_sqrt h_one_sub_c_nonneg, Real.sq_sqrt h_one_sub_c'_nonneg]
  have h_denom_pos : 0 < (Real.sqrt (1 - c) + Real.sqrt (1 - c')) * Real.sqrt (1 - c) * Real.sqrt (1 - c') := by
    positivity
  have h_sqrt_ge : (1 : ℝ) - 2 / 10 ^ 30 ≤ Real.sqrt ((1 : ℝ) - 2 / 10 ^ 30) := by
    have h_sq : ((1 : ℝ) - 2 / 10 ^ 30) ^ 2 ≤ (1 : ℝ) - 2 / 10 ^ 30 := by
      have hpos : 0 ≤ 2 / 10 ^ 30 := by positivity
      have hle1 : 2 / 10 ^ 30 ≤ 1 := by norm_num
      nlinarith
    have h_nonneg : 0 ≤ (1 : ℝ) - 2 / 10 ^ 30 := by norm_num
    exact Real.le_sqrt_of_sq_le h_sq
  have h_sqrt_c_ge : 1 - 2 / 10 ^ 30 ≤ Real.sqrt (1 - c) := by
    have : 1 - 2 / 10 ^ 30 ≤ 1 - c := by linarith
    have h := Real.sqrt_le_sqrt this
    linarith
  have h_sqrt_c'_ge : 1 - 2 / 10 ^ 30 ≤ Real.sqrt (1 - c') := by
    have : 1 - 2 / 10 ^ 30 ≤ 1 - c' := by linarith
    have h := Real.sqrt_le_sqrt this
    linarith
  have h_denom_ge_one : 1 ≤ (Real.sqrt (1 - c) + Real.sqrt (1 - c')) * Real.sqrt (1 - c) * Real.sqrt (1 - c') := by
    have h_sum_ge : 2 * (1 - 2 / 10 ^ 30) ≤ Real.sqrt (1 - c) + Real.sqrt (1 - c') := by linarith
    have h_prod_ge : (1 - 2 / 10 ^ 30) ^ 2 ≤ Real.sqrt (1 - c) * Real.sqrt (1 - c') := by
      have h_nonneg_sqrt_c : 0 ≤ Real.sqrt (1 - c) := Real.sqrt_nonneg _
      have h_nonneg_sqrt_c' : 0 ≤ Real.sqrt (1 - c') := Real.sqrt_nonneg _
      have h_nonneg_val : 0 ≤ 1 - 2 / 10 ^ 30 := by norm_num
      -- Use the fact that if 0 ≤ a ≤ A and 0 ≤ b ≤ B, then a*b ≤ A*B
      -- But we need (1-2e)^2 ≤ √(1-c) * √(1-c'), which follows from √(1-c) ≥ 1-2e and √(1-c') ≥ 1-2e
      -- Since both sides are nonnegative, we can multiply the inequalities
      nlinarith
    have h_lower : (2 * (1 - 2 / 10 ^ 30)) * (1 - 2 / 10 ^ 30) ^ 2 ≤
        (Real.sqrt (1 - c) + Real.sqrt (1 - c')) * Real.sqrt (1 - c) * Real.sqrt (1 - c') := by
      nlinarith
    have h_num_ge_one : 1 ≤ (2 * (1 - 2 / 10 ^ 30)) * (1 - 2 / 10 ^ 30) ^ 2 := by
      norm_num
    linarith
  have h_second : |(Real.sqrt (1 - c'))⁻¹ - (Real.sqrt (1 - c))⁻¹| ≤ Δ := by
    rw [h_sqrt_diff_eq]
    rw [abs_div, abs_of_pos h_denom_pos]
    refine (div_le_self (abs_nonneg _) h_denom_ge_one).trans hcc
  calc
    |s1 - (Real.sqrt (1 - c))⁻¹| = |(s1 - (Real.sqrt (1 - c'))⁻¹) + ((Real.sqrt (1 - c'))⁻¹ - (Real.sqrt (1 - c))⁻¹)| := by ring_nf
    _ ≤ |s1 - (Real.sqrt (1 - c'))⁻¹| + |(Real.sqrt (1 - c'))⁻¹ - (Real.sqrt (1 - c))⁻¹| := abs_add_le _ _
    _ ≤ tp + Δ := by linarith

theorem e3_scal_sqrt (c c' Δ cb X1 tp s3 : ℝ) (hc : |c| ≤ cb) (hcc : |c' - c| ≤ Δ)
    (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 1000)
    (hs3 : s3 ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < s3 + tp) :
    |s3 - Real.sqrt (1 - c)| ≤ tp + Δ := by
  rcases hs3 with ⟨hs3_le, hs3_lt⟩
  -- First term bound: |s3 - √(1-c')| ≤ tp
  have h_first : |s3 - Real.sqrt (1 - c')| ≤ tp := by
    rw [abs_of_nonpos (sub_nonpos.mpr hs3_le)]
    linarith
  -- Nonnegativity of 1-c and 1-c'
  have hX1sq_nonneg : 0 ≤ X1 ^ 2 := pow_two_nonneg _
  have hcb_le : cb ≤ 1 / 10 ^ 30 := by nlinarith
  have hΔ_le : Δ ≤ 1 / 10 ^ 30 := by nlinarith
  have hc_lower : -cb ≤ c := by
    have := abs_le.mp hc
    exact this.1
  have hc_upper : c ≤ cb := by
    have := abs_le.mp hc
    exact this.2
  have hc'_lower : -cb - Δ ≤ c' := by
    have h := abs_le.mp hcc
    nlinarith
  have hc'_upper : c' ≤ cb + Δ := by
    have h := abs_le.mp hcc
    nlinarith
  have h_nonneg_c : 0 ≤ 1 - c := by nlinarith
  have h_nonneg_c' : 0 ≤ 1 - c' := by nlinarith
  -- Key identity: (√(1-c') - √(1-c)) * (√(1-c') + √(1-c)) = c - c'
  have h_sqrt_diff_mul_sum : (Real.sqrt (1 - c') - Real.sqrt (1 - c)) * (Real.sqrt (1 - c') + Real.sqrt (1 - c)) = c - c' := by
    calc
      (Real.sqrt (1 - c') - Real.sqrt (1 - c)) * (Real.sqrt (1 - c') + Real.sqrt (1 - c))
          = (Real.sqrt (1 - c')) ^ 2 - (Real.sqrt (1 - c)) ^ 2 := by ring
      _ = (1 - c') - (1 - c) := by rw [Real.sq_sqrt h_nonneg_c', Real.sq_sqrt h_nonneg_c]
      _ = c - c' := by ring
  have h_sum_nonneg : 0 ≤ Real.sqrt (1 - c') + Real.sqrt (1 - c) := by
    have h1 : 0 ≤ Real.sqrt (1 - c') := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (1 - c) := Real.sqrt_nonneg _
    nlinarith
  -- |√(1-c') - √(1-c)| * (√(1-c') + √(1-c)) = |c' - c|
  have h_abs_eq : |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * (Real.sqrt (1 - c') + Real.sqrt (1 - c)) = |c' - c| := by
    calc
      |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * (Real.sqrt (1 - c') + Real.sqrt (1 - c))
          = |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * |Real.sqrt (1 - c') + Real.sqrt (1 - c)| := by
            rw [abs_of_nonneg h_sum_nonneg]
      _ = |(Real.sqrt (1 - c') - Real.sqrt (1 - c)) * (Real.sqrt (1 - c') + Real.sqrt (1 - c))| := by
            rw [abs_mul]
      _ = |c - c'| := by rw [h_sqrt_diff_mul_sum]
      _ = |c' - c| := by rw [abs_sub_comm]
  -- √(1-c') + √(1-c) ≥ 1
  have h_sum_ge_one : 1 ≤ Real.sqrt (1 - c') + Real.sqrt (1 - c) := by
    have h_sqrt1_ge_half : 1/2 ≤ Real.sqrt (1 - 1 / 10 ^ 30) := by
      rw [Real.le_sqrt]
      · have hpos : (0 : ℝ) < 10 ^ 30 := by norm_num
        nlinarith
      · norm_num
      · have h : (1 : ℝ) / (10 : ℝ) ^ 30 ≤ 1 := by
          refine (div_le_one ?_).mpr ?_
          · refine pow_pos (by norm_num : 0 < (10 : ℝ)) 30
          · norm_num
        linarith
    have h_sqrt2_ge_half : 1/2 ≤ Real.sqrt (1 - 2 / 10 ^ 30) := by
      rw [Real.le_sqrt]
      · have hpos : (0 : ℝ) < 10 ^ 30 := by norm_num
        nlinarith
      · have h : (2 : ℝ) / (10 : ℝ) ^ 30 ≤ 1 := by
          refine (div_le_one ?_).mpr ?_
          · refine pow_pos (by norm_num : 0 < (10 : ℝ)) 30
          · nlinarith
        linarith
      · have h : (2 : ℝ) / (10 : ℝ) ^ 30 ≤ 1 := by
          refine (div_le_one ?_).mpr ?_
          · refine pow_pos (by norm_num : 0 < (10 : ℝ)) 30
          · nlinarith
        linarith
    have h_one_minus_c_ge : 1 - 1 / 10 ^ 30 ≤ 1 - c := by nlinarith
    have h_one_minus_c'_ge : 1 - 2 / 10 ^ 30 ≤ 1 - c' := by nlinarith
    have h_sqrt_c_ge_half : 1/2 ≤ Real.sqrt (1 - c) := by
      calc
        1/2 ≤ Real.sqrt (1 - 1 / 10 ^ 30) := h_sqrt1_ge_half
        _ ≤ Real.sqrt (1 - c) := Real.sqrt_le_sqrt h_one_minus_c_ge
    have h_sqrt_c'_ge_half : 1/2 ≤ Real.sqrt (1 - c') := by
      calc
        1/2 ≤ Real.sqrt (1 - 2 / 10 ^ 30) := h_sqrt2_ge_half
        _ ≤ Real.sqrt (1 - c') := Real.sqrt_le_sqrt h_one_minus_c'_ge
    nlinarith
  -- Second term bound: |√(1-c') - √(1-c)| ≤ Δ
  have h_second : |Real.sqrt (1 - c') - Real.sqrt (1 - c)| ≤ Δ := by
    have h_mul_le : |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * (Real.sqrt (1 - c') + Real.sqrt (1 - c)) ≤ Δ := by
      rw [h_abs_eq]
      exact hcc
    have h_mul_one_le : |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * 1 ≤ Δ := by
      calc
        |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * 1 ≤
            |Real.sqrt (1 - c') - Real.sqrt (1 - c)| * (Real.sqrt (1 - c') + Real.sqrt (1 - c)) := by
          apply mul_le_mul_of_nonneg_left h_sum_ge_one (abs_nonneg _)
        _ ≤ Δ := h_mul_le
    simpa [mul_one] using h_mul_one_le
  -- Triangle inequality
  have h_triangle : |s3 - Real.sqrt (1 - c)| ≤ |s3 - Real.sqrt (1 - c')| + |Real.sqrt (1 - c') - Real.sqrt (1 - c)| := by
    calc
      |s3 - Real.sqrt (1 - c)| = |(s3 - Real.sqrt (1 - c')) + (Real.sqrt (1 - c') - Real.sqrt (1 - c))| := by ring
      _ ≤ |s3 - Real.sqrt (1 - c')| + |Real.sqrt (1 - c') - Real.sqrt (1 - c)| := abs_add_le _ _
  nlinarith

/-- The quotient step of E3: from `|s - c'/D2| ≤ tp/2` and the two denominators close, `|s - c/D|`. -/
theorem e3_core (c c' Δ cb tp Dq D D2 M s : ℝ) (hc : |c| ≤ cb) (hcc : |c' - c| ≤ Δ) (hcb : cb ≤ 1 / 10 ^ 30)
    (htp0 : 0 ≤ tp) (hDq : 0 ≤ Dq) (hD : 0 < D) (hD2 : 19 / 10 ≤ D2) (hM : M ≤ D * D2)
    (hDD : |D - D2| ≤ M * (2 * tp + Δ + Dq)) (hs : |s - c' / D2| ≤ tp / 2) :
    |s - c / D| ≤ 51 / 100 * tp + Δ + cb * Dq := by
  have hcb0 : 0 ≤ cb := (abs_nonneg c).trans hc
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hcc
  have hD2p : 0 < D2 := by linarith
  have hDD2 : 0 < D * D2 := mul_pos hD hD2p
  have hT : 0 ≤ 2 * tp + Δ + Dq := by linarith
  have e : c' / D2 - c / D = (c' - c) / D2 + c * (D - D2) / (D * D2) := by
    field_simp
    ring
  have h1 : |(c' - c) / D2| ≤ 10 / 19 * Δ := by
    rw [abs_div, abs_of_pos hD2p, div_le_iff₀ hD2p]
    nlinarith
  have h2 : |c * (D - D2) / (D * D2)| ≤ cb * (2 * tp + Δ + Dq) := by
    rw [abs_div, abs_mul, abs_of_pos hDD2, div_le_iff₀ hDD2]
    have hM0 : 0 ≤ M * (2 * tp + Δ + Dq) := (abs_nonneg _).trans hDD
    calc |c| * |D - D2| ≤ cb * (M * (2 * tp + Δ + Dq)) := mul_le_mul hc hDD (abs_nonneg _) hcb0
      _ ≤ cb * (2 * tp + Δ + Dq) * (D * D2) := by
        have := mul_le_mul_of_nonneg_left hM (mul_nonneg hcb0 hT)
        nlinarith
  have h3 : |s - c / D| ≤ |s - c' / D2| + |c' / D2 - c / D| := abs_sub_le _ _ _
  have h4 : |c' / D2 - c / D| ≤ |(c' - c) / D2| + |c * (D - D2) / (D * D2)| := by
    rw [e]; exact abs_add_le _ _
  have h5 : cb * tp ≤ 1 / 200 * tp := by nlinarith
  have h6 : cb * Δ ≤ 9 / 19 * Δ := by nlinarith
  nlinarith

/-- `|√x - √y| ≤ |x - y|` when `√x + √y ≥ 1`. -/
theorem sqrt_sub_abs_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : 1 ≤ Real.sqrt x + Real.sqrt y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    rw [show (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = Real.sqrt x ^ 2 - Real.sqrt y ^ 2 by ring,
      Real.sq_sqrt hx, Real.sq_sqrt hy]
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt x + Real.sqrt y)]
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

/-- The root of a number within `10⁻²⁹` of `1` lies in `[0.99, 1.01]`. -/
theorem sqrt_near_one (x : ℝ) (hx : |x - 1| ≤ 1 / 10 ^ 29) :
    99 / 100 ≤ Real.sqrt x ∧ Real.sqrt x ≤ 101 / 100 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  have e1 : (99 / 100 : ℝ) = Real.sqrt ((99 / 100) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have e2 : (101 / 100 : ℝ) = Real.sqrt ((101 / 100) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  constructor
  · rw [e1]; exact Real.sqrt_le_sqrt (by norm_num at h1 ⊢; linarith)
  · rw [e2]; exact Real.sqrt_le_sqrt (by norm_num at h2 ⊢; linarith)

/-- The four radicands of E3 lie within `10⁻²⁹` of `1`. -/
theorem e3_near (c c' Δ cb X1 xx xx' : ℝ) (hc : |c| ≤ cb) (hcc : |c' - c| ≤ Δ)
    (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hxx : 0 ≤ xx)
    (hxx1 : xx ≤ X1 ^ 2) (hxx' : 0 ≤ xx') (hxx1' : xx' ≤ X1 ^ 2) :
    cb ≤ 1 / 10 ^ 30 ∧ |(1 - c) - 1| ≤ 1 / 10 ^ 29 ∧ |(1 - c') - 1| ≤ 1 / 10 ^ 29 ∧
      |(1 - c + c * xx) - 1| ≤ 1 / 10 ^ 29 ∧ |(1 - c' + c' * xx') - 1| ≤ 1 / 10 ^ 29 := by
  have hcb0 : 0 ≤ cb := (abs_nonneg c).trans hc
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans hcc
  have hX : 0 ≤ X1 ^ 2 := sq_nonneg _
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  obtain ⟨hd1, hd2⟩ := abs_le.1 hcc
  have k1 : cb ≤ 1 / 10 ^ 30 := by nlinarith
  have k2 : Δ ≤ 1 / 10 ^ 30 := by nlinarith
  have hp : (1 : ℝ) / 10 ^ 30 * 5 ≤ 1 / 10 ^ 29 := by norm_num
  have m1 : (cb - c) * xx ≥ 0 := mul_nonneg (by linarith) hxx
  have m2 : (cb + c) * xx ≥ 0 := mul_nonneg (by linarith) hxx
  have m3 : cb * xx ≤ cb * X1 ^ 2 := mul_le_mul_of_nonneg_left hxx1 hcb0
  have m4 : (cb + Δ - c') * xx' ≥ 0 := mul_nonneg (by linarith) hxx'
  have m5 : (cb + Δ + c') * xx' ≥ 0 := mul_nonneg (by linarith) hxx'
  have m6 : (cb + Δ) * xx' ≤ (cb + Δ) * X1 ^ 2 := mul_le_mul_of_nonneg_left hxx1' (by linarith)
  refine ⟨k1, abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by nlinarith, by nlinarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

/-- A Lipschitz bound of `(x, y) ↦ x y (x + y)` on `[0.98, 1.02]²`. -/
theorem f3_lip (x y u w : ℝ) (hx : 98 / 100 ≤ x) (hx' : x ≤ 102 / 100) (hy : 98 / 100 ≤ y) (hy' : y ≤ 102 / 100)
    (hu : 98 / 100 ≤ u) (hu' : u ≤ 102 / 100) (hw : 98 / 100 ≤ w) (hw' : w ≤ 102 / 100) :
    |x * y * (x + y) - u * w * (u + w)| ≤ 16 / 5 * (|x - u| + |y - w|) := by
  have e : x * y * (x + y) - u * w * (u + w) = (x - u) * ((x + u) * y + y ^ 2) + (y - w) * (u ^ 2 + u * (y + w)) := by
    ring
  have hA0 : 0 ≤ (x + u) * y + y ^ 2 := by positivity
  have hA : (x + u) * y + y ^ 2 ≤ 16 / 5 := by nlinarith
  have hB0 : 0 ≤ u ^ 2 + u * (y + w) := by positivity
  have hB : u ^ 2 + u * (y + w) ≤ 16 / 5 := by nlinarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hB0]
  nlinarith [abs_nonneg (x - u), abs_nonneg (y - w)]

/-- The roots of E3 at BL's precision: `√a, √q` and BL's `s3, rq` with their errors. -/
theorem e3_roots (c c' Δ cb X1 tp xx xx' Dq s3 rq : ℝ) (hc : |c| ≤ cb)
    (hcc : |c' - c| ≤ Δ) (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30)
    (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 1000) (hxx : 0 ≤ xx) (hxx1 : xx ≤ X1 ^ 2) (hxx' : 0 ≤ xx') (hxx1' : xx' ≤ X1 ^ 2)
    (hDq : |(1 - c' + c' * xx') - (1 - c + c * xx)| ≤ Dq)
    (hs3 : s3 ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < s3 + tp)
    (hrq : rq ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < rq + tp) :
    cb ≤ 1 / 10 ^ 30 ∧ 0 ≤ Dq ∧
      99 / 100 ≤ Real.sqrt (1 - c) ∧ Real.sqrt (1 - c) ≤ 101 / 100 ∧
      99 / 100 ≤ Real.sqrt (1 - c + c * xx) ∧ Real.sqrt (1 - c + c * xx) ≤ 101 / 100 ∧
      989 / 1000 ≤ s3 ∧ s3 ≤ 101 / 100 ∧ 989 / 1000 ≤ rq ∧ rq ≤ 101 / 100 ∧
      |Real.sqrt (1 - c) - s3| ≤ tp + Δ ∧ |Real.sqrt (1 - c + c * xx) - rq| ≤ tp + Dq := by
  obtain ⟨k1, ha, ha2, hq, hq2⟩ := e3_near c c' Δ cb X1 xx xx' hc hcc hcb hΔ hxx hxx1 hxx' hxx1'
  have hDq0 : 0 ≤ Dq := (abs_nonneg _).trans hDq
  obtain ⟨ra1, ra2⟩ := sqrt_near_one _ ha
  obtain ⟨rb1, rb2⟩ := sqrt_near_one _ ha2
  obtain ⟨rq1, rq2⟩ := sqrt_near_one _ hq
  obtain ⟨rr1, rr2⟩ := sqrt_near_one _ hq2
  have nn : ∀ z : ℝ, |z - 1| ≤ 1 / 10 ^ 29 → 0 ≤ z := fun z hz => by
    have := (abs_le.1 hz).1; norm_num at this; linarith
  have da : |Real.sqrt (1 - c) - Real.sqrt (1 - c')| ≤ Δ := by
    refine (sqrt_sub_abs_le _ _ (nn _ ha) (nn _ ha2) (by linarith)).trans ?_
    rw [show 1 - c - (1 - c') = c' - c by ring]; exact hcc
  have dq : |Real.sqrt (1 - c + c * xx) - Real.sqrt (1 - c' + c' * xx')| ≤ Dq := by
    refine (sqrt_sub_abs_le _ _ (nn _ hq) (nn _ hq2) (by linarith)).trans ?_
    rw [abs_sub_comm]; exact hDq
  have t1 : |Real.sqrt (1 - c') - s3| ≤ tp := abs_le.2 ⟨by linarith [hs3.1], by linarith [hs3.2]⟩
  have t2 : |Real.sqrt (1 - c' + c' * xx') - rq| ≤ tp := abs_le.2 ⟨by linarith [hrq.1], by linarith [hrq.2]⟩
  refine ⟨k1, hDq0, ra1, ra2, rq1, rq2, by linarith [hs3.2], by linarith [hs3.1], by linarith [hrq.2],
    by linarith [hrq.1], ?_, ?_⟩
  · calc |Real.sqrt (1 - c) - s3| ≤ |Real.sqrt (1 - c) - Real.sqrt (1 - c')| + |Real.sqrt (1 - c') - s3| :=
          abs_sub_le _ _ _
      _ ≤ tp + Δ := by linarith
  · calc |Real.sqrt (1 - c + c * xx) - rq| ≤
          |Real.sqrt (1 - c + c * xx) - Real.sqrt (1 - c' + c' * xx')| + |Real.sqrt (1 - c' + c' * xx') - rq| :=
          abs_sub_le _ _ _
      _ ≤ tp + Dq := by linarith

theorem e3_scal_phi (c c' Δ cb X1 tp xx xx' Dq s3 rq s2 : ℝ) (hc : |c| ≤ cb)
    (hcc : |c' - c| ≤ Δ) (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30)
    (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 1000) (hxx : 0 ≤ xx) (hxx1 : xx ≤ X1 ^ 2) (hxx' : 0 ≤ xx') (hxx1' : xx' ≤ X1 ^ 2)
    (hDq : |(1 - c' + c' * xx') - (1 - c + c * xx)| ≤ Dq)
    (hs3 : s3 ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < s3 + tp)
    (hrq : rq ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < rq + tp)
    (hs2 : |s2 - c' / (s3 * rq * (s3 + rq))| ≤ tp / 2) :
    |s2 - c / (Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)))| ≤
      51 / 100 * tp + Δ + cb * Dq := by
  obtain ⟨k1, hDq0, a1, a2, q1, q2, s1, s2', r1, r2, ea, eq⟩ :=
    e3_roots c c' Δ cb X1 tp xx xx' Dq s3 rq hc hcc hcb hΔ htp0 htp hxx hxx1 hxx' hxx1' hDq hs3 hrq
  set x := Real.sqrt (1 - c)
  set y := Real.sqrt (1 - c + c * xx)
  have hD : 0 < x * y * (x + y) := by positivity
  have hD2 : 19 / 10 ≤ s3 * rq * (s3 + rq) := by
    have h2 : 989 / 1000 * (989 / 1000) ≤ s3 * rq := mul_le_mul s1 r1 (by norm_num) (by linarith)
    have h3 : 1978 / 1000 ≤ s3 + rq := by linarith
    nlinarith [mul_le_mul h2 h3 (by norm_num) (by positivity)]
  have hM : 16 / 5 ≤ x * y * (x + y) * (s3 * rq * (s3 + rq)) := by
    have : 99 / 100 * (99 / 100) ≤ x * y := mul_le_mul a1 q1 (by norm_num) (by linarith)
    have : 99 / 100 * (99 / 100) * (198 / 100) ≤ x * y * (x + y) :=
      mul_le_mul this (by linarith) (by norm_num) (by positivity)
    nlinarith [mul_le_mul this hD2 (by norm_num) (by positivity)]
  have hDD : |x * y * (x + y) - s3 * rq * (s3 + rq)| ≤ 16 / 5 * (2 * tp + Δ + Dq) := by
    refine (f3_lip x y s3 rq (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)).trans ?_
    nlinarith
  exact e3_core c c' Δ cb tp Dq _ _ _ s2 hc hcc k1 htp0 hDq0 hD hD2 hM hDD hs2

theorem e3_scal_psi (c c' Δ cb X1 tp xx xx' Dq s3 rq s4 : ℝ) (hc : |c| ≤ cb)
    (hcc : |c' - c| ≤ Δ) (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30) (hΔ : Δ * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30)
    (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 1000) (hxx : 0 ≤ xx) (hxx1 : xx ≤ X1 ^ 2) (hxx' : 0 ≤ xx') (hxx1' : xx' ≤ X1 ^ 2)
    (hDq : |(1 - c' + c' * xx') - (1 - c + c * xx)| ≤ Dq)
    (hs3 : s3 ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < s3 + tp)
    (hrq : rq ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < rq + tp)
    (hs4 : |s4 - c' / (s3 + rq)| ≤ tp / 2) :
    |s4 - c / (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx))| ≤ 51 / 100 * tp + Δ + cb * Dq := by
  obtain ⟨k1, hDq0, a1, a2, q1, q2, s1, s2', r1, r2, ea, eq⟩ :=
    e3_roots c c' Δ cb X1 tp xx xx' Dq s3 rq hc hcc hcb hΔ htp0 htp hxx hxx1 hxx' hxx1' hDq hs3 hrq
  have hD : 0 < Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) := by linarith
  have hD2 : 19 / 10 ≤ s3 + rq := by linarith
  have hM : 1 ≤ (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)) * (s3 + rq) := by nlinarith
  have hDD : |Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) - (s3 + rq)| ≤ 1 * (2 * tp + Δ + Dq) := by
    have e : Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) - (s3 + rq) =
        (Real.sqrt (1 - c) - s3) + (Real.sqrt (1 - c + c * xx) - rq) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  exact e3_core c c' Δ cb tp Dq _ _ _ s4 hc hcc k1 htp0 hDq0 hD hD2 hM hDD hs4

theorem e3_coef_le (c cb X1 xx : ℝ) (hc : |c| ≤ cb) (hcb : cb * (1 + X1 ^ 2) ≤ 1 / 10 ^ 30)
    (hxx : 0 ≤ xx) (hxx1 : xx ≤ X1 ^ 2) :
    |c / (Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)))| ≤ cb ∧
      |c / (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx))| ≤ cb := by
  have hX1_sq_nonneg : 0 ≤ X1 ^ 2 := sq_nonneg X1
  have h_one_plus_xx_nonneg : 0 ≤ 1 + xx := by nlinarith
  have h_one_plus_X1_sq_nonneg : 0 ≤ 1 + X1 ^ 2 := by nlinarith
  have hcb_nonneg : 0 ≤ cb := by
    have h_abs := abs_nonneg c
    nlinarith
  have hcb_le_ε : cb ≤ 1 / 10 ^ 30 := by
    have h_one_le : 1 ≤ 1 + X1 ^ 2 := by nlinarith
    nlinarith
  have hc_abs_le_ε : |c| ≤ 1 / 10 ^ 30 := by
    nlinarith
  have hc_xx_abs_le_ε : |c * xx| ≤ 1 / 10 ^ 30 := by
    have hxx_abs : |xx| = xx := abs_of_nonneg hxx
    have hxx_le_X1_sq : xx ≤ X1 ^ 2 := hxx1
    have h_abs_mul : |c * xx| = |c| * |xx| := abs_mul c xx
    rw [h_abs_mul, hxx_abs]
    have h1 : |c| * xx ≤ cb * X1 ^ 2 := by
      nlinarith
    have h2 : cb * X1 ^ 2 ≤ 1 / 10 ^ 30 := by
      nlinarith
    nlinarith
  have hc_range : -(1 / 10 ^ 30) ≤ c ∧ c ≤ 1 / 10 ^ 30 := by
    exact abs_le.mp hc_abs_le_ε
  have hc_xx_range : -(1 / 10 ^ 30) ≤ c * xx ∧ c * xx ≤ 1 / 10 ^ 30 := by
    exact abs_le.mp hc_xx_abs_le_ε
  have h_radicand1_nonneg : 0 ≤ 1 - c := by
    nlinarith
  have h_radicand2_nonneg : 0 ≤ 1 - c + c * xx := by
    nlinarith
  have h_radicand1_ge_099 : 0.99 ≤ 1 - c := by
    nlinarith
  have h_radicand2_ge_099 : 0.99 ≤ 1 - c + c * xx := by
    nlinarith
  have h_sqrt1_ge_099 : 0.99 ≤ Real.sqrt (1 - c) := by
    rw [Real.le_sqrt (by norm_num : 0 ≤ (0.99 : ℝ)) h_radicand1_nonneg]
    have h_sq : (0.99 : ℝ) ^ 2 = 0.9801 := by norm_num
    rw [h_sq]
    nlinarith
  have h_sqrt2_ge_099 : 0.99 ≤ Real.sqrt (1 - c + c * xx) := by
    rw [Real.le_sqrt (by norm_num : 0 ≤ (0.99 : ℝ)) h_radicand2_nonneg]
    have h_sq : (0.99 : ℝ) ^ 2 = 0.9801 := by norm_num
    rw [h_sq]
    nlinarith
  have h_denom1_nonneg : 0 ≤ Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)) := by
    positivity
  have h_denom2_nonneg : 0 ≤ Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) := by
    positivity
  have h_denom1_ge_one : 1 ≤ Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)) := by
    have h_prod_ge : (0.99 : ℝ) * 0.99 ≤ Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) := by
      nlinarith
    have h_sum_ge : (0.99 : ℝ) + 0.99 ≤ Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) := by
      nlinarith
    have h_prod_sum : (0.99 : ℝ) * 0.99 * ((0.99 : ℝ) + 0.99) ≤
        Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)) := by
      nlinarith
    have h_bound : 1 ≤ (0.99 : ℝ) * 0.99 * ((0.99 : ℝ) + 0.99) := by norm_num
    nlinarith
  have h_denom2_ge_one : 1 ≤ Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx) := by
    nlinarith
  have h_abs_c_nonneg : 0 ≤ |c| := abs_nonneg c
  have h_first : |c / (Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)))| ≤ cb := by
    rw [abs_div, abs_of_nonneg h_denom1_nonneg]
    have h_div_le : |c| / (Real.sqrt (1 - c) * Real.sqrt (1 - c + c * xx) * (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx))) ≤ |c| := by
      refine (div_le_self ?_ h_denom1_ge_one).trans_eq ?_
      · exact h_abs_c_nonneg
      · rfl
    nlinarith
  have h_second : |c / (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx))| ≤ cb := by
    rw [abs_div, abs_of_nonneg h_denom2_nonneg]
    have h_div_le : |c| / (Real.sqrt (1 - c) + Real.sqrt (1 - c + c * xx)) ≤ |c| := by
      refine (div_le_self ?_ h_denom2_ge_one).trans_eq ?_
      · exact h_abs_c_nonneg
      · rfl
    nlinarith
  exact And.intro h_first h_second

set_option maxHeartbeats 800000 in
theorem e3_mat {d : ℕ} (ξ ξ' : Fin d → ℝ) (s1 s2 n1 n2 X1 ex e1 e2 cb : ℝ)
    (hξ : oNorm ξ ≤ X1) (hξ' : oNorm ξ' ≤ X1) (hdx : oNorm (ξ' - ξ) ≤ ex) (h1 : |s1 - n1| ≤ e1) (h2 : |s2 - n2| ≤ e2)
    (hn2 : |n2| ≤ cb) :
    opN ((s1 • (1 : Matrix (Fin d) (Fin d) ℝ) + s2 • vecMulVec ξ' ξ') -
        (n1 • (1 : Matrix (Fin d) (Fin d) ℝ) + n2 • vecMulVec ξ ξ)) ≤
      e1 + e2 * X1 ^ 2 + cb * (2 * X1) * ex := by
  have hX1 : 0 ≤ X1 := by
    have h := oNorm_nonneg ξ
    linarith
  have he1 : 0 ≤ e1 := by
    have h := abs_nonneg (s1 - n1)
    linarith
  have he2 : 0 ≤ e2 := by
    have h := abs_nonneg (s2 - n2)
    linarith
  have hcb : 0 ≤ cb := by
    have h := abs_nonneg n2
    linarith
  have h_diff : (s1 • (1 : Matrix (Fin d) (Fin d) ℝ) + s2 • vecMulVec ξ' ξ') -
      (n1 • (1 : Matrix (Fin d) (Fin d) ℝ) + n2 • vecMulVec ξ ξ) =
      (s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ' +
      n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [h_diff]
  have h_tri1 : opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ' +
      n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) ≤
      opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ') +
      opN (n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) :=
    opN_add_le _ _
  have h_tri2 : opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ') ≤
      opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ)) + opN ((s2 - n2) • vecMulVec ξ' ξ') :=
    opN_add_le _ _
  have h_smul1 : opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ)) = |s1 - n1| * opN (1 : Matrix (Fin d) (Fin d) ℝ) :=
    opN_smul _ _
  have h_smul2 : opN ((s2 - n2) • vecMulVec ξ' ξ') = |s2 - n2| * opN (vecMulVec ξ' ξ') :=
    opN_smul _ _
  have h_smul3 : opN (n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) = |n2| * opN (vecMulVec ξ' ξ' - vecMulVec ξ ξ) :=
    opN_smul _ _
  have h_one : opN (1 : Matrix (Fin d) (Fin d) ℝ) ≤ 1 := opN_one_le
  have h_vec : opN (vecMulVec ξ' ξ') ≤ oNorm ξ' * oNorm ξ' := opN_vecMulVec_le _ _
  have h_diff_vec : opN (vecMulVec ξ' ξ' - vecMulVec ξ ξ) ≤ (oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ) :=
    vecMulVec_diff _ _
  have h_abs_s1n1 : 0 ≤ |s1 - n1| := abs_nonneg _
  have h_abs_s2n2 : 0 ≤ |s2 - n2| := abs_nonneg _
  have h_abs_n2 : 0 ≤ |n2| := abs_nonneg _
  have h_oξ'_nonneg : 0 ≤ oNorm ξ' := oNorm_nonneg _
  have h_oξ_nonneg : 0 ≤ oNorm ξ := oNorm_nonneg _
  have h_diff_nonneg : 0 ≤ oNorm (ξ' - ξ) := oNorm_nonneg _
  -- Step 1: apply triangle inequalities and smul to bound opN of the matrix sum
  have h_step1 : opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ' +
      n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) ≤
      (|s1 - n1| * opN (1 : Matrix (Fin d) (Fin d) ℝ) + |s2 - n2| * opN (vecMulVec ξ' ξ')) +
      |n2| * opN (vecMulVec ξ' ξ' - vecMulVec ξ ξ) := by
    have h_intermediate : opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ) + (s2 - n2) • vecMulVec ξ' ξ') +
        opN (n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) ≤
        (opN ((s1 - n1) • (1 : Matrix (Fin d) (Fin d) ℝ)) + opN ((s2 - n2) • vecMulVec ξ' ξ')) +
        opN (n2 • (vecMulVec ξ' ξ' - vecMulVec ξ ξ)) :=
      add_le_add h_tri2 (le_refl _)
    refine le_trans h_tri1 ?_
    refine le_trans h_intermediate ?_
    rw [h_smul1, h_smul2, h_smul3]
  -- Step 2: bound each opN term by oNorm products
  have h_step2 : (|s1 - n1| * opN (1 : Matrix (Fin d) (Fin d) ℝ) + |s2 - n2| * opN (vecMulVec ξ' ξ')) +
      |n2| * opN (vecMulVec ξ' ξ' - vecMulVec ξ ξ) ≤
      (|s1 - n1| * 1 + |s2 - n2| * (oNorm ξ' * oNorm ξ')) + |n2| * ((oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ)) := by
    have h1' : |s1 - n1| * opN (1 : Matrix (Fin d) (Fin d) ℝ) ≤ |s1 - n1| * 1 :=
      mul_le_mul_of_nonneg_left h_one h_abs_s1n1
    have h2' : |s2 - n2| * opN (vecMulVec ξ' ξ') ≤ |s2 - n2| * (oNorm ξ' * oNorm ξ') :=
      mul_le_mul_of_nonneg_left h_vec h_abs_s2n2
    have h3' : |n2| * opN (vecMulVec ξ' ξ' - vecMulVec ξ ξ) ≤ |n2| * ((oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ)) :=
      mul_le_mul_of_nonneg_left h_diff_vec h_abs_n2
    nlinarith
  -- Step 3: bound using the given hypotheses
  have h_step3 : (|s1 - n1| * 1 + |s2 - n2| * (oNorm ξ' * oNorm ξ')) + |n2| * ((oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ)) ≤
      (e1 * 1 + e2 * (X1 * X1)) + cb * ((X1 + X1) * ex) := by
    have h_ex : 0 ≤ ex := by
      have h := oNorm_nonneg (ξ' - ξ)
      linarith
    have h_prod : oNorm ξ' * oNorm ξ' ≤ X1 * X1 :=
      mul_le_mul hξ' hξ' h_oξ'_nonneg hX1
    have h_sum : oNorm ξ' + oNorm ξ ≤ X1 + X1 :=
      add_le_add hξ' hξ
    have h_prod2 : (oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ) ≤ (X1 + X1) * ex :=
      mul_le_mul h_sum hdx h_diff_nonneg (add_nonneg hX1 hX1)
    have h_term1 : |s1 - n1| * 1 ≤ e1 * 1 :=
      mul_le_mul_of_nonneg_right h1 (by norm_num)
    have h_term2 : |s2 - n2| * (oNorm ξ' * oNorm ξ') ≤ e2 * (X1 * X1) :=
      mul_le_mul h2 h_prod (mul_nonneg h_oξ'_nonneg h_oξ'_nonneg) he2
    have h_term3 : |n2| * ((oNorm ξ' + oNorm ξ) * oNorm (ξ' - ξ)) ≤ cb * ((X1 + X1) * ex) :=
      mul_le_mul hn2 h_prod2 (mul_nonneg (add_nonneg h_oξ'_nonneg h_oξ_nonneg) h_diff_nonneg) hcb
    have h_sum12 : |s1 - n1| * 1 + |s2 - n2| * (oNorm ξ' * oNorm ξ') ≤ e1 * 1 + e2 * (X1 * X1) :=
      add_le_add h_term1 h_term2
    exact add_le_add h_sum12 h_term3
  -- Step 4: ring normalization
  have h_step4 : (e1 * 1 + e2 * (X1 * X1)) + cb * ((X1 + X1) * ex) = e1 + e2 * X1 ^ 2 + cb * (2 * X1) * ex := by
    ring
  -- Combine all steps
  apply le_trans h_step1
  apply le_trans h_step2
  apply le_trans h_step3
  rw [h_step4]

theorem frob_mul_le {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, ∑ j, ((M * N) i j) ^ 2 ≤ opN M ^ 2 * ∑ i, ∑ j, (N i j) ^ 2 := by
  have h_mulVec_eq (j : Fin d) : ∀ i, (M * N) i j = (M.mulVec (fun k => N k j)) i := by
    intro i
    rw [Matrix.mul_apply, Matrix.mulVec_apply]
    simp [dotProduct]
  calc
    ∑ i, ∑ j, ((M * N) i j) ^ 2
        = ∑ j, ∑ i, ((M * N) i j) ^ 2 := by rw [Finset.sum_comm]
    _ ≤ ∑ j, (opN M ^ 2 * ∑ i, (N i j) ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc
        ∑ i, ((M * N) i j) ^ 2
            = ∑ i, ((M.mulVec (fun k => N k j)) i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [h_mulVec_eq j i]
        _ = oNorm (M.mulVec (fun k => N k j)) ^ 2 := by
          rw [oNorm_sq]
          simp [dotProduct, sq]
        _ ≤ (opN M * oNorm (fun k => N k j)) ^ 2 := by
          have hle := oNorm_mulVec_le M (fun k => N k j)
          have hnonneg : 0 ≤ oNorm (M.mulVec (fun k => N k j)) := oNorm_nonneg _
          have hnonneg' : 0 ≤ opN M * oNorm (fun k => N k j) := by
            nlinarith [opN_nonneg M, oNorm_nonneg (fun k => N k j)]
          nlinarith
        _ = opN M ^ 2 * oNorm (fun k => N k j) ^ 2 := by ring
        _ = opN M ^ 2 * (∑ i, (N i j) ^ 2) := by
          rw [oNorm_sq]
          simp [dotProduct, sq]
    _ = opN M ^ 2 * ∑ j, ∑ i, (N i j) ^ 2 := by rw [Finset.mul_sum]
    _ = opN M ^ 2 * ∑ i, ∑ j, (N i j) ^ 2 := by rw [Finset.sum_comm]

theorem frob_le_of {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℝ) (h L : ℝ) (hH : opN H ≤ h)
    (hA : (A * Aᵀ).trace ≤ L) :
    ∑ i, ∑ j, (((1 + H) * A) i j) ^ 2 ≤ (1 + h) ^ 2 * L := by
  have h_trace : (A * Aᵀ).trace = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have h_opN_one_add_H : opN (1 + H) ≤ 1 + h := by
    calc
      opN (1 + H) ≤ opN (1 : Matrix (Fin d) (Fin d) ℝ) + opN H := opN_add_le _ _
      _ ≤ 1 + opN H := by gcongr; exact opN_one_le
      _ ≤ 1 + h := by gcongr
  have h_opN_nonneg : 0 ≤ opN (1 + H) := opN_nonneg _
  calc
    ∑ i : Fin d, ∑ j : Fin d, (((1 + H) * A) i j) ^ 2 ≤ opN (1 + H) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 :=
      frob_mul_le (1 + H) A
    _ ≤ (1 + h) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
      gcongr
    _ = (1 + h) ^ 2 * (A * Aᵀ).trace := by rw [h_trace]
    _ ≤ (1 + h) ^ 2 * L := by gcongr

theorem ybar_real (pip G gv e L Lg ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4)
    (hpip : pip = max 1 (G / (1 - ε))) (hG0 : 0 ≤ G) (hG : G ≤ Real.sqrt L) (hgv0 : 0 ≤ gv) (hgv1 : gv ≤ 1)
    (he : |e| ≤ Real.sqrt Lg) (hLg : 1 / 4 ≤ Lg) (hL : 1 ≤ L) :
    |pip * (gv + e) + 2 * (pip - 1) / ε| ≤
      2 * Real.sqrt L * (1 / 2 + Real.sqrt Lg) + 4 * Real.sqrt L / ε := by
  set s := Real.sqrt L with hs
  set x := Real.sqrt Lg with hx
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hs_one : 1 ≤ s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hL
  have hx_half : 1 / 2 ≤ x := by
    have h_sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by norm_num
    rw [← h_sqrt_quarter]
    exact Real.sqrt_le_sqrt hLg
  have h_one_minus_ε_pos : 0 < 1 - ε := by linarith
  have h_one_minus_ε_ge_three_fourths : 3 / 4 ≤ 1 - ε := by linarith
  have hpip_ge_one : 1 ≤ pip := by
    rw [hpip]
    exact le_max_left _ _
  have hpip_ge_G_div : G / (1 - ε) ≤ pip := by
    rw [hpip]
    exact le_max_right _ _
  have hpip_le_four_thirds_s : pip ≤ (4 / 3) * s := by
    rw [hpip]
    have h1 : (1 : ℝ) ≤ (4 / 3) * s := by
      nlinarith
    have h2 : G / (1 - ε) ≤ (4 / 3) * s := by
      calc
        G / (1 - ε) ≤ s / (1 - ε) := by gcongr
        _ ≤ s / (3 / 4) := by gcongr
        _ = (4 / 3) * s := by ring
    exact max_le h1 h2
  have h_gv_plus_e_abs_le : |gv + e| ≤ 1 + x := by
    calc
      |gv + e| ≤ |gv| + |e| := abs_add_le _ _
      _ = gv + |e| := by rw [abs_of_nonneg hgv0]
      _ ≤ 1 + |e| := by gcongr
      _ ≤ 1 + x := by gcongr
  have h_first_term : |pip * (gv + e)| ≤ s * (1 + 2 * x) := by
    calc
      |pip * (gv + e)| = |pip| * |gv + e| := abs_mul _ _
      _ = pip * |gv + e| := by rw [abs_of_nonneg (by linarith)]
      _ ≤ pip * (1 + x) := by gcongr
      _ ≤ ((4 / 3) * s) * (1 + x) := by gcongr
      _ ≤ s * (1 + 2 * x) := by
        nlinarith
  have h_second_term_nonneg : 0 ≤ 2 * (pip - 1) / ε := by
    have h_nonneg : 0 ≤ pip - 1 := by linarith
    positivity
  have h_second_term : |2 * (pip - 1) / ε| = 2 * (pip - 1) / ε :=
    abs_of_nonneg h_second_term_nonneg
  have h_second_bound : 2 * (pip - 1) / ε ≤ 4 * s / ε := by
    calc
      2 * (pip - 1) / ε ≤ 2 * ((4 / 3) * s - 1) / ε := by gcongr
      _ ≤ 2 * ((4 / 3) * s) / ε := by
        gcongr
        nlinarith
      _ = (8 / 3) * s / ε := by ring
      _ ≤ 4 * s / ε := by
        gcongr
        norm_num
  calc
    |pip * (gv + e) + 2 * (pip - 1) / ε| ≤ |pip * (gv + e)| + |2 * (pip - 1) / ε| := abs_add_le _ _
    _ = |pip * (gv + e)| + (2 * (pip - 1) / ε) := by rw [h_second_term]
    _ ≤ s * (1 + 2 * x) + (2 * (pip - 1) / ε) := by gcongr
    _ ≤ s * (1 + 2 * x) + (4 * s / ε) := by gcongr
    _ = 2 * s * (1 / 2 + x) + 4 * s / ε := by ring
    _ = 2 * Real.sqrt L * (1 / 2 + Real.sqrt Lg) + 4 * Real.sqrt L / ε := by
      simp [hs, hx]

theorem inc_b {d : ℕ} (u' u0 μ : Fin d → ℝ) (P' P0 : Matrix (Fin d) (Fin d) ℝ)
    (c' c0 U U0 Du Pm DP R Δ cb : ℝ) (hu' : oNorm u' ≤ U) (hu0 : oNorm u0 ≤ U0) (hdu : oNorm (u' - u0) ≤ Du)
    (hP' : opN P' ≤ Pm) (hdP : opN (P' - P0) ≤ DP) (hμ : oNorm μ ≤ R) (hc : |c' - c0| ≤ Δ) (hc0 : |c0| ≤ cb) :
    oNorm (c' • ((u' ⬝ᵥ μ) • u' - P' *ᵥ μ) - c0 • ((u0 ⬝ᵥ μ) • u0 - P0 *ᵥ μ)) ≤
      Δ * R * (U ^ 2 + Pm) + cb * R * ((U + U0) * Du + DP) := by
  set X1 := (u' ⬝ᵥ μ) • u' - P' *ᵥ μ with hX1
  set X0 := (u0 ⬝ᵥ μ) • u0 - P0 *ᵥ μ with hX0
  have h_triangle (a b : Fin d → ℝ) : oNorm (a + b) ≤ oNorm a + oNorm b := by
    rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
    rw [WithLp.toLp_add]
    exact norm_add_le _ _
  have h_triangle_sub (a b : Fin d → ℝ) : oNorm (a - b) ≤ oNorm a + oNorm b := by
    rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
    rw [WithLp.toLp_sub]
    exact norm_sub_le _ _
  have h_smul (a : ℝ) (v : Fin d → ℝ) : oNorm (a • v) = |a| * oNorm v := by
    rw [oNorm_eq_norm, oNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  have h_split (a b : ℝ) (x y : Fin d → ℝ) : a • x - b • y = (a - b) • x + b • (x - y) := by
    calc
      a • x - b • y = (a • x - b • x) + (b • x - b • y) := by abel
      _ = (a - b) • x + b • (x - y) := by simp [sub_smul, smul_sub]
  have h_decomp : X1 - X0 = (u' ⬝ᵥ μ) • (u' - u0) + ((u' - u0) ⬝ᵥ μ) • u0 - (P' - P0) *ᵥ μ := by
    dsimp [X1, X0]
    ext i
    simp [Matrix.sub_mulVec, sub_dotProduct]
    ring
  have hU_nonneg : 0 ≤ U := by linarith [oNorm_nonneg u', hu']
  have hU0_nonneg : 0 ≤ U0 := by linarith [oNorm_nonneg u0, hu0]
  have hR_nonneg : 0 ≤ R := by linarith [oNorm_nonneg μ, hμ]
  have hPm_nonneg : 0 ≤ Pm := by
    have h := opN_nonneg P'
    linarith
  have h_bound_X1 : oNorm X1 ≤ R * (U ^ 2 + Pm) := by
    have h_abs : |u' ⬝ᵥ μ| ≤ oNorm u' * oNorm μ := abs_dot_le u' μ
    have h_mulvec : oNorm (P' *ᵥ μ) ≤ opN P' * oNorm μ := oNorm_mulVec_le P' μ
    have h_nonneg_u' : 0 ≤ oNorm u' := oNorm_nonneg _
    have h_nonneg_μ : 0 ≤ oNorm μ := oNorm_nonneg _
    have h_prod_nonneg : 0 ≤ U * R := mul_nonneg hU_nonneg hR_nonneg
    have h_prod : oNorm u' * oNorm μ ≤ U * R :=
      mul_le_mul hu' hμ h_nonneg_μ hU_nonneg
    have h_first : (oNorm u' * oNorm μ) * oNorm u' ≤ (U * R) * U :=
      mul_le_mul h_prod hu' h_nonneg_u' h_prod_nonneg
    have h_second : opN P' * oNorm μ ≤ Pm * R :=
      mul_le_mul hP' hμ h_nonneg_μ hPm_nonneg
    calc
      oNorm X1 = oNorm ((u' ⬝ᵥ μ) • u' - P' *ᵥ μ) := rfl
      _ ≤ oNorm ((u' ⬝ᵥ μ) • u') + oNorm (P' *ᵥ μ) := h_triangle_sub _ _
      _ = |u' ⬝ᵥ μ| * oNorm u' + oNorm (P' *ᵥ μ) := by rw [h_smul]
      _ ≤ (oNorm u' * oNorm μ) * oNorm u' + oNorm (P' *ᵥ μ) := by
        refine add_le_add ?_ (le_refl _)
        exact mul_le_mul_of_nonneg_right h_abs h_nonneg_u'
      _ ≤ (oNorm u' * oNorm μ) * oNorm u' + opN P' * oNorm μ := by
        refine add_le_add (le_refl _) h_mulvec
      _ ≤ (U * R) * U + Pm * R := add_le_add h_first h_second
      _ = R * (U ^ 2 + Pm) := by ring
  have h_bound_X1mX0 : oNorm (X1 - X0) ≤ R * ((U + U0) * Du + DP) := by
    set A := (u' ⬝ᵥ μ) • (u' - u0) with hA
    set B := ((u' - u0) ⬝ᵥ μ) • u0 with hB
    set C := (P' - P0) *ᵥ μ with hC
    have h_abs1 : |u' ⬝ᵥ μ| ≤ oNorm u' * oNorm μ := abs_dot_le u' μ
    have h_abs2 : |(u' - u0) ⬝ᵥ μ| ≤ oNorm (u' - u0) * oNorm μ := abs_dot_le (u' - u0) μ
    have h_mulvec : oNorm C ≤ opN (P' - P0) * oNorm μ := by rw [hC]; exact oNorm_mulVec_le (P' - P0) μ
    have h_nonneg_u' : 0 ≤ oNorm u' := oNorm_nonneg _
    have h_nonneg_u0 : 0 ≤ oNorm u0 := oNorm_nonneg _
    have h_nonneg_μ : 0 ≤ oNorm μ := oNorm_nonneg _
    have h_nonneg_u'_sub_u0 : 0 ≤ oNorm (u' - u0) := oNorm_nonneg _
    have h_nonneg_Du : 0 ≤ Du := by linarith
    have h_nonneg_DP : 0 ≤ DP := by
      have h := opN_nonneg (P' - P0)
      linarith
    have hA_bound : oNorm A ≤ (U * R) * Du := by
      rw [hA]
      have h_first : |u' ⬝ᵥ μ| * oNorm (u' - u0) ≤ (oNorm u' * oNorm μ) * oNorm (u' - u0) :=
        mul_le_mul_of_nonneg_right h_abs1 h_nonneg_u'_sub_u0
      have h_second : (oNorm u' * oNorm μ) * oNorm (u' - u0) ≤ (oNorm u' * oNorm μ) * Du :=
        mul_le_mul_of_nonneg_left hdu (mul_nonneg h_nonneg_u' h_nonneg_μ)
      have h_third : (oNorm u' * oNorm μ) * Du ≤ (U * R) * Du :=
        mul_le_mul_of_nonneg_right (mul_le_mul hu' hμ h_nonneg_μ hU_nonneg) h_nonneg_Du
      calc
        oNorm ((u' ⬝ᵥ μ) • (u' - u0)) = |u' ⬝ᵥ μ| * oNorm (u' - u0) := h_smul _ _
        _ ≤ (oNorm u' * oNorm μ) * oNorm (u' - u0) := h_first
        _ ≤ (oNorm u' * oNorm μ) * Du := h_second
        _ ≤ (U * R) * Du := h_third
    have hB_bound : oNorm B ≤ (Du * R) * U0 := by
      rw [hB]
      have h_first : |(u' - u0) ⬝ᵥ μ| * oNorm u0 ≤ (oNorm (u' - u0) * oNorm μ) * oNorm u0 :=
        mul_le_mul_of_nonneg_right h_abs2 h_nonneg_u0
      have h_second : (oNorm (u' - u0) * oNorm μ) * oNorm u0 ≤ (Du * oNorm μ) * oNorm u0 := by
        gcongr
      have h_third : (Du * oNorm μ) * oNorm u0 ≤ (Du * R) * U0 := by
        have h1 : Du * oNorm μ ≤ Du * R := mul_le_mul_of_nonneg_left hμ h_nonneg_Du
        have h_nonneg_DuR : 0 ≤ Du * R := mul_nonneg h_nonneg_Du hR_nonneg
        exact mul_le_mul h1 hu0 h_nonneg_u0 h_nonneg_DuR
      calc
        oNorm (((u' - u0) ⬝ᵥ μ) • u0) = |(u' - u0) ⬝ᵥ μ| * oNorm u0 := h_smul _ _
        _ ≤ (oNorm (u' - u0) * oNorm μ) * oNorm u0 := h_first
        _ ≤ (Du * oNorm μ) * oNorm u0 := h_second
        _ ≤ (Du * R) * U0 := h_third
    have hC_bound : oNorm C ≤ DP * R := by
      rw [hC]
      calc
        oNorm ((P' - P0) *ᵥ μ) ≤ opN (P' - P0) * oNorm μ := h_mulvec
        _ ≤ DP * R := mul_le_mul hdP hμ h_nonneg_μ h_nonneg_DP
    have h_sum : oNorm A + oNorm B + oNorm C ≤ R * ((U + U0) * Du + DP) := by
      nlinarith
    calc
      oNorm (X1 - X0) = oNorm (A + B - C) := by
        rw [h_decomp, hA, hB, hC]
      _ ≤ oNorm (A + B) + oNorm C := h_triangle_sub _ _
      _ ≤ (oNorm A + oNorm B) + oNorm C := by
        nlinarith [h_triangle A B]
      _ = oNorm A + oNorm B + oNorm C := by ring
      _ ≤ R * ((U + U0) * Du + DP) := h_sum
  have hΔ_nonneg : 0 ≤ Δ := by
    have h_abs_nonneg : 0 ≤ |c' - c0| := abs_nonneg _
    linarith
  have hcb_nonneg : 0 ≤ cb := by
    have h_abs_nonneg : 0 ≤ |c0| := abs_nonneg _
    linarith
  calc
    oNorm (c' • X1 - c0 • X0) = oNorm ((c' - c0) • X1 + c0 • (X1 - X0)) := by
      rw [h_split c' c0 X1 X0]
    _ ≤ oNorm ((c' - c0) • X1) + oNorm (c0 • (X1 - X0)) := h_triangle _ _
    _ = |c' - c0| * oNorm X1 + |c0| * oNorm (X1 - X0) := by simp [h_smul]
    _ ≤ Δ * oNorm X1 + cb * oNorm (X1 - X0) := by
      have hX1_nonneg := oNorm_nonneg X1
      have hX1mX0_nonneg := oNorm_nonneg (X1 - X0)
      nlinarith
    _ ≤ Δ * (R * (U ^ 2 + Pm)) + cb * (R * ((U + U0) * Du + DP)) := by
      have h1 : Δ * oNorm X1 ≤ Δ * (R * (U ^ 2 + Pm)) :=
        mul_le_mul_of_nonneg_left h_bound_X1 hΔ_nonneg
      have h2 : cb * oNorm (X1 - X0) ≤ cb * (R * ((U + U0) * Du + DP)) :=
        mul_le_mul_of_nonneg_left h_bound_X1mX0 hcb_nonneg
      nlinarith
    _ = Δ * R * (U ^ 2 + Pm) + cb * R * ((U + U0) * Du + DP) := by ring

theorem inc_k {d : ℕ} (u' u0 μ : Fin d → ℝ) (P' P0 : Matrix (Fin d) (Fin d) ℝ)
    (c' c0 U U0 Du Pm DP R Δ cb : ℝ) (hu' : oNorm u' ≤ U) (hu0 : oNorm u0 ≤ U0) (hdu : oNorm (u' - u0) ≤ Du)
    (hP' : opN P' ≤ Pm) (hdP : opN (P' - P0) ≤ DP) (hμ : oNorm μ ≤ R) (hc : |c' - c0| ≤ Δ) (hc0 : |c0| ≤ cb) :
    |c' / 2 * ((u' ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P' *ᵥ μ)) - c0 / 2 * ((u0 ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P0 *ᵥ μ))| ≤
      Δ / 2 * R ^ 2 * (U ^ 2 + Pm) + cb / 2 * R ^ 2 * ((U + U0) * Du + DP) := by
  set X1 := (u' ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P' *ᵥ μ) with hX1
  set X0 := (u0 ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P0 *ᵥ μ) with hX0
  have hU : 0 ≤ U := le_trans (oNorm_nonneg u') hu'
  have hU0 : 0 ≤ U0 := le_trans (oNorm_nonneg u0) hu0
  have hR : 0 ≤ R := le_trans (oNorm_nonneg μ) hμ
  have hPm : 0 ≤ Pm := le_trans (opN_nonneg P') hP'
  have hDu : 0 ≤ Du := le_trans (oNorm_nonneg (u' - u0)) hdu
  have hDP : 0 ≤ DP := le_trans (opN_nonneg (P' - P0)) hdP
  have h_sum_norm : oNorm (u' + u0) ≤ U + U0 := by
    have h_tri : oNorm (u' + u0) ≤ oNorm u' + oNorm u0 := by
      rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
      exact norm_add_le _ _
    linarith
  have hX1_bound : |X1| ≤ R ^ 2 * (U ^ 2 + Pm) := by
    rw [hX1]
    have h_sq1 : (u' ⬝ᵥ μ) ^ 2 ≤ (U * R) ^ 2 := by
      have h_dot : |u' ⬝ᵥ μ| ≤ oNorm u' * oNorm μ := abs_dot_le u' μ
      have h_bound : oNorm u' * oNorm μ ≤ U * R := mul_le_mul hu' hμ (oNorm_nonneg μ) hU
      have h_abs : |u' ⬝ᵥ μ| ≤ U * R := le_trans h_dot h_bound
      rcases abs_le.mp h_abs with ⟨hl, hr⟩
      nlinarith
    have h_dot2_abs : |μ ⬝ᵥ (P' *ᵥ μ)| ≤ R * (Pm * R) := by
      have h1 : |μ ⬝ᵥ (P' *ᵥ μ)| ≤ oNorm μ * oNorm (P' *ᵥ μ) := abs_dot_le μ (P' *ᵥ μ)
      have h2 : oNorm (P' *ᵥ μ) ≤ opN P' * oNorm μ := oNorm_mulVec_le P' μ
      have h3 : opN P' * oNorm μ ≤ Pm * oNorm μ := mul_le_mul_of_nonneg_right hP' (oNorm_nonneg μ)
      have h4 : oNorm μ * oNorm (P' *ᵥ μ) ≤ oNorm μ * (Pm * oNorm μ) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3) (oNorm_nonneg μ)
      have h5 : oNorm μ * (Pm * oNorm μ) = oNorm μ * Pm * oNorm μ := by ring
      have h6 : oNorm μ * Pm * oNorm μ ≤ R * (Pm * R) := by
        have hsq : oNorm μ ^ 2 ≤ R ^ 2 := by
          have := mul_self_le_mul_self (oNorm_nonneg μ) hμ
          simpa [pow_two] using this
        nlinarith
      linarith
    have h_tri : |(u' ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P' *ᵥ μ)| ≤ |(u' ⬝ᵥ μ) ^ 2| + |μ ⬝ᵥ (P' *ᵥ μ)| := abs_sub _ _
    have h_sq1_abs : |(u' ⬝ᵥ μ) ^ 2| = (u' ⬝ᵥ μ) ^ 2 := abs_of_nonneg (pow_two_nonneg _)
    have h_sum : (u' ⬝ᵥ μ) ^ 2 + |μ ⬝ᵥ (P' *ᵥ μ)| ≤ (U * R) ^ 2 + R * (Pm * R) := by
      linarith
    have h_rhs : (U * R) ^ 2 + R * (Pm * R) = R ^ 2 * (U ^ 2 + Pm) := by ring
    linarith
  have h_diff_bound : |X1 - X0| ≤ R ^ 2 * ((U + U0) * Du + DP) := by
    rw [hX1, hX0]
    have h_sub_sq : (u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2 = ((u' - u0) ⬝ᵥ μ) * ((u' + u0) ⬝ᵥ μ) := by
      calc
        (u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2 = ((u' ⬝ᵥ μ) - (u0 ⬝ᵥ μ)) * ((u' ⬝ᵥ μ) + (u0 ⬝ᵥ μ)) := by ring
        _ = ((u' - u0) ⬝ᵥ μ) * ((u' + u0) ⬝ᵥ μ) := by simp [sub_dotProduct, add_dotProduct]
    have h_sub_mul : μ ⬝ᵥ (P' *ᵥ μ) - μ ⬝ᵥ (P0 *ᵥ μ) = μ ⬝ᵥ ((P' - P0) *ᵥ μ) := by
      simp [dotProduct_sub, sub_mulVec]
    have h_part1 : |(u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2| ≤ oNorm (u' - u0) * oNorm μ * (oNorm (u' + u0) * oNorm μ) := by
      rw [h_sub_sq]
      calc
        |((u' - u0) ⬝ᵥ μ) * ((u' + u0) ⬝ᵥ μ)| = |(u' - u0) ⬝ᵥ μ| * |(u' + u0) ⬝ᵥ μ| := abs_mul _ _
        _ ≤ (oNorm (u' - u0) * oNorm μ) * (oNorm (u' + u0) * oNorm μ) :=
          mul_le_mul (abs_dot_le _ _) (abs_dot_le _ _) (abs_nonneg _) (mul_nonneg (oNorm_nonneg _) (oNorm_nonneg _))
        _ = oNorm (u' - u0) * oNorm μ * (oNorm (u' + u0) * oNorm μ) := by ring
    have h_part2 : |μ ⬝ᵥ (P' *ᵥ μ) - μ ⬝ᵥ (P0 *ᵥ μ)| ≤ oNorm μ * oNorm ((P' - P0) *ᵥ μ) := by
      rw [h_sub_mul]
      exact abs_dot_le μ ((P' - P0) *ᵥ μ)
    have h_bound_part1 : oNorm (u' - u0) * oNorm μ * (oNorm (u' + u0) * oNorm μ) ≤
        Du * R * ((U + U0) * R) := by
      have hA : oNorm (u' - u0) * oNorm μ ≤ Du * R :=
        mul_le_mul hdu hμ (oNorm_nonneg μ) hDu
      have hB : oNorm (u' + u0) * oNorm μ ≤ (U + U0) * R :=
        mul_le_mul h_sum_norm hμ (oNorm_nonneg μ) (by linarith)
      have h_nonneg_A : 0 ≤ oNorm (u' - u0) * oNorm μ := mul_nonneg (oNorm_nonneg _) (oNorm_nonneg μ)
      have h_nonneg_B : 0 ≤ oNorm (u' + u0) * oNorm μ := mul_nonneg (oNorm_nonneg _) (oNorm_nonneg μ)
      have h_nonneg_DuR : 0 ≤ Du * R := mul_nonneg hDu hR
      have hC : (oNorm (u' - u0) * oNorm μ) * (oNorm (u' + u0) * oNorm μ) ≤ (Du * R) * ((U + U0) * R) :=
        mul_le_mul hA hB h_nonneg_B h_nonneg_DuR
      simpa [mul_assoc] using hC
    have h_bound_part2 : oNorm μ * oNorm ((P' - P0) *ᵥ μ) ≤ R * (DP * R) := by
      have h_mulVec : oNorm ((P' - P0) *ᵥ μ) ≤ opN (P' - P0) * oNorm μ := oNorm_mulVec_le (P' - P0) μ
      have h_opN : opN (P' - P0) * oNorm μ ≤ DP * oNorm μ :=
        mul_le_mul_of_nonneg_right hdP (oNorm_nonneg μ)
      have h1 : oNorm μ * oNorm ((P' - P0) *ᵥ μ) ≤ oNorm μ * (DP * oNorm μ) :=
        mul_le_mul_of_nonneg_left (le_trans h_mulVec h_opN) (oNorm_nonneg μ)
      have h2 : oNorm μ * (DP * oNorm μ) = oNorm μ * DP * oNorm μ := by ring
      have h3 : oNorm μ * DP * oNorm μ ≤ R * (DP * R) := by
        have hsq : oNorm μ ^ 2 ≤ R ^ 2 := by
          have := mul_self_le_mul_self (oNorm_nonneg μ) hμ
          simpa [pow_two] using this
        nlinarith
      linarith
    have h_total : |((u' ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P' *ᵥ μ)) - ((u0 ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P0 *ᵥ μ))| ≤
        oNorm (u' - u0) * oNorm μ * (oNorm (u' + u0) * oNorm μ) + oNorm μ * oNorm ((P' - P0) *ᵥ μ) := by
      have h_expr : ((u' ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P' *ᵥ μ)) - ((u0 ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P0 *ᵥ μ)) =
          ((u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2) - (μ ⬝ᵥ (P' *ᵥ μ) - μ ⬝ᵥ (P0 *ᵥ μ)) := by ring
      rw [h_expr]
      have h_tri : |((u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2) - (μ ⬝ᵥ (P' *ᵥ μ) - μ ⬝ᵥ (P0 *ᵥ μ))| ≤
          |(u' ⬝ᵥ μ) ^ 2 - (u0 ⬝ᵥ μ) ^ 2| + |μ ⬝ᵥ (P' *ᵥ μ) - μ ⬝ᵥ (P0 *ᵥ μ)| := abs_sub _ _
      linarith
    have h_sum : oNorm (u' - u0) * oNorm μ * (oNorm (u' + u0) * oNorm μ) +
        oNorm μ * oNorm ((P' - P0) *ᵥ μ) ≤
        Du * R * ((U + U0) * R) + R * (DP * R) := by
      linarith
    have h_rhs : Du * R * ((U + U0) * R) + R * (DP * R) = R ^ 2 * ((U + U0) * Du + DP) := by ring
    linarith
  have h_main_eq : c' / 2 * X1 - c0 / 2 * X0 = ((c' - c0) / 2) * X1 + (c0 / 2) * (X1 - X0) := by
    ring
  rw [hX1, hX0]
  rw [h_main_eq]
  calc
    |((c' - c0) / 2) * X1 + (c0 / 2) * (X1 - X0)|
        ≤ |((c' - c0) / 2) * X1| + |(c0 / 2) * (X1 - X0)| := abs_add_le _ _
    _ = |(c' - c0) / 2| * |X1| + |c0 / 2| * |X1 - X0| := by simp [abs_mul]
    _ = (|c' - c0| / 2) * |X1| + (|c0| / 2) * |X1 - X0| := by simp [abs_div]
    _ ≤ (Δ / 2) * (R ^ 2 * (U ^ 2 + Pm)) + (cb / 2) * (R ^ 2 * ((U + U0) * Du + DP)) := by
      have hΔ_nonneg : 0 ≤ Δ := le_trans (abs_nonneg (c' - c0)) hc
      have hcb_nonneg : 0 ≤ cb := le_trans (abs_nonneg c0) hc0
      have h1 : (|c' - c0| / 2) * |X1| ≤ (Δ / 2) * (R ^ 2 * (U ^ 2 + Pm)) := by
        have hpos1 : 0 ≤ |c' - c0| / 2 := by positivity
        have hpos2 : 0 ≤ |X1| := abs_nonneg _
        have hpos3 : 0 ≤ Δ / 2 := by linarith
        have h_mul : |c' - c0| / 2 ≤ Δ / 2 := by linarith
        have h_mul2 : |X1| ≤ R ^ 2 * (U ^ 2 + Pm) := hX1_bound
        exact mul_le_mul h_mul h_mul2 hpos2 hpos3
      have h2 : (|c0| / 2) * |X1 - X0| ≤ (cb / 2) * (R ^ 2 * ((U + U0) * Du + DP)) := by
        have hpos1 : 0 ≤ |c0| / 2 := by positivity
        have hpos2 : 0 ≤ |X1 - X0| := abs_nonneg _
        have hpos3 : 0 ≤ cb / 2 := by linarith
        have h_mul : |c0| / 2 ≤ cb / 2 := by linarith
        have h_mul2 : |X1 - X0| ≤ R ^ 2 * ((U + U0) * Du + DP) := h_diff_bound
        exact mul_le_mul h_mul h_mul2 hpos2 hpos3
      linarith
    _ = Δ / 2 * R ^ 2 * (U ^ 2 + Pm) + cb / 2 * R ^ 2 * ((U + U0) * Du + DP) := by ring

end AdversarialBco.Bit.BLP.RC
