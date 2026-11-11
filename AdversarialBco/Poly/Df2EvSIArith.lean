/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The arithmetic of the levels of LQ and DQ

Inequalities between explicit real expressions in `δ = de`, `x = log(1/δ)`, `λ = lam = 1/(725 d (36x)²)`, `ε = eps`,
`R = 134 d (log(2d + 2))^{1/2}`, `k0 = (1 - λ)⁻²`, under `14 + 3 log(d n) ≤ x`, `1/√n ≤ ε ≤ 1/2`, `n δ/λ² ≤ 1`.
The proofs rest on the common facts `arF` and `arQ`.
-/

-- The leaves share one list of hypotheses, so most of them leave some unused.
set_option linter.unusedVariables false

namespace AdversarialBco.Poly.EvSI

/-- The small quantities of the arithmetic leaves. -/
theorem arF (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de)
    (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x) (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) :
    14 ≤ x ∧ 0 < lam ∧ lam ≤ 1 / 1000 ∧ 144 * x * lam ≤ 1 ∧ (d : ℝ) * lam ≤ 1 / 1000 ∧ 0 ≤ R * lam ∧
      R * lam ≤ 1 / 10000 ∧ 1 / eps ≤ n ∧ n * de ≤ lam ^ 2 ∧ de ≤ lam ^ 2 ∧ 1 ≤ k0 ∧ k0 ≤ 21 / 20 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (1 : ℝ) ≤ d * n := by nlinarith
  have hlog : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg hdn
  have hx1 : 14 ≤ x := by linarith
  have hl0 : 0 < lam := by rw [hlam]; positivity
  have hdl : (d : ℝ) * lam * (725 * 1296 * x ^ 2) = 1 := by rw [hlam]; field_simp; ring
  have hdl0 : 0 ≤ (d : ℝ) * lam := by positivity
  have hdlx : (d : ℝ) * lam * x ≤ 1 / (725 * 1296 * 14) := by
    rw [le_div_iff₀ (by norm_num)]
    have : (d : ℝ) * lam * x * (725 * 1296 * 14) ≤ (d : ℝ) * lam * x * (725 * 1296 * x) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith
  have hdls : (d : ℝ) * lam ≤ 1 / 1000 := by
    have : (d : ℝ) * lam * 14 ≤ (d : ℝ) * lam * x := mul_le_mul_of_nonneg_left hx1 hdl0
    have h2 : (1 : ℝ) / (725 * 1296 * 14) ≤ 14 / 1000 := by norm_num
    linarith
  have hld : lam ≤ (d : ℝ) * lam := by nlinarith
  have hls : lam ≤ 1 / 1000 := by linarith
  have hlx : 144 * x * lam ≤ 1 := by
    have : x * lam ≤ (d : ℝ) * lam * x := by nlinarith
    have h2 : (1 : ℝ) / (725 * 1296 * 14) ≤ 1 / 144 := by norm_num
    linarith
  have hL2 : Real.log (2 * d + 2) ≤ x := by
    have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc Real.log (2 * d + 2) ≤ Real.log (4 * (d * n)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 4 + Real.log (d * n) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ x := by linarith
  have hsL : Real.sqrt (Real.log (2 * d + 2)) ≤ x := by
    calc _ ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = x := Real.sqrt_sq (by linarith)
  have hRl0 : 0 ≤ R * lam := by rw [hR]; positivity
  have hRl : R * lam ≤ 1 / 10000 := by
    have e : R * lam = 134 * Real.sqrt (Real.log (2 * d + 2)) * ((d : ℝ) * lam) := by rw [hR]; ring
    rw [e]
    calc _ ≤ 134 * x * ((d : ℝ) * lam) := by gcongr
      _ = 134 * ((d : ℝ) * lam * x) := by ring
      _ ≤ 134 * (1 / (725 * 1296 * 14)) := by gcongr
      _ ≤ 1 / 10000 := by norm_num
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have he1 : 1 ≤ eps * Real.sqrt n := by rwa [div_le_iff₀ hsn] at hepsn
  have hsnn : Real.sqrt n ≤ n := by
    calc Real.sqrt n ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = n := Real.sqrt_sq (by linarith)
  have he : 1 / eps ≤ n := by
    rw [div_le_iff₀ heps0]
    have := mul_le_mul_of_nonneg_left hsnn heps0.le; linarith
  have hnd : n * de ≤ lam ^ 2 := by rwa [div_le_one (by positivity)] at hcnu
  have hde2 : de ≤ lam ^ 2 := by
    have := mul_le_mul_of_nonneg_right hnR hde0.le; linarith
  have hk1 : 1 ≤ k0 := by
    rw [hk0]; exact one_le_inv_iff₀.2 ⟨pow_pos (by linarith) 2, pow_le_one₀ (by linarith) (by linarith)⟩
  have hk2 : k0 ≤ 21 / 20 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 999 / 1000) (by linarith : (999 / 1000 : ℝ) ≤ 1 - lam) 2
    rw [hk0, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num at h ⊢; linarith
  exact ⟨hx1, hl0, hls, hlx, hdls, hRl0, hRl, he, hnd, hde2, hk1, hk2⟩

/-- `λ Q ≤ (1 + 10⁻³)/(72 x λ)`. -/
theorem arQ (de x lam : ℝ) (hde0 : 0 < de) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (hls : lam ≤ 1 / 1000)
    (hlx : 144 * x * lam ≤ 1) (hde2 : de ≤ lam ^ 2) :
    lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) ≤ 1001 / 1000 / (72 * x * lam) := by
  have hx0 : 0 < x := by linarith
  have e1 : lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) =
      ((1 + de) + 2 * de ^ 6 * lam * (72 * x * lam)) / (72 * x * lam) := by field_simp; ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hde1 : de ≤ 1 / 1000000 := by nlinarith
  have hd6 : de ^ 6 ≤ de := pow_le_of_le_one hde0.le (by linarith) (by norm_num)
  have h3 : 2 * de ^ 6 * lam * (72 * x * lam) = de ^ 6 * lam * (144 * x * lam) := by ring
  have h4 : de ^ 6 * lam * (144 * x * lam) ≤ (1 / 1000000) * (1 / 1000) * 1 :=
    mul_le_mul (mul_le_mul (hd6.trans hde1) hls hl0.le (by norm_num)) hlx (by positivity) (by positivity)
  linarith


open scoped ENNReal NNReal Matrix RealInnerProductSpace
open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.EvSI

-- helper lemma for the main inequality
theorem lqC_exp_ineq (x R : ℝ) (hR : R ≤ Real.exp (x / 2) / 4) (hx : 14 ≤ x) :
    1 + 2 * R * (Real.exp x) ^ 4 ≤ (Real.exp x) ^ 5 := by
  have hx_half_ge_7 : 7 ≤ x / 2 := by linarith
  have h_exp_half_ge_128 : 128 ≤ Real.exp (x / 2) := by
    have h_exp_7_ge_128 : 128 ≤ Real.exp 7 := by
      calc
        128 = (2 : ℝ)^7 := by norm_num
        _ ≤ (Real.exp 1)^7 := by
          have h2le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
          have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
          exact pow_le_pow_left₀ h2_nonneg h2le 7
        _ = Real.exp 7 := by
          simp
    have h_exp_mono : Real.exp 7 ≤ Real.exp (x / 2) :=
      Real.exp_le_exp_of_le hx_half_ge_7
    linarith
  have hR_bound : 2 * R * (Real.exp x) ^ 4 ≤ Real.exp (9 * x / 2) / 2 := by
    have htemp : 2 * R ≤ 2 * (Real.exp (x / 2) / 4) := by linarith
    calc
      2 * R * (Real.exp x) ^ 4 ≤ (2 * (Real.exp (x / 2) / 4)) * (Real.exp x) ^ 4 :=
        mul_le_mul_of_nonneg_right htemp (by positivity)
      _ = (Real.exp (x / 2) * (Real.exp x) ^ 4) / 2 := by ring
      _ = (Real.exp (x / 2) * Real.exp (4 * x)) / 2 := by
        rw [show (Real.exp x)^4 = Real.exp (4*x) from by simpa using (Real.exp_nat_mul x 4).symm]
      _ = Real.exp (x / 2 + 4 * x) / 2 := by rw [Real.exp_add]
      _ = Real.exp (9 * x / 2) / 2 := by ring
  have h_main_ineq : 1 + Real.exp (9 * x / 2) / 2 ≤ (Real.exp x) ^ 5 := by
    have h_nonneg_exp : 0 ≤ Real.exp (9 * x / 2) := by positivity
    have h_mul : Real.exp (9 * x / 2) * 128 ≤ Real.exp (9 * x / 2) * Real.exp (x / 2) :=
      mul_le_mul_of_nonneg_left h_exp_half_ge_128 h_nonneg_exp
    have h_sum : Real.exp (9 * x / 2) / 2 + 1 ≤ Real.exp (9 * x / 2) * 128 := by
      have hpos : 1 ≤ Real.exp (9 * x / 2) := by
        have h_nonneg : 0 ≤ 9 * x / 2 := by nlinarith
        exact Real.one_le_exp_iff.mpr h_nonneg
      calc
        Real.exp (9 * x / 2) / 2 + 1 ≤ Real.exp (9 * x / 2) / 2 + Real.exp (9 * x / 2) := by linarith
        _ = Real.exp (9 * x / 2) * (3/2) := by ring
        _ ≤ Real.exp (9 * x / 2) * 128 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    calc
      1 + Real.exp (9 * x / 2) / 2 = Real.exp (9 * x / 2) / 2 + 1 := by ring
      _ ≤ Real.exp (9 * x / 2) * 128 := h_sum
      _ ≤ Real.exp (9 * x / 2) * Real.exp (x / 2) := h_mul
      _ = Real.exp (9 * x / 2 + x / 2) := by rw [Real.exp_add]
      _ = Real.exp (5 * x) := by ring
      _ = (Real.exp x) ^ 5 := by simpa using (Real.exp_nat_mul x 5)
  linarith

theorem lq_card (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (C : ℝ) (hC1 : 1 ≤ C) (hC : C ≤ (1 + 2 * R / de ^ 4) ^ d) :
    Real.log C ≤ 5 * d * x := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hdn_ge_one : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by
    nlinarith
  have hx_ge_14 : 14 ≤ x := by
    have hlog_nonneg : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg hdn_ge_one
    linarith
  have h_exp_x : Real.exp x = 1 / de := by
    rw [hx, Real.exp_log (div_pos (by norm_num) hde0)]
  have hde_eq : de = Real.exp (-x) := by
    calc
      de = (1 / de)⁻¹ := by field_simp
      _ = (Real.exp x)⁻¹ := by rw [h_exp_x]
      _ = Real.exp (-x) := by rw [Real.exp_neg]
  have h_log_dn_le : Real.log ((d : ℝ) * n) ≤ (x - 14) / 3 := by linarith
  have h_log_d_le : Real.log (d : ℝ) ≤ (x - 14) / 3 := by
    have h_log_mul : Real.log ((d : ℝ) * (n : ℝ)) = Real.log (d : ℝ) + Real.log (n : ℝ) :=
      Real.log_mul (by linarith) (by linarith)
    have h_log_n_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
    rw [h_log_mul] at h_log_dn_le
    linarith
  have hd_le_exp : (d : ℝ) ≤ Real.exp ((x - 14) / 3) := by
    rw [← Real.log_le_iff_le_exp (by exact_mod_cast hd_pos)]
    exact h_log_d_le
  have h_log_2d2_le_3d : Real.log (2 * (d : ℝ) + 2) ≤ 3 * (d : ℝ) := by
    have hpos : 0 < 2 * (d : ℝ) + 2 := by nlinarith
    have h := Real.log_le_sub_one_of_pos hpos
    nlinarith
  have h_sqrt_d_le : Real.sqrt (d : ℝ) ≤ Real.exp ((x - 14) / 6) := by
    have h_exp_nonneg : 0 ≤ Real.exp ((x - 14) / 6) := by positivity
    have hd_sq : (d : ℝ) ≤ (Real.exp ((x - 14) / 6)) ^ 2 := by
      calc
        (d : ℝ) ≤ Real.exp ((x - 14) / 3) := hd_le_exp
        _ = Real.exp (((x - 14) / 6) + ((x - 14) / 6)) := by ring
        _ = Real.exp ((x - 14) / 6) * Real.exp ((x - 14) / 6) := by rw [Real.exp_add]
        _ = (Real.exp ((x - 14) / 6)) ^ 2 := by ring
    calc
      Real.sqrt (d : ℝ) ≤ Real.sqrt ((Real.exp ((x - 14) / 6)) ^ 2) :=
        Real.sqrt_le_sqrt hd_sq
      _ = Real.exp ((x - 14) / 6) := Real.sqrt_sq h_exp_nonneg
  have hR_le : R ≤ 134 * Real.sqrt 3 * Real.exp ((x - 14) / 2) := by
    rw [hR]
    have h_sqrt_log_le : Real.sqrt (Real.log (2 * (d : ℝ) + 2)) ≤ Real.sqrt (3 * (d : ℝ)) :=
      Real.sqrt_le_sqrt h_log_2d2_le_3d
    have h_sqrt_3d : Real.sqrt (3 * (d : ℝ)) = Real.sqrt 3 * Real.sqrt (d : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ))]
    calc
      134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))
          ≤ 134 * (d : ℝ) * Real.sqrt (3 * (d : ℝ)) := by nlinarith
      _ = 134 * (d : ℝ) * (Real.sqrt 3 * Real.sqrt (d : ℝ)) := by rw [h_sqrt_3d]
      _ = 134 * Real.sqrt 3 * ((d : ℝ) * Real.sqrt (d : ℝ)) := by ring
      _ ≤ 134 * Real.sqrt 3 * (Real.exp ((x - 14) / 3) * Real.exp ((x - 14) / 6)) := by
        have h_mul : (d : ℝ) * Real.sqrt (d : ℝ) ≤
            Real.exp ((x - 14) / 3) * Real.exp ((x - 14) / 6) := by
          have h_nonneg_sqrt_d : 0 ≤ Real.sqrt (d : ℝ) := by positivity
          have h_nonneg_exp1 : 0 ≤ Real.exp ((x - 14) / 3) := by positivity
          exact mul_le_mul hd_le_exp h_sqrt_d_le h_nonneg_sqrt_d h_nonneg_exp1
        have h_nonneg_sqrt3 : 0 ≤ Real.sqrt 3 := by positivity
        have h_nonneg_d : 0 ≤ (d : ℝ) := by linarith
        nlinarith
      _ = 134 * Real.sqrt 3 * Real.exp ((x - 14) / 2) := by
        rw [← Real.exp_add]
        ring
  have h_numeric : 536 * Real.sqrt 3 ≤ Real.exp 7 := by
    have h_sq_eq : (536 * Real.sqrt 3)^2 = 861888 := by
      calc
        (536 * Real.sqrt 3)^2 = 536^2 * (Real.sqrt 3)^2 := by ring
        _ = 287296 * (Real.sqrt 3)^2 := by norm_num
        _ = 287296 * 3 := by rw [Real.sq_sqrt (show 0 ≤ (3 : ℝ) from by norm_num)]
        _ = 861888 := by norm_num
    have h_lt_sq : 861888 < (Real.exp 7)^2 := by
      have h_exp_one_gt : (27 : ℝ) / 10 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h_pow_gt : ((27 : ℝ) / 10)^14 < (Real.exp 1)^14 :=
        pow_lt_pow_left₀ h_exp_one_gt (by norm_num) (by norm_num : 14 ≠ 0)
      have h_exp_14_eq : (Real.exp 1)^14 = Real.exp 14 := by
        rw [Real.exp_one_pow 14]
        norm_num
      have h_exp_14_eq' : Real.exp 14 = (Real.exp 7)^2 := by
        calc
          Real.exp 14 = Real.exp ((7 : ℝ) + 7) := by norm_num
          _ = Real.exp 7 * Real.exp 7 := by rw [Real.exp_add]
          _ = (Real.exp 7)^2 := by ring
      have h_num : 861888 < ((27 : ℝ) / 10)^14 := by norm_num
      calc
        861888 < ((27 : ℝ) / 10)^14 := h_num
        _ < (Real.exp 1)^14 := h_pow_gt
        _ = Real.exp 14 := h_exp_14_eq
        _ = (Real.exp 7)^2 := h_exp_14_eq'
    have h_sq_lt : (536 * Real.sqrt 3)^2 < (Real.exp 7)^2 := by linarith
    have h_nonneg : 0 ≤ 536 * Real.sqrt 3 := by positivity
    have h_exp_nonneg : 0 ≤ Real.exp 7 := by positivity
    exact ((pow_lt_pow_iff_left₀ h_nonneg h_exp_nonneg (by norm_num : 2 ≠ 0)).mp h_sq_lt).le
  have h_bound_R : 134 * Real.sqrt 3 * Real.exp ((x - 14) / 2) ≤ Real.exp (x / 2) / 4 := by
    have h_exp_identity : Real.exp (x / 2) = Real.exp ((x - 14) / 2) * Real.exp 7 := by
      calc
        Real.exp (x / 2) = Real.exp (((x - 14) / 2) + 7) := by ring
        _ = Real.exp ((x - 14) / 2) * Real.exp 7 := by rw [Real.exp_add]
    rw [h_exp_identity]
    have hpos : 0 ≤ Real.exp ((x - 14) / 2) := by positivity
    have hineq : 134 * Real.sqrt 3 ≤ Real.exp 7 / 4 := by linarith [h_numeric]
    calc
      134 * Real.sqrt 3 * Real.exp ((x - 14) / 2) ≤
          (Real.exp 7 / 4) * Real.exp ((x - 14) / 2) :=
        mul_le_mul_of_nonneg_right hineq hpos
      _ = (Real.exp ((x - 14) / 2) * Real.exp 7) / 4 := by ring
  have hR_le_exp : R ≤ Real.exp (x / 2) / 4 := by
    linarith
  have h_main : 1 + 2 * R / de ^ 4 ≤ (de ^ 5)⁻¹ := by
    rw [hde_eq]
    -- de = exp(-x), so 1/de^4 = (exp x)^4 and (de^5)⁻¹ = (exp x)^5
    have h1 : 2 * R / (Real.exp (-x)) ^ 4 = 2 * R * (Real.exp x) ^ 4 := by
      calc
        2 * R / (Real.exp (-x)) ^ 4 = 2 * R / ((Real.exp x)⁻¹) ^ 4 := by rw [Real.exp_neg]
        _ = 2 * R / ((Real.exp x) ^ 4)⁻¹ := by simp
        _ = 2 * R * ((Real.exp x) ^ 4) := by field_simp
        _ = 2 * R * (Real.exp x) ^ 4 := rfl
    have h2 : ((Real.exp (-x)) ^ 5)⁻¹ = (Real.exp x) ^ 5 := by
      calc
        ((Real.exp (-x)) ^ 5)⁻¹ = (((Real.exp x)⁻¹) ^ 5)⁻¹ := by rw [Real.exp_neg]
        _ = ((Real.exp x) ^ 5)⁻¹⁻¹ := by simp
        _ = (Real.exp x) ^ 5 := by simp
    rw [h1, h2]
    exact lqC_exp_ineq x R hR_le_exp hx_ge_14
  have hC_bound : C ≤ ((de ^ 5)⁻¹) ^ d := by
    apply le_trans hC
    have h_base : 1 + 2 * R / de ^ 4 ≤ (de ^ 5)⁻¹ := h_main
    have h_nonneg_base : 0 ≤ 1 + 2 * R / de ^ 4 := by
      have hR_nonneg : 0 ≤ R := by
        rw [hR]
        positivity
      positivity
    exact pow_le_pow_left₀ h_nonneg_base h_base d
  have h_log_C : Real.log C ≤ Real.log (((de ^ 5)⁻¹) ^ d) :=
    Real.log_le_log (by linarith [hC1]) hC_bound
  have h_log_pow : Real.log (((de ^ 5)⁻¹) ^ d) = (d : ℝ) * Real.log ((de ^ 5)⁻¹) := by
    rw [Real.log_pow]
  have h_log_inv : Real.log ((de ^ 5)⁻¹) = -Real.log (de ^ 5) := by
    rw [Real.log_inv]
  have h_log_de5 : Real.log (de ^ 5) = 5 * Real.log de := by
    rw [Real.log_pow, Nat.cast_ofNat]
  have h_log_de : Real.log de = -x := by
    rw [hde_eq, Real.log_exp]
  calc
    Real.log C ≤ Real.log (((de ^ 5)⁻¹) ^ d) := h_log_C
    _ = d * Real.log ((de ^ 5)⁻¹) := h_log_pow
    _ = d * (-Real.log (de ^ 5)) := by rw [h_log_inv]
    _ = d * (-(5 * Real.log de)) := by rw [h_log_de5]
    _ = d * (-(5 * (-x))) := by rw [h_log_de]
    _ = 5 * d * x := by ring

/-- `W δ² ≤ 10⁻⁴`, the core of the two tails. -/
theorem tailC_core (d n : ℕ) (de x lam eps R : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de)
    (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x) (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hcnu : n * de / lam ^ 2 ≤ 1) :
    (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2 ≤ 1 / 10000 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (1 : ℝ) ≤ d * n := by nlinarith
  have hlog : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg hdn
  have hx1 : 14 ≤ x := by linarith
  have hl0 : 0 < lam := by rw [hlam]; positivity
  -- `d λ (725 · 1296 x²) = 1`
  have hdl : (d : ℝ) * lam * (725 * 1296 * x ^ 2) = 1 := by rw [hlam]; field_simp; ring
  have hdl0 : 0 ≤ (d : ℝ) * lam := by positivity
  have hdlx : (d : ℝ) * lam * x ≤ 1 / (725 * 1296 * 14) := by
    rw [le_div_iff₀ (by norm_num)]
    have : (d : ℝ) * lam * x * (725 * 1296 * 14) ≤ (d : ℝ) * lam * x * (725 * 1296 * x) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith
  have hdls : (d : ℝ) * lam ≤ 1 / 1000 := by
    have : (d : ℝ) * lam * 14 ≤ (d : ℝ) * lam * x := mul_le_mul_of_nonneg_left hx1 hdl0
    have h2 : (1 : ℝ) / (725 * 1296 * 14) ≤ 14 / 1000 := by norm_num
    linarith
  have hls : lam ≤ 1 / 1000 := by
    have : lam ≤ (d : ℝ) * lam := by nlinarith
    linarith
  -- `log(2d + 2) ≤ x`, so `R λ ≤ 134 x d λ`
  have hL2 : Real.log (2 * d + 2) ≤ x := by
    have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc Real.log (2 * d + 2) ≤ Real.log (4 * (d * n)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 4 + Real.log (d * n) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ x := by linarith
  have hsL : Real.sqrt (Real.log (2 * d + 2)) ≤ x := by
    calc _ ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = x := Real.sqrt_sq (by linarith)
  have hRl0 : 0 ≤ R * lam := by rw [hR]; positivity
  have hRl : R * lam ≤ 1 / 10000 := by
    have e : R * lam = 134 * Real.sqrt (Real.log (2 * d + 2)) * ((d : ℝ) * lam) := by rw [hR]; ring
    rw [e]
    calc _ ≤ 134 * x * ((d : ℝ) * lam) := by gcongr
      _ = 134 * ((d : ℝ) * lam * x) := by ring
      _ ≤ 134 * (1 / (725 * 1296 * 14)) := by gcongr
      _ ≤ 1 / 10000 := by norm_num
  -- `1/ε⁴ ≤ n²` and `n δ ≤ λ²`
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have he1 : 1 ≤ eps * Real.sqrt n := by rwa [div_le_iff₀ hsn] at hepsn
  have he4 : 1 / eps ^ 4 ≤ (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ (eps * Real.sqrt n) ^ 4 := one_le_pow₀ he1
    have h2 : (eps * Real.sqrt n) ^ 4 = eps ^ 4 * (n : ℝ) ^ 2 := by
      rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt _), Real.sq_sqrt (by linarith)]
    nlinarith
  have hnd : n * de ≤ lam ^ 2 := by rwa [div_le_one (by positivity)] at hcnu
  have hde2 : de ≤ lam ^ 2 := by nlinarith
  have hnd2 : (n : ℝ) ^ 2 * de ^ 2 ≤ lam ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hnd 2
    rw [mul_pow] at this; nlinarith
  have hde4 : de ^ 2 ≤ lam ^ 4 := by
    have := pow_le_pow_left₀ hde0.le hde2 2
    rw [← pow_mul] at this; exact this
  have hW : (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2 ≤
      72 * lam ^ 4 + 25600 * ((R * lam) ^ 4 + 3 * ((d : ℝ) * lam) ^ 2 * lam ^ 2) := by
    have hA : 0 ≤ R ^ 4 + 3 * (d : ℝ) ^ 2 := by positivity
    have h1 : (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4 * de ^ 2 ≤ (R ^ 4 + 3 * (d : ℝ) ^ 2) * lam ^ 4 := by
      rw [div_eq_mul_one_div, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hA
      calc 1 / eps ^ 4 * de ^ 2 ≤ (n : ℝ) ^ 2 * de ^ 2 := mul_le_mul_of_nonneg_right he4 (by positivity)
        _ ≤ lam ^ 4 := hnd2
    have e : (R ^ 4 + 3 * (d : ℝ) ^ 2) * lam ^ 4 = (R * lam) ^ 4 + 3 * ((d : ℝ) * lam) ^ 2 * lam ^ 2 := by ring
    calc _ = 72 * de ^ 2 + 25600 * ((R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4 * de ^ 2) := by ring
      _ ≤ 72 * lam ^ 4 + 25600 * ((R ^ 4 + 3 * (d : ℝ) ^ 2) * lam ^ 4) := by gcongr
      _ = _ := by rw [e]
  have a1 : lam ^ 4 ≤ (1 / 1000) ^ 4 := pow_le_pow_left₀ hl0.le hls 4
  have a2 : (R * lam) ^ 4 ≤ (1 / 10000) ^ 4 := pow_le_pow_left₀ hRl0 hRl 4
  have a3 : ((d : ℝ) * lam) ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ hdl0 hdls 2
  have a4 : lam ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ hl0.le hls 2
  have a5 : ((d : ℝ) * lam) ^ 2 * lam ^ 2 ≤ (1 / 1000) ^ 2 * (1 / 1000) ^ 2 :=
    mul_le_mul a3 a4 (by positivity) (by positivity)
  norm_num at a1 a2 a5
  linarith

theorem tailC_exp (de x : ℝ) (hde0 : 0 < de) (hx : x = Real.log (1 / de)) : Real.exp (-x) = de := by
  rw [Real.exp_neg, hx, Real.exp_log (by positivity), one_div, inv_inv]

theorem lq_tail (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) :
    Real.sqrt (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * Real.sqrt (Real.sqrt 105 * Real.exp (-(8 * x) / 4)) ≤ 1 := by
  have hc := tailC_core d n de x lam eps R hd hn hde0 hx14 hlam heps0 hepsn hR hcnu
  have he : Real.exp (-(8 * x) / 4) = de ^ 2 := by
    rw [show -(8 * x) / 4 = ((2 : ℕ) : ℝ) * (-x) by push_cast; ring, Real.exp_nat_mul, tailC_exp de x hde0 hx]
  have hW0 : 0 ≤ 72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4 := by positivity
  have h105 : Real.sqrt 105 ≤ 11 :=
    (Real.sqrt_le_sqrt (by norm_num : (105 : ℝ) ≤ 11 ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  rw [he, ← Real.sqrt_mul hW0, ← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  have e : (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * (Real.sqrt 105 * de ^ 2) =
      Real.sqrt 105 * ((72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2) := by ring
  rw [e]
  have h0 : 0 ≤ (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2 := by positivity
  nlinarith [Real.sqrt_nonneg 105]

theorem dq_tail (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) :
    Real.sqrt (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * x) ^ 2) / 4)) ≤ 1 := by
  have hc := tailC_core d n de x lam eps R hd hn hde0 hx14 hlam heps0 hepsn hR hcnu
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg (by nlinarith)
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp (-Real.sqrt ((16 * x) ^ 2) / 4) = de ^ 4 := by
    rw [Real.sqrt_sq (by linarith), show -(16 * x) / 4 = ((4 : ℕ) : ℝ) * (-x) by push_cast; ring,
      Real.exp_nat_mul, tailC_exp de x hde0 hx]
  have hW0 : 0 ≤ 72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4 := by positivity
  have hs : Real.sqrt 2027025 ≤ 1424 :=
    (Real.sqrt_le_sqrt (by norm_num : (2027025 : ℝ) ≤ 1424 ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  have hd2 : de ^ 2 ≤ 1 := pow_le_one₀ hde0.le hde1.le
  rw [he, ← Real.sqrt_mul hW0, ← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  have e : (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * (Real.sqrt 2027025 * de ^ 4) =
      Real.sqrt 2027025 * ((72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2) * de ^ 2 := by ring
  rw [e]
  have h0 : 0 ≤ (72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2 := by positivity
  have h1 : Real.sqrt 2027025 * ((72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2) ≤ 1424 * (1 / 10000) :=
    mul_le_mul hs hc h0 (by norm_num)
  have h2 : 0 ≤ Real.sqrt 2027025 * ((72 + 25600 * (R ^ 4 + 3 * (d : ℝ) ^ 2) / eps ^ 4) * de ^ 2) := by positivity
  nlinarith

theorem lq_V (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    k0 * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (8 * x * (9 * n) + n * T)) ≤ 11 / 10 * n / lam ^ 2 := by
  obtain ⟨hx1, hl0, hls, hlx, -, -, -, -, -, hde2, hk1, hk2⟩ :=
    arF d n de x lam eps R k0 hd hn hde0 hx14 hlam heps0 hepsn hR hk0 hcnu
  have hq := arQ de x lam hde0 hx1 hl0 hls hlx hde2
  have hx0 : 0 < x := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 : 0 ≤ (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 := by positivity
  have e : k0 * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (8 * x * (9 * n) + n * T)) =
      k0 * (lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) * ((72 * x * n + n * T) / lam) := by
    field_simp; ring
  rw [e]
  have h1 : (72 * x * n + n * T) / lam ≤ (72 * x * n + n) / lam :=
    div_le_div_of_nonneg_right (by nlinarith) hl0.le
  calc _ ≤ 21 / 20 * (1001 / 1000 / (72 * x * lam)) * ((72 * x * n + n) / lam) := by
        gcongr
    _ = 21 / 20 * (1001 / 1000) * ((72 * x + 1) / (72 * x)) * (n / lam ^ 2) := by field_simp
    _ ≤ 11 / 10 * (n / lam ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ = 11 / 10 * n / lam ^ 2 := by ring

theorem dq_V (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (lam * k0) ^ 2 * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) ^ 2 * ((16 * x) ^ 2 * (9 * n) + n * T)) ≤ n / lam ^ 2 := by
  obtain ⟨hx1, hl0, hls, hlx, -, -, -, -, -, hde2, hk1, hk2⟩ :=
    arF d n de x lam eps R k0 hd hn hde0 hx14 hlam heps0 hepsn hR hk0 hcnu
  have hq := arQ de x lam hde0 hx1 hl0 hls hlx hde2
  have hx0 : 0 < x := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 : 0 ≤ lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) := by positivity
  have e : (lam * k0) ^ 2 * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) ^ 2 * ((16 * x) ^ 2 * (9 * n) + n * T)) =
      (k0 * (lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6))) ^ 2 * ((16 * x) ^ 2 * (9 * n) + n * T) := by
    ring
  rw [e]
  have h1 : k0 * (lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) ≤ 21 / 20 * (1001 / 1000 / (72 * x * lam)) :=
    mul_le_mul hk2 hq hQ0 (by norm_num)
  have h2 : (k0 * (lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6))) ^ 2 ≤
      (21 / 20 * (1001 / 1000 / (72 * x * lam))) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (16 * x) ^ 2 * (9 * n) + n * T ≤ (16 * x) ^ 2 * (9 * n) + n := by nlinarith
  calc _ ≤ (21 / 20 * (1001 / 1000 / (72 * x * lam))) ^ 2 * ((16 * x) ^ 2 * (9 * n) + n) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (21 / 20 * (1001 / 1000)) ^ 2 * ((2304 * x ^ 2 + 1) / (5184 * x ^ 2)) * (n / lam ^ 2) := by
        field_simp; ring
    _ ≤ 1 * (n / lam ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ = n / lam ^ 2 := by ring

theorem lqd_A (d n : ℕ) (x lam V : ℝ) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (hV : V ≤ 11 / 10 * n / lam ^ 2) :
    3 * Real.sqrt (V * (7 * d * x)) ≤ 1 / 2 * (Real.sqrt (10 * d * n * (36 * x)) / lam) := by
  have hx0 : 0 < x := by linarith
  have hdn : (0 : ℝ) ≤ d * n := by positivity
  have h1 : V * (7 * d * x) ≤ (Real.sqrt (10 * d * n * x) / lam) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    calc V * (7 * d * x) ≤ 11 / 10 * n / lam ^ 2 * (7 * d * x) := mul_le_mul_of_nonneg_right hV (by positivity)
      _ = 77 / 10 * (d * n * x) / lam ^ 2 := by ring
      _ ≤ 10 * (d * n * x) / lam ^ 2 :=
          div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hdn hx0.le]) (by positivity)
      _ = 10 * d * n * x / lam ^ 2 := by ring
  have h2 : Real.sqrt (V * (7 * d * x)) ≤ Real.sqrt (10 * d * n * x) / lam :=
    (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))
  have h3 : Real.sqrt (10 * d * n * (36 * x)) = 6 * Real.sqrt (10 * d * n * x) := by
    rw [show (10 : ℝ) * d * n * (36 * x) = 6 ^ 2 * (10 * d * n * x) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h3]
  have : 0 ≤ Real.sqrt (10 * d * n * x) / lam := by positivity
  calc 3 * Real.sqrt (V * (7 * d * x)) ≤ 3 * (Real.sqrt (10 * d * n * x) / lam) := by gcongr
    _ = 1 / 2 * (6 * Real.sqrt (10 * d * n * x) / lam) := by ring

theorem lqd_S (d : ℕ) (x lam k0 Q : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (hk0 : 0 ≤ k0)
    (hk2 : k0 ≤ 21 / 20) (hQ0 : 0 ≤ Q) (hq : lam * Q ≤ 1001 / 1000 / (72 * x * lam)) :
    Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) * Real.sqrt Q ≤ Real.sqrt d / (3 * lam) := by
  have hx0 : 0 < x := by linarith
  have hQ : Q ≤ 1001 / 1000 / (72 * x * lam ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hq
    nlinarith
  rw [← Real.sqrt_mul hk0, ← Real.sqrt_mul (by positivity)]
  have h1 : k0 * (32 / 9 * d * x) * Q ≤ (Real.sqrt d / (3 * lam)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hdx : (0 : ℝ) ≤ 32 / 9 * d * x := by positivity
    calc k0 * (32 / 9 * d * x) * Q ≤ 21 / 20 * (32 / 9 * d * x) * (1001 / 1000 / (72 * x * lam ^ 2)) := by
          gcongr
      _ = (21 / 20 * (32 / 9) * (1001 / 1000) / 72) * (d / lam ^ 2) := by field_simp
      _ ≤ 1 / 9 * (d / lam ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = d / (3 ^ 2 * lam ^ 2) := by field_simp; ring
  exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))

theorem lqd_R (d : ℕ) (x lam eps R : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (heps0 : 0 < eps)
    (hR0 : 0 ≤ R) (hRl : R * lam ≤ 1 / 10000) :
    8 / eps * (2 * R) ≤ Real.sqrt d * x / (eps * lam) := by
  have hsd : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have e : 8 / eps * (2 * R) = 16 * (R * lam) / (eps * lam) := by field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem lqd_RL (d : ℕ) (x lam eps R S : ℝ) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (heps0 : 0 < eps) (hS0 : 0 ≤ S)
    (hS : S ≤ Real.sqrt d / (3 * lam)) (hR : 8 / eps * (2 * R) ≤ Real.sqrt d * x / (eps * lam)) :
    S * (36 * x / (2 * eps)) + 8 / eps * (2 * R) ≤ 7 * (Real.sqrt d * x / (eps * lam)) := by
  have hx0 : 0 < x := by linarith
  have h1 : S * (36 * x / (2 * eps)) ≤ Real.sqrt d / (3 * lam) * (36 * x / (2 * eps)) :=
    mul_le_mul_of_nonneg_right hS (by positivity)
  have e : Real.sqrt d / (3 * lam) * (36 * x / (2 * eps)) = 6 * (Real.sqrt d * x / (eps * lam)) := by
    field_simp; ring
  linarith

theorem lqd_comb (d n : ℕ) (x lam eps A RL : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (heps0 : 0 < eps)
    (hA : A ≤ 1 / 2 * (Real.sqrt (10 * d * n * (36 * x)) / lam)) (hRL0 : 0 ≤ RL)
    (hRL : RL ≤ 7 * (Real.sqrt d * x / (eps * lam))) :
    A + 2 * RL * (7 * d * x) ≤
      1 / lam * (11 / 20 * Real.sqrt (10 * d * n * (36 * x)) + 13 / 100 * (d * Real.sqrt d) * (36 * x) ^ 2 / eps) := by
  have hx0 : 0 < x := by linarith
  have h1 : 2 * RL * (7 * d * x) ≤ 2 * (7 * (Real.sqrt d * x / (eps * lam))) * (7 * d * x) := by gcongr
  have e1 : 2 * (7 * (Real.sqrt d * x / (eps * lam))) * (7 * d * x) = 98 * (d * Real.sqrt d * x ^ 2 / (eps * lam)) := by
    field_simp; ring
  have e2 : 1 / lam * (11 / 20 * Real.sqrt (10 * d * n * (36 * x)) + 13 / 100 * (d * Real.sqrt d) * (36 * x) ^ 2 / eps) =
      11 / 20 * (Real.sqrt (10 * d * n * (36 * x)) / lam) + 16848 / 100 * (d * Real.sqrt d * x ^ 2 / (eps * lam)) := by
    field_simp; ring
  have hB : 0 ≤ d * Real.sqrt d * x ^ 2 / (eps * lam) := by positivity
  have hC : 0 ≤ Real.sqrt (10 * d * n * (36 * x)) / lam := by positivity
  rw [e2]
  linarith

theorem lq_dev (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ 11 / 10 * n / lam ^ 2) :
    3 * Real.sqrt (V * (7 * d * x)) + 2 * (Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) * Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) *
        (36 * x / (2 * eps)) + 8 / eps * (2 * R)) * (7 * d * x) ≤
      1 / lam * (11 / 20 * Real.sqrt (10 * d * n * (36 * x)) + 13 / 100 * (d * Real.sqrt d) * (36 * x) ^ 2 / eps) := by
  obtain ⟨hx1, hl0, hls, hlx, -, hRl0, hRl, -, -, hde2, hk1, hk2⟩ :=
    arF d n de x lam eps R k0 hd hn hde0 hx14 hlam heps0 hepsn hR hk0 hcnu
  have hq := arQ de x lam hde0 hx1 hl0 hls hlx hde2
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hQ0 : 0 ≤ (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 := by positivity
  have hA := lqd_A d n x lam V hx1 hl0 hV
  have hS := lqd_S d x lam k0 _ hd hx1 hl0 (by linarith) hk2 hQ0 hq
  have hRR := lqd_R d x lam eps R hd hx1 hl0 heps0 hR0 (by nlinarith)
  have hRL := lqd_RL d x lam eps R _ hx1 hl0 heps0 (by positivity) hS hRR
  exact lqd_comb d n x lam eps _ _ hd hx1 hl0 heps0 hA (by positivity) hRL

open scoped ENNReal NNReal Matrix RealInnerProductSpace
open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.EvSI


theorem lqsV_sqrt_helper {d x lam : ℝ} (hd : 1 ≤ d) (hx : 14 ≤ x) (hlam_pos : 0 < lam) :
    Real.sqrt (32 / 9 * d * x) / Real.sqrt (72 * x) = 2 * Real.sqrt d / 9 := by
  have hxpos : 0 < x := by linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hxpos
  have hd_nonneg : 0 ≤ d := by linarith
  have h_nonneg : 0 ≤ 32 / 9 * d * x := by positivity
  have h_nonneg2 : 0 ≤ 72 * x := by positivity
  calc
    Real.sqrt (32 / 9 * d * x) / Real.sqrt (72 * x) = Real.sqrt ((32 / 9 * d * x) / (72 * x)) := by
      rw [Real.sqrt_div h_nonneg _]
    _ = Real.sqrt ((32 / 9 * d) / 72) := by
      congr 1
      field_simp [hxpos.ne.symm]
    _ = Real.sqrt (4 * d / 81) := by ring_nf
    _ = Real.sqrt (4 * d) / Real.sqrt 81 := by rw [Real.sqrt_div (by positivity : 0 ≤ 4 * d) _]
    _ = (Real.sqrt 4 * Real.sqrt d) / 9 := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), show Real.sqrt (81 : ℝ) = 9 by norm_num]
    _ = (2 * Real.sqrt d) / 9 := by norm_num
    _ = 2 * Real.sqrt d / 9 := by ring

theorem lqsV_inner_bound {de x lam : ℝ} (hde0 : 0 < de) (hxpos : 0 < x) (hlam_pos : 0 < lam) :
    1 / (72 * x * lam ^ 2) ≤ (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 := by
  have hpos_denom : 0 ≤ 72 * x * lam ^ 2 := by positivity
  have hnum : (1 : ℝ) ≤ 1 + de := by linarith
  have hdenom_eq : 2 * (36 * x) * lam ^ 2 = 72 * x * lam ^ 2 := by ring
  rw [hdenom_eq]
  have h1 : 1 / (72 * x * lam ^ 2) ≤ (1 + de) / (72 * x * lam ^ 2) :=
    div_le_div_of_nonneg_right hnum hpos_denom
  have h2 : 0 ≤ 2 * de ^ 6 := by positivity
  linarith

theorem lqsV_sqrt_inner_bound {de x lam : ℝ} (hde0 : 0 < de) (hxpos : 0 < x) (hlam_pos : 0 < lam) :
    1 / (lam * Real.sqrt (72 * x)) ≤ Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) := by
  have h_inner := lqsV_inner_bound hde0 hxpos hlam_pos
  have h_sqrt := Real.sqrt_le_sqrt h_inner
  have h_sqrt_div : Real.sqrt (1 / (72 * x * lam ^ 2)) = 1 / (lam * Real.sqrt (72 * x)) := by
    rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)) _, Real.sqrt_one]
    -- Goal: 1 / Real.sqrt (72 * x * lam ^ 2) = 1 / (lam * Real.sqrt (72 * x))
    -- Rewrite both sides as inverses
    rw [one_div, one_div]
    -- Goal: (Real.sqrt (72 * x * lam ^ 2))⁻¹ = (lam * Real.sqrt (72 * x))⁻¹
    -- Need to prove: Real.sqrt (72 * x * lam ^ 2) = lam * Real.sqrt (72 * x)
    have h_eq : Real.sqrt (72 * x * lam ^ 2) = lam * Real.sqrt (72 * x) := by
      calc
        Real.sqrt (72 * x * lam ^ 2) = Real.sqrt ((72 * x) * (lam ^ 2)) := by ring
        _ = Real.sqrt (72 * x) * Real.sqrt (lam ^ 2) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ 72 * x)]
        _ = Real.sqrt (72 * x) * |lam| := by rw [Real.sqrt_sq_eq_abs]
        _ = Real.sqrt (72 * x) * lam := by rw [abs_of_pos hlam_pos]
        _ = lam * Real.sqrt (72 * x) := mul_comm _ _
    rw [h_eq]
  rw [h_sqrt_div] at h_sqrt
  exact h_sqrt

theorem lqsV_lam_lt_one {d x lam : ℝ} (hd : 1 ≤ d) (hx_ge_14 : 14 ≤ x) (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) : lam < 1 := by
  rw [hlam]
  have hdenom : 1 < 725 * d * (36 * x) ^ 2 := by
    have hdpos : 0 < d := by linarith
    have hxpos : 0 < x := by linarith
    have h_sq_pos : 0 < (36 * x) ^ 2 := pow_pos (by nlinarith) 2
    have h : 725 * 1 * (36 * 14) ^ 2 ≤ 725 * d * (36 * x) ^ 2 := by
      nlinarith
    have h_gt_one : 1 < 725 * 1 * (36 * 14) ^ 2 := by norm_num
    nlinarith
  exact (div_lt_one (by positivity)).mpr hdenom

theorem lqsV_A_bound {d n x lam eps de : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hx_ge_14 : 14 ≤ x)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2) (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) :
    112 / lam ≤ Real.sqrt (((1 - lam) ^ 2)⁻¹) * Real.sqrt (32 / 9 * d * x) *
      Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (36 * x / (2 * eps)) := by
  have hlam_pos : 0 < lam := by
    rw [hlam]
    positivity
  have hlam_lt_one : lam < 1 := lqsV_lam_lt_one hd hx_ge_14 hlam
  have h_sqrt_k0_ge_one : 1 ≤ Real.sqrt (((1 - lam) ^ 2)⁻¹) := by
    have h_one_minus_lam_pos : 0 < 1 - lam := by linarith
    have hsq_pos : 0 < (1 - lam) ^ 2 := pow_pos h_one_minus_lam_pos 2
    have hsq_le_one : (1 - lam) ^ 2 ≤ 1 := by
      have h : 1 - lam ≤ 1 := by linarith
      nlinarith
    have hk0_ge_one : 1 ≤ ((1 - lam) ^ 2)⁻¹ := by
      simpa using one_le_one_div hsq_pos hsq_le_one
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (((1 - lam) ^ 2)⁻¹) := Real.sqrt_le_sqrt hk0_ge_one
  have h_sqrt_d_ge_one : 1 ≤ Real.sqrt d := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
  have h_one_div_eps_ge_two : 2 ≤ 1 / eps := by
    have htemp := (one_div_le_one_div (by norm_num : 0 < (1/2 : ℝ)) heps0).mpr heps1
    simpa using htemp
  have h_sqrt_inner := lqsV_sqrt_inner_bound hde0 (by linarith) hlam_pos
  -- Now we need to combine all these bounds
  have hA : 112 / lam ≤ Real.sqrt (((1 - lam) ^ 2)⁻¹) * Real.sqrt (32 / 9 * d * x) *
      Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (36 * x / (2 * eps)) := by
    have h_factor : 36 * x / (2 * eps) = 18 * x / eps := by ring
    rw [h_factor]
    set S := Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) with hS
    set sqrt_k0 := Real.sqrt (((1 - lam) ^ 2)⁻¹) with hsqrt_k0
    set sqrt_32 := Real.sqrt (32 / 9 * d * x) with hsqrt_32
    set sqrt_d := Real.sqrt d with hsqrt_d
    have h_sqrt_32_eq : sqrt_32 = (2 * sqrt_d / 9) * Real.sqrt (72 * x) := by
      rw [hsqrt_32, hsqrt_d]
      have h := lqsV_sqrt_helper hd hx_ge_14 hlam_pos
      have hpos_sqrt : Real.sqrt (72 * x) > 0 := Real.sqrt_pos.mpr (by nlinarith)
      -- h: sqrt(32/9*d*x) / sqrt(72*x) = 2*sqrt(d)/9
      -- Multiply both sides by sqrt(72*x)
      calc
        Real.sqrt (32 / 9 * d * x) = (Real.sqrt (32 / 9 * d * x) / Real.sqrt (72 * x)) * Real.sqrt (72 * x) := by
          field_simp [hpos_sqrt.ne.symm]
        _ = (2 * Real.sqrt d / 9) * Real.sqrt (72 * x) := by rw [h]
    have h_sqrt_72x_S : Real.sqrt (72 * x) * S ≥ 1 / lam := by
      have hxpos' : 0 < x := by linarith
      have hS_bound := lqsV_sqrt_inner_bound hde0 hxpos' hlam_pos
      -- hS_bound: 1/(lam * sqrt(72*x)) ≤ S
      -- So sqrt(72*x) * S ≥ sqrt(72*x) * (1/(lam * sqrt(72*x))) = 1/lam
      have hpos_sqrt_72x : 0 ≤ Real.sqrt (72 * x) := Real.sqrt_nonneg _
      calc
        Real.sqrt (72 * x) * S ≥ Real.sqrt (72 * x) * (1 / (lam * Real.sqrt (72 * x))) :=
          mul_le_mul_of_nonneg_left hS_bound hpos_sqrt_72x
        _ = 1 / lam := by
          have hpos_sqrt : Real.sqrt (72 * x) > 0 := Real.sqrt_pos.mpr (by nlinarith)
          field_simp [ne_of_gt hpos_sqrt, ne_of_gt hlam_pos]
    have h_mul : sqrt_32 * S ≥ (2 * sqrt_d / 9) * (1 / lam) := by
      rw [h_sqrt_32_eq]
      calc
        (2 * sqrt_d / 9) * Real.sqrt (72 * x) * S = (2 * sqrt_d / 9) * (Real.sqrt (72 * x) * S) := by ring
        _ ≥ (2 * sqrt_d / 9) * (1 / lam) :=
          mul_le_mul_of_nonneg_left h_sqrt_72x_S (by positivity)
    have h_main : sqrt_k0 * (sqrt_32 * S) * (18 * x / eps) ≥ 112 / lam := by
      have hX : 0 ≤ sqrt_32 * S * (18 * x / eps) := by positivity
      have hY : 0 ≤ 18 * x / eps := by positivity
      calc
        sqrt_k0 * (sqrt_32 * S) * (18 * x / eps) ≥ 1 * (sqrt_32 * S) * (18 * x / eps) := by
          nlinarith
        _ = sqrt_32 * S * (18 * x / eps) := by ring
        _ ≥ ((2 * sqrt_d / 9) * (1 / lam)) * (18 * x / eps) :=
          mul_le_mul_of_nonneg_right h_mul hY
        _ = (2 * sqrt_d / 9) * (1 / lam) * (18 * x / eps) := by ring
        _ = (4 * sqrt_d * x) / (lam * eps) := by ring
        _ = (4 * sqrt_d * x) / lam * (1 / eps) := by ring
        _ ≥ (4 * 1 * 14) / lam * 2 := by
          have h_nonneg_div : 0 ≤ 4 * sqrt_d * x / lam := by positivity
          have h_nonneg_14_div : 0 ≤ (4 * 1 * 14 : ℝ) / lam := by positivity
          have h_nonneg_1_div_eps : 0 ≤ 1 / eps := by positivity
          have h1 : 4 * sqrt_d * x / lam ≥ 4 * 1 * 14 / lam := by
            -- Since sqrt_d ≥ 1, x ≥ 14, and lam > 0
            have hnum : 4 * sqrt_d * x ≥ 4 * 1 * 14 := by nlinarith
            have hpos_lam : 0 ≤ lam := by linarith
            -- Use: a ≥ b and c > 0 implies a/c ≥ b/c
            -- This is `div_le_div_of_nonneg_right` with reversed arguments
            have := div_le_div_of_nonneg_right hnum hpos_lam
            -- this: (4*sqrt_d*x)/lam ≥ (4*1*14)/lam
            -- Wait, div_le_div_of_nonneg_right hnum hpos_lam gives:
            -- (4*1*14)/lam ≤ (4*sqrt_d*x)/lam
            -- which is what we want
            exact this
          have h2 : 1 / eps ≥ 2 := h_one_div_eps_ge_two
          nlinarith
        _ = 112 / lam := by ring
    -- Now we need to rewrite the goal in terms of sqrt_k0, sqrt_32, S
    -- Goal: 112/lam ≤ sqrt_k0 * sqrt_32 * S * (18*x/eps)
    -- This is exactly h_main (after reassociating multiplication)
    calc
      112 / lam ≤ sqrt_k0 * (sqrt_32 * S) * (18 * x / eps) := h_main
      _ = sqrt_k0 * sqrt_32 * S * (18 * x / eps) := by ring
  exact hA

theorem lq_sqrtV (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ 11 / 10 * n / lam ^ 2) :
    Real.sqrt V ≤ Real.sqrt n * (Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) * Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) *
        (36 * x / (2 * eps)) + 8 / eps * (2 * R)) := by
  -- cast the natural number inequalities to ℝ
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdpos : 0 < (d : ℝ) := by linarith
  have hnpos : 0 < (n : ℝ) := by linarith
  have hprod_ge_one : 1 ≤ (d : ℝ) * (n : ℝ) := by
    nlinarith
  have hxpos : 0 < x := by
    have hlog : 0 ≤ Real.log ((d : ℝ) * (n : ℝ)) := Real.log_nonneg hprod_ge_one
    linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hxpos
  have hx_ge_14 : 14 ≤ x := by
    have hlog_nonneg : 0 ≤ Real.log ((d : ℝ) * (n : ℝ)) := Real.log_nonneg hprod_ge_one
    linarith
  have hlam_pos : 0 < lam := by
    rw [hlam]
    positivity
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
  have hR_nonneg : 0 ≤ R := by
    rw [hR]
    positivity
  have hk0_val : k0 = ((1 - lam) ^ 2)⁻¹ := hk0
  -- Bound sqrt(V) using hV
  have h_sqrtV : Real.sqrt V ≤ Real.sqrt (11/10 * (n : ℝ)) / lam := by
    calc
      Real.sqrt V ≤ Real.sqrt ((11 : ℝ) / 10 * (n : ℝ) / lam ^ 2) := Real.sqrt_le_sqrt hV
      _ = Real.sqrt ((11 : ℝ) / 10 * (n : ℝ)) / Real.sqrt (lam ^ 2) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ (11 : ℝ)/10 * (n : ℝ)) _]
      _ = Real.sqrt ((11 : ℝ) / 10 * (n : ℝ)) / |lam| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt ((11 : ℝ) / 10 * (n : ℝ)) / lam := by rw [abs_of_pos hlam_pos]
  -- Rewrite sqrt(11/10 * n) = sqrt(11/10) * sqrt(n)
  have h_sqrt_mul : Real.sqrt ((11 : ℝ) / 10 * (n : ℝ)) = Real.sqrt ((11 : ℝ) / 10) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (11 : ℝ)/10)]
  rw [h_sqrt_mul] at h_sqrtV
  -- Now h_sqrtV: sqrt(V) ≤ sqrt(11/10) * sqrt(n) / lam
  -- We need: sqrt(V) ≤ sqrt(n) * (A + B)
  -- It suffices to show: sqrt(11/10) * sqrt(n) / lam ≤ sqrt(n) * (A + B)
  -- Since sqrt(n) > 0, divide both sides by sqrt(n):
  -- sqrt(11/10) / lam ≤ A + B
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  -- Actually, n ≥ 1, so sqrt(n) ≥ 1 > 0
  have h_sqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- We'll show that 112/lam ≤ A + B, and sqrt(11/10) ≤ 112
  have h_sqrt_11_10_le_112 : Real.sqrt ((11 : ℝ) / 10) ≤ 112 := by
    -- Square both sides: 11/10 ≤ 112^2 = 12544, which is true
    have h_sq : (Real.sqrt ((11 : ℝ) / 10)) ^ 2 ≤ (112 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (11 : ℝ)/10)]
      norm_num
    have h_nonneg : 0 ≤ Real.sqrt ((11 : ℝ) / 10) := Real.sqrt_nonneg _
    nlinarith
  have h_A_bound : 112 / lam ≤ Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) *
      Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (36 * x / (2 * eps)) := by
    rw [hk0_val]
    exact lqsV_A_bound hd_real hn_real hde0 hx_ge_14 heps0 heps1 hlam
  have h_B_nonneg : 0 ≤ 8 / eps * (2 * R) := by
    positivity
  have h_sum : 112 / lam ≤ Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) *
      Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (36 * x / (2 * eps)) +
      8 / eps * (2 * R) := by
    linarith
  -- Now we have: sqrt(11/10)/lam ≤ 112/lam ≤ A + B
  -- So sqrt(11/10)/lam ≤ A + B
  -- Multiply both sides by sqrt(n):
  -- sqrt(11/10) * sqrt(n) / lam ≤ sqrt(n) * (A + B)
  -- And sqrt(V) ≤ sqrt(11/10) * sqrt(n) / lam from h_sqrtV
  -- So sqrt(V) ≤ sqrt(n) * (A + B)
  calc
    Real.sqrt V ≤ Real.sqrt ((11 : ℝ) / 10) * Real.sqrt (n : ℝ) / lam := h_sqrtV
    _ = Real.sqrt (n : ℝ) * (Real.sqrt ((11 : ℝ) / 10) / lam) := by ring
    _ ≤ Real.sqrt (n : ℝ) * (112 / lam) := by
      have hdiv : Real.sqrt ((11 : ℝ) / 10) / lam ≤ 112 / lam :=
        div_le_div_of_nonneg_right h_sqrt_11_10_le_112 (by positivity)
      apply mul_le_mul_of_nonneg_left hdiv
      exact Real.sqrt_nonneg _
    _ ≤ Real.sqrt (n : ℝ) * (Real.sqrt k0 * Real.sqrt (32 / 9 * d * x) *
        Real.sqrt ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (36 * x / (2 * eps)) +
        8 / eps * (2 * R)) := by
      apply mul_le_mul_of_nonneg_left h_sum
      exact Real.sqrt_nonneg _


theorem dqD_lam (d : ℕ) (x lam : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) :
    0 < lam ∧ 144 * x * lam ≤ 1 ∧ lam ≤ 1 / 100 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl0 : 0 < lam := by rw [hlam]; positivity
  have hlid : lam * (725 * d * (36 * x) ^ 2) = 1 := by rw [hlam]; field_simp
  have h1 : lam * (725 * 1 * (36 * x) ^ 2) ≤ lam * (725 * d * (36 * x) ^ 2) := by gcongr
  have hlx : 144 * x * lam ≤ 1 := by nlinarith
  exact ⟨hl0, hlx, by nlinarith⟩

theorem dqD_q (de x lam : ℝ) (hde0 : 0 < de) (hde1 : de < 1) (hx1 : 14 ≤ x) (hl0 : 0 < lam)
    (hlx : 144 * x * lam ≤ 1) :
    lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) ≤ 1 / (24 * x * lam) := by
  have hx0 : 0 < x := by linarith
  have e1 : lam * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) =
      (1 + de) / (72 * x * lam) + 2 * de ^ 6 * lam := by field_simp; ring
  have h1 : (1 + de) / (72 * x * lam) ≤ 2 / (72 * x * lam) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hd6 : de ^ 6 ≤ 1 := pow_le_one₀ hde0.le hde1.le
  have hd60 : 0 ≤ de ^ 6 := by positivity
  have h2 : 2 * de ^ 6 * lam ≤ 1 / (72 * x * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : 2 * de ^ 6 * lam * (72 * x * lam) = de ^ 6 * lam * (144 * x * lam) := by ring
    rw [h3]
    have h4 : de ^ 6 * lam * (144 * x * lam) ≤ de ^ 6 * lam * 1 :=
      mul_le_mul_of_nonneg_left hlx (by positivity)
    have hlam1 : lam ≤ 1 := by nlinarith
    have h5 : de ^ 6 * lam ≤ 1 * 1 := mul_le_mul hd6 hlam1 hl0.le zero_le_one
    linarith
  rw [e1]
  calc _ ≤ 2 / (72 * x * lam) + 1 / (72 * x * lam) := add_le_add h1 h2
    _ = 1 / (24 * x * lam) := by field_simp; ring

theorem dqD_A (d n : ℕ) (x lam V : ℝ) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (hV : V ≤ n / lam ^ 2) :
    Real.sqrt (V * (7 * d * x)) ≤ x * Real.sqrt (10 * d * n) / lam := by
  have hx0 : 0 < x := by linarith
  have hS : (x * Real.sqrt (10 * d * n) / lam) ^ 2 = 10 * d * n * x ^ 2 / lam ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h1 : V * (7 * d * x) ≤ (x * Real.sqrt (10 * d * n) / lam) ^ 2 := by
    rw [hS]
    have hdn : (0 : ℝ) ≤ d * n := by positivity
    have h7 : 7 * ((d : ℝ) * n) * x ≤ 10 * (d * n) * x ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hdn hx0.le) (show (0 : ℝ) ≤ 10 * x - 7 by linarith)]
    calc V * (7 * d * x) ≤ n / lam ^ 2 * (7 * d * x) := mul_le_mul_of_nonneg_right hV (by positivity)
      _ = 7 * (d * n) * x / lam ^ 2 := by ring
      _ ≤ 10 * (d * n) * x ^ 2 / lam ^ 2 := div_le_div_of_nonneg_right h7 (by positivity)
      _ = 10 * d * n * x ^ 2 / lam ^ 2 := by ring
  calc _ ≤ Real.sqrt ((x * Real.sqrt (10 * d * n) / lam) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

theorem dqD_P1 (d : ℕ) (x lam eps k0 Q : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (heps0 : 0 < eps)
    (hk : k0 ≤ 2) (hQ0 : 0 ≤ Q) (hq : lam * Q ≤ 1 / (24 * x * lam)) :
    36 * x / (2 * eps) * (lam * k0) * (Q * (32 / 9 * d * x + 1)) ≤ 15 / 2 * (d * x / (eps * lam)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by linarith
  have e1 : 36 * x / (2 * eps) * (lam * k0) * (Q * (32 / 9 * d * x + 1)) =
      18 * x / eps * k0 * (lam * Q) * (32 / 9 * d * x + 1) := by ring
  have h5 : 32 / 9 * d * x + 1 ≤ 5 * d * x := by nlinarith
  have hq0 : 0 ≤ lam * Q := by positivity
  rw [e1]
  calc _ ≤ 18 * x / eps * 2 * (1 / (24 * x * lam)) * (5 * d * x) := by
        gcongr
    _ = 15 / 2 * (d * x / (eps * lam)) := by field_simp; ring

theorem dqD_P2 (d : ℕ) (x lam eps Q : ℝ) (hd : 1 ≤ d) (hx1 : 14 ≤ x) (hl0 : 0 < lam) (hl1 : lam ≤ 1 / 100)
    (heps0 : 0 < eps) (hQ0 : 0 ≤ Q) (hq : lam * Q ≤ 1 / (24 * x * lam)) :
    lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * Q ≤ d * x / (eps * lam) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by linarith
  have h1l : (1 - lam)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hq0 : 0 ≤ lam * Q := by positivity
  have e1 : lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * Q =
      8 / eps * (1 - lam)⁻¹ * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * (lam * Q) := by ring
  have ht : 1 / (8 * (36 * x)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hs : Real.sqrt (2 * d * (1 / (8 * (36 * x)))) ≤ d := by
    have h2 : 2 * (d : ℝ) * (1 / (8 * (36 * x))) ≤ (d : ℝ) ^ 2 := by
      have h3 : 2 * (d : ℝ) * (1 / (8 * (36 * x))) ≤ 2 * d * (1 / 2) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      nlinarith
    calc _ ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = d := Real.sqrt_sq (by positivity)
  have h4 : 2 / 3 * (d / (x * eps * lam)) ≤ d * x / (eps * lam) := by
    have e : (d : ℝ) / (x * eps * lam) = (d / (eps * lam)) * x⁻¹ := by field_simp
    have e2 : (d : ℝ) * x / (eps * lam) = (d / (eps * lam)) * x := by ring
    rw [e, e2]
    have hw : 0 ≤ (d : ℝ) / (eps * lam) := by positivity
    have hxi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hxi hw, mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ x by linarith) hw]
  rw [e1]
  calc _ ≤ 8 / eps * 2 * d * (1 / (24 * x * lam)) := by
        gcongr
    _ = 2 / 3 * (d / (x * eps * lam)) := by field_simp; ring
    _ ≤ d * x / (eps * lam) := h4

theorem dq_dev (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ n / lam ^ 2) :
    3 * Real.sqrt (V * (7 * d * x)) + 2 * (36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * d * x + 1)) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) * (7 * d * x) ≤
      36 * x / lam * (Real.sqrt (10 * d * n) + (d : ℝ) ^ 2 * (36 * x) / eps) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg (by nlinarith)
  have hx1 : 14 ≤ x := by linarith
  obtain ⟨hl0, hlx, hl1⟩ := dqD_lam d x lam hd hx1 hlam
  have hk : k0 ≤ 2 := by
    rw [hk0, inv_le_comm₀ (by nlinarith) (by norm_num)]; nlinarith

  have hQ0 : 0 ≤ (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 := by positivity
  have hq := dqD_q de x lam hde0 hde1 hx1 hl0 hlx
  have hP1 := dqD_P1 d x lam eps k0 _ hd hx1 hl0 heps0 hk hQ0 hq
  have hP2 := dqD_P2 d x lam eps _ hd hx1 hl0 hl1 heps0 hQ0 hq
  have hA := dqD_A d n x lam V hx1 hl0 hV
  have hB0 : 0 ≤ (d : ℝ) ^ 2 * x ^ 2 / (eps * lam) := by positivity
  have hA0 : 0 ≤ x * Real.sqrt (10 * d * n) / lam := by positivity
  have hdx : 0 ≤ 7 * (d : ℝ) * x := by positivity
  have hsum : 2 * (36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) *
      (32 / 9 * d * x + 1)) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) *
      ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) * (7 * d * x) ≤
      119 * ((d : ℝ) ^ 2 * x ^ 2 / (eps * lam)) := by
    calc _ ≤ 2 * (15 / 2 * (d * x / (eps * lam)) + d * x / (eps * lam)) * (7 * d * x) := by
          gcongr
      _ = 119 * ((d : ℝ) ^ 2 * x ^ 2 / (eps * lam)) := by field_simp; ring
  have hR : 36 * x / lam * (Real.sqrt (10 * d * n) + (d : ℝ) ^ 2 * (36 * x) / eps) =
      36 * (x * Real.sqrt (10 * d * n) / lam) + 1296 * ((d : ℝ) ^ 2 * x ^ 2 / (eps * lam)) := by
    field_simp; ring
  rw [hR]
  linarith

theorem dq_sqrtV (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ n / lam ^ 2) :
    Real.sqrt V ≤ Real.sqrt n * (36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * d * x + 1)) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) := by
  have hxpos : 0 < x := by
    have h_log_nonneg : 0 ≤ Real.log ((d : ℝ) * n) := by
      have : 1 ≤ (d : ℝ) * n := by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      exact Real.log_nonneg this
    linarith
  have hx_ge_14 : 14 ≤ x := by
    have h_log_nonneg : 0 ≤ Real.log ((d : ℝ) * n) := by
      have : 1 ≤ (d : ℝ) * n := by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      exact Real.log_nonneg this
    linarith
  have hlam_pos : 0 < lam := by
    rw [hlam]
    positivity
  have hlam_lt_one : lam < 1 := by
    rw [hlam]
    refine (div_lt_one ?_).mpr ?_
    · positivity
    · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
  have h_sqrt_V_le : Real.sqrt V ≤ Real.sqrt n / lam := by
    calc
      Real.sqrt V ≤ Real.sqrt (n / lam ^ 2) := Real.sqrt_le_sqrt hV
      _ = Real.sqrt n / Real.sqrt (lam ^ 2) := by
        rw [Real.sqrt_div (show 0 ≤ (n : ℝ) from by exact mod_cast (Nat.zero_le n))]
      _ = Real.sqrt n / lam := by rw [Real.sqrt_sq hlam_pos.le]
  set T1 := 36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * d * x + 1)) with hT1_def
  set T2 := lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) with hT2_def
  have hT2_nonneg : 0 ≤ T2 := by
    rw [hT2_def]
    positivity
  have hT1_ge_one_div_lam : 1 / lam ≤ T1 := by
    rw [hT1_def]
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h_eps_bound : 2 ≤ 1 / eps := by
      have h := (one_div_le_one_div (by norm_num : 0 < (1/2 : ℝ)) heps0).mpr heps1
      have h' : (1 : ℝ) / (1/2) = 2 := by norm_num
      simpa [h'] using h
    have hk0_ge_one : 1 ≤ k0 := by
      rw [hk0]
      have hpos : 0 < (1 - lam)^2 := by positivity
      have hle : (1 - lam)^2 ≤ 1 := by
        have h1 : 0 ≤ 1 - lam := by linarith
        nlinarith
      simpa [one_div] using one_le_one_div hpos hle
    have h_inner_ge : (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 ≥ 1 / (72 * x * lam ^ 2) := by
      have h_term1 : (1 + de) / (2 * (36 * x) * lam ^ 2) ≥ 1 / (72 * x * lam ^ 2) := by
        have : 2 * (36 * x) * lam ^ 2 = 72 * x * lam ^ 2 := by ring
        rw [this]
        have h_denom : 0 < 72 * x * lam ^ 2 := by positivity
        have h_num : (1 : ℝ) ≤ 1 + de := by linarith
        exact div_le_div_of_nonneg_right h_num (by positivity)
      have h_term2 : 0 ≤ 2 * de ^ 6 := by positivity
      linarith
    have h_factor_ge : (32 / 9 * (d : ℝ) * x + 1) ≥ 457/9 := by
      nlinarith
    have hA : 36 * x ≤ 36 * x / (2 * eps) := by
      have h_inv_ge_one : 1 ≤ 1 / (2 * eps) := by
        have : 2 * eps ≤ 1 := by linarith
        exact one_le_one_div (by positivity) this
      have hx_nonneg : 0 ≤ 36 * x := by positivity
      calc
        36 * x = (36 * x) * 1 := by ring
        _ ≤ (36 * x) * (1 / (2 * eps)) := mul_le_mul_of_nonneg_left h_inv_ge_one hx_nonneg
        _ = 36 * x / (2 * eps) := by ring
    have hB : lam ≤ lam * k0 := by
      calc
        lam = lam * 1 := by ring
        _ ≤ lam * k0 := mul_le_mul_of_nonneg_left hk0_ge_one hlam_pos.le
    have hC : 1 / (72 * x * lam ^ 2) ≤ (1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6 := h_inner_ge
    have hD : 457/9 ≤ 32 / 9 * (d : ℝ) * x + 1 := h_factor_ge
    have h_nonneg_36x_div : 0 ≤ 36 * x / (2 * eps) := by positivity
    have h_nonneg_inner' : 0 ≤ 1 / (72 * x * lam ^ 2) := by positivity
    have h_nonneg_factor' : 0 ≤ (457/9 : ℝ) := by norm_num
    have hCD : (1 / (72 * x * lam ^ 2)) * (457/9) ≤
        ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * (d : ℝ) * x + 1) :=
      mul_le_mul hC hD h_nonneg_factor' (by positivity)
    have hAB : (36 * x) * lam ≤ (36 * x / (2 * eps)) * (lam * k0) :=
      mul_le_mul hA hB hlam_pos.le h_nonneg_36x_div
    have h_total : ((36 * x) * lam) * ((1 / (72 * x * lam ^ 2)) * (457/9)) ≤
        ((36 * x / (2 * eps)) * (lam * k0)) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * (d : ℝ) * x + 1)) :=
      mul_le_mul hAB hCD (by positivity) (by positivity)
    have h_simplify : ((36 * x) * lam) * ((1 / (72 * x * lam ^ 2)) * (457/9)) = (36 * 457) / (648 * lam) := by
      field_simp [hxpos.ne.symm, hlam_pos.ne.symm]
      ring
    have h_final : 1 / lam ≤ (36 * 457) / (648 * lam) := by
      have h_eq : (36 * 457) / (648 * lam) = ((457 : ℝ) / 18) / lam := by ring
      rw [h_eq]
      have h_one_le : (1 : ℝ) ≤ (457 : ℝ) / 18 := by norm_num
      exact div_le_div_of_nonneg_right h_one_le hlam_pos.le
    calc
      1 / lam ≤ (36 * 457) / (648 * lam) := h_final
      _ = ((36 * x) * lam) * ((1 / (72 * x * lam ^ 2)) * (457/9)) := by rw [h_simplify]
      _ ≤ ((36 * x / (2 * eps)) * (lam * k0)) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * (d : ℝ) * x + 1)) := h_total
      _ = 36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * d * x + 1)) := by ring
  have h_main : Real.sqrt n / lam ≤ Real.sqrt n * (T1 + T2) := by
    have hpos : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hineq : 1 / lam ≤ T1 + T2 := by linarith
    calc
      Real.sqrt n / lam = Real.sqrt n * (1 / lam) := by field_simp
      _ ≤ Real.sqrt n * (T1 + T2) := mul_le_mul_of_nonneg_left hineq hpos
  calc
    Real.sqrt V ≤ Real.sqrt n / lam := h_sqrt_V_le
    _ ≤ Real.sqrt n * (T1 + T2) := h_main
    _ = Real.sqrt n * (36 * x / (2 * eps) * (lam * k0) * (((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6) * (32 / 9 * d * x + 1)) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x)))) * ((1 + de) / (2 * (36 * x) * lam ^ 2) + 2 * de ^ 6)) := by
      rw [hT1_def, hT2_def]

theorem lq_disc (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) :
    n * (36 * x / (2 * eps) * Real.sqrt k0 * Real.sqrt (32 / 9 * d * x / de) + 8 / eps) * de ^ 4 ≤ 1 := by
  obtain ⟨hx1, hl0, hls, hlx, hdls, hRl0, hRl, he, hnd, hde2, hk1, hk2⟩ :=
    arF d n de x lam eps R k0 hd hn hde0 hx14 hlam heps0 hepsn hR hk0 hcnu
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd3 : de ^ 3 ≤ 1 := pow_le_one₀ hde0.le hde1.le
  have hne : (n : ℝ) * (1 / eps) * de ^ 3 ≤ lam ^ 4 := by
    have h1 : (n : ℝ) * (1 / eps) ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left he (by positivity)
    have h2 : ((n : ℝ) * de) ^ 2 ≤ (lam ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hnd 2
    calc (n : ℝ) * (1 / eps) * de ^ 3 ≤ (n : ℝ) * n * de ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((n : ℝ) * de) ^ 2 * de := by ring
      _ ≤ (lam ^ 2) ^ 2 * 1 := mul_le_mul h2 hde1.le hde0.le (by positivity)
      _ = lam ^ 4 := by ring
  -- `√(32/9 d x/δ) δ⁴ ≤ 2 d x δ³`
  have hs : Real.sqrt (32 / 9 * d * x / de) * de ^ 4 ≤ 2 * d * x * de ^ 3 := by
    have e1 : Real.sqrt (32 / 9 * d * x / de) * de ^ 4 = Real.sqrt (32 / 9 * d * x / de * (de ^ 4) ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e1]
    calc _ ≤ Real.sqrt ((2 * d * x * de ^ 3) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have e2 : 32 / 9 * (d : ℝ) * x / de * (de ^ 4) ^ 2 = 32 / 9 * (d * x) * de ^ 7 := by field_simp
          rw [e2]
          have h6 : (0 : ℝ) ≤ de ^ 6 := by positivity
          have hdx : (1 : ℝ) ≤ d * x := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hde1.le (mul_nonneg (by positivity : (0 : ℝ) ≤ d * x) h6),
            mul_le_mul_of_nonneg_right hdx (mul_nonneg (by positivity : (0 : ℝ) ≤ d * x) h6)]
      _ = 2 * d * x * de ^ 3 := Real.sqrt_sq (by positivity)
  have hk : Real.sqrt k0 ≤ 2 :=
    (Real.sqrt_le_sqrt (by linarith : k0 ≤ 2 ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  have e : n * (36 * x / (2 * eps) * Real.sqrt k0 * Real.sqrt (32 / 9 * d * x / de) + 8 / eps) * de ^ 4 =
      18 * x * Real.sqrt k0 * (Real.sqrt (32 / 9 * d * x / de) * de ^ 4) * ((n : ℝ) * (1 / eps)) +
        8 * ((n : ℝ) * (1 / eps) * de ^ 3) * de := by
    field_simp; ring
  rw [e]
  have hT1 : 18 * x * Real.sqrt k0 * (Real.sqrt (32 / 9 * d * x / de) * de ^ 4) * ((n : ℝ) * (1 / eps)) ≤ 1 / 2 := by
    calc _ ≤ 18 * x * 2 * (2 * d * x * de ^ 3) * ((n : ℝ) * (1 / eps)) := by gcongr
      _ = 72 * (x * x * d) * ((n : ℝ) * (1 / eps) * de ^ 3) := by ring
      _ ≤ 72 * (x * x * d) * lam ^ 4 := by gcongr
      _ = 72 * (144 * x * lam) ^ 2 * ((d : ℝ) * lam) * lam / 144 ^ 2 := by ring
      _ ≤ 72 * 1 ^ 2 * (1 / 1000) * (1 / 1000) / 144 ^ 2 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hT2 : 8 * ((n : ℝ) * (1 / eps) * de ^ 3) * de ≤ 1 / 2 := by
    calc _ ≤ 8 * lam ^ 4 * 1 := by gcongr
      _ ≤ 8 * (1 / 1000) ^ 4 * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  linarith

theorem dq_disc (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) :
    n * (lam * k0 * (36 * x / (2 * eps)) * ((32 / 9 * d * x) / de + de⁻¹) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (d / de)) * (de ^ 4 * (4 * R)) ≤ 1 := by
  obtain ⟨hx1, hl0, hls, hlx, hdls, hRl0, hRl, he, hnd, hde2, hk1, hk2⟩ :=
    arF d n de x lam eps R k0 hd hn hde0 hx14 hlam heps0 hepsn hR hk0 hcnu
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hd3 : de ^ 3 ≤ 1 := pow_le_one₀ hde0.le hde1.le
  -- `(n/ε) δ³ ≤ λ⁴`
  have hne : (n : ℝ) * (1 / eps) * de ^ 3 ≤ lam ^ 4 := by
    have h1 : (n : ℝ) * (1 / eps) ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left he (by positivity)
    have h2 : ((n : ℝ) * de) ^ 2 ≤ (lam ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hnd 2
    calc (n : ℝ) * (1 / eps) * de ^ 3 ≤ (n : ℝ) * n * de ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((n : ℝ) * de) ^ 2 * de := by ring
      _ ≤ (lam ^ 2) ^ 2 * 1 := mul_le_mul h2 hde1.le hde0.le (by positivity)
      _ = lam ^ 4 := by ring
  -- `√(d/δ) δ⁴ ≤ d δ³`
  have hs : Real.sqrt (d / de) * de ^ 4 ≤ d * de ^ 3 := by
    have e1 : Real.sqrt (d / de) * de ^ 4 = Real.sqrt (d / de * (de ^ 4) ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e1]
    calc _ ≤ Real.sqrt (((d : ℝ) * de ^ 3) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have e2 : (d : ℝ) / de * (de ^ 4) ^ 2 = d * de ^ 7 := by field_simp
          rw [e2]
          have : (0 : ℝ) ≤ d * de ^ 6 := by positivity
          nlinarith
      _ = d * de ^ 3 := Real.sqrt_sq (by positivity)
  have hl1 : lam / (1 - lam) ≤ 2 * lam := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have e : n * (lam * k0 * (36 * x / (2 * eps)) * ((32 / 9 * d * x) / de + de⁻¹) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (d / de)) * (de ^ 4 * (4 * R)) =
      72 * k0 * (lam * x) * (32 / 9 * d * x + 1) * R * ((n : ℝ) * (1 / eps) * de ^ 3) +
        32 * (lam / (1 - lam)) * R * ((n : ℝ) * (1 / eps)) * (Real.sqrt (d / de) * de ^ 4) := by
    have : (1 : ℝ) - lam ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  have h5 : 32 / 9 * d * x + 1 ≤ 5 * d * x := by nlinarith
  have hxl : 0 ≤ lam * x := by positivity
  have hT1 : 72 * k0 * (lam * x) * (32 / 9 * d * x + 1) * R * ((n : ℝ) * (1 / eps) * de ^ 3) ≤ 1 / 2 := by
    calc _ ≤ 72 * (21 / 20) * (lam * x) * (5 * d * x) * R * lam ^ 4 := by gcongr
      _ = 378 * (144 * x * lam) ^ 2 * ((d : ℝ) * lam) * (R * lam) * lam / 144 ^ 2 := by ring
      _ ≤ 378 * 1 ^ 2 * (1 / 1000) * (1 / 10000) * (1 / 1000) / 144 ^ 2 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hT2 : 32 * (lam / (1 - lam)) * R * ((n : ℝ) * (1 / eps)) * (Real.sqrt (d / de) * de ^ 4) ≤ 1 / 2 := by
    have hl1' : 0 ≤ lam / (1 - lam) := div_nonneg hl0.le (by linarith)
    calc _ ≤ 32 * (2 * lam) * R * ((n : ℝ) * (1 / eps)) * (d * de ^ 3) := by gcongr
      _ = 64 * (R * lam) * ((d : ℝ) * lam) * ((n : ℝ) * (1 / eps) * de ^ 3) / lam := by field_simp; ring
      _ ≤ 64 * (R * lam) * ((d : ℝ) * lam) * lam ^ 4 / lam := by gcongr
      _ = 64 * (R * lam) * ((d : ℝ) * lam) * lam ^ 3 := by field_simp
      _ ≤ 64 * (1 / 10000) * (1 / 1000) * (1 / 1000) ^ 3 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  linarith

theorem ev_log (d n : ℕ) (de x lam eps R k0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hde0 : 0 < de) (hde1 : de < 1)
    (hx : x = Real.log (1 / de)) (hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ x)
    (hlam : lam = 1 / (725 * d * (36 * x) ^ 2)) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (hepsn : 1 / Real.sqrt n ≤ eps) (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hcnu : n * de / lam ^ 2 ≤ 1) (C M k : ℝ) (hk1 : 1 ≤ k) (hk : k ≤ 21) (hC1 : 1 ≤ C) (hC : Real.log C ≤ 5 * d * x)
    (hM1 : 1 ≤ M) (hM : M ≤ Real.sqrt n) :
    Real.log (4 * (n * C) * M / (de / k)) ≤ 7 * d * x := by
  -- x ≥ 14 (from hx14 and log(d*n) ≥ 0)
  have hx_ge_14 : 14 ≤ x := by
    have h_nonneg : 0 ≤ Real.log ((d : ℝ) * n) :=
      Real.log_nonneg (by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith)
    linarith
  -- log 4 ≤ 2 (since log 4 = 2*log 2 and log 2 ≤ 1)
  have hlog_4_bound : Real.log 4 ≤ 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
    rw [hlog4]
    nlinarith
  -- log 21 ≤ 5 (since exp(5) > 2^5 = 32 > 21)
  have hlog_21_bound : Real.log 21 ≤ 5 := by
    have h_exp5_gt_21 : (21 : ℝ) < Real.exp 5 := by
      have h2_lt_exp1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h_exp5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
        rw [← Real.exp_nat_mul 1 5]
        norm_num
      rw [h_exp5]
      have h32 : (21 : ℝ) < (2 : ℝ) ^ 5 := by norm_num
      have h2pow5_lt : (2 : ℝ) ^ 5 < (Real.exp 1) ^ 5 :=
        pow_lt_pow_left₀ h2_lt_exp1 (by linarith) (by norm_num : (5 : ℕ) ≠ 0)
      linarith
    by_contra! h
    -- h : 5 < Real.log 21
    have h_exp_lt : Real.exp 5 < 21 := by
      calc
        Real.exp 5 < Real.exp (Real.log 21) := Real.exp_lt_exp.mpr h
        _ = 21 := Real.exp_log (by norm_num : (0 : ℝ) < 21)
    linarith
  -- log n ≤ (x - 14)/3
  have hlog_n_bound : Real.log (n : ℝ) ≤ (x - 14) / 3 := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos_d : (d : ℝ) ≠ 0 := by linarith
    have hpos_n : (n : ℝ) ≠ 0 := by linarith
    have h_log_mul : Real.log ((d : ℝ) * n) = Real.log (d : ℝ) + Real.log (n : ℝ) :=
      Real.log_mul hpos_d hpos_n
    have hlog_d_nonneg : 0 ≤ Real.log (d : ℝ) :=
      Real.log_nonneg hd'
    rw [h_log_mul] at hx14
    linarith
  -- log M ≤ (1/2) * log n (since M ≤ √n and both ≥ 1)
  have hlog_M_bound : Real.log M ≤ (1/2 : ℝ) * Real.log (n : ℝ) := by
    have hM_nonneg : 0 ≤ M := by linarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hM_sq_le_n : M ^ 2 ≤ (n : ℝ) := by
      calc
        M ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by nlinarith
        _ = (n : ℝ) := Real.sq_sqrt hn_nonneg
    have hM_sq_pos : 0 < M ^ 2 := by
      have : 0 < M := by linarith
      positivity
    have hn_pos : 0 < (n : ℝ) := by linarith
    have h_log_M_sq : Real.log (M ^ 2) = 2 * Real.log M := by
      rw [Real.log_pow, Nat.cast_ofNat]
    have h_log_n : Real.log (M ^ 2) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hM_sq_pos hM_sq_le_n
    rw [h_log_M_sq] at h_log_n
    linarith
  -- log de = -x
  have hlog_de : Real.log de = -x := by
    rw [hx, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by linarith : de ≠ 0), Real.log_one]
    ring
  -- Decompose the log expression
  have hlog_expr : Real.log (4 * (n * C) * M / (de / k)) =
      Real.log 4 + Real.log (n : ℝ) + Real.log C + Real.log M + Real.log k + x := by
    have hpos_4 : (4 : ℝ) ≠ 0 := by norm_num
    have hpos_n : (n : ℝ) ≠ 0 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hpos_C : C ≠ 0 := by linarith
    have hpos_M : M ≠ 0 := by linarith
    have hpos_k : k ≠ 0 := by linarith
    have hpos_de : de ≠ 0 := by linarith
    have hpos_nC : (n : ℝ) * C ≠ 0 := mul_ne_zero hpos_n hpos_C
    have hpos_4nC : 4 * ((n : ℝ) * C) ≠ 0 := mul_ne_zero hpos_4 hpos_nC
    have hpos_4nCM : 4 * ((n : ℝ) * C) * M ≠ 0 := mul_ne_zero hpos_4nC hpos_M
    have hpos_de_div_k : de / k ≠ 0 := div_ne_zero hpos_de hpos_k
    rw [Real.log_div hpos_4nCM hpos_de_div_k]
    rw [Real.log_mul hpos_4nC hpos_M]
    rw [Real.log_mul hpos_4 hpos_nC]
    rw [Real.log_mul hpos_n hpos_C]
    rw [Real.log_div hpos_de hpos_k]
    rw [hlog_de]
    ring
  -- Now combine the bounds
  rw [hlog_expr]
  have hk_bound : Real.log k ≤ Real.log 21 :=
    Real.log_le_log (by linarith) hk
  have h_total : Real.log 4 + Real.log (n : ℝ) + Real.log C + Real.log M + Real.log k + x ≤ 7 * (d : ℝ) * x := by
    have hsum : Real.log 4 + Real.log (n : ℝ) + Real.log C + Real.log M + Real.log k + x ≤
        2 + (x - 14)/3 + 5*(d:ℝ)*x + (1/2)*((x - 14)/3) + 5 + x := by
      linarith
    have hsimp : 2 + (x - 14)/3 + 5*(d:ℝ)*x + (1/2)*((x - 14)/3) + 5 + x ≤ 7*(d:ℝ)*x := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hx_nonneg : 0 ≤ x := by linarith
      nlinarith
    linarith
  exact h_total

end AdversarialBco.Poly.EvSI
