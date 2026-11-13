/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Run

@[expose] public section

/-!
# Bounds on the parameters of DF2-O

For `1 ≤ d`, `1 ≤ n` and `0 < δ`: `0 < δ₁ ≤ e^{-14}` and `1/δ₁ ≤ 3/δ + e^{14} (d n)³`, `L ≥ 504`, `ε ≥ 1/√n`,
`0 < R ≤ 268 d²`, `e^{14} ≤ 1210000`, and for `δ < 1`, with `X = 2 d n/δ`, `0 < δ_e ≤ 1` and `1/δ_e ≤ 10⁵ X⁴`.
-/

namespace AdversarialBco.Poly

/-- `δ₁ = min (δ/3) (e^{-14}/(d n)³)`. -/
theorem df2oPar_δ1_bounds (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    0 < (df2oPar d n δ).δ1 ∧ (df2oPar d n δ).δ1 ≤ Real.exp (-14) ∧
      1 / (df2oPar d n δ).δ1 ≤ 3 / δ + Real.exp 14 * ((d : ℝ) * n) ^ 3 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have hpow : (1 : ℝ) ≤ ((d : ℝ) * n) ^ 3 := one_le_pow₀ hdn
  have hb : 0 < Real.exp (-14) / ((d : ℝ) * n) ^ 3 := div_pos (Real.exp_pos _) (by linarith)
  have hb' : Real.exp (-14) / ((d : ℝ) * n) ^ 3 ≤ Real.exp (-14) := div_le_self (Real.exp_pos _).le hpow
  show 0 < min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) ∧
    min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) ≤ Real.exp (-14) ∧
    1 / min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) ≤ 3 / δ + Real.exp 14 * ((d : ℝ) * n) ^ 3
  refine ⟨lt_min (by positivity) hb, (min_le_right _ _).trans hb', ?_⟩
  have h1 : 0 ≤ Real.exp 14 * ((d : ℝ) * n) ^ 3 := by positivity
  have h2 : 0 ≤ 3 / δ := by positivity
  rcases min_choice (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) with h | h <;> rw [h]
  · rw [one_div_div]; linarith
  · rw [one_div_div, Real.exp_neg, div_inv_eq_mul, mul_comm]; linarith

/-- `L = C₀ log (1/δ_e) ≥ 36 · 14`. -/
theorem df2oPar_Le_ge (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    504 ≤ (df2oPar d n δ).Le := by
  obtain ⟨h0, h1, -⟩ := df2oPar_δ1_bounds d n hd hn δ hδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδe : Real.exp 14 ≤ 1 / (4 * (df2oPar d n δ).δ1 / (5 * n)) := by
    rw [one_div_div, le_div_iff₀ (by positivity)]
    have e : Real.exp 14 * Real.exp (-14) = 1 := by rw [← Real.exp_add]; norm_num
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos 14).le
    nlinarith
  have hlog : 14 ≤ Real.log (1 / (4 * (df2oPar d n δ).δ1 / (5 * n))) := by
    have := Real.log_le_log (Real.exp_pos 14) hδe
    rwa [Real.log_exp] at this
  show 504 ≤ df2C0 * Real.log (1 / (4 * (df2oPar d n δ).δ1 / (5 * n)))
  unfold df2C0; linarith

/-- `ε ≥ 1/√n`. -/
theorem df2oPar_eps_ge (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    1 / Real.sqrt n ≤ (df2oPar d n δ).eps := by
  have hLe := df2oPar_Le_ge d n hd hn δ hδ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : 1 ≤ Real.sqrt d := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hd'
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hL5 : 1 ≤ (df2oPar d n δ).Le ^ 5 := one_le_pow₀ (by linarith)
  show 1 / Real.sqrt n ≤ 20 * df2oClam * (d * Real.sqrt d) * (df2oPar d n δ).Le ^ 5 / Real.sqrt n
  apply div_le_div_of_nonneg_right _ hsn.le
  unfold df2oClam
  have : 1 ≤ (d : ℝ) * Real.sqrt d := by nlinarith
  nlinarith

/-- `0 < R ≤ 268 d²`. -/
theorem df2oPar_R_bound (d n : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    0 < (df2oPar d n δ).R ∧ (df2oPar d n δ).R ≤ 268 * (d : ℝ) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 * d + 2) := Real.log_pos (by linarith)
  have hlog2 : Real.log (2 * d + 2) ≤ (2 * d) ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d + 2 by linarith)
    nlinarith
  have hs : Real.sqrt (Real.log (2 * d + 2)) ≤ 2 * d := Real.sqrt_le_iff.2 ⟨by linarith, hlog2⟩
  show 0 < 134 * (d : ℝ) * Real.sqrt (Real.log (2 * d + 2)) ∧
    134 * (d : ℝ) * Real.sqrt (Real.log (2 * d + 2)) ≤ 268 * (d : ℝ) ^ 2
  refine ⟨mul_pos (by positivity) (Real.sqrt_pos.2 hlog), ?_⟩
  nlinarith

/-- `e^{14} ≤ 1210000`. -/
theorem df2_exp14_le : Real.exp 14 ≤ 1210000 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 14
    _ ≤ 1210000 := by norm_num

/-- `d, n, d n ≤ X/2` and `2 ≤ X` for `X = 2 d n/δ`. -/
theorem df2_X_bounds (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (d : ℝ) * n ≤ 2 * d * n / δ / 2 ∧ (d : ℝ) ≤ 2 * d * n / δ / 2 ∧ (n : ℝ) ≤ 2 * d * n / δ / 2 ∧
      2 ≤ 2 * d * n / δ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : 2 * (d : ℝ) * n / δ / 2 = d * n / δ := by ring
  have h1 : (d : ℝ) * n ≤ d * n / δ := by
    rw [le_div_iff₀ hδ]; nlinarith [mul_le_mul_of_nonneg_left hδ1.le (show (0 : ℝ) ≤ d * n by positivity)]
  have hdn1 : (d : ℝ) ≤ d * n := by nlinarith
  have hnd1 : (n : ℝ) ≤ d * n := by nlinarith
  have e2 : 2 * (d : ℝ) * n / δ = 2 * (d * n / δ) := by ring
  refine ⟨by rw [e]; exact h1, by rw [e]; linarith, by rw [e]; linarith, by rw [e2]; nlinarith⟩

/-- `0 < δ_e ≤ 1` and `1/δ_e ≤ 10⁵ X⁴`. -/
theorem df2oPar_δe_bounds (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < (df2oPar d n δ).δe ∧ (df2oPar d n δ).δe ≤ 1 ∧
      1 / (df2oPar d n δ).δe ≤ 10 ^ 5 * (2 * d * n / δ) ^ 4 := by
  obtain ⟨h0, h1, h2⟩ := df2oPar_δ1_bounds d n hd hn δ hδ
  obtain ⟨hDX, -, hnX, hX2⟩ := df2_X_bounds d n hd hn δ hδ hδ1
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hE := df2_exp14_le
  have hem : Real.exp (-14) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  set X := 2 * (d : ℝ) * n / δ with hX
  have e : (df2oPar d n δ).δe = 4 * (df2oPar d n δ).δ1 / (5 * n) := rfl
  have h3δ : 3 / δ ≤ 3 / 2 * X := by
    have e3 : 3 / 2 * X = 3 * ((d : ℝ) * n) / δ := by rw [hX]; ring
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [e3]; exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  refine ⟨by rw [e]; positivity, ?_, ?_⟩
  · rw [e, div_le_one (by positivity)]; nlinarith
  · rw [e, one_div_div]
    have hD3 : ((d : ℝ) * n) ^ 3 ≤ (X / 2) ^ 3 := by gcongr
    have s1 : 5 * (n : ℝ) / (4 * (df2oPar d n δ).δ1) = 5 / 4 * n * (1 / (df2oPar d n δ).δ1) := by
      field_simp
    rw [s1]
    have hX0 : 0 ≤ X := by linarith
    calc 5 / 4 * (n : ℝ) * (1 / (df2oPar d n δ).δ1) ≤ 5 / 4 * (X / 2) * (3 / 2 * X + 1210000 * (X / 2) ^ 3) := by
          have : 1 / (df2oPar d n δ).δ1 ≤ 3 / 2 * X + 1210000 * (X / 2) ^ 3 := by
            have : Real.exp 14 * ((d : ℝ) * n) ^ 3 ≤ 1210000 * (X / 2) ^ 3 := by
              calc Real.exp 14 * ((d : ℝ) * n) ^ 3 ≤ 1210000 * ((d : ℝ) * n) ^ 3 := by gcongr
                _ ≤ 1210000 * (X / 2) ^ 3 := by gcongr
            linarith
          gcongr
      _ = 15 / 16 * X ^ 2 + 5 / 8 * 151250 * X ^ 4 := by ring
      _ ≤ 10 ^ 5 * X ^ 4 := by
          have : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith

end AdversarialBco.Poly
