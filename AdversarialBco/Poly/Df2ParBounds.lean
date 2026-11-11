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
`0 < R ≤ 268 d²`, and for `δ < 1` the bound `j ≤ 70 log (2 d n/δ)` on the number of steps of the bisection of the
gauge, which the cost of a round of `df2Prog` reads.
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

/-- `log 10⁹ ≤ 21`. -/
theorem df2_log_1e9_le : Real.log (10 ^ 9) ≤ 21 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 21 = Real.exp 1 ^ 21 := by rw [← Real.exp_nat_mul]; norm_num
  have : (10 : ℝ) ^ 9 ≤ Real.exp 21 := by
    rw [e]
    calc (10 : ℝ) ^ 9 ≤ (2.7182818283 : ℝ) ^ 21 := by norm_num
      _ ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num) h.le 21
  calc Real.log (10 ^ 9) ≤ Real.log (Real.exp 21) := Real.log_le_log (by norm_num) this
    _ = 21 := Real.log_exp 21

/-- `j = ⌈log₂ (n R (R + 7)/(δ₁ ε))⌉ ≤ 70 log (2 d n/δ)`. -/
theorem df2oPar_j_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((df2oPar d n δ).j : ℝ) ≤ 70 * Real.log (2 * d * n / δ) := by
  obtain ⟨h0, -, h2⟩ := df2oPar_δ1_bounds d n hd hn δ hδ
  obtain ⟨hR0, hR⟩ := df2oPar_R_bound d n hd δ
  have he := df2oPar_eps_ge d n hd hn δ hδ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  set X := 2 * (d : ℝ) * n / δ with hX
  set D := (d : ℝ) * n with hD
  have hDX : D ≤ X / 2 := by
    have e : X / 2 = D / δ := by rw [hX, hD]; ring
    rw [e, le_div_iff₀ hδ]; nlinarith
  have hX2 : 2 ≤ X := by linarith
  have h3δ : 3 / δ ≤ 3 / 2 * X := by
    rw [hX, div_le_iff₀ hδ]; field_simp; nlinarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have heps0 : 0 < (df2oPar d n δ).eps := lt_of_lt_of_le (by positivity) he
  have hie : 1 / (df2oPar d n δ).eps ≤ n := by
    have h1 : 1 / (df2oPar d n δ).eps ≤ Real.sqrt n := by
      rw [div_le_iff₀ heps0]; rw [div_le_iff₀ hsn] at he; linarith
    have h2 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    linarith
  set A := (n : ℝ) * (df2oPar d n δ).R * ((df2oPar d n δ).R + 7) / ((df2oPar d n δ).δ1 * (df2oPar d n δ).eps)
    with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hE := df2_exp14_le
  have hA1 : A ≤ 10 ^ 9 * X ^ 7 := by
    have e : A = (n : ℝ) * (df2oPar d n δ).R * ((df2oPar d n δ).R + 7) * (1 / (df2oPar d n δ).δ1) *
        (1 / (df2oPar d n δ).eps) := by rw [hA]; field_simp
    have hR7 : (df2oPar d n δ).R + 7 ≤ 275 * (d : ℝ) ^ 2 := by nlinarith
    have hi1 : 0 ≤ 1 / (df2oPar d n δ).δ1 := by positivity
    have hi2 : 0 ≤ 1 / (df2oPar d n δ).eps := by positivity
    have s1 : A ≤ (n : ℝ) * (268 * (d : ℝ) ^ 2) * (275 * (d : ℝ) ^ 2) * (3 / δ + Real.exp 14 * D ^ 3) * n := by
      rw [e]
      gcongr
    have hd4 : (n : ℝ) * (268 * (d : ℝ) ^ 2) * (275 * (d : ℝ) ^ 2) * (3 / δ + Real.exp 14 * D ^ 3) * n =
        73700 * (D ^ 2 * (d : ℝ) ^ 2) * (3 / δ + Real.exp 14 * D ^ 3) := by rw [hD]; ring
    have hdD : (d : ℝ) ≤ D := by rw [hD]; nlinarith
    have hD0 : 0 ≤ D := by linarith
    have s2 : D ^ 2 * (d : ℝ) ^ 2 ≤ (X / 2) ^ 4 := by
      calc D ^ 2 * (d : ℝ) ^ 2 ≤ D ^ 2 * D ^ 2 := by gcongr
        _ = D ^ 4 := by ring
        _ ≤ (X / 2) ^ 4 := by gcongr
    have s3 : 3 / δ + Real.exp 14 * D ^ 3 ≤ 3 / 2 * X + 1210000 * (X / 2) ^ 3 := by
      have : D ^ 3 ≤ (X / 2) ^ 3 := by gcongr
      have : Real.exp 14 * D ^ 3 ≤ 1210000 * (X / 2) ^ 3 := by
        calc Real.exp 14 * D ^ 3 ≤ 1210000 * D ^ 3 := by gcongr
          _ ≤ 1210000 * (X / 2) ^ 3 := by gcongr
      linarith
    have hX0 : 0 ≤ X := by linarith
    have s4 : X ^ 5 ≤ X ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc A ≤ 73700 * (D ^ 2 * (d : ℝ) ^ 2) * (3 / δ + Real.exp 14 * D ^ 3) := by rw [← hd4]; exact s1
      _ ≤ 73700 * ((X / 2) ^ 4) * (3 / 2 * X + 1210000 * (X / 2) ^ 3) := by
        have : 0 ≤ 3 / δ + Real.exp 14 * D ^ 3 := by positivity
        gcongr
      _ = 73700 / 16 * 3 / 2 * X ^ 5 + 73700 / 16 * 1210000 / 8 * X ^ 7 := by ring
      _ ≤ 10 ^ 9 * X ^ 7 := by nlinarith
  have hL : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hlA : Real.log A ≤ 21 + 7 * Real.log X := by
    have hl1 := Real.log_le_log hA0 hA1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow X 7] at hl1
    have := df2_log_1e9_le
    push_cast at hl1 ⊢
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  show ((⌈Real.logb 2 A⌉₊ : ℕ) : ℝ) ≤ 70 * Real.log X
  rcases le_or_gt (Real.logb 2 A) 0 with h | h
  · rw [Nat.ceil_eq_zero.2 h]; push_cast; linarith
  · have hc := Nat.ceil_lt_add_one h.le
    have hlb : Real.logb 2 A = Real.log A / Real.log 2 := rfl
    have : Real.logb 2 A ≤ (21 + 7 * Real.log X) / Real.log 2 := by
      rw [hlb]; exact div_le_div_of_nonneg_right hlA (by linarith)
    have : (21 + 7 * Real.log X) / Real.log 2 + 1 ≤ 70 * Real.log X := by
      rw [div_add_one (by linarith), div_le_iff₀ (by linarith)]
      have a1 : 0.69 * Real.log X ≤ Real.log 2 * Real.log X := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    linarith

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

/-- `1 ≤ R`. -/
theorem df2oPar_R_ge_one (d n : ℕ) (hd : 1 ≤ d) (δ : ℝ) : 1 ≤ (df2oPar d n δ).R := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : Real.log 4 ≤ Real.log (2 * d + 2) := Real.log_le_log (by norm_num) (by linarith)
  have h4 : (1 : ℝ) / 100 ≤ Real.log 4 := by
    have := Real.log_two_gt_d9
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hs : (1 : ℝ) / 10 ≤ Real.sqrt (Real.log (2 * d + 2)) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  show 1 ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * d + 2))
  nlinarith

/-- `L ≤ 36/δ_e`. -/
theorem df2oPar_Le_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (df2oPar d n δ).Le ≤ 36 / (df2oPar d n δ).δe := by
  obtain ⟨h0, -, -⟩ := df2oPar_δe_bounds d n hd hn δ hδ hδ1
  show df2C0 * Real.log (1 / (df2oPar d n δ).δe) ≤ 36 / (df2oPar d n δ).δe
  unfold df2C0
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / (df2oPar d n δ).δe by positivity)
  have e : 36 / (df2oPar d n δ).δe = 36 * (1 / (df2oPar d n δ).δe) := by ring
  rw [e]; linarith

/-- `0 < s_b ≤ 1` and `1/s_b ≤ (R + 1)²/δ_e²`. -/
theorem df2oPar_sb_bounds (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < (df2oPar d n δ).sb ∧ (df2oPar d n δ).sb ≤ 1 ∧
      1 / (df2oPar d n δ).sb ≤ ((df2oPar d n δ).R + 1) ^ 2 * (1 / (df2oPar d n δ).δe) ^ 2 := by
  obtain ⟨h0, h1, -⟩ := df2oPar_δe_bounds d n hd hn δ hδ hδ1
  have hR := df2oPar_R_ge_one d n hd δ
  have e : (df2oPar d n δ).sb = (df2oPar d n δ).δe ^ 2 / ((df2oPar d n δ).R * ((df2oPar d n δ).R + 1)) := rfl
  refine ⟨by rw [e]; positivity, ?_, ?_⟩
  · rw [e, div_le_one (by positivity)]
    have : (df2oPar d n δ).δe ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · rw [e, one_div_div, div_pow, one_pow, ← div_eq_mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith

/-- `η ≤ √d ≤ d`. -/
theorem df2oPar_eta_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ (df2oPar d n δ).eta ∧ (df2oPar d n δ).eta ≤ d := by
  have hLe := df2oPar_Le_ge d n hd hn δ hδ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsn : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hsd : Real.sqrt d ≤ d := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  show 0 ≤ Real.sqrt d / ((df2oPar d n δ).Le * Real.sqrt n) ∧ Real.sqrt d / ((df2oPar d n δ).Le * Real.sqrt n) ≤ d
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ (df2oPar d n δ).Le * Real.sqrt n := by nlinarith
  nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- `α ρ/2 ≥ 1`, so the accuracy of the first call of AP is `1`. -/
theorem df2oPar_e1 (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    min 1 ((df2oPar d n δ).alpha * (df2oPar d n δ).rho / 2) = 1 := by
  have hLe := df2oPar_Le_ge d n hd hn δ hδ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply min_eq_left
  show 1 ≤ 1 / 4 * (2 * df2oClam * (d : ℝ) ^ 2 * (df2oPar d n δ).Le ^ 3) / 2
  unfold df2oClam
  have : 1 ≤ (d : ℝ) ^ 2 := by nlinarith
  have : 1 ≤ (df2oPar d n δ).Le ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

/-- A quantity at most `c X^m` (`X ≥ 2`, `c ≥ 1`) has logarithm at most `(log c/log 2 + m) log X`. -/
theorem df2_log_le_of_le_pow {X y c : ℝ} {m : ℕ} (hX : 2 ≤ X) (hc : 1 ≤ c) (hy : 0 < y) (h : y ≤ c * X ^ m) :
    Real.log y ≤ (Real.log c / Real.log 2 + m) * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have h1 : Real.log y ≤ Real.log c + m * Real.log X := by
    have := Real.log_le_log hy h
    rwa [Real.log_mul (by linarith) (by positivity), Real.log_pow] at this
  have h2 : Real.log c ≤ Real.log c / Real.log 2 * Real.log X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlX hlc
  nlinarith

/-- The same for `log₂` and its ceiling: `⌈log₂ y⌉₊ ≤ (log c/log 2 + m) log X/log 2 + 1`. -/
theorem df2_ceil_logb_le {X y c : ℝ} {m : ℕ} (hX : 2 ≤ X) (hc : 1 ≤ c) (hy : 0 < y) (h : y ≤ c * X ^ m) :
    (⌈Real.logb 2 y⌉₊ : ℝ) ≤ (Real.log c / Real.log 2 + m) * Real.log X / Real.log 2 + 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hk : 0 ≤ (Real.log c / Real.log 2 + m) * Real.log X / Real.log 2 := by
    have : 0 ≤ Real.log c := Real.log_nonneg hc
    positivity
  rcases le_or_gt (Real.logb 2 y) 0 with h0 | h0
  · rw [Nat.ceil_eq_zero.2 h0]; push_cast; linarith
  · have := Nat.ceil_lt_add_one h0.le
    have hb : Real.logb 2 y ≤ (Real.log c / Real.log 2 + m) * Real.log X / Real.log 2 :=
      div_le_div_of_nonneg_right (df2_log_le_of_le_pow hX hc hy h) hl2.le
    linarith

end AdversarialBco.Poly
