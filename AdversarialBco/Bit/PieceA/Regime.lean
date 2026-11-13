/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Defs

@[expose] public section

/-!
# Piece A: the regime facts on the explicit constants

(F1) to (F4) and the bounds on `R`, at `ε ≤ 1/2`, for the constants of Bit/PieceA/Defs.lean. (F1)
`regime_N` is proved as a bootstrap: `N ≥ 2^20` gives `Le ≥ 498`, and each step
`N ≥ 15 · 2^17 · 29000^8 Le^40 ≥ 2^b` raises the bound on `Le = 36 ln N` (`regN_step`), up to `N ≥ 2^701`.
-/

namespace AdversarialBco.Bit.PieceA

theorem regime_n4 {d n : ℕ} (hd : 1 ≤ d) : (32 : ℝ) ^ 4 * (n : ℝ) ^ 4 ≤ Ne d n := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hcube : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have h1_nonneg : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    have hd_sq_nonneg : (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) := mul_nonneg hd_nonneg hd_nonneg
    have h_mul : (1 : ℝ) * (1 : ℝ) ≤ (d : ℝ) * (d : ℝ) := mul_le_mul hd' hd' h1_nonneg hd_nonneg
    have h_mul' : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ (d : ℝ) * (d : ℝ) * (d : ℝ) := mul_le_mul h_mul hd' h1_nonneg hd_sq_nonneg
    calc
      (1 : ℝ) = (1 : ℝ) * (1 : ℝ) * (1 : ℝ) := by norm_num
      _ ≤ (d : ℝ) * (d : ℝ) * (d : ℝ) := h_mul'
      _ = (d : ℝ) ^ 3 := by ring
  have hconst : (32 : ℝ) ^ 4 ≤ (15 : ℝ) * ((2 : ℝ) ^ 17) := by norm_num
  have hn_nonneg : 0 ≤ (n : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg _) 4
  have h_main : (32 : ℝ) ^ 4 ≤ (15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) * ((d : ℝ) ^ 3) := by
    calc
      (32 : ℝ) ^ 4 ≤ (15 : ℝ) * ((2 : ℝ) ^ 17) := hconst
      _ = (15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) := by norm_num
      _ ≤ (15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) * ((d : ℝ) ^ 3) := by
        have hpos : 0 ≤ (15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) := by norm_num
        nlinarith
  calc
    (32 : ℝ) ^ 4 * (n : ℝ) ^ 4 ≤ ((15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) * ((d : ℝ) ^ 3)) * (n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right h_main hn_nonneg
    _ = (15 : ℝ) * ((2 : ℕ) ^ 17 : ℝ) * ((d : ℝ) ^ 3) * (n : ℝ) ^ 4 := by ring
    _ = Ne d n := by
      unfold Ne NeN
      push_cast
      ring

theorem regime_n_ge {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : eps d n ≤ 1 / 2) :
    (29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n ^ 10 ≤ n := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hn
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by linarith
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := by linarith
  have hNe_gt_one : 1 < Ne d n := by
    rw [Ne, NeN]
    have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hd' 3
      simpa using this
    have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hn' 4
      simpa using this
    push_cast
    nlinarith
  have hLe_pos : 0 < Le d n := by
    rw [Le]
    have hlog_pos : 0 < Real.log (Ne d n) := Real.log_pos hNe_gt_one
    positivity
  unfold eps at h
  have h_mul : 14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5 ≤ (1/2 : ℝ) * Real.sqrt (n : ℝ) :=
    (div_le_iff₀ hsqrt_n_pos).mp h
  have h_mul2 : (29000 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5 ≤ Real.sqrt (n : ℝ) := by
    linarith
  have h_nonneg_left : 0 ≤ (29000 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5 := by
    positivity
  have h_sq : ((29000 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5)^2 ≤ (Real.sqrt (n : ℝ))^2 :=
    pow_le_pow_left₀ h_nonneg_left h_mul2 2
  have h_right : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
  have h_left : ((29000 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5)^2 = (29000 : ℝ)^2 * (d : ℝ)^3 * (Le d n)^10 := by
    calc
      ((29000 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5)^2
          = ((29000 : ℝ)^2) * ((d : ℝ)^2) * ((Real.sqrt (d : ℝ))^2) * ((Le d n)^10) := by ring
      _ = ((29000 : ℝ)^2) * ((d : ℝ)^2) * (d : ℝ) * ((Le d n)^10) := by simp [Real.sq_sqrt hd_nonneg]
      _ = (29000 : ℝ)^2 * (d : ℝ)^3 * (Le d n)^10 := by ring
  rw [h_left, h_right] at h_sq
  exact h_sq

theorem regime_d15 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : eps d n ≤ 1 / 2) : (d : ℝ) ^ 15 ≤ Ne d n := by
  -- Cast natural inequalities to ℝ
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact mod_cast Nat.zero_le d
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact mod_cast Nat.zero_le n
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd0' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.one_pos.trans_le hd)
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.one_pos.trans_le hn)
  -- Unfold Ne for convenience
  have hNe_val : Ne d n = (15 * 2 ^ 17 : ℝ) * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
    unfold Ne NeN
    push_cast
    ring
  rw [hNe_val]
  -- Ne > 1, so log(Ne) > 0 and Le > 0
  have hNe_gt_one : 1 < Ne d n := by
    rw [hNe_val]
    have hbase : (1 : ℝ) < (15 * 2 ^ 17 : ℝ) := by norm_num
    have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
      simpa [one_pow] using pow_le_pow_left₀ (by norm_num) hd1 3
    have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      simpa [one_pow] using pow_le_pow_left₀ (by norm_num) hn1 4
    nlinarith
  have hlog_pos : 0 < Real.log (Ne d n) := Real.log_pos hNe_gt_one
  have hLe_pos : 0 < Le d n := by
    rw [Le]
    nlinarith
  -- From eps ≤ 1/2, multiply by sqrt(n) > 0
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0'
  have h_mul : 14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5 ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
    unfold eps at h
    exact ((div_le_iff₀ h_sqrt_n_pos).mp h)
  -- Square both sides (all terms nonnegative)
  have h_nonneg_A : 0 ≤ 14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5 := by
    positivity
  have h_nonneg_B : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
    positivity
  have h_sq : (14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5) ^ 2 ≤ ((1 / 2 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
    nlinarith
  -- Expand both squares
  have h_left : (14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5) ^ 2 = (14500 : ℝ) ^ 2 * (d : ℝ) ^ 3 * (Le d n) ^ 10 := by
    calc
      (14500 * (d : ℝ) * Real.sqrt (d : ℝ) * (Le d n) ^ 5) ^ 2
          = (14500 : ℝ) ^ 2 * ((d : ℝ) ^ 2 * ((Real.sqrt (d : ℝ)) ^ 2) * ((Le d n) ^ 5) ^ 2) := by ring
      _ = (14500 : ℝ) ^ 2 * ((d : ℝ) ^ 2 * (d : ℝ) * ((Le d n) ^ 5) ^ 2) := by
        simp [Real.sq_sqrt hd0]
      _ = (14500 : ℝ) ^ 2 * ((d : ℝ) ^ 2 * (d : ℝ) * (Le d n) ^ 10) := by
        rw [← pow_mul (Le d n) 5 2, show (5:ℕ)*2 = 10 by norm_num]
      _ = (14500 : ℝ) ^ 2 * (d : ℝ) ^ 3 * (Le d n) ^ 10 := by ring
  have h_right : ((1 / 2 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 = (1 / 4 : ℝ) * (n : ℝ) := by
    calc
      ((1 / 2 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 = (1 / 4 : ℝ) * ((Real.sqrt (n : ℝ)) ^ 2) := by ring
      _ = (1 / 4 : ℝ) * (n : ℝ) := by simp [Real.sq_sqrt hn0]
  have h_expanded : (14500 : ℝ) ^ 2 * (d : ℝ) ^ 3 * (Le d n) ^ 10 ≤ (1 / 4 : ℝ) * (n : ℝ) := by
    linarith
  -- Multiply by 4: 4 * 14500^2 = 29000^2
  have h_n_ineq : (29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * (Le d n) ^ 10 ≤ (n : ℝ) := by
    have h4 : (4 : ℝ) * (14500 : ℝ) ^ 2 = (29000 : ℝ) ^ 2 := by norm_num
    nlinarith
  -- Le ≥ 1 because Ne ≥ 1966080 > e
  have hLe_ge_one : 1 ≤ Le d n := by
    rw [Le]
    have hNe_gt_e : Real.exp 1 < Ne d n := by
      have hNe_lb : (1966080 : ℝ) ≤ Ne d n := by
        rw [hNe_val]
        have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
          simpa [one_pow] using pow_le_pow_left₀ (by norm_num) hd1 3
        have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
          simpa [one_pow] using pow_le_pow_left₀ (by norm_num) hn1 4
        have hbase : (15 * 2 ^ 17 : ℝ) = (1966080 : ℝ) := by norm_num
        rw [hbase]
        nlinarith
      have he_lt_1966080 : Real.exp 1 < (1966080 : ℝ) := by
        linarith [Real.exp_one_lt_d9]
      linarith
    have hlog_gt_one : 1 < Real.log (Ne d n) := by
      have h := Real.log_lt_log (Real.exp_pos 1) hNe_gt_e
      simpa [Real.log_exp] using h
    nlinarith
  -- From n ≥ 29000^2 * d^3 * Le^10 and Le ≥ 1, get n ≥ d^3
  have hn_ge_d3 : (d : ℝ) ^ 3 ≤ (n : ℝ) := by
    have h_factor : (1 : ℝ) ≤ (29000 : ℝ) ^ 2 * (Le d n) ^ 10 := by
      have h29000 : (1 : ℝ) ≤ (29000 : ℝ) ^ 2 := by norm_num
      have hLe10 : (1 : ℝ) ≤ (Le d n) ^ 10 := by
        simpa [one_pow] using pow_le_pow_left₀ (by norm_num) hLe_ge_one 10
      nlinarith
    nlinarith
  -- Hence n^4 ≥ d^12
  have hn4_ge_d12 : (d : ℝ) ^ 12 ≤ (n : ℝ) ^ 4 := by
    have hd3_nonneg : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd0 3
    have h := pow_le_pow_left₀ hd3_nonneg hn_ge_d3 4
    simpa [show ((d : ℝ) ^ 3) ^ 4 = (d : ℝ) ^ 12 by ring] using h
  -- Final chain: d^15 = d^3 * d^12 ≤ d^3 * n^4 ≤ (15*2^17) * d^3 * n^4
  have hd3_nonneg : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd0 3
  have hn4_nonneg : 0 ≤ (n : ℝ) ^ 4 := pow_nonneg hn0 4
  calc
    (d : ℝ) ^ 15 = (d : ℝ) ^ 3 * (d : ℝ) ^ 12 := by ring
    _ ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by nlinarith
    _ ≤ (15 * 2 ^ 17 : ℝ) * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by nlinarith

/-- One step of the bootstrap of (F1): from `a ≤ Le` and `c Le^40 ≤ N` with `2^b ≤ c a^40`, `2^b ≤ N`, so
`36 · 0.6931 b ≤ Le = 36 ln N`. -/
theorem regN_step {L N a : ℝ} (b : ℕ) (hL : L = 36 * Real.log N) (ha : 0 ≤ a) (haL : a ≤ L)
    (hN : 15 * 2 ^ 17 * 29000 ^ 8 * L ^ 40 ≤ N) (hb : (2 : ℝ) ^ b ≤ 15 * 2 ^ 17 * 29000 ^ 8 * a ^ 40) :
    (2 : ℝ) ^ b ≤ N ∧ 36 * (6931 / 10000) * b ≤ L := by
  have h1 : (2 : ℝ) ^ b ≤ N := hb.trans (le_trans (by gcongr) hN)
  refine ⟨h1, ?_⟩
  have hlog : Real.log ((2 : ℝ) ^ b) ≤ Real.log N := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at hlog
  have h2 := Real.log_two_gt_d9
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rw [hL]
  nlinarith

set_option exponentiation.threshold 800 in
theorem regime_N {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : eps d n ≤ 1 / 2) : (2 : ℝ) ^ 700 < Ne d n := by
  have hge := regime_n_ge hd hn h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNdef : Ne d n = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
    unfold Ne NeN; push_cast; ring
  have hL : Le d n = 36 * Real.log (Ne d n) := rfl
  have hL0 : 0 ≤ Le d n := by
    rw [hL]
    have : (1 : ℝ) ≤ Ne d n := by
      rw [hNdef]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd'
      have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
      nlinarith
    have := Real.log_nonneg this
    linarith
  -- `N ≥ 15 · 2^17 · 29000^8 · Le^40`
  have hN : 15 * 2 ^ 17 * 29000 ^ 8 * Le d n ^ 40 ≤ Ne d n := by
    rw [hNdef]
    have h4 : ((29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n ^ 10) ^ 4 ≤ (n : ℝ) ^ 4 := by
      gcongr
    have hd12 : (1 : ℝ) ≤ (d : ℝ) ^ 15 := one_le_pow₀ hd'
    have hL40 : 0 ≤ Le d n ^ 40 := by positivity
    calc 15 * 2 ^ 17 * 29000 ^ 8 * Le d n ^ 40 ≤ 15 * 2 ^ 17 * 29000 ^ 8 * Le d n ^ 40 * (d : ℝ) ^ 15 := by
          nlinarith
      _ = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * ((29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n ^ 10) ^ 4 := by ring
      _ ≤ 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by gcongr
  -- the start: `N ≥ 2^20`, so `Le ≥ 498`
  have h0 : (2 : ℝ) ^ 20 ≤ Ne d n := by
    rw [hNdef]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd'
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
    nlinarith
  have hA : 498 ≤ Le d n := by
    have hlog : Real.log ((2 : ℝ) ^ 20) ≤ Real.log (Ne d n) := Real.log_le_log (by positivity) h0
    rw [Real.log_pow] at hlog
    have := Real.log_two_gt_d9
    rw [hL]; push_cast at hlog; nlinarith
  obtain ⟨-, hB⟩ := regN_step 497 hL (by norm_num) hA hN (by norm_num)
  obtain ⟨-, hC⟩ := regN_step 683 hL (by norm_num) (le_trans (by norm_num) hB) hN (a := 12400) (by norm_num)
  obtain ⟨hD, -⟩ := regN_step 701 hL (by norm_num) (le_trans (by norm_num) hC) hN (a := 17041) (by norm_num)
  calc (2 : ℝ) ^ 700 < 2 ^ 701 := by norm_num
    _ ≤ Ne d n := hD

theorem regime_Le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : (2 : ℝ) ^ 700 < Ne d n) : 17467 ≤ Le d n := by
  have hNe_pos : 0 < Ne d n := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.one_pos.trans_le hd
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.one_pos.trans_le hn
    unfold Ne NeN
    positivity
  have h2pow_pos : 0 < (2 : ℝ) ^ 700 := by positivity
  have hlog : Real.log ((2 : ℝ) ^ 700) < Real.log (Ne d n) :=
    Real.log_lt_log h2pow_pos h
  have hlog_pow : Real.log ((2 : ℝ) ^ 700) = (700 : ℝ) * Real.log 2 := by
    simpa using Real.log_pow (2 : ℝ) 700
  have hlog_ineq : (700 : ℝ) * Real.log 2 < Real.log (Ne d n) := by
    linarith
  have hLe_ineq : (25200 : ℝ) * Real.log 2 < Le d n := by
    unfold Le
    have hcalc : (25200 : ℝ) * Real.log 2 = 36 * ((700 : ℝ) * Real.log 2) := by ring
    rw [hcalc]
    nlinarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hfinal : (17467 : ℝ) < Le d n := by
    have h_mid : (17467 : ℝ) < (25200 : ℝ) * (0.6931471803 : ℝ) := by
      norm_num
    have h_trans : (25200 : ℝ) * (0.6931471803 : ℝ) < (25200 : ℝ) * Real.log 2 := by
      have hpos : (0 : ℝ) < 25200 := by norm_num
      exact mul_lt_mul_of_pos_left hlog2 hpos
    linarith
  linarith

theorem regime_Le40 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : (2 : ℝ) ^ 700 < Ne d n) : (10 * Le d n) ^ 40 ≤ Ne d n := by
  set x := Real.log (Ne d n) with hx_def
  have hN_pos : 0 < Ne d n := by
    have : 0 < NeN d n := by
      unfold NeN
      positivity
    have h' : (0 : ℝ) < (NeN d n : ℝ) := by exact_mod_cast this
    simpa [Ne] using h'
  have hN_gt_one : 1 < Ne d n := by
    have : 1 < NeN d n := by
      unfold NeN
      have hd3 : 1 ≤ d ^ 3 := by
        simpa using Nat.pow_le_pow_left hd 3
      have hn4 : 1 ≤ n ^ 4 := by
        simpa using Nat.pow_le_pow_left hn 4
      nlinarith
    have h' : (1 : ℝ) < (NeN d n : ℝ) := by exact_mod_cast this
    simpa [Ne] using h'
  have hx_pos : 0 < x := by
    rw [hx_def]
    exact Real.log_pos hN_gt_one
  have hx_gt : 700 * Real.log 2 < x := by
    rw [hx_def]
    have hpos : 0 < (2 : ℝ) ^ 700 := by positivity
    have hlog := Real.log_lt_log hpos h
    have hlog_pow : Real.log ((2 : ℝ) ^ 700) = 700 * Real.log 2 :=
      Real.log_pow (2 : ℝ) 700
    rw [hlog_pow] at hlog
    exact hlog
  -- key inequality: 40 * log(360 * x) ≤ x
  have h_key : 40 * Real.log (360 * x) ≤ x := by
    set x₀ := 700 * Real.log 2 with hx₀_def
    have hx₀_pos : 0 < x₀ := by
      rw [hx₀_def]
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
      positivity
    have hx_gt_x₀ : x₀ < x := hx_gt
    have h_ratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
    have h_log_ratio : Real.log (x / x₀) ≤ x / x₀ - 1 :=
      Real.log_le_sub_one_of_pos h_ratio_pos
    have h_log_prod : Real.log (360 * x) = Real.log (360 * x₀) + Real.log (x / x₀) := by
      calc
        Real.log (360 * x) = Real.log ((360 * x₀) * (x / x₀)) := by
          field_simp [hx₀_pos.ne']
        _ = Real.log (360 * x₀) + Real.log (x / x₀) :=
          Real.log_mul (by positivity) (by positivity)
    rw [h_log_prod]
    -- need: 40 * (log(360*x₀) + log(x/x₀)) ≤ x
    -- using log(x/x₀) ≤ x/x₀ - 1, it suffices: 40*log(360*x₀) - 40 + 40*x/x₀ ≤ x
    -- i.e., 40*log(360*x₀) - 40 ≤ x*(1 - 40/x₀)
    -- since x > x₀ and 1 - 40/x₀ > 0, it suffices: 40*log(360*x₀) - 40 ≤ x₀ - 40
    -- i.e., 40*log(360*x₀) ≤ x₀
    have h_core : 40 * Real.log (360 * x₀) ≤ x₀ := by
      rw [hx₀_def]
      -- goal: 40 * Real.log (360 * (700 * Real.log 2)) ≤ 700 * Real.log 2
      -- simplify 360 * 700 = 252000
      have h_simp : (360 : ℝ) * (700 * Real.log 2) = (252000 : ℝ) * Real.log 2 := by ring
      rw [h_simp]
      -- goal: 40 * Real.log (252000 * Real.log 2) ≤ 700 * Real.log 2
      have hlog2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      -- First, bound 252000 * log 2 above by 174674
      have h_prod_bound : (252000 : ℝ) * Real.log 2 < 174674 := by
        have h_mul : (252000 : ℝ) * Real.log 2 < (252000 : ℝ) * 0.6931471808 :=
          mul_lt_mul_of_pos_left hlog2_lt (by norm_num : 0 < (252000 : ℝ))
        have h_lt : (252000 : ℝ) * 0.6931471808 < 174674 := by norm_num
        nlinarith
      have h_prod_pos : 0 < (252000 : ℝ) * Real.log 2 := by
        have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
        positivity
      -- So log(252000 * log 2) < log(174674)
      have h_log_lt : Real.log ((252000 : ℝ) * Real.log 2) < Real.log 174674 :=
        Real.log_lt_log h_prod_pos h_prod_bound
      -- Now bound log(174674) using the decomposition 174674 = 2^17 * (174674/131072)
      have h_log_174674 : Real.log (174674 : ℝ) ≤ 17 * Real.log 2 + (43602 : ℝ) / 131072 := by
        have h174674_eq : (174674 : ℝ) = (131072 : ℝ) * ((174674 : ℝ) / 131072) := by
          field_simp
        rw [h174674_eq]
        have hpos1 : 0 < (131072 : ℝ) := by norm_num
        have hpos2 : 0 < (174674 : ℝ) / 131072 := by norm_num
        rw [Real.log_mul hpos1.ne' hpos2.ne']
        have h_log_131072 : Real.log (131072 : ℝ) = 17 * Real.log 2 := by
          have h_pow : (131072 : ℝ) = (2 : ℝ) ^ 17 := by norm_num
          rw [h_pow, Real.log_pow (2 : ℝ) 17, Nat.cast_ofNat]
        rw [h_log_131072]
        have h_log_ratio : Real.log ((174674 : ℝ) / 131072) ≤ (174674 : ℝ) / 131072 - 1 :=
          Real.log_le_sub_one_of_pos hpos2
        have h_ratio_bound : (174674 : ℝ) / 131072 - 1 = (43602 : ℝ) / 131072 := by
          norm_num
        rw [h_ratio_bound] at h_log_ratio
        nlinarith
      -- Now combine: log(252000 * log 2) < log(174674) ≤ 17*log(2) + 43602/131072
      have h_log_bound : Real.log ((252000 : ℝ) * Real.log 2) < 17 * Real.log 2 + (43602 : ℝ) / 131072 := by
        nlinarith
      -- Multiply by 40
      have h_mul_bound : 40 * Real.log ((252000 : ℝ) * Real.log 2) < 40 * (17 * Real.log 2 + (43602 : ℝ) / 131072) := by
        nlinarith
      -- Compute RHS: 40*(17*log(2) + 43602/131072) = 680*log(2) + 40*43602/131072
      have h_rhs_simp : 40 * (17 * Real.log 2 + (43602 : ℝ) / 131072) = 680 * Real.log 2 + (40 * 43602 : ℝ) / 131072 := by
        ring
      rw [h_rhs_simp] at h_mul_bound
      -- Now we need to show: 680*log(2) + 40*43602/131072 ≤ 700*log(2)
      -- i.e., 40*43602/131072 ≤ 20*log(2)
      -- i.e., log(2) ≥ (40*43602)/(131072*20) = 43602/(131072*0.5) = 43602/65536 = 21801/32768 ≈ 0.6653
      have h_final_bound : 680 * Real.log 2 + (40 * 43602 : ℝ) / 131072 ≤ 700 * Real.log 2 := by
        have h_ineq : (40 * 43602 : ℝ) / 131072 ≤ 20 * Real.log 2 := by
          have h_log2_gt' : 87202 / 262144 < Real.log 2 := by
            -- 87202/262144 ≈ 0.3326, but we need ≈ 0.6653
            -- Let me recompute: 40*43602/131072 / 20 = 43602/(131072*0.5) = 43602/65536 = 21801/32768 ≈ 0.6653
            -- 21801/32768 = ?
            -- Actually, let me just use the numeric bound directly
            have h := hlog2_gt
            -- 0.6931471803 < log 2
            -- 21801/32768 ≈ 0.6653 < 0.6931471803
            have h_frac : (21801 : ℝ) / 32768 < 0.6931471803 := by norm_num
            nlinarith
          -- Actually, we can just use nlinarith with the known bounds
          have h_log2_gt_val : 0.6931471803 < Real.log 2 := hlog2_gt
          have h_target : (40 * 43602 : ℝ) / 131072 / 20 < 0.6931471803 := by norm_num
          nlinarith
        nlinarith
      have h_lt : 40 * Real.log ((252000 : ℝ) * Real.log 2) < 700 * Real.log 2 := by
        apply lt_of_lt_of_le h_mul_bound h_final_bound
      exact h_lt.le
    have hpos_factor : 0 < 1 - 40 / x₀ := by
      have hx₀_gt_40 : 40 < x₀ := by
        rw [hx₀_def]
        have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
        nlinarith
      exact sub_pos.mpr ((div_lt_one hx₀_pos).mpr hx₀_gt_40)
    have h_main : 40 * (Real.log (360 * x₀) + (x / x₀ - 1)) ≤ x := by
      have hcalc : 40 * (Real.log (360 * x₀) + (x / x₀ - 1)) = 40 * Real.log (360 * x₀) - 40 + 40 * (x / x₀) := by ring
      rw [hcalc]
      have hineq1 : 40 * Real.log (360 * x₀) - 40 ≤ x₀ - 40 := by nlinarith
      have hineq2 : x₀ - 40 + 40 * (x / x₀) ≤ x := by
        have h_diff : x - (x₀ - 40 + 40 * (x / x₀)) = (x - x₀) * (1 - 40 / x₀) := by
          field_simp [hx₀_pos.ne']
          ring
        have h_pos : 0 < x - (x₀ - 40 + 40 * (x / x₀)) := by
          rw [h_diff]
          apply mul_pos
          · nlinarith
          · exact hpos_factor
        nlinarith
      nlinarith
    have h_log_sum_le : Real.log (360 * x₀) + Real.log (x / x₀) ≤ Real.log (360 * x₀) + (x / x₀ - 1) := by
      nlinarith
    have h_final : 40 * (Real.log (360 * x₀) + Real.log (x / x₀)) ≤ x := by
      nlinarith
    exact h_final
  -- Now use h_key to prove the target
  have h_exp : (10 * Le d n) ^ 40 ≤ Ne d n := by
    rw [Le]
    -- (10 * (36 * x)) ^ 40 ≤ exp(x)
    have h_expand : (10 * (36 * x)) ^ 40 = Real.exp (40 * Real.log (360 * x)) := by
      have hpos : 0 < 360 * x := by positivity
      calc
        (10 * (36 * x)) ^ 40 = ((360 : ℝ) * x) ^ 40 := by ring
        _ = Real.exp (Real.log (((360 : ℝ) * x) ^ 40)) := by
          rw [Real.exp_log (pow_pos hpos 40)]
        _ = Real.exp (40 * Real.log ((360 : ℝ) * x)) := by
          rw [Real.log_pow, Nat.cast_ofNat]
        _ = Real.exp (40 * Real.log (360 * x)) := by ring
    rw [h_expand]
    have h_exp_le : Real.exp (40 * Real.log (360 * x)) ≤ Real.exp x :=
      Real.exp_le_exp.mpr h_key
    have h_exp_x : Real.exp x = Ne d n := by
      rw [hx_def, Real.exp_log hN_pos]
    rw [h_exp_x] at h_exp_le
    exact h_exp_le
  exact h_exp

theorem regime_u {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : (2 : ℝ) ^ 160 * Ne d n ^ 10 * (d : ℝ) ^ 16 * u d n ≤ 1 := by
  have hNe_size : (NeN d n : ℝ) < (2 : ℝ) ^ le d n := by
    exact mod_cast Nat.lt_size_self (NeN d n)
  have hd_size : (d : ℝ) < (2 : ℝ) ^ ld d := by
    exact mod_cast Nat.lt_size_self d
  have hNe_pow : (NeN d n : ℝ) ^ 10 ≤ ((2 : ℝ) ^ le d n) ^ 10 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hNe_size.le 10
  have hd_pow : (d : ℝ) ^ 16 ≤ ((2 : ℝ) ^ ld d) ^ 16 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hd_size.le 16
  have hpos_pB : 0 < (2 : ℝ) ^ pB d n := by positivity
  have h_main : (2 : ℝ) ^ 160 * (NeN d n : ℝ) ^ 10 * (d : ℝ) ^ 16 ≤ (2 : ℝ) ^ pB d n := by
    have hpos_2pow : 0 ≤ (2 : ℝ) ^ 160 := by positivity
    have hpos_dpow : 0 ≤ (d : ℝ) ^ 16 := pow_nonneg (Nat.cast_nonneg _) _
    have hpos_2lepow : 0 ≤ ((2 : ℝ) ^ le d n) ^ 10 := pow_nonneg (by positivity) _
    have h1 : (2 : ℝ) ^ 160 * (NeN d n : ℝ) ^ 10 * (d : ℝ) ^ 16 ≤
             (2 : ℝ) ^ 160 * ((2 : ℝ) ^ le d n) ^ 10 * (d : ℝ) ^ 16 := by
      apply mul_le_mul_of_nonneg_right ?_ hpos_dpow
      apply mul_le_mul_of_nonneg_left hNe_pow hpos_2pow
    have h2 : (2 : ℝ) ^ 160 * ((2 : ℝ) ^ le d n) ^ 10 * (d : ℝ) ^ 16 ≤
             (2 : ℝ) ^ 160 * ((2 : ℝ) ^ le d n) ^ 10 * ((2 : ℝ) ^ ld d) ^ 16 := by
      apply mul_le_mul_of_nonneg_left hd_pow (mul_nonneg hpos_2pow hpos_2lepow)
    have h3 : (2 : ℝ) ^ 160 * ((2 : ℝ) ^ le d n) ^ 10 * ((2 : ℝ) ^ ld d) ^ 16
             = (2 : ℝ) ^ pB d n := by
      calc
        (2 : ℝ) ^ 160 * ((2 : ℝ) ^ le d n) ^ 10 * ((2 : ℝ) ^ ld d) ^ 16
            = (2 : ℝ) ^ 160 * ((2 : ℝ) ^ (le d n * 10)) * ((2 : ℝ) ^ (ld d * 16)) := by
              simp [pow_mul]
        _ = (2 : ℝ) ^ (160 + le d n * 10 + ld d * 16) := by
          rw [← pow_add, ← pow_add]
        _ = (2 : ℝ) ^ (10 * le d n + 16 * ld d + 160) := by ring
        _ = (2 : ℝ) ^ pB d n := rfl
    exact le_trans (le_trans h1 h2) h3.le
  calc
    (2 : ℝ) ^ 160 * Ne d n ^ 10 * (d : ℝ) ^ 16 * u d n
        = ((2 : ℝ) ^ 160 * (NeN d n : ℝ) ^ 10 * (d : ℝ) ^ 16) * (1 / (2 : ℝ) ^ pB d n) := by
          dsimp [u, Ne]
    _ ≤ (2 : ℝ) ^ pB d n * (1 / (2 : ℝ) ^ pB d n) := by
      gcongr
    _ = 1 := by field_simp [hpos_pB.ne']

theorem regime_eh {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n ≤ eh d n ∧ eh d n ≤ (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n := by
  have hle_pos : 1 ≤ le d n := by
    have hNeN_pos : 0 < NeN d n := by
      unfold NeN
      positivity
    by_contra! h0
    have h0' : le d n = 0 := by omega
    have hsize0 : (NeN d n).size = 0 := h0'
    have hzero : NeN d n = 0 := by
      simpa [Nat.size_eq_zero] using hsize0
    linarith
  have hld_pos : 1 ≤ ld d := by
    have hd_pos : 0 < d := by omega
    by_contra! h0
    have h0' : ld d = 0 := by omega
    have hsize0 : d.size = 0 := h0'
    have hzero : d = 0 := by
      simpa [Nat.size_eq_zero] using hsize0
    linarith
  have hNe_lt : Ne d n < (2 : ℝ) ^ le d n := by
    have h := Nat.lt_size_self (NeN d n)
    have h' : (NeN d n : ℝ) < (2 : ℝ) ^ (le d n : ℕ) := by exact_mod_cast h
    simpa [Ne] using h'
  have hd_lt : (d : ℝ) < (2 : ℝ) ^ ld d := by
    have h := Nat.lt_size_self d
    exact_mod_cast h
  have hNe_ge : (2 : ℝ) ^ (le d n - 1) ≤ Ne d n := by
    have h_lt : le d n - 1 < (NeN d n).size := by
      have : le d n - 1 < le d n := by omega
      simpa [le] using this
    have h_le := (Nat.lt_size (m := le d n - 1) (n := NeN d n)).mp h_lt
    have h_le' : (2 ^ (le d n - 1) : ℝ) ≤ (NeN d n : ℝ) := by exact_mod_cast h_le
    simpa [Ne] using h_le'
  have hd_ge : (2 : ℝ) ^ (ld d - 1) ≤ (d : ℝ) := by
    have h_lt : ld d - 1 < d.size := by
      have : ld d - 1 < ld d := by omega
      simpa [ld] using this
    have h_le := (Nat.lt_size (m := ld d - 1) (n := d)).mp h_lt
    have h_le' : (2 ^ (ld d - 1) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h_le
    simpa [ld] using h_le'
  have h_nonneg_d : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have h_nonneg_Ne : 0 ≤ Ne d n := by
    unfold Ne
    exact_mod_cast Nat.zero_le (NeN d n)
  have h_pos_Ne : 0 < Ne d n := by
    unfold Ne NeN
    positivity
  -- Key inequality for lower bound: 2^64 * d^6 * Ne^3 ≤ 2^(3*le + 6*ld + 64)
  have h_lower_key : (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n ^ 3 ≤ (2 : ℝ) ^ (3 * le d n + 6 * ld d + 64) := by
    have h_d_pow : (d : ℝ) ^ 6 < ((2 : ℝ) ^ ld d) ^ 6 := by
      gcongr
    have h_Ne_pow : Ne d n ^ 3 < ((2 : ℝ) ^ le d n) ^ 3 := by
      gcongr
    have h_d_pow' : ((2 : ℝ) ^ ld d) ^ 6 = (2 : ℝ) ^ (6 * ld d) := by
      calc
        ((2 : ℝ) ^ ld d) ^ 6 = (2 : ℝ) ^ (ld d * 6) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (6 * ld d) := by rw [mul_comm]
    have h_Ne_pow' : ((2 : ℝ) ^ le d n) ^ 3 = (2 : ℝ) ^ (3 * le d n) := by
      calc
        ((2 : ℝ) ^ le d n) ^ 3 = (2 : ℝ) ^ (le d n * 3) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (3 * le d n) := by rw [mul_comm]
    rw [h_d_pow'] at h_d_pow
    rw [h_Ne_pow'] at h_Ne_pow
    have h_prod : (d : ℝ) ^ 6 * Ne d n ^ 3 < (2 : ℝ) ^ (6 * ld d) * (2 : ℝ) ^ (3 * le d n) :=
      mul_lt_mul h_d_pow h_Ne_pow.le (pow_pos h_pos_Ne 3) (by positivity)
    have h_pow_add : (2 : ℝ) ^ (6 * ld d) * (2 : ℝ) ^ (3 * le d n) = (2 : ℝ) ^ (6 * ld d + 3 * le d n) := by
      rw [pow_add]
    rw [h_pow_add] at h_prod
    have h_sum : 6 * ld d + 3 * le d n = 3 * le d n + 6 * ld d := by omega
    rw [h_sum] at h_prod
    -- h_prod: d^6 * Ne^3 < 2^(3*le + 6*ld)
    have h_mul : (2 : ℝ) ^ 64 * ((d : ℝ) ^ 6 * Ne d n ^ 3) < (2 : ℝ) ^ 64 * (2 : ℝ) ^ (3 * le d n + 6 * ld d) :=
      mul_lt_mul_of_pos_left h_prod (by positivity)
    -- Now combine the RHS using pow_add, handling normalization
    have h_mul' : (2 : ℝ) ^ 64 * ((d : ℝ) ^ 6 * Ne d n ^ 3) < (2 : ℝ) ^ (64 + (3 * le d n + 6 * ld d)) := by
      -- h_mul: A < 2^64 * 2^(3*le + 6*ld)
      -- We need A < 2^(64 + (3*le + 6*ld))
      -- The RHS of h_mul may be normalized to 2^64 * (2^(3*le) * 2^(6*ld))
      -- So we use `h_mul.trans_le` with the appropriate inequality
      -- First, note that 2^64 * (2^(3*le) * 2^(6*ld)) ≤ 2^(64 + (3*le + 6*ld))
      -- because 2^(3*le) * 2^(6*ld) = 2^(3*le + 6*ld) and then 2^64 * 2^(3*le + 6*ld) = 2^(64 + (3*le + 6*ld))
      apply h_mul.trans_le
      -- Goal: 2^64 * 2^(3*le + 6*ld) ≤ 2^(64 + (3*le + 6*ld))
      -- But the LHS may be normalized. Let's use `rw` to handle both cases.
      -- Actually, the goal is: 2^64 * 2^(3*le + 6*ld) ≤ 2^(64 + (3*le + 6*ld))
      -- This is an equality by pow_add, so ≤ holds.
      -- But the LHS might be displayed as 2^64 * (2^(3*le) * 2^(6*ld))
      -- Let me use `rw [← pow_add, pow_add]` to close the goal:
      rw [← pow_add, pow_add]
    have h_sum2 : 64 + (3 * le d n + 6 * ld d) = 3 * le d n + 6 * ld d + 64 := by omega
    rw [h_sum2] at h_mul'
    -- h_mul': 2^64 * (d^6 * Ne^3) < 2^(3*le + 6*ld + 64)
    -- Reassociate to match the goal
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul'.le
  -- Lower bound: 2^64 * d^6 * Ne^3 * u ≤ eh
  have h_lower : (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n ≤ eh d n := by
    have h_pos_u : 0 ≤ u d n := by
      unfold u
      refine div_nonneg (by norm_num) (by positivity)
    calc
      (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n = ((2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n ^ 3) * u d n := by ring
      _ ≤ (2 : ℝ) ^ (3 * le d n + 6 * ld d + 64) * u d n :=
        mul_le_mul_of_nonneg_right h_lower_key h_pos_u
      _ = eh d n := by
        unfold u eh
        have h_pB : pB d n = 10 * le d n + 16 * ld d + 160 := rfl
        rw [h_pB]
        field_simp [show (2 : ℝ) ^ (10 * le d n + 16 * ld d + 160) ≠ 0 from by positivity]
        rw [← pow_add]
        apply congrArg (fun (e : ℕ) => (2 : ℝ) ^ e)
        omega
  -- Key inequality for upper bound: 2^(3*le + 6*ld + 64) ≤ 2^73 * d^6 * Ne^3
  have h_upper_key : (2 : ℝ) ^ (3 * le d n + 6 * ld d + 64) ≤ (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3 := by
    -- From hNe_ge: 2^(le - 1) ≤ Ne, we get 2^le ≤ 2 * Ne
    have h_Ne_bound : (2 : ℝ) ^ le d n ≤ 2 * Ne d n := by
      have h_pow : (2 : ℝ) ^ le d n = (2 : ℝ) * (2 : ℝ) ^ (le d n - 1) := by
        have h : le d n = (le d n - 1) + 1 := by omega
        nth_rw 1 [h]
        rw [pow_succ']
      rw [h_pow]
      gcongr
    -- From hd_ge: 2^(ld - 1) ≤ d, we get 2^ld ≤ 2 * d
    have h_d_bound : (2 : ℝ) ^ ld d ≤ 2 * (d : ℝ) := by
      have h_pow : (2 : ℝ) ^ ld d = (2 : ℝ) * (2 : ℝ) ^ (ld d - 1) := by
        have h : ld d = (ld d - 1) + 1 := by omega
        nth_rw 1 [h]
        rw [pow_succ']
      rw [h_pow]
      gcongr
    -- 2^(3*le) = (2^le)^3 ≤ (2*Ne)^3 = 8 * Ne^3
    have h_Ne_cube : (2 : ℝ) ^ (3 * le d n) ≤ 8 * Ne d n ^ 3 := by
      calc
        (2 : ℝ) ^ (3 * le d n) = ((2 : ℝ) ^ le d n) ^ 3 := by
          rw [← pow_mul, mul_comm]
        _ ≤ (2 * Ne d n) ^ 3 := by gcongr
        _ = 8 * Ne d n ^ 3 := by ring
    -- 2^(6*ld) = (2^ld)^6 ≤ (2*d)^6 = 64 * d^6
    have h_d_six : (2 : ℝ) ^ (6 * ld d) ≤ 64 * (d : ℝ) ^ 6 := by
      calc
        (2 : ℝ) ^ (6 * ld d) = ((2 : ℝ) ^ ld d) ^ 6 := by
          rw [← pow_mul, mul_comm]
        _ ≤ (2 * (d : ℝ)) ^ 6 := by gcongr
        _ = 64 * (d : ℝ) ^ 6 := by ring
    -- 2^(3*le + 6*ld + 64) = 2^64 * 2^(3*le) * 2^(6*ld)
    -- ≤ 2^64 * (8 * Ne^3) * (64 * d^6) = 2^64 * 512 * d^6 * Ne^3 = 2^73 * d^6 * Ne^3
    have h_pow_512 : (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
    calc
      (2 : ℝ) ^ (3 * le d n + 6 * ld d + 64) = (2 : ℝ) ^ ((3 * le d n + 6 * ld d) + 64) := by ring
      _ = (2 : ℝ) ^ (3 * le d n + 6 * ld d) * (2 : ℝ) ^ 64 := by rw [pow_add]
      _ = ((2 : ℝ) ^ (3 * le d n) * (2 : ℝ) ^ (6 * ld d)) * (2 : ℝ) ^ 64 := by rw [pow_add]
      _ = (2 : ℝ) ^ 64 * (2 : ℝ) ^ (3 * le d n) * (2 : ℝ) ^ (6 * ld d) := by ring
      _ ≤ (2 : ℝ) ^ 64 * (8 * Ne d n ^ 3) * (64 * (d : ℝ) ^ 6) := by
        have h_left : (2 : ℝ) ^ 64 * (2 : ℝ) ^ (3 * le d n) ≤ (2 : ℝ) ^ 64 * (8 * Ne d n ^ 3) := by
          gcongr
        exact mul_le_mul h_left h_d_six (by positivity) (by positivity)
      _ = ((2 : ℝ) ^ 64 * 512) * ((d : ℝ) ^ 6 * Ne d n ^ 3) := by ring
      _ = ((2 : ℝ) ^ 64 * (2 : ℝ) ^ 9) * ((d : ℝ) ^ 6 * Ne d n ^ 3) := by rw [h_pow_512]
      _ = (2 : ℝ) ^ (64 + 9) * ((d : ℝ) ^ 6 * Ne d n ^ 3) := by rw [pow_add]
      _ = (2 : ℝ) ^ 73 * ((d : ℝ) ^ 6 * Ne d n ^ 3) := by norm_num
      _ = (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3 := by ring
  -- Upper bound: eh ≤ 2^73 * d^6 * Ne^3 * u
  have h_upper : eh d n ≤ (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n := by
    have h_pos_u : 0 ≤ u d n := by
      unfold u
      refine div_nonneg (by norm_num) (by positivity)
    calc
      eh d n = (2 : ℝ) ^ (3 * le d n + 6 * ld d + 64) * u d n := by
        unfold u eh
        have h_pB : pB d n = 10 * le d n + 16 * ld d + 160 := rfl
        rw [h_pB]
        field_simp [show (2 : ℝ) ^ (10 * le d n + 16 * ld d + 160) ≠ 0 from by positivity]
        rw [← pow_add]
        apply congrArg (fun (e : ℕ) => (2 : ℝ) ^ e)
        omega
      _ ≤ ((2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3) * u d n := by
        gcongr
      _ = (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n ^ 3 * u d n := by ring
  exact And.intro h_lower h_upper

theorem ref_R_lower {d : ℕ} (hd : 1 ≤ d) : 157 ≤ R d := by
  -- cast hd to ℝ for arithmetic
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- Since d ≥ 1, we have 2d+2 ≥ 4
  have h_ineq1 : (4 : ℝ) ≤ 2 * (d : ℝ) + 2 := by nlinarith
  -- log is monotone, so log 4 ≤ log(2d+2)
  have h_log : Real.log (4 : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) :=
    Real.log_le_log (by norm_num) h_ineq1
  -- sqrt is monotone
  have h_sqrt : Real.sqrt (Real.log (4 : ℝ)) ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) :=
    Real.sqrt_le_sqrt h_log
  -- R d = 134 * d * sqrt(log(2d+2)) ≥ 134 * sqrt(log 4) since d ≥ 1
  have h_R : 134 * Real.sqrt (Real.log (4 : ℝ)) ≤ R d := by
    dsimp [R]
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (Real.log (4 : ℝ)) := Real.sqrt_nonneg _
    have h_nonneg_d : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have h1 : 134 * Real.sqrt (Real.log (4 : ℝ)) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (4 : ℝ)) := by
      nlinarith
    have h2 : 134 * (d : ℝ) * Real.sqrt (Real.log (4 : ℝ)) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      have h_nonneg_coeff : 0 ≤ 134 * (d : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_left h_sqrt h_nonneg_coeff
    nlinarith
  -- Now we need 157 ≤ 134 * sqrt(log 4), i.e., 157/134 ≤ sqrt(log 4)
  have h_log4_pos : 0 < Real.log (4 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have h_key : (157 : ℝ) / 134 ≤ Real.sqrt (Real.log (4 : ℝ)) := by
    rw [Real.le_sqrt (by norm_num : 0 ≤ (157 : ℝ) / 134) (by linarith)]
    -- Need (157/134)² ≤ log 4 = 2 * log 2
    rw [Real.log_four_eq]
    -- Real.log_two_gt_d9 gives 0.6931471803 < log 2
    have h_log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h_sq_ineq : ((157 : ℝ) / 134) ^ 2 ≤ 2 * (0.6931471803 : ℝ) := by norm_num
    nlinarith
  -- Combine: 157 = 134 * (157/134) ≤ 134 * sqrt(log 4) ≤ R d
  have h_final : (157 : ℝ) ≤ R d := by
    nlinarith
  exact_mod_cast h_final

theorem ref_R_upper {d : ℕ} (hd : 1 ≤ d) : R d ^ 2 ≤ 190 ^ 2 * (d : ℝ) ^ 3 := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 ≤ Real.log (2 * (d : ℝ) + 2) := by
    apply Real.log_nonneg
    nlinarith
  have hR_sq : R d ^ 2 = (134 : ℝ) ^ 2 * ((d : ℝ) ^ 2) * Real.log (2 * (d : ℝ) + 2) := by
    dsimp [R]
    calc
      (134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2
          = (134 * (d : ℝ)) ^ 2 * (Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 := by ring
      _ = ((134 : ℝ) ^ 2 * (d : ℝ) ^ 2) * Real.log (2 * (d : ℝ) + 2) := by
        rw [Real.sq_sqrt hpos]
        ring
      _ = (134 : ℝ) ^ 2 * ((d : ℝ) ^ 2) * Real.log (2 * (d : ℝ) + 2) := by ring
  have h_log_bound : Real.log (2 * (d : ℝ) + 2) ≤ 2 * (d : ℝ) := by
    have h_log_eq : Real.log (2 * (d : ℝ) + 2) = Real.log 2 + Real.log ((d : ℝ) + 1) := by
      have h_mul : 2 * (d : ℝ) + 2 = 2 * ((d : ℝ) + 1) := by ring
      rw [h_mul]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by nlinarith : (d : ℝ) + 1 ≠ 0)]
    rw [h_log_eq]
    have h_log2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h_log_dp1_le : Real.log ((d : ℝ) + 1) ≤ (d : ℝ) := by
      have hpos' : 0 < (d : ℝ) + 1 := by nlinarith
      have h := Real.log_le_sub_one_of_pos hpos'
      linarith
    have h_sum_lt : Real.log 2 + Real.log ((d : ℝ) + 1) < 0.6931471808 + (d : ℝ) := by linarith
    have h_final : 0.6931471808 + (d : ℝ) ≤ 2 * (d : ℝ) := by
      nlinarith
    linarith
  rw [hR_sq]
  have h_const : (134 : ℝ) ^ 2 * 2 ≤ (190 : ℝ) ^ 2 := by
    norm_num
  nlinarith

end AdversarialBco.Bit.PieceA
