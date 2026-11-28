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
