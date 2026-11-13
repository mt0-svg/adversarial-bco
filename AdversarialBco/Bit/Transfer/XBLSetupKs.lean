/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupBL
public import AdversarialBco.Bit.Transfer.XBLMagLem

@[expose] public section

/-!
# BL's setup on the machine: its units are polynomial

`initUnits_le`: the units of `xinitBL` (`initUnits` at FRAME's `sF` and TRI's `sT`) are at most
`(10^7 + C_f 4^{k_f} + C_t (5 + C_f 4^{k_f})^{k_t}) W^{(k_f + 1)(k_t + 1) + 2}` with
`W = d m (size n + 1)(size M + 1)`, from `parG d n ≤ 4000 (size d + size n + 1)` (`parG_bound`) and `frMhat A b ≤ M`.
The arithmetic is `ks_poly`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP

theorem ks_poly (d m n M Mh G Cf kf Ct kt sf st : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hM : 1 ≤ M) (hMh : Mh ≤ M) (hG : G ≤ 4000 * (d.size + n.size + 1))
    (hsf : sf = Cf * (d + m + Mh.size + 1) ^ kf) (hst : st = Ct * (d + m + n.size + Mh.size + sf + 1) ^ kt) :
    (696 * G + 3222) + (1 + ((sf + (1 + ((1 + ((d + 1) * (2 + 6) + 3)) + (st + (1 + ((1 + (d * (2 + 6) + 3)) +
      (1 + (1 + (d * d * (2 + 6) + 3))))))))) + ((1 + (m * (((18 * d + 28) + ((d * 10 + 5) +
      ((1 + ((d * 10 + 5) + (1 + 3))) + 2))) + 3) + 3)) + ((1 + (1 + (1 + (1 + ((d * (1 + 6) + 3) +
      (1 + (d * (1 + 6) + 3))))))) + 6)))) ≤
      (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt) * (d * m * (n.size + 1) * (M.size + 1)) ^
        ((kf + 1) * (kt + 1) + 2) := by
  set W := d * m * (n.size + 1) * (M.size + 1) with hWdef
  set k := (kf + 1) * (kt + 1) + 2 with hkdef
  -- Basic bounds using Nat lemmas
  have hWpos : 1 ≤ W := by
    rw [hWdef]
    have hdpos : 0 < d := by omega
    have hmpos : 0 < m := by omega
    have hnpos : 0 < n.size + 1 := by omega
    have hMpos : 0 < M.size + 1 := by omega
    have hpos : 0 < d * m * (n.size + 1) * (M.size + 1) :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos hmpos) hnpos) hMpos
    omega
  have hdW : d ≤ W := by
    rw [hWdef]
    have hm' : 1 ≤ m := hm
    have hn' : 1 ≤ n.size + 1 := by omega
    have hM' : 1 ≤ M.size + 1 := by omega
    calc
      d = d * 1 := by simp
      _ ≤ d * m := Nat.mul_le_mul (le_refl d) hm'
      _ = d * m * 1 := by simp
      _ ≤ d * m * (n.size + 1) := Nat.mul_le_mul (le_refl _) hn'
      _ = d * m * (n.size + 1) * 1 := by simp
      _ ≤ d * m * (n.size + 1) * (M.size + 1) := Nat.mul_le_mul (le_refl _) hM'
  have hmW : m ≤ W := by
    rw [hWdef]
    have hd' : 1 ≤ d := hd
    have hn' : 1 ≤ n.size + 1 := by omega
    have hM' : 1 ≤ M.size + 1 := by omega
    calc
      m = 1 * m := by simp
      _ ≤ d * m := Nat.mul_le_mul hd' (le_refl m)
      _ = d * m * 1 := by simp
      _ ≤ d * m * (n.size + 1) := Nat.mul_le_mul (le_refl _) hn'
      _ = d * m * (n.size + 1) * 1 := by simp
      _ ≤ d * m * (n.size + 1) * (M.size + 1) := Nat.mul_le_mul (le_refl _) hM'
  have hnW : n.size + 1 ≤ W := by
    rw [hWdef]
    have hd' : 1 ≤ d := hd
    have hm' : 1 ≤ m := hm
    have hM' : 1 ≤ M.size + 1 := by omega
    have hdm : d ≤ d * m := by
      calc
        d = d * 1 := by simp
        _ ≤ d * m := Nat.mul_le_mul (le_refl d) hm'
    calc
      n.size + 1 = 1 * (n.size + 1) := by simp
      _ ≤ d * (n.size + 1) := Nat.mul_le_mul hd' (le_refl _)
      _ ≤ d * m * (n.size + 1) := Nat.mul_le_mul_right (n.size + 1) hdm
      _ = d * m * (n.size + 1) * 1 := by simp
      _ ≤ d * m * (n.size + 1) * (M.size + 1) := Nat.mul_le_mul (le_refl _) hM'
  have hMW : M.size + 1 ≤ W := by
    rw [hWdef]
    have hd' : 1 ≤ d := hd
    have hm' : 1 ≤ m := hm
    have hn' : 1 ≤ n.size + 1 := by omega
    have hdm : d ≤ d * m := by
      calc
        d = d * 1 := by simp
        _ ≤ d * m := Nat.mul_le_mul (le_refl d) hm'
    have h : d * m ≤ d * m * (n.size + 1) := by
      calc
        d * m = d * m * 1 := by simp
        _ ≤ d * m * (n.size + 1) := Nat.mul_le_mul (le_refl _) hn'
    calc
      M.size + 1 = 1 * (M.size + 1) := by simp
      _ ≤ d * (M.size + 1) := Nat.mul_le_mul hd' (le_refl _)
      _ ≤ d * m * (M.size + 1) := Nat.mul_le_mul hdm (le_refl _)
      _ ≤ d * m * (n.size + 1) * (M.size + 1) := Nat.mul_le_mul_right (M.size + 1) h
  have hMhW : Mh.size ≤ W := by
    have hMhsz : Mh.size ≤ M.size := Nat.size_le_size hMh
    have hMsz : M.size ≤ W := by
      -- M.size ≤ M.size + 1 ≤ W
      omega
    exact Nat.le_trans hMhsz hMsz
  have h_dsz_d : d.size ≤ d := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := d)
  -- Bound 1: 696*G + 3222 ≤ 5571222 * W ^ k
  have hG_bound : 696 * G + 3222 ≤ 5571222 * W ^ k := by
    have h_dsz_n : d.size + n.size + 1 ≤ d + n.size + 1 := by omega
    have hsum : d + n.size + 1 ≤ 2 * W := by omega
    have hG' : G ≤ 8000 * W := by omega
    have hbound : 696 * G + 3222 ≤ 696 * (8000 * W) + 3222 := by omega
    have hbound2 : 696 * (8000 * W) + 3222 ≤ 5571222 * W := by
      nlinarith
    have hWk : W ≤ W ^ k := by
      have hpos : 1 ≤ k := by
        rw [hkdef]
        omega
      have h := Nat.pow_le_pow_right hWpos hpos
      simpa [Nat.pow_one] using h
    have hfinal : 5571222 * W ≤ 5571222 * W ^ k := by omega
    omega
  -- Bound 2: sf ≤ Cf * 4 ^ kf * W ^ k
  have hsf_bound : sf ≤ Cf * 4 ^ kf * W ^ k := by
    rw [hsf]
    have hsum : d + m + Mh.size + 1 ≤ 4 * W := by omega
    have hpow : (d + m + Mh.size + 1) ^ kf ≤ (4 * W) ^ kf :=
      Nat.pow_le_pow_left hsum kf
    have hmul : Cf * (d + m + Mh.size + 1) ^ kf ≤ Cf * (4 * W) ^ kf :=
      Nat.mul_le_mul_left Cf hpow
    have hpow2 : (4 * W) ^ kf = 4 ^ kf * W ^ kf := by
      simp [mul_pow]
    rw [hpow2] at hmul
    have hWkf : W ^ kf ≤ W ^ k := by
      have hpos : kf ≤ k := by
        rw [hkdef]
        have hk : kf + 1 ≤ (kf + 1) * (kt + 1) := by
          have hkt : 1 ≤ kt + 1 := by omega
          nlinarith
        omega
      exact Nat.pow_le_pow_right hWpos hpos
    calc
      Cf * (d + m + Mh.size + 1) ^ kf ≤ Cf * (4 ^ kf * W ^ kf) := hmul
      _ = (Cf * 4 ^ kf) * W ^ kf := by ring
      _ ≤ (Cf * 4 ^ kf) * W ^ k := Nat.mul_le_mul_left _ hWkf
      _ = Cf * 4 ^ kf * W ^ k := by ring
  -- Bound 3: st ≤ Ct * (5 + Cf * 4 ^ kf) ^ kt * W ^ k
  have hst_bound : st ≤ Ct * (5 + Cf * 4 ^ kf) ^ kt * W ^ k := by
    rw [hst]
    have h_sf_bound : sf ≤ Cf * 4 ^ kf * W ^ kf := by
      rw [hsf]
      have hsum' : d + m + Mh.size + 1 ≤ 4 * W := by omega
      have hpow : (d + m + Mh.size + 1) ^ kf ≤ (4 * W) ^ kf :=
        Nat.pow_le_pow_left hsum' kf
      have hmul : Cf * (d + m + Mh.size + 1) ^ kf ≤ Cf * (4 * W) ^ kf :=
        Nat.mul_le_mul_left Cf hpow
      have hpow2 : (4 * W) ^ kf = 4 ^ kf * W ^ kf := by
        simp [mul_pow]
      rw [hpow2] at hmul
      simpa [mul_assoc] using hmul
    have h_sf_bound2 : sf ≤ Cf * 4 ^ kf * W ^ (kf + 1) := by
      have hpow : W ^ kf ≤ W ^ (kf + 1) := by
        have h : kf ≤ kf + 1 := by omega
        exact Nat.pow_le_pow_right hWpos h
      calc
        sf ≤ Cf * 4 ^ kf * W ^ kf := h_sf_bound
        _ ≤ Cf * 4 ^ kf * W ^ (kf + 1) := Nat.mul_le_mul_left (Cf * 4 ^ kf) hpow
    have h_base1 : d + m + n.size + Mh.size + 1 ≤ 4 * W := by omega
    have h_base : d + m + n.size + Mh.size + sf + 1 ≤ (5 + Cf * 4 ^ kf) * W ^ (kf + 1) := by
      have h4W : 4 * W ≤ 5 * W ^ (kf + 1) := by
        have hWle : W ≤ W ^ (kf + 1) := by
          have hpos : 1 ≤ kf + 1 := by omega
          have h := Nat.pow_le_pow_right hWpos hpos
          simpa [Nat.pow_one] using h
        omega
      have hsum : d + m + n.size + Mh.size + 1 ≤ 5 * W ^ (kf + 1) :=
        Nat.le_trans h_base1 h4W
      have htotal : d + m + n.size + Mh.size + sf + 1 ≤ 5 * W ^ (kf + 1) + Cf * 4 ^ kf * W ^ (kf + 1) := by
        have h_sf_le : d + m + n.size + Mh.size + sf + 1 ≤ d + m + n.size + Mh.size + 1 + Cf * 4 ^ kf * W ^ (kf + 1) := by
          omega
        exact Nat.le_trans h_sf_le (Nat.add_le_add_right hsum _)
      have hfactor : 5 * W ^ (kf + 1) + Cf * 4 ^ kf * W ^ (kf + 1) = (5 + Cf * 4 ^ kf) * W ^ (kf + 1) := by
        ring
      rw [hfactor] at htotal
      exact htotal
    have h_pow : (d + m + n.size + Mh.size + sf + 1) ^ kt ≤ ((5 + Cf * 4 ^ kf) * W ^ (kf + 1)) ^ kt :=
      Nat.pow_le_pow_left h_base kt
    have h_mul : Ct * (d + m + n.size + Mh.size + sf + 1) ^ kt ≤ Ct * ((5 + Cf * 4 ^ kf) * W ^ (kf + 1)) ^ kt :=
      Nat.mul_le_mul_left Ct h_pow
    have h_expand : ((5 + Cf * 4 ^ kf) * W ^ (kf + 1)) ^ kt = (5 + Cf * 4 ^ kf) ^ kt * (W ^ (kf + 1)) ^ kt := by
      simp [mul_pow]
    rw [h_expand] at h_mul
    have h_pow_mul : (W ^ (kf + 1)) ^ kt = W ^ ((kf + 1) * kt) := by
      simp [pow_mul]
    rw [h_pow_mul] at h_mul
    have h_exp_bound : (kf + 1) * kt ≤ k := by
      rw [hkdef]
      have h : (kf + 1) * kt ≤ (kf + 1) * (kt + 1) := by
        have hkt : kt ≤ kt + 1 := by omega
        exact Nat.mul_le_mul_left (kf + 1) hkt
      omega
    have h_pow_final : W ^ ((kf + 1) * kt) ≤ W ^ k :=
      Nat.pow_le_pow_right hWpos h_exp_bound
    have h_result : Ct * ((5 + Cf * 4 ^ kf) ^ kt * W ^ ((kf + 1) * kt)) ≤ Ct * ((5 + Cf * 4 ^ kf) ^ kt * W ^ k) :=
      Nat.mul_le_mul_left Ct (Nat.mul_le_mul_left _ h_pow_final)
    simpa [mul_assoc] using Nat.le_trans h_mul h_result
  -- Bound 4: polynomial part + 45 ≤ 1000 * W ^ k
  have h_poly_bound : d * 30 + d * m * 38 + d ^ 2 * 8 + m * 48 + 45 ≤ 1000 * W ^ k := by
    have hdm : d * m ≤ W * W :=
      Nat.mul_le_mul hdW hmW
    have hd2 : d ^ 2 ≤ W * W := by
      have h := Nat.pow_le_pow_left hdW 2
      simpa [Nat.pow_two] using h
    have h1 : d * 30 ≤ 30 * W := by omega
    have h2 : d * m * 38 ≤ 38 * W * W := by
      calc
        d * m * 38 ≤ (W * W) * 38 := Nat.mul_le_mul_right 38 hdm
        _ = 38 * W * W := by ring
    have h3 : d ^ 2 * 8 ≤ 8 * W * W := by
      calc
        d ^ 2 * 8 ≤ (W * W) * 8 := Nat.mul_le_mul_right 8 hd2
        _ = 8 * W * W := by ring
    have h4 : m * 48 ≤ 48 * W := by omega
    have h45' : 45 ≤ 45 * (W * W) := by
      have hpos : 1 ≤ W * W := by
        have hsq : 1 * 1 ≤ W * W := Nat.mul_le_mul hWpos hWpos
        simpa using hsq
      calc
        45 = 45 * 1 := by simp
        _ ≤ 45 * (W * W) := Nat.mul_le_mul_left 45 hpos
    -- Combine all bounds: sum ≤ 30*W + (38+8+45)*W*W + 48*W = 30*W + 91*W*W + 48*W = 78*W + 91*W*W
    -- Actually: 30*W + 48*W = 78*W, and 38*W*W + 8*W*W + 45*W*W = 91*W*W
    have hsum_le : d * 30 + d * m * 38 + d ^ 2 * 8 + m * 48 + 45 ≤ 78 * W + 91 * (W * W) := by
      have h12 : d * 30 + d * m * 38 ≤ 30 * W + 38 * W * W := Nat.add_le_add h1 h2
      have h34 : d ^ 2 * 8 + m * 48 + 45 ≤ 8 * W * W + 48 * W + 45 * (W * W) := by
        have h34' : d ^ 2 * 8 + m * 48 ≤ 8 * W * W + 48 * W := Nat.add_le_add h3 h4
        omega
      have hsum' : (30 * W + 38 * W * W) + (8 * W * W + 48 * W + 45 * (W * W)) = 78 * W + 91 * (W * W) := by ring
      omega
    have hW_le_Wk : W ≤ W ^ k := by
      have hpos : 1 ≤ k := by
        rw [hkdef]
        omega
      have h := Nat.pow_le_pow_right hWpos hpos
      simpa [Nat.pow_one] using h
    have hW2_le_Wk : W * W ≤ W ^ k := by
      have hpos : 2 ≤ k := by
        rw [hkdef]
        omega
      have h := Nat.pow_le_pow_right hWpos hpos
      simpa [Nat.pow_two] using h
    have h_bound : 78 * W + 91 * (W * W) ≤ 1000 * W ^ k := by
      have hW_term : 78 * W ≤ 78 * W ^ k := Nat.mul_le_mul_left 78 hW_le_Wk
      have hW2_term : 91 * (W * W) ≤ 91 * W ^ k := Nat.mul_le_mul_left 91 hW2_le_Wk
      have hsum : 78 * W + 91 * (W * W) ≤ 78 * W ^ k + 91 * W ^ k := Nat.add_le_add hW_term hW2_term
      have hcoeff : 78 * W ^ k + 91 * W ^ k = 169 * W ^ k := by ring
      rw [hcoeff] at hsum
      have h169 : 169 * W ^ k ≤ 1000 * W ^ k := by
        have hcoeff' : 169 ≤ 1000 := by norm_num
        exact Nat.mul_le_mul_right _ hcoeff'
      exact Nat.le_trans hsum h169
    exact Nat.le_trans hsum_le h_bound
  -- Combine all bounds
  -- First, rewrite the LHS using ring
  have hLHS : (696 * G + 3222) + (1 + ((sf + (1 + ((1 + ((d + 1) * (2 + 6) + 3)) + (st + (1 + ((1 + (d * (2 + 6) + 3)) +
      (1 + (1 + (d * d * (2 + 6) + 3))))))))) + ((1 + (m * (((18 * d + 28) + ((d * 10 + 5) +
      ((1 + ((d * 10 + 5) + (1 + 3))) + 2))) + 3) + 3)) + ((1 + (1 + (1 + (1 + ((d * (1 + 6) + 3) +
      (1 + (d * (1 + 6) + 3))))))) + 6)))) = 3267 + G * 696 + sf + d * 30 + d * m * 38 + d ^ 2 * 8 + st + m * 48 := by
    ring
  rw [hLHS]
  -- Goal: 3267 + G * 696 + sf + d * 30 + d * m * 38 + d ^ 2 * 8 + st + m * 48 ≤
  --   (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt) * W ^ k
  have hsum : 3267 + G * 696 + sf + d * 30 + d * m * 38 + d ^ 2 * 8 + st + m * 48 ≤
      (5571222 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt + 1000) * W ^ k := by
    have hG' : 3267 + G * 696 = 45 + (696 * G + 3222) := by omega
    rw [hG']
    have hsplit : 45 + (696 * G + 3222) + sf + d * 30 + d * m * 38 + d ^ 2 * 8 + st + m * 48 =
        (696 * G + 3222) + sf + (d * 30 + d * m * 38 + d ^ 2 * 8 + m * 48 + 45) + st := by omega
    rw [hsplit]
    have h_total : (696 * G + 3222) + sf + (d * 30 + d * m * 38 + d ^ 2 * 8 + m * 48 + 45) + st ≤
        5571222 * W ^ k + Cf * 4 ^ kf * W ^ k + 1000 * W ^ k + Ct * (5 + Cf * 4 ^ kf) ^ kt * W ^ k := by
      have h_add1 : (696 * G + 3222) + sf ≤ 5571222 * W ^ k + Cf * 4 ^ kf * W ^ k := by
        omega
      have h_add2 : (696 * G + 3222) + sf + (d * 30 + d * m * 38 + d ^ 2 * 8 + m * 48 + 45) + st ≤
          (5571222 * W ^ k + Cf * 4 ^ kf * W ^ k) + 1000 * W ^ k + Ct * (5 + Cf * 4 ^ kf) ^ kt * W ^ k := by
        omega
      omega
    have h_rhs : 5571222 * W ^ k + Cf * 4 ^ kf * W ^ k + 1000 * W ^ k + Ct * (5 + Cf * 4 ^ kf) ^ kt * W ^ k =
        (5571222 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt + 1000) * W ^ k := by ring
    rw [h_rhs] at h_total
    exact h_total
  have hfinal : (5571222 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt + 1000) * W ^ k ≤
      (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt) * W ^ k := by
    have hcoeff' : 5571222 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt + 1000 ≤ 10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt := by
      omega
    exact Nat.mul_le_mul_right _ hcoeff'
  exact Nat.le_trans hsum hfinal

/-- **The units of BL's setup are polynomial** in `W = d m (size n + 1)(size M + 1)`. -/
theorem initUnits_le {d n m M : ℕ} (Cf kf Ct kt : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hH : RealRAM.HeightLE A b M) (hM : 1 ≤ M) :
    initUnits d n m (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b) ≤
      (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt) * (d * m * (n.size + 1) * (M.size + 1)) ^
        ((kf + 1) * (kt + 1) + 2) := by
  have hG : parG d n ≤ 4000 * (d.size + n.size + 1) := by
    unfold parG gsm_prec
    exact parG_bound d n (BLP.Ne d n).size d.size (par d n).p (par d n).q (par d n).pF (par d n).B hd hn rfl rfl rfl
      rfl rfl rfl
  unfold initUnits callUnits s3Units s3rowUnits epochUnits
  exact ks_poly d m n M (RQ.frMhat A b) (parG d n) Cf kf Ct kt _ _ hd hm hM (frMhat_le_M A b hH hM) hG rfl rfl

end AdversarialBco.Bit.Transfer.BLM
