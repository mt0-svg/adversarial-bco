/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameE

@[expose] public section

/-!
# The work term of FRAME

The units, the exponent bound and the register bound of `xframe` against `W = d + m + size M̂ + 1`: the units of the
branch for `d ≥ 2` below `10^7 W^11`, `64 frEx + 16` below `10^8 W^11`, the register bound below `10^4 W^9`, and the
bound `2 M̂^{2(d+1)} < 2^{10^8 W^11}` of the read-off for `d = 1`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco.Bit.RQ

theorem frG_le_W
    (d m M : ℕ) : frG d m M ≤ 3 * (d + m + Nat.size M + 1) ^ 3 := by
  set W := d + m + Nat.size M + 1 with hW
  have hsize_d : Nat.size d ≤ d := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := d)
  have hsize_m : Nat.size m ≤ m := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := m)
  have hW_ge_d1 : d + 1 ≤ W := by
    omega
  have hW_ge_sizeM : Nat.size M ≤ W := by
    omega
  have hsum : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ W + 2 * W * W := by
    have h1 : Nat.size d + Nat.size m ≤ d + m := Nat.add_le_add hsize_d hsize_m
    have h2 : d + m ≤ W := by omega
    have h3 : 2 * (d + 1) * Nat.size M ≤ 2 * W * W := by
      have htemp : 2 * (d + 1) ≤ 2 * W := Nat.mul_le_mul_left 2 hW_ge_d1
      have := Nat.mul_le_mul htemp hW_ge_sizeM
      -- this gives (2*(d+1)) * Nat.size M ≤ (2*W) * W
      -- but we need 2*(d+1)*Nat.size M ≤ 2*W*W
      -- these are the same by associativity
      simpa [mul_assoc] using this
    omega
  calc
    frG d m M = (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) := rfl
    _ ≤ W * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) :=
      Nat.mul_le_mul_right _ hW_ge_d1
    _ ≤ W * (W + 2 * W * W) := Nat.mul_le_mul_left _ hsum
    _ = W * (W + 2 * W ^ 2) := by
      simp [pow_two, mul_assoc]
    _ ≤ W * (W ^ 2 + 2 * W ^ 2) := by
      apply Nat.mul_le_mul_left W
      have hW_le_Wsq : W ≤ W ^ 2 := by
        by_cases hW0 : W = 0
        · rw [hW0]; simp
        · have hW1 : 1 ≤ W := Nat.one_le_of_lt (Nat.pos_of_ne_zero hW0)
          calc
            W = W * 1 := by simp
            _ ≤ W * W := Nat.mul_le_mul_left W hW1
            _ = W ^ 2 := by simp [sq]
      omega
    _ = W * (3 * W ^ 2) := by ring
    _ = 3 * (W ^ 3) := by ring
    _ = 3 * (d + m + Nat.size M + 1) ^ 3 := by simp [hW]

theorem frame1_hb
    (d m : ℕ) (M : ℕ) : 2 * ((M : ℤ) ^ (d + 1) * (M : ℤ) ^ (d + 1)) < 2 ^ (10 ^ 8 * (d + m + Nat.size M + 1) ^ 11) := by
  set W := d + m + Nat.size M + 1 with hW
  have hWpos : 1 ≤ W := by omega
  have hW_gt_0 : 0 < W := by omega
  have hM_nat : M < 2 ^ (Nat.size M) := Nat.lt_size_self M
  have hM_nonneg : 0 ≤ (M : ℤ) := by exact mod_cast Nat.zero_le M
  have hMpow_nonneg : 0 ≤ (M : ℤ) ^ (d + 1) := pow_nonneg hM_nonneg (d + 1)
  have h2pow_nonneg : 0 ≤ ((2 : ℤ) ^ (Nat.size M)) ^ (d + 1) :=
    pow_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) (Nat.size M)) (d + 1)
  have hM : (M : ℤ) ≤ (2 : ℤ) ^ (Nat.size M) := by exact mod_cast hM_nat.le
  have hMpow_nat : M ^ (d + 1) ≤ (2 ^ (Nat.size M)) ^ (d + 1) :=
    Nat.pow_le_pow_left hM_nat.le (d + 1)
  have hMpow : (M : ℤ) ^ (d + 1) ≤ ((2 : ℤ) ^ (Nat.size M)) ^ (d + 1) := by
    exact mod_cast hMpow_nat
  have hMpow' : ((2 : ℤ) ^ (Nat.size M)) ^ (d + 1) = (2 : ℤ) ^ ((Nat.size M) * (d + 1)) := by
    rw [pow_mul]
  have hMbound : (M : ℤ) ^ (d + 1) ≤ (2 : ℤ) ^ ((Nat.size M) * (d + 1)) := by
    calc
      (M : ℤ) ^ (d + 1) ≤ ((2 : ℤ) ^ (Nat.size M)) ^ (d + 1) := hMpow
      _ = (2 : ℤ) ^ ((Nat.size M) * (d + 1)) := hMpow'
  have h2pow_nonneg' : 0 ≤ (2 : ℤ) ^ ((Nat.size M) * (d + 1)) := pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) _
  have h_sq : ((M : ℤ) ^ (d + 1)) * ((M : ℤ) ^ (d + 1)) ≤ ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) * ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) :=
    mul_le_mul hMbound hMbound hMpow_nonneg h2pow_nonneg'
  have h_sq'' : ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) * ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) = (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1)) := by
    calc
      ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) * ((2 : ℤ) ^ ((Nat.size M) * (d + 1))) = (2 : ℤ) ^ (((Nat.size M) * (d + 1)) + ((Nat.size M) * (d + 1))) := by rw [pow_add]
      _ = (2 : ℤ) ^ (2 * ((Nat.size M) * (d + 1))) := by ring
      _ = (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1)) := by ring
  have h_exp_ineq : 2 * (Nat.size M) * (d + 1) + 1 < 10 ^ 8 * W ^ 11 := by
    have hs_le_W : Nat.size M ≤ W := by omega
    have hd_le_W : d + 1 ≤ W := by omega
    have h_mul : (Nat.size M) * (d + 1) ≤ W * W := Nat.mul_le_mul hs_le_W hd_le_W
    have h_bound : 2 * (Nat.size M) * (d + 1) + 1 ≤ 2 * W ^ 2 + 1 := by
      have h_sq_eq : W * W = W ^ 2 := by ring
      have h_mul' : (Nat.size M) * (d + 1) ≤ W * W := h_mul
      have h_mul'' : 2 * ((Nat.size M) * (d + 1)) ≤ 2 * (W * W) := Nat.mul_le_mul_left 2 h_mul'
      have h_sq_mul : 2 * (W * W) = 2 * W ^ 2 := by rw [h_sq_eq]
      have h_target : 2 * (Nat.size M) * (d + 1) ≤ 2 * W ^ 2 := by
        calc
          2 * (Nat.size M) * (d + 1) = 2 * ((Nat.size M) * (d + 1)) := by ring
          _ ≤ 2 * (W * W) := h_mul''
          _ = 2 * W ^ 2 := h_sq_mul
      omega
    have h_pow : W ^ 2 ≤ W ^ 11 := Nat.pow_le_pow_right hW_gt_0 (by omega : 2 ≤ 11)
    have h_mul_pow : 10 ^ 8 * W ^ 2 ≤ 10 ^ 8 * W ^ 11 := Nat.mul_le_mul_left (10 ^ 8) h_pow
    have h_ineq : 2 * W ^ 2 + 1 < 10 ^ 8 * W ^ 2 := by
      have hW_sq_ge_one : 1 ≤ W ^ 2 := by
        have : 1 ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hWpos 2
        simpa using this
      have h_factor : 1 ≤ (10 ^ 8 - 2) * W ^ 2 := by
        have h10 : 1 ≤ 10 ^ 8 - 2 := by omega
        calc
          1 = 1 * 1 := by omega
          _ ≤ (10 ^ 8 - 2) * 1 := Nat.mul_le_mul_right 1 h10
          _ ≤ (10 ^ 8 - 2) * W ^ 2 := Nat.mul_le_mul_left (10 ^ 8 - 2) hW_sq_ge_one
      omega
    omega
  have h_final : (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1) + 1) < (2 : ℤ) ^ (10 ^ 8 * W ^ 11) := by
    apply pow_lt_pow_right₀ (by norm_num : 1 < (2 : ℤ)) h_exp_ineq
  have h_two_mul_pow : 2 * ((2 : ℤ) ^ (2 * (Nat.size M) * (d + 1))) = (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1) + 1) := by
    calc
      2 * ((2 : ℤ) ^ (2 * (Nat.size M) * (d + 1))) = ((2 : ℤ) ^ 1) * ((2 : ℤ) ^ (2 * (Nat.size M) * (d + 1))) := by norm_num
      _ = (2 : ℤ) ^ (1 + 2 * (Nat.size M) * (d + 1)) := by rw [pow_add]
      _ = (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1) + 1) := by ring
  calc
    2 * ((M : ℤ) ^ (d + 1) * (M : ℤ) ^ (d + 1)) ≤ 2 * (((2 : ℤ) ^ (Nat.size M * (d + 1))) * ((2 : ℤ) ^ (Nat.size M * (d + 1)))) := by
      nlinarith
    _ = 2 * ((2 : ℤ) ^ (2 * (Nat.size M) * (d + 1))) := by
      rw [h_sq'']
    _ = (2 : ℤ) ^ (2 * (Nat.size M) * (d + 1) + 1) := h_two_mul_pow
    _ < (2 : ℤ) ^ (10 ^ 8 * W ^ 11) := h_final
    _ = 2 ^ (10 ^ 8 * (d + m + Nat.size M + 1) ^ 11) := by
      simp [hW]


theorem frKb_le_W
    (d m M : ℕ) : frKb d m (frEx d m M) + 2 ≤ 10 ^ 6 * (d + m + Nat.size M + 1) ^ 6 := by
  set W := d + m + Nat.size M + 1 with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    omega
  have hsize_d : Nat.size d ≤ W := by
    rw [hWdef]
    have h := (Nat.size_le (m := d) (n := d)).mpr (Nat.lt_two_pow_self (n := d))
    omega
  have hsize_m : Nat.size m ≤ W := by
    rw [hWdef]
    have h := (Nat.size_le (m := m) (n := m)).mpr (Nat.lt_two_pow_self (n := m))
    omega
  have hsize_M : Nat.size M ≤ W := by
    rw [hWdef]
    omega
  have hd1 : d + 1 ≤ W := by
    rw [hWdef]
    omega
  have hfrG : frG d m M ≤ 3 * W ^ 3 := by
    -- frG = (d+1)*(Nat.size d + Nat.size m + 2*(d+1)*Nat.size M)
    -- ≤ W * (W + W + 2*W*W) = W*(2W + 2W²) = 2W² + 2W³ ≤ 3W³ (for W ≥ 1)
    rw [hWdef]
    dsimp [frG]
    have hinner : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ 3 * (d + m + Nat.size M + 1) ^ 2 := by
      -- Each Nat.size ≤ d+m+Nat.size M+1, and d+1 ≤ d+m+Nat.size M+1
      have h1 : Nat.size d ≤ d + m + Nat.size M + 1 := by
        have h := (Nat.size_le (m := d) (n := d)).mpr (Nat.lt_two_pow_self (n := d))
        omega
      have h2 : Nat.size m ≤ d + m + Nat.size M + 1 := by
        have h := (Nat.size_le (m := m) (n := m)).mpr (Nat.lt_two_pow_self (n := m))
        omega
      have h3 : Nat.size M ≤ d + m + Nat.size M + 1 := by omega
      have h4 : d + 1 ≤ d + m + Nat.size M + 1 := by omega
      nlinarith
    have hd1' : d + 1 ≤ d + m + Nat.size M + 1 := by omega
    nlinarith
  have hfrEx : frEx d m M ≤ 69 * W ^ 3 := by
    rw [hWdef]
    dsimp [frEx]
    have h4d : 4 * d ≤ 4 * (d + m + Nat.size M + 1) := by omega
    have hdm : (d + 1) * Nat.size M ≤ (d + m + Nat.size M + 1) * (d + m + Nat.size M + 1) := by
      have hd1 : d + 1 ≤ d + m + Nat.size M + 1 := by omega
      have hM : Nat.size M ≤ d + m + Nat.size M + 1 := by omega
      nlinarith
    have h40 : 40 ≤ 40 * (d + m + Nat.size M + 1) ^ 3 := by
      have hpos : 1 ≤ d + m + Nat.size M + 1 := by omega
      have hsq : 1 ≤ (d + m + Nat.size M + 1) ^ 3 := by
        exact Nat.one_le_pow 3 (d + m + Nat.size M + 1) hWpos
      omega
    have h8frG : 8 * frG d m M ≤ 8 * (3 * (d + m + Nat.size M + 1) ^ 3) := by
      -- need frG bound in terms of the expression, not W
      have hfrG' : frG d m M ≤ 3 * (d + m + Nat.size M + 1) ^ 3 := by
        -- from hfrG but without W
        rw [hWdef] at hfrG
        exact hfrG
      nlinarith
    nlinarith
  rw [hWdef]
  dsimp [frKb, frRowK]
  -- Goal: 4 + (m * (46*d + 59 + 2) + 2) + (200 * (frEx d m M + 1) ^ 2 + 8) + 2 ≤
  --   10^6 * (d + m + Nat.size M + 1) ^ 6
  -- Simplify: 4 + (m*(46*d+61) + 2) + (200*(E+1)^2 + 8) + 2
  -- = 16 + m*(46*d+61) + 200*(E+1)^2
  set X := d + m + Nat.size M + 1 with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    omega
  have hm : m ≤ X := by
    rw [hXdef]
    omega
  have hd' : d ≤ X := by
    rw [hXdef]
    omega
  have hsizeM' : Nat.size M ≤ X := by
    rw [hXdef]
    omega
  have hfrEx' : frEx d m M + 1 ≤ 69 * X ^ 3 + 1 := by
    have : frEx d m M ≤ 69 * X ^ 3 := hfrEx
    omega
  -- Bound m*(46*d+61) ≤ X*(46*X+61) = 46*X^2 + 61*X
  have hmterm : m * (46 * d + 61) ≤ X * (46 * X + 61) := by
    nlinarith
  -- Bound (frEx+1)^2 ≤ (69*X^3+1)^2
  have hsqterm : (frEx d m M + 1) ^ 2 ≤ (69 * X ^ 3 + 1) ^ 2 :=
    Nat.pow_le_pow_left hfrEx' 2
  have h200term : 200 * (frEx d m M + 1) ^ 2 ≤ 200 * (69 * X ^ 3 + 1) ^ 2 := by
    nlinarith
  -- Now LHS ≤ 16 + X*(46*X+61) + 200*(69*X^3+1)^2
  -- Expand RHS of this bound:
  -- X*(46*X+61) = 46*X^2 + 61*X
  -- (69*X^3+1)^2 = 4761*X^6 + 138*X^3 + 1
  -- 200*(4761*X^6 + 138*X^3 + 1) = 952200*X^6 + 27600*X^3 + 200
  -- So LHS ≤ 16 + 46*X^2 + 61*X + 952200*X^6 + 27600*X^3 + 200
  -- = 952200*X^6 + 27600*X^3 + 46*X^2 + 61*X + 216
  -- Need ≤ 10^6 * X^6 = 1000000*X^6
  -- i.e., 27600*X^3 + 46*X^2 + 61*X + 216 ≤ 47800*X^6
  have hmain : 16 + X * (46 * X + 61) + 200 * (69 * X ^ 3 + 1) ^ 2 ≤ 10 ^ 6 * X ^ 6 := by
    -- Case split on X = 1 vs X ≥ 2
    by_cases hX1 : X = 1
    · rw [hX1]; norm_num
    · have hX2 : 2 ≤ X := by omega
      -- For X ≥ 2, we have X^6 ≥ 64, so 47800*X^6 ≥ 3059200
      -- and 27600*X^3 + 46*X^2 + 61*X + 216 ≤ 28123*X^3
      -- and 28123*X^3 ≤ 47800*X^6 (since X^3 ≥ 8, 47800*X^3 ≥ 382400 > 28123)
      have hXcube_pos : 1 ≤ X ^ 3 := Nat.one_le_pow 3 X hXpos
      have hX6_pos : 1 ≤ X ^ 6 := Nat.one_le_pow 6 X hXpos
      -- Show X^3 ≤ X^6
      have hcube_le_6 : X ^ 3 ≤ X ^ 6 := by
        calc
          X ^ 3 = X ^ 3 * 1 := by omega
          _ ≤ X ^ 3 * X ^ 3 := Nat.mul_le_mul_left (X ^ 3) hXcube_pos
          _ = X ^ 6 := by ring
      -- Show X ≤ X^6
      have hX_le_X6 : X ≤ X ^ 6 := by
        have h_one_le : 1 ≤ X ^ 5 := Nat.one_le_pow 5 X hXpos
        calc
          X = X * 1 := by omega
          _ ≤ X * X ^ 5 := Nat.mul_le_mul_left X h_one_le
          _ = X ^ 6 := by ring
      -- Show X^2 ≤ X^6
      have hsq_le_6 : X ^ 2 ≤ X ^ 6 := by
        have h_one_le : 1 ≤ X ^ 4 := Nat.one_le_pow 4 X hXpos
        calc
          X ^ 2 = X ^ 2 * 1 := by omega
          _ ≤ X ^ 2 * X ^ 4 := Nat.mul_le_mul_left (X ^ 2) h_one_le
          _ = X ^ 6 := by ring
      have hbound : 27600 * X ^ 3 + 46 * X ^ 2 + 61 * X + 216 ≤ 47800 * X ^ 6 := by
        have h1 : 27600 * X ^ 3 ≤ 27600 * X ^ 6 := Nat.mul_le_mul_left 27600 hcube_le_6
        have h2 : 46 * X ^ 2 ≤ 46 * X ^ 6 := Nat.mul_le_mul_left 46 hsq_le_6
        have h3 : 61 * X ≤ 61 * X ^ 6 := Nat.mul_le_mul_left 61 hX_le_X6
        have h4 : 216 ≤ 216 * X ^ 6 := by
          have : 1 ≤ X ^ 6 := hX6_pos
          omega
        omega
      -- Now compute the expanded LHS
      -- 16 + X*(46*X+61) + 200*(69*X^3+1)^2
      -- = 16 + 46*X^2 + 61*X + 200*(4761*X^6 + 138*X^3 + 1)
      -- = 16 + 46*X^2 + 61*X + 952200*X^6 + 27600*X^3 + 200
      -- = 952200*X^6 + 27600*X^3 + 46*X^2 + 61*X + 216
      -- ≤ 952200*X^6 + 47800*X^6 = 1000000*X^6 = 10^6*X^6
      have hcalc : 16 + X * (46 * X + 61) + 200 * (69 * X ^ 3 + 1) ^ 2 ≤
          10 ^ 6 * X ^ 6 := by
        nlinarith
      exact hcalc
  -- Now chain the inequalities
  have hLHS : 4 + (m * (46 * d + 61) + 2) + (200 * (frEx d m M + 1) ^ 2 + 8) + 2 ≤
      16 + X * (46 * X + 61) + 200 * (69 * X ^ 3 + 1) ^ 2 := by
    nlinarith
  have hRHS : 16 + X * (46 * X + 61) + 200 * (69 * X ^ 3 + 1) ^ 2 ≤ 10 ^ 6 * X ^ 6 :=
    hmain
  -- Combine
  have hgoal : 4 + (m * (46 * d + 61) + 2) + (200 * (frEx d m M + 1) ^ 2 + 8) + 2 ≤
      10 ^ 6 * X ^ 6 := le_trans hLHS hRHS
  rw [hXdef]
  exact hgoal


theorem frE0U_le_W
    (d m M : ℕ) : frE0U d m M ≤ 100 * (d + m + Nat.size M + 1) ^ 3 := by
  set W := d + m + Nat.size M + 1 with hW
  have hWpos : 1 ≤ W := by
    omega
  have h_size_d : Nat.size d ≤ d := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := d)
  have h_size_m : Nat.size m ≤ m := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := m)
  have h_size_M : Nat.size M ≤ M := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := M)
  have h_size_d_W : Nat.size d ≤ W := by
    apply le_trans h_size_d
    omega
  have h_size_m_W : Nat.size m ≤ W := by
    apply le_trans h_size_m
    omega
  have h_size_M_W : Nat.size M ≤ W := by
    omega
  have h_d1_W : d + 1 ≤ W := by
    omega
  have hm_W : m ≤ W := by
    omega
  have h_d1_m_le_W_sq : (d + 1) * m ≤ W ^ 2 := by
    nlinarith
  have h_frG_le : frG d m M ≤ 3 * W ^ 3 := by
    unfold frG
    have h_inner : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ 3 * W ^ 2 := by
      have h1 : Nat.size d ≤ W := h_size_d_W
      have h2 : Nat.size m ≤ W := h_size_m_W
      have h3 : 2 * (d + 1) * Nat.size M ≤ 2 * W * W := by
        have hd1 : d + 1 ≤ W := h_d1_W
        have hM : Nat.size M ≤ W := h_size_M_W
        nlinarith
      nlinarith
    have h_mul : (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤ W * (3 * W ^ 2) := by
      apply Nat.mul_le_mul h_d1_W h_inner
    calc
      (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤ W * (3 * W ^ 2) := h_mul
      _ = 3 * W ^ 3 := by ring
  have h_frE0U_eq : frE0U d m M = 18 * ((d + 1) * m) + 12 * (d + 1) + 4 * frG d m M + 30 := by
    unfold frE0U
    zify
    ring_nf
  rw [h_frE0U_eq]
  have hWcube : 1 ≤ W ^ 3 := Nat.one_le_pow 3 W (by omega)
  nlinarith

set_option maxHeartbeats 800000 in
theorem frEx_lt_C
    (d m M : ℕ) : 64 * frEx d m M + 16 < 10 ^ 8 * (d + m + Nat.size M + 1) ^ 11 := by
  set W := d + m + Nat.size M + 1 with hW
  have hWpos : 0 < W := by
    rw [hW]
    omega
  have h_size_le : ∀ n : ℕ, Nat.size n ≤ n := by
    intro n
    exact (Nat.size_le (m := n) (n := n)).mpr (Nat.lt_two_pow_self (n := n))
  have h_sd_W : Nat.size d ≤ W :=
    calc
      Nat.size d ≤ d := h_size_le d
      _ ≤ d + m + Nat.size M + 1 := by omega
      _ = W := by rw [hW]
  have h_sm_W : Nat.size m ≤ W :=
    calc
      Nat.size m ≤ m := h_size_le m
      _ ≤ d + m + Nat.size M + 1 := by omega
      _ = W := by rw [hW]
  have h_sM_W : Nat.size M ≤ W := by
    rw [hW]
    calc
      Nat.size M ≤ Nat.size M + (d + m + 1) := Nat.le_add_right _ _
      _ = d + m + Nat.size M + 1 := by omega
  have hA : d + 1 ≤ W := by rw [hW]; omega
  have hd_W : d ≤ W := by rw [hW]; omega
  have h_sq_le_cube : W ^ 2 ≤ W ^ 3 :=
    Nat.pow_le_pow_right hWpos (by decide : 2 ≤ 3)
  have h_le_cube : W ≤ W ^ 3 := by
    calc
      W = W ^ 1 := by simp
      _ ≤ W ^ 3 := Nat.pow_le_pow_right hWpos (by decide : 1 ≤ 3)
  have h_frG_le : frG d m M ≤ 4 * W ^ 3 := by
    unfold frG
    have h_inner : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ 2 * W + 2 * W ^ 2 := by
      have h1 : 2 * (d + 1) * Nat.size M ≤ 2 * W ^ 2 := by
        calc
          2 * (d + 1) * Nat.size M ≤ 2 * W * W :=
            Nat.mul_le_mul (Nat.mul_le_mul (by rfl) hA) h_sM_W
          _ = 2 * W ^ 2 := by ring
      have h_total : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ W + W + 2 * W ^ 2 :=
        Nat.add_le_add (Nat.add_le_add h_sd_W h_sm_W) h1
      have h_WW : W + W = 2 * W := by ring
      omega
    calc
      (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤
          W * (2 * W + 2 * W ^ 2) := Nat.mul_le_mul hA h_inner
      _ = 2 * W ^ 2 + 2 * W ^ 3 := by ring
      _ ≤ 2 * W ^ 3 + 2 * W ^ 3 := by
        omega
      _ = 4 * W ^ 3 := by ring
  have h_frEx_le : frEx d m M ≤ 77 * W ^ 3 := by
    unfold frEx
    have h1 : 8 * frG d m M ≤ 8 * (4 * W ^ 3) := Nat.mul_le_mul (by rfl) h_frG_le
    have h2 : 4 * d ≤ 4 * W ^ 3 :=
      Nat.mul_le_mul (by rfl) (le_trans hd_W h_le_cube)
    have h3 : (d + 1) * Nat.size M ≤ W * W := Nat.mul_le_mul hA h_sM_W
    have h3' : W * W = W ^ 2 := by ring
    have h4 : 40 ≤ 40 * W ^ 3 := by
      have hpos : 1 ≤ W ^ 3 := by
        calc
          1 = W ^ 0 := by simp
          _ ≤ W ^ 3 := Nat.pow_le_pow_right hWpos (by decide : 0 ≤ 3)
      omega
    omega
  have h_main : 64 * frEx d m M + 16 < 10 ^ 8 * W ^ 11 := by
    have h1 : 64 * frEx d m M + 16 ≤ 64 * (77 * W ^ 3) + 16 := by
      omega
    have h2 : 64 * (77 * W ^ 3) + 16 ≤ 4944 * W ^ 3 := by
      have hpos : 1 ≤ W ^ 3 := by
        calc
          1 = W ^ 0 := by simp
          _ ≤ W ^ 3 := Nat.pow_le_pow_right hWpos (by decide : 0 ≤ 3)
      omega
    have h3 : 4944 * W ^ 3 < 10 ^ 8 * W ^ 11 := by
      have h_cube_le : W ^ 3 ≤ W ^ 11 :=
        Nat.pow_le_pow_right hWpos (by decide : 3 ≤ 11)
      have h_coeff : 4944 < 10 ^ 8 := by norm_num
      have h_temp : 4944 * W ^ 3 ≤ 4944 * W ^ 11 := Nat.mul_le_mul (by rfl) h_cube_le
      have h_temp2 : 4944 * W ^ 11 < 10 ^ 8 * W ^ 11 :=
        Nat.mul_lt_mul_of_pos_right h_coeff (Nat.pow_pos hWpos (n := 11))
      exact Nat.lt_of_le_of_lt h_temp h_temp2
    exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt h2 h3)
  simpa [hW] using h_main

theorem frN_le_W (d m M : ℕ) : frN d (frER d m M) ≤ 9 * (d + m + Nat.size M + 1) ^ 5 := by
  set W := d + m + Nat.size M + 1 with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    omega
  have hWge1 : 1 ≤ W := by omega
  have hdW : d ≤ W := by
    rw [hWdef]
    omega
  have hmW : m ≤ W := by
    rw [hWdef]
    omega
  have hsMW : Nat.size M ≤ W := by
    rw [hWdef]
    omega
  have h_d1_le_W : d + 1 ≤ W := by
    rw [hWdef]
    omega
  have h_size_d_le_d : Nat.size d ≤ d := by
    have h : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
    exact ((Nat.size_le (m := d) (n := d)).mpr h)
  have h_size_m_le_m : Nat.size m ≤ m := by
    have h : m < 2 ^ m := Nat.lt_two_pow_self (n := m)
    exact ((Nat.size_le (m := m) (n := m)).mpr h)
  have h_size_d_le_W : Nat.size d ≤ W := by omega
  have h_size_m_le_W : Nat.size m ≤ W := by omega
  -- frER_leG from Deps
  have hfrER_le_frG : frER d m M ≤ frG d m M := frER_leG d m M
  -- Bound frG ≤ 3*W^3
  have hfrG_le_3W3 : frG d m M ≤ 3 * W ^ 3 := by
    rw [frG]
    have h_inner : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ 2 * W + 2 * W * W := by
      have hsum : Nat.size d + Nat.size m ≤ 2 * W := by
        omega
      have hprod : 2 * (d + 1) * Nat.size M ≤ 2 * W * W := by
        have h_mul : (d + 1) * Nat.size M ≤ W * W := by
          apply Nat.mul_le_mul h_d1_le_W hsMW
        calc
          2 * (d + 1) * Nat.size M = 2 * ((d + 1) * Nat.size M) := by ring
          _ ≤ 2 * (W * W) := Nat.mul_le_mul_left 2 h_mul
          _ = 2 * W * W := by ring
      omega
    have h_d1W' : d + 1 ≤ W := h_d1_le_W
    -- (d+1) * (inner) ≤ W * (2*W + 2*W*W) = 2*W^2 + 2*W^3
    have h_mul : (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤ W * (2 * W + 2 * W * W) := by
      apply Nat.mul_le_mul h_d1W' h_inner
    have h_W_mul : W * (2 * W + 2 * W * W) = 2 * W ^ 2 + 2 * W ^ 3 := by ring
    rw [h_W_mul] at h_mul
    -- Now we need 2*W^2 + 2*W^3 ≤ 3*W^3
    by_cases hW2 : W < 2
    · -- W = 1
      have hW1 : W = 1 := by omega
      rw [hW1]
      -- Since W=1, we have d=0, m=0, size M=0
      have hd0 : d = 0 := by
        have : d ≤ W := hdW
        rw [hW1] at this
        omega
      have hm0 : m = 0 := by
        have : m ≤ W := hmW
        rw [hW1] at this
        omega
      have hsM0 : Nat.size M = 0 := by
        have : Nat.size M ≤ W := hsMW
        rw [hW1] at this
        omega
      rw [hd0, hm0, hsM0]
      simp
    · -- W ≥ 2
      have hW2' : 2 ≤ W := by omega
      have hineq : 2 * W ^ 2 ≤ W ^ 3 := by
        calc
          2 * W ^ 2 ≤ W * W ^ 2 := Nat.mul_le_mul_right (W ^ 2) hW2'
          _ = W ^ 3 := by ring
      omega
  -- Combine: frER ≤ 3*W^3
  have hfrER_le_3W3 : frER d m M ≤ 3 * W ^ 3 := by omega
  -- Monotonicity of frN in second argument
  have hfrN_mono : frN d (frER d m M) ≤ frN d (3 * W ^ 3) := by
    unfold frN
    have h' : frER d m M + 1 ≤ (3 * W ^ 3) + 1 := by omega
    have h_mul : 2 * d * (d + 1) * (frER d m M + 1) ≤ 2 * d * (d + 1) * ((3 * W ^ 3) + 1) := by
      apply Nat.mul_le_mul_left (2 * d * (d + 1)) h'
    omega
  -- Now bound frN d (3*W^3) ≤ 9*W^5
  have hfrN_bound : frN d (3 * W ^ 3) ≤ 9 * W ^ 5 := by
    unfold frN
    have hprod : d * (d + 1) ≤ W * W := by
      apply Nat.mul_le_mul hdW h_d1_le_W
    have h_mul : 2 * d * (d + 1) * (3 * W ^ 3 + 1) ≤ 2 * W * W * (3 * W ^ 3 + 1) := by
      have h_factor : 2 * d * (d + 1) ≤ 2 * W * W := by
        calc
          2 * d * (d + 1) = 2 * (d * (d + 1)) := by ring
          _ ≤ 2 * (W * W) := Nat.mul_le_mul_left 2 hprod
          _ = 2 * W * W := by ring
      apply Nat.mul_le_mul_right (3 * W ^ 3 + 1) h_factor
    have h_target : 6 * W ^ 5 + 2 * W ^ 2 + 1 ≤ 9 * W ^ 5 := by
      have hineq : 2 * W ^ 2 + 1 ≤ 3 * W ^ 5 := by
        have hWpos' : 0 < W := hWpos
        have hsq_cube : W ^ 2 ≤ W ^ 5 := by
          calc
            W ^ 2 = W ^ 2 * 1 := by ring
            _ ≤ W ^ 2 * W ^ 3 := Nat.mul_le_mul_left (W ^ 2) (Nat.one_le_pow 3 W hWpos')
            _ = W ^ 5 := by ring
        have hcube : 1 ≤ W ^ 5 := Nat.one_le_pow 5 W hWpos'
        omega
      omega
    calc
      2 * d * (d + 1) * (3 * W ^ 3 + 1) + 1 ≤ 2 * W * W * (3 * W ^ 3 + 1) + 1 := by omega
      _ = 6 * W ^ 5 + 2 * W ^ 2 + 1 := by ring
      _ ≤ 9 * W ^ 5 := h_target
  -- Combine everything
  calc
    frN d (frER d m M) ≤ frN d (3 * W ^ 3) := hfrN_mono
    _ ≤ 9 * W ^ 5 := hfrN_bound
    _ = 9 * (d + m + Nat.size M + 1) ^ 5 := by rw [hWdef]

theorem frRegB_le_W (d m M : ℕ) : frRegB d m M ≤ 10 ^ 4 * (d + m + Nat.size M + 1) ^ 9 := by
  set W := d + m + Nat.size M + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have h_d1_W : d + 1 ≤ W := by omega
  have h_dm1_W : d + m + 1 ≤ W := by omega
  have h_size_d_le_d : Nat.size d ≤ d := by
    have h_lt : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
    exact ((Nat.size_le (m := d) (n := d)).mpr h_lt)
  have h_size_m_le_m : Nat.size m ≤ m := by
    have h_lt : m < 2 ^ m := Nat.lt_two_pow_self (n := m)
    exact ((Nat.size_le (m := m) (n := m)).mpr h_lt)
  have h_size_M_le_M : Nat.size M ≤ M := by
    have h_lt : M < 2 ^ M := Nat.lt_two_pow_self (n := M)
    exact ((Nat.size_le (m := M) (n := M)).mpr h_lt)
  have h_size_d_W : Nat.size d ≤ W := by omega
  have h_size_m_W : Nat.size m ≤ W := by omega
  have h_size_M_W : Nat.size M ≤ W := by omega
  have h_size_sum_le_W : Nat.size d + Nat.size m ≤ W := by
    have h : Nat.size d + Nat.size m ≤ d + m := Nat.add_le_add h_size_d_le_d h_size_m_le_m
    omega
  have h_2dp1_sizeM_le_2W2 : 2 * (d + 1) * Nat.size M ≤ 2 * W ^ 2 := by
    have h : (d + 1) * Nat.size M ≤ W * W := Nat.mul_le_mul h_d1_W h_size_M_W
    have h' : 2 * (d + 1) * Nat.size M ≤ 2 * (W * W) := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 h
    simpa [Nat.pow_two] using h'
  have h_inner : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ 3 * W ^ 2 := by
    have h_sum : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ W + 2 * W ^ 2 :=
      add_le_add h_size_sum_le_W h_2dp1_sizeM_le_2W2
    have h_W_le_W2 : W ≤ W ^ 2 := by
      have h := Nat.mul_le_mul_left W hW1
      simpa [Nat.pow_two] using h
    have h_final : W + 2 * W ^ 2 ≤ 3 * W ^ 2 := by omega
    exact le_trans h_sum h_final
  have h_frG_le_3W3 : frG d m M ≤ 3 * W ^ 3 := by
    dsimp [frG]
    have h_prod : (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤ W * (3 * W ^ 2) :=
      Nat.mul_le_mul h_d1_W h_inner
    have h_eq : W * (3 * W ^ 2) = 3 * W ^ 3 := by ring
    calc
      (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) ≤ W * (3 * W ^ 2) := h_prod
      _ = 3 * W ^ 3 := h_eq
  have h_sum_le_4W3 : d + m + frG d m M + 1 ≤ 4 * W ^ 3 := by
    have h_sum : d + m + frG d m M + 1 ≤ W + 3 * W ^ 3 := by omega
    have h_W_le_W3 : W ≤ W ^ 3 := by
      have hW_le_W2 : W ≤ W ^ 2 := by
        have h := Nat.mul_le_mul_left W hW1
        simpa [Nat.pow_two] using h
      have hW2_le_W3 : W ^ 2 ≤ W ^ 3 := by
        have h_mul : 1 * W ^ 2 ≤ W * W ^ 2 := Nat.mul_le_mul_right (W ^ 2) hW1
        simpa [Nat.pow_succ, Nat.mul_comm] using h_mul
      exact le_trans hW_le_W2 hW2_le_W3
    have h_final : W + 3 * W ^ 3 ≤ 4 * W ^ 3 := by omega
    exact le_trans h_sum h_final
  calc
    frRegB d m M = 100 * (d + m + frG d m M + 1) ^ 3 := rfl
    _ ≤ 100 * (4 * W ^ 3) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h_sum_le_4W3 3)
    _ = 100 * (4 ^ 3 * (W ^ 3) ^ 3) := by rw [mul_pow]
    _ = 100 * (64 * (W ^ 3) ^ 3) := by norm_num
    _ = 100 * (64 * W ^ (3 * 3)) := by rw [pow_mul]
    _ = 100 * (64 * W ^ 9) := by norm_num
    _ = 6400 * W ^ 9 := by ring
    _ ≤ 10000 * W ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 10 ^ 4 * W ^ 9 := by norm_num
    _ = 10 ^ 4 * (d + m + Nat.size M + 1) ^ 9 := by rw [hW]

theorem frBrU_le_W (d m M : ℕ) (hd : 1 ≤ d) : frBrU d m M ≤ 10 ^ 7 * (d + m + Nat.size M + 1) ^ 11 := by
  have hN := frN_le_W d m M
  have hK := frKb_le_W d m M
  have hE0 := frE0U_le_W d m M
  have hG := frG_le_W d m M
  have he := frER_leG d m M
  obtain ⟨-, c2, c3⟩ := clog_bounds
  have hcd := c2 d
  have hcq := c3 d hd
  have hNK := Nat.mul_le_mul hN hK
  unfold frBrU frP frQ frOutU
  generalize hW : d + m + Nat.size M + 1 = W at hN hK hE0 hG hNK ⊢
  have hW1 : 1 ≤ W := by omega
  have hdW : d ≤ W := by omega
  have e11 : 9 * W ^ 5 * (10 ^ 6 * W ^ 6) = 9 * 10 ^ 6 * W ^ 11 := by ring
  have h3 : W ^ 3 ≤ W ^ 11 := Nat.pow_le_pow_right hW1 (by norm_num)
  have h2 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have h1 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
  have hdd : d * d ≤ W ^ 2 := by rw [sq]; exact Nat.mul_le_mul hdW hdW
  omega

end AdversarialBco.Bit.Transfer
