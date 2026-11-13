/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadG
public import AdversarialBco.Bit.Transfer.XBLHeadB
public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# The arithmetic glue of BL's round, second part

The units of the round as a power of its work term, the lower bound of `E` split into the magnitudes, the exponent
of R14's point, the sampler and the position's work term, `E + 4 ≤ ℓ`, R14's linear term from R10's and R13's tests,
the bounds of a state at a larger exponent, the sizes, a height bound at the next integer.
-/

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer.BLM Matrix

/-- The units of the round in mode `run` as a quartic term plus the tail's. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_tot (W B d m U Kt r1 r24 r57 mid : ℕ) (hW : 1 ≤ W)
    (hr1 : r1 ≤ 600 * (d + 1) * (B + 1) ^ 2)
    (hB : B + 1 ≤ 20000 * W) (hdm : d + m + 1 ≤ W) (hr24 : r24 ≤ 200 * (d + m + 1) ^ 2)
    (hr57 : r57 ≤ 200 * (d + U + 1)) (hmid : mid ≤ 1000 * (d + U + 1) ^ 2) (hU : U ≤ 12 * W ^ 2) :
    r1 + (1 + (r24 + (r57 + (2 + (2 + (mid + Kt)))) + 2)) ≤ 10 ^ 12 * W ^ 4 + Kt := by
  -- Simplify LHS: r1 + (1 + (r24 + (r57 + (2 + (2 + (mid + Kt)))) + 2))
  -- = r1 + r24 + r57 + mid + Kt + 7
  have h_simplify : r1 + (1 + (r24 + (r57 + (2 + (2 + (mid + Kt)))) + 2)) = r1 + r24 + r57 + mid + Kt + 7 := by
    omega
  rw [h_simplify]
  -- Now goal: r1 + r24 + r57 + mid + Kt + 7 ≤ 10 ^ 12 * W ^ 4 + Kt
  -- Cancel Kt from both sides
  have h_cancel : r1 + r24 + r57 + mid + Kt + 7 ≤ 10 ^ 12 * W ^ 4 + Kt ↔
      r1 + r24 + r57 + mid + 7 ≤ 10 ^ 12 * W ^ 4 := by
    omega
  rw [h_cancel]
  -- Goal: r1 + r24 + r57 + mid + 7 ≤ 10 ^ 12 * W ^ 4
  -- Bound each term by a multiple of W^4
  have hW_sq : W ≤ W ^ 2 := by
    calc
      W = W * 1 := by omega
      _ ≤ W * W := Nat.mul_le_mul_left W hW
      _ = W ^ 2 := by ring
  have hW_cu : W ^ 2 ≤ W ^ 3 := by
    calc
      W ^ 2 = W ^ 2 * 1 := by omega
      _ ≤ W ^ 2 * W := Nat.mul_le_mul_left (W ^ 2) hW
      _ = W ^ 3 := by ring
  have hW_qu : W ^ 3 ≤ W ^ 4 := by
    calc
      W ^ 3 = W ^ 3 * 1 := by omega
      _ ≤ W ^ 3 * W := Nat.mul_le_mul_left (W ^ 3) hW
      _ = W ^ 4 := by ring
  have hW_qu2 : W ^ 2 ≤ W ^ 4 := by
    apply Nat.le_trans hW_cu hW_qu
  have h_d1 : d + 1 ≤ W := by
    omega
  have h_U_bound : d + U + 1 ≤ 13 * W ^ 2 := by
    calc
      d + U + 1 ≤ (d + 1) + U := by omega
      _ ≤ W + U := by omega
      _ ≤ W + 12 * W ^ 2 := by omega
      _ ≤ W ^ 2 + 12 * W ^ 2 := by omega
      _ = 13 * W ^ 2 := by ring
  have h_r1 : r1 ≤ 240000000000 * W ^ 4 := by
    calc
      r1 ≤ 600 * (d + 1) * (B + 1) ^ 2 := hr1
      _ ≤ 600 * W * ((20000 * W) ^ 2) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left 600 h_d1) ?_
        apply Nat.pow_le_pow_left hB 2
      _ = 600 * W * (400000000 * W ^ 2) := by ring
      _ = 240000000000 * W ^ 3 := by ring
      _ ≤ 240000000000 * W ^ 4 := Nat.mul_le_mul_left _ hW_qu
  have h_r24 : r24 ≤ 200 * W ^ 4 := by
    calc
      r24 ≤ 200 * (d + m + 1) ^ 2 := hr24
      _ ≤ 200 * W ^ 2 := Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hdm 2)
      _ ≤ 200 * W ^ 4 := Nat.mul_le_mul_left 200 hW_qu2
  have h_r57 : r57 ≤ 2600 * W ^ 4 := by
    calc
      r57 ≤ 200 * (d + U + 1) := hr57
      _ ≤ 200 * (13 * W ^ 2) := Nat.mul_le_mul_left 200 h_U_bound
      _ = 2600 * W ^ 2 := by ring
      _ ≤ 2600 * W ^ 4 := Nat.mul_le_mul_left 2600 hW_qu2
  have h_mid : mid ≤ 169000 * W ^ 4 := by
    calc
      mid ≤ 1000 * (d + U + 1) ^ 2 := hmid
      _ ≤ 1000 * (13 * W ^ 2) ^ 2 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left h_U_bound 2)
      _ = 1000 * (169 * W ^ 4) := by ring
      _ = 169000 * W ^ 4 := by ring
  have h_seven : 7 ≤ 7 * W ^ 4 := by
    have : 1 ≤ W ^ 4 := by
      calc
        1 ≤ W := hW
        _ ≤ W ^ 4 := by
          apply Nat.le_trans hW_sq ?_
          apply Nat.le_trans hW_cu ?_
          exact hW_qu
    omega
  -- Now sum all bounds using Nat.add_le_add
  have h_sum : r1 + r24 + r57 + mid + 7 ≤ (240000000000 + 200 + 2600 + 169000 + 7) * W ^ 4 := by
    have h_add1 : r1 + r24 ≤ (240000000000 + 200) * W ^ 4 := by
      have : 240000000000 * W ^ 4 + 200 * W ^ 4 = (240000000000 + 200) * W ^ 4 := by ring
      -- Nat.add_le_add h_r1 h_r24 gives r1 + r24 ≤ 240000000000 * W^4 + 200 * W^4
      -- Then rewrite RHS
      apply (Nat.add_le_add h_r1 h_r24).trans
      rw [this]
    have h_add2 : (r1 + r24) + r57 ≤ ((240000000000 + 200) + 2600) * W ^ 4 := by
      have : (240000000000 + 200) * W ^ 4 + 2600 * W ^ 4 = ((240000000000 + 200) + 2600) * W ^ 4 := by ring
      apply (Nat.add_le_add h_add1 h_r57).trans
      rw [this]
    have h_add3 : ((r1 + r24) + r57) + mid ≤ (((240000000000 + 200) + 2600) + 169000) * W ^ 4 := by
      have : ((240000000000 + 200) + 2600) * W ^ 4 + 169000 * W ^ 4 =
          (((240000000000 + 200) + 2600) + 169000) * W ^ 4 := by ring
      apply (Nat.add_le_add h_add2 h_mid).trans
      rw [this]
    have h_add4 : (((r1 + r24) + r57) + mid) + 7 ≤ ((((240000000000 + 200) + 2600) + 169000) + 7) * W ^ 4 := by
      have : (((240000000000 + 200) + 2600) + 169000) * W ^ 4 + 7 * W ^ 4 =
          ((((240000000000 + 200) + 2600) + 169000) + 7) * W ^ 4 := by ring
      apply (Nat.add_le_add h_add3 h_seven).trans
      rw [this]
    -- Now rewrite the LHS to the simplified form
    simpa [add_assoc] using h_add4
  -- 240000000000 + 200 + 2600 + 169000 + 7 = 24000171807 ≤ 10^12
  have h_const : (240000000000 + 200 + 2600 + 169000 + 7 : ℕ) ≤ 10 ^ 12 := by
    omega
  -- Now combine
  calc
    r1 + r24 + r57 + mid + 7 ≤ (240000000000 + 200 + 2600 + 169000 + 7) * W ^ 4 := h_sum
    _ ≤ 10 ^ 12 * W ^ 4 := Nat.mul_le_mul_right (W ^ 4) h_const

/-- The units of the modes `off` and `guard` as a quartic term. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_ogt (W B d og : ℕ) (hW : 1 ≤ W)
    (hog : og ≤ 700 * (d + 1) * (B + 1) ^ 2) (hB : B + 1 ≤ 20000 * W)
    (hd : d + 1 ≤ W) : og ≤ 10 ^ 12 * W ^ 4 := by
  have hW3_le_W4 : W ^ 3 ≤ W ^ 4 := by
    calc
      W ^ 3 = W ^ 3 * 1 := by rw [mul_one]
      _ ≤ W ^ 3 * W := Nat.mul_le_mul_left (W ^ 3) hW
      _ = W ^ 4 := by rw [← pow_succ W 3]
  have h_sq : (B + 1) ^ 2 ≤ (20000 * W) ^ 2 := Nat.pow_le_pow_left hB 2
  have h_mul : (d + 1) * (B + 1) ^ 2 ≤ W * (20000 * W) ^ 2 :=
    Nat.mul_le_mul hd h_sq
  have h_main : 700 * (d + 1) * (B + 1) ^ 2 ≤ 700 * W * (20000 * W) ^ 2 := by
    calc
      700 * (d + 1) * (B + 1) ^ 2 = 700 * ((d + 1) * (B + 1) ^ 2) := by rw [mul_assoc]
      _ ≤ 700 * (W * (20000 * W) ^ 2) := Nat.mul_le_mul_left 700 h_mul
      _ = 700 * W * (20000 * W) ^ 2 := by rw [mul_assoc]
  have h_coeff : 700 * 20000 ^ 2 ≤ 10 ^ 12 := by norm_num
  have h_final : 700 * W * (20000 * W) ^ 2 ≤ 10 ^ 12 * W ^ 4 := by
    calc
      700 * W * (20000 * W) ^ 2 = 700 * W * (20000 ^ 2 * W ^ 2) := by rw [mul_pow]
      _ = (700 * 20000 ^ 2) * (W * W ^ 2) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = (700 * 20000 ^ 2) * W ^ 3 := by rw [← pow_succ' W 2]
      _ ≤ 10 ^ 12 * W ^ 3 := Nat.mul_le_mul h_coeff (le_refl _)
      _ ≤ 10 ^ 12 * W ^ 4 := Nat.mul_le_mul (le_refl _) hW3_le_W4
  exact le_trans hog (le_trans h_main h_final)

/-- The two unit terms under one power. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_C (W Ct kt : ℕ) (hW : 1 ≤ W) :
    10 ^ 12 * W ^ 4 + Ct * 600 ^ kt * W ^ (2 * kt) ≤ (10 ^ 12 + Ct * 600 ^ kt) * W ^ (2 * kt + 4) := by
  have hWpos : 0 < W := by omega
  have hW4 : W ^ 4 ≤ W ^ (2 * kt + 4) :=
    Nat.pow_le_pow_right hWpos (by omega)
  have hW2kt : W ^ (2 * kt) ≤ W ^ (2 * kt + 4) :=
    Nat.pow_le_pow_right hWpos (by omega)
  have h1 : 10 ^ 12 * W ^ 4 ≤ 10 ^ 12 * W ^ (2 * kt + 4) :=
    Nat.mul_le_mul_left (10 ^ 12) hW4
  have h2 : Ct * 600 ^ kt * W ^ (2 * kt) ≤ Ct * 600 ^ kt * W ^ (2 * kt + 4) :=
    Nat.mul_le_mul_left (Ct * 600 ^ kt) hW2kt
  calc
    10 ^ 12 * W ^ 4 + Ct * 600 ^ kt * W ^ (2 * kt) ≤ 10 ^ 12 * W ^ (2 * kt + 4) + Ct * 600 ^ kt * W ^ (2 * kt + 4) :=
      Nat.add_le_add h1 h2
    _ = (10 ^ 12 + Ct * 600 ^ kt) * W ^ (2 * kt + 4) := by rw [Nat.add_mul]

/-- The sampler's width from PARAM's bound. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_Bw (B G s1 s2 W : ℕ) (hB : B ≤ 4 * G + 4)
    (hG : G ≤ 4000 * (s1 + s2 + 1)) (hW : s1 + s2 + 1 ≤ W) :
    B + 1 ≤ 20000 * W := by
  omega

/-- The lower bound of `E` covers the magnitudes, the exponent of R14's point, the sampler and `W₀`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_E (W0 G Cm km Cx kx E : ℕ) (hW : 1 ≤ W0) (hG : G ≤ 4000 * W0)
    (hE : (Cm + Cx * 1501727 ^ kx + 500000) * W0 ^ (km + kx + 1) ≤ E) :
    Cm * W0 ^ km ≤ E ∧ (75 * G + 343) + Cx * (W0 + (5 * (75 * G + 343) + 5)) ^ kx ≤ E ∧
      4 * (3 * (4 * G + 4) + 4) ≤ E ∧ W0 ≤ E := by
  set K := km + kx + 1 with hK
  set P := W0 ^ K with hP
  have hKpos : K ≠ 0 := by
    intro hzero
    have : km + kx + 1 = 0 := hzero
    omega
  have hWpos : 0 < W0 := by omega
  have hWleP : W0 ≤ P := by
    rw [hP]
    exact Nat.le_self_pow hKpos W0
  have hpos_sum : 1 ≤ Cm + Cx * 1501727 ^ kx + 500000 := by
    have : 1 ≤ 500000 := by decide
    omega
  have hCm : Cm * W0 ^ km ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P := by
    calc
      Cm * W0 ^ km ≤ Cm * W0 ^ K :=
        Nat.mul_le_mul_left Cm (Nat.pow_le_pow_right hWpos (by omega))
      _ = Cm * P := by rw [hP]
      _ ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P :=
        Nat.mul_le_mul_right P (by
          simpa [add_assoc] using Nat.le_add_right Cm (Cx * 1501727 ^ kx + 500000))
  have h343le343W0 : 343 ≤ 343 * W0 := by
    calc
      343 = 343 * 1 := by simp
      _ ≤ 343 * W0 := Nat.mul_le_mul_left 343 hW
  have hGpart : 75 * G + 343 ≤ 300343 * W0 := by
    have h75G : 75 * G ≤ 300000 * W0 := by
      calc
        75 * G ≤ 75 * (4000 * W0) := Nat.mul_le_mul_left 75 hG
        _ = 300000 * W0 := by ring
    have hsum : 75 * G + 343 ≤ 300000 * W0 + 343 * W0 :=
      Nat.add_le_add h75G h343le343W0
    calc
      75 * G + 343 ≤ 300000 * W0 + 343 * W0 := hsum
      _ = 300343 * W0 := by ring
  have h5le11W0 : 5 ≤ 11 * W0 := by
    calc
      5 ≤ 11 := by decide
      _ = 11 * 1 := by simp
      _ ≤ 11 * W0 := Nat.mul_le_mul_left 11 hW
  have hWsum : W0 + (5 * (75 * G + 343) + 5) ≤ 1501727 * W0 := by
    have h5 : 5 * (75 * G + 343) ≤ 1501715 * W0 := by
      calc
        5 * (75 * G + 343) ≤ 5 * (300343 * W0) := Nat.mul_le_mul_left 5 hGpart
        _ = 1501715 * W0 := by ring
    calc
      W0 + (5 * (75 * G + 343) + 5) ≤ W0 + (1501715 * W0 + 5) :=
        Nat.add_le_add_left (Nat.add_le_add_right h5 5) W0
      _ = W0 + 1501715 * W0 + 5 := by ring
      _ ≤ W0 + 1501715 * W0 + 11 * W0 :=
        Nat.add_le_add_left h5le11W0 (W0 + 1501715 * W0)
      _ = 1501727 * W0 := by ring
  have hCxpart : Cx * (W0 + (5 * (75 * G + 343) + 5)) ^ kx ≤ Cx * 1501727 ^ kx * P := by
    calc
      Cx * (W0 + (5 * (75 * G + 343) + 5)) ^ kx ≤ Cx * (1501727 * W0) ^ kx :=
        Nat.mul_le_mul_left Cx (Nat.pow_le_pow_left hWsum kx)
      _ = Cx * (1501727 ^ kx * W0 ^ kx) := by rw [Nat.mul_pow]
      _ = Cx * 1501727 ^ kx * W0 ^ kx := by ring
      _ ≤ Cx * 1501727 ^ kx * W0 ^ K :=
        Nat.mul_le_mul_left (Cx * 1501727 ^ kx) (Nat.pow_le_pow_right hWpos (by omega))
      _ = Cx * 1501727 ^ kx * P := by rw [hP]
  have hGpartP : 75 * G + 343 ≤ 300343 * P :=
    le_trans hGpart (Nat.mul_le_mul_left 300343 hWleP)
  have hpart2 : (75 * G + 343) + Cx * (W0 + (5 * (75 * G + 343) + 5)) ^ kx ≤
      (300343 + Cx * 1501727 ^ kx) * P := by
    apply le_trans (Nat.add_le_add hGpartP hCxpart)
    calc
      300343 * P + Cx * 1501727 ^ kx * P = (300343 + Cx * 1501727 ^ kx) * P := by ring
      _ ≤ (300343 + Cx * 1501727 ^ kx) * P := le_refl _
  have h300343le500000 : 300343 ≤ 500000 := by decide
  have h300343leCm500000 : 300343 ≤ Cm + 500000 :=
    Nat.le_trans h300343le500000 (Nat.le_add_left 500000 Cm)
  have hpart2' : (300343 + Cx * 1501727 ^ kx) * P ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P :=
    Nat.mul_le_mul_right P (by
      -- need 300343 + Cx*... ≤ Cm + Cx*... + 500000
      -- which follows from 300343 ≤ Cm + 500000
      simpa [add_comm, add_left_comm, add_assoc] using
        Nat.add_le_add_right h300343leCm500000 (Cx * 1501727 ^ kx))
  have h64le64W0 : 64 ≤ 64 * W0 := by
    calc
      64 = 64 * 1 := by simp
      _ ≤ 64 * W0 := Nat.mul_le_mul_left 64 hW
  have hGpart3 : 4 * (3 * (4 * G + 4) + 4) ≤ 500000 * P := by
    have h_eq : 4 * (3 * (4 * G + 4) + 4) = 48 * G + 64 := by omega
    rw [h_eq]
    have h_le : 48 * G + 64 ≤ 192064 * W0 := by
      have h48G : 48 * G ≤ 192000 * W0 := by
        calc
          48 * G ≤ 48 * (4000 * W0) := Nat.mul_le_mul_left 48 hG
          _ = 192000 * W0 := by ring
      have hsum : 48 * G + 64 ≤ 192000 * W0 + 64 * W0 :=
        Nat.add_le_add h48G h64le64W0
      calc
        48 * G + 64 ≤ 192000 * W0 + 64 * W0 := hsum
        _ = 192064 * W0 := by ring
    have hPle : 192064 * W0 ≤ 192064 * P := Nat.mul_le_mul_left 192064 hWleP
    have h192064le500000 : 192064 ≤ 500000 := by decide
    have hPle' : 192064 * P ≤ 500000 * P := Nat.mul_le_mul_right P h192064le500000
    exact le_trans h_le (le_trans hPle hPle')
  have h500000leSum : 500000 ≤ Cm + Cx * 1501727 ^ kx + 500000 := by
    simpa [add_comm, add_assoc] using Nat.le_add_right 500000 (Cm + Cx * 1501727 ^ kx)
  have hGpart3' : 500000 * P ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P :=
    Nat.mul_le_mul_right P h500000leSum
  have hWleE : W0 ≤ E := by
    have hP_le : P ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P := by
      calc
        P = 1 * P := by simp
        _ ≤ (Cm + Cx * 1501727 ^ kx + 500000) * P := Nat.mul_le_mul_right P hpos_sum
    have hE' : (Cm + Cx * 1501727 ^ kx + 500000) * P ≤ E := by
      rw [hP, hK]
      exact hE
    exact le_trans hWleP (le_trans hP_le hE')
  refine ⟨le_trans hCm hE, le_trans (le_trans hpart2 hpart2') hE,
    le_trans hGpart3 (le_trans hGpart3' hE), hWleE⟩

/-- The round's width covers `E + 4`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_ellE (E W C k ℓ : ℕ) (hW : E + 1 ≤ W)
    (hC : 2000 ≤ C) (hk : 1 ≤ k) (h : C * W ^ k ≤ ℓ) :
    E + 4 ≤ ℓ := by
  have hk0 : k ≠ 0 := by omega
  have hWpow : W ≤ W ^ k := Nat.le_self_pow hk0 W
  have h_ell : E + 1 ≤ W ^ k := le_trans hW hWpow
  have h_mul : 2000 * (E + 1) ≤ C * W ^ k := Nat.mul_le_mul hC h_ell
  have h_total : 2000 * (E + 1) ≤ ℓ := le_trans h_mul h
  omega

/-- R14's linear term `(B'B'ᵀ) w_μ` from R10's and R13's tests. -/
theorem AdversarialBco.Bit.Transfer.BLM.f_abs {d : ℕ} (Bp : Matrix (Fin d) (Fin d) ℚ) (w : Fin d → ℚ) (Lam : ℕ) (W : ℚ)
    (a : ℕ)
    (hF : frob2 Bp ≤ 2 * (Lam : ℚ)) (hL : (Lam : ℚ) ≤ 2 ^ a) (hw : ∀ j, |w j| ≤ 2 * |W|) (hW : |W| ≤ 2 ^ a)
    (hd : (d : ℚ) ≤ 2 ^ a) (i : Fin d) : |((Bp * Bpᵀ) *ᵥ w) i| ≤ 2 ^ (5 * a + 5) := by
  set T : ℚ := 2 * (Lam : ℚ) + 1 with hTdef
  set R : ℚ := 2 * |W| with hRdef
  have hLam_nonneg : 0 ≤ (Lam : ℚ) := by exact_mod_cast Nat.zero_le Lam
  have h_absW_nonneg : 0 ≤ |W| := abs_nonneg _
  have hT_one : 1 ≤ T := by
    rw [hTdef]
    nlinarith
  have hTpos : 0 ≤ T := by nlinarith
  have hRpos : 0 ≤ R := by
    rw [hRdef]
    nlinarith
  have h_frob_le_T : frob2 Bp ≤ T := by
    rw [hTdef]
    nlinarith
  have hT_le : T ≤ (2 : ℚ) ^ (a + 2) := by
    rw [hTdef]
    have h_pow_ge_one : 1 ≤ (2 : ℚ) ^ a :=
      Nat.rec (by norm_num) (fun k ih => by
        rw [pow_succ]
        nlinarith) a
    calc
      2 * (Lam : ℚ) + 1 ≤ 2 * ((2 : ℚ) ^ a) + 1 := by nlinarith
      _ ≤ 2 * ((2 : ℚ) ^ a) + (2 : ℚ) ^ a := by nlinarith
      _ = 3 * ((2 : ℚ) ^ a) := by ring
      _ ≤ 4 * ((2 : ℚ) ^ a) := by
        have h_nonneg : 0 ≤ (2 : ℚ) ^ a := pow_nonneg (by norm_num) a
        nlinarith
      _ = (2 : ℚ) ^ 2 * ((2 : ℚ) ^ a) := by norm_num
      _ = (2 : ℚ) ^ (a + 2) := by rw [← pow_add, add_comm 2 a]
  have hR_le : R ≤ (2 : ℚ) ^ (a + 1) := by
    rw [hRdef]
    calc
      2 * |W| ≤ 2 * ((2 : ℚ) ^ a) := by nlinarith
      _ = (2 : ℚ) ^ (a + 1) := by rw [mul_comm, ← pow_succ]
  have hB : ∀ i j, |Bp i j| ≤ T := by
    intro i j
    exact gl_frob Bp T h_frob_le_T hT_one i j
  have hw' : ∀ j, |w j| ≤ R := by
    intro j
    rw [hRdef]
    exact hw j
  have h_bound : |((Bp * Bpᵀ) *ᵥ w) i| ≤ (d : ℚ) * (d : ℚ) * T * T * R :=
    hb_Pw Bp w T R hTpos hRpos hB hw' i
  have h_final : (d : ℚ) * (d : ℚ) * T * T * R ≤ (2 : ℚ) ^ (5 * a + 5) := by
    have h_prod : (d : ℚ) * (d : ℚ) * T * T * R ≤
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) := by
      have h_nonneg_d : 0 ≤ (d : ℚ) := by exact_mod_cast Nat.zero_le d
      have h_nonneg_T : 0 ≤ T := hTpos
      have h_nonneg_2a : 0 ≤ (2 : ℚ) ^ a := pow_nonneg (by norm_num) a
      have h_nonneg_2a2 : 0 ≤ (2 : ℚ) ^ (a + 2) := pow_nonneg (by norm_num) (a + 2)
      have h1 : (d : ℚ) * (d : ℚ) ≤ (2 : ℚ) ^ a * (2 : ℚ) ^ a :=
        mul_le_mul hd hd h_nonneg_d h_nonneg_2a
      have h2 : T * T ≤ (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) :=
        mul_le_mul hT_le hT_le h_nonneg_T h_nonneg_2a2
      have h12 : ((d : ℚ) * (d : ℚ)) * (T * T) ≤
          ((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      have h_final : (((d : ℚ) * (d : ℚ)) * (T * T)) * R ≤
          (((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2))) * (2 : ℚ) ^ (a + 1) :=
        mul_le_mul h12 hR_le (by positivity) (by positivity)
      simpa [mul_assoc] using h_final
    have h_pow_eq : (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) =
        (2 : ℚ) ^ (5 * a + 5) := by
      calc
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1)
            = ((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2)) * (2 : ℚ) ^ (a + 1) := by ring
        _ = (2 : ℚ) ^ (a + a) * (2 : ℚ) ^ ((a + 2) + (a + 2)) * (2 : ℚ) ^ (a + 1) := by rw [← pow_add, ← pow_add]
        _ = (2 : ℚ) ^ ((a + a) + ((a + 2) + (a + 2))) * (2 : ℚ) ^ (a + 1) := by rw [← pow_add]
        _ = (2 : ℚ) ^ (((a + a) + ((a + 2) + (a + 2))) + (a + 1)) := by rw [← pow_add]
        _ = (2 : ℚ) ^ (5 * a + 5) := by ring
    calc
      (d : ℚ) * (d : ℚ) * T * T * R ≤
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) := h_prod
      _ = (2 : ℚ) ^ (5 * a + 5) := h_pow_eq
  exact le_trans h_bound h_final

/-- The bounds of a state at a larger exponent. -/
theorem AdversarialBco.Bit.Transfer.BLM.StBnd_mono {d : ℕ} {p E E' R : ℕ} {st : St d}
    (h : StBnd p E R st) (hE : E ≤ E') : StBnd p E' R st := by
  rcases h with ⟨hA, hB, hb, hk, hG, hl, hmu⟩
  have hp : (2 : ℤ) ^ E ≤ (2 : ℤ) ^ E' :=
    pow_le_pow_right₀ (by norm_num) hE
  exact ⟨λ i j => (hA i j).trans hp, λ i j => (hB i j).trans hp, λ j => (hb j).trans hp,
    hk.trans hp, λ j => (hG j).trans hp, hl.trans hp, hmu⟩

/-- `M + 1 ≤ 2^E` from `size M ≤ E`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_sizeM (M E : ℕ) (h : M.size ≤ E) : M + 1 ≤ 2 ^ E := by
  have hlt : M < 2 ^ M.size := Nat.lt_size_self M
  have hpow : 2 ^ M.size ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) h
  have hlt' : M < 2 ^ E := lt_of_lt_of_le hlt hpow
  exact Nat.succ_le_of_lt hlt'

/-- `d ≤ 2^E` from `d ≤ E`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_dE (d E : ℕ) (h : d ≤ E) : d ≤ 2 ^ E := by
  have h_lt : d < 2 ^ d := Nat.lt_two_pow_self
  have h_pow : 2 ^ d ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) h
  have h_le : d ≤ 2 ^ d := Nat.le_of_lt h_lt
  exact Nat.le_trans h_le h_pow

/-- The size is at most the number. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_sz (d : ℕ) : d.size ≤ d := by
  rw [Nat.size_le]
  exact Nat.lt_two_pow_self

/-- A height bound holds at the next integer. -/
theorem AdversarialBco.Bit.Transfer.BLM.heightLE_succ {d m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {M : ℕ}
    (h : RealRAM.HeightLE A b M) : RealRAM.HeightLE A b (M + 1) := by
  rcases h with ⟨hA, hb⟩
  constructor
  · intro i j
    rcases hA i j with ⟨hn, hd⟩
    exact ⟨Nat.le_succ_of_le hn, Nat.le_succ_of_le hd⟩
  · intro i
    rcases hb i with ⟨hn, hd⟩
    exact ⟨Nat.le_succ_of_le hn, Nat.le_succ_of_le hd⟩
