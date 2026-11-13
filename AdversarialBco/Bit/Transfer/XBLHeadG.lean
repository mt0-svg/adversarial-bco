/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR3
public import AdversarialBco.Bit.Transfer.XBLR2g

@[expose] public section

/-!
# The arithmetic glue of BL's round

The units of R1 and of the round in the modes `off` and `guard` as quadratic terms, the bound `U` of the head and the
tail's work term as quadratic in the round's, the width facts (`130 U + 120 < ℓ`, the input area), `M ≤ 2^E` from
`size M ≤ E`, an entry of a matrix from its squared Frobenius norm.
-/

open AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM Matrix

/-- The sampler's precision is linear. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_gsm (B : ℕ) : gsm_prec B ≤ 3 * B + 4 := by
  unfold gsm_prec
  have hsize : Nat.size B ≤ B := by
    rw [Nat.size_le]
    exact Nat.lt_pow_self (a := 2) (by norm_num) (n := B)
  omega

/-- A power of a quadratically bounded term. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_pow (x c W C k : ℕ) (h : x ≤ c * W ^ 2) :
    C * x ^ k ≤ C * c ^ k * W ^ (2 * k) := by
  have hpow : x ^ k ≤ (c * W ^ 2) ^ k := Nat.pow_le_pow_left h k
  have hmul : (c * W ^ 2) ^ k = c ^ k * (W ^ 2) ^ k := by rw [Nat.mul_pow]
  have hsq : (W ^ 2) ^ k = W ^ (2 * k) := by rw [← Nat.pow_mul]
  have hineq : x ^ k ≤ c ^ k * W ^ (2 * k) := by
    calc
      x ^ k ≤ (c * W ^ 2) ^ k := hpow
      _ = c ^ k * (W ^ 2) ^ k := hmul
      _ = c ^ k * W ^ (2 * k) := by rw [hsq]
  have hC : C * x ^ k ≤ C * (c ^ k * W ^ (2 * k)) := Nat.mul_le_mul_left C hineq
  simpa [mul_assoc] using hC

/-- The bound `U` of the head is quadratic. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_U (d E : ℕ) : tG d E + E + 1 ≤ 12 * (d + E + 1) ^ 2 := by
  unfold tG
  nlinarith [Nat.zero_le (d * E), Nat.zero_le d, Nat.zero_le E]

/-- The work term of the tail is quadratic in the round's. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_W1 (d m a b E : ℕ) :
    d + m + a + b + (36 * (tG d E + E + 1) + 30) + 1 ≤ 600 * (d + m + a + b + E + 1) ^ 2 := by
  set W := d + m + a + b + E + 1 with hW
  have hWpos : 1 ≤ W := by
    omega
  have hE : E ≤ W := by
    omega
  have hd : d ≤ W := by
    omega
  have hsq : E * d ≤ W * W := Nat.mul_le_mul hE hd
  unfold tG
  nlinarith

/-- The ℓ bound of the head from the round's. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_ell (U W C k ℓ : ℕ) (hW : 1 ≤ W) (hk : 2 ≤ k) (hC : 2000 ≤ C)
    (hU : U ≤ 12 * W ^ 2) (h : C * W ^ k ≤ ℓ) : 130 * U + 120 < ℓ := by
  have hW2 : 1 ≤ W ^ 2 := by
    calc
      1 = 1 ^ 2 := by norm_num
      _ ≤ W ^ 2 := Nat.pow_le_pow_left hW 2
  have hpos : 0 < W ^ 2 := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hW2
  have hpow : W ^ 2 ≤ W ^ k := Nat.pow_le_pow_right hW hk
  have h1 : 130 * U + 120 ≤ 130 * (12 * W ^ 2) + 120 := by
    nlinarith
  have h2 : 130 * (12 * W ^ 2) + 120 = 1560 * W ^ 2 + 120 := by ring
  have h3 : 1560 * W ^ 2 + 120 ≤ 1680 * W ^ 2 := by
    nlinarith
  have h4 : 1680 * W ^ 2 < 2000 * W ^ 2 := by
    nlinarith
  have h5 : 2000 * W ^ 2 ≤ C * W ^ 2 := by
    nlinarith
  have h6 : C * W ^ 2 ≤ C * W ^ k := by
    nlinarith
  calc
    130 * U + 120 ≤ 130 * (12 * W ^ 2) + 120 := h1
    _ = 1560 * W ^ 2 + 120 := by ring
    _ ≤ 1680 * W ^ 2 := h3
    _ < 2000 * W ^ 2 := h4
    _ ≤ C * W ^ 2 := h5
    _ ≤ C * W ^ k := h6
    _ ≤ ℓ := h

/-- The input area fits the address width. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_ma (d m W C k X : ℕ) (hW : d + m + 1 ≤ W) (hk : 2 ≤ k) (hC : 8 ≤ C)
    (h : C * W ^ k < X) : 4 + 2 * ((d + 1) * m) < X ∧ d * d + d < X ∧ d + 2 < X := by
  have hWpos : 1 ≤ W := by omega
  have hW_sq_le_Wk : W * W ≤ W ^ k := by
    by_cases hW0 : W = 0
    · subst hW0; simp
    · have hWpos' : 0 < W := Nat.pos_of_ne_zero hW0
      calc
        W * W = W ^ 2 := by simp [Nat.pow_two]
        _ ≤ W ^ k := Nat.pow_le_pow_right hWpos' hk
  have h1 : (d + 1) * m ≤ W * W := by nlinarith
  have h2 : d * d + d ≤ W * W := by nlinarith
  have h3 : d + 2 ≤ 2 * W := by nlinarith
  have hW_sq_pos : 0 < W * W := by
    have : 1 ≤ W := hWpos
    nlinarith
  have h_chain1 : 4 + 2 * ((d + 1) * m) < X := by
    have hle : 4 + 2 * ((d + 1) * m) ≤ 4 + 2 * (W * W) := by nlinarith
    have hlt : 4 + 2 * (W * W) < 8 * (W * W) := by nlinarith
    have hle2 : 8 * (W * W) ≤ C * W ^ k := by
      have : W * W ≤ W ^ k := hW_sq_le_Wk
      nlinarith
    have hlt2 : 8 * (W * W) < X := lt_of_le_of_lt hle2 h
    have h_mid : 4 + 2 * (W * W) < X := lt_trans hlt hlt2
    exact lt_of_le_of_lt hle h_mid
  have h_chain2 : d * d + d < X := by
    have hle : d * d + d ≤ W * W := h2
    have hle2 : W * W ≤ W ^ k := hW_sq_le_Wk
    have hle3 : W ^ k ≤ C * W ^ k := by
      have : 1 ≤ C := by omega
      nlinarith
    have h_chain : d * d + d ≤ C * W ^ k :=
      Nat.le_trans hle (Nat.le_trans hle2 hle3)
    exact Nat.lt_of_le_of_lt h_chain h
  have h_chain3 : d + 2 < X := by
    have hle : d + 2 ≤ 2 * W := h3
    have hW_sq_ge_W : W ≤ W * W := by
      have : 1 ≤ W := hWpos
      nlinarith
    have hle2 : 2 * W ≤ 2 * (W * W) := by nlinarith
    have hlt : 2 * (W * W) < 8 * (W * W) := by nlinarith
    have hle3 : 8 * (W * W) ≤ C * W ^ k := by
      have : W * W ≤ W ^ k := hW_sq_le_Wk
      nlinarith
    have hlt2 : 8 * (W * W) < X := lt_of_le_of_lt hle3 h
    have h_mid : 2 * (W * W) < X := lt_trans hlt hlt2
    have h_mid2 : 2 * W < X := lt_of_le_of_lt hle2 h_mid
    exact lt_of_le_of_lt hle h_mid2
  exact ⟨h_chain1, h_chain2, h_chain3⟩

/-- An entry of a matrix is at most its squared Frobenius norm when that is at most `c ≥ 1`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) (c : ℚ) (h : frob2 M ≤ c)
    (hc : 1 ≤ c) (i j : Fin d) : |M i j| ≤ c := by
  have hsq : M i j ^ 2 ≤ c := by
    calc
      M i j ^ 2 ≤ ∑ j : Fin d, M i j ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, M i j ^ 2 :=
        Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
      _ = frob2 M := rfl
      _ ≤ c := h
  have habssq : |M i j| ^ 2 ≤ c := by
    calc
      |M i j| ^ 2 = M i j ^ 2 := sq_abs _
      _ ≤ c := hsq
  by_cases hle : |M i j| ≤ 1
  · linarith
  · have hone : 1 ≤ |M i j| := by linarith
    have hpow : |M i j| ≤ |M i j| ^ 2 := by
      nlinarith
    linarith

/-- The units of R1. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_r1 (d B : ℕ) : r1Units d B ≤ 600 * (d + 1) * (B + 1) ^ 2 := by
  have h_size : Nat.size B ≤ B := (Nat.size_le.2 (Nat.lt_two_pow_self (n := B)))
  have h_gsm : gsm_prec B ≤ 3 * B + 4 := by
    unfold gsm_prec
    omega
  have h_bm : bmUnits B ≤ 72 * B ^ 2 + 426 * B + 478 := by
    have h_size_int : (Nat.size B : ℤ) ≤ (B : ℤ) := by exact_mod_cast h_size
    have h_gsm_int : (gsm_prec B : ℤ) ≤ (3 * B + 4 : ℤ) := by exact_mod_cast h_gsm
    have h_eq_nat : 4*B + 9*B + 92*(3*B+4) + 110 + B*(24*(3*B+4) + 41) = 72*B^2 + 426*B + 478 :=
      (Nat.cast_inj (R := ℤ)).mp (by
        push_cast
        ring)
    have h_int : (bmUnits B : ℤ) ≤ (72 * B ^ 2 + 426 * B + 478 : ℤ) := by
      unfold bmUnits
      have h_cast_sub : ((B - 1 : ℕ) : ℤ) ≤ (B : ℤ) := by
        have : (B - 1 : ℕ) ≤ B := Nat.sub_le B 1
        exact_mod_cast this
      have h1 : (4 : ℤ) * (Nat.size B : ℤ) ≤ (4 : ℤ) * (B : ℤ) := by nlinarith
      have h3 : (92 : ℤ) * (gsm_prec B : ℤ) ≤ (92 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) := by nlinarith
      have h_inner : (24 : ℤ) * (gsm_prec B : ℤ) + 41 ≤ (24 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + 41 := by nlinarith
      have h5 : ((B - 1 : ℕ) : ℤ) * ((24 : ℤ) * (gsm_prec B : ℤ) + 41) ≤
          (B : ℤ) * ((24 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + 41) := by
        nlinarith
      have h_sum : (4 : ℤ) * (Nat.size B : ℤ) + (9 : ℤ) * (B : ℤ) + (92 : ℤ) * (gsm_prec B : ℤ) + (110 : ℤ) +
            ((B - 1 : ℕ) : ℤ) * ((24 : ℤ) * (gsm_prec B : ℤ) + 41) ≤
          (4 : ℤ) * (B : ℤ) + (9 : ℤ) * (B : ℤ) + (92 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + (110 : ℤ) +
            (B : ℤ) * ((24 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + 41) := by
        nlinarith
      have h_eq_int : (4 : ℤ) * (B : ℤ) + (9 : ℤ) * (B : ℤ) + (92 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + (110 : ℤ) +
          (B : ℤ) * ((24 : ℤ) * ((3 : ℤ) * (B : ℤ) + 4) + 41) =
          (72 : ℤ) * (B : ℤ) ^ 2 + (426 : ℤ) * (B : ℤ) + 478 := by
        ring
      exact h_sum.trans (by rw [h_eq_int])
    exact_mod_cast h_int
  have h_nBlk : Sched.nBlk d ≤ d + 1 := by
    unfold Sched.nBlk
    omega
  calc
    r1Units d B = Sched.nBlk d * (bmUnits B + 18) + 5 := rfl
    _ ≤ (d + 1) * (bmUnits B + 18) + 5 := by
      nlinarith
    _ ≤ (d + 1) * ((72 * B ^ 2 + 426 * B + 478) + 18) + 5 := by
      nlinarith
    _ = (d + 1) * (72 * B ^ 2 + 426 * B + 496) + 5 := by
      ring
    _ ≤ 600 * (d + 1) * (B + 1) ^ 2 := by
      nlinarith

/-- The units of the round in the modes `off` and `guard`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_og (d B : ℕ) : ogUnits d B ≤ 700 * (d + 1) * (B + 1) ^ 2 := by
  have h_simplify : ogUnits d B = r1Units d B + 9 * d + 14 := by
    unfold ogUnits r3gUnits
    omega
  rw [h_simplify]
  have h_r1 : r1Units d B ≤ 600 * (d + 1) * (B + 1) ^ 2 := by
    unfold r1Units
    have h_nBlk_pos : 1 ≤ Sched.nBlk d := by
      unfold Sched.nBlk
      omega
    have h_bm : bmUnits B + 23 ≤ 600 * (B + 1) ^ 2 := by
      unfold bmUnits gsm_prec
      have hsize : Nat.size B ≤ B := (Nat.size_le.2 (Nat.lt_two_pow_self (n := B)))
      have hsub : B - 1 ≤ B := Nat.sub_le _ _
      nlinarith
    have h_mul : Sched.nBlk d * (bmUnits B + 18) + 5 ≤ Sched.nBlk d * (bmUnits B + 23) := by
      nlinarith [h_nBlk_pos]
    have h_mul2 : Sched.nBlk d * (bmUnits B + 23) ≤ (d + 1) * (600 * (B + 1) ^ 2) := by
      have h_nBlk : Sched.nBlk d ≤ d + 1 := by
        unfold Sched.nBlk
        omega
      apply Nat.mul_le_mul h_nBlk h_bm
    have h_final : (d + 1) * (600 * (B + 1) ^ 2) = 600 * (d + 1) * (B + 1) ^ 2 := by ring
    rw [h_final] at h_mul2
    exact le_trans h_mul h_mul2
  have h_rest : 9 * d + 14 ≤ 100 * (d + 1) * (B + 1) ^ 2 := by
    have h_sq : 1 ≤ (B + 1) ^ 2 := by
      have h_pos : 0 < B + 1 := by omega
      exact calc
        1 = 1 ^ 2 := by norm_num
        _ ≤ (B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h_linear : 9 * d + 14 ≤ 100 * (d + 1) := by
      omega
    have h_mul : 100 * (d + 1) ≤ 100 * (d + 1) * (B + 1) ^ 2 := by
      calc
        100 * (d + 1) = (100 * (d + 1)) * 1 := by ring
        _ ≤ (100 * (d + 1)) * (B + 1) ^ 2 := Nat.mul_le_mul_left _ h_sq
    exact le_trans h_linear h_mul
  nlinarith
