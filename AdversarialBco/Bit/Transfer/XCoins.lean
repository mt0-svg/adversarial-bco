/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAM
public import AdversarialBco.Bit.Transfer.XTrans

@[expose] public section

/-!
# The integer read off a block of coins

`readCoins_eq_iff`: the integer `readCoins cs c k` read by the leaf `coins` is `v < 2^k` exactly when the coins are
the binary digits of `v`, most significant first.
-/

open AdversarialBco AdversarialBco.BitRAM MeasureTheory

theorem AdversarialBco.Bit.Transfer.readCoins_eq_iff (cs : ℕ → Bool) (c k : ℕ) (v : ℕ) (hv : v < 2 ^ k) :
    readCoins cs c k = v ↔ ∀ i < k, cs (c + i) = v.testBit (k - 1 - i) := by
  induction k generalizing v with
  | zero =>
    have hv0 : v = 0 := by
      have h1 : (2 : ℕ)^0 = 1 := by norm_num
      rw [h1] at hv
      exact Nat.lt_one_iff.mp hv
    constructor
    · intro _ i hi
      exact (Nat.not_lt_zero _ hi).elim
    · intro _
      simp [readCoins, hv0]
  | succ k ih =>
    have hpow : 2^(k+1 : ℕ) = 2 * 2^k := by
      rw [Nat.pow_succ, mul_comm]
    rw [hpow] at hv
    -- hv : v < 2 * 2^k
    let r : ℤ := readCoins cs c k
    let e : ℤ := (if cs (c + k) then 1 else 0)
    have hread : readCoins cs c (k+1) = 2 * r + e := by
      simp [readCoins, r, e]
    have he_val : e = 0 ∨ e = 1 := by
      dsimp [e]
      split <;> simp
    -- From hv : v < 2 * 2^k, we have v/2 < 2^k
    have hv_div : v / 2 < 2^k := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mpr
      simpa [mul_comm] using hv
    have h_eq_nat : (v : ℤ) = 2 * ((v / 2 : ℕ) : ℤ) + ((v % 2 : ℕ) : ℤ) := by
      have := Nat.div_add_mod v 2
      have htemp := congrArg (fun x : ℕ => (x : ℤ)) this.symm
      simpa [mul_comm] using htemp
    have h_mod_cases : ((v % 2 : ℕ) : ℤ) = 0 ∨ ((v % 2 : ℕ) : ℤ) = 1 := by
      have h_cases : (v % 2 : ℕ) = 0 ∨ (v % 2 : ℕ) = 1 := by
        have h := Nat.mod_lt v (by norm_num : 0 < 2)
        omega
      rcases h_cases with (h0 | h1)
      · left; simp [h0]
      · right; simp [h1]
    have h_sub_add : ∀ i, i < k → (k - 1 - i) + 1 = k - i := by
      intro i hi; omega
    have h_testBit_succ : ∀ i, i < k → (v / 2).testBit (k - 1 - i) = v.testBit (k - i) := by
      intro i hi
      calc
        (v / 2).testBit (k - 1 - i) = v.testBit ((k - 1 - i) + 1) := by
          rw [Nat.testBit_div_two]
        _ = v.testBit (k - i) := by rw [h_sub_add i hi]
    have ih_vdiv2 := ih (v / 2) hv_div
    -- ih_vdiv2 : readCoins cs c k = (v / 2) ↔ ∀ i < k, cs (c + i) = (v / 2).testBit (k - 1 - i)
    constructor
    · intro h_eq
      rw [hread] at h_eq
      -- h_eq : 2 * r + e = (v : ℤ)
      have h_eq' : 2 * r + e = 2 * ((v / 2 : ℕ) : ℤ) + ((v % 2 : ℕ) : ℤ) := by
        rw [h_eq_nat] at h_eq; exact h_eq
      have h_diff : 2 * (r - ((v / 2 : ℕ) : ℤ)) = ((v % 2 : ℕ) : ℤ) - e := by
        linarith
      have h_e_eq_mod : e = ((v % 2 : ℕ) : ℤ) := by
        have h_rhs_range : ((v % 2 : ℕ) : ℤ) - e = -1 ∨ ((v % 2 : ℕ) : ℤ) - e = 0 ∨ ((v % 2 : ℕ) : ℤ) - e = 1 := by
          rcases h_mod_cases with (hm | hm)
          · rcases he_val with (he' | he')
            · -- hm: 0, he': 0 → 0-0=0
              right; left; simp [hm, he']
            · -- hm: 0, he': 1 → 0-1=-1
              left; simp [hm, he']
          · rcases he_val with (he' | he')
            · -- hm: 1, he': 0 → 1-0=1
              right; right; simp [hm, he']
            · -- hm: 1, he': 1 → 1-1=0
              right; left; simp [hm, he']
        rcases h_rhs_range with (hr' | hr' | hr')
        · rw [hr'] at h_diff; omega
        · omega
        · rw [hr'] at h_diff; omega
      have h_r_eq : r = ((v / 2 : ℕ) : ℤ) := by
        rw [h_e_eq_mod] at h_diff
        have hzero : ((v % 2 : ℕ) : ℤ) - ((v % 2 : ℕ) : ℤ) = 0 := by ring
        rw [hzero] at h_diff
        omega
      have h_inner : ∀ i < k, cs (c + i) = (v / 2).testBit (k - 1 - i) := by
        have h_r_eq' : readCoins cs c k = (v / 2) := by
          dsimp [r] at h_r_eq; exact h_r_eq
        exact (ih_vdiv2.mp h_r_eq')
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hi_lt_k | hi_eq_k)
      · -- i < k
        have hbit := h_inner i hi_lt_k
        rw [h_testBit_succ i hi_lt_k] at hbit
        have h_sub' : (k+1 : ℕ) - 1 - i = k - i := by omega
        rw [h_sub']; exact hbit
      · -- i = k
        rw [hi_eq_k]
        have h_sub0 : (k+1 : ℕ) - 1 - k = 0 := by omega
        rw [h_sub0]
        dsimp [e] at h_e_eq_mod
        have h_testBit0 : v.testBit 0 = decide (v % 2 = 1) := Nat.testBit_zero v
        rw [h_testBit0]
        by_cases h_cs : cs (c + k)
        · -- cs (c + k) = true
          have h_one : ((v % 2 : ℕ) : ℤ) = 1 := by
            simpa [h_cs] using h_e_eq_mod.symm
          have h_mod_one : (v % 2 : ℕ) = 1 :=
            (Nat.cast_inj (R := ℤ)).mp h_one
          simp [h_cs, h_mod_one]
        · -- cs (c + k) = false
          have h_zero : ((v % 2 : ℕ) : ℤ) = 0 := by
            simpa [h_cs] using h_e_eq_mod.symm
          have h_mod_zero : (v % 2 : ℕ) = 0 :=
            (Nat.cast_inj (R := ℤ)).mp h_zero
          simp [h_cs, h_mod_zero]
    · -- reverse direction
      intro h_forall
      rw [hread]
      have h_e_eq_mod : e = ((v % 2 : ℕ) : ℤ) := by
        dsimp [e]
        have h_bit0 := h_forall k (by omega)
        have h_sub0 : (k+1 : ℕ) - 1 - k = 0 := by omega
        rw [h_sub0] at h_bit0
        rw [Nat.testBit_zero v] at h_bit0
        by_cases h_cs : cs (c + k)
        · -- cs (c + k) = true
          have h_mod_one : (v % 2 : ℕ) = 1 := by
            simpa [h_cs] using h_bit0
          simp [h_cs]
          exact_mod_cast h_mod_one.symm
        · -- cs (c + k) = false
          have h_mod_zero : (v % 2 : ℕ) = 0 := by
            have h_not_one : ¬ (v % 2 = 1) := by
              intro h_eq
              have h_true : decide (v % 2 = 1) = true := by simp [h_eq]
              have h_contra : cs (c + k) = true := by
                rw [h_true] at h_bit0
                exact h_bit0
              exact h_cs h_contra
            have h_lt : v % 2 < 2 := Nat.mod_lt v (by norm_num)
            omega
          simp [h_cs]
          exact_mod_cast h_mod_zero.symm
      have h_r_eq : r = ((v / 2 : ℕ) : ℤ) := by
        have h_inner : ∀ i < k, cs (c + i) = v.testBit (k - i) := by
          intro i hi
          have hi' := h_forall i (by omega)
          have h_sub' : (k+1 : ℕ) - 1 - i = k - i := by omega
          rw [h_sub'] at hi'; exact hi'
        have h_inner' : ∀ i < k, cs (c + i) = (v / 2).testBit (k - 1 - i) := by
          intro i hi
          have h := h_inner i hi
          rw [← h_testBit_succ i hi] at h; exact h
        have h_r_eq_nat : readCoins cs c k = (v / 2) := (ih_vdiv2.mpr h_inner')
        dsimp [r]; exact h_r_eq_nat
      rw [h_r_eq, h_e_eq_mod]
      exact h_eq_nat.symm

