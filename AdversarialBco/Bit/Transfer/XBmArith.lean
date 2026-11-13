/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.GsSpec

@[expose] public section

/-!
# The arithmetic of Procedure BM-INT on the machine

Bounds and identities that the run of BM-INT (Bit/Transfer/XBmInt.lean) reads: the half-angle chain and the product
loop stay bounded (`bm_chainq_le`, `bm_prodq_le`), the Mercator powers and sums
(`bm_powq_le`, `bm_mercq_le`), the scaled logarithm (`bm_LLq_bounds`), the precision (`bm_prec`), the digit
extraction (`bm_digit`, `bm_top_digit`), the loop exits (`bm_size_eq`, `bm_log_eq`), `bm_X_le`, `bm_sqrt_le`.
-/

open AdversarialBco.Bit

theorem AdversarialBco.Bit.Transfer.bm_chainq_le (p k : ℕ) (hp : 1 ≤ p) :
    (gsm_chainq p k).1 ≤ 2 ^ p ∧ (gsm_chainq p k).2 ≤ 2 ^ p
 := by
  induction' k with k ih
  · -- base case k = 0: gsm_chainq p 0 = (0, 2^p)
    simp [gsm_chainq]
  · -- induction step
    rcases ih with ⟨h1, h2⟩
    set cs := gsm_chainq p k with hcs
    set c := Nat.sqrt (2 ^ (p - 1) * (2 ^ p + cs.1)) with hc
    have hp_pos : 0 < p := by omega
    have hp_sub_pos : 0 < 2 ^ (p - 1) := pow_pos (by norm_num) (p - 1)
    have h_pow_le : 2 ^ (p - 1) ≤ 2 ^ p :=
      Nat.pow_le_pow_right (by norm_num) (Nat.sub_le p 1)
    -- (i) c ≤ 2^p
    have hc_le : c ≤ 2 ^ p := by
      rw [hc]
      have h_sum : 2 ^ p + cs.1 ≤ 2 ^ (p + 1) := by
        have : cs.1 ≤ 2 ^ p := h1
        have h_add : 2 ^ p + cs.1 ≤ 2 ^ p + 2 ^ p := Nat.add_le_add_left this (2 ^ p)
        calc
          2 ^ p + cs.1 ≤ 2 ^ p + 2 ^ p := h_add
          _ = 2 ^ (p + 1) := by
            rw [← two_mul, ← pow_succ' 2 p]
      have h_mul : 2 ^ (p - 1) * (2 ^ p + cs.1) ≤ 2 ^ (p - 1) * 2 ^ (p + 1) :=
        Nat.mul_le_mul_left (2 ^ (p - 1)) h_sum
      have h_pow_eq : 2 ^ (p - 1) * 2 ^ (p + 1) = (2 ^ p) * (2 ^ p) := by
        calc
          2 ^ (p - 1) * 2 ^ (p + 1) = 2 ^ ((p - 1) + (p + 1)) := by rw [← pow_add]
          _ = 2 ^ (p + p) := by
            have : (p - 1) + (p + 1) = p + p := by omega
            rw [this]
          _ = 2 ^ (2 * p) := by ring
          _ = 2 ^ (p * 2) := by rw [mul_comm]
          _ = (2 ^ p) ^ 2 := by rw [pow_mul]
          _ = (2 ^ p) * (2 ^ p) := by ring
      have h_sq : 2 ^ (p - 1) * (2 ^ p + cs.1) ≤ (2 ^ p) * (2 ^ p) := by
        calc
          2 ^ (p - 1) * (2 ^ p + cs.1) ≤ 2 ^ (p - 1) * 2 ^ (p + 1) := h_mul
          _ = (2 ^ p) * (2 ^ p) := h_pow_eq
      calc
        Nat.sqrt (2 ^ (p - 1) * (2 ^ p + cs.1)) ≤ Nat.sqrt ((2 ^ p) * (2 ^ p)) :=
          Nat.sqrt_le_sqrt h_sq
        _ = 2 ^ p := Nat.sqrt_eq (2 ^ p)
    -- (ii) cs.2 * 2^(p-1) / c ≤ 2^p
    have h_div_le : cs.2 * 2 ^ (p - 1) / c ≤ 2 ^ p := by
      have h_le_sqrt : 2 ^ (p - 1) ≤ c := by
        rw [hc, Nat.le_sqrt]
        have h_sq_le : (2 ^ (p - 1)) * (2 ^ (p - 1)) ≤ 2 ^ (p - 1) * (2 ^ p + cs.1) :=
          Nat.mul_le_mul_left (2 ^ (p - 1)) (by
            calc
              2 ^ (p - 1) ≤ 2 ^ p := h_pow_le
              _ ≤ 2 ^ p + cs.1 := Nat.le_add_right _ _)
        exact h_sq_le
      calc
        cs.2 * 2 ^ (p - 1) / c ≤ cs.2 * 2 ^ (p - 1) / (2 ^ (p - 1)) :=
          Nat.div_le_div_left h_le_sqrt hp_sub_pos
        _ = cs.2 := Nat.mul_div_cancel cs.2 hp_sub_pos
        _ ≤ 2 ^ p := h2
    -- unfold gsm_chainq for k+1
    simp [gsm_chainq]
    exact And.intro hc_le h_div_le

theorem AdversarialBco.Bit.Transfer.bm_prodq_le (p B J : ℕ)
    (hc : ∀ k, (gsm_chainq p k).1 ≤ 2 ^ p ∧ (gsm_chainq p k).2 ≤ 2 ^ p) (k : ℕ) :
    |(gsm_prodq p B J k).1| < 2 ^ (p + k + 1) ∧ |(gsm_prodq p B J k).2| < 2 ^ (p + k + 1)
 := by
  induction' k with k IH
  · -- base case k = 0
    have hpos : 0 ≤ (2 : ℤ) ^ p := pow_nonneg (by norm_num) p
    have h_lt : (2 : ℤ) ^ p < (2 : ℤ) ^ (p + 1) := by
      calc
        (2 : ℤ) ^ p < (2 : ℤ) ^ p * 2 := by
          have hpos' : 0 < (2 : ℤ) ^ p := pow_pos (by norm_num) p
          nlinarith
        _ = (2 : ℤ) ^ (p + 1) := by ring
    constructor
    · unfold gsm_prodq
      split
      · simp [abs_of_nonneg hpos, h_lt]
      · simp [abs_of_nonneg hpos, h_lt]
    · unfold gsm_prodq
      simp
  · -- inductive step: k → k+1
    rcases IH with ⟨h1, h2⟩
    have hDpos : 0 < (2 : ℤ) ^ p := pow_pos (by norm_num) p
    have hDne0 : (2 : ℤ) ^ p ≠ 0 := by linarith
    set D := (2 : ℤ) ^ p with hDdef
    set Z := (2 : ℤ) ^ (p + k + 1) with hZdef
    have hZpos : 0 < Z := pow_pos (by norm_num) (p + k + 1)
    have h2Z : (2 : ℤ) ^ (p + (k + 1) + 1) = 2 * Z := by
      calc
        (2 : ℤ) ^ (p + (k + 1) + 1) = (2 : ℤ) ^ ((p + k + 1) + 1) := by ring
        _ = (2 : ℤ) ^ (p + k + 1) * 2 := by ring
        _ = Z * 2 := by rw [hZdef]
        _ = 2 * Z := by ring
    set cs := gsm_chainq p k with hcsdef
    have hc1 : cs.1 ≤ 2 ^ p := (hc k).1
    have hc2 : cs.2 ≤ 2 ^ p := (hc k).2
    have hc1' : (cs.1 : ℤ) ≤ D := by
      simpa [hDdef, Nat.cast_pow] using mod_cast hc1
    have hc2' : (cs.2 : ℤ) ≤ D := by
      simpa [hDdef, Nat.cast_pow] using mod_cast hc2
    have hc1_nonneg : 0 ≤ (cs.1 : ℤ) := Nat.cast_nonneg _
    have hc2_nonneg : 0 ≤ (cs.2 : ℤ) := Nat.cast_nonneg _
    have hZ_lt_2Z : Z < 2 * Z := by nlinarith
    constructor
    · -- first component
      unfold gsm_prodq
      split
      · -- testBit true: do complex multiplication
        rename_i hbit
        set ab := gsm_prodq p B J k with habdef
        have hab1 : |ab.1| < Z := by
          rw [habdef]
          simpa [hZdef] using h1
        have hab2 : |ab.2| < Z := by
          rw [habdef]
          simpa [hZdef] using h2
        have h_num_bound : |ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)| ≤ (2 * Z - 2) * D := by
          calc
            |ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)| ≤ |ab.1 * (cs.1 : ℤ)| + |ab.2 * (cs.2 : ℤ)| := abs_sub _ _
            _ = |ab.1| * |(cs.1 : ℤ)| + |ab.2| * |(cs.2 : ℤ)| := by simp [abs_mul]
            _ ≤ |ab.1| * D + |ab.2| * D := by
              have hc_abs : |(cs.1 : ℤ)| ≤ D := by
                rw [abs_of_nonneg hc1_nonneg]
                exact hc1'
              have hs_abs : |(cs.2 : ℤ)| ≤ D := by
                rw [abs_of_nonneg hc2_nonneg]
                exact hc2'
              have h1 : |ab.1| * |(cs.1 : ℤ)| ≤ |ab.1| * D :=
                mul_le_mul_of_nonneg_left hc_abs (abs_nonneg _)
              have h2 : |ab.2| * |(cs.2 : ℤ)| ≤ |ab.2| * D :=
                mul_le_mul_of_nonneg_left hs_abs (abs_nonneg _)
              nlinarith
            _ = (|ab.1| + |ab.2|) * D := by ring
            _ ≤ (Z - 1 + (Z - 1)) * D := by
              have ha_int : |ab.1| ≤ Z - 1 := by omega
              have hb_int : |ab.2| ≤ Z - 1 := by omega
              nlinarith
            _ = (2 * Z - 2) * D := by ring
        have h_ediv_bound : |(ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D| ≤ 2 * Z - 2 := by
          have h_upper : (ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D ≤ 2 * Z - 2 := by
            have hle := Int.ediv_mul_le (ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) hDne0
            have hvle : ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ) ≤ (2 * Z - 2) * D :=
              (abs_le.mp h_num_bound).right
            nlinarith
          have h_lower : -(2 * Z - 2) ≤ (ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D := by
            have hlt := Int.lt_ediv_add_one_mul_self (ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) hDpos
            have hvincl : -((2 * Z - 2) * D) ≤ ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ) :=
              (abs_le.mp h_num_bound).left
            have hineq : -((2 * Z - 2) * D) < (((ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D) + 1) * D := by
              linarith
            have hdivineq : -(2 * Z - 2) < ((ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D) + 1 := by
              nlinarith
            omega
          rw [abs_le]
          constructor
          · exact h_lower
          · exact h_upper
        have h_lt : |(ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D| < 2 * Z := by
          have : |(ab.1 * (cs.1 : ℤ) - ab.2 * (cs.2 : ℤ)) / D| ≤ 2 * Z - 2 := h_ediv_bound
          omega
        simpa [gsm_cmulq, habdef, hcsdef, hDdef, h2Z] using h_lt
      · -- testBit false: unchanged
        simpa [hZdef, h2Z] using lt_of_lt_of_le h1 (by nlinarith)
    · -- second component
      unfold gsm_prodq
      split
      · -- testBit true: do complex multiplication
        rename_i hbit
        set ab := gsm_prodq p B J k with habdef
        have hab1 : |ab.1| < Z := by
          rw [habdef]
          simpa [hZdef] using h1
        have hab2 : |ab.2| < Z := by
          rw [habdef]
          simpa [hZdef] using h2
        have h_num_bound : |ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)| ≤ (2 * Z - 2) * D := by
          calc
            |ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)| ≤ |ab.1 * (cs.2 : ℤ)| + |ab.2 * (cs.1 : ℤ)| := abs_add_le _ _
            _ = |ab.1| * |(cs.2 : ℤ)| + |ab.2| * |(cs.1 : ℤ)| := by simp [abs_mul]
            _ ≤ |ab.1| * D + |ab.2| * D := by
              have hs_abs : |(cs.2 : ℤ)| ≤ D := by
                rw [abs_of_nonneg hc2_nonneg]
                exact hc2'
              have hc_abs : |(cs.1 : ℤ)| ≤ D := by
                rw [abs_of_nonneg hc1_nonneg]
                exact hc1'
              have h1 : |ab.1| * |(cs.2 : ℤ)| ≤ |ab.1| * D :=
                mul_le_mul_of_nonneg_left hs_abs (abs_nonneg _)
              have h2 : |ab.2| * |(cs.1 : ℤ)| ≤ |ab.2| * D :=
                mul_le_mul_of_nonneg_left hc_abs (abs_nonneg _)
              nlinarith
            _ = (|ab.1| + |ab.2|) * D := by ring
            _ ≤ (Z - 1 + (Z - 1)) * D := by
              have ha_int : |ab.1| ≤ Z - 1 := by omega
              have hb_int : |ab.2| ≤ Z - 1 := by omega
              nlinarith
            _ = (2 * Z - 2) * D := by ring
        have h_ediv_bound : |(ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D| ≤ 2 * Z - 2 := by
          have h_upper : (ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D ≤ 2 * Z - 2 := by
            have hle := Int.ediv_mul_le (ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) hDne0
            have hvle : ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ) ≤ (2 * Z - 2) * D :=
              (abs_le.mp h_num_bound).right
            nlinarith
          have h_lower : -(2 * Z - 2) ≤ (ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D := by
            have hlt := Int.lt_ediv_add_one_mul_self (ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) hDpos
            have hvincl : -((2 * Z - 2) * D) ≤ ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ) :=
              (abs_le.mp h_num_bound).left
            have hineq : -((2 * Z - 2) * D) < (((ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D) + 1) * D := by
              linarith
            have hdivineq : -(2 * Z - 2) < ((ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D) + 1 := by
              nlinarith
            omega
          rw [abs_le]
          constructor
          · exact h_lower
          · exact h_upper
        have h_lt : |(ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D| < 2 * Z := by
          have : |(ab.1 * (cs.2 : ℤ) + ab.2 * (cs.1 : ℤ)) / D| ≤ 2 * Z - 2 := h_ediv_bound
          omega
        simpa [gsm_cmulq, habdef, hcsdef, hDdef, h2Z] using h_lt
      · -- testBit false: unchanged
        simpa [hZdef, h2Z] using lt_of_lt_of_le h2 (by nlinarith)

theorem AdversarialBco.Bit.Transfer.bm_powq_le (q X : ℕ) (hX : X ≤ 2 ^ q) (i : ℕ) : gsm_powq q X i ≤ X
 := by
  induction' i with i ih
  · rfl
  · rw [gsm_powq]
    have hprod : gsm_powq q X i * X ≤ X * (2 ^ q) := by
      have h1 : gsm_powq q X i * X ≤ X * X := Nat.mul_le_mul ih (le_refl X)
      have h2 : X * X ≤ X * (2 ^ q) := Nat.mul_le_mul (le_refl X) hX
      exact Nat.le_trans h1 h2
    have hdiv : gsm_powq q X i * X / (2 ^ q) ≤ X * (2 ^ q) / (2 ^ q) :=
      Nat.div_le_div_right hprod
    have hcancel : X * (2 ^ q) / (2 ^ q) = X := by
      have hpos : 0 < 2 ^ q := pow_pos (by norm_num : 0 < 2) q
      exact Nat.mul_div_cancel X hpos
    rw [hcancel] at hdiv
    exact hdiv

theorem AdversarialBco.Bit.Transfer.bm_mercq_le (q X n : ℕ) (hX : X ≤ 2 ^ q) : gsm_mercq q X n ≤ n * X
 := by
  have hp : 0 < 2 ^ q := pow_pos (by norm_num) q
  have hpow_le : ∀ i, gsm_powq q X i ≤ X := by
    intro i
    induction' i with i ih
    · rfl
    · rw [gsm_powq]
      calc
        gsm_powq q X i * X / 2 ^ q ≤ gsm_powq q X i * (2 ^ q) / 2 ^ q :=
          Nat.div_le_div_right (Nat.mul_le_mul_left (gsm_powq q X i) hX)
        _ = gsm_powq q X i := by rw [Nat.mul_div_cancel _ hp]
        _ ≤ X := ih
  have hsum : gsm_mercq q X n ≤ ∑ _i ∈ Finset.range n, X := by
    rw [gsm_mercq]
    refine Finset.sum_le_sum ?_
    intro i hi
    have := hpow_le i
    exact le_trans (Nat.div_le_self _ _) this
  simpa [Finset.sum_const_nat, smul_eq_mul] using hsum

theorem AdversarialBco.Bit.Transfer.bm_digit (J k : ℕ) :
    J / 2 ^ k - 2 * (J / 2 ^ (k + 1)) = if J.testBit k then 1 else 0
 := by
  have hdiv : J / 2 ^ (k + 1) = (J / 2 ^ k) / 2 := by
    calc
      J / 2 ^ (k + 1) = J / (2 ^ k * 2) := by rw [pow_succ]
      _ = (J / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul]
  have hmod : (J / 2 ^ k) - 2 * ((J / 2 ^ k) / 2) = (J / 2 ^ k) % 2 := by
    have := Nat.div_add_mod (J / 2 ^ k) 2
    omega
  have htestBit : J.testBit k = decide ((J / 2 ^ k) % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq (x := J) (i := k)
  rw [hdiv, hmod, htestBit]
  by_cases h : (J / 2 ^ k) % 2 = 1
  · simp [h]
  · have h0 : (J / 2 ^ k) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (J / 2 ^ k) with (h0 | h1)
      · exact h0
      · exfalso; exact h h1
    simp [h0]

theorem AdversarialBco.Bit.Transfer.bm_top_digit (B J : ℕ) (hB : 1 ≤ B) (hJ : J < 2 ^ B) :
    J / 2 ^ (B - 1) = if J.testBit (B - 1) then 1 else 0
 := by
  have hpos : 0 < 2 ^ (B - 1) := by
    apply pow_pos (by norm_num) (B - 1)
  have h_lt : J / 2 ^ (B - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h_eq : 2 ^ B = 2 * 2 ^ (B - 1) := by
      calc
        2 ^ B = 2 ^ ((B - 1) + 1) := by rw [Nat.sub_add_cancel hB]
        _ = 2 ^ (B - 1) * 2 := by rw [Nat.pow_succ]
        _ = 2 * 2 ^ (B - 1) := by rw [Nat.mul_comm]
    rw [← h_eq]
    exact hJ
  have h_bit_eq : J.testBit (B - 1) = decide ((J / 2 ^ (B - 1)) % 2 = 1) := by
    calc
      J.testBit (B - 1) = J.testBit (0 + (B - 1)) := by rw [Nat.zero_add]
      _ = (J / 2 ^ (B - 1)).testBit 0 := by rw [← Nat.testBit_div_two_pow (n := B - 1) J 0]
      _ = decide ((J / 2 ^ (B - 1)) % 2 = 1) := by rw [Nat.testBit_zero]
  have h_mod_eq : (J / 2 ^ (B - 1)) % 2 = J / 2 ^ (B - 1) :=
    Nat.mod_eq_of_lt h_lt
  rw [h_bit_eq, h_mod_eq]
  have h_le_one : J / 2 ^ (B - 1) ≤ 1 := by omega
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp h_le_one) with (h | h)
  · rw [h]; simp
  · rw [h]; simp

theorem AdversarialBco.Bit.Transfer.bm_size_eq (B l : ℕ) (h1 : l = 0 ∨ 2 ^ (l - 1) ≤ B) (h2 : B < 2 ^ l) :
    Nat.size B = l
 := by
  have hle_size : Nat.size B ≤ l := (Nat.size_le.mpr h2)
  rcases h1 with (hl | hle)
  · subst hl
    simpa using Nat.eq_zero_of_le_zero hle_size
  · have hlt : l - 1 < Nat.size B := (Nat.lt_size.mpr hle)
    have hle' : l ≤ Nat.size B := by
      omega
    exact Nat.le_antisymm hle_size hle'

theorem AdversarialBco.Bit.Transfer.bm_log_eq (N e : ℕ) (h1 : 2 ^ e ≤ N) (h2 : N < 2 ^ (e + 1)) : Nat.log 2 N = e
 := by
  exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

theorem AdversarialBco.Bit.Transfer.bm_X_le (N e q : ℕ) (h : 2 ^ e ≤ N) : (N - 2 ^ e) * 2 ^ q / N ≤ 2 ^ q
 := by
  have hNpos : 0 < N := by
    have hpos : 0 < 2 ^ e := pow_pos (by norm_num : 0 < 2) e
    exact lt_of_lt_of_le hpos h
  have hsub_le : N - 2 ^ e ≤ N := Nat.sub_le _ _
  have hmul : (N - 2 ^ e) * 2 ^ q ≤ N * 2 ^ q :=
    Nat.mul_le_mul hsub_le (le_refl _)
  have hdiv : (N - 2 ^ e) * 2 ^ q / N ≤ N * 2 ^ q / N :=
    Nat.div_le_div_right hmul
  have hcancel : N * 2 ^ q / N = 2 ^ q :=
    Nat.mul_div_cancel_left (2 ^ q) hNpos
  rw [hcancel] at hdiv
  exact hdiv

theorem AdversarialBco.Bit.Transfer.bm_sqrt_le (n k : ℕ) (h : n ≤ 2 ^ (2 * k)) : Nat.sqrt n ≤ 2 ^ k
 := by
  apply Nat.le_trans (Nat.sqrt_le_sqrt h)
  have hsq : 2 ^ (2 * k) = (2 ^ k) * (2 ^ k) := by
    calc
      2 ^ (2 * k) = 2 ^ (k + k) := by rw [two_mul]
      _ = 2 ^ k * 2 ^ k := by rw [pow_add]
  rw [hsq]
  exact Nat.le_of_eq (Nat.sqrt_eq (2 ^ k))

theorem AdversarialBco.Bit.Transfer.bm_two_pow_ge_cube (n : ℕ) (hn : 10 ≤ n) : n ^ 3 ≤ 2 ^ n := by
  have h_base : 10 ^ 3 ≤ 2 ^ 10 := by decide
  have h_step : ∀ k, 10 ≤ k → k ^ 3 ≤ 2 ^ k → (k + 1) ^ 3 ≤ 2 ^ (k + 1) := by
    intro k hk hk_ih
    have h_cube_ineq : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by
      have h_ineq : 3 * k ^ 2 + 3 * k + 1 ≤ k ^ 3 := by
        have h1 : 3 * k ^ 2 + 3 * k + 1 ≤ 7 * k ^ 2 := by
          have : 3 * k + 1 ≤ 4 * k ^ 2 := by nlinarith
          nlinarith
        have h2 : 7 * k ^ 2 ≤ 10 * k ^ 2 := by omega
        have h3 : 10 * k ^ 2 ≤ k * k ^ 2 := by nlinarith
        have h4 : k * k ^ 2 = k ^ 3 := by ring
        rw [h4] at h3
        nlinarith
      nlinarith
    calc
      (k + 1) ^ 3 ≤ 2 * k ^ 3 := h_cube_ineq
      _ ≤ 2 * (2 ^ k) := Nat.mul_le_mul_left 2 hk_ih
      _ = 2 ^ (k + 1) := by ring
  exact Nat.le_induction h_base h_step n hn

theorem AdversarialBco.Bit.Transfer.bm_prec (B : ℕ) :
    B + 4 ≤ gsm_prec B ∧ 2 * B * (2 * gsm_prec B) + 2 ≤ 2 ^ gsm_prec B
:= by
  have h_first : B + 4 ≤ gsm_prec B := by
    unfold gsm_prec
    omega
  have h_second : 2 * B * (2 * gsm_prec B) + 2 ≤ 2 ^ gsm_prec B := by
    set l := Nat.size B with hl
    -- Let p = B + 2*l + 4 = gsm_prec B
    have hp_def : gsm_prec B = B + 2 * l + 4 := by
      unfold gsm_prec
      rw [hl]
    rw [hp_def]
    -- Goal: 2*B*(2*(B + 2*l + 4)) + 2 ≤ 2^(B + 2*l + 4)
    -- Rewrite LHS: 2*B*(2*(B + 2*l + 4)) + 2 = 4*B*(B + 2*l + 4) + 2
    have h_lhs : 2 * B * (2 * (B + 2 * l + 4)) + 2 = 4 * B * (B + 2 * l + 4) + 2 := by ring
    rw [h_lhs]
    -- Goal: 4*B*(B + 2*l + 4) + 2 ≤ 2^(B + 2*l + 4)
    by_cases hB : B < 3
    · -- B = 0, 1, 2: direct computation
      interval_cases B
      · -- B = 0
        simp [hl, show Nat.size 0 = 0 from Nat.size_zero]
      · -- B = 1
        simp [hl, show Nat.size 1 = 1 from Nat.size_one]
      · -- B = 2
        have hsize : Nat.size 2 = 2 := by decide
        simp [hl, hsize]
    · -- B ≥ 3
      have hB3 : 3 ≤ B := by omega
      have hp_ge_10 : 10 ≤ B + 2 * l + 4 := by
        have hl_ge_2 : 2 ≤ l := by
          rw [hl]
          by_contra! h
          have hsize_le_1 : Nat.size B ≤ 1 := by omega
          rw [Nat.size_le] at hsize_le_1
          omega
        omega
      have h_cube : (B + 2 * l + 4) ^ 3 ≤ 2 ^ (B + 2 * l + 4) :=
        AdversarialBco.Bit.Transfer.bm_two_pow_ge_cube (B + 2 * l + 4) hp_ge_10
      have h_ineq : 4 * B * (B + 2 * l + 4) + 2 ≤ (B + 2 * l + 4) ^ 3 := by
        -- We need: 4*B*p + 2 ≤ p^3 where p = B + 2*l + 4
        have hp_ge_B_add_4 : B + 4 ≤ B + 2 * l + 4 := by omega
        have hp_sq_ge_4B_add_2 : 4 * B + 2 ≤ (B + 2 * l + 4) ^ 2 := by
          have h_sq : 4 * B + 2 ≤ (B + 4)^2 := by nlinarith
          have h_pow : (B + 4)^2 ≤ (B + 2 * l + 4)^2 :=
            Nat.pow_le_pow_left hp_ge_B_add_4 2
          exact Nat.le_trans h_sq h_pow
        have hp_pos : 1 ≤ B + 2 * l + 4 := by omega
        calc
          4 * B * (B + 2 * l + 4) + 2 ≤ 4 * B * (B + 2 * l + 4) + 2 * (B + 2 * l + 4) := by
            have : 2 ≤ 2 * (B + 2 * l + 4) := by omega
            omega
          _ = (B + 2 * l + 4) * (4 * B + 2) := by ring
          _ ≤ (B + 2 * l + 4) * ((B + 2 * l + 4) ^ 2) :=
            Nat.mul_le_mul_left (B + 2 * l + 4) hp_sq_ge_4B_add_2
          _ = (B + 2 * l + 4) ^ 3 := by ring
      exact Nat.le_trans h_ineq h_cube
  exact And.intro h_first h_second

theorem AdversarialBco.Bit.Transfer.bm_LLq_bounds (B q U : ℕ) (hU : U < 2 ^ B) (hq : 1 ≤ q) :
    0 ≤ gsm_LLq B q U ∧ gsm_LLq B q U ≤ B * q * 2 ^ q
 := by
  have hU' : U + 1 ≤ 2 ^ B := by omega
  have hlog_le_B : Nat.log 2 (U + 1) ≤ B := by
    have hclog : Nat.clog 2 (U + 1) ≤ B := Nat.clog_le_of_le_pow hU'
    have hlog_clog : Nat.log 2 (U + 1) ≤ Nat.clog 2 (U + 1) := Nat.log_le_clog _ _
    exact Nat.le_trans hlog_clog hclog
  have hpos2q : 0 < 2 ^ q := pow_pos (by omega) q
  have h_two_pow_sub_le : 2 ^ (q - 1) ≤ 2 ^ q := by
    have hq' : q - 1 ≤ q := Nat.sub_le _ _
    exact Nat.pow_le_pow_right (by omega) hq'
  -- Lemma: gsm_powq q X i ≤ X when X ≤ 2^q
  have h_powq_le : ∀ (X i : ℕ), X ≤ 2 ^ q → gsm_powq q X i ≤ X := by
    intro X i hX
    induction' i with i ih
    · rfl
    · unfold gsm_powq
      have h_mul : gsm_powq q X i * X ≤ X * X := Nat.mul_le_mul ih (le_refl X)
      have h_div1 : gsm_powq q X i * X / 2 ^ q ≤ X * X / 2 ^ q :=
        Nat.div_le_div_right h_mul
      have h_div2 : X * X / 2 ^ q ≤ X := by
        rw [Nat.div_le_iff_le_mul hpos2q]
        have hXsq : X * X ≤ X * 2 ^ q := Nat.mul_le_mul_left X hX
        omega
      exact Nat.le_trans h_div1 h_div2
  -- Bound for Lam = gsm_mercq q (2^(q-1)) q
  have h_Lam_le : gsm_mercq q (2 ^ (q - 1)) q ≤ q * 2 ^ q := by
    unfold gsm_mercq
    calc
      ∑ i ∈ Finset.range q, gsm_powq q (2 ^ (q - 1)) i / (i + 1) ≤
          ∑ i ∈ Finset.range q, gsm_powq q (2 ^ (q - 1)) i :=
        Finset.sum_le_sum fun i _ => Nat.div_le_self _ _
      _ ≤ ∑ i ∈ Finset.range q, 2 ^ (q - 1) :=
        Finset.sum_le_sum fun i _ => h_powq_le (2 ^ (q - 1)) i h_two_pow_sub_le
      _ = q * 2 ^ (q - 1) := by simp
      _ ≤ q * 2 ^ q := Nat.mul_le_mul_left q (Nat.pow_le_pow_right (by omega) (by omega))
  have h_S_nonneg : 0 ≤ gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q :=
    Nat.zero_le _
  unfold gsm_LLq
  -- Goal: 0 ≤ max (((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q -
  --   gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q) 0 ∧
  --   max (...) 0 ≤ B * q * 2 ^ q
  have h_nonneg : 0 ≤ max (((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q -
      gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q) 0 :=
    le_max_right _ _
  have h_le : max (((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q -
      gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q) 0 ≤ (B : ℤ) * (q * 2 ^ q) := by
    apply max_le
    · -- expression ≤ B * (q * 2^q)
      have h_expr_le : ((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q -
          gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q ≤
          ((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q := by
        omega
      have h_mul_le : ((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q ≤
          (B : ℤ) * gsm_mercq q (2 ^ (q - 1)) q := by
        have h_nonneg_Lam : 0 ≤ (gsm_mercq q (2 ^ (q - 1)) q : ℤ) := Nat.cast_nonneg _
        have h_e_nonneg : 0 ≤ (Nat.log 2 (U + 1) : ℤ) := Nat.cast_nonneg _
        nlinarith
      have h_Lam_le' : (gsm_mercq q (2 ^ (q - 1)) q : ℤ) ≤ (q * 2 ^ q : ℕ) :=
        Nat.cast_le.mpr h_Lam_le
      have h_final : (B : ℤ) * gsm_mercq q (2 ^ (q - 1)) q ≤ (B : ℤ) * (q * 2 ^ q) := by
        nlinarith
      omega
    · -- 0 ≤ B * (q * 2^q)
      positivity
  -- Rewrite (B : ℤ) * (q * 2 ^ q) to B * q * 2 ^ q (which is automatically coerced)
  simpa [mul_assoc] using And.intro h_nonneg h_le
