/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-! # Roundings and square roots on the integers

`sqrtDn` of a fraction of integers through the Euclidean quotient (`qn_sqrtDn_div`) and the positivity of its
numerator (`sqrtNum_pos`); a rounded increment added to a point of the grid (`qn_rnd_add`).
-/

open AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer.BLM

/-- The numerator of the square root of a fraction at least `1/2` is positive once `k ≥ 1`. -/
theorem AdversarialBco.Bit.Transfer.BLM.sqrtNum_pos (k : ℕ) (U V : ℤ) (hk : 1 ≤ k) (hV : 0 < V) (h : V ≤ 2 * U) :
    1 ≤ Nat.sqrt (U * 4 ^ k / V).toNat := by
  have hUpos : 0 < U := by
    linarith
  have h_num_nonneg : 0 ≤ U * (4 : ℤ) ^ k := by
    have hU_nonneg : 0 ≤ U := by linarith
    have h4k_nonneg : 0 ≤ (4 : ℤ) ^ k := pow_nonneg (by norm_num) k
    nlinarith
  have h_div_nonneg : 0 ≤ U * (4 : ℤ) ^ k / V :=
    Int.ediv_nonneg h_num_nonneg (by linarith)
  have h4k_ge_4 : (4 : ℤ) ≤ (4 : ℤ) ^ k := by
    have h_nat : (4 : ℕ) ^ 1 ≤ (4 : ℕ) ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast h_nat
  have hV_le_U4k : (V : ℤ) ≤ U * (4 : ℤ) ^ k := by
    calc
      V ≤ 2 * U := h
      _ ≤ (4 : ℤ) * U := by
        nlinarith
      _ = U * (4 : ℤ) := by ring
      _ ≤ U * (4 : ℤ) ^ k := by
        nlinarith
  rw [Nat.le_sqrt]
  simp
  rw [Int.le_toNat h_div_nonneg]
  rw [Int.le_ediv_iff_mul_le hV]
  simpa [one_mul] using hV_le_U4k

/-- Adding a rounded increment to a point of the grid: the sum stays on the grid and its numerator is the sum of the
numerators. -/
theorem AdversarialBco.Bit.Transfer.BLM.qn_rnd_add (k : ℕ) (x y : ℚ) (hx : OnG k x) :
    OnG k (x + rnd k y) ∧ qn k (x + rnd k y) = qn k x + ⌊y * 2 ^ k + 1 / 2⌋ := by
  unfold OnG qn rnd
  have hpow : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hx_eq : (⌊x * (2 : ℚ) ^ k⌋ : ℚ) = x * (2 : ℚ) ^ k := hx
  have hcalc : (x + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ k = x * (2 : ℚ) ^ k + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) := by
    field_simp [hpow]
  have hfloor_add : ⌊x * (2 : ℚ) ^ k + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ)⌋ = ⌊x * (2 : ℚ) ^ k⌋ + ⌊y * (2 : ℚ) ^ k + 1 / 2⌋ := by
    simpa [add_comm] using Int.floor_add_intCast (x * (2 : ℚ) ^ k) ⌊y * (2 : ℚ) ^ k + 1 / 2⌋
  constructor
  · calc
      (⌊(x + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ k⌋ : ℚ) = (⌊x * (2 : ℚ) ^ k + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ)⌋ : ℚ) := by
        rw [hcalc]
      _ = ((⌊x * (2 : ℚ) ^ k⌋ + ⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℤ) : ℚ) := by
        exact congrArg (fun z : ℤ => (z : ℚ)) hfloor_add
      _ = (⌊x * (2 : ℚ) ^ k⌋ : ℚ) + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) := by simp
      _ = x * (2 : ℚ) ^ k + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) := by simp [hx_eq]
      _ = (x + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ k := by rw [hcalc]
  · calc
      ⌊(x + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ k⌋ = ⌊x * (2 : ℚ) ^ k + (⌊y * (2 : ℚ) ^ k + 1 / 2⌋ : ℚ)⌋ := by
        rw [hcalc]
      _ = ⌊x * (2 : ℚ) ^ k⌋ + ⌊y * (2 : ℚ) ^ k + 1 / 2⌋ := hfloor_add

/-- The numerator of `sqrtDn` of a nonnegative fraction of integers, on the grid `2^{-k}`. -/
theorem AdversarialBco.Bit.Transfer.BLM.qn_sqrtDn_div (k : ℕ) (U V : ℤ) (hU : 0 ≤ U) (hV : 0 < V) :
    qn k (sqrtDn k ((U : ℚ) / V)) = ((Nat.sqrt (U * 4 ^ k / V).toNat : ℕ) : ℤ) ∧
      OnG k (sqrtDn k ((U : ℚ) / V)) := by
  have hVpos : (0 : ℚ) < V := by exact_mod_cast hV
  have hUnonneg : (0 : ℚ) ≤ U := by exact_mod_cast hU
  have h_two_pow_pos : 0 < ((2 : ℚ) ^ k) := by positivity
  have h_two_pow_ne_zero : ((2 : ℚ) ^ k) ≠ 0 := by linarith
  set A := (U : ℚ) * ((4 : ℚ) ^ k) / (V : ℚ) with hA
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    refine div_nonneg (mul_nonneg hUnonneg (by positivity)) (by linarith)
  have hA_eq : A = ((U * 4 ^ k : ℤ) : ℚ) / (V : ℚ) := by
    dsimp [A]
    push_cast
    ring
  -- Unfold definitions
  simp [qn, sqrtDn, OnG]
  -- Simplify the expression
  have h_mul_div : ((Nat.sqrt ⌊A⌋₊ : ℚ) / ((2 : ℚ) ^ k)) * ((2 : ℚ) ^ k) = (Nat.sqrt ⌊A⌋₊ : ℚ) := by
    field_simp [h_two_pow_ne_zero]
  -- Now the goal becomes:
  -- ⌊(Nat.sqrt ⌊A⌋₊ : ℚ)⌋ = ↑(U * 4 ^ k / V).toNat.sqrt ∧
  --   ↑⌊(Nat.sqrt ⌊A⌋₊ : ℚ)⌋ = (Nat.sqrt ⌊A⌋₊ : ℚ)
  -- The second conjunct is trivial by simp
  have h_floor_natCast : ⌊(Nat.sqrt ⌊A⌋₊ : ℚ)⌋ = (Nat.sqrt ⌊A⌋₊ : ℤ) := by
    simp
  -- For the first conjunct, we need ⌊A⌋₊ = (U * 4 ^ k / V).toNat
  have h_floor_eq : ⌊A⌋₊ = (U * 4 ^ k / V).toNat := by
    set q := U * 4 ^ k / V with hq_def
    have hq_nonneg : 0 ≤ q := by
      rw [hq_def]
      exact Int.ediv_nonneg (mul_nonneg hU (pow_nonneg (by norm_num) k)) hV.le
    have hq_natCast : ((q.toNat : ℕ) : ℚ) = (q : ℚ) := by
      -- Int.toNat_of_nonneg gives equality in ℤ, we need it in ℚ
      have := Int.toNat_of_nonneg hq_nonneg
      -- this : (q.toNat : ℤ) = q
      exact_mod_cast this
    have hV_ne_zero : V ≠ 0 := by linarith
    have hV_pos_rat : 0 < (V : ℚ) := by exact_mod_cast hV
    apply (Nat.floor_eq_iff hA_nonneg).mpr
    constructor
    · -- ((q.toNat : ℕ) : ℚ) ≤ A
      rw [hq_natCast, hA]
      -- Need (q : ℚ) ≤ (U : ℚ) * 4 ^ k / V
      have h_mul_le : q * V ≤ U * 4 ^ k := by
        rw [hq_def]
        exact Int.ediv_mul_le (U * 4 ^ k) hV_ne_zero
      have h_mul_le_rat : (q : ℚ) * (V : ℚ) ≤ ((U * 4 ^ k : ℤ) : ℚ) := by
        exact_mod_cast h_mul_le
      field_simp [hV_pos_rat.ne.symm] at h_mul_le_rat ⊢
      push_cast at h_mul_le_rat ⊢
      exact h_mul_le_rat
    · -- A < ((q.toNat : ℕ) : ℚ) + 1
      rw [hq_natCast, hA]
      -- Need (U : ℚ) * 4 ^ k / V < (q : ℚ) + 1
      have h_div_add_emod := EuclideanDomain.div_add_mod (U * 4 ^ k) V
      rw [← hq_def] at h_div_add_emod
      set r := U * 4 ^ k % V with hr_def
      have hr_lt_V : r < V := by
        have h_lt_natAbs := Int.emod_lt (U * 4 ^ k) hV_ne_zero
        have h_natAbs_eq : (V.natAbs : ℤ) = V := Int.natAbs_of_nonneg hV.le
        rw [← hr_def, h_natAbs_eq] at h_lt_natAbs
        exact h_lt_natAbs
      have h_eq_rat : (U : ℚ) * ((4 : ℚ) ^ k) / (V : ℚ) = (q : ℚ) + (r : ℚ) / (V : ℚ) := by
        field_simp [hV_pos_rat.ne.symm]
        -- Goal: (U : ℚ) * 4 ^ k = (V : ℚ) * (q : ℚ) + (r : ℚ)
        -- From h_div_add_emod: V * q + r = U * 4 ^ k (in ℤ)
        -- Cast to ℚ and rearrange
        have htemp := congrArg (fun x : ℤ => (x : ℚ)) h_div_add_emod
        -- htemp: (V * q + r : ℚ) = (U * 4 ^ k : ℚ)
        push_cast at htemp
        -- htemp: (V : ℚ) * (q : ℚ) + (r : ℚ) = (U : ℚ) * 4 ^ k
        linarith
      rw [h_eq_rat]
      have h_lt : (r : ℚ) / (V : ℚ) < 1 := by
        apply (div_lt_one hV_pos_rat).mpr
        exact_mod_cast hr_lt_V
      linarith
  -- Now combine everything
  have h_first_conjunct : ⌊A⌋₊.sqrt = (U * 4 ^ k / V).toNat.sqrt := by
    rw [h_floor_eq]
  have hA' : A = (U : ℚ) / V * ((4 : ℚ) ^ k) := by
    dsimp [A]
    ring
  rw [← hA']
  exact h_first_conjunct
