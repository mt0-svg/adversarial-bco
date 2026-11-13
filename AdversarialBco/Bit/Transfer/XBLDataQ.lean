/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The call data of BL's round: bounds, casts and grid facts

The polynomial bounds of the call data commands (`units_le`, `s_le`, `l_lt`, `a_lt`), the integer slots (`slot_pow_le`,
`slot_rat`, `eHat_int`), positivity on the grid (`floor_pos_of_grid`, `QQD_bound`) and the Gram product
with a vector (`gram_mulVec_bound`).
-/

open Matrix

theorem AdversarialBco.Bit.Transfer.DataP.units_le (d E : ℕ) (hd : 1 ≤ d) :
    22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 ≤ 1024 * (d + E + 1) ^ 3 := by
  have hdpos : 0 < d := by omega
  have hd_le_d3 : d ≤ d ^ 3 := by
    calc
      d = d ^ 1 := by simp
      _ ≤ d ^ 3 := Nat.pow_le_pow_right hdpos (by omega)
  have hd2_le_d3 : d ^ 2 ≤ d ^ 3 :=
    Nat.pow_le_pow_right hdpos (by omega)
  have h1_le_d3 : 1 ≤ d ^ 3 :=
    le_trans hd hd_le_d3
  have h200 : 200 ≤ 200 * d ^ 3 :=
    Nat.mul_le_mul_left 200 h1_le_d3
  have h100d : 100 * d ≤ 100 * d ^ 3 :=
    Nat.mul_le_mul_left 100 hd_le_d3
  have h50d2 : 50 * d ^ 2 ≤ 50 * d ^ 3 :=
    Nat.mul_le_mul_left 50 hd2_le_d3
  have hLHS : 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 ≤ 372 * d ^ 3 := by
    have hsum : 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 ≤ 22 * d ^ 3 + 50 * d ^ 3 + 100 * d ^ 3 + 200 * d ^ 3 := by
      exact add_le_add (add_le_add (add_le_add (le_refl _) h50d2) h100d) h200
    have hsum_eq : 22 * d ^ 3 + 50 * d ^ 3 + 100 * d ^ 3 + 200 * d ^ 3 = 372 * d ^ 3 := by ring
    rw [hsum_eq] at hsum
    exact hsum
  have hRHS : 1024 * d ^ 3 ≤ 1024 * (d + E + 1) ^ 3 := by
    have hcube : d ^ 3 ≤ (d + E + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    exact Nat.mul_le_mul_left 1024 hcube
  have h372_1024 : 372 * d ^ 3 ≤ 1024 * d ^ 3 :=
    Nat.mul_le_mul_right (d ^ 3) (by omega)
  calc
    22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 ≤ 372 * d ^ 3 := hLHS
    _ ≤ 1024 * d ^ 3 := h372_1024
    _ ≤ 1024 * (d + E + 1) ^ 3 := hRHS

theorem AdversarialBco.Bit.Transfer.DataP.s_le (d E : ℕ) : d + 5 * E + 12 ≤ 1024 * (d + E + 1) ^ 3 := by
  set W := d + E + 1 with hW
  have hWpos : W ≠ 0 := by
    omega
  have h1 : d + 5 * E + 12 ≤ 12 * W := by
    omega
  have h2 : 12 * W ≤ 1024 * W := by
    omega
  have h3 : 1024 * W ≤ 1024 * W ^ 3 := by
    have hWle : W ≤ W ^ 3 := Nat.le_self_pow (by omega : 3 ≠ 0) W
    exact Nat.mul_le_mul_left 1024 hWle
  exact le_trans h1 (le_trans h2 h3)

theorem AdversarialBco.Bit.Transfer.DataP.l_lt (d E ℓ : ℕ) (h : 1024 * (d + E + 1) ^ 3 ≤ ℓ) : 4 * d + 10 * E + 100 < ℓ := by
  have hd : (0 : ℤ) ≤ d := by exact_mod_cast Nat.zero_le _
  have hE : (0 : ℤ) ≤ E := by exact_mod_cast Nat.zero_le _
  have hx : (1 : ℤ) ≤ (d : ℤ) + (E : ℤ) + 1 := by
    omega
  have hineq : (4 * (d : ℤ) + 10 * (E : ℤ) + 100) < 1024 * ((d : ℤ) + (E : ℤ) + 1) ^ 3 := by
    have h_upper : 4 * (d : ℤ) + 10 * (E : ℤ) + 100 ≤ 10 * ((d : ℤ) + (E : ℤ) + 1) + 90 := by
      nlinarith
    have hcube : ((d : ℤ) + (E : ℤ) + 1) ^ 3 ≥ (d : ℤ) + (E : ℤ) + 1 := by
      have hx' : (0 : ℤ) ≤ (d : ℤ) + (E : ℤ) + 1 := by omega
      have hsq : ((d : ℤ) + (E : ℤ) + 1) ^ 2 - 1 ≥ 0 := by
        nlinarith
      have h_eq : ((d : ℤ) + (E : ℤ) + 1) ^ 3 - ((d : ℤ) + (E : ℤ) + 1) =
          ((d : ℤ) + (E : ℤ) + 1) * (((d : ℤ) + (E : ℤ) + 1) ^ 2 - 1) := by ring
      have h_nonneg : 0 ≤ ((d : ℤ) + (E : ℤ) + 1) * (((d : ℤ) + (E : ℤ) + 1) ^ 2 - 1) := by
        nlinarith
      omega
    have h_lower : 10 * ((d : ℤ) + (E : ℤ) + 1) + 90 < 1024 * ((d : ℤ) + (E : ℤ) + 1) ^ 3 := by
      nlinarith
    linarith
  have h' : (1024 * (d + E + 1) ^ 3 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast h
  have hlt : (4 * (d : ℤ) + 10 * (E : ℤ) + 100) < (ℓ : ℤ) := by
    linarith
  exact_mod_cast hlt

theorem AdversarialBco.Bit.Transfer.DataP.a_lt (d E ℓa : ℕ) (h : 1024 * (d + E + 1) ^ 3 < 2 ^ ℓa) : d * d + d < 2 ^ ℓa := by
  set W := d + E + 1 with hW
  have hd_le_W : d ≤ W := by omega
  have hd1_le_W : d + 1 ≤ W := by omega
  have hW_sq_le_2W_sq : W ^ 2 ≤ 2 * W ^ 2 := by omega
  have hW_sq_le_W_cu : W ^ 2 ≤ W ^ 3 := by
    by_cases hW0 : W = 0
    · have hd0 : d = 0 := by omega
      have hE1 : E + 1 = 0 := by omega
      omega
    · have hW1 : 1 ≤ W := by omega
      calc
        W ^ 2 = 1 * W ^ 2 := by simp
        _ ≤ W * W ^ 2 := Nat.mul_le_mul hW1 (le_refl _)
        _ = W ^ 3 := by ring
  have h2_le_1024 : 2 ≤ 1024 := by norm_num
  calc
    d * d + d = d * (d + 1) := by ring
    _ ≤ W * W := Nat.mul_le_mul hd_le_W hd1_le_W
    _ = W ^ 2 := by ring
    _ ≤ 2 * W ^ 2 := hW_sq_le_2W_sq
    _ ≤ 2 * W ^ 3 := Nat.mul_le_mul (le_refl _) hW_sq_le_W_cu
    _ ≤ 1024 * W ^ 3 := Nat.mul_le_mul h2_le_1024 (le_refl _)
    _ = 1024 * (d + E + 1) ^ 3 := by simp [hW]
    _ < 2 ^ ℓa := h

theorem AdversarialBco.Bit.Transfer.DataP.slot_pow_le (v : ℝ) (k E : ℕ) (hb : ∃ z : ℤ, v = z ∧ |z| ≤ 2 ^ E)
    (hv : v = (2 : ℝ) ^ k) : k ≤ E := by
  rcases hb with ⟨z, hz1, hz2⟩
  have hz_eq_real : (z : ℝ) = (2 : ℝ) ^ k := by
    calc
      (z : ℝ) = v := by symm; exact hz1
      _ = (2 : ℝ) ^ k := hv
  have hz_eq : z = (2 : ℤ) ^ k := by exact_mod_cast hz_eq_real
  have h_nonneg : 0 ≤ (2 : ℤ) ^ k := pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) k
  have h_abs' : |(2 : ℤ) ^ k| = (2 : ℤ) ^ k := abs_of_nonneg h_nonneg
  have h_pow_le : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ E := by
    calc
      (2 : ℤ) ^ k = |(2 : ℤ) ^ k| := by symm; exact h_abs'
      _ = |z| := by rw [hz_eq]
      _ ≤ (2 : ℤ) ^ E := hz2
  have h_pos : 1 < (2 : ℤ) := by norm_num
  exact ((pow_le_pow_iff_right₀ h_pos).mp h_pow_le)

theorem AdversarialBco.Bit.Transfer.DataP.slot_rat (v : ℝ) (q : ℚ) (E : ℕ) (hb : ∃ z : ℤ, v = z ∧ |z| ≤ 2 ^ E)
    (hv : v = (q : ℝ)) : ∃ z : ℤ, q = z ∧ v = z ∧ |z| ≤ 2 ^ E := by
  rcases hb with ⟨z, hvz, hz⟩
  have hqz : q = z := by
    apply Rat.cast_injective (α := ℝ)
    calc
      (q : ℝ) = v := by symm; exact hv
      _ = (z : ℝ) := hvz
  exact ⟨z, hqz, hvz, hz⟩

theorem AdversarialBco.Bit.Transfer.DataP.floor_pos_of_grid (R : ℚ) (k : ℕ) (hR : 0 < R)
    (hon : ((⌊R * 2 ^ k⌋ : ℤ) : ℚ) = R * 2 ^ k) : 0 < ⌊R * 2 ^ k⌋ := by
  have hpos : 0 < R * ((2 : ℚ) ^ k) := by
    have h2 : 0 < (2 : ℚ) := by norm_num
    have h2pow : 0 < (2 : ℚ) ^ k := pow_pos h2 k
    exact mul_pos hR h2pow
  have hpos' : 0 < ((⌊R * 2 ^ k⌋ : ℤ) : ℚ) := by
    rw [hon]
    exact hpos
  exact_mod_cast hpos'

theorem AdversarialBco.Bit.Transfer.DataP.eHat_int (e : ℚ) (H : ℤ) (h : e⁻¹ = (H : ℚ)) (hpos : 0 < e⁻¹) :
    0 < H ∧ e = 1 / (H : ℚ) := by
  have hHpos_rat : 0 < (H : ℚ) := by
    rw [← h]
    exact hpos
  have hHpos_int : 0 < H := by exact_mod_cast hHpos_rat
  have heq : e = 1 / (H : ℚ) := by
    calc
      e = (e⁻¹)⁻¹ := by simp
      _ = ((H : ℚ))⁻¹ := by rw [h]
      _ = 1 / (H : ℚ) := by simp
  exact And.intro hHpos_int heq

theorem AdversarialBco.Bit.Transfer.DataP.QQD_bound (p E : ℕ) (Dw : ℤ) (hp : p ≤ E) (hD : 0 < Dw) (bD : Dw ≤ 2 ^ E) :
    0 < 2 ^ p * 2 ^ p * Dw ∧ 2 ^ p * 2 ^ p * Dw ≤ (2 : ℤ) ^ (3 * E) := by
  have h2pos : (0 : ℤ) < 2 := by norm_num
  have h2pow_pos : ∀ n : ℕ, 0 < (2 : ℤ) ^ n := fun n => pow_pos h2pos n
  have hpos : 0 < (2 : ℤ) ^ p * (2 : ℤ) ^ p * Dw := by
    apply mul_pos
    · apply mul_pos
      · exact h2pow_pos p
      · exact h2pow_pos p
    · exact hD
  have hpow_le : (2 : ℤ) ^ p ≤ (2 : ℤ) ^ E := by
    have h_one_le_two : (1 : ℤ) ≤ 2 := by norm_num
    exact pow_le_pow_right₀ h_one_le_two hp
  have h_nonneg_pow : ∀ n : ℕ, 0 ≤ (2 : ℤ) ^ n := fun n => pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) n
  have h_nonneg_Dw : 0 ≤ Dw := le_of_lt hD
  have h_mul_le : (2 : ℤ) ^ p * (2 : ℤ) ^ p * Dw ≤ (2 : ℤ) ^ E * (2 : ℤ) ^ E * (2 : ℤ) ^ E := by
    have h_sq_le : (2 : ℤ) ^ p * (2 : ℤ) ^ p ≤ (2 : ℤ) ^ E * (2 : ℤ) ^ E :=
      mul_le_mul hpow_le hpow_le (h_nonneg_pow p) (h_nonneg_pow E)
    exact mul_le_mul h_sq_le bD h_nonneg_Dw (mul_nonneg (h_nonneg_pow E) (h_nonneg_pow E))
  have h_pow_add : (2 : ℤ) ^ E * (2 : ℤ) ^ E * (2 : ℤ) ^ E = (2 : ℤ) ^ (3 * E) := by
    calc
      (2 : ℤ) ^ E * (2 : ℤ) ^ E * (2 : ℤ) ^ E = ((2 : ℤ) ^ E * (2 : ℤ) ^ E) * (2 : ℤ) ^ E := rfl
      _ = (2 : ℤ) ^ (E + E) * (2 : ℤ) ^ E := by rw [← pow_add]
      _ = (2 : ℤ) ^ ((E + E) + E) := by rw [← pow_add]
      _ = (2 : ℤ) ^ (3 * E) := by ring
  have h_le : (2 : ℤ) ^ p * (2 : ℤ) ^ p * Dw ≤ (2 : ℤ) ^ (3 * E) :=
    h_mul_le.trans (by rw [h_pow_add])
  exact And.intro hpos h_le

theorem AdversarialBco.Bit.Transfer.DataP.gram_mulVec_bound {d E : ℕ} (Bh : Matrix (Fin d) (Fin d) ℤ) (wh : Fin d → ℤ)
    (hB : ∀ i j, |Bh i j| ≤ 2 ^ E) (hw : ∀ j, |wh j| ≤ 2 ^ E) (i : Fin d) :
    |((Bh * Bhᵀ) *ᵥ wh) i| ≤ 2 ^ (2 * d + 3 * E) := by
  have h_bound_entry : ∀ i j, |(Bh * Bhᵀ) i j| ≤ (d : ℤ) * ((2 : ℤ) ^ (2 * E)) := by
    intro i j
    rw [Matrix.mul_apply]
    calc
      |∑ k, Bh i k * Bhᵀ k j| ≤ ∑ k, |Bh i k * Bhᵀ k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |Bh i k| * |Bhᵀ k j| := by
        simp_rw [abs_mul]
      _ = ∑ k, |Bh i k| * |Bh j k| := by simp
      _ ≤ ∑ k : Fin d, (2 ^ E) * (2 ^ E) := by
        refine Finset.sum_le_sum ?_
        intro k _
        refine mul_le_mul (hB i k) (hB j k) (by positivity) (by positivity)
      _ = (Finset.card (Finset.univ : Finset (Fin d))) • ((2 : ℤ) ^ E * (2 : ℤ) ^ E) := by
        simp [Finset.sum_const]
      _ = (d : ℤ) * ((2 : ℤ) ^ E * (2 : ℤ) ^ E) := by
        simp
      _ = (d : ℤ) * ((2 : ℤ) ^ (2 * E)) := by
        rw [show ((2 : ℤ) ^ E) * ((2 : ℤ) ^ E) = ((2 : ℤ) ^ (E + E)) by rw [pow_add],
          show (E + E : ℕ) = (2 * E : ℕ) by omega]
  calc
    |((Bh * Bhᵀ) *ᵥ wh) i| = |∑ j, (Bh * Bhᵀ) i j * wh j| := by rw [Matrix.mulVec_apply_eq_sum]
    _ ≤ ∑ j, |(Bh * Bhᵀ) i j * wh j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |(Bh * Bhᵀ) i j| * |wh j| := by simp_rw [abs_mul]
    _ ≤ ∑ j : Fin d, ((d : ℤ) * ((2 : ℤ) ^ (2 * E))) * ((2 : ℤ) ^ E) := by
      refine Finset.sum_le_sum ?_
      intro j _
      refine mul_le_mul (h_bound_entry i j) (hw j) (by positivity) (by positivity)
    _ = (Finset.card (Finset.univ : Finset (Fin d))) • (((d : ℤ) * ((2 : ℤ) ^ (2 * E))) * ((2 : ℤ) ^ E)) := by
      simp [Finset.sum_const]
    _ = (d : ℤ) * (((d : ℤ) * ((2 : ℤ) ^ (2 * E))) * ((2 : ℤ) ^ E)) := by
      simp
    _ = (d : ℤ) * ((d : ℤ) * (((2 : ℤ) ^ (2 * E)) * ((2 : ℤ) ^ E))) := by ring
    _ = (d : ℤ) * ((d : ℤ) * ((2 : ℤ) ^ (2 * E + E))) := by rw [pow_add]
    _ = (d : ℤ) * ((d : ℤ) * ((2 : ℤ) ^ (3 * E))) := by ring
    _ ≤ (d : ℤ) * (((2 : ℤ) ^ d) * ((2 : ℤ) ^ (3 * E))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
      exact mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := d))
    _ = (d : ℤ) * ((2 : ℤ) ^ (d + 3 * E)) := by rw [pow_add]
    _ ≤ ((2 : ℤ) ^ d) * ((2 : ℤ) ^ (d + 3 * E)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := d))
    _ = (2 : ℤ) ^ (d + (d + 3 * E)) := by rw [← pow_add]
    _ = (2 : ℤ) ^ (2 * d + 3 * E) := by ring

