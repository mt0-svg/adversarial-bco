/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# The bit length of a cleared call of BL: the lemmas on rationals

The kept rows `α̃_i = A_Sᵀ a_i`, `(1 - ε') β̃_i` of a call of BL have denominators dividing `D_S ∏_k den(a_ik)` (times
`2^{p_F} den(b_i)` for `β`), so the cleared rows are below `2^{poly}`; the call data's denominators are at most `2^s`
each. The lemmas on rationals behind these bounds: `den_num_le_of_mul`, `pair_bound`, `prod_den_le_pow`,
`natmul_bound`, `clr_bound`, `prod_den_mat`.
-/

namespace AdversarialBco.Bit.Transfer.CallSz

open Matrix

/-! ## Rationals with a bounded denominator -/

theorem den_num_le_of_mul (x : ℚ) (D : ℕ) (z : ℤ) (hD : 0 < D) (h : x * D = z) :
    x.den ≤ D ∧ x.num.natAbs ≤ z.natAbs ∧ |x| ≤ |(z : ℚ)| := by
  have hD_ne_zero : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hD_one_le : 1 ≤ (D : ℚ) := by exact_mod_cast hD
  have hx_eq_div : x = (z : ℚ) / (D : ℚ) :=
    ((eq_div_iff_mul_eq hD_ne_zero).mpr h)
  have hx_den_dvd : (x.den : ℤ) ∣ (D : ℤ) := by
    have : x = Rat.divInt z (D : ℤ) :=
      calc
        x = (z : ℚ) / (D : ℚ) := hx_eq_div
        _ = (Rat.divInt z (D : ℤ) : ℚ) := (Rat.cast_divInt z (D : ℤ)).symm
    rw [this]
    exact Rat.den_dvd z (D : ℤ)
  have h_den_le : x.den ≤ D :=
    Nat.le_of_dvd hD (by exact_mod_cast hx_den_dvd)
  have hx_den_ne_zero : (x.den : ℚ) ≠ 0 := by
    exact_mod_cast x.den_ne_zero
  have h_num_eq : (x.num : ℚ) * (D : ℚ) = (z : ℚ) * (x.den : ℚ) := by
    calc
      (x.num : ℚ) * (D : ℚ) = (((x.num : ℚ) / (x.den : ℚ)) * (x.den : ℚ)) * (D : ℚ) := by
        nth_rw 1 [← div_mul_cancel₀ (x.num : ℚ) hx_den_ne_zero]
      _ = ((x.num : ℚ) / (x.den : ℚ)) * (x.den : ℚ) * (D : ℚ) := by ring
      _ = x * (x.den : ℚ) * (D : ℚ) := by rw [Rat.num_div_den x]
      _ = (x * (D : ℚ)) * (x.den : ℚ) := by ring
      _ = (z : ℚ) * (x.den : ℚ) := by rw [h]
  have h_num_eq_int : x.num * (D : ℤ) = z * (x.den : ℤ) := by
    exact_mod_cast h_num_eq
  have h_natAbs_eq : x.num.natAbs * D = z.natAbs * x.den := by
    calc
      x.num.natAbs * D = (x.num * (D : ℤ)).natAbs := by
        simpa using (Int.natAbsHom.map_mul x.num (D : ℤ)).symm
      _ = (z * (x.den : ℤ)).natAbs := by rw [h_num_eq_int]
      _ = z.natAbs * (x.den : ℤ).natAbs := Int.natAbsHom.map_mul z (x.den : ℤ)
      _ = z.natAbs * x.den := by simp
  have h_num_natAbs_le : x.num.natAbs ≤ z.natAbs := by
    have h_mul_le : x.num.natAbs * D ≤ z.natAbs * D := by
      calc
        x.num.natAbs * D = z.natAbs * x.den := h_natAbs_eq
        _ ≤ z.natAbs * D := Nat.mul_le_mul_left z.natAbs h_den_le
    exact le_of_mul_le_mul_right h_mul_le hD
  have h_abs_le : |x| ≤ |(z : ℚ)| := by
    calc
      |x| = |(z : ℚ) / (D : ℚ)| := by rw [hx_eq_div]
      _ = |(z : ℚ)| / |(D : ℚ)| := by rw [abs_div]
      _ = |(z : ℚ)| / (D : ℚ) := by
        have : |(D : ℚ)| = (D : ℚ) := abs_of_pos (by exact_mod_cast hD)
        rw [this]
      _ ≤ |(z : ℚ)| := div_le_self (abs_nonneg _) hD_one_le
  exact And.intro h_den_le (And.intro h_num_natAbs_le h_abs_le)

theorem clr_bound {s S R : ℕ} (x : ℚ) (hdvd : x.den ∣ R) (hR : R ≤ 2 ^ S) (hx : |x| ≤ 2 ^ s) :
    (x.num * ((R / x.den : ℕ) : ℤ)).natAbs ≤ 2 ^ (s + S) := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left c x.den_pos]
  have key : ((x.num * (c : ℤ) : ℤ) : ℚ) = x * ((x.den * c : ℕ) : ℚ) := by
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have h1 : |((x.num * (c : ℤ) : ℤ) : ℚ)| ≤ 2 ^ (s + S) := by
    rw [key, abs_mul, pow_add, Nat.abs_cast]
    exact mul_le_mul hx (by exact_mod_cast hR) (by positivity) (by positivity)
  have h2 : |x.num * (c : ℤ)| ≤ 2 ^ (s + S) := by exact_mod_cast h1
  have h3 : ((x.num * (c : ℤ)).natAbs : ℤ) ≤ 2 ^ (s + S) := by rw [Int.natCast_natAbs]; exact h2
  exact_mod_cast h3

theorem pair_bound {s : ℕ} (u v : ℤ) (x : ℚ) (hv : 0 < v) (hu : |u| ≤ 2 ^ s)
    (hvs : v ≤ 2 ^ s) (h : (u : ℚ) / v = x) : x.den ≤ 2 ^ s ∧ x.num.natAbs ≤ 2 ^ s ∧ |x| ≤ 2 ^ s := by
  have hpos : 0 ≤ v := by linarith
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hx_mul : x * (v : ℚ) = (u : ℚ) := by
    calc
      x * (v : ℚ) = ((u : ℚ) / (v : ℚ)) * (v : ℚ) := by rw [h]
      _ = (u : ℚ) := by field_simp [hv']
  have h_cast : (v.toNat : ℚ) = (v : ℚ) := by
    exact mod_cast Int.toNat_of_nonneg hpos
  have h_mul_nat : x * (v.toNat : ℚ) = (u : ℚ) := by
    rw [h_cast]
    exact hx_mul
  have hDpos : 0 < v.toNat := by
    have hne : v.toNat ≠ 0 := by
      intro hzero
      have hle : v ≤ 0 := (Int.toNat_eq_zero.mp hzero)
      linarith
    exact Nat.pos_of_ne_zero hne
  rcases den_num_le_of_mul x v.toNat u hDpos h_mul_nat with ⟨hden, hnum, hxabs⟩
  have hden' : x.den ≤ 2 ^ s := by
    apply le_trans hden
    have : (v.toNat : ℤ) ≤ (2 ^ s : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
      exact hvs
    exact_mod_cast this
  have hnum' : x.num.natAbs ≤ 2 ^ s := by
    apply le_trans hnum
    have : (u.natAbs : ℤ) ≤ (2 ^ s : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hu
    exact_mod_cast this
  have habs' : |x| ≤ 2 ^ s := by
    apply le_trans hxabs
    -- need |(u : ℚ)| ≤ (2 ^ s : ℚ)
    -- from hu : |u| ≤ 2 ^ s in ℤ
    have htemp : (|u| : ℚ) ≤ (2 ^ s : ℚ) := by exact_mod_cast hu
    simpa [Int.cast_abs] using htemp
  exact And.intro hden' (And.intro hnum' habs')

theorem prod_den_le_pow {ι : Type*} [Fintype ι] {s : ℕ} (x : ι → ℚ)
    (h : ∀ i, (x i).den ≤ 2 ^ s) : ∏ i, (x i).den ≤ 2 ^ (s * Fintype.card ι) := by
  calc
    ∏ i, (x i).den ≤ (2 ^ s) ^ (Fintype.card ι) := by
      calc
        ∏ i, (x i).den = (Finset.univ : Finset ι).prod (fun i => (x i).den) := by simp
        _ ≤ (2 ^ s) ^ ((Finset.univ : Finset ι).card) :=
          Finset.prod_le_pow_card _ _ _ (fun i hi => h i)
        _ = (2 ^ s) ^ (Fintype.card ι) := by simp
    _ = 2 ^ (s * Fintype.card ι) := by rw [pow_mul]

theorem natmul_bound {s S : ℕ} (N : ℕ) (x : ℚ) (hN : N ≤ 2 ^ S)
    (hd : x.den ≤ 2 ^ s) (hn : x.num.natAbs ≤ 2 ^ s) :
    ((N : ℚ) * x).num.natAbs ≤ 2 ^ (S + s) ∧ ((N : ℚ) * x).den ≤ 2 ^ s := by
  have hden_pos : 0 < x.den := Rat.den_pos _
  have h_eq : ((N : ℚ) * x) * (x.den : ℚ) = (((N : ℤ) * x.num : ℤ) : ℚ) := by
    calc
      ((N : ℚ) * x) * (x.den : ℚ) = (N : ℚ) * (x * (x.den : ℚ)) := by ring
      _ = (N : ℚ) * (x.num : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = (((N : ℤ) * x.num : ℤ) : ℚ) := by simp
  have h_results := den_num_le_of_mul ((N : ℚ) * x) x.den ((N : ℤ) * x.num) hden_pos h_eq
  rcases h_results with ⟨hden_le, hnum_le, _⟩
  have hden_le' : ((N : ℚ) * x).den ≤ 2 ^ s := le_trans hden_le hd
  have hnum_le' : ((N : ℚ) * x).num.natAbs ≤ 2 ^ (S + s) := by
    calc
      ((N : ℚ) * x).num.natAbs ≤ ((N : ℤ) * x.num).natAbs := hnum_le
      _ = (N : ℤ).natAbs * x.num.natAbs := by rw [Int.natAbs_mul]
      _ = N * x.num.natAbs := by simp
      _ ≤ 2 ^ S * 2 ^ s := Nat.mul_le_mul hN hn
      _ = 2 ^ (S + s) := by rw [pow_add]
  exact And.intro hnum_le' hden_le'

/-- The denominators of a matrix, at most `2^s` each: their product is at most `2^(s d²)`. -/
theorem prod_den_mat {d s : ℕ} (X : Matrix (Fin d) (Fin d) ℚ) (h : ∀ i j, (X i j).den ≤ 2 ^ s) :
    ∏ i, ∏ j, (X i j).den ≤ 2 ^ (s * (d * d)) := by
  calc ∏ i, ∏ j, (X i j).den ≤ ∏ _i : Fin d, 2 ^ (s * d) :=
        Finset.prod_le_prod fun i _ => by
          simpa [Fintype.card_fin] using prod_den_le_pow (X i) (h i)
    _ = 2 ^ (s * (d * d)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring_nf

end AdversarialBco.Bit.Transfer.CallSz

