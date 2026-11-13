/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# The bit length of a cleared call of BL

`ellSz_call`: the integer problem `clearQ (callOf cfg H g ℓ r P f e)` of a call of BL, with `cfg = mkCfg d n m A b c S`,
has bit length at most `callSzB d E s (size M) = 4 (d + 1)^2 (E + s + size M + 1) + 1` when the input has height `M`,
the position sits in BL's cells with integers at most `2^E` (`RowCtx`) and the call data are pairs below `2^s`
(`PrepIn`). The kept rows `α̃_i = A_Sᵀ a_i`, `(1 - ε') β̃_i` have denominators dividing `D_S ∏_k den(a_ik)` (times
`2^{p_F} den(b_i)` for `β`), so `rowDen` and the cleared rows are below `2^{poly}`; the call data's denominators are at
most `2^s` each.
The lemmas on rationals: `den_num_le_of_mul`, `row_scale`, `prod_den_le`, `pair_bound`, `prod_den_le_pow`,
`natmul_bound`, `clr_row_bound`, `callSz_exps`, `clr_bound`, `colDot_bound`, `beta_bound`.
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

theorem row_scale {d M : ℕ} (a : Fin d → ℚ) (ha : ∀ k, (a k).num.natAbs ≤ M ∧ (a k).den ≤ M) (k : Fin d) :
    ∃ z : ℤ, a k * ((∏ l, (a l).den : ℕ) : ℚ) = z ∧ z.natAbs ≤ M ^ d := by
  set z := (a k).num * ∏ l ∈ Finset.univ.erase k, (a l).den with hz
  refine ⟨z, ?_, ?_⟩
  · -- a k * ((∏ l, (a l).den : ℕ) : ℚ) = (z : ℚ)
    have hprod_split : (∏ l : Fin d, (a l).den : ℕ) = (a k).den * ∏ l ∈ Finset.univ.erase k, (a l).den := by
      simpa [mul_comm] using (Finset.prod_erase_mul (Finset.univ : Finset (Fin d)) (fun l => (a l).den) (Finset.mem_univ k)).symm
    calc
      a k * ((∏ l, (a l).den : ℕ) : ℚ) = a k * (((a k).den * ∏ l ∈ Finset.univ.erase k, (a l).den : ℕ) : ℚ) := by
        rw [hprod_split]
      _ = a k * (((a k).den : ℚ) * ((∏ l ∈ Finset.univ.erase k, (a l).den : ℕ) : ℚ)) := by
        push_cast
        ring
      _ = (a k * ((a k).den : ℚ)) * ((∏ l ∈ Finset.univ.erase k, (a l).den : ℕ) : ℚ) := by ring
      _ = ((a k).num : ℚ) * ((∏ l ∈ Finset.univ.erase k, (a l).den : ℕ) : ℚ) := by
        rw [Rat.mul_den_eq_num (a k)]
      _ = ((a k).num * ∏ l ∈ Finset.univ.erase k, (a l).den : ℤ) := by
        push_cast
        ring
      _ = (z : ℚ) := by simp [hz]
  · -- z.natAbs ≤ M ^ d
    rw [hz]
    rw [Int.natAbs_mul]
    rcases ha k with ⟨hnum, hden⟩
    have hprod : (∏ l ∈ Finset.univ.erase k, (a l).den) ≤ M ^ (d - 1) := by
      calc
        (∏ l ∈ Finset.univ.erase k, (a l).den) ≤ ∏ l ∈ Finset.univ.erase k, M := by
          refine Finset.prod_le_prod ?_
          intro l hl
          rcases ha l with ⟨_, hden'⟩
          exact hden'
        _ = M ^ (Finset.card (Finset.univ.erase k)) := by simp
        _ = M ^ (d - 1) := by
          simp [Finset.card_erase_of_mem (Finset.mem_univ k), Fintype.card_fin]
    have hdpos : 0 < d := by
      have : Nonempty (Fin d) := ⟨k⟩
      have hcard := Fintype.card_pos (α := Fin d)
      rw [Fintype.card_fin] at hcard
      exact hcard
    calc
      ((a k).num.natAbs : ℕ) * (∏ l ∈ Finset.univ.erase k, (a l).den) ≤ M * (∏ l ∈ Finset.univ.erase k, (a l).den) := by
        exact Nat.mul_le_mul hnum (by rfl)
      _ ≤ M * (M ^ (d - 1)) := Nat.mul_le_mul_left M hprod
      _ = M ^ (d - 1) * M := by rw [mul_comm]
      _ = M ^ ((d - 1) + 1) := by rw [Nat.pow_succ]
      _ = M ^ d := by rw [Nat.sub_add_cancel hdpos]

theorem prod_den_le {d M : ℕ} (a : Fin d → ℚ) (ha : ∀ k, (a k).den ≤ M) : ∏ k, (a k).den ≤ M ^ d := by
  refine (Finset.prod_le_pow_card (Finset.univ : Finset (Fin d)) (fun k => (a k).den) M ?_).trans ?_
  · intro k hk
    exact ha k
  · simp

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

theorem callSz_exps (d E s Ms : ℕ) :
    (d + E + Ms * d) + d * (E + Ms * d) + (2 * E + Ms * (d + 1)) ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧
    (d + 1 + 2 * E + Ms * (d + 1)) + d * (E + Ms * d) + (2 * E + Ms * (d + 1)) ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧
    s + s * (d * d + d + 1) ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧ s + s * (d * d) ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧
    s + s * d + s * (d * d) ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧ s * d ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧
    s ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) ∧ s * (d * d) + s ≤ 4 * (d + 1) ^ 2 * (E + s + Ms + 1) := by
  ring_nf; omega

theorem colDot_bound {d M E Ms : ℕ} (S2 : Matrix (Fin d) (Fin d) ℚ)
    (a : Fin d → ℚ) (DS : ℤ) (x : Fin d → Fin d → ℤ) (hDS : 0 < DS) (bD : DS ≤ 2 ^ E)
    (hx : ∀ k j, (x k j : ℚ) / DS = S2 k j) (bx : ∀ k j, |x k j| ≤ 2 ^ E)
    (ha : ∀ k, (a k).num.natAbs ≤ M ∧ (a k).den ≤ M) (hM : M ≤ 2 ^ Ms) (j : Fin d) :
    ∃ (D : ℕ) (z : ℤ), 0 < D ∧ D ≤ 2 ^ (E + Ms * d) ∧ (S2ᵀ *ᵥ a) j * D = z ∧ |z| ≤ 2 ^ (d + E + Ms * d) := by
  choose w hw bw using fun k => row_scale a ha k
  have hMd : M ^ d ≤ 2 ^ (Ms * d) := by rw [pow_mul]; exact Nat.pow_le_pow_left hM d
  have bwz : ∀ k, |w k| ≤ 2 ^ (Ms * d) := fun k => by
    rw [← Int.natCast_natAbs]; exact_mod_cast (bw k).trans hMd
  have hq0 : 0 < ∏ l, (a l).den := Finset.prod_pos fun l _ => (a l).den_pos
  have hqM : ∏ l, (a l).den ≤ 2 ^ (Ms * d) := (prod_den_le a fun k => (ha k).2).trans hMd
  have hDSn : ((DS.toNat : ℕ) : ℚ) = (DS : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hDS.le
  have hDS0 : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  refine ⟨DS.toNat * ∏ l, (a l).den, ∑ k, x k j * w k, Nat.mul_pos (by omega) hq0, ?_, ?_, ?_⟩
  · rw [pow_add]; exact Nat.mul_le_mul (Int.toNat_le.mpr (by push_cast; exact bD)) hqM
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Nat.cast_mul, hDSn, Finset.sum_mul,
      Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hx k j, ← hw k]
    field_simp
  · calc |∑ k, x k j * w k| ≤ ∑ k, |x k j * w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, 2 ^ E * 2 ^ (Ms * d) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul (bx k j) (bwz k) (abs_nonneg _) (by positivity)
      _ = d * (2 ^ E * 2 ^ (Ms * d)) := by simp
      _ ≤ 2 ^ d * (2 ^ E * 2 ^ (Ms * d)) := by
          gcongr; exact_mod_cast (Nat.lt_two_pow_self).le
      _ = 2 ^ (d + E + Ms * d) := by rw [pow_add, pow_add]; ring

theorem beta_bound {d M E Ms pF : ℕ} (a : Fin d → ℚ) (bb : ℚ) (mu : Fin d → ℚ)
    (eps : ℚ) (DS : ℤ) (y : Fin d → ℤ) (e1 : ℤ) (hDS : 0 < DS) (bD : DS ≤ 2 ^ E)
    (hy : ∀ j, (y j : ℚ) / DS = mu j) (bY : ∀ j, |y j| ≤ 2 ^ E)
    (ha : ∀ k, (a k).num.natAbs ≤ M ∧ (a k).den ≤ M) (hb : bb.num.natAbs ≤ M ∧ bb.den ≤ M) (hM : M ≤ 2 ^ Ms)
    (he : (1 - eps) * 2 ^ pF = e1) (be : |e1| ≤ 2 ^ pF) (hpF : pF ≤ E) :
    ∃ (D : ℕ) (z : ℤ), 0 < D ∧ D ≤ 2 ^ (2 * E + Ms * (d + 1)) ∧ ((1 - eps) * (bb - a ⬝ᵥ mu)) * D = z ∧
      |z| ≤ 2 ^ (d + 1 + 2 * E + Ms * (d + 1)) := by
  choose w hw bw using fun k => row_scale a ha k
  set q := ∏ l, (a l).den with hq
  have hMd : M ^ d ≤ 2 ^ (Ms * d) := by rw [pow_mul]; exact Nat.pow_le_pow_left hM d
  have bwz : ∀ k, |w k| ≤ 2 ^ (Ms * d) := fun k => by
    rw [← Int.natCast_natAbs]; exact_mod_cast (bw k).trans hMd
  have hq0 : 0 < q := Finset.prod_pos fun l _ => (a l).den_pos
  have hqM : q ≤ 2 ^ (Ms * d) := (prod_den_le a fun k => (ha k).2).trans hMd
  have hDSn : ((DS.toNat : ℕ) : ℚ) = (DS : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hDS.le
  have hDS0 : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have hDSt : DS.toNat ≤ 2 ^ E := Int.toNat_le.mpr (by push_cast; exact bD)
  have hpE : 2 ^ pF ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hpF
  have hbM : bb.den ≤ 2 ^ Ms := hb.2.trans hM
  refine ⟨2 ^ pF * DS.toNat * q * bb.den, e1 * (DS * (q : ℤ) * bb.num - (bb.den : ℤ) * ∑ k, w k * y k),
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) hq0) bb.den_pos, ?_, ?_, ?_⟩
  · calc 2 ^ pF * DS.toNat * q * bb.den ≤ 2 ^ E * 2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hpE hDSt) hqM) hbM
      _ = 2 ^ (2 * E + Ms * (d + 1)) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  · have hnum : (bb.num : ℚ) = bb * bb.den := (Rat.mul_den_eq_num bb).symm
    have hwy : ∀ k, (w k : ℚ) * y k = a k * mu k * (q * DS) := fun k => by
      rw [← hw k, ← hy k]; field_simp
    simp only [dotProduct, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hDSn, Int.cast_mul, Int.cast_sub,
      Int.cast_sum, Int.cast_natCast, ← he, hnum, hwy, ← Finset.sum_mul]
    ring
  · have hq' : |(q : ℤ)| ≤ 2 ^ (Ms * d) := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hqM
    have hn' : |bb.num| ≤ 2 ^ Ms := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hb.1.trans hM
    have hd' : |(bb.den : ℤ)| ≤ 2 ^ Ms := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hbM
    have hD' : |DS| ≤ 2 ^ E := by rw [abs_of_pos hDS]; exact bD
    have h1 : |DS * (q : ℤ) * bb.num| ≤ 2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hD' hq' (abs_nonneg _) (by positivity)) hn' (abs_nonneg _) (by positivity)
    have hs : |∑ k, w k * y k| ≤ d * (2 ^ (Ms * d) * 2 ^ E) := by
      calc |∑ k, w k * y k| ≤ ∑ k, |w k * y k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin d, 2 ^ (Ms * d) * 2 ^ E := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]; exact mul_le_mul (bwz k) (bY k) (abs_nonneg _) (by positivity)
        _ = d * (2 ^ (Ms * d) * 2 ^ E) := by simp
    have h2 : |(bb.den : ℤ) * ∑ k, w k * y k| ≤ 2 ^ Ms * (d * (2 ^ (Ms * d) * 2 ^ E)) := by
      rw [abs_mul]; exact mul_le_mul hd' hs (abs_nonneg _) (by positivity)
    have hd2 : ((d : ℤ) + 1) ≤ 2 ^ (d + 1) := by
      have := Nat.lt_two_pow_self (n := d + 1); exact_mod_cast this.le.trans' (by omega)
    have h3 : |DS * (q : ℤ) * bb.num - (bb.den : ℤ) * ∑ k, w k * y k| ≤
        2 ^ (d + 1) * (2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms) := by
      calc _ ≤ |DS * (q : ℤ) * bb.num| + |(bb.den : ℤ) * ∑ k, w k * y k| := abs_sub _ _
        _ ≤ 2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms + 2 ^ Ms * (d * (2 ^ (Ms * d) * 2 ^ E)) := add_le_add h1 h2
        _ = ((d : ℤ) + 1) * (2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hd2 (by positivity)
    have he' : |e1| ≤ 2 ^ E := be.trans (pow_le_pow_right₀ (by norm_num) hpF)
    calc |e1 * (DS * (q : ℤ) * bb.num - (bb.den : ℤ) * ∑ k, w k * y k)| ≤
          2 ^ E * (2 ^ (d + 1) * (2 ^ E * 2 ^ (Ms * d) * 2 ^ Ms)) := by
          rw [abs_mul]; exact mul_le_mul he' h3 (abs_nonneg _) (by positivity)
      _ = 2 ^ (d + 1 + 2 * E + Ms * (d + 1)) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; ring_nf

theorem clr_row_bound {d Da Db Ta Tb : ℕ} (α : Fin d → ℚ) (β : ℚ)
    (hDa : ∀ j, (α j).den ≤ 2 ^ Da) (hDb : β.den ≤ 2 ^ Db) (hTa : ∀ j, |α j| ≤ 2 ^ Ta) (hTb : |β| ≤ 2 ^ Tb) :
    (∏ j, (α j).den) * β.den ≤ 2 ^ (d * Da + Db) ∧
      (∀ j, ((α j).num * ((((∏ j, (α j).den) * β.den) / (α j).den : ℕ) : ℤ)).natAbs ≤ 2 ^ (Ta + (d * Da + Db))) ∧
      (β.num * ((((∏ j, (α j).den) * β.den) / β.den : ℕ) : ℤ)).natAbs ≤ 2 ^ (Tb + (d * Da + Db)) := by
  let R := (∏ j, (α j).den) * β.den
  have hR_le : R ≤ 2 ^ (d * Da + Db) := by
    have hprod : ∏ j, (α j).den ≤ (2 ^ Da) ^ d := prod_den_le α hDa
    calc
      R = (∏ j, (α j).den) * β.den := rfl
      _ ≤ (2 ^ Da) ^ d * 2 ^ Db := Nat.mul_le_mul hprod hDb
      _ = 2 ^ (Da * d) * 2 ^ Db := by rw [pow_mul]
      _ = 2 ^ (Da * d + Db) := by rw [pow_add]
      _ = 2 ^ (d * Da + Db) := by rw [mul_comm Da d]
  have h_den_dvd (j : Fin d) : (α j).den ∣ R := by
    dsimp [R]
    have h := Finset.dvd_prod_of_mem (λ l => (α l).den) (Finset.mem_univ j)
    exact h.mul_right β.den
  have h_den_dvd_β : β.den ∣ R := by
    dsimp [R]
    exact ⟨∏ j, (α j).den, by ring⟩
  have h_clr (j : Fin d) : ((α j).num * ((R / (α j).den : ℕ) : ℤ)).natAbs ≤ 2 ^ (Ta + (d * Da + Db)) := by
    apply clr_bound (α j) (h_den_dvd j) hR_le (hTa j)
  have h_clr_β : (β.num * ((R / β.den : ℕ) : ℤ)).natAbs ≤ 2 ^ (Tb + (d * Da + Db)) := by
    apply clr_bound β h_den_dvd_β hR_le hTb
  exact And.intro hR_le (And.intro h_clr h_clr_β)

/-- A bounded rational `x = z / D` with `D ≤ 2^a` and `|z| ≤ 2^t`: its denominator is at most `2^a`, its absolute
value at most `2^t`. -/
theorem den_abs_of {x : ℚ} {a t : ℕ} (h : ∃ (D : ℕ) (z : ℤ), 0 < D ∧ D ≤ 2 ^ a ∧ x * D = z ∧ |z| ≤ 2 ^ t) :
    x.den ≤ 2 ^ a ∧ |x| ≤ 2 ^ t := by
  obtain ⟨D, z, hD, hDa, hx, hz⟩ := h
  obtain ⟨h1, -, h3⟩ := den_num_le_of_mul x D z hD hx
  exact ⟨h1.trans hDa, h3.trans (by exact_mod_cast hz)⟩

/-- The denominators of a matrix, at most `2^s` each: their product is at most `2^(s d²)`. -/
theorem prod_den_mat {d s : ℕ} (X : Matrix (Fin d) (Fin d) ℚ) (h : ∀ i j, (X i j).den ≤ 2 ^ s) :
    ∏ i, ∏ j, (X i j).den ≤ 2 ^ (s * (d * d)) := by
  calc ∏ i, ∏ j, (X i j).den ≤ ∏ _i : Fin d, 2 ^ (s * d) :=
        Finset.prod_le_prod fun i _ => by
          simpa [Fintype.card_fin] using prod_den_le_pow (X i) (h i)
    _ = 2 ^ (s * (d * d)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring_nf

end AdversarialBco.Bit.Transfer.CallSz

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.Bit.Transfer.CallSz

variable {d : ℕ}

/-- The bit bound of a cleared call of BL. -/
def callSzB (d E s Ms : ℕ) : ℕ := 4 * (d + 1) ^ 2 * (E + s + Ms + 1) + 1

/-- The largest integer of a problem against per-entry bounds. -/
theorem ellMx_le_of {I : EllI d} {T : ℕ} (hα : ∀ i j, (I.α i j).natAbs ≤ 2 ^ T) (hβ : ∀ i, (I.β i).natAbs ≤ 2 ^ T)
    (hH : ∀ i j, (I.H i j).natAbs ≤ 2 ^ T) (hP : ∀ i j, (I.P i j).natAbs ≤ 2 ^ T)
    (hg : ∀ j, (I.g j).natAbs ≤ 2 ^ T) (hf : ∀ j, (I.f j).natAbs ≤ 2 ^ T) (hl : I.ℓ.natAbs ≤ 2 ^ T)
    (hD : I.Df ≤ 2 ^ T) (hR : I.R.num.natAbs ≤ 2 ^ T ∧ I.R.den ≤ 2 ^ T)
    (hr : I.r.num.natAbs ≤ 2 ^ T ∧ I.r.den ≤ 2 ^ T) (he : I.e.num.natAbs ≤ 2 ^ T ∧ I.e.den ≤ 2 ^ T) :
    ellMx I ≤ 2 ^ T := by
  unfold ellMx
  simp only [max_le_iff, Finset.sup_le_iff, Finset.mem_univ, forall_const]
  exact ⟨fun i => ⟨fun j => hα i j, hβ i⟩, fun i j => ⟨hH i j, hP i j⟩, fun j => ⟨hg j, hf j⟩, hl, hD,
    hR, hr, he⟩

set_option maxHeartbeats 1000000 in
/-- **The bit length of a cleared call of BL** is at most `callSzB d E s (size M)`. -/
theorem ellSz_call {L : Layout} {n m M E s : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ}
    {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {H : Matrix (Fin d) (Fin d) ℚ} {g : Fin d → ℚ} {ℓq r : ℚ}
    {P : Matrix (Fin d) (Fin d) ℚ} {f : Fin d → ℚ} {e : ℚ} {σ : Env d}
    (hM : RealRAM.HeightLE A b M) (hOn : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1) (hC : RowCtx L m E (mkCfg d n m A b c S) σ)
    (hI : PrepIn σ (mkCfg d n m A b c S) s H g ℓq r P f e) :
    ellSz (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)) ≤ callSzB d E s M.size := by
  have hMs : M ≤ 2 ^ M.size := (Nat.lt_size_self M).le
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := callSz_exps d E s M.size
  -- the position
  have h2pF : σ.sc s2pF = 2 ^ (par d n).pF := hC.consts.2.1
  obtain ⟨DS, hDS, eDS, hmu, hAS⟩ := hC.pos
  obtain ⟨bS, bA⟩ := hC.bnd
  obtain ⟨z1, ez1, bz1⟩ := bS s2pF (by simp)
  obtain ⟨z3, ez3, bz3⟩ := bS sDS (by simp)
  have hpF : (par d n).pF ≤ E := by
    have e1 : z1 = 2 ^ (par d n).pF := by exact_mod_cast ez1.symm.trans h2pF
    rw [e1, abs_of_pos (by positivity)] at bz1
    by_contra hc
    have : (2 : ℤ) ^ E < 2 ^ (par d n).pF := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have bD : DS ≤ 2 ^ E := by
    have : DS = z3 := by exact_mod_cast eDS.symm.trans ez3
    rw [this]; exact (le_abs_self _).trans bz3
  have hidx : ∀ i j : Fin d, d * (i : ℕ) + j < asz d := fun i j => by
    unfold asz; nlinarith [i.2, j.2]
  choose xA hxA using hAS
  choose yM hyM using hmu
  have bxA : ∀ k j, |xA k j| ≤ 2 ^ E := fun k j => by
    obtain ⟨z, ez, bz⟩ := bA aAS (by simp) _ (hidx k j)
    have : xA k j = z := by exact_mod_cast (hxA k j).1.symm.trans ez
    rw [this]; exact bz
  have byM : ∀ j, |yM j| ≤ 2 ^ E := fun j => by
    obtain ⟨z, ez, bz⟩ := bA aMuS (by simp) j (by unfold asz; nlinarith [j.2])
    have : yM j = z := by exact_mod_cast (hyM j).1.symm.trans ez
    rw [this]; exact bz
  -- `ε'`
  have he : (1 - (par d n).eps) * 2 ^ (par d n).pF =
      ((2 ^ (par d n).pF - qn (par d n).pF (par d n).eps : ℤ) : ℚ) := by
    unfold OnG at hOn
    push_cast; rw [hOn]; ring
  have be : |(2 ^ (par d n).pF - qn (par d n).pF (par d n).eps : ℤ)| ≤ 2 ^ (par d n).pF := by
    have h0 : (0 : ℚ) ≤ ((2 ^ (par d n).pF - qn (par d n).pF (par d n).eps : ℤ) : ℚ) := by
      rw [← he]; exact mul_nonneg (by linarith) (by positivity)
    have h1 : ((2 ^ (par d n).pF - qn (par d n).pF (par d n).eps : ℤ) : ℚ) ≤ 2 ^ (par d n).pF := by
      rw [← he]; nlinarith [pow_pos (two_pos : (0 : ℚ) < 2) (par d n).pF]
    have h0' : (0 : ℤ) ≤ 2 ^ (par d n).pF - qn (par d n).pF (par d n).eps := by exact_mod_cast h0
    have h1' : 2 ^ (par d n).pF - qn (par d n).pF (par d n).eps ≤ (2 : ℤ) ^ (par d n).pF := by exact_mod_cast h1
    exact abs_le.mpr ⟨by linarith, h1'⟩
  -- the call data
  obtain ⟨-, -, -, -, -, hRs, pH0, pg0, pP0, pf0, pl0, pr0, pe0⟩ := hI
  have pH : ∀ i j, (H i j).den ≤ 2 ^ s ∧ (H i j).num.natAbs ≤ 2 ^ s ∧ |H i j| ≤ 2 ^ s := fun i j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pH0 i j
    exact pair_bound u v _ hv hu hvs huv
  have pP : ∀ i j, (P i j).den ≤ 2 ^ s ∧ (P i j).num.natAbs ≤ 2 ^ s ∧ |P i j| ≤ 2 ^ s := fun i j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pP0 i j
    exact pair_bound u v _ hv hu hvs huv
  have pg : ∀ j, (g j).den ≤ 2 ^ s ∧ (g j).num.natAbs ≤ 2 ^ s ∧ |g j| ≤ 2 ^ s := fun j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pg0 j
    exact pair_bound u v _ hv hu hvs huv
  have pf : ∀ j, (f j).den ≤ 2 ^ s ∧ (f j).num.natAbs ≤ 2 ^ s ∧ |f j| ≤ 2 ^ s := fun j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pf0 j
    exact pair_bound u v _ hv hu hvs huv
  have pl : ℓq.den ≤ 2 ^ s ∧ ℓq.num.natAbs ≤ 2 ^ s ∧ |ℓq| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pl0
    exact pair_bound u v _ hv hu hvs huv
  have pr : r.den ≤ 2 ^ s ∧ r.num.natAbs ≤ 2 ^ s ∧ |r| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pr0
    exact pair_bound u v _ hv hu hvs huv
  have pe : e.den ≤ 2 ^ s ∧ e.num.natAbs ≤ 2 ^ s ∧ |e| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pe0
    exact pair_bound u v _ hv hu hvs huv
  have hgd : ∏ j, (g j).den ≤ 2 ^ (s * d) := by
    simpa [Fintype.card_fin] using prod_den_le_pow g (fun j => (pg j).1)
  have hfd : ∏ j, (f j).den ≤ 2 ^ (s * d) := by
    simpa [Fintype.card_fin] using prod_den_le_pow f (fun j => (pf j).1)
  have hPd : ∏ i, ∏ j, (P i j).den ≤ 2 ^ (s * (d * d)) := prod_den_mat P fun i j => (pP i j).1
  have hQ : (∏ i, ∏ j, (H i j).den) * (∏ j, (g j).den) * ℓq.den ≤ 2 ^ (s * (d * d + d + 1)) := by
    calc _ ≤ 2 ^ (s * (d * d)) * 2 ^ (s * d) * 2 ^ s :=
          Nat.mul_le_mul (Nat.mul_le_mul (prod_den_mat H fun i j => (pH i j).1) hgd) pl.1
      _ = _ := by rw [← pow_add, ← pow_add]; ring_nf
  have pw : ∀ {a : ℕ}, a ≤ 4 * (d + 1) ^ 2 * (E + s + M.size + 1) →
      2 ^ a ≤ 2 ^ (4 * (d + 1) ^ 2 * (E + s + M.size + 1)) := fun h => Nat.pow_le_pow_right (by norm_num) h
  unfold ellSz callSzB
  refine Nat.size_le.mpr (lt_of_le_of_lt (ellMx_le_of (T := 4 * (d + 1) ^ 2 * (E + s + M.size + 1))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  · -- the rows `α`
    intro i j
    have hα' := fun j => den_abs_of (colDot_bound S.2 (A ((keptIdx A).get i)) DS xA hDS bD
      (fun k j => (hxA k j).2) bxA (hM.1 _) hMs j)
    have hβ' := den_abs_of (beta_bound (A ((keptIdx A).get i)) (b ((keptIdx A).get i)) S.1 (par d n).eps DS yM _
      hDS bD (fun j => (hyM j).2) byM (hM.1 _) (hM.2 _) hMs he be hpF)
    obtain ⟨-, hA, -⟩ := clr_row_bound _ _ (fun j => (hα' j).1) hβ'.1 (fun j => (hα' j).2) hβ'.2
    exact (hA j).trans (pw (by omega))
  · -- the rows `β`
    intro i
    have hα' := fun j => den_abs_of (colDot_bound S.2 (A ((keptIdx A).get i)) DS xA hDS bD
      (fun k j => (hxA k j).2) bxA (hM.1 _) hMs j)
    have hβ' := den_abs_of (beta_bound (A ((keptIdx A).get i)) (b ((keptIdx A).get i)) S.1 (par d n).eps DS yM _
      hDS bD (fun j => (hyM j).2) byM (hM.1 _) (hM.2 _) hMs he be hpF)
    obtain ⟨-, -, hB⟩ := clr_row_bound _ _ (fun j => (hα' j).1) hβ'.1 (fun j => (hα' j).2) hβ'.2
    exact hB.trans (pw (by omega))
  · -- `H`
    intro i j
    refine (clr_bound (H i j) ?_ hQ (pH i j).2.2).trans (pw (by omega))
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((Finset.dvd_prod_of_mem (fun j => (H i j).den)
      (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (H i j).den) (Finset.mem_univ i))) _) _
  · -- `P`
    intro i j
    refine (clr_bound (P i j) ?_ hPd (pP i j).2.2).trans (pw (by omega))
    exact (Finset.dvd_prod_of_mem (fun j => (P i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (P i j).den) (Finset.mem_univ i))
  · -- `g`
    intro j
    refine (clr_bound (g j) ?_ hQ (pg j).2.2).trans (pw (by omega))
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun j => (g j).den) (Finset.mem_univ j)) _) _
  · -- `f`
    intro j
    have h1 := clr_bound (f j) (Finset.dvd_prod_of_mem (fun j => (f j).den) (Finset.mem_univ j)) hfd (pf j).2.2
    show (clr (linDen (callOf (mkCfg d n m A b c S) H g ℓq r P f e)) (f j) *
      (objDen (callOf (mkCfg d n m A b c S) H g ℓq r P f e) : ℤ)).natAbs ≤ _
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    refine (Nat.mul_le_mul h1 hPd).trans ?_
    rw [← pow_add]; exact pw (by omega)
  · -- `ℓ`
    exact (clr_bound ℓq (dvd_mul_left _ _) hQ pl.2.2).trans (pw (by omega))
  · -- `D_f`
    exact hfd.trans (pw (by omega))
  · -- `R`
    show ((par d n).Rint : ℚ).num.natAbs ≤ _ ∧ ((par d n).Rint : ℚ).den ≤ _
    rw [Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
    have : (par d n).Rint ≤ 2 ^ s := by exact_mod_cast hRs
    exact ⟨this.trans (pw (by omega)), Nat.one_le_two_pow⟩
  · -- `r`
    exact ⟨pr.2.1.trans (pw (by omega)), pr.1.trans (pw (by omega))⟩
  · -- `e`
    obtain ⟨h1, h2⟩ := natmul_bound _ e hPd pe.1 pe.2.1
    exact ⟨h1.trans (pw (by omega)), h2.trans (pw (by omega))⟩

end AdversarialBco.Bit.Transfer.BLM
