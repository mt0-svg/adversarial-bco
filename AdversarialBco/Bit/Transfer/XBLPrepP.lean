/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowP

@[expose] public section

/-!
# Pure lemmas of the call preparation

`objDen_range`: `D_P` from integers equal to the denominators of `P`; `e_numden`: the reduced form of `D_P e`.
-/

/-- `D_P` (the product of the denominators of `P`) from integers equal to them, in the cells `d i + j`. -/
theorem AdversarialBco.Bit.Transfer.RowP.objDen_range {d : ℕ} (P : Matrix (Fin d) (Fin d) ℚ) (yP : ℕ → ℤ)
    (hP : ∀ i j : Fin d, ((P i j).den : ℤ) = yP (d * i + j)) :
    ((∏ i, ∏ j, (P i j).den : ℕ) : ℤ) = ∏ k ∈ Finset.range (d * d), yP k := by
  simp only [Nat.cast_prod, hP]
  have h := (Fintype.prod_prod_type (λ (x : Fin d × Fin d) => yP (d * (x.1 : ℕ) + (x.2 : ℕ)))).symm
  simp at h
  rw [h]
  rw [Fintype.prod_equiv finProdFinEquiv (λ x => yP (d * (x.1 : ℕ) + (x.2 : ℕ))) (λ k => yP (k : ℕ)) ?_]
  · rw [Fin.prod_univ_eq_prod_range]
  · intro x
    simp [finProdFinEquiv_apply_val, add_comm]

/-- The reduced form of `D_P e` with `e = u / v`, `v > 0`, `D_P > 0`. -/
theorem AdversarialBco.Bit.Transfer.RowP.e_numden (DP : ℕ) (_hDP : 0 < DP) (e : ℚ) (u v : ℤ) (hv : 0 < v)
    (he : (u : ℚ) / v = e) :
    ((DP : ℚ) * e).num = (DP * u) / (Int.gcd (DP * u) v : ℤ) ∧
      ((((DP : ℚ) * e).den : ℕ) : ℤ) = v / (Int.gcd (DP * u) v : ℤ) := by
  have hv_nonneg : 0 ≤ v := by linarith
  have hv_nat_pos : Int.toNat v ≠ 0 := by
    intro hzero
    have hzero' : (Int.toNat v : ℤ) = 0 := by exact_mod_cast hzero
    have hv_eq_zero : v = 0 := by
      rw [← Int.toNat_of_nonneg hv_nonneg, hzero']
    linarith
  have h_mkrat : (DP : ℚ) * e = mkRat (DP * u) (Int.toNat v) := by
    calc
      (DP : ℚ) * e = (DP : ℚ) * ((u : ℚ) / (v : ℚ)) := by rw [← he]
      _ = ((DP : ℚ) * (u : ℚ)) / (v : ℚ) := by ring
      _ = ((DP * u : ℤ) : ℚ) / (v : ℚ) := by push_cast; ring
      _ = ((DP * u : ℤ) : ℚ) / ((Int.toNat v : ℕ) : ℚ) := by
        have hcast : (Int.toNat v : ℚ) = (v : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
        rw [hcast]
      _ = mkRat (DP * u) (Int.toNat v) := by rw [← Rat.mkRat_eq_div]
  have h_natAbs_eq : v.natAbs = Int.toNat v := by
    have h1 : (v.natAbs : ℤ) = v := Int.natAbs_of_nonneg hv_nonneg
    have h2 : (Int.toNat v : ℤ) = v := Int.toNat_of_nonneg hv_nonneg
    have h3 : (v.natAbs : ℤ) = (Int.toNat v : ℤ) := by rw [h1, h2]
    exact_mod_cast h3
  have h_gcd_eq : Int.gcd (DP * u) v = Nat.gcd ((DP * u).natAbs) (Int.toNat v) := by
    rw [Int.gcd_eq_natAbs]
    rw [h_natAbs_eq]
  have h_num : ((DP : ℚ) * e).num = (DP * u) / (Int.gcd (DP * u) v : ℤ) := by
    rw [h_mkrat]
    rw [Rat.num_mkRat]
    simp only [hv_nat_pos, ↓reduceIte]
    rw [h_gcd_eq]
    simp [Nat.gcd_comm]
  have h_den : (((DP : ℚ) * e).den : ℤ) = v / (Int.gcd (DP * u) v : ℤ) := by
    rw [h_mkrat]
    rw [Rat.den_mkRat]
    simp only [hv_nat_pos, ↓reduceIte]
    push_cast
    rw [h_gcd_eq]
    rw [Int.toNat_of_nonneg hv_nonneg]
    simp [Nat.gcd_comm]
  exact And.intro h_num h_den
