/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The row provider of BL, part 0: pure facts

* `num_den_of_div`, `red_bounds`: the reduced form of `N / D` by the gcd, and its bounds; `clr_out`.
* The ranges and the magnitudes of the integers of a row: `cells_mat`, `quadDen_range`, `scale_bound`.
-/

open Matrix

/-- The reduced form of `N / D`, `D > 0`: numerator `N / gcd(N, D)`, denominator `D / gcd(N, D)`. -/
theorem AdversarialBco.Bit.Transfer.RowP.num_den_of_div (N D : ℤ) (hD : 0 < D) (x : ℚ) (hx : x = (N : ℚ) / D) :
    x.num = N / (Int.gcd N D : ℤ) ∧ (x.den : ℤ) = D / (Int.gcd N D : ℤ) := by
  have hD_nonneg : 0 ≤ D := le_of_lt hD
  have hD_ne_zero : D ≠ 0 := by linarith
  have hD_toNat_ne_zero : D.toNat ≠ 0 := by
    intro h
    have hle : D ≤ 0 := (Int.toNat_eq_zero.mp h)
    linarith
  have hD_eq_toNat : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hD_nonneg
  have hx_mkRat : x = mkRat N D.toNat := by
    rw [hx]
    calc
      (N : ℚ) / D = (N : ℚ) / ((D.toNat : ℤ) : ℚ) := by simp [hD_eq_toNat]
      _ = (N : ℚ) / (D.toNat : ℚ) := by norm_cast
      _ = mkRat N D.toNat := (Rat.mkRat_eq_div N D.toNat).symm
  have h_natAbs_eq_toNat : D.natAbs = D.toNat := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hD_nonneg, hD_eq_toNat]
  have h_gcd_eq : (D.toNat.gcd N.natAbs : ℤ) = (Int.gcd N D : ℤ) := by
    rw [Int.gcd_eq_natAbs, h_natAbs_eq_toNat, Nat.gcd_comm]
  have h_num : x.num = N / (Int.gcd N D : ℤ) := by
    rw [hx_mkRat, Rat.num_mkRat N D.toNat]
    rw [ite_eq_right hD_toNat_ne_zero]
    rw [h_gcd_eq]
  have h_den : (x.den : ℤ) = D / (Int.gcd N D : ℤ) := by
    rw [hx_mkRat, Rat.den_mkRat N D.toNat]
    rw [ite_eq_right hD_toNat_ne_zero]
    rw [Int.natCast_div, hD_eq_toNat]
    rw [h_gcd_eq]
  exact And.intro h_num h_den

/-- The reduced numerator and denominator of `N / D`, `D > 0`, by the gcd: `|N / g| ≤ |N|`, `1 ≤ D / g ≤ D`,
`g ≥ 1`. -/
theorem AdversarialBco.Bit.Transfer.RowP.red_bounds (N D : ℤ) (hD : 0 < D) :
    1 ≤ (Int.gcd N D : ℤ) ∧ |N / (Int.gcd N D : ℤ)| ≤ |N| ∧ 1 ≤ D / (Int.gcd N D : ℤ) ∧
      D / (Int.gcd N D : ℤ) ≤ D := by
  set g := (Int.gcd N D : ℤ) with hg
  have hg_pos : 0 < g := by
    have hgcd_pos : 0 < Int.gcd N D := Int.gcd_pos_of_ne_zero_right N hD.ne'
    exact Nat.cast_pos.mpr hgcd_pos
  have hg_dvd_D : g ∣ D := GCDMonoid.gcd_dvd_right N D
  have hg_le_D : g ≤ D := by
    have := (Int.le_iff_pos_of_dvd hg_pos hg_dvd_D).mpr hD
    exact this
  have h1 : 1 ≤ g := by omega
  have h2 : |N / g| ≤ |N| := Int.abs_ediv_le_abs N g
  have h3 : 1 ≤ D / g := by
    rw [Int.le_div_iff_of_dvd_of_pos hg_pos hg_dvd_D]
    simpa using hg_le_D
  have h4 : D / g ≤ D := Int.ediv_le_self g hD.le
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))

/-- The cleared entry `num(x) (R / den(x))` from integers equal to the numerator and the denominator. -/
theorem AdversarialBco.Bit.Transfer.RowP.clr_out (R : ℕ) (x : ℚ) (nu de : ℤ) (hn : x.num = nu) (hd : (x.den : ℤ) = de) :
    x.num * ((R / x.den : ℕ) : ℤ) = nu * ((R : ℤ) / de) := by
  calc
    x.num * ((R / x.den : ℕ) : ℤ) = x.num * ((R : ℤ) / (x.den : ℤ)) := by
      rw [Int.natCast_div]
    _ = nu * ((R : ℤ) / (x.den : ℤ)) := by rw [hn]
    _ = nu * ((R : ℤ) / de) := by rw [hd]

/-- A property of the cells `d i + j`, `i j : Fin d`, is a property of the cells `k < d d`, and back. -/
theorem AdversarialBco.Bit.Transfer.RowP.cells_mat {d : ℕ} (p : ℕ → Prop) :
    (∀ i j : Fin d, p (d * i + j)) ↔ ∀ k < d * d, p k := by
  constructor
  · intro h k hk
    have hdpos : 0 < d := by
      by_contra! hd
      have hd0 : d = 0 := by omega
      have : k < 0 := by simpa [hd0, mul_zero] using hk
      exact Nat.not_lt_zero _ this
    have hdiv : k / d < d := by
      rw [Nat.div_lt_iff_lt_mul hdpos]
      exact hk
    have hmod : k % d < d := Nat.mod_lt _ hdpos
    have hcell := h ⟨k / d, hdiv⟩ ⟨k % d, hmod⟩
    simpa [mul_comm, Nat.div_add_mod k d] using hcell
  · intro h i j
    apply h
    have hi : (i : ℕ) < d := i.2
    have hj : (j : ℕ) < d := j.2
    nlinarith

/-- `D_H` (the product of the denominators of `H`, `g`, `ℓ`) from integers equal to the denominators, `H` in the
cells `d i + j`. -/
theorem AdversarialBco.Bit.Transfer.RowP.quadDen_range {d : ℕ} (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ : ℚ) (yH yg : ℕ → ℤ) (yl : ℤ)
    (hH : ∀ i j : Fin d, ((H i j).den : ℤ) = yH (d * i + j)) (hg : ∀ j : Fin d, ((g j).den : ℤ) = yg j)
    (hl : (ℓ.den : ℤ) = yl) :
    (((∏ i, ∏ j, (H i j).den) * (∏ j, (g j).den) * ℓ.den : ℕ) : ℤ) =
      (∏ k ∈ Finset.range (d * d), yH k) * (∏ j ∈ Finset.range d, yg j) * yl := by
  push_cast
  calc
    ((∏ i : Fin d, ∏ j : Fin d, ((H i j).den : ℤ)) * (∏ j : Fin d, ((g j).den : ℤ)) * ((ℓ.den : ℤ)))
        = ((∏ i : Fin d, ∏ j : Fin d, yH (d * i + j)) * (∏ j : Fin d, yg j) * yl) := by
      simp [hH, hg, hl]
    _ = ((∏ ij : Fin d × Fin d, yH (d * ij.1 + ij.2)) * (∏ j : Fin d, yg j) * yl) := by
      simp [Fintype.prod_prod_type]
    _ = ((∏ k : Fin (d * d), yH k.val) * (∏ j : Fin d, yg j) * yl) := by
      rw [Fintype.prod_equiv (finProdFinEquiv) (λ ij => yH (d * ij.1 + ij.2)) (λ k => yH k.val) (λ ij => by
        simp [finProdFinEquiv_apply_val, add_comm])]
    _ = ((∏ k ∈ Finset.range (d * d), yH k) * (∏ j ∈ Finset.range d, yg j) * yl) := by
      simp [Fin.prod_univ_eq_prod_range]

/-- A reduced numerator times the quotient of a common denominator: `|u (D / v)| ≤ 2^(s + S)`. -/
theorem AdversarialBco.Bit.Transfer.RowP.scale_bound (u v D : ℤ) (s S : ℕ) (hu : |u| ≤ 2 ^ s) (hv : 1 ≤ v) (hD0 : 0 ≤ D) (hD : D ≤ 2 ^ S) :
    |u * (D / v)| ≤ 2 ^ (s + S) ∧ 0 ≤ D / v ∧ D / v ≤ D := by
  have h_nonneg_div : 0 ≤ D / v := Int.ediv_nonneg hD0 (by linarith)
  have h_div_le_D : D / v ≤ D := Int.ediv_le_self v hD0
  have h_div_le_pow : D / v ≤ 2 ^ S := by
    exact le_trans h_div_le_D hD
  have h_pow_add : (2 : ℤ) ^ s * (2 : ℤ) ^ S = (2 : ℤ) ^ (s + S) := by
    simpa [add_comm] using (pow_add (2 : ℤ) s S).symm
  have h_pow_nonneg : 0 ≤ (2 : ℤ) ^ s := pow_nonneg (by norm_num) s
  have h_main : |u * (D / v)| ≤ (2 : ℤ) ^ (s + S) := by
    calc
      |u * (D / v)| = |u| * |D / v| := abs_mul u (D / v)
      _ = |u| * (D / v) := by rw [abs_of_nonneg h_nonneg_div]
      _ ≤ (2 : ℤ) ^ s * (2 : ℤ) ^ S :=
        mul_le_mul hu h_div_le_pow h_nonneg_div h_pow_nonneg
      _ = (2 : ℤ) ^ (s + S) := h_pow_add
  exact And.intro h_main (And.intro h_nonneg_div h_div_le_D)

