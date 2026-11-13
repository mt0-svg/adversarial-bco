/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The call data of BL's round, part 0: the integer forms

The values of the call data of R11 TEST and R14 LINE as fractions of integers, from numerators on the grids `2^{-p}`
and `2^{-pF}`: the Gram matrix `B Bᵀ` (`gram_link`), `(B Bᵀ) (ŵ / D_w)` (`mulVec_link`), `b' - (η'/2) G'` (`f_link`), the
levels `7.99 ρ - ê - k` and `8 ρ - ê - k` (`level`), the radii (`radius`), the accuracies (`acc`, `eBL_link`), and the
bounds of their numerators and denominators.
-/

open Matrix Finset

theorem AdversarialBco.Bit.Transfer.DataP.gram_bound {d E : ℕ} (Bh : Matrix (Fin d) (Fin d) ℤ)
    (hB : ∀ i j, |Bh i j| ≤ 2 ^ E) (i j : Fin d) : |(Bh * Bhᵀ) i j| ≤ 2 ^ (d + 2 * E) := by
  calc
    |(Bh * Bhᵀ) i j| = |∑ k, Bh i k * (Bhᵀ) k j| := by rw [Matrix.mul_apply]
    _ = |∑ k, Bh i k * Bh j k| := by simp [Matrix.transpose_apply]
    _ ≤ ∑ k, |Bh i k * Bh j k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |Bh i k| * |Bh j k| := by simp [abs_mul]
    _ ≤ ∑ k : Fin d, (2 ^ E) * (2 ^ E) := by
      refine Finset.sum_le_sum ?_
      intro k _
      have hi := hB i k
      have hj := hB j k
      exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
    _ = (Finset.card (Finset.univ : Finset (Fin d))) • ((2 ^ E) * (2 ^ E)) := by simp
    _ = (d : ℤ) * ((2 ^ E) * (2 ^ E)) := by simp
    _ = (d : ℤ) * (2 ^ (2 * E)) := by ring
    _ ≤ ((2 : ℤ) ^ d) * (2 ^ (2 * E)) := by
      have hd : (d : ℤ) ≤ (2 : ℤ) ^ d := by
        have := Nat.lt_two_pow_self (n := d)
        exact mod_cast this.le
      have hpos : 0 ≤ (2 : ℤ) ^ (2 * E) := by positivity
      nlinarith
    _ = (2 : ℤ) ^ (d + 2 * E) := by
      rw [pow_add]

theorem AdversarialBco.Bit.Transfer.DataP.gram_link {d p : ℕ} (B : Matrix (Fin d) (Fin d) ℚ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (hB : ∀ i j, B i j = (Bh i j : ℚ) / 2 ^ p) (i j : Fin d) :
    (B * Bᵀ) i j = (((Bh * Bhᵀ) i j : ℤ) : ℚ) / (((2 ^ p * 2 ^ p : ℤ)) : ℚ) := by
  calc
    (B * Bᵀ) i j = ∑ k : Fin d, B i k * (Bᵀ) k j := by rw [Matrix.mul_apply]
    _ = ∑ k : Fin d, B i k * B j k := by simp
    _ = ∑ k : Fin d, ((Bh i k : ℚ) / 2 ^ p) * ((Bh j k : ℚ) / 2 ^ p) := by simp_rw [hB i, hB j]
    _ = ∑ k : Fin d, ((Bh i k : ℚ) * (Bh j k : ℚ)) / ((2 ^ p : ℚ) * (2 ^ p : ℚ)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    _ = (∑ k : Fin d, ((Bh i k : ℚ) * (Bh j k : ℚ))) / ((2 ^ p : ℚ) * (2 ^ p : ℚ)) := by rw [Finset.sum_div]
    _ = ((∑ k : Fin d, (Bh i k * Bh j k : ℤ)) : ℚ) / ((2 ^ p : ℚ) * (2 ^ p : ℚ)) := by
      simp [Int.cast_mul]
    _ = (((Bh * Bhᵀ) i j : ℤ) : ℚ) / (((2 ^ p * 2 ^ p : ℤ)) : ℚ) := by
      simp [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

theorem AdversarialBco.Bit.Transfer.DataP.mulVec_link {d p : ℕ} (B : Matrix (Fin d) (Fin d) ℚ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (wh : Fin d → ℤ) (Dw : ℤ) (hDw : 0 < Dw) (hB : ∀ i j, B i j = (Bh i j : ℚ) / 2 ^ p) (i : Fin d) :
    ((B * Bᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) i = ((((Bh * Bhᵀ) *ᵥ wh) i : ℤ) : ℚ) / (((2 ^ p * 2 ^ p * Dw : ℤ)) : ℚ) := by
  have hB_ext : B = Matrix.of (λ i j => (Bh i j : ℚ) / 2 ^ p) := by
    ext i j; exact hB i j
  rw [hB_ext]
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h2p : (2 ^ p : ℚ) ≠ 0 := pow_ne_zero p (by norm_num : (2 : ℚ) ≠ 0)
  have hDw' : (Dw : ℚ) ≠ 0 := by exact mod_cast hDw.ne.symm
  have h_denom : ((2 ^ p * 2 ^ p * Dw : ℤ) : ℚ) ≠ 0 := by
    intro hzero
    have hzero' : (2 ^ p * 2 ^ p * Dw : ℤ) = 0 := by exact mod_cast hzero
    have h := mul_ne_zero (mul_ne_zero (pow_ne_zero p (by norm_num : (2 : ℤ) ≠ 0))
      (pow_ne_zero p (by norm_num : (2 : ℤ) ≠ 0))) hDw.ne.symm
    exact h hzero'
  rw [eq_div_iff h_denom]
  push_cast
  simp only [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h2p, hDw']
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem AdversarialBco.Bit.Transfer.DataP.f_link {d p pF : ℕ} (bp Gp : Fin d → ℚ) (bh Gh : Fin d → ℤ) (eta : ℚ) (eh : ℤ)
    (hb : ∀ j, bp j = (bh j : ℚ) / 2 ^ p) (hG : ∀ j, Gp j = (Gh j : ℚ) / 2 ^ p) (he : eta = (eh : ℚ) / 2 ^ pF)
    (j : Fin d) :
    (bp - (eta / 2) • Gp) j = ((2 * 2 ^ pF * bh j - eh * Gh j : ℤ) : ℚ) / ((2 * 2 ^ pF * 2 ^ p : ℤ) : ℚ) := by
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb j, hG j, he]
  push_cast
  field_simp

theorem AdversarialBco.Bit.Transfer.DataP.level (rho eHat k : ℚ) (rh H kh F Q : ℤ) (hF : 0 < F) (hH : 0 < H) (hQ : 0 < Q)
    (hr : rho = (rh : ℚ) / F) (he : eHat = 1 / (H : ℚ)) (hk : k = (kh : ℚ) / Q) :
    799 / 100 * rho - eHat - k = ((799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H : ℤ) : ℚ) / ((100 * F * H * Q : ℤ) : ℚ) ∧
      8 * rho - eHat - k = ((8 * rh * H * Q - F * Q - kh * F * H : ℤ) : ℚ) / ((F * H * Q : ℤ) : ℚ) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hH' : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne.symm
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  rw [hr, he, hk]
  push_cast
  field_simp [hF', hH', hQ']
  simp

theorem AdversarialBco.Bit.Transfer.DataP.radius (eps sb : ℚ) (eh sh F : ℤ) (hF : 0 < F) (he : eps = (eh : ℚ) / F)
    (hs : sb = (sh : ℚ) / F) :
    1 - eps = ((F - eh : ℤ) : ℚ) / (F : ℚ) ∧ sb * (1 - eps) / 2 = ((sh * (F - eh) : ℤ) : ℚ) / ((2 * F ^ 2 : ℤ) : ℚ) := by
  have hF' : (F : ℚ) ≠ 0 := by exact mod_cast hF.ne.symm
  constructor
  · rw [he]
    push_cast
    field_simp [hF']
  · rw [he, hs]
    push_cast
    field_simp [hF']

theorem AdversarialBco.Bit.Transfer.DataP.acc (eps sb : ℚ) (eh sh F : ℤ) (Ne d Lam : ℕ) (hF : 0 < F) (hNe : 1 ≤ Ne)
    (hd : 1 ≤ d) (hLam : Lam = d * Ne) (he : eps = (eh : ℚ) / F) (hs : sb = (sh : ℚ) / F) :
    (1 - eps) ^ 2 / ((Ne : ℚ) * d * 8) = (((F - eh) ^ 2 : ℤ) : ℚ) / ((8 * Lam * F ^ 2 : ℤ) : ℚ) ∧
      (sb * (1 - eps)) ^ 2 / ((Ne : ℚ) * d * 8) = (((sh * (F - eh)) ^ 2 : ℤ) : ℚ) / ((8 * Lam * F ^ 4 : ℤ) : ℚ) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hNe' : (Ne : ℚ) ≠ 0 := by
    have h : Ne ≠ 0 := by omega
    exact_mod_cast h
  have hd' : (d : ℚ) ≠ 0 := by
    have h : d ≠ 0 := by omega
    exact_mod_cast h
  have hLamZ : (Lam : ℤ) = (d : ℤ) * (Ne : ℤ) := by exact_mod_cast hLam
  have he' : eps = (eh : ℚ) / (F : ℚ) := by exact_mod_cast he
  have hs' : sb = (sh : ℚ) / (F : ℚ) := by exact_mod_cast hs
  rw [he', hs', hLamZ]
  constructor
  · push_cast
    field_simp [hF', hNe', hd']
  · push_cast
    field_simp [hF', hNe', hd']

theorem AdversarialBco.Bit.Transfer.DataP.eBL_link (R : ℚ) (Rh F : ℤ) (Ne d n Lam : ℕ) (hF : 0 < F) (hR : 0 < Rh)
    (hNe : 1 ≤ Ne) (hd : 1 ≤ d) (hn : 1 ≤ n) (hLam : Lam = d * Ne) (hRe : R = (Rh : ℚ) / F) :
    1 / ((Ne : ℚ) * (128 * (n : ℚ) ^ 2 * R ^ 2 * d)) = ((F ^ 2 : ℤ) : ℚ) / ((128 * Lam * n ^ 2 * Rh ^ 2 : ℤ) : ℚ) := by
  subst hLam
  subst hRe
  push_cast
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne'
  have hRh' : (Rh : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hNe' : (Ne : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  have hd' : (d : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  have hn' : (n : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  field_simp [hF', hRh', hNe', hd', hn']

theorem AdversarialBco.Bit.Transfer.DataP.level_bound (rh H kh F Q : ℤ) (E : ℕ) (b1 : |rh| ≤ 2 ^ E) (b2 : |H| ≤ 2 ^ E)
    (b3 : |kh| ≤ 2 ^ E) (b4 : |F| ≤ 2 ^ E) (b5 : |Q| ≤ 2 ^ E) :
    |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| ≤ 2 ^ (3 * E + 12) ∧ |100 * F * H * Q| ≤ 2 ^ (3 * E + 12) ∧
      |8 * rh * H * Q - F * Q - kh * F * H| ≤ 2 ^ (3 * E + 12) ∧ |F * H * Q| ≤ 2 ^ (3 * E + 12) := by
  set x := (2 : ℤ) ^ E with hx
  have hx_nonneg : 0 ≤ x := pow_nonneg (by norm_num) E
  have hx_ge_one : (1 : ℤ) ≤ x := by
    have h := Nat.one_le_pow' E 1
    have h' : (1 : ℤ) ≤ (2 : ℤ) ^ E := by exact_mod_cast h
    rw [hx]
    exact h'
  have hx_cube_nonneg : 0 ≤ x ^ 3 := pow_nonneg hx_nonneg 3
  -- Bound for a product of three terms each bounded by x
  have h_cube (a b c : ℤ) (ha : |a| ≤ x) (hb : |b| ≤ x) (hc : |c| ≤ x) : |a * b * c| ≤ x ^ 3 := by
    calc
      |a * b * c| = |a| * |b| * |c| := by simp [abs_mul]
      _ ≤ x * x * x := by
        refine mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hx_nonneg) hc (abs_nonneg _) ?_
        nlinarith
      _ = x ^ 3 := by ring
  -- Bound for a product of two terms each bounded by x
  have h_sq (a b : ℤ) (ha : |a| ≤ x) (hb : |b| ≤ x) : |a * b| ≤ x ^ 2 := by
    calc
      |a * b| = |a| * |b| := by simp [abs_mul]
      _ ≤ x * x := mul_le_mul ha hb (abs_nonneg _) hx_nonneg
      _ = x ^ 2 := by ring
  -- h4: |F * H * Q| ≤ 2^(3*E+12)
  have h4 : |F * H * Q| ≤ (2 : ℤ) ^ (3 * E + 12) := by
    calc
      |F * H * Q| ≤ x ^ 3 := h_cube F H Q b4 b2 b5
      _ = ((2 : ℤ) ^ E) ^ 3 := rfl
      _ = (2 : ℤ) ^ (E * 3) := by ring
      _ = (2 : ℤ) ^ (3 * E) := by rw [mul_comm]
      _ ≤ (2 : ℤ) ^ (3 * E + 12) := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
  -- h2: |100 * F * H * Q| ≤ 2^(3*E+12)
  have h2 : |100 * F * H * Q| ≤ (2 : ℤ) ^ (3 * E + 12) := by
    calc
      |100 * F * H * Q| = |(100 : ℤ)| * |F| * |H| * |Q| := by simp [abs_mul]
      _ = (100 : ℤ) * |F| * |H| * |Q| := by norm_num
      _ ≤ (100 : ℤ) * x * x * x := by
        -- (100 * |F|) * |H| * |Q| ≤ (100 * x) * x * x
        have h1 : (100 : ℤ) * |F| ≤ (100 : ℤ) * x :=
          mul_le_mul_of_nonneg_left b4 (by norm_num : (0 : ℤ) ≤ 100)
        have h2' : ((100 : ℤ) * |F|) * |H| ≤ ((100 : ℤ) * x) * x :=
          mul_le_mul h1 b2 (abs_nonneg _) (by nlinarith)
        exact mul_le_mul h2' b5 (abs_nonneg _) (by nlinarith)
      _ = (100 : ℤ) * x ^ 3 := by ring
      _ ≤ ((2 : ℤ) ^ 12) * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num : (100 : ℤ) ≤ (2 : ℤ) ^ 12) hx_cube_nonneg
      _ = (2 : ℤ) ^ (3 * E + 12) := by
        calc
          ((2 : ℤ) ^ 12) * x ^ 3 = ((2 : ℤ) ^ 12) * ((2 : ℤ) ^ E) ^ 3 := rfl
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (E * 3) := by ring
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (3 * E) := by rw [mul_comm E 3]
          _ = (2 : ℤ) ^ (12 + 3 * E) := by rw [pow_add]
          _ = (2 : ℤ) ^ (3 * E + 12) := by ring
  -- h1: |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| ≤ 2^(3*E+12)
  have h1 : |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| ≤ (2 : ℤ) ^ (3 * E + 12) := by
    -- First, use triangle inequality to break down the expression
    have h_triangle : |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| ≤
        |799 * rh * H * Q| + |100 * F * Q| + |100 * kh * F * H| := by
      calc
        |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| =
            |(799 * rh * H * Q) - (100 * F * Q + 100 * kh * F * H)| := by ring
        _ ≤ |799 * rh * H * Q| + |100 * F * Q + 100 * kh * F * H| := abs_sub _ _
        _ ≤ |799 * rh * H * Q| + (|100 * F * Q| + |100 * kh * F * H|) := by
          nlinarith [abs_add_le (100 * F * Q) (100 * kh * F * H)]
        _ = |799 * rh * H * Q| + |100 * F * Q| + |100 * kh * F * H| := by ring
    calc
      |799 * rh * H * Q - 100 * F * Q - 100 * kh * F * H| ≤
          |799 * rh * H * Q| + |100 * F * Q| + |100 * kh * F * H| := h_triangle
      _ = (|(799 : ℤ)| * |rh| * |H| * |Q|) + (|(100 : ℤ)| * |F| * |Q|) + (|(100 : ℤ)| * |kh| * |F| * |H|) := by
        simp [abs_mul]
      _ = (799 * |rh| * |H| * |Q|) + (100 * |F| * |Q|) + (100 * |kh| * |F| * |H|) := by norm_num
      _ ≤ (799 * x * x * x) + (100 * x * x) + (100 * x * x * x) := by
        have h799 : 799 * |rh| * |H| * |Q| ≤ 799 * x * x * x := by
          have h1' : 799 * |rh| ≤ 799 * x :=
            mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℤ) ≤ 799)
          have h2' : (799 * |rh|) * |H| ≤ (799 * x) * x :=
            mul_le_mul h1' b2 (abs_nonneg _) (by nlinarith)
          exact mul_le_mul h2' b5 (abs_nonneg _) (by nlinarith)
        have h100_1 : 100 * |F| * |Q| ≤ 100 * x * x := by
          have h1' : 100 * |F| ≤ 100 * x :=
            mul_le_mul_of_nonneg_left b4 (by norm_num : (0 : ℤ) ≤ 100)
          exact mul_le_mul h1' b5 (abs_nonneg _) (by nlinarith)
        have h100_2 : 100 * |kh| * |F| * |H| ≤ 100 * x * x * x := by
          have h1' : 100 * |kh| ≤ 100 * x :=
            mul_le_mul_of_nonneg_left b3 (by norm_num : (0 : ℤ) ≤ 100)
          have h2' : (100 * |kh|) * |F| ≤ (100 * x) * x :=
            mul_le_mul h1' b4 (abs_nonneg _) (by nlinarith)
          exact mul_le_mul h2' b2 (abs_nonneg _) (by nlinarith)
        nlinarith
      _ = (799 * x ^ 3) + (100 * x ^ 2) + (100 * x ^ 3) := by ring
      _ = (899 * x ^ 3) + (100 * x ^ 2) := by ring
      _ ≤ (899 * x ^ 3) + (100 * x ^ 3) := by
        have h_sq_le_cube : x ^ 2 ≤ x ^ 3 := by
          calc
            x ^ 2 = x ^ 2 * 1 := by ring
            _ ≤ x ^ 2 * x := mul_le_mul_of_nonneg_left hx_ge_one (pow_nonneg hx_nonneg 2)
            _ = x ^ 3 := by ring
        nlinarith
      _ = 999 * x ^ 3 := by ring
      _ ≤ ((2 : ℤ) ^ 12) * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num : (999 : ℤ) ≤ (2 : ℤ) ^ 12) hx_cube_nonneg
      _ = (2 : ℤ) ^ (3 * E + 12) := by
        calc
          ((2 : ℤ) ^ 12) * x ^ 3 = ((2 : ℤ) ^ 12) * ((2 : ℤ) ^ E) ^ 3 := rfl
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (E * 3) := by ring
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (3 * E) := by rw [mul_comm E 3]
          _ = (2 : ℤ) ^ (12 + 3 * E) := by rw [pow_add]
          _ = (2 : ℤ) ^ (3 * E + 12) := by ring
  -- h3: |8 * rh * H * Q - F * Q - kh * F * H| ≤ 2^(3*E+12)
  have h3 : |8 * rh * H * Q - F * Q - kh * F * H| ≤ (2 : ℤ) ^ (3 * E + 12) := by
    -- First, use triangle inequality to break down the expression
    have h_triangle : |8 * rh * H * Q - F * Q - kh * F * H| ≤
        |8 * rh * H * Q| + |F * Q| + |kh * F * H| := by
      calc
        |8 * rh * H * Q - F * Q - kh * F * H| =
            |(8 * rh * H * Q) - (F * Q + kh * F * H)| := by ring
        _ ≤ |8 * rh * H * Q| + |F * Q + kh * F * H| := abs_sub _ _
        _ ≤ |8 * rh * H * Q| + (|F * Q| + |kh * F * H|) := by
          nlinarith [abs_add_le (F * Q) (kh * F * H)]
        _ = |8 * rh * H * Q| + |F * Q| + |kh * F * H| := by ring
    calc
      |8 * rh * H * Q - F * Q - kh * F * H| ≤
          |8 * rh * H * Q| + |F * Q| + |kh * F * H| := h_triangle
      _ = (|(8 : ℤ)| * |rh| * |H| * |Q|) + (|F| * |Q|) + (|kh| * |F| * |H|) := by
        simp [abs_mul]
      _ = (8 * |rh| * |H| * |Q|) + (|F| * |Q|) + (|kh| * |F| * |H|) := by norm_num
      _ ≤ (8 * x * x * x) + (x * x) + (x * x * x) := by
        have h8 : 8 * |rh| * |H| * |Q| ≤ 8 * x * x * x := by
          have h1' : 8 * |rh| ≤ 8 * x :=
            mul_le_mul_of_nonneg_left b1 (by norm_num : (0 : ℤ) ≤ 8)
          have h2' : (8 * |rh|) * |H| ≤ (8 * x) * x :=
            mul_le_mul h1' b2 (abs_nonneg _) (by nlinarith)
          exact mul_le_mul h2' b5 (abs_nonneg _) (by nlinarith)
        have hFQ : |F| * |Q| ≤ x * x :=
          mul_le_mul b4 b5 (abs_nonneg _) hx_nonneg
        have hkhFH : |kh| * |F| * |H| ≤ x * x * x := by
          have h1' : |kh| * |F| ≤ x * x :=
            mul_le_mul b3 b4 (abs_nonneg _) hx_nonneg
          exact mul_le_mul h1' b2 (abs_nonneg _) (by nlinarith)
        nlinarith
      _ = (8 * x ^ 3) + (x ^ 2) + (x ^ 3) := by ring
      _ = (9 * x ^ 3) + (x ^ 2) := by ring
      _ ≤ (9 * x ^ 3) + (x ^ 3) := by
        have h_sq_le_cube : x ^ 2 ≤ x ^ 3 := by
          calc
            x ^ 2 = x ^ 2 * 1 := by ring
            _ ≤ x ^ 2 * x := mul_le_mul_of_nonneg_left hx_ge_one (pow_nonneg hx_nonneg 2)
            _ = x ^ 3 := by ring
        nlinarith
      _ = 10 * x ^ 3 := by ring
      _ ≤ ((2 : ℤ) ^ 12) * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num : (10 : ℤ) ≤ (2 : ℤ) ^ 12) hx_cube_nonneg
      _ = (2 : ℤ) ^ (3 * E + 12) := by
        calc
          ((2 : ℤ) ^ 12) * x ^ 3 = ((2 : ℤ) ^ 12) * ((2 : ℤ) ^ E) ^ 3 := rfl
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (E * 3) := by ring
          _ = ((2 : ℤ) ^ 12) * (2 : ℤ) ^ (3 * E) := by rw [mul_comm E 3]
          _ = (2 : ℤ) ^ (12 + 3 * E) := by rw [pow_add]
          _ = (2 : ℤ) ^ (3 * E + 12) := by ring
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))
theorem AdversarialBco.Bit.Transfer.DataP.acc_bound (sh eh F Lam Rh n : ℤ) (E : ℕ) (b1 : |sh| ≤ 2 ^ E) (b2 : |eh| ≤ 2 ^ E)
    (b3 : |F| ≤ 2 ^ E) (b4 : |Lam| ≤ 2 ^ E) (b5 : |Rh| ≤ 2 ^ E) (b6 : |n| ≤ 2 ^ E) :
    |(F - eh) ^ 2| ≤ 2 ^ (5 * E + 8) ∧ |8 * Lam * F ^ 2| ≤ 2 ^ (5 * E + 8) ∧ |(sh * (F - eh)) ^ 2| ≤ 2 ^ (5 * E + 8) ∧
      |8 * Lam * F ^ 4| ≤ 2 ^ (5 * E + 8) ∧ |F ^ 2| ≤ 2 ^ (5 * E + 8) ∧ |128 * Lam * n ^ 2 * Rh ^ 2| ≤ 2 ^ (5 * E + 8) ∧
      |F - eh| ≤ 2 ^ (5 * E + 8) ∧ |sh * (F - eh)| ≤ 2 ^ (5 * E + 8) ∧ |2 * F ^ 2| ≤ 2 ^ (5 * E + 8) := by
  set X := (2 : ℤ) ^ E with hX
  have hXpos : 1 ≤ X := by
    rw [hX]
    have h_nat : (1 : ℕ) ^ E ≤ (2 : ℕ) ^ E := Nat.pow_le_pow_left (by omega) E
    have h_cast : (1 : ℤ) ^ E ≤ (2 : ℤ) ^ E := by exact mod_cast h_nat
    have h_one : (1 : ℤ) ^ E = 1 := by simp
    rw [h_one] at h_cast
    exact h_cast
  have hXnonneg : 0 ≤ X := by linarith
  have h_pow2_le : X ^ 2 ≤ X ^ 5 :=
    pow_le_pow_right₀ hXpos (by omega : (2 : ℕ) ≤ (5 : ℕ))
  have h_pow3_le : X ^ 3 ≤ X ^ 5 :=
    pow_le_pow_right₀ hXpos (by omega : (3 : ℕ) ≤ (5 : ℕ))
  have h_pow4_le : X ^ 4 ≤ X ^ 5 :=
    pow_le_pow_right₀ hXpos (by omega : (4 : ℕ) ≤ (5 : ℕ))
  have hX5_nonneg : 0 ≤ X ^ 5 := pow_nonneg hXnonneg 5
  have h256_X5_nonneg : 0 ≤ (256 : ℤ) * X ^ 5 := by nlinarith
  have h_bound1 : |F - eh| ≤ 2 * X := by
    calc
      |F - eh| ≤ |F| + |eh| := abs_sub _ _
      _ ≤ X + X := add_le_add b3 b2
      _ = 2 * X := by ring
  have h_bound2 : |sh * (F - eh)| ≤ 2 * X ^ 2 := by
    calc
      |sh * (F - eh)| = |sh| * |F - eh| := abs_mul _ _
      _ ≤ X * (2 * X) :=
        mul_le_mul b1 h_bound1 (abs_nonneg _) (by linarith)
      _ = 2 * X ^ 2 := by ring
  have h_256_X5 : (256 : ℤ) * X ^ 5 = (2 : ℤ) ^ (5 * E + 8) := by
    calc
      (256 : ℤ) * X ^ 5 = (2 ^ 8) * ((2 : ℤ) ^ E) ^ 5 := by
        norm_num [hX]
      _ = (2 ^ 8) * (2 ^ (E * 5)) := by simp [pow_mul]
      _ = (2 ^ 8) * (2 ^ (5 * E)) := by rw [mul_comm E 5]
      _ = 2 ^ (8 + 5 * E) := by rw [pow_add]
      _ = 2 ^ (5 * E + 8) := by ring
  have h_target1 : |(F - eh) ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_sq : |F - eh| ^ 2 ≤ (2 * X) ^ 2 := by
      simpa [sq] using mul_self_le_mul_self (abs_nonneg _) h_bound1
    calc
      |(F - eh) ^ 2| = |F - eh| ^ 2 := abs_pow _ _
      _ ≤ (2 * X) ^ 2 := h_sq
      _ = 4 * X ^ 2 := by ring
      _ ≤ 4 * X ^ 5 := mul_le_mul_of_nonneg_left h_pow2_le (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target2 : |8 * Lam * F ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_prod : 8 * |Lam| * |F| ^ 2 ≤ 8 * X * X ^ 2 := by
      have hLam_le : 8 * |Lam| ≤ 8 * X :=
        mul_le_mul_of_nonneg_left b4 (by norm_num)
      have h_sq : |F| ^ 2 ≤ X ^ 2 := by
        simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b3
      have h_sq_nonneg : 0 ≤ |F| ^ 2 := pow_two_nonneg _
      have h_8X_nonneg : 0 ≤ 8 * X := by nlinarith
      -- (8*|Lam|) * |F|^2 ≤ (8*X) * X^2
      exact mul_le_mul hLam_le h_sq h_sq_nonneg h_8X_nonneg
    calc
      |8 * Lam * F ^ 2| = 8 * |Lam| * |F| ^ 2 := by simp [abs_mul, mul_assoc]
      _ ≤ 8 * X * X ^ 2 := h_prod
      _ = 8 * X ^ 3 := by ring
      _ ≤ 8 * X ^ 5 := mul_le_mul_of_nonneg_left h_pow3_le (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target3 : |(sh * (F - eh)) ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_sq : |sh * (F - eh)| ^ 2 ≤ (2 * X ^ 2) ^ 2 := by
      simpa [sq] using mul_self_le_mul_self (abs_nonneg _) h_bound2
    calc
      |(sh * (F - eh)) ^ 2| = |sh * (F - eh)| ^ 2 := abs_pow _ _
      _ ≤ (2 * X ^ 2) ^ 2 := h_sq
      _ = 4 * X ^ 4 := by ring
      _ ≤ 4 * X ^ 5 := mul_le_mul_of_nonneg_left h_pow4_le (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target4 : |8 * Lam * F ^ 4| ≤ 2 ^ (5 * E + 8) := by
    have h_prod : 8 * |Lam| * |F| ^ 4 ≤ 8 * X * X ^ 4 := by
      have hLam_le : 8 * |Lam| ≤ 8 * X :=
        mul_le_mul_of_nonneg_left b4 (by norm_num)
      have h_four : |F| ^ 4 ≤ X ^ 4 := by
        have h_sq : |F| ^ 2 ≤ X ^ 2 := by
          simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b3
        have h_sq_nonneg : 0 ≤ |F| ^ 2 := pow_two_nonneg _
        have h_sq_sq : (|F| ^ 2) ^ 2 ≤ (X ^ 2) ^ 2 := by
          simpa [sq] using mul_self_le_mul_self h_sq_nonneg h_sq
        calc
          |F| ^ 4 = (|F| ^ 2) ^ 2 := by ring
          _ ≤ (X ^ 2) ^ 2 := h_sq_sq
          _ = X ^ 4 := by ring
      have h_four_nonneg : 0 ≤ |F| ^ 4 := by
        have : |F| ^ 4 = (|F| ^ 2) ^ 2 := by ring
        rw [this]
        exact pow_two_nonneg _
      have h_8X_nonneg : 0 ≤ 8 * X := by nlinarith
      exact mul_le_mul hLam_le h_four h_four_nonneg h_8X_nonneg
    calc
      |8 * Lam * F ^ 4| = 8 * |Lam| * |F| ^ 4 := by simp [abs_mul, mul_assoc]
      _ ≤ 8 * X * X ^ 4 := h_prod
      _ = 8 * X ^ 5 := by ring
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target5 : |F ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_sq : |F| ^ 2 ≤ X ^ 2 := by
      simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b3
    rw [abs_pow]
    apply le_trans h_sq ?_
    apply le_trans h_pow2_le ?_
    have h : X ^ 5 ≤ 256 * X ^ 5 := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1 : ℤ) ≤ 256) hX5_nonneg
    apply le_trans h ?_
    rw [h_256_X5]
  have h_target6 : |128 * Lam * n ^ 2 * Rh ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_prod : 128 * |Lam| * |n| ^ 2 * |Rh| ^ 2 ≤ 128 * X * X ^ 2 * X ^ 2 := by
      have hLam_le : 128 * |Lam| ≤ 128 * X :=
        mul_le_mul_of_nonneg_left b4 (by norm_num)
      have hn_sq : |n| ^ 2 ≤ X ^ 2 := by
        simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b6
      have hRh_sq : |Rh| ^ 2 ≤ X ^ 2 := by
        simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b5
      have hn_sq_nonneg : 0 ≤ |n| ^ 2 := pow_two_nonneg _
      have hRh_sq_nonneg : 0 ≤ |Rh| ^ 2 := pow_two_nonneg _
      have h128X_nonneg : 0 ≤ 128 * X := by nlinarith
      have h128Xsq_nonneg : 0 ≤ 128 * X * X ^ 2 := by nlinarith
      have h2 : 128 * |Lam| * |n| ^ 2 ≤ 128 * X * X ^ 2 :=
        mul_le_mul hLam_le hn_sq hn_sq_nonneg h128X_nonneg
      have h3 : 128 * |Lam| * |n| ^ 2 * |Rh| ^ 2 ≤ 128 * X * X ^ 2 * X ^ 2 :=
        mul_le_mul h2 hRh_sq hRh_sq_nonneg h128Xsq_nonneg
      exact h3
    calc
      |128 * Lam * n ^ 2 * Rh ^ 2| = 128 * |Lam| * |n| ^ 2 * |Rh| ^ 2 := by
        simp [abs_mul, mul_assoc]
      _ ≤ 128 * X * X ^ 2 * X ^ 2 := h_prod
      _ = 128 * X ^ 5 := by ring
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have hX_le_X5 : X ≤ X ^ 5 := by
    have h := pow_le_pow_right₀ hXpos (by omega : (1 : ℕ) ≤ (5 : ℕ))
    simpa using h
  have h_target7 : |F - eh| ≤ 2 ^ (5 * E + 8) := by
    calc
      |F - eh| ≤ 2 * X := h_bound1
      _ ≤ 2 * X ^ 5 := mul_le_mul_of_nonneg_left hX_le_X5 (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target8 : |sh * (F - eh)| ≤ 2 ^ (5 * E + 8) := by
    calc
      |sh * (F - eh)| ≤ 2 * X ^ 2 := h_bound2
      _ ≤ 2 * X ^ 5 := mul_le_mul_of_nonneg_left h_pow2_le (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  have h_target9 : |2 * F ^ 2| ≤ 2 ^ (5 * E + 8) := by
    have h_sq : 2 * |F| ^ 2 ≤ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_left (by
        simpa [sq] using mul_self_le_mul_self (abs_nonneg _) b3) (by norm_num)
    calc
      |2 * F ^ 2| = 2 * |F| ^ 2 := by simp [abs_mul]
      _ ≤ 2 * X ^ 2 := h_sq
      _ ≤ 2 * X ^ 5 := mul_le_mul_of_nonneg_left h_pow2_le (by norm_num)
      _ ≤ 256 * X ^ 5 := mul_le_mul_of_nonneg_right (by norm_num) hX5_nonneg
      _ = 2 ^ (5 * E + 8) := h_256_X5
  exact And.intro h_target1 (And.intro h_target2 (And.intro h_target3 (And.intro h_target4 (And.intro h_target5 (And.intro h_target6 (And.intro h_target7 (And.intro h_target8 h_target9)))))))

theorem AdversarialBco.Bit.Transfer.DataP.up_pos (k q d : ℕ) (x : ℚ) (hd : 1 ≤ d) :
    0 < (⌈134 * (d : ℚ) * (((Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1) / 2 ^ q) * 2 ^ k⌉ : ℚ) / 2 ^ k := by
  have hd' : 0 < (d : ℚ) := by
    have hd_nat : 0 < d := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hd
    exact_mod_cast hd_nat
  have h_two_pow_q : 0 < (2 : ℚ) ^ q := pow_pos (by norm_num : 0 < (2 : ℚ)) q
  have h_two_pow_k : 0 < (2 : ℚ) ^ k := pow_pos (by norm_num : 0 < (2 : ℚ)) k
  have h_sqrt_nonneg : 0 ≤ (Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) := by
    exact mod_cast Nat.zero_le _
  have h_num_pos : 0 < (Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1 := by
    linarith
  have h_div_pos : 0 < ((Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1) / (2 : ℚ) ^ q :=
    div_pos h_num_pos h_two_pow_q
  have h_inner_pos : 0 < 134 * (d : ℚ) * (((Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1) / (2 : ℚ) ^ q) * (2 : ℚ) ^ k := by
    positivity
  have h_ceil_pos : 0 < ⌈134 * (d : ℚ) * (((Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1) / (2 : ℚ) ^ q) * (2 : ℚ) ^ k⌉ :=
    (Int.ceil_pos.mpr h_inner_pos)
  have h_ceil_pos_q : 0 < (⌈134 * (d : ℚ) * (((Nat.sqrt ⌈x * 4 ^ q⌉₊ : ℚ) + 1) / (2 : ℚ) ^ q) * (2 : ℚ) ^ k⌉ : ℚ) := by
    exact_mod_cast h_ceil_pos
  exact div_pos h_ceil_pos_q h_two_pow_k
