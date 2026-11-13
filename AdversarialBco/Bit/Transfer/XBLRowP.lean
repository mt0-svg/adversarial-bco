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

* `scanK`: the scan of the rows for the `i`-th kept row, as the machine runs it; `scanK_succ`.
* `num_den_of_div`, `red_bounds`: the reduced form of `N / D` by the gcd, and its bounds; `clr_out`.
* The ranges and the magnitudes of the integers of a row: `cells_mat`, `colDot_range`, `quadDen_range`, `scale_bound`,
  `beta_range`, `mag_t`, `mag_beta`; `keep_link`.
-/

namespace AdversarialBco.Bit.Transfer.RowP

open Matrix

/-- The kept-row scan: after the rows `< k`, the number of rows with `keep` and the index of the kept row number `i`
(`0` before it is met). -/
def scanK (keep : ℕ → Bool) (i : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 =>
    if keep k then
      (if (scanK keep i k).1 = i then ((scanK keep i k).1 + 1, k) else ((scanK keep i k).1 + 1, (scanK keep i k).2))
    else scanK keep i k

theorem scanK_succ (keep : ℕ → Bool) (i k : ℕ) : scanK keep i (k + 1) =
    if keep k then (if (scanK keep i k).1 = i then ((scanK keep i k).1 + 1, k)
      else ((scanK keep i k).1 + 1, (scanK keep i k).2)) else scanK keep i k := rfl

end AdversarialBco.Bit.Transfer.RowP

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

/-- Entry `q` of `S₂ᵀ a` with `S₂ i j = xa (d i + j) / DS` and `a = â / P`, as a sum over `range d`. -/
theorem AdversarialBco.Bit.Transfer.RowP.colDot_range {d : ℕ} (S2 : Matrix (Fin d) (Fin d) ℚ) (a : Fin d → ℚ)
    (xa ah : ℕ → ℤ) (DS P : ℤ) (hDS : 0 < DS) (hP : 0 < P)
    (hS : ∀ i j : Fin d, (xa (d * i + j) : ℚ) / DS = S2 i j) (ha : ∀ l : Fin d, (ah l : ℚ) / P = a l)
    (q : Fin d) :
    (S2ᵀ *ᵥ a) q = ((∑ l ∈ Finset.range d, xa (q + d * l) * ah l : ℤ) : ℚ) / ((DS * P : ℤ) : ℚ) := by
  have h_mulvec : (S2ᵀ *ᵥ a) q = ∑ l : Fin d, S2 l q * a l := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [h_mulvec]
  have h_term (l : Fin d) : S2 l q * a l = ((xa (d * l + q) * ah l : ℤ) : ℚ) / ((DS * P : ℤ) : ℚ) := by
    rw [← hS l q, ← ha l]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun l _ => h_term l)]
  rw [← Finset.sum_div]
  congr 1
  have h_num : (∑ l : Fin d, ((xa (d * l + q) * ah l : ℤ) : ℚ)) = ((∑ l : Fin d, xa (d * l + q) * ah l : ℤ) : ℚ) := by
    simp
  rw [h_num]
  congr 1
  have h_sum_eq : (∑ l : Fin d, xa (d * l + q) * ah l) = (∑ l ∈ Finset.range d, xa (q + d * l) * ah l) := by
    calc
      (∑ l : Fin d, xa (d * l + q) * ah l) = (∑ l : Fin d, xa (q + d * l) * ah l) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [add_comm (d * (l : ℕ)) (q : ℕ)]
      _ = (∑ l ∈ Finset.range d, xa (q + d * l) * ah l) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => xa (q + d * k) * ah k) d]
  rw [h_sum_eq]

/-- The magnitudes of a cleared input row: `M^(d+2) ≤ 2^t` and `2^E M^(d+1) ≤ 2^t`, `t = E + size(M) (d + 2)`. -/
theorem AdversarialBco.Bit.Transfer.RowP.mag_t (M d E : ℕ) (hM : 1 ≤ M) :
    (M : ℤ) ^ (d + 2) ≤ 2 ^ (E + M.size * (d + 2)) ∧ (2 : ℤ) ^ E * (M : ℤ) ^ (d + 1) ≤ 2 ^ (E + M.size * (d + 2)) := by
  have hM0 : 0 ≤ (M : ℤ) := Nat.cast_nonneg _
  have hM_le : (M : ℤ) ≤ (2 : ℤ) ^ (M.size) := by
    have h := Nat.lt_size_self M
    have hle : (M : ℤ) ≤ ((2 : ℕ) ^ (M.size) : ℤ) := mod_cast h.le
    simpa [Nat.cast_pow] using hle
  have h_two_one : (1 : ℤ) ≤ (2 : ℤ) := by norm_num
  -- First conjunct: (M : ℤ) ^ (d + 2) ≤ 2 ^ (E + M.size * (d + 2))
  have h1 : (M : ℤ) ^ (d + 2) ≤ (2 : ℤ) ^ (M.size * (d + 2)) := by
    calc
      (M : ℤ) ^ (d + 2) ≤ ((2 : ℤ) ^ (M.size)) ^ (d + 2) :=
        pow_le_pow_left₀ hM0 hM_le (d + 2)
      _ = (2 : ℤ) ^ (M.size * (d + 2)) := by rw [pow_mul]
  have h1' : (M : ℤ) ^ (d + 2) ≤ (2 : ℤ) ^ (E + M.size * (d + 2)) := by
    apply h1.trans
    apply pow_le_pow_right₀ h_two_one
    omega
  -- Second conjunct: (2 : ℤ) ^ E * (M : ℤ) ^ (d + 1) ≤ 2 ^ (E + M.size * (d + 2))
  have h_pow_le : (M : ℤ) ^ (d + 1) ≤ (M : ℤ) ^ (d + 2) := by
    have hM_one : (1 : ℤ) ≤ (M : ℤ) := by exact mod_cast hM
    apply pow_le_pow_right₀ hM_one
    omega
  have h3 : (M : ℤ) ^ (d + 2) ≤ (2 : ℤ) ^ (M.size * (d + 2)) := by
    calc
      (M : ℤ) ^ (d + 2) ≤ ((2 : ℤ) ^ (M.size)) ^ (d + 2) :=
        pow_le_pow_left₀ hM0 hM_le (d + 2)
      _ = (2 : ℤ) ^ (M.size * (d + 2)) := by rw [pow_mul]
  have h4 : (2 : ℤ) ^ E * (M : ℤ) ^ (d + 2) ≤ (2 : ℤ) ^ (E + M.size * (d + 2)) := by
    calc
      (2 : ℤ) ^ E * (M : ℤ) ^ (d + 2) ≤ (2 : ℤ) ^ E * ((2 : ℤ) ^ (M.size)) ^ (d + 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM_le (d + 2)) (pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) _)
      _ = (2 : ℤ) ^ E * (2 : ℤ) ^ (M.size * (d + 2)) := by rw [pow_mul]
      _ = (2 : ℤ) ^ (E + M.size * (d + 2)) := by rw [pow_add]
  have h2' : (2 : ℤ) ^ E * (M : ℤ) ^ (d + 1) ≤ (2 : ℤ) ^ (E + M.size * (d + 2)) := by
    apply (mul_le_mul_of_nonneg_left h_pow_le (pow_nonneg (by norm_num : 0 ≤ (2 : ℤ)) _)).trans h4
  exact And.intro h1' h2'

/-- A row of `A` is nonzero exactly when the sum of the squares of the numerators of its entries is positive. -/
theorem AdversarialBco.Bit.Transfer.RowP.keep_link {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (Nm : ℕ → ℕ → ℤ)
    (h : ∀ (k : Fin m) (j : Fin d), Nm k j = (A k j).num) (k : Fin m) :
    decide (0 < ∑ j ∈ Finset.range d, Nm k j * Nm k j) = decide (A k ≠ 0) := by
  apply decide_eq_decide.mpr
  constructor
  · intro hsum
    by_contra hzero
    have hsumzero : ∑ j ∈ Finset.range d, Nm k j * Nm k j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj_lt : j < d := Finset.mem_range.1 hj
      let jfin : Fin d := ⟨j, hj_lt⟩
      have hzero_entry : A k jfin = 0 := by simp [hzero]
      have hnum_zero : (A k jfin).num = 0 := by rw [hzero_entry, Rat.num_zero]
      have hnum_eq : Nm k jfin.val = (A k jfin).num := h k jfin
      have hnum_zero' : Nm k j = 0 := by
        simpa [jfin] using congrArg id (hnum_eq.trans hnum_zero)
      rw [hnum_zero', zero_mul]
    rw [hsumzero] at hsum
    exact lt_irrefl 0 hsum
  · intro hne
    rcases Function.ne_iff.mp hne with ⟨j, hj⟩
    have hnum_ne_zero : (A k j).num ≠ 0 := Rat.num_ne_zero.mpr hj
    have hsq_pos : 0 < (A k j).num * (A k j).num := mul_self_pos.mpr hnum_ne_zero
    have h_eq : Nm k (j.val) = (A k j).num := h k j
    have hsq_pos' : 0 < Nm k (j.val) * Nm k (j.val) := by rw [h_eq]; exact hsq_pos
    have hmem : j.val ∈ Finset.range d := Finset.mem_range.2 j.is_lt
    have h_nonneg : ∀ i ∈ Finset.range d, 0 ≤ Nm k i * Nm k i := by
      intro i hi; apply mul_self_nonneg
    exact Finset.sum_pos' h_nonneg ⟨j.val, hmem, hsq_pos'⟩

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

/-- `(1 - ε)(b - a·μ)` with `ε = ε̂/2^pF`, `b = b̂/P`, `a = â/P`, `μ = μ̂/DS`, over the common denominator
`2^pF DS P`, the dot product as a sum over `range d`. -/
theorem AdversarialBco.Bit.Transfer.RowP.beta_range {d : ℕ} (pF : ℕ) (eps : ℚ) (eh : ℤ)
    (heps : (eh : ℚ) = eps * 2 ^ pF) (bq : ℚ) (a mu : Fin d → ℚ) (bh : ℤ) (ah xmu : ℕ → ℤ) (DS P : ℤ)
    (hDS : 0 < DS) (hP : 0 < P) (hb : (bh : ℚ) / P = bq) (ha : ∀ l : Fin d, (ah l : ℚ) / P = a l)
    (hmu : ∀ l : Fin d, (xmu l : ℚ) / DS = mu l) :
    (1 - eps) * (bq - a ⬝ᵥ mu) =
      (((2 ^ pF - eh) * (bh * DS - ∑ l ∈ Finset.range d, ah l * xmu l) : ℤ) : ℚ) / ((2 ^ pF * (DS * P) : ℤ) : ℚ) := by
  have hP' : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne.symm
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne.symm
  have h2' : ((2 ^ pF : ℤ) : ℚ) ≠ 0 := by
    have h : (2 : ℤ) ^ pF ≠ 0 := pow_ne_zero pF (by norm_num : (2 : ℤ) ≠ 0)
    exact_mod_cast h
  have hdot : a ⬝ᵥ mu = ((∑ l ∈ Finset.range d, ah l * xmu l : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ) := by
    have h1 : a ⬝ᵥ mu = ∑ l : Fin d, a l * mu l := rfl
    have h2 : (∑ l : Fin d, a l * mu l) = (∑ l : Fin d, ((ah l.val : ℚ) / (P : ℚ)) * ((xmu l.val : ℚ) / (DS : ℚ))) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [← ha l, ← hmu l]
    have h3 : (∑ l : Fin d, ((ah l.val : ℚ) / (P : ℚ)) * ((xmu l.val : ℚ) / (DS : ℚ))) =
             (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ)) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      push_cast
      ring
    have h4 : (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ)) =
             (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ)) / ((P * DS : ℤ) : ℚ) := by
      rw [Finset.sum_div]
    have h5 : (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ)) / ((P * DS : ℤ) : ℚ) =
             ((∑ l : Fin d, (ah l.val * xmu l.val : ℤ)) : ℚ) / ((P * DS : ℤ) : ℚ) := by
      simp
    calc
      a ⬝ᵥ mu = ∑ l : Fin d, a l * mu l := h1
      _ = (∑ l : Fin d, ((ah l.val : ℚ) / (P : ℚ)) * ((xmu l.val : ℚ) / (DS : ℚ))) := h2
      _ = (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ)) := h3
      _ = (∑ l : Fin d, ((ah l.val * xmu l.val : ℤ) : ℚ)) / ((P * DS : ℤ) : ℚ) := h4
      _ = ((∑ l : Fin d, (ah l.val * xmu l.val : ℤ)) : ℚ) / ((P * DS : ℤ) : ℚ) := h5
      _ = ((∑ l ∈ Finset.range d, ah l * xmu l : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ) := by
        simp [Fin.sum_univ_eq_sum_range (fun l => (ah l * xmu l : ℚ)) d]
  have heps' : eps = (eh : ℚ) / ((2 ^ pF : ℤ) : ℚ) := by
    calc
      eps = (eps * ((2 ^ pF : ℤ) : ℚ)) / ((2 ^ pF : ℤ) : ℚ) := by field_simp [h2']
      _ = (eps * (2 ^ pF : ℚ)) / ((2 ^ pF : ℤ) : ℚ) := by norm_cast
      _ = (eh : ℚ) / ((2 ^ pF : ℤ) : ℚ) := by rw [← heps]
  have hb' : bq = (bh : ℚ) / (P : ℚ) := by
    symm; exact hb
  calc
    (1 - eps) * (bq - a ⬝ᵥ mu) = (1 - ((eh : ℚ) / ((2 ^ pF : ℤ) : ℚ))) * ((bh : ℚ) / (P : ℚ) - ((∑ l ∈ Finset.range d, ah l * xmu l : ℤ) : ℚ) / ((P * DS : ℤ) : ℚ)) := by
      rw [heps', hb', hdot]
    _ = (((2 ^ pF - eh) * (bh * DS - ∑ l ∈ Finset.range d, ah l * xmu l) : ℤ) : ℚ) / ((2 ^ pF * (DS * P) : ℤ) : ℚ) := by
      field_simp [hP', hDS', h2']
      push_cast
      ring

/-- The numerator of `(1 - ε) β̃` is below `2^(3t + d + 1)`. -/
theorem AdversarialBco.Bit.Transfer.RowP.mag_beta (d t : ℕ) (e1 bh DS S : ℤ) (he : |e1| ≤ 2 ^ t)
    (hb : |bh| ≤ 2 ^ t) (hD : |DS| ≤ 2 ^ t) (hS : |S| ≤ d * 2 ^ (2 * t)) :
    |e1 * (bh * DS - S)| ≤ 2 ^ (3 * t + d + 1) := by
  have h1 : |bh * DS| ≤ 2 ^ (2 * t) := by
    rw [abs_mul, two_mul, pow_add]; exact mul_le_mul hb hD (abs_nonneg _) (by positivity)
  have h2 : |bh * DS - S| ≤ ((d : ℤ) + 1) * 2 ^ (2 * t) := by
    calc |bh * DS - S| ≤ |bh * DS| + |S| := abs_sub _ _
      _ ≤ 2 ^ (2 * t) + d * 2 ^ (2 * t) := add_le_add h1 hS
      _ = ((d : ℤ) + 1) * 2 ^ (2 * t) := by ring
  have h3 : ((d : ℤ) + 1) ≤ 2 ^ (d + 1) := by
    have := (Nat.lt_two_pow_self (n := d + 1)).le
    exact_mod_cast this
  have h4 : |bh * DS - S| ≤ 2 ^ (2 * t + (d + 1)) := by
    rw [pow_add]
    calc |bh * DS - S| ≤ ((d : ℤ) + 1) * 2 ^ (2 * t) := h2
      _ ≤ 2 ^ (d + 1) * 2 ^ (2 * t) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 2 ^ (2 * t) * 2 ^ (d + 1) := by ring
  rw [abs_mul, show 3 * t + d + 1 = t + (2 * t + (d + 1)) by ring, pow_add]
  exact mul_le_mul he h4 (abs_nonneg _) (by positivity)
