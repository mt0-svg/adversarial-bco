/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRs
public import AdversarialBco.Bit.Transfer.XBLR8M

@[expose] public section

/-!
# Tests and magnitudes of BL's round

R10's test on the cells `d i + j` of an array (`frob2_flat`), R12's test in the form the machine computes (`r12_mach`),
and the magnitude bounds of the round's values: `x·x`, the numerators of `rnd_p`, the linear terms of R11 and R14,
the numerators of `w_μ` and the two sides of R12's test.
-/

open AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer.BLM Matrix

/-- A sum over the `d²` cells `0, ..., d² - 1` as the double sum over the rows `i` and the columns `j` of the cell
`d i + j`. -/
theorem AdversarialBco.Bit.Transfer.BLM.flat_sum {d : ℕ} (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (d * d), f k = ∑ i : Fin d, ∑ j : Fin d, f (d * i + j) := by
  have h : ∀ r : ℕ, ∑ k ∈ Finset.range (d * r), f k = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range d, f (d * i + j) := by
    intro r
    induction' r with r ih
    · simp
    · rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
  calc
    ∑ k ∈ Finset.range (d * d), f k = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d, f (d * i + j) := h d
    _ = ∑ i : Fin d, ∑ j ∈ Finset.range d, f (d * (i : ℕ) + j) := by rw [← Fin.sum_univ_eq_sum_range]
    _ = ∑ i : Fin d, ∑ j : Fin d, f (d * (i : ℕ) + (j : ℕ)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← Fin.sum_univ_eq_sum_range]

/-- R10's test on the machine: the cells `d i + j` of an array hold the numerators of `M` on the grid `2^{-p}`, the
machine compares `2 Λ 2^p 2^p` with the sum of the squares of the `d²` cells. -/
theorem AdversarialBco.Bit.Transfer.BLM.frob2_flat {d : ℕ} (p Lam : ℕ) (M : Matrix (Fin d) (Fin d) ℚ) (Bf : ℕ → ℤ)
    (hB : ∀ i j : Fin d, Bf (d * i + j) = qn p (M i j)) (h : ∀ i j, OnG p (M i j)) :
    (2 * (Lam : ℚ) < frob2 M ↔ 2 * (Lam : ℤ) * 2 ^ p * 2 ^ p < ∑ k ∈ Finset.range (d * d), Bf k * Bf k) := by
  have h_grid := frob2_grid p Lam M h
  have h_flat := flat_sum (d := d) (fun k => Bf k * Bf k)
  have h_left : 2 * (Lam : ℤ) * 2 ^ p * 2 ^ p = 2 * (Lam : ℤ) * (2 ^ p) ^ 2 := by ring
  have h_right : (∑ k ∈ Finset.range (d * d), Bf k * Bf k) = ∑ i : Fin d, ∑ j : Fin d, qn p (M i j) ^ 2 := by
    rw [h_flat]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp [hB i j, pow_two]
  rw [← h_left, ← h_right] at h_grid
  exact h_grid

/-- R12 FIRE in the form the machine computes: `x·(B̂ B̂ᵀ x)` as `(B̂ᵀ x)·(B̂ᵀ x)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r12_mach {d : ℕ} (F Q D H eh lh kh rh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Gh bh x : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hD : 0 < D) (hH : 0 < H) :
    ((eh : ℚ) / F * ((lh : ℚ) / Q - (fun k => (Gh k : ℚ) / Q) ⬝ᵥ fun k => (x k : ℚ) / D) -
          2 * ((fun k => (x k : ℚ) / D) ⬝ᵥ (((Matrix.of fun a b => (Bh a b : ℚ) / Q) *
              (Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ) *ᵥ fun k => (x k : ℚ) / D) / 2 -
            (fun k => (bh k : ℚ) / Q) ⬝ᵥ (fun k => (x k : ℚ) / D) + (kh : ℚ) / Q) ≤
        -((rh : ℚ) / F) + 1 / (H : ℚ)) ↔
      eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
          F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D + kh * Q * D * D) ≤
        (F - rh * H) * Q * Q * D * D := by
  have h_fire := r12_fire F Q D H eh lh kh rh Bh Gh bh x hF hQ hD hH
  have h_dot : x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) = (Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) :=
    dot_mulVec_mul_transpose Bh x
  have hA : (eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
      F * H * (x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) - 2 * Q * D * (bh ⬝ᵥ x) + 2 * Q * D ^ 2 * kh)) =
      (eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
      F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
        kh * Q * D * D)) := by
    rw [h_dot]
    ring
  have hB : ((F - rh * H) * Q ^ 2 * D ^ 2) = ((F - rh * H) * Q * Q * D * D) := by
    ring
  apply h_fire.trans
  constructor
  · intro h
    simpa [hA, hB] using h
  · intro h
    simpa [hA, hB] using h

/-- `0 ≤ x·x ≤ 2^(2E + d)` for coordinates at most `2^E`. -/
theorem AdversarialBco.Bit.Transfer.BLM.dot_self_le {d : ℕ} (x : Fin d → ℤ) (E : ℕ) (hx : ∀ j, |x j| ≤ 2 ^ E) :
    0 ≤ x ⬝ᵥ x ∧ x ⬝ᵥ x ≤ 2 ^ (2 * E + d) := by
  have h_lower : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    refine Finset.sum_nonneg (fun j _ => ?_)
    apply mul_self_nonneg
  have h_upper : x ⬝ᵥ x ≤ 2 ^ (2 * E + d) := by
    rw [dotProduct]
    have h_nonneg_two : ∀ (k : ℕ), 0 ≤ (2 : ℤ) ^ k := by
      intro k; apply pow_nonneg; norm_num
    have h_sq_bound (j : Fin d) : x j * x j ≤ ((2 : ℤ) ^ E) * ((2 : ℤ) ^ E) := by
      have hxj := hx j
      -- hxj : |x j| ≤ 2 ^ E, where 2 ^ E : ℕ coerced to ℤ
      have hxj' : |x j| ≤ (2 : ℤ) ^ E := by
        simpa using hxj
      calc
        x j * x j = |x j| * |x j| := by rw [abs_mul_abs_self]
        _ ≤ ((2 : ℤ) ^ E) * ((2 : ℤ) ^ E) := by
          have h_abs_nonneg := abs_nonneg (x j)
          have h_pow_nonneg := h_nonneg_two E
          nlinarith
    calc
      ∑ j : Fin d, x j * x j ≤ ∑ j : Fin d, ((2 : ℤ) ^ E) * ((2 : ℤ) ^ E) :=
        Finset.sum_le_sum (fun j _ => h_sq_bound j)
      _ = (Finset.card (Finset.univ : Finset (Fin d)) : ℤ) * (((2 : ℤ) ^ E) * ((2 : ℤ) ^ E)) := by
        simp [Finset.sum_const]
      _ = (d : ℤ) * (((2 : ℤ) ^ E) * ((2 : ℤ) ^ E)) := by simp
      _ ≤ ((2 : ℤ) ^ d) * (((2 : ℤ) ^ E) * ((2 : ℤ) ^ E)) := by
        have hd_nat : d ≤ 2 ^ d := Nat.le_of_lt (Nat.lt_two_pow_self (n := d))
        have hd : (d : ℤ) ≤ ((2 : ℤ) ^ d) := by
          exact_mod_cast hd_nat
        nlinarith [h_nonneg_two d, h_nonneg_two E]
      _ = ((2 : ℤ) ^ d) * ((2 : ℤ) ^ (2 * E)) := by ring
      _ = (2 : ℤ) ^ (d + 2 * E) := by rw [pow_add]
      _ = (2 : ℤ) ^ (2 * E + d) := by rw [add_comm]
  exact And.intro h_lower h_upper

/-- A point `x / 2^X` in the box of radius `N/D` (`(x·x) D² ≤ 2^(2X) N²`) has every coordinate `|x_j| D ≤ 2^X N`. -/
theorem AdversarialBco.Bit.Transfer.BLM.num_le_of_box {d : ℕ} (x : Fin d → ℤ) (D N : ℤ) (X : ℕ) (hD : 0 < D)
    (hN : 0 ≤ N) (h : (x ⬝ᵥ x) * D ^ 2 ≤ 2 ^ (2 * X) * N ^ 2) (j : Fin d) : |x j| * D ≤ 2 ^ X * N := by
  have hD_sq_nonneg : 0 ≤ D ^ 2 := by nlinarith
  have h_two_pow_nonneg : 0 ≤ (2 : ℤ) ^ X := by
    apply pow_nonneg (by norm_num) X
  have h_rhs_nonneg : 0 ≤ 2 ^ X * N := by
    nlinarith
  have h_single_le : (x j) ^ 2 ≤ x ⬝ᵥ x := by
    -- x ⬝ᵥ x is definitionally ∑ i, x i * x i
    simpa [sq, dotProduct] using Finset.single_le_sum (fun i _ => mul_self_nonneg (x i)) (Finset.mem_univ j)
  have h_mul : (x j) ^ 2 * D ^ 2 ≤ (x ⬝ᵥ x) * D ^ 2 := by
    nlinarith
  have h_sq : (x j) ^ 2 * D ^ 2 ≤ (2 : ℤ) ^ (2 * X) * N ^ 2 := by
    nlinarith
  have h_sq' : (|x j| * D) ^ 2 ≤ (2 ^ X * N) ^ 2 := by
    calc
      (|x j| * D) ^ 2 = (|x j|) ^ 2 * D ^ 2 := by ring
      _ = (x j) ^ 2 * D ^ 2 := by simp [sq_abs]
      _ ≤ (2 : ℤ) ^ (2 * X) * N ^ 2 := h_sq
      _ = ((2 : ℤ) ^ X) ^ 2 * N ^ 2 := by
        have h_pow : (2 : ℤ) ^ (2 * X) = ((2 : ℤ) ^ X) ^ 2 := by
          simpa [mul_comm] using pow_mul (2 : ℤ) X 2
        rw [h_pow]
      _ = (2 ^ X * N) ^ 2 := by ring
  have h_abs_nonneg : 0 ≤ |x j| * D := by
    have h_abs : 0 ≤ |x j| := abs_nonneg _
    nlinarith
  rcases abs_le_of_sq_le_sq' h_sq' h_rhs_nonneg with ⟨_, hle⟩
  exact hle

/-- The numerator of `rnd_p (u/v)`, `(2 u Q + v)/(2 v)`, is at most `2^(a + b + 1)` in absolute value for `|u| ≤ 2^a`,
`0 ≤ Q ≤ 2^b`, `v ≥ 1`. -/
theorem AdversarialBco.Bit.Transfer.BLM.rndZ_abs_pow (u v Q : ℤ) (a b : ℕ) (hv : 1 ≤ v) (hQ : 0 ≤ Q)
    (hu : |u| ≤ 2 ^ a) (hQb : Q ≤ 2 ^ b) : |rndZ u v Q| ≤ 2 ^ (a + b + 1) := by
  set N := u * Q + u * Q + v with hN
  set V := v + v with hV
  have hVpos : 0 < V := by
    rw [hV]
    have hvpos : 0 < v := by omega
    omega
  have hVne0 : V ≠ 0 := by linarith
  have hpow_nonneg : ∀ n : ℕ, 0 ≤ (2 : ℤ) ^ n := by
    intro n; exact pow_nonneg (by norm_num) n
  have hpow_pos : ∀ n : ℕ, 0 < (2 : ℤ) ^ n := by
    intro n; exact pow_pos (by norm_num) n
  have hpow_one_le : ∀ n : ℕ, 1 ≤ (2 : ℤ) ^ n := by
    intro n
    have h := hpow_pos n
    omega
  -- bound on |u*Q|
  have habs_uQ : |u * Q| ≤ (2 : ℤ) ^ (a + b) := by
    calc
      |u * Q| = |u| * |Q| := abs_mul u Q
      _ = |u| * Q := by rw [abs_of_nonneg hQ]
      _ ≤ (2 : ℤ) ^ a * Q := mul_le_mul_of_nonneg_right hu hQ
      _ ≤ (2 : ℤ) ^ a * (2 : ℤ) ^ b :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hQb) (hpow_nonneg a)
      _ = (2 : ℤ) ^ (a + b) := by rw [pow_add]
  -- bound N from below
  have hN_low : -(2 : ℤ) * (2 : ℤ) ^ (a + b) + v ≤ N := by
    rw [hN]
    have hneg : -((2 : ℤ) ^ (a + b)) ≤ u * Q := by
      have := abs_le.mp habs_uQ
      exact this.1
    nlinarith
  -- bound N from above
  have hN_high : N ≤ (2 : ℤ) * (2 : ℤ) ^ (a + b) + v := by
    rw [hN]
    have hpos : u * Q ≤ (2 : ℤ) ^ (a + b) := by
      have := abs_le.mp habs_uQ
      exact this.2
    nlinarith
  -- helper: 2*2^(a+b) = 2^(a+b+1)
  have h2pow : (2 : ℤ) * (2 : ℤ) ^ (a + b) = (2 : ℤ) ^ (a + b + 1) := by
    calc
      (2 : ℤ) * (2 : ℤ) ^ (a + b) = (2 : ℤ) ^ (a + b) * 2 := mul_comm _ _
      _ = (2 : ℤ) ^ (a + b + 1) := by rw [pow_succ]
  rw [abs_le]
  have hgoal : rndZ u v Q = N / V := by
    dsimp [rndZ, N, V]
  rw [hgoal]
  constructor
  · -- lower bound: -2^(a+b+1) ≤ N/V
    have h_lt : N < (N / V + 1) * V := Int.lt_ediv_add_one_mul_self N hVpos
    have h_lower : -(2 : ℤ) * (2 : ℤ) ^ (a + b) + v < (N / V + 1) * V := by
      linarith
    -- show that -(2*2^(a+b) + v) > -V*2^(a+b) - V = V*(-2^(a+b) - 1)
    have h_key : -(2 : ℤ) * (2 : ℤ) ^ (a + b) + v > V * (-((2 : ℤ) ^ (a + b)) - 1) := by
      rw [hV]
      have hp := hpow_one_le (a + b)
      nlinarith
    have h_lt2 : V * (-((2 : ℤ) ^ (a + b)) - 1) < (N / V + 1) * V := by
      linarith
    -- cancel V (V > 0)
    have h_lt3 : -((2 : ℤ) ^ (a + b)) - 1 < N / V + 1 := by
      -- rewrite RHS of h_lt2 to have V on the left
      have h_lt2' : V * (-((2 : ℤ) ^ (a + b)) - 1) < V * (N / V + 1) := by
        simpa [mul_comm] using h_lt2
      exact Int.lt_of_mul_lt_mul_left h_lt2' (by linarith)
    -- so N/V > -2^(a+b) - 2
    -- since N/V is integer, N/V ≥ -2^(a+b) - 1
    have h_le : -((2 : ℤ) ^ (a + b)) - 1 ≤ N / V := by
      omega
    -- now -2^(a+b) - 1 ≥ -2^(a+b+1) because 2^(a+b) ≥ 1
    have h_final : -((2 : ℤ) ^ (a + b + 1)) ≤ -((2 : ℤ) ^ (a + b)) - 1 := by
      have hp := hpow_one_le (a + b)
      rw [← h2pow]
      nlinarith
    linarith
  · -- upper bound: N/V ≤ 2^(a+b+1)
    have h_le_mul : N / V * V ≤ N := Int.ediv_mul_le N hVne0
    have h_mul_bound : N / V * V ≤ (2 : ℤ) * (2 : ℤ) ^ (a + b) + v := by
      linarith
    -- show 2*2^(a+b) + v ≤ V*(2^(a+b) + 1)
    have h_key : (2 : ℤ) * (2 : ℤ) ^ (a + b) + v ≤ V * ((2 : ℤ) ^ (a + b) + 1) := by
      rw [hV]
      have hp := hpow_one_le (a + b)
      nlinarith
    have h_mul_bound2 : N / V * V ≤ V * ((2 : ℤ) ^ (a + b) + 1) := by
      linarith
    -- cancel V (V > 0) using Int.le_of_mul_le_mul_right
    have h_le : N / V ≤ (2 : ℤ) ^ (a + b) + 1 :=
      Int.le_of_mul_le_mul_right (by simpa [mul_comm] using h_mul_bound2) hVpos
    -- now 2^(a+b) + 1 ≤ 2^(a+b+1) because 2^(a+b) ≥ 1
    have h_final : (2 : ℤ) ^ (a + b) + 1 ≤ (2 : ℤ) ^ (a + b + 1) := by
      have hp := hpow_one_le (a + b)
      rw [← h2pow]
      nlinarith
    linarith

/-- The linear term `b' - (η'/2) G'` of R11 is at most `2^(2E+1)` in absolute value when its numerators are. -/
theorem AdversarialBco.Bit.Transfer.BLM.wp_abs {d : ℕ} (F Q eh : ℤ) (bh Gh : Fin d → ℤ) (E : ℕ) (hF : 1 ≤ F)
    (hQ : 1 ≤ Q) (he : |eh| ≤ 2 ^ E) (hb : ∀ j, |bh j| ≤ 2 ^ E) (hG : ∀ j, |Gh j| ≤ 2 ^ E) (j : Fin d) :
    |((fun k => (bh k : ℚ) / Q) - ((eh : ℚ) / F / 2) • fun k => (Gh k : ℚ) / Q) j| ≤ 2 ^ (2 * E + 1) := by
  have hF' : (1 : ℚ) ≤ (F : ℚ) := by exact_mod_cast hF
  have hQ' : (1 : ℚ) ≤ (Q : ℚ) := by exact_mod_cast hQ
  have he' : (|eh| : ℚ) ≤ (2 ^ E : ℚ) := by exact_mod_cast he
  have hb' : ∀ j, (|bh j| : ℚ) ≤ (2 ^ E : ℚ) := by
    intro j
    exact_mod_cast hb j
  have hG' : ∀ j, (|Gh j| : ℚ) ≤ (2 ^ E : ℚ) := by
    intro j
    exact_mod_cast hG j
  have hQ_nonneg : (0 : ℚ) ≤ (Q : ℚ) := by linarith
  have hF_nonneg : (0 : ℚ) ≤ (F : ℚ) := by linarith
  have h_two_nonneg : (0 : ℚ) ≤ (2 : ℚ) := by norm_num
  -- simplify the goal
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- goal: |(bh j : ℚ) / (Q : ℚ) - ((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ))| ≤ 2 ^ (2 * E + 1)
  have h_tri := abs_sub ((bh j : ℚ) / (Q : ℚ)) (((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ)))
  apply le_trans h_tri
  -- goal: |(bh j : ℚ) / (Q : ℚ)| + |((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ))| ≤ 2 ^ (2 * E + 1)
  have h_term1 : |(bh j : ℚ) / (Q : ℚ)| ≤ (2 ^ E : ℚ) := by
    calc
      |(bh j : ℚ) / (Q : ℚ)| = |(bh j : ℚ)| / |(Q : ℚ)| := by rw [abs_div]
      _ = (|bh j| : ℚ) / |(Q : ℚ)| := by simp
      _ = (|bh j| : ℚ) / (Q : ℚ) := by rw [abs_of_nonneg hQ_nonneg]
      _ ≤ (|bh j| : ℚ) := div_le_self (abs_nonneg _) hQ'
      _ ≤ (2 ^ E : ℚ) := hb' j
  have h_term2 : |((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ))| ≤ (2 ^ (2 * E) : ℚ) / 2 := by
    calc
      |((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ))| =
          |(eh : ℚ) / (F : ℚ) / 2| * |(Gh j : ℚ) / (Q : ℚ)| := by rw [abs_mul]
      _ = (|(eh : ℚ)| / |(F : ℚ)| / |(2 : ℚ)|) * (|(Gh j : ℚ)| / |(Q : ℚ)|) := by simp only [abs_div]
      _ = (|(eh : ℚ)| / (F : ℚ) / 2) * (|(Gh j : ℚ)| / (Q : ℚ)) := by
        simp [abs_of_nonneg hF_nonneg, abs_of_nonneg hQ_nonneg]
      _ ≤ (|(eh : ℚ)| / 2) * |(Gh j : ℚ)| := by
        have h1 : |(eh : ℚ)| / (F : ℚ) ≤ |(eh : ℚ)| := div_le_self (abs_nonneg _) hF'
        have h2 : |(Gh j : ℚ)| / (Q : ℚ) ≤ |(Gh j : ℚ)| := div_le_self (abs_nonneg _) hQ'
        have h_nonneg_eh_divF : 0 ≤ |(eh : ℚ)| / (F : ℚ) := by positivity
        have h_nonneg_Gh_divQ : 0 ≤ |(Gh j : ℚ)| / (Q : ℚ) := by positivity
        have h_nonneg_half : 0 ≤ (1 : ℚ) / 2 := by norm_num
        calc
          (|(eh : ℚ)| / (F : ℚ) / 2) * (|(Gh j : ℚ)| / (Q : ℚ)) =
              ((|(eh : ℚ)| / (F : ℚ)) * (|(Gh j : ℚ)| / (Q : ℚ))) * (1 / 2) := by ring
          _ ≤ (|(eh : ℚ)| * |(Gh j : ℚ)|) * (1 / 2) := by
            nlinarith
          _ = (|(eh : ℚ)| / 2) * |(Gh j : ℚ)| := by ring
      _ = |(eh : ℚ)| * |(Gh j : ℚ)| / 2 := by ring
      _ = (|eh| : ℚ) * (|Gh j| : ℚ) / 2 := by simp
      _ ≤ (2 ^ E : ℚ) * (2 ^ E : ℚ) / 2 := by
        have h_eh : (|eh| : ℚ) ≤ (2 ^ E : ℚ) := he'
        have h_Gh : (|Gh j| : ℚ) ≤ (2 ^ E : ℚ) := hG' j
        have h_nonneg_eh_abs : 0 ≤ (|eh| : ℚ) := abs_nonneg _
        have h_nonneg_Gh_abs : 0 ≤ (|Gh j| : ℚ) := abs_nonneg _
        have h_nonneg_2E : 0 ≤ (2 ^ E : ℚ) := by positivity
        nlinarith
      _ = ((2 : ℚ) ^ E) * ((2 : ℚ) ^ E) / 2 := rfl
      _ = ((2 : ℚ) ^ (E + E)) / 2 := by rw [← pow_add]
      _ = ((2 : ℚ) ^ (2 * E)) / 2 := by rw [two_mul]
  have h_sum : |(bh j : ℚ) / (Q : ℚ)| + |((eh : ℚ) / (F : ℚ) / 2) * ((Gh j : ℚ) / (Q : ℚ))| ≤
      (2 ^ E : ℚ) + (2 ^ (2 * E) : ℚ) / 2 := by
    nlinarith
  have h_final : (2 ^ E : ℚ) + (2 ^ (2 * E) : ℚ) / 2 ≤ (2 : ℚ) ^ (2 * E + 1) := by
    have h_pow_le : (2 : ℚ) ^ E ≤ (2 : ℚ) ^ (2 * E) := by
      have h_exp_le : E ≤ 2 * E := by
        omega
      exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h_exp_le
    have h_nonneg_2pow : 0 ≤ (2 : ℚ) ^ (2 * E) := by positivity
    have h_add : (2 ^ E : ℚ) + (2 ^ (2 * E) : ℚ) / 2 ≤ (2 ^ (2 * E) : ℚ) + (2 ^ (2 * E) : ℚ) / 2 := by
      nlinarith
    have h_mid : (2 ^ (2 * E) : ℚ) + (2 ^ (2 * E) : ℚ) / 2 ≤ 2 * (2 ^ (2 * E) : ℚ) := by
      nlinarith
    have h_succ : 2 * (2 ^ (2 * E) : ℚ) = (2 : ℚ) ^ (2 * E + 1) := by
      rw [pow_succ, mul_comm]
    nlinarith
  nlinarith

/-- The numerator `μ̂_j Q² G - ŝ5 (Â Γ)_j D_μ` of `w_μ` (R13) is at most `2^(4E + d + 1)` in absolute value. -/
theorem AdversarialBco.Bit.Transfer.BLM.wn_abs {d : ℕ} (Q G Dm s5 : ℤ) (mu Γ : Fin d → ℤ)
    (Ah : Matrix (Fin d) (Fin d) ℤ) (E : ℕ) (hQ : |Q| ≤ 2 ^ E) (hG : |G| ≤ 2 ^ E) (hD : |Dm| ≤ 2 ^ E)
    (hs : |s5| ≤ 2 ^ E) (hm : ∀ j, |mu j| ≤ 2 ^ E) (hA : ∀ i j, |Ah i j| ≤ 2 ^ E) (hΓ : ∀ j, |Γ j| ≤ 2 ^ E)
    (j : Fin d) : |mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * Dm| ≤ 2 ^ (4 * E + d + 1) := by
  -- bound on |Q^2|
  have hQ2 : |Q ^ 2| ≤ ((2 : ℤ) ^ E) ^ 2 := by
    calc
      |Q ^ 2| = |Q| ^ 2 := abs_pow Q 2
      _ ≤ ((2 : ℤ) ^ E) ^ 2 := by
        have hQ_nonneg : 0 ≤ |Q| := abs_nonneg _
        have h2_nonneg : 0 ≤ (2 : ℤ) ^ E := pow_nonneg (by norm_num) E
        nlinarith
  -- bound on |mu j * Q^2 * G|
  have h_term1 : |mu j * Q ^ 2 * G| ≤ (2 : ℤ) ^ (4 * E) := by
    calc
      |mu j * Q ^ 2 * G| = |mu j| * |Q ^ 2| * |G| := by simp [abs_mul]
      _ ≤ (2 ^ E) * (((2 : ℤ) ^ E) ^ 2) * (2 ^ E) := by
        have h_nonneg_mu : 0 ≤ |mu j| := abs_nonneg _
        have h_nonneg_Q2 : 0 ≤ |Q ^ 2| := abs_nonneg _
        have h_nonneg_G : 0 ≤ |G| := abs_nonneg _
        have h_nonneg_2E : 0 ≤ (2 : ℤ) ^ E := pow_nonneg (by norm_num) E
        have h_nonneg_2E_sq : 0 ≤ ((2 : ℤ) ^ E) ^ 2 := pow_nonneg h_nonneg_2E 2
        have h_nonneg_prod : 0 ≤ (2 ^ E) * (((2 : ℤ) ^ E) ^ 2) := mul_nonneg h_nonneg_2E h_nonneg_2E_sq
        have h1 : |mu j| * |Q ^ 2| ≤ (2 ^ E) * (((2 : ℤ) ^ E) ^ 2) :=
          mul_le_mul (hm j) hQ2 h_nonneg_Q2 h_nonneg_2E
        have h2 : (|mu j| * |Q ^ 2|) * |G| ≤ ((2 ^ E) * (((2 : ℤ) ^ E) ^ 2)) * (2 ^ E) :=
          mul_le_mul h1 hG h_nonneg_G h_nonneg_prod
        simpa [mul_assoc] using h2
      _ = (2 : ℤ) ^ (4 * E) := by
        ring
  -- bound on |(Ah *ᵥ Γ) j|
  have h_sum : |(Ah *ᵥ Γ) j| ≤ (d : ℤ) * ((2 : ℤ) ^ (2 * E)) := by
    calc
      |(Ah *ᵥ Γ) j| = |∑ k : Fin d, Ah j k * Γ k| := rfl
      _ ≤ ∑ k : Fin d, |Ah j k * Γ k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin d, (|Ah j k| * |Γ k|) := by simp [abs_mul]
      _ ≤ ∑ k : Fin d, ((2 : ℤ) ^ E * (2 : ℤ) ^ E) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h_nonneg_A : 0 ≤ |Ah j k| := abs_nonneg _
        have h_nonneg_Γ : 0 ≤ |Γ k| := abs_nonneg _
        have h_nonneg_2E : 0 ≤ (2 : ℤ) ^ E := pow_nonneg (by norm_num) E
        gcongr
        · exact hA j k
        · exact hΓ k
      _ = (Finset.card (Finset.univ : Finset (Fin d))) • ((2 : ℤ) ^ E * (2 : ℤ) ^ E) := by
        simp [Finset.sum_const]
      _ = (d : ℤ) * ((2 : ℤ) ^ E * (2 : ℤ) ^ E) := by simp
      _ = (d : ℤ) * ((2 : ℤ) ^ (2 * E)) := by
        rw [← pow_add, two_mul]
  -- bound on |s5 * (Ah *ᵥ Γ) j * Dm|
  have h_term2 : |s5 * (Ah *ᵥ Γ) j * Dm| ≤ (2 : ℤ) ^ (4 * E + d) := by
    calc
      |s5 * (Ah *ᵥ Γ) j * Dm| = |s5| * |(Ah *ᵥ Γ) j| * |Dm| := by simp [abs_mul]
      _ ≤ (2 ^ E) * ((d : ℤ) * ((2 : ℤ) ^ (2 * E))) * (2 ^ E) := by
        have h_nonneg_s5 : 0 ≤ |s5| := abs_nonneg _
        have h_nonneg_Dm : 0 ≤ |Dm| := abs_nonneg _
        have h_nonneg_sum : 0 ≤ |(Ah *ᵥ Γ) j| := abs_nonneg _
        have h_nonneg_2E : 0 ≤ (2 : ℤ) ^ E := pow_nonneg (by norm_num) E
        have h_nonneg_d_2E : 0 ≤ (d : ℤ) * ((2 : ℤ) ^ (2 * E)) := by
          have hd_nonneg : 0 ≤ (d : ℤ) := Nat.cast_nonneg _
          have h2E_nonneg : 0 ≤ (2 : ℤ) ^ (2 * E) := pow_nonneg (by norm_num) (2 * E)
          nlinarith
        have h_nonneg_prod : 0 ≤ (2 ^ E) * ((d : ℤ) * ((2 : ℤ) ^ (2 * E))) :=
          mul_nonneg h_nonneg_2E h_nonneg_d_2E
        have h1 : |s5| * |(Ah *ᵥ Γ) j| ≤ (2 ^ E) * ((d : ℤ) * ((2 : ℤ) ^ (2 * E))) :=
          mul_le_mul hs h_sum h_nonneg_sum h_nonneg_2E
        have h2 : (|s5| * |(Ah *ᵥ Γ) j|) * |Dm| ≤ ((2 ^ E) * ((d : ℤ) * ((2 : ℤ) ^ (2 * E)))) * (2 ^ E) :=
          mul_le_mul h1 hD h_nonneg_Dm h_nonneg_prod
        simpa [mul_assoc] using h2
      _ = (d : ℤ) * ((2 : ℤ) ^ (2 * E)) * (2 ^ E) * (2 ^ E) := by ring
      _ = (d : ℤ) * ((2 : ℤ) ^ (2 * E + E + E)) := by
        rw [pow_add, pow_add]
        ring
      _ = (d : ℤ) * ((2 : ℤ) ^ (4 * E)) := by ring
      _ ≤ ((2 : ℤ) ^ d) * ((2 : ℤ) ^ (4 * E)) := by
        have hd_le_2d : (d : ℤ) ≤ (2 : ℤ) ^ d := by
          have h := Nat.lt_two_pow_self (n := d)
          exact mod_cast h.le
        have h_nonneg_2d : 0 ≤ (2 : ℤ) ^ d := pow_nonneg (by norm_num) d
        have h_nonneg_4E : 0 ≤ (2 : ℤ) ^ (4 * E) := pow_nonneg (by norm_num) (4 * E)
        gcongr
      _ = (2 : ℤ) ^ (d + 4 * E) := by rw [pow_add]
      _ = (2 : ℤ) ^ (4 * E + d) := by rw [add_comm]
  -- combine using triangle inequality
  calc
    |mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * Dm| ≤ |mu j * Q ^ 2 * G| + |s5 * (Ah *ᵥ Γ) j * Dm| :=
      abs_sub _ _
    _ ≤ (2 : ℤ) ^ (4 * E) + (2 : ℤ) ^ (4 * E + d) := by
      have h_nonneg_term1 : 0 ≤ (2 : ℤ) ^ (4 * E) := pow_nonneg (by norm_num) (4 * E)
      have h_nonneg_term2 : 0 ≤ (2 : ℤ) ^ (4 * E + d) := pow_nonneg (by norm_num) (4 * E + d)
      nlinarith
    _ ≤ (2 : ℤ) ^ (4 * E + d) + (2 : ℤ) ^ (4 * E + d) := by
      have h_le : (2 : ℤ) ^ (4 * E) ≤ (2 : ℤ) ^ (4 * E + d) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_add_right (4 * E) d)
      nlinarith
    _ = 2 * (2 : ℤ) ^ (4 * E + d) := by ring
    _ = (2 : ℤ) ^ (4 * E + d) * 2 := by ring
    _ = (2 : ℤ) ^ (4 * E + d + 1) := by rw [pow_succ]

/-- The two sides of R12's test on the machine are at most `2^(7E + 3d + 3)` and `2^(6E + 1)` in absolute value. -/
theorem AdversarialBco.Bit.Transfer.BLM.r12_abs {d : ℕ} (F Q D H eh lh kh rh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Gh bh x : Fin d → ℤ) (E : ℕ) (hF : |F| ≤ 2 ^ E) (hQ : |Q| ≤ 2 ^ E) (hD : |D| ≤ 2 ^ E) (hH : |H| ≤ 2 ^ E)
    (he : |eh| ≤ 2 ^ E) (hl : |lh| ≤ 2 ^ E) (hk : |kh| ≤ 2 ^ E) (hr : |rh| ≤ 2 ^ E)
    (hB : ∀ i j, |Bh i j| ≤ 2 ^ E) (hG : ∀ j, |Gh j| ≤ 2 ^ E) (hb : ∀ j, |bh j| ≤ 2 ^ E) (hx : ∀ j, |x j| ≤ 2 ^ E) :
    |eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
        F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D + kh * Q * D * D)| ≤
      2 ^ (7 * E + 3 * d + 3) ∧
    |(F - rh * H) * Q * Q * D * D| ≤ 2 ^ (6 * E + 1) := by
  set T := (2 : ℤ)^E with hTdef
  have hTnonneg : (0 : ℤ) ≤ T := by
    have h := pow_pos (by norm_num : (0 : ℤ) < 2) E
    omega
  have hTpos : (1 : ℤ) ≤ T := by
    have h := pow_pos (by norm_num : (0 : ℤ) < 2) E
    omega
  -- rewrite hypotheses in terms of T
  have hF' : |F| ≤ T := by rw [hTdef]; exact hF
  have hQ' : |Q| ≤ T := by rw [hTdef]; exact hQ
  have hD' : |D| ≤ T := by rw [hTdef]; exact hD
  have hH' : |H| ≤ T := by rw [hTdef]; exact hH
  have he' : |eh| ≤ T := by rw [hTdef]; exact he
  have hl' : |lh| ≤ T := by rw [hTdef]; exact hl
  have hk' : |kh| ≤ T := by rw [hTdef]; exact hk
  have hr' : |rh| ≤ T := by rw [hTdef]; exact hr
  have hB' (i j) : |Bh i j| ≤ T := by rw [hTdef]; exact hB i j
  have hG' (j) : |Gh j| ≤ T := by rw [hTdef]; exact hG j
  have hb' (j) : |bh j| ≤ T := by rw [hTdef]; exact hb j
  have hx' (j) : |x j| ≤ T := by rw [hTdef]; exact hx j
  -- helper: |a + b| ≤ |a| + |b|
  have h_abs_add (a b : ℤ) : |a + b| ≤ |a| + |b| := by
    calc
      |a + b| = |a - (-b)| := by simp
      _ ≤ |a| + |-b| := abs_sub _ _
      _ = |a| + |b| := by simp
  -- bound for |Gh ⬝ᵥ x|
  have hG_dot : |Gh ⬝ᵥ x| ≤ (d : ℤ) * T^2 := by
    calc
      |Gh ⬝ᵥ x| = |∑ j, Gh j * x j| := rfl
      _ ≤ ∑ j, |Gh j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |Gh j| * |x j| := by simp [abs_mul]
      _ ≤ ∑ j : Fin d, T * T := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul (hG' j) (hx' j) (abs_nonneg _) hTnonneg
      _ = (d : ℤ) * (T * T) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = (d : ℤ) * T^2 := by ring
  -- bound for |bh ⬝ᵥ x|
  have hb_dot : |bh ⬝ᵥ x| ≤ (d : ℤ) * T^2 := by
    calc
      |bh ⬝ᵥ x| = |∑ j, bh j * x j| := rfl
      _ ≤ ∑ j, |bh j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |bh j| * |x j| := by simp [abs_mul]
      _ ≤ ∑ j : Fin d, T * T := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul (hb' j) (hx' j) (abs_nonneg _) hTnonneg
      _ = (d : ℤ) * (T * T) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = (d : ℤ) * T^2 := by ring
  -- bound for components of Bhᵀ *ᵥ x
  have h_mulVec_bound (j : Fin d) : |(Bhᵀ *ᵥ x) j| ≤ (d : ℤ) * T^2 := by
    calc
      |(Bhᵀ *ᵥ x) j| = |∑ k, Bhᵀ j k * x k| := rfl
      _ ≤ ∑ k, |Bhᵀ j k * x k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |Bhᵀ j k| * |x k| := by simp [abs_mul]
      _ = ∑ k, |Bh k j| * |x k| := by simp [Matrix.transpose_apply]
      _ ≤ ∑ k : Fin d, T * T := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul (hB' k j) (hx' k) (abs_nonneg _) hTnonneg
      _ = (d : ℤ) * (T * T) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = (d : ℤ) * T^2 := by ring
  -- bound for |(Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x)|
  have h_dot_self_bound : |(Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x)| ≤ (d : ℤ)^3 * T^4 := by
    have h_comp (j : Fin d) : |(Bhᵀ *ᵥ x) j| ≤ (d : ℤ) * T^2 := h_mulVec_bound j
    have hd_nonneg : 0 ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le _
    have hT_sq_nonneg : 0 ≤ T^2 := pow_two_nonneg T
    have h_comp_nonneg : 0 ≤ (d : ℤ) * T^2 := by nlinarith
    calc
      |(Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x)| = |∑ j, (Bhᵀ *ᵥ x) j * (Bhᵀ *ᵥ x) j| := rfl
      _ ≤ ∑ j, |(Bhᵀ *ᵥ x) j * (Bhᵀ *ᵥ x) j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(Bhᵀ *ᵥ x) j| * |(Bhᵀ *ᵥ x) j| := by simp [abs_mul]
      _ ≤ ∑ j : Fin d, ((d : ℤ) * T^2) * ((d : ℤ) * T^2) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul (h_comp j) (h_comp j) (abs_nonneg _) h_comp_nonneg
      _ = (d : ℤ) * (((d : ℤ) * T^2) * ((d : ℤ) * T^2)) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = (d : ℤ)^3 * T^4 := by ring
  -- bound (d : ℤ) ≤ 2^d
  have h_d_bound : (d : ℤ) ≤ (2 : ℤ)^d := by
    have h := Nat.lt_two_pow_self (n := d)
    exact_mod_cast h.le
  -- bound each of the 7 terms by 2^(7E+3d)
  have h_term1 : |eh*lh*D*Q*D*H| ≤ (2 : ℤ)^(7*E + 3*d) := by
    calc
      |eh*lh*D*Q*D*H| = |eh| * |lh| * |D| * |Q| * |D| * |H| := by simp [abs_mul]
      _ ≤ T * T * T * T * T * T := by
        gcongr
      _ = T^6 := by ring
      _ ≤ T^7 := by
        calc
          T^6 = T^6 * 1 := by ring
          _ ≤ T^6 * T := by
            apply mul_le_mul_of_nonneg_left hTpos (by positivity)
          _ = T^7 := by ring
      _ = ((2 : ℤ)^E)^7 := by rw [hTdef]
      _ = (2 : ℤ)^(7*E) := by simp [pow_mul, mul_comm]
      _ ≤ (2 : ℤ)^(7*E) * (2 : ℤ)^(3*d) := by
        have hpos : 0 ≤ (2 : ℤ)^(7*E) := pow_nonneg (by norm_num) _
        have hpos' : 1 ≤ (2 : ℤ)^(3*d) := by
          have := pow_pos (by norm_num : (0 : ℤ) < 2) (3*d)
          omega
        nlinarith
      _ = (2 : ℤ)^(7*E + 3*d) := by rw [pow_add]
  have h_term2 : |eh*(Gh⬝ᵥx)*Q*D*H| ≤ (2 : ℤ)^(7*E + 3*d) := by
    calc
      |eh*(Gh⬝ᵥx)*Q*D*H| = |eh| * |Gh⬝ᵥx| * |Q| * |D| * |H| := by simp [abs_mul]
      _ ≤ T * ((d : ℤ) * T^2) * T * T * T := by
        gcongr
      _ = (d : ℤ) * T^6 := by ring
      _ ≤ (2 : ℤ)^d * T^6 := by
        apply mul_le_mul_of_nonneg_right h_d_bound (by positivity)
      _ = (2 : ℤ)^d * ((2 : ℤ)^E)^6 := by rw [hTdef]
      _ = (2 : ℤ)^(d + 6*E) := by simp [pow_add, pow_mul, mul_comm]
      _ ≤ (2 : ℤ)^(7*E + 3*d) := by
        refine pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ?_
        omega
  have h_term3 : |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| ≤ (2 : ℤ)^(7*E + 3*d) := by
    calc
      |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| = |F| * |H| * |(Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)| := by simp [abs_mul]
      _ ≤ T * T * ((d : ℤ)^3 * T^4) := by
        gcongr
      _ = (d : ℤ)^3 * T^6 := by ring
      _ ≤ ((2 : ℤ)^d)^3 * T^6 := by
        have hd_nonneg : 0 ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le _
        have h2d_nonneg : 0 ≤ (2 : ℤ)^d := pow_nonneg (by norm_num) _
        have h_cube : (d : ℤ)^3 ≤ ((2 : ℤ)^d)^3 := by
          have hd_nonneg : 0 ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le _
          have h2d_nonneg : 0 ≤ (2 : ℤ)^d := pow_nonneg (by norm_num) _
          have hd_sq_nonneg : 0 ≤ (d : ℤ)^2 := pow_nonneg hd_nonneg 2
          have h1 : (d : ℤ)^2 ≤ ((2 : ℤ)^d)^2 := by
            have := mul_le_mul h_d_bound h_d_bound hd_nonneg h2d_nonneg
            simpa [sq] using this
          have h2 : (d : ℤ)^3 ≤ ((2 : ℤ)^d)^3 := by
            have := mul_le_mul h_d_bound h1 hd_sq_nonneg h2d_nonneg
            simpa [pow_succ, pow_succ, mul_assoc] using this
          exact h2
        exact mul_le_mul_of_nonneg_right h_cube (by positivity)
      _ = (2 : ℤ)^(3*d) * T^6 := by simp [pow_mul, mul_comm]
      _ = (2 : ℤ)^(3*d) * ((2 : ℤ)^E)^6 := by rw [hTdef]
      _ = (2 : ℤ)^(3*d) * (2 : ℤ)^(6*E) := by simp [pow_mul, mul_comm]
      _ = (2 : ℤ)^(6*E + 3*d) := by rw [add_comm, pow_add]
      _ ≤ (2 : ℤ)^(7*E + 3*d) := by
        refine pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ?_
        omega
  have h_term4 : |F*H*(bh⬝ᵥx)*Q*D| ≤ (2 : ℤ)^(7*E + 3*d) := by
    calc
      |F*H*(bh⬝ᵥx)*Q*D| = |F| * |H| * |bh⬝ᵥx| * |Q| * |D| := by simp [abs_mul]
      _ ≤ T * T * ((d : ℤ) * T^2) * T * T := by
        gcongr
      _ = (d : ℤ) * T^6 := by ring
      _ ≤ (2 : ℤ)^d * T^6 := by
        apply mul_le_mul_of_nonneg_right h_d_bound (by positivity)
      _ = (2 : ℤ)^d * ((2 : ℤ)^E)^6 := by rw [hTdef]
      _ = (2 : ℤ)^(d + 6*E) := by simp [pow_add, pow_mul, mul_comm]
      _ ≤ (2 : ℤ)^(7*E + 3*d) := by
        refine pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ?_
        omega
  have h_term5 : |F*H*kh*Q*D*D| ≤ (2 : ℤ)^(7*E + 3*d) := by
    calc
      |F*H*kh*Q*D*D| = |F| * |H| * |kh| * |Q| * |D| * |D| := by simp [abs_mul]
      _ ≤ T * T * T * T * T * T := by
        gcongr
      _ = T^6 := by ring
      _ ≤ T^7 := by
        calc
          T^6 = T^6 * 1 := by ring
          _ ≤ T^6 * T := by
            apply mul_le_mul_of_nonneg_left hTpos (by positivity)
          _ = T^7 := by ring
      _ = ((2 : ℤ)^E)^7 := by rw [hTdef]
      _ = (2 : ℤ)^(7*E) := by simp [pow_mul, mul_comm]
      _ ≤ (2 : ℤ)^(7*E) * (2 : ℤ)^(3*d) := by
        have hpos : 0 ≤ (2 : ℤ)^(7*E) := pow_nonneg (by norm_num) _
        have hpos' : 1 ≤ (2 : ℤ)^(3*d) := by
          have := pow_pos (by norm_num : (0 : ℤ) < 2) (3*d)
          omega
        nlinarith
      _ = (2 : ℤ)^(7*E + 3*d) := by rw [pow_add]
  -- now combine all 7 terms using triangle inequality
  have h_first : |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D - 2*F*H*kh*Q*D*D| ≤
      2 ^ (7 * E + 3 * d + 3) := by
    -- rewrite the target as 2^(7E+3d+3) = 2^3 * 2^(7E+3d) = 8 * 2^(7E+3d)
    have h_target : (2 : ℤ)^(7*E + 3*d + 3) = (8 : ℤ) * (2 : ℤ)^(7*E + 3*d) := by
      calc
        (2 : ℤ)^(7*E + 3*d + 3) = (2 : ℤ)^(7*E + 3*d) * (2 : ℤ)^3 := by rw [pow_add]
        _ = (2 : ℤ)^(7*E + 3*d) * 8 := by norm_num
        _ = (8 : ℤ) * (2 : ℤ)^(7*E + 3*d) := by ring
    rw [h_target]
    -- now we need to show |sum of 5 terms| ≤ 8 * 2^(7E+3d)
    -- we have 7 individual bounds, each ≤ 2^(7E+3d)
    -- using triangle inequality, the sum of absolute values ≤ 7 * 2^(7E+3d) ≤ 8 * 2^(7E+3d)
    have h_sum_abs : |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| +
        |2*F*H*(bh⬝ᵥx)*Q*D| + |2*F*H*kh*Q*D*D| ≤ (7 : ℤ) * (2 : ℤ)^(7*E + 3*d) := by
      have h1 : |eh*lh*D*Q*D*H| ≤ (2 : ℤ)^(7*E + 3*d) := h_term1
      have h2 : |eh*(Gh⬝ᵥx)*Q*D*H| ≤ (2 : ℤ)^(7*E + 3*d) := h_term2
      have h3 : |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| ≤ (2 : ℤ)^(7*E + 3*d) := h_term3
      have h4 : |2*F*H*(bh⬝ᵥx)*Q*D| = 2 * |F*H*(bh⬝ᵥx)*Q*D| := by
        simp [abs_mul, mul_assoc]
      have h4' : |F*H*(bh⬝ᵥx)*Q*D| ≤ (2 : ℤ)^(7*E + 3*d) := h_term4
      have h5 : |2*F*H*kh*Q*D*D| = 2 * |F*H*kh*Q*D*D| := by
        simp [abs_mul, mul_assoc]
      have h5' : |F*H*kh*Q*D*D| ≤ (2 : ℤ)^(7*E + 3*d) := h_term5
      calc
        |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| +
            |2*F*H*(bh⬝ᵥx)*Q*D| + |2*F*H*kh*Q*D*D| =
          |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| +
            (2 * |F*H*(bh⬝ᵥx)*Q*D|) + (2 * |F*H*kh*Q*D*D|) := by
          simp [h4, h5]
        _ ≤ (2 : ℤ)^(7*E + 3*d) + (2 : ℤ)^(7*E + 3*d) + (2 : ℤ)^(7*E + 3*d) +
            (2 * (2 : ℤ)^(7*E + 3*d)) + (2 * (2 : ℤ)^(7*E + 3*d)) := by
          gcongr
        _ = (7 : ℤ) * (2 : ℤ)^(7*E + 3*d) := by ring
    -- now use triangle inequality to relate |sum| to sum of absolute values
    have h_triangle : |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D -
          2*F*H*kh*Q*D*D| ≤
        |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
          |2*F*H*kh*Q*D*D| := by
      calc
        |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D - 2*F*H*kh*Q*D*D| ≤
          |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| :=
          abs_sub _ _
        _ ≤ (|eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D|) +
            |2*F*H*kh*Q*D*D| := by
          gcongr
          have h := h_abs_add (eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))) (2*F*H*(bh⬝ᵥx)*Q*D)
          simpa [sub_eq_add_neg, add_assoc] using h
        _ = |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| := by ring
        _ ≤ (|eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))|) + |2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| := by
          gcongr
          simpa [sub_eq_add_neg, add_assoc] using
            abs_sub (eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H) (F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)))
        _ = |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| := by ring
        _ ≤ (|eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H|) + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| := by
          gcongr
          simpa [sub_eq_add_neg] using abs_sub (eh*lh*D*Q*D*H) (eh*(Gh⬝ᵥx)*Q*D*H)
        _ = |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
            |2*F*H*kh*Q*D*D| := by ring
    -- combine triangle inequality with sum bound
    calc
      |eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D - 2*F*H*kh*Q*D*D| ≤
        |eh*lh*D*Q*D*H| + |eh*(Gh⬝ᵥx)*Q*D*H| + |F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx))| + |2*F*H*(bh⬝ᵥx)*Q*D| +
          |2*F*H*kh*Q*D*D| := h_triangle
      _ ≤ (7 : ℤ) * (2 : ℤ)^(7*E + 3*d) := h_sum_abs
      _ ≤ (8 : ℤ) * (2 : ℤ)^(7*E + 3*d) := by
        gcongr
        norm_num
  -- second conjunct
  have hT_sq : T ≤ T^2 := by
    calc
      T = T * 1 := by ring
      _ ≤ T * T := mul_le_mul_of_nonneg_left hTpos hTnonneg
      _ = T^2 := by ring
  have h_second : |(F - rh * H) * Q * Q * D * D| ≤ 2 ^ (6 * E + 1) := by
    calc
      |(F - rh * H) * Q * Q * D * D| = |F - rh * H| * |Q| * |Q| * |D| * |D| := by simp [abs_mul]
      _ ≤ (|F| + |rh| * |H|) * T * T * T * T := by
        have h_sub : |F - rh * H| ≤ |F| + |rh| * |H| := by
          calc
            |F - rh * H| ≤ |F| + |rh * H| := abs_sub _ _
            _ = |F| + |rh| * |H| := by simp [abs_mul]
        gcongr
      _ ≤ (T + T * T) * T * T * T * T := by
        gcongr
      _ = (T + T^2) * T^4 := by ring
      _ ≤ (T^2 + T^2) * T^4 := by
        gcongr
      _ = 2 * T^2 * T^4 := by ring
      _ = 2 * T^6 := by ring
      _ = 2 * ((2 : ℤ)^E)^6 := by rw [hTdef]
      _ = 2 * (2 : ℤ)^(6*E) := by simp [pow_mul, mul_comm]
      _ = (2 : ℤ)^(6*E + 1) := by
        rw [pow_add, pow_one]
        ring
  -- expand the original expression to match h_first
  have h_expr : eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
      F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D + kh * Q * D * D) =
      eh*lh*D*Q*D*H - eh*(Gh⬝ᵥx)*Q*D*H - F*H*((Bhᵀ*ᵥx)⬝ᵥ(Bhᵀ*ᵥx)) + 2*F*H*(bh⬝ᵥx)*Q*D - 2*F*H*kh*Q*D*D := by
    ring
  rw [h_expr]
  exact And.intro h_first h_second
