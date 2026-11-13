/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Generic bounds for the magnitudes of BL's state

Facts on `ℚ` and `ℝ` that `MagBL` uses: the inverse of a grid point, the fold `foldl max 0`, `(2B)^{1/2} ≤ B`, the
products `Av` and `v·w` of bounded entries, the inverse of a positive `b - a·(x/D_S)`; PARAM's magnitude linear in the
sizes of `d` and `n`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

theorem grid_inv_abs (z : ℤ) (k : ℕ) : |((z : ℚ) / 2 ^ k)⁻¹| ≤ 2 ^ k := by
  by_cases hz : z = 0
  · rw [hz]
    simp
  · have habs : (1 : ℚ) ≤ |(z : ℚ)| := by
      have h := Int.one_le_abs hz
      exact_mod_cast h
    have hpos : (0 : ℚ) ≤ (2 : ℚ) ^ k := by
      apply pow_nonneg
      norm_num
    calc
      |((z : ℚ) / 2 ^ k)⁻¹| = |(2 ^ k : ℚ) / (z : ℚ)| := by rw [inv_div]
      _ = |(2 ^ k : ℚ)| / |(z : ℚ)| := by rw [abs_div]
      _ = (2 ^ k : ℚ) / |(z : ℚ)| := by
        simp
      _ ≤ (2 ^ k : ℚ) / (1 : ℚ) :=
        div_le_div_of_nonneg_left hpos (by norm_num) habs
      _ = (2 ^ k : ℚ) := by simp
      _ ≤ 2 ^ k := le_rfl

theorem foldlMax_spec (l : List ℚ) :
    0 ≤ l.foldl max 0 ∧ (∀ x ∈ l, x ≤ l.foldl max 0) ∧
      ∀ S : ℚ, 0 ≤ S → (∀ x ∈ l, x ≤ S) → l.foldl max 0 ≤ S := by
  have h_aux : ∀ (l : List ℚ) (a : ℚ), a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧
      ∀ S : ℚ, a ≤ S → (∀ x ∈ l, x ≤ S) → l.foldl max a ≤ S := by
    intro l a
    induction' l with h t ih generalizing a
    · simp
    · rw [List.foldl_cons]
      rcases ih (max a h) with ⟨hle, hall, hS⟩
      have ha_max : a ≤ max a h := le_max_left _ _
      have hh_max : h ≤ max a h := le_max_right _ _
      refine ⟨?_, ?_, ?_⟩
      · exact le_trans ha_max hle
      · intro x hx
        have hx_cases := (List.mem_cons.mp hx)
        rcases hx_cases with (rfl | hx')
        · exact le_trans hh_max hle
        · exact hall x hx'
      · intro S haS hxS
        have hmaxS : max a h ≤ S := max_le haS (hxS h (by simp))
        apply hS S hmaxS
        intro x hx'
        exact hxS x (by simp [hx'])
  exact h_aux l 0

theorem sqrt_two_mul_le (B : ℕ) (hB : 2 ≤ B) : Real.sqrt (2 * B) ≤ B := by
  have hB' : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hB_nonneg : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast Nat.zero_le B
  have hsq : (2 : ℝ) * (B : ℝ) ≤ (B : ℝ) ^ 2 := by
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · exact hB_nonneg
  · simpa [Nat.cast_mul, Nat.cast_ofNat] using hsq

theorem mulVecQ_abs_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) (a b : ℚ)
    (hA : ∀ i j, |A i j| ≤ a) (hv : ∀ j, |v j| ≤ b) (i : Fin d) : |Matrix.mulVec A v i| ≤ d * a * b := by
  by_cases hd : Nonempty (Fin d)
  · obtain ⟨j₀⟩ := hd
    have ha : 0 ≤ a := by
      have h0 := abs_nonneg (A i j₀)
      have h1 := hA i j₀
      linarith
    calc
      |Matrix.mulVec A v i| = |∑ j : Fin d, A i j * v j| := by rw [Matrix.mulVec_apply_eq_sum]
      _ ≤ ∑ j : Fin d, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin d, |A i j| * |v j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul]
      _ ≤ (Finset.card (Finset.univ : Finset (Fin d))) • (a * b) :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ =>
          mul_le_mul (hA i j) (hv j) (abs_nonneg _) ha
      _ = d • (a * b) := by simp
      _ = (d : ℚ) * (a * b) := by simp
      _ = d * a * b := by ring
  · have : IsEmpty (Fin d) := not_nonempty_iff.mp hd
    exact (this.false i).elim

theorem dotQ_abs_le {d : ℕ} (v w : Fin d → ℚ) (a b : ℚ) (hv : ∀ j, |v j| ≤ a)
    (hw : ∀ j, |w j| ≤ b) : |v ⬝ᵥ w| ≤ d * a * b := by
  calc
    |v ⬝ᵥ w| = |∑ j, v j * w j| := by
      rw [dotProduct]
    _ ≤ ∑ j, |v j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |v j| * |w j| := by
      simp [abs_mul]
    _ ≤ ∑ j : Fin d, a * b := by
      refine Finset.sum_le_sum ?_
      intro j _
      have ha : 0 ≤ a := le_trans (abs_nonneg _) (hv j)
      have hc : 0 ≤ |w j| := abs_nonneg _
      exact mul_le_mul (hv j) (hw j) hc ha
    _ = (Finset.card (Finset.univ : Finset (Fin d))) • (a * b) := by
      simp [Finset.sum_const]
    _ = d • (a * b) := by simp
    _ = (d : ℚ) * (a * b) := by simp [nsmul_eq_mul]
    _ = d * a * b := by ring

/-- The magnitude `q + pF + 2 gsm_prec B` of PARAM is linear in the sizes of `d` and `n`. -/
theorem parG_bound (d n le ld p q pF B : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hle : le = (15 * 2 ^ 17 * d ^ 3 * n ^ 4).size) (hld : ld = d.size) (hp : p = 10 * le + 16 * ld + 160)
    (hq : q = p + 2 * le.size + 24) (hpF : pF = p + 2 * le + 4 * ld + 40) (hB : B = 2 * (p + (n * (d + 2)).size + 2)) :
    q + pF + 2 * (B + 2 * B.size + 4) ≤ 4000 * (d.size + n.size + 1) := by
  -- helper lemma: size of product is at most sum of sizes
  have h_size_mul (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
    have ha : a < 2 ^ Nat.size a := Nat.lt_size_self a
    have hb : b < 2 ^ Nat.size b := Nat.lt_size_self b
    have h : a * b < 2 ^ (Nat.size a + Nat.size b) := by
      calc
        a * b < 2 ^ Nat.size a * 2 ^ Nat.size b := Nat.mul_lt_mul_of_lt_of_lt ha hb
        _ = 2 ^ (Nat.size a + Nat.size b) := by rw [Nat.pow_add]
    exact (Nat.size_le.2 h)
  -- helper lemma: size of a is at most a
  have h_size_le (a : ℕ) : Nat.size a ≤ a := by
    have h : a < 2 ^ a := Nat.lt_two_pow_self (n := a)
    exact (Nat.size_le.2 h)
  -- compute size of 15 * 2^17
  have h_size_const : Nat.size (15 * 2 ^ 17) = 21 := by decide
  -- bound le
  have hle_bound : le ≤ 21 + 3 * d.size + 4 * n.size := by
    rw [hle]
    have h_d3 : Nat.size (d ^ 3) ≤ 3 * d.size := by
      have hd_lt : d < 2 ^ d.size := Nat.lt_size_self d
      have h_pow : d ^ 3 < (2 ^ d.size) ^ 3 := Nat.pow_lt_pow_left hd_lt (by norm_num : 3 ≠ 0)
      have h_eq : (2 ^ d.size) ^ 3 = 2 ^ (3 * d.size) := by
        rw [← Nat.pow_mul, Nat.mul_comm]
      have h_lt : d ^ 3 < 2 ^ (3 * d.size) := by
        rw [← h_eq]; exact h_pow
      exact (Nat.size_le.2 h_lt)
    have h_n4 : Nat.size (n ^ 4) ≤ 4 * n.size := by
      have hn_lt : n < 2 ^ n.size := Nat.lt_size_self n
      have h_pow : n ^ 4 < (2 ^ n.size) ^ 4 := Nat.pow_lt_pow_left hn_lt (by norm_num : 4 ≠ 0)
      have h_eq : (2 ^ n.size) ^ 4 = 2 ^ (4 * n.size) := by
        rw [← Nat.pow_mul, Nat.mul_comm]
      have h_lt : n ^ 4 < 2 ^ (4 * n.size) := by
        rw [← h_eq]; exact h_pow
      exact (Nat.size_le.2 h_lt)
    have h_mul : Nat.size (15 * 2 ^ 17 * d ^ 3 * n ^ 4) ≤
        Nat.size (15 * 2 ^ 17) + Nat.size (d ^ 3) + Nat.size (n ^ 4) := by
      apply le_trans (h_size_mul (15 * 2 ^ 17 * d ^ 3) (n ^ 4))
      have htemp := add_le_add_right (h_size_mul (15 * 2 ^ 17) (d ^ 3)) (Nat.size (n ^ 4))
      -- htemp : (15 * 2 ^ 17 * d ^ 3).size + (n ^ 4).size ≤ ((15 * 2 ^ 17).size + (d ^ 3).size) + (n ^ 4).size
      -- The goal is the same but RHS is (15*2^17).size + (d^3).size + (n^4).size without parens
      -- Use `omega` to handle the associativity
      omega
    apply le_trans h_mul
    rw [h_size_const]
    omega
  -- bound (n * (d + 2)).size
  have h_nd_size : (n * (d + 2)).size ≤ n.size + d.size + 2 := by
    have h_d2 : (d + 2).size ≤ d.size + 2 := by
      have hdd : d + 2 < 2 ^ (d.size + 2) := by
        have hd_lt : d < 2 ^ d.size := Nat.lt_size_self d
        calc
          d + 2 < 2 ^ d.size + 2 := by omega
          _ ≤ 2 ^ d.size + 2 * 2 ^ d.size := by
            have hpos : 1 ≤ 2 ^ d.size := Nat.one_le_two_pow (n := d.size)
            omega
          _ = 3 * 2 ^ d.size := by ring
          _ < 4 * 2 ^ d.size := by omega
          _ = 2 ^ (d.size + 2) := by ring
      exact (Nat.size_le.2 hdd)
    calc
      (n * (d + 2)).size ≤ n.size + (d + 2).size := h_size_mul n (d + 2)
      _ ≤ n.size + (d.size + 2) := add_le_add_right h_d2 n.size
      _ = n.size + d.size + 2 := by omega
  -- bound le.size
  have h_le_size : le.size ≤ le := h_size_le le
  -- bound B.size
  have hB_size : B.size ≤ B := h_size_le B
  -- now substitute ld and use omega
  subst hld
  -- rewrite everything in terms of d.size, n.size, le, le.size, p, q, pF, B, B.size
  rw [hq, hpF, hB, hp]
  -- bound the inner size term using h_size_le and h_nd_size
  have h_inner_size : (2 * (10 * le + 16 * d.size + 160 + (n * (d + 2)).size + 2)).size ≤
      2 * (10 * le + 16 * d.size + 160 + (n.size + d.size + 2) + 2) := by
    have hX := h_size_le (2 * (10 * le + 16 * d.size + 160 + (n * (d + 2)).size + 2))
    apply le_trans hX
    have h_inner_expr : 2 * (10 * le + 16 * d.size + 160 + (n * (d + 2)).size + 2) ≤
        2 * (10 * le + 16 * d.size + 160 + (n.size + d.size + 2) + 2) := by
      apply Nat.mul_le_mul_left 2
      omega
    exact h_inner_expr
  -- convert d, n ≥ 1 to size bounds
  have hdsize : 1 ≤ d.size := by
    have hpos : 0 < d.size := (Nat.size_pos.2 (by omega : 0 < d))
    omega
  have hnsize : 1 ≤ n.size := by
    have hpos : 0 < n.size := (Nat.size_pos.2 (by omega : 0 < n))
    omega
  -- now use zify and linarith
  zify [hdsize, hnsize, hle_bound, h_le_size, h_nd_size, h_inner_size]
  linarith

/-- `1/(b - a·(x/D_S))` is at most `2^{E₀} M^{d+1}` when it is positive: times `D_S den(b) ∏ den(a_k)` the difference is a
positive integer. -/
theorem beta_inv_le {d : ℕ} (b : ℚ) (a : Fin d → ℚ) (x : Fin d → ℤ) (DS : ℤ)
    (M E0 : ℕ) (hDS : 0 < DS) (hDSE : DS ≤ 2 ^ E0) (hb : b.den ≤ M) (ha : ∀ k, (a k).den ≤ M)
    (hpos : 0 < b - a ⬝ᵥ (fun k => (x k : ℚ) / DS)) :
    1 / (b - a ⬝ᵥ (fun k => (x k : ℚ) / DS)) ≤ 2 ^ E0 * M ^ (d + 1) := by
  set P : ℕ := ∏ k, (a k).den with hP
  have hP0 : 0 < P := Finset.prod_pos fun k _ => (a k).den_pos
  have hk : ∀ k, ∃ w : ℤ, (P : ℚ) * a k = w := fun k => by
    refine ⟨(a k).num * ∏ j ∈ Finset.univ.erase k, ((a j).den : ℤ), ?_⟩
    rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose w hw using hk
  have hDSq : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have hint : ((DS : ℚ) * b.den * P) * (b - a ⬝ᵥ (fun k => (x k : ℚ) / DS)) =
      ((DS * P * b.num - b.den * ∑ k, w k * x k : ℤ) : ℚ) := by
    have e1 : ((DS : ℚ) * b.den * P) * b = DS * P * b.num := by
      rw [← Rat.mul_den_eq_num]; ring
    have e2 : ((DS : ℚ) * b.den * P) * (a ⬝ᵥ (fun k => (x k : ℚ) / DS)) = b.den * ∑ k, (w k : ℚ) * x k := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hw k]
      field_simp
    rw [mul_sub, e1, e2]
    push_cast
    ring
  set z : ℤ := DS * P * b.num - b.den * ∑ k, w k * x k
  have hQ : (0 : ℚ) < (DS : ℚ) * b.den * P := by
    have : (0 : ℚ) < DS := by exact_mod_cast hDS
    positivity
  have hz : (0 : ℚ) < z := by rw [← hint]; exact mul_pos hQ hpos
  have hz1 : (1 : ℚ) ≤ z := by
    have : (0 : ℤ) < z := by exact_mod_cast hz
    exact_mod_cast this
  set v := b - a ⬝ᵥ (fun k => (x k : ℚ) / DS)
  have hv : 1 / v ≤ (DS : ℚ) * b.den * P := by
    rw [div_le_iff₀ hpos]
    linarith
  have hPM : (P : ℚ) ≤ (M : ℚ) ^ d := by
    have : P ≤ M ^ d := by
      rw [hP]
      calc ∏ k, (a k).den ≤ ∏ _k : Fin d, M := Finset.prod_le_prod fun k _ => ha k
        _ = M ^ d := by simp
    exact_mod_cast this
  have hbM : (b.den : ℚ) ≤ M := by exact_mod_cast hb
  have hDSE' : (DS : ℚ) ≤ 2 ^ E0 := by exact_mod_cast hDSE
  calc 1 / v ≤ (DS : ℚ) * b.den * P := hv
    _ ≤ 2 ^ E0 * M * M ^ d := by gcongr
    _ = 2 ^ E0 * M ^ (d + 1) := by ring

end AdversarialBco.Bit.Transfer.BLM
