/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRa

@[expose] public section

/-!
# The tail of BL's round, part f: magnitudes, flattening, work

The magnitudes of R12's and R13's values and of R10's and R13's tests at the word size; the row-major flattening of a
matrix (`flatM`); the work of the tail and its magnitudes polynomial in `W` (`tl_poly`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open Matrix

/-- A `d × d` matrix flattened row-major: entry `(i, j)` at `d i + j`, `0` beyond `d²`. -/
def flatM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) (k : ℕ) : ℤ :=
  if h : k < d * d then M ⟨k / d, Nat.div_lt_of_lt_mul h⟩ ⟨k % d, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by
    subst h0; simp at h)⟩ else 0

/-- The magnitudes of R12's inputs at the exponent `Gu = 4 E1 + 2 X + 3 d`. -/
theorem tl_r12_bnds {d : ℕ} (Bh : Matrix (Fin d) (Fin d) ℤ) (bh Gh x : Fin d → ℤ)
    (E1 X : ℕ) (hB : ∀ i j, |Bh i j| ≤ 2 ^ E1) (hb : ∀ j, |bh j| ≤ 2 ^ E1) (hG : ∀ j, |Gh j| ≤ 2 ^ E1)
    (hx : ∀ j, |x j| ≤ 2 ^ (X + E1)) :
    (∀ i j, |Bh i j| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d)) ∧ (∀ j, |x j| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d)) ∧
      (∀ j, |bh j| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d)) ∧ (∀ j, |Gh j| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d)) ∧
      (∀ j, |(Bhᵀ *ᵥ x) j| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d)) ∧
      |(Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x)| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d) ∧
      |bh ⬝ᵥ x| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d) ∧ |Gh ⬝ᵥ x| ≤ 2 ^ (4 * E1 + 2 * X + 3 * d) ∧
      (2 : ℤ) ^ X ≤ 2 ^ (4 * E1 + 2 * X + 3 * d) := by
  set M := 4 * E1 + 2 * X + 3 * d with hM
  have h2pos : (1 : ℤ) ≤ (2 : ℤ) := by norm_num
  have hd_lt : d < 2 ^ d :=
    Nat.rec (by norm_num) (fun k ih => by
      rw [pow_succ]
      have hk : k < 2 ^ k := ih
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow (n := k)
      calc
        k + 1 < 2 ^ k + 2 ^ k := Nat.add_lt_add_of_lt_of_le hk h1
        _ = 2 * 2 ^ k := by rw [Nat.two_mul]
        _ = 2 ^ k * 2 := by rw [mul_comm]
        _ = 2 ^ (k + 1) := by rw [pow_succ]
    ) d
  have hd : d ≤ 2 ^ d := Nat.le_of_lt hd_lt
  have hE1M : E1 ≤ M := by dsimp [M]; omega
  have hXE1M : X + E1 ≤ M := by dsimp [M]; omega
  have h_exp_dot : E1 + (X + E1) + d ≤ M := by dsimp [M]; omega
  have h_transpose : ∀ i k, |Bhᵀ i k| ≤ (2 : ℤ) ^ E1 := by
    intro i k
    rw [transpose_apply]
    exact hB k i
  have h_mulVec_all : ∀ j, |(Bhᵀ *ᵥ x) j| ≤ (2 : ℤ) ^ (2 * E1 + X + d) := by
    intro j
    have h := mulVec_abs_le h_transpose hx hd j
    have h_exp : E1 + (X + E1) + d ≤ 2 * E1 + X + d := by omega
    apply le_trans h
    apply pow_le_pow_right₀ h2pos h_exp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    apply le_trans (hB i j)
    apply pow_le_pow_right₀ h2pos hE1M
  · intro j
    apply le_trans (hx j)
    apply pow_le_pow_right₀ h2pos hXE1M
  · intro j
    apply le_trans (hb j)
    apply pow_le_pow_right₀ h2pos hE1M
  · intro j
    apply le_trans (hG j)
    apply pow_le_pow_right₀ h2pos hE1M
  · intro j
    apply le_trans (h_mulVec_all j)
    have h_exp : 2 * E1 + X + d ≤ M := by dsimp [M]; omega
    apply pow_le_pow_right₀ h2pos h_exp
  · have h_dot := dot_abs_le h_mulVec_all h_mulVec_all hd
    have h_exp : (2 * E1 + X + d) + (2 * E1 + X + d) + d = M := by dsimp [M]; omega
    apply le_trans h_dot
    apply pow_le_pow_right₀ h2pos
    rw [h_exp]
  · have h_dot := dot_abs_le hb hx hd
    apply le_trans h_dot
    apply pow_le_pow_right₀ h2pos h_exp_dot
  · have h_dot := dot_abs_le hG hx hd
    apply le_trans h_dot
    apply pow_le_pow_right₀ h2pos h_exp_dot
  · have hXM : X ≤ M := by dsimp [M]; omega
    apply pow_le_pow_right₀ h2pos hXM

/-- The two sides of R12's test fit the word size. -/
theorem tl_r12_test_abs {d : ℕ} (F Q D H eh lh kh rh : ℤ)
    (Bh : Matrix (Fin d) (Fin d) ℤ) (Gh bh x : Fin d → ℤ) (E ℓ : ℕ) (hF : |F| ≤ 2 ^ E) (hQ : |Q| ≤ 2 ^ E)
    (hD : |D| ≤ 2 ^ E) (hH : |H| ≤ 2 ^ E) (he : |eh| ≤ 2 ^ E) (hl : |lh| ≤ 2 ^ E) (hk : |kh| ≤ 2 ^ E)
    (hr : |rh| ≤ 2 ^ E) (hB : ∀ i j, |Bh i j| ≤ 2 ^ E) (hG : ∀ j, |Gh j| ≤ 2 ^ E) (hb : ∀ j, |bh j| ≤ 2 ^ E)
    (hx : ∀ j, |x j| ≤ 2 ^ E) (hℓ : 7 * E + 3 * d + 3 < ℓ) :
    |(((eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
        F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
          kh * Q * D * D)) : ℤ) : ℝ)| < 2 ^ ℓ ∧
      |((((F - rh * H) * Q * Q * D * D) : ℤ) : ℝ)| < 2 ^ ℓ := by
  rcases r12_abs F Q D H eh lh kh rh Bh Gh bh x E hF hQ hD hH he hl hk hr hB hG hb hx with ⟨h1, h2⟩
  have hℓ2 : 6 * E + 1 < ℓ := by
    omega
  have h2pow : (1 : ℝ) < (2 : ℝ) := by norm_num
  constructor
  · -- first bound
    have h1' : ((|eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
      F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
        kh * Q * D * D)| : ℤ) : ℝ) ≤ ((2 ^ (7 * E + 3 * d + 3) : ℤ) : ℝ) := by
      exact_mod_cast h1
    calc
      |(((eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
        F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
          kh * Q * D * D)) : ℤ) : ℝ)| = ((|eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
        F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
          kh * Q * D * D)| : ℤ) : ℝ) := by
        simp [Int.cast_abs]
      _ ≤ ((2 ^ (7 * E + 3 * d + 3) : ℤ) : ℝ) := h1'
      _ = (2 : ℝ) ^ (7 * E + 3 * d + 3) := by simp
      _ < (2 : ℝ) ^ ℓ := pow_lt_pow_right₀ h2pow hℓ
  · -- second bound
    have h2' : ((|(F - rh * H) * Q * Q * D * D| : ℤ) : ℝ) ≤ ((2 ^ (6 * E + 1) : ℤ) : ℝ) := by
      exact_mod_cast h2
    calc
      |((((F - rh * H) * Q * Q * D * D) : ℤ) : ℝ)| = ((|(F - rh * H) * Q * Q * D * D| : ℤ) : ℝ) := by
        simp [Int.cast_abs]
      _ ≤ ((2 ^ (6 * E + 1) : ℤ) : ℝ) := h2'
      _ = (2 : ℝ) ^ (6 * E + 1) := by simp
      _ < (2 : ℝ) ^ ℓ := pow_lt_pow_right₀ h2pow hℓ2

/-- The magnitudes of R13's values at the exponents `2 E1 + d` and `G2 = 8 E1 + 3 d + 2`. -/
theorem tl_r13_bnds {d : ℕ} (Q G Dm s5 F Wh : ℤ) (mu Γ : Fin d → ℤ)
    (Ah : Matrix (Fin d) (Fin d) ℤ) (E1 : ℕ) (hQ : |Q| ≤ 2 ^ E1) (hG : |G| ≤ 2 ^ E1) (hD : |Dm| ≤ 2 ^ E1)
    (hs : |s5| ≤ 2 ^ E1) (hF : |F| ≤ 2 ^ E1) (hW : |Wh| ≤ 2 ^ E1) (hm : ∀ j, |mu j| ≤ 2 ^ E1)
    (hA : ∀ i j, |Ah i j| ≤ 2 ^ E1) (hΓ : ∀ j, |Γ j| ≤ 2 ^ E1) :
    (∀ j, |(Ah *ᵥ Γ) j| ≤ 2 ^ (2 * E1 + d)) ∧
      (∀ j, |mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm| ≤ 2 ^ (8 * E1 + 3 * d + 2)) ∧
      |Dm * Q * Q * G| ≤ 2 ^ (8 * E1 + 3 * d + 2) ∧ |F| ≤ 2 ^ (8 * E1 + 3 * d + 2) ∧
      |Wh| ≤ 2 ^ (8 * E1 + 3 * d + 2) ∧ (4 : ℤ) ≤ 2 ^ (8 * E1 + 3 * d + 2) ∧
      |(fun j => mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm) ⬝ᵥ (fun j => mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm)| ≤
        2 ^ (8 * E1 + 3 * d + 2) := by
  have hd : d ≤ 2 ^ d := by
    have h := Nat.lt_two_pow_self (n := d)
    exact Nat.le_of_lt h
  have h_mulVec : ∀ j, |(Ah *ᵥ Γ) j| ≤ 2 ^ (2 * E1 + d) := by
    intro j
    have h := mulVec_abs_le hA hΓ hd j
    simpa [two_mul] using h
  have h_num : ∀ j, |mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm| ≤ 2 ^ (8 * E1 + 3 * d + 2) := by
    intro j
    have h_wn := wn_abs Q G Dm s5 mu Γ Ah E1 hQ hG hD hs hm hA hΓ j
    have h_eq : mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm = mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * Dm := by
      ring
    have h_bound : |mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm| ≤ 2 ^ (4 * E1 + d + 1) := by
      simpa [h_eq] using h_wn
    have h_exp : 4 * E1 + d + 1 ≤ 8 * E1 + 3 * d + 2 := by omega
    have h_pow : (2 : ℤ) ^ (4 * E1 + d + 1) ≤ (2 : ℤ) ^ (8 * E1 + 3 * d + 2) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_exp
    exact le_trans h_bound h_pow
  have h_DQQG : |Dm * Q * Q * G| ≤ 2 ^ (8 * E1 + 3 * d + 2) := by
    have h_mul : |Dm| * |Q| * |Q| * |G| ≤ (2 ^ E1) * (2 ^ E1) * (2 ^ E1) * (2 ^ E1) := by
      have h1 : |Dm| * |Q| ≤ (2 ^ E1) * (2 ^ E1) := by
        apply mul_le_mul hD hQ (abs_nonneg _) (pow_nonneg (by norm_num) _)
      have h2 : |Q| * |G| ≤ (2 ^ E1) * (2 ^ E1) := by
        apply mul_le_mul hQ hG (abs_nonneg _) (pow_nonneg (by norm_num) _)
      have h_nonneg_absQ : 0 ≤ |Q| := abs_nonneg _
      have h_nonneg_absG : 0 ≤ |G| := abs_nonneg _
      have h_nonneg_absDm : 0 ≤ |Dm| := abs_nonneg _
      have h_nonneg_2E1 : 0 ≤ (2 : ℤ) ^ E1 := pow_nonneg (by norm_num) _
      -- combine: |Dm| * |Q| * |Q| * |G| = (|Dm| * |Q|) * (|Q| * |G|)
      -- ≤ (2^E1 * 2^E1) * (2^E1 * 2^E1)
      calc
        |Dm| * |Q| * |Q| * |G| = (|Dm| * |Q|) * (|Q| * |G|) := by ring
        _ ≤ ((2 ^ E1) * (2 ^ E1)) * ((2 ^ E1) * (2 ^ E1)) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (2 ^ E1) * (2 ^ E1) * (2 ^ E1) * (2 ^ E1) := by ring
    calc
      |Dm * Q * Q * G| = |Dm| * |Q| * |Q| * |G| := by simp [abs_mul]
      _ ≤ (2 ^ E1) * (2 ^ E1) * (2 ^ E1) * (2 ^ E1) := h_mul
      _ = (2 : ℤ) ^ (4 * E1) := by ring
      _ ≤ (2 : ℤ) ^ (8 * E1 + 3 * d + 2) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
  have h_F : |F| ≤ 2 ^ (8 * E1 + 3 * d + 2) :=
    le_trans hF (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : E1 ≤ 8 * E1 + 3 * d + 2))
  have h_Wh : |Wh| ≤ 2 ^ (8 * E1 + 3 * d + 2) :=
    le_trans hW (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : E1 ≤ 8 * E1 + 3 * d + 2))
  have h_4 : (4 : ℤ) ≤ 2 ^ (8 * E1 + 3 * d + 2) := by
    have h_eq : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [h_eq]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    omega
  have h_dot : |(fun j => mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm) ⬝ᵥ (fun j => mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm)| ≤
      2 ^ (8 * E1 + 3 * d + 2) := by
    let x : Fin d → ℤ := fun j => mu j * Q * Q * G - s5 * (Ah *ᵥ Γ) j * Dm
    have hx_bound : ∀ j, |x j| ≤ 2 ^ (4 * E1 + d + 1) := by
      intro j
      have h_wn := wn_abs Q G Dm s5 mu Γ Ah E1 hQ hG hD hs hm hA hΓ j
      have h_eq : x j = mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * Dm := by
        dsimp [x]
        ring
      simpa [h_eq] using h_wn
    have h_dot_self := dot_self_le x (4 * E1 + d + 1) hx_bound
    rcases h_dot_self with ⟨h_nonneg, h_le⟩
    have h_exp : 2 * (4 * E1 + d + 1) + d = 8 * E1 + 3 * d + 2 := by omega
    rw [h_exp] at h_le
    rw [abs_of_nonneg h_nonneg]
    exact h_le
  exact And.intro h_mulVec
    (And.intro h_num
      (And.intro h_DQQG
        (And.intro h_F
          (And.intro h_Wh
            (And.intro h_4 h_dot)))))

/-- The two sides of R13's test fit the word size. -/
theorem tl_r13_test_abs (Wh Dw F S : ℤ) (G2 ℓ : ℕ) (hW : |Wh| ≤ 2 ^ G2)
    (hD : |Dw| ≤ 2 ^ G2) (hF : |F| ≤ 2 ^ G2) (h4 : (4 : ℤ) ≤ 2 ^ G2) (hS : |S| ≤ 2 ^ G2) (hℓ : 5 * G2 < ℓ) :
    |((4 * Wh * Wh * Dw * Dw : ℤ) : ℝ)| < 2 ^ ℓ ∧ |((S * F * F : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h4_nonneg : (0 : ℤ) ≤ 4 := by norm_num
  have h4_abs : |(4 : ℤ)| ≤ (2 : ℤ) ^ G2 := by
    simpa [abs_of_nonneg h4_nonneg] using h4
  have h_pow_nonneg (n : ℕ) : 0 ≤ (2 : ℤ) ^ n := pow_nonneg (by norm_num) n
  have h_abs_nonneg (a : ℤ) : 0 ≤ |a| := abs_nonneg _
  have h_two_gt_one : (1 : ℤ) < 2 := by norm_num
  -- Bound for |4*Wh*Wh*Dw*Dw|
  have h_bound1 : |4 * Wh * Wh * Dw * Dw| ≤ (2 : ℤ) ^ (5 * G2) := by
    calc
      |4 * Wh * Wh * Dw * Dw| = |(4 : ℤ)| * |Wh| * |Wh| * |Dw| * |Dw| := by
        simp [abs_mul]
      _ ≤ (2 ^ G2) * (2 ^ G2) * (2 ^ G2) * (2 ^ G2) * (2 ^ G2) := by
        have h1 : |(4 : ℤ)| * |Wh| ≤ (2 ^ G2) * (2 ^ G2) :=
          mul_le_mul h4_abs hW (h_abs_nonneg _) (h_pow_nonneg _)
        have h2 : (|(4 : ℤ)| * |Wh|) * |Wh| ≤ ((2 ^ G2) * (2 ^ G2)) * (2 ^ G2) :=
          mul_le_mul h1 hW (h_abs_nonneg _) (mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _))
        have h3 : ((|(4 : ℤ)| * |Wh|) * |Wh|) * |Dw| ≤ (((2 ^ G2) * (2 ^ G2)) * (2 ^ G2)) * (2 ^ G2) :=
          mul_le_mul h2 hD (h_abs_nonneg _) (mul_nonneg (mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _)) (h_pow_nonneg _))
        have h4' : (((|(4 : ℤ)| * |Wh|) * |Wh|) * |Dw|) * |Dw| ≤ ((((2 ^ G2) * (2 ^ G2)) * (2 ^ G2)) * (2 ^ G2)) * (2 ^ G2) :=
          mul_le_mul h3 hD (h_abs_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _)) (h_pow_nonneg _)) (h_pow_nonneg _))
        -- simplify the associativity
        simpa [mul_assoc] using h4'
      _ = (2 : ℤ) ^ (5 * G2) := by
        calc
          (2 ^ G2) * (2 ^ G2) * (2 ^ G2) * (2 ^ G2) * (2 ^ G2) = ((2 : ℤ) ^ G2) ^ 5 := by ring
          _ = (2 : ℤ) ^ (G2 * 5) := by rw [pow_mul]
          _ = (2 : ℤ) ^ (5 * G2) := by rw [mul_comm G2 5]
  -- Bound for |S*F*F|
  have h_bound2 : |S * F * F| ≤ (2 : ℤ) ^ (5 * G2) := by
    calc
      |S * F * F| = |S| * |F| * |F| := by simp [abs_mul]
      _ ≤ (2 ^ G2) * (2 ^ G2) * (2 ^ G2) := by
        have h1 : |S| * |F| ≤ (2 ^ G2) * (2 ^ G2) :=
          mul_le_mul hS hF (h_abs_nonneg _) (h_pow_nonneg _)
        have h2 : (|S| * |F|) * |F| ≤ ((2 ^ G2) * (2 ^ G2)) * (2 ^ G2) :=
          mul_le_mul h1 hF (h_abs_nonneg _) (mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _))
        simpa [mul_assoc] using h2
      _ = (2 : ℤ) ^ (3 * G2) := by
        calc
          (2 ^ G2) * (2 ^ G2) * (2 ^ G2) = ((2 : ℤ) ^ G2) ^ 3 := by ring
          _ = (2 : ℤ) ^ (G2 * 3) := by rw [pow_mul]
          _ = (2 : ℤ) ^ (3 * G2) := by rw [mul_comm G2 3]
      _ ≤ (2 : ℤ) ^ (5 * G2) := by
        have h_le : 3 * G2 ≤ 5 * G2 := by omega
        exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_le
  -- Now cast to ℝ
  have h_goal1 : |((4 * Wh * Wh * Dw * Dw : ℤ) : ℝ)| < (2 : ℝ) ^ ℓ := by
    calc
      |((4 * Wh * Wh * Dw * Dw : ℤ) : ℝ)| = (|4 * Wh * Wh * Dw * Dw| : ℝ) := by
        simpa using (Int.cast_abs (a := 4 * Wh * Wh * Dw * Dw)).symm
      _ ≤ ((2 : ℤ) ^ (5 * G2) : ℝ) := by exact_mod_cast h_bound1
      _ < (2 : ℝ) ^ ℓ := by
        have h_lt : (2 : ℤ) ^ (5 * G2) < (2 : ℤ) ^ ℓ :=
          pow_lt_pow_right₀ h_two_gt_one hℓ
        exact_mod_cast h_lt
  have h_goal2 : |((S * F * F : ℤ) : ℝ)| < (2 : ℝ) ^ ℓ := by
    calc
      |((S * F * F : ℤ) : ℝ)| = (|S * F * F| : ℝ) := by
        simpa using (Int.cast_abs (a := S * F * F)).symm
      _ ≤ ((2 : ℤ) ^ (5 * G2) : ℝ) := by exact_mod_cast h_bound2
      _ < (2 : ℝ) ^ ℓ := by
        have h_lt : (2 : ℤ) ^ (5 * G2) < (2 : ℤ) ^ ℓ :=
          pow_lt_pow_right₀ h_two_gt_one hℓ
        exact_mod_cast h_lt
  exact And.intro h_goal1 h_goal2

/-- The values of R10's tests fit the word size. -/
theorem tl_r10_test_abs (d : ℕ) (Lam Q : ℤ) (Bf : ℕ → ℤ) (E ℓ : ℕ)
    (hL : |Lam| ≤ 2 ^ E) (hQ : |Q| ≤ 2 ^ E) (hB : ∀ k < d * d, |Bf k| ≤ 2 ^ E) (hE : 3 * E + 1 < ℓ)
    (hℓ : d * d * 2 ^ (2 * E) < 2 ^ ℓ) :
    |((2 * Lam * Q * Q : ℤ) : ℝ)| < 2 ^ ℓ ∧
      |((∑ k ∈ Finset.range (d * d), Bf k * Bf k : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h1_int : |2 * Lam * Q * Q| < (2 : ℤ) ^ ℓ := by
    have h_bound : |2 * Lam * Q * Q| ≤ (2 : ℤ) ^ (3 * E + 1) := by
      have h_nonneg_Lam : 0 ≤ |Lam| := abs_nonneg _
      have h_nonneg_Q : 0 ≤ |Q| := abs_nonneg _
      have h_nonneg_2E : 0 ≤ (2 : ℤ) ^ E := pow_nonneg (by norm_num) E
      calc
        |2 * Lam * Q * Q| = |(2 : ℤ)| * |Lam| * |Q| * |Q| := by
          simp [abs_mul]
        _ = 2 * |Lam| * |Q| * |Q| := by norm_num
        _ ≤ 2 * (2 ^ E) * (2 ^ E) * (2 ^ E) := by
          have h1 : 2 * |Lam| ≤ 2 * (2 ^ E) := mul_le_mul_of_nonneg_left hL (by norm_num)
          have h2 : (2 * |Lam|) * |Q| ≤ (2 * (2 ^ E)) * (2 ^ E) :=
            mul_le_mul h1 hQ h_nonneg_Q (mul_nonneg (by norm_num) h_nonneg_2E)
          have h3 : ((2 * |Lam|) * |Q|) * |Q| ≤ ((2 * (2 ^ E)) * (2 ^ E)) * (2 ^ E) :=
            mul_le_mul h2 hQ h_nonneg_Q (mul_nonneg (mul_nonneg (by norm_num) h_nonneg_2E) h_nonneg_2E)
          simpa [mul_assoc] using h3
        _ = (2 : ℤ) ^ (3 * E + 1) := by
          ring
    have h_pow_lt : (2 : ℤ) ^ (3 * E + 1) < (2 : ℤ) ^ ℓ := by
      have h_nat_lt : 2 ^ (3 * E + 1) < 2 ^ ℓ :=
        Nat.pow_lt_pow_right (by norm_num) hE
      exact_mod_cast h_nat_lt
    exact lt_of_le_of_lt h_bound h_pow_lt
  have h2_int : |∑ k ∈ Finset.range (d * d), Bf k * Bf k| < (2 : ℤ) ^ ℓ := by
    have h_bound : |∑ k ∈ Finset.range (d * d), Bf k * Bf k| ≤ (d * d : ℤ) * (2 : ℤ) ^ (2 * E) := by
      calc
        |∑ k ∈ Finset.range (d * d), Bf k * Bf k| ≤ ∑ k ∈ Finset.range (d * d), |Bf k * Bf k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range (d * d), |Bf k| ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp [abs_mul, pow_two]
        _ ≤ ∑ k ∈ Finset.range (d * d), (2 ^ E) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_mem : k < d * d := Finset.mem_range.1 hk
          have hBk : |Bf k| ≤ (2 : ℤ) ^ E := by exact_mod_cast hB k hk_mem
          have h_nonneg : 0 ≤ |Bf k| := abs_nonneg _
          nlinarith
        _ = (d * d : ℤ) * ((2 : ℤ) ^ E) ^ 2 := by
          simp [Finset.card_range]
        _ = (d * d : ℤ) * (2 : ℤ) ^ (2 * E) := by
          ring
    have hℓ_int : (d * d : ℤ) * (2 : ℤ) ^ (2 * E) < (2 : ℤ) ^ ℓ := by
      exact_mod_cast hℓ
    exact lt_of_le_of_lt h_bound hℓ_int
  have h1_real : |((2 * Lam * Q * Q : ℤ) : ℝ)| < (2 : ℝ) ^ ℓ := by
    calc
      |((2 * Lam * Q * Q : ℤ) : ℝ)| = (|2 * Lam * Q * Q| : ℝ) := by simp
      _ < (2 ^ ℓ : ℝ) := by exact_mod_cast h1_int
      _ = (2 : ℝ) ^ ℓ := by simp
  have h2_real : |((∑ k ∈ Finset.range (d * d), Bf k * Bf k : ℤ) : ℝ)| < (2 : ℝ) ^ ℓ := by
    calc
      |((∑ k ∈ Finset.range (d * d), Bf k * Bf k : ℤ) : ℝ)| = (|∑ k ∈ Finset.range (d * d), Bf k * Bf k| : ℝ) := by simp
      _ < (2 ^ ℓ : ℝ) := by exact_mod_cast h2_int
      _ = (2 : ℝ) ^ ℓ := by simp
  exact And.intro h1_real h2_real

/-- Two word-size requirements from linear ones. -/
theorem tl_pow_req (d E G ℓ : ℕ) :
    (2 * E + 2 * d ≤ ℓ → d * d * 2 ^ (2 * E) < 2 ^ ℓ) ∧ (2 * G + d ≤ ℓ → d * 2 ^ (2 * G) < 2 ^ ℓ) := by
  constructor
  · intro h
    have hd_lt : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
    have hdd_lt : d * d < 2 ^ d * 2 ^ d := Nat.mul_lt_mul'' hd_lt hd_lt
    have hdd_lt' : d * d < 2 ^ (2 * d) := by
      calc
        d * d < 2 ^ d * 2 ^ d := hdd_lt
        _ = 2 ^ (d + d) := by rw [pow_add]
        _ = 2 ^ (2 * d) := by rw [Nat.two_mul]
    have hpos : 0 < 2 ^ (2 * E) := Nat.pow_pos (a := 2) (n := 2 * E) (by decide : 0 < 2)
    have h_mul_lt : d * d * 2 ^ (2 * E) < 2 ^ (2 * d) * 2 ^ (2 * E) :=
      Nat.mul_lt_mul_of_pos_right hdd_lt' hpos
    have h_pow_le : 2 ^ (2 * E + 2 * d) ≤ 2 ^ ℓ :=
      Nat.pow_le_pow_right (by decide : 2 > 0) h
    calc
      d * d * 2 ^ (2 * E) < 2 ^ (2 * d) * 2 ^ (2 * E) := h_mul_lt
      _ = 2 ^ (2 * d + 2 * E) := by rw [pow_add]
      _ = 2 ^ (2 * E + 2 * d) := by rw [add_comm]
      _ ≤ 2 ^ ℓ := h_pow_le
  · intro h
    have hd_lt : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
    have hpos : 0 < 2 ^ (2 * G) := Nat.pow_pos (a := 2) (n := 2 * G) (by decide : 0 < 2)
    have h_mul_lt : d * 2 ^ (2 * G) < 2 ^ d * 2 ^ (2 * G) :=
      Nat.mul_lt_mul_of_pos_right hd_lt hpos
    have h_pow_le : 2 ^ (2 * G + d) ≤ 2 ^ ℓ :=
      Nat.pow_le_pow_right (by decide : 2 > 0) h
    calc
      d * 2 ^ (2 * G) < 2 ^ d * 2 ^ (2 * G) := h_mul_lt
      _ = 2 ^ (d + 2 * G) := by rw [pow_add]
      _ = 2 ^ (2 * G + d) := by rw [add_comm]
      _ ≤ 2 ^ ℓ := h_pow_le

/-- R11's linear term `b' - (η/2) G'` from numerators on the grids `2^{-p}` and `2^{-pF}`. -/
theorem tl_wp_grid {d : ℕ} (p pF E : ℕ) (eta : ℚ) (bp Gp : Fin d → ℚ)
    (hη : OnG pF eta) (hb : ∀ j, OnG p (bp j)) (hG : ∀ j, OnG p (Gp j)) (be : |qn pF eta| ≤ 2 ^ E)
    (bb : ∀ j, |qn p (bp j)| ≤ 2 ^ E) (bG : ∀ j, |qn p (Gp j)| ≤ 2 ^ E) (j : Fin d) :
    |(bp - (eta / 2) • Gp) j| ≤ 2 ^ (2 * E + 1) := by
  -- Get rewriting equations from OnG
  have h_eta_eq : eta = ((qn pF eta : ℤ) : ℚ) / ((2 : ℚ) ^ pF) := by
    field_simp [show ((2 : ℚ) ^ pF) ≠ 0 from by positivity]
    simpa [mul_comm] using hη.symm
  have h_bp_eq (j : Fin d) : bp j = ((qn p (bp j) : ℤ) : ℚ) / ((2 : ℚ) ^ p) := by
    field_simp [show ((2 : ℚ) ^ p) ≠ 0 from by positivity]
    simpa [mul_comm] using (hb j).symm
  have h_Gp_eq (j : Fin d) : Gp j = ((qn p (Gp j) : ℤ) : ℚ) / ((2 : ℚ) ^ p) := by
    field_simp [show ((2 : ℚ) ^ p) ≠ 0 from by positivity]
    simpa [mul_comm] using (hG j).symm
  -- F = 2^pF, Q = 2^p are both ≥ 1
  have hF : 1 ≤ (2 : ℤ) ^ pF := by
    exact_mod_cast Nat.one_le_pow' pF 1
  have hQ : 1 ≤ (2 : ℤ) ^ p := by
    exact_mod_cast Nat.one_le_pow' p 1
  -- Expand (bp - (eta/2) • Gp) j = bp j - (eta/2) * Gp j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Rewrite bp, Gp, eta in terms of qn, then apply wp_abs
  rw [h_bp_eq j, h_Gp_eq j, h_eta_eq]
  simpa [push_cast] using wp_abs ((2 : ℤ) ^ pF) ((2 : ℤ) ^ p) (qn pF eta)
    (fun j => qn p (bp j)) (fun j => qn p (Gp j)) E hF hQ be bb bG j

/-- The flattened matrix at the cell `d i + j`. -/
theorem tl_flat_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    flatM M (d * i + j) = M i j := by
  have hpos : 0 < d := by
    by_contra h
    have h0 : d = 0 := Nat.eq_zero_of_not_pos h
    have hi : (i : ℕ) < 0 := by simpa [h0] using i.2
    exact Nat.not_lt_zero _ hi
  have h_lt : (d : ℕ) * (i : ℕ) + (j : ℕ) < d * d := by
    have hi : (i : ℕ) < d := i.2
    have hj : (j : ℕ) < d := j.2
    nlinarith
  unfold flatM
  rw [dite_eq_left h_lt]
  have hdiv : ((d : ℕ) * (i : ℕ) + (j : ℕ)) / d = (i : ℕ) := by
    rw [add_comm, Nat.add_mul_div_left (j : ℕ) (i : ℕ) hpos]
    simp [Nat.div_eq_of_lt j.2]
  have hmod : ((d : ℕ) * (i : ℕ) + (j : ℕ)) % d = (j : ℕ) := by
    rw [add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.2
  have hM : M ⟨((d : ℕ) * (i : ℕ) + (j : ℕ)) / d, Nat.div_lt_of_lt_mul h_lt⟩
      ⟨((d : ℕ) * (i : ℕ) + (j : ℕ)) % d, Nat.mod_lt _ hpos⟩ = M i j := by
    simp [hdiv, hmod]
  exact hM

/-- Every cell below `d²` is a cell `d i + j`. -/
theorem tl_flat_cover {d : ℕ} (k : ℕ) (hk : k < d * d) :
    ∃ i j : Fin d, k = d * i + j := by
  by_cases hd0 : d = 0
  · subst hd0
    simp at hk
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
    refine ⟨⟨k / d, Nat.div_lt_of_lt_mul hk⟩, ⟨k % d, Nat.mod_lt k hpos⟩, ?_⟩
    exact (Nat.div_add_mod k d).symm

/-- The work and the magnitudes of the tail of BL's round are polynomial in `W = d + m + Ms + ns + E1 + 1`. -/
theorem tl_poly (Cx kx Ct kt Ca ka Cl kl Cc kc Cf kf : ℕ) :
    ∃ C k : ℕ, ∀ d m Ms ns E1 X : ℕ, X ≤ Cx * (d + ns + (2 * E1 + 1) + 1) ^ kx →
      (20 * d * d + 4 * d + 25) + (10 * d * d + 41 * d + 4 * X + 83) + (31 * d + 30) +
        Ct * (d + E1 + 1) ^ kt + Ca * (d + m + Ms + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka +
        Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl +
        Ca * (d + m + Ms + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka +
        Cc * (d + E1 + 1) ^ kc + Cf * (d + E1 + 1) ^ kf +
        7 * (4 * E1 + 2 * X + 3 * d) + 5 * (8 * E1 + 3 * d + 2) + X + d * d + d + 100 ≤
      C * (d + m + Ms + ns + E1 + 1) ^ k := by
  refine ⟨1000 + 19 * (Cx * 2 ^ kx) + Ct + Ca * (1 + Ct) ^ ka + Cl * 8 ^ kl + Ca * (1 + Cl * 8 ^ kl) ^ ka +
    Cc + Cf, 2 + kx + (kt + 1) * ka + (kl + 1) * ka + kt + kl + kc + kf, ?_⟩
  intro d m Ms ns E1 X hX
  set V := d + m + Ms + ns + E1 + 1 with hVdef
  set K := 2 + kx + (kt + 1) * ka + (kl + 1) * ka + kt + kl + kc + kf with hK
  have hV1 : 1 ≤ V := by omega
  have hpow : ∀ a, a ≤ K → V ^ a ≤ V ^ K := fun a ha => Nat.pow_le_pow_right hV1 ha
  set P := V ^ K with hP
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ hV1
  have hVP : V ≤ P := by simpa using hpow 1 (by omega)
  have hV2 : V * V ≤ P := by rw [← pow_two]; exact hpow 2 (by omega)
  have hdd : d * d ≤ P := le_trans (Nat.mul_le_mul (by omega : d ≤ V) (by omega : d ≤ V)) hV2
  -- X
  have hXb : X ≤ Cx * 2 ^ kx * P := by
    refine hX.trans ?_
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (d + ns + (2 * E1 + 1) + 1) ^ kx ≤ (2 * V) ^ kx := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ kx * V ^ kx := mul_pow _ _ _
      _ ≤ 2 ^ kx * P := Nat.mul_le_mul_left _ (hpow _ (by omega))
  -- the bases of the composite terms
  have hb1 : d + E1 + 1 ≤ V := by omega
  have hb2 : d + (8 * E1 + 3 * d + 2) + 1 ≤ 8 * V := by omega
  have ht : Ct * (d + E1 + 1) ^ kt ≤ Ct * V ^ kt := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb1 _)
  have hl : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ Cl * 8 ^ kl * V ^ kl := by
    rw [mul_assoc, ← mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb2 _)
  have hVk : ∀ a, V ≤ V ^ (a + 1) ∧ V ^ a ≤ V ^ (a + 1) := fun a =>
    ⟨by simpa using Nat.pow_le_pow_right hV1 (by omega : 1 ≤ a + 1), Nat.pow_le_pow_right hV1 (by omega)⟩
  have h6 : Ca * (d + m + Ms + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ Ca * (1 + Ct) ^ ka * P := by
    rw [mul_assoc]; refine Nat.mul_le_mul_left _ ?_
    calc (d + m + Ms + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ ((1 + Ct) * V ^ (kt + 1)) ^ ka := by
          refine Nat.pow_le_pow_left ?_ _
          have := (hVk kt).1; have := (hVk kt).2
          have : Ct * V ^ kt ≤ Ct * V ^ (kt + 1) := Nat.mul_le_mul_left _ (hVk kt).2
          nlinarith
      _ = (1 + Ct) ^ ka * V ^ ((kt + 1) * ka) := by rw [mul_pow, ← pow_mul]
      _ ≤ (1 + Ct) ^ ka * P := Nat.mul_le_mul_left _ (hpow _ (by omega))
  have h8 : Ca * (d + m + Ms + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤
      Ca * (1 + Cl * 8 ^ kl) ^ ka * P := by
    rw [mul_assoc]; refine Nat.mul_le_mul_left _ ?_
    calc (d + m + Ms + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka
        ≤ ((1 + Cl * 8 ^ kl) * V ^ (kl + 1)) ^ ka := by
          refine Nat.pow_le_pow_left ?_ _
          have := (hVk kl).1
          have : Cl * 8 ^ kl * V ^ kl ≤ Cl * 8 ^ kl * V ^ (kl + 1) := Nat.mul_le_mul_left _ (hVk kl).2
          nlinarith
      _ = (1 + Cl * 8 ^ kl) ^ ka * V ^ ((kl + 1) * ka) := by rw [mul_pow, ← pow_mul]
      _ ≤ (1 + Cl * 8 ^ kl) ^ ka * P := Nat.mul_le_mul_left _ (hpow _ (by omega))
  have h5 : Ct * (d + E1 + 1) ^ kt ≤ Ct * P := ht.trans (Nat.mul_le_mul_left _ (hpow _ (by omega)))
  have h7 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ Cl * 8 ^ kl * P :=
    hl.trans (Nat.mul_le_mul_left _ (hpow _ (by omega)))
  have h9 : Cc * (d + E1 + 1) ^ kc ≤ Cc * P :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb1 _).trans (hpow _ (by omega)))
  have h10 : Cf * (d + E1 + 1) ^ kf ≤ Cf * P :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb1 _).trans (hpow _ (by omega)))
  have hdP : d ≤ P := by omega
  have hEP : E1 ≤ P := by omega
  generalize Ct * (d + E1 + 1) ^ kt = T5 at h5 h6 ⊢
  generalize Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl = T7 at h7 h8 ⊢
  generalize Ca * (d + m + Ms + E1 + T5 + 1) ^ ka = T6 at h6 ⊢
  generalize Ca * (d + m + Ms + E1 + T7 + 1) ^ ka = T8 at h8 ⊢
  generalize Cc * (d + E1 + 1) ^ kc = T9 at h9 ⊢
  generalize Cf * (d + E1 + 1) ^ kf = T10 at h10 ⊢
  generalize Cx * 2 ^ kx = A at hXb ⊢
  generalize Ca * (1 + Ct) ^ ka = B6 at h6 ⊢
  generalize Ca * (1 + Cl * 8 ^ kl) ^ ka = B8 at h8 ⊢
  generalize Cl * 8 ^ kl = B7 at h7 ⊢
  linarith

end AdversarialBco.Bit.Transfer.BLM
