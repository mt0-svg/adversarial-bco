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

Facts on `ℚ` and `ℝ` for the magnitudes of BL's state: the inverse of a grid point (`grid_inv_abs`), `(2B)^{1/2} ≤ B`
(`sqrt_two_mul_le`), and the products `Av` and `v·w` of bounded entries (`mulVecQ_abs_le`, `dotQ_abs_le`).
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

end AdversarialBco.Bit.Transfer.BLM
