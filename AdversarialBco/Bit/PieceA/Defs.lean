/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# Piece A: the reference constants written out

The reference constants as explicit functions of `(d, n)`: `N = 15 · 2^17 d^3 n^4` (`NeN`, `Ne`), `Le = 36 ln N`,
`ε = 14500 d^{3/2} Le^5/n^{1/2}`, `R = 134 d (ln(2d + 2))^{1/2}`, `ℓd = size d`. At BL's confidence
`δ = 2^{-19}/(dn)^3`, `δ/3 ≤ e^{-14}/(dn)^3` (`deltaBL_third_le`).
-/

namespace AdversarialBco.Bit.PieceA

open AdversarialBco.Bit.BLP (po par)
open AdversarialBco.Bit.Asm (RunCase deltaBL)

/-- `N = 15 · 2^17 d^3 n^4` as a natural number. -/
def NeN (d n : ℕ) : ℕ := 15 * 2 ^ 17 * d ^ 3 * n ^ 4

/-- `N` as a real number. -/
noncomputable def Ne (d n : ℕ) : ℝ := (NeN d n : ℝ)

/-- `Le = 36 ln N`. -/
noncomputable def Le (d n : ℕ) : ℝ := 36 * Real.log (Ne d n)

/-- `ε = 14500 d^{3/2} Le^5 / n^{1/2}`. -/
noncomputable def eps (d n : ℕ) : ℝ := 14500 * d * Real.sqrt d * Le d n ^ 5 / Real.sqrt n

/-- `R = 134 d (ln(2d + 2))^{1/2}`. -/
noncomputable def R (d : ℕ) : ℝ := 134 * d * Real.sqrt (Real.log (2 * d + 2))

/-- `ℓd = size d`. -/
def ld (d : ℕ) : ℕ := d.size

/-! ## The constants of `Bud` -/

theorem exp14_le : Real.exp 14 ≤ 3 * 2 ^ 19 := by
  have h1 := Real.exp_one_lt_d9
  have h : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 := by
        gcongr
    _ ≤ 3 * 2 ^ 19 := by norm_num

/-- `δ/3 ≤ e^{-14}/(dn)^3` at BL's `δ = 2^{-19}/(dn)^3`. -/
theorem deltaBL_third_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    deltaBL d n / 3 ≤ Real.exp (-14) / ((d : ℝ) * n) ^ 3 := by
  have hdn : 0 < ((d : ℝ) * n) ^ 3 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h : (2⁻¹ : ℝ) ^ 19 / 3 ≤ Real.exp (-14) := by
    rw [Real.exp_neg]
    have := inv_anti₀ (by positivity) exp14_le
    calc (2⁻¹ : ℝ) ^ 19 / 3 = (3 * 2 ^ 19 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := this
  calc deltaBL d n / 3 = ((2⁻¹ : ℝ) ^ 19 / 3) / ((d : ℝ) * n) ^ 3 := by unfold deltaBL; ring
    _ ≤ _ := div_le_div_of_nonneg_right h hdn.le

end AdversarialBco.Bit.PieceA
