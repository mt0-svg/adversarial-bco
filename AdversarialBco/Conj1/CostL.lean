/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGBound

@[expose] public section

/-!
# The variable of the step bound of PG with `n` only inside the logarithm

`pgb_XL`: the dominating variable `X = d L Λ`, `L = log (2dn/δ)`, `Λ = 2 + log (R₀/r₀)`, has `1 ≤ X`, `d ≤ X`,
`2 Λ ≤ 3 X`, `L ≤ X/2`, `1/2 ≤ L` and `2 ≤ Λ` for `d, n ≥ 1`, `0 < δ < 1` and `0 < r₀ ≤ R₀`. The step bound
`kPGNS_boundL` (Conj1Arith/MachN/Bound.lean) bounds every parameter of a stage by a power of this `X`: `n` enters the
step count of PG only through `δ₁` (`pgb_delta1`), inside the logarithm.
-/
open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL

namespace AdversarialBco.Poly.PG

theorem pgb_XL {d n : ℕ} {δ r0 R0 : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h0 : 0 < δ) (h1 : δ < 1)
    (hr0 : 0 < r0) (hr : r0 ≤ R0) :
    let L := Real.log (2 * d * n / δ)
    let Λ := 2 + Real.log (R0 / r0)
    let X := (d : ℝ) * L * Λ
    1 ≤ X ∧ (d : ℝ) ≤ X ∧ 2 * Λ ≤ 3 * X ∧ L ≤ X / 2 ∧ 1 / 2 ≤ L ∧ 2 ≤ Λ := by
  intro L Λ X
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have h2 : (2 : ℝ) ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ h0]; nlinarith
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) h2
  have hl2 := Real.log_two_gt_d9
  have hy : 1 ≤ R0 / r0 := by rw [le_div_iff₀ hr0]; linarith
  have hΛ : 2 ≤ Λ := by have := Real.log_nonneg hy; show 2 ≤ 2 + Real.log (R0 / r0); linarith
  have hL23 : 2 / 3 ≤ L := by linarith
  have hLΛ : 4 / 3 ≤ L * Λ := by nlinarith
  have hX : X = (d : ℝ) * (L * Λ) := by show (d : ℝ) * L * Λ = _; ring
  have hXge : L * Λ ≤ X := by rw [hX]; nlinarith
  refine ⟨by linarith, ?_, ?_, ?_, by linarith, hΛ⟩
  · rw [hX]; nlinarith
  · nlinarith
  · nlinarith

end AdversarialBco.Poly.PG
