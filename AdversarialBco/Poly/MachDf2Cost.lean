/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2B
public import AdversarialBco.Poly.MachPGParts
public import AdversarialBco.Poly.MachPGBound
public import AdversarialBco.Poly.Df2ParBounds
public import AdversarialBco.Conj1Arith.MachN.Bound

@[expose] public section

/-!
# The cost of DF2-O in VL

Polynomial bounds on the step counts of `df2Prog` (`kDf2A_le`, `kDf2B_le`, `kMode0_le`, `df2B0_le`), and
`log (2dn/δ) ≥ 1/2` (`df2_log_ge`). The machine layer built on them, with the steps of PG (PG-N with CLAMP-NS,
`Conj1Arith.kPGNS`) and the caps of AP, is `df2oMachine_ofL` (Conj1/MachL.lean).
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly

/-- The steps of part A of a round. -/
theorem kDf2A_le (d j : ℕ) (hd : 1 ≤ d) : kDf2A d j ≤ 241 * d ^ 2 * (j + 1) := by
  have e : kDf2A d j = 30 * d ^ 2 + 121 * d + 90 + j * (10 * d ^ 2 + 44 * d + 33) := by
    unfold kDf2A kARun kMemKp; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith [Nat.mul_le_mul_left j h1, Nat.mul_le_mul_left j h2]

/-- The steps of part B of a round, with caps `K1`, `K2` on the calls of AP. -/
theorem kDf2B_le (d K1 K2 : ℕ) (hd : 1 ≤ d) : kDf2B d K1 K2 ≤ 761 * d ^ 2 + K1 + K2 := by
  have e : kDf2B d K1 K2 = 145 * d ^ 2 + 311 * d + 305 + K1 + K2 := by
    unfold kDf2B kNext kC1 kC2 kC3 kC4 kC5 kC6 kCommit kInit; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith

/-- The steps of the code of the first mode. -/
theorem kMode0_le (d : ℕ) (hd : 1 ≤ d) : kMode0 d ≤ 124 * d ^ 2 := by
  have e : kMode0 d = 20 * d ^ 2 + 46 * d + 58 := by unfold kMode0; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith

/-- The steps before the first play: the setup, the preparation (with PG) and part A of round `0`. -/
theorem df2B0_le (d n : ℕ) (hd : 1 ≤ d) (r0 R0 δ : ℝ) :
    df2L.NS + 2 * df2L.NA + 4 * d + 7 + kPre d n r0 R0 δ + kDf2A d (df2oPar d n δ).j + 3 ≤
      Conj1Arith.kPGNS d r0 R0 (df2oPar d n δ).δ1 + 1006 * d ^ 2 * ((df2oPar d n δ).j + 1) := by
  have hA := kDf2A_le d (df2oPar d n δ).j hd
  have hM := kMode0_le d hd
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  have h3 := Nat.mul_le_mul_left (df2oPar d n δ).j h2
  unfold kPre
  simp only [df2L]
  nlinarith

/-- `log (2 d n / δ) ≥ 1 / 2`. -/
theorem df2_log_ge (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 / 2 ≤ Real.log (2 * d * n / δ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) h2
  linarith

end AdversarialBco.Poly.Mach.VL
