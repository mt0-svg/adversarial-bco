/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataU
public import AdversarialBco.Bit.Transfer.XBLDataQ
public import AdversarialBco.Bit.Transfer.XBLCall
public import AdversarialBco.Bit.Transfer.XBLSetupParV
public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.PieceA.Enc

@[expose] public section

/-!
# The data of R11 TEST: the command `xdt`

`xdt`: `xdtC` (the constants, `P`, `f`), then `xdtF` at the first round of an epoch (the slot `sFirst` holds `1`),
else `xdtA`. The values of the slots come from `BLInv` in mode `run`: the fields of PARAM on the grid `2^{-pF}`
(`ε'`, `η'`, `ρ'`, `s'_b`, rounded by PARAM), `k'` on the grid `2^{-p}`, `1/ê` an integer, `Λ = d N_e`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The call data of R11 TEST. -/
def xdt (L : Layout) : XCmd := .seq (xdtC L) (xifS L sZ sFirst (xdtF L) (xdtA L))

theorem dtF_le (d : ℕ) : dtFUnits d + 1 ≤ dtAUnits d + 2 := by
  simp only [dtFUnits, dtAUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, eF2, eF5, eA0, eA1,
    eA2, eA3, eA5]
  nlinarith [Nat.zero_le (d * d * d)]

theorem dt_le (d : ℕ) : dtCUnits d + (dtAUnits d + 2) ≤ 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 := by
  simp only [dtCUnits, dtAUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, ieF, eA0, eA1, eA2,
    eA3, eA5]
  ring_nf
  nlinarith [Nat.zero_le (d * d * d)]

/-- An integer slot value within the bound of `BLInv`. -/
theorem bnd_sc {σ : Env d} {y E : ℕ} {w : ℤ} (hb : ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ E) (hv : σ.sc y = w) :
    |w| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb
  have : w = z := by rw [hv] at hz; exact_mod_cast hz
  rw [this]; exact bz

/-- An integer cell within the bound of `BLInv`. -/
theorem bnd_arr {σ : Env d} {a k E : ℕ} {w : ℤ} (hb : ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E) (hv : σ.arr a k = w) :
    |w| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb
  have : w = z := by rw [hv] at hz; exact_mod_cast hz
  rw [this]; exact bz

/-- An integer over `2^k` lies on the grid `2^{-k}`. -/
theorem onG_int_div (k : ℕ) (z : ℤ) : OnG k ((z : ℚ) / 2 ^ k) := by
  unfold OnG qn; rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

theorem onG_up' (k : ℕ) (x : ℚ) : OnG k (up k x) := onG_int_div k _

theorem onG_dn' (k : ℕ) (x : ℚ) : OnG k (dn k x) := onG_int_div k _

/-- A field on the grid `2^{-k}` as its numerator over `2^k`. -/
theorem grid_div {k : ℕ} {x : ℚ} (h : OnG k x) : x = (qn k x : ℚ) / ((2 ^ k : ℤ) : ℚ) := by
  rw [Int.cast_pow, Int.cast_ofNat]; exact eq_qn_div k h

end AdversarialBco.Bit.Transfer.BLM.DataM
