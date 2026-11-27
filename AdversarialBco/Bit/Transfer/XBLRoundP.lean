/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadR
public import AdversarialBco.Bit.Transfer.XBLRoundG
public import AdversarialBco.Bit.Transfer.XBLExp
public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# One round of BL's program: the units of R5 to R9

`units_r57`, `units_mid`: the units of R5 and R7's scalars, and those of R7's roots to R9.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## The glue of the round -/

/-- The units of R5 and R7's scalars. -/
theorem units_r57 (d U : ℕ) : r57Units d U ≤ 200 * (d + U + 1) := by
  have h : SL.unitsP sl1Et sl1St = (0, 145) := by rfl
  unfold r57Units; rw [h]; simp only [ev]; omega

/-- The units of R7's roots to R9. -/
theorem units_mid (d U : ℕ) : midUnits d U ≤ 1000 * (d + U + 1) ^ 2 := by
  have h2 : SL.unitsP sl2Et sl2St = (276, 356) := by rfl
  have h3 : SL.unitsP sl3Et sl3St = (0, 52) := by rfl
  have e1 : ieBp.units = 36 := rfl
  have e2 : ieGh.units = 19 := rfl
  have e3 : ieGp.units = 5 := rfl
  have e4 : ieLp.units = 21 := rfl
  unfold midUnits r8Units r9aUnits r9bUnits map2Units
  rw [h2, h3, e1, e2, e3, e4]
  simp only [ev]
  nlinarith [Nat.zero_le (d * U), Nat.zero_le (d * d), Nat.zero_le (U * U)]

end AdversarialBco.Bit.Transfer.BLM
