/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupCall
public import AdversarialBco.Bit.Transfer.XBLSetupRows
public import AdversarialBco.Bit.Transfer.XBLR2q

@[expose] public section

/-!
# BL's setup on the machine: the copies of PARAM's values

`prmCopies_cover`: every slot `y` with `4 ≤ y < 22` receives a copy of a value of PARAM.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

theorem prmCopies_cover : ∀ y < 22, 4 ≤ y → ∃ p ∈ prmCopies, p.1 = y := by decide

end AdversarialBco.Bit.Transfer.BLM
