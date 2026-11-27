/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRc

@[expose] public section

/-!
# The tail of BL's round, part d: the units of R12

`r12Units_mono`: the units of R12 FIRE (`r12Units`, Bit/Transfer/XBLR12.lean) grow with the bound `X`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

theorem r12Units_mono (d : ℕ) {X X' : ℕ} (h : X ≤ X') : r12Units d X ≤ r12Units d X' := by
  unfold r12Units; gcongr

end AdversarialBco.Bit.Transfer.BLM
