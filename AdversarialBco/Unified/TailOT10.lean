/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOT12

@[expose] public section

/-!
# BL-O's tail, R10 on the machine

The port of v2.1's `XV.t10` (Bit/Transfer/XBLTailRe.lean): `xtailO` is R10's sums (`xR10`), the two trace guards
`sc 88 < sc 89` (`B'`) and `sc 88 < sc 90` (`A'`), then R11 to R15 (`xT11O`). From `TIn` it ends in `RPost` with the
mode `tailModeO`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- **The tail of BL-O's round**: R10, its two guards, then R11 to R15. -/
def xtailO (xdt : Layout → XCmd) (xcall : Layout → XCmdO) (xfire xdl xcom : Layout → XCmd) (L : Layout) :
    XCmdO :=
  .seq (.base (xR10 L)) (xifSO L 88 89 (.base (xG L)) (xifSO L 88 90 (.base (xG L)) (xT11O xdt xcall xfire xdl xcom L)))

end AdversarialBco.Unified.ProgO
