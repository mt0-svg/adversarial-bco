/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailAsm
public import AdversarialBco.UW.ProgMachMagW
public import AdversarialBco.UW.ProgMachMagExp
public import AdversarialBco.UW.ProgMachTailData
public import AdversarialBco.UW.ProgMachTailCall

@[expose] public section

/-!
# `progTailW : ProgTailW`

R5 to R15 of BL-OW's round in mode `run` on the machine: `progTailW_of` (UW/ProgMachTailAsm.lean) at BL-OW's
magnitudes `magBLW`, its exponent contract `expBLW`, and the tail's sub-block contracts `dataTW_holds`,
`dataLW_holds`, `fireW_holds` (UW/ProgMachTailData.lean) and `callW_holds` (UW/ProgMachTailCall.lean).
-/

namespace AdversarialBco.UW.ProgW

/-- **`ProgTailW`**: the tail of BL-OW's round on the machine. -/
theorem progTailW : ProgTailW :=
  progTailW_of magBLW expBLW dataTW_holds dataLW_holds fireW_holds callW_holds

end AdversarialBco.UW.ProgW
