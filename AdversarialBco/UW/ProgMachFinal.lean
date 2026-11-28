/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachMain
public import AdversarialBco.UW.PrmWSpec
public import AdversarialBco.UW.ProgMachTailW

@[expose] public section

/-!
# BL-OW's program on the oracle bit RAM

`theoremProgW`: some program `P` of the oracle bit RAM with cost constants `C'`, `k` plays BL-OW's pure plays
(`BLOWLink (implW P C' k)`) and meets the machine clauses of `TheoremUW` (`BLOMachOK P C' k`). It is
`theoremProgW_of_parts` (UW/ProgMachMain.lean) at PARAM-W's contract (`progParamW`, UW/PrmWSpec.lean) and
the tail's (`progTailW`, UW/ProgMachTailW.lean).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco.Unified.BLO (BLOMachOK)
open AdversarialBco.BitRAMO (InstrO)
open AdversarialBco.UW.BLOW (implW)

/-- **BL-OW's program text**: some program of the oracle bit RAM plays BL-OW's pure plays and meets the machine
clauses of `TheoremUW`. -/
theorem theoremProgW : ∃ (P : List InstrO) (C' : ℝ) (k : ℕ), BLOWLink (implW P C' k) ∧ BLOMachOK P C' k :=
  theoremProgW_of_parts PrmW.progParamW progTailW

end AdversarialBco.UW.ProgW
