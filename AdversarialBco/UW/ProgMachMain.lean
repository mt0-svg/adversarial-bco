/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachSetup
public import AdversarialBco.UW.ProgMachR1
public import AdversarialBco.UW.ProgMachR2
public import AdversarialBco.UW.ProgRec

@[expose] public section

/-!
# BL-OW's program on the oracle bit RAM

`theoremProgW_of_parts`: some program `P` of the oracle bit RAM with cost constants `C'`, `k` plays BL-OW's pure plays
(`BLOWLink (implW P C' k)`, UW/Interfaces.lean, UW/ProgRec.lean) and meets the machine clauses (`BLOMachOK P C' k`),
from PARAM-W's contract (`ParamWSpecS`) and the tail's (`ProgTailW`). The round's other
blocks are proved (`progR1aW`, `progR2W`, `progOGW`, `progR3W`, `progR1bW`), the setup from PARAM-W's contract
(`progSetupW`), and the assembly is BL-O's driver (`theoremProgW_of`).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (implW)
open BitRAM BitRAMO

/-- **BL-OW's round on the machine** from the tail's contract. -/
theorem progRoundW (ht : ProgTailW) : ProgRoundW :=
  progRoundW_of progR1aW progR2W progOGW progR3W progR1bW ht

/-- **BL-OW's program text** from PARAM-W's and the tail's contracts: some program of the oracle bit RAM plays BL-OW's
pure plays and meets the machine clauses of `TheoremUW`. -/
theorem theoremProgW_of_parts (hw : ∃ (xpw : Layout → XCmdO) (C k nS nN nA : ℕ), ParamWSpecS xpw C k nS nN nA)
    (ht : ProgTailW) : ∃ (P : List InstrO) (C' : ℝ) (k : ℕ), BLOWLink (implW P C' k) ∧ BLOMachOK P C' k := by
  obtain ⟨P, C', k, hL, hM⟩ := theoremProgW_of (progSetupW hw) (progRoundW ht)
  exact ⟨P, C', k, hL, hM⟩

end AdversarialBco.UW.ProgW
