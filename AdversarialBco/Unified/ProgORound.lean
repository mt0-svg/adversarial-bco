/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOR1
public import AdversarialBco.Unified.ProgOR2s
public import AdversarialBco.Unified.ProgOOG
public import AdversarialBco.Unified.ProgOR3

@[expose] public section

/-!
# BL-O's round from its sub-blocks

`progRoundO_of_tail`: `ProgRoundO` from the tail's contract `ProgTail`, the five other sub-block contracts being proved
(`progR1a`, `progR2`, `progOG`, `progR3`, `progR1b`); `theoremProg_of_tail`: the program of UNI-PROG from the setup's
contract and the tail's.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open BitRAM BitRAMO

/-- **The round from the tail**: R1a, R2, the play off the run, R3 and R1b are proved. -/
theorem progRoundO_of_tail (ht : ProgTail) : ProgRoundO :=
  progRoundO_of progR1a progR2 progOG progR3 progR1b ht

/-- **UNI-PROG from the setup and the tail.** -/
theorem theoremProg_of_tail (hS : ProgSetupO) (ht : ProgTail) :
    ∃ (P : List InstrO) (C' : ℝ) (k : ℕ), BLOLink P ∧ BLOMachOK P C' k :=
  theoremProg_of hS (progRoundO_of_tail ht)

end AdversarialBco.Unified.ProgO
