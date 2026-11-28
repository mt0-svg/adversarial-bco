/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPure

@[expose] public section

/-!
# The cells of an ELL-O call of BL-O's tail

`SCall`, `NCall`, `ACall`: the cells that one ELL-O call of BL-O writes, those of v2.1's call (`oE` up, the
preparation's).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The ELL-O call -/

/-- The cells a call writes: v2.1's (the block from `oE`, `rEE`, `aWE`, and the preparation's own cells). -/
def SCall (y : ℕ) : Prop := oE ≤ y ∨ SPrep y
def NCall (j : ℕ) : Prop := rEE ≤ j ∨ NPrep j
def ACall (a _k : ℕ) : Prop := aWE ≤ a ∨ APrep a

end AdversarialBco.Unified.ProgO
