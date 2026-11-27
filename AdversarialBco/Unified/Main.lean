/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.Sanity
public import AdversarialBco.Unified.AsmMain
public import AdversarialBco.Unified.AsmThr
public import AdversarialBco.Unified.AsmMeas
public import AdversarialBco.Unified.AsmPos
public import AdversarialBco.Unified.AsmBits
public import AdversarialBco.Unified.AsmMeasRec
public import AdversarialBco.Unified.ProgORound
public import AdversarialBco.Unified.EngMain
public import AdversarialBco.Unified.EngC2d
public import AdversarialBco.Unified.TailOAsm
public import AdversarialBco.Unified.TailOAll
public import AdversarialBco.Unified.ProgOSetupAll

@[expose] public section

/-!
# `TheoremUnified` (release v2.3, the upper half)

The solution module of the Comparator configuration config-unified.json, which imports the sanity module
whose witnesses the configuration certifies next to the theorem.

`theoremUnified_of_asm`: `TheoremUnified` from the named hypotheses `AsmU` of the assembly (Unified/AsmMain.lean,
`theoremUnified_of`). Five of them are proved: the arithmetic `ThrO` (`thrO`, Unified/AsmThr.lean), the measurability
of the regret `RegMeasU` (`regMeasU`, Unified/AsmMeas.lean), (POS) for BL-O's record `PosRecO` (`posRecO`,
Unified/AsmPos.lean), the bit clause (O4) `BitsRecO` (`bitsRecO`, Unified/AsmBits.lean) and (O4-M) `MeasRecO`
(`measRecO`, Unified/AsmMeasRec.lean). `theoremUnified_of_open`: `TheoremUnified` from the open ones, `AsmOpen`: the
setup and round contracts of BL-O's program text (`ProgSetupO`, `ProgRoundO`) and the engine hypothesis of SHADOW on
BL-O's record (`EngineRecO`).

`theoremUnified_of_prog`: `TheoremUnified` from the setup contract `ProgSetupO` and the contract of the round's tail
`ProgTail`, with the round from its sub-blocks (`progRoundO_of_tail`, Unified/ProgORound.lean) and the engine
hypothesis proved (`engineRecO_of_C2 c2O`, Unified/EngMain.lean and Unified/EngC2d.lean). `theoremUnified`: the setup
contract `progSetupO` (Unified/ProgOSetupAll.lean) and the tail's `progTail_holds` (Unified/TailOAll.lean) are proved.
-/

namespace AdversarialBco

/-- **Theorem U from the named hypotheses of the assembly.** -/
theorem theoremUnified_of_asm (h : Unified.Asm.AsmU) : TheoremUnified :=
  Unified.Asm.theoremUnified_of h

/-- The named hypotheses of the assembly that are still open. -/
structure Unified.Asm.AsmOpen : Prop where
  setup : Unified.ProgO.ProgSetupO
  round : Unified.ProgO.ProgRoundO
  engine : Unified.Asm.EngineRecO

/-- **Theorem U from the open hypotheses.** -/
theorem theoremUnified_of_open (h : Unified.Asm.AsmOpen) : TheoremUnified :=
  theoremUnified_of_asm ⟨h.setup, h.round, Unified.Asm.posRecO, Unified.Asm.measRecO, Unified.Asm.bitsRecO,
    h.engine, Unified.Asm.regMeasU, Unified.Asm.thrO⟩

/-- **Theorem U from the setup contract and the tail's contract**: the round from its sub-blocks, the engine proved. -/
theorem theoremUnified_of_prog (hS : Unified.ProgO.ProgSetupO) (ht : Unified.ProgO.ProgTail) : TheoremUnified :=
  theoremUnified_of_open ⟨hS, Unified.ProgO.progRoundO_of_tail ht, Unified.Eng.engineRecO_of_C2 Unified.Eng.c2O⟩

/-- **Theorem U.** -/
theorem theoremUnified : TheoremUnified :=
  theoremUnified_of_prog Unified.ProgO.progSetupO Unified.ProgO.progTail_holds

end AdversarialBco
