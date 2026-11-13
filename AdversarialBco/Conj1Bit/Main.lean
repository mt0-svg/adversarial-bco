/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDrvMain
public import AdversarialBco.Bit.Transfer.XEllRoute
public import AdversarialBco.Bit.Transfer.XBLPrepF
public import AdversarialBco.Bit.Transfer.XBLRowF
public import AdversarialBco.Bit.Transfer.XCallBL
public import AdversarialBco.Bit.Transfer.XBLDataTF
public import AdversarialBco.Bit.Transfer.XBLDataLF
public import AdversarialBco.Bit.Transfer.XBLCommit
public import AdversarialBco.Bit.Transfer.XBLFire
public import AdversarialBco.Bit.Transfer.XBLExp
public import AdversarialBco.Bit.Transfer.XBLMag
public import AdversarialBco.Bit.Transfer.XBLTailRe
public import AdversarialBco.Bit.Transfer.XBLRoundP
public import AdversarialBco.Conj1Bit.Exp

@[expose] public section

/-!
# The bit-model upper bound (solution module of config-conj1-bit.json)

The contracts of BL's program, proved: one call of the projection routine (`callBL`, from `ellRule`, `callPrepBL`,
`rowBL`), the tail of a round in mode `run` (`tailBL`, from `callBL`, `dataT`, `dataL`, `commitBL`, `fireBL`,
`expBL`), and one round (`roundBL_of : TailBL → MagBL → ExpBL → RoundBL`, Bit/Transfer/XBLRoundP.lean).
`theoremConj1UpperBit_of_round`: `TheoremConj1UpperBit` from the round contract `RoundBL`
(Bit/Transfer/XBLRound.lean), through `theoremConj1UpperBit_of_roundBL` (Bit/Transfer/XDrvMain.lean).
`theoremConj1UpperBit` is the theorem of the challenge; `theoremConj1UpperBit_exp` (Conj1Bit/Exp.lean) applies to it.
-/

namespace AdversarialBco

namespace Bit.Transfer.BLM

/-- **One call of BL's projection routine.** -/
theorem callBL : CallBL :=
  callBL_of ellRule PrepM.callPrepBL RowM.rowBL

/-- **The tail of BL's round in mode `run`** (R10 to R15). -/
theorem tailBL : TailBL :=
  tailBL_of callBL DataM.dataT DataM.dataL commitBL fireBL expBL

end Bit.Transfer.BLM

/-- `TheoremConj1UpperBit` from the round contract. -/
theorem theoremConj1UpperBit_of_round (h : Bit.Transfer.BLM.RoundBL) : TheoremConj1UpperBit :=
  Bit.Transfer.BLM.theoremConj1UpperBit_of_roundBL h

/-- `TheoremConj1UpperBit` from a proof of the round with the signature of `roundBL_of`
(Bit/Transfer/XBLRoundP.lean). -/
theorem theoremConj1UpperBit_of_roundOf
    (hR : Bit.Transfer.BLM.TailBL → Bit.Transfer.BLM.MagBL → Bit.Transfer.BLM.ExpBL → Bit.Transfer.BLM.RoundBL) :
    TheoremConj1UpperBit :=
  theoremConj1UpperBit_of_round (hR Bit.Transfer.BLM.tailBL Bit.Transfer.BLM.magBL Bit.Transfer.BLM.expBL)

/-- **The bit-model upper bound** (the theorem of config-conj1-bit.json). -/
theorem theoremConj1UpperBit : TheoremConj1UpperBit :=
  theoremConj1UpperBit_of_roundOf Bit.Transfer.BLM.roundBL_of

end AdversarialBco
