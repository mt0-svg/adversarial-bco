/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOFld

@[expose] public section

/-!
# BL-O's round after R5: R7's tests, R7 to R9, the tail

BL's round after R5 for BL-O: from BL-O's invariant in mode `run` at round `t + 1` (after the reading) and the first
line's values in the slots `45 + k` (R5, R7's scalars), the command `xRunTO` (R7's two tests, `xMid`: R7's roots, R8,
R9, then a tail meeting BL-O's tail contract) ends in BL-O's invariant with the mode `stepO` gives. v2.1's pure lemmas
of the head run at `cfgH` (TailOPure.lean), a configuration of BL whose gauge at `X'` is BL-O's, so that its `pt'` is
BL-O's (`ptO_eq`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM AdversarialBco.Bit.RQ
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- R7's tests (`v1 6 > 0` or `v1 8 > 0` leave for `guard`), then R7's roots to R9 and the tail. -/
def xRunTO (xtail : Layout → XCmdO) (L : Layout) : XCmdO :=
  xifSO L sZ 51 (.base (xG L)) (xifSO L sZ 53 (.base (xG L)) (.seq (.base (xMid L)) (xtail L)))

end AdversarialBco.Unified.ProgO
