/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngBnd
public import AdversarialBco.Unified.EngPlay
public import AdversarialBco.Unified.EngC1b

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record from C2

`engineRecO : RoundCO → PlayCO → EngineRecO` (Unified/EngBnd.lean) with piece C's play `playCO` (Unified/EngPlay.lean)
and C1 `c1O` (Unified/EngC1b.lean): `EngineRecO` follows from C2 alone.
-/

namespace AdversarialBco.Unified.Eng

open AdversarialBco.Unified.Asm (EngineRecO)

/-- **`EngineRecO` from C2** (the test call, the fire and line μ of piece C). -/
theorem engineRecO_of_C2 (h2 : C2O) : EngineRecO :=
  engineRecO (roundCO_of c1O h2) EngC.playCO

end AdversarialBco.Unified.Eng
