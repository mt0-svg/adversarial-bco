/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngBnd
public import AdversarialBco.UW.EngPlay
public import AdversarialBco.UW.EngC1b
public import AdversarialBco.UW.EngC2d
public import AdversarialBco.UW.ParamW

@[expose] public section

/-!
# The engine of BL-OW's record (Step 1 of SHADOW for Theorem UW)

`engineOfW`: the route `DomW → EngineRecUW (implW P C' k)` of `theoremUW_of_open` (UW/Main.lean), assembled from
piece C1 (`c1OW`, UW/EngC1b.lean), piece C2 (`c2OW`, UW/EngC2d.lean), the play (`playCOW`, UW/EngPlay.lean), the
regime of PARAM-W's reference (`schedUW`, UW/ParamW.lean) and the record induction (`engineRecW`, UW/EngBnd.lean).
`engineOfW_of` is the same route with piece C2 as a hypothesis.
-/

namespace AdversarialBco.UW.Eng

open AdversarialBco.UW.BLOW (implW schedUW)

/-- **The engine of BL-OW's record from piece C2 of the round.** -/
theorem engineOfW_of (h2 : C2OW) (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) :
    DomW → EngineRecUW (implW P C' k) :=
  fun _ => engineRecW (roundCOW_of c1OW h2) EngC.playCOW (regRefW_of_sched (schedUW P C' k)) P C' k

/-- **The engine of BL-OW's record** (Step 1 of SHADOW for Theorem UW). -/
theorem engineOfW (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : DomW → EngineRecUW (implW P C' k) :=
  engineOfW_of c2OW P C' k

end AdversarialBco.UW.Eng
