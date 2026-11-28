/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvG
public import AdversarialBco.UW.EvY
public import AdversarialBco.UW.EvMain
public import AdversarialBco.UW.EvDSDF
public import AdversarialBco.UW.SIFacts
public import AdversarialBco.UW.RowsEvNeeds

@[expose] public section

/-!
# The route `evProbOf` of Theorem UW

`evProbOfUW : RowsUW → CondIncrW → CondBiasW → LemmaUSetW → EvProbUW`, the field `evProbOf` of `AllUW`
(UW/Interfaces.lean): W-EV at the level `δc` (`evProbUW_of`, UW/EvMain.lean) from the five events of setting (E),

* (a) `evGPropUW` (UW/EvG.lean) and (b) `evYPropUW_of` (UW/EvY.lean);
* (c) `evLQPropUW_of` (UW/EvCLQ.lean), (d) `evSDFPropUW_of` (UW/EvDSDF.lean), (e) `evDQPropUW_of`
  (UW/EvEDQ.lean);

with the facts of SI at T4U (`sifactsUW`, UW/SIFacts.lean) and the needs of events (c) to (e) (`evNeedsUW`,
UW/RowsEvNeeds.lean). The wrapper's three Props are proved in the project (`condIncrW`, `condBiasW`,
`lemmaUSetW`) and enter the events through these files, so the route ignores its last three arguments.
-/

namespace AdversarialBco.UW

/-- **The route `evProbOf`**: W-EV at the level `δc` from the rows. -/
theorem evProbOfUW : RowsUW → CondIncrW → CondBiasW → LemmaUSetW → EvProbUW := fun hR _ _ _ =>
  evProbUW_of evGPropUW (evYPropUW_of sifactsUW hR) (evLQPropUW_of sifactsUW hR evNeedsUW)
    (evSDFPropUW_of sifactsUW hR evNeedsUW) (evDQPropUW_of sifactsUW hR evNeedsUW)

end AdversarialBco.UW
