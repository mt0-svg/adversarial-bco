/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.Main
public import AdversarialBco.UnifiedLower.Main

@[expose] public section

/-!
# Corollary MATCH (release v2.3)

The solution module of the Comparator configuration config-match.json, which certifies `corollaryMatch`
next to the five witnesses of Unified/Sanity.lean and the nine of UnifiedLower/Sanity.lean, all imported here.

`corollaryMatch_of_prog`: `CorollaryMatch` from the setup contract `ProgSetupO` and the contract of the round's tail
`ProgTail`, by `theoremUnified_of_prog` (Unified/Main.lean), `theoremLowerUProg` (UnifiedLower/Main.lean) and
`corollaryMatch_of_unified_lower` (UnifiedLower/Sanity.lean). `corollaryMatch : CorollaryMatch`: the two contracts
are proved (`progSetupO`, Unified/ProgOSetupAll.lean; `progTail_holds`, Unified/TailOAll.lean).
-/

namespace AdversarialBco

/-- **Corollary MATCH from the setup contract and the tail's contract.** -/
theorem corollaryMatch_of_prog (hS : Unified.ProgO.ProgSetupO) (ht : Unified.ProgO.ProgTail) : CorollaryMatch :=
  UnifiedLower.LowerSanity.corollaryMatch_of_unified_lower (theoremUnified_of_prog hS ht) theoremLowerUProg

/-- **Corollary MATCH.** -/
theorem corollaryMatch : CorollaryMatch :=
  corollaryMatch_of_prog Unified.ProgO.progSetupO Unified.ProgO.progTail_holds

end AdversarialBco
