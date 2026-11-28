import Lean
import AdversarialBco.UW.TheoremU
import AdversarialBco.LowerDeltaQ.Minimax
import AdversarialBco.Matched.Main
import AdversarialBco.Conj1BitHP.Main

/-! For the badges of ci.yml: the hypotheses of the main theorems of the six configurations (the binders whose type
is a proposition, with the definitions at the head of the type unfolded, so that a premise hidden in a definition such
as `TheoremUW` counts) and the axioms they use. Run with `lake env lean code/formal-proof/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``AdversarialBco.theoremUnified, ``AdversarialBco.UW.theoremUW,
      ``AdversarialBco.LowerDeltaQ.theoremLowerUDQ, ``AdversarialBco.LowerDeltaQ.theoremLowerUDProgQ,
      ``AdversarialBco.LowerDeltaQ.theoremMinimaxQ, ``AdversarialBco.theoremConj1LowerPolyDQ_holds,
      ``AdversarialBco.Grow.theoremGrowG, ``AdversarialBco.Grow.theoremGrowGProg,
      ``AdversarialBco.Matched.theoremMinimaxMatched, ``AdversarialBco.theoremConj1UpperBitHP] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescopeReducing c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
