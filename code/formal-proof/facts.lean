import Lean
import AdversarialBco.Solution

/-! For the badges of ci.yml: the hypotheses of the theorems of config.json (the binders whose type is a
proposition, with the definitions at the head of the type unfolded, so that a premise hidden in a definition
such as `CorollaryADV` counts) and the axioms they use. Run with `lake env lean code/formal-proof/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``AdversarialBco.corollaryADV] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescopeReducing c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
