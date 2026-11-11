/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Poly32OTop
public import AdversarialBco.Poly.Df2SIFactsProof
public import AdversarialBco.Poly.Df2EvGProof
public import AdversarialBco.Poly.Df2EvYProof
public import AdversarialBco.Poly.Df2EvSIDQ
public import AdversarialBco.Poly.Df2EvSISDF

@[expose] public section

/-!
# Theorem POLY32-O

`theoremPoly32O_holds`: the frozen `TheoremPoly32O` (StatementPoly.lean), from `theoremPoly32O_of_open`
(Poly32OTop.lean) with its open hypotheses discharged: the facts of SI (`SIF.df2SIFacts_holds`), the budgets Gauss
(`EvGY.df2EvGProp_holds`) and Y (`EvGY.df2EvYProp_of`), LQ and DQ (`EvSI.df2EvLQProp_holds`,
`EvSI.df2EvDQProp_holds`, proved outright) and S-DF (`EvSI.SDF.df2EvSDFProp_of`).
-/

namespace AdversarialBco

/-- Theorem POLY32-O of the frozen statement (`AdversarialBco/StatementPoly.lean`). -/
theorem theoremPoly32O_holds : TheoremPoly32O :=
  Poly.theoremPoly32O_of_open Poly.SIF.df2SIFacts_holds Poly.EvGY.df2EvGProp_holds Poly.EvGY.df2EvYProp_of
    (fun _ => Poly.EvSI.df2EvLQProp_holds) Poly.EvSI.SDF.df2EvSDFProp_of (fun _ => Poly.EvSI.df2EvDQProp_holds)

end AdversarialBco
