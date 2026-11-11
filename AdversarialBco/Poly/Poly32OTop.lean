/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2CompProof
public import AdversarialBco.Poly.Df2PlayProof
public import AdversarialBco.Poly.Df2R1Proof
public import AdversarialBco.Poly.WrapperProof
public import AdversarialBco.Poly.PgProcProof
public import AdversarialBco.Poly.PgMeasProof
public import AdversarialBco.Poly.Df2AzumaProof
public import AdversarialBco.Poly.Df2OracleProof
public import AdversarialBco.Poly.Df2PropGProof
public import AdversarialBco.Poly.Df2ApMeasProof
public import AdversarialBco.Poly.MachDf2Caps

@[expose] public section

/-!
# Theorem POLY32-O from what remains open

`theoremPoly32O_of_open`: `TheoremPoly32O` (StatementPoly.lean) from the hypotheses still open, every proved input
discharged: the layer-1 Props (`df2LayerOne_holds`), Lemma D.14, `PropAP`, Theorem 8.3 with `PgMeas` and `PgGoodMeas`, the
Azuma event, Lemma TV and Proposition G (`PropG.df2PropG`), condition (L1) of `apCall` (`ApMeas.df2ApCallMeas`), the
chain of the second layer (`df2Layer2Comp`), the passage to the theorem (`theoremPoly32O_of_df2oMeas`) and the machine
layer (`Mach.VL.df2oMachine`).

The open hypotheses: `Df2SIFacts`; the budget Gauss `Df2EvGProp` (`EvGY.df2EvGProp_holds` plugs in); the
budgets Y, LQ, S-DF, DQ, each in the form `Df2SIFacts → _`, so that a proof of the budget from the facts of `Df2SIFacts`, or outright (`fun _ => h`), plugs in directly.
-/

namespace AdversarialBco.Poly

open Mach.VL

/-- The layer-1 Props of `Df2.lean` and `Df2R1.lean`, all proved. -/
theorem df2LayerOne_holds : Df2LayerOne :=
  ⟨lemmaDFI_holds, lemmaMON_holds, propINC2_holds, lemmaD2_holds, lemmaONS2Core_holds, lemmaZCore_holds,
    df2RowZ_holds, playShift_holds, lemmaUBPrime_holds, playHess_holds, df2Trivial_holds, df2Carriers_holds,
    lemmaR1i, lemmaR1ii, lemmaR1iii, lemmaR1iv, lemmaR1v⟩

/-- The regret clause of DF2-O from the facts of SI and the four open budgets. -/
theorem df2ORegretMeas_of_open (SI : Df2SIFacts) (EG : Df2EvGProp) (EY : Df2SIFacts → Df2EvYProp)
    (ELQ : Df2SIFacts → Df2EvLQProp) (ESDF : Df2SIFacts → Df2EvSDFProp) (EDQ : Df2SIFacts → Df2EvDQProp) :
    Df2ORegretMeas :=
  df2Layer2Comp df2LayerOne_holds lemmaW propAP pgThm PgMeas.pgMeas PgMeas.pgGoodMeas SI EG (EY SI) (ELQ SI)
    (ESDF SI) (EDQ SI) df2AzumaEvent.{0} PropG.df2PropG ApMeas.df2ApCallMeas

/-- Theorem POLY32-O from the open hypotheses of the analysis and the machine layer `Df2OMachine`. -/
theorem theoremPoly32O_of_open_machine (SI : Df2SIFacts) (EG : Df2EvGProp) (EY : Df2SIFacts → Df2EvYProp)
    (ELQ : Df2SIFacts → Df2EvLQProp) (ESDF : Df2SIFacts → Df2EvSDFProp) (EDQ : Df2SIFacts → Df2EvDQProp)
    (hM : Df2OMachine) : TheoremPoly32O :=
  theoremPoly32O_of_df2oMeas (df2ORegretMeas_of_open SI EG EY ELQ ESDF EDQ) hM

/-- Theorem POLY32-O from what remains open: the facts of SI and the budgets Gauss, Y, LQ, S-DF, DQ. -/
theorem theoremPoly32O_of_open (SI : Df2SIFacts) (EG : Df2EvGProp) (EY : Df2SIFacts → Df2EvYProp)
    (ELQ : Df2SIFacts → Df2EvLQProp) (ESDF : Df2SIFacts → Df2EvSDFProp) (EDQ : Df2SIFacts → Df2EvDQProp) :
    TheoremPoly32O :=
  theoremPoly32O_of_open_machine SI EG EY ELQ ESDF EDQ df2oMachine

end AdversarialBco.Poly
