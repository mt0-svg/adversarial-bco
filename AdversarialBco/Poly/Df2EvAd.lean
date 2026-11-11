/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdG
public import AdversarialBco.Poly.Df2EvAdY
public import AdversarialBco.Poly.Df2EvAdLQ
public import AdversarialBco.Poly.Df2EvAdSDF
public import AdversarialBco.Poly.Df2EvAdDQ
public import AdversarialBco.Poly.Df2EvAdE1
public import AdversarialBco.Poly.Poly32OTop

@[expose] public section

/-!
# The five budgets and E1-loc with an adapted parameter

The adapted setting `Df2OnSetEAd` (Df2SetEAd.lean): the loss of round `s` read at `θ s`, measurable in `𝒢 s`.

* `df2EvBudgetsAd`: the five budgets G, Y, LQ, S-DF, DQ on it, outright;
* `df2Det_holds : Df2Det`, DET from its proved inputs, and `df2E1LocAd_holds : Df2E1LocAd`, E1-loc on it;
* `theoremPoly32O_via_ad : TheoremPoly32O`, the frozen theorem with its five budgets read from the adapted ones
  through `df2OnSetE_of_ad`, a check that the adapted budgets contain the fixed ones (the delivered proof is
  `theoremPoly32O_holds`, Poly32OFinal.lean, which does not import this module).
-/

namespace AdversarialBco.Poly

/-- The five budgets with an adapted parameter. -/
theorem df2EvBudgetsAd :
    Df2EvGPropAd ∧ Df2EvYPropAd ∧ Df2EvLQPropAd ∧ Df2EvSDFPropAd ∧ Df2EvDQPropAd :=
  ⟨EvAd.df2EvGPropAd_holds, EvAd.df2EvYPropAd_holds, EvAd.df2EvLQPropAd_holds, EvAd.df2EvSDFPropAd_holds,
    EvAd.df2EvDQPropAd_holds⟩

/-- DET from its proved inputs: the layer-1 Props, Lemma D.14, the facts `Df2SIFacts` and the rows. -/
theorem df2Det_holds : Df2Det :=
  df2DetOf_holds df2LayerOne_holds lemmaW SIF.df2SIFacts_holds df2RowsHold

/-- E1-loc with an adapted parameter: the epoch fails with probability at most `(149/168) δ_e`. -/
theorem df2E1LocAd_holds : Df2E1LocAd :=
  df2E1LocAdOf_holds df2Det_holds EvAd.df2EvGPropAd_holds EvAd.df2EvYPropAd_holds EvAd.df2EvLQPropAd_holds
    EvAd.df2EvSDFPropAd_holds EvAd.df2EvDQPropAd_holds

/-- The frozen Theorem POLY32-O, its five budgets read from the adapted ones (`df2OnSetE_of_ad`). -/
theorem theoremPoly32O_via_ad : TheoremPoly32O :=
  theoremPoly32O_of_open SIF.df2SIFacts_holds (df2EvGProp_of_ad EvAd.df2EvGPropAd_holds)
    (fun _ => df2EvYProp_of_ad EvAd.df2EvYPropAd_holds) (fun _ => df2EvLQProp_of_ad EvAd.df2EvLQPropAd_holds)
    (fun _ => df2EvSDFProp_of_ad EvAd.df2EvSDFPropAd_holds) (fun _ => df2EvDQProp_of_ad EvAd.df2EvDQPropAd_holds)

end AdversarialBco.Poly
