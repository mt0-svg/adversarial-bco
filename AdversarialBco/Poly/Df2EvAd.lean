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
# DET and E1-loc with an adapted parameter

The adapted setting `Df2OnSetEAd` (Df2SetEAd.lean): the loss of round `s` read at `θ s`, measurable in `𝒢 s`.

* `df2Det_holds : Df2Det`, DET from its proved inputs;
* `df2E1LocAd_holds : Df2E1LocAd`, E1-loc on it, from DET and the five budgets G, Y, LQ, S-DF, DQ on it, proved
  outright (`EvAd.df2EvGPropAd_holds` to `EvAd.df2EvDQPropAd_holds`).
-/

namespace AdversarialBco.Poly

/-- DET from its proved inputs: the layer-1 Props, the restart-wrapper lemma, the facts `Df2SIFacts` and the rows. -/
theorem df2Det_holds : Df2Det :=
  df2DetOf_holds df2LayerOne_holds lemmaW SIF.df2SIFacts_holds df2RowsHold

/-- E1-loc with an adapted parameter: the epoch fails with probability at most `(149/168) δ_e`. -/
theorem df2E1LocAd_holds : Df2E1LocAd :=
  df2E1LocAdOf_holds df2Det_holds EvAd.df2EvGPropAd_holds EvAd.df2EvYPropAd_holds EvAd.df2EvLQPropAd_holds
    EvAd.df2EvSDFPropAd_holds EvAd.df2EvDQPropAd_holds

end AdversarialBco.Poly
