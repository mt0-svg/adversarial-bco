/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.CompAd
public import AdversarialBco.Conj1.WorldAzAd
public import AdversarialBco.Poly.Df2EvAd
public import AdversarialBco.Poly.Poly32OTop
public import AdversarialBco.Poly.Df2SIFactsProof

@[expose] public section

/-!
# `TheoremConj1Upper`

The chain in strategy form, as `df2Layer2Comp` (Df2Layer2CompProof.lean) for a fixed sequence: E1-loc in its adapted
form (`df2E1LocAd_holds`), Lemma 8.8 and the Azuma event on the world of a loss process (`df2VEWorldAdOf_holds`,
`df2AzWorldAdOf_holds`), Lemma 8.10 (`df2WorldDet_of` with the facts of SI), Proposition 8.11
(`PropGAd.df2PropGAd`), Theorem 8.3 with `PgMeas` and `PgGoodMeas`, condition (L1) of `apCall`, the trivial bound, and
the composition `df2ORegretMeasAd_of`. With the machine layer (`theoremConj1Upper_of_regret`, Top.lean) this is the
frozen `TheoremConj1Upper` (StatementConj1.lean).
-/

namespace AdversarialBco.Poly

/-- The regret clause of DF2-O against a strategy. -/
theorem df2ORegretMeasAd_holds : Df2ORegretMeasAd :=
  Conj1.df2ORegretMeasAd_of
    (Conj1.df2VEWorldAdOf_holds df2E1LocAd_holds propAP PgMeas.pgMeas PgMeas.pgGoodMeas ApMeas.df2ApCallMeas)
    (Conj1.df2AzWorldAdOf_holds df2AzumaEvent.{0} PgMeas.pgMeas PgMeas.pgGoodMeas ApMeas.df2ApCallMeas)
    (Layer2.df2WorldDet_of SIF.df2SIFacts_holds) PropGAd.df2PropGAd pgThm PgMeas.pgMeas PgMeas.pgGoodMeas
    df2Trivial_holds

end AdversarialBco.Poly

namespace AdversarialBco

/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee against a strategy, as frozen in StatementConj1.lean. -/
theorem theoremConj1Upper_holds : TheoremConj1Upper :=
  Poly.theoremConj1Upper_of_regret Poly.df2ORegretMeasAd_holds

end AdversarialBco
