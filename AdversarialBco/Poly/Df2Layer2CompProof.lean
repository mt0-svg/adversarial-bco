/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldAz
public import AdversarialBco.Poly.Df2WorldDetProof
public import AdversarialBco.Poly.Df2CompProof
public import AdversarialBco.Poly.Df2DetProof

@[expose] public section

/-!
# DF2-O, second layer: the composition

`df2Layer2Comp : Df2Layer2Comp`, the chain of `Df2Layer2.lean`: DET (`df2DetOf_holds`, with the rows
`df2RowsHold`), E1-loc (`df2E1LocOf_holds`), Lemma 8.8 on the world (`df2VEWorldOf_holds`), the Azuma event on
the world (`df2AzWorldOf_holds`), Lemma 8.10 with the regret (`df2WorldDet_of`) and the last step
(`df2CompOf_holds`, with `df2Trivial_holds` outside the regime).
-/

namespace AdversarialBco.Poly

/-- The composition of the second layer. -/
theorem df2Layer2Comp : Df2Layer2Comp := by
  intro L1 W PAP PG PGM PGG SI EG EY ELQ ESDF EDQ AZ PROPG APM
  have DET := df2DetOf_holds L1 W SI df2RowsHold
  have E1 := df2E1LocOf_holds DET EG EY ELQ ESDF EDQ
  have VE := Layer2.df2VEWorldOf_holds E1 PAP PGM PGG APM
  have AZW := Layer2.df2AzWorldOf_holds AZ PGM PGG APM
  exact Layer2.df2CompOf_holds VE AZW (Layer2.df2WorldDet_of SI) PROPG PG PGM PGG df2Trivial_holds

end AdversarialBco.Poly
