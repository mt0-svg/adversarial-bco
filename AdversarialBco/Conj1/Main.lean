/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.ChainAd
public import AdversarialBco.Conj1.Poly32O

@[expose] public section

/-!
# The solution module of the Comparator challenge of `TheoremConj1Upper`

The two theorems of `AdversarialBco/ChallengeConj1.lean` (config-conj1.json):
`theoremConj1Upper : TheoremConj1Upper` (ChainAd.lean) and `theoremPoly32O_of_conj1 : TheoremConj1Upper →
TheoremPoly32O` (Poly32O.lean).
-/

namespace AdversarialBco

/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee against a strategy, as frozen in StatementConj1.lean. -/
theorem theoremConj1Upper : TheoremConj1Upper := theoremConj1Upper_holds

end AdversarialBco
