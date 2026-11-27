/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.ChainAd
public import AdversarialBco.Conj1.Sanity

@[expose] public section

/-!
# The upper bound on a convex body (solution module of config-conj1.json)

`theoremConj1Upper : TheoremConj1Upper` (StatementConj1.lean), from `theoremConj1Upper_holds` (ChainAd.lean). The
non-vacuity witnesses that the configuration names next to it are proved in Conj1/Sanity.lean.
-/

namespace AdversarialBco

/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee against a strategy, on a convex body given by a membership
oracle, as frozen in StatementConj1.lean. -/
theorem theoremConj1Upper : TheoremConj1Upper := theoremConj1Upper_holds

end AdversarialBco
