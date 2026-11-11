/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-conj1-poly.json: the theorems proved by `sorry` over the copies of the statement files
-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are
-- expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Poly

@[expose] public section

namespace AdversarialBco

/-- Theorem 1.3 (a): the theorem that the solution module `AdversarialBco.Conj1Poly.Main` proves. -/
theorem theoremConj1UpperPoly : TheoremConj1UpperPoly := by
  sorry

/-- Remark 1.2 implies Theorem 1.3 (a). -/
theorem theoremConj1UpperPoly_of_conj1 : TheoremConj1Upper → TheoremConj1UpperPoly := by
  sorry

end AdversarialBco
