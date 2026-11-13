/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1BitExp
public import AdversarialBco.Conj1Bit.Main
public import AdversarialBco.Conj1Bit.Exp

@[expose] public section

/-!
# The bit-model theorem in expectation

`theoremConj1UpperBitExp_of_bit`: `TheoremConj1UpperBit` implies `TheoremConj1UpperBitExp`, by
`theoremConj1UpperBit_exp` (Conj1Bit/Exp.lean), whose conclusion is the statement word for word.
`theoremConj1UpperBitExp`: the statement, from `theoremConj1UpperBit` (Conj1Bit/Main.lean).
-/

namespace AdversarialBco

/-- `TheoremConj1UpperBit` gives `TheoremConj1UpperBitExp`. -/
theorem theoremConj1UpperBitExp_of_bit : TheoremConj1UpperBit → TheoremConj1UpperBitExp :=
  theoremConj1UpperBit_exp

/-- Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in the bit-cost model, in expectation. -/
theorem theoremConj1UpperBitExp : TheoremConj1UpperBitExp :=
  theoremConj1UpperBitExp_of_bit theoremConj1UpperBit

end AdversarialBco
