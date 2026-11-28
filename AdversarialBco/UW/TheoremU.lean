/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Main
public import AdversarialBco.UW.ToUnified
public import AdversarialBco.Unified.Sanity

@[expose] public section

/-!
# Theorem U as the corollary of Theorem UW

`theoremUnified : TheoremUnified` is `UW.theoremUnified_of_UW UW.theoremUW`: Theorem U at the constant `2 max(C, 0)`,
with the program, the cost constants and the coin windows of Theorem UW (UW/ToUnified.lean).

The solution module of the Comparator configurations of StatementUnified.lean and StatementUW.lean in the release
(config-unified.json, config-uw.json): it imports the non-vacuity witnesses of Unified/Sanity.lean.
-/

namespace AdversarialBco

/-- **Theorem U** (`TheoremUnified`), the corollary of Theorem UW. -/
theorem theoremUnified : TheoremUnified :=
  UW.theoremUnified_of_UW UW.theoremUW

end AdversarialBco
