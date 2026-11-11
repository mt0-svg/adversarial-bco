/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Explicit.Main
public import AdversarialBco.Body2.Main

@[expose] public section

/-!
# Theorem 1.5, Lemma 7.13 and Corollary 1.6 with explicit constants

The solution module of `config-explicit.json`: `TheoremExplicit` and `CorollaryExplicit`
(`AdversarialBco/StatementExplicit.lean`) from `theoremExplicit_of_bodyH` and `corollaryExplicit_of_bodyH`
(`AdversarialBco/Explicit/Main.lean`) at `BodySpec.bodyHExplicit` (`AdversarialBco/Body2/Main.lean`); `lemmaMarg` is
`AdversarialBco/Explicit/Marg.lean`.
-/

namespace AdversarialBco.Explicit

/-- Theorem 1.5 with its constants and its adaptive form. -/
theorem theoremExplicit : TheoremExplicit := theoremExplicit_of_bodyH BodySpec.bodyHExplicit

/-- Corollary 1.6 for the policies of Section 1. -/
theorem corollaryExplicit : CorollaryExplicit := corollaryExplicit_of_bodyH BodySpec.bodyHExplicit

end AdversarialBco.Explicit
