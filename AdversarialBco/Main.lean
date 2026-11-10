/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Lemmas
public import AdversarialBco.Body

@[expose] public section

/-!
# Corollary 1.2

The closing module of the formalization: Corollary 1.2, from Theorem 7.2 for the learner of Algorithm 7.1 and
Proposition 2.2.
-/

/-- Corollary 1.2 of the frozen statement (`AdversarialBco/Statement.lean`): the proof of Corollary 1.2 for the learner of Algorithm 7.1
(`corollaryADV_of_bodyH`, in `Lemmas.lean`) on hypothesis (H) of the inner body (`body_H`, in `Body.lean`). -/
theorem AdversarialBco.corollaryADV : AdversarialBco.CorollaryADV :=
  AdversarialBco.corollaryADV_of_bodyH AdversarialBco.body_H
