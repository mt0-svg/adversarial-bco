/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1LowerPolyD
public import AdversarialBco.Conj1Lower.Sanity

@[expose] public section

/-!
# Sanity checks of the statement `TheoremConj1LowerPolyD` (AdversarialBco/StatementConj1LowerPolyD.lean)

The witness, stated with the definitions of the statement only:

* `constLearner_mem_of_mem`: on every body `K` with a point `c`, the constant learner at `c` on the seed space `Unit`
  is a learner of `IsLearnerAd K n`, so the inner implication of the statement is not vacuous.
-/

open MeasureTheory

namespace AdversarialBco.Lower.PolyDSanity

open RealRAM

/-- On every body `K` with a point `c`, the constant learner that plays `c` is a learner of the class, for every `n`. -/
theorem constLearner_mem_of_mem {d : ℕ} {K : Set (E d)} {c : E d} (hc : c ∈ K) (n : ℕ) :
    IsLearnerAd (Ω := Unit) K n (fun _ _ _ _ => c) :=
  fun _ _ => ⟨measurable_const, fun _ _ _ => hc⟩

end AdversarialBco.Lower.PolyDSanity
