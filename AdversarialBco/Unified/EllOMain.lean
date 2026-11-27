/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOProof
public import AdversarialBco.Unified.SepGrid

@[expose] public section

/-!
# UNI-ELL: statements (a) and (b), unconditional

`ellOAcc_of` (EllOProof.lean) with Lemma SEP on the grid (`sepAcc`, SepGrid.lean) and the accuracy of the bisection
gauge (`gaugeAcc`, SepMath.lean).
-/

namespace AdversarialBco.Uni.EllO

/-- **Statement (b)** of ELL-O and BIS-O, (HQ-O). -/
theorem ellOAcc : EllOAcc := ellOAcc_of sepAcc gaugeAcc

end AdversarialBco.Uni.EllO
