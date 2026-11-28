/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1LowerPolyD
public import AdversarialBco.LowerDelta.Cube
public import AdversarialBco.Conj1Poly.Sanity
public import AdversarialBco.Conj1LowerPolyD.Sanity

@[expose] public section

/-!
# The cube as a polytope of the class, for the lower half of Conjecture 1

`polytope_cube_eq`: the polytope of the rows `± e_j` with right-hand sides `1` (`cubeA`, `cubeB` of
AdversarialBco/Conj1Poly/Sanity.lean) is the cube `{x | ∀ i, |x i| ≤ 1}` (`mem_cube_iff`), the polytope on which the
lower half of Conjecture 1 on a polytope of the class is proved (LowerDeltaQ/Conj1.lean). The module imports the
witnesses of Conj1LowerPolyD/Sanity.lean.
-/

open MeasureTheory

namespace AdversarialBco

open Lower RealRAM RealRAM.Conj1PolySanity LowerDelta

/-- The polytope of the rows `± e_j` with right-hand sides `1` is the cube `{x | ∀ i, |x i| ≤ 1}`. -/
theorem polytope_cube_eq (d : ℕ) : polytope (cubeA d) (cubeB d) = {x : E d | ∀ i, |x i| ≤ 1} :=
  Set.ext mem_cube_iff

end AdversarialBco
