/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1LowerPoly
public import AdversarialBco.Conj1Lower.Main
public import AdversarialBco.Conj1LowerPoly.Cube

@[expose] public section

/-!
# The lower half of Conjecture 1 on a polytope of the class, non-oblivious reading (the lower bound on a polytope)

The solution module of config-conj1-lower-poly.json: `TheoremConj1LowerPoly`
(StatementConj1LowerPoly.lean) on the cube `[-1, 1]^d`, the rows `± e_j` with right-hand sides `1`. The cube is convex,
contains `B(0, 1/2)` and lies in `B(0, √d)` with `1 ≤ √d ≤ d` (Cube.lean), so `Lower.Top.lowerBody_of_inputs` applies
with `R0 = √d` and the hypotheses `lowerTopInputs` (Conj1Lower/Main.lean); the class conditions are
those of AdversarialBco/Conj1Poly/Sanity.lean (`cube_height`, `cube_ball`, `cube_diam`).
-/

open MeasureTheory

namespace AdversarialBco

open Lower RealRAM RealRAM.Conj1PolySanity

theorem theoremConj1LowerPoly_holds : TheoremConj1LowerPoly := by
  intro d hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hR1, hRd⟩ := sqrt_nat_bounds d hd1
  refine ⟨2 * d, cubeA d, cubeB d, rfl, cube_height d, ⟨0, cube_ball d⟩, fun n hn => ⟨?_, ?_⟩⟩
  · intro x hx y hy
    calc dist x y ≤ ((2 * d : ℕ) : ℝ) := cube_diam hd1 x hx y hy
      _ ≤ n := by
        have h2 : 2 * d ≤ d ^ 10 :=
          calc 2 * d ≤ d * d := Nat.mul_le_mul_right d (by omega)
            _ = d ^ 2 := by ring
            _ ≤ d ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
        exact_mod_cast h2.trans hn
  · intro Ω _ μ hμ pol hpol
    exact Top.lowerBody_of_inputs lowerTopInputs hd hn (convex_polytope _ _) (half_ball_subset_cube d)
      (cube_subset_ball d) hR1 hRd μ hpol

end AdversarialBco
