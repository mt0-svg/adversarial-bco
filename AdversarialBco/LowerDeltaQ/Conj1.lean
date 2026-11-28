/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Statement
public import AdversarialBco.LowerDeltaQ.Sanity
public import AdversarialBco.LowerDelta.Cube
public import AdversarialBco.Conj1LowerPolyD.Main

@[expose] public section

/-!
# The lower half of Conjecture 1 on a polytope of the class, at `3.71·10^-9`

`theoremConj1LowerPolyDQ_holds : TheoremConj1LowerPolyDQ` (StatementMinimaxQ.lean) on the cube `[-1, 1]^d`, the rows
`± e_j` with right-hand sides `1`, with clause (b) of `theoremLowerUDQ` on the cube (`a = 0`, `r0 = 1`, `R0 = √d`,
`UnifiedLower.Cube.bodyU_cube`): the polytope is the cube (`polytope_cube_eq`), and a strategy of `StratsLowU` at the
inner radius `1`
is in `StratsLip` (`stratsLowU_one_subset`). The Comparator configuration config-minimax-q.json certifies it from the
solution module LowerDeltaQ/Minimax.lean, next to the witnesses of LowerDeltaQ/Sanity.lean and
Conj1LowerPolyD/Sanity.lean.
-/

open MeasureTheory

namespace AdversarialBco

open Lower RealRAM RealRAM.Conj1PolySanity LowerDelta

/-- **The lower half of Conjecture 1 on a polytope of the class, the mean `3.71·10^-9 d^{3/2} n^{1/2} / log d`
derived from the probability form.** -/
theorem theoremConj1LowerPolyDQ_holds : TheoremConj1LowerPolyDQ := by
  intro d hd
  have hd1 : 1 ≤ d := by omega
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
    have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
    rw [polytope_cube_eq] at hpol ⊢
    obtain ⟨σ, hσ, hint, hge⟩ := (LowerDeltaQ.theoremLowerUDQ d hd1 n hn1 0 1 (Real.sqrt d) _
      (UnifiedLower.Cube.bodyU_cube hd1) Ω _ μ hμ pol hpol).2.1 hd hn
    exact ⟨σ, stratsLowU_one_subset _ hσ, hint, hge⟩

end AdversarialBco
