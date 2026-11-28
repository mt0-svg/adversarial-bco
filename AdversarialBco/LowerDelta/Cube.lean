/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDelta.Main
public import AdversarialBco.StatementMinimax
public import AdversarialBco.UnifiedLower.Small
public import AdversarialBco.UnifiedLower.Prog
public import AdversarialBco.UnifiedLower.Cube

@[expose] public section

/-!
# Strategies of `StratsLowU` at the inner radius `1`

`stratsLowU_one_subset`: at the inner radius `1` a strategy of `StratsLowU K n 1` is in `StratsLip K n`, the class of
`TheoremConj1Lower` and of the lower bound on a polytope: its losses are `1/4`-Lipschitz on `E d`, hence on `K`.
-/

open MeasureTheory

namespace AdversarialBco.LowerDelta

open Lower RealRAM UnifiedLower Minimax

/-- A strategy of `StratsLowU K n 1` is in `StratsLip K n`. -/
theorem stratsLowU_one_subset {d n : ℕ} (K : Set (E d)) : StratsLowU K n 1 ⊆ StratsLip K n := by
  rintro σ ⟨hσ, h⟩
  refine ⟨hσ, fun t ht x o o' => ⟨(h t ht x o o').1, fun y _ z _ => ?_⟩⟩
  simpa using (h t ht x o o').2.2 y z

end AdversarialBco.LowerDelta
