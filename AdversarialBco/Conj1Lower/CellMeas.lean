/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Cells

@[expose] public section

/-!
# The measurable structure of the genie's answers

The answers of the rule S' take values in `Option Cell` (`none` is the cell rest). Both types are finite and carry the
discrete σ-algebra. One home for these instances: every module of the lower bound that needs them imports this one.
-/

namespace AdversarialBco.Lower

instance Cell.instMeasurableSpace : MeasurableSpace Cell := ⊤

instance Cell.instMeasurableSpaceOption : MeasurableSpace (Option Cell) := ⊤

instance Cell.instDiscreteMeasurableSpace : DiscreteMeasurableSpace Cell := ⟨fun _ => trivial⟩

instance Cell.instDiscreteMeasurableSpaceOption : DiscreteMeasurableSpace (Option Cell) := ⟨fun _ => trivial⟩

example : MeasurableSingletonClass (Option Cell) := inferInstance

example : Fintype (Option Cell) := inferInstance

example : Inhabited (Option Cell) := inferInstance

end AdversarialBco.Lower
