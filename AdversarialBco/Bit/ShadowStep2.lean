/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowSetE
public import AdversarialBco.Bit.ShadowFarm
public import AdversarialBco.Poly.Df2PropGTools

@[expose] public section

/-!
# Step 2 of SHADOW: the measurability of the coupling bound

`tvB_measurable`: the bound `tvB` of the coupling lemma is measurable. Step 2 on an abstract coupled world is
`coupStepPropW_holds` (Unified/WorldShadow.lean).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

theorem tvB_measurable : Measurable fun x : ℝ × ℝ => tvB x.1 x.2 := by
  unfold tvB; fun_prop

end AdversarialBco.Bit.Cpl
