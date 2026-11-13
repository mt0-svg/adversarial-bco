/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdGV
public import AdversarialBco.Poly.Df2EvAdYV
public import AdversarialBco.Poly.Df2EvAdLQV
public import AdversarialBco.Poly.Df2EvAdSDFV
public import AdversarialBco.Poly.Df2EvAdDQV
public import AdversarialBco.Poly.Poly32OTop

@[expose] public section

/-!
# The five budgets with an adapted parameter and an advice per round

`df2EvBudgetsAdV`: the budgets G, Y, LQ, S-DF, DQ on `Df2OnSetEAdV` (Df2SetEAdV.lean), the routine of round `s`
being `apθ (ψ s ω)` with `ψ s` measurable in `𝒢 (s + 1)`.
-/

namespace AdversarialBco.Poly

/-- The five budgets with an adapted parameter and an advice per round. -/
theorem df2EvBudgetsAdV :
    Df2EvGPropAdV ∧ Df2EvYPropAdV ∧ Df2EvLQPropAdV ∧ Df2EvSDFPropAdV ∧ Df2EvDQPropAdV :=
  ⟨EvAd.df2EvGPropAdV_holds, EvAd.df2EvYPropAdV_holds, EvAd.df2EvLQPropAdV_holds, EvAd.df2EvSDFPropAdV_holds,
    EvAd.df2EvDQPropAdV_holds⟩

end AdversarialBco.Poly
