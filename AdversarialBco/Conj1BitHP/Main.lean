/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.Main
public import AdversarialBco.Unified.PolyMain
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# The bit-model upper bound with high probability (solution module of config-conj1-bit-hp.json)

`theoremConj1UpperBitHP`: `TheoremConj1UpperBitHP` (StatementConj1BitHP.lean) from Theorem U, by
`conj1BitHP_of_unified` (Unified/PolyMain.lean) at `theoremUnified` (Unified/Main.lean).
`theoremConj1UpperBit_of_hp`: the statement contains `TheoremConj1UpperBit`, with the majorant `R = max (Reg, 0)`,
measurable since `Reg` is, and `∫⁻ R = ENNReal.ofReal (∫ max (Reg, 0))` since `max (Reg, 0)` is integrable and
nonnegative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace AdversarialBco

/-- **Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in the bit-cost model, in expectation and with high
probability** (the theorem of config-conj1-bit-hp.json), from Theorem U. -/
theorem theoremConj1UpperBitHP : TheoremConj1UpperBitHP :=
  conj1BitHP_of_unified theoremUnified

/-- `TheoremConj1UpperBitHP` implies `TheoremConj1UpperBit`. -/
theorem theoremConj1UpperBit_of_hp : TheoremConj1UpperBitHP → TheoremConj1UpperBit := by
  rintro ⟨P, C, C', k, hP⟩
  refine ⟨P, C, C', k, ?_⟩
  intro d hd n hn m M A b hH hball hdiam Θ _ ρ hρ σ hσ
  obtain ⟨hrun, hmeas, hi, hint, -⟩ := hP d hd n hn m M A b hH hball hdiam Θ ρ hρ σ hσ
  refine ⟨hrun, fun ω => Real.toNNReal _, hmeas.real_toNNReal, fun ω => Real.le_coe_toNNReal _, ?_⟩
  calc _ = ENNReal.ofReal (∫ ω, max (RealRAM.regretPts (RealRAM.polytope A b)
          (RealRAM.lossAd (σ ω.1) 0 (BitRAM.playedBit P ⟨σ ω.1, ω.2⟩ (BitRAM.initBit d n m A b)))
          (BitRAM.playedBit P ⟨σ ω.1, ω.2⟩ (BitRAM.initBit d n m A b)) n) 0 ∂(ρ.prod BitRAM.coinStream)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hi.pos_part
          (Filter.Eventually.of_forall fun ω => le_max_right _ _)]
        refine lintegral_congr fun ω => ?_
        simp only [ENNReal.ofReal, ENNReal.coe_inj]
        ext
        simp [Real.coe_toNNReal']
    _ ≤ _ := ENNReal.ofReal_le_ofReal hint

end AdversarialBco
