/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UnifiedLower.Sanity
public import AdversarialBco.UnifiedLower.Body
public import AdversarialBco.UnifiedLower.Small
public import AdversarialBco.UnifiedLower.Prog
public import AdversarialBco.UnifiedLower.Cube

@[expose] public section

/-!
# `TheoremLowerU` and `TheoremLowerUProg` (release v2.3, the lower half)

The solution module of the Comparator configuration config-unified-lower.json: the two frozen theorems of
StatementUnifiedLower.lean, next to the witnesses of the sanity module, which this module imports.

* `theoremLowerU`: clauses (a) and (b) on every body of `BodyU` through the position of Theorem PG and the strategy of
  the tip in the class `StratsMid` (UnifiedLower/Body.lean: `lowerU_mean`, `lowerU_prob`), clause (c) by Lemma SMALL
  (UnifiedLower/Small.lean: `lowerU_small_mean`, `lowerU_small_prob`).
* `theoremLowerUProg`: from `theoremLowerU` by Lemmas BRIDGE and REAL (UnifiedLower/Prog.lean: `progU_of_lowerU`), on
  the run facts M1 and M2 of the oracle machine (Unified/RunFacts.lean).
* `theoremLowerU_cube`: `theoremLowerU` on the cube `[-1, 1]^d`, with `a = 0`, `r0 = 1`, `R0 = √d`
  (UnifiedLower/Cube.lean: `bodyU_cube`).
-/

namespace AdversarialBco

open UnifiedLower

/-- **Theorem LU, with Lemma SMALL.** -/
theorem theoremLowerU : TheoremLowerU := by
  intro d hd n hn a r0 R0 K hb Ω _ μ hμ pol hpol
  exact ⟨fun h1 h2 => ⟨Body.lowerU_mean h1 h2 hb μ hpol, Body.lowerU_prob h1 h2 hb μ hpol⟩,
    Small.lowerU_small_mean μ hd hn hb hpol, Small.lowerU_small_prob μ hd hn hb hpol⟩

/-- **Theorem LU for the programs of the oracle machine, in the objects of `TheoremUnified`.** -/
theorem theoremLowerUProg : TheoremLowerUProg :=
  Prog.progU_of_lowerU theoremLowerU

open Lower in
/-- **Theorem LU on the cube `[-1, 1]^d`** (`a = 0`, `r0 = 1`, `R0 = √d`): for every `d, n ≥ 1` and every measurable
randomised learner on the cube, (a) if `d ≥ 4·10^6` and `n ≥ d^10`, a strategy of `StratsLowU` on the cube at the
inner radius `1` with mean regret at least `7·10^-9 d^{3/2} n^{1/2} / log d`; (b) in the same range, one with regret
at least `2.8·10^-9 d^{3/2} n^{1/2} / log d` with probability at least `1/2`; (c) one with mean regret at least
`n^{1/2} / (4 √3)`, and one with regret at least `n^{1/2} / (8 √3)` with probability at least `1/48`. -/
theorem theoremLowerU_cube :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd {x : E d | ∀ i, |x i| ≤ 1} n pol →
      (4000000 ≤ d → d ^ 10 ≤ n →
        LowerMean {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol
            (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ∧
          LowerProb {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol
            (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2)) ∧
      LowerMean {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      LowerProb {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48) :=
  fun d hd n hn Ω _ μ hμ pol hpol =>
    theoremLowerU d hd n hn 0 1 (Real.sqrt d) _ (Cube.bodyU_cube hd) Ω _ μ hμ pol hpol

end AdversarialBco
