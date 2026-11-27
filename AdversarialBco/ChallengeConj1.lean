/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-conj1.json: the theorem `theoremConj1Upper` and three non-vacuity witnesses, each
-- proved by `sorry`, over the copy of AdversarialBco/StatementConj1.lean (code/formal-proof/challenges.sh). Nothing
-- imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1

@[expose] public section

open MeasureTheory

namespace AdversarialBco

/-- The upper bound on a convex body given by a membership oracle, on the real RAM: the theorem that the solution
module `AdversarialBco.Conj1.Main` proves. -/
theorem theoremConj1Upper : TheoremConj1Upper := by
  sorry

namespace RealRAM.Conj1Sanity

/-- The hypotheses hold together for every `d` and `n`, with a strategy of the class whose loss of round `1` reads the
observation of round `0`. -/
theorem hyps_satisfiable_exists (d n : ℕ) :
    ∃ (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ν : Measure (ℕ → ℝ)),
      0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
        K ⊆ Metric.closedBall 0 R0 ∧ σ ∈ Strats K n ∧ NoiseOK ν ∧
        ∀ (x : Fin 1 → E d) (y : E d), σ 1 x (fun _ => 0) y ≠ σ 1 x (fun _ => 1) y := by
  sorry

/-- The law of the runs in the regret clause is a probability measure for every noise law that meets `NoiseOK`. -/
theorem isProbabilityMeasure_runs (ν : Measure (ℕ → ℝ)) (h : NoiseOK ν) :
    IsProbabilityMeasure (gaussStream.prod ν) := by
  sorry

/-- The empty program never plays: it fails the cost clause on every instance. -/
theorem nil_not_costOKAd {d : ℕ} (g : GameAd d) (n : ℕ) (r0 R0 δ B0 B : ℝ) :
    ¬ CostOKAd [] g (init d n r0 R0 δ) n B0 B := by
  sorry

end RealRAM.Conj1Sanity

end AdversarialBco
