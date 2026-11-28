/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Stop

@[expose] public section

/-!
# Proposition STOP: the posterior before the first round is live

Proposition STOP (the paper's stopped balance) at the parameters of a `Good` strategy, for plays in `B(0, R0)`: Lemma
COUNT (b) at the prior gives that the posterior before the first round is live (`live_zero`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Stop

open RealRAM Bayes _root_.AdversarialBco.Lower.Top

/-! ## (F5) on the reals: the stopped sum of the dents -/

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-! ## (F4): the stopped live event fails only through a crossing or a dead posterior -/

section Live

omit [MeasurableSpace Ω] in
/-- The posterior before the first round is live when `N* > 0` (Lemma COUNT (b) at the prior, whose divergence is
`0`). -/
theorem live_zero {P : SParams} (hP : Good P d R0) (hX : Real.exp 1 / 2 ≤ xCount d (P.w d))
    (hN : 0 < nStar d (P.w d)) (pol : Learner Ω d) (s : Sample d Ω) : s ∈ liveSet P pol 0 := by
  by_contra h
  have hd' : dLive (P.w d) (covM (postT P pol 0 s)) < d / 2 := not_le.1 h
  have hR := ruleS_meas_prior hP
  obtain ⟨C, hC, hρC⟩ := dens_le_bound (prior d (1 / 2)) (ruleS d P) P.sc 0
    (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)
  have hρ : Measurable (dens (prior d (1 / 2)) (ruleS d P) P.sc 0
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)) := by
    have h' := (measurable_dens (prior d (1 / 2)) (ruleS d P) hR P.sc 0).comp
      (measurable_prodMk_left (x := hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s))
    exact h'
  have hc := count_b (by have := hP.d_pos; omega) hP.w_pos hX hρ hC hρC
    ((dens_props (prior d (1 / 2)) (ruleS d P) hR P.sc 0).2.2 _) hd'
  have h0 : klDens (prior d (1 / 2)) (dens (prior d (1 / 2)) (ruleS d P) P.sc 0
      (hist (prior d (1 / 2)) (ruleS d P) P.sc pol 0 s)) = 0 := klDens_one _
  linarith

end Live

end AdversarialBco.Lower.Stop
