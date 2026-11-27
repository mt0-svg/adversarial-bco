/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1
public import AdversarialBco.Conj1Poly.Sanity

@[expose] public section

/-!
# Non-vacuity of the statement `TheoremConj1Upper` (StatementConj1.lean)

The witnesses stated after `theoremConj1Upper` in the challenge (ChallengeConj1.lean) are proved here under the same
names.

* The hypotheses hold together for every dimension `d` and every horizon `n`: the closed unit ball with
  `r₀ = R₀ = 1`, `δ = 1/2`, the noiseless game (`noiseOK_dirac`, Conj1Poly/Sanity.lean) and a strategy of the class
  that reads the observations: from round `1` on its loss is the last observation clipped to `[0, 1]`, so the loss of
  round `1` takes the value `0` after the observation `0` and the value `1` after the observation `1`
  (`hyps_satisfiable_exists`).
* The law of the runs in the regret clause, `gaussStream.prod ν`, is a probability measure for every noise law `ν`
  that meets `NoiseOK` (`isProbabilityMeasure_runs`): the clause bounds a probability, never the junk measure `0`.
* The existential is not witnessed for free: the empty program never plays, so it fails the cost clause on every
  instance (`nil_not_costOKAd`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.RealRAM.Conj1Sanity

/-- A strategy that reads the history: from round `1` on, the loss is the constant `min 1 |o (t - 1)|`, the last
observation clipped to `[0, 1]`. -/
noncomputable def lastObs (d : ℕ) : Strategy d := fun t _ o _ =>
  if h : 0 < t then min 1 |o ⟨t - 1, by omega⟩| else 0

/-- `lastObs` is in the class on every convex body, for every horizon. -/
theorem lastObs_mem {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) : lastObs d ∈ Strats K n := by
  intro t _
  refine ⟨fun x o => ⟨convexOn_const _ hK, fun _ _ => ?_⟩, fun y _ => ?_⟩
  · unfold lastObs
    split_ifs
    · exact ⟨le_min zero_le_one (abs_nonneg _), min_le_left _ _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · unfold lastObs
    split_ifs with h
    · exact measurable_const.min (continuous_abs.measurable.comp ((measurable_pi_apply _).comp measurable_snd))
    · exact measurable_const

/-- The hypotheses of `TheoremConj1Upper` hold together for every `d` and `n`, with a strategy of the class whose loss
of round `1` reads the observation of round `0`. -/
theorem hyps_satisfiable_exists (d n : ℕ) :
    ∃ (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ν : Measure (ℕ → ℝ)),
      0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
        K ⊆ Metric.closedBall 0 R0 ∧ σ ∈ Strats K n ∧ NoiseOK ν ∧
        ∀ (x : Fin 1 → E d) (y : E d), σ 1 x (fun _ => 0) y ≠ σ 1 x (fun _ => 1) y := by
  refine ⟨1, 1, 1 / 2, Metric.closedBall 0 1, lastObs d, Measure.dirac 0, one_pos, le_rfl, by norm_num,
    by norm_num, isCompact_closedBall _ _, convex_closedBall _ _, subset_rfl, subset_rfl,
    lastObs_mem (convex_closedBall _ _) n, Conj1PolySanity.noiseOK_dirac, fun x y => ?_⟩
  simp [lastObs]

/-- The law of the runs in the regret clause is a probability measure for every noise law that meets `NoiseOK`. -/
theorem isProbabilityMeasure_runs (ν : Measure (ℕ → ℝ)) (h : NoiseOK ν) :
    IsProbabilityMeasure (gaussStream.prod ν) := by
  have := h.1
  have : IsProbabilityMeasure gaussStream := by unfold gaussStream; infer_instance
  infer_instance

/-- The empty program never plays, so it fails the cost clause on every instance. -/
theorem nil_not_costOKAd {d : ℕ} (g : GameAd d) (n : ℕ) (r0 R0 δ B0 B : ℝ) :
    ¬ CostOKAd [] g (init d n r0 R0 δ) n B0 B := by
  have hrun : ∀ k, runAd [] g (init d n r0 R0 δ) k = init d n r0 R0 δ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [runAd, Function.iterate_succ_apply', ← runAd, ih]; simp [stepAd, step]
  intro h
  have h1 := h.1
  rw [hrun] at h1
  simp [init] at h1

end AdversarialBco.RealRAM.Conj1Sanity
