/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Sanity checks of the lower bound on a polytope (`TheoremConj1LowerPoly`, AdversarialBco/StatementConj1LowerPoly.lean)

* The run: the transcript's points are the points played (`transcript_fst`), its observations are those of `obsAd`
  (`transcript_snd`), and the losses of the regret are the losses the learner faced (`lossAd_plays`).
* The bound is positive (`bound_pos`).
* The learners exist: on every body with a point `c`, the constant learner that plays `c` is a learner of the class,
  for every `n` (`constLearner_mem_of_mem`).
* The existential is not witnessed for free: the regret against the zero strategy is `0` for every play rule
  (`regretAd_zero`), so on every nonempty body the zero strategy fails the bound against every learner
  (`zeroStrat_fails_of_nonempty`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Lower.Sanity

open RealRAM

variable {d : ℕ}

/-! ## The run -/

/-- The points of the transcript are the points played. -/
theorem transcript_fst (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (transcript σ ε p t).1 = fun i : Fin t => plays σ ε p i
  | 0 => funext fun i => i.elim0
  | t + 1 => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [transcript, plays]
    · simp [transcript, transcript_fst σ ε p t]

/-- The observations of the transcript are those of `obsAd` at the points played. -/
theorem transcript_snd (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (transcript σ ε p t).2 = obsAd σ ε (plays σ ε p) t
  | 0 => funext fun i => i.elim0
  | t + 1 => by
    have ih := transcript_snd σ ε p t
    have hf := transcript_fst σ ε p t
    simp only [transcript, obsAd]
    rw [← ih, ← hf]
    rfl

/-- The losses of the regret are the losses the learner faced: the loss of round `t` at the points played is the loss
that `σ` chose from the transcript before round `t`. -/
theorem lossAd_plays (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) :
    lossAd σ ε (plays σ ε p) t = σ t (transcript σ ε p t).1 (transcript σ ε p t).2 := by
  rw [transcript_fst, transcript_snd]
  rfl

/-! ## The bound -/

theorem log_ge_one {d : ℕ} (hd : 4000000 ≤ d) : 1 ≤ Real.log d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The bound of `TheoremConj1LowerPoly` is positive. -/
theorem bound_pos {d n : ℕ} (hd : 4000000 ≤ d) (hn : 1 ≤ n) :
    0 < 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog := log_ge_one hd
  have h1 : 0 < (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h3 : 0 < Real.log d := by linarith
  positivity

/-! ## The zero strategy does not witness the claim -/

/-- The zero strategy: the loss `0` at every round. -/
def zeroStrat (d : ℕ) : Strategy d := fun _ _ _ _ => 0

/-- The regret against the zero strategy is `0`, for every play rule. -/
theorem regretAd_zero {K : Set (E d)} (hK : K.Nonempty) (p : Policy d) (n : ℕ) :
    regretAd K (zeroStrat d) p n = 0 := by
  have h : (fun y => ∑ t ∈ Finset.range n, lossAd (zeroStrat d) (fun _ => 0)
      (plays (zeroStrat d) (fun _ => 0) p) t y) '' K = {0} := by
    simp only [lossAd, zeroStrat, Finset.sum_const_zero]
    exact hK.image_const 0
  unfold regretAd regretPts
  rw [h, csInf_singleton]
  simp [lossAd, zeroStrat]

/-! ## The Gaussian stream -/

/-- The Gaussian stream is a probability measure. -/
instance : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

/-! ## The learners exist, and the zero strategy fails the bound -/

/-- On every body `K` with a point `c`, the constant learner that plays `c` is a learner of the class, for every `n`:
on the polytope that `TheoremConj1LowerPoly` provides, which contains a ball, the learners it quantifies over exist. -/
theorem constLearner_mem_of_mem {d : ℕ} {K : Set (E d)} {c : E d} (hc : c ∈ K) (n : ℕ) :
    IsLearnerAd (Ω := Unit) K n (fun _ _ _ _ => c) :=
  fun _ _ => ⟨measurable_const, fun _ _ _ => hc⟩

/-- On every nonempty body, the zero strategy fails the bound of `TheoremConj1LowerPoly` against every learner: the
strategy that the theorem provides is not the trivial one. -/
theorem zeroStrat_fails_of_nonempty {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : K.Nonempty) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pol : Learner Ω d) :
    ¬ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n ∂μ := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hpos := bound_pos hd hn1
  have h0 : (fun ω => regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n) = fun _ => 0 :=
    funext fun ω => regretAd_zero hK _ n
  rw [h0, integral_zero]
  linarith

end AdversarialBco.Lower.Sanity
