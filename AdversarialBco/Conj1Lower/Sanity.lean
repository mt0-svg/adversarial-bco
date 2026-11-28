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
# Helper lemmas for the lower bound on a polytope

* The run: the transcript's points are the points played (`transcript_fst`), its observations are those of `obsAd`
  (`transcript_snd`), and the losses of the regret are the losses the learner faced (`lossAd_plays`).
* The regret against the zero strategy is `0` for every play rule (`regretAd_zero`), and the zero strategy is in
  `StratsLip K n` (`zeroStrat_mem`).
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

/-- The transcript of the rounds before `t` reads the strategy of the rounds before `t` only. -/
theorem transcript_congr {σ σ' : Strategy d} (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (∀ u < t, σ u = σ' u) → transcript σ ε p t = transcript σ' ε p t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := transcript_congr ε p t fun u hu => h u (by omega)
    simp only [transcript, ih, h t (by omega)]

/-- Non-anticipation of the learner: the point of round `t` reads the strategy of the rounds before `t` only, that is
the losses of the rounds before `t`. -/
theorem plays_congr {σ σ' : Strategy d} (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) (h : ∀ u < t, σ u = σ' u) :
    plays σ ε p t = plays σ' ε p t := by
  simp only [plays, transcript_congr ε p t h]

/-- The points of the rounds `t < n` of a rule with values in `K` are in `K`. -/
theorem plays_mem {K : Set (E d)} {n : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d)
    (hp : ∀ t < n, ∀ x o, p t x o ∈ K) {t : ℕ} (ht : t < n) : plays σ ε p t ∈ K :=
  hp t ht _ _

/-! ## The bound -/

theorem log_ge_one {d : ℕ} (hd : 4000000 ≤ d) : 1 ≤ Real.log d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-! ## The zero strategy does not witness the claim -/

/-- The zero strategy: the loss `0` at every round. -/
def zeroStrat (d : ℕ) : Strategy d := fun _ _ _ _ => 0

theorem zeroStrat_mem {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) : zeroStrat d ∈ StratsLip K n := by
  refine ⟨fun t _ => ⟨fun x o => ⟨convexOn_const 0 hK, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩,
    fun _ _ => measurable_const⟩, fun t _ x o o' => ⟨rfl, fun y _ z _ => ?_⟩⟩
  simp only [zeroStrat, sub_self, abs_zero]
  positivity

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

/-! ## Integrability over the class -/

theorem measurable_snoc {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {t : ℕ} {f : α → Fin t → β}
    {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => Fin.snoc (α := fun _ => β) (f a) (g a) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact hg
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp hf

/-! ## A learner that randomises at every round -/

/-- The Gaussian stream is a probability measure. -/
instance : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

end AdversarialBco.Lower.Sanity
