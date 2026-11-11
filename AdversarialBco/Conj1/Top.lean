/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.MachL
public import AdversarialBco.Conj1.RunAd

@[expose] public section

/-!
# `TheoremConj1Upper` from the machine layer and the analysis in strategy form

`conj1_of`: `Df2OMachineL` (MachL.lean) and `Df2ORegretMeasAd`, the regret clause of DF2-O against a strategy, give
`TheoremConj1Upper`. Every step is pathwise: the run of the program against a strategy is its run in the fixed world
of the losses the strategy chose on that run (`runAd_eq_run`), the machine layer applies there with `f` those losses
(they are admissible, `lossAd_mem`), and the points it plays below round `n` are those of `df2oPlayAd` by uniqueness
of the fixed point (`fix_unique`). With `df2oMachineL` proved, `theoremConj1Upper_of_regret` leaves
`Df2ORegretMeasAd` alone.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM Conj1

variable {d : ℕ}

/-- The analysis in strategy form: the regret clause of `TheoremConj1Upper` for the learner `df2oPlayAd`. -/
def Df2ORegretMeasAd : Prop :=
  ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ σ ∈ Strats K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts K (lossAd σ ω.2 (df2oPlayAd n r0 R0 δ K σ ω.2 ω.1)) (df2oPlayAd n r0 R0 δ K σ ω.2 ω.1) n} ≤
        ENNReal.ofReal δ

/-- The losses a strategy of the class chooses on any run are an admissible sequence. -/
theorem lossAd_mem {K : Set (E d)} {n : ℕ} {σ : Strategy d} (hσ : σ ∈ Strats K n) (ε : ℕ → ℝ) (x : ℕ → E d) :
    lossAd σ ε x ∈ Advs K n :=
  fun t ht => (hσ t ht).1 _ _

/-- The regret against a strategy reads the points of the rounds `t < n` only. -/
theorem regretAd_congr (K : Set (E d)) (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (n : ℕ)
    (h : ∀ t < n, x t = y t) : regretPts K (lossAd σ ε x) x n = regretPts K (lossAd σ ε y) y n := by
  unfold regretPts
  have hl : ∀ t ∈ Finset.range n, lossAd σ ε x t = lossAd σ ε y t := fun t ht =>
    lossAd_congr σ ε t fun i hi => h i (by rw [Finset.mem_range] at ht; omega)
  congr 1
  · exact Finset.sum_congr rfl fun t ht => by rw [hl t ht, h t (Finset.mem_range.1 ht)]
  · congr 1
    ext z
    simp only [Set.mem_image]
    refine exists_congr fun y' => and_congr_right fun _ => ?_
    rw [Finset.sum_congr rfl fun t ht => congrFun (hl t ht) y']

/-- `TheoremConj1Upper` from the machine layer with `n` inside the logarithm and the regret clause against a strategy:
on every run the program plays the points of `df2oPlayAd` below round `n`. -/
theorem conj1_of (hM : Df2OMachineL) (hR : Df2ORegretMeasAd) : TheoremConj1Upper := by
  obtain ⟨P, C', k, hP⟩ := hM
  obtain ⟨C, hC⟩ := hR
  refine ⟨P, C, C', k, fun d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub σ hσ ν hν => ?_⟩
  -- on every run, the points below round `n` are those of `df2oPlayAd`
  have key : ∀ gs noise : ℕ → ℝ,
      CostOKAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 δ) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k)
          (C' * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k) ∧
        ∀ t < n, playedAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 δ) t = df2oPlayAd n r0 R0 δ K σ noise gs t := by
    intro gs noise
    set g : GameAd d := ⟨K, σ, noise, gs⟩
    obtain ⟨hc, hpl⟩ := hP d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub _
      (lossAd_mem hσ noise (playedAd P g (init d n r0 R0 δ))) gs noise
    refine ⟨(costOKAd_iff P g _ n _ _).2 hc, ?_⟩
    have hfix : ∀ t < n, playedAd P g (init d n r0 R0 δ) t =
        df2oPlay d n r0 R0 δ ⟨K, lossAd σ noise (playedAd P g (init d n r0 R0 δ)), noise, gs⟩ t := by
      intro t ht
      exact (congrFun (playedAd_eq_played P g (init d n r0 R0 δ)) t).trans (hpl t ht)
    exact fix_unique n r0 R0 δ K σ noise gs _ hfix
  refine ⟨fun gs noise => ⟨(key gs noise).1, fun t ht => ?_⟩, ?_⟩
  · rw [(key gs noise).2 t ht, df2oPlayAd_fix]
    exact df2oPlay_mem d n r0 R0 δ hr0 K hball _ gs noise t
  · refine le_of_eq_of_le ?_ (hC d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub σ hσ ν hν)
    congr 1
    ext ω
    show (_ : ℝ) < _ ↔ (_ : ℝ) < _
    rw [regretAd_congr K σ ω.2 n (key ω.1 ω.2).2]

/-- `TheoremConj1Upper` from the regret clause of DF2-O against a strategy alone. -/
theorem theoremConj1Upper_of_regret (hR : Df2ORegretMeasAd) : TheoremConj1Upper :=
  conj1_of Mach.VL.df2oMachineL hR

end AdversarialBco.Poly
