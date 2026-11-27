/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower

@[expose] public section

/-!
# LOW-AFF: the affine transport of the lower-bound game

Lemma AFF (the paper's affine invariance), on the definitions of StatementConj1Lower.lean (`Policy`, `Learner`,
`IsLearnerAd`, `transcript`, `plays`, `regretAd`, `StratsLip`) and StatementConj1.lean (`Strategy`, `Strats`,
`obsAd`, `lossAd`). For an invertible affine map `T` of `ℝ^d`:

1. `isLearnerAd_push`: a learner on `K` pushed forward by `T` (`pushLearner`: play `T` of what the learner plays on the
   pulled-back history) is a learner on `T K`.
2. `pullStrat_mem_strats`: a strategy on `T K` pulled back by `T` (`pullStrat`: the loss `f' ∘ T` on the history
   pushed forward) is a strategy on `K`; `pullStrat_mem_stratsLipL`: reading the past points only is kept, and a
   loss `L`-Lipschitz on `T K` becomes `L M`-Lipschitz on `K` when `T` is `M`-Lipschitz (`StratsLipL`, the class
   `StratsLip` with the constant `L` in place of `1/4`; `stratsLip_eq`).
3. `transcript_push`, `plays_push`: the run of the pushed learner against `σ'` is the image by `T` of the run of the
   learner against the pulled strategy, with the same observations; `regretAd_push`: the regrets are equal, pointwise
   in the seed (`regretAd_pushLearner`), so integrability and the mean carry over.
-/

open MeasureTheory Metric

namespace AdversarialBco.Lower

open RealRAM

variable {d : ℕ}

/-! ## The transported objects -/

/-- The image of a play rule under `T`: on the history `y` of the new coordinates, play `T` of what `p` plays on the
pulled-back history `T⁻¹ y`. -/
noncomputable def pushPolicy (T : E d ≃ᵃ[ℝ] E d) (p : Policy d) : Policy d :=
  fun t y o => T (p t (fun i => T.symm (y i)) o)

/-- The image of a learner under `T`, seed by seed. -/
noncomputable def pushLearner {Ω : Type} (T : E d ≃ᵃ[ℝ] E d) (pol : Learner Ω d) : Learner Ω d :=
  fun t ω y o => T (pol t ω (fun i => T.symm (y i)) o)

/-- The pull-back of a strategy of the new coordinates: the loss `σ t (T x) o ∘ T`. -/
def pullStrat (T : E d ≃ᵃ[ℝ] E d) (σ : Strategy d) : Strategy d :=
  fun t x o z => σ t (fun i => T (x i)) o (T z)

/-- The strategies of `Strats K n` whose losses read the past points only and are `L`-Lipschitz on `K`. -/
def StratsLipL (K : Set (E d)) (n : ℕ) (L : ℝ) : Set (Strategy d) :=
  {σ | σ ∈ Strats K n ∧
    ∀ t < n, ∀ (x : Fin t → E d) (o o' : Fin t → ℝ), σ t x o = σ t x o' ∧
      ∀ y ∈ K, ∀ z ∈ K, |σ t x o y - σ t x o z| ≤ L * dist y z}

/-! ## Learners and strategies -/

theorem aff_measurable (T : E d ≃ᵃ[ℝ] E d) : Measurable (T : E d → E d) :=
  (AffineMap.continuous_of_finiteDimensional T.toAffineMap).measurable

/-- Lemma AFF (1): the pushed learner is a learner on `T K`. -/
theorem isLearnerAd_push {Ω : Type} [MeasurableSpace Ω] (T : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {n : ℕ}
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) : IsLearnerAd (T '' K) n (pushLearner T pol) := by
  have hT := aff_measurable T
  have hTs := aff_measurable T.symm
  intro t ht
  refine ⟨?_, fun ω y o => ⟨_, (hpol t ht).2 ω _ o, rfl⟩⟩
  have hg : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) =>
      (p.1, (fun i => T.symm (p.2.1 i)), p.2.2) :=
    measurable_fst.prodMk ((measurable_pi_iff.2 fun i => hTs.comp ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  exact hT.comp ((hpol t ht).1.comp hg)

/-- Lemma AFF (2): the pulled-back strategy is a strategy on `K`. -/
theorem pullStrat_mem_strats (T : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {n : ℕ} {σ : Strategy d}
    (hσ : σ ∈ Strats (T '' K) n) : pullStrat T σ ∈ Strats K n := by
  have hT := aff_measurable T
  intro t ht
  refine ⟨fun x o => ⟨?_, fun z hz => ((hσ t ht).1 _ o).2 (T z) ⟨z, hz, rfl⟩⟩, fun y hy => ?_⟩
  · have h := ((hσ t ht).1 (fun i => T (x i)) o).1.comp_affineMap T.toAffineMap
    convert h using 1
    all_goals first | rfl | exact (Set.preimage_image_eq K T.injective).symm
  · have hg : Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => ((fun i => T (h.1 i)), h.2) :=
      (measurable_pi_iff.2 fun i => hT.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
        measurable_snd
    exact ((hσ t ht).2 (T y) ⟨y, hy, rfl⟩).comp hg

/-- Lemma AFF (2) and (4): reading the past points only is kept, and the Lipschitz constant is multiplied by that of
`T`. -/
theorem pullStrat_mem_stratsLipL (T : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {n : ℕ} {σ : Strategy d} {L M : ℝ}
    (hL : 0 ≤ L) (hT : ∀ y z, dist (T y) (T z) ≤ M * dist y z) (hσ : σ ∈ StratsLipL (T '' K) n L) :
    pullStrat T σ ∈ StratsLipL K n (L * M) := by
  refine ⟨pullStrat_mem_strats T hσ.1, fun t ht x o o' => ⟨?_, fun y hy z hz => ?_⟩⟩
  · have h := (hσ.2 t ht (fun i => T (x i)) o o').1
    show (fun z => σ t (fun i => T (x i)) o (T z)) = fun z => σ t (fun i => T (x i)) o' (T z)
    rw [h]
  · have h := (hσ.2 t ht (fun i => T (x i)) o o).2 (T y) ⟨y, hy, rfl⟩ (T z) ⟨z, hz, rfl⟩
    calc |pullStrat T σ t x o y - pullStrat T σ t x o z| ≤ L * dist (T y) (T z) := h
      _ ≤ L * (M * dist y z) := mul_le_mul_of_nonneg_left (hT y z) hL
      _ = L * M * dist y z := by ring

/-! ## Runs and regret -/

/-- Lemma AFF (3): the transcript of the pushed rule against `σ` is the image by `T` of the transcript of the rule
against the pulled-back strategy, with the same observations. -/
theorem transcript_push (T : E d ≃ᵃ[ℝ] E d) (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, transcript σ ε (pushPolicy T p) t =
      ((fun i => T ((transcript (pullStrat T σ) ε p t).1 i)), (transcript (pullStrat T σ) ε p t).2)
  | 0 => Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0)
  | t + 1 => by
    have ih := transcript_push T σ ε p t
    simp only [transcript, ih, pushPolicy, AffineEquiv.symm_apply_apply, pullStrat]
    refine Prod.ext ?_ rfl
    exact (Fin.comp_snoc T _ _).symm

/-- The point of round `t` of the pushed rule is `T` of the point of the rule against the pulled-back strategy. -/
theorem plays_push (T : E d ≃ᵃ[ℝ] E d) (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) :
    plays σ ε (pushPolicy T p) t = T (plays (pullStrat T σ) ε p t) := by
  simp only [plays, transcript_push, pushPolicy, AffineEquiv.symm_apply_apply]

/-- The observations at the points `T x` against `σ` are those at `x` against the pulled-back strategy. -/
theorem obsAd_pull (T : E d ≃ᵃ[ℝ] E d) (σ : Strategy d) (ε : ℕ → ℝ) (x : ℕ → E d) :
    ∀ t, obsAd σ ε (fun s => T (x s)) t = obsAd (pullStrat T σ) ε x t
  | 0 => rfl
  | t + 1 => by simp only [obsAd, obsAd_pull T σ ε x t, pullStrat]

theorem lossAd_pull (T : E d ≃ᵃ[ℝ] E d) (σ : Strategy d) (ε : ℕ → ℝ) (x : ℕ → E d) (t : ℕ) (z : E d) :
    lossAd σ ε (fun s => T (x s)) t (T z) = lossAd (pullStrat T σ) ε x t z := by
  simp only [lossAd, obsAd_pull T σ ε x t, pullStrat]

/-- Lemma AFF (3): the regret of the pushed rule on `T K` against `σ` equals the regret of the rule on `K` against the
pulled-back strategy. -/
theorem regretAd_push (T : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (σ : Strategy d) (p : Policy d) (n : ℕ) :
    regretAd (T '' K) σ (pushPolicy T p) n = regretAd K (pullStrat T σ) p n := by
  have hpl : plays σ (fun _ => 0) (pushPolicy T p) = fun t => T (plays (pullStrat T σ) (fun _ => 0) p t) :=
    funext (plays_push T σ _ p)
  unfold regretAd regretPts
  rw [hpl, Set.image_image]
  simp only [lossAd_pull]

/-- The regrets of a learner and of its image are equal seed by seed. -/
theorem regretAd_pushLearner {Ω : Type} (T : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (σ : Strategy d) (pol : Learner Ω d)
    (n : ℕ) (ω : Ω) :
    regretAd (T '' K) σ (fun t => pushLearner T pol t ω) n = regretAd K (pullStrat T σ) (fun t => pol t ω) n :=
  regretAd_push T K σ (fun t => pol t ω) n

end AdversarialBco.Lower
