/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowIface
public import AdversarialBco.Poly.Df2ApMeasTools

@[expose] public section

/-!
# The checked advice routine: measurability

* `continuous_ellF`: `(P, w, x) ↦ ellF P w x` is continuous;
* `meas_advOK`: along measurable families with a measurable graph of regions, the test of the candidate is a
  measurable event (a countable intersection over the rational points);
* `meas_apAdv`: the checked advice routine is measurable along measurable families, jointly in the advice, as
  `meas_apCall` (Poly/Df2ApMeasTools.lean) for `apCall`.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.Poly AdversarialBco.Poly.ApMeas

variable {d : ℕ}

theorem continuous_ellF :
    Continuous fun x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ) => ellF x.1 x.2.1 x.2.2 := by
  unfold ellF
  refine Continuous.mul continuous_const ?_
  refine Continuous.dotProduct ?_ ?_
  · exact (continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd)
  · exact continuous_fst.matrix_mulVec ((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd))

theorem measurable_ellF {X : Type*} [MeasurableSpace X] {P : X → Matrix (Fin d) (Fin d) ℝ} {w y : X → Fin d → ℝ}
    (hP : Measurable P) (hw : Measurable w) (hy : Measurable y) : Measurable fun x => ellF (P x) (w x) (y x) :=
  continuous_ellF.measurable.comp (hP.prodMk (hw.prodMk hy))

theorem measurable_advPick {X : Type*} [MeasurableSpace X] {v : X → Adv d} {e : X → ℝ} (hv : Measurable v)
    (he : Measurable e) : Measurable fun x => advPick (v x) (e x) := by
  unfold advPick
  exact Measurable.ite (measurableSet_le measurable_const he) hv.fst hv.snd

theorem meas_advOK {X : Type*} [MeasurableSpace X] (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q) {R : X → ℝ}
    {P : X → Matrix (Fin d) (Fin d) ℝ} {w y : X → Fin d → ℝ} {e : X → ℝ} (hR : Measurable R) (hP : Measurable P)
    (hw : Measurable w) (he : Measurable e) (hy : Measurable y) :
    MeasurableSet {x | advOK (Q x) (R x) (P x) (w x) (e x) (y x)} := by
  unfold advOK
  refine (hQ.mem hy).inter ((measurableSet_le (measurable_oNorm.comp hy) hR).inter ?_)
  have h2 : MeasurableSet (⋂ q : Fin d → ℚ, ({x | (fun i => (q i : ℝ)) ∈ Q x}ᶜ ∪
      {x | ellF (P x) (w x) (y x) ≤ ellF (P x) (w x) (fun i => (q i : ℝ)) + e x})) :=
    MeasurableSet.iInter fun q => (hQ.mem measurable_const).compl.union
      (measurableSet_le (measurable_ellF hP hw hy) ((measurable_ellF hP hw measurable_const).add he))
  have h3 : {x | ∀ q : Fin d → ℚ, (fun i => (q i : ℝ)) ∈ Q x →
      ellF (P x) (w x) (y x) ≤ ellF (P x) (w x) (fun i => (q i : ℝ)) + e x} =
      ⋂ q : Fin d → ℚ, ({x | (fun i => (q i : ℝ)) ∈ Q x}ᶜ ∪
        {x | ellF (P x) (w x) (y x) ≤ ellF (P x) (w x) (fun i => (q i : ℝ)) + e x}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    exact forall_congr' fun q => imp_iff_not_or
  rw [← h3] at h2
  exact h2

/-- The checked advice routine is measurable along measurable families, jointly in the advice. -/
theorem meas_apAdv {X : Type*} [MeasurableSpace X] (v : X → Adv d) (hv : Measurable v)
    (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (P : X → Matrix (Fin d) (Fin d) ℝ) (w : X → Fin d → ℝ) (e : X → ℝ)
    (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hP : Measurable P) (hw : Measurable w)
    (he : Measurable e) :
    Measurable fun x => apAdv (v x) (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x) := by
  classical
  have hy := measurable_advPick hv he
  unfold apAdv
  exact Measurable.ite (meas_advOK Q hQ hR hP hw he hy) (measurable_some'.comp hy)
    (meas_apCall Q hQ a0 r R P w e ha0 hr hR hP hw he)

end AdversarialBco.Bit.Cpl
