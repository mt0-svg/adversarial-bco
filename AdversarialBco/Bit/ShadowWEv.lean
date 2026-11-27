/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowAz
public import AdversarialBco.Bit.ShadowWDet
public import AdversarialBco.Bit.ShadowStep2
public import AdversarialBco.Poly.Df2EvAdV

@[expose] public section

/-!
# W-EV: the measurability of P°'s epoch with the checked advice

The virtual epoch of P° started before round `a < n` is an instance of the advice form `Df2OnSetEAdV`
(Poly/Df2SetEAdV.lean). This file holds its clause (L1), jointly in the advice: `epochMeasV_inst` (`gauge_kTh_meas`,
`ext_kTh_measAd`, `nextAdv_measurable` on the graph of `K_ε` of `kTh`, `keps_kTh_graph`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Poly.Conj1 (lamAt ext_kTh_measAd)

variable {d : ℕ}

/-- The graph of `K_ε` of the body of the instance is measurable. -/
theorem keps_kTh_graph {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K) (ε : ℝ) :
    MeasurableSet {q : PgSp d × (Fin d → ℝ) | q.2 ∈ df2KepsOf (kTh n δ K q.1) ε} := by
  have hm : Measurable fun q : PgSp d × (Fin d → ℝ) => (q.1, (WithLp.toLp 2 ((1 - ε)⁻¹ • q.2) : E d)) :=
    measurable_fst.prodMk ((PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_const_smul ((1 - ε)⁻¹) |>.comp measurable_snd))
  exact (mem_kTh_meas (n := n) (δ := δ) hKc hKconv PgMeas.pgGoodMeas).preimage hm

/-- (L1) with the checked advice for the instance of P°'s epoch at the start round `a`: the gauge and the extensions
measurable, the round map after the observation jointly in the advice. -/
theorem epochMeasV_inst {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) (heps0 : 0 < (df2oPar d n δ).eps)
    (heps1 : (df2oPar d n δ).eps < 1) {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ}
    (hadm : ∀ t < n, ∀ l, AdmLoss K (L t l)) (hm : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y)
    (a : ℕ) :
    Df2EpochMeasV (df2oPar d n δ) n (n - a) (fun x : PgSp d × Λ => kTh n δ K x.1)
      (fun s x => gTh n δ K (fun t => L t x.2) a s x.1) (apAdv (d := d)) := by
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · have h := gauge_kTh_meas (n := n) (δ := δ) hKc hKconv PgMeas.pgGoodMeas hR hmw
    have h2 := h.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd :
      Measurable fun x : (PgSp d × Λ) × E d => (x.1.1, x.2))
    rw [Function.comp_def] at h2
    exact h2
  · exact ext_kTh_measAd hKc hKconv PgMeas.pgGoodMeas hR hmw heps0 heps1 (fun l => (hadm (a + s) (by omega) l).1)
      (hm (a + s) (by omega))
  · have h := nextAdv_measurable (df2oPar d n δ) n (fun q => df2KepsOf (kTh n δ K q) (df2oPar d n δ).eps)
      (keps_kTh_graph hKc hKconv _)
    have h2 := h.comp (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd :
      Measurable fun x : ((PgSp d × Λ) × Adv d) × Df2St d × (Fin d → ℝ) × ℝ => ((x.1.1.1, x.1.2), x.2))
    rw [Function.comp_def] at h2
    exact h2

end AdversarialBco.Bit.Cpl
