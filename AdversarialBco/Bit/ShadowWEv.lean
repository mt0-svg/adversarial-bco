/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowRef
public import AdversarialBco.Poly.Df2EvAdV

@[expose] public section

/-!
# W-EV, and SHADOW without hypothesis on the reference

The virtual epoch of P° started before round `a < n` (`Run.ctx`, `Run.path`) is an instance of the advice form
`Df2OnSetEAdV` (Poly/Df2SetEAdV.lean), on the table:

* parameter `θ s = (S', lamAt n F.lam a s)` in `PgSp d × F.Λ`, body `kTh n δ K S'` (`body_kTh`), losses
  `gTh n δ K (F.L · l) a s S'` (`adm_gTh`), measurable in `cσ d (a + s)` (`lamAt_meas_c`);
* advice `ψ s = B.adv (a + s) ω (B.mode δ (a + s) ω)` in `Adv d`, measurable in `cσ d (a + s + 1)` (`adv_meas`,
  `mode_meas`), routine `apAdv` with `apAdv_spec`;
* (L1) jointly in the advice: `epochMeasV_inst` (`gauge_kTh_meas`, `ext_kTh_measAd`, `nextAdv_measurable` on the
  graph of `K_ε` of `kTh`, `keps_kTh_graph`);
* setting (E) on `fshift (cσ d) a`: `setE_ref` and `setE_shift`.

So the five budgets hold on the whole space (`Run.epoch_bound`), hence on `Case`: `wevProp_holds : WEvProp`, and
`shadowProp_holds : ShadowProp` through `shadowProp_of_wev` (Bit/ShadowRef.lean).
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

/-- The loss parameter of round `s` of the instance at the start `a < n` is known before round `a + s`. -/
theorem lamAt_meas_c {n : ℕ} {K : Set (E d)} (F : Df2LossProcF d n K (cσ d)) {a : ℕ} (ha : a < n) (s : ℕ) :
    Measurable[cσ d (a + s)] (lamAt n F.lam a s) := by
  unfold lamAt
  by_cases h : a + s < n
  · simp only [h, ↓reduceIte]
    exact F.lam_meas (a + s) h
  · simp only [h, ↓reduceIte]
    exact (F.lam_meas a ha).mono ((cσ d).mono (Nat.le_add_right a s)) le_rfl

namespace Run

variable {n : ℕ} {K : Set (E d)} {B : Run d n K} {δ : ℝ} {ν : Measure (ℕ → ℝ)}

/-- The virtual epoch of P° started before round `a < n` is an instance of the advice form of setting (E): every
bound of `Df2OnSetEAdV` holds for it on the whole coupled world. -/
theorem epoch_bound {k : ℝ} {Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop} (h : Df2OnSetEAdV k Bad)
    (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hν : NoiseOK ν)
    (hpos : Measurable[cσ d 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeas B) {a : ℕ} (ha : a < n) :
    μs ν {ω | Bad d (B.ctx δ a ω) (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (k * (df2oPar d n δ).δe) := by
  have := hν.1
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hmode := mode_meas B δ ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hpos hB hC
  have hE := setE_shift (μs ν) (cσ d) (ξc d) (fun t => B.eRef δ t)
    (setE_ref ν hν hB hC ⟨hd, hn, hδ0, hδ1, heps⟩ hKc hKconv hpos) a
  have hθ : ∀ s, Measurable[fshift (cσ d) a s] fun ω => (B.pos ω, lamAt n B.F.lam a s ω) := fun s =>
    (hpos.mono ((cσ d).mono (Nat.zero_le _)) le_rfl).prodMk (lamAt_meas_c B.F ha s)
  have hψ : ∀ s, Measurable[fshift (cσ d) a (s + 1)] fun ω => B.adv (a + s) ω (B.mode δ (a + s) ω) := fun s =>
    adv_meas B δ hB (hmode (a + s))
  exact h d n (n - a) δ hd hn (by omega) (Nat.sub_le n a) hδ0 hδ1 heps (PgSp d × B.F.Λ) (Adv d)
    (fun x => kTh n δ K x.1) (fun s x => gTh n δ K (fun t => B.F.L t x.2) a s x.1) apAdv
    (fun x => body_kTh hKc hKconv hR hmw x.1)
    (fun x s hs => adm_gTh (f := fun t => B.F.L t x.2) hKconv hKc hR hmw (B.F.adm (a + s) (by omega) x.2) x.1)
    (apAdv_spec hd) (epochMeasV_inst hKc hKconv hR hmw heps0 heps1 B.F.adm B.F.meas a)
    WΩ (μs ν) inferInstance (fshift (cσ d) a)
    (fun s ω => (B.pos ω, lamAt n B.F.lam a s ω)) (fun s ω => B.adv (a + s) ω (B.mode δ (a + s) ω))
    (fun s => ξc d (a + s)) (fun s => B.eRef δ (a + s)) hθ hψ (fun _ _ => rfl) hE

end Run

/-- The proposition of the reference on the coupled world: the five budgets of every virtual epoch of P°, from the
advice
form of the five adapted budgets (`df2EvBudgetsAdV`). -/
theorem wevProp_holds : WEvProp := by
  intro d n δ K ν B hreg hKc hKconv hν hpos hC hB a ha
  obtain ⟨hG, hY, hLQ, hSDF, hDQ⟩ := df2EvBudgetsAdV
  exact ⟨(measure_mono fun ω hω => hω.2).trans (Run.epoch_bound hG hreg hKc hKconv hν hpos hC hB ha),
    (measure_mono fun ω hω => hω.2).trans (Run.epoch_bound hY hreg hKc hKconv hν hpos hC hB ha),
    (measure_mono fun ω hω => hω.2).trans (Run.epoch_bound hLQ hreg hKc hKconv hν hpos hC hB ha),
    (measure_mono fun ω hω => hω.2).trans (Run.epoch_bound hSDF hreg hKc hKconv hν hpos hC hB ha),
    (measure_mono fun ω hω => hω.2).trans (Run.epoch_bound hDQ hreg hKc hKconv hν hpos hC hB ha)⟩

/-- The proposition of the coupling of a run, with (O1) proved. -/
theorem shadowProp_holds : ShadowProp :=
  shadowProp_of_wev wevProp_holds

end AdversarialBco.Bit.Cpl
