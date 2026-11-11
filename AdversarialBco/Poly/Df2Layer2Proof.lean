/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2
public import AdversarialBco.Poly.Df2DetW
public import AdversarialBco.Poly.Df2RowsProof

@[expose] public section

/-!
# DF2-O, second layer: proofs

Proofs of the statements of `Df2Layer2.lean`, in the order of the chain of `Df2Layer2Comp`.

* `lemmaFR : LemmaFR`, the freezing lemma: the conditional law of `ζ` given `𝒢` is its law (independence,
  `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable` with the constant kernel), and the conditional expectation
  of `F(x, ζ)` is the integral against it (`condExp_prod_ae_eq_integral_condDistrib`, conditioning on the identity map
  from `(Ω, m0)` to `(Ω, 𝒢)`).
* `lemmaNZProd : LemmaNZProd`, the noise on a product (Fubini on the slices, `setIntegral_condExp`).
* `df2E1LocOf_holds : Df2E1LocOf`, a union bound of the five budgets off which DET applies.
* `df2DetOf_holds : Df2DetOf`, DET: the hypotheses bundled in `DetHyp` (Df2DetMain.lean), the proof in
  Df2DetState.lean to Df2DetW.lean, ending with `DetHyp.epoch_ok`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

/-! ## Lemma FR -/

theorem lemmaFR : LemmaFR := by
  intro Ω X Z 𝒢 m0 mX mZ _ _ μ _ x ζ F h𝒢 hx hζ hind hF hint
  -- the identity of `Ω`, from `m0` to `𝒢`
  have hid : @Measurable Ω Ω m0 𝒢 id := measurable_id'' h𝒢
  have hidae : @AEMeasurable Ω Ω 𝒢 m0 id μ := ⟨id, hid, Filter.EventuallyEq.rfl⟩
  -- the integrand as a function on `(Ω, 𝒢) × Z`
  have hmeas : @Measurable (Ω × Z) ℝ (@Prod.instMeasurableSpace Ω Z 𝒢 mZ) _ (fun p : Ω × Z => F (x p.1, p.2)) :=
    hF.comp (@Measurable.prodMap Ω X Z Z 𝒢 mX mZ mZ x id hx measurable_id)
  have hcond := condExp_prod_ae_eq_integral_condDistrib (mβ := 𝒢) (μ := μ) (X := id) (Y := ζ)
    (f := fun p : Ω × Z => F (x p.1, p.2)) hid hζ.aemeasurable hmeas.stronglyMeasurable hint
  rw [MeasurableSpace.comap_id] at hcond
  -- independence: the joint law is the product of the laws
  have hindF : @IndepFun Ω Ω Z m0 𝒢 mZ id ζ μ := by
    rw [IndepFun_iff_Indep (mβ := 𝒢) (mγ := mZ), MeasurableSpace.comap_id]
    exact hind.symm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map (mβ := 𝒢) (mβ' := mZ) hidae hζ.aemeasurable).1 hindF
  have hκ : @Measure.map Ω (Ω × Z) m0 (@Prod.instMeasurableSpace Ω Z 𝒢 mZ) (fun ω => (id ω, ζ ω)) μ =
      (@Measure.map Ω Ω m0 𝒢 id μ) ⊗ₘ (@Kernel.const Ω Z 𝒢 mZ (μ.map ζ)) := by
    rw [Measure.compProd_const]
    exact hprod
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hid hζ hκ
  have hcd' := ae_of_ae_map hidae hcd
  filter_upwards [hcond, hcd'] with ω h1 h2
  simp only [id_eq] at h1 h2
  rw [h1, h2, Kernel.const_apply]

/-! ## Lemma NZ on a product -/

/-- The noise on a product: conditioning `h(ω.2)` on `mX ⊗ m` gives the conditional expectation of `h` given `m`.
The candidate is measurable in the product sigma-field of `mX` and `m`; on a set `S` of it, Fubini reduces the two
set integrals to the slices of `S`, which are `m`-measurable. -/
theorem lemmaNZProd : LemmaNZProd := by
  intro X Y mX m mY γ ν _ _ h hm hint
  have hle : MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m ≤
      @Prod.instMeasurableSpace X Y mX mY :=
    sup_le le_sup_left ((MeasurableSpace.comap_mono hm).trans le_sup_right)
  have hsnd : @Measurable (X × Y) Y (MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m) m
      Prod.snd := @measurable_snd X Y mX m
  have hgm : StronglyMeasurable[MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m]
      (fun ω : X × Y => (ν[h | m]) ω.2) :=
    (stronglyMeasurable_condExp (m := m) (μ := ν)).comp_measurable hsnd
  have hcint : Integrable (ν[h | m]) ν := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := γ.prod ν) hle (hint.comp_snd γ)
    (fun s _ _ => (hcint.comp_snd γ).integrableOn) (fun S hS _ => ?_) hgm.aestronglyMeasurable).symm
  have hS' : @MeasurableSet (X × Y) (@Prod.instMeasurableSpace X Y mX mY) S := hle S hS
  rw [← integral_indicator hS', ← integral_indicator hS', integral_prod _ ((hcint.comp_snd γ).indicator hS'),
    integral_prod _ ((hint.comp_snd γ).indicator hS')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hsl : MeasurableSet[m] (Prod.mk x ⁻¹' S) := @measurable_prodMk_left X Y mX m x S hS
  have e1 : (fun y => S.indicator (fun ω : X × Y => (ν[h | m]) ω.2) (x, y)) =
      (Prod.mk x ⁻¹' S).indicator (ν[h | m]) := by
    funext y; by_cases hy : (x, y) ∈ S <;> simp [Set.indicator, hy]
  have e2 : (fun y => S.indicator (fun ω : X × Y => h ω.2) (x, y)) = (Prod.mk x ⁻¹' S).indicator h := by
    funext y; by_cases hy : (x, y) ∈ S <;> simp [Set.indicator, hy]
  beta_reduce
  rw [e1, e2, integral_indicator (hm _ hsl), integral_indicator (hm _ hsl), setIntegral_condExp hm hint hsl]

/-! ## DET -/

/-- DET from its inputs: one epoch on every path, (F) or (N). -/
theorem df2DetOf_holds : Df2DetOf := by
  intro L1 W SI RH d n δ Kt ap π m hd hn hδ0 hδ1 heps hm1 hmn hbody hap hadm evG evY evLQ evSDF evDQ
  exact (DetHyp.mk (DetBase.mk (c := df2CtxAt d n δ Kt ap) L1 W SI hd hn hδ0 hδ1 rfl heps
    (RH d n δ hd hn hδ0 hδ1 heps) hm1 hmn hbody hap hadm) evG evY evLQ evSDF evDQ).epoch_ok

/-! ## E1-loc -/

/-- E1-loc from DET and the five budgets: off the union of the five bad events the epoch is good (DET), and the
budgets add up to `(3/7 + 1/7 + 1/21 + 1/7 + 1/8) δ_e = (149/168) δ_e`. -/
theorem df2E1LocOf_holds : Df2E1LocOf := by
  intro hDet hG hY hLQ hSDF hDQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω _ μ hμ
    𝒢 θ ξ e hθ hE
  have hde : 0 ≤ (df2oPar d n δ).δe := (Layer2.rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  let c : Ω → Df2Ctx d := fun ω => df2CtxAt d n δ (Kθ (θ ω)) ap
  let π : Ω → Df2Path d := fun ω => ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩
  have key : {ω | ¬ (c ω).EpochOK (π ω) m} ⊆
      {ω | ¬ (c ω).EvG (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} ∪
        {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m} := by
    intro ω hω
    by_contra hn'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hn'
    obtain ⟨⟨⟨⟨hg, hy⟩, hlq⟩, hsdf⟩, hdq⟩ := hn'
    exact hω (hDet d n δ (Kθ (θ ω)) ap (π ω) m hd hn hδ0 hδ1 heps hm1 hmn (hbody _) hap (hadm _) hg (hy hg)
      (hlq hg) (hsdf hg) (hdq hg))
  have h1 := hG d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hE
  have h2 := hY d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hE
  have h3 := hLQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hE
  have h4 := hSDF d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hE
  have h5 := hDQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hE
  calc μ {ω | ¬ (c ω).EpochOK (π ω) m}
      ≤ μ ({ω | ¬ (c ω).EvG (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m}) := measure_mono key
    _ ≤ μ {ω | ¬ (c ω).EvG (π ω) m} + μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m} := by
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (3 / 7 * (df2oPar d n δ).δe) + ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) +
          ENNReal.ofReal (1 / 21 * (df2oPar d n δ).δe) + ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) +
          ENNReal.ofReal (1 / 8 * (df2oPar d n δ).δe) := by gcongr
    _ = ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

end AdversarialBco.Poly
