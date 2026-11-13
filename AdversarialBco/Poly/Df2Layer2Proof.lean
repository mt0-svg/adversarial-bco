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

Proofs of two standard facts stated in `Df2Layer2.lean`.

* `lemmaFR : LemmaFR`, the freezing lemma: the conditional law of `ζ` given `𝒢` is its law (independence,
  `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable` with the constant kernel), and the conditional expectation
  of `F(x, ζ)` is the integral against it (`condExp_prod_ae_eq_integral_condDistrib`, conditioning on the identity map
  from `(Ω, m0)` to `(Ω, 𝒢)`).
* `lemmaNZProd : LemmaNZProd`, the noise on a product (Fubini on the slices, `setIntegral_condExp`).
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

end AdversarialBco.Poly
