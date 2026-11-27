/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Generic lemmas of the extension of an environment

Measure theory on products, used to extend an environment of `TheoremUnified` by a Gaussian stream:

* `indep_prod`: independence on each factor gives the independence of the joined σ-algebras under the product
  measure;
* `exists_fill` (FILL): a measurable map `b` to a finite type whose fibres all have positive mass has a measurable
  section `f` from a uniform seed, `b (f c u) = c` everywhere, which carries the law of `b` times the uniform law back
  to the measure (the conditional laws represented by `Kernel.exists_measurable_map_eq_unitInterval`);
* `infinitePi_zip`, `infinitePi_sumElim`: two product measures zipped coordinatewise, or glued along a sum type, are
  product measures;
* `coordσ_indep`: under a product measure, the coordinates in disjoint sets are independent;
* `condExp_fst`, `condExp_fst_eq_zero`, `condExp_fst_le`: Lemma NZ of Poly/Df2Layer2.lean with the factors swapped:
  conditioning a function of the first factor on a sub-σ-algebra of the first factor joined with the whole second
  factor is conditioning on the sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdversarialBco.Unified.World

/-! ## Independence on a product -/

theorem indep_prod {X Y : Type} {A B : MeasurableSpace X} {C D : MeasurableSpace Y} [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : A ≤ mX) (hB : B ≤ mX) (hC : C ≤ mY) (hD : D ≤ mY) (h1 : Indep A B μ) (h2 : Indep C D ν) :
    Indep (MeasurableSpace.comap Prod.fst A ⊔ MeasurableSpace.comap Prod.snd C)
      (MeasurableSpace.comap Prod.fst B ⊔ MeasurableSpace.comap Prod.snd D) (μ.prod ν) := by
  have hgen : ∀ (M : MeasurableSpace X) (N : MeasurableSpace Y),
      MeasurableSpace.comap Prod.fst M ⊔ MeasurableSpace.comap Prod.snd N =
        MeasurableSpace.generateFrom
          (Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet[M] s} {t : Set Y | MeasurableSet[N] t}) :=
    fun M N => (@generateFrom_prod X Y M N).symm
  have hpi : ∀ (M : MeasurableSpace X) (N : MeasurableSpace Y),
      IsPiSystem (Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet[M] s} {t : Set Y | MeasurableSet[N] t}) :=
    fun M N => @isPiSystem_prod X Y M N
  have hle : ∀ (M : MeasurableSpace X) (N : MeasurableSpace Y), M ≤ mX → N ≤ mY →
      MeasurableSpace.comap Prod.fst M ⊔ MeasurableSpace.comap Prod.snd N ≤
        @Prod.instMeasurableSpace X Y mX mY := fun M N hM hN =>
    sup_le ((MeasurableSpace.comap_mono hM).trans (@measurable_fst X Y mX mY).comap_le)
      ((MeasurableSpace.comap_mono hN).trans (@measurable_snd X Y mX mY).comap_le)
  refine IndepSets.indep (hle A C hA hC) (hle B D hB hD) (hpi A C) (hpi B D) (hgen A C) (hgen B D) ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨b, hb, e, he, rfl⟩
  rw [Indep_iff] at h1 h2
  rw [Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, h1 a b ha hb, h2 c e hc he]
  ring

/-- The σ-algebra of the coordinates in `S` of a product space. -/
abbrev coordσ {ι : Type} {Z : Type} [MeasurableSpace Z] (S : Set ι) : MeasurableSpace (ι → Z) :=
  ⨆ i ∈ S, MeasurableSpace.comap (fun x : ι → Z => x i) inferInstance

theorem coordσ_le {ι : Type} {Z : Type} [MeasurableSpace Z] (S : Set ι) :
    coordσ (Z := Z) S ≤ (inferInstance : MeasurableSpace (ι → Z)) :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

theorem le_coordσ {ι : Type} {Z : Type} [MeasurableSpace Z] {S : Set ι} {i : ι} (hi : i ∈ S) :
    MeasurableSpace.comap (fun x : ι → Z => x i) inferInstance ≤ coordσ S :=
  le_iSup₂_of_le i hi le_rfl

theorem coordσ_mono {ι : Type} {Z : Type} [MeasurableSpace Z] {S T : Set ι} (h : S ⊆ T) :
    coordσ (Z := Z) S ≤ coordσ T :=
  iSup₂_le fun _i hi => le_coordσ (h hi)

theorem measurable_coordσ {ι : Type} {Z : Type} [MeasurableSpace Z] {S : Set ι} {i : ι} (hi : i ∈ S) :
    Measurable[coordσ S] fun x : ι → Z => x i :=
  Measurable.of_comap_le (le_coordσ hi)

/-- Under a product of probability measures, the coordinates in disjoint sets are independent. -/
theorem coordσ_indep {ι : Type} {Z : Type} [MeasurableSpace Z] (ρ : Measure Z) [IsProbabilityMeasure ρ]
    {S T : Set ι} (hST : Disjoint S T) :
    Indep (coordσ (Z := Z) S) (coordσ T) (Measure.infinitePi fun _ : ι => ρ) := by
  have h : iIndep (fun i : ι => MeasurableSpace.comap (fun x : ι → Z => x i) inferInstance)
      (Measure.infinitePi fun _ : ι => ρ) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ (z : Z) => z) (fun _ => measurable_id))
  exact indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) h hST

/-! ## FILL -/

theorem exists_fill {C X : Type} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (γ : Measure X) [IsProbabilityMeasure γ] (b : X → C) (hb : Measurable b)
    (hpos : ∀ c, γ (b ⁻¹' {c}) ≠ 0) :
    ∃ f : C → I → X, Measurable (Function.uncurry f) ∧ (∀ c u, b (f c u) = c) ∧
      ((γ.map b).prod (volume : Measure I)).map (Function.uncurry f) = γ := by
  classical
  have hfib : ∀ c, MeasurableSet (b ⁻¹' {c}) := fun c => hb (measurableSet_singleton c)
  have hprob : ∀ c, IsProbabilityMeasure (γ[|b ⁻¹' {c}]) := fun c => cond_isProbabilityMeasure (hpos c)
  let κ : Kernel C X := Kernel.ofFunOfCountable fun c => γ[|b ⁻¹' {c}]
  have hκ : IsMarkovKernel κ := ⟨fun c => hprob c⟩
  obtain ⟨f0, hf0m, hf0⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  have hne : ∀ c, (b ⁻¹' {c}).Nonempty := fun c => by
    by_contra h
    exact hpos c (by rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty])
  choose x hx using hne
  let f : C → I → X := fun c u => if b (f0 c u) = c then f0 c u else x c
  have hgood : MeasurableSet {p : C × I | b (f0 p.1 p.2) = p.1} := by
    have : {p : C × I | b (f0 p.1 p.2) = p.1} =
        ⋃ c, {p : C × I | p.1 = c} ∩ (Function.uncurry f0 ⁻¹' (b ⁻¹' {c})) := by
      ext p; simp [Function.uncurry]
    rw [this]
    exact MeasurableSet.iUnion fun c =>
      (measurable_fst (measurableSet_singleton c)).inter (hf0m (hfib c))
  have hfm : Measurable (Function.uncurry f) := by
    have : Function.uncurry f =
        fun p : C × I => if b (f0 p.1 p.2) = p.1 then Function.uncurry f0 p else x p.1 := by
      funext p; rfl
    rw [this]
    exact Measurable.ite hgood hf0m (measurable_of_countable _ |>.comp measurable_fst)
  refine ⟨f, hfm, fun c u => ?_, ?_⟩
  · simp only [f]
    split_ifs with h
    · exact h
    · exact hx c
  have hsec : ∀ c, (volume : Measure I).map (f c) = γ[|b ⁻¹' {c}] := by
    intro c
    have hmc : Measurable (f0 c) := hf0m.comp (measurable_const.prodMk measurable_id)
    have hae : f c =ᵐ[volume] f0 c := by
      have h0 : (volume : Measure I) {u | b (f0 c u) ≠ c} = 0 := by
        have := hf0 c
        have hs : {u | b (f0 c u) ≠ c} = f0 c ⁻¹' (b ⁻¹' {c})ᶜ := by ext u; simp
        rw [hs, ← Measure.map_apply hmc (hfib c).compl, this]
        show (γ[|b ⁻¹' {c}]) (b ⁻¹' {c})ᶜ = 0
        rw [cond_apply (hfib c), Set.inter_compl_self, measure_empty, mul_zero]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with u hu
      simp only [not_not] at hu
      simp [f, hu]
    rw [Measure.map_congr hae, hf0 c]
    rfl
  ext S hS
  have hfS : MeasurableSet (Function.uncurry f ⁻¹' S) := hfm hS
  rw [Measure.map_apply hfm hS, Measure.prod_apply hfS]
  have hsl : ∀ c, (volume : Measure I) (Prod.mk c ⁻¹' (Function.uncurry f ⁻¹' S)) = γ[|b ⁻¹' {c}] S := by
    intro c
    have hmc : Measurable (f c) := hfm.comp (measurable_const.prodMk measurable_id)
    rw [← hsec c, Measure.map_apply hmc hS]
    rfl
  simp_rw [hsl]
  rw [lintegral_fintype]
  have hterm : ∀ c, γ[S | b ⁻¹' {c}] * (γ.map b) {c} = (γ.restrict S) (b ⁻¹' {c}) := by
    intro c
    rw [Measure.map_apply hb (measurableSet_singleton c), cond_apply (hfib c), Measure.restrict_apply (hfib c),
      Set.inter_comm, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (hpos c) (measure_ne_top _ _), one_mul]
  simp_rw [hterm]
  rw [sum_measure_preimage_singleton Finset.univ (fun c _ => hfib c), Finset.coe_univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

/-! ## Product measures over infinite index sets -/

theorem infinitePi_zip {ι : Type*} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A)
    (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi fun _ : ι => μ).prod (Measure.infinitePi fun _ : ι => ν)).map
      (fun p : (ι → A) × (ι → B) => fun i => (p.1 i, p.2 i)) = Measure.infinitePi fun _ : ι => μ.prod ν := by
  have hm : Measurable fun p : (ι → A) × (ι → B) => fun i => (p.1 i, p.2 i) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  refine (Measure.isProjectiveLimit_infinitePi (fun _ : ι => μ.prod ν)).unique ?_ |>.symm
  intro J
  rw [Measure.map_map (Finset.measurable_restrict J) hm]
  have hfac : J.restrict ∘ (fun p : (ι → A) × (ι → B) => fun i => (p.1 i, p.2 i)) =
      (MeasurableEquiv.arrowProdEquivProdArrow A B J).symm ∘ Prod.map J.restrict J.restrict := by
    funext p i; rfl
  rw [hfac, ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B J).symm.measurable
    ((Finset.measurable_restrict J).prodMap (Finset.measurable_restrict J)),
    ← Measure.map_prod_map _ _ (Finset.measurable_restrict J) (Finset.measurable_restrict J),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact ((measurePreserving_arrowProdEquivProdArrow A B J (fun _ => μ) (fun _ => ν)).symm _).map_eq

theorem infinitePi_sumElim {α β : Type*} {γ : Type*} [MeasurableSpace γ] (ρ : Measure γ) [IsProbabilityMeasure ρ] :
    ((Measure.infinitePi fun _ : α => ρ).prod (Measure.infinitePi fun _ : β => ρ)).map
      (fun p : (α → γ) × (β → γ) => Sum.elim p.1 p.2) = Measure.infinitePi fun _ : α ⊕ β => ρ := by
  have hm : Measurable fun p : (α → γ) × (β → γ) => Sum.elim p.1 p.2 := by
    refine measurable_pi_iff.mpr fun k => ?_
    cases k with
    | inl a => exact (measurable_pi_apply a).comp measurable_fst
    | inr b => exact (measurable_pi_apply b).comp measurable_snd
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  classical
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : (α → γ) × (β → γ) => Sum.elim p.1 p.2) ⁻¹' Set.pi (↑s) t =
      Set.pi (↑s.toLeft) (fun a => t (.inl a)) ×ˢ Set.pi (↑s.toRight) (fun b => t (.inr b)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun a ha => h _ ha, fun b hb => h _ hb⟩
    · rintro ⟨h1, h2⟩ k hk
      cases k with
      | inl a => exact h1 a hk
      | inr b => exact h2 b hk
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ fun a _ => ht _, Measure.infinitePi_pi _ fun b _ => ht _]
  conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum]

/-- A product over `α ⊕ β`, split, is the product of the two products. -/
theorem infinitePi_split {α β : Type*} {γ : Type*} [MeasurableSpace γ] (ρ : Measure γ) [IsProbabilityMeasure ρ] :
    (Measure.infinitePi fun _ : α ⊕ β => ρ).map (fun x : α ⊕ β → γ => (fun a => x (.inl a), fun b => x (.inr b))) =
      (Measure.infinitePi fun _ : α => ρ).prod (Measure.infinitePi fun _ : β => ρ) := by
  have hm : Measurable fun p : (α → γ) × (β → γ) => Sum.elim p.1 p.2 := by
    refine measurable_pi_iff.mpr fun k => ?_
    cases k with
    | inl a => exact (measurable_pi_apply a).comp measurable_fst
    | inr b => exact (measurable_pi_apply b).comp measurable_snd
  have hs : Measurable fun x : α ⊕ β → γ => (fun a => x (.inl a), fun b => x (.inr b)) :=
    (measurable_pi_iff.mpr fun a => measurable_pi_apply _).prodMk (measurable_pi_iff.mpr fun b => measurable_pi_apply _)
  rw [← infinitePi_sumElim ρ, Measure.map_map hs hm]
  have : ((fun x : α ⊕ β → γ => (fun a => x (.inl a), fun b => x (.inr b))) ∘
      fun p : (α → γ) × (β → γ) => Sum.elim p.1 p.2) = id := by
    funext p; rfl
  rw [this, Measure.map_id]

/-! ## Lemma NZ on the first factor -/

theorem ae_prod_fst {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ω ∂(μ.prod ν), p ω.1 :=
  (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hp

/-- Conditioning `h(ω.1)` on `m ⊗ (whole second factor)` gives the conditional expectation of `h` given `m`. -/
theorem condExp_fst {X Y : Type} (m : MeasurableSpace X) [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    (μ : Measure[mX] X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : X → ℝ) (hm : m ≤ mX)
    (hint : Integrable h μ) :
    (μ.prod ν)[fun ω => h ω.1 | MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY] =ᵐ[μ.prod ν]
      fun ω => (μ[h | m]) ω.1 := by
  have hle : MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY ≤
      @Prod.instMeasurableSpace X Y mX mY :=
    sup_le ((MeasurableSpace.comap_mono hm).trans le_sup_left) le_sup_right
  have hfst : @Measurable (X × Y) X (MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY) m
      Prod.fst := @measurable_fst X Y m mY
  have hgm : StronglyMeasurable[MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY]
      (fun ω : X × Y => (μ[h | m]) ω.1) :=
    (stronglyMeasurable_condExp (m := m) (μ := μ)).comp_measurable hfst
  have hcint : Integrable (μ[h | m]) μ := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ.prod ν) hle (hint.comp_fst ν)
    (fun s _ _ => (hcint.comp_fst ν).integrableOn) (fun S hS _ => ?_) hgm.aestronglyMeasurable).symm
  have hS' : @MeasurableSet (X × Y) (@Prod.instMeasurableSpace X Y mX mY) S := hle S hS
  rw [← integral_indicator hS', ← integral_indicator hS', integral_prod_symm _ ((hcint.comp_fst ν).indicator hS'),
    integral_prod_symm _ ((hint.comp_fst ν).indicator hS')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hsl : MeasurableSet[m] ((fun x => (x, y)) ⁻¹' S) := @measurable_prodMk_right X Y m mY y S hS
  have e1 : (fun x => S.indicator (fun ω : X × Y => (μ[h | m]) ω.1) (x, y)) =
      ((fun x => (x, y)) ⁻¹' S).indicator (μ[h | m]) := by
    funext x; by_cases hx : (x, y) ∈ S <;> simp [Set.indicator, hx]
  have e2 : (fun x => S.indicator (fun ω : X × Y => h ω.1) (x, y)) = ((fun x => (x, y)) ⁻¹' S).indicator h := by
    funext x; by_cases hx : (x, y) ∈ S <;> simp [Set.indicator, hx]
  beta_reduce
  rw [e1, e2, integral_indicator (hm _ hsl), integral_indicator (hm _ hsl), setIntegral_condExp hm hint hsl]

theorem condExp_fst_eq_zero {X Y : Type} (m : MeasurableSpace X) [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    (μ : Measure[mX] X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hm : m ≤ mX)
    (H : MeasurableSpace (X × Y)) (hH : H ≤ MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY)
    (h : X → ℝ) (hi : Integrable h μ) (hc : μ[h | m] =ᵐ[μ] 0) :
    (μ.prod ν)[fun ω => h ω.1 | H] =ᵐ[μ.prod ν] 0 := by
  have hB : MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY ≤
      (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) :=
    sup_le ((MeasurableSpace.comap_mono hm).trans (@measurable_fst X Y mX mY).comap_le)
      (@measurable_snd X Y mX mY).comap_le
  have h1 := condExp_condExp_of_le (μ := μ.prod ν) (f := fun ω : X × Y => h ω.1) hH hB
  have h3 := condExp_congr_ae (m := H) (condExp_fst m μ ν h hm hi)
  have hG0 : (fun ω : X × Y => (μ[h | m]) ω.1) =ᵐ[μ.prod ν] 0 := ae_prod_fst μ ν hc
  have h4 := condExp_congr_ae (m := H) hG0
  rw [condExp_zero] at h4
  filter_upwards [h1, h3, h4] with ω e1 e3 e4
  rw [← e1, e3]; exact e4

theorem condExp_fst_le {X Y : Type} (m : MeasurableSpace X) [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    (μ : Measure[mX] X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hm : m ≤ mX)
    (H : MeasurableSpace (X × Y)) (hH : H ≤ MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY)
    (h : X → ℝ) (hi : Integrable h μ) (c : ℝ) (hc : μ[h | m] ≤ᵐ[μ] fun _ => c) :
    (μ.prod ν)[fun ω => h ω.1 | H] ≤ᵐ[μ.prod ν] fun _ => c := by
  have hB : MeasurableSpace.comap Prod.fst m ⊔ MeasurableSpace.comap Prod.snd mY ≤
      (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) :=
    sup_le ((MeasurableSpace.comap_mono hm).trans (@measurable_fst X Y mX mY).comap_le)
      (@measurable_snd X Y mX mY).comap_le
  have hHB : H ≤ (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) := hH.trans hB
  have hG := (integrable_condExp (m := m) (μ := μ) (f := h)).comp_fst ν
  have h1 := condExp_condExp_of_le (μ := μ.prod ν) (f := fun ω : X × Y => h ω.1) hH hB
  have h3 := condExp_congr_ae (m := H) (condExp_fst m μ ν h hm hi)
  have hGc : (fun ω : X × Y => (μ[h | m]) ω.1) ≤ᵐ[μ.prod ν] fun _ => c := ae_prod_fst μ ν hc
  have h4 := condExp_mono (m := H) hG (integrable_const c) hGc
  rw [condExp_const hHB] at h4
  filter_upwards [h1, h3, h4] with ω e1 e3 e4
  rw [← e1, e3]; exact e4

end AdversarialBco.Unified.World
