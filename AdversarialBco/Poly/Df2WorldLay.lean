/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# The world as a probability space

The world `ω = (gs, noise)` under `gaussStream.prod ν` (`WΩ`), with the sigma-field `gσ i` of term `i` of the Gaussian
stream.

* Generic lemmas: the gauge of a family of convex bodies containing `B̄(0, 1)` is measurable once membership is
  (`gauge_family_measurable`); independence on a product (`iIndep_prod_snd`); the exponential moments behind
  `E exp(e²) ≤ 2` for the noise of an instance (`gauss_exp_quarter`, `exp_sq_mid_le`); conditional expectations of a
  function of the second factor (`condExp_snd_le`, `condExp_snd_eq_zero`, from Lemma NZ on the product); the mean width
  of a ball (`pgMw_closedBall_le`, `inv_R_le_df2Mw`); an affine image of an interior point (`affine_interior_mem`).
* `indep_world`: the terms of the Gaussian stream at disjoint index sets, with the whole noise on one side, are
  independent (`iIndep_world`, from `iIndep_coords`).
* The marginals of the world and the integrability of the noise (`map_fst_world`, `map_snd_world`,
  `integrable_noise_world`, `integrable_noise_exp`, `integrable_noise_lin`).
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

/-! ## Generic lemmas -/

open Pointwise in
theorem gauge_family_measurable {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (C : Θ → Set (EuclideanSpace ℝ (Fin d)))
    (hC : MeasurableSet {p : Θ × EuclideanSpace ℝ (Fin d) | p.2 ∈ C p.1})
    (hconv : ∀ q, Convex ℝ (C q)) (hball : ∀ q, Metric.closedBall 0 1 ⊆ C q) :
    Measurable fun p : Θ × EuclideanSpace ℝ (Fin d) => gauge (C p.1) p.2 := by
  have habs : ∀ q, Absorbent ℝ (C q) := fun q =>
    absorbent_nhds_zero (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) (hball q))
  have h0 : ∀ q, (0 : EuclideanSpace ℝ (Fin d)) ∈ C q := fun q =>
    hball q (Metric.mem_closedBall_self zero_le_one)
  have key : ∀ t : ℝ, (fun p : Θ × EuclideanSpace ℝ (Fin d) => gauge (C p.1) p.2) ⁻¹' Set.Iio t =
      ⋃ r ∈ {r : ℚ | 0 < r ∧ (r : ℝ) < t},
        (fun p : Θ × EuclideanSpace ℝ (Fin d) => (p.1, (r : ℝ)⁻¹ • p.2)) ⁻¹' {p | p.2 ∈ C p.1} := by
    intro t
    ext ⟨q, x⟩
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      obtain ⟨b, hb0, hbt, hxb⟩ := exists_lt_of_gauge_lt (habs q) h
      obtain ⟨r, hbr, hrt⟩ := exists_rat_btwn hbt
      have hr0 : (0 : ℝ) < r := hb0.trans hbr
      refine ⟨r, ⟨by exact_mod_cast hr0, hrt⟩, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hb0.ne'] at hxb
      have e : (r : ℝ)⁻¹ • x = (b / r) • (b⁻¹ • x) := by
        rw [smul_smul]; congr 1; field_simp
      rw [e]
      exact (hconv q).smul_mem_of_zero_mem (h0 q) hxb ⟨by positivity, (div_le_one hr0).mpr hbr.le⟩
    · rintro ⟨r, ⟨hr0, hrt⟩, hx⟩
      have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
      have hx' : x ∈ (r : ℝ) • C q := (Set.mem_smul_set_iff_inv_smul_mem₀ hr0'.ne' _ _).mpr hx
      exact (gauge_le_of_mem hr0'.le hx').trans_lt hrt
  refine measurable_of_Iio fun t => ?_
  rw [key t]
  refine MeasurableSet.biUnion (Set.to_countable _) fun r _ => ?_
  exact hC.preimage (measurable_fst.prodMk (by fun_prop))

theorem iIndep_prod_snd {ι X Y : Type*} [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y] (m : ι → MeasurableSpace X) (hm : ∀ i, m i ≤ mX) (γ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν] (h : iIndep m γ) :
    iIndep (fun k : Option ι => k.elim (MeasurableSpace.comap Prod.snd mY) fun i => MeasurableSpace.comap Prod.fst (m i))
      (γ.prod ν) := by
  classical
  rw [iIndep_iff] at h ⊢
  intro s f hf
  have hrep : ∀ k ∈ s, ∃ A : Set X, ∃ B : Set Y, f k = A ×ˢ B ∧
      (∀ i, k = some i → MeasurableSet[m i] A ∧ B = Set.univ) ∧ (k = none → A = Set.univ) := by
    intro k hk
    have hfk := hf k hk
    cases k with
    | none =>
      obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.mp hfk
      refine ⟨Set.univ, B, ?_, fun i hi => by simp at hi, fun _ => rfl⟩
      rw [← hB]; ext ⟨x, y⟩; simp
    | some i =>
      obtain ⟨A, hA, hA'⟩ := MeasurableSpace.measurableSet_comap.mp hfk
      refine ⟨A, Set.univ, ?_, fun j hj => ?_, fun h => by simp at h⟩
      · rw [← hA']; ext ⟨x, y⟩; simp
      · cases hj; exact ⟨hA, rfl⟩
  choose! A B hAB hsome hnone using hrep
  have hinter : (⋂ k ∈ s, f k) = (⋂ k ∈ s, A k) ×ˢ (⋂ k ∈ s, B k) := by
    ext ⟨x, y⟩
    simp only [Set.mem_iInter, Set.mem_prod]
    constructor
    · intro hxy
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · have := hxy k hk; rw [hAB k hk] at this; exact this.1
      · have := hxy k hk; rw [hAB k hk] at this; exact this.2
    · rintro ⟨hx, hy⟩ k hk
      rw [hAB k hk]; exact ⟨hx k hk, hy k hk⟩
  have hprod : ∀ k ∈ s, (γ.prod ν) (f k) = γ (A k) * ν (B k) := fun k hk => by
    rw [hAB k hk, Measure.prod_prod]
  rw [hinter, Measure.prod_prod, Finset.prod_congr rfl hprod, Finset.prod_mul_distrib]
  congr 1
  · -- the first factor: the stages `some i`
    have hs : ∀ x ∈ s, x ∉ Set.range (some : ι → Option ι) → γ (A x) = 1 := by
      intro x hx hxr
      cases x with
      | none => rw [hnone none hx rfl]; simp
      | some i => exact absurd ⟨i, rfl⟩ hxr
    rw [← Finset.prod_preimage some s (Option.some_injective ι).injOn _ hs]
    have hI : (⋂ k ∈ s, A k) = ⋂ i ∈ s.preimage some (Option.some_injective ι).injOn, A (some i) := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_preimage]
      constructor
      · intro hx i hi; exact hx _ hi
      · intro hx k hk
        cases k with
        | none => rw [hnone none hk rfl]; trivial
        | some i => exact hx i hk
    rw [hI]
    exact h _ fun i hi => (hsome (some i) (Finset.mem_preimage.mp hi) i rfl).1
  · -- the second factor: the noise
    by_cases hn : none ∈ s
    · have hI : (⋂ k ∈ s, B k) = B none := by
        ext y
        simp only [Set.mem_iInter]
        constructor
        · intro hy; exact hy none hn
        · intro hy k hk
          cases k with
          | none => exact hy
          | some i => rw [(hsome (some i) hk i rfl).2]; trivial
      rw [hI, Finset.prod_eq_single_of_mem none hn]
      intro k hk hne
      cases k with
      | none => exact absurd rfl hne
      | some i => rw [(hsome (some i) hk i rfl).2]; simp
    · have hI : (⋂ k ∈ s, B k) = Set.univ := by
        ext y
        simp only [Set.mem_iInter, Set.mem_univ, iff_true]
        intro k hk
        cases k with
        | none => exact absurd hk hn
        | some i => rw [(hsome (some i) hk i rfl).2]; trivial
      rw [hI, Finset.prod_eq_one]
      · simp
      · intro k hk
        cases k with
        | none => exact absurd hk hn
        | some i => rw [(hsome (some i) hk i rfl).2]; simp

theorem gauss_exp_quarter :
    Integrable (fun x : ℝ => Real.exp ((x / 2) ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp ((x / 2) ^ 2) ∂(gaussianReal 0 1) ≤ 2 := by
  have hv : (1 : NNReal) ≠ 0 := by norm_num
  have hb : (0 : ℝ) < 1/4 := by norm_num
  have h2pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
  have hπpos : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr (by positivity : 0 < Real.pi)
  have hpdf_eq : gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    ext x
    simp [gaussianPDFReal_def]
  have h_exp_prod (x : ℝ) : Real.exp (-x ^ 2 / 2) * Real.exp ((x / 2) ^ 2) = Real.exp (-(1/4 : ℝ) * x ^ 2) := by
    calc
      Real.exp (-x ^ 2 / 2) * Real.exp ((x / 2) ^ 2) = Real.exp ((-x ^ 2 / 2) + ((x / 2) ^ 2)) := by
        rw [Real.exp_add]
      _ = Real.exp (-(1/4 : ℝ) * x ^ 2) := by ring_nf
  constructor
  · -- integrability
    rw [gaussianReal_of_var_ne_zero 0 hv]
    rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1) ?_]
    · -- integrability of the product with density
      have h_int : Integrable (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x ^ 2)) volume :=
        integrable_exp_neg_mul_sq hb
      have h_eq : (fun x : ℝ => Real.exp ((x / 2) ^ 2) * (gaussianPDF 0 1 x).toReal) =
                 (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/4 : ℝ) * x ^ 2)) := by
        ext x
        have hpos : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by positivity
        calc
          Real.exp ((x / 2) ^ 2) * (gaussianPDF 0 1 x).toReal
              = Real.exp ((x / 2) ^ 2) * (ENNReal.ofReal (gaussianPDFReal 0 1 x)).toReal := by rfl
          _ = Real.exp ((x / 2) ^ 2) * (ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2))).toReal := by rw [hpdf_eq]
          _ = Real.exp ((x / 2) ^ 2) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
            rw [ENNReal.toReal_ofReal hpos]
          _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * Real.exp ((x / 2) ^ 2)) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
          _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/4 : ℝ) * x ^ 2) := by rw [h_exp_prod x]
      rw [h_eq]
      exact h_int.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    · -- finite almost everywhere
      refine Filter.Eventually.of_forall fun x => ?_
      simp [gaussianPDF]
  · -- integral inequality
    calc
      ∫ x, Real.exp ((x / 2) ^ 2) ∂(gaussianReal 0 1)
          = ∫ x, gaussianPDFReal 0 1 x • Real.exp ((x / 2) ^ 2) := by
        rw [integral_gaussianReal_eq_integral_smul hv]
      _ = ∫ x, (gaussianPDFReal 0 1 x * Real.exp ((x / 2) ^ 2)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp [smul_eq_mul]
      _ = ∫ x, ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) * Real.exp ((x / 2) ^ 2) := by
        simp [hpdf_eq]
      _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * Real.exp ((x / 2) ^ 2)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        ring
      _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/4 : ℝ) * x ^ 2) := by
        simp [h_exp_prod]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, Real.exp (-(1/4 : ℝ) * x ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/4 : ℝ)) := by rw [integral_gaussian]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (4 * Real.pi) := by ring_nf
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt 4 * Real.sqrt Real.pi) := by
        rw [Real.sqrt_mul (show 0 ≤ (4 : ℝ) from by norm_num) Real.pi]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 * Real.sqrt Real.pi) := by norm_num
      _ = Real.sqrt 2 := by
        field_simp [ne_of_gt h2pos, ne_of_gt hπpos]
        calc
          2 * Real.sqrt Real.pi = Real.sqrt 4 * Real.sqrt Real.pi := by norm_num
          _ = Real.sqrt (4 * Real.pi) := by rw [← Real.sqrt_mul (show 0 ≤ (4 : ℝ) from by norm_num) Real.pi]
          _ = Real.sqrt (2 * (2 * Real.pi)) := by ring_nf
          _ = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
            rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) from by norm_num) (2 * Real.pi)]
          _ = Real.sqrt (2 * Real.pi) * Real.sqrt 2 := by ring
      _ ≤ 2 := by
        have h : Real.sqrt 2 ≤ 2 := by
          have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
          nlinarith
        exact h

theorem exp_sq_mid_le (a c : ℝ) :
    Real.exp (((a + c) / 2) ^ 2) ≤ (Real.exp (a ^ 2) + Real.exp (c ^ 2)) / 2 := by
  have h_sq_ineq : ((a + c) / 2) ^ 2 ≤ (a ^ 2 + c ^ 2) / 2 := by
    have h : (a - c) ^ 2 ≥ 0 := sq_nonneg (a - c)
    nlinarith
  have h_exp_ineq : Real.exp (((a + c) / 2) ^ 2) ≤ Real.exp ((a ^ 2 + c ^ 2) / 2) := by
    rwa [Real.exp_le_exp]
  have h_exp_add : Real.exp ((a ^ 2 + c ^ 2) / 2) = Real.exp (a ^ 2 / 2) * Real.exp (c ^ 2 / 2) := by
    calc
      Real.exp ((a ^ 2 + c ^ 2) / 2) = Real.exp (a ^ 2 / 2 + c ^ 2 / 2) := by ring
      _ = Real.exp (a ^ 2 / 2) * Real.exp (c ^ 2 / 2) := by rw [Real.exp_add]
  have h_mul_ineq : Real.exp (a ^ 2 / 2) * Real.exp (c ^ 2 / 2) ≤
      ((Real.exp (a ^ 2 / 2)) ^ 2 + (Real.exp (c ^ 2 / 2)) ^ 2) / 2 := by
    have h := two_mul_le_add_sq (Real.exp (a ^ 2 / 2)) (Real.exp (c ^ 2 / 2))
    linarith
  have h_sq_exp_a : (Real.exp (a ^ 2 / 2)) ^ 2 = Real.exp (a ^ 2) := by
    calc
      (Real.exp (a ^ 2 / 2)) ^ 2 = Real.exp (a ^ 2 / 2) * Real.exp (a ^ 2 / 2) := by ring
      _ = Real.exp (a ^ 2 / 2 + a ^ 2 / 2) := by rw [Real.exp_add]
      _ = Real.exp (a ^ 2) := by ring
  have h_sq_exp_c : (Real.exp (c ^ 2 / 2)) ^ 2 = Real.exp (c ^ 2) := by
    calc
      (Real.exp (c ^ 2 / 2)) ^ 2 = Real.exp (c ^ 2 / 2) * Real.exp (c ^ 2 / 2) := by ring
      _ = Real.exp (c ^ 2 / 2 + c ^ 2 / 2) := by rw [Real.exp_add]
      _ = Real.exp (c ^ 2) := by ring
  calc
    Real.exp (((a + c) / 2) ^ 2) ≤ Real.exp ((a ^ 2 + c ^ 2) / 2) := h_exp_ineq
    _ = Real.exp (a ^ 2 / 2) * Real.exp (c ^ 2 / 2) := h_exp_add
    _ ≤ ((Real.exp (a ^ 2 / 2)) ^ 2 + (Real.exp (c ^ 2 / 2)) ^ 2) / 2 := h_mul_ineq
    _ = (Real.exp (a ^ 2) + Real.exp (c ^ 2)) / 2 := by rw [h_sq_exp_a, h_sq_exp_c]

theorem ae_prod_snd {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (γ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν] {p : Y → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ ω ∂(γ.prod ν), p ω.2 :=
  (measurePreserving_snd (μ := γ) (ν := ν)).quasiMeasurePreserving.ae hp

theorem integrable_prod_snd {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (γ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure γ] [IsProbabilityMeasure ν] {g : Y → ℝ} (hg : Integrable g ν) :
    Integrable (fun ω : X × Y => g ω.2) (γ.prod ν) :=
  ((measurePreserving_snd (μ := γ) (ν := ν)).integrable_comp hg.aestronglyMeasurable).mpr hg

theorem condExp_snd_le (NZ : LemmaNZProd) {X Y : Type} [mX : MeasurableSpace X]
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y] (γ : Measure X) (ν : Measure[mY] Y) [IsProbabilityMeasure γ]
    [IsProbabilityMeasure ν] (hm : m ≤ mY) (H : MeasurableSpace (X × Y))
    (hH : H ≤ MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m) (h : Y → ℝ) (hi : Integrable h ν)
    (c : ℝ) (hc : ν[h | m] ≤ᵐ[ν] fun _ => c) :
    (γ.prod ν)[fun ω => h ω.2 | H] ≤ᵐ[γ.prod ν] fun _ => c := by
  have hB : MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m ≤
      (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) := by
    refine sup_le ?_ ?_
    · exact (@measurable_fst X Y mX mY).comap_le
    · exact (MeasurableSpace.comap_mono hm).trans (@measurable_snd X Y mX mY).comap_le
  have hHB : H ≤ (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) := hH.trans hB
  have hG := integrable_prod_snd γ ν (integrable_condExp (m := m) (μ := ν) (f := h))
  have h1 := condExp_condExp_of_le (μ := γ.prod ν) (f := fun ω : X × Y => h ω.2) hH hB
  have h2 := NZ X Y m γ ν h hm hi
  have h3 := condExp_congr_ae (m := H) h2
  have hGc : (fun ω : X × Y => (ν[h | m]) ω.2) ≤ᵐ[γ.prod ν] fun _ => c := ae_prod_snd γ ν hc
  have h4 := condExp_mono (m := H) hG (integrable_const c) hGc
  rw [condExp_const hHB] at h4
  filter_upwards [h1, h3, h4] with ω e1 e3 e4
  rw [← e1, e3]; exact e4

theorem condExp_snd_eq_zero (NZ : LemmaNZProd) {X Y : Type} [mX : MeasurableSpace X]
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y] (γ : Measure X) (ν : Measure[mY] Y) [IsProbabilityMeasure γ]
    [IsProbabilityMeasure ν] (hm : m ≤ mY) (H : MeasurableSpace (X × Y))
    (hH : H ≤ MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m) (h : Y → ℝ) (hi : Integrable h ν)
    (hc : ν[h | m] =ᵐ[ν] 0) :
    (γ.prod ν)[fun ω => h ω.2 | H] =ᵐ[γ.prod ν] 0 := by
  have hB : MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m ≤
      (Prod.instMeasurableSpace : MeasurableSpace (X × Y)) := by
    refine sup_le ?_ ?_
    · exact (@measurable_fst X Y mX mY).comap_le
    · exact (MeasurableSpace.comap_mono hm).trans (@measurable_snd X Y mX mY).comap_le
  have h1 := condExp_condExp_of_le (μ := γ.prod ν) (f := fun ω : X × Y => h ω.2) hH hB
  have h2 := NZ X Y m γ ν h hm hi
  have h3 := condExp_congr_ae (m := H) h2
  have hG0 : (fun ω : X × Y => (ν[h | m]) ω.2) =ᵐ[γ.prod ν] 0 := ae_prod_snd γ ν hc
  have h4 := condExp_congr_ae (m := H) hG0
  rw [condExp_zero] at h4
  filter_upwards [h1, h3, h4] with ω e1 e3 e4
  rw [← e1, e3]; exact e4

theorem pgMw_closedBall_le {d : ℕ} (R : ℝ) (hR : 0 < R) :
    pgMw (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) ≤ 1 / R := by
  unfold pgMw
  have hg : (fun g : EuclideanSpace ℝ (Fin d) =>
    gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) g) =
    (fun g => ‖g‖ / R) := by
    ext g
    exact gauge_closedBall (hR.le) g
  rw [hg]
  rw [MeasureTheory.integral_div]
  by_cases hI : (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = 0
  · rw [hI]
    simp
    exact hR.le
  · have h_eq : ((∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / R) /
      (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = 1 / R := by
      field_simp [hI]
    rw [h_eq]

theorem inv_R_le_df2Mw (d : ℕ) (hd : 1 ≤ d) :
    1 / (134 * d * Real.sqrt (Real.log (2 * d + 2))) ≤ df2Mw d := by
  have hdpos_nat : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- log(2d+2) ≥ 1
  have hlog_one : (1 : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) := by
    have h4le : (4 : ℝ) ≤ 2 * (d : ℝ) + 2 := by nlinarith
    have h4pos : (0 : ℝ) < (4 : ℝ) := by norm_num
    have hlog4 : Real.log (4 : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) :=
      Real.log_le_log h4pos h4le
    have h_one_le_log4 : (1 : ℝ) ≤ Real.log (4 : ℝ) := by
      have h_exp_lt : Real.exp (1 : ℝ) < (4 : ℝ) := by
        have h := Real.exp_one_lt_d9
        linarith
      have hpos_exp : (0 : ℝ) < Real.exp (1 : ℝ) := Real.exp_pos (1 : ℝ)
      have h := Real.log_lt_log hpos_exp h_exp_lt
      have h' : (1 : ℝ) < Real.log (4 : ℝ) := by
        simpa [Real.log_exp (1 : ℝ)] using h
      exact le_of_lt h'
    linarith
  -- sqrt(log(2d+2)) ≥ 1
  have hsqrt_log_one : (1 : ℝ) ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
    calc
      (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := Real.sqrt_le_sqrt hlog_one
  -- sqrt(d+1) ≥ 1
  have h_sqrt_d_ge_one : (1 : ℝ) ≤ Real.sqrt ((d : ℝ) + 1) := by
    calc
      (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt ((d : ℝ) + 1) := Real.sqrt_le_sqrt (by nlinarith)
  -- key inequality: 1/134 ≤ 1.27 * sqrt(d+1)
  have h_one_div_134_le : (1 : ℝ) / 134 ≤ 1.27 * Real.sqrt ((d : ℝ) + 1) := by
    have h_ineq : (1 : ℝ) / 134 ≤ 1.27 * Real.sqrt (2 : ℝ) := by
      have h_sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt (2 : ℝ) := by
        calc
          (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
          _ ≤ Real.sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
      nlinarith
    calc
      (1 : ℝ) / 134 ≤ 1.27 * Real.sqrt (2 : ℝ) := h_ineq
      _ ≤ 1.27 * Real.sqrt ((d : ℝ) + 1) := by
        have h_sqrt2_le : Real.sqrt (2 : ℝ) ≤ Real.sqrt ((d : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by nlinarith)
        nlinarith
  -- combine
  have h_left : 1 / (134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ≤
      1 / (134 * (d : ℝ)) := by
    refine (one_div_le_one_div ?_ ?_).mpr ?_
    · positivity
    · positivity
    · nlinarith
  have h_right : 1 / (134 * (d : ℝ)) ≤ df2Mw d := by
    unfold df2Mw
    calc
      1 / (134 * (d : ℝ)) = (1 / 134) / (d : ℝ) := by ring
      _ ≤ (1.27 * Real.sqrt ((d : ℝ) + 1)) / (d : ℝ) :=
        div_le_div_of_nonneg_right h_one_div_134_le (by positivity)
      _ = 1.27 * Real.sqrt ((d : ℝ) + 1) / (d : ℝ) := by ring
  linarith

theorem affine_interior_mem {d : ℕ} (K C : Set (EuclideanSpace ℝ (Fin d)))
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Function.Surjective A) (hC : ∀ y ∈ C, μ + A y ∈ K) (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ interior C) :
    μ + A y ∈ interior K := by
  have h_open_A : IsOpenMap A := ContinuousLinearMap.isOpenMap A hA
  have h_open_trans : IsOpenMap (fun (z : EuclideanSpace ℝ (Fin d)) => μ + z) := by
    have : IsOpenMap (Homeomorph.addLeft μ) := (Homeomorph.addLeft μ).isOpenMap
    simpa [Homeomorph.coe_addLeft] using this
  have h_open_h : IsOpenMap (fun (z : EuclideanSpace ℝ (Fin d)) => μ + A z) :=
    h_open_trans.comp h_open_A
  have h_int_open : IsOpen (interior C) := isOpen_interior
  have h_int_sub_C : interior C ⊆ C := interior_subset
  set h := fun (z : EuclideanSpace ℝ (Fin d)) => μ + A z with hh
  have h_img_open : IsOpen (h '' interior C) :=
    h_open_h (interior C) h_int_open
  have h_img_sub_K : h '' interior C ⊆ K := by
    rintro z ⟨w, hw, rfl⟩
    exact hC w (h_int_sub_C hw)
  have h_img_sub_int_K : h '' interior C ⊆ interior K :=
    interior_maximal h_img_sub_K h_img_open
  have hy_mem : h y ∈ h '' interior C := by
    refine ⟨y, hy, ?_⟩
    rfl
  exact h_img_sub_int_K hy_mem

/-! ## The world as a probability space -/

/-- The sample space of the world: the Gaussian stream and the noise. -/
abbrev WΩ : Type := (ℕ → ℝ) × (ℕ → ℝ)

/-- The sigma-field of term `i` of the Gaussian stream. -/
abbrev gσ (i : ℕ) : MeasurableSpace WΩ :=
  MeasurableSpace.comap Prod.fst (MeasurableSpace.comap (fun x : ℕ → ℝ => x i) inferInstance)

/-- The terms of the Gaussian stream and the noise: an independent family under `gaussStream.prod ν`. -/
abbrev famσ (k : Option ℕ) : MeasurableSpace WΩ :=
  k.elim (MeasurableSpace.comap Prod.snd inferInstance) gσ

theorem gσ_le (i : ℕ) : gσ i ≤ (inferInstance : MeasurableSpace WΩ) := by
  rw [gσ, MeasurableSpace.comap_comp]
  exact ((measurable_pi_apply i).comp measurable_fst).comap_le

theorem famσ_le (k : Option ℕ) : famσ k ≤ (inferInstance : MeasurableSpace WΩ) := by
  cases k with
  | none => exact measurable_snd.comap_le
  | some i => exact gσ_le i

instance isProb_gaussStream : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

theorem iIndep_coords : iIndep (fun i : ℕ => MeasurableSpace.comap (fun x : ℕ → ℝ => x i) inferInstance) gaussStream :=
  (iIndepFun_iff_iIndep _ _ _).mp (iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ => id) fun _ => measurable_id)

theorem iIndep_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] : iIndep famσ (gaussStream.prod ν) := by
  have := iIndep_prod_snd (fun i : ℕ => MeasurableSpace.comap (fun x : ℕ → ℝ => x i) inferInstance)
    (fun i => (measurable_pi_apply i).comap_le) gaussStream ν iIndep_coords
  convert this using 2 with k

/-- Terms of the Gaussian stream at disjoint index sets are independent, with the whole noise on one side. -/
theorem indep_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (S T : Set ℕ) (hST : Disjoint S T) :
    Indep (⨆ i ∈ S, gσ i) ((⨆ i ∈ T, gσ i) ⊔ MeasurableSpace.comap Prod.snd inferInstance) (gaussStream.prod ν) := by
  have h := indep_iSup_of_disjoint famσ_le (iIndep_world ν)
    (S := Option.some '' S) (T := insert none (Option.some '' T)) (by
      rw [Set.disjoint_insert_right]
      refine ⟨by simp, ?_⟩
      exact (Set.disjoint_image_iff (Option.some_injective _)).mpr hST)
  rw [iSup_insert, iSup_image, iSup_image] at h
  rw [sup_comm]
  exact h

/-- A term of the Gaussian stream is measurable for a sigma-field above its own. -/
theorem meas_coord {𝒢 : MeasurableSpace WΩ} (i : ℕ) (h : gσ i ≤ 𝒢) : Measurable[𝒢] fun ω : WΩ => ω.1 i := by
  refine Measurable.of_comap_le ?_
  rw [show (fun ω : WΩ => ω.1 i) = (fun x : ℕ → ℝ => x i) ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
  exact h

/-- A past term of the noise is measurable for the past of the noise. -/
theorem meas_noise (t j : ℕ) (hj : j < t) :
    Measurable[MeasurableSpace.comap Prod.snd (pastNoise t)] fun ω : WΩ => ω.2 j := by
  have h1 : Measurable[MeasurableSpace.comap Prod.snd (pastNoise t)]
      ((fun ε : ℕ → ℝ => fun i : Fin t => ε i) ∘ (Prod.snd : WΩ → ℕ → ℝ)) := by
    refine Measurable.of_comap_le ?_
    rw [← MeasurableSpace.comap_comp]
  exact (measurable_pi_apply (⟨j, hj⟩ : Fin t)).comp h1

theorem pastNoise_le (t : ℕ) : pastNoise t ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (show Measurable fun ε : ℕ → ℝ => fun i : Fin t => ε i by fun_prop).comap_le

theorem pastNoise_mono {s t : ℕ} (h : s ≤ t) : pastNoise s ≤ pastNoise t := by
  have hr : Measurable fun v : Fin t → ℝ => fun i : Fin s => v ⟨i, lt_of_lt_of_le i.2 h⟩ := by fun_prop
  have : (fun ε : ℕ → ℝ => fun i : Fin s => ε i) = (fun v : Fin t → ℝ => fun i : Fin s => v ⟨i, lt_of_lt_of_le i.2 h⟩) ∘
      (fun ε : ℕ → ℝ => fun i : Fin t => ε i) := rfl
  unfold pastNoise
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hr.comap_le

theorem measurable_pi_of {Ω ι : Type*} {m : MeasurableSpace Ω} {g : Ω → ι → ℝ} (h : ∀ i, Measurable[m] fun x => g x i) :
    Measurable[m] g :=
  measurable_pi_iff.mpr h

variable {d : ℕ}

/-! ## The marginals of the world and the noise -/

section Inst

variable (N0 S n a : ℕ)

theorem map_fst_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] :
    (gaussStream.prod ν).map Prod.fst = gaussStream := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem map_snd_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] :
    (gaussStream.prod ν).map Prod.snd = ν := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem abs_le_exp_sq (x : ℝ) : |x| ≤ Real.exp (x ^ 2) := by
  nlinarith [abs_nonneg x, sq_abs x, Real.add_one_le_exp (x ^ 2), sq_nonneg (|x| - 1 / 2)]

theorem integrable_noise_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (F : (ℕ → ℝ) → ℝ)
    (hF : Integrable F ν) : Integrable (fun ω : WΩ => F ω.2) (gaussStream.prod ν) := by
  rw [← map_snd_world ν] at hF
  exact hF.comp_measurable measurable_snd

section Noise

variable (NZ : LemmaNZProd) (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν)
include hν

theorem integrable_noise_exp (t : ℕ) :
    Integrable (fun ω : WΩ => Real.exp (ω.2 t ^ 2)) (gaussStream.prod ν) := by
  have := hν.1
  exact integrable_noise_world ν (fun ε => Real.exp (ε t ^ 2)) (hν.2 t).1

theorem integrable_noise_lin (t : ℕ) : Integrable (fun ε : ℕ → ℝ => ε t) ν :=
  (hν.2 t).1.mono' (measurable_pi_apply t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ε => by simpa [Real.norm_eq_abs] using abs_le_exp_sq (ε t))

end Noise

end Inst

end Layer2

end AdversarialBco.Poly
