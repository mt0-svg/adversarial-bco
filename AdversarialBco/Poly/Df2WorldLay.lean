/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# The world as an instance of setting (E)

The world `ω = (gs, noise)` under `gaussStream.prod ν`. The epoch of D0 started before round `a` reads, in its round
`s`, the `d + 1` terms of the block of round `a + s` of the Gaussian stream when `a + s < n`; past the horizon the
block of round `a + s ≥ n` lies in the spare region, which the out-of-range entries of the stream of PG read too, so
the instance reads fresh terms there instead (`lay`: `S + pair 0 (pair 0 (d + …))`, which PG never reads,
`mrA_ne_lay`, `mrT_ne_lay`). The filtration `𝒢w a s` holds every term of the Gaussian stream outside the rounds
`s' ≥ s` of the instance, and the noise before round `a + s`.

* `indep_world`: the terms of the Gaussian stream at disjoint index sets, with the whole noise on one side, are
  independent (`iIndep_prod_snd`, `iIndepFun_infinitePi`).
* `setE_world`: the instance is a setting (E) (`Df2SetE`): the draw `ξ s` is a standard Gaussian vector independent of
  `𝒢w a s`; the noise `e s = (ε_{a+s} + g/2)/2` is centred with `E exp(e²) ≤ 2` given `𝒢w a s` and `ξ s`
  (`exp_sq_mid_le`, `gauss_exp_quarter`, Lemma NZ on the product).
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

/-! ## The layout of the instance -/

/-- The index of coordinate `c` (`c ≤ d`) of round `s` of the epoch started before round `a`: the block of round
`a + s` of the stream when `a + s < n`, else a fresh index past the spare index `S`. -/
def lay (N0 S n d a s : ℕ) (c : Fin (d + 1)) : ℕ :=
  if a + s < n then N0 + (a + s) * (d + 1) + c else S + Nat.pair 0 (Nat.pair 0 (d + (s * (d + 1) + c)))

theorem lay_inj (N0 S n d a s s' : ℕ) (hS : N0 + n * (d + 1) ≤ S) (c c' : Fin (d + 1))
    (h : lay N0 S n d a s c = lay N0 S n d a s' c') : s = s' ∧ c = c' := by
  have hc := c.isLt
  have hc' := c'.isLt
  have key : ∀ x y : ℕ, x * (d + 1) + c = y * (d + 1) + c' → x = y ∧ c = c' := fun x y e => by
    obtain ⟨h1, h2⟩ := mr_divmod_inj (d + 1) x y c c' hc hc' e
    exact ⟨h1, Fin.ext h2⟩
  unfold lay at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨e1, e2⟩ := key (a + s) (a + s') (by omega)
    exact ⟨by omega, e2⟩
  · exfalso
    have : (a + s) * (d + 1) + c < n * (d + 1) := by
      have : (a + s + 1) * (d + 1) ≤ n * (d + 1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    omega
  · exfalso
    have : (a + s') * (d + 1) + c' < n * (d + 1) := by
      have : (a + s' + 1) * (d + 1) ≤ n * (d + 1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    omega
  · have e := Nat.add_left_cancel h
    rw [Nat.pair_eq_pair] at e
    rw [Nat.pair_eq_pair] at e
    exact key s s' (by omega)

theorem lay_ge (N0 S n d a s : ℕ) (hS : N0 ≤ S) (c : Fin (d + 1)) : N0 ≤ lay N0 S n d a s c := by
  unfold lay; split_ifs <;> omega

theorem lay_lt_or (N0 S n d a s : ℕ) (hS : S = N0 + n * (d + 1)) (c : Fin (d + 1)) :
    lay N0 S n d a s c < S ∨ lay N0 S n d a s c = S + Nat.pair 0 (Nat.pair 0 (d + (s * (d + 1) + c))) := by
  unfold lay
  split_ifs with h
  · left
    have hc := c.isLt
    have : (a + s + 1) * (d + 1) ≤ n * (d + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · right; rfl

theorem mrA_ne_lay (m Jr d S n : ℕ) (Ns NT W : ℕ → ℕ) (MT : ℕ)
    (hW : ∀ i, W i = Ns i + MT * NT i) (hS : S = mrOff Jr d W m + n * (d + 1)) (i r k : ℕ) (c : Fin d) (a s : ℕ)
    (c' : Fin (d + 1)) : mrA m Jr d S Ns W i r k c ≠ lay (mrOff Jr d W m) S n d a s c' := by
  intro h
  have hge := lay_ge (mrOff Jr d W m) S n d a s (by omega) c'
  unfold mrA at h
  split_ifs at h with hin
  · obtain ⟨hi, hr, hk⟩ := hin
    have hkW : k < W i := by rw [hW i]; omega
    have := mrOff_add_lt Jr d m i _ W hi (mr_slot_lt Jr (W i) d r k c hr hkW c.isLt)
    omega
  · rcases lay_lt_or (mrOff Jr d W m) S n d a s hS c' with hl | hl
    · omega
    · rw [hl] at h
      have e := Nat.add_left_cancel h
      rw [Nat.pair_eq_pair, Nat.pair_eq_pair] at e
      have hc := c.isLt
      omega

theorem mrT_ne_lay (m Jr MT d S n : ℕ) (Ns NT W : ℕ → ℕ)
    (hW : ∀ i, W i = Ns i + MT * NT i) (hS : S = mrOff Jr d W m + n * (d + 1)) (i r v k : ℕ) (c : Fin d) (a s : ℕ)
    (c' : Fin (d + 1)) : mrT m Jr MT d S Ns NT W i r v k c ≠ lay (mrOff Jr d W m) S n d a s c' := by
  intro h
  have hge := lay_ge (mrOff Jr d W m) S n d a s (by omega) c'
  unfold mrT at h
  split_ifs at h with hin
  · obtain ⟨hi, hr, hv, hk⟩ := hin
    have hy : Ns i + v * NT i + k < W i := by
      rw [hW i]
      have : (v + 1) * NT i ≤ MT * NT i := Nat.mul_le_mul_right _ hv
      nlinarith
    have := mrOff_add_lt Jr d m i _ W hi (mr_slot_lt Jr (W i) d r (Ns i + v * NT i + k) c hr hy c.isLt)
    have e : r * W i + Ns i + v * NT i + k = r * W i + (Ns i + v * NT i + k) := by ring
    rw [e] at h
    omega
  · rcases lay_lt_or (mrOff Jr d W m) S n d a s hS c' with hl | hl
    · omega
    · rw [hl] at h
      have e := Nat.add_left_cancel h
      rw [Nat.pair_eq_pair, Nat.pair_eq_pair] at e
      omega

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

/-! ## The filtration of the instance -/

variable {d : ℕ}

/-- The indices of the rounds `s' ≥ s` of the instance. -/
def fut (N0 S n d a s : ℕ) : Set ℕ := {i | ∃ s', s ≤ s' ∧ ∃ c, lay N0 S n d a s' c = i}

theorem fut_anti (N0 S n d a : ℕ) {s t : ℕ} (h : s ≤ t) : fut N0 S n d a t ⊆ fut N0 S n d a s := by
  rintro i ⟨s', hs', c, rfl⟩
  exact ⟨s', h.trans hs', c, rfl⟩

/-- The sigma-field before round `s` of the instance at start `a`: the terms of the Gaussian stream outside the rounds
`s' ≥ s`, and the noise before round `a + s`. -/
def 𝒢w (N0 S n d a : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace WΩ) where
  seq s := (⨆ i ∈ (fut N0 S n d a s)ᶜ, gσ i) ⊔ MeasurableSpace.comap Prod.snd (pastNoise (a + s))
  mono' s t h := sup_le_sup
    (iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ (fut N0 S n d a t)ᶜ) => gσ i) i
      (fun h' => hi (fut_anti N0 S n d a h h')))
    (MeasurableSpace.comap_mono (pastNoise_mono (by omega)))
  le' s := sup_le (iSup₂_le fun i _ => gσ_le i)
    ((MeasurableSpace.comap_mono (pastNoise_le _)).trans measurable_snd.comap_le)

/-- The draw of round `s` of the instance. -/
def xiL (N0 S n d a s : ℕ) (ω : WΩ) : Fin d → ℝ := fun c => ω.1 (lay N0 S n d a s c.castSucc)

/-- The noise of round `s` of the instance: `(ε_{a+s} + g/2)/2`, `g` the last term of the block. -/
noncomputable def eL (N0 S n d a s : ℕ) (ω : WΩ) : ℝ := (ω.2 (a + s) + ω.1 (lay N0 S n d a s (Fin.last d)) / 2) / 2

/-! ## The instance -/

section Inst

variable (N0 S n a : ℕ)

theorem lay_mem_fut (s : ℕ) (c : Fin (d + 1)) : lay N0 S n d a s c ∈ fut N0 S n d a s := ⟨s, le_rfl, c, rfl⟩

theorem lay_not_fut (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) (c : Fin (d + 1)) :
    lay N0 S n d a s c ∉ fut N0 S n d a (s + 1) := by
  rintro ⟨s', hs', c', h⟩
  have := (lay_inj N0 S n d a s' s hS c' c h).1
  omega

theorem gσ_le_𝒢w (s i : ℕ) (hi : i ∉ fut N0 S n d a s) : gσ i ≤ 𝒢w N0 S n d a s :=
  (le_iSup₂ (f := fun i (_ : i ∈ (fut N0 S n d a s)ᶜ) => gσ i) i hi).trans le_sup_left

theorem xiL_meas (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) : Measurable[𝒢w N0 S n d a (s + 1)] (xiL N0 S n d a s) :=
  measurable_pi_of fun _ => meas_coord _ (gσ_le_𝒢w N0 S n a (s + 1) _ (lay_not_fut N0 S n a hS s _))

theorem xiL_meas_fut (s : ℕ) : Measurable[⨆ i ∈ fut N0 S n d a s, gσ i] (xiL N0 S n d a s) :=
  measurable_pi_of fun _ => meas_coord _
    (le_iSup₂ (f := fun i (_ : i ∈ fut N0 S n d a s) => gσ i) _ (lay_mem_fut N0 S n a s _))

theorem map_fst_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] :
    (gaussStream.prod ν).map Prod.fst = gaussStream := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem map_snd_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] :
    (gaussStream.prod ν).map Prod.snd = ν := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem map_coord_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (i : ℕ) :
    (gaussStream.prod ν).map (fun ω : WΩ => ω.1 i) = gaussianReal 0 1 := by
  rw [show (fun ω : WΩ => ω.1 i) = (fun x : ℕ → ℝ => x i) ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_pi_apply i) measurable_fst, map_fst_world, gaussStream,
    Measure.infinitePi_map_eval]

theorem xiL_law (hS : N0 + n * (d + 1) ≤ S) (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (s : ℕ) :
    (gaussStream.prod ν).map (xiL N0 S n d a s) = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  have hσ : Function.Injective fun c : Fin d => lay N0 S n d a s c.castSucc := fun c c' h =>
    Fin.castSucc_injective _ (lay_inj N0 S n d a s s hS _ _ h).2
  rw [show xiL N0 S n d a s = (fun x : ℕ → ℝ => fun c : Fin d => x (lay N0 S n d a s c.castSucc)) ∘ Prod.fst
    from rfl, ← Measure.map_map (by fun_prop) measurable_fst, map_fst_world, gaussStream,
    infinitePi_comp_inj _ _ hσ, Measure.infinitePi_eq_pi]

theorem xiL_indep (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (s : ℕ) :
    Indep (MeasurableSpace.comap (xiL N0 S n d a s) inferInstance) (𝒢w N0 S n d a s) (gaussStream.prod ν) := by
  have h := indep_world ν (fut N0 S n d a s) (fut N0 S n d a s)ᶜ disjoint_compl_right
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h (xiL_meas_fut N0 S n a s).comap_le) ?_
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (pastNoise_le _))

theorem abs_le_exp_sq (x : ℝ) : |x| ≤ Real.exp (x ^ 2) := by
  nlinarith [abs_nonneg x, sq_abs x, Real.add_one_le_exp (x ^ 2), sq_nonneg (|x| - 1 / 2)]

/-- The index of the dither of round `s` of the instance. -/
abbrev idxZ (s : ℕ) : ℕ := lay N0 S n d a s (Fin.last d)

/-- The sigma-field of (E3) at round `s`. -/
abbrev HL (s : ℕ) : MeasurableSpace WΩ :=
  𝒢w N0 S n d a s ⊔ MeasurableSpace.comap (xiL N0 S n d a s) inferInstance

theorem HL_le (s : ℕ) : HL (d := d) N0 S n a s ≤ (inferInstance : MeasurableSpace WΩ) :=
  sup_le ((𝒢w N0 S n d a).le s) (xiL_meas_fut N0 S n a s |>.mono
    (iSup₂_le fun i _ => gσ_le i) le_rfl).comap_le

theorem HL_le_noise (s : ℕ) :
    HL (d := d) N0 S n a s ≤ MeasurableSpace.comap Prod.fst inferInstance ⊔
      MeasurableSpace.comap Prod.snd (pastNoise (a + s)) := by
  have hfst : ∀ i, gσ i ≤ MeasurableSpace.comap (Prod.fst : WΩ → ℕ → ℝ) inferInstance := fun i =>
    MeasurableSpace.comap_mono (measurable_pi_apply i).comap_le
  refine sup_le (sup_le ((iSup₂_le fun i _ => hfst i).trans le_sup_left) le_sup_right) ?_
  refine le_sup_of_le_left ?_
  rw [show xiL N0 S n d a s = (fun x : ℕ → ℝ => fun c : Fin d => x (lay N0 S n d a s c.castSucc)) ∘ Prod.fst
    from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

theorem HL_le_dither (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) :
    HL (d := d) N0 S n a s ≤ (⨆ i ∈ ({idxZ (d := d) N0 S n a s} : Set ℕ)ᶜ, gσ i) ⊔
      MeasurableSpace.comap Prod.snd inferInstance := by
  have hmem : ∀ i, i ≠ idxZ (d := d) N0 S n a s →
      gσ i ≤ ⨆ i ∈ ({idxZ (d := d) N0 S n a s} : Set ℕ)ᶜ, gσ i := fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ ({idxZ (d := d) N0 S n a s} : Set ℕ)ᶜ) => gσ i) i hi
  refine sup_le (sup_le (iSup₂_le fun i hi => (hmem i ?_).trans le_sup_left)
    (le_sup_of_le_right (MeasurableSpace.comap_mono (pastNoise_le _)))) (le_sup_of_le_left ?_)
  · rintro rfl
    exact hi (lay_mem_fut N0 S n a s _)
  · refine (measurable_pi_of fun c => meas_coord _ (hmem _ fun h => ?_)).comap_le
    have := (lay_inj N0 S n d a s s hS _ _ h).2
    exact Fin.castSucc_ne_last c this

theorem indep_dither (hS : N0 + n * (d + 1) ≤ S) (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (s : ℕ) :
    Indep (gσ (idxZ (d := d) N0 S n a s)) (HL (d := d) N0 S n a s) (gaussStream.prod ν) := by
  have h := indep_world ν {idxZ (d := d) N0 S n a s} {idxZ (d := d) N0 S n a s}ᶜ disjoint_compl_right
  rw [iSup_singleton] at h
  exact indep_of_indep_of_le_right h (HL_le_dither N0 S n a hS s)

theorem integral_coord_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (i : ℕ) (F : ℝ → ℝ)
    (hF : Measurable F) : ∫ ω, F (ω.1 i) ∂(gaussStream.prod ν) = ∫ x, F x ∂(gaussianReal 0 1) := by
  rw [← map_coord_world ν i, integral_map (by fun_prop) hF.aestronglyMeasurable]

theorem integrable_coord_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (i : ℕ) (F : ℝ → ℝ)
    (hF : Integrable F (gaussianReal 0 1)) : Integrable (fun ω : WΩ => F (ω.1 i)) (gaussStream.prod ν) := by
  rw [← map_coord_world ν i] at hF
  exact hF.comp_measurable (by fun_prop)

theorem integrable_noise_world (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (F : (ℕ → ℝ) → ℝ)
    (hF : Integrable F ν) : Integrable (fun ω : WΩ => F ω.2) (gaussStream.prod ν) := by
  rw [← map_snd_world ν] at hF
  exact hF.comp_measurable measurable_snd

theorem eL_meas (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) : Measurable[𝒢w N0 S n d a (s + 1)] (eL N0 S n d a s) := by
  have h1 : Measurable[𝒢w N0 S n d a (s + 1)] fun ω : WΩ => ω.2 (a + s) :=
    (meas_noise (a + (s + 1)) (a + s) (by omega)).mono le_sup_right le_rfl
  have h2 : Measurable[𝒢w N0 S n d a (s + 1)] fun ω : WΩ => ω.1 (idxZ (d := d) N0 S n a s) :=
    meas_coord _ (gσ_le_𝒢w N0 S n a (s + 1) _ (lay_not_fut N0 S n a hS s _))
  exact (h1.add (h2.div_const 2)).div_const 2

theorem eL_bound (s : ℕ) (ω : WΩ) :
    Real.exp (eL N0 S n d a s ω ^ 2) ≤
      (1 / 2 : ℝ) * (Real.exp (ω.2 (a + s) ^ 2) + Real.exp ((ω.1 (idxZ (d := d) N0 S n a s) / 2) ^ 2)) := by
  have := exp_sq_mid_le (ω.2 (a + s)) (ω.1 (idxZ (d := d) N0 S n a s) / 2)
  simp only [eL, idxZ] at this ⊢
  linarith

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

theorem integrable_eL_exp (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) :
    Integrable (fun ω => Real.exp (eL N0 S n d a s ω ^ 2)) (gaussStream.prod ν) := by
  have := hν.1
  have hA := integrable_noise_exp ν hν (a + s)
  have hB := integrable_coord_world ν (idxZ (d := d) N0 S n a s) _ gauss_exp_quarter.1
  refine ((hA.add hB).const_mul (1 / 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp ((eL_meas N0 S n a hS s).mono ((𝒢w N0 S n d a).le _) le_rfl |>.pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact eL_bound N0 S n a s ω

theorem condExp_dither (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) (F : ℝ → ℝ) (hF : Measurable F) :
    (gaussStream.prod ν)[fun ω => F (ω.1 (idxZ (d := d) N0 S n a s)) | HL (d := d) N0 S n a s] =ᵐ[gaussStream.prod ν]
      fun _ => ∫ x, F x ∂(gaussianReal 0 1) := by
  have := hν.1
  rw [← integral_coord_world ν _ F hF]
  exact condExp_indep_eq (gσ_le _) (HL_le N0 S n a s)
    (hF.comp (meas_coord _ le_rfl)).stronglyMeasurable (indep_dither N0 S n a hS ν s)

include NZ in
theorem eL_mean (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) :
    (gaussStream.prod ν)[eL N0 S n d a s | HL (d := d) N0 S n a s] =ᵐ[gaussStream.prod ν] 0 := by
  have := hν.1
  have he : eL N0 S n d a s = (1 / 2 : ℝ) • ((fun ω : WΩ => ω.2 (a + s)) +
      fun ω : WΩ => ω.1 (idxZ (d := d) N0 S n a s) / 2) := by
    funext ω; simp only [eL, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hF := integrable_noise_world ν _ (integrable_noise_lin ν hν (a + s))
  have hG : Integrable (fun ω : WΩ => ω.1 (idxZ (d := d) N0 S n a s) / 2) (gaussStream.prod ν) :=
    integrable_coord_world ν _ (fun x => x / 2) ((memLp_id_gaussianReal 1).integrable le_rfl |>.div_const 2)
  have h1 := condExp_snd_eq_zero NZ (pastNoise (a + s)) gaussStream ν (pastNoise_le _) _ (HL_le_noise (d := d) N0 S n a s)
    (fun ε => ε (a + s)) (integrable_noise_lin ν hν (a + s)) (hν.2 (a + s)).2.1
  have h2 := condExp_dither N0 S n a ν hν hS s (fun x => x / 2) (by fun_prop)
  have h0 : ∫ x, x / 2 ∂(gaussianReal 0 1) = 0 := by
    rw [integral_div, integral_id_gaussianReal, zero_div]
  rw [he]
  refine (condExp_smul _ _ _).trans ?_
  have hadd := condExp_add hF hG (HL (d := d) N0 S n a s)
  filter_upwards [hadd, h1, h2] with ω hω h1ω h2ω
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hω h1ω h2ω ⊢
  rw [hω, Pi.add_apply, h1ω, h2ω, h0]
  simp

include NZ in
theorem eL_exp (hS : N0 + n * (d + 1) ≤ S) (s : ℕ) :
    (gaussStream.prod ν)[fun ω => Real.exp (eL N0 S n d a s ω ^ 2) | HL (d := d) N0 S n a s] ≤ᵐ[gaussStream.prod ν]
      fun _ => 2 := by
  have := hν.1
  have hA := integrable_noise_exp ν hν (a + s)
  have hB := integrable_coord_world ν (idxZ (d := d) N0 S n a s) _ gauss_exp_quarter.1
  have hmono := condExp_mono (m := HL (d := d) N0 S n a s) (integrable_eL_exp N0 S n a ν hν hS s)
    ((hA.add hB).smul (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using eL_bound N0 S n a s ω)
  have hsm := condExp_smul (μ := gaussStream.prod ν) (1 / 2 : ℝ)
    ((fun ω : WΩ => Real.exp (ω.2 (a + s) ^ 2)) + fun ω : WΩ => Real.exp ((ω.1 (idxZ (d := d) N0 S n a s) / 2) ^ 2))
    (HL (d := d) N0 S n a s)
  have hadd := condExp_add hA hB (HL (d := d) N0 S n a s)
  have h1 := condExp_snd_le NZ (pastNoise (a + s)) gaussStream ν (pastNoise_le _) _ (HL_le_noise (d := d) N0 S n a s)
    (fun ε => Real.exp (ε (a + s) ^ 2)) (hν.2 (a + s)).1 2 (hν.2 (a + s)).2.2
  have h2 := condExp_dither N0 S n a ν hν hS s (fun x => Real.exp ((x / 2) ^ 2)) (by fun_prop)
  have h0 := gauss_exp_quarter.2
  filter_upwards [hmono, hsm, hadd, h1, h2] with ω hm hs ha h1ω h2ω
  have hm2 := hm.trans_eq hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm2
  rw [ha] at hm2
  simp only [Pi.add_apply] at hm2
  rw [h2ω] at hm2
  linarith

include NZ in
/-- The world is an instance of setting (E), for every start round `a`. -/
theorem setE_world (hS : N0 + n * (d + 1) ≤ S) :
    Df2SetE d (gaussStream.prod ν) (𝒢w N0 S n d a) (xiL N0 S n d a) (eL N0 S n d a) := by
  have := hν.1
  exact
  { xi_meas := xiL_meas N0 S n a hS
    xi_law := xiL_law N0 S n a hS ν
    xi_indep := xiL_indep N0 S n a ν
    e_meas := eL_meas N0 S n a hS
    e_int := integrable_eL_exp N0 S n a ν hν hS
    e_mean := eL_mean N0 S n a NZ ν hν hS
    e_exp := eL_exp N0 S n a NZ ν hν hS }

end Noise

end Inst

end Layer2

end AdversarialBco.Poly
