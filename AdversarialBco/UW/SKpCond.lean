/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.WrapBias
public import AdversarialBco.UW.SKpGauss
public import AdversarialBco.UW.EvCProc

@[expose] public section

/-!
# Lemma SK' (ii), (iii), (iv) given the past

In the round of setting (E) of UW/WrapIncr.lean (`σ` measurable in the past `𝒢`, `ξ` standard Gaussian independent of
`𝒢`, the noise `e` centred with `E[exp(e²) | 𝒢 ∨ ξ] ≤ 2`):

* `cond_bset` (SK' (ii)): the set `B = {|ξ|² > b0} ∪ {P(σ, ξ) > 10} ∪ {|e| > t0}` has `P(B | 𝒢) ≤ c₁ + c₂ + 2 e^{-t0²}`
  when `γ(|z|² > b0) ≤ c₁` and `γ(P(s, ·) > 10) ≤ c₂` for every `s`;
* `cond_pow_four` (SK' (iii)): `|Y| ≤ C (1 + |ξ|₂)(1 + |e|)` gives `E[Y⁴ | 𝒢] ≤ 1536 C⁴ d²`;
* `bias_round` (SK' (iv)): with the weight and the clip `obsW b0 y0`, when `Y` stays in `[-y0, y0]` off `B`, the
  conditional mean of `obsW(ξ, Y) D` is `∫ E D dγ` up to
  `2 (1536 C⁴ d²)^{1/4} (E_z D⁴)^{1/4} (c₁ + c₂ + 2 e^{-t0²})^{1/2}`
  (`cond_bias_w` with the two bounds above).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AdversarialBco.UW.SKp

open AdversarialBco.Poly AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-! ## Real facts -/

/-- `∫ 1_A dγ ≤ c` from `γ(A) ≤ c`. -/
theorem int_indicator_le {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c)
    (h : gam d A ≤ ENNReal.ofReal c) : ∫ z, A.indicator (1 : (Fin d → ℝ) → ℝ) z ∂(gam d) ≤ c := by
  rw [integral_indicator_one hA, measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc h

/-- `(1 + |x|)⁴ ≤ 24 exp(x²)`. -/
theorem one_add_abs_pow_four_le (x : ℝ) : (1 + |x|) ^ 4 ≤ 24 * Real.exp (x ^ 2) := by
  have ha := abs_nonneg x
  have h1 : (1 + |x|) ^ 4 ≤ 8 * (1 + |x| ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (|x| - 1)) (show 0 ≤ 7 * |x| ^ 2 + 10 * |x| + 7 by positivity)]
  have h2 : |x| ^ 4 ≤ 2 * Real.exp (x ^ 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (sq_nonneg x)
    have e : |x| ^ 4 = (x ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
    nlinarith [sq_nonneg x]
  have h3 : 1 ≤ Real.exp (x ^ 2) := Real.one_le_exp (sq_nonneg x)
  linarith

/-- `E(1 + |ξ|₂)⁴ ≤ 32 d²`, with the Euclidean norm `|z|₂ = (z ⬝ z)^{1/2}`. -/
theorem int_one_add_sqrt_pow_four (hd : 1 ≤ d) :
    ∫ z, (1 + Real.sqrt (z ⬝ᵥ z)) ^ 4 ∂(gam d) ≤ 32 * (d : ℝ) ^ 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpt : ∀ z : Fin d → ℝ, (1 + Real.sqrt (z ⬝ᵥ z)) ^ 4 ≤ 8 + 8 * (z ⬝ᵥ z) ^ 2 := by
    intro z
    have hs := Real.sq_sqrt (dot_self_nonneg' z)
    set r := Real.sqrt (z ⬝ᵥ z)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have h3 : (1 + r) ^ 4 ≤ 8 + 8 * (r ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (r - 1)) (show 0 ≤ 7 * r ^ 2 + 10 * r + 7 by positivity)]
    rw [← hs]; exact h3
  have hdot : Continuous fun z : Fin d → ℝ => z ⬝ᵥ z := continuous_id.dotProduct continuous_id
  have hi2 : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) (gam d) := by
    refine integrable_of_poly (hdot.pow 2).aestronglyMeasurable ((d : ℝ) ^ 2) 4 fun z => ?_
    have h1 := dot_self_le z
    have h0 := dot_self_nonneg' z
    have hn := norm_nonneg z
    rw [abs_of_nonneg (sq_nonneg _)]
    have h2 : z ⬝ᵥ z ≤ d * (1 + ‖z‖) ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by linarith))
    calc (z ⬝ᵥ z) ^ 2 ≤ (d * (1 + ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ h0 h2 2
      _ = (d : ℝ) ^ 2 * (1 + ‖z‖) ^ 4 := by ring
  have hi : Integrable (fun z : Fin d → ℝ => 8 + 8 * (z ⬝ᵥ z) ^ 2) (gam d) :=
    (integrable_const 8).add (hi2.const_mul 8)
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) hi
    (Filter.Eventually.of_forall hpt)
  have hc : ∫ _ : Fin d → ℝ, (8 : ℝ) ∂(gam d) = 8 := by simp
  rw [integral_add (integrable_const 8) (hi2.const_mul 8), hc, integral_const_mul] at hm
  have h3 := integral_dot_self_sq_le (d := d)
  nlinarith

/-- `|z|₂ ≤ √d (1 + |z|)` (sup norm on the right). -/
theorem sqrt_dot_le_poly (z : Fin d → ℝ) : Real.sqrt (z ⬝ᵥ z) ≤ Real.sqrt d * (1 + ‖z‖) := by
  have h := sqrt_dot_le z
  have hn := norm_nonneg z
  have hs := Real.sqrt_nonneg (d : ℝ)
  calc Real.sqrt (z ⬝ᵥ z) ≤ Real.sqrt d * ‖z‖ := h
    _ ≤ Real.sqrt d * (1 + ‖z‖) := mul_le_mul_of_nonneg_left (by linarith) hs

/-! ## The round -/

section Round

variable {Ω S : Type} [MeasurableSpace S]

/-- The set where the weight or the clip may act: `|ξ|² > b0`, `P > 10` or `|e| > t0`. -/
def bset (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ) (P : S × (Fin d → ℝ) → ℝ) (b0 t0 : ℝ) : Set Ω :=
  {ω | b0 < ξ ω ⬝ᵥ ξ ω} ∪ {ω | 10 < P (σ ω, ξ ω)} ∪ {ω | t0 < |e ω|}

/-- The indicator of `|z|² > b0` on `S × ℝ^d`. -/
noncomputable def ind1 (b0 : ℝ) (x : S × (Fin d → ℝ)) : ℝ := if b0 < x.2 ⬝ᵥ x.2 then 1 else 0

/-- The indicator of `P > 10` on `S × ℝ^d`. -/
noncomputable def ind2 (P : S × (Fin d → ℝ) → ℝ) (x : S × (Fin d → ℝ)) : ℝ := if 10 < P x then 1 else 0

theorem measurable_ind1 (b0 : ℝ) : Measurable (ind1 (S := S) (d := d) b0) := by
  have hdot : Measurable fun z : Fin d → ℝ => z ⬝ᵥ z := (continuous_id.dotProduct continuous_id).measurable
  exact Measurable.ite (measurableSet_lt measurable_const (hdot.comp measurable_snd)) measurable_const
    measurable_const

theorem measurable_ind2 {P : S × (Fin d → ℝ) → ℝ} (hP : Measurable P) : Measurable (ind2 P) :=
  Measurable.ite (measurableSet_lt measurable_const hP) measurable_const measurable_const

theorem measurableSet_bset {m0 : MeasurableSpace Ω} {σ : Ω → S} {ξ : Ω → Fin d → ℝ} {e : Ω → ℝ}
    {P : S × (Fin d → ℝ) → ℝ} (hσ : Measurable σ) (hξ : Measurable ξ) (he : Measurable e) (hP : Measurable P)
    (b0 t0 : ℝ) :
    MeasurableSet (bset σ ξ e P b0 t0) := by
  have hdot : Measurable fun z : Fin d → ℝ => z ⬝ᵥ z := (continuous_id.dotProduct continuous_id).measurable
  exact ((measurableSet_lt measurable_const (hdot.comp hξ)).union
    (measurableSet_lt measurable_const (hP.comp (hσ.prodMk hξ)))).union
    (measurableSet_lt measurable_const he.abs)

/-- A measurable function with values in `[0, 1]` is integrable for a probability measure. -/
theorem integrable_of_unit {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]; exact (hb ω).2)

/-- `E[exp(e²) | 𝒢] ≤ 2` from `E[exp(e²) | 𝒢 ∨ ξ] ≤ 2`. -/
theorem cond_exp_sq_le (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h𝒢 : 𝒢 ≤ m0) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ) (hξ : Measurable ξ) (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2) :
    μ[fun ω => Real.exp (e ω ^ 2) | 𝒢] ≤ᵐ[μ] fun _ => 2 := by
  have h𝒢' : 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance ≤ m0 := sup_le h𝒢 hξ.comap_le
  have h1 := condExp_condExp_of_le (μ := μ) (f := fun ω => Real.exp (e ω ^ 2)) le_sup_left h𝒢'
  have h2 := condExp_mono (m := 𝒢) (μ := μ) integrable_condExp (integrable_const (2 : ℝ)) hee
  rw [condExp_const h𝒢] at h2
  filter_upwards [h1, h2] with ω h1 h2
  rw [← h1]; exact h2

/-- **Lemma SK' (ii)**: `P(B | 𝒢) ≤ c₁ + c₂ + 2 e^{-t0²}`. -/
theorem cond_bset (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ) (hσ : Measurable[𝒢] σ)
    (hξ : Measurable ξ) (he : Measurable e)
    (hlaw : μ.map ξ = gam d) (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (P : S × (Fin d → ℝ) → ℝ) (hP : Measurable P) (b0 t0 c1 c2 : ℝ) (ht0 : 0 ≤ t0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (h1 : gam d {z | b0 < z ⬝ᵥ z} ≤ ENNReal.ofReal c1)
    (h2 : ∀ s, gam d {z | 10 < P (s, z)} ≤ ENNReal.ofReal c2) :
    μ[(bset σ ξ e P b0 t0).indicator 1 | 𝒢] ≤ᵐ[μ] fun _ => c1 + c2 + 2 * Real.exp (-t0 ^ 2) := by
  classical
  have hσ0 : Measurable σ := hσ.mono h𝒢 le_rfl
  have hp : Measurable fun ω => (σ ω, ξ ω) := hσ0.prodMk hξ
  have hB := measurableSet_bset hσ0 hξ he hP b0 t0
  have m1 := (measurable_ind1 (S := S) (d := d) b0).comp hp
  have m2 := (measurable_ind2 hP).comp hp
  set I3 : Ω → ℝ := fun ω => if t0 < |e ω| then 1 else 0 with hI3
  have m3 : Measurable I3 := Measurable.ite (measurableSet_lt measurable_const he.abs) measurable_const
    measurable_const
  have u1 : ∀ x : S × (Fin d → ℝ), 0 ≤ ind1 b0 x ∧ ind1 b0 x ≤ 1 := fun x => by
    unfold ind1; split_ifs <;> norm_num
  have u2 : ∀ x : S × (Fin d → ℝ), 0 ≤ ind2 P x ∧ ind2 P x ≤ 1 := fun x => by
    unfold ind2; split_ifs <;> norm_num
  have u3 : ∀ ω, 0 ≤ I3 ω ∧ I3 ω ≤ 1 := fun ω => by
    simp only [hI3]; split_ifs <;> norm_num
  have i1 : Integrable (fun ω => ind1 b0 (σ ω, ξ ω)) μ := integrable_of_unit m1 fun ω => u1 _
  have i2 : Integrable (fun ω => ind2 P (σ ω, ξ ω)) μ := integrable_of_unit m2 fun ω => u2 _
  have i3 : Integrable I3 μ := integrable_of_unit m3 u3
  have iB : Integrable ((bset σ ξ e P b0 t0).indicator (1 : Ω → ℝ)) μ :=
    integrable_of_unit (measurable_one.indicator hB) fun ω => by
      by_cases h : ω ∈ bset σ ξ e P b0 t0 <;> simp [h]
  -- the union bound
  have hle : (bset σ ξ e P b0 t0).indicator (1 : Ω → ℝ) ≤ᵐ[μ]
      (fun ω => ind1 b0 (σ ω, ξ ω)) + (fun ω => ind2 P (σ ω, ξ ω)) + I3 := by
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, hI3, ind1, ind2]
    by_cases k1 : b0 < ξ ω ⬝ᵥ ξ ω <;> by_cases k2 : 10 < P (σ ω, ξ ω) <;> by_cases k3 : t0 < |e ω| <;>
      simp [bset, Set.indicator_apply, k1, k2, k3] <;> norm_num
  have hU := condExp_mono (m := 𝒢) iB ((i1.add i2).add i3) hle
  have hA1 := condExp_add (i1.add i2) i3 𝒢
  have hA2 := condExp_add i1 i2 𝒢
  -- the first two terms by freezing
  have hF1 := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ (ind1 b0) h𝒢 hσ hξ hind (measurable_ind1 b0) i1
  have hF2 := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ (ind2 P) h𝒢 hσ hξ hind (measurable_ind2 hP) i2
  rw [hlaw] at hF1 hF2
  have b1 : ∀ s : S, ∫ z, ind1 b0 (s, z) ∂(gam d) ≤ c1 := by
    intro s
    have hA : MeasurableSet {z : Fin d → ℝ | b0 < z ⬝ᵥ z} :=
      measurableSet_lt measurable_const (continuous_id.dotProduct continuous_id).measurable
    have e : (fun z => ind1 b0 (s, z)) = {z : Fin d → ℝ | b0 < z ⬝ᵥ z}.indicator 1 := by
      funext z; simp [ind1, Set.indicator_apply]
    rw [e]; exact int_indicator_le hA hc1 h1
  have b2 : ∀ s : S, ∫ z, ind2 P (s, z) ∂(gam d) ≤ c2 := by
    intro s
    have hA : MeasurableSet {z : Fin d → ℝ | 10 < P (s, z)} :=
      measurableSet_lt measurable_const (hP.comp measurable_prodMk_left)
    have e : (fun z => ind2 P (s, z)) = {z : Fin d → ℝ | 10 < P (s, z)}.indicator 1 := by
      funext z; simp [ind2, Set.indicator_apply]
    rw [e]; exact int_indicator_le hA hc2 (h2 s)
  -- the noise term
  have hexp := cond_exp_sq_le 𝒢 μ h𝒢 ξ e hξ hei hee
  have hI3le : I3 ≤ᵐ[μ] (Real.exp (-t0 ^ 2)) • fun ω => Real.exp (e ω ^ 2) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [hI3, Pi.smul_apply, smul_eq_mul]
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      have : t0 ^ 2 < e ω ^ 2 := by rw [← sq_abs (e ω)]; exact pow_lt_pow_left₀ h ht0 (by norm_num)
      linarith
    · exact (Real.exp_pos _).le
  have h3 := condExp_mono (m := 𝒢) i3 (hei.smul (Real.exp (-t0 ^ 2))) hI3le
  have h3s := condExp_smul (μ := μ) (Real.exp (-t0 ^ 2)) (fun ω => Real.exp (e ω ^ 2)) 𝒢
  filter_upwards [hU, hA1, hA2, hF1, hF2, h3, h3s, hexp] with ω hU hA1 hA2 hF1 hF2 h3 h3s hexp
  rw [hA1, Pi.add_apply, hA2, Pi.add_apply, hF1, hF2] at hU
  rw [h3s, Pi.smul_apply, smul_eq_mul] at h3
  have he0 := (Real.exp_pos (-t0 ^ 2)).le
  have h3' : μ[I3 | 𝒢] ω ≤ 2 * Real.exp (-t0 ^ 2) := by nlinarith
  have := b1 (σ ω)
  have := b2 (σ ω)
  linarith

/-- **Lemma SK' (iii)**: `|Y| ≤ C (1 + |ξ|₂)(1 + |e|)` gives `E[Y⁴ | 𝒢] ≤ 1536 C⁴ d²`. -/
theorem cond_pow_four (hd : 1 ≤ d) (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ) (hξ : Measurable ξ) (he : Measurable e)
    (hlaw : μ.map ξ = gam d) (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (Y : Ω → ℝ) (hY : Measurable Y) (C : ℝ) (hC : 0 ≤ C)
    (hYb : ∀ ω, |Y ω| ≤ C * (1 + Real.sqrt (ξ ω ⬝ᵥ ξ ω)) * (1 + |e ω|)) :
    μ[fun ω => Y ω ^ 4 | 𝒢] ≤ᵐ[μ] fun _ => 1536 * C ^ 4 * (d : ℝ) ^ 2 := by
  have h𝒢' : (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) ≤ m0 := sup_le h𝒢 hξ.comap_le
  have hdot : Continuous fun z : Fin d → ℝ => z ⬝ᵥ z := continuous_id.dotProduct continuous_id
  set Φ : (Fin d → ℝ) → ℝ := fun z => (1 + Real.sqrt (z ⬝ᵥ z)) ^ 4 with hΦ
  have mΦ : Measurable Φ := ((continuous_const.add (Real.continuous_sqrt.comp hdot)).pow 4).measurable
  set F : Ω → ℝ := fun ω => Φ (ξ ω) with hF
  set G : Ω → ℝ := fun ω => (1 + |e ω|) ^ 4 with hG
  have mF : Measurable F := mΦ.comp hξ
  have mG : Measurable G := (measurable_const.add he.abs).pow_const 4
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => by show 0 ≤ (1 + Real.sqrt (ξ ω ⬝ᵥ ξ ω)) ^ 4; positivity
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => by show 0 ≤ (1 + |e ω|) ^ 4; positivity
  -- polynomial bounds for the integrability
  have hsd := Real.sqrt_nonneg (d : ℝ)
  have hΦb : ∀ z : Fin d → ℝ, Φ z ≤ (1 + Real.sqrt d) ^ 4 * (1 + ‖z‖) ^ 4 := by
    intro z
    have h1 := sqrt_dot_le_poly z
    have hn := norm_nonneg z
    have h2 : 1 + Real.sqrt (z ⬝ᵥ z) ≤ (1 + Real.sqrt d) * (1 + ‖z‖) := by nlinarith
    calc Φ z = (1 + Real.sqrt (z ⬝ᵥ z)) ^ 4 := rfl
      _ ≤ ((1 + Real.sqrt d) * (1 + ‖z‖)) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
      _ = _ := by ring
  have hdom := fun {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (K : ℝ) (i j : ℕ) (hi : i ≤ 4)
      (hfb : ∀ ω, |f ω| ≤ K * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) =>
    integrable_of_dom4 hξ he hlaw hei hf K i j hi hfb
  have iF : Integrable F μ := hdom mF.aestronglyMeasurable ((1 + Real.sqrt d) ^ 4) 0 4 (by norm_num) fun ω => by
    rw [abs_of_nonneg (hF0 ω), pow_zero, mul_one]; exact hΦb (ξ ω)
  have iG : Integrable G μ := hdom mG.aestronglyMeasurable 1 4 0 le_rfl fun ω => by
    rw [abs_of_nonneg (hG0 ω), pow_zero, one_mul, one_mul]
  have iFG : Integrable (F * G) μ := hdom (mF.mul mG).aestronglyMeasurable ((1 + Real.sqrt d) ^ 4) 4 4 le_rfl
    fun ω => by
      rw [Pi.mul_apply, abs_of_nonneg (mul_nonneg (hF0 ω) (hG0 ω))]
      have := hΦb (ξ ω)
      calc F ω * G ω ≤ (1 + Real.sqrt d) ^ 4 * (1 + ‖ξ ω‖) ^ 4 * G ω := mul_le_mul_of_nonneg_right this (hG0 ω)
        _ = _ := by rw [hG]; ring
  have hY4b : ∀ ω, Y ω ^ 4 ≤ C ^ 4 * (F * G) ω := by
    intro ω
    have h := hYb ω
    have h0 : 0 ≤ C * (1 + Real.sqrt (ξ ω ⬝ᵥ ξ ω)) * (1 + |e ω|) := le_trans (abs_nonneg _) h
    calc Y ω ^ 4 = |Y ω| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      _ ≤ (C * (1 + Real.sqrt (ξ ω ⬝ᵥ ξ ω)) * (1 + |e ω|)) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h 4
      _ = C ^ 4 * (F * G) ω := by simp only [Pi.mul_apply, hF, hG, hΦ]; ring
  have iY4 : Integrable (fun ω => Y ω ^ 4) μ :=
    (iFG.const_mul (C ^ 4)).mono' (hY.pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hY4b ω)
  -- (a) the domination
  have ha := condExp_mono (m := 𝒢) iY4 (iFG.smul (C ^ 4)) (Filter.Eventually.of_forall fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact hY4b ω)
  have has := condExp_smul (μ := μ) (C ^ 4) (F * G) 𝒢
  -- (b) the tower
  have hb := condExp_condExp_of_le (μ := μ) (f := F * G)
    (le_sup_left : 𝒢 ≤ 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) h𝒢'
  -- (c) the pull-out of `F`
  have hFm : StronglyMeasurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] F := by
    have h1 : Measurable[MeasurableSpace.comap ξ inferInstance] ξ := Measurable.of_comap_le le_rfl
    have h2 : Measurable[𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] F :=
      (mΦ.comp h1).mono
        (le_sup_right : MeasurableSpace.comap ξ inferInstance ≤ 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) le_rfl
    exact h2.stronglyMeasurable
  have hc := condExp_mul_of_stronglyMeasurable_left
    (m := 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) (μ := μ) hFm iFG iG
  -- (d) the noise
  have hGle : G ≤ᵐ[μ] (24 : ℝ) • fun ω => Real.exp (e ω ^ 2) := Filter.Eventually.of_forall fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul, hG]; exact one_add_abs_pow_four_le (e ω)
  have hd1 := condExp_mono (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) iG (hei.smul (24 : ℝ)) hGle
  have hd2 := condExp_smul (μ := μ) (24 : ℝ) (fun ω => Real.exp (e ω ^ 2)) (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
  have hGc : μ[G | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ≤ᵐ[μ] fun _ => 48 := by
    filter_upwards [hd1, hd2, hee] with ω h1 h2 h3
    rw [h2, Pi.smul_apply, smul_eq_mul] at h1
    linarith
  -- (e), (f)
  have hf1 : μ[F * G | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ≤ᵐ[μ] (48 : ℝ) • F := by
    filter_upwards [hc, hGc] with ω h1 h2
    rw [h1, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have := hF0 ω
    nlinarith
  have hf2 := condExp_mono (m := 𝒢)
    (integrable_condExp (m := 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) (μ := μ) (f := F * G)) (iF.smul (48 : ℝ)) hf1
  have hf3 := condExp_smul (μ := μ) (48 : ℝ) F 𝒢
  -- (g) the freezing of `F`
  have hFR : μ[F | 𝒢] =ᵐ[μ] fun _ => ∫ z, Φ z ∂(gam d) := by
    have h := lemmaFR Ω Unit (Fin d → ℝ) 𝒢 μ (fun _ => ()) ξ (fun x => Φ x.2) h𝒢 measurable_const hξ hind
      (mΦ.comp measurable_snd) iF
    rw [hlaw] at h
    exact h
  have hΦint : ∫ z, Φ z ∂(gam d) ≤ 32 * (d : ℝ) ^ 2 := int_one_add_sqrt_pow_four hd
  have hC4 : 0 ≤ C ^ 4 := pow_nonneg hC 4
  filter_upwards [ha, has, hb, hf2, hf3, hFR] with ω ha has hb hf2 hf3 hFR
  rw [has, Pi.smul_apply, smul_eq_mul, ← hb] at ha
  rw [hf3, Pi.smul_apply, smul_eq_mul, hFR] at hf2
  calc μ[fun ω => Y ω ^ 4 | 𝒢] ω ≤ C ^ 4 * μ[μ[F * G | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] | 𝒢] ω := ha
    _ ≤ C ^ 4 * (48 * (32 * (d : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hf2.trans ?_) hC4
        linarith
    _ = 1536 * C ^ 4 * (d : ℝ) ^ 2 := by ring

/-- **Lemma SK' (iv)**: the bias of the weight and the clip in one round. -/
theorem bias_round (hd : 1 ≤ d) (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (hσ : Measurable[𝒢] σ) (hξ : Measurable ξ) (he : Measurable e)
    (hlaw : μ.map ξ = gam d) (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (E P D : S × (Fin d → ℝ) → ℝ) (hE : Measurable E) (hP : Measurable P) (hD : Measurable D)
    (K : ℝ) (k : ℕ) (hK : 0 ≤ K) (hEK : ∀ x, |E x| ≤ K * (1 + ‖x.2‖) ^ k)
    (hPK : ∀ x, |P x| ≤ K * (1 + ‖x.2‖) ^ k) (hDK : ∀ x, |D x| ≤ K * (1 + ‖x.2‖) ^ k)
    (C : ℝ) (hC : 0 ≤ C) (hYb : ∀ x y, |E x + P x * y| ≤ C * (1 + Real.sqrt (x.2 ⬝ᵥ x.2)) * (1 + |y|))
    (b0 y0 t0 c1 c2 : ℝ) (hy0 : 0 ≤ y0) (ht0 : 0 ≤ t0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (h1 : gam d {z | b0 < z ⬝ᵥ z} ≤ ENNReal.ofReal c1) (h2 : ∀ s, gam d {z | 10 < P (s, z)} ≤ ENNReal.ofReal c2)
    (hoff : ∀ x y, x.2 ⬝ᵥ x.2 ≤ b0 → P x ≤ 10 → |y| ≤ t0 → |E x + P x * y| ≤ y0) :
    ∀ᵐ ω ∂μ, |μ[fun ω => obsW b0 y0 (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω -
        ∫ z, E (σ ω, z) * D (σ ω, z) ∂(gam d)| ≤
      2 * (1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) * (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ) *
        (c1 + c2 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ) := by
  have hσ0 : Measurable σ := hσ.mono h𝒢 le_rfl
  have hp : Measurable fun ω => (σ ω, ξ ω) := hσ0.prodMk hξ
  have hB := measurableSet_bset hσ0 hξ he hP b0 t0
  have hoff' : ∀ ω ∉ bset σ ξ e P b0 t0, obsW b0 y0 (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) =
      E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω := by
    intro ω hω
    simp only [bset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hω
    obtain ⟨⟨k1, k2⟩, k3⟩ := hω
    exact (obsW_sure hy0 b0 (ξ ω) _).2.2.2 k1 (hoff (σ ω, ξ ω) (e ω) k1 k2 k3)
  have hW := cond_bias_w 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee E P D hE hP hD K k hK hEK hPK hDK
    (obsW b0 y0) (measurable_obsW_uncurry b0 y0) (fun x y => (obsW_sure hy0 b0 x y).2.1)
    (bset σ ξ e P b0 t0) hB hoff'
  have hA := cond_bset 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hee P hP b0 t0 c1 c2 ht0 hc1 hc2 h1 h2
  have hYm : Measurable fun ω => E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω := (hE.comp hp).add ((hP.comp hp).mul he)
  have hY := cond_pow_four hd 𝒢 μ h𝒢 ξ e hξ he hlaw hind hei hee _ hYm C hC
    (fun ω => hYb (σ ω, ξ ω) (e ω))
  have hY0 := condExp_nonneg (m := 𝒢) (μ := μ) (f := fun ω => (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) ^ 4)
    (Filter.Eventually.of_forall fun ω => by positivity)
  have hI0 := condExp_nonneg (m := 𝒢) (μ := μ) (f := (bset σ ξ e P b0 t0).indicator (1 : Ω → ℝ))
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hc0 : 0 ≤ c1 + c2 + 2 * Real.exp (-t0 ^ 2) := by
    have := Real.exp_pos (-t0 ^ 2)
    linarith
  have a4 : 0 ≤ (1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  filter_upwards [hW, hA, hY, hY0, hI0] with ω hW hA hY hY0 hI0
  refine hW.trans ?_
  set D4 := (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ) with hD4def
  have hD4 : 0 ≤ D4 := Real.rpow_nonneg (integral_nonneg fun z => by positivity) _
  have a1 := Real.rpow_le_rpow hY0 hY (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have a2 := Real.rpow_le_rpow hI0 hA (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have a3 := Real.rpow_nonneg hI0 (1 / 2 : ℝ)
  calc 2 * (μ[fun ω => (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) * D4 *
        (μ[(bset σ ξ e P b0 t0).indicator 1 | 𝒢] ω) ^ (1 / 2 : ℝ)
      = (2 * D4) * ((μ[fun ω => (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) *
        (μ[(bset σ ξ e P b0 t0).indicator 1 | 𝒢] ω) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ (2 * D4) * ((1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) *
        (c1 + c2 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 a3 a4) (by linarith)
    _ = _ := by ring

end Round

end AdversarialBco.UW.SKp
