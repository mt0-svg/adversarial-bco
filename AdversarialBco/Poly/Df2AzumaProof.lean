/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Poly.Df2Azuma

@[expose] public section

/-!
# DF2, the event Azuma: proofs

Proves the four statements of `Df2Azuma.lean`: `azumaHoeffding : AzumaHoeffding`,
`azumaHoeffdingAbs : AzumaHoeffdingAbs`, `azumaMartingale : AzumaMartingale` (the source's thm:azuma) and
`df2AzumaEvent : Df2AzumaEvent` (the event Azuma of DF2 at the level `δ/7`), on any probability space.

Route. Mathlib's Azuma-Hoeffding (`measure_sum_ge_le_of_hasCondSubgaussianMGF`) needs a standard Borel space and the
conditional sub-Gaussian property through the conditional expectation kernel; the statements here take any `Ω`, so the
proof goes through `condExp` directly:
* `hoeffding_core`: Hoeffding's lemma in deterministic form, from Mathlib's Hoeffding lemma
  (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) on the two-point law with mean `m`;
* `condExp_exp_sub_le`: the conditional Hoeffding lemma `E[exp (s (Z - E[Z | m])) | m] ≤ exp (s² (b - a)²/8)`, by the
  chord bound under `condExp` and the pull-out of `exp (-s E[Z | m])`;
* `integral_exp_azS_succ_le`, `integral_exp_azS_le`: the tower step and its induction for
  `S_n = Σ_{t<n} (Z_t - E[Z_t | ℱ_t])`; `hasSubgaussianMGF_azS`, then Mathlib's Chernoff bound
  (`HasSubgaussianMGF.measure_ge_le`) in `azuma_tail`;
* the two-sided form by `-Z`, the martingale form with the increments `M_{t+1} - M_t`, the event of DF2 with `[0, 1]`.
-/
open MeasureTheory ProbabilityTheory

universe u

/-- The chord bound: on `[a, b]`, `exp (s ·)` lies below its chord. -/
theorem AdversarialBco.Poly.Azuma.exp_mul_le_chord (s a b z : ℝ) (ha : a ≤ z) (hb : z ≤ b) :
    (b - a) * Real.exp (s * z) ≤ (b - z) * Real.exp (s * a) + (z - a) * Real.exp (s * b) := by
  by_cases h_eq : a = b
  · rw [h_eq] at ha ⊢
    have hz : z = b := by linarith
    rw [hz]
    simp
  · have h_lt : a < b := by
      by_contra! hle
      apply h_eq
      linarith
    have h_denom_pos : 0 < b - a := by linarith
    have h_denom_ne_zero : b - a ≠ 0 := by linarith
    set θ := (b - z) / (b - a) with hθ
    set φ := (z - a) / (b - a) with hφ
    have hθ_nonneg : 0 ≤ θ := by
      rw [hθ]
      refine div_nonneg (by linarith) (by linarith)
    have hφ_nonneg : 0 ≤ φ := by
      rw [hφ]
      refine div_nonneg (by linarith) (by linarith)
    have h_sum : θ + φ = 1 := by
      rw [hθ, hφ]
      field_simp [h_denom_ne_zero]
      ring
    have h_key : θ * (s * a) + φ * (s * b) = s * z := by
      rw [hθ, hφ]
      field_simp [h_denom_ne_zero]
      ring
    have h_conv := convexOn_exp.2 (x := s * a) (y := s * b) (Set.mem_univ _) (Set.mem_univ _) hθ_nonneg hφ_nonneg h_sum
    have h_expanded : Real.exp (s * z) ≤ θ * Real.exp (s * a) + φ * Real.exp (s * b) := by
      simpa [smul_eq_mul, h_key] using h_conv
    have h_mul : (b - a) * Real.exp (s * z) ≤ (b - a) * (θ * Real.exp (s * a) + φ * Real.exp (s * b)) := by
      apply mul_le_mul_of_nonneg_left h_expanded
      linarith
    calc
      (b - a) * Real.exp (s * z) ≤ (b - a) * (θ * Real.exp (s * a) + φ * Real.exp (s * b)) := h_mul
      _ = (b - z) * Real.exp (s * a) + (z - a) * Real.exp (s * b) := by
        rw [hθ, hφ]
        field_simp [h_denom_ne_zero]

/-- Hoeffding's lemma, deterministic form: `(b - m) e^{sa} + (m - a) e^{sb} ≤ (b - a) exp (s m + s² (b - a)²/8)` for
`a ≤ m ≤ b`. -/
theorem AdversarialBco.Poly.Azuma.hoeffding_core (s a b m : ℝ) (ha : a ≤ m) (hb : m ≤ b) :
    (b - m) * Real.exp (s * a) + (m - a) * Real.exp (s * b) ≤
      (b - a) * Real.exp (s * m + s ^ 2 * (b - a) ^ 2 / 8) := by
  rcases (ha.trans hb).lt_or_eq with hab | hab
  · have hba : 0 < b - a := sub_pos.2 hab
    set p := (m - a) / (b - a) with hp
    have hp0 : 0 ≤ p := div_nonneg (sub_nonneg.2 ha) hba.le
    have hp1 : p ≤ 1 := (div_le_one hba).2 (by linarith)
    have hpb : (b - a) * p = m - a := by rw [hp]; field_simp
    set ν : Measure ℝ := ENNReal.ofReal (1 - p) • Measure.dirac a + ENNReal.ofReal p • Measure.dirac b
      with hν
    have : IsProbabilityMeasure ν := by
      constructor
      simp only [hν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) hp0]
      simp
    -- integrals under the two-point law
    have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂ν = (1 - p) * f a + p * f b := by
      intro f
      have hfi : ∀ c : ℝ, Integrable f (Measure.dirac c) := fun c => integrable_dirac (by simp)
      rw [hν, integral_add_measure ((hfi a).smul_measure (by simp)) ((hfi b).smul_measure (by simp)),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0, smul_eq_mul, smul_eq_mul]
    -- Hoeffding's lemma for `x ↦ x - m` under `ν`
    have hX : ∀ᵐ x ∂ν, x - m ∈ Set.Icc (a - m) (b - m) := by
      rw [hν, ae_add_measure_iff]
      constructor
      · refine Measure.ae_smul_measure ?_ _
        rw [ae_dirac_eq]
        exact Filter.eventually_pure.2 ⟨le_refl _, by linarith⟩
      · refine Measure.ae_smul_measure ?_ _
        rw [ae_dirac_eq]
        exact Filter.eventually_pure.2 ⟨by linarith, le_refl _⟩
    have hmean : ∫ x, (x - m) ∂ν = 0 := by
      rw [hint (fun x => x - m)]
      have : (1 - p) * (a - m) + p * (b - m) = a - m + (b - a) * p := by ring
      rw [this, hpb]
      ring
    have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := ν) (X := fun x => x - m)
      (measurable_id.sub_const m).aemeasurable hX hmean
    have hmgf := hsub.mgf_le s
    have hc : ((‖(b - m) - (a - m)‖₊ / 2) ^ 2 : NNReal) = ((b - a) ^ 2 / 4 : ℝ) := by
      push_cast
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      ring
    rw [mgf, hint (fun x => Real.exp (s * (x - m))), hc] at hmgf
    have hkey : (b - m) * Real.exp (s * a) + (m - a) * Real.exp (s * b) =
        (b - a) * Real.exp (s * m) *
          ((1 - p) * Real.exp (s * (a - m)) + p * Real.exp (s * (b - m))) := by
      have e1 : Real.exp (s * m) * Real.exp (s * (a - m)) = Real.exp (s * a) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (s * m) * Real.exp (s * (b - m)) = Real.exp (s * b) := by
        rw [← Real.exp_add]; ring_nf
      have hq : (b - a) * (1 - p) = b - m := by linear_combination -hpb
      calc (b - m) * Real.exp (s * a) + (m - a) * Real.exp (s * b)
          = (b - a) * (1 - p) * (Real.exp (s * m) * Real.exp (s * (a - m))) +
              (b - a) * p * (Real.exp (s * m) * Real.exp (s * (b - m))) := by rw [e1, e2, hq, hpb]
        _ = _ := by ring
    rw [hkey, Real.exp_add, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left (hmgf.trans_eq ?_) (mul_nonneg hba.le (Real.exp_pos _).le)
    congr 1
    ring
  · subst hab
    have : m = a := le_antisymm hb ha
    subst this
    simp

/-- The arithmetic of the event Azuma: `exp (-2 ε²/n) = (δ/7)^4 ≤ δ/7` at `ε = (2 n log(7/δ))^{1/2}`. -/
theorem AdversarialBco.Poly.Azuma.azuma_event_arith (n : ℕ) (δ : ℝ) (hn : 0 < n) (hδ : 0 < δ) (hδ7 : δ ≤ 7) :
    Real.exp (-2 * Real.sqrt (2 * n * Real.log (7 / δ)) ^ 2 / n) ≤ δ / 7 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h7pos : 0 < (7 : ℝ) := by norm_num
  have h_div_pos : 0 < 7 / δ := div_pos h7pos hδ
  have hone : 1 ≤ 7 / δ := (one_le_div hδ).mpr hδ7
  have hlog_nonneg : 0 ≤ Real.log (7 / δ) := Real.log_nonneg hone
  have h_inner_nonneg : 0 ≤ 2 * (n : ℝ) * Real.log (7 / δ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_sqrt_sq : Real.sqrt (2 * (n : ℝ) * Real.log (7 / δ)) ^ 2 = 2 * (n : ℝ) * Real.log (7 / δ) :=
    Real.sq_sqrt h_inner_nonneg
  have h_exp_arg : -2 * Real.sqrt (2 * (n : ℝ) * Real.log (7 / δ)) ^ 2 / (n : ℝ) = -4 * Real.log (7 / δ) := by
    rw [h_sqrt_sq]
    field_simp [hn'.ne.symm]
    ring_nf
  rw [h_exp_arg]
  have h_exp_neg_log : Real.exp (-Real.log (7 / δ)) = δ / 7 := by
    rw [Real.exp_neg, Real.exp_log h_div_pos, inv_div]
  calc
    Real.exp (-4 * Real.log (7 / δ)) = Real.exp ((4 : ℝ) * (-Real.log (7 / δ))) := by
      congr 1
      ring
    _ = (Real.exp (-Real.log (7 / δ))) ^ (4 : ℕ) := by
      simpa using Real.exp_nat_mul (-Real.log (7 / δ)) 4
    _ = (δ / 7) ^ (4 : ℕ) := by rw [h_exp_neg_log]
    _ ≤ δ / 7 := by
      have hxpos : 0 ≤ δ / 7 := by positivity
      have hxle1 : δ / 7 ≤ 1 := by
        linarith
      have h_pow : (δ / 7) ^ (4 : ℕ) ≤ (δ / 7) ^ (1 : ℕ) :=
        pow_le_pow_of_le_one hxpos hxle1 (by omega)
      simpa [pow_one] using h_pow

/-- The arithmetic of the martingale form: `exp (-2 ε²/(4 C)) = δ` at `ε = (2 C log(1/δ))^{1/2}`. -/
theorem AdversarialBco.Poly.Azuma.azuma_mart_arith (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (-2 * Real.sqrt (2 * C * Real.log (1 / δ)) ^ 2 / (4 * C)) ≤ δ := by
  have hδinv_ge_one : 1 ≤ 1 / δ :=
    one_le_one_div hδ hδ1
  have hL_nonneg : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg hδinv_ge_one
  have h_sq_sqrt : Real.sqrt (2 * C * Real.log (1 / δ)) ^ 2 = 2 * C * Real.log (1 / δ) := by
    apply Real.sq_sqrt
    nlinarith
  have h_log_eq : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hδ.ne.symm, Real.log_one]
    simp
  have h_eq : Real.exp (-2 * Real.sqrt (2 * C * Real.log (1 / δ)) ^ 2 / (4 * C)) = δ := by
    calc
      Real.exp (-2 * Real.sqrt (2 * C * Real.log (1 / δ)) ^ 2 / (4 * C))
          = Real.exp (-2 * (2 * C * Real.log (1 / δ)) / (4 * C)) := by rw [h_sq_sqrt]
      _ = Real.exp (-Real.log (1 / δ)) := by
        field_simp [hC.ne.symm]
        ring_nf
      _ = Real.exp (-(-Real.log δ)) := by rw [h_log_eq]
      _ = Real.exp (Real.log δ) := by rw [neg_neg]
      _ = δ := Real.exp_log hδ
  rw [h_eq]

/-- The conditional expectation of a variable with values in `[a, b]` a.e. has values in `[a, b]` a.e. -/
theorem AdversarialBco.Poly.Azuma.condExp_mem_Icc {Ω : Type*} {m m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ m0) (Z : Ω → ℝ) (a b : ℝ)
    (hZm : AEMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc a b) :
    ∀ᵐ ω ∂μ, μ[Z | m] ω ∈ Set.Icc a b := by
  have hZ_int : Integrable Z μ := Integrable.of_mem_Icc a b hZm hZ
  have ha_int : Integrable (fun _ => a) μ := integrable_const a
  have hb_int : Integrable (fun _ => b) μ := integrable_const b
  have ha_le_Z : (fun _ => a) ≤ᵐ[μ] Z := by
    filter_upwards [hZ] with ω hω
    exact (Set.mem_Icc.mp hω).1
  have hZ_le_b : Z ≤ᵐ[μ] (fun _ => b) := by
    filter_upwards [hZ] with ω hω
    exact (Set.mem_Icc.mp hω).2
  have h_cond_le : μ[fun _ => a | m] ≤ᵐ[μ] μ[Z | m] :=
    condExp_mono ha_int hZ_int ha_le_Z
  have h_cond_le' : μ[Z | m] ≤ᵐ[μ] μ[fun _ => b | m] :=
    condExp_mono hZ_int hb_int hZ_le_b
  have h_cond_const_a : μ[fun _ => a | m] =ᵐ[μ] (fun _ => a) := by
    rw [condExp_const hm a]
  have h_cond_const_b : μ[fun _ => b | m] =ᵐ[μ] (fun _ => b) := by
    rw [condExp_const hm b]
  filter_upwards [h_cond_le, h_cond_le', h_cond_const_a, h_cond_const_b] with ω h1 h2 h3 h4
  exact Set.mem_Icc.mpr ⟨h3 ▸ h1, h4 ▸ h2⟩

/-- The conditional Hoeffding lemma: `E[exp (s (Z - E[Z | m])) | m] ≤ exp (s² (b - a)²/8)` a.e. for `Z ∈ [a, b]` a.e. -/
theorem AdversarialBco.Poly.Azuma.condExp_exp_sub_le {Ω : Type*} {m m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ m0) (Z : Ω → ℝ) (a b : ℝ)
    (hZm : StronglyMeasurable Z) (hZ : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc a b) (s : ℝ) :
    μ[fun ω => Real.exp (s * (Z ω - μ[Z | m] ω)) | m] ≤ᵐ[μ] fun _ => Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  set E := μ[Z | m] with hE_def
  have hZa : AEMeasurable Z μ := hZm.measurable.aemeasurable
  have hZi : Integrable Z μ := Integrable.of_mem_Icc a b hZa hZ
  have hEI : ∀ᵐ ω ∂μ, E ω ∈ Set.Icc a b := condExp_mem_Icc μ hm Z a b hZa hZ
  have hEsm : StronglyMeasurable[m] E := stronglyMeasurable_condExp
  have hEa : AEMeasurable E μ := (hEsm.mono hm).measurable.aemeasurable
  set c := s ^ 2 * (b - a) ^ 2 / 8 with hc
  have hab : a ≤ b := by
    obtain ⟨ω, hω⟩ := hZ.exists
    exact hω.1.trans hω.2
  rcases hab.lt_or_eq with hab | hab
  · -- the main case `a < b`
    have hf : Integrable (fun ω => Real.exp (s * Z ω)) μ := integrable_exp_mul_of_mem_Icc hZa hZ
    have hg : StronglyMeasurable[m] (fun ω => Real.exp (-s * E ω)) :=
      Real.continuous_exp.comp_stronglyMeasurable (hEsm.const_mul (-s))
    have hZE : ∀ᵐ ω ∂μ, Z ω - E ω ∈ Set.Icc (a - b) (b - a) := by
      filter_upwards [hZ, hEI] with ω h1 h2
      exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    have hfg : Integrable ((fun ω => Real.exp (s * Z ω)) * fun ω => Real.exp (-s * E ω)) μ := by
      have := integrable_exp_mul_of_mem_Icc (t := s) (hZa.sub hEa) hZE
      refine this.congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.mul_apply, Pi.sub_apply, ← Real.exp_add]
      ring_nf
    -- pull-out
    have hpull : μ[fun ω => Real.exp (s * (Z ω - E ω)) | m] =ᵐ[μ]
        μ[fun ω => Real.exp (s * Z ω) | m] * fun ω => Real.exp (-s * E ω) := by
      have heq : (fun ω => Real.exp (s * (Z ω - E ω))) =
          (fun ω => Real.exp (s * Z ω)) * fun ω => Real.exp (-s * E ω) := by
        funext ω
        simp only [Pi.mul_apply, ← Real.exp_add]
        ring_nf
      rw [heq]
      exact condExp_mul_of_stronglyMeasurable_right hg hfg hf
    -- the chord bound under the conditional expectation
    set k0 := b * Real.exp (s * a) - a * Real.exp (s * b) with hk0
    set k1 := Real.exp (s * b) - Real.exp (s * a) with hk1
    have hchord : (fun ω => (b - a) * Real.exp (s * Z ω)) ≤ᵐ[μ] fun ω => k0 + k1 * Z ω := by
      filter_upwards [hZ] with ω hω
      have := AdversarialBco.Poly.Azuma.exp_mul_le_chord s a b (Z ω) hω.1 hω.2
      simp only [hk0, hk1]
      linarith
    have hL : μ[fun ω => (b - a) * Real.exp (s * Z ω) | m] =ᵐ[μ]
        fun ω => (b - a) * μ[fun ω => Real.exp (s * Z ω) | m] ω := by
      have := condExp_smul (μ := μ) (b - a) (fun ω => Real.exp (s * Z ω)) m
      exact this
    have hR : μ[fun ω => k0 + k1 * Z ω | m] =ᵐ[μ] fun ω => k0 + k1 * E ω := by
      have h1 := condExp_add (integrable_const k0) (hZi.const_mul k1) m (μ := μ)
      have h2 := condExp_smul (μ := μ) k1 Z m
      rw [condExp_const hm k0] at h1
      filter_upwards [h1, h2] with ω h1 h2
      have h2' : μ[fun ω => k1 * Z ω | m] ω = k1 * E ω := by
        exact h2
      simp only [Pi.add_apply] at h1
      rw [show (fun ω => k0 + k1 * Z ω) = (fun _ => k0) + fun ω => k1 * Z ω from rfl, h1, h2']
    have hmono : μ[fun ω => (b - a) * Real.exp (s * Z ω) | m] ≤ᵐ[μ] μ[fun ω => k0 + k1 * Z ω | m] :=
      condExp_mono (hf.const_mul (b - a)) ((integrable_const k0).add (hZi.const_mul k1)) hchord
    have hcond : ∀ᵐ ω ∂μ, μ[fun ω => Real.exp (s * Z ω) | m] ω ≤ Real.exp (s * E ω + c) := by
      filter_upwards [hmono, hL, hR, hEI] with ω h1 h2 h3 h4
      rw [h2, h3] at h1
      have hcore := AdversarialBco.Poly.Azuma.hoeffding_core s a b (E ω) h4.1 h4.2
      have : (b - a) * μ[fun ω => Real.exp (s * Z ω) | m] ω ≤ (b - a) * Real.exp (s * E ω + c) := by
        refine h1.trans (le_of_eq_of_le ?_ hcore)
        simp only [hk0, hk1]
        ring
      exact le_of_mul_le_mul_left this (by linarith)
    filter_upwards [hpull, hcond] with ω h1 h2
    rw [h1, Pi.mul_apply]
    calc μ[fun ω => Real.exp (s * Z ω) | m] ω * Real.exp (-s * E ω)
        ≤ Real.exp (s * E ω + c) * Real.exp (-s * E ω) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp c := by rw [← Real.exp_add]; ring_nf
  · -- the degenerate case `a = b`: `Z - E = 0` a.e.
    subst hab
    have hZE : (fun ω => Real.exp (s * (Z ω - E ω))) =ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [hZ, hEI] with ω h1 h2
      have : Z ω = E ω := by linarith [h1.1, h1.2, h2.1, h2.2]
      simp [this]
    filter_upwards [condExp_congr_ae (m := m) hZE] with ω h
    rw [h, condExp_const hm]
    simp [hc]

/-- `S_n = Σ_{t<n} (Z_t - E[Z_t | ℱ_t])`. -/
noncomputable def AdversarialBco.Poly.Azuma.azS {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)

/-- `S_n` is `ℱ n`-measurable. -/
theorem AdversarialBco.Poly.Azuma.azS_stronglyMeasurable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (AdversarialBco.Poly.Azuma.azS μ ℱ Z n) := by
  unfold AdversarialBco.Poly.Azuma.azS
  refine Finset.stronglyMeasurable_fun_sum (Finset.range n) (M := ℝ) ?_
  intro t ht
  have ht_n : t < n := Finset.mem_range.1 ht
  have h_le_tn : ℱ t ≤ ℱ n := ℱ.mono (Nat.le_of_lt ht_n)
  have h_le_t1n : ℱ (t + 1) ≤ ℱ n := ℱ.mono (Nat.succ_le_of_lt ht_n)
  have hZt : StronglyMeasurable[ℱ n] (Z t) :=
    (hZm t).mono h_le_t1n
  have h_cond : StronglyMeasurable[ℱ n] (μ[Z t | ℱ t]) :=
    (stronglyMeasurable_condExp (m := ℱ t)).mono h_le_tn
  exact hZt.sub h_cond

/-- `|S_n| ≤ Σ_{t<n} (b_t - a_t)` a.e. -/
theorem AdversarialBco.Poly.Azuma.azS_abs_le {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ) :
    ∀ᵐ ω ∂μ, |AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω| ≤ ∑ t ∈ Finset.range n, (b t - a t) := by
  unfold azS
  have h_bound : ∀ t, ∀ᵐ ω ∂μ, |Z t ω - μ[Z t | ℱ t] ω| ≤ b t - a t := by
    intro t
    have h_cond_ae := condExp_mem_Icc μ (ℱ.le t) (Z t) (a t) (b t)
      (((hZm t).mono (ℱ.le (t + 1))).aemeasurable) (hZ t)
    have h_both : ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t) ∧ μ[Z t | ℱ t] ω ∈ Set.Icc (a t) (b t) :=
      (hZ t).and h_cond_ae
    filter_upwards [h_both] with ω ⟨⟨hZl, hZr⟩, ⟨hCl, hCr⟩⟩
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  have h_all : ∀ᵐ ω ∂μ, ∀ t, |Z t ω - μ[Z t | ℱ t] ω| ≤ b t - a t := by
    rw [ae_all_iff]
    exact h_bound
  filter_upwards [h_all] with ω h
  calc
    |∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)| ≤ ∑ t ∈ Finset.range n, |Z t ω - μ[Z t | ℱ t] ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range n, (b t - a t) :=
      Finset.sum_le_sum fun t ht => h t

/-- `exp (s S_n)` is integrable. -/
theorem AdversarialBco.Poly.Azuma.integrable_exp_azS {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ)
    (s : ℝ) :
    Integrable (fun ω => Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω)) μ := by
  set X := AdversarialBco.Poly.Azuma.azS μ ℱ Z n with hX
  have hX_meas_ℱ : StronglyMeasurable[ℱ n] X :=
    AdversarialBco.Poly.Azuma.azS_stronglyMeasurable μ ℱ Z hZm n
  have hX_meas_m0 : StronglyMeasurable[m0] X :=
    hX_meas_ℱ.mono (ℱ.le n)
  have h_exp_meas : StronglyMeasurable[m0] (fun ω => Real.exp (s * X ω)) := by
    have h_cont : Continuous (fun x : ℝ => Real.exp (s * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact h_cont.comp_stronglyMeasurable hX_meas_m0
  have h_ae_meas : AEStronglyMeasurable (fun ω => Real.exp (s * X ω)) μ :=
    h_exp_meas.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ‖Real.exp (s * X ω)‖ ≤ Real.exp (|s| * (∑ t ∈ Finset.range n, (b t - a t))) := by
    filter_upwards [AdversarialBco.Poly.Azuma.azS_abs_le μ ℱ Z a b hZm hZ n] with ω hω
    have h_norm : ‖Real.exp (s * X ω)‖ = Real.exp (s * X ω) := abs_of_pos (Real.exp_pos _)
    rw [h_norm]
    have h_ineq : s * X ω ≤ |s| * (∑ t ∈ Finset.range n, (b t - a t)) := by
      calc
        s * X ω ≤ |s * X ω| := le_abs_self _
        _ = |s| * |X ω| := abs_mul s (X ω)
        _ ≤ |s| * (∑ t ∈ Finset.range n, (b t - a t)) :=
          mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    exact Real.exp_le_exp.mpr h_ineq
  refine MeasureTheory.Integrable.of_bound h_ae_meas (Real.exp (|s| * (∑ t ∈ Finset.range n, (b t - a t)))) h_bound

/-- The tower step: `E exp (s S_{n+1}) ≤ E exp (s S_n) · exp (s² (b_n - a_n)²/8)`. -/
theorem AdversarialBco.Poly.Azuma.integral_exp_azS_succ_le {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ)
    (s : ℝ) :
    ∫ ω, Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z (n + 1) ω) ∂μ ≤
      (∫ ω, Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω) ∂μ) * Real.exp (s ^ 2 * (b n - a n) ^ 2 / 8) := by
  set S := AdversarialBco.Poly.Azuma.azS μ ℱ Z with hS
  set Y : Ω → ℝ := fun ω => Z n ω - μ[Z n | ℱ n] ω with hY
  set c := s ^ 2 * (b n - a n) ^ 2 / 8 with hc
  have hsucc : ∀ ω, S (n + 1) ω = S n ω + Y ω := by
    intro ω
    simp only [hS, hY, AdversarialBco.Poly.Azuma.azS, Finset.sum_range_succ]
  have hexp : (fun ω => Real.exp (s * S (n + 1) ω)) =
      (fun ω => Real.exp (s * S n ω)) * fun ω => Real.exp (s * Y ω) := by
    funext ω
    simp only [Pi.mul_apply, hsucc, ← Real.exp_add]
    ring_nf
  have hSm : StronglyMeasurable[ℱ n] (fun ω => Real.exp (s * S n ω)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      ((AdversarialBco.Poly.Azuma.azS_stronglyMeasurable μ ℱ Z hZm n).const_mul s)
  have hZn : StronglyMeasurable (Z n) := (hZm n).mono (ℱ.le (n + 1))
  have hI1 : Integrable (fun ω => Real.exp (s * S (n + 1) ω)) μ :=
    AdversarialBco.Poly.Azuma.integrable_exp_azS μ ℱ Z a b hZm hZ (n + 1) s
  have hIn : Integrable (fun ω => Real.exp (s * S n ω)) μ :=
    AdversarialBco.Poly.Azuma.integrable_exp_azS μ ℱ Z a b hZm hZ n s
  have hIY : Integrable (fun ω => Real.exp (s * Y ω)) μ := by
    have hE := AdversarialBco.Poly.Azuma.condExp_mem_Icc μ (ℱ.le n) (Z n) (a n) (b n)
      hZn.measurable.aemeasurable (hZ n)
    have hYI : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (a n - b n) (b n - a n) := by
      filter_upwards [hZ n, hE] with ω h1 h2
      exact ⟨by simp only [hY]; linarith [h1.1, h2.2], by simp only [hY]; linarith [h1.2, h2.1]⟩
    exact integrable_exp_mul_of_mem_Icc
      (hZn.measurable.aemeasurable.sub
        ((stronglyMeasurable_condExp (m := ℱ n) (μ := μ) (f := Z n)).mono (ℱ.le n)).measurable.aemeasurable) hYI
  have hpull : μ[fun ω => Real.exp (s * S (n + 1) ω) | ℱ n] =ᵐ[μ]
      (fun ω => Real.exp (s * S n ω)) * μ[fun ω => Real.exp (s * Y ω) | ℱ n] := by
    rw [hexp]
    exact condExp_mul_of_stronglyMeasurable_left hSm (hexp ▸ hI1) hIY
  have hH : μ[fun ω => Real.exp (s * Y ω) | ℱ n] ≤ᵐ[μ] fun _ => Real.exp c :=
    AdversarialBco.Poly.Azuma.condExp_exp_sub_le μ (ℱ.le n) (Z n) (a n) (b n) hZn (hZ n) s
  have hIL : Integrable (fun ω => Real.exp (s * S n ω) * μ[fun ω => Real.exp (s * Y ω) | ℱ n] ω) μ :=
    integrable_condExp.congr hpull
  calc ∫ ω, Real.exp (s * S (n + 1) ω) ∂μ
      = ∫ ω, μ[fun ω => Real.exp (s * S (n + 1) ω) | ℱ n] ω ∂μ := (integral_condExp (ℱ.le n)).symm
    _ = ∫ ω, Real.exp (s * S n ω) * μ[fun ω => Real.exp (s * Y ω) | ℱ n] ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, Real.exp (s * S n ω) * Real.exp c ∂μ := by
        refine integral_mono_ae hIL (hIn.mul_const _) ?_
        filter_upwards [hH] with ω h
        exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = (∫ ω, Real.exp (s * S n ω) ∂μ) * Real.exp c := integral_mul_const _ _

/-- `E exp (s S_n) ≤ exp (s² Σ_{t<n} (b_t - a_t)²/8)`. -/
theorem AdversarialBco.Poly.Azuma.integral_exp_azS_le {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ)
    (s : ℝ) :
    ∫ ω, Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω) ∂μ ≤
      Real.exp (s ^ 2 * (∑ t ∈ Finset.range n, (b t - a t) ^ 2) / 8) := by
  induction' n with n ih
  · -- n = 0
    simp [AdversarialBco.Poly.Azuma.azS, integral_const, probReal_univ]
  · -- n → n+1
    have h := integral_exp_azS_succ_le μ ℱ Z a b hZm hZ n s
    have hpos : 0 ≤ Real.exp (s ^ 2 * (b n - a n) ^ 2 / 8) := by
      positivity
    calc
      ∫ ω, Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z (n + 1) ω) ∂μ ≤
          (∫ ω, Real.exp (s * AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω) ∂μ) * Real.exp (s ^ 2 * (b n - a n) ^ 2 / 8) := h
      _ ≤ Real.exp (s ^ 2 * (∑ t ∈ Finset.range n, (b t - a t) ^ 2) / 8) * Real.exp (s ^ 2 * (b n - a n) ^ 2 / 8) := by
        gcongr
      _ = Real.exp ((s ^ 2 * (∑ t ∈ Finset.range n, (b t - a t) ^ 2) / 8) + (s ^ 2 * (b n - a n) ^ 2 / 8)) := by
        rw [Real.exp_add]
      _ = Real.exp (s ^ 2 * ((∑ t ∈ Finset.range n, (b t - a t) ^ 2) + (b n - a n) ^ 2) / 8) := by
        ring_nf
      _ = Real.exp (s ^ 2 * (∑ t ∈ Finset.range (n + 1), (b t - a t) ^ 2) / 8) := by
        rw [Finset.sum_range_succ]

/-- `S_n` has a sub-Gaussian moment generating function with parameter `Σ_{t<n} (b_t - a_t)²/4`. -/
theorem AdversarialBco.Poly.Azuma.hasSubgaussianMGF_azS {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ) :
    HasSubgaussianMGF (AdversarialBco.Poly.Azuma.azS μ ℱ Z n)
      ((∑ t ∈ Finset.range n, (b t - a t) ^ 2) / 4).toNNReal μ := by
  set C := ∑ t ∈ Finset.range n, (b t - a t) ^ 2 with hC_def
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg (fun t _ => sq_nonneg _)
  have hc_eq : ((C / 4).toNNReal : ℝ) = C / 4 :=
    Real.coe_toNNReal (C / 4) (div_nonneg hC_nonneg (by norm_num))
  refine ⟨fun t => integrable_exp_azS μ ℱ Z a b hZm hZ n t, fun t => ?_⟩
  calc
    mgf (AdversarialBco.Poly.Azuma.azS μ ℱ Z n) μ t
        = ∫ ω, Real.exp (t * AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω) ∂μ := rfl
    _ ≤ Real.exp (t ^ 2 * C / 8) := integral_exp_azS_le μ ℱ Z a b hZm hZ n t
    _ = Real.exp (((C / 4).toNNReal : ℝ) * t ^ 2 / 2) := by
      rw [hc_eq]
      ring_nf

/-- The upper tail `P(S_n ≥ ε) ≤ exp (-2 ε² / Σ_{t<n} (b_t - a_t)²)`. -/
theorem AdversarialBco.Poly.Azuma.azuma_tail {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (a b : ℕ → ℝ)
    (hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (hZ : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (a t) (b t)) (n : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ AdversarialBco.Poly.Azuma.azS μ ℱ Z n ω} ≤
      ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / ∑ t ∈ Finset.range n, (b t - a t) ^ 2)) := by
  have h := (AdversarialBco.Poly.Azuma.hasSubgaussianMGF_azS μ ℱ Z a b hZm hZ n).measure_ge_le hε
  have hC : 0 ≤ (∑ t ∈ Finset.range n, (b t - a t) ^ 2) / 4 := by positivity
  rw [Real.coe_toNNReal _ hC] at h
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans_eq ?_)
  congr 1
  ring

/-- The two-sided form from the upper tail, applied to `Z` and `-Z`. -/
theorem AdversarialBco.Poly.azumaHoeffdingAbs_of (h : AdversarialBco.Poly.AzumaHoeffding.{u}) :
    AdversarialBco.Poly.AzumaHoeffdingAbs.{u} := by
  intro Ω m0 μ _ ℱ Z a b hZm hZ n ε hε
  set S := fun ω => ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) with hS
  set C := ∑ t ∈ Finset.range n, (b t - a t) ^ 2 with hC
  -- apply h to Z, a, b (upper tail)
  have hS_upper : μ {ω | ε ≤ S ω} ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / C)) := by
    have h_apply := h μ ℱ Z a b hZm hZ n ε hε
    simpa [hS, hC] using h_apply
  -- define Z' = -Z
  set Z' := fun t ω => -Z t ω with hZ'
  have hZm' : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z' t) := by
    intro t
    have h_eq : Z' t = -Z t := by
      ext ω; simp [Z']
    simpa [h_eq] using (hZm t).neg
  have hZ' : ∀ t, ∀ᵐ ω ∂μ, Z' t ω ∈ Set.Icc (-b t) (-a t) := by
    intro t
    filter_upwards [hZ t] with ω hω
    rcases hω with ⟨hlo, hhi⟩
    constructor <;> linarith
  have h_cond_exp : ∀ t, μ[Z' t | ℱ t] =ᵐ[μ] -μ[Z t | ℱ t] := by
    intro t
    have h_eq : Z' t = -Z t := by
      ext ω; simp [Z']
    simpa [h_eq] using MeasureTheory.condExp_neg (Z t) (ℱ t)
  -- combine the a.e. equalities using ae_all_iff
  have h_all : ∀ᵐ ω ∂μ, ∀ t, μ[Z' t | ℱ t] ω = -μ[Z t | ℱ t] ω := by
    rw [MeasureTheory.ae_all_iff]
    intro t
    exact h_cond_exp t
  have h_S_eq : (fun ω => ∑ t ∈ Finset.range n, (Z' t ω - μ[Z' t | ℱ t] ω)) =ᵐ[μ]
      (fun ω => -S ω) := by
    filter_upwards [h_all] with ω hω
    calc
      ∑ t ∈ Finset.range n, (Z' t ω - μ[Z' t | ℱ t] ω)
          = ∑ t ∈ Finset.range n, (-Z t ω - μ[Z' t | ℱ t] ω) := by simp [Z']
      _ = ∑ t ∈ Finset.range n, (-Z t ω - (-μ[Z t | ℱ t] ω)) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [hω t]
      _ = ∑ t ∈ Finset.range n, (-(Z t ω - μ[Z t | ℱ t] ω)) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        ring_nf
      _ = -∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) := by
        rw [Finset.sum_neg_distrib]
      _ = -S ω := rfl
  -- apply h to Z', -b, -a (upper tail for -Z)
  have h_S'_upper : μ {ω | ε ≤ -S ω} ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / C)) := by
    have h_apply := h μ ℱ Z' (-b) (-a) hZm' hZ' n ε hε
    have h_sq_eq : ∀ t, ((-a) t - (-b) t) ^ 2 = (b t - a t) ^ 2 := by
      intro t
      have h : (-a) t - (-b) t = b t - a t := by
        simp [sub_eq_add_neg, add_comm]
      rw [h]
    have h_denom : ∑ t ∈ Finset.range n, ((-a) t - (-b) t) ^ 2 = C := by
      calc
        ∑ t ∈ Finset.range n, ((-a) t - (-b) t) ^ 2
            = ∑ t ∈ Finset.range n, (b t - a t) ^ 2 := by
          refine Finset.sum_congr rfl (fun t ht => ?_)
          rw [h_sq_eq t]
        _ = C := by rw [hC]
    have h_set_eq : {ω | ε ≤ ∑ t ∈ Finset.range n, (Z' t ω - μ[Z' t | ℱ t] ω)} =ᵐ[μ]
        {ω | ε ≤ -S ω} := by
      filter_upwards [h_S_eq] with ω hω
      simp [hω]
    have h_measure_eq : μ {ω | ε ≤ ∑ t ∈ Finset.range n, (Z' t ω - μ[Z' t | ℱ t] ω)} =
        μ {ω | ε ≤ -S ω} := by
      rw [MeasureTheory.measure_congr h_set_eq]
    rw [h_measure_eq, h_denom] at h_apply
    exact h_apply
  -- combine: {ε ≤ |S|} = {ε ≤ S} ∪ {ε ≤ -S}
  have h_union : {ω | ε ≤ |S ω|} = {ω | ε ≤ S ω} ∪ {ω | ε ≤ -S ω} := by
    ext ω; simp [le_abs, Set.mem_union]
  rw [h_union]
  calc
    μ ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -S ω}) ≤ μ {ω | ε ≤ S ω} + μ {ω | ε ≤ -S ω} :=
      MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / C)) + ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / C)) :=
      add_le_add hS_upper h_S'_upper
    _ = ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / C) + Real.exp (-2 * ε ^ 2 / C)) := by
      rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    _ = ENNReal.ofReal (2 * Real.exp (-2 * ε ^ 2 / C)) := by ring_nf

/-- The source's thm:azuma from the upper tail, applied to the increments `M_{t+1} - M_t`. -/
theorem AdversarialBco.Poly.azumaMartingale_of (h : AdversarialBco.Poly.AzumaHoeffding.{u}) :
    AdversarialBco.Poly.AzumaMartingale.{u} := by
  intro Ω m0 μ _ ℱ M c hM hc n δ hδ
  set C := ∑ t ∈ Finset.range n, c t ^ 2 with hCdef
  set ε := Real.sqrt (2 * C * Real.log (1 / δ)) with hε
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  set Z : ℕ → Ω → ℝ := fun t ω => M (t + 1) ω - M t ω with hZ
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := fun t =>
    (hM.1 (t + 1)).sub ((hM.1 t).mono (ℱ.mono (Nat.le_succ t)))
  have hZI : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (-c t) (c t) := fun t => by
    filter_upwards [hc t] with ω hω
    exact abs_le.1 hω
  have hcond : ∀ t, μ[Z t | ℱ t] =ᵐ[μ] 0 := by
    intro t
    have h1 := condExp_sub (hM.integrable (t + 1)) (hM.integrable t) (ℱ t) (μ := μ)
    have h2 := hM.2 t (t + 1) (Nat.le_succ t)
    have h3 : μ[M t | ℱ t] = M t := condExp_of_stronglyMeasurable (ℱ.le t) (hM.1 t) (hM.integrable t)
    filter_upwards [h1, h2] with ω h1 h2
    change μ[M (t + 1) - M t | ℱ t] ω = 0
    rw [h1, Pi.sub_apply, h2, h3, sub_self]
  have hsum : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) = M n ω - M 0 ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ t, μ[Z t | ℱ t] ω = 0 := ae_all_iff.2 hcond
    filter_upwards [hall] with ω hω
    calc ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) = ∑ t ∈ Finset.range n, (M (t + 1) ω - M t ω) :=
          Finset.sum_congr rfl fun t _ => by rw [hω t, sub_zero]
      _ = M n ω - M 0 ω := Finset.sum_range_sub (fun t => M t ω) n
  rcases (show 0 ≤ C from Finset.sum_nonneg fun t _ => sq_nonneg (c t)).lt_or_eq with hC | hC
  · have hsub : {ω | M 0 ω + ε < M n ω} ≤ᵐ[μ]
        {ω | ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)} := by
      filter_upwards [hsum] with ω hω hmem
      have hlt : M 0 ω + ε < M n ω := hmem
      show ε ≤ _
      rw [hω]
      linarith
    refine (measure_mono_ae hsub).trans ((h μ ℱ Z (fun t => -c t) c hZm hZI n ε (Real.sqrt_nonneg _)).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have h4 : ∑ t ∈ Finset.range n, (c t - -c t) ^ 2 = 4 * C := by
      rw [hCdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [h4]
    exact AdversarialBco.Poly.Azuma.azuma_mart_arith C δ hC hδ hδ1.le
  · have hc0 : ∀ t ∈ Finset.range n, c t = 0 := by
      intro t ht
      have := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (c t)).1 hC.symm t ht
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have hZ0 : ∀ᵐ ω ∂μ, ∀ t, t < n → Z t ω = 0 := by
      rw [ae_all_iff]
      intro t
      by_cases ht : t < n
      · filter_upwards [hZI t] with ω hω _
        rw [hc0 t (Finset.mem_range.2 ht)] at hω
        exact le_antisymm (by linarith [hω.2]) (by linarith [hω.1])
      · exact ae_of_all _ fun ω h => absurd h ht
    have hMn : ∀ᵐ ω ∂μ, M n ω = M 0 ω := by
      filter_upwards [hZ0] with ω hω
      have h1 := Finset.sum_range_sub (fun t => M t ω) n
      have h0 : ∑ t ∈ Finset.range n, (M (t + 1) ω - M t ω) = 0 :=
        Finset.sum_eq_zero fun t ht => hω t (Finset.mem_range.1 ht)
      linarith
    have hε0 : ε = 0 := by rw [hε, ← hC]; simp
    calc μ {ω | M 0 ω + ε < M n ω} ≤ μ ∅ := by
          refine measure_mono_ae ?_
          filter_upwards [hMn] with ω hω hmem
          have hlt : M 0 ω + ε < M n ω := hmem
          rw [hε0, hω, add_zero] at hlt
          exact (lt_irrefl _ hlt).elim
      _ = 0 := measure_empty
      _ ≤ ENNReal.ofReal δ := zero_le

/-- The event Azuma of DF2 from the upper tail, with `[a_t, b_t] = [0, 1]`. -/
theorem AdversarialBco.Poly.df2AzumaEvent_of (h : AdversarialBco.Poly.AzumaHoeffding.{u}) :
    AdversarialBco.Poly.Df2AzumaEvent.{u} := by
  intro Ω m0 μ _ ℱ Z hZm hZ n δ hδ
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hδ7 : (7 : ℝ) ≤ δ
    · have h_one_le : (1 : ℝ) ≤ δ / 7 := by
        linarith
      calc
        μ {ω | ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * (n : ℝ) * Real.log (7 / δ)) <
            ∑ t ∈ Finset.range n, Z t ω} ≤ 1 :=
          MeasureTheory.prob_le_one
        _ ≤ ENNReal.ofReal (δ / 7) := by
          simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h_one_le
    · have hδ_lt_7 : δ < 7 := by linarith
      set ε := Real.sqrt (2 * (n : ℝ) * Real.log (7 / δ)) with hεdef
      have hε_nonneg : 0 ≤ ε := Real.sqrt_nonneg _
      have h_sum_sq : (∑ t ∈ Finset.range n, ((1 : ℝ) - (0 : ℝ)) ^ 2) = (n : ℝ) := by
        simp
      have h_subset : {ω | ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + ε <
          ∑ t ∈ Finset.range n, Z t ω} ⊆
          {ω | ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)} := by
        intro ω hω
        have hω' : (∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω) + ε < ∑ t ∈ Finset.range n, Z t ω := hω
        have hsumsub : (∑ t ∈ Finset.range n, Z t ω) - (∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω) =
            ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) := by
          simp [Finset.sum_sub_distrib]
        have hineq : ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω) := by
          linarith
        exact hineq
      have h_azuma := h μ ℱ Z (fun _ => 0) (fun _ => 1) hZm (by
        intro t
        simpa using hZ t) n ε hε_nonneg
      have h_simplified : μ {ω | ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)} ≤
          ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / (n : ℝ))) := by
        simpa [h_sum_sq] using h_azuma
      calc
        μ {ω | ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + ε <
            ∑ t ∈ Finset.range n, Z t ω} ≤
            μ {ω | ε ≤ ∑ t ∈ Finset.range n, (Z t ω - μ[Z t | ℱ t] ω)} :=
          MeasureTheory.measure_mono h_subset
        _ ≤ ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / (n : ℝ))) := h_simplified
        _ ≤ ENNReal.ofReal (δ / 7) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hεdef]
          exact AdversarialBco.Poly.Azuma.azuma_event_arith n δ hnpos hδ (by linarith)

/-- Azuma-Hoeffding, upper tail. -/
theorem AdversarialBco.Poly.azumaHoeffding : AdversarialBco.Poly.AzumaHoeffding.{u} := by
  intro Ω m0 μ _ ℱ Z a b hZm hZ n ε hε
  exact AdversarialBco.Poly.Azuma.azuma_tail μ ℱ Z a b hZm hZ n ε hε

/-- Azuma-Hoeffding, two-sided. -/
theorem AdversarialBco.Poly.azumaHoeffdingAbs : AdversarialBco.Poly.AzumaHoeffdingAbs.{u} :=
  AdversarialBco.Poly.azumaHoeffdingAbs_of AdversarialBco.Poly.azumaHoeffding

/-- The source's thm:azuma. -/
theorem AdversarialBco.Poly.azumaMartingale : AdversarialBco.Poly.AzumaMartingale.{u} :=
  AdversarialBco.Poly.azumaMartingale_of AdversarialBco.Poly.azumaHoeffding

/-- The event Azuma of DF2 at the level `δ/7`. -/
theorem AdversarialBco.Poly.df2AzumaEvent : AdversarialBco.Poly.Df2AzumaEvent.{u} :=
  AdversarialBco.Poly.df2AzumaEvent_of AdversarialBco.Poly.azumaHoeffding
