/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.WrapIncr

@[expose] public section

/-!
# The bias of the weighted increment (W2; Lemma SK' (i), (iv))

In the round of setting (E) of UW/WrapIncr.lean, with `Y = E(σ, ξ) + P(σ, ξ) e` and `X = W(ξ, Y) D(σ, ξ)`: when the
weight and the clip change the observation only on a measurable set `B`, the conditional mean of `X` given `𝒢` is
Lemma ub's mean `∫ E D dγ` up to `2 (E[Y⁴ | 𝒢])^{1/4} (∫ D⁴ dγ)^{1/4} P(B | 𝒢)^{1/2}` (`cond_bias_w`,
`condBiasW : CondBiasW`).

Proof: `E[Y D | 𝒢] = ∫ E D dγ` by `cond_incr` with `A = E D`, `B = P D`; off `B`, `X = Y D`, and on
`B`, `|X - Y D| ≤ 2 |Y D|`; then two conditional Cauchy and Schwarz steps (`cond_cauchy_schwarz`),
`E[|Y D| 1_B | 𝒢] ≤ E[Y² D² | 𝒢]^{1/2} P(B | 𝒢)^{1/2}` and `E[Y² D² | 𝒢] ≤ E[Y⁴ | 𝒢]^{1/2} E[D⁴ | 𝒢]^{1/2}`, and the
freezing of `E[D⁴ | 𝒢]` (`lemmaFR`). The fourth moment of `Y` reads the eighth moment of the noise, which
`E[exp(e²)] < ∞` gives (`integrable_eight_of_exp`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-! ## Moments of the noise up to the eighth -/

/-- `(1 + |x|)⁸ ≤ 6400 exp(x²)`. -/
theorem one_add_abs_pow_eight_le (x : ℝ) : (1 + |x|) ^ 8 ≤ 6400 * Real.exp (x ^ 2) := by
  have h1 : (1 + |x|) ^ 8 ≤ 256 * (1 + |x| ^ 8) := by
    rcases le_total 1 |x| with h | h
    · have h2 : 1 + |x| ≤ 2 * |x| := by linarith
      calc (1 + |x|) ^ 8 ≤ (2 * |x|) ^ 8 := pow_le_pow_left₀ (by positivity) h2 8
        _ = 256 * |x| ^ 8 := by ring
        _ ≤ 256 * (1 + |x| ^ 8) := by linarith
    · have h2 : 1 + |x| ≤ 2 := by linarith
      have h3 := pow_nonneg (abs_nonneg x) 8
      calc (1 + |x|) ^ 8 ≤ 2 ^ 8 := pow_le_pow_left₀ (by positivity) h2 8
        _ ≤ 256 * (1 + |x| ^ 8) := by nlinarith
  have h2 : |x| ^ 8 ≤ 24 * Real.exp (x ^ 2) := by
    have h := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) 4
    have e : |x| ^ 8 = (x ^ 2) ^ 4 := by rw [← sq_abs x]; ring
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf, div_le_iff₀ (by norm_num)] at h
    rw [e]; linarith
  have h3 : 1 ≤ Real.exp (x ^ 2) := Real.one_le_exp (sq_nonneg x)
  linarith

theorem integrable_eight_of_exp {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {e : Ω → ℝ}
    (he : Measurable e) (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ) :
    Integrable (fun ω => (1 + |e ω|) ^ 8) μ :=
  (hei.const_mul 6400).mono' ((measurable_const.add he.abs).pow_const 8).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact one_add_abs_pow_eight_le (e ω))

/-- Domination by a polynomial in `‖ξ‖` times `(1 + |e|)^i`, `i ≤ 4`. -/
theorem integrable_of_dom4 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Ω → Fin d → ℝ} {e : Ω → ℝ} (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (i j : ℕ) (hi : i ≤ 4) (hfb : ∀ ω, |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) : Integrable f μ := by
  have hP1 : ∀ ω, 1 ≤ 1 + ‖ξ ω‖ := fun ω => by have := norm_nonneg (ξ ω); linarith
  have hE1 : ∀ ω, 1 ≤ 1 + |e ω| := fun ω => by have := abs_nonneg (e ω); linarith
  have hb : ∀ ω, |f ω| ≤ |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 8) := by
    intro ω
    have hPj : 1 ≤ (1 + ‖ξ ω‖) ^ j := one_le_pow₀ (hP1 ω)
    have hEi : 1 ≤ (1 + |e ω|) ^ i := one_le_pow₀ (hE1 ω)
    have hE2 : ((1 + |e ω|) ^ i) ^ 2 ≤ (1 + |e ω|) ^ 8 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (hE1 ω) (by omega)
    have hamgm := two_mul_le_add_sq ((1 + ‖ξ ω‖) ^ j) ((1 + |e ω|) ^ i)
    have hprod : 0 ≤ (1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i := by positivity
    have hC := mul_le_mul_of_nonneg_right (le_abs_self C) hprod
    have hle : (1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i ≤ ((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 8 := by nlinarith
    calc |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := hfb ω
      _ ≤ |C| * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := hC
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (abs_nonneg C)
  have h_int1 : Integrable (fun ω => ((1 + ‖ξ ω‖) ^ j) ^ 2) μ := by
    have h_int_gam : Integrable (fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) (gam d) := integrable_poly_gam (2 * j)
    rw [← hlaw] at h_int_gam
    have h_map : Integrable ((fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) ∘ ξ) μ := h_int_gam.comp_measurable hξ
    have e1 : ((fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) ∘ ξ) = (fun ω => ((1 + ‖ξ ω‖) ^ j) ^ 2) := by
      ext ω; simp [← pow_mul, mul_comm]
    rw [e1] at h_map
    exact h_map
  refine ((h_int1.add (integrable_eight_of_exp he hei)).const_mul |C|).mono' hf
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact hb ω

theorem sqrt_sqrt_eq_rpow {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (Real.sqrt y) = y ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
  norm_num

/-! ## (W2) -/

/-- **(W2) `cond_bias_w`** (Lemma SK' (i) and (iv)): the bias of the weighted increment. -/
theorem cond_bias_w {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (hσ : Measurable[𝒢] σ) (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (E P D : S × (Fin d → ℝ) → ℝ) (hE : Measurable E) (hP : Measurable P) (hD : Measurable D)
    (K : ℝ) (k : ℕ) (hK : 0 ≤ K) (hEK : ∀ x, |E x| ≤ K * (1 + ‖x.2‖) ^ k)
    (hPK : ∀ x, |P x| ≤ K * (1 + ‖x.2‖) ^ k) (hDK : ∀ x, |D x| ≤ K * (1 + ‖x.2‖) ^ k)
    (Wf : (Fin d → ℝ) → ℝ → ℝ) (hW : Measurable (Function.uncurry Wf)) (hWle : ∀ x y, |Wf x y| ≤ |y|)
    (Bset : Set Ω) (hB : MeasurableSet Bset)
    (hoff : ∀ ω ∉ Bset, Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) = E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) :
    ∀ᵐ ω ∂μ, |μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω -
        ∫ z, E (σ ω, z) * D (σ ω, z) ∂(gam d)| ≤
      2 * (μ[fun ω => (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) *
        (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ) * (μ[Bset.indicator 1 | 𝒢] ω) ^ (1 / 2 : ℝ) := by
  set Y : Ω → ℝ := fun ω => E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω with hYdef
  set Dv : Ω → ℝ := fun ω => D (σ ω, ξ ω) with hDv
  set X : Ω → ℝ := fun ω => Wf (ξ ω) (Y ω) * Dv ω with hXdef
  set A : S × (Fin d → ℝ) → ℝ := fun x => E x * D x with hAdef
  set B : S × (Fin d → ℝ) → ℝ := fun x => P x * D x with hBdef
  have hσ0 : Measurable σ := hσ.mono h𝒢 le_rfl
  have hp : Measurable fun ω => (σ ω, ξ ω) := hσ0.prodMk hξ
  have hYm : Measurable Y := (hE.comp hp).add ((hP.comp hp).mul he)
  have hDm : Measurable Dv := hD.comp hp
  have hXm : Measurable X := (hW.comp (hξ.prodMk hYm)).mul hDm
  have hYDm : Measurable fun ω => Y ω * Dv ω := hYm.mul hDm
  -- the polynomial bounds
  have hpk : ∀ ω, 0 ≤ (1 + ‖ξ ω‖) ^ k := fun ω => pow_nonneg (by positivity) k
  have hYb : ∀ ω, |Y ω| ≤ K * (1 + ‖ξ ω‖) ^ k * (1 + |e ω|) := by
    intro ω
    have h1 := hEK (σ ω, ξ ω)
    have h2 := hPK (σ ω, ξ ω)
    have h3 : |P (σ ω, ξ ω) * e ω| ≤ K * (1 + ‖ξ ω‖) ^ k * |e ω| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    calc |Y ω| ≤ |E (σ ω, ξ ω)| + |P (σ ω, ξ ω) * e ω| := abs_add_le _ _
      _ ≤ K * (1 + ‖ξ ω‖) ^ k + K * (1 + ‖ξ ω‖) ^ k * |e ω| := add_le_add h1 h3
      _ = _ := by ring
  have hDb : ∀ ω, |Dv ω| ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => hDK (σ ω, ξ ω)
  have hKp : ∀ ω, 0 ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => mul_nonneg hK (hpk ω)
  have hYj : ∀ (j : ℕ) ω, |Y ω| ^ j ≤ K ^ j * ((1 + ‖ξ ω‖) ^ (k * j) * (1 + |e ω|) ^ j) := by
    intro j ω
    calc |Y ω| ^ j ≤ (K * (1 + ‖ξ ω‖) ^ k * (1 + |e ω|)) ^ j := pow_le_pow_left₀ (abs_nonneg _) (hYb ω) j
      _ = _ := by rw [mul_pow, mul_pow, pow_mul]; ring
  have hDj : ∀ (j : ℕ) ω, |Dv ω| ^ j ≤ K ^ j * ((1 + ‖ξ ω‖) ^ (k * j) * (1 + |e ω|) ^ 0) := by
    intro j ω
    calc |Dv ω| ^ j ≤ (K * (1 + ‖ξ ω‖) ^ k) ^ j := pow_le_pow_left₀ (abs_nonneg _) (hDb ω) j
      _ = _ := by rw [mul_pow, pow_mul]; ring
  have hdom := fun {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ) (i j : ℕ) (hi : i ≤ 4)
      (hfb : ∀ ω, |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) =>
    integrable_of_dom4 hξ he hlaw hei hf C i j hi hfb
  have hYD2 : ∀ ω, |Y ω * Dv ω| ^ 2 ≤ K ^ 4 * ((1 + ‖ξ ω‖) ^ (k * 4) * (1 + |e ω|) ^ 2) := by
    intro ω
    have h1 := hYj 2 ω
    have h2 := hDj 2 ω
    rw [abs_mul, mul_pow]
    calc |Y ω| ^ 2 * |Dv ω| ^ 2 ≤ (K ^ 2 * ((1 + ‖ξ ω‖) ^ (k * 2) * (1 + |e ω|) ^ 2)) *
          (K ^ 2 * ((1 + ‖ξ ω‖) ^ (k * 2) * (1 + |e ω|) ^ 0)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by rw [show k * 4 = k * 2 + k * 2 by ring, pow_add]; ring
  have hYD1 : ∀ ω, |Y ω * Dv ω| ≤ K ^ 2 * ((1 + ‖ξ ω‖) ^ (k * 2) * (1 + |e ω|) ^ 1) := by
    intro ω
    rw [abs_mul]
    calc |Y ω| * |Dv ω| ≤ (K * (1 + ‖ξ ω‖) ^ k * (1 + |e ω|)) * (K * (1 + ‖ξ ω‖) ^ k) :=
          mul_le_mul (hYb ω) (hDb ω) (abs_nonneg _) (mul_nonneg (hKp ω) (by positivity))
      _ = _ := by rw [pow_mul]; ring
  -- integrability
  have i_YD : Integrable (fun ω => Y ω * Dv ω) μ := hdom hYDm.aestronglyMeasurable (K ^ 2) 1 (k * 2) (by norm_num) hYD1
  have hXle : ∀ ω, |X ω| ≤ |Y ω * Dv ω| := by
    intro ω
    rw [hXdef, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hWle _ _) (abs_nonneg _)
  have i_X : Integrable X μ :=
    i_YD.norm.mono' hXm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hXle ω)
  have i_Y4 : Integrable (fun ω => Y ω ^ 4) μ :=
    hdom (hYm.pow_const 4).aestronglyMeasurable (K ^ 4) 4 (k * 4) le_rfl fun ω => by
      rw [abs_pow]; exact hYj 4 ω
  have i_D4 : Integrable (fun ω => Dv ω ^ 4) μ :=
    hdom (hDm.pow_const 4).aestronglyMeasurable (K ^ 4) 0 (k * 4) (by norm_num) fun ω => by
      rw [abs_pow]; exact hDj 4 ω
  have i_YD2 : Integrable (fun ω => Y ω ^ 2 * Dv ω ^ 2) μ :=
    hdom ((hYm.pow_const 2).mul (hDm.pow_const 2)).aestronglyMeasurable (K ^ 4) 2 (k * 4) (by norm_num)
      fun ω => by rw [← mul_pow, abs_pow]; exact hYD2 ω
  have hIm : Measurable (Bset.indicator (1 : Ω → ℝ)) := measurable_one.indicator hB
  have hI01 : ∀ ω, 0 ≤ Bset.indicator (1 : Ω → ℝ) ω ∧ Bset.indicator (1 : Ω → ℝ) ω ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ Bset <;> simp [hω]
  have hIsq : (fun ω => Bset.indicator (1 : Ω → ℝ) ω ^ 2) = Bset.indicator 1 := by
    funext ω
    by_cases hω : ω ∈ Bset <;> simp [hω]
  have i_I2 : Integrable (fun ω => Bset.indicator (1 : Ω → ℝ) ω ^ 2) μ := by
    rw [hIsq]
    exact (integrable_const (1 : ℝ)).mono' hIm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hI01 ω).1]; exact (hI01 ω).2)
  -- (1) the conditional mean of `Y D`
  have hAK : ∀ x, |A x| ≤ K ^ 2 * (1 + ‖x.2‖) ^ (2 * k) := by
    intro x
    rw [hAdef, abs_mul, pow_mul', sq, sq, mul_mul_mul_comm]
    exact mul_le_mul (hEK x) (hDK x) (abs_nonneg _) (mul_nonneg hK (pow_nonneg (by positivity) _))
  have hBK : ∀ x, |B x| ≤ K ^ 2 * (1 + ‖x.2‖) ^ (2 * k) := by
    intro x
    rw [hBdef, abs_mul, pow_mul', sq, sq, mul_mul_mul_comm]
    exact mul_le_mul (hPK x) (hDK x) (abs_nonneg _) (mul_nonneg hK (pow_nonneg (by positivity) _))
  obtain ⟨i_inc, -, h_inc0, -⟩ := cond_incr 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee A B (hE.mul hD)
    (hP.mul hD) (K ^ 2) (2 * k) (sq_nonneg K) hAK hBK
  set mσ : Ω → ℝ := fun ω => mean A (σ ω) with hmσ
  have hm𝒢 : Measurable[𝒢] mσ := (measurable_mean (hE.mul hD)).comp hσ
  have hYDsplit : (fun ω => Y ω * Dv ω) = incr A B σ ξ e + mσ := by
    funext ω; simp only [hYdef, hDv, hmσ, incr, hAdef, hBdef, Pi.add_apply]; ring
  have i_m : Integrable mσ μ := by
    have e1 : mσ = (fun ω => Y ω * Dv ω) - incr A B σ ξ e := by rw [hYDsplit]; abel
    rw [e1]; exact i_YD.sub i_inc
  have hYDmean : μ[fun ω => Y ω * Dv ω | 𝒢] =ᵐ[μ] mσ := by
    rw [hYDsplit]
    have h1 := condExp_add i_inc i_m 𝒢
    have h2 : μ[mσ | 𝒢] = mσ := condExp_of_stronglyMeasurable h𝒢 hm𝒢.stronglyMeasurable i_m
    filter_upwards [h1, h_inc0] with ω h1 h0
    rw [h1, Pi.add_apply, h0, h2, Pi.zero_apply, zero_add]
  -- (2) the difference `X - Y D` and its bound
  set f : Ω → ℝ := X - fun ω => Y ω * Dv ω with hfdef
  set h : Ω → ℝ := fun ω => |Y ω * Dv ω| * Bset.indicator 1 ω with hhdef
  have hfle : ∀ ω, |f ω| ≤ ((2 : ℝ) • h) ω := by
    intro ω
    simp only [hfdef, hhdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hω : ω ∈ Bset
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one, hXdef]
      have h1 : Wf (ξ ω) (Y ω) * Dv ω - Y ω * Dv ω = (Wf (ξ ω) (Y ω) - Y ω) * Dv ω := by ring
      rw [h1, abs_mul, abs_mul]
      have h2 : |Wf (ξ ω) (Y ω) - Y ω| ≤ 2 * |Y ω| := by
        have := abs_sub (Wf (ξ ω) (Y ω)) (Y ω)
        have := hWle (ξ ω) (Y ω)
        linarith
      calc |Wf (ξ ω) (Y ω) - Y ω| * |Dv ω| ≤ (2 * |Y ω|) * |Dv ω| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hω, mul_zero, mul_zero, hXdef]
      have h1 : Wf (ξ ω) (Y ω) = Y ω := hoff ω hω
      simp only
      rw [h1, sub_self, abs_zero]
  have i_f : Integrable f μ := i_X.sub i_YD
  have i_h : Integrable h μ :=
    i_YD.norm.mono' (hYDm.abs.mul hIm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hhdef, abs_mul, abs_abs, abs_of_nonneg (hI01 ω).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hI01 ω).2)
  have h1 := condExp_sub (m := 𝒢) i_X i_YD
  have h2 := abs_condExp_ae_le_condExp_abs (m := 𝒢) (μ := μ) f
  have h3 := condExp_mono (m := 𝒢) i_f.abs (i_h.smul (2 : ℝ))
    (Filter.Eventually.of_forall fun ω => by simpa using hfle ω)
  have h4 := condExp_smul (μ := μ) (2 : ℝ) h 𝒢
  -- (3) the two conditional Cauchy and Schwarz steps
  have hU1 : MemLp (fun ω => |Y ω * Dv ω|) 2 μ :=
    (memLp_two_iff_integrable_sq hYDm.abs.aestronglyMeasurable).2 (by
      have e1 : (fun ω => |Y ω * Dv ω| ^ 2) = fun ω => Y ω ^ 2 * Dv ω ^ 2 := by
        funext ω; rw [sq_abs, mul_pow]
      rw [e1]; exact i_YD2)
  have hV1 : MemLp (Bset.indicator (1 : Ω → ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq hIm.aestronglyMeasurable).2 i_I2
  have hcs1 : ∀ᵐ ω ∂μ, μ[fun ω => |Y ω * Dv ω| * Bset.indicator 1 ω | 𝒢] ω ≤
      Real.sqrt (μ[fun ω => |Y ω * Dv ω| ^ 2 | 𝒢] ω) *
        Real.sqrt (μ[fun ω => Bset.indicator (1 : Ω → ℝ) ω ^ 2 | 𝒢] ω) :=
    cond_cauchy_schwarz μ 𝒢 h𝒢 (fun ω => |Y ω * Dv ω|) (Bset.indicator 1) hU1 hV1
  have e2 : (fun ω => |Y ω * Dv ω| ^ 2) = fun ω => Y ω ^ 2 * Dv ω ^ 2 := by
    funext ω; rw [sq_abs, mul_pow]
  rw [e2, hIsq] at hcs1
  have hU2 : MemLp (fun ω => Y ω ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (hYm.pow_const 2).aestronglyMeasurable).2 (by
      have e3 : (fun ω => (Y ω ^ 2) ^ 2) = fun ω => Y ω ^ 4 := by funext ω; ring
      rw [e3]; exact i_Y4)
  have hV2 : MemLp (fun ω => Dv ω ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (hDm.pow_const 2).aestronglyMeasurable).2 (by
      have e3 : (fun ω => (Dv ω ^ 2) ^ 2) = fun ω => Dv ω ^ 4 := by funext ω; ring
      rw [e3]; exact i_D4)
  have hcs2 : ∀ᵐ ω ∂μ, μ[fun ω => Y ω ^ 2 * Dv ω ^ 2 | 𝒢] ω ≤
      Real.sqrt (μ[fun ω => (Y ω ^ 2) ^ 2 | 𝒢] ω) * Real.sqrt (μ[fun ω => (Dv ω ^ 2) ^ 2 | 𝒢] ω) :=
    cond_cauchy_schwarz μ 𝒢 h𝒢 (fun ω => Y ω ^ 2) (fun ω => Dv ω ^ 2) hU2 hV2
  have e4 : (fun ω => (Y ω ^ 2) ^ 2) = fun ω => Y ω ^ 4 := by funext ω; ring
  have e5 : (fun ω => (Dv ω ^ 2) ^ 2) = fun ω => D (σ ω, ξ ω) ^ 4 := by funext ω; simp only [hDv]; ring
  rw [e4, e5] at hcs2
  -- (4) the freezing of `E[D⁴ | 𝒢]`
  have hFR := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ (fun x => D x ^ 4) h𝒢 hσ hξ hind (hD.pow_const 4) i_D4
  rw [hlaw] at hFR
  have hY4n := condExp_nonneg (m := 𝒢) (μ := μ) (f := fun ω => Y ω ^ 4)
    (Filter.Eventually.of_forall fun ω => by positivity)
  have hIn := condExp_nonneg (m := 𝒢) (μ := μ) (f := Bset.indicator (1 : Ω → ℝ))
    (Filter.Eventually.of_forall fun ω => (hI01 ω).1)
  have hYD2n := condExp_nonneg (m := 𝒢) (μ := μ) (f := fun ω => Y ω ^ 2 * Dv ω ^ 2)
    (Filter.Eventually.of_forall fun ω => by positivity)
  filter_upwards [h1, h2, h3, h4, hYDmean, hcs1, hcs2, hFR, hY4n, hIn, hYD2n] with ω h1 h2 h3 h4 hm hcs1 hcs2 hFR
    hY4n hIn hYD2n
  have hD4n : 0 ≤ ∫ z, D (σ ω, z) ^ 4 ∂(gam d) := integral_nonneg fun z => by positivity
  rw [hFR] at hcs2
  -- assemble
  have hdiff : μ[X | 𝒢] ω - ∫ z, E (σ ω, z) * D (σ ω, z) ∂(gam d) = μ[f | 𝒢] ω := by
    rw [hfdef, h1, Pi.sub_apply, hm]; rfl
  have hstep : |μ[f | 𝒢] ω| ≤ 2 * μ[h | 𝒢] ω := by
    refine h2.trans (le_of_le_of_eq h3 ?_)
    rw [h4, Pi.smul_apply, smul_eq_mul]
  have hsq : Real.sqrt (μ[fun ω => Y ω ^ 2 * Dv ω ^ 2 | 𝒢] ω) ≤
      (μ[fun ω => Y ω ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) * (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ) := by
    rw [← sqrt_sqrt_eq_rpow hY4n, ← sqrt_sqrt_eq_rpow hD4n, ← Real.sqrt_mul (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hcs2
  have hb : (μ[Bset.indicator 1 | 𝒢] ω) ^ (1 / 2 : ℝ) = Real.sqrt (μ[Bset.indicator 1 | 𝒢] ω) := by
    rw [Real.sqrt_eq_rpow]
  show |μ[X | 𝒢] ω - ∫ z, E (σ ω, z) * D (σ ω, z) ∂(gam d)| ≤ _
  rw [hdiff, hb]
  have hsb := Real.sqrt_nonneg (μ[Bset.indicator 1 | 𝒢] ω)
  calc |μ[f | 𝒢] ω| ≤ 2 * μ[h | 𝒢] ω := hstep
    _ ≤ 2 * (Real.sqrt (μ[fun ω => Y ω ^ 2 * Dv ω ^ 2 | 𝒢] ω) * Real.sqrt (μ[Bset.indicator 1 | 𝒢] ω)) := by
        have : μ[h | 𝒢] ω ≤ _ := hcs1
        linarith
    _ ≤ 2 * (((μ[fun ω => Y ω ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) * (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ)) *
          Real.sqrt (μ[Bset.indicator 1 | 𝒢] ω)) := by
        gcongr
    _ = _ := by ring

/-- **(W2)** as the interface states it. -/
theorem condBiasW : CondBiasW := by
  intro d Ω S 𝒢 m0 _ μ _ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee E P D hE hP hD K k hK hEK hPK hDK Wf hW hWle
    Bset hB hoff
  exact cond_bias_w 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee E P D hE hP hD K k hK hEK hPK hDK Wf hW hWle
    Bset hB hoff

end AdversarialBco.UW
