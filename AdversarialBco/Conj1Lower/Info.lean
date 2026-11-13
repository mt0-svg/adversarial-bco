/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Ledger
public import AdversarialBco.Conj1Lower.RuleS

@[expose] public section

/-!
# The information: the chain-rule lemma and the count lemma

One round: a law `π` of the tip `θ`, the genie's answer `c θ` in a finite set, the signal `s θ`, the observation
`y = s θ + σ z`, `z ∼ N(0, 1)`. The normaliser of the Bayes update is `Z(a, y) = ∫ 1[c θ' = a] φ_σ(y - s θ') dπ(θ')`
(`normZ`), the information density at the true tip is `ln(φ_σ(σ z)/Z(c θ, y))` (`infoDens`), and its mean is the
information `J` of the round (`infoJ`), the mutual information of the tip and `(A, Y)`.

* The chain-rule lemma in the form (S1) (`infoJ_chain`): for any constants `ĉ_a`,
  `J ≤ H(A) + ∑_a ∫_{c = a} (s - ĉ_a)² dπ / (2σ²)`, with `H(A) = ∑_a p_a ln(1/p_a)` (`ansEntropy`). Gibbs on `ℝ`
  against `N(ĉ_a, σ²)`; no Gaussian maximum entropy.
* Route (S2): the Kullback-Leibler divergence from the prior of a law with the density `ρ` on `π₀`,
  `K(ρ) = ∫ ρ ln ρ dπ₀` (`klDens`); after a round, `E K(ρ') = K(ρ) + J` (`kl_round`, the density recursion
  `updDens` of Bayes.lean's `dens`); `K ≥ 0`, `J ≥ 0`.
* The count lemma (b) (`count_b`): on the prior uniform on `B(0, 1/2)`, a law with fewer than `d/2` eigenvalues of its
  covariance at least `w²` has `K ≥ N*` (`nStar` of Balance.lean): Gibbs against the Gaussian density whose precision
  is the clipped metric `M` of Frame.lean, the volume of the ball, crude Stirling (S3).
* The game (`count_game`): `∑_{t < n} E J_t = E K(π_n) ≥ N* P(π_n dead)`, the field `count` of `GameFacts`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal NNReal

namespace AdversarialBco.Lower

open Bayes

/-! ## One round: the information -/

section Round

variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

/-- The normaliser of the Bayes update, `Z(a, y) = ∫ 1[c θ = a] φ_v(y - s θ) dπ(θ)` (a real number). -/
noncomputable def normZ (π : Measure Θ) (c : Θ → α) (s : Θ → ℝ) (v : ℝ≥0) (a : α) (y : ℝ) : ℝ :=
  ∫ θ, (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ ∂π

/-- The information density of the round at the tip `θ` and the noise `z`: `ln(φ_σ(σ z)/Z(c θ, s θ + σ z))`. -/
noncomputable def infoDens (π : Measure Θ) (c : Θ → α) (s : Θ → ℝ) (sc : ℝ) (θ : Θ) (z : ℝ) : ℝ :=
  Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z) /
    normZ π c s (noiseVar sc) (c θ) (s θ + sc * z))

/-- The information `J` of the round: the mean information density, the mutual information of the tip and of the
answer and observation. -/
noncomputable def infoJ (π : Measure Θ) (c : Θ → α) (s : Θ → ℝ) (sc : ℝ) : ℝ :=
  ∫ θ, ∫ z, infoDens π c s sc θ z ∂gaussianReal 0 1 ∂π

/-- The entropy of the answer, `H(A) = ∑_a p_a ln(1/p_a)`. -/
noncomputable def ansEntropy [Fintype α] (π : Measure Θ) (c : Θ → α) : ℝ :=
  ∑ a, Real.negMulLog (π.real (c ⁻¹' {a}))

/-- `ln φ_μ(y) = -(1/2) ln(2π v) - (y - μ)²/(2v)`. -/
theorem log_gaussianPDFReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    Real.log (gaussianPDFReal μ v y) = -(Real.log (2 * Real.pi * v) / 2) - (y - μ) ^ 2 / (2 * v) := by
  have hv_pos : (v : ℝ) > 0 := by
    have hle : (0 : ℝ) ≤ v := v.2
    have hne : (v : ℝ) ≠ 0 := by exact mod_cast hv
    exact lt_of_le_of_ne hle hne.symm
  rw [gaussianPDFReal]
  have hsqrt_pos : Real.sqrt (2 * Real.pi * (v : ℝ)) > 0 := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hsqrt_ne_zero : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 := by linarith
  have hsqrt_inv_ne_zero : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 :=
    inv_ne_zero hsqrt_ne_zero
  have hexp_pos : Real.exp (-(y - μ) ^ 2 / (2 * (v : ℝ))) > 0 := Real.exp_pos _
  have hexp_ne_zero : Real.exp (-(y - μ) ^ 2 / (2 * (v : ℝ))) ≠ 0 := by linarith
  rw [Real.log_mul hsqrt_inv_ne_zero hexp_ne_zero]
  rw [Real.log_inv, Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi * (v : ℝ))]
  rw [Real.log_exp (-(y - μ) ^ 2 / (2 * (v : ℝ)))]
  ring

/-- The normaliser of a cell is at most its mass times the peak of the Gaussian density. -/
theorem normZ_le [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α} (hc : Measurable c)
    {s : Θ → ℝ} (hs : Measurable s) {v : ℝ≥0} (hv : v ≠ 0) (a : α) (y : ℝ) :
    normZ π c s v a y ≤ π.real (c ⁻¹' {a}) * (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  have hmeas : MeasurableSet (c ⁻¹' {a}) := hc (measurableSet_singleton a)
  have hv_pos : 0 < (v : ℝ) := by
    by_contra! H
    have hzero : (v : ℝ) = 0 := by linarith
    exact hv (by exact_mod_cast hzero)
  have h_bound : ∀ (θ : Θ), (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ ≤
      (c ⁻¹' {a}).indicator (fun _ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) θ := by
    intro θ
    by_cases hθ : θ ∈ c ⁻¹' {a}
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, gaussianPDFReal_def]
      have h_exp : Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h_sq_nonneg : 0 ≤ (y - s θ) ^ 2 := sq_nonneg _
        have h_denom_pos : 0 < 2 * (v : ℝ) := by nlinarith
        have h_nonpos : -(y - s θ) ^ 2 / (2 * (v : ℝ)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by nlinarith)
        exact h_nonpos
      have h_sqrt_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
        positivity
      calc
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ))) ≤
            (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp h_sqrt_nonneg
        _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by simp
    · simp [hθ]
  have h_meas_left : Measurable (fun (θ : Θ) => (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ) := by
    have h_meas_inner : Measurable (fun (θ : Θ) => gaussianPDFReal (s θ) v y) := by
      have h_cont : Continuous (fun (μ : ℝ) => gaussianPDFReal μ v y) := by
        unfold gaussianPDFReal
        continuity
      exact h_cont.measurable.comp hs
    exact Measurable.indicator h_meas_inner hmeas
  have h_int_left : Integrable (fun (θ : Θ) => (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ) π := by
    refine Integrable.of_bound h_meas_left.aestronglyMeasurable
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ?_
    filter_upwards [] with θ
    have h_val : (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
      have h_le := h_bound θ
      by_cases hθ : θ ∈ c ⁻¹' {a}
      · have h_rhs : (c ⁻¹' {a}).indicator (fun _ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) θ =
            (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by simp [hθ]
        rw [h_rhs] at h_le
        exact h_le
      · have h_lhs : (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ = 0 := by
          simp [hθ]
        rw [h_lhs]
        positivity
    -- For ℝ, ‖x‖ = |x|. Since the indicator is nonnegative (gaussianPDFReal is positive),
    -- we have ‖indicator ... θ‖ = indicator ... θ
    have h_nonneg : 0 ≤ (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ := by
      by_cases hθ : θ ∈ c ⁻¹' {a}
      · have h_pos : 0 < gaussianPDFReal (s θ) v y := gaussianPDFReal_pos _ _ _ hv
        simp [hθ, h_pos.le]
      · simp [hθ]
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_val
  have h_int_right : Integrable (fun (θ : Θ) => (c ⁻¹' {a}).indicator (fun _ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) θ) π := by
    have h_const : Integrable (fun (_ : Θ) => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) π :=
      integrable_const _
    exact h_const.indicator hmeas
  calc
    normZ π c s v a y = ∫ θ, (c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ ∂π := rfl
    _ ≤ ∫ θ, (c ⁻¹' {a}).indicator (fun _ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) θ ∂π :=
      integral_mono h_int_left h_int_right h_bound
    _ = π.real (c ⁻¹' {a}) • (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
      rw [integral_indicator_const _ hmeas]
    _ = π.real (c ⁻¹' {a}) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by simp

/-- The Gaussian density at `y` with mean `|s| ≤ S₀` is at least its value at distance `|y| + S₀`. -/
theorem gaussianPDFReal_ge_far {s y S₀ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hsb : |s| ≤ S₀) :
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(|y| + S₀) ^ 2 / (2 * (v : ℝ))) ≤
    gaussianPDFReal s v y := by
  have hv_pos : (0 : ℝ) < v := by
    have h : 0 < (v : ℝ≥0) := pos_of_ne_zero hv
    exact_mod_cast h
  have h_two_v_pos : 0 < 2 * (v : ℝ) := by linarith
  have h_abs : |y - s| ≤ |y| + S₀ := by
    calc
      |y - s| ≤ |y| + |s| := abs_sub _ _
      _ ≤ |y| + S₀ := by linarith
  have h_nonneg_sum : 0 ≤ |y| + S₀ := by
    have h_abs_y : 0 ≤ |y| := abs_nonneg _
    have h_S0 : 0 ≤ S₀ := by
      have h_abs_s : 0 ≤ |s| := abs_nonneg _
      linarith
    linarith
  have h_sq : (y - s) ^ 2 ≤ (|y| + S₀) ^ 2 := by
    calc
      (y - s) ^ 2 = |y - s| ^ 2 := by rw [sq_abs]
      _ ≤ |(|y| + S₀)| ^ 2 := by
        have h_abs' : |y - s| ≤ |(|y| + S₀)| := by
          rw [abs_of_nonneg h_nonneg_sum]
          exact h_abs
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs' 2
      _ = (|y| + S₀) ^ 2 := by rw [abs_of_nonneg h_nonneg_sum]
  have h_exp : Real.exp (-(|y| + S₀) ^ 2 / (2 * (v : ℝ))) ≤ Real.exp (-(y - s) ^ 2 / (2 * (v : ℝ))) := by
    refine Real.exp_le_exp_of_le ?_
    have h_neg : -( |y| + S₀) ^ 2 ≤ -(y - s) ^ 2 := by linarith
    exact (div_le_div_iff_of_pos_right h_two_v_pos).mpr h_neg
  have h_inv_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  simpa [gaussianPDFReal_def] using mul_le_mul_of_nonneg_left h_exp h_inv_nonneg


/-- With a bounded signal, the normaliser of a cell is at least its mass times the Gaussian density at distance
`|y| + S₀`. -/
theorem le_normZ [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α} (hc : Measurable c)
    {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {v : ℝ≥0} (hv : v ≠ 0) (a : α) (y : ℝ) :
    π.real (c ⁻¹' {a}) * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(|y| + S₀) ^ 2 / (2 * v))) ≤
      normZ π c s v a y := by
  let s0 := c ⁻¹' {a}
  let A := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(|y| + S₀) ^ 2 / (2 * (v : ℝ)))
  have hs0 : MeasurableSet s0 :=
    hc (MeasurableSet.singleton a)
  have h_bound : ∀ θ, ‖gaussianPDFReal (s θ) v y‖ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    intro θ
    have h_nonneg : 0 ≤ gaussianPDFReal (s θ) v y := gaussianPDFReal_nonneg _ _ _
    have h_le : gaussianPDFReal (s θ) v y ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
      rw [gaussianPDFReal_def (s θ) v]
      have h_exp_le_one : Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
        have h_nonpos : -(y - s θ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
          refine div_nonpos_of_nonpos_of_nonneg ?_ (by linarith)
          have h_sq_nonneg : 0 ≤ (y - s θ) ^ 2 := pow_two_nonneg _
          linarith
        exact (Real.exp_le_one_iff.mpr h_nonpos)
      have h_inv_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h := mul_le_mul_of_nonneg_left h_exp_le_one h_inv_nonneg
      simpa [mul_one] using h
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le
  have h_meas_gauss : Measurable (fun θ => gaussianPDFReal (s θ) v y) := by
    have h_cont : Continuous (fun (μ : ℝ) => gaussianPDFReal μ v y) := by
      continuity
    exact h_cont.measurable.comp hs
  have h_aestrongly : AEStronglyMeasurable (fun θ => gaussianPDFReal (s θ) v y) π :=
    h_meas_gauss.aemeasurable.aestronglyMeasurable
  have h_int_gauss : Integrable (fun θ => gaussianPDFReal (s θ) v y) π :=
    Integrable.of_bound h_aestrongly (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
      (ae_of_all _ h_bound)
  have h_int_const : Integrable (fun _ : Θ => A) π :=
    integrable_const A
  have h_pointwise : ∀ θ ∈ s0, A ≤ gaussianPDFReal (s θ) v y := by
    intro θ hθ
    dsimp [A]
    exact gaussianPDFReal_ge_far hv (hsb θ)
  calc
    π.real s0 * A = ∫ θ in s0, A ∂π := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ θ in s0, gaussianPDFReal (s θ) v y ∂π := by
      refine setIntegral_mono_on (integrableOn_const (C := A)) (h_int_gauss.integrableOn) hs0 ?_
      intro θ hθ
      exact h_pointwise θ hθ
    _ = ∫ θ, s0.indicator (fun θ => gaussianPDFReal (s θ) v y) θ ∂π := by rw [integral_indicator hs0]
    _ = normZ π c s v a y := rfl

theorem measurable_normZ [Countable α] [MeasurableSingletonClass α] (π : Measure Θ) [SFinite π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) (v : ℝ≥0) :
    Measurable (fun p : α × ℝ => normZ π c s v p.1 p.2) := by
  let F : (α × ℝ) × Θ → ℝ := fun x =>
    (c ⁻¹' {x.1.1}).indicator (fun θ' => gaussianPDFReal (s θ') v x.1.2) x.2
  have h_set : MeasurableSet {x : (α × ℝ) × Θ | c x.2 = x.1.1} :=
    measurableSet_eq_fun (hc.comp measurable_snd) (measurable_fst.comp measurable_fst)
  have hF2 : Measurable (fun (x : (α × ℝ) × Θ) => gaussianPDFReal (s x.2) v x.1.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      ((hs.comp measurable_snd).prodMk (measurable_const.prodMk (measurable_snd.comp measurable_fst)))
  have hF_eq : F = Set.indicator {x : (α × ℝ) × Θ | c x.2 = x.1.1}
    (fun x => gaussianPDFReal (s x.2) v x.1.2) := by
    ext x
    simp [F, Set.indicator]
    by_cases h : c x.2 = x.1.1
    · simp [h, Set.mem_preimage, Set.mem_singleton_iff]
    · simp [h, Set.mem_preimage, Set.mem_singleton_iff]
  have hF : StronglyMeasurable F := by
    rw [hF_eq]
    exact (Measurable.indicator hF2 h_set).stronglyMeasurable
  have h_eq : (fun p : α × ℝ => normZ π c s v p.1 p.2) = fun p => ∫ θ, F (p, θ) ∂π := by
    ext p
    simp [normZ, F]
  rw [h_eq]
  exact hF.integral_prod_right'.measurable

/-- The mass of the likelihood is the normaliser: `∫⁻ lik_{a,y} dπ = Z(a, y)`. -/
theorem lintegral_lik [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) (v : ℝ≥0) (a : α) (y : ℝ) :
    ∫⁻ θ, lik c s v a y θ ∂π = ENNReal.ofReal (normZ π c s v a y) := by
  have h_lik_eq : lik c s v a y = fun θ =>
      ENNReal.ofReal ((c ⁻¹' {a}).indicator (fun θ => gaussianPDFReal (s θ) v y) θ) := by
    ext θ
    by_cases hθ : θ ∈ c ⁻¹' {a}
    · simp [lik, ProbabilityTheory.gaussianPDF_def, hθ]
    · simp [lik, ProbabilityTheory.gaussianPDF_def, hθ]
  rw [h_lik_eq]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · -- integrability of the indicator times gaussianPDFReal
    have h_measSet : MeasurableSet (c ⁻¹' {a}) := hc (measurableSet_singleton a)
    have h_int_gaussian : Integrable (fun θ => gaussianPDFReal (s θ) v y) π := by
      have h_bound : ∀ θ, |gaussianPDFReal (s θ) v y| ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
        intro θ
        have h_nonneg : 0 ≤ gaussianPDFReal (s θ) v y := gaussianPDFReal_nonneg _ _ _
        have h_le : gaussianPDFReal (s θ) v y ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
          rw [ProbabilityTheory.gaussianPDFReal]
          have h_exp : Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
            have h_nonpos : -(y - s θ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
              have h_num_nonpos : -(y - s θ) ^ 2 ≤ 0 := by
                have h_sq_nonneg : 0 ≤ (y - s θ) ^ 2 := pow_two_nonneg _
                linarith
              have h_denom_nonneg : 0 ≤ 2 * (v : ℝ) := by
                have hv_nonneg : 0 ≤ (v : ℝ) := NNReal.coe_nonneg _
                nlinarith
              exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos h_denom_nonneg
            have h_exp' : Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ))) ≤ Real.exp (0 : ℝ) :=
              Real.exp_le_exp.mpr h_nonpos
            simpa using h_exp'
          by_cases hv : (v : ℝ) = 0
          · have hzero : Real.sqrt (2 * Real.pi * (v : ℝ)) = 0 := by
              simp [hv]
            simp [hzero]
          · have hvpos : 0 < (v : ℝ) := by
              have hv_nonneg : 0 ≤ (v : ℝ) := NNReal.coe_nonneg _
              exact Ne.lt_of_le (Ne.symm hv) hv_nonneg
            have h_nonneg_sqrt : 0 ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := Real.sqrt_nonneg _
            have h_inv_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := inv_nonneg.mpr h_nonneg_sqrt
            calc
              (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - s θ) ^ 2 / (2 * (v : ℝ)))
                  ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left h_exp h_inv_nonneg
              _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by simp
        rw [abs_of_nonneg h_nonneg]
        exact h_le
      have h_ae_strongly_measurable : AEStronglyMeasurable (fun θ => gaussianPDFReal (s θ) v y) π := by
        have h_meas : Measurable (fun θ => gaussianPDFReal (s θ) v y) :=
          ProbabilityTheory.measurable_uncurry_gaussianPDFReal.comp
            (Measurable.prod (f := fun θ => (s θ, v, y)) hs
              (Measurable.prod (f := fun _ => (v, y)) measurable_const measurable_const))
        exact h_meas.aestronglyMeasurable
      exact Integrable.of_bound h_ae_strongly_measurable _ (ae_of_all _ h_bound)
    exact h_int_gaussian.indicator h_measSet
  · -- nonnegativity almost everywhere
    refine ae_of_all _ (fun θ => Set.indicator_nonneg ?_ _)
    intro θ' hθ'
    exact gaussianPDFReal_nonneg _ _ _

/-- The log-ratio of two Gaussian densities of the same variance, in mean: `E_z ln(φ_μ(μ + σz)/φ_ĉ(μ + σz)) = (μ - ĉ)²/(2σ²)`. -/
theorem integral_log_gauss_ratio {sc : ℝ} (hsc : sc ≠ 0) (μ ĉ : ℝ) :
    ∫ z, (Real.log (gaussianPDFReal μ (noiseVar sc) (μ + sc * z)) -
        Real.log (gaussianPDFReal ĉ (noiseVar sc) (μ + sc * z))) ∂gaussianReal 0 1 = (μ - ĉ) ^ 2 / (2 * sc ^ 2) := by
  set v := noiseVar sc with hv_def
  have hv_ne_zero : v ≠ 0 := by
    rw [hv_def, noiseVar]
    intro h
    apply hsc
    have := congrArg Subtype.val h
    simpa using this
  have hpos_μ (x : ℝ) : gaussianPDFReal μ v x > 0 := gaussianPDFReal_pos μ v x hv_ne_zero
  have hpos_ĉ (x : ℝ) : gaussianPDFReal ĉ v x > 0 := gaussianPDFReal_pos ĉ v x hv_ne_zero
  have hv_eq : (v : ℝ) = sc ^ 2 := rfl
  have h_log_diff (z : ℝ) : Real.log (gaussianPDFReal μ v (μ + sc * z)) -
      Real.log (gaussianPDFReal ĉ v (μ + sc * z)) =
      ((μ - ĉ) ^ 2) / (2 * sc ^ 2) + ((μ - ĉ) / sc) * z := by
    set y := μ + sc * z
    have h_log_ratio : Real.log (gaussianPDFReal μ v y) - Real.log (gaussianPDFReal ĉ v y) =
        ((y - ĉ) ^ 2 - (y - μ) ^ 2) / (2 * (v : ℝ)) := by
      rw [gaussianPDFReal_def μ v, gaussianPDFReal_def ĉ v]
      simp only
      rw [Real.log_mul, Real.log_mul]
      · rw [Real.log_exp, Real.log_exp]
        ring
      · positivity
      · positivity
      · positivity
      · positivity
    rw [h_log_ratio]
    dsimp [y]
    rw [hv_eq]
    field_simp [hsc]
    ring
  have h_int_const : Integrable (fun _ : ℝ => ((μ - ĉ) ^ 2) / (2 * sc ^ 2)) (gaussianReal 0 1) :=
    integrable_const _
  have h_int_id : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    rw [← memLp_one_iff_integrable]
    exact memLp_id_gaussianReal 1
  calc
    ∫ z, (Real.log (gaussianPDFReal μ (noiseVar sc) (μ + sc * z)) -
        Real.log (gaussianPDFReal ĉ (noiseVar sc) (μ + sc * z))) ∂gaussianReal 0 1
        = ∫ z, (Real.log (gaussianPDFReal μ v (μ + sc * z)) -
            Real.log (gaussianPDFReal ĉ v (μ + sc * z))) ∂gaussianReal 0 1 := by
      simp [hv_def]
    _ = ∫ z, (((μ - ĉ) ^ 2) / (2 * sc ^ 2) + ((μ - ĉ) / sc) * z) ∂gaussianReal 0 1 := by
      refine integral_congr_ae ?_
      filter_upwards with z
      rw [h_log_diff z]
    _ = (∫ z, ((μ - ĉ) ^ 2) / (2 * sc ^ 2) ∂gaussianReal 0 1) +
        (∫ z, ((μ - ĉ) / sc) * z ∂gaussianReal 0 1) := by
      rw [integral_add h_int_const (h_int_id.const_mul ((μ - ĉ) / sc))]
    _ = (((μ - ĉ) ^ 2) / (2 * sc ^ 2)) * (∫ z, (1 : ℝ) ∂gaussianReal 0 1) +
        ((μ - ĉ) / sc) * (∫ z, z ∂gaussianReal 0 1) := by
      rw [integral_const ((μ - ĉ) ^ 2 / (2 * sc ^ 2)), integral_const_mul ((μ - ĉ) / sc)]
      simp
    _ = (((μ - ĉ) ^ 2) / (2 * sc ^ 2)) * 1 + ((μ - ĉ) / sc) * (0 : ℝ) := by
      simp [integral_id_gaussianReal]
    _ = (μ - ĉ) ^ 2 / (2 * sc ^ 2) := by ring

/-- Tonelli for a round: the tip and the noise, read through the answer and the observation, as an integral over the
observation of a sum over the answers. -/
theorem lintegral_obs_noise [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [SFinite π] {c : Θ → α}
    {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0) {G : Θ × α × ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ θ, ∫⁻ z, G (θ, c θ, s θ + sc * z) ∂gaussianReal 0 1 ∂π =
      ∫⁻ y, ∑ a, ∫⁻ θ, lik c s (noiseVar sc) a y θ * G (θ, a, y) ∂π := by
  rw [← lintegral_obs π hc hs (noiseVar_ne_zero hsc) hG]
  refine lintegral_congr fun θ => ?_
  exact lintegral_gauss_affine (s θ) sc (hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

/-- The posterior lemma for one round with the standard noise: the tip and the noise against the tip drawn again from
the
posterior of the answer and of the observation. -/
theorem lintegral_bayes_noise [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π]
    {c : Θ → α} {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0)
    {G : Θ × α × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ, ∫⁻ z, G (θ, c θ, s θ + sc * z) ∂gaussianReal 0 1 ∂π =
      ∫⁻ θ, ∫⁻ z, ∫⁻ θ', G (θ', c θ, s θ + sc * z) ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z))
        ∂gaussianReal 0 1 ∂π := by
  have hΦ := measurable_lintegral_bayesUpd π hc hs (noiseVar sc) hG
  have e1 : ∀ θ, ∫⁻ z, G (θ, c θ, s θ + sc * z) ∂gaussianReal 0 1 =
      ∫⁻ y, G (θ, c θ, y) ∂gaussianReal (s θ) (noiseVar sc) := fun θ =>
    lintegral_gauss_affine (s θ) sc (f := fun y => G (θ, c θ, y))
      (hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have e2 : ∀ θ, ∫⁻ z, ∫⁻ θ', G (θ', c θ, s θ + sc * z)
        ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1 =
      ∫⁻ y, ∫⁻ θ', G (θ', c θ, y) ∂bayesUpd π (lik c s (noiseVar sc) (c θ) y)
        ∂gaussianReal (s θ) (noiseVar sc) := fun θ =>
    lintegral_gauss_affine (s θ) sc
      (f := fun y => ∫⁻ θ', G (θ', c θ, y) ∂bayesUpd π (lik c s (noiseVar sc) (c θ) y))
      (hΦ.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_congr e1, lintegral_congr e2]
  exact bayes_step π hc hs (noiseVar_ne_zero hsc) hG

/-- The information density is jointly measurable. -/
theorem measurable_infoDens [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [SFinite π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) (sc : ℝ) :
    Measurable (fun p : Θ × ℝ => infoDens π c s sc p.1 p.2) := by
  have hy : Measurable (fun p : Θ × ℝ => s p.1 + sc * p.2) :=
    (hs.comp measurable_fst).add (measurable_const.mul measurable_snd)
  have hZ : Measurable (fun p : Θ × ℝ => normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) :=
    (measurable_normZ π hc hs (noiseVar sc)).comp ((hc.comp measurable_fst).prodMk hy)
  have hφ : Measurable (fun p : Θ × ℝ => gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) :=
    measurable_uncurry_gaussianPDFReal.comp ((hs.comp measurable_fst).prodMk (measurable_const.prodMk hy))
  unfold infoDens
  exact Real.measurable_log.comp (hφ.div hZ)

/-- Almost every tip lies in a cell of positive mass. -/
theorem ae_pos_cell [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α}
    (hc : Measurable c) : ∀ᵐ θ ∂π, 0 < π.real (c ⁻¹' {c θ}) := by
  rw [ae_iff (p := fun θ => 0 < π.real (c ⁻¹' {c θ}))]
  have h_nonneg : ∀ θ, 0 ≤ π.real (c ⁻¹' {c θ}) := fun _ => measureReal_nonneg
  have h_eq_zero : {θ | ¬ 0 < π.real (c ⁻¹' {c θ})} = {θ | π.real (c ⁻¹' {c θ}) = 0} := by
    ext θ; constructor
    · intro h; exact le_antisymm (not_lt.mp h) (h_nonneg θ)
    · intro h; have hx : π.real (c ⁻¹' {c θ}) = 0 := h; simpa [Set.mem_setOf_eq, hx]
  rw [h_eq_zero]
  have h_fin : ∀ θ, π (c ⁻¹' {c θ}) ≠ ∞ := fun θ => measure_ne_top π _
  have h_real_zero_iff : ∀ θ, π.real (c ⁻¹' {c θ}) = 0 ↔ π (c ⁻¹' {c θ}) = 0 := fun θ =>
    measureReal_eq_zero_iff (h_fin θ)
  have h_set_eq : {θ | π.real (c ⁻¹' {c θ}) = 0} = c ⁻¹' {a | π (c ⁻¹' {a}) = 0} := by
    ext θ; simp [h_real_zero_iff θ]
  rw [h_set_eq]
  let B : Set α := {a | π (c ⁻¹' {a}) = 0}
  have hB_finite : B.Finite := by
    have : Finite α := inferInstance
    exact Set.toFinite B
  have h_union : c ⁻¹' B = ⋃ a ∈ B, c ⁻¹' {a} := by
    ext θ; simp [B, eq_comm]
  rw [h_union]
  have hB_countable : B.Countable := hB_finite.countable
  rw [measure_biUnion_null_iff hB_countable]
  intro a ha
  exact ha

/-- The information density at a tip of a cell of positive mass, with a bounded signal:
`-z²/2 ≤ ln(φ_σ(σz)/Z) ≤ -ln p + 4 S₀²/σ² + z²`. -/
theorem infoDens_bounds [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ} (hsc : sc ≠ 0)
    (θ : Θ) (z : ℝ) (hp : 0 < π.real (c ⁻¹' {c θ})) :
    -(z ^ 2 / 2) ≤ infoDens π c s sc θ z ∧
      infoDens π c s sc θ z ≤ -Real.log (π.real (c ⁻¹' {c θ})) + 4 * S₀ ^ 2 / sc ^ 2 + z ^ 2 := by
  have hv : noiseVar sc ≠ 0 := noiseVar_ne_zero hsc
  have hvr : ((noiseVar sc : ℝ≥0) : ℝ) = sc ^ 2 := rfl
  have hsc2 : 0 < sc ^ 2 := by positivity
  have hp1 : π.real (c ⁻¹' {c θ}) ≤ 1 := measureReal_le_one
  have hS0 : 0 ≤ S₀ := (abs_nonneg _).trans (hsb θ)
  have hφ : 0 < gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z) := gaussianPDFReal_pos _ _ _ hv
  have hlogφ : Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) =
      -(Real.log (2 * Real.pi * (noiseVar sc : ℝ)) / 2) - z ^ 2 / 2 := by
    rw [log_gaussianPDFReal _ hv]
    congr 1
    rw [hvr]
    field_simp
    ring
  have hsq : 0 < Real.sqrt (2 * Real.pi * (noiseVar sc : ℝ)) := Real.sqrt_pos.2 (by rw [hvr]; positivity)
  have hZle := normZ_le π hc hs hv (c θ) (s θ + sc * z)
  have hZge := le_normZ π hc hs hsb hv (c θ) (s θ + sc * z)
  have hZ : 0 < normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) := lt_of_lt_of_le (by positivity) hZge
  have hlogsq : Real.log (Real.sqrt (2 * Real.pi * (noiseVar sc : ℝ)))⁻¹ =
      -(Real.log (2 * Real.pi * (noiseVar sc : ℝ)) / 2) := by
    rw [Real.log_inv, Real.log_sqrt (by rw [hvr]; positivity)]
  have hup : Real.log (normZ π c s (noiseVar sc) (c θ) (s θ + sc * z)) ≤
      Real.log (π.real (c ⁻¹' {c θ})) - Real.log (2 * Real.pi * (noiseVar sc : ℝ)) / 2 := by
    have h := Real.log_le_log hZ hZle
    rw [Real.log_mul hp.ne' (inv_ne_zero hsq.ne'), hlogsq] at h
    linarith
  have hlo : Real.log (π.real (c ⁻¹' {c θ})) - Real.log (2 * Real.pi * (noiseVar sc : ℝ)) / 2 -
      (|s θ + sc * z| + S₀) ^ 2 / (2 * (noiseVar sc : ℝ)) ≤
      Real.log (normZ π c s (noiseVar sc) (c θ) (s θ + sc * z)) := by
    have h := Real.log_le_log (by positivity) hZge
    rw [Real.log_mul hp.ne' (by positivity), Real.log_mul (inv_ne_zero hsq.ne') (Real.exp_pos _).ne', hlogsq,
      Real.log_exp] at h
    have e : -(|s θ + sc * z| + S₀) ^ 2 / (2 * (noiseVar sc : ℝ)) =
        -((|s θ + sc * z| + S₀) ^ 2 / (2 * (noiseVar sc : ℝ))) := by ring
    linarith
  have hlogp : Real.log (π.real (c ⁻¹' {c θ})) ≤ 0 := Real.log_nonpos hp.le hp1
  have hy : |s θ + sc * z| ≤ S₀ + |sc * z| := (abs_add_le _ _).trans (by linarith [hsb θ])
  have hQ : (|s θ + sc * z| + S₀) ^ 2 / (2 * (noiseVar sc : ℝ)) ≤ 4 * S₀ ^ 2 / sc ^ 2 + z ^ 2 := by
    have h1 : (|s θ + sc * z| + S₀) ^ 2 ≤ (2 * S₀ + |sc * z|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 : |sc * z| ^ 2 = sc ^ 2 * z ^ 2 := by rw [sq_abs, mul_pow]
    have h3 : (|s θ + sc * z| + S₀) ^ 2 ≤ 8 * S₀ ^ 2 + 2 * (sc ^ 2 * z ^ 2) := by
      nlinarith [sq_nonneg (2 * S₀ - |sc * z|)]
    rw [hvr, div_le_iff₀ (by positivity)]
    have e : (4 * S₀ ^ 2 / sc ^ 2 + z ^ 2) * (2 * sc ^ 2) = 8 * S₀ ^ 2 + 2 * (sc ^ 2 * z ^ 2) := by
      field_simp
      ring
    linarith
  have hI : infoDens π c s sc θ z = Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) -
      Real.log (normZ π c s (noiseVar sc) (c θ) (s θ + sc * z)) := by
    unfold infoDens
    exact Real.log_div hφ.ne' hZ.ne'
  rw [hI, hlogφ]
  constructor
  · linarith
  · nlinarith [sq_nonneg z]

/-- The information density is integrable over the tip and the noise. -/
theorem integrable_infoDens [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ}
    (hsc : sc ≠ 0) :
    Integrable (fun p : Θ × ℝ => infoDens π c s sc p.1 p.2) (π.prod (gaussianReal 0 1)) := by
  have hS : 0 ≤ 4 * S₀ ^ 2 / sc ^ 2 + ∑ a, |Real.log (π.real (c ⁻¹' {a}))| :=
    add_nonneg (by positivity) (Finset.sum_nonneg fun a _ => abs_nonneg _)
  have hae : ∀ᵐ p ∂π.prod (gaussianReal 0 1), ‖infoDens π c s sc p.1 p.2‖ ≤
      (4 * S₀ ^ 2 / sc ^ 2 + ∑ a, |Real.log (π.real (c ⁻¹' {a}))|) + 2 * p.2 ^ 2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := π) (ν := gaussianReal 0 1)).ae
      (ae_pos_cell π hc)] with p hp
    obtain ⟨h1, h2⟩ := infoDens_bounds π hc hs hsb hsc p.1 p.2 hp
    have h3 : -Real.log (π.real (c ⁻¹' {c p.1})) ≤ ∑ a, |Real.log (π.real (c ⁻¹' {a}))| :=
      (neg_le_abs _).trans (Finset.single_le_sum (f := fun a => |Real.log (π.real (c ⁻¹' {a}))|)
        (fun a _ => abs_nonneg _) (Finset.mem_univ (c p.1)))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg p.2]
  have hz : Integrable (fun p : Θ × ℝ => p.2 ^ 2) (π.prod (gaussianReal 0 1)) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.comp_snd π
  exact ((integrable_const _).add (hz.const_mul 2)).mono'
    (measurable_infoDens π hc hs sc).aestronglyMeasurable hae

/-- Gibbs on the observation, cell by cell: `E p_A φ_{ĉ_A}(Y)/Z(A, Y) ≤ 1`. -/
theorem lintegral_ratio_le_one [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0) (ĉ : α → ℝ) :
    ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z) /
      normZ π c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π ≤ 1 := by
  have hv : noiseVar sc ≠ 0 := noiseVar_ne_zero hsc
  have hZm := measurable_normZ π hc hs (noiseVar sc)
  have hpm : Measurable (fun a : α => π.real (c ⁻¹' {a})) := measurable_of_countable _
  have hcm : Measurable ĉ := measurable_of_countable _
  have hG : Measurable (fun q : Θ × α × ℝ => ENNReal.ofReal (π.real (c ⁻¹' {q.2.1}) *
      gaussianPDFReal (ĉ q.2.1) (noiseVar sc) q.2.2 / normZ π c s (noiseVar sc) q.2.1 q.2.2)) :=
    (((hpm.comp (measurable_fst.comp measurable_snd)).mul (measurable_uncurry_gaussianPDFReal.comp
      ((hcm.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd))))).div
      (hZm.comp measurable_snd)).ennreal_ofReal
  have hgm : ∀ a, Measurable (fun y => ENNReal.ofReal (π.real (c ⁻¹' {a})) * gaussianPDF (ĉ a) (noiseVar sc) y) :=
    fun a => (measurable_gaussianPDF _ _).const_mul _
  calc ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z) /
        normZ π c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π
      = ∫⁻ y, ∑ a, ∫⁻ θ, lik c s (noiseVar sc) a y θ * ENNReal.ofReal (π.real (c ⁻¹' {a}) *
          gaussianPDFReal (ĉ a) (noiseVar sc) y / normZ π c s (noiseVar sc) a y) ∂π :=
        lintegral_obs_noise π hc hs hsc hG
    _ ≤ ∫⁻ y, ∑ a, ENNReal.ofReal (π.real (c ⁻¹' {a})) * gaussianPDF (ĉ a) (noiseVar sc) y := by
        refine lintegral_mono fun y => Finset.sum_le_sum fun a _ => ?_
        have hl : Measurable (fun θ => lik c s (noiseVar sc) a y θ) :=
          (measurable_lik hc hs (noiseVar sc)).comp ((measurable_const (a := (a, y))).prodMk measurable_id)
        have hZ0 : 0 ≤ normZ π c s (noiseVar sc) a y :=
          integral_nonneg fun θ => Set.indicator_nonneg (fun θ _ => gaussianPDFReal_nonneg _ _ _) θ
        have hpφ : 0 ≤ π.real (c ⁻¹' {a}) * gaussianPDFReal (ĉ a) (noiseVar sc) y :=
          mul_nonneg measureReal_nonneg (gaussianPDFReal_nonneg _ _ _)
        rw [lintegral_mul_const _ hl, lintegral_lik π hc hs (noiseVar sc) a y, ← ENNReal.ofReal_mul hZ0, gaussianPDF,
          ← ENNReal.ofReal_mul measureReal_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases hZ0.eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul]
          exact hpφ
        · rw [mul_div_cancel₀ _ hpos.ne']
    _ = ∑ a, ENNReal.ofReal (π.real (c ⁻¹' {a})) * ∫⁻ y, gaussianPDF (ĉ a) (noiseVar sc) y := by
        rw [lintegral_finsetSum _ fun a _ => hgm a]
        exact Finset.sum_congr rfl fun a _ => lintegral_const_mul _ (measurable_gaussianPDF _ _)
    _ = ∑ a, π (c ⁻¹' {a}) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_gaussianPDF_eq_one _ hv, mul_one, ofReal_measureReal (measure_ne_top _ _)]
    _ = 1 := by
        rw [sum_measure_preimage_singleton _ fun a _ => hc (measurableSet_singleton a), Finset.coe_univ,
          Set.preimage_univ, measure_univ]

/-- `E Z(A, Y)/φ_σ(σ z) ≤ 1`. -/
theorem lintegral_inv_ratio_le_one [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ)
    [IsProbabilityMeasure π] {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {sc : ℝ}
    (hsc : sc ≠ 0) :
    ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) /
      gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π ≤ 1 := by
  have hv : noiseVar sc ≠ 0 := noiseVar_ne_zero hsc
  have hZm := measurable_normZ π hc hs (noiseVar sc)
  have hG : Measurable (fun q : Θ × α × ℝ => ENNReal.ofReal (normZ π c s (noiseVar sc) q.2.1 q.2.2 /
      gaussianPDFReal (s q.1) (noiseVar sc) q.2.2)) :=
    ((hZm.comp measurable_snd).div (measurable_uncurry_gaussianPDFReal.comp ((hs.comp measurable_fst).prodMk
      (measurable_const.prodMk (measurable_snd.comp measurable_snd))))).ennreal_ofReal
  have hZy : ∀ a, Measurable (fun y => ENNReal.ofReal (normZ π c s (noiseVar sc) a y)) := fun a =>
    (hZm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hZa : ∀ a, ∫⁻ y, ENNReal.ofReal (normZ π c s (noiseVar sc) a y) = π (c ⁻¹' {a}) := by
    intro a
    have hl : Measurable (fun p : ℝ × Θ => lik c s (noiseVar sc) a p.1 p.2) :=
      (measurable_lik hc hs (noiseVar sc)).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    calc ∫⁻ y, ENNReal.ofReal (normZ π c s (noiseVar sc) a y)
        = ∫⁻ y, ∫⁻ θ, lik c s (noiseVar sc) a y θ ∂π :=
          lintegral_congr fun y => (lintegral_lik π hc hs (noiseVar sc) a y).symm
      _ = ∫⁻ θ, (∫⁻ y, lik c s (noiseVar sc) a y θ) ∂π := lintegral_lintegral_swap hl.aemeasurable
      _ = ∫⁻ θ, (c ⁻¹' {a}).indicator 1 θ ∂π := by
          refine lintegral_congr fun θ => ?_
          by_cases hθ : θ ∈ c ⁻¹' {a}
          · simp only [lik, Set.indicator_of_mem hθ, Pi.one_apply]
            exact lintegral_gaussianPDF_eq_one _ hv
          · simp only [lik, Set.indicator_of_notMem hθ, lintegral_zero]
      _ = π (c ⁻¹' {a}) := lintegral_indicator_one (hc (measurableSet_singleton a))
  calc ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) /
        gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π
      = ∫⁻ y, ∑ a, ∫⁻ θ, lik c s (noiseVar sc) a y θ * ENNReal.ofReal (normZ π c s (noiseVar sc) a y /
          gaussianPDFReal (s θ) (noiseVar sc) y) ∂π := lintegral_obs_noise π hc hs hsc hG
    _ = ∫⁻ y, ∑ a, ENNReal.ofReal (normZ π c s (noiseVar sc) a y) * π (c ⁻¹' {a}) := by
        refine lintegral_congr fun y => Finset.sum_congr rfl fun a _ => ?_
        rw [← lintegral_indicator_const (hc (measurableSet_singleton a))]
        refine lintegral_congr fun θ => ?_
        by_cases hθ : θ ∈ c ⁻¹' {a}
        · have hφ : 0 < gaussianPDFReal (s θ) (noiseVar sc) y := gaussianPDFReal_pos _ _ _ hv
          simp only [lik, Set.indicator_of_mem hθ, gaussianPDF]
          rw [← ENNReal.ofReal_mul hφ.le]
          congr 1
          field_simp
        · simp only [lik, Set.indicator_of_notMem hθ, zero_mul]
    _ = ∑ a, ∫⁻ y, ENNReal.ofReal (normZ π c s (noiseVar sc) a y) * π (c ⁻¹' {a}) :=
        lintegral_finsetSum _ fun a _ => (hZy a).mul_const _
    _ = ∑ a, π (c ⁻¹' {a}) * π (c ⁻¹' {a}) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_mul_const _ (hZy a), hZa]
    _ ≤ ∑ a, π (c ⁻¹' {a}) := Finset.sum_le_sum fun a _ => mul_le_of_le_one_left zero_le prob_le_one
    _ = 1 := by
        rw [sum_measure_preimage_singleton _ fun a _ => hc (measurableSet_singleton a), Finset.coe_univ,
          Set.preimage_univ, measure_univ]

/-- A nonnegative measurable function of mass at most one in the iterated lower integral is integrable on the
product, of integral at most one. -/
theorem integrable_of_lintegral_le_one {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    [SFinite μ] (ν : Measure Y) [SFinite ν] {f : X × Y → ℝ} (hf : Measurable f) (h0 : ∀ p, 0 ≤ f p)
    (h1 : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν ∂μ ≤ 1) :
    Integrable f (μ.prod ν) ∧ ∫ p, f p ∂(μ.prod ν) ≤ 1 := by
  have hmeas : AEMeasurable (fun (p : X × Y) => ENNReal.ofReal (f p)) (μ.prod ν) :=
    (ENNReal.measurable_ofReal.comp hf).aemeasurable
  have h_lintegral_finite : ∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν) < ⊤ := by
    calc
      ∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν ∂μ := by
        rw [lintegral_prod _ hmeas]
      _ ≤ 1 := h1
      _ < ⊤ := by simp
  have h_finite_integral : HasFiniteIntegral f (μ.prod ν) := by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)]
    exact h_lintegral_finite
  have h_ae_strongly_measurable : AEStronglyMeasurable f (μ.prod ν) :=
    hf.aestronglyMeasurable
  have h_integrable : Integrable f (μ.prod ν) :=
    ⟨h_ae_strongly_measurable, h_finite_integral⟩
  have h_integral_eq : ∫ p, f p ∂(μ.prod ν) = (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) h_ae_strongly_measurable
  have h_integral_le_one : ∫ p, f p ∂(μ.prod ν) ≤ 1 := by
    rw [h_integral_eq]
    have h_le : ∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν) ≤ (1 : ENNReal) := by
      calc
        ∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν ∂μ := by
          rw [lintegral_prod _ hmeas]
        _ ≤ 1 := h1
        _ = (1 : ENNReal) := by simp
    have h_val : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod ν)).toReal ≤ (1 : ENNReal).toReal :=
      (ENNReal.toReal_le_toReal (h_lintegral_finite.ne_top) (by simp)).mpr h_le
    simpa [ENNReal.toReal_one] using h_val
  exact And.intro h_integrable h_integral_le_one

/-- The iterated lower integral of a nonnegative integrable function on a product is its iterated integral. -/
theorem lintegral_ofReal_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} [SFinite μ]
    {ν : Measure Y} [SFinite ν] {f : X → Y → ℝ} (hf : Integrable (fun p : X × Y => f p.1 p.2) (μ.prod ν))
    (h0 : ∀ p : X × Y, 0 ≤ f p.1 p.2) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x y) ∂ν ∂μ = ENNReal.ofReal (∫ x, ∫ y, f x y ∂ν ∂μ) := by
  let F : X × Y → ℝ := fun p => f p.1 p.2
  have hF_int : Integrable F (μ.prod ν) := hf
  have hF_nonneg : 0 ≤ᵐ[μ.prod ν] F := ae_of_all _ h0
  have hF_aemeas : AEMeasurable (fun p : X × Y => ENNReal.ofReal (F p)) (μ.prod ν) :=
    hF_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  calc
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x y) ∂ν ∂μ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)) ∂ν ∂μ := rfl
    _ = ∫⁻ (p : X × Y), ENNReal.ofReal (F p) ∂(μ.prod ν) := by
      rw [MeasureTheory.lintegral_prod _ hF_aemeas]
    _ = ENNReal.ofReal (∫ (p : X × Y), F p ∂(μ.prod ν)) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int hF_nonneg]
    _ = ENNReal.ofReal (∫ x, ∫ y, f x y ∂ν ∂μ) := by
      rw [MeasureTheory.integral_integral hF_int]

theorem integral_ratio_le_one [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0) (ĉ : α → ℝ) :
    Integrable (fun p : Θ × ℝ => π.real (c ⁻¹' {c p.1}) *
        gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
        normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) (π.prod (gaussianReal 0 1)) ∧
      ∫ p, π.real (c ⁻¹' {c p.1}) * gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
        normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) ∂(π.prod (gaussianReal 0 1)) ≤ 1 := by
  set f : Θ × ℝ → ℝ := fun p => π.real (c ⁻¹' {c p.1}) *
    gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
    normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) with hf_def
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    have hπreal : 0 ≤ π.real (c ⁻¹' {c p.1}) := measureReal_nonneg
    have hgauss : 0 ≤ gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) :=
      gaussianPDFReal_nonneg _ _ _
    have hnormZ_nonneg : 0 ≤ normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) := by
      dsimp [normZ]
      refine integral_nonneg (fun θ => ?_)
      refine Set.indicator_nonneg (fun θ hθ => ?_) θ
      exact gaussianPDFReal_nonneg _ _ _
    have hnum : 0 ≤ π.real (c ⁻¹' {c p.1}) *
        gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) :=
      mul_nonneg hπreal hgauss
    rw [hf_def]
    exact div_nonneg hnum hnormZ_nonneg
  have h_meas_ĉ : Measurable ĉ := measurable_of_finite _
  have h_meas_c : Measurable (fun p : Θ × ℝ => c p.1) := hc.comp measurable_fst
  have h_meas_s' : Measurable (fun p : Θ × ℝ => s p.1) := hs.comp measurable_fst
  have h_triple : Measurable (fun p : Θ × ℝ => ((ĉ (c p.1) : ℝ), (noiseVar sc : ℝ≥0), (s p.1 + sc * p.2 : ℝ))) := by
    refine Measurable.prodMk (h_meas_ĉ.comp h_meas_c) ?_
    refine Measurable.prodMk (measurable_const : Measurable (fun (_ : Θ × ℝ) => (noiseVar sc : ℝ≥0))) ?_
    exact Measurable.add h_meas_s' (Measurable.mul measurable_const measurable_snd)
  have h_meas_gauss : Measurable (fun p : Θ × ℝ =>
      gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2)) := by
    have h_comp := measurable_uncurry_gaussianPDFReal.comp h_triple
    convert h_comp using 1
    ext p
    simp
  have h_meas_arg : Measurable (fun p : Θ × ℝ => (c p.1, s p.1 + sc * p.2)) :=
    Measurable.prodMk h_meas_c (Measurable.add h_meas_s' (Measurable.mul measurable_const measurable_snd))
  have h_meas_normZ : Measurable (fun p : Θ × ℝ => normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) := by
    have h_comp := (measurable_normZ π hc hs (noiseVar sc)).comp h_meas_arg
    convert h_comp using 1
    ext p
    simp
  have h_meas_πreal_fun : Measurable (fun (a : α) => π.real (c ⁻¹' {a})) :=
    measurable_of_finite _
  have h_meas_πreal : Measurable (fun p : Θ × ℝ => π.real (c ⁻¹' {c p.1})) :=
    h_meas_πreal_fun.comp h_meas_c
  have hf_meas : Measurable f := by
    rw [hf_def]
    exact Measurable.div (Measurable.mul h_meas_πreal h_meas_gauss) h_meas_normZ
  have h_bound : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂(gaussianReal 0 1) ∂π ≤ 1 := by
    rw [hf_def]
    exact lintegral_ratio_le_one π hc hs hsc ĉ
  exact integrable_of_lintegral_le_one π (gaussianReal 0 1) hf_meas hf_nonneg h_bound

theorem integral_inv_ratio_le_one [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ)
    [IsProbabilityMeasure π] {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {sc : ℝ}
    (hsc : sc ≠ 0) :
    Integrable (fun p : Θ × ℝ => normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) /
        gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) (π.prod (gaussianReal 0 1)) ∧
      ∫ p, normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) /
        gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2) ∂(π.prod (gaussianReal 0 1)) ≤ 1 := by
  set f : Θ × ℝ → ℝ := fun p =>
    normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) /
      gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2) with hf
  have hf_meas : Measurable f := by
    unfold f
    have h_num : Measurable (fun (p : Θ × ℝ) => normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) := by
      have := measurable_normZ π hc hs (noiseVar sc)
      -- this : Measurable (fun (p : α × ℝ) => normZ π c s (noiseVar sc) p.1 p.2)
      have h_map : Measurable (fun (p : Θ × ℝ) => (c p.1, s p.1 + sc * p.2)) := by
        refine (hc.comp measurable_fst).prodMk ?_
        refine (hs.comp measurable_fst).add ?_
        exact (measurable_const_mul sc).comp measurable_snd
      -- Use `show` to guide the type inference
      show Measurable ((fun (q : α × ℝ) => normZ π c s (noiseVar sc) q.1 q.2) ∘
        (fun (p : Θ × ℝ) => (c p.1, s p.1 + sc * p.2)))
      exact this.comp h_map
    have h_denom : Measurable (fun (p : Θ × ℝ) => gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) := by
      have h_map2 : Measurable (fun (p : Θ × ℝ) => (s p.1, noiseVar sc, s p.1 + sc * p.2)) := by
        refine Measurable.prodMk (Measurable.comp hs measurable_fst)
          (Measurable.prodMk (measurable_const : Measurable (fun (_ : Θ × ℝ) => noiseVar sc))
            ((Measurable.comp hs measurable_fst).add ((measurable_const_mul sc).comp measurable_snd)))
      show Measurable ((fun (x : ℝ × ℝ≥0 × ℝ) => gaussianPDFReal x.1 x.2.1 x.2.2) ∘
        (fun (p : Θ × ℝ) => (s p.1, noiseVar sc, s p.1 + sc * p.2)))
      exact measurable_uncurry_gaussianPDFReal.comp h_map2
    exact h_num.div h_denom
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    rw [hf]
    refine div_nonneg ?_ (gaussianPDFReal_nonneg _ _ _)
    unfold normZ
    refine integral_nonneg ?_
    intro θ
    refine Set.indicator_nonneg (fun θ hθ => ?_) _
    exact gaussianPDFReal_nonneg _ _ _
  have h_bound : ∫⁻ (x : Θ), ∫⁻ (y : ℝ), ENNReal.ofReal (f (x, y)) ∂(gaussianReal 0 1) ∂π ≤ 1 := by
    rw [hf]
    simpa using lintegral_inv_ratio_le_one π hc hs hsc
  exact integrable_of_lintegral_le_one π (gaussianReal 0 1) hf_meas hf_nonneg h_bound

/-- An integral read through a finite answer, cell by cell. -/
theorem integral_comp_cells [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) {c : Θ → α}
    (hc : Measurable c) {f : Θ → α → ℝ} (hf : ∀ a, Integrable (fun θ => f θ a) π) :
    Integrable (fun θ => f θ (c θ)) π ∧ ∫ θ, f θ (c θ) ∂π = ∑ a, ∫ θ in c ⁻¹' {a}, f θ a ∂π := by
  classical
  have h_pointwise : (fun θ => f θ (c θ)) = fun θ => ∑ a, (c ⁻¹' {a}).indicator (fun θ => f θ a) θ := by
    ext θ
    calc
      f θ (c θ) = (∑ a, if c θ = a then f θ a else 0) := by
        rw [← Fintype.sum_ite_eq (c θ) (fun a => f θ a)]
      _ = ∑ a, (c ⁻¹' {a}).indicator (fun θ => f θ a) θ := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        by_cases h : c θ = a
        · subst h
          simp [Set.indicator_of_mem, Set.mem_preimage, Set.mem_singleton_iff]
        · simp [Set.mem_preimage, Set.mem_singleton_iff, h]
  constructor
  · rw [h_pointwise]
    refine integrable_finsetSum Finset.univ ?_
    intro a _
    exact (hf a).indicator (hc (MeasurableSet.singleton a))
  · rw [h_pointwise]
    rw [integral_finsetSum Finset.univ]
    · refine Finset.sum_congr rfl ?_
      intro a _
      rw [integral_indicator (hc (MeasurableSet.singleton a))]
    · intro a _
      exact (hf a).indicator (hc (MeasurableSet.singleton a))

/-- The mean of `-ln p_A` is the entropy of the answer. -/
theorem integral_negLog_cell [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) :
    Integrable (fun θ => -Real.log (π.real (c ⁻¹' {c θ}))) π ∧
      ∫ θ, -Real.log (π.real (c ⁻¹' {c θ})) ∂π = ansEntropy π c := by
  have h_preimage (a : α) : MeasurableSet (c ⁻¹' {a}) :=
    hc (MeasurableSet.singleton a)
  have h_f_int (a : α) : Integrable (fun (_θ : Θ) => -Real.log (π.real (c ⁻¹' {a}))) π :=
    integrable_const _
  have h_f_int' : ∀ a, Integrable (fun (θ : Θ) => (-Real.log (π.real (c ⁻¹' {a}))) : Θ → ℝ) π :=h_f_int
  have h_eq : (fun θ => -Real.log (π.real (c ⁻¹' {c θ}))) = fun θ =>
      ∑ a, (c ⁻¹' {a}).indicator (fun (_θ : Θ) => -Real.log (π.real (c ⁻¹' {a}))) θ := by
    ext θ
    classical
      simp [Fintype.sum_ite_eq (c θ) (fun a => -Real.log (π.real (c ⁻¹' {a}))), Set.indicator, Set.mem_preimage]
  have h_int (a : α) : Integrable (fun θ => (c ⁻¹' {a}).indicator (fun (_θ : Θ) => -Real.log (π.real (c ⁻¹' {a}))) θ) π :=
    (h_f_int a).indicator (h_preimage a)
  constructor
  · rw [h_eq]
    exact integrable_finsetSum Finset.univ fun a _ => h_int a
  · rw [h_eq]
    calc
      ∫ θ, (∑ a, (c ⁻¹' {a}).indicator (fun (_θ : Θ) => -Real.log (π.real (c ⁻¹' {a}))) θ) ∂π
          = ∑ a, ∫ θ, (c ⁻¹' {a}).indicator (fun (_θ : Θ) => -Real.log (π.real (c ⁻¹' {a}))) θ ∂π := by
        rw [integral_finsetSum Finset.univ fun a _ => h_int a]
      _ = ∑ a, ∫ θ in c ⁻¹' {a}, (-Real.log (π.real (c ⁻¹' {a}))) ∂π := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_indicator (h_preimage a)]
      _ = ∑ a, ((-Real.log (π.real (c ⁻¹' {a}))) * (π.real (c ⁻¹' {a}))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ = ∑ a, Real.negMulLog (π.real (c ⁻¹' {a})) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        dsimp [Real.negMulLog]
        ring
      _ = ansEntropy π c := rfl

/-- The log-ratio of the Gaussian densities centred at the signal and at `ĉ_A` is integrable. -/
theorem integrable_gauss_ratio [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ}
    (hsc : sc ≠ 0) (ĉ : α → ℝ) :
    Integrable (fun p : Θ × ℝ => Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
        Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) (π.prod (gaussianReal 0 1)) := by
  let v := noiseVar sc
  have hv : v ≠ 0 := by
    intro h
    apply hsc
    have hsq : (v : ℝ) = sc ^ 2 := rfl
    have hzero : (v : ℝ) = (0 : ℝ) := by simp [h]
    rw [hsq] at hzero
    nlinarith
  have hv_real : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  -- S₀ ≥ 0 because |s θ| ≥ 0
  have hS₀_nonneg : 0 ≤ S₀ := by
    by_cases h : Nonempty Θ
    · obtain ⟨θ⟩ := h
      have h' := hsb θ
      have h_abs_nonneg : 0 ≤ |s θ| := abs_nonneg _
      nlinarith
    · have h_empty : IsEmpty Θ := not_nonempty_iff.mp h
      have hπ_zero : π = 0 := by
        ext s hs
        have h_empty_s : s = (∅ : Set Θ) := by
          ext x
          exact ⟨fun _ => h_empty.elim x, fun hx => hx.elim⟩
        simp [h_empty_s]
      have hπ_ne_zero : π ≠ 0 := IsProbabilityMeasure.ne_zero (μ := π)
      exact absurd hπ_zero hπ_ne_zero
  -- bound for |ĉ(c θ)|
  let K := S₀ + ∑ a : α, |ĉ a|
  have hK_nonneg : 0 ≤ K := by
    have hsum : 0 ≤ ∑ a : α, |ĉ a| := Finset.sum_nonneg fun a _ => abs_nonneg _
    nlinarith
  have h_bound_ĉ (θ : Θ) : |ĉ (c θ)| ≤ ∑ a : α, |ĉ a| := by
    apply Finset.single_le_sum (f := fun a => |ĉ a|) (fun a _ => abs_nonneg _) (Finset.mem_univ (c θ))
  have h_bound_diff (θ : Θ) : |s θ - ĉ (c θ)| ≤ K := by
    calc
      |s θ - ĉ (c θ)| ≤ |s θ| + |ĉ (c θ)| := abs_sub _ _
      _ ≤ S₀ + |ĉ (c θ)| := by nlinarith [hsb θ]
      _ ≤ S₀ + ∑ a : α, |ĉ a| := by nlinarith [h_bound_ĉ θ]
      _ = K := rfl
  have h_log_diff (θ : Θ) (z : ℝ) :
      Real.log (gaussianPDFReal (s θ) v (s θ + sc * z)) -
      Real.log (gaussianPDFReal (ĉ (c θ)) v (s θ + sc * z)) =
      ((s θ - ĉ (c θ)) ^ 2) / (2 * (v : ℝ)) + (sc * (s θ - ĉ (c θ)) / (v : ℝ)) * z := by
    rw [log_gaussianPDFReal (s θ) hv (s θ + sc * z),
      log_gaussianPDFReal (ĉ (c θ)) hv (s θ + sc * z)]
    field_simp [hv_real]
    ring
  have hv_pos : 0 < (v : ℝ) := by
    have hsq : (v : ℝ) = sc ^ 2 := rfl
    rw [hsq]
    exact sq_pos_iff.mpr hsc
  -- integrability of z w.r.t. gaussianReal 0 1
  have h_int_id : Integrable id (gaussianReal 0 1) := by
    have h_mem : MemLp id (1 : ℝ≥0) (gaussianReal 0 1) := memLp_id_gaussianReal 1
    exact h_mem.integrable (by norm_num : 1 ≤ (1 : ℝ≥0∞))
  -- ĉ is measurable because α is finite with measurable singletons
  have hĉ_meas : Measurable ĉ := measurable_of_finite _
  -- A(θ) = (s θ - ĉ(c θ))² / (2v) is bounded and measurable
  have hA_meas : AEStronglyMeasurable (fun θ : Θ => ((s θ - ĉ (c θ)) ^ 2) / (2 * (v : ℝ))) π := by
    have h_meas : Measurable (fun θ : Θ => ((s θ - ĉ (c θ)) ^ 2)) :=
      ((hs.sub (hĉ_meas.comp hc)).pow_const (2 : ℕ))
    exact (h_meas.div_const (2 * (v : ℝ))).aestronglyMeasurable
  -- B(θ) = sc * (s θ - ĉ(c θ)) / v is bounded and measurable
  have hB_meas : AEStronglyMeasurable (fun θ : Θ => sc * (s θ - ĉ (c θ)) / (v : ℝ)) π := by
    have h_meas : Measurable (fun θ : Θ => sc * (s θ - ĉ (c θ))) :=
      measurable_const.mul (hs.sub (hĉ_meas.comp hc))
    exact (h_meas.div_const (v : ℝ)).aestronglyMeasurable
  -- bounds for A and B using Integrable.of_bound
  have hA_bound (θ : Θ) : ‖((s θ - ĉ (c θ)) ^ 2) / (2 * (v : ℝ))‖ ≤ K ^ 2 / (2 * (v : ℝ)) := by
    have h_nonneg : 0 ≤ ((s θ - ĉ (c θ)) ^ 2) / (2 * (v : ℝ)) := by
      refine div_nonneg (pow_two_nonneg _) (by nlinarith)
    rw [Real.norm_of_nonneg h_nonneg]
    have h_sq_le : (s θ - ĉ (c θ)) ^ 2 ≤ K ^ 2 := by
      have h_abs := h_bound_diff θ
      have h := abs_le.mp h_abs
      nlinarith
    have h_denom_nonneg : 0 ≤ 2 * (v : ℝ) := by nlinarith
    exact div_le_div_of_nonneg_right h_sq_le h_denom_nonneg
  have hB_bound (θ : Θ) : ‖sc * (s θ - ĉ (c θ)) / (v : ℝ)‖ ≤ (|sc| * K) / (v : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_mul]
    have h_abs : |s θ - ĉ (c θ)| ≤ K := h_bound_diff θ
    have hpos : 0 < (v : ℝ) := hv_pos
    rw [abs_of_pos hpos]
    have h_nonneg_abs_sc : 0 ≤ |sc| := abs_nonneg _
    have h_mul : |sc| * |s θ - ĉ (c θ)| ≤ |sc| * K :=
      mul_le_mul_of_nonneg_left h_abs h_nonneg_abs_sc
    exact (div_le_div_of_nonneg_right h_mul (by nlinarith))
  have hA_int : Integrable (fun θ : Θ => ((s θ - ĉ (c θ)) ^ 2) / (2 * (v : ℝ))) π :=
    Integrable.of_bound hA_meas (K ^ 2 / (2 * (v : ℝ))) (ae_of_all _ hA_bound)
  have hB_int : Integrable (fun θ : Θ => sc * (s θ - ĉ (c θ)) / (v : ℝ)) π :=
    Integrable.of_bound hB_meas ((|sc| * K) / (v : ℝ)) (ae_of_all _ hB_bound)
  -- lift to product measure
  have hA_prod : Integrable (fun p : Θ × ℝ => ((s p.1 - ĉ (c p.1)) ^ 2) / (2 * (v : ℝ))) (π.prod (gaussianReal 0 1)) :=
    hA_int.comp_fst (gaussianReal 0 1)
  have hBz_prod : Integrable (fun p : Θ × ℝ => (sc * (s p.1 - ĉ (c p.1)) / (v : ℝ)) * p.2) (π.prod (gaussianReal 0 1)) :=
    Integrable.mul_prod hB_int h_int_id
  -- the sum is integrable
  have h_sum : Integrable (fun p : Θ × ℝ => (((s p.1 - ĉ (c p.1)) ^ 2) / (2 * (v : ℝ))) + ((sc * (s p.1 - ĉ (c p.1)) / (v : ℝ)) * p.2)) (π.prod (gaussianReal 0 1)) :=
    Integrable.add hA_prod hBz_prod
  -- rewrite using the simplification
  have h_eq : (fun p : Θ × ℝ => Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
      Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) =
      (fun p : Θ × ℝ => (((s p.1 - ĉ (c p.1)) ^ 2) / (2 * (v : ℝ))) + ((sc * (s p.1 - ĉ (c p.1)) / (v : ℝ)) * p.2)) := by
    ext p
    simp [v, h_log_diff p.1 p.2]
  rw [h_eq]
  exact h_sum

/-- The mean log-ratio of the Gaussian densities centred at the signal and at `ĉ_A`, cell by cell. -/
theorem integral_gauss_ratio_cells [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ)
    [IsProbabilityMeasure π] {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ}
    (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ} (hsc : sc ≠ 0) (ĉ : α → ℝ) :
    ∫ p, (Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
        Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) ∂(π.prod (gaussianReal 0 1)) =
      ∑ a, (∫ θ in c ⁻¹' {a}, (s θ - ĉ a) ^ 2 ∂π) / (2 * sc ^ 2) := by
  have h_int : Integrable (fun (p : Θ × ℝ) => Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
    Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) (π.prod (gaussianReal 0 1)) :=
    integrable_gauss_ratio π hc hs hsb hsc ĉ
  rw [integral_prod _ h_int]
  have h_inner (θ : Θ) : ∫ z, (Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) -
    Real.log (gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z))) ∂(gaussianReal 0 1) =
    (s θ - ĉ (c θ)) ^ 2 / (2 * sc ^ 2) :=
    integral_log_gauss_ratio hsc (s θ) (ĉ (c θ))
  have h_inner_fun : (fun (θ : Θ) => ∫ z, (Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) -
    Real.log (gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z))) ∂(gaussianReal 0 1)) =
    (fun (θ : Θ) => (s θ - ĉ (c θ)) ^ 2 / (2 * sc ^ 2)) := by
    ext θ; exact h_inner θ
  rw [h_inner_fun]
  set f : Θ → α → ℝ := fun θ a => (s θ - ĉ a) ^ 2 / (2 * sc ^ 2) with hf
  have hf_int (a : α) : Integrable (fun (θ : Θ) => f θ a) π := by
    dsimp [f]
    have h_meas : AEStronglyMeasurable (fun (θ : Θ) => (s θ - ĉ a) ^ 2 / (2 * sc ^ 2)) π := by
      have hmeas : Measurable (fun (θ : Θ) => (s θ - ĉ a) ^ 2 / (2 * sc ^ 2)) := by
        refine Measurable.div_const ?_ (2 * sc ^ 2)
        refine (hs.sub measurable_const).pow_const (2 : ℕ)
      exact hmeas.aestronglyMeasurable
    have h_bound : ∀ᵐ θ ∂π, ‖(s θ - ĉ a) ^ 2 / (2 * sc ^ 2)‖ ≤ ((S₀ + |ĉ a|) ^ 2) / (2 * sc ^ 2) := by
      filter_upwards with θ
      have hpos : 0 < 2 * sc ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hpos]
      gcongr
      calc
        |s θ - ĉ a| ≤ |s θ| + |ĉ a| := abs_sub _ _
        _ ≤ S₀ + |ĉ a| := by gcongr; exact hsb θ
    exact Integrable.of_bound h_meas _ h_bound
  obtain ⟨_, h_eq⟩ := integral_comp_cells π hc hf_int
  rw [h_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_div]

/-- The information density split at a tip: the Gaussian log-ratio, `ln R ≤ R - 1` for the ratio `R` of
`lintegral_ratio_le_one`, and `-ln p_A`. -/
theorem infoDens_le_split [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ} (hsc : sc ≠ 0)
    (ĉ : α → ℝ) (θ : Θ) (z : ℝ) (hp : 0 < π.real (c ⁻¹' {c θ})) :
    infoDens π c s sc θ z ≤
      (Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) -
          Real.log (gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z))) +
        (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z) /
          normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) - 1) +
        -Real.log (π.real (c ⁻¹' {c θ})) := by
  set y := s θ + sc * z
  set v := noiseVar sc
  have hv_pos : 0 < v := by
    dsimp [v, noiseVar]
    have hsq : sc ^ 2 > 0 := sq_pos_iff.mpr hsc
    exact hsq
  have hv_ne_zero : v ≠ 0 := by linarith
  have hφs_pos : 0 < gaussianPDFReal (s θ) v y :=
    ProbabilityTheory.gaussianPDFReal_pos (s θ) v y hv_ne_zero
  have hφc_pos : 0 < gaussianPDFReal (ĉ (c θ)) v y :=
    ProbabilityTheory.gaussianPDFReal_pos (ĉ (c θ)) v y hv_ne_zero
  have hZ_pos : 0 < normZ π c s v (c θ) y := by
    have hineq := le_normZ π hc hs hsb hv_ne_zero (c θ) y
    have hpos_factor : 0 < π.real (c ⁻¹' {c θ}) * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(|y| + S₀) ^ 2 / (2 * v))) := by
      positivity
    by_contra! hle
    have hzero : normZ π c s v (c θ) y ≤ 0 := hle
    have hle' : π.real (c ⁻¹' {c θ}) * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(|y| + S₀) ^ 2 / (2 * v))) ≤ 0 := by
      linarith
    linarith
  have hR_pos : 0 < π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y := by
    positivity
  have h_logR_le : Real.log (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) ≤
      π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y - 1 :=
    Real.log_le_sub_one_of_pos hR_pos
  have h_identity : Real.log (gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) =
      Real.log (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) -
      Real.log (π.real (c ⁻¹' {c θ})) := by
    calc
      Real.log (gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) =
          (Real.log (π.real (c ⁻¹' {c θ})) + Real.log (gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y)) -
          Real.log (π.real (c ⁻¹' {c θ})) := by ring
      _ = Real.log (π.real (c ⁻¹' {c θ}) * (gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y)) -
          Real.log (π.real (c ⁻¹' {c θ})) := by
        rw [Real.log_mul (ne_of_gt hp) (ne_of_gt (div_pos hφc_pos hZ_pos))]
      _ = Real.log (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) -
          Real.log (π.real (c ⁻¹' {c θ})) := by ring
  calc
    infoDens π c s sc θ z = Real.log (gaussianPDFReal (s θ) v y / normZ π c s v (c θ) y) := rfl
    _ = Real.log (gaussianPDFReal (s θ) v y) - Real.log (normZ π c s v (c θ) y) := by
      rw [Real.log_div (ne_of_gt hφs_pos) (ne_of_gt hZ_pos)]
    _ = (Real.log (gaussianPDFReal (s θ) v y) - Real.log (gaussianPDFReal (ĉ (c θ)) v y)) +
        (Real.log (gaussianPDFReal (ĉ (c θ)) v y) - Real.log (normZ π c s v (c θ) y)) := by ring
    _ = (Real.log (gaussianPDFReal (s θ) v y) - Real.log (gaussianPDFReal (ĉ (c θ)) v y)) +
        Real.log (gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) := by
      rw [Real.log_div (ne_of_gt hφc_pos) (ne_of_gt hZ_pos)]
    _ = (Real.log (gaussianPDFReal (s θ) v y) - Real.log (gaussianPDFReal (ĉ (c θ)) v y)) +
        (Real.log (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y) -
         Real.log (π.real (c ⁻¹' {c θ}))) := by
      rw [h_identity]
    _ ≤ (Real.log (gaussianPDFReal (s θ) v y) - Real.log (gaussianPDFReal (ĉ (c θ)) v y)) +
        (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) v y / normZ π c s v (c θ) y - 1) -
        Real.log (π.real (c ⁻¹' {c θ})) := by
      nlinarith
    _ = (Real.log (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) -
        Real.log (gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z))) +
      (π.real (c ⁻¹' {c θ}) * gaussianPDFReal (ĉ (c θ)) (noiseVar sc) (s θ + sc * z) /
        normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) - 1) +
      -Real.log (π.real (c ⁻¹' {c θ})) := by
      simp [y, v]; ring

/-- `ln x ≥ 1 - 1/x` at a tip. -/
theorem one_sub_le_infoDens [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π] {c : Θ → α}
    (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ} (hsc : sc ≠ 0)
    (θ : Θ) (z : ℝ) (hp : 0 < π.real (c ⁻¹' {c θ})) :
    1 - normZ π c s (noiseVar sc) (c θ) (s θ + sc * z) / gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z) ≤
      infoDens π c s sc θ z := by
  set v := noiseVar sc
  set y := s θ + sc * z
  have hv : v ≠ 0 := by
    intro hzero
    apply hsc
    have : (v : ℝ) = sc ^ 2 := rfl
    have hzero' : (v : ℝ) = 0 := by simp [hzero]
    nlinarith
  have hφ : 0 < gaussianPDFReal (s θ) v y :=
    ProbabilityTheory.gaussianPDFReal_pos (s θ) v y hv
  have hZ : 0 < normZ π c s v (c θ) y := by
    have hbound := le_normZ π hc hs hsb hv (c θ) y
    have hpos : 0 < π.real (c ⁻¹' {c θ}) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(|y| + S₀) ^ 2 / (2 * (v : ℝ)))) := by
      have hsqrt : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
        apply Real.sqrt_pos.mpr
        have : 0 < (v : ℝ) := by
          have hsqpos : 0 < sc ^ 2 := sq_pos_iff.mpr hsc
          dsimp [v, noiseVar]
          exact hsqpos
        positivity
      positivity
    linarith [hbound, hpos]
  have h_ratio_pos : 0 < gaussianPDFReal (s θ) v y / normZ π c s v (c θ) y :=
    div_pos hφ hZ
  calc
    1 - normZ π c s v (c θ) y / gaussianPDFReal (s θ) v y
        = 1 - ((gaussianPDFReal (s θ) v y / normZ π c s v (c θ) y)⁻¹) := by
          field_simp [ne_of_gt hφ, ne_of_gt hZ]
    _ ≤ Real.log (gaussianPDFReal (s θ) v y / normZ π c s v (c θ) y) :=
      Real.one_sub_inv_le_log_of_pos h_ratio_pos
    _ = infoDens π c s sc θ z := by
      unfold infoDens
      simp [v, y]

/-- The entropy of the answer is at most the number of answers. -/
theorem ansEntropy_le [Fintype α] (π : Measure Θ) [IsProbabilityMeasure π] (c : Θ → α) :
    ansEntropy π c ≤ Fintype.card α := by
  rw [AdversarialBco.Lower.ansEntropy]
  calc
    ∑ a : α, Real.negMulLog (π.real (c ⁻¹' {a})) ≤ ∑ a : α, (1 - π.real (c ⁻¹' {a})) := by
      refine Finset.sum_le_sum fun a _ => ?_
      refine Real.negMulLog_le_one_sub_self (measureReal_nonneg (μ := π) (s := c ⁻¹' {a}))
    _ = (∑ _a : α, (1 : ℝ)) - (∑ a : α, π.real (c ⁻¹' {a})) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ _a : α, (1 : ℝ) := by
      refine sub_le_self ?_ (Finset.sum_nonneg fun a _ => measureReal_nonneg (μ := π))
    _ = (Fintype.card α : ℝ) := by simp
    _ = Fintype.card α := by norm_cast

/-- The quadratic term of the chain at `ĉ = 0`. -/
theorem sum_setIntegral_sq_le [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) (sc : ℝ) :
    ∑ a, (∫ θ in c ⁻¹' {a}, (s θ - 0) ^ 2 ∂π) / (2 * sc ^ 2) ≤ S₀ ^ 2 / (2 * sc ^ 2) := by
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hb : ∀ a, ∫ θ in c ⁻¹' {a}, (s θ - 0) ^ 2 ∂π ≤ π.real (c ⁻¹' {a}) * S₀ ^ 2 := by
    intro a
    calc ∫ θ in c ⁻¹' {a}, (s θ - 0) ^ 2 ∂π ≤ ∫ θ in c ⁻¹' {a}, S₀ ^ 2 ∂π := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _) (integrable_const _)
            (Filter.Eventually.of_forall fun θ => ?_)
          simp only [sub_zero]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hsb θ) 2
      _ = π.real (c ⁻¹' {a}) * S₀ ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  calc ∑ a, ∫ θ in c ⁻¹' {a}, (s θ - 0) ^ 2 ∂π ≤ ∑ a, π.real (c ⁻¹' {a}) * S₀ ^ 2 :=
        Finset.sum_le_sum fun a _ => hb a
    _ = (∑ a, π.real (c ⁻¹' {a})) * S₀ ^ 2 := by rw [Finset.sum_mul]
    _ = S₀ ^ 2 := by
        rw [sum_measureReal_preimage_singleton Finset.univ (fun a _ => hc (measurableSet_singleton a)),
          Finset.coe_univ, Set.preimage_univ, probReal_univ, one_mul]

/-- A function whose positive and negative parts have finite lower integrals is integrable. -/
theorem integral_bayes_step_aux {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞)
    (h2 : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ∞) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (-f x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (f x) with h | h
        · rw [abs_of_nonneg h]
          exact le_self_add
        · rw [abs_of_nonpos h]
          exact le_add_self
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ + ∫⁻ x, ENNReal.ofReal (-f x) ∂μ :=
        lintegral_add_left' hf.aemeasurable.ennreal_ofReal _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1.lt_top, h2.lt_top⟩

/-- The posterior lemma for one round, signed: a function of the tip, the answer and the observation, integrable at the
true
tip, has the same mean when the tip is drawn again from the posterior. -/
theorem integral_bayes_step [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0)
    {g : Θ × α × ℝ → ℝ} (hg : Measurable g)
    (hint : Integrable (fun p : Θ × ℝ => g (p.1, c p.1, s p.1 + sc * p.2)) (π.prod (gaussianReal 0 1))) :
    Integrable (fun p : Θ × ℝ => ∫ θ', g (θ', c p.1, s p.1 + sc * p.2)
        ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) (π.prod (gaussianReal 0 1)) ∧
      ∫ p, (∫ θ', g (θ', c p.1, s p.1 + sc * p.2) ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)))
          ∂(π.prod (gaussianReal 0 1)) =
        ∫ p, g (p.1, c p.1, s p.1 + sc * p.2) ∂(π.prod (gaussianReal 0 1)) := by
  have hy : Measurable (fun p : Θ × ℝ => (c p.1, s p.1 + sc * p.2)) :=
    (hc.comp measurable_fst).prodMk ((hs.comp measurable_fst).add (measurable_const.mul measurable_snd))
  have key : ∀ {G : Θ × α × ℝ → ℝ≥0∞}, Measurable G →
      ∫⁻ p, ∫⁻ θ', G (θ', c p.1, s p.1 + sc * p.2) ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))
          ∂(π.prod (gaussianReal 0 1)) =
        ∫⁻ p, G (p.1, c p.1, s p.1 + sc * p.2) ∂(π.prod (gaussianReal 0 1)) := by
    intro G hG
    have hA : Measurable (fun p : Θ × ℝ => ∫⁻ θ', G (θ', c p.1, s p.1 + sc * p.2)
        ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) :=
      (measurable_lintegral_bayesUpd π hc hs (noiseVar sc) hG).comp hy
    have hf : Measurable (fun p : Θ × ℝ => G (p.1, c p.1, s p.1 + sc * p.2)) := hG.comp (measurable_fst.prodMk hy)
    rw [lintegral_prod _ hA.aemeasurable, lintegral_prod _ hf.aemeasurable]
    exact (lintegral_bayes_noise π hc hs hsc hG).symm
  have hGp : Measurable (fun q : Θ × α × ℝ => ENNReal.ofReal (g q)) := hg.ennreal_ofReal
  have hGm : Measurable (fun q : Θ × α × ℝ => ENNReal.ofReal (-g q)) := hg.neg.ennreal_ofReal
  have hAp : Measurable (fun p : Θ × ℝ => ∫⁻ θ', ENNReal.ofReal (g (θ', c p.1, s p.1 + sc * p.2))
      ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) :=
    (measurable_lintegral_bayesUpd π hc hs (noiseVar sc) hGp).comp hy
  have hAm : Measurable (fun p : Θ × ℝ => ∫⁻ θ', ENNReal.ofReal (-g (θ', c p.1, s p.1 + sc * p.2))
      ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) :=
    (measurable_lintegral_bayesUpd π hc hs (noiseVar sc) hGm).comp hy
  have kp : ∫⁻ p, ∫⁻ θ', ENNReal.ofReal (g (θ', c p.1, s p.1 + sc * p.2))
        ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) =
      ∫⁻ p, ENNReal.ofReal (g (p.1, c p.1, s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) := key hGp
  have km : ∫⁻ p, ∫⁻ θ', ENNReal.ofReal (-g (θ', c p.1, s p.1 + sc * p.2))
        ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) =
      ∫⁻ p, ENNReal.ofReal (-g (p.1, c p.1, s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) := key hGm
  have hfp : ∫⁻ p, ENNReal.ofReal (g (p.1, c p.1, s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) ≠ ∞ :=
    hint.lintegral_lt_top.ne
  have hfm : ∫⁻ p, ENNReal.ofReal (-g (p.1, c p.1, s p.1 + sc * p.2)) ∂(π.prod (gaussianReal 0 1)) ≠ ∞ :=
    hint.neg.lintegral_lt_top.ne
  have hAp_fin := kp ▸ hfp
  have hAm_fin := km ▸ hfm
  have hae_p := ae_lt_top hAp hAp_fin
  have hae_m := ae_lt_top hAm hAm_fin
  have hIp := integrable_toReal_of_lintegral_ne_top hAp.aemeasurable hAp_fin
  have hIm := integrable_toReal_of_lintegral_ne_top hAm.aemeasurable hAm_fin
  have hFeq : (fun p : Θ × ℝ => ∫ θ', g (θ', c p.1, s p.1 + sc * p.2)
      ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) =ᵐ[π.prod (gaussianReal 0 1)]
      fun p => (∫⁻ θ', ENNReal.ofReal (g (θ', c p.1, s p.1 + sc * p.2))
          ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))).toReal -
        (∫⁻ θ', ENNReal.ofReal (-g (θ', c p.1, s p.1 + sc * p.2))
          ∂bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))).toReal := by
    filter_upwards [hae_p, hae_m] with p h1 h2
    have hgi : Integrable (fun θ' => g (θ', c p.1, s p.1 + sc * p.2))
        (bayesUpd π (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))) :=
      integral_bayes_step_aux (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable h1.ne h2.ne
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi
  refine ⟨(hIp.sub hIm).congr hFeq.symm, ?_⟩
  rw [integral_congr_ae hFeq, integral_sub hIp hIm, integral_toReal hAp.aemeasurable hae_p,
    integral_toReal hAm.aemeasurable hae_m, kp, km, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]

/-- The chain-rule lemma with the channel bound (S1): for any constants `ĉ_a`,
`J ≤ H(A) + ∑_a ∫_{c = a} (s - ĉ_a)² dπ / (2σ²)`. -/
theorem infoJ_chain [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ}
    (hsc : sc ≠ 0) (ĉ : α → ℝ) :
    infoJ π c s sc ≤ ansEntropy π c + ∑ a, (∫ θ in c ⁻¹' {a}, (s θ - ĉ a) ^ 2 ∂π) / (2 * sc ^ 2) := by
  have hI0 := integrable_infoDens π hc hs hsb hsc
  have hT1 := integrable_gauss_ratio π hc hs hsb hsc ĉ
  obtain ⟨hR, -⟩ := integral_ratio_le_one π hc hs hsc ĉ
  have hR1 := (integral_ratio_le_one π hc hs hsc ĉ).2
  obtain ⟨hT3, hT3e⟩ := integral_negLog_cell π hc
  have hT3' := hT3.comp_fst (gaussianReal 0 1)
  have hRm1 : Integrable (fun p : Θ × ℝ => π.real (c ⁻¹' {c p.1}) *
      gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
      normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) - 1) (π.prod (gaussianReal 0 1)) :=
    hR.sub (integrable_const (1 : ℝ))
  have hA1 : Integrable (fun p : Θ × ℝ =>
      (Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
          Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) +
        (π.real (c ⁻¹' {c p.1}) * gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
          normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) - 1)) (π.prod (gaussianReal 0 1)) :=
    hT1.add hRm1
  have hA2 : Integrable (fun p : Θ × ℝ =>
      (Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
          Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) +
        (π.real (c ⁻¹' {c p.1}) * gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
          normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) - 1) +
        -Real.log (π.real (c ⁻¹' {c p.1}))) (π.prod (gaussianReal 0 1)) :=
    hA1.add hT3'
  have hae : ∀ᵐ p ∂π.prod (gaussianReal 0 1), infoDens π c s sc p.1 p.2 ≤
      (Real.log (gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) -
          Real.log (gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2))) +
        (π.real (c ⁻¹' {c p.1}) * gaussianPDFReal (ĉ (c p.1)) (noiseVar sc) (s p.1 + sc * p.2) /
          normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) - 1) +
        -Real.log (π.real (c ⁻¹' {c p.1})) :=
    ((Measure.quasiMeasurePreserving_fst (μ := π) (ν := gaussianReal 0 1)).ae (ae_pos_cell π hc)).mono
      fun p hp => infoDens_le_split π hc hs hsb hsc ĉ p.1 p.2 hp
  have hfst : ∫ p, -Real.log (π.real (c ⁻¹' {c p.1})) ∂π.prod (gaussianReal 0 1) = ansEntropy π c := by
    have := integral_fun_fst (μ := π) (ν := gaussianReal 0 1) (fun θ => -Real.log (π.real (c ⁻¹' {c θ})))
    rw [probReal_univ, one_smul] at this
    rw [this, hT3e]
  have hJ : infoJ π c s sc = ∫ p, infoDens π c s sc p.1 p.2 ∂π.prod (gaussianReal 0 1) := by
    rw [integral_prod _ hI0]; rfl
  have hmono := integral_mono_ae hI0 hA2 hae
  rw [integral_add hA1 hT3', integral_add hT1 hRm1, integral_sub hR (integrable_const (1 : ℝ)), integral_const,
    probReal_univ, one_smul, hfst, integral_gauss_ratio_cells π hc hs hsb hsc ĉ] at hmono
  rw [hJ]
  linarith

/-- The information of a round is nonnegative. -/
theorem infoJ_nonneg [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsProbabilityMeasure π]
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ}
    (hsc : sc ≠ 0) : 0 ≤ infoJ π c s sc := by
  have hI0 := integrable_infoDens π hc hs hsb hsc
  obtain ⟨hQ, hQ1⟩ := integral_inv_ratio_le_one π hc hs hsc
  have hae : ∀ᵐ p ∂π.prod (gaussianReal 0 1),
      1 - normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) /
        gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2) ≤ infoDens π c s sc p.1 p.2 :=
    ((Measure.quasiMeasurePreserving_fst (μ := π) (ν := gaussianReal 0 1)).ae (ae_pos_cell π hc)).mono
      fun p hp => one_sub_le_infoDens π hc hs hsb hsc p.1 p.2 hp
  have h1Q : Integrable (fun p : Θ × ℝ => 1 - normZ π c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2) /
      gaussianPDFReal (s p.1) (noiseVar sc) (s p.1 + sc * p.2)) (π.prod (gaussianReal 0 1)) :=
    (integrable_const (1 : ℝ)).sub hQ
  have hmono := integral_mono_ae h1Q hI0 hae
  rw [integral_sub (integrable_const (1 : ℝ)) hQ, integral_const, probReal_univ, one_smul] at hmono
  have hJ : infoJ π c s sc = ∫ p, infoDens π c s sc p.1 p.2 ∂π.prod (gaussianReal 0 1) := by
    rw [integral_prod _ hI0]; rfl
  rw [hJ]
  linarith

/-- A round with a constant answer and a constant signal (a dead round) carries no information. -/
theorem infoJ_const (π : Measure Θ) [IsProbabilityMeasure π] (a₀ : α) (b : ℝ) {sc : ℝ} (hsc : sc ≠ 0) :
    infoJ π (fun _ => a₀) (fun _ => b) sc = 0 := by
  have hv_ne_zero : noiseVar sc ≠ 0 := by
    intro h
    apply hsc
    have := congrArg Subtype.val h
    simpa [noiseVar] using this
  have h_normZ : ∀ (θ : Θ) (z : ℝ),
    normZ π (fun _ => a₀) (fun _ => b) (noiseVar sc) ((fun _ => a₀) θ) (b + sc * z) =
    gaussianPDFReal b (noiseVar sc) (b + sc * z) := by
    intro θ z
    unfold normZ
    have h_preimage : ((fun _ : Θ => a₀) ⁻¹' {a₀}) = Set.univ :=
      Set.preimage_const_of_mem (by simp)
    simp [h_preimage]
  have h_infoDens_zero : ∀ (θ : Θ) (z : ℝ), infoDens π (fun _ => a₀) (fun _ => b) sc θ z = 0 := by
    intro θ z
    unfold infoDens
    rw [h_normZ θ z]
    have hpos : gaussianPDFReal b (noiseVar sc) (b + sc * z) > 0 :=
      gaussianPDFReal_pos b (noiseVar sc) (b + sc * z) hv_ne_zero
    have hne : gaussianPDFReal b (noiseVar sc) (b + sc * z) ≠ 0 := by linarith
    field_simp [hne]
    exact Real.log_one
  unfold infoJ
  have h_inner : ∀ θ, (∫ z, infoDens π (fun _ => a₀) (fun _ => b) sc θ z ∂gaussianReal 0 1) = (0 : ℝ) := by
    intro θ
    simp [h_infoDens_zero θ]
  simp [h_inner]

end Round

/-! ## One round: the divergence from the prior -/

section KL

variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

/-- `K(ρ) = ∫ ρ ln ρ dπ₀`, the Kullback-Leibler divergence of `π₀.withDensity ρ` from `π₀`. -/
noncomputable def klDens (π₀ : Measure Θ) (ρ : Θ → ℝ≥0∞) : ℝ :=
  ∫ θ, (ρ θ).toReal * Real.log (ρ θ).toReal ∂π₀

/-- The density after a round with the likelihood `L`: the recursion of `dens` (Bayes.lean). -/
noncomputable def updDens (π₀ : Measure Θ) (g L : Θ → ℝ≥0∞) : Θ → ℝ≥0∞ :=
  if ∫⁻ θ, g θ * L θ ∂π₀ = 0 ∨ ∫⁻ θ, g θ * L θ ∂π₀ = ∞ then g
  else fun θ => (∫⁻ θ', g θ' * L θ' ∂π₀)⁻¹ * (g θ * L θ)

/-- Gibbs: `K(ρ) ≥ 0` for a probability density. -/
theorem klDens_nonneg (π₀ : Measure Θ) [IsProbabilityMeasure π₀] {ρ : Θ → ℝ≥0∞} (hρ : Measurable ρ)
    (h1 : ∫⁻ θ, ρ θ ∂π₀ = 1) : 0 ≤ klDens π₀ ρ := by
  -- klDens π₀ ρ = ∫ θ, (ρ θ).toReal * Real.log (ρ θ).toReal ∂π₀
  have h_lt_top : ∫⁻ θ, ρ θ ∂π₀ ≠ ⊤ := by simp [h1]
  have h_ae_lt_top : ∀ᵐ θ ∂π₀, ρ θ < ⊤ := MeasureTheory.ae_lt_top hρ h_lt_top
  have h_int_toReal : Integrable (fun θ => (ρ θ).toReal) π₀ :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hρ.aemeasurable h_lt_top
  have h_integral_toReal : ∫ θ, (ρ θ).toReal ∂π₀ = 1 := by
    rw [MeasureTheory.integral_toReal hρ.aemeasurable h_ae_lt_top, h1]
    simp
  have h_int_one : Integrable (fun _ => (1 : ℝ)) π₀ :=
    MeasureTheory.integrable_const (1 : ℝ)
  have h_int_sub : Integrable (fun θ => (ρ θ).toReal - 1) π₀ :=
    MeasureTheory.Integrable.sub h_int_toReal h_int_one
  have h_pointwise : (fun θ => (ρ θ).toReal - 1) ≤ (fun θ => (ρ θ).toReal * Real.log (ρ θ).toReal) := by
    intro θ
    have hx_nonneg : 0 ≤ (ρ θ).toReal := ENNReal.toReal_nonneg
    by_cases hx_pos : 0 < (ρ θ).toReal
    · have h := Real.one_sub_inv_le_log_of_pos hx_pos
      have h_mul : (ρ θ).toReal * (1 - ((ρ θ).toReal)⁻¹) ≤ (ρ θ).toReal * Real.log (ρ θ).toReal := by
        exact mul_le_mul_of_nonneg_left h (by linarith)
      have h_simp : (ρ θ).toReal * (1 - ((ρ θ).toReal)⁻¹) = (ρ θ).toReal - 1 := by
        field_simp [hx_pos.ne']
      rw [h_simp] at h_mul
      exact h_mul
    · have hx_zero : (ρ θ).toReal = 0 := by linarith
      simp [hx_zero, Real.log_zero]
  by_cases h_int : Integrable (fun θ => (ρ θ).toReal * Real.log (ρ θ).toReal) π₀
  · have h_le := MeasureTheory.integral_mono h_int_sub h_int h_pointwise
    have h_int_sub_val : ∫ θ, ((ρ θ).toReal - 1) ∂π₀ = (0 : ℝ) := by
      rw [MeasureTheory.integral_sub h_int_toReal h_int_one, h_integral_toReal]
      have h_int_one_val : ∫ θ, (1 : ℝ) ∂π₀ = (1 : ℝ) := by
        rw [MeasureTheory.integral_const (1 : ℝ), MeasureTheory.probReal_univ]
        simp
      rw [h_int_one_val]
      ring
    rw [h_int_sub_val] at h_le
    exact h_le
  · unfold klDens
    rw [MeasureTheory.integral_undef h_int]

theorem klDens_one (π₀ : Measure Θ) : klDens π₀ (fun _ => 1) = 0 := by
  simp [klDens]

/-- A bounded density stays bounded after a round with a bounded likelihood. -/
theorem updDens_le (π₀ : Measure Θ) {g L : Θ → ℝ≥0∞} {C D : ℝ≥0∞} (hg : ∀ θ, g θ ≤ C) (hL : ∀ θ, L θ ≤ D)
    (hC : C ≠ ∞) (hD : D ≠ ∞) : ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ∀ θ, updDens π₀ g L θ ≤ C' := by
  unfold updDens
  split_ifs with h
  · refine ⟨C, hC, ?_⟩
    intro θ
    exact hg θ
  · rename_i h
    have hZ : ∫⁻ θ, g θ * L θ ∂π₀ ≠ 0 ∧ ∫⁻ θ, g θ * L θ ∂π₀ ≠ ∞ := by
      simpa [not_or] using h
    have hZ_inv : (∫⁻ θ, g θ * L θ ∂π₀)⁻¹ ≠ ∞ :=
      ENNReal.inv_ne_top.mpr hZ.1
    have hC' : (∫⁻ θ, g θ * L θ ∂π₀)⁻¹ * (C * D) ≠ ∞ :=
      ENNReal.mul_ne_top hZ_inv (ENNReal.mul_ne_top hC hD)
    refine ⟨(∫⁻ θ, g θ * L θ ∂π₀)⁻¹ * (C * D), hC', ?_⟩
    intro θ
    have hprod : g θ * L θ ≤ C * D := by
      have hgθ := hg θ
      have hLθ := hL θ
      exact mul_le_mul hgθ hLθ (by positivity) (by positivity)
    refine mul_le_mul (le_of_eq rfl) hprod (by positivity) (by positivity)

/-- `K(ρ) = ∫ ln ρ d(ρ π₀)`. -/
theorem klDens_eq_integral_log (π₀ : Measure Θ) {ρ : Θ → ℝ≥0∞} (hρ : Measurable ρ) (hfin : ∀ θ, ρ θ ≠ ∞) :
    klDens π₀ ρ = ∫ θ, Real.log (ρ θ).toReal ∂π₀.withDensity ρ := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ (ae_of_all _ fun θ => (hfin θ).lt_top)]
  rfl

/-- `ln ρ` is integrable on `ρ π₀` for a bounded density. -/
theorem integrable_log_dens (π₀ : Measure Θ) [IsFiniteMeasure π₀] {ρ : Θ → ℝ≥0∞} (hρ : Measurable ρ) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C) :
    Integrable (fun θ => Real.log (ρ θ).toReal) (π₀.withDensity ρ) := by
  have h_fin : ∀ᵐ θ ∂π₀, ρ θ < ∞ := by
    filter_upwards with θ
    exact lt_of_le_of_lt (hρC θ) (Ne.lt_top hC)
  rw [MeasureTheory.integrable_withDensity_iff hρ h_fin]
  -- goal: Integrable (fun θ => Real.log (ρ θ).toReal * (ρ θ).toReal) π₀
  have h_ae : AEStronglyMeasurable (fun θ => Real.log (ρ θ).toReal * (ρ θ).toReal) π₀ := by
    have h_meas_toReal : Measurable fun θ => (ρ θ).toReal :=
      hρ.ennreal_toReal
    have h_meas_log : Measurable fun θ => Real.log (ρ θ).toReal :=
      Real.measurable_log.comp h_meas_toReal
    exact (h_meas_log.mul h_meas_toReal).aestronglyMeasurable
  refine (MeasureTheory.Integrable.of_bound h_ae (1 + (C.toReal) ^ 2) ?_)
  · -- pointwise bound: ‖Real.log (ρ θ).toReal * (ρ θ).toReal‖ ≤ 1 + (C.toReal)^2
    filter_upwards with θ
    have hx0 : 0 ≤ (ρ θ).toReal := ENNReal.toReal_nonneg
    have hxK : (ρ θ).toReal ≤ C.toReal := ENNReal.toReal_mono hC (hρC θ)
    by_cases hx1 : (ρ θ).toReal ≤ 1
    · -- case 0 ≤ x ≤ 1
      by_cases hx0' : (ρ θ).toReal = 0
      · rw [hx0']
        have : 0 ≤ 1 + (C.toReal) ^ 2 := by nlinarith [sq_nonneg (C.toReal)]
        simpa
      · have hpos : 0 < (ρ θ).toReal := by
          by_contra! H
          apply hx0'
          linarith
        have h_abs_lt_one : |Real.log ((ρ θ).toReal) * (ρ θ).toReal| < 1 :=
          Real.abs_log_mul_self_lt ((ρ θ).toReal) hpos hx1
        have h_norm_le_one : ‖Real.log ((ρ θ).toReal) * (ρ θ).toReal‖ ≤ 1 := by
          simpa using h_abs_lt_one.le
        nlinarith
    · -- case x > 1: 0 ≤ log x ≤ x - 1 ≤ x ≤ K
      have hlog_nonneg : 0 ≤ Real.log ((ρ θ).toReal) := Real.log_nonneg (by linarith)
      have hlog_le : Real.log ((ρ θ).toReal) ≤ (ρ θ).toReal - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      have h_nonneg : 0 ≤ Real.log ((ρ θ).toReal) * (ρ θ).toReal :=
        mul_nonneg hlog_nonneg hx0
      have h_norm : ‖Real.log ((ρ θ).toReal) * (ρ θ).toReal‖ = Real.log ((ρ θ).toReal) * (ρ θ).toReal :=
        abs_of_nonneg h_nonneg
      rw [h_norm]
      have hx_mul_log : Real.log ((ρ θ).toReal) * (ρ θ).toReal ≤ (C.toReal) ^ 2 := by
        nlinarith
      nlinarith

/-- The density after the round, at the true tip: `ln ρ' = ln ρ + ln(φ_σ(σ z)/Z(c θ, y))`. -/
theorem log_updDens_tip [MeasurableSingletonClass α] (π₀ : Measure Θ) [IsFiniteMeasure π₀] {ρ : Θ → ℝ≥0∞}
    (hρ : Measurable ρ) {C : ℝ≥0∞} (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C) {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ}
    (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ} (hsc : sc ≠ 0) (θ : Θ) (z : ℝ) (hρθ : ρ θ ≠ 0)
    (hp : 0 < (π₀.withDensity ρ).real (c ⁻¹' {c θ})) :
    Real.log (updDens π₀ ρ (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) θ).toReal =
      Real.log (ρ θ).toReal + infoDens (π₀.withDensity ρ) c s sc θ z := by
  have : IsFiniteMeasure (π₀.withDensity ρ) := by
    refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top π₀ Set.univ)) ?_)
    calc ∫⁻ θ, ρ θ ∂π₀ ≤ ∫⁻ _, C ∂π₀ := lintegral_mono hρC
      _ = C * π₀ Set.univ := lintegral_const C
  have hv : noiseVar sc ≠ 0 := noiseVar_ne_zero hsc
  have hv' : (0 : ℝ) < noiseVar sc := by
    have := (noiseVar sc).2
    have h2 : ((noiseVar sc : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne this h2.symm
  have hZ : 0 < normZ (π₀.withDensity ρ) c s (noiseVar sc) (c θ) (s θ + sc * z) := by
    refine lt_of_lt_of_le ?_ (le_normZ (π₀.withDensity ρ) hc hs hsb hv (c θ) (s θ + sc * z))
    have : 0 < Real.sqrt (2 * Real.pi * (noiseVar sc : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hcont : Continuous (fun μ : ℝ => gaussianPDFReal μ (noiseVar sc) (s θ + sc * z)) := by
    simp only [gaussianPDFReal_def]
    fun_prop
  have hL : Measurable (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) :=
    (ENNReal.measurable_ofReal.comp (hcont.measurable.comp hs)).indicator (hc (measurableSet_singleton _))
  have hN : ∫⁻ θ', ρ θ' * lik c s (noiseVar sc) (c θ) (s θ + sc * z) θ' ∂π₀ =
      ENNReal.ofReal (normZ (π₀.withDensity ρ) c s (noiseVar sc) (c θ) (s θ + sc * z)) := by
    rw [← lintegral_lik (π₀.withDensity ρ) hc hs (noiseVar sc) (c θ) (s θ + sc * z),
      lintegral_withDensity_eq_lintegral_mul _ hρ hL]
    rfl
  have hcond : ¬(ENNReal.ofReal (normZ (π₀.withDensity ρ) c s (noiseVar sc) (c θ) (s θ + sc * z)) = 0 ∨
      ENNReal.ofReal (normZ (π₀.withDensity ρ) c s (noiseVar sc) (c θ) (s θ + sc * z)) = ∞) := by
    simp [hZ]
  have hlik : lik c s (noiseVar sc) (c θ) (s θ + sc * z) θ =
      ENNReal.ofReal (gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z)) := by
    unfold lik
    rw [Set.indicator_of_mem (show θ ∈ c ⁻¹' {c θ} from rfl)]
    rfl
  have hφ : 0 < gaussianPDFReal (s θ) (noiseVar sc) (s θ + sc * z) := gaussianPDFReal_pos _ _ _ hv
  have hr : 0 < (ρ θ).toReal := ENNReal.toReal_pos hρθ (ne_top_of_le_ne_top hC (hρC θ))
  unfold updDens
  simp only [hN, hcond, ↓reduceIte]
  rw [hlik, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofReal hZ.le,
    ENNReal.toReal_ofReal hφ.le, Real.log_mul (inv_ne_zero hZ.ne') (mul_ne_zero hr.ne' hφ.ne'), Real.log_inv,
    Real.log_mul hr.ne' hφ.ne']
  unfold infoDens
  rw [Real.log_div hφ.ne' hZ.ne']
  ring

theorem measurable_updDens (π₀ : Measure Θ) {ρ L : Θ → ℝ≥0∞} (hρ : Measurable ρ) (hL : Measurable L) :
    Measurable (updDens π₀ ρ L) := by
  unfold updDens
  split_ifs
  · exact hρ
  · exact measurable_const.mul (hρ.mul hL)

/-- A round keeps a probability density a probability density. -/
theorem lintegral_updDens (π₀ : Measure Θ) {ρ L : Θ → ℝ≥0∞} (hρ : Measurable ρ) (hL : Measurable L)
    (h1 : ∫⁻ θ, ρ θ ∂π₀ = 1) : ∫⁻ θ, updDens π₀ ρ L θ ∂π₀ = 1 := by
  unfold updDens
  split_ifs with h
  · exact h1
  · push_neg at h
    show ∫⁻ θ, (∫⁻ θ', ρ θ' * L θ' ∂π₀)⁻¹ * (ρ θ * L θ) ∂π₀ = 1
    rw [lintegral_const_mul (f := fun θ => ρ θ * L θ) _ (hρ.mul hL)]
    exact ENNReal.inv_mul_cancel h.1 h.2

/-- The density after the round is jointly measurable in the tip, the answer and the observation. -/
theorem measurable_updDens_lik [Countable α] [MeasurableSingletonClass α] (π₀ : Measure Θ) [SFinite π₀]
    {ρ : Θ → ℝ≥0∞} (hρ : Measurable ρ) {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s)
    (v : ℝ≥0) : Measurable (fun q : Θ × α × ℝ => updDens π₀ ρ (lik c s v q.2.1 q.2.2) q.1) := by
  have hl := measurable_lik hc hs v
  have hN : Measurable (fun r : α × ℝ => ∫⁻ θ, ρ θ * lik c s v r.1 r.2 θ ∂π₀) :=
    ((hρ.comp measurable_snd).mul hl).lintegral_prod_right'
  have hN' : Measurable (fun q : Θ × α × ℝ => ∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀) :=
    hN.comp measurable_snd
  have hL : Measurable (fun q : Θ × α × ℝ => lik c s v q.2.1 q.2.2 q.1) :=
    hl.comp (measurable_snd.prodMk measurable_fst)
  have hS : MeasurableSet {q : Θ × α × ℝ | ∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀ = 0 ∨
      ∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀ = ∞} :=
    (hN' (measurableSet_singleton 0)).union (hN' (measurableSet_singleton ∞))
  have e : (fun q : Θ × α × ℝ => updDens π₀ ρ (lik c s v q.2.1 q.2.2) q.1) = fun q =>
      if (∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀ = 0 ∨ ∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀ = ∞) then ρ q.1
      else (∫⁻ θ, ρ θ * lik c s v q.2.1 q.2.2 θ ∂π₀)⁻¹ * (ρ q.1 * lik c s v q.2.1 q.2.2 q.1) := by
    funext q
    unfold updDens
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite hS (hρ.comp measurable_fst) (hN'.inv.mul ((hρ.comp measurable_fst).mul hL))

end KL

section KLRound

variable {Θ : Type} {α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

/-- (S2), one round: the mean divergence from the prior after the round is the divergence before it plus the
information of the round. -/
theorem kl_round [Fintype α] [MeasurableSingletonClass α] (π₀ : Measure Θ) [IsProbabilityMeasure π₀]
    {ρ : Θ → ℝ≥0∞} (hρ : Measurable ρ) {C : ℝ≥0∞} (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C) (h1 : ∫⁻ θ, ρ θ ∂π₀ = 1)
    {c : Θ → α} (hc : Measurable c) {s : Θ → ℝ} (hs : Measurable s) {S₀ : ℝ} (hsb : ∀ θ, |s θ| ≤ S₀) {sc : ℝ}
    (hsc : sc ≠ 0) :
    Integrable (fun p : Θ × ℝ =>
        klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))))
        ((π₀.withDensity ρ).prod (gaussianReal 0 1)) ∧
      ∫ θ, ∫ z, klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) ∂gaussianReal 0 1
          ∂π₀.withDensity ρ =
        klDens π₀ ρ + infoJ (π₀.withDensity ρ) c s sc := by
  have hfinρ : ∀ θ, ρ θ ≠ ∞ := fun θ => ne_top_of_le_ne_top hC (hρC θ)
  have : IsProbabilityMeasure (π₀.withDensity ρ) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1]⟩
  have hlik := measurable_lik hc hs (noiseVar sc)
  obtain ⟨g, hg⟩ : ∃ g : Θ × α × ℝ → ℝ, ∀ q,
      g q = Real.log (updDens π₀ ρ (lik c s (noiseVar sc) q.2.1 q.2.2) q.1).toReal := ⟨_, fun _ => rfl⟩
  have hgm : Measurable g := by
    rw [show g = _ from funext hg]
    exact Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (measurable_updDens_lik π₀ hρ hc hs (noiseVar sc)))
  -- the divergence after the round is the posterior mean of `g`
  have hA : ∀ a y, klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) a y)) =
      ∫ θ', g (θ', a, y) ∂bayesUpd (π₀.withDensity ρ) (lik c s (noiseVar sc) a y) := by
    intro a y
    have hLm : Measurable (lik c s (noiseVar sc) a y) := hlik.comp (measurable_prodMk_left (x := (a, y)))
    obtain ⟨C', hC', hle⟩ := updDens_le π₀ hρC (fun θ => lik_le c s (noiseVar sc) a y θ) hC ENNReal.ofReal_ne_top
    have hum : Measurable (updDens π₀ ρ (lik c s (noiseVar sc) a y)) := by
      unfold updDens
      split_ifs
      · exact hρ
      · exact measurable_const.mul (hρ.mul hLm)
    have hw : π₀.withDensity (updDens π₀ ρ (lik c s (noiseVar sc) a y)) =
        bayesUpd (π₀.withDensity ρ) (lik c s (noiseVar sc) a y) := withDensity_upd π₀ hρ hLm
    rw [klDens_eq_integral_log π₀ hum (fun θ => ne_top_of_le_ne_top hC' (hle θ)), hw]
    exact integral_congr_ae (ae_of_all _ fun θ' => (hg (θ', a, y)).symm)
  -- at the true tip, `g = ln ρ + infoDens`
  have hB : ∀ᵐ θ ∂π₀.withDensity ρ, ∀ z : ℝ,
      g (θ, c θ, s θ + sc * z) = Real.log (ρ θ).toReal + infoDens (π₀.withDensity ρ) c s sc θ z := by
    filter_upwards [ae_pos_cell (π₀.withDensity ρ) hc,
      (ae_withDensity_iff hρ).2 (ae_of_all _ fun θ (h : ρ θ ≠ 0) => h)] with θ hp hρθ z
    rw [hg]
    exact log_updDens_tip π₀ hρ hC hρC hc hs hsb hsc θ z hρθ hp
  have hI0 := integrable_infoDens (π₀.withDensity ρ) hc hs hsb hsc
  have hIρ := (integrable_log_dens π₀ hρ hC hρC).comp_fst (gaussianReal 0 1)
  have hae : (fun p : Θ × ℝ => g (p.1, c p.1, s p.1 + sc * p.2)) =ᵐ[(π₀.withDensity ρ).prod (gaussianReal 0 1)]
      fun p => Real.log (ρ p.1).toReal + infoDens (π₀.withDensity ρ) c s sc p.1 p.2 :=
    ((Measure.quasiMeasurePreserving_fst (μ := π₀.withDensity ρ) (ν := gaussianReal 0 1)).ae hB).mono
      fun p hp => hp p.2
  have hgI : Integrable (fun p : Θ × ℝ => g (p.1, c p.1, s p.1 + sc * p.2))
      ((π₀.withDensity ρ).prod (gaussianReal 0 1)) := (hIρ.add hI0).congr hae.symm
  obtain ⟨hpI, hpE⟩ := integral_bayes_step (π₀.withDensity ρ) hc hs hsc hgm hgI
  have hfun : (fun p : Θ × ℝ => klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)))) =
      fun p => ∫ θ', g (θ', c p.1, s p.1 + sc * p.2)
        ∂bayesUpd (π₀.withDensity ρ) (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)) :=
    funext fun p => hA _ _
  have hKI : Integrable (fun p : Θ × ℝ =>
      klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2))))
      ((π₀.withDensity ρ).prod (gaussianReal 0 1)) := by
    rw [hfun]; exact hpI
  refine ⟨hKI, ?_⟩
  have hfst : ∫ p, Real.log (ρ p.1).toReal ∂(π₀.withDensity ρ).prod (gaussianReal 0 1) = klDens π₀ ρ := by
    have := integral_fun_fst (μ := π₀.withDensity ρ) (ν := gaussianReal 0 1) (fun θ => Real.log (ρ θ).toReal)
    rw [probReal_univ, one_smul] at this
    rw [this, klDens_eq_integral_log π₀ hρ hfinρ]
  calc ∫ θ, ∫ z, klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) ∂gaussianReal 0 1
          ∂π₀.withDensity ρ
        = ∫ p, klDens π₀ (updDens π₀ ρ (lik c s (noiseVar sc) (c p.1) (s p.1 + sc * p.2)))
            ∂(π₀.withDensity ρ).prod (gaussianReal 0 1) := (integral_prod _ hKI).symm
    _ = ∫ p, g (p.1, c p.1, s p.1 + sc * p.2) ∂(π₀.withDensity ρ).prod (gaussianReal 0 1) := by
        rw [hfun]; exact hpE
    _ = ∫ p, (Real.log (ρ p.1).toReal + infoDens (π₀.withDensity ρ) c s sc p.1 p.2)
            ∂(π₀.withDensity ρ).prod (gaussianReal 0 1) := integral_congr_ae hae
    _ = klDens π₀ ρ + infoJ (π₀.withDensity ρ) c s sc := by
        rw [integral_add hIρ hI0, hfst, integral_prod _ hI0]
        rfl

end KLRound

/-! ## The count lemma (b) -/

/-- Gibbs against a reference density: `∫ ρ ln G dπ₀ ≤ ∫ ρ ln ρ dπ₀` when `∫ ρ dπ₀ = 1` and `∫ G dπ₀ ≤ 1`. -/
theorem gibbs_ref {Θ : Type*} [MeasurableSpace Θ] (π₀ : Measure Θ) [IsProbabilityMeasure π₀] {ρ : Θ → ℝ≥0∞}
    (hρ : Measurable ρ) {C : ℝ≥0∞} (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C) (h1 : ∫⁻ θ, ρ θ ∂π₀ = 1) {G : Θ → ℝ}
    (hG : Measurable G) (hG0 : ∀ θ, 0 < G θ) (hGi : Integrable G π₀) (hG1 : ∫ θ, G θ ∂π₀ ≤ 1)
    (hlog : Integrable (fun θ => (ρ θ).toReal * Real.log (G θ)) π₀) :
    ∫ θ, (ρ θ).toReal * Real.log (G θ) ∂π₀ ≤ klDens π₀ ρ := by
  set x := fun θ => (ρ θ).toReal with hx_def
  have hx_meas : Measurable x :=
    ENNReal.measurable_toReal.comp hρ
  have hx_nonneg : ∀ θ, 0 ≤ x θ := fun θ => ENNReal.toReal_nonneg
  have hx_bound : ∀ θ, x θ ≤ C.toReal := by
    intro θ
    exact ENNReal.toReal_mono hC (hρC θ)
  have hx_ae_measurable : AEMeasurable x π₀ := hx_meas.aemeasurable
  have hx_int : Integrable x π₀ := by
    refine Integrable.of_mem_Icc 0 C.toReal hx_ae_measurable ?_
    filter_upwards with θ
    exact ⟨hx_nonneg θ, hx_bound θ⟩
  have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC
  have h_ae_lt_top : ∀ᵐ θ ∂π₀, ρ θ < ⊤ := by
    filter_upwards with θ
    exact lt_of_le_of_lt (hρC θ) hC_lt_top
  have hx_int_eq_one : ∫ θ, x θ ∂π₀ = 1 := by
    rw [hx_def]
    rw [MeasureTheory.integral_toReal hρ.aemeasurable h_ae_lt_top]
    rw [h1]
    simp
  have hxlogx_meas : Measurable (fun θ => x θ * Real.log (x θ)) :=
    (Real.continuous_mul_log.measurable.comp hx_meas)
  have hxlogx_ae_measurable : AEMeasurable (fun θ => x θ * Real.log (x θ)) π₀ :=
    hxlogx_meas.aemeasurable
  have h_compact : IsCompact (Set.Icc (0 : ℝ) C.toReal) := isCompact_Icc
  have h_cont_on : ContinuousOn (fun (t : ℝ) => t * Real.log t) (Set.Icc (0 : ℝ) C.toReal) :=
    Real.continuous_mul_log.continuousOn
  have h_bdd_above : BddAbove ((fun (t : ℝ) => t * Real.log t) '' Set.Icc (0 : ℝ) C.toReal) :=
    IsCompact.bddAbove_image h_compact h_cont_on
  have h_bdd_below : BddBelow ((fun (t : ℝ) => t * Real.log t) '' Set.Icc (0 : ℝ) C.toReal) :=
    IsCompact.bddBelow_image h_compact h_cont_on
  obtain ⟨M₁, hM₁⟩ := h_bdd_above
  obtain ⟨M₂, hM₂⟩ := h_bdd_below
  let M := max (|M₁|) (|M₂|)
  have hxlogx_int : Integrable (fun θ => x θ * Real.log (x θ)) π₀ := by
    refine Integrable.of_mem_Icc (-M) M hxlogx_ae_measurable ?_
    filter_upwards with θ
    have hx_mem : x θ ∈ Set.Icc (0 : ℝ) C.toReal := ⟨hx_nonneg θ, hx_bound θ⟩
    have himg : x θ * Real.log (x θ) ∈ (fun (t : ℝ) => t * Real.log t) '' Set.Icc (0 : ℝ) C.toReal := by
      exact ⟨x θ, hx_mem, rfl⟩
    have h_le_M₁ : x θ * Real.log (x θ) ≤ M₁ := hM₁ himg
    have h_ge_M₂ : M₂ ≤ x θ * Real.log (x θ) := hM₂ himg
    have h_val_le_M : x θ * Real.log (x θ) ≤ M := by
      have h1 : M₁ ≤ |M₁| := le_abs_self M₁
      have h2 : |M₁| ≤ M := le_max_left _ _
      linarith
    have h_neg_M_le_val : -M ≤ x θ * Real.log (x θ) := by
      have h1 : -|M₂| ≤ M₂ := by
        by_cases hM₂_nonneg : 0 ≤ M₂
        · have h_abs_eq : |M₂| = M₂ := abs_of_nonneg hM₂_nonneg
          linarith
        · have h_abs_eq : |M₂| = -M₂ := abs_of_neg (not_le.mp hM₂_nonneg)
          linarith
      have h2 : -M ≤ -|M₂| := by
        have h_abs_le_M : |M₂| ≤ M := le_max_right _ _
        linarith
      linarith
    exact ⟨h_neg_M_le_val, h_val_le_M⟩
  have h_pointwise : ∀ θ, x θ * Real.log (G θ) ≤ x θ * Real.log (x θ) + G θ - x θ := by
    intro θ
    by_cases hx_pos : x θ > 0
    · have hG_div_x_pos : 0 < G θ / x θ := div_pos (hG0 θ) hx_pos
      have h_log_le : Real.log (G θ / x θ) ≤ G θ / x θ - 1 := Real.log_le_sub_one_of_pos hG_div_x_pos
      have h_log_div : Real.log (G θ / x θ) = Real.log (G θ) - Real.log (x θ) :=
        Real.log_div (ne_of_gt (hG0 θ)) (ne_of_gt hx_pos)
      calc
        x θ * Real.log (G θ) = x θ * (Real.log (x θ) + Real.log (G θ / x θ)) := by
          rw [h_log_div]
          ring
        _ = x θ * Real.log (x θ) + x θ * Real.log (G θ / x θ) := by ring
        _ ≤ x θ * Real.log (x θ) + x θ * (G θ / x θ - 1) := by
          nlinarith
        _ = x θ * Real.log (x θ) + G θ - x θ := by
          field_simp [ne_of_gt hx_pos]
          ring
    · have hx_nonpos : x θ ≤ 0 := by linarith
      have hx_zero : x θ = 0 := by linarith [hx_nonneg θ, hx_nonpos]
      rw [hx_zero]
      simp
      exact (hG0 θ).le
  have h_rhs_int : Integrable (fun θ => x θ * Real.log (x θ) + G θ - x θ) π₀ := by
    exact (hxlogx_int.add hGi).sub hx_int
  have h_int_ineq : ∫ θ, x θ * Real.log (G θ) ∂π₀ ≤ ∫ θ, (x θ * Real.log (x θ) + G θ - x θ) ∂π₀ :=
    integral_mono hlog h_rhs_int h_pointwise
  have h_rhs_eq' : ∫ θ, (x θ * Real.log (x θ) + G θ - x θ) ∂π₀ = (klDens π₀ ρ + (∫ θ, G θ ∂π₀)) - 1 := by
    calc
      ∫ θ, (x θ * Real.log (x θ) + G θ - x θ) ∂π₀
          = (∫ θ, (x θ * Real.log (x θ) + G θ) ∂π₀) - (∫ θ, x θ ∂π₀) := by
        simpa using integral_sub (hxlogx_int.add hGi) hx_int
      _ = ((∫ θ, x θ * Real.log (x θ) ∂π₀) + (∫ θ, G θ ∂π₀)) - (∫ θ, x θ ∂π₀) := by
        rw [integral_add hxlogx_int hGi]
      _ = (klDens π₀ ρ + (∫ θ, G θ ∂π₀)) - 1 := by
        rw [hx_int_eq_one]
        rfl
  have h_rhs_eq : ∫ θ, (x θ * Real.log (x θ) + G θ - x θ) ∂π₀ ≤ klDens π₀ ρ := by
    rw [h_rhs_eq']
    nlinarith
  calc
    ∫ θ, (ρ θ).toReal * Real.log (G θ) ∂π₀ = ∫ θ, x θ * Real.log (G θ) ∂π₀ := by simp [hx_def]
    _ ≤ klDens π₀ ρ := by
      linarith

/-- The Gaussian integral of an invertible linear change of variables:
`∫ exp(-‖A(θ - m)‖²/2) dθ = (2π)^{d/2} / |det A|`. -/
theorem integral_gauss_linear {d : ℕ} (A : E d →L[ℝ] E d) (hA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0)
    (m : E d) :
    ∫ θ, Real.exp (-‖A (θ - m)‖ ^ 2 / 2) = (2 * Real.pi) ^ ((d : ℝ) / 2) / |LinearMap.det (A : E d →ₗ[ℝ] E d)| := by
  set f : E d → ℝ := fun θ => Real.exp (-(1/2 : ℝ) * ‖θ‖ ^ 2) with hf
  have h_pos : (0 : ℝ) < 1/2 := by norm_num
  have h_gaussian : ∫ θ : E d, Real.exp (-(1/2 : ℝ) * ‖θ‖ ^ 2) = (Real.pi / (1/2 : ℝ)) ^ ((Module.finrank ℝ (E d) : ℝ) / 2) :=
    GaussianFourier.integral_rexp_neg_mul_sq_norm h_pos (V := E d)
  have h_finrank : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := d)
  have h_map : Measure.map (A : E d →ₗ[ℝ] E d) volume = ENNReal.ofReal |(LinearMap.det (A : E d →ₗ[ℝ] E d))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hA
  have hf_cont : Continuous f := by
    dsimp [f]
    continuity
  have hf_aestrongly : AEStronglyMeasurable f (Measure.map (A : E d → E d) volume) :=
    hf_cont.aestronglyMeasurable
  calc
    ∫ θ, Real.exp (-‖A (θ - m)‖ ^ 2 / 2) = ∫ θ, Real.exp (-‖A θ‖ ^ 2 / 2) := by
      rw [MeasureTheory.integral_sub_right_eq_self (f := fun θ => Real.exp (-‖A θ‖ ^ 2 / 2)) (g := m) (μ := volume)]
    _ = ∫ θ, Real.exp (-(1/2 : ℝ) * ‖A θ‖ ^ 2) := by
      refine integral_congr_ae ?_
      filter_upwards with θ
      ring
    _ = ∫ θ, f (A θ) := by
      simp [hf]
    _ = ∫ θ, f θ ∂(Measure.map (A : E d → E d) volume) := by
      rw [← MeasureTheory.integral_map A.measurable.aemeasurable hf_aestrongly]
    _ = ∫ θ, f θ ∂(Measure.map (A : E d →ₗ[ℝ] E d) volume) := by rfl
    _ = ∫ θ, f θ ∂(ENNReal.ofReal |(LinearMap.det (A : E d →ₗ[ℝ] E d))⁻¹| • volume) := by rw [h_map]
    _ = (ENNReal.ofReal |(LinearMap.det (A : E d →ₗ[ℝ] E d))⁻¹|).toReal • ∫ θ, f θ := by
      rw [integral_smul_measure]
    _ = |(LinearMap.det (A : E d →ₗ[ℝ] E d))⁻¹| • ∫ θ, f θ := by simp
    _ = |(LinearMap.det (A : E d →ₗ[ℝ] E d))⁻¹| * ∫ θ, f θ := by simp
    _ = |LinearMap.det (A : E d →ₗ[ℝ] E d)|⁻¹ * ∫ θ, f θ := by rw [abs_inv]
    _ = |LinearMap.det (A : E d →ₗ[ℝ] E d)|⁻¹ * ((Real.pi / (1/2 : ℝ)) ^ ((Module.finrank ℝ (E d) : ℝ) / 2)) := by rw [h_gaussian]
    _ = |LinearMap.det (A : E d →ₗ[ℝ] E d)|⁻¹ * ((2 * Real.pi) ^ ((Module.finrank ℝ (E d) : ℝ) / 2)) := by ring
    _ = |LinearMap.det (A : E d →ₗ[ℝ] E d)|⁻¹ * ((2 * Real.pi) ^ ((d : ℝ) / 2)) := by rw [h_finrank]
    _ = (2 * Real.pi) ^ ((d : ℝ) / 2) / |LinearMap.det (A : E d →ₗ[ℝ] E d)| := by ring

/-- The volume of the ball: `ln vol(r B^d) = d ln r + (d/2) ln π - ln Γ(d/2 + 1)`. -/
theorem log_volume_closedBall {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    Real.log (volume (Metric.closedBall (0 : E d) r)).toReal =
      d * Real.log r + d / 2 * Real.log Real.pi - Real.log (Real.Gamma (d / 2 + 1)) := by
  have h_nonempty : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hvol := EuclideanSpace.volume_closedBall (Fin d) (0 : E d) r
  have hcard : Fintype.card (Fin d) = d := by simp
  rw [hcard] at hvol
  have hpos : 0 ≤ Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    refine div_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg ?_)
    positivity
  have hr_nonneg : 0 ≤ r := le_of_lt hr
  have hvol_toReal : (volume (Metric.closedBall (0 : E d) r)).toReal = r ^ d * (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
    rw [hvol]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hr_nonneg]
    congr 1
    rw [ENNReal.toReal_ofReal hpos]
  rw [hvol_toReal]
  have hpos_sqrt_pow : 0 < Real.sqrt Real.pi ^ d := by positivity
  have hpos_gamma : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity : 0 < (d : ℝ) / 2 + 1)
  have hpos_div : 0 < Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := div_pos hpos_sqrt_pow hpos_gamma
  have hpos_rd : 0 < r ^ d := by positivity
  rw [Real.log_mul (ne_of_gt hpos_rd) (ne_of_gt hpos_div)]
  rw [Real.log_pow, Real.log_div (ne_of_gt hpos_sqrt_pow) (ne_of_gt hpos_gamma)]
  have hlog_sqrt_pow : Real.log (Real.sqrt Real.pi ^ d) = (d : ℝ) / 2 * Real.log Real.pi := by
    calc
      Real.log (Real.sqrt Real.pi ^ d) = (d : ℝ) * Real.log (Real.sqrt Real.pi) := by rw [Real.log_pow]
      _ = (d : ℝ) * (Real.log Real.pi / 2) := by rw [Real.log_sqrt (le_of_lt Real.pi_pos)]
      _ = (d : ℝ) / 2 * Real.log Real.pi := by ring
  rw [hlog_sqrt_pow]
  ring

open Stirling Filter Topology in
/-- Robbins: `ln n! ≤ n ln n - n + (1/2) ln(2π n) + 1/(12 n)` for `n ≥ 1`. -/
theorem log_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by
  have hnpos : n ≠ 0 := by omega
  have hnpos_real : 0 < (n : ℝ) := by
    have h : 0 < n := Nat.pos_of_ne_zero hnpos
    exact_mod_cast h
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := by positivity
  have h_sqrt_pi_ne_zero : Real.sqrt Real.pi ≠ 0 := by positivity
  -- Key lemma: log(stirlingSeq n) ≤ log(√π) + 1/(12*n)
  have h_stirling_bound : Real.log (stirlingSeq n) ≤ Real.log (Real.sqrt Real.pi) + 1 / (12 * (n : ℝ)) := by
    -- For any j, telescoping sum gives log(stirlingSeq n) ≤ log(stirlingSeq (n+j)) + 1/(12*n)
    have h_telescope (j : ℕ) : Real.log (stirlingSeq n) ≤ Real.log (stirlingSeq (n + j)) + 1 / (12 * (n : ℝ)) := by
      have h_diff_bound : Real.log (stirlingSeq n) - Real.log (stirlingSeq (n + j)) ≤ 1 / (12 * (n : ℝ)) := by
        have h_sum_eq : Real.log (stirlingSeq n) - Real.log (stirlingSeq (n + j)) =
            ∑ i ∈ Finset.range j, (Real.log (stirlingSeq (n + i)) - Real.log (stirlingSeq (n + i + 1))) := by
          simpa [add_assoc] using (Finset.sum_range_sub' (fun i => Real.log (stirlingSeq (n + i))) j).symm
        rw [h_sum_eq]
        calc
          ∑ i ∈ Finset.range j, (Real.log (stirlingSeq (n + i)) - Real.log (stirlingSeq (n + i + 1))) ≤
              ∑ i ∈ Finset.range j, (1 / (12 * ((n : ℝ) + i) * ((n : ℝ) + i + 1))) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            simpa [Nat.cast_add, add_assoc] using log_stirlingSeq_sdiff_le (n + i)
          _ = (1 / 12) * ∑ i ∈ Finset.range j, (1 / (((n : ℝ) + i) * ((n : ℝ) + i + 1))) := by
            simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
          _ = (1 / 12) * ∑ i ∈ Finset.range j, (1 / ((n : ℝ) + i) - 1 / ((n : ℝ) + i + 1)) := by
            refine congrArg (fun s => (1 / 12) * s) (Finset.sum_congr rfl (fun i hi => ?_))
            field_simp [show (n : ℝ) + i ≠ 0 from by linarith, show (n : ℝ) + i + 1 ≠ 0 from by linarith]
            ring
          _ = (1 / 12) * (1 / (n : ℝ) - 1 / ((n : ℝ) + j)) := by
            have hsum := Finset.sum_range_sub' (fun i => 1 / ((n : ℝ) + i)) j
            -- hsum: ∑ i in range j, (1/(n+i) - 1/(n+(i+1))) = 1/(n+0) - 1/(n+j)
            have hsum' : (∑ i ∈ Finset.range j, (1 / ((n : ℝ) + i) - 1 / ((n : ℝ) + i + 1))) =
                1 / (n : ℝ) - 1 / ((n : ℝ) + j) := by
              simpa [add_assoc, add_zero] using hsum
            rw [hsum']
          _ ≤ (1 / 12) * (1 / (n : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by norm_num)
          _ = 1 / (12 * (n : ℝ)) := by ring
      linarith
    have h_limit_f : Tendsto (fun _ : ℕ => Real.log (stirlingSeq n)) atTop (𝓝 (Real.log (stirlingSeq n))) :=
      tendsto_const_nhds
    have h_limit_g : Tendsto (fun j : ℕ => Real.log (stirlingSeq (n + j)) + 1 / (12 * (n : ℝ))) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi) + 1 / (12 * (n : ℝ)))) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have h_seq_limit : Tendsto (fun j : ℕ => stirlingSeq (n + j)) atTop (𝓝 (Real.sqrt Real.pi)) := by
        have h := tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat n)
        simpa [Function.comp_def, add_comm] using h
      exact (Real.continuousAt_log h_sqrt_pi_ne_zero).tendsto.comp h_seq_limit
    have h_eventually : (fun _ : ℕ => Real.log (stirlingSeq n)) ≤ᶠ[atTop]
        (fun j : ℕ => Real.log (stirlingSeq (n + j)) + 1 / (12 * (n : ℝ))) := by
      refine eventually_atTop.mpr ⟨0, fun j hj => h_telescope j⟩
    exact tendsto_le_of_eventuallyLE h_limit_f h_limit_g h_eventually
  -- Use log_stirlingSeq_formula to relate log(n!) to log(stirlingSeq n)
  have h_formula := log_stirlingSeq_formula n
  have h_log_n_div_exp : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
    rw [Real.log_div (by exact_mod_cast hnpos) (by positivity : Real.exp 1 ≠ 0), Real.log_exp]
  -- Identity: log(√π) + 1/2*log(2*n) = log(2*π*n)/2
  have h_log_sqrt_pi_add_half_log_two_n : Real.log (Real.sqrt Real.pi) + 1/2 * Real.log (2 * (n : ℝ)) =
      Real.log (2 * Real.pi * (n : ℝ)) / 2 := by
    have hpi_nonneg : 0 ≤ Real.pi := by positivity
    have h2n_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
    have h2pi_n_nonneg : 0 ≤ 2 * Real.pi * (n : ℝ) := by positivity
    calc
      Real.log (Real.sqrt Real.pi) + 1/2 * Real.log (2 * (n : ℝ)) =
          Real.log (Real.sqrt Real.pi) + Real.log (Real.sqrt (2 * (n : ℝ))) := by
        rw [Real.log_sqrt h2n_nonneg, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos_real.ne.symm]
        ring
      _ = Real.log (Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ))) := by
        rw [Real.log_mul (by positivity : Real.sqrt Real.pi ≠ 0) (by positivity : Real.sqrt (2 * (n : ℝ)) ≠ 0)]
      _ = Real.log (Real.sqrt (Real.pi * (2 * (n : ℝ)))) := by rw [Real.sqrt_mul hpi_nonneg]
      _ = Real.log (Real.sqrt (2 * Real.pi * (n : ℝ))) := by ring
      _ = Real.log (2 * Real.pi * (n : ℝ)) / 2 := by rw [Real.log_sqrt h2pi_n_nonneg]
  -- Combine: from h_formula and h_stirling_bound, derive the target inequality
  rw [h_formula] at h_stirling_bound
  rw [h_log_n_div_exp] at h_stirling_bound
  -- h_stirling_bound: log(n!) - 1/2*log(2*n) - n*(log n - 1) ≤ log(√π) + 1/(12*n)
  -- Rearranged: log(n!) ≤ n*log n - n + (log(√π) + 1/2*log(2*n)) + 1/(12*n)
  -- = n*log n - n + log(2*π*n)/2 + 1/(12*n)
  have hcalc : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
      Real.log (2 * Real.pi * (n : ℝ)) / 2 + 1 / (12 * (n : ℝ)) := by
    linarith [h_stirling_bound, h_log_sqrt_pi_add_half_log_two_n]
  simpa using hcalc

set_option maxHeartbeats 800000 in
/-- Crude Stirling (S3): `ln Γ(d/2 + 1) ≤ (d/2) ln(d/2) - d/2 + (1/2) ln(π d) + 1/d` for `d ≥ 1`. -/
theorem log_gamma_half_le {d : ℕ} (hd : 1 ≤ d) :
    Real.log (Real.Gamma (d / 2 + 1)) ≤
      d / 2 * Real.log (d / 2) - d / 2 + Real.log (Real.pi * d) / 2 + 1 / d := by
  rcases Nat.even_or_odd' d with ⟨n, hn | hn⟩
  · -- d = 2 * n
    have hnpos : 1 ≤ n := by
      rcases n with (rfl | n)
      · rw [hn] at hd; simp at hd
      · exact Nat.succ_pos _
    have hd2 : (d : ℝ) / 2 = (n : ℝ) := by
      rw [hn]; push_cast; ring
    have hd_eq : (d : ℝ) = 2 * (n : ℝ) := by rw [hn]; push_cast; ring
    have harg : Real.Gamma (d / 2 + 1) = (n.factorial : ℝ) := by
      rw [hn]; push_cast; simp [Real.Gamma_nat_eq_factorial]
    rw [harg, hd2, hd_eq]
    have h := log_factorial_le hnpos
    have hlog : Real.log (2 * Real.pi * (n : ℝ)) = Real.log (Real.pi * (2 * (n : ℝ))) := by ring
    rw [hlog] at h
    have hineq : (1 : ℝ) / (12 * (n : ℝ)) ≤ (1 : ℝ) / (2 * (n : ℝ)) := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · positivity
      · nlinarith
    have hgoal : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (Real.pi * (2 * (n : ℝ))) / 2 + 1 / (12 * (n : ℝ)) ≤
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (Real.pi * (2 * (n : ℝ))) / 2 + 1 / (2 * (n : ℝ)) := by
      nlinarith
    exact le_trans h hgoal
  · -- d = 2 * n + 1
    by_cases hn0 : n = 0
    · -- n = 0, so d = 1
      subst hn0
      have hd1 : (d : ℝ) = 1 := by rw [hn]; push_cast; ring
      rw [hd1]
      push_cast
      have hgamma : Real.Gamma (3/2 : ℝ) = Real.sqrt Real.pi / 2 := by
        calc
          Real.Gamma (3/2 : ℝ) = Real.Gamma (1/2 + 1) := by ring
          _ = (1/2 : ℝ) * Real.Gamma (1/2) := by rw [Real.Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0)]
          _ = (1/2 : ℝ) * Real.sqrt Real.pi := by rw [Real.Gamma_one_half_eq]
          _ = Real.sqrt Real.pi / 2 := by ring
      have hgoal : Real.Gamma ((1 : ℝ)/2 + 1) = Real.Gamma (3/2 : ℝ) := by ring
      rw [hgoal, hgamma]
      rw [Real.log_div (by positivity : Real.sqrt Real.pi ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_sqrt (show 0 ≤ Real.pi from by positivity)]
      have hlog2 : Real.log (1/2 : ℝ) = -Real.log 2 := by
        calc
          Real.log (1/2 : ℝ) = Real.log 1 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
          _ = 0 - Real.log 2 := by rw [Real.log_one]
          _ = -Real.log 2 := by ring
      rw [hlog2]
      ring_nf
      have hlog2pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    · -- n ≥ 1
      have hnpos : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn0)
      have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
      set x := (n : ℝ) + 1/2 with hx
      have hxpos : 0 < x := by nlinarith
      have hd2 : (d : ℝ) / 2 = x := by
        rw [hn]; push_cast; ring
      have hd_eq : (d : ℝ) = 2*x := by
        rw [hn]; dsimp [x]; push_cast; ring
      -- Log-convexity: Gamma(x + 1) ≤ Gamma(n+1)^(1/2) * Gamma(n+2)^(1/2)
      have hconv : Real.Gamma (x + 1) ≤
          Real.Gamma ((n : ℝ) + 1) ^ (1/2 : ℝ) * Real.Gamma ((n : ℝ) + 2) ^ (1/2 : ℝ) := by
        have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
          (by nlinarith : 0 < (n : ℝ) + 1)
          (by nlinarith : 0 < (n : ℝ) + 2)
          (by norm_num : 0 < (1/2 : ℝ))
          (by norm_num : 0 < (1/2 : ℝ))
          (by norm_num : (1/2 : ℝ) + (1/2 : ℝ) = 1)
        have hsum : (1/2 : ℝ) * ((n : ℝ) + 1) + (1/2 : ℝ) * ((n : ℝ) + 2) = (n : ℝ) + 3/2 := by ring
        have htarget : (n : ℝ) + 3/2 = x + 1 := by
          dsimp [x]; ring
        rw [hsum, htarget] at h
        exact h
      have hpos_g1 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by nlinarith)
      have hpos_g2 : 0 < Real.Gamma ((n : ℝ) + 2) := Real.Gamma_pos_of_pos (by nlinarith)
      have hpos_g3 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by nlinarith)
      -- Take logs
      have hlog_conv : Real.log (Real.Gamma (x + 1)) ≤
          Real.log (Real.Gamma ((n : ℝ) + 1) ^ (1/2 : ℝ) * Real.Gamma ((n : ℝ) + 2) ^ (1/2 : ℝ)) :=
        Real.log_le_log hpos_g3 hconv
      rw [Real.log_mul (by positivity : Real.Gamma ((n : ℝ) + 1) ^ (1/2 : ℝ) ≠ 0)
        (by positivity : Real.Gamma ((n : ℝ) + 2) ^ (1/2 : ℝ) ≠ 0),
        Real.log_rpow hpos_g1, Real.log_rpow hpos_g2] at hlog_conv
      -- hlog_conv: log(Gamma(x+1)) ≤ (1/2)*log(Gamma(n+1)) + (1/2)*log(Gamma(n+2))
      -- Gamma(n+1) = n!, Gamma(n+2) = (n+1)!
      have hgam1 : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := by
        rw [Real.Gamma_nat_eq_factorial]
      have hgam2 : Real.Gamma ((n : ℝ) + 2) = ((n+1).factorial : ℝ) := by
        rw [show ((n : ℝ) + 2) = (((n : ℕ) + 1 : ℕ) + 1 : ℝ) by push_cast; ring]
        rw [Real.Gamma_nat_eq_factorial]
      rw [hgam1, hgam2] at hlog_conv
      -- hlog_conv: log(Gamma(x+1)) ≤ (1/2)*log(n!) + (1/2)*log((n+1)!)
      -- = log(n!) + (1/2)*log(n+1)
      have h_log_fact : Real.log ((n+1).factorial : ℝ) = Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
        push_cast
        rw [show ((n+1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) by
          rw [Nat.factorial_succ]; push_cast; ring,
          Real.log_mul (by nlinarith : (n : ℝ) + 1 ≠ 0) (by exact_mod_cast Nat.factorial_ne_zero n)]
      rw [h_log_fact] at hlog_conv
      -- hlog_conv: log(Gamma(x+1)) ≤ log(n!) + (1/2)*log(n+1)
      -- Now use log_factorial_le for n
      have hfn := log_factorial_le hnpos
      -- hfn: log(n!) ≤ n*log(n) - n + log(2*pi*n)/2 + 1/(12*n)
      -- So log(Gamma(x+1)) ≤ n*log(n) - n + log(2*pi*n)/2 + 1/(12*n) + (1/2)*log(n+1)
      -- We need to show this ≤ x*log(x) - x + log(pi*d)/2 + 1/d
      -- Using d = 2x:
      rw [hd2, hd_eq]
      -- Goal: log(Gamma(x+1)) ≤ x*log(x) - x + log(pi*(2x))/2 + 1/(2x)
      -- = x*log(x) - x + log(2*pi*x)/2 + 1/(2x)
      have hRHS : x * Real.log x - x + Real.log (Real.pi * (2 * x)) / 2 + 1 / (2 * x) =
          x * Real.log x - x + Real.log (2 * Real.pi * x) / 2 + 1 / (2 * x) := by ring
      rw [hRHS]
      -- Now goal: log(Gamma(x+1)) ≤ x*log(x) - x + log(2*pi*x)/2 + 1/(2x)
      -- From hlog_conv and hfn, we have:
      -- log(Gamma(x+1)) ≤ n*log(n) - n + log(2*pi*n)/2 + 1/(12*n) + (1/2)*log(n+1)
      -- So it suffices to show:
      -- n*log(n) - n + log(2*pi*n)/2 + 1/(12*n) + (1/2)*log(n+1) ≤ x*log(x) - x + log(2*pi*x)/2 + 1/(2x)
      have h_suffices : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * Real.pi * (n : ℝ)) / 2 + 1 / (12 * (n : ℝ)) +
          (1/2 : ℝ) * Real.log ((n : ℝ) + 1) ≤
          x * Real.log x - x + Real.log (2 * Real.pi * x) / 2 + 1 / (2 * x) := by
        have hn1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
        have hx0 : x ≠ 0 := hxpos.ne'
        have hlogx : Real.log (2 * Real.pi * x) = Real.log (2 * Real.pi) + Real.log x :=
          Real.log_mul (by positivity) hx0
        have hlogn : Real.log (2 * Real.pi * (n:ℝ)) = Real.log (2 * Real.pi) + Real.log n :=
          Real.log_mul (by positivity) hnpos'.ne'
        have h1 : 1 - (n:ℝ) / x ≤ Real.log x - Real.log n := by
          have := Real.one_sub_inv_le_log_of_pos (show 0 < x / n by positivity)
          rwa [Real.log_div hx0 hnpos'.ne', inv_div] at this
        have hmul : (n:ℝ) * (1 - n / x) ≤ (n:ℝ) * (Real.log x - Real.log n) :=
          mul_le_mul_of_nonneg_left h1 hnpos'.le
        have h2 : Real.log n + Real.log ((n:ℝ) + 1) ≤ 2 * Real.log x := by
          rw [← Real.log_mul hnpos'.ne' hn1.ne', show (2:ℝ) * Real.log x = Real.log (x ^ 2) by
            rw [Real.log_pow]; norm_num]
          exact Real.log_le_log (by positivity) (by rw [hx]; nlinarith)
        have h3 : (n:ℝ) * (1 - n / x) - 1/2 + 1 / (2 * x) = 1 / (4 * x) := by
          field_simp
          rw [hx]
          ring
        have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hnpos
        have h4 : 1 / (12 * (n:ℝ)) ≤ 1 / (4 * x) :=
          one_div_le_one_div_of_le (by positivity) (by rw [hx]; linarith)
        have hxlog : x * Real.log x = (n:ℝ) * Real.log x + 1/2 * Real.log x := by
          rw [hx]; ring
        linarith
      have h_intermediate : Real.log (Real.Gamma (x + 1)) ≤
          (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * Real.pi * (n : ℝ)) / 2 + 1 / (12 * (n : ℝ)) +
          (1/2 : ℝ) * Real.log ((n : ℝ) + 1) := by
        linarith
      exact le_trans h_intermediate h_suffices

/-- The count lemma (a) on the spectrum, clipped: if fewer than `d/2` of the `λ_i ≥ 0` are at least `w²`, their sum is
at most `r₀²` and `w² ≤ 2 r₀²/(e d)`, then `∑_i ln max(λ_i, w²) ≤ (d/2) ln(2 r₀² w²/d)`. -/
theorem count_a_spec {d : ℕ} (hd : 0 < d) (lam : Fin d → ℝ) (hlam : ∀ i, 0 ≤ lam i) {r₀ w : ℝ} (hw : 0 < w)
    (hsum : ∑ i, lam i ≤ r₀ ^ 2) (hX : w ^ 2 ≤ 2 * r₀ ^ 2 / (Real.exp 1 * d))
    (hfew : ((Finset.univ.filter fun i => w ^ 2 ≤ lam i).card : ℝ) < d / 2) :
    ∑ i, Real.log (max (lam i) (w ^ 2)) ≤ d / 2 * Real.log (2 * r₀ ^ 2 * w ^ 2 / d) := by
  set a := 2 * r₀ ^ 2 / (d : ℝ) with ha_def
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha_pos : 0 < a := by
    have hr0sq_pos : 0 < r₀ ^ 2 := by
      have hw_sq_pos : 0 < w ^ 2 := pow_pos hw 2
      have hden : 0 < Real.exp 1 * (d : ℝ) := by positivity
      have htemp := (le_div_iff₀ hden).mp hX
      nlinarith
    refine div_pos (by nlinarith) hd'
  have hr0_ne_zero : r₀ ≠ 0 := by
    intro hzero
    have hzero' : a = 0 := by
      rw [ha_def, hzero]
      simp
    linarith
  have hw_sq_pos : 0 < w ^ 2 := pow_pos hw 2
  -- From hX: w² ≤ 2r₀²/(e·d), so a/w² ≥ e, so log(a/w²) ≥ 1
  have h_log_coe : 1 ≤ Real.log (a / (w ^ 2)) := by
    have h_ineq : Real.exp 1 ≤ a / (w ^ 2) := by
      rw [ha_def]
      apply (le_div_iff₀ hw_sq_pos).2
      have hden : 0 < Real.exp 1 * (d : ℝ) := by positivity
      have htemp := (le_div_iff₀ hden).mp hX
      apply (le_div_iff₀ hd').2
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < Real.exp 1) h_ineq
    rwa [Real.log_exp] at h
  set L := Finset.univ.filter fun i : Fin d => w ^ 2 ≤ lam i with hL_def
  have hL_card : (L.card : ℝ) < d / 2 := hfew
  have hL_card_le : (L.card : ℝ) ≤ d / 2 := by linarith
  -- Split the sum into L and its complement
  have h_sum_split : ∑ i : Fin d, Real.log (max (lam i) (w ^ 2)) =
      (∑ i ∈ L, Real.log (max (lam i) (w ^ 2))) + (∑ i ∈ Lᶜ, Real.log (max (lam i) (w ^ 2))) := by
    calc
      ∑ i : Fin d, Real.log (max (lam i) (w ^ 2)) = ∑ i ∈ Finset.univ, Real.log (max (lam i) (w ^ 2)) := by simp
      _ = (∑ i ∈ Finset.univ with w ^ 2 ≤ lam i, Real.log (max (lam i) (w ^ 2))) +
          (∑ i ∈ Finset.univ with ¬ w ^ 2 ≤ lam i, Real.log (max (lam i) (w ^ 2))) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      _ = (∑ i ∈ L, Real.log (max (lam i) (w ^ 2))) + (∑ i ∈ Lᶜ, Real.log (max (lam i) (w ^ 2))) := by
        simp [L]
  have h_max_L : ∀ i ∈ L, max (lam i) (w ^ 2) = lam i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact max_eq_left hi.2
  have h_max_notL : ∀ i ∉ L, max (lam i) (w ^ 2) = w ^ 2 := by
    intro i hi
    have hi' : ¬ w ^ 2 ≤ lam i := by
      intro hle
      apply hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hle⟩
    exact max_eq_right (by linarith)
  have h_sum_L : (∑ i ∈ L, Real.log (max (lam i) (w ^ 2))) ≤
      (L.card : ℝ) * Real.log a - (L.card : ℝ) + (∑ i ∈ L, lam i) / a := by
    calc
      (∑ i ∈ L, Real.log (max (lam i) (w ^ 2))) = (∑ i ∈ L, Real.log (lam i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [h_max_L i hi]
      _ ≤ (∑ i ∈ L, (Real.log a + lam i / a - 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hlam_pos : 0 < lam i := by
          have hmem := (Finset.mem_filter.mp hi).2
          linarith
        have h_div_pos : 0 < lam i / a := div_pos hlam_pos ha_pos
        have h_log_bound := Real.log_le_sub_one_of_pos h_div_pos
        rw [Real.log_div (ne_of_gt hlam_pos) (ne_of_gt ha_pos)] at h_log_bound
        linarith
      _ = (∑ i ∈ L, Real.log a) + (∑ i ∈ L, lam i / a) - (∑ i ∈ L, (1 : ℝ)) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ((L.card : ℝ) * Real.log a) + ((∑ i ∈ L, lam i) / a) - (L.card : ℝ) := by
        simp [Finset.sum_div, Finset.sum_const]
      _ = (L.card : ℝ) * Real.log a - (L.card : ℝ) + (∑ i ∈ L, lam i) / a := by ring
  have h_sum_notL : (∑ i ∈ Lᶜ, Real.log (max (lam i) (w ^ 2))) = ((Lᶜ.card : ℕ) : ℝ) * Real.log (w ^ 2) := by
    calc
      (∑ i ∈ Lᶜ, Real.log (max (lam i) (w ^ 2))) = (∑ i ∈ Lᶜ, Real.log (w ^ 2)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [h_max_notL i (Finset.mem_compl.mp hi)]
      _ = (Lᶜ.card : ℝ) • Real.log (w ^ 2) := by simp
      _ = (Lᶜ.card : ℝ) * Real.log (w ^ 2) := by simp
  have h_compl_card : (Lᶜ.card : ℝ) = (d : ℝ) - (L.card : ℝ) := by
    have h_card_add := Finset.card_add_card_compl L
    have h_total : Fintype.card (Fin d) = d := Fintype.card_fin d
    rw [h_total] at h_card_add
    have h_card_add' : (L.card : ℝ) + (Lᶜ.card : ℝ) = (d : ℝ) := by exact_mod_cast h_card_add
    linarith
  have h_sum_total : ∑ i : Fin d, Real.log (max (lam i) (w ^ 2)) ≤
      (L.card : ℝ) * Real.log a - (L.card : ℝ) + (∑ i ∈ L, lam i) / a + ((d : ℝ) - (L.card : ℝ)) * Real.log (w ^ 2) := by
    rw [h_sum_split, h_sum_notL, h_compl_card]
    apply add_le_add h_sum_L
    rfl
  have h_sum_lam_L : (∑ i ∈ L, lam i) ≤ r₀ ^ 2 := by
    calc
      (∑ i ∈ L, lam i) ≤ ∑ i : Fin d, lam i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
          intro i hi hi'
          apply hlam i)
      _ ≤ r₀ ^ 2 := hsum
  have h_bound1 : (L.card : ℝ) * Real.log a - (L.card : ℝ) + (∑ i ∈ L, lam i) / a + ((d : ℝ) - (L.card : ℝ)) * Real.log (w ^ 2) ≤
      (L.card : ℝ) * Real.log a - (L.card : ℝ) + r₀ ^ 2 / a + ((d : ℝ) - (L.card : ℝ)) * Real.log (w ^ 2) := by
    have hdiv : (∑ i ∈ L, lam i) / a ≤ r₀ ^ 2 / a :=
      div_le_div_of_nonneg_right h_sum_lam_L (by linarith)
    nlinarith
  have h_r0sq_div_a : r₀ ^ 2 / a = (d : ℝ) / 2 := by
    rw [ha_def]
    field_simp [hd'.ne', hr0_ne_zero]
  have h_bound2 : (L.card : ℝ) * Real.log a - (L.card : ℝ) + r₀ ^ 2 / a + ((d : ℝ) - (L.card : ℝ)) * Real.log (w ^ 2) =
      (L.card : ℝ) * (Real.log a - Real.log (w ^ 2) - 1) + (d : ℝ) / 2 + (d : ℝ) * Real.log (w ^ 2) := by
    rw [h_r0sq_div_a]
    ring
  have h_log_diff_nonneg : 0 ≤ Real.log a - Real.log (w ^ 2) - 1 := by
    have : Real.log (w ^ 2) + 1 ≤ Real.log a := by
      have h := h_log_coe
      rw [Real.log_div (ne_of_gt ha_pos) (ne_of_gt hw_sq_pos)] at h
      linarith
    linarith
  have h_bound3 : (L.card : ℝ) * (Real.log a - Real.log (w ^ 2) - 1) + (d : ℝ) / 2 + (d : ℝ) * Real.log (w ^ 2) ≤
      (d / 2 : ℝ) * (Real.log a - Real.log (w ^ 2) - 1) + (d : ℝ) / 2 + (d : ℝ) * Real.log (w ^ 2) := by
    nlinarith
  have h_bound4 : (d / 2 : ℝ) * (Real.log a - Real.log (w ^ 2) - 1) + (d : ℝ) / 2 + (d : ℝ) * Real.log (w ^ 2) =
      (d / 2 : ℝ) * Real.log (a * (w ^ 2)) := by
    rw [Real.log_mul (ne_of_gt ha_pos) (ne_of_gt hw_sq_pos)]
    ring
  have h_final : (d / 2 : ℝ) * Real.log (a * (w ^ 2)) = d / 2 * Real.log (2 * r₀ ^ 2 * w ^ 2 / d) := by
    rw [ha_def]
    have h_eq : (2 * r₀ ^ 2 / (d : ℝ)) * (w ^ 2) = 2 * r₀ ^ 2 * w ^ 2 / (d : ℝ) := by ring
    rw [h_eq]
  linarith

/-- `ln |det M^{1/2}| = -(1/2) ∑_i ln max(λ_i, w²)`. -/
theorem log_det_frameA {d : ℕ} (w : ℝ) (hw : w ≠ 0) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    Real.log |LinearMap.det ((frameA w S : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)| =
      -(∑ i, Real.log (max (hS.eigenvalues i) (w ^ 2))) / 2 := by
  have hw_sq_pos : w ^ 2 > 0 := by
    exact sq_pos_iff.mpr hw
  have hw_sq_pos' : 0 ≤ w ^ 2 := by linarith
  set f : ℝ → ℝ := fun s => (Real.sqrt (max s (w ^ 2)))⁻¹ with hf
  have hf_pos : ∀ x : ℝ, f x > 0 := by
    intro x
    dsimp [f]
    have hmax : max x (w ^ 2) ≥ w ^ 2 := by
      exact le_max_right x (w ^ 2)
    have hpos : max x (w ^ 2) > 0 := by linarith
    have hsqrt_pos : Real.sqrt (max x (w ^ 2)) > 0 := Real.sqrt_pos.mpr hpos
    exact inv_pos.mpr hsqrt_pos
  have h_det_frameA : LinearMap.det ((frameA w S : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) = (clipSqrt w S).det := by
    dsimp [frameA]
    have h1 : LinearMap.det ((Matrix.toEuclideanCLM (𝕜 := ℝ) (clipSqrt w S) : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) =
             LinearMap.det (Matrix.toEuclideanLin (clipSqrt w S)) := by
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    have h2 : LinearMap.det (Matrix.toEuclideanLin (clipSqrt w S)) =
             LinearMap.det ((Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
               (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) (clipSqrt w S)) := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    have h3 : LinearMap.det ((Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
               (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) (clipSqrt w S)) = (clipSqrt w S).det := by
      rw [LinearMap.det_toLin]
    rw [h1, h2, h3]
  have h_clipSqrt_eq : clipSqrt w S = hS.cfc f := by
    dsimp [clipSqrt, cfc]
    rw [Matrix.IsHermitian.cfc_eq hS f]
  have h_cfc_det : (hS.cfc f).det = ∏ i : Fin d, f (hS.eigenvalues i) := by
    have h_cfc_eq : hS.cfc f = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) hS.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hS.eigenvalues)) := rfl
    rw [h_cfc_eq, Unitary.conjStarAlgAut_apply]
    have h_starU : star (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      simpa using Unitary.star_mul_self hS.eigenvectorUnitary
    have hU_star : (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * star (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      simpa using Unitary.mul_star_self hS.eigenvectorUnitary
    rw [Matrix.det_conj_of_mul_eq_one hU_star h_starU]
    rw [Matrix.det_diagonal]
    simp [RCLike.ofReal]
  have h_pos : 0 ≤ ∏ i : Fin d, f (hS.eigenvalues i) := by
    refine Finset.prod_nonneg ?_
    intro i _
    exact le_of_lt (hf_pos (hS.eigenvalues i))
  rw [h_det_frameA, h_clipSqrt_eq, h_cfc_det]
  rw [abs_of_nonneg h_pos]
  rw [Real.log_prod (fun i _ => ne_of_gt (hf_pos (hS.eigenvalues i)))]
  simp_rw [hf]
  -- ∑ i, Real.log ((Real.sqrt (max (hS.eigenvalues i) (w ^ 2)))⁻¹)
  -- = ∑ i, -Real.log (Real.sqrt (max (hS.eigenvalues i) (w ^ 2)))
  -- = -∑ i, Real.log (Real.sqrt (max (hS.eigenvalues i) (w ^ 2)))
  -- = -∑ i, (Real.log (max (hS.eigenvalues i) (w ^ 2))) / 2
  -- = -(∑ i, Real.log (max (hS.eigenvalues i) (w ^ 2))) / 2
  have h_max_pos : ∀ i, 0 ≤ max (hS.eigenvalues i) (w ^ 2) := by
    intro i
    have hmax : max (hS.eigenvalues i) (w ^ 2) ≥ w ^ 2 := le_max_right _ _
    linarith
  simp_rw [Real.log_inv, Real.log_sqrt (h_max_pos _)]
  rw [Finset.sum_neg_distrib]
  calc
    -∑ x : Fin d, (Real.log (max (hS.eigenvalues x) (w ^ 2))) / 2
        = -((∑ x : Fin d, Real.log (max (hS.eigenvalues x) (w ^ 2))) / 2) := by rw [Finset.sum_div]
    _ = (-∑ x : Fin d, Real.log (max (hS.eigenvalues x) (w ^ 2))) / 2 := by rw [neg_div]

/-- `E |θ - m|_M² = tr(M Σ) = D_M` at the mean. -/
theorem integral_norm_frameA_sq {d : ℕ} (π : Measure (E d)) [IsProbabilityMeasure π]
    (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) (w : ℝ) (hw : w ≠ 0) :
    ∫ θ, ‖frameA w (covM π) (θ - meanV π)‖ ^ 2 ∂π = DM w (covM π) := by
  have h_cov_herm : (covM π).IsHermitian := (covM_posSemidef π h2).isHermitian
  calc
    ∫ θ, ‖frameA w (covM π) (θ - meanV π)‖ ^ 2 ∂π
        = ∫ θ, ((θ - meanV π).ofLp ⬝ᵥ (clipM w (covM π) *ᵥ (θ - meanV π).ofLp)) ∂π := by
      refine integral_congr_ae ?_
      filter_upwards with θ
      rw [norm_frameA_sq w (covM π) h_cov_herm hw (θ - meanV π)]
    _ = trace (clipM w (covM π) * secMom π (meanV π)) := by
      rw [trace_mul_secMom π h2 (meanV π) (clipM w (covM π))]
    _ = trace (clipM w (covM π) * covM π) := rfl
    _ = DM w (covM π) := rfl

/-- The Gaussian reference density on the prior uniform on `r₀ B^d`:
`G(θ) = vol(r₀ B^d) |det A| (2π)^{-d/2} exp(-‖A(θ - m)‖²/2)`. -/
noncomputable def gaussRef {d : ℕ} (r₀ : ℝ) (A : E d →L[ℝ] E d) (m θ : E d) : ℝ :=
  (volume (Metric.closedBall (0 : E d) r₀)).toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
    (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖A (θ - m)‖ ^ 2 / 2)

theorem gaussRef_pos {d : ℕ} {r₀ : ℝ} (hr : 0 < r₀) (A : E d →L[ℝ] E d)
    (hA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0) (m θ : E d) : 0 < gaussRef r₀ A m θ := by
  dsimp [gaussRef]
  have hvol : 0 < (volume (Metric.closedBall (0 : E d) r₀)).toReal := by
    refine ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : E d) hr).ne' ?_
    exact measure_closedBall_lt_top.ne
  have hdet : 0 < |LinearMap.det (A : E d →ₗ[ℝ] E d)| := abs_pos.2 hA
  have hpirexp : 0 < (2 * Real.pi) ^ (-(d : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hexp : 0 < Real.exp (-‖A (θ - m)‖ ^ 2 / 2) := Real.exp_pos _
  positivity

theorem integrable_gaussRef {d : ℕ} {r₀ : ℝ} (hr : 0 < r₀) (A : E d →L[ℝ] E d) (m : E d) :
    Integrable (gaussRef r₀ A m) (prior d r₀) := by
  set K : ℝ := (volume (Metric.closedBall (0 : E d) r₀)).toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
    (2 * Real.pi) ^ (-(d : ℝ) / 2) with hK
  have h_cont : Continuous (gaussRef r₀ A m) := by
    unfold gaussRef
    have h_exp : Continuous (fun θ : E d => Real.exp (-‖A (θ - m)‖ ^ 2 / 2)) := by
      refine Real.continuous_exp.comp ?_
      refine Continuous.div ?_ continuous_const (fun _ => by norm_num)
      refine Continuous.neg ?_
      refine Continuous.pow ?_ 2
      refine Continuous.norm ?_
      refine A.continuous.comp ?_
      exact Continuous.sub continuous_id continuous_const
    refine ((continuous_const.mul ?_).mul ?_).mul h_exp
    · exact continuous_const
    · exact continuous_const
  have h_meas : AEStronglyMeasurable (gaussRef r₀ A m) (prior d r₀) :=
    h_cont.measurable.aestronglyMeasurable
  have h_nonneg : ∀ θ, 0 ≤ gaussRef r₀ A m θ := by
    intro θ
    unfold gaussRef
    have h_vol : 0 ≤ (volume (Metric.closedBall (0 : E d) r₀)).toReal := ENNReal.toReal_nonneg
    have h_det : 0 ≤ |LinearMap.det (A : E d →ₗ[ℝ] E d)| := abs_nonneg _
    have h_pi : 0 ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have h_exp : 0 ≤ Real.exp (-‖A (θ - m)‖ ^ 2 / 2) := Real.exp_nonneg _
    positivity
  have h_bound : ∀ θ, |gaussRef r₀ A m θ| ≤ K := by
    intro θ
    unfold gaussRef
    have h_exp_le_one : Real.exp (-‖A (θ - m)‖ ^ 2 / 2) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [sq_nonneg (‖A (θ - m)‖)]
    have h_nonneg_prod : 0 ≤ (volume (Metric.closedBall (0 : E d) r₀)).toReal *
      |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
      positivity
    calc
      |(volume (Metric.closedBall (0 : E d) r₀)).toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖A (θ - m)‖ ^ 2 / 2)|
          = (volume (Metric.closedBall (0 : E d) r₀)).toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
            (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖A (θ - m)‖ ^ 2 / 2) :=
        abs_of_nonneg (by positivity)
      _ ≤ (volume (Metric.closedBall (0 : E d) r₀)).toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
            (2 * Real.pi) ^ (-(d : ℝ) / 2) * 1 := by
        refine mul_le_mul_of_nonneg_left h_exp_le_one h_nonneg_prod
      _ = K := by
        dsimp [K]
        ring
  have h_prob : IsProbabilityMeasure (prior d r₀) := isProbabilityMeasure_prior d hr
  have h_finite : IsFiniteMeasure (prior d r₀) := by infer_instance
  have h_int_const : Integrable (fun _ : E d => K) (prior d r₀) :=
    integrable_const K
  refine MeasureTheory.Integrable.mono' h_int_const h_meas ?_
  filter_upwards with θ
  simpa [Real.norm_eq_abs] using h_bound θ

/-- The reference density has mass at most one on the prior. -/
theorem integral_gaussRef_le {d : ℕ} {r₀ : ℝ} (hr : 0 < r₀) (A : E d →L[ℝ] E d)
    (hA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0) (m : E d) : ∫ θ, gaussRef r₀ A m θ ∂prior d r₀ ≤ 1 := by
  set V := volume (Metric.closedBall (0 : E d) r₀) with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    exact Metric.measure_closedBall_pos volume (0 : E d) hr
  have hVfin : V < ∞ := by
    rw [hVdef]
    exact MeasureTheory.measure_closedBall_lt_top
  have hVne0 : V ≠ 0 := hVpos.ne'
  have hVne_top : V ≠ ∞ := hVfin.ne
  have hVtoReal_pos : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVne_top
  have hbase_pos : 0 < 2 * Real.pi := by positivity
  have hbase_nonneg : 0 ≤ 2 * Real.pi := hbase_pos.le
  have hdet_abs_pos : 0 < |LinearMap.det (A : E d →ₗ[ℝ] E d)| := abs_pos.mpr hA
  have hGnonneg : 0 ≤ᵐ[volume] gaussRef r₀ A m := by
    filter_upwards [] with θ
    dsimp [gaussRef]
    positivity
  have hprior_eq : prior d r₀ = V⁻¹ • volume.restrict (Metric.closedBall (0 : E d) r₀) := by
    dsimp [prior, V, ProbabilityTheory.cond]
  -- gaussRef is integrable on the whole space
  have hGint : Integrable (gaussRef r₀ A m) volume := by
    by_contra! h_not_int
    have h_int_zero : ∫ θ, gaussRef r₀ A m θ ∂volume = 0 := MeasureTheory.integral_undef h_not_int
    have h_int_pos : 0 < ∫ θ, gaussRef r₀ A m θ ∂volume := by
      have h_exp_int : ∫ θ, Real.exp (-‖A (θ - m)‖ ^ 2 / 2) ∂volume =
          (2 * Real.pi) ^ ((d : ℝ) / 2) / |LinearMap.det (A : E d →ₗ[ℝ] E d)| :=
        integral_gauss_linear A hA m
      have h_eq : gaussRef r₀ A m = fun θ =>
          (V.toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2)) *
          Real.exp (-‖A (θ - m)‖ ^ 2 / 2) := by
        ext θ; dsimp [gaussRef]
      rw [h_eq]
      rw [integral_const_mul (V.toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2))]
      rw [h_exp_int]
      have h_factor_pos : 0 < V.toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
        positivity
      have h_rpow_prod : (2 * Real.pi) ^ (-(d : ℝ) / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) = 1 := by
        have h_expand : -(d : ℝ) / 2 = -((d : ℝ) / 2) := by ring
        rw [h_expand]
        rw [Real.rpow_neg hbase_nonneg]
        have h_rpow_pos : (2 * Real.pi) ^ ((d : ℝ) / 2) > 0 := Real.rpow_pos_of_pos hbase_pos _
        field_simp [h_rpow_pos.ne']
      positivity
    exact h_int_pos.ne' h_int_zero
  -- Compute ∫ G over the whole space = V.toReal
  have h_int_G : ∫ θ, gaussRef r₀ A m θ ∂volume = V.toReal := by
    have h_eq : gaussRef r₀ A m = fun θ =>
        (V.toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2)) *
        Real.exp (-‖A (θ - m)‖ ^ 2 / 2) := by
      ext θ; dsimp [gaussRef]
    rw [h_eq]
    rw [integral_const_mul (V.toReal * |LinearMap.det (A : E d →ₗ[ℝ] E d)| * (2 * Real.pi) ^ (-(d : ℝ) / 2))]
    rw [integral_gauss_linear A hA m]
    field_simp [hdet_abs_pos.ne']
    have h_rpow_prod : (2 * Real.pi) ^ (-(d : ℝ) / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) = 1 := by
      have h_expand : -(d : ℝ) / 2 = -((d : ℝ) / 2) := by ring
      rw [h_expand]
      rw [Real.rpow_neg hbase_nonneg]
      have h_rpow_pos : (2 * Real.pi) ^ ((d : ℝ) / 2) > 0 := Real.rpow_pos_of_pos hbase_pos _
      field_simp [h_rpow_pos.ne']
    have h_expand2 : -(↑d / 2 : ℝ) = (-(d : ℝ)) / 2 := by ring
    rw [h_expand2]
    exact h_rpow_prod
  calc
    ∫ θ, gaussRef r₀ A m θ ∂prior d r₀ = ∫ θ, gaussRef r₀ A m θ ∂(V⁻¹ • volume.restrict (Metric.closedBall (0 : E d) r₀)) := by
      rw [hprior_eq]
    _ = (V⁻¹).toReal • ∫ θ, gaussRef r₀ A m θ ∂(volume.restrict (Metric.closedBall (0 : E d) r₀)) := by
      rw [MeasureTheory.integral_smul_measure]
    _ = (V⁻¹).toReal • (∫ θ in Metric.closedBall (0 : E d) r₀, gaussRef r₀ A m θ ∂volume) := rfl
    _ ≤ (V⁻¹).toReal • (∫ θ, gaussRef r₀ A m θ ∂volume) := by
      refine smul_le_smul_of_nonneg_left ?_ (by positivity)
      refine MeasureTheory.setIntegral_le_integral hGint hGnonneg
    _ = (V⁻¹).toReal * V.toReal := by
      rw [h_int_G]
      rw [smul_eq_mul]
    _ = 1 := by
      rw [ENNReal.toReal_inv]
      field_simp [hVtoReal_pos.ne']


/-- `∫ ρ ln G dπ₀ = ln vol(r₀ B^d) + ln |det A| - (d/2) ln(2π) - (1/2) ∫ ‖A(θ - m)‖² d(ρ π₀)`. -/
theorem integral_log_gaussRef {d : ℕ} {r₀ : ℝ} (hr : 0 < r₀) (A : E d →L[ℝ] E d)
    (hA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0) (m : E d) {ρ : E d → ℝ≥0∞} (hρ : Measurable ρ) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C) (h1 : ∫⁻ θ, ρ θ ∂prior d r₀ = 1) :
    Integrable (fun θ => (ρ θ).toReal * Real.log (gaussRef r₀ A m θ)) (prior d r₀) ∧
      ∫ θ, (ρ θ).toReal * Real.log (gaussRef r₀ A m θ) ∂prior d r₀ =
        Real.log (volume (Metric.closedBall (0 : E d) r₀)).toReal +
          Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)| - d / 2 * Real.log (2 * Real.pi) -
          (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) / 2 := by
  set V := (volume (Metric.closedBall (0 : E d) r₀)).toReal with hV_def
  set D := |LinearMap.det (A : E d →ₗ[ℝ] E d)| with hD_def
  have hV_pos : 0 < V := by
    dsimp [V]
    refine ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : E d) hr).ne'
      (measure_closedBall_lt_top (x := (0 : E d)) (r := r₀)).ne
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hD_pos : 0 < D := abs_pos.mpr hA
  have hD_ne_zero : D ≠ 0 := hD_pos.ne'
  have h2π_pos : 0 < 2 * Real.pi := by positivity
  have h_log_gaussRef (θ : E d) : Real.log (gaussRef r₀ A m θ) =
      Real.log V + Real.log D - ((d : ℝ) / 2) * Real.log (2 * Real.pi) - ‖A (θ - m)‖ ^ 2 / 2 := by
    dsimp [gaussRef, V, D]
    have hC_ne_zero : (2 * Real.pi) ^ (-(d : ℝ) / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos h2π_pos _).ne'
    have hE_ne_zero : Real.exp (-‖A (θ - m)‖ ^ 2 / 2) ≠ 0 := (Real.exp_pos _).ne'
    have hprod1 : ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)|) *
        (2 * Real.pi) ^ (-(d : ℝ) / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hV_ne_zero hD_ne_zero) hC_ne_zero
    calc
      Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖A (θ - m)‖ ^ 2 / 2))
      = Real.log (((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2)) * Real.exp (-‖A (θ - m)‖ ^ 2 / 2)) := by ring
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2)) +
        Real.log (Real.exp (-‖A (θ - m)‖ ^ 2 / 2)) := by
        rw [Real.log_mul hprod1 hE_ne_zero]
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2)) + (-‖A (θ - m)‖ ^ 2 / 2) := by
        rw [Real.log_exp (-‖A (θ - m)‖ ^ 2 / 2)]
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)| *
        (2 * Real.pi) ^ (-(d : ℝ) / 2)) - ‖A (θ - m)‖ ^ 2 / 2 := by ring
      _ = Real.log (((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)|) *
        (2 * Real.pi) ^ (-(d : ℝ) / 2)) - ‖A (θ - m)‖ ^ 2 / 2 := by ring
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)|) +
        Real.log ((2 * Real.pi) ^ (-(d : ℝ) / 2)) - ‖A (θ - m)‖ ^ 2 / 2 := by
        rw [Real.log_mul (mul_ne_zero hV_ne_zero hD_ne_zero) hC_ne_zero]
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal *
        |LinearMap.det (A : E d →ₗ[ℝ] E d)|) +
        (-(d : ℝ) / 2) * Real.log (2 * Real.pi) - ‖A (θ - m)‖ ^ 2 / 2 := by
        rw [Real.log_rpow h2π_pos (-(d : ℝ) / 2)]
      _ = (Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal) +
        Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)|) +
        (-(d : ℝ) / 2) * Real.log (2 * Real.pi) - ‖A (θ - m)‖ ^ 2 / 2 := by
        rw [Real.log_mul hV_ne_zero hD_ne_zero]
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal) +
        Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)| +
        (-(d : ℝ) / 2) * Real.log (2 * Real.pi) - ‖A (θ - m)‖ ^ 2 / 2 := by ring
      _ = Real.log ((volume (Metric.closedBall (0 : E d) r₀)).toReal) +
        Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)| -
        ((d : ℝ) / 2) * Real.log (2 * Real.pi) - ‖A (θ - m)‖ ^ 2 / 2 := by ring
  set L := Real.log V + Real.log D - ((d : ℝ) / 2) * Real.log (2 * Real.pi) with hL_def
  haveI : IsProbabilityMeasure (prior d r₀) := isProbabilityMeasure_prior d hr
  have h_int_x : Integrable (fun θ => (ρ θ).toReal) (prior d r₀) := by
    refine integrable_toReal_of_lintegral_ne_top hρ.aemeasurable ?_
    rw [h1]
    exact ENNReal.one_ne_top
  have h_x_bound : ∀ᵐ θ ∂prior d r₀, (ρ θ).toReal ≤ C.toReal := by
    refine ae_of_all _ (fun θ => ENNReal.toReal_mono hC (hρC θ))
  have h_bound_norm : ∀ᵐ θ ∂prior d r₀, ‖A (θ - m)‖ ^ 2 ≤ (‖A‖ * (r₀ + ‖m‖)) ^ 2 := by
    filter_upwards [prior_ae_mem d r₀] with θ hθ
    have hnorm : ‖θ‖ ≤ r₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hθ
      exact hθ
    have h_norm_sub : ‖θ - m‖ ≤ r₀ + ‖m‖ := by
      calc
        ‖θ - m‖ ≤ ‖θ‖ + ‖m‖ := norm_sub_le _ _
        _ ≤ r₀ + ‖m‖ := by linarith
    have h_le_opNorm : ‖A (θ - m)‖ ≤ ‖A‖ * ‖θ - m‖ := A.le_opNorm (θ - m)
    have h_bound_norm' : ‖A (θ - m)‖ ≤ ‖A‖ * (r₀ + ‖m‖) := by
      calc
        ‖A (θ - m)‖ ≤ ‖A‖ * ‖θ - m‖ := h_le_opNorm
        _ ≤ ‖A‖ * (r₀ + ‖m‖) := by gcongr
    have h_bound_sq : ‖A (θ - m)‖ ^ 2 ≤ (‖A‖ * (r₀ + ‖m‖)) ^ 2 := by
      have h_nonneg : 0 ≤ ‖A (θ - m)‖ := norm_nonneg _
      have h_nonneg_bound : 0 ≤ ‖A‖ * (r₀ + ‖m‖) := by positivity
      have h := mul_self_le_mul_self h_nonneg h_bound_norm'
      simpa [sq] using h
    exact h_bound_sq
  have h_bound_prod : ∀ᵐ θ ∂prior d r₀,
      (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 ≤ C.toReal * (‖A‖ * (r₀ + ‖m‖)) ^ 2 := by
    filter_upwards [h_x_bound, h_bound_norm] with θ hx hn
    have h_nonneg_x : 0 ≤ (ρ θ).toReal := ENNReal.toReal_nonneg
    have h_nonneg_sq : 0 ≤ ‖A (θ - m)‖ ^ 2 := by positivity
    nlinarith
  have h_int_prod_sq : Integrable (fun θ => (ρ θ).toReal * ‖A (θ - m)‖ ^ 2) (prior d r₀) := by
    have h_nonneg : ∀ θ, 0 ≤ (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 :=
      fun θ => mul_nonneg (ENNReal.toReal_nonneg) (by positivity)
    have h_bound_prod_norm : ∀ᵐ θ ∂prior d r₀, ‖(ρ θ).toReal * ‖A (θ - m)‖ ^ 2‖ ≤
        C.toReal * (‖A‖ * (r₀ + ‖m‖)) ^ 2 := by
      filter_upwards [h_bound_prod] with θ h
      simpa [Real.norm_of_nonneg (h_nonneg θ)] using h
    refine Integrable.mono' (integrable_const _) ?_ h_bound_prod_norm
    refine ((hρ.ennreal_toReal).mul ?_).aestronglyMeasurable
    refine (Continuous.norm (A.continuous.comp (continuous_id.sub continuous_const))).pow 2 |>.measurable
  have hρ_lt_top : ∀ᵐ θ ∂prior d r₀, ρ θ < ⊤ := by
    refine ae_of_all _ (fun θ => ?_)
    have hC_lt_top : C < ⊤ := (lt_top_iff_ne_top.mpr hC)
    exact lt_of_le_of_lt (hρC θ) hC_lt_top
  have h_int_eq : ∫ θ, (ρ θ).toReal * Real.log (gaussRef r₀ A m θ) ∂prior d r₀ =
      Real.log (volume (Metric.closedBall (0 : E d) r₀)).toReal +
      Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)| - (d : ℝ) / 2 * Real.log (2 * Real.pi) -
      (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) / 2 := by
    calc
      ∫ θ, (ρ θ).toReal * Real.log (gaussRef r₀ A m θ) ∂prior d r₀
      = ∫ θ, (ρ θ).toReal * (L - ‖A (θ - m)‖ ^ 2 / 2) ∂prior d r₀ := by
        refine integral_congr_ae ?_
        filter_upwards with θ
        rw [h_log_gaussRef θ]
      _ = ∫ θ, ((ρ θ).toReal * L - (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2)) ∂prior d r₀ := by
        refine integral_congr_ae ?_
        filter_upwards with θ
        ring
      _ = ∫ θ, (ρ θ).toReal * L ∂prior d r₀ - ∫ θ, (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2) ∂prior d r₀ := by
        refine integral_sub (h_int_x.mul_const L) ?_
        have : Integrable (fun θ => (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2)) (prior d r₀) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            h_int_prod_sq.const_mul (1/2 : ℝ)
        exact this
      _ = L * (∫ θ, (ρ θ).toReal ∂prior d r₀) -
          (∫ θ, (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 ∂prior d r₀) * (1/2 : ℝ) := by
        rw [integral_mul_const_of_integrable h_int_x (c := L)]
        have htemp : ∫ θ, (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2) ∂prior d r₀ =
            (∫ θ, (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 ∂prior d r₀) * (1/2 : ℝ) := by
          calc
            ∫ θ, (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2) ∂prior d r₀
            = ∫ θ, ((ρ θ).toReal * ‖A (θ - m)‖ ^ 2) * (1/2 : ℝ) ∂prior d r₀ := by
              refine integral_congr_ae ?_
              filter_upwards with θ; ring
            _ = (∫ θ, (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 ∂prior d r₀) * (1/2 : ℝ) := by
              rw [integral_mul_const_of_integrable h_int_prod_sq (c := (1/2 : ℝ))]
        rw [htemp]
        ring
      _ = L * 1 - (∫ θ, (ρ θ).toReal * ‖A (θ - m)‖ ^ 2 ∂prior d r₀) * (1/2 : ℝ) := by
        rw [integral_toReal hρ.aemeasurable hρ_lt_top, h1, ENNReal.toReal_one]
      _ = L - (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) * (1/2 : ℝ) := by
        rw [integral_withDensity_eq_integral_toReal_smul hρ hρ_lt_top
          (fun θ => ‖A (θ - m)‖ ^ 2)]
        simp [smul_eq_mul]
      _ = L - (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) / 2 := by ring
      _ = (Real.log V + Real.log D - ((d : ℝ) / 2) * Real.log (2 * Real.pi)) -
          (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) / 2 := by rfl
      _ = Real.log (volume (Metric.closedBall (0 : E d) r₀)).toReal +
          Real.log |LinearMap.det (A : E d →ₗ[ℝ] E d)| -
          (d : ℝ) / 2 * Real.log (2 * Real.pi) -
          (∫ θ, ‖A (θ - m)‖ ^ 2 ∂(prior d r₀).withDensity ρ) / 2 := by
        simp [V, D]
  refine ⟨?_, h_int_eq⟩
  -- integrability of the target
  have h_target_eq : (fun θ => (ρ θ).toReal * Real.log (gaussRef r₀ A m θ)) =
      (fun θ => (ρ θ).toReal * (L - ‖A (θ - m)‖ ^ 2 / 2)) := by
    ext θ; rw [h_log_gaussRef θ]
  rw [h_target_eq]
  have h_int_sub : Integrable (fun θ => (ρ θ).toReal * (L - ‖A (θ - m)‖ ^ 2 / 2)) (prior d r₀) := by
    have h1 : Integrable (fun θ => (ρ θ).toReal * L) (prior d r₀) := h_int_x.mul_const L
    have h2 : Integrable (fun θ => (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2)) (prior d r₀) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        h_int_prod_sq.const_mul (1/2 : ℝ)
    have hsub := h1.sub h2
    have h_eq : ((fun θ => (ρ θ).toReal * L) - (fun θ => (ρ θ).toReal * (‖A (θ - m)‖ ^ 2 / 2))) =
        (fun θ => (ρ θ).toReal * (L - ‖A (θ - m)‖ ^ 2 / 2)) := by
      ext θ
      dsimp
      ring
    rw [h_eq] at hsub
    exact hsub
  exact h_int_sub

/-- The arithmetic of the count lemma (b): the volume of the ball, the determinant of the clipped metric and `D_M ≤ d`
give `N*`. -/
theorem count_b_real {d : ℕ} (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) {lv la D : ℝ}
    (hlv : d * Real.log (1 / 2) + d / 2 * Real.log Real.pi -
      (d / 2 * Real.log (d / 2) - d / 2 + Real.log (Real.pi * d) / 2 + 1 / d) ≤ lv)
    (hla : -(d / 2 * Real.log (2 * (1 / 2) ^ 2 * w ^ 2 / d)) / 2 ≤ la) (hD : D ≤ d) :
    nStar d w ≤ lv + la - d / 2 * Real.log (2 * Real.pi) - D / 2 := by
  set x := (d : ℝ) with hx
  have hxpos : 0 < x := by
    have hdpos_nat : 0 < d := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hd
    have hdpos_real : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
    rwa [hx]
  have hxne0 : x ≠ 0 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne0 : Real.pi ≠ 0 := by linarith
  have hw_sq_pos : 0 < w ^ 2 := pow_pos hw 2
  have hw_sq_ne0 : w ^ 2 ≠ 0 := by linarith
  have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
  have hhalf_ne0 : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hw_ne0 : w ≠ 0 := by linarith
  -- Expand nStar
  unfold nStar
  -- Key identity: after expanding all logs, the RHS lower bounds sum to nStar + x/2*log(2π) + x/2
  have h_identity : x / 4 * Real.log (((1 : ℝ) / 2) ^ 2 / (2 * x * w ^ 2)) - Real.log (Real.pi * x) / 2 - 1 / x
      + x / 2 * Real.log (2 * Real.pi) + x / 2 =
      (x * Real.log (1 / 2) + x / 2 * Real.log Real.pi -
        (x / 2 * Real.log (x / 2) - x / 2 + Real.log (Real.pi * x) / 2 + 1 / x)) +
      (-(x / 2 * Real.log (2 * ((1 : ℝ) / 2) ^ 2 * w ^ 2 / x)) / 2) := by
    -- Expand log(((1/2)^2) / (2*x*w^2))
    rw [Real.log_div (pow_ne_zero 2 hhalf_ne0) (mul_ne_zero (mul_ne_zero h2ne0 hxne0) hw_sq_ne0)]
    -- Expand log((1/2)^2)
    rw [Real.log_pow]
    -- Expand log(2*x*w^2) = log((2*x)*w^2) = log(2*x) + log(w^2)
    rw [Real.log_mul (mul_ne_zero h2ne0 hxne0) hw_sq_ne0]
    -- Expand log(2*x) = log 2 + log x
    rw [Real.log_mul h2ne0 hxne0]
    -- Expand log(w^2) = 2*log w
    rw [Real.log_pow w 2]
    -- Expand log(π*x) = log π + log x
    rw [Real.log_mul hpi_ne0 hxne0]
    -- Expand log(x/2) = log x - log 2
    rw [Real.log_div hxne0 h2ne0]
    -- Expand log(2*π) = log 2 + log π
    rw [Real.log_mul h2ne0 hpi_ne0]
    -- Expand log(2*(1/2)^2*w^2/x)
    rw [Real.log_div (mul_ne_zero (mul_ne_zero h2ne0 (pow_ne_zero 2 hhalf_ne0)) hw_sq_ne0) hxne0]
    -- Expand log(2*(1/2)^2*w^2) = log((2*(1/2)^2)*w^2) = log(2*(1/2)^2) + log(w^2)
    rw [Real.log_mul (mul_ne_zero h2ne0 (pow_ne_zero 2 hhalf_ne0)) hw_sq_ne0]
    -- Expand log(2*(1/2)^2) = log 2 + log((1/2)^2)
    rw [Real.log_mul h2ne0 (pow_ne_zero 2 hhalf_ne0)]
    -- Expand log(w^2) = 2*log w
    rw [Real.log_pow w 2]
    -- Expand the remaining log((1/2)^2) on the RHS
    rw [Real.log_pow]
    ring_nf
  -- From h_identity, we get nStar + x/2*log(2π) + x/2 = lower bounds sum
  -- So nStar ≤ lower bounds sum - x/2*log(2π) - x/2
  have h_goal : x / 4 * Real.log (((1 : ℝ) / 2) ^ 2 / (2 * x * w ^ 2)) - Real.log (Real.pi * x) / 2 - 1 / x ≤
      (x * Real.log (1 / 2) + x / 2 * Real.log Real.pi -
        (x / 2 * Real.log (x / 2) - x / 2 + Real.log (Real.pi * x) / 2 + 1 / x)) +
      (-(x / 2 * Real.log (2 * ((1 : ℝ) / 2) ^ 2 * w ^ 2 / x)) / 2) - x / 2 * Real.log (2 * Real.pi) - x / 2 := by
    linarith
  -- Translate hlv and hla to use x
  have h_lv : x * Real.log (1 / 2) + x / 2 * Real.log Real.pi -
      (x / 2 * Real.log (x / 2) - x / 2 + Real.log (Real.pi * x) / 2 + 1 / x) ≤ lv := by
    simpa [hx] using hlv
  have h_la : -(x / 2 * Real.log (2 * ((1 : ℝ) / 2) ^ 2 * w ^ 2 / x)) / 2 ≤ la := by
    simpa [hx] using hla
  -- From hD: D ≤ x, so -x/2 ≤ -D/2
  have h_D_ineq : -x / 2 ≤ -D / 2 := by
    have hD' : (D : ℝ) ≤ x := by exact_mod_cast hD
    linarith
  -- Combine: lower bounds sum - x/2*log(2π) - x/2 ≤ lv + la - x/2*log(2π) - D/2
  have h_sum : (x * Real.log (1 / 2) + x / 2 * Real.log Real.pi -
      (x / 2 * Real.log (x / 2) - x / 2 + Real.log (Real.pi * x) / 2 + 1 / x)) +
      (-(x / 2 * Real.log (2 * ((1 : ℝ) / 2) ^ 2 * w ^ 2 / x)) / 2) - x / 2 * Real.log (2 * Real.pi) - x / 2 ≤
      lv + la - x / 2 * Real.log (2 * Real.pi) - D / 2 := by
    linarith
  -- Chain inequalities
  linarith

/-- The count lemma (b) in the form (S2): on the prior uniform on `B(0, 1/2)`, a law with a bounded density `ρ` and
fewer than `d/2` eigenvalues of its covariance at least `w²` lies at least `N*` from the prior. -/
theorem count_b {d : ℕ} (hd : 1 ≤ d) {w : ℝ} (hw : 0 < w) (hX : Real.exp 1 / 2 ≤ xCount d w)
    {ρ : E d → ℝ≥0∞} (hρ : Measurable ρ) {C : ℝ≥0∞} (hC : C ≠ ∞) (hρC : ∀ θ, ρ θ ≤ C)
    (h1 : ∫⁻ θ, ρ θ ∂prior d (1 / 2) = 1)
    (hdead : dLive w (covM ((prior d (1 / 2)).withDensity ρ)) < d / 2) :
    nStar d w ≤ klDens (prior d (1 / 2)) ρ := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  haveI : IsProbabilityMeasure (prior d (1 / 2)) := isProbabilityMeasure_prior d hr
  haveI : IsProbabilityMeasure ((prior d (1 / 2)).withDensity ρ) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1]⟩
  have hball : ∀ᵐ θ ∂(prior d (1 / 2)).withDensity ρ, θ ∈ Metric.closedBall (0 : E d) (1 / 2) :=
    (withDensity_absolutelyContinuous _ _).ae_le (prior_ae_mem d _)
  have h2 := integrable_sq_norm_of_ae_mem _ hball
  have hS := covM_posSemidef _ h2
  have hw0 : w ≠ 0 := hw.ne'
  have hAinj := frameA_injective w _ hS.1 hw0
  have hA : LinearMap.det ((frameA w (covM ((prior d (1 / 2)).withDensity ρ)) : E d →L[ℝ] E d) :
      E d →ₗ[ℝ] E d) ≠ 0 := fun h =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hAinj)
  have hGm : Measurable (gaussRef (1 / 2) (frameA w (covM ((prior d (1 / 2)).withDensity ρ)))
      (meanV ((prior d (1 / 2)).withDensity ρ))) := by
    unfold gaussRef
    exact Continuous.measurable (by fun_prop)
  obtain ⟨hint, heq⟩ := integral_log_gaussRef hr _ hA (meanV ((prior d (1 / 2)).withDensity ρ)) hρ hC hρC h1
  have hgibbs := gibbs_ref (prior d (1 / 2)) hρ hC hρC h1 hGm (fun θ => gaussRef_pos hr _ hA _ θ)
    (integrable_gaussRef hr _ _) (integral_gaussRef_le hr _ hA _) hint
  rw [heq, integral_norm_frameA_sq _ h2 w hw0] at hgibbs
  refine le_trans (count_b_real hd hw ?_ ?_ (DM_le w _ hS hw0)) hgibbs
  · rw [log_volume_closedBall (by omega) hr]
    have := log_gamma_half_le hd
    linarith
  · rw [log_det_frameA w hw0 _ hS.1]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hsum : ∑ i, hS.1.eigenvalues i ≤ (1 / 2) ^ 2 := by
      have htr := hS.1.trace_eq_sum_eigenvalues
      simp only [RCLike.ofReal_real_eq_id, id] at htr
      rw [← htr]
      refine le_trans (trace_covM_le _ h2) ?_
      have hb : ∀ᵐ θ ∂(prior d (1 / 2)).withDensity ρ, ‖θ‖ ^ 2 ≤ (1 / 2) ^ 2 := hball.mono fun θ hθ => by
        rw [Metric.mem_closedBall, dist_zero_right] at hθ
        exact pow_le_pow_left₀ (norm_nonneg _) hθ 2
      calc ∫ θ, ‖θ‖ ^ 2 ∂(prior d (1 / 2)).withDensity ρ ≤ ∫ _θ, (1 / 2 : ℝ) ^ 2 ∂(prior d (1 / 2)).withDensity ρ :=
            integral_mono_ae h2 (integrable_const _) hb
        _ = (1 / 2) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
    have hX' : w ^ 2 ≤ 2 * (1 / 2) ^ 2 / (Real.exp 1 * d) := by
      unfold xCount at hX
      rw [le_div_iff₀ (by positivity)] at hX
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.exp_pos 1]
    have hfew : ((Finset.univ.filter fun i => w ^ 2 ≤ hS.1.eigenvalues i).card : ℝ) < d / 2 := by
      rw [← dLive_eq_card w _ hS.1]
      exact hdead
    have hca := count_a_spec (by omega) hS.1.eigenvalues (fun i => hS.eigenvalues_nonneg i) hw hsum hX' hfew
    linarith

/-! ## Measurability in the history -/

section HistMeas

variable {d : ℕ}

/-- The information of a round is measurable in a parameter that drives the density, the answer and the signal. -/
theorem measurable_infoJ_dens {H : Type} [MeasurableSpace H] {α : Type} [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) {Q : Type} [MeasurableSpace Q] {hp : Q → H}
    (hhp : Measurable hp) {c : Q → E d → α} (hc : Measurable (Function.uncurry c)) {s : Q → E d → ℝ}
    (hs : Measurable (Function.uncurry s)) (sc : ℝ) :
    Measurable (fun q => infoJ (π0.withDensity (g (hp q))) (c q) (s q) sc) := by
  have hF1 : Measurable (fun r : (Q × α × ℝ) × E d =>
      (c r.1.1 ⁻¹' {r.1.2.1}).indicator (fun θ => gaussianPDFReal (s r.1.1 θ) (noiseVar sc) r.1.2.2) r.2) := by
    have hcr : Measurable (fun r : (Q × α × ℝ) × E d => c r.1.1 r.2) :=
      hc.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hsr : Measurable (fun r : (Q × α × ℝ) × E d => s r.1.1 r.2) :=
      hs.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hset : MeasurableSet {r : (Q × α × ℝ) × E d | c r.1.1 r.2 = r.1.2.1} :=
      measurableSet_eq_fun hcr ((measurable_fst.comp measurable_snd).comp measurable_fst)
    have e : (fun r : (Q × α × ℝ) × E d =>
        (c r.1.1 ⁻¹' {r.1.2.1}).indicator (fun θ => gaussianPDFReal (s r.1.1 θ) (noiseVar sc) r.1.2.2) r.2) =
        {r : (Q × α × ℝ) × E d | c r.1.1 r.2 = r.1.2.1}.indicator
          (fun r => gaussianPDFReal (s r.1.1 r.2) (noiseVar sc) r.1.2.2) := by
      rfl
    rw [e]
    exact (measurable_uncurry_gaussianPDFReal.comp (hsr.prodMk (measurable_const.prodMk
      ((measurable_snd.comp measurable_snd).comp measurable_fst)))).indicator hset
  have hZ : Measurable (fun r : Q × α × ℝ =>
      normZ (π0.withDensity (g (hp r.1))) (c r.1) (s r.1) (noiseVar sc) r.2.1 r.2.2) :=
    measurable_integral_dens π0 hg hfin (hhp.comp measurable_fst) hF1
  have hsq : Measurable (fun p : (Q × E d) × ℝ => s p.1.1 p.1.2) := hs.comp measurable_fst
  have hy : Measurable (fun p : (Q × E d) × ℝ => s p.1.1 p.1.2 + sc * p.2) :=
    hsq.add (measurable_const.mul measurable_snd)
  have hZ' := hZ.comp ((measurable_fst.comp measurable_fst).prodMk ((hc.comp measurable_fst).prodMk hy))
  have hφ : Measurable (fun p : (Q × E d) × ℝ =>
      gaussianPDFReal (s p.1.1 p.1.2) (noiseVar sc) (s p.1.1 p.1.2 + sc * p.2)) :=
    measurable_uncurry_gaussianPDFReal.comp (hsq.prodMk (measurable_const.prodMk hy))
  have hG : Measurable (fun p : (Q × E d) × ℝ =>
      infoDens (π0.withDensity (g (hp p.1.1))) (c p.1.1) (s p.1.1) sc p.1.2 p.2) :=
    by unfold infoDens; exact Real.measurable_log.comp (hφ.div hZ')
  have hI : Measurable (fun p : Q × E d =>
      ∫ z, infoDens (π0.withDensity (g (hp p.1))) (c p.1) (s p.1) sc p.2 z ∂gaussianReal 0 1) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  exact measurable_integral_dens π0 hg hfin hhp hI

/-- The divergence from the prior is measurable in the parameter of the density. -/
theorem measurable_klDens_dens {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H] (π₀ : Measure Θ) [SFinite π₀]
    {g : H → Θ → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) : Measurable (fun h => klDens π₀ (g h)) := by
  have hF : Measurable (fun p : H × Θ => (g p.1 p.2).toReal * Real.log (g p.1 p.2).toReal) :=
    hg.ennreal_toReal.mul (Real.measurable_log.comp hg.ennreal_toReal)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := π₀)).measurable

end HistMeas

/-! ## The game -/

section Game

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The density after a round with the play `x`, the observation `y` and the answer `a`. -/
theorem dens_succ_push (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (t : ℕ)
    (h : Hist d (Option Cell)) (x : E d) (y : ℝ) (a : Option Cell) :
    dens π0 R sc (t + 1) (Hist.push h t x y a) =
      updDens π0 (dens π0 R sc t h)
        (lik (R.ans (post π0 R sc t h) x) (R.sig (post π0 R sc t h) x) (noiseVar sc) a y) := by
  have hc : dens π0 R sc t (Hist.push h t x y a) = dens π0 R sc t h :=
    dens_congr π0 R sc t _ h fun i hi => by simp [Hist.push, Function.update_of_ne (Nat.ne_of_lt hi)]
  rw [dens_succ, hc]
  simp only [updDens, roundLik, Hist.push, Function.update_self, post]
  exact if_congr Iff.rfl rfl rfl

/-- The information of round `t` on the sample `s`. -/
noncomputable def infoRound (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (pol : Learner Ω d)
    (t : ℕ) (s : Sample d Ω) : ℝ :=
  infoJ (post π0 R sc t (hist π0 R sc pol t s))
    (R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)))
    (R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s))) sc

omit [MeasurableSpace Ω] in
/-- The information of a round lies between `0` and the number of answers plus `S₀²/(2σ²)`. -/
theorem infoRound_bounds (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell))
    (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ} {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) {t : ℕ} (ht : t < n)
    (s : Sample d Ω) :
    0 ≤ infoRound π0 R sc pol t s ∧
      infoRound π0 R sc pol t s ≤ Fintype.card (Option Cell) + S₀ ^ 2 / (2 * sc ^ 2) := by
  unfold infoRound
  generalize hist π0 R sc pol t s = h
  have : IsProbabilityMeasure (post π0 R sc t h) := isProbabilityMeasure_post π0 R hR sc t h
  have hmr := measurable_rule_post π0 R hR sc t
  have hg : Measurable (fun θ : E d => (h, play pol t s.2.2 h, θ)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hc : Measurable (R.ans (post π0 R sc t h) (play pol t s.2.2 h)) := by
    have h' := hmr.1.comp hg
    exact h'
  have hs : Measurable (R.sig (post π0 R sc t h) (play pol t s.2.2 h)) := by
    have h' := hmr.2.comp hg
    exact h'
  have hb : ∀ θ, |R.sig (post π0 R sc t h) (play pol t s.2.2 h) θ| ≤ S₀ := fun θ => hsb t ht h θ s.2.2
  refine ⟨infoJ_nonneg (post π0 R sc t h) hc hs hb hsc, ?_⟩
  have hch := infoJ_chain (post π0 R sc t h) hc hs hb hsc (fun _ => 0)
  beta_reduce at hch
  have he := ansEntropy_le (post π0 R sc t h) (R.ans (post π0 R sc t h) (play pol t s.2.2 h))
  have hq := sum_setIntegral_sq_le (post π0 R sc t h) hc hs hb sc
  linarith

/-- The information of a round is integrable over the game (its signal bounded by `S₀` along the plays). -/
theorem integrable_infoRound (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Rule d (Option Cell)) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0)
    {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) {t : ℕ} (ht : t < n) :
    Integrable (infoRound π0 R sc pol t) (gameLaw π0 μ) := by
  have : IsProbabilityMeasure (gameLaw π0 μ) := isProbabilityMeasure_gameLaw π0 μ
  have hhist := measurable_hist π0 R hR sc hpol ht.le
  have hmr := measurable_rule_post π0 R hR sc t
  have hq : Measurable (fun q : Sample d Ω => (q.2.2, hist π0 R sc pol t q)) :=
    (measurable_snd.comp measurable_snd).prodMk hhist
  have hx : Measurable (fun q : Sample d Ω => play pol t q.2.2 (hist π0 R sc pol t q)) := by
    have h' := (measurable_play (α := Option Cell) (hpol t ht)).comp hq
    exact h'
  have hq2 : Measurable (fun p : Sample d Ω × E d =>
      (hist π0 R sc pol t p.1, play pol t p.1.2.2 (hist π0 R sc pol t p.1), p.2)) :=
    (hhist.comp measurable_fst).prodMk ((hx.comp measurable_fst).prodMk measurable_snd)
  have hcm : Measurable (Function.uncurry fun (q : Sample d Ω) (θ : E d) =>
      R.ans (post π0 R sc t (hist π0 R sc pol t q)) (play pol t q.2.2 (hist π0 R sc pol t q)) θ) := by
    have h' := hmr.1.comp hq2
    exact h'
  have hsm : Measurable (Function.uncurry fun (q : Sample d Ω) (θ : E d) =>
      R.sig (post π0 R sc t (hist π0 R sc pol t q)) (play pol t q.2.2 (hist π0 R sc pol t q)) θ) := by
    have h' := hmr.2.comp hq2
    exact h'
  have hm : Measurable (infoRound π0 R sc pol t) := by
    have h' := measurable_infoJ_dens π0 (measurable_dens π0 R hR sc t) (dens_props π0 R hR sc t).2.1 hhist hcm hsm sc
    exact h'
  refine Integrable.of_bound hm.aestronglyMeasurable (Fintype.card (Option Cell) + S₀ ^ 2 / (2 * sc ^ 2))
    (ae_of_all _ fun s => ?_)
  obtain ⟨h0, h1⟩ := infoRound_bounds π0 R hR hsc hsb ht s
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- (S2) over one round of the game: `E K(π_{t+1}) = E K(π_t) + E J_t`. -/
theorem kl_step (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) {t : ℕ} (ht : t < n) :
    ∫⁻ s, ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1) (hist π0 R sc pol (t + 1) s))) ∂gameLaw π0 μ =
      ∫⁻ s, ENNReal.ofReal (klDens π0 (dens π0 R sc t (hist π0 R sc pol t s))) ∂gameLaw π0 μ +
        ENNReal.ofReal (∫ s, infoRound π0 R sc pol t s ∂gameLaw π0 μ) := by
  have hKm : ∀ k, Measurable (fun h : Hist d (Option Cell) => ENNReal.ofReal (klDens π0 (dens π0 R sc k h))) :=
    fun k => ENNReal.measurable_ofReal.comp (measurable_klDens_dens π0 (measurable_dens π0 R hR sc k))
  have hΨ : Measurable (fun p : E d × Hist d (Option Cell) × Ω =>
      ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1) p.2.1))) := by
    have hp : Measurable (fun p : E d × Hist d (Option Cell) × Ω => p.2.1) := measurable_fst.comp measurable_snd
    have h' := (hKm (t + 1)).comp hp
    exact h'
  have hexp := hist_succ_expand π0 μ R hR hsc hpol ht hΨ
  dsimp only at hexp
  rw [hexp]
  have hJI := integrable_infoRound π0 μ R hR hsc hpol hsb ht
  have hKt : Measurable (fun s => ENNReal.ofReal (klDens π0 (dens π0 R sc t (hist π0 R sc pol t s)))) := by
    have h' := (hKm t).comp (measurable_hist π0 R hR sc hpol ht.le)
    exact h'
  rw [ofReal_integral_eq_lintegral_ofReal hJI (ae_of_all _ fun s => (infoRound_bounds π0 R hR hsc hsb ht s).1),
    ← lintegral_add_left hKt]
  refine lintegral_congr fun s => ?_
  have hJ0 := (infoRound_bounds π0 R hR hsc hsb ht s).1
  unfold infoRound at hJ0 ⊢
  have hb : ∀ θ, |R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) θ| ≤ S₀ :=
    fun θ => hsb t ht _ θ s.2.2
  revert hb hJ0
  generalize hist π0 R sc pol t s = h
  intro hJ0 hb
  simp only [dens_succ_push]
  have hP : IsProbabilityMeasure (post π0 R sc t h) := isProbabilityMeasure_post π0 R hR sc t h
  obtain ⟨C, hC, hρC⟩ := dens_le_bound π0 R sc t h
  have hρ : Measurable (dens π0 R sc t h) := by
    have h' := (measurable_dens π0 R hR sc t).comp (measurable_prodMk_left (x := h))
    exact h'
  have h1 := (dens_props π0 R hR sc t).2.2 h
  have hmr := measurable_rule_post π0 R hR sc t
  have hg : Measurable (fun θ : E d => (h, play pol t s.2.2 h, θ)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hc : Measurable (R.ans (post π0 R sc t h) (play pol t s.2.2 h)) := by
    have h' := hmr.1.comp hg
    exact h'
  have hs : Measurable (R.sig (post π0 R sc t h) (play pol t s.2.2 h)) := by
    have h' := hmr.2.comp hg
    exact h'
  obtain ⟨hI, hE⟩ := kl_round π0 hρ hC hρC h1 hc hs hb hsc
  have hlik := measurable_lik hc hs (noiseVar sc)
  have hK0 : ∀ p : E d × ℝ, 0 ≤ klDens π0 (updDens π0 (dens π0 R sc t h)
      (lik (R.ans (post π0 R sc t h) (play pol t s.2.2 h)) (R.sig (post π0 R sc t h) (play pol t s.2.2 h))
        (noiseVar sc) (R.ans (post π0 R sc t h) (play pol t s.2.2 h) p.1)
        (R.sig (post π0 R sc t h) (play pol t s.2.2 h) p.1 + sc * p.2))) := by
    intro p
    have hL : Measurable (lik (R.ans (post π0 R sc t h) (play pol t s.2.2 h))
        (R.sig (post π0 R sc t h) (play pol t s.2.2 h)) (noiseVar sc) (R.ans (post π0 R sc t h) (play pol t s.2.2 h) p.1)
        (R.sig (post π0 R sc t h) (play pol t s.2.2 h) p.1 + sc * p.2)) := by
      have h' := hlik.comp (measurable_prodMk_left (x := (R.ans (post π0 R sc t h) (play pol t s.2.2 h) p.1,
        R.sig (post π0 R sc t h) (play pol t s.2.2 h) p.1 + sc * p.2)))
      exact h'
    exact klDens_nonneg π0 (measurable_updDens π0 hρ hL) (lintegral_updDens π0 hρ hL h1)
  have hKρ : 0 ≤ klDens π0 (dens π0 R sc t h) := klDens_nonneg π0 hρ h1
  refine (lintegral_ofReal_prod (μ := post π0 R sc t h) (ν := gaussianReal 0 1) hI hK0).trans ?_
  rw [← ENNReal.ofReal_add hKρ hJ0]
  exact congrArg ENNReal.ofReal hE

/-- (S2) summed over the game: `∑_{t < n} E J_t = E K(π_n)`. -/
theorem sum_infoRound (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) :
    ∑ t ∈ Finset.range n, ENNReal.ofReal (∫ s, infoRound π0 R sc pol t s ∂gameLaw π0 μ) =
      ∫⁻ s, ENNReal.ofReal (klDens π0 (dens π0 R sc n (hist π0 R sc pol n s))) ∂gameLaw π0 μ := by
  have key : ∀ m ≤ n, ∑ t ∈ Finset.range m, ENNReal.ofReal (∫ s, infoRound π0 R sc pol t s ∂gameLaw π0 μ) =
      ∫⁻ s, ENNReal.ofReal (klDens π0 (dens π0 R sc m (hist π0 R sc pol m s))) ∂gameLaw π0 μ := by
    intro m hm
    induction m with
    | zero =>
      have h0 : ∀ s, klDens π0 (dens π0 R sc 0 (hist π0 R sc pol 0 s)) = 0 := fun _ => klDens_one π0
      simp [h0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm), kl_step π0 μ R hR hsc hpol hsb (Nat.lt_of_succ_le hm)]
  exact key n le_rfl

/-- The chain-rule lemma and the count lemma (b) over the game, the field `count` of `GameFacts`:
`N* P(π_n has fewer than d/2 live directions) ≤ ∑_{t < n} E J_t`. -/
theorem count_game (hd : 1 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Rule d (Option Cell))
    (hR : R.Meas (prior d (1 / 2))) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post (prior d (1 / 2)) R sc t h) (play pol t ω h) θ| ≤ S₀) {w : ℝ}
    (hw : 0 < w) (hX : Real.exp 1 / 2 ≤ xCount d w) :
    nStar d w * (gameLaw (prior d (1 / 2)) μ).real
        {s | dLive w (covM (post (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s))) < d / 2} ≤
      ∑ t ∈ Finset.range n, ∫ s, infoRound (prior d (1 / 2)) R sc pol t s ∂gameLaw (prior d (1 / 2)) μ := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have : IsProbabilityMeasure (prior d (1 / 2)) := isProbabilityMeasure_prior d hr
  have : IsProbabilityMeasure (gameLaw (prior d (1 / 2)) μ) := isProbabilityMeasure_gameLaw _ μ
  have hsum := sum_infoRound (prior d (1 / 2)) μ R hR hsc hpol hsb
  have hJ0 : ∀ t ∈ Finset.range n,
      0 ≤ ∫ s, infoRound (prior d (1 / 2)) R sc pol t s ∂gameLaw (prior d (1 / 2)) μ := fun t ht =>
    integral_nonneg fun s => (infoRound_bounds _ R hR hsc hsb (Finset.mem_range.1 ht) s).1
  rw [← ENNReal.ofReal_sum_of_nonneg hJ0] at hsum
  have hsum0 := Finset.sum_nonneg hJ0
  by_cases hN : nStar d w ≤ 0
  · have := measureReal_nonneg (μ := gameLaw (prior d (1 / 2)) μ)
      (s := {s | dLive w (covM (post (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s))) < d / 2})
    nlinarith
  push Not at hN
  have hAE : AEMeasurable (fun s => ENNReal.ofReal (klDens (prior d (1 / 2))
      (dens (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s)))) (gameLaw (prior d (1 / 2)) μ) :=
    (ENNReal.measurable_ofReal.comp ((measurable_klDens_dens _ (measurable_dens _ R hR sc n)).comp
      (measurable_hist _ R hR sc hpol le_rfl))).aemeasurable
  have hmk := mul_meas_ge_le_lintegral₀ hAE (ENNReal.ofReal (nStar d w))
  have hsub : {s | dLive w (covM (post (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s))) < d / 2} ⊆
      {s | ENNReal.ofReal (nStar d w) ≤ ENNReal.ofReal (klDens (prior d (1 / 2))
        (dens (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s)))} := by
    intro s hs
    obtain ⟨C, hC, hρC⟩ := dens_le_bound (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s)
    have hρ : Measurable (dens (prior d (1 / 2)) R sc n (hist (prior d (1 / 2)) R sc pol n s)) := by
      have h' := (measurable_dens (prior d (1 / 2)) R hR sc n).comp
        (measurable_prodMk_left (x := hist (prior d (1 / 2)) R sc pol n s))
      exact h'
    exact ENNReal.ofReal_le_ofReal
      (count_b hd hw hX hρ hC hρC ((dens_props _ R hR sc n).2.2 _) hs)
  have h2 := le_trans (mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le) hmk
  rw [← hsum] at h2
  rw [← ENNReal.ofReal_le_ofReal_iff hsum0, ENNReal.ofReal_mul hN.le, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact h2

end Game

end AdversarialBco.Lower
