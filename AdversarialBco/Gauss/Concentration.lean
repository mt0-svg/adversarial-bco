/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Gauss.MaureyPisier

@[expose] public section

/-!
# Gaussian concentration for Lipschitz functions

The weaker form of Theorem A.1 of the paper proved in Lean (Section 9.2 of the paper), with the constant `2 / π^2`
in place of `1/2` in the exponent.

* `cloud b S`: the law of `b + S g` on `ℝ^d`, `g` standard Gaussian on `ℝ^k` (Mathlib's `stdGaussian` on
  `EuclideanSpace ℝ (Fin k)`), `S` a linear map. Mathlib's `multivariateGaussian b A` is `cloud b S` with
  `S = toEuclideanCLM (CFC.sqrt A)` (`multivariateGaussian_eq_cloud`).
* `GaussConcAt c`: for every `L`-Lipschitz `F : ℝ^d → ℝ`, `F` is integrable under `cloud b S` and its upper tail
  about the mean satisfies `P(F - E F ≥ r) ≤ exp(-c r^2 / (L ‖S‖)^2)` for `r ≥ 0`.
* `GaussConc`: `GaussConcAt c` for some absolute `c > 0`.
* `gaussConcAt : GaussConcAt (2 / π^2)`, from the Maurey and Pisier argument of
  `AdversarialBco/Gauss/MaureyPisier.lean`, a smoothing of `F` by a bump (Part 1) and the limit of the smoothing
  radius to `0` (Part 3).

Junk values. If `L ‖S‖ = 0` the exponent is `-(c r^2) / 0 = 0` and the bound reads `≤ 1`, which is true; the
statement is then weaker than the truth (the tail is `0` for `r > 0`), never false. The mean `∫ F ∂(cloud b S)` is
not a junk value since `F` is integrable (first conjunct).
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace AdversarialBco.Gauss

/-- The law of `b + S g` on `ℝ^d`, `g` a standard Gaussian vector of `ℝ^k`: the Gaussian `N(b, S Sᵀ)`. -/
noncomputable def cloud {k d : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun g => b + S g)

instance isProbabilityMeasure_cloud {k d : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d)) : IsProbabilityMeasure (cloud b S) :=
  by unfold cloud; infer_instance

/-- Gaussian concentration for Lipschitz functions with the constant `c` in the exponent: under every Gaussian
cloud `N(b, S Sᵀ)` an `L`-Lipschitz function is integrable and has upper tail
`P(F - E F ≥ r) ≤ exp(-c r^2 / (L ‖S‖)^2)` about its mean, for every `r ≥ 0`. -/
def GaussConcAt (c : ℝ) : Prop :=
  ∀ (k d : ℕ) (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : NNReal), LipschitzWith L F →
      Integrable F (cloud b S) ∧
        ∀ r : ℝ, 0 ≤ r →
          (cloud b S).real {x | (∫ y, F y ∂cloud b S) + r ≤ F x} ≤
            Real.exp (-(c * r ^ 2) / ((L : ℝ) * ‖S‖) ^ 2)

/-! ## Part 1. Smoothing a Lipschitz function by a bump -/

section smoothing

open MeasureTheory Metric
open scoped NNReal Convolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A Lipschitz function is uniformly approximated by smooth functions with the same Lipschitz constant. -/
theorem exists_contDiff_lipschitz_approx (F : E → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F) (ε : ℝ)
    (hε : 0 < ε) : ∃ G : E → ℝ, ContDiff ℝ 1 G ∧ LipschitzWith L G ∧ ∀ x, |G x - F x| ≤ L * ε := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hloc : LocallyIntegrable F μ := hF.continuous.locallyIntegrable
  refine ⟨φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] F, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hloc
  · have hex : ∀ x, ConvolutionExistsAt (φ.normed μ) F x (ContinuousLinearMap.lsmul ℝ ℝ) μ := fun x =>
      φ.hasCompactSupport_normed.convolutionExists_left _ φ.continuous_normed hloc x
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, convolution_def, convolution_def, ← integral_sub (hex x) (hex y)]
    calc |∫ t, ((ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed μ t) (F (x - t)) -
            (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed μ t) (F (y - t))) ∂μ|
        ≤ ∫ t, φ.normed μ t * (L * dist x y) ∂μ := by
          refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ (Filter.Eventually.of_forall fun t => ?_))
          · exact (φ.integrable_normed).mul_const _
          · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_sub, abs_mul,
              abs_of_nonneg (φ.nonneg_normed t)]
            refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
            have h := hF.dist_le_mul (x - t) (y - t)
            rw [Real.dist_eq, dist_sub_right] at h
            exact h
      _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]
  · intro x
    have h := φ.dist_normed_convolution_le (μ := μ) (x₀ := x) hF.continuous.aestronglyMeasurable
      (ε := L * ε) fun y hy => by
        refine (hF.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left ?_ L.2)
        exact (mem_ball.1 hy).le
    rwa [Real.dist_eq] at h

end smoothing

/-! ## Part 2. Two lemmas on exponential moments -/

open MeasureTheory in
/-- Exponential moments of two variables at uniform distance at most `δ`. -/
theorem mgf_centered_le_of_close {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (δ l : ℝ) (hXY : ∀ ω, |X ω - Y ω| ≤ δ) (hX : Integrable X μ)
    (hY : Integrable Y μ) (hYe : Integrable (fun ω => Real.exp (l * (Y ω - ∫ ω', Y ω' ∂μ))) μ) :
    ∫ ω, Real.exp (l * (X ω - ∫ ω', X ω' ∂μ)) ∂μ ≤
      Real.exp (2 * |l| * δ) * ∫ ω, Real.exp (l * (Y ω - ∫ ω', Y ω' ∂μ)) ∂μ := by
  set mX := ∫ ω, X ω ∂μ with hmX
  set mY := ∫ ω, Y ω ∂μ with hmY
  have h_diff_bound : |mX - mY| ≤ δ := by
    have h_sub : mX - mY = ∫ ω, (X ω - Y ω) ∂μ := by
      rw [hmX, hmY, MeasureTheory.integral_sub hX hY]
    rw [h_sub]
    calc
      |∫ ω, (X ω - Y ω) ∂μ| ≤ ∫ ω, |X ω - Y ω| ∂μ :=
        MeasureTheory.abs_integral_le_integral_abs (f := X - Y)
      _ ≤ ∫ ω, δ ∂μ := by
        refine MeasureTheory.integral_mono ?_ ?_ (fun ω => hXY ω)
        · exact (hX.sub hY).abs
        · exact integrable_const δ
      _ = δ := by simp
  have h_pointwise : ∀ ω, Real.exp (l * (X ω - mX)) ≤
      Real.exp (2 * |l| * δ) * Real.exp (l * (Y ω - mY)) := by
    intro ω
    have h_diff_bound' : |(X ω - mX) - (Y ω - mY)| ≤ 2 * δ := by
      calc
        |(X ω - mX) - (Y ω - mY)| = |(X ω - Y ω) - (mX - mY)| := by ring_nf
        _ ≤ |X ω - Y ω| + |mX - mY| := abs_sub _ _
        _ ≤ δ + δ := add_le_add (hXY ω) h_diff_bound
        _ = 2 * δ := by ring
    have h_val : l * (X ω - mX) - l * (Y ω - mY) ≤ 2 * |l| * δ := by
      have h_eq : l * (X ω - mX) - l * (Y ω - mY) = l * ((X ω - mX) - (Y ω - mY)) := by ring
      rw [h_eq]
      calc
        l * ((X ω - mX) - (Y ω - mY)) ≤ |l * ((X ω - mX) - (Y ω - mY))| :=
          le_abs_self _
        _ = |l| * |(X ω - mX) - (Y ω - mY)| := by rw [abs_mul]
        _ ≤ |l| * (2 * δ) := by gcongr
        _ = 2 * |l| * δ := by ring
    calc
      Real.exp (l * (X ω - mX)) = Real.exp ((l * (Y ω - mY)) + (l * (X ω - mX) - l * (Y ω - mY))) := by ring_nf
      _ = Real.exp (l * (Y ω - mY)) * Real.exp (l * (X ω - mX) - l * (Y ω - mY)) := by
        rw [Real.exp_add]
      _ ≤ Real.exp (l * (Y ω - mY)) * Real.exp (2 * |l| * δ) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_val) (Real.exp_pos _).le
      _ = Real.exp (2 * |l| * δ) * Real.exp (l * (Y ω - mY)) := by ring
  have h_int_right : Integrable (fun ω => Real.exp (2 * |l| * δ) * Real.exp (l * (Y ω - mY))) μ := by
    exact hYe.const_mul (Real.exp (2 * |l| * δ))
  have h_int_left : Integrable (fun ω => Real.exp (l * (X ω - mX))) μ := by
    have h_ae : AEStronglyMeasurable (fun ω => Real.exp (l * (X ω - mX))) μ := by
      refine Real.continuous_exp.comp_aestronglyMeasurable ?_
      refine (aestronglyMeasurable_const.mul ?_)
      exact hX.aestronglyMeasurable.sub aestronglyMeasurable_const
    refine Integrable.mono h_int_right h_ae ?_
    filter_upwards with ω
    have hpos_f : 0 ≤ Real.exp (l * (X ω - mX)) := (Real.exp_pos _).le
    have hpos_g : 0 ≤ Real.exp (2 * |l| * δ) * Real.exp (l * (Y ω - mY)) :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    simp [Real.norm_eq_abs, abs_of_nonneg hpos_f, h_pointwise ω]
  rw [hmX, hmY]
  calc
    ∫ ω, Real.exp (l * (X ω - ∫ ω', X ω' ∂μ)) ∂μ = ∫ ω, Real.exp (l * (X ω - mX)) ∂μ := by rfl
    _ ≤ ∫ ω, Real.exp (2 * |l| * δ) * Real.exp (l * (Y ω - mY)) ∂μ :=
      MeasureTheory.integral_mono h_int_left h_int_right h_pointwise
    _ = Real.exp (2 * |l| * δ) * ∫ ω, Real.exp (l * (Y ω - mY)) ∂μ := by rw [integral_const_mul]
    _ = Real.exp (2 * |l| * δ) * ∫ ω, Real.exp (l * (Y ω - ∫ ω', Y ω' ∂μ)) ∂μ := by rfl

open Filter Topology in
/-- An inequality that holds up to every positive excess holds. -/
theorem le_of_forall_exp_mul (M B c : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (h : ∀ ε, 0 < ε → M ≤ Real.exp (c * ε) * B) : M ≤ B := by
  have h_cont : ContinuousAt (fun (ε : ℝ) => Real.exp (c * ε) * B) 0 := by
    have h_inner : ContinuousAt (fun (ε : ℝ) => c * ε) 0 :=
      (continuous_const.mul continuous_id).continuousAt
    have h_exp_cont : ContinuousAt (fun (ε : ℝ) => Real.exp (c * ε)) 0 :=
      Real.continuous_exp.continuousAt.comp h_inner
    exact h_exp_cont.mul_const B
  have h_tendsto : Tendsto (fun (ε : ℝ) => Real.exp (c * ε) * B) (𝓝 0) (𝓝 B) := by
    simpa [Real.exp_zero, mul_zero, one_mul] using h_cont.tendsto
  have h_tendsto' : Tendsto (fun (ε : ℝ) => Real.exp (c * ε) * B) (𝓝[>] 0) (𝓝 B) :=
    h_tendsto.mono_left inf_le_left
  have h_eventually : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, M ≤ Real.exp (c * ε) * B := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    exact h ε hε
  exact ge_of_tendsto h_tendsto' h_eventually


/-! ## Part 3. Lipschitz functions, the tail, the cloud -/

section lipschitz

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of an `L`-Lipschitz function has norm at most `L`. -/
theorem norm_gradient_le_of_lipschitz {G : E → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G) (x : E) :
    ‖gradient G x‖ ≤ L := by
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Linear growth of a Lipschitz function. -/
theorem abs_le_of_lipschitz {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (x : E) :
    |F x| ≤ |F 0| + L * ‖x‖ := by
  have h := hF.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

/-- Maurey and Pisier for a Lipschitz function: under the standard Gaussian measure, `F - E F` is sub-Gaussian with
variance proxy `π^2 L^2 / 4`. Smoothing by a bump (Part 1), the port for the smooth function, and the limit of the
smoothing radius to `0`. -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitz {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂stdGaussian E) (gaussianConcentrationConst * L ^ 2)
      (stdGaussian E) := by
  set μ := stdGaussian E with hμ
  set m := ∫ y, F y ∂μ with hm
  have hgrowth : ∀ x, |F x - m| ≤ (|F 0| + |m|) + L * ‖x‖ := fun x => by
    have h1 := abs_le_of_lipschitz hF x
    have h2 := abs_sub (F x) m
    linarith
  have hmeas : AEStronglyMeasurable (fun x => F x - m) μ :=
    (hF.continuous.sub continuous_const).aestronglyMeasurable
  have hint : ∀ t, Integrable (fun x => exp (t * (F x - m))) μ := fun t =>
    integrable_exp_of_abs_le_add_mul_norm hmeas hgrowth t
  refine ⟨hint, fun t => ?_⟩
  change ∫ x, exp (t * (F x - m)) ∂μ ≤ exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2)
  have hFi : Integrable F μ :=
    integrable_of_abs_le_add_mul_norm hF.continuous.aestronglyMeasurable (abs_le_of_lipschitz hF)
  refine le_of_forall_exp_mul _ _ (2 * |t| * L) (by positivity) (exp_pos _).le fun ε hε => ?_
  obtain ⟨G, hGc, hGL, hGF⟩ := exists_contDiff_lipschitz_approx F L hF ε hε
  have hMP := hasSubgaussianMGF_sub_integral_stdGaussian (E := E) hGc (norm_gradient_le_of_lipschitz hGL)
  have hGi : Integrable G μ := integrable_of_norm_gradient_le hGc (norm_gradient_le_of_lipschitz hGL)
  have hclose := mgf_centered_le_of_close μ F G (L * ε) t (fun x => by rw [abs_sub_comm]; exact hGF x) hFi hGi
    (hMP.integrable_exp_mul t)
  calc ∫ x, exp (t * (F x - m)) ∂μ
      ≤ exp (2 * |t| * (L * ε)) * ∫ x, exp (t * (G x - ∫ y, G y ∂μ)) ∂μ := hclose
    _ ≤ exp (2 * |t| * (L * ε)) * exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2) := by
        gcongr
        exact hMP.mgf_le t
    _ = exp (2 * |t| * L * ε) * exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2) := by
        rw [← mul_assoc]

/-- The upper tail of a Lipschitz function under the standard Gaussian measure, about its mean. -/
theorem tail_stdGaussian_of_lipschitz {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussian E).real {x | (∫ y, F y ∂stdGaussian E) + r ≤ F x} ≤
      exp (-(2 / π ^ 2 * r ^ 2) / (L : ℝ) ^ 2) := by
  have h := (hasSubgaussianMGF_sub_integral_of_lipschitz hF).measure_ge_le hr
  have hset : {x | (∫ y, F y ∂stdGaussian E) + r ≤ F x} = {x | r ≤ F x - ∫ y, F y ∂stdGaussian E} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  rw [NNReal.coe_mul, NNReal.coe_pow, coe_gaussianConcentrationConst]
  ring

end lipschitz

section cloud

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- Gaussian concentration for Lipschitz functions under every cloud, with the constant `2/π^2` of Maurey and
Pisier. -/
theorem gaussConcAt : GaussConcAt (2 / π ^ 2) := by
  intro k d b S F L hF
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  have hmap : Measurable (fun g => b + S g) := by fun_prop
  have hFm : AEStronglyMeasurable F (cloud b S) := hF.continuous.aestronglyMeasurable
  have h1 : LipschitzWith ‖S‖₊ (fun g => b + S g) := by
    have := ((isometry_add_left b).lipschitzWith).comp S.lipschitzWith
    simpa [Function.comp_def] using this
  have hG : LipschitzWith (L * ‖S‖₊) (fun g => F (b + S g)) := hF.comp h1
  have hGi : Integrable (fun g => F (b + S g)) μ :=
    integrable_of_abs_le_add_mul_norm hG.continuous.aestronglyMeasurable (abs_le_of_lipschitz hG)
  have hint_eq : ∫ y, F y ∂cloud b S = ∫ g, F (b + S g) ∂μ := integral_map hmap.aemeasurable hFm
  refine ⟨(integrable_map_measure hFm hmap.aemeasurable).2 hGi, fun r hr => ?_⟩
  have hs : MeasurableSet {x | (∫ g, F (b + S g) ∂μ) + r ≤ F x} :=
    measurableSet_le measurable_const hF.continuous.measurable
  have hreal : (cloud b S).real {x | (∫ y, F y ∂cloud b S) + r ≤ F x} =
      μ.real {g | (∫ g', F (b + S g') ∂μ) + r ≤ F (b + S g)} := by
    rw [hint_eq]
    unfold cloud
    rw [map_measureReal_apply hmap hs]
    rfl
  rw [hreal]
  refine (tail_stdGaussian_of_lipschitz hG hr).trans_eq ?_
  rw [NNReal.coe_mul, coe_nnnorm]

end cloud

end AdversarialBco.Gauss
