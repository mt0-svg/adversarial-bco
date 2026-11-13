/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Moments of a law on `ℝ^d` and the prior

For the paper's section on the lower bound: the frame reads the mean and the covariance of the law of the tip; the
ledger
`Λ(π) = (1/2) ln det(Σ(π) + w² I)` and the cell moments `S_c`; the prior, uniform on `r₀ B^d`.

* `meanV π = ∫ θ dπ`; `secMom π m = ∫ (θ - m)(θ - m)ᵀ dπ` (the second moment about the point `m`, as a matrix;
  `secMom (π.restrict c) m = p_c S_c` is the unnormalised moment of a cell); `covM π = secMom π (meanV π)`.
* `prior d r₀`: the uniform law on the closed ball `r₀ B^d`.
* The quadratic forms (`quad_secMom`, `bilin_secMom`, `trace_mul_secMom`), positivity, `covM ≤ secMom` (the covariance
  is the least second moment), additivity over a finite partition (`sum_secMom_restrict`), the trace bound on the ball.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal NNReal

namespace AdversarialBco.Lower

variable {d : ℕ}

/-- The mean of a law on `ℝ^d`. -/
noncomputable def meanV (π : Measure (E d)) : E d := ∫ θ, θ ∂π

/-- The second moment of `π` about the point `m`, `∫ (θ - m)(θ - m)ᵀ dπ`. -/
noncomputable def secMom (π : Measure (E d)) (m : E d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π

/-- The covariance of a law on `ℝ^d`. -/
noncomputable def covM (π : Measure (E d)) : Matrix (Fin d) (Fin d) ℝ := secMom π (meanV π)

/-- The prior: the uniform law on the closed ball `r₀ B^d`. -/
noncomputable def prior (d : ℕ) (r₀ : ℝ) : Measure (E d) :=
  ProbabilityTheory.cond volume (Metric.closedBall (0 : E d) r₀)

/-! ## The prior -/

theorem isProbabilityMeasure_prior (d : ℕ) {r₀ : ℝ} (hr : 0 < r₀) : IsProbabilityMeasure (prior d r₀) := by
  have hvol_ne_zero : volume (Metric.closedBall (0 : E d) r₀) ≠ 0 := by
    have hpos := Metric.measure_closedBall_pos volume (0 : E d) hr
    exact hpos.ne.symm
  have hvol_ne_top : volume (Metric.closedBall (0 : E d) r₀) ≠ ∞ := by
    exact measure_closedBall_lt_top.ne
  unfold prior
  exact cond_isProbabilityMeasure_of_finite hvol_ne_zero hvol_ne_top

theorem prior_ae_mem (d : ℕ) (r₀ : ℝ) : ∀ᵐ θ ∂prior d r₀, θ ∈ Metric.closedBall (0 : E d) r₀ := by
  apply ProbabilityTheory.ae_cond_mem
  exact measurableSet_closedBall

/-! ## Quadratic forms -/

/-- Each entry of the second moment is integrable when `‖θ‖²` is. -/
theorem integrable_secMom_entry (π : Measure (E d)) [IsFiniteMeasure π]
    (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) (m : E d) (i j : Fin d) :
    Integrable (fun θ : E d => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) π := by
  have hmeas : AEStronglyMeasurable (fun θ : E d => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) π := by
    fun_prop
  have hintegrable_bound : Integrable (fun θ : E d => 2 * ‖θ‖ ^ 2 + 2 * ‖m‖ ^ 2) π := by
    have h1 : Integrable (fun θ : E d => 2 * ‖θ‖ ^ 2) π := by
      simpa [mul_comm] using h2.mul_const (2 : ℝ)
    have h2const : Integrable (fun _ : E d => 2 * ‖m‖ ^ 2) π := by
      rw [MeasureTheory.integrable_const_iff]
      right
      exact inferInstance
    exact h1.add h2const
  have hbound : ∀ᵐ θ ∂π, ‖(θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)‖ ≤ 2 * ‖θ‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
    filter_upwards [] with θ
    have h_factor_i : ‖θ.ofLp i - m.ofLp i‖ ≤ ‖θ‖ + ‖m‖ := by
      calc
        ‖θ.ofLp i - m.ofLp i‖ ≤ ‖θ.ofLp i‖ + ‖m.ofLp i‖ := norm_sub_le _ _
        _ ≤ ‖θ‖ + ‖m.ofLp i‖ := add_le_add (PiLp.norm_apply_le θ i) (le_refl _)
        _ ≤ ‖θ‖ + ‖m‖ := add_le_add (le_refl _) (PiLp.norm_apply_le m i)
    have h_factor_j : ‖θ.ofLp j - m.ofLp j‖ ≤ ‖θ‖ + ‖m‖ := by
      calc
        ‖θ.ofLp j - m.ofLp j‖ ≤ ‖θ.ofLp j‖ + ‖m.ofLp j‖ := norm_sub_le _ _
        _ ≤ ‖θ‖ + ‖m.ofLp j‖ := add_le_add (PiLp.norm_apply_le θ j) (le_refl _)
        _ ≤ ‖θ‖ + ‖m‖ := add_le_add (le_refl _) (PiLp.norm_apply_le m j)
    have h_nonneg_sum : 0 ≤ ‖θ‖ + ‖m‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖(θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)‖ = ‖θ.ofLp i - m.ofLp i‖ * ‖θ.ofLp j - m.ofLp j‖ := by
        simp [norm_mul (θ.ofLp i - m.ofLp i) (θ.ofLp j - m.ofLp j)]
      _ ≤ (‖θ‖ + ‖m‖) * (‖θ‖ + ‖m‖) :=
        mul_le_mul h_factor_i h_factor_j (norm_nonneg _) h_nonneg_sum
      _ = (‖θ‖ + ‖m‖) ^ 2 := by ring
      _ ≤ 2 * (‖θ‖ ^ 2 + ‖m‖ ^ 2) := add_sq_le
      _ = 2 * ‖θ‖ ^ 2 + 2 * ‖m‖ ^ 2 := by ring
  exact Integrable.mono' hintegrable_bound hmeas hbound

/-- `uᵀ S v = ∫ ⟪u, θ - m⟫ ⟪v, θ - m⟫ dπ`. -/
theorem bilin_secMom (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m u v : E d) :
    u.ofLp ⬝ᵥ (secMom π m *ᵥ v.ofLp) = ∫ θ, ⟪u, θ - m⟫ * ⟪v, θ - m⟫ ∂π := by
  have h_int_entry (i j : Fin d) : Integrable (fun θ : E d => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) π :=
    integrable_secMom_entry π h2 m i j
  have h_int_inner (i j : Fin d) : Integrable (fun θ : E d => u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j) π := by
    have h := (h_int_entry i j).const_mul (u.ofLp i * v.ofLp j)
    refine h.congr (by
      filter_upwards with θ
      ring)
  have h_int_outer (i : Fin d) : Integrable (fun θ : E d => ∑ j : Fin d, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j) π :=
    integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => h_int_inner i j)
  have h_int_outer' (i : Fin d) (hi : i ∈ (Finset.univ : Finset (Fin d))) : Integrable (fun θ : E d => ∑ j : Fin d, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j) π :=
    h_int_outer i
  calc
    u.ofLp ⬝ᵥ (secMom π m *ᵥ v.ofLp)
        = ∑ i, ∑ j, u.ofLp i * ((secMom π m) i j * v.ofLp j) := by
          simp [dotProduct, mulVec_apply_eq_sum, Finset.mul_sum]
    _ = ∑ i, ∑ j, u.ofLp i * ((∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π) * v.ofLp j) := by
          simp [secMom]
    _ = ∑ i, ∑ j, (∫ θ, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j ∂π) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      calc
        u.ofLp i * ((∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π) * v.ofLp j)
            = (u.ofLp i * (∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π)) * v.ofLp j := by ring
        _ = (∫ θ, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) ∂π) * v.ofLp j := by
              rw [← integral_const_mul]
        _ = ∫ θ, (u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j))) * v.ofLp j ∂π := by
              rw [← integral_mul_const]
        _ = ∫ θ, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j ∂π := by ring
    _ = ∫ θ, ∑ i, ∑ j, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j ∂π := by
      rw [integral_finsetSum (Finset.univ : Finset (Fin d)) h_int_outer']
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← integral_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj => h_int_inner i j)]
    _ = ∫ θ, (∑ i, u.ofLp i * (θ.ofLp i - m.ofLp i)) * (∑ j, v.ofLp j * (θ.ofLp j - m.ofLp j)) ∂π := by
      refine integral_congr_ae ?_
      filter_upwards with θ
      calc
        ∑ i, ∑ j, u.ofLp i * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) * v.ofLp j
            = ∑ i, ∑ j, (u.ofLp i * (θ.ofLp i - m.ofLp i)) * (v.ofLp j * (θ.ofLp j - m.ofLp j)) := by
              simp [mul_assoc, mul_comm, mul_left_comm]
        _ = (∑ i, u.ofLp i * (θ.ofLp i - m.ofLp i)) * (∑ j, v.ofLp j * (θ.ofLp j - m.ofLp j)) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
    _ = ∫ θ, ⟪u, θ - m⟫ * ⟪v, θ - m⟫ ∂π := by
      simp [PiLp.inner_apply, mul_comm]

/-- `vᵀ S v = ∫ ⟪v, θ - m⟫² dπ`. -/
theorem quad_secMom (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m v : E d) :
    v.ofLp ⬝ᵥ (secMom π m *ᵥ v.ofLp) = ∫ θ, ⟪v, θ - m⟫ ^ 2 ∂π := by
  simpa [sq] using bilin_secMom π h2 m v v

/-- `tr(Q S) = ∫ (θ - m)ᵀ Q (θ - m) dπ`. -/
theorem trace_mul_secMom (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m : E d) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace (Q * secMom π m) = ∫ θ, (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp) ∂π := by
  have h_int (i j : Fin d) : Integrable (fun θ : E d => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) π :=
    integrable_secMom_entry π h2 m i j
  have h_int' (i j : Fin d) : Integrable (fun θ : E d => Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i))) π := by
    have := h_int j i
    simpa [mul_comm] using this.const_mul (Q i j)
  have h_int_sum_i (i : Fin d) : Integrable (fun θ : E d => ∑ j : Fin d, Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i))) π :=
    integrable_finsetSum Finset.univ fun j _ => h_int' i j
  have h_sum_eq (θ : E d) : (∑ i : Fin d, ∑ j : Fin d, Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i))) =
      (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp) := by
    simp [dotProduct, Matrix.mulVec, PiLp.sub_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]
  calc
    Matrix.trace (Q * secMom π m)
        = ∑ i, (Q * secMom π m) i i := rfl
    _ = ∑ i, ∑ j, Q i j * secMom π m j i := by
      simp [Matrix.mul_apply]
    _ = ∑ i, ∑ j, Q i j * (∫ θ, (θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i) ∂π) := by
      simp [secMom, Matrix.of_apply]
    _ = ∑ i, ∑ j, (∫ θ, Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i)) ∂π) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul (Q i j) _]
    _ = ∑ i, ∫ θ, ∑ j, Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i)) ∂π := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← integral_finsetSum Finset.univ (fun j hj => h_int' i j)]
    _ = ∫ θ, ∑ i, ∑ j, Q i j * ((θ.ofLp j - m.ofLp j) * (θ.ofLp i - m.ofLp i)) ∂π := by
      rw [← integral_finsetSum Finset.univ (fun i hi => h_int_sum_i i)]
    _ = ∫ θ, (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp) ∂π := by
      refine integral_congr_ae (ae_of_all _ h_sum_eq)

theorem secMom_isHermitian (π : Measure (E d)) (m : E d) : (secMom π m).IsHermitian := by
  ext i j
  simp [secMom, Matrix.conjTranspose_apply, mul_comm]

theorem secMom_posSemidef (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m : E d) : (secMom π m).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (secMom_isHermitian π m) ?_
  intro x
  have h := quad_secMom π h2 m (WithLp.toLp 2 x)
  have h' : x ⬝ᵥ (secMom π m *ᵥ x) = ∫ θ, ⟪WithLp.toLp 2 x, θ - m⟫ ^ 2 ∂π := by
    simpa using h
  have h_nonneg : 0 ≤ ∫ θ, ⟪WithLp.toLp 2 x, θ - m⟫ ^ 2 ∂π :=
    integral_nonneg (fun θ => pow_two_nonneg _)
  have hx : star x ⬝ᵥ (secMom π m).mulVec x = x ⬝ᵥ (secMom π m *ᵥ x) := by
    simp
  rw [hx, h']
  exact h_nonneg

theorem covM_posSemidef (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) :
    (covM π).PosSemidef :=
  secMom_posSemidef π h2 (meanV π)

/-- The second moment about `m` is the covariance plus the rank-one term of the offset of the mean. -/
theorem secMom_eq_covM_add (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m : E d) :
    secMom π m = covM π + Matrix.vecMulVec (meanV π - m).ofLp (meanV π - m).ofLp := by
  ext i j
  dsimp [secMom, covM, Matrix.of_apply]
  simp only [Matrix.vecMulVec_apply]
  set μ := meanV π
  -- Basic integrability from h2
  have h_mem_θ : MemLp (fun θ : E d => θ) 2 π := by
    rw [memLp_two_iff_integrable_sq_norm]
    · exact h2
    · exact continuous_id.aestronglyMeasurable
  have h_int_θ : Integrable (fun θ : E d => θ) π := h_mem_θ.integrable (by norm_num)
  have h_int_coord (k : Fin d) : Integrable (fun θ : E d => (θ k : ℝ)) π :=
    h_int_θ.eval_piLp k
  have h_int_sub (k : Fin d) : Integrable (fun θ : E d => (θ k : ℝ) - (μ k : ℝ)) π :=
    Integrable.sub (h_int_coord k) (integrable_const (μ k : ℝ))
  -- Norm squared decomposition
  have h_norm_sq_eq (θ : E d) : ‖θ‖ ^ 2 = ∑ i : Fin d, ((θ i : ℝ)) ^ 2 := by
    simpa using EuclideanSpace.norm_sq_eq θ
  have h_sq_nonneg (θ : E d) (k : Fin d) : 0 ≤ ((θ k : ℝ)) ^ 2 := sq_nonneg _
  have h_sq_le_norm_sq (θ : E d) (k : Fin d) : ((θ k : ℝ)) ^ 2 ≤ ‖θ‖ ^ 2 := by
    rw [h_norm_sq_eq θ]
    exact Finset.single_le_sum (fun i _ => h_sq_nonneg θ i) (Finset.mem_univ k)
  -- Integrability of (θ k)^2
  have h_int_sq_coord (k : Fin d) : Integrable (fun θ : E d => ((θ k : ℝ)) ^ 2) π := by
    have h_ae : (fun θ : E d => ((θ k : ℝ)) ^ 2) ≤ᵐ[π] (fun θ : E d => ‖θ‖ ^ 2) :=
      Filter.Eventually.of_forall (fun θ => h_sq_le_norm_sq θ k)
    have h_nonneg : (fun _ : E d => (0 : ℝ)) ≤ᵐ[π] (fun θ : E d => ((θ k : ℝ)) ^ 2) :=
      Filter.Eventually.of_forall (fun θ => h_sq_nonneg θ k)
    refine integrable_of_le_of_le ?_ h_nonneg h_ae (integrable_const _) h2
    exact ((EuclideanSpace.proj k).continuous.aestronglyMeasurable.pow 2)
  -- MemLp 2 for centered coordinates
  have h_mem_sub (k : Fin d) : MemLp (fun θ : E d => (θ k : ℝ) - (μ k : ℝ)) 2 π := by
    have h_ae : AEStronglyMeasurable (fun θ : E d => (θ k : ℝ) - (μ k : ℝ)) π :=
      (h_int_coord k).aestronglyMeasurable.sub ((integrable_const (μ k : ℝ)).aestronglyMeasurable)
    rw [memLp_two_iff_integrable_sq h_ae]
    have h1 : Integrable (fun θ : E d => ((θ k : ℝ)) ^ 2) π := h_int_sq_coord k
    have h2' : Integrable (fun θ : E d => (θ k : ℝ)) π := h_int_coord k
    have h3 : Integrable (fun _ : E d => (μ k : ℝ) ^ 2) π := integrable_const _
    have h4 : Integrable (fun θ : E d => 2 * (μ k : ℝ) * (θ k : ℝ)) π :=
      (h_int_coord k).const_mul (2 * (μ k : ℝ))
    have h_eq : (fun θ : E d => (((θ k : ℝ) - (μ k : ℝ)) ^ 2)) =
        (fun θ => ((θ k : ℝ)) ^ 2 - 2 * (μ k : ℝ) * (θ k : ℝ) + (μ k : ℝ) ^ 2) := by
      ext θ; ring
    rw [h_eq]
    exact Integrable.add (Integrable.sub h1 h4) h3
  -- Mean identity
  have h_mean (k : Fin d) : ∫ θ : E d, (θ k : ℝ) ∂π = (μ k : ℝ) := by
    calc
      ∫ θ : E d, (θ k : ℝ) ∂π = ∫ θ : E d, (EuclideanSpace.proj k) θ ∂π := by simp
      _ = (EuclideanSpace.proj k) (∫ θ : E d, θ ∂π) := by
        rw [ContinuousLinearMap.integral_comp_id_comm h_int_θ (EuclideanSpace.proj k)]
      _ = (μ k : ℝ) := rfl
  -- Zero-mean residual integrates to zero
  have h_zero_mean (k : Fin d) : ∫ θ : E d, ((θ k : ℝ) - (μ k : ℝ)) ∂π = 0 := by
    rw [integral_sub (h_int_coord k) (integrable_const (μ k : ℝ)), h_mean k, integral_const (μ k : ℝ),
      probReal_univ, smul_eq_mul, one_mul, sub_self]
  -- Product integrability
  have h_int_prod (a b : Fin d) : Integrable (fun θ : E d => ((θ a : ℝ) - (μ a : ℝ)) * ((θ b : ℝ) - (μ b : ℝ))) π :=
    (h_mem_sub a).integrable_mul (h_mem_sub b)
  -- Key identity: the cross terms integrate to zero
  have h_cross : ∫ θ : E d, ((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
      + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)) ∂π = 0 := by
    rw [integral_add ((h_int_sub j).const_mul ((μ i : ℝ) - (m i : ℝ)))
      ((h_int_sub i).mul_const ((μ j : ℝ) - (m j : ℝ)))]
    simp [integral_const_mul, integral_mul_const, h_zero_mean i, h_zero_mean j]
  -- Algebraic expansion of the main identity
  have h_int_cross : Integrable (fun θ : E d => ((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
    + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) π :=
    ((h_int_sub j).const_mul ((μ i : ℝ) - (m i : ℝ))).add
      ((h_int_sub i).mul_const ((μ j : ℝ) - (m j : ℝ)))
  have h_int_const : Integrable (fun _ : E d => ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) π :=
    integrable_const _
  have h_eq_integrand : (fun θ : E d => ((θ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (m j : ℝ))) =
      (fun θ => ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
        + ((((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
        + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))
        + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))) := by
    ext θ; ring_nf
  calc
    ∫ θ : E d, ((θ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (m j : ℝ)) ∂π
        = ∫ θ : E d, (((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
            + ((((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
            + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))
            + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))) ∂π := by
      rw [h_eq_integrand]
    _ = (∫ θ : E d, ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) ∂π)
        + (∫ θ : E d, (((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
            + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))
            + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)) ∂π) := by
      have h_int_cross_plus_d : Integrable (fun θ : E d =>
        (((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)))
        + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) π :=
        h_int_cross.add (integrable_const (((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))))
      simpa using integral_add (h_int_prod i j) h_int_cross_plus_d
    _ = (∫ θ : E d, ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) ∂π)
        + ((∫ θ : E d, (((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
            + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) ∂π)
          + (∫ θ : E d, ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)) ∂π)) := by
      rw [integral_add h_int_cross h_int_const]
    _ = (∫ θ : E d, ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) ∂π)
        + ((∫ θ : E d, ((μ i : ℝ) - (m i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ))
            + ((θ i : ℝ) - (μ i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)) ∂π)
          + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) := by
      rw [integral_const (((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))), probReal_univ, smul_eq_mul, one_mul]
    _ = (∫ θ : E d, ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) ∂π)
        + (0 + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ))) := by rw [h_cross]
    _ = (∫ θ : E d, ((θ i : ℝ) - (μ i : ℝ)) * ((θ j : ℝ) - (μ j : ℝ)) ∂π)
        + ((μ i : ℝ) - (m i : ℝ)) * ((μ j : ℝ) - (m j : ℝ)) := by ring

/-- The covariance is the least second moment: `Σ ≤ ∫ (θ - m)(θ - m)ᵀ dπ` for every point `m`. -/
theorem covM_le_secMom (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m : E d) : covM π ≤ secMom π m := by
  have h_eq : secMom π m = covM π + Matrix.vecMulVec (meanV π - m).ofLp (meanV π - m).ofLp :=
    secMom_eq_covM_add π h2 m
  rw [Matrix.le_iff]
  have h_sub : secMom π m - covM π = Matrix.vecMulVec (meanV π - m).ofLp (meanV π - m).ofLp := by
    rw [h_eq, add_sub_cancel_left]
  rw [h_sub]
  convert Matrix.posSemidef_vecMulVec_self_star ((meanV π - m).ofLp : Fin d → ℝ) using 1

/-- The moments of the cells of a finite measurable partition add up. -/
theorem sum_secMom_restrict {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) {c : E d → α}
    (hc : Measurable c) (m : E d) :
    ∑ a, secMom (π.restrict (c ⁻¹' {a})) m = secMom π m := by
  ext i j
  simp only [secMom, Matrix.sum_apply, Matrix.of_apply]
  have hf : Integrable (fun (θ : E d) => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) π :=
    integrable_secMom_entry π h2 m i j
  have hfm : ∀ a, IntegrableOn (fun (θ : E d) => (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) (c ⁻¹' {a}) π :=
    fun a => hf.integrableOn
  have hs : ∀ a, MeasurableSet (c ⁻¹' {a}) :=
    fun a => hc (measurableSet_singleton a)
  have hdisj : Pairwise (Function.onFun Disjoint (fun (a : α) => c ⁻¹' {a})) := by
    intro a b hne
    exact ((Set.disjoint_singleton.mpr hne).preimage c)
  have h_cover : (⋃ a : α, c ⁻¹' {a}) = Set.univ := by
    ext x; simp
  calc
    ∑ a, ∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂(π.restrict (c ⁻¹' {a}))
        = ∑ a, ∫ θ in c ⁻¹' {a}, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π := by
      simp
    _ = ∫ θ in ⋃ a, c ⁻¹' {a}, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π := by
      rw [← MeasureTheory.integral_iUnion_fintype hs hdisj hfm]
    _ = ∫ θ in Set.univ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π := by rw [h_cover]
    _ = ∫ θ, (θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j) ∂π := by simp

/-- A law on the ball `r B^d` has its `‖θ‖²` integrable. -/
theorem integrable_sq_norm_of_ae_mem (π : Measure (E d)) [IsFiniteMeasure π] {r : ℝ}
    (h : ∀ᵐ θ ∂π, θ ∈ Metric.closedBall (0 : E d) r) : Integrable (fun θ => ‖θ‖ ^ 2) π := by
  have h_bound : ∀ᵐ θ ∂π, ‖‖θ‖ ^ 2‖ ≤ r ^ 2 := by
    filter_upwards [h] with θ hθ
    have hnorm : ‖θ‖ ≤ r := (mem_closedBall_zero_iff.mp hθ)
    have h_sq : ‖θ‖ ^ 2 ≤ r ^ 2 := by
      have h_nonneg : 0 ≤ ‖θ‖ := norm_nonneg _
      nlinarith
    have h_norm_sq : ‖‖θ‖ ^ 2‖ = ‖θ‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h_norm_sq]
    exact h_sq
  have h_meas : AEStronglyMeasurable (fun θ => ‖θ‖ ^ 2) π := by
    refine Continuous.aestronglyMeasurable ?_
    continuity
  exact MeasureTheory.Integrable.of_bound h_meas (r ^ 2) h_bound

/-- The mean of a probability law on the ball `r B^d` lies in the ball. -/
theorem meanV_mem_closedBall (π : Measure (E d)) [IsProbabilityMeasure π] {r : ℝ}
    (h : ∀ᵐ θ ∂π, θ ∈ Metric.closedBall (0 : E d) r) : meanV π ∈ Metric.closedBall (0 : E d) r := by
  have h_norm : ∀ᵐ θ ∂π, ‖θ‖ ≤ r := by
    filter_upwards [h] with θ hθ
    rw [mem_closedBall_zero_iff] at hθ
    exact hθ
  rw [mem_closedBall_zero_iff]
  calc
    ‖meanV π‖ = ‖∫ θ, θ ∂π‖ := rfl
    _ ≤ r * π.real Set.univ := MeasureTheory.norm_integral_le_of_norm_le_const h_norm
    _ = r * 1 := by rw [MeasureTheory.probReal_univ]
    _ = r := by ring

/-- The trace of the covariance is at most the second moment about `0`: `tr Σ ≤ ∫ ‖θ‖² dπ`. -/
theorem trace_covM_le (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) :
    Matrix.trace (covM π) ≤ ∫ θ, ‖θ‖ ^ 2 ∂π := by
  have h1 : Matrix.trace (covM π) ≤ Matrix.trace (secMom π 0) := by
    have h := covM_le_secMom π h2 0
    rw [Matrix.le_iff] at h
    have := h.trace_nonneg
    rw [Matrix.trace_sub] at this
    linarith
  have h3 : Matrix.trace (secMom π 0) = ∫ θ, ‖θ‖ ^ 2 ∂π := by
    have := trace_mul_secMom π h2 0 1
    rw [Matrix.one_mul] at this
    rw [this]
    congr 1
    funext θ
    rw [EuclideanSpace.norm_sq_eq]
    simp [Matrix.one_mulVec, dotProduct, sq]
  linarith

end AdversarialBco.Lower
