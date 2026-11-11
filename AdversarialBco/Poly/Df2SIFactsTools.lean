/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetTools
public import AdversarialBco.Poly.Df2PlayProof
public import AdversarialBco.Poly.SrcToolsProof
public import AdversarialBco.Lemmas
public import AdversarialBco.Body.Gauss

@[expose] public section

/-!
# Generic tools of `Df2SIFacts`

Statements on their own data (no parameter of the learner), read by `Df2SIFactsProof.lean`.
`γ = stdGaussian (EuclideanSpace ℝ (Fin d))`.

* Gaussian facts: `E |⟪u, g⟫| ≤ ‖u‖`, `E ⟪u, g⟫ ⟪v, g⟫ = ⟪u, v⟫`, the quadratic form of `A g`, the tail of a linear
  form, the truncated second moment of `‖g‖`.
* The split: `a g₁ + b g₂` (independent standard, `a² + b² = 1`) has the law of `g`.
* The Cameron-Martin identity `E H(c + g) = E[H(g) exp(⟪c, g⟫ - ‖c‖²/2)]` (from the density `Df2Play.gdens`) and the
  comparison `E H(c + g) ≤ 2 E H(g) + β P(⟪c, g⟫ > log 2 - ‖c‖²/2)` for `0 ≤ H ≤ β`.
* The Stein form of a Gaussian Hessian: `|E[e(w + T g)(⟪g, S a⟫ ⟪g, S b⟫ - ⟪S a, S b⟫)]| ≤ K ‖b‖ ‖S a‖` for `e`
  convex and `K`-Lipschitz, `T S = 1` (Gaussian integration by parts twice, `ibpLip`).
* Taylor from below with a lower bound on the second derivative along the segment.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal ENNReal Matrix

namespace AdversarialBco.Poly.SIF

variable {d : ℕ}

/-! ## Gaussian moments -/

/-- `E |⟪u, g⟫| ≤ ‖u‖`. -/
theorem integral_abs_inner_le (u : EuclideanSpace ℝ (Fin d)) :
    ∫ g, |⟪u, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ‖u‖ := by
  let E := EuclideanSpace ℝ (Fin d)
  let μ := stdGaussian E
  have h_int : (μ[(fun g => ⟪u, g⟫)]) = 0 := by
    simpa using integral_strongDual_stdGaussian (innerSL ℝ u)
  have h_var : Var[fun g => ⟪u, g⟫; μ] = ‖u‖ ^ 2 := by
    calc
      Var[fun g => ⟪u, g⟫; μ] = Var[innerSL ℝ u; μ] := rfl
      _ = ‖innerSL ℝ u‖ ^ 2 := variance_dual_stdGaussian (innerSL ℝ u)
      _ = ‖u‖ ^ 2 := by
        simp
  have h_memLp : MemLp (fun g => ⟪u, g⟫) 2 μ := by
    have h_id : MemLp (id : E → E) 2 μ := IsGaussian.memLp_two_id (μ := μ)
    simpa using (innerSL ℝ u).comp_memLp' h_id
  have h_sq_int : μ[(fun g => ⟪u, g⟫) ^ 2] = ‖u‖ ^ 2 := by
    have h_var_eq := variance_eq_sub h_memLp
    rw [h_var, h_int] at h_var_eq
    -- h_var_eq : ‖u‖² = μ[X²] - 0
    simpa using h_var_eq.symm
  have h_nonneg : 0 ≤ ∫ g, |⟪u, g⟫| ∂μ := integral_nonneg (fun g => abs_nonneg _)
  have h_memLp_f : MemLp (fun g => ⟪u, g⟫) (ENNReal.ofReal 2) μ := by
    simpa using h_memLp
  have h_memLp_one : MemLp (fun _ => (1 : ℝ)) (ENNReal.ofReal 2) μ :=
    memLp_const (1 : ℝ)
  have h_cauchy_raw : (∫ g, ‖(fun g => ⟪u, g⟫) g‖ * ‖(fun _ => (1 : ℝ)) g‖ ∂μ) ≤
      (∫ g, ‖(fun g => ⟪u, g⟫) g‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫ g, ‖(fun _ => (1 : ℝ)) g‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) (Real.HolderConjugate.two_two) h_memLp_f h_memLp_one
  have h_int_one_pow_two : (∫ g, ‖(fun _ : E => (1 : ℝ)) g‖ ^ (2 : ℝ) ∂μ) = 1 := by
    simp
  have h_int_abs_sq : (∫ g, ‖(fun g => ⟪u, g⟫) g‖ ^ (2 : ℝ) ∂μ) = ∫ g, (⟪u, g⟫) ^ 2 ∂μ := by
    simp [sq_abs]
  rw [h_int_one_pow_two, h_int_abs_sq] at h_cauchy_raw
  have h_left_simp : (∫ g, ‖(fun g => ⟪u, g⟫) g‖ * ‖(fun _ : E => (1 : ℝ)) g‖ ∂μ) =
      (∫ g, |⟪u, g⟫| ∂μ) := by
    simp
  rw [h_left_simp] at h_cauchy_raw
  have h_right_simp : (∫ g, (⟪u, g⟫) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (1 : ℝ) ^ (1 / (2 : ℝ)) =
      (∫ g, (⟪u, g⟫) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by simp
  rw [h_right_simp] at h_cauchy_raw
  have h_sq_eq : (∫ g, |⟪u, g⟫| ∂μ) ^ 2 ≤ (∫ g, (⟪u, g⟫) ^ 2 ∂μ) := by
    have h_nonneg_int : 0 ≤ ∫ g, |⟪u, g⟫| ∂μ := h_nonneg
    have h_nonneg_sq : 0 ≤ ∫ g, (⟪u, g⟫) ^ 2 ∂μ := by
      apply integral_nonneg; intro g; apply pow_two_nonneg
    have h_nonneg_sqrt : 0 ≤ (∫ g, (⟪u, g⟫) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) :=
      Real.rpow_nonneg h_nonneg_sq _
    have h_sq_sqrt : ((∫ g, (⟪u, g⟫) ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 = ∫ g, (⟪u, g⟫) ^ 2 ∂μ := by
      simpa [show ((1 : ℝ)/2) * (2 : ℝ) = (1 : ℝ) by norm_num, Real.rpow_one] using
        (Real.rpow_mul h_nonneg_sq (1/(2:ℝ)) 2).symm
    -- From h_cauchy_raw: ∫ |X| ≤ (∫ X²)^(1/2)
    -- Square both sides (both nonnegative)
    nlinarith
  -- h_sq_int : ∫ ((fun g => ⟪u, g⟫) ^ 2) = ‖u‖ ^ 2
  -- Need to relate this to ∫ (⟪u, g⟫) ^ 2
  have h_sq_int' : (∫ g, (⟪u, g⟫) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    simpa using h_sq_int
  rw [h_sq_int'] at h_sq_eq
  -- h_sq_eq : (∫ |X|)² ≤ ‖u‖²
  -- We need ∫ |X| ≤ ‖u‖
  -- Since both sides are nonnegative, we can take square roots
  have h_nonneg_norm : 0 ≤ ‖u‖ := norm_nonneg _
  have h_nonneg_int : 0 ≤ ∫ g, |⟪u, g⟫| ∂μ := integral_nonneg (fun g => abs_nonneg _)
  -- From a² ≤ b² and a, b ≥ 0, we get a ≤ b
  -- Proof: b² - a² = (b - a)(b + a) ≥ 0, and b + a ≥ 0, so b - a ≥ 0
  have h_nonneg_sum : 0 ≤ (∫ g, |⟪u, g⟫| ∂μ) + ‖u‖ := add_nonneg h_nonneg_int h_nonneg_norm
  have h_diff_sq : ‖u‖ ^ 2 - (∫ g, |⟪u, g⟫| ∂μ) ^ 2 = (‖u‖ - ∫ g, |⟪u, g⟫| ∂μ) * (‖u‖ + ∫ g, |⟪u, g⟫| ∂μ) := by ring
  have h_nonneg_prod : 0 ≤ (‖u‖ - ∫ g, |⟪u, g⟫| ∂μ) * (‖u‖ + ∫ g, |⟪u, g⟫| ∂μ) := by
    rw [← h_diff_sq]
    linarith
  rcases lt_or_eq_of_le h_nonneg_sum with (hsum | hsum)
  · -- sum > 0
    have h_nonneg_diff : 0 ≤ ‖u‖ - ∫ g, |⟪u, g⟫| ∂μ := by
      nlinarith
    linarith
  · -- sum = 0, so both are zero
    have h_int_zero : ∫ g, |⟪u, g⟫| ∂μ = 0 := by linarith
    have h_norm_zero : ‖u‖ = 0 := by linarith
    rw [h_int_zero, h_norm_zero]

/-- `E ⟪u, g⟫ ⟪v, g⟫ = ⟪u, v⟫`. -/
theorem integral_inner_mul_inner (u v : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪u, g⟫ * ⟪v, g⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ⟪u, v⟫ := by
  have h_mem : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
  have h_apply := covarianceBilin_apply h_mem u v
  calc
    ∫ g, ⟪u, g⟫ * ⟪v, g⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ g, ⟪u, g - (∫ x, id x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))⟫
            * ⟪v, g - (∫ x, id x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))⟫
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      simp [integral_id_stdGaussian]
    _ = covarianceBilin (stdGaussian (EuclideanSpace ℝ (Fin d))) u v := by
      rw [← h_apply]
    _ = ⟪u, v⟫ := by
      rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ]

/-- The quadratic form of `A g`: `E (A g)ᵀ H (A g) = tr(H A Aᵀ)`. -/
theorem integral_sq_mulVec (H A : Matrix (Fin d) (Fin d) ℝ) :
    ∫ g, df2Sq H (A *ᵥ WithLp.ofLp g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (H * (A * Aᵀ)).trace := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  -- For each row i, define a_i = WithLp.toLp 2 (A i ·)
  -- Key identity: (A *ᵥ WithLp.ofLp g) i = ⟪a_i, g⟫
  have h_mulVec_eq_inner (g : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
      (A *ᵥ WithLp.ofLp g) i = ⟪WithLp.toLp 2 (A i ·), g⟫ := by
    rw [Matrix.mulVec_apply, EuclideanSpace.inner_toLp_toLp]
    simp [Matrix.row, dotProduct, mul_comm]
  -- Expand df2Sq as a double sum
  have h_expand (g : EuclideanSpace ℝ (Fin d)) :
      df2Sq H (A *ᵥ WithLp.ofLp g) =
      ∑ i : Fin d, ∑ j : Fin d, (A *ᵥ WithLp.ofLp g) i * H i j * (A *ᵥ WithLp.ofLp g) j := by
    dsimp [df2Sq]
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  have h_expand_ae : ∀ᵐ g ∂μ,
      df2Sq H (A *ᵥ WithLp.ofLp g) =
      ∑ i : Fin d, ∑ j : Fin d, (A *ᵥ WithLp.ofLp g) i * H i j * (A *ᵥ WithLp.ofLp g) j := by
    filter_upwards with g using h_expand g
  rw [integral_congr_ae h_expand_ae]
  -- Now we have ∫ g, ∑ i, ∑ j, ...
  -- Prove integrability of each inner term
  have h_int_inner (u : EuclideanSpace ℝ (Fin d)) : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) μ :=
    IsGaussian.integrable_dual μ (innerSL ℝ u)
  have h_int_term (i j : Fin d) : Integrable (fun g : EuclideanSpace ℝ (Fin d) =>
      (A *ᵥ WithLp.ofLp g) i * H i j * (A *ᵥ WithLp.ofLp g) j) μ := by
    have h_eq : (fun g : EuclideanSpace ℝ (Fin d) =>
        (A *ᵥ WithLp.ofLp g) i * H i j * (A *ᵥ WithLp.ofLp g) j) =
        (fun g => H i j * (⟪WithLp.toLp 2 (A i ·), g⟫ * ⟪WithLp.toLp 2 (A j ·), g⟫)) := by
      ext g
      simp [h_mulVec_eq_inner g i, h_mulVec_eq_inner g j, mul_comm, mul_assoc]
    rw [h_eq]
    have h_mem_i : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪WithLp.toLp 2 (A i ·), g⟫) 2 μ :=
      IsGaussian.memLp_dual μ (innerSL ℝ (WithLp.toLp 2 (A i ·))) 2 (by norm_num)
    have h_mem_j : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪WithLp.toLp 2 (A j ·), g⟫) 2 μ :=
      IsGaussian.memLp_dual μ (innerSL ℝ (WithLp.toLp 2 (A j ·))) 2 (by norm_num)
    have h_int_prod : Integrable (fun g => ⟪WithLp.toLp 2 (A i ·), g⟫ * ⟪WithLp.toLp 2 (A j ·), g⟫) μ :=
      h_mem_i.integrable_mul h_mem_j
    exact h_int_prod.const_mul (H i j)
  -- Now apply integral_finsetSum twice to swap integral and sums
  -- First, for each i, the inner sum is integrable
  have h_int_inner_sum (i : Fin d) : Integrable (fun g : EuclideanSpace ℝ (Fin d) =>
      ∑ j : Fin d, (A *ᵥ WithLp.ofLp g) i * H i j * (A *ᵥ WithLp.ofLp g) j) μ := by
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro j hj
    exact h_int_term i j
  -- Now apply integral_finsetSum for the outer sum
  have h_swap_outer : ∫ a, ∑ i : Fin d, ∑ j : Fin d, (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j ∂μ =
      ∑ i : Fin d, ∫ a, ∑ j : Fin d, (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j ∂μ :=
    integral_finsetSum (Finset.univ : Finset (Fin d)) (fun i hi => h_int_inner_sum i)
  rw [h_swap_outer]
  -- Now we have ∑ i, ∫ a, ∑ j, ...
  -- Apply integral_finsetSum for each inner sum
  have h_inner (i : Fin d) : ∫ a, ∑ j : Fin d, (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j ∂μ =
      ∑ j : Fin d, ∫ a, (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j ∂μ :=
    integral_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj => h_int_term i j)
  simp_rw [h_inner]
  -- Now we have ∑ i, ∑ j, ∫ a, (A *ᵥ ...) i * H i j * (A *ᵥ ...) j
  -- Simplify each inner integral using integral_inner_mul_inner
  have h_inner_integral (i j : Fin d) : ∫ a : EuclideanSpace ℝ (Fin d),
      (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j ∂μ =
      H i j * (A * Aᵀ) i j := by
    have h_eq : (fun (a : EuclideanSpace ℝ (Fin d)) =>
        (A *ᵥ WithLp.ofLp a) i * H i j * (A *ᵥ WithLp.ofLp a) j) =
        (fun a => H i j * (⟪WithLp.toLp 2 (A i ·), a⟫ * ⟪WithLp.toLp 2 (A j ·), a⟫)) := by
      ext a
      simp [h_mulVec_eq_inner a i, h_mulVec_eq_inner a j, mul_comm, mul_assoc]
    rw [h_eq]
    rw [integral_const_mul (H i j)]
    rw [integral_inner_mul_inner]
    have h_inner_eq : ⟪WithLp.toLp 2 (A i ·), WithLp.toLp 2 (A j ·)⟫ = (A * Aᵀ) i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, PiLp.inner_apply, mul_comm]
    rw [h_inner_eq]
  -- Now replace each inner integral with H i j * (A * Aᵀ) i j
  simp_rw [h_inner_integral]
  -- Now we have ∑ i, ∑ j, H i j * (A * Aᵀ) i j = (H * (A * Aᵀ)).trace
  -- Use the symmetry of A * Aᵀ
  have h_symm : (A * Aᵀ).IsSymm := Matrix.isSymm_mul_transpose_self A
  have h_symm_eq (i j : Fin d) : (A * Aᵀ) j i = (A * Aᵀ) i j := by
    calc
      (A * Aᵀ) j i = ((A * Aᵀ)ᵀ) i j := by rw [Matrix.transpose_apply]
      _ = (A * Aᵀ) i j := by rw [h_symm.eq]
  -- Rewrite the RHS trace
  rw [Matrix.trace]
  -- Goal: ∑ i, ∑ j, H i j * (A * Aᵀ) i j = ∑ i, (H * (A * Aᵀ)) i i
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
  -- Goal: ∑ i, ∑ j, H i j * (∑ k, A i k * A j k) = ∑ i, ∑ j, H i j * (∑ k, A j k * A i k)
  -- The RHS has A j k * A i k instead of A i k * A j k, use mul_comm
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have h_sum_eq : (∑ k : Fin d, A i k * A j k) = (∑ k : Fin d, A j k * A i k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_comm]
  rw [h_sum_eq]
  rfl

/-- The tail of a linear form: `P(b < ⟪c, g⟫) ≤ exp(-b²/(2 ‖c‖²))/2` for `b ≥ 0`. -/
theorem inner_tail (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (hb : 0 ≤ b) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | b < ⟪c, g⟫} ≤ Real.exp (-(b ^ 2 / (2 * ‖c‖ ^ 2))) / 2 := by
  by_cases hc : c = 0
  · subst hc
    have h_empty : {g : EuclideanSpace ℝ (Fin d) | b < (0 : ℝ)} = ∅ := by
      ext g; simp [hb]
    simp [measureReal_def, h_empty]
  · have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hc_norm_ne_zero : ‖c‖ ≠ 0 := by linarith
    set u := (‖c‖⁻¹ : ℝ) • c with hu_def
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm]
      field_simp [hc_norm_ne_zero]
    have h_inner_eq : ∀ g, ⟪c, g⟫ = ‖c‖ * ⟪u, g⟫ := by
      intro g
      rw [hu_def, real_inner_smul_left]
      field_simp [hc_norm_ne_zero]
    have h_set_eq : {g | b < ⟪c, g⟫} = {g | b / ‖c‖ < ⟪u, g⟫} := by
      ext g
      simp [h_inner_eq g]
      constructor
      · intro h
        exact (div_lt_iff₀ hc_norm_pos).mpr (by simpa [mul_comm] using h)
      · intro h
        simpa [mul_comm] using (div_lt_iff₀ hc_norm_pos).mp h
    have h_meas_inner : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫) :=
      (continuous_const.inner continuous_id).measurable
    have h_meas_Ioi : MeasurableSet (Set.Ioi (b / ‖c‖)) :=
      measurableSet_Ioi
    rw [measureReal_def, h_set_eq]
    have h_preimage_eq : (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫) ⁻¹' Set.Ioi (b / ‖c‖) =
        {g | b / ‖c‖ < ⟪u, g⟫} := by
      ext g; simp
    have h_map_eq : (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫) = gaussianReal 0 1 :=
      AdversarialBco.Body.map_inner_stdGaussian u hu_norm
    have h_measure_map : ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) (Set.Ioi (b / ‖c‖)) =
        (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | b / ‖c‖ < ⟪u, g⟫} := by
      rw [Measure.map_apply h_meas_inner h_meas_Ioi, h_preimage_eq]
    have h_nonneg_div : 0 ≤ b / ‖c‖ := div_nonneg hb hc_norm_pos.le
    have h_gauss_tail := (gaussTailT1 (b / ‖c‖) h_nonneg_div).1
    have h_Ioi_subset_Ici : Set.Ioi (b / ‖c‖) ⊆ Set.Ici (b / ‖c‖) :=
      Set.Ioi_subset_Ici_self
    have h_measure_mono : gaussianReal 0 1 (Set.Ioi (b / ‖c‖)) ≤ gaussianReal 0 1 (Set.Ici (b / ‖c‖)) :=
      measure_mono h_Ioi_subset_Ici
    have h_measure_le : gaussianReal 0 1 (Set.Ioi (b / ‖c‖)) ≤ ENNReal.ofReal (Real.exp (-(b / ‖c‖) ^ 2 / 2) / 2) :=
      le_trans h_measure_mono h_gauss_tail
    have h_toReal_le : ENNReal.toReal (gaussianReal 0 1 (Set.Ioi (b / ‖c‖))) ≤
        Real.exp (-(b / ‖c‖) ^ 2 / 2) / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by
        have hpos : 0 ≤ Real.exp (-(b / ‖c‖) ^ 2 / 2) := Real.exp_pos _ |>.le
        nlinarith) h_measure_le
    have h_exp_eq : Real.exp (-(b / ‖c‖) ^ 2 / 2) = Real.exp (-(b ^ 2 / (2 * ‖c‖ ^ 2))) := by
      congr 1
      ring
    calc
      ENNReal.toReal ((stdGaussian (EuclideanSpace ℝ (Fin d))) {g | b / ‖c‖ < ⟪u, g⟫}) =
          ENNReal.toReal (((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) (Set.Ioi (b / ‖c‖))) := by
        rw [h_measure_map]
      _ = ENNReal.toReal (gaussianReal 0 1 (Set.Ioi (b / ‖c‖))) := by rw [h_map_eq]
      _ ≤ Real.exp (-(b / ‖c‖) ^ 2 / 2) / 2 := h_toReal_le
      _ = Real.exp (-(b ^ 2 / (2 * ‖c‖ ^ 2))) / 2 := by rw [h_exp_eq]

/-- The truncated second moment: `E[‖g‖² 1{T < ‖g‖²}] ≤ 8 · 2^{d/2} e^{-T/8}`. -/
theorem norm_sq_tail_integral (T : ℝ) :
    ∫ g, Set.indicator {g : EuclideanSpace ℝ (Fin d) | T < ‖g‖ ^ 2} (fun g => ‖g‖ ^ 2) g
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 8 * Real.sqrt 2 ^ d * Real.exp (-(T / 8)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let A : Set (EuclideanSpace ℝ (Fin d)) := {g | T < ‖g‖ ^ 2}
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun g => ‖g‖ ^ 2
  let bound : EuclideanSpace ℝ (Fin d) → ℝ := fun g => 8 * Real.exp (-(T / 8)) * Real.exp (‖g‖ ^ 2 / 4)
  have h_bound_nonneg : ∀ g, 0 ≤ bound g := by
    intro g
    dsimp [bound]
    positivity
  have h_pointwise : ∀ g, Set.indicator A f g ≤ bound g := by
    intro g
    by_cases hgA : g ∈ A
    · rw [Set.indicator_of_mem hgA]
      dsimp [f, bound, A] at hgA ⊢
      have h_exp1 : ‖g‖ ^ 2 ≤ 8 * Real.exp (‖g‖ ^ 2 / 8) := by
        have h := Real.add_one_le_exp (‖g‖ ^ 2 / 8)
        linarith
      have h_exp2 : (1 : ℝ) ≤ Real.exp ((‖g‖ ^ 2 - T) / 8) := by
        have h_nonneg_diff : 0 ≤ ‖g‖ ^ 2 - T := by linarith
        have h := Real.add_one_le_exp ((‖g‖ ^ 2 - T) / 8)
        have hdiv : 0 ≤ (‖g‖ ^ 2 - T) / 8 := div_nonneg h_nonneg_diff (by norm_num)
        linarith
      calc
        ‖g‖ ^ 2 = (‖g‖ ^ 2) * (1 : ℝ) := by ring
        _ ≤ (8 * Real.exp (‖g‖ ^ 2 / 8)) * Real.exp ((‖g‖ ^ 2 - T) / 8) := by
          nlinarith
        _ = 8 * (Real.exp (‖g‖ ^ 2 / 8) * Real.exp ((‖g‖ ^ 2 - T) / 8)) := by ring
        _ = 8 * Real.exp (‖g‖ ^ 2 / 8 + (‖g‖ ^ 2 - T) / 8) := by rw [Real.exp_add]
        _ = 8 * Real.exp (‖g‖ ^ 2 / 4 - T / 8) := by ring_nf
        _ = 8 * (Real.exp (‖g‖ ^ 2 / 4) * Real.exp (-(T / 8))) := by
          rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg (T / 8)]
        _ = 8 * Real.exp (-(T / 8)) * Real.exp (‖g‖ ^ 2 / 4) := by ring
    · rw [Set.indicator_of_notMem hgA]
      dsimp [bound]
      exact h_bound_nonneg g
  have h_nonneg_indicator : 0 ≤ᵐ[γ] fun g => Set.indicator A f g := by
    refine ae_of_all _ (fun g => ?_)
    refine Set.indicator_apply_nonneg (fun h => ?_)
    dsimp [f]
    positivity
  have h_sqrt2_eq : (1 / Real.sqrt (1 - 2 * ((1 : ℝ)/4))) = Real.sqrt 2 := by
    have h_inner : 1 - 2 * ((1 : ℝ)/4) = (1/2 : ℝ) := by ring
    rw [h_inner]
    -- Goal: 1 / Real.sqrt (1/2) = Real.sqrt 2
    apply (div_eq_iff (by positivity : Real.sqrt (1/2) ≠ 0)).mpr
    -- Goal: 1 = Real.sqrt 2 * Real.sqrt (1/2)
    calc
      1 = Real.sqrt 1 := by rw [Real.sqrt_one]
      _ = Real.sqrt ((1/2 : ℝ) * 2) := by ring
      _ = Real.sqrt (1/2) * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (1/2 : ℝ))]
      _ = Real.sqrt 2 * Real.sqrt (1/2) := by ring
  have h_int_exp : Integrable (fun g => Real.exp (‖g‖ ^ 2 / 4)) γ := by
    by_contra h_not
    have h_zero : ∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂γ = 0 := MeasureTheory.integral_undef h_not
    have h_pos : 0 < ∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂γ := by
      dsimp [γ]
      have h_chi := chi2_mgf d (1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      have h_eq : (∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
          (Real.sqrt 2) ^ d := by
        have h_chi := chi2_mgf d (1/4) (by norm_num : (1/4 : ℝ) < 1/2)
        calc
          (∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
              (∫ g, Real.exp (((1 : ℝ)/4) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
            refine integral_congr_ae ?_
            filter_upwards with g
            congr 1
            ring
          _ = (1 / Real.sqrt (1 - 2 * ((1 : ℝ)/4))) ^ d := h_chi
          _ = (Real.sqrt 2) ^ d := by rw [h_sqrt2_eq]
      rw [h_eq]
      have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
      exact pow_pos h_sqrt2_pos d
    linarith
  have h_int_bound : Integrable bound γ := by
    dsimp [bound]
    exact h_int_exp.const_mul (8 * Real.exp (-(T / 8)))
  calc
    ∫ g, Set.indicator A f g ∂γ ≤ ∫ g, bound g ∂γ :=
      MeasureTheory.integral_mono_of_nonneg h_nonneg_indicator h_int_bound (ae_of_all _ h_pointwise)
    _ = ∫ g, (8 * Real.exp (-(T / 8))) * Real.exp (‖g‖ ^ 2 / 4) ∂γ := rfl
    _ = (8 * Real.exp (-(T / 8))) * ∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂γ := by
      rw [integral_const_mul_of_integrable h_int_exp]
    _ = (8 * Real.exp (-(T / 8))) * ((Real.sqrt 2) ^ d) := by
      dsimp [γ]
      have h_chi := chi2_mgf d (1/4) (by norm_num : (1/4 : ℝ) < 1/2)
      have h_integral_eq : (∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
          (Real.sqrt 2) ^ d := by
        calc
          (∫ g, Real.exp (‖g‖ ^ 2 / 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
              (∫ g, Real.exp (((1 : ℝ)/4) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
            refine integral_congr_ae ?_
            filter_upwards with g
            congr 1
            ring
          _ = (1 / Real.sqrt (1 - 2 * ((1 : ℝ)/4))) ^ d := h_chi
          _ = (Real.sqrt 2) ^ d := by rw [h_sqrt2_eq]
      rw [h_integral_eq]
    _ = 8 * Real.sqrt 2 ^ d * Real.exp (-(T / 8)) := by ring

/-! ## The split -/

/-- `a g₁ + b g₂` has the law of `g` when `a² + b² = 1`, as an iterated integral, for `F` continuous of linear
growth. -/
theorem integral_integral_split (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : Continuous F) (B0 B1 : ℝ)
    (hgrowth : ∀ x, |F x| ≤ B0 + B1 * ‖x‖) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ g₁, ∫ g₂, F (a • g₁ + b • g₂) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hb1 : b ≤ 1 := by
    nlinarith
  have ha_sq_eq : a ^ 2 = 1 - b ^ 2 := by
    nlinarith
  have ha_eq_sqrt : a = Real.sqrt (1 - b ^ 2) := by
    calc
      a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ = Real.sqrt (1 - b ^ 2) := by rw [ha_sq_eq]
  set θ := Real.arccos b with hθ_def
  have hcos : Real.cos θ = b := Real.cos_arccos (by linarith) hb1
  have hsin : Real.sin θ = a := by
    rw [Real.sin_arccos, ha_eq_sqrt]
  -- the second component of the rotation equals a • p.1 + b • p.2
  have hR2 : ∀ (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      (Real.cos θ • p.1 - Real.sin θ • p.2, Real.sin θ • p.1 + Real.cos θ • p.2).2 =
      a • p.1 + b • p.2 := by
    intro p
    simp [hcos, hsin]
  -- integrability of the identity function under Gaussian measure
  have h_int_id : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) γ := by
    have h_memLp : MemLp id 1 γ := IsGaussian.memLp_id γ 1 (by norm_num)
    exact memLp_one_iff_integrable.1 h_memLp
  have h_int_norm : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) γ :=
    h_int_id.norm
  have h_int_norm_fst : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => ‖p.1‖)
      (γ.prod γ) :=
    h_int_norm.comp_fst γ
  have h_int_norm_snd : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => ‖p.2‖)
      (γ.prod γ) :=
    h_int_norm.comp_snd γ
  -- pointwise bound for F (using |B1| since B1 may be negative)
  have h_bound : ∀ (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      ‖F (a • p.1 + b • p.2)‖ ≤ B0 + |B1| * (a * ‖p.1‖ + b * ‖p.2‖) := by
    intro p
    have hg := hgrowth (a • p.1 + b • p.2)
    have hnorm : ‖a • p.1 + b • p.2‖ ≤ a * ‖p.1‖ + b * ‖p.2‖ := by
      calc
        ‖a • p.1 + b • p.2‖ ≤ ‖a • p.1‖ + ‖b • p.2‖ := norm_add_le _ _
        _ = |a| * ‖p.1‖ + |b| * ‖p.2‖ := by simp [norm_smul]
        _ = a * ‖p.1‖ + b * ‖p.2‖ := by simp [abs_of_nonneg ha, abs_of_nonneg hb]
    have h_abs_eq_norm : ‖F (a • p.1 + b • p.2)‖ = |F (a • p.1 + b • p.2)| := Real.norm_eq_abs _
    rw [h_abs_eq_norm]
    have h_norm_nonneg : 0 ≤ ‖a • p.1 + b • p.2‖ := norm_nonneg _
    have h_abs_self : B1 ≤ |B1| := le_abs_self B1
    have h_abs_nonneg : 0 ≤ |B1| := abs_nonneg _
    have h1 : B1 * ‖a • p.1 + b • p.2‖ ≤ |B1| * ‖a • p.1 + b • p.2‖ :=
      mul_le_mul_of_nonneg_right h_abs_self h_norm_nonneg
    have h2 : |B1| * ‖a • p.1 + b • p.2‖ ≤ |B1| * (a * ‖p.1‖ + b * ‖p.2‖) :=
      mul_le_mul_of_nonneg_left hnorm h_abs_nonneg
    nlinarith
  -- the bounding function is integrable
  have h_bound_int : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      B0 + |B1| * (a * ‖p.1‖ + b * ‖p.2‖)) (γ.prod γ) := by
    have h1 : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => a * ‖p.1‖) (γ.prod γ) :=
      h_int_norm_fst.smul a
    have h2 : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => b * ‖p.2‖) (γ.prod γ) :=
      h_int_norm_snd.smul b
    have h_sum : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        a * ‖p.1‖ + b * ‖p.2‖) (γ.prod γ) := h1.add h2
    have h_mul : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        |B1| * (a * ‖p.1‖ + b * ‖p.2‖)) (γ.prod γ) :=
      h_sum.smul (|B1|)
    exact (integrable_const B0).add h_mul
  -- the integrand is AEStronglyMeasurable
  have h_ae_meas : AEStronglyMeasurable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      F (a • p.1 + b • p.2)) (γ.prod γ) := by
    have h_cont : Continuous (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        a • p.1 + b • p.2) := by
      fun_prop
    exact (hF.comp h_cont).measurable.aestronglyMeasurable
  -- the integrand is integrable
  have h_int : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      F (a • p.1 + b • p.2)) (γ.prod γ) :=
    h_bound_int.mono' h_ae_meas (ae_of_all _ h_bound)
  -- Step 1: convert iterated integral to product integral using Fubini
  rw [integral_integral h_int]
  -- Step 2: rewrite using the rotation map
  set R : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
    fun p => (Real.cos θ • p.1 - Real.sin θ • p.2, Real.sin θ • p.1 + Real.cos θ • p.2) with hR_def
  have h_rot_eq : (γ.prod γ).map R = γ.prod γ :=
    AdversarialBco.stdGaussian_prod_rotation d θ
  have h_meas_R : Measurable R := by
    unfold R
    fun_prop
  have h_ae_meas_f : AEStronglyMeasurable (fun (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      F (w.2)) ((γ.prod γ).map R) :=
    (hF.comp continuous_snd).measurable.aestronglyMeasurable
  calc
    ∫ z, F (a • z.1 + b • z.2) ∂(γ.prod γ) = ∫ z, F ((R z).2) ∂(γ.prod γ) := by
      refine integral_congr_ae ?_
      filter_upwards with p
      rw [hR2 p]
    _ = ∫ w, F (w.2) ∂((γ.prod γ).map R) := by
      rw [← integral_map h_meas_R.aemeasurable h_ae_meas_f]
    _ = ∫ w, F (w.2) ∂(γ.prod γ) := by rw [h_rot_eq]
    _ = ∫ g, F g ∂γ := by
      rw [integral_fun_snd F]
      have h_meas : γ.real Set.univ = 1 := by
        rw [measureReal_def, IsProbabilityMeasure.measure_univ]
        simp
      simp [h_meas]

/-! ## The shift -/

/-- The Cameron-Martin identity for the standard Gaussian. -/
theorem integral_shift_cm (H : EuclideanSpace ℝ (Fin d) → ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    ∫ g, H (c + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, H g * Real.exp (⟪c, g⟫ - ‖c‖ ^ 2 / 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  calc
    ∫ g, H (c + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ y, H y * Df2Play.gdens d (y - c) := by
      rw [Df2Play.integral_stdGaussian_shift d H c]
    _ = ∫ y, H y * (Real.exp (⟪c, y⟫ - ‖c‖ ^ 2 / 2) * Df2Play.gdens d y) := by
      refine integral_congr_ae ?_
      filter_upwards with y
      dsimp [Df2Play.gdens]
      have h := norm_sub_sq_real y c
      have hexp : -(‖y - c‖ ^ 2) / 2 = (-(‖y‖ ^ 2) / 2) + (⟪c, y⟫ - ‖c‖ ^ 2 / 2) := by
        rw [h]
        calc
          -(‖y‖ ^ 2 - 2 * inner ℝ y c + ‖c‖ ^ 2) / 2 = (-(‖y‖ ^ 2) + 2 * inner ℝ y c - ‖c‖ ^ 2) / 2 := by ring
          _ = (-(‖y‖ ^ 2) / 2) + (inner ℝ y c - ‖c‖ ^ 2 / 2) := by ring
          _ = (-(‖y‖ ^ 2) / 2) + (⟪c, y⟫ - ‖c‖ ^ 2 / 2) := by rw [real_inner_comm y c]
      calc
        H y * ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-(‖y - c‖ ^ 2) / 2))
            = H y * ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp ((-(‖y‖ ^ 2) / 2) + (⟪c, y⟫ - ‖c‖ ^ 2 / 2))) := by rw [hexp]
        _ = H y * ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * (Real.exp (-(‖y‖ ^ 2) / 2) * Real.exp (⟪c, y⟫ - ‖c‖ ^ 2 / 2))) := by rw [Real.exp_add]
        _ = H y * (Real.exp (⟪c, y⟫ - ‖c‖ ^ 2 / 2) * ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-(‖y‖ ^ 2) / 2))) := by ring
    _ = ∫ y, (H y * Real.exp (⟪c, y⟫ - ‖c‖ ^ 2 / 2)) * Df2Play.gdens d y := by
      refine integral_congr_ae ?_
      filter_upwards with y
      dsimp [Df2Play.gdens]
      ring
    _ = ∫ g, H g * Real.exp (⟪c, g⟫ - ‖c‖ ^ 2 / 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      rw [Df2Play.integral_stdGaussian_eq d (fun g => H g * Real.exp (⟪c, g⟫ - ‖c‖ ^ 2 / 2))]

/-- The comparison under a shift: for `0 ≤ H ≤ β` measurable,
`E H(c + g) ≤ 2 E H(g) + β P(log 2 - ‖c‖²/2 < ⟪c, g⟫)`. -/
theorem integral_shift_le (H : EuclideanSpace ℝ (Fin d) → ℝ) (hH : Measurable H) (β : ℝ)
    (h0 : ∀ x, 0 ≤ H x) (h1 : ∀ x, H x ≤ β) (c : EuclideanSpace ℝ (Fin d)) :
    ∫ g, H (c + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      2 * ∫ g, H g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        β * (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫} := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set r : EuclideanSpace ℝ (Fin d) → ℝ := fun g => Real.exp (⟪c, g⟫ - ‖c‖ ^ 2 / 2) with hr
  have hinm : Measurable fun g : EuclideanSpace ℝ (Fin d) => ⟪c, g⟫ := (continuous_const.inner continuous_id).measurable
  have hrm : Measurable r := ((hinm.sub measurable_const).exp)
  have hr0 : ∀ g, 0 < r g := fun g => Real.exp_pos _
  have hβ : 0 ≤ β := (h0 0).trans (h1 0)
  have hrint : Integrable r γ := by
    by_contra hni
    have h := integral_shift_cm (d := d) (fun _ => (1 : ℝ)) c
    have h0' : ∫ g, r g ∂γ = 0 := integral_undef hni
    simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    rw [hr] at h0'
    linarith
  have hHint : Integrable H γ :=
    Integrable.mono' (integrable_const β) hH.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
  have hHr : Integrable (fun g => H g * r g) γ :=
    Integrable.mono' (hrint.const_mul β) (hH.mul hrm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 x) (hr0 x).le)]
        exact mul_le_mul_of_nonneg_right (h1 x) (hr0 x).le)
  set E := {g : EuclideanSpace ℝ (Fin d) | 2 < r g} with hE
  have hEm : MeasurableSet E := measurableSet_lt measurable_const hrm
  have hRint : Integrable (fun g => 2 * H g + β * E.indicator r g) γ :=
    (hHint.const_mul 2).add ((hrint.indicator hEm).const_mul β)
  have hpt : ∀ g, H g * r g ≤ 2 * H g + β * E.indicator r g := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
      have := mul_le_mul_of_nonneg_right (h1 g) (hr0 g).le
      linarith [h0 g]
    · rw [Set.indicator_of_notMem hg, mul_zero, add_zero]
      have : r g ≤ 2 := not_lt.mp hg
      nlinarith [h0 g]
  have hind : ∫ g, E.indicator r g ∂γ = γ.real {g | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫} := by
    have h := integral_shift_cm (d := d) (E.indicator fun _ => (1 : ℝ)) c
    have e1 : ∀ g, E.indicator (fun _ => (1 : ℝ)) g * Real.exp (⟪c, g⟫ - ‖c‖ ^ 2 / 2) = E.indicator r g := by
      intro g
      by_cases hg : g ∈ E
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    simp only [e1] at h
    rw [← h]
    have hiff : ∀ g, c + g ∈ E ↔ Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫ := by
      intro g
      show 2 < Real.exp (⟪c, c + g⟫ - ‖c‖ ^ 2 / 2) ↔ _
      rw [← Real.log_lt_iff_lt_exp (by norm_num), inner_add_right, real_inner_self_eq_norm_sq]
      constructor <;> intro h <;> linarith
    have e2 : (fun g => E.indicator (fun _ => (1 : ℝ)) (c + g)) =
        {g | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫}.indicator 1 := by
      funext g
      by_cases hg : Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫
      · rw [Set.indicator_of_mem ((hiff g).mpr hg), Set.indicator_of_mem (s := {g : EuclideanSpace ℝ (Fin d) | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫}) hg]; rfl
      · rw [Set.indicator_of_notMem (mt (hiff g).mp hg), Set.indicator_of_notMem (s := {g : EuclideanSpace ℝ (Fin d) | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫}) hg]
    rw [e2, integral_indicator_one (measurableSet_lt measurable_const hinm)]
  calc ∫ g, H (c + g) ∂γ = ∫ g, H g * r g ∂γ := integral_shift_cm H c
    _ ≤ ∫ g, (2 * H g + β * E.indicator r g) ∂γ := integral_mono hHr hRint hpt
    _ = 2 * ∫ g, H g ∂γ + β * ∫ g, E.indicator r g ∂γ := by
      rw [integral_add (hHint.const_mul 2) ((hrint.indicator hEm).const_mul β), integral_const_mul,
        integral_const_mul]
    _ = _ := by rw [hind]

/-! ## Derivatives -/

/-- A function that moves by at most `K |t|` along `t ↦ g + t u` has `|DF(g) u| ≤ K` (`fderiv` is `0` where `F` is
not differentiable). -/
theorem abs_fderiv_apply_le_of_dir (F : EuclideanSpace ℝ (Fin d) → ℝ) (g u : EuclideanSpace ℝ (Fin d)) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ t : ℝ, |F (g + t • u) - F g| ≤ K * |t|) : |fderiv ℝ F g u| ≤ K := by
  by_cases hdiff : DifferentiableAt ℝ F g
  · -- F is differentiable at g: use the derivative
    have h_deriv : HasDerivAt (fun (t : ℝ) => F (g + t • u)) ((fderiv ℝ F g) u) 0 := by
      have h_affine : HasDerivAt (fun (t : ℝ) => g + t • u) u 0 := by
        have h_smul : HasDerivAt (fun (t : ℝ) => t • u) u 0 := by
          have h := (hasDerivAt_id (0 : ℝ)).smul_const u
          simpa using h
        simpa [add_comm] using h_smul.add_const g
      have hF : HasFDerivAt F (fderiv ℝ F g) ((fun (t : ℝ) => g + t • u) 0) := by
        simpa [zero_smul, add_zero] using hdiff.hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF h_affine
    have h_slope : Filter.Tendsto (slope (fun (t : ℝ) => F (g + t • u)) 0) (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds ((fderiv ℝ F g) u)) := by
      rwa [hasDerivAt_iff_tendsto_slope] at h_deriv
    have h_slope_bound (t : ℝ) (ht : t ≠ 0) : |slope (fun (t : ℝ) => F (g + t • u)) 0 t| ≤ K := by
      have h_abs : |t⁻¹ • (F (g + t • u) - F g)| ≤ K := by
        calc
          |t⁻¹ • (F (g + t • u) - F g)| = |t⁻¹| * |F (g + t • u) - F g| := abs_smul _ _
          _ = |t|⁻¹ * |F (g + t • u) - F g| := by rw [abs_inv]
          _ ≤ |t|⁻¹ * (K * |t|) := by
            gcongr
            exact h t
          _ = K := by field_simp [ht]
      simpa [slope_def_module] using h_abs
    have h_upper : (fderiv ℝ F g) u ≤ K := by
      have h_eventually : ∀ᶠ (t : ℝ) in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, slope (fun (t : ℝ) => F (g + t • u)) 0 t ≤ K := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h_abs := h_slope_bound t ht
        exact (abs_le.mp h_abs).2
      exact le_of_tendsto h_slope h_eventually
    have h_lower : -K ≤ (fderiv ℝ F g) u := by
      have h_eventually : ∀ᶠ (t : ℝ) in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, (-slope (fun (t : ℝ) => F (g + t • u)) 0) t ≤ K := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h_abs := h_slope_bound t ht
        have h_le := (abs_le.mp h_abs).1
        have h' : -(slope (fun (t : ℝ) => F (g + t • u)) 0 t) ≤ K := by linarith
        simpa using h'
      have h_tendsto_neg : Filter.Tendsto ((-slope (fun (t : ℝ) => F (g + t • u)) 0)) (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds (-((fderiv ℝ F g) u))) :=
        h_slope.neg
      have h_neg_le : -((fderiv ℝ F g) u) ≤ K := le_of_tendsto h_tendsto_neg h_eventually
      linarith
    exact abs_le.mpr ⟨h_lower, h_upper⟩
  · -- F is not differentiable at g: fderiv is zero
    have h_fderiv_zero : fderiv ℝ F g = 0 := fderiv_zero_of_not_differentiableAt hdiff
    simp [h_fderiv_zero, hK]

/-- The Stein form of a Gaussian Hessian: for `e` convex and `K`-Lipschitz and `T S = 1`,
`|E[e(w + T g)(⟪g, S a⟫ ⟪g, S b⟫ - ⟪S a, S b⟫)]| ≤ K ‖b‖ ‖S a‖`. -/
theorem stein_hess_bound (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (w : EuclideanSpace ℝ (Fin d))
    (T S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hTS : ∀ x, T (S x) = x)
    (a b : EuclideanSpace ℝ (Fin d)) :
    |∫ g, e (w + T g) * (⟪g, S a⟫ * ⟪g, S b⟫ - ⟪S a, S b⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      K * ‖b‖ * ‖S a‖ := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun g => e (w + T g) with hF
  have hF_convex : ConvexOn ℝ Set.univ F := by
    let g : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      { toFun := fun x => w + T x
        linear := T.toLinearMap
        map_vadd' := by
          intro p v
          simp [vadd_eq_add, add_comm, add_left_comm, T.map_add] }
    have hF_eq : F = e ∘ g := by
      ext x
      simp [F, g]
    rw [hF_eq]
    exact hc.comp_affineMap g
  have hF_lip : LipschitzWith (K * ‖T‖₊) F := by
    have hT_lip : LipschitzWith ‖T‖₊ (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
      T.lipschitzWith
    have h_add_lip : LipschitzWith 1 (fun (x : EuclideanSpace ℝ (Fin d)) => w + x) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp [dist_eq_norm, add_sub_add_left_eq_sub]
    have h_add_T_lip : LipschitzWith (1 * ‖T‖₊) (fun x => w + T x) :=
      h_add_lip.comp hT_lip
    have hF_lip' : LipschitzWith (K * (1 * ‖T‖₊)) (fun x => e (w + T x)) :=
      he.comp h_add_T_lip
    have hconst : (K : ℝ≥0) * (1 * ‖T‖₊) = K * ‖T‖₊ := by
      ext; simp
    simpa [F, hconst] using hF_lip'
  have h_eq := ibpLip d F (K * ‖T‖₊) hF_lip hF_convex (S a) (S b)
  rcases h_eq with ⟨_, h_eq2⟩
  have h_target_integral_eq : ∫ g, e (w + T g) * (⟪g, S a⟫ * ⟪g, S b⟫ - ⟪S a, S b⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ⟪S a, g⟫ * fderiv ℝ F g (S b) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    calc
      ∫ g, e (w + T g) * (⟪g, S a⟫ * ⟪g, S b⟫ - ⟪S a, S b⟫) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
          = ∫ g, (⟪S a, g⟫ * ⟪S b, g⟫ - ⟪S a, S b⟫) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [F, mul_comm, real_inner_comm]
      _ = ∫ g, ⟪S a, g⟫ * fderiv ℝ F g (S b) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := h_eq2
  rw [h_target_integral_eq]
  have h_fderiv_bound : ∀ g, |fderiv ℝ F g (S b)| ≤ (K : ℝ) * ‖b‖ := by
    intro g
    apply abs_fderiv_apply_le_of_dir F g (S b) ((K : ℝ) * ‖b‖)
    · have hK : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
      have hb : 0 ≤ ‖b‖ := norm_nonneg _
      nlinarith
    · intro t
      calc
        |F (g + t • S b) - F g| = |e (w + T (g + t • S b)) - e (w + T g)| := rfl
        _ = |e (w + (T g + t • T (S b))) - e (w + T g)| := by
          simp [T.map_add]
        _ = |e (w + T g + t • T (S b)) - e (w + T g)| := by
          simp [add_assoc, sub_eq_add_neg]
        _ = |e (w + T g + t • b) - e (w + T g)| := by rw [hTS b]
        _ ≤ (K : ℝ) * ‖(w + T g + t • b) - (w + T g)‖ := he.dist_le_mul _ _
        _ = (K : ℝ) * ‖t • b‖ := by simp
        _ = (K : ℝ) * (|t| * ‖b‖) := by rw [norm_smul, Real.norm_eq_abs]
        _ = ((K : ℝ) * ‖b‖) * |t| := by ring
  have h_int_inner : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪S a, g⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa using IsGaussian.integrable_dual (stdGaussian (EuclideanSpace ℝ (Fin d))) (innerSL ℝ (S a))
  have h_int_abs_inner : Integrable (fun g : EuclideanSpace ℝ (Fin d) => |⟪S a, g⟫|)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h := (integrable_norm_iff (h_int_inner.aestronglyMeasurable)).mpr h_int_inner
    simpa using h
  have h_nonneg_abs : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (Fin d))]
      (fun g => |⟪S a, g⟫| * |fderiv ℝ F g (S b)|) := by
    filter_upwards with g
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h_bound_pointwise : (fun g => |⟪S a, g⟫| * |fderiv ℝ F g (S b)|) ≤ᵐ[stdGaussian (EuclideanSpace ℝ (Fin d))]
      (fun g => |⟪S a, g⟫| * ((K : ℝ) * ‖b‖)) := by
    filter_upwards with g
    refine mul_le_mul_of_nonneg_left (h_fderiv_bound g) (abs_nonneg _)
  have h_int_bound : Integrable (fun g : EuclideanSpace ℝ (Fin d) => |⟪S a, g⟫| * ((K : ℝ) * ‖b‖))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have : (fun g => |⟪S a, g⟫| * ((K : ℝ) * ‖b‖)) = (fun g => ((K : ℝ) * ‖b‖) * |⟪S a, g⟫|) := by
      ext g; ring
    rw [this]
    exact h_int_abs_inner.const_mul ((K : ℝ) * ‖b‖)
  calc
    |∫ g, ⟪S a, g⟫ * fderiv ℝ F g (S b) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
        ∫ g, |⟪S a, g⟫ * fderiv ℝ F g (S b)| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ g, |⟪S a, g⟫| * |fderiv ℝ F g (S b)| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine integral_congr_ae ?_
      filter_upwards with g
      simp [abs_mul]
    _ ≤ ∫ g, |⟪S a, g⟫| * ((K : ℝ) * ‖b‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      MeasureTheory.integral_mono_of_nonneg h_nonneg_abs h_int_bound h_bound_pointwise
    _ = (∫ g, |⟪S a, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) * ((K : ℝ) * ‖b‖) := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ ‖S a‖ * ((K : ℝ) * ‖b‖) := by
      have h := integral_abs_inner_le (S a)
      have h_nonneg : 0 ≤ (K : ℝ) * ‖b‖ := by
        have hK : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
        have hb : 0 ≤ ‖b‖ := norm_nonneg _
        nlinarith
      exact mul_le_mul_of_nonneg_right h h_nonneg
    _ = (K : ℝ) * ‖b‖ * ‖S a‖ := by ring

/-- Taylor from below: a lower bound `m` on `f''(μ + t v)(v, v)` along the segment gives
`f(μ + v) ≥ f(μ) + f'(μ) v + m/2`. -/
theorem taylor_lower (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 2 f) (μ v : EuclideanSpace ℝ (Fin d))
    (m : ℝ) (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, m ≤ fderiv ℝ (fderiv ℝ f) (μ + t • v) v v) :
    f μ + fderiv ℝ f μ v + m / 2 ≤ f (μ + v) := by
  have hn1 : fderiv ℝ (fun y => -f y) = fun x => -fderiv ℝ f x := funext fun x => fderiv_neg
  have hn2 : fderiv ℝ (fun x => -fderiv ℝ f x) = fun x => -fderiv ℝ (fderiv ℝ f) x := funext fun x => fderiv_neg
  have h := Layer2.taylor_upper (fun y => -f y) hf.neg μ v (-m) (fun t ht => by
    rw [hn1, hn2]
    simp only [neg_apply]
    linarith [hm t ht])
  rw [hn1] at h
  simp only [neg_apply] at h
  linarith

end AdversarialBco.Poly.SIF
