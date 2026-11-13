/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSICond
public import AdversarialBco.Poly.SrcToolsProof

@[expose] public section

/-!
# Gaussian integrals along a direction

Under the standard Gaussian `gam d` on `Fin d → ℝ`: the law of `z ⬝ᵥ b` for a unit vector `b`, its moments and
tails, the moments of `z ⬝ᵥ z`, and Lemma TR along a direction: for `Y ≥ 0` in `L²`,

* `tr_dot`: `∫ Y (z ⬝ᵥ b)² ≤ |b|² (T ∫ Y + (∫ Y²)^{1/2} (105^{1/2} e^{-T/4})^{1/2})`;
* `tr_quad`: `∫ Y ((z ⬝ᵥ b)² - |b|²)² ≤ |b|⁴ (T ∫ Y + (∫ Y²)^{1/2} (2027025^{1/2} e^{-T^{1/2}/4})^{1/2})`
  for `T ≥ 1`.

The first is the variance of the LQ increment, the second that of the S-DF and DQ increments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-! ## Leaves -/

theorem charFunDual_gaussianReal_smul_id (c : ℝ) :
    charFunDual (gaussianReal 0 1) (c • ContinuousLinearMap.id ℝ ℝ) = charFun (gaussianReal 0 1) c := by
  rw [charFunDual_eq_charFun_map_one]
  have h : (fun x : ℝ => (c • ContinuousLinearMap.id ℝ ℝ) x) = (fun x => c * x) := by
    ext x; simp
  simp [h, charFun_map_mul, mul_one]

-- Helper lemma: (t • L).comp (ContinuousLinearMap.single ...) = (t * b i) • id
-- where L is the linear functional z ↦ z ⬝ᵥ b
theorem dotL_comp_single_eq (d : ℕ) (b : Fin d → ℝ) (t : ℝ) (i : Fin d)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : ∀ z, L z = z ⬝ᵥ b) :
    (t • L).comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i) = (t * b i) • ContinuousLinearMap.id ℝ ℝ := by
  refine ContinuousLinearMap.ext fun x => ?_
  calc
    ((t • L).comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)) x
        = (t • L) ((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i) x) := rfl
    _ = (t • L) (Pi.single i x) := rfl
    _ = t * (L (Pi.single i x)) := by simp [smul_eq_mul]
    _ = t * ((Pi.single i x) ⬝ᵥ b) := by rw [hL]
    _ = t * (x * b i) := by simp [dotProduct, Pi.single, Function.update]
    _ = (t * b i) * x := by ring
    _ = ((t * b i) • ContinuousLinearMap.id ℝ ℝ) x := by simp [smul_eq_mul]

theorem map_dot_gam (b : Fin d → ℝ) (hb : b ⬝ᵥ b = 1) :
    (gam d).map (fun z => z ⬝ᵥ b) = gaussianReal 0 1 := by
  -- define the linear functional z ↦ z ⬝ᵥ b
  let L : (Fin d → ℝ) →L[ℝ] ℝ := by
    let f : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun z => z ⬝ᵥ b
        map_add' := fun x y => by
          simp [dotProduct, add_mul, Finset.sum_add_distrib]
        map_smul' := fun r x => by
          simp [dotProduct, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm] }
    exact f.toContinuousLinearMap
  have hL_apply (z : Fin d → ℝ) : L z = z ⬝ᵥ b := rfl
  have h_map_eq : (fun z => z ⬝ᵥ b) = (L : (Fin d → ℝ) → ℝ) := by
    ext z; simp [hL_apply]
  rw [h_map_eq]
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_eq_charFunDual_smul L t]
  rw [charFunDual_pi (t • L)]
  have h_comp (i : Fin d) : (t • L).comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i) = (t * b i) • ContinuousLinearMap.id ℝ ℝ :=
    dotL_comp_single_eq d b t i L hL_apply
  simp_rw [h_comp]
  simp_rw [charFunDual_gaussianReal_smul_id]
  simp_rw [charFun_gaussianReal]
  -- Simplify the expressions inside cexp
  simp
  -- Now we have: ∏ i, cexp (-(↑t * ↑(b i)) ^ 2 / 2) = cexp (-(↑t ^ 2) / 2)
  have h_sum_sq' : (∑ i : Fin d, ((b i : ℂ)) ^ 2) = (1 : ℂ) := by
    have h : (∑ i : Fin d, b i * b i) = 1 := by simpa [dotProduct] using hb
    simpa [sq] using congrArg (fun x : ℝ => (x : ℂ)) h
  -- Use cexp of sum
  rw [← Complex.exp_sum]
  -- Goal: cexp (∑ i, -((t * b i)^2 / 2)) = cexp (-(t^2) / 2)
  congr
  -- Need: ∑ i, -((t * b i)^2 / 2) = -(t^2) / 2  (in ℂ)
  calc
    (∑ i : Fin d, -(((t : ℂ) * (b i : ℂ)) ^ 2 / 2))
        = -(∑ i : Fin d, ((t : ℂ) * (b i : ℂ)) ^ 2 / 2) := by rw [Finset.sum_neg_distrib]
    _ = -((∑ i : Fin d, ((t : ℂ) * (b i : ℂ)) ^ 2) / 2) := by rw [Finset.sum_div]
    _ = -(((t : ℂ)^2 * (∑ i : Fin d, (b i : ℂ)^2)) / 2) := by
      simp [Finset.mul_sum, mul_pow]
    _ = -(((t : ℂ)^2 * (1 : ℂ)) / 2) := by rw [h_sum_sq']
    _ = -((t : ℂ) ^ 2 / 2) := by simp


theorem memLp_dot (b : Fin d → ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun z : Fin d → ℝ => z ⬝ᵥ b) p (gam d) := by
  have h_coord (i : Fin d) : MemLp (fun z : Fin d → ℝ => z i) p (gam d) := by
    have h_mp : MeasurePreserving (fun z : Fin d → ℝ => z i) (gam d) (gaussianReal (0 : ℝ) 1) := by
      unfold gam
      exact measurePreserving_eval (fun _ : Fin d => gaussianReal (0 : ℝ) 1) i
    have h_id : MemLp id p (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal' p hp
    exact h_id.comp_measurePreserving h_mp
  have h_scaled (i : Fin d) (hi : i ∈ Finset.univ) : MemLp (fun z : Fin d → ℝ => z i * b i) p (gam d) :=
    (h_coord i).mul_const (b i)
  have h_sum : (fun z : Fin d → ℝ => z ⬝ᵥ b) = (fun z => ∑ i : Fin d, z i * b i) := by
    ext z
    simp [dotProduct]
  rw [h_sum]
  exact memLp_finsetSum Finset.univ h_scaled

theorem iteratedDeriv_four_exp_half_sq_zero : iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  -- First derivative: deriv f = fun t => t * exp(t^2/2)
  have h1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_exp (by fun_prop)]
    simp [deriv_div_const, deriv_fun_pow, deriv_id'']
    ring
  rw [h1]
  -- Second derivative: deriv (fun t => t * exp(t^2/2)) = fun t => (1 + t^2) * exp(t^2/2)
  have h2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) = fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t
    have h_hasDeriv : HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
      have h_exp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
        have h_inner : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
          have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
            simpa using hasDerivAt_pow 2 t
          simpa using this.div_const 2
        have h_comp : HasDerivAt (Real.exp ∘ (fun t : ℝ => t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t :=
          (Real.hasDerivAt_exp (t ^ 2 / 2)).comp t h_inner
        have : Real.exp ∘ (fun t : ℝ => t ^ 2 / 2) = (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by
          ext s; rfl
        rw [this] at h_comp
        simpa [mul_comm] using h_comp
      have h_mul := HasDerivAt.mul h_id h_exp
      have : (fun t : ℝ => t) * (fun t : ℝ => Real.exp (t ^ 2 / 2)) = (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) := by
        ext s; rfl
      rw [this] at h_mul
      have : (1 : ℝ) * Real.exp (t ^ 2 / 2) + t * (t * Real.exp (t ^ 2 / 2)) = (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
        ring
      rw [this] at h_mul
      exact h_mul
    exact h_hasDeriv.deriv
  rw [h2]
  -- Third derivative: deriv (fun t => (1 + t^2) * exp(t^2/2)) = fun t => (3*t + t^3) * exp(t^2/2)
  have h3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) = fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t
    have h_hasDeriv : HasDerivAt (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
      have h_poly : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).add_const 1)
      have h_exp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
        have h_inner : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
          have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
            simpa using hasDerivAt_pow 2 t
          simpa using this.div_const 2
        have h_comp : HasDerivAt (Real.exp ∘ (fun t : ℝ => t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t :=
          (Real.hasDerivAt_exp (t ^ 2 / 2)).comp t h_inner
        have : Real.exp ∘ (fun t : ℝ => t ^ 2 / 2) = (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by
          ext s; rfl
        rw [this] at h_comp
        simpa [mul_comm] using h_comp
      have h_mul := HasDerivAt.mul h_poly h_exp
      have : (fun t : ℝ => 1 + t ^ 2) * (fun t : ℝ => Real.exp (t ^ 2 / 2)) = (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) := by
        ext s; rfl
      rw [this] at h_mul
      have : (2 * t) * Real.exp (t ^ 2 / 2) + (1 + t ^ 2) * (t * Real.exp (t ^ 2 / 2)) = (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
        ring
      rw [this] at h_mul
      exact h_mul
    exact h_hasDeriv.deriv
  rw [h3]
  -- Fourth derivative: deriv (fun t => (3*t + t^3) * exp(t^2/2)) 0 = 3
  have h_hasDeriv : HasDerivAt (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) 3 0 := by
    have h_poly : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) 3 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (3 : ℝ) * t) 3 0 := by
        have := (hasDerivAt_id 0).const_mul (3 : ℝ)
        simpa [mul_comm] using this
      have h2 : HasDerivAt (fun t : ℝ => t ^ 3) 0 0 := by
        simpa using hasDerivAt_pow 3 (0 : ℝ)
      have h_add := HasDerivAt.add h1 h2
      have : (fun t : ℝ => (3 : ℝ) * t) + (fun t : ℝ => t ^ 3) = (fun t : ℝ => 3 * t + t ^ 3) := by
        ext s; simp [mul_comm]
      rw [this] at h_add
      simpa [add_zero] using h_add
    have h_exp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 0 := by
      have h_inner : HasDerivAt (fun t : ℝ => t ^ 2 / 2) 0 0 := by
        have : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
          simpa using hasDerivAt_pow 2 (0 : ℝ)
        simpa using this.div_const 2
      have h_comp : HasDerivAt (Real.exp ∘ (fun t : ℝ => t ^ 2 / 2)) (Real.exp (0 ^ 2 / 2) * 0) 0 :=
        (Real.hasDerivAt_exp (0 ^ 2 / 2)).comp 0 h_inner
      have : Real.exp ∘ (fun t : ℝ => t ^ 2 / 2) = (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by
        ext s; rfl
      rw [this] at h_comp
      simpa [Real.exp_zero] using h_comp
    have h_mul := HasDerivAt.mul h_poly h_exp
    have : (fun t : ℝ => 3 * t + t ^ 3) * (fun t : ℝ => Real.exp (t ^ 2 / 2)) = (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) := by
      ext s; rfl
    rw [this] at h_mul
    simpa [add_zero, mul_one, Real.exp_zero] using h_mul
  exact h_hasDeriv.deriv

-- Helper lemma: the fourth moment of the standard Gaussian is 3
theorem integral_id_pow_four_gaussianReal_zero_one : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h_mem : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) 1)) := by
    rw [integrableExpSet_id_gaussianReal]
    rw [interior_univ]
    exact Set.mem_univ _
  have h_mgf := iteratedDeriv_mgf_zero h_mem 4
  have h_moment : (gaussianReal (0 : ℝ) 1)[id ^ 4] = ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) := by
    simp
  rw [h_moment] at h_mgf
  rw [← h_mgf]
  rw [mgf_id_gaussianReal]
  have h_simp : (fun t : ℝ => Real.exp (0 * t + (1 : NNReal) * t ^ 2 / 2)) = (fun t : ℝ => Real.exp (t ^ 2 / 2)) := by
    ext t
    simp
  rw [h_simp]
  exact iteratedDeriv_four_exp_half_sq_zero

theorem integral_dot_self_sq_le : ∫ z, (z ⬝ᵥ z) ^ 2 ∂(gam d) ≤ 3 * (d : ℝ) ^ 2 := by
  -- Step 1: Pointwise inequality (z ⬝ᵥ z)^2 ≤ d * ∑ i, (z i)^4
  have h_pointwise : ∀ z : Fin d → ℝ, (z ⬝ᵥ z) ^ 2 ≤ (d : ℝ) * (∑ i : Fin d, (z i) ^ 4) := by
    intro z
    have h_dot : z ⬝ᵥ z = ∑ i : Fin d, z i ^ 2 := by
      simp [dotProduct, sq]
    rw [h_dot]
    have h_sq_sum : (∑ i : Fin d, z i ^ 2) ^ 2 ≤ (d : ℝ) * (∑ i : Fin d, (z i ^ 2) ^ 2) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin d => z i ^ 2)
      simpa [Finset.card_fin] using h
    have h_pow4 : ∀ i : Fin d, (z i ^ 2) ^ 2 = (z i) ^ 4 := by
      intro i; ring
    simpa [h_pow4] using h_sq_sum

  -- Step 2: Integrability of x^4 under standard Gaussian
  have h_int_x4_gaussian : Integrable (fun x : ℝ => x ^ 4) (gaussianReal (0 : ℝ) 1) := by
    have h_mem : MemLp id 4 (gaussianReal (0 : ℝ) 1) :=
      memLp_id_gaussianReal (μ := 0) (v := 1) 4
    have h_norm : Integrable (fun x : ℝ => ‖x ^ 4‖) (gaussianReal 0 1) := by
      have : (fun x : ℝ => ‖x ^ 4‖) = (fun x : ℝ => |x| ^ 4) := by
        ext x; simp [Real.norm_eq_abs]
      rw [this]
      simpa using h_mem.integrable_norm_pow' (p := 4)
    have h_ae : AEStronglyMeasurable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
      refine (continuous_id.pow 4).aestronglyMeasurable
    exact ((integrable_norm_iff h_ae).mp h_norm)

  -- Step 3: Integrability of each (z i)^4 w.r.t. gam d
  have h_int_zi4 (i : Fin d) : Integrable (fun z : Fin d → ℝ => (z i) ^ 4) (gam d) := by
    -- gam d = Measure.pi fun _ => gaussianReal 0 1
    -- Use integrable_comp_eval
    simpa [gam] using integrable_comp_eval h_int_x4_gaussian (μ := fun _ : Fin d => gaussianReal (0 : ℝ) (1 : NNReal)) (i := i)

  -- Step 4: Integrability of the RHS (sum of x_i^4)
  have h_int_rhs : Integrable (fun z : Fin d → ℝ => (d : ℝ) * (∑ i : Fin d, (z i) ^ 4)) (gam d) := by
    have h_sum : Integrable (fun z : Fin d → ℝ => ∑ i : Fin d, (z i) ^ 4) (gam d) :=
      integrable_finsetSum _ (fun i _ => h_int_zi4 i)
    exact h_sum.const_mul (d : ℝ)

  -- Step 5: Integrability of LHS (by comparison with RHS)
  have h_int_lhs : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) (gam d) := by
    have h_ae : AEStronglyMeasurable (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) (gam d) := by
      refine ((continuous_id.dotProduct continuous_id).pow 2).aestronglyMeasurable
    have h_nonneg : (fun _ : Fin d → ℝ => (0 : ℝ)) ≤ᵐ[gam d] (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) := by
      filter_upwards with z
      exact pow_two_nonneg (z ⬝ᵥ z)
    have h_le : (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) ≤ᵐ[gam d] (fun z : Fin d → ℝ => (d : ℝ) * (∑ i : Fin d, (z i) ^ 4)) := by
      filter_upwards with z
      exact h_pointwise z
    have h_zero_int : Integrable (fun _ : Fin d → ℝ => (0 : ℝ)) (gam d) :=
      integrable_const _
    exact integrable_of_le_of_le h_ae h_nonneg h_le h_zero_int h_int_rhs

  -- Step 6: Integrate both sides
  have h_int_ineq : ∫ z : Fin d → ℝ, (z ⬝ᵥ z) ^ 2 ∂(gam d) ≤ ∫ z : Fin d → ℝ, (d : ℝ) * (∑ i : Fin d, (z i) ^ 4) ∂(gam d) := by
    refine integral_mono h_int_lhs h_int_rhs h_pointwise

  -- Step 7: Compute the RHS integral
  have h_rhs : ∫ z : Fin d → ℝ, (d : ℝ) * (∑ i : Fin d, (z i) ^ 4) ∂(gam d) = 3 * (d : ℝ) ^ 2 := by
    calc
      ∫ z : Fin d → ℝ, (d : ℝ) * (∑ i : Fin d, (z i) ^ 4) ∂(gam d)
          = (d : ℝ) * ∫ z : Fin d → ℝ, (∑ i : Fin d, (z i) ^ 4) ∂(gam d) := by
        rw [integral_const_mul]
      _ = (d : ℝ) * (∑ i : Fin d, ∫ z : Fin d → ℝ, (z i) ^ 4 ∂(gam d)) := by
        rw [integral_finsetSum Finset.univ (fun i _ => h_int_zi4 i)]
      _ = (d : ℝ) * (∑ i : Fin d, ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) := by
        refine congrArg (fun t => (d : ℝ) * t) (Finset.sum_congr rfl (fun i hi => ?_))
        rw [integral_comp_eval h_int_x4_gaussian.aestronglyMeasurable (μ := fun _ : Fin d => gaussianReal (0 : ℝ) (1 : NNReal)) (i := i)]
      _ = (d : ℝ) * (∑ i : Fin d, 3) := by
        simp [integral_id_pow_four_gaussianReal_zero_one]
      _ = (d : ℝ) * ((d : ℝ) * 3) := by simp
      _ = 3 * (d : ℝ) ^ 2 := by ring

  -- Step 8: Combine
  linarith

theorem tail_dot (b : Fin d → ℝ) (hb : b ⬝ᵥ b = 1) (k : ℕ) (T : ℝ) (hk : 1 ≤ k) (hT : 0 ≤ T) :
    ∫ z, {z : Fin d → ℝ | T < |z ⬝ᵥ b|}.indicator (fun z => (z ⬝ᵥ b) ^ (2 * k)) z ∂(gam d) ≤
      Real.sqrt ((4 * k - 1).doubleFactorial) * Real.exp (-T ^ 2 / 4) := by
  have h_meas : AEMeasurable (fun (z : Fin d → ℝ) => z ⬝ᵥ b) (gam d) := by
    refine (Continuous.aemeasurable ?_)
    continuity
  have h_set_meas : MeasurableSet {x : ℝ | T < |x|} := by
    have h_abs : Measurable (fun (x : ℝ) => |x|) := measurable_abs
    exact measurableSet_lt measurable_const h_abs
  have h_f_meas : Measurable (fun (x : ℝ) => x ^ (2 * k)) :=
    measurable_id.pow_const (2 * k)
  have h_indicator_meas : Measurable ({x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k))) :=
    (h_f_meas.indicator h_set_meas)
  have h_ae : AEStronglyMeasurable (fun (x : ℝ) => {x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k)) x)
      ((gam d).map (fun (z : Fin d → ℝ) => z ⬝ᵥ b)) :=
    h_indicator_meas.aestronglyMeasurable
  have h_integrand_eq : ∀ z : Fin d → ℝ,
      {z : Fin d → ℝ | T < |z ⬝ᵥ b|}.indicator (fun z => (z ⬝ᵥ b) ^ (2 * k)) z =
      ({x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k))) (z ⬝ᵥ b) := by
    intro z
    by_cases hz : T < |z ⬝ᵥ b|
    · simp [hz]
    · simp [hz]
  calc
    ∫ z, {z : Fin d → ℝ | T < |z ⬝ᵥ b|}.indicator (fun z => (z ⬝ᵥ b) ^ (2 * k)) z ∂(gam d)
        = ∫ z, ({x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k))) (z ⬝ᵥ b) ∂(gam d) := by
      refine integral_congr_ae ?_
      filter_upwards with z
      exact h_integrand_eq z
    _ = ∫ x, {x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k)) x ∂((gam d).map (fun z => z ⬝ᵥ b)) := by
      rw [← MeasureTheory.integral_map h_meas h_ae]
    _ = ∫ x, {x : ℝ | T < |x|}.indicator (fun x => x ^ (2 * k)) x ∂(gaussianReal 0 1) := by
      rw [map_dot_gam b hb]
    _ ≤ Real.sqrt ((4 * k - 1).doubleFactorial) * Real.exp (-T ^ 2 / 4) :=
      gauss_tail_T1' k T hk hT

/-! ## Moments -/

theorem memLp_dot_pow (b : Fin d → ℝ) (k : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun z : Fin d → ℝ => (z ⬝ᵥ b) ^ k) p (gam d) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero]; exact memLp_const 1
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have h := (memLp_dot b (p * k) (ENNReal.mul_ne_top hp (ENNReal.natCast_ne_top k))).norm_rpow_div (k : ℝ≥0∞)
  rw [ENNReal.mul_div_cancel_right hk0 (ENNReal.natCast_ne_top k)] at h
  have hm : AEStronglyMeasurable (fun z : Fin d → ℝ => (z ⬝ᵥ b) ^ k) (gam d) :=
    ((continuous_id.dotProduct continuous_const).pow k).aestronglyMeasurable
  refine h.mono hm (Filter.Eventually.of_forall fun z => ?_)
  simp [Real.norm_eq_abs, ENNReal.toReal_natCast, Real.rpow_natCast]

/-! ## Lemma TR along a direction -/

theorem unit_of_ne {b : Fin d → ℝ} (hb : b ⬝ᵥ b ≠ 0) :
    ((Real.sqrt (b ⬝ᵥ b))⁻¹ • b) ⬝ᵥ ((Real.sqrt (b ⬝ᵥ b))⁻¹ • b) = 1 := by
  have h0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hpos : 0 < b ⬝ᵥ b := lt_of_le_of_ne h0 (Ne.symm hb)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt h0, inv_mul_cancel₀ hpos.ne']

theorem dot_eq_unit {b : Fin d → ℝ} (hb : b ⬝ᵥ b ≠ 0) (z : Fin d → ℝ) :
    (z ⬝ᵥ b) ^ 2 = (b ⬝ᵥ b) * (z ⬝ᵥ ((Real.sqrt (b ⬝ᵥ b))⁻¹ • b)) ^ 2 := by
  have h0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hs : Real.sqrt (b ⬝ᵥ b) ≠ 0 := by
    rw [Real.sqrt_ne_zero h0]; exact hb
  rw [dotProduct_smul, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt h0]
  field_simp

theorem dot_self_eq_zero {b : Fin d → ℝ} (hb : b ⬝ᵥ b = 0) : b = 0 := by
  funext i
  have h : ∀ j ∈ Finset.univ, 0 ≤ b j * b j := fun j _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg h).1 hb i (Finset.mem_univ i)
  simpa using this

theorem tr_dot (Y : (Fin d → ℝ) → ℝ) (hY0 : ∀ z, 0 ≤ Y z) (hY2 : MemLp Y 2 (gam d)) (b : Fin d → ℝ) (T : ℝ)
    (hT : 0 ≤ T) :
    ∫ z, Y z * (z ⬝ᵥ b) ^ 2 ∂(gam d) ≤
      (b ⬝ᵥ b) * (T * ∫ z, Y z ∂(gam d) +
        Real.sqrt (∫ z, Y z ^ 2 ∂(gam d)) * Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4))) := by
  by_cases hb : b ⬝ᵥ b = 0
  · rw [dot_self_eq_zero hb]; simp
  set u := (Real.sqrt (b ⬝ᵥ b))⁻¹ • b with hu
  have hu1 : u ⬝ᵥ u = 1 := unit_of_ne hb
  have e1 : (fun z => Y z * (z ⬝ᵥ b) ^ 2) = fun z => (b ⬝ᵥ b) * (Y z * (z ⬝ᵥ u) ^ 2) := by
    funext z; rw [dot_eq_unit hb z]; ring
  rw [e1, integral_const_mul]
  have h0 : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ h0
  have hZ2 : MemLp (fun z : Fin d → ℝ => (z ⬝ᵥ u) ^ 2) 2 (gam d) := memLp_dot_pow u 2 2 (by norm_num)
  have hTR := lemmaTR1_main (gam d) Y (fun z => (z ⬝ᵥ u) ^ 2) T hY0 (fun z => sq_nonneg _) hT hY2 hZ2
  refine hTR.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)))
  have hsT := Real.sqrt_nonneg T
  have e2 : {z : Fin d → ℝ | T < (z ⬝ᵥ u) ^ 2}.indicator (fun z => ((z ⬝ᵥ u) ^ 2) ^ 2) =
      {z : Fin d → ℝ | Real.sqrt T < |z ⬝ᵥ u|}.indicator (fun z => (z ⬝ᵥ u) ^ (2 * 2)) := by
    funext z
    have hiff : T < (z ⬝ᵥ u) ^ 2 ↔ Real.sqrt T < |z ⬝ᵥ u| := by
      rw [← Real.sqrt_lt_sqrt_iff hT, Real.sqrt_sq_eq_abs]
    by_cases h : T < (z ⬝ᵥ u) ^ 2
    · rw [Set.indicator_of_mem (show z ∈ {z : Fin d → ℝ | T < (z ⬝ᵥ u) ^ 2} from h),
        Set.indicator_of_mem (show z ∈ {z : Fin d → ℝ | Real.sqrt T < |z ⬝ᵥ u|} from hiff.1 h)]
      ring
    · rw [Set.indicator_of_notMem (show z ∉ {z : Fin d → ℝ | T < (z ⬝ᵥ u) ^ 2} from h),
        Set.indicator_of_notMem (show z ∉ {z : Fin d → ℝ | Real.sqrt T < |z ⬝ᵥ u|} from fun h' => h (hiff.2 h'))]
  rw [e2]
  have ht := tail_dot u hu1 2 (Real.sqrt T) (by norm_num) hsT
  have h7 : ((4 * 2 - 1 : ℕ)).doubleFactorial = 105 := by decide
  rw [h7, Real.sq_sqrt hT] at ht
  calc _ ≤ Real.sqrt ((105 : ℕ) : ℝ) * Real.exp (-T / 4) := ht
    _ = Real.sqrt 105 * Real.exp (-T / 4) := by norm_num

theorem tr_quad (Y : (Fin d → ℝ) → ℝ) (hY0 : ∀ z, 0 ≤ Y z) (hY2 : MemLp Y 2 (gam d)) (b : Fin d → ℝ) (T : ℝ)
    (hT : 1 ≤ T) :
    ∫ z, Y z * ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 2 ∂(gam d) ≤
      (b ⬝ᵥ b) ^ 2 * (T * ∫ z, Y z ∂(gam d) +
        Real.sqrt (∫ z, Y z ^ 2 ∂(gam d)) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4))) := by
  by_cases hb : b ⬝ᵥ b = 0
  · rw [dot_self_eq_zero hb]; simp
  set u := (Real.sqrt (b ⬝ᵥ b))⁻¹ • b with hu
  have hu1 : u ⬝ᵥ u = 1 := unit_of_ne hb
  have e1 : (fun z => Y z * ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 2) =
      fun z => (b ⬝ᵥ b) ^ 2 * (Y z * ((z ⬝ᵥ u) ^ 2 - 1) ^ 2) := by
    funext z; rw [dot_eq_unit hb z]; ring
  rw [e1, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hT0 : 0 ≤ T := by linarith
  have hZ2 : MemLp (fun z : Fin d → ℝ => ((z ⬝ᵥ u) ^ 2 - 1) ^ 2) 2 (gam d) := by
    have h4 := memLp_dot_pow u 4 2 (by norm_num)
    have h2 := memLp_dot_pow u 2 2 (by norm_num)
    have e : (fun z : Fin d → ℝ => ((z ⬝ᵥ u) ^ 2 - 1) ^ 2) =
        fun z => (z ⬝ᵥ u) ^ 4 - 2 * (z ⬝ᵥ u) ^ 2 + 1 := by funext z; ring
    rw [e]
    exact (h4.sub (h2.const_mul 2)).add (memLp_const 1)
  have hTR := lemmaTR1_main (gam d) Y (fun z => ((z ⬝ᵥ u) ^ 2 - 1) ^ 2) T hY0 (fun z => sq_nonneg _) hT0 hY2 hZ2
  refine hTR.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)))
  set c := Real.sqrt (Real.sqrt T) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = Real.sqrt T := Real.sq_sqrt (Real.sqrt_nonneg T)
  have hsT1 : 1 ≤ Real.sqrt T := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT
  -- pointwise domination of the tail
  have hdom : ∀ z, {z : Fin d → ℝ | T < ((z ⬝ᵥ u) ^ 2 - 1) ^ 2}.indicator
      (fun z => (((z ⬝ᵥ u) ^ 2 - 1) ^ 2) ^ 2) z ≤
      {z : Fin d → ℝ | c < |z ⬝ᵥ u|}.indicator (fun z => (z ⬝ᵥ u) ^ (2 * 4)) z := by
    intro z
    set g := z ⬝ᵥ u
    by_cases h : T < (g ^ 2 - 1) ^ 2
    · have hg : Real.sqrt T < g ^ 2 - 1 := by
        have h1 : Real.sqrt T < |g ^ 2 - 1| := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt hT0 h
        rcases le_or_gt 0 (g ^ 2 - 1) with h2 | h2
        · rwa [abs_of_nonneg h2] at h1
        · rw [abs_of_neg h2] at h1; nlinarith [sq_nonneg g]
      have hgc : c < |g| := by
        rw [hc, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg T) (by linarith)
      rw [Set.indicator_of_mem (show z ∈ {z : Fin d → ℝ | T < ((z ⬝ᵥ u) ^ 2 - 1) ^ 2} from h),
        Set.indicator_of_mem (show z ∈ {z : Fin d → ℝ | c < |z ⬝ᵥ u|} from hgc)]
      have h0 : 0 ≤ g ^ 2 - 1 := by linarith [Real.sqrt_nonneg T]
      have h3 : g ^ 2 - 1 ≤ g ^ 2 := by linarith
      have h4 : (g ^ 2 - 1) ^ 4 ≤ (g ^ 2) ^ 4 := pow_le_pow_left₀ h0 h3 4
      calc ((g ^ 2 - 1) ^ 2) ^ 2 = (g ^ 2 - 1) ^ 4 := by ring
        _ ≤ (g ^ 2) ^ 4 := h4
        _ = g ^ (2 * 4) := by ring
    · rw [Set.indicator_of_notMem (show z ∉ {z : Fin d → ℝ | T < ((z ⬝ᵥ u) ^ 2 - 1) ^ 2} from h)]
      exact Set.indicator_nonneg (fun z _ => by rw [pow_mul]; positivity) z
  have hint : Integrable ({z : Fin d → ℝ | c < |z ⬝ᵥ u|}.indicator (fun z => (z ⬝ᵥ u) ^ (2 * 4))) (gam d) := by
    have hi := (memLp_dot_pow u (2 * 4) 1 (by norm_num)).integrable le_rfl
    exact hi.indicator (measurableSet_lt measurable_const
      ((continuous_id.dotProduct continuous_const).abs.measurable))
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => Set.indicator_nonneg (fun z _ => by positivity) z) hint
    (Filter.Eventually.of_forall hdom)
  refine hmono.trans ?_
  have ht := tail_dot u hu1 4 c (by norm_num) hc0
  have h15 : ((4 * 4 - 1 : ℕ)).doubleFactorial = 2027025 := by decide
  rw [h15, hc2] at ht
  calc _ ≤ Real.sqrt ((2027025 : ℕ) : ℝ) * Real.exp (-Real.sqrt T / 4) := ht
    _ = Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4) := by norm_num

end AdversarialBco.Poly.EvSI
