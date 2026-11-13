/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Statement

@[expose] public section

/-!
# Analytic lemmas on Gaussian laws, convexity and compactness

Lemmas that the proofs use: the Lipschitz constant of a function composed with an
affine map; the derivative of the standard Gaussian density and Gaussian integration by parts on `ℝ` and on `ℝ^d`;
Jensen's inequality at the centre of a symmetric law; `∫ x in Ioi 0, x exp (-x²/(2v)) = v` and the mean of `|x|` under
`gaussianReal 0 v`; the derivative of `log det (S + t D)` at `t = 0`; the convexity of a convolution with a nonnegative
kernel; the bounds `‖b‖ ≤ E ‖b + w‖` and `E ‖w‖ ≤ E ‖b + w‖` under a symmetric law; a bound on `s` from
`a s - l max (log s) 0 ≤ C`; a minimiser on a set with a compact sublevel set; the rotation invariance of the law of a
pair of independent standard Gaussian vectors; and the bound `√d` on the mean norm of a standard Gaussian vector.
-/

open MeasureTheory ProbabilityTheory Real Matrix

theorem AdversarialBco.lipschitzWith_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : F → ℝ)
    (L : NNReal) (hG : LipschitzWith L G) (b : F) (S : F →L[ℝ] F) :
    LipschitzWith (L * ‖S‖₊) (fun g => G (b + S g)) := by
  have hS : LipschitzWith ‖S‖₊ S := S.lipschitzWith
  have h_add : LipschitzWith 1 (fun (x : F) => b + x) :=
    (isometry_add_left b).lipschitzWith
  have h_comp : LipschitzWith ‖S‖₊ (fun g => b + S g) := by
    convert LipschitzWith.comp h_add hS using 1
    · simp
    · ext g; simp
  have h_final : LipschitzWith (L * ‖S‖₊) (fun g => G (b + S g)) :=
    LipschitzWith.comp hG h_comp
  simpa using h_final

open Set in
/-- The derivative of the standard Gaussian density. -/
theorem AdversarialBco.hasDerivAt_gaussianPDFReal_0_1 (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(gaussianPDFReal 0 1 x) * x) x := by
  have h_gaussian_eq : gaussianPDFReal 0 1 = fun (t : ℝ) => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
    ext t; simp [gaussianPDFReal]
  rw [h_gaussian_eq]
  -- Now compute derivative of (√(2π))⁻¹ * exp(-t^2/2)
  set c := (Real.sqrt (2 * Real.pi))⁻¹ with hc
  have h_deriv_exp : HasDerivAt (fun (t : ℝ) => Real.exp (-(t ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * (-x)) x := by
    have h_inner : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-x) x := by
      have h_sq : HasDerivAt (fun (t : ℝ) => t ^ 2) (2 * x) x := by
        simpa [pow_two] using hasDerivAt_pow 2 x
      have h_neg_sq : HasDerivAt (fun (t : ℝ) => -(t ^ 2)) (-(2 * x)) x := by
        have := h_sq.neg
        -- this : HasDerivAt (-(fun t => t^2)) (-(2*x)) x
        -- we need : HasDerivAt (fun t => -(t^2)) (-(2*x)) x
        -- Note: -(fun t => t^2) = fun t => -(t^2) by definition
        -- But the types are different: HasDerivAt expects a function ℝ → ℝ
        -- Let's use `apply` with `this` after rewriting
        simpa [Pi.neg_def] using this
      have h_div : HasDerivAt (fun (t : ℝ) => -(t ^ 2) / 2) (-(2 * x) / 2) x :=
        h_neg_sq.div_const 2
      have h_simp : -(2 * x) / 2 = -x := by ring
      simpa [h_simp] using h_div
    simpa using h_inner.exp
  have h_const : HasDerivAt (fun (_ : ℝ) => c) 0 x :=
    hasDerivAt_const _ _
  have h_mul := HasDerivAt.mul h_const h_deriv_exp
  -- h_mul : HasDerivAt ((fun _ => c) * (fun t => exp(...))) (0 * exp(...) + c * (exp(...) * (-x))) x
  -- Simplify both the function and the derivative
  have h_simp_fun : ((fun (_ : ℝ) => c) * fun (t : ℝ) => Real.exp (-(t ^ 2) / 2)) =
      fun (t : ℝ) => c * Real.exp (-(t ^ 2) / 2) := rfl
  have h_simp_deriv : (0 : ℝ) * Real.exp (-(x ^ 2) / 2) + c * (Real.exp (-(x ^ 2) / 2) * (-x)) =
      -(c * (Real.exp (-(x ^ 2) / 2) * x)) := by
    ring
  -- h_mul : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (0 * exp + c * (exp * (-x))) x
  -- Goal: HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-((fun t => c * Real.exp (-t^2/2)) x) * x) x
  -- i.e., HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * Real.exp (-x^2/2) * x)) x
  -- h_mul' : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * (Real.exp (-x^2/2) * x))) x
  -- We need to rewrite the goal's derivative to match h_mul'
  have h_mul' := h_mul
  rw [h_simp_fun] at h_mul'
  rw [h_simp_deriv] at h_mul'
  -- Now h_mul' : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * (Real.exp (-x^2/2) * x))) x
  -- Goal : HasDerivAt (fun t => c * Real.exp (-t^2/2)) (-(c * Real.exp (-x^2/2) * x)) x
  -- These differ by associativity: c * (exp * x) vs (c * exp) * x
  -- We can simpa [mul_assoc] using h_mul'
  simpa [mul_assoc] using h_mul'

open Set in
theorem AdversarialBco.gaussian_ibp_1d (H H' : ℝ → ℝ) (hH : ∀ x, HasDerivAt H (H' x) x)
    (hint1 : Integrable (fun x => x * H x) (gaussianReal 0 1)) (hint2 : Integrable H' (gaussianReal 0 1))
    (hint3 : Integrable H (gaussianReal 0 1)) :
    ∫ x, x * H x ∂(gaussianReal 0 1) = ∫ x, H' x ∂(gaussianReal 0 1) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  set φ := gaussianPDFReal 0 1 with hφ
  have hφ_deriv (x : ℝ) : HasDerivAt φ (-(φ x) * x) x := AdversarialBco.hasDerivAt_gaussianPDFReal_0_1 x
  -- Rewrite integrals using integral_gaussianReal_eq_integral_smul
  have h_int_left : ∫ x, x * H x ∂(gaussianReal 0 1) = ∫ x, φ x • (x * H x) := by
    simpa [hφ] using integral_gaussianReal_eq_integral_smul hv (f := fun x => x * H x)
  have h_int_right : ∫ x, H' x ∂(gaussianReal 0 1) = ∫ x, φ x • H' x := by
    simpa [hφ] using integral_gaussianReal_eq_integral_smul hv (f := fun x => H' x)
  rw [h_int_left, h_int_right]
  -- Convert integrability hypotheses from gaussianReal to volume with density
  rw [gaussianReal_of_var_ne_zero _ hv] at hint1 hint2 hint3
  have h_int1' : Integrable (fun x => φ x • (x * H x)) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint1
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  have h_int2' : Integrable (fun x => φ x • H' x) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint2
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  have h_int3' : Integrable (fun x => φ x • H x) := by
    have := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => gaussianPDF_lt_top)).mp hint3
    simpa [hφ, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)] using this
  -- Apply integration by parts: integral_mul_deriv_eq_deriv_mul_of_integrable
  -- u := H, v := φ, u' := H', v' := fun x => -(φ x) * x
  have h_parts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu := fun x hx => hH x)
    (hv := fun x hx => hφ_deriv x)
    (huv' := ?_)
    (hu'v := ?_)
    (huv := ?_)
  -- h_parts : ∫ x, H x * (-(φ x) * x) = -∫ x, H' x * φ x
  -- We need: ∫ x, φ x • (x * H x) = ∫ x, φ x • H' x
  -- Note: φ x • (x * H x) = x * H x * φ x = -(H x * (-(φ x) * x))
  -- and φ x • H' x = H' x * φ x
  -- So from h_parts: -∫ x, φ x • (x * H x) = -∫ x, φ x • H' x
  -- Cancel minus sign
  have h_eq1 : (fun x => φ x • (x * H x)) = (fun x => -(H x * (-(φ x) * x))) := by
    ext x; simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have h_eq2 : (fun x => φ x • H' x) = (fun x => H' x * φ x) := by
    ext x; simp [smul_eq_mul, mul_comm]
  rw [h_eq1, h_eq2]
  -- Goal: ∫ x, -(H x * (-(φ x) * x)) = ∫ x, H' x * φ x
  rw [integral_neg]
  -- Goal: -∫ x, H x * (-(φ x) * x) = ∫ x, H' x * φ x
  rw [h_parts]
  -- Goal: -(-∫ x, H' x * φ x) = ∫ x, H' x * φ x
  simp
  -- Now provide the integrability conditions
  · -- huv' : Integrable (H * (fun x => -(φ x) * x))
    -- Goal: Integrable (H * (fun x => -(φ x) * x))
    -- which is definitionally Integrable (fun x => H x * (-(φ x) * x))
    -- We have h_int1' : Integrable (fun x => φ x • (x * H x))
    -- Note: H x * (-(φ x) * x) = -(φ x • (x * H x)) by ring
    simpa [Pi.mul_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h_int1'.neg
  · -- hu'v : Integrable (H' * φ)
    -- Goal: Integrable (H' * φ) which is definitionally Integrable (fun x => H' x * φ x)
    -- h_int2' : Integrable (fun x => φ x • H' x) = Integrable (fun x => φ x * H' x)
    -- By commutativity, these are equal
    simpa [Pi.mul_def, smul_eq_mul, mul_comm] using h_int2'
  · -- huv : Integrable (H * φ)
    -- Goal: Integrable (H * φ) which is definitionally Integrable (fun x => H x * φ x)
    -- h_int3' : Integrable (fun x => φ x • H x) = Integrable (fun x => φ x * H x)
    -- By commutativity, these are equal
    simpa [Pi.mul_def, smul_eq_mul, mul_comm] using h_int3'

open MeasureTheory ProbabilityTheory in
theorem AdversarialBco.gaussian_ibp_pi {d : ℕ} (i : Fin d) (H D : (Fin d → ℝ) → ℝ)
    (hH : ∀ w u, HasDerivAt (fun v => H (Function.update w i v)) (D (Function.update w i u)) u)
    (hint1 : Integrable (fun w => w i * H w) (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hint2 : Integrable D (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hint3 : Integrable H (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    ∫ w, w i * H w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      ∫ w, D w ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  -- If d = 0, then i : Fin 0 is impossible
  have h_ne_zero : d ≠ 0 := by
    intro h
    have : Fin 0 := by rw [h] at i; exact i
    exact Fin.elim0 this
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h_ne_zero
  subst hk
  -- Now d = k.succ, i : Fin (k.succ)
  let μ := fun _ : Fin (k.succ) => gaussianReal 0 1
  let γ := gaussianReal 0 1
  let ν := Measure.pi fun j : Fin k => μ (i.succAbove j)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k.succ) => ℝ) i).symm
  -- e : ℝ × ((j : Fin k) → ℝ) ≃ᵐ ((j : Fin (k.succ)) → ℝ)
  have h_meas_preserve : MeasurePreserving e ((γ).prod ν) (Measure.pi μ) := by
    have h := measurePreserving_piFinSuccAbove μ i
    exact h.symm
  have h_map_eq : Measure.map e ((γ).prod ν) = Measure.pi μ := h_meas_preserve.map_eq
  -- Use integral_map_equiv to change variables
  have hL : ∫ w, w i * H w ∂(Measure.pi μ) = ∫ (p : ℝ × ((j : Fin k) → ℝ)), (e p) i * H (e p) ∂((γ).prod ν) := by
    rw [← h_map_eq, integral_map_equiv e]
  have hR : ∫ w, D w ∂(Measure.pi μ) = ∫ (p : ℝ × ((j : Fin k) → ℝ)), D (e p) ∂((γ).prod ν) := by
    rw [← h_map_eq, integral_map_equiv e]
  rw [hL, hR]
  -- Key property: (e p) i = p.1
  have h_e_i (p : ℝ × ((j : Fin k) → ℝ)) : (e p) i = p.1 := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp [Fin.insertNthEquiv_apply]
  -- Rewrite using h_e_i
  have hL' : ∫ (p : ℝ × ((j : Fin k) → ℝ)), (e p) i * H (e p) ∂((γ).prod ν) =
            ∫ (p : ℝ × ((j : Fin k) → ℝ)), p.1 * H (e p) ∂((γ).prod ν) := by
    refine integral_congr_ae ?_
    filter_upwards with p
    rw [h_e_i p]
  rw [hL']
  -- Goal: ∫ p, p.1 * H (e p) ∂(γ.prod ν) = ∫ p, D (e p) ∂(γ.prod ν)
  -- Transport integrability hypotheses through the measure-preserving map
  have hint1' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) ((γ).prod ν) := by
    have h1_map : Integrable (fun w => w i * H w) (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h1_comp := (integrable_map_equiv e (fun w => w i * H w) (μ := (γ).prod ν)).mp h1_map
    have : ((fun w => w i * H w) ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) := by
      ext p; simp [h_e_i p]
    rwa [this] at h1_comp
  have hint2' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) ((γ).prod ν) := by
    have h2_map : Integrable D (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h2_comp := (integrable_map_equiv e D (μ := (γ).prod ν)).mp h2_map
    have : (D ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) := rfl
    rwa [this] at h2_comp
  have hint3' : Integrable (fun (p : ℝ × ((j : Fin k) → ℝ)) => H (e p)) ((γ).prod ν) := by
    have h3_map : Integrable H (Measure.map e ((γ).prod ν)) := by rwa [h_map_eq]
    have h3_comp := (integrable_map_equiv e H (μ := (γ).prod ν)).mp h3_map
    have : (H ∘ e) = (fun (p : ℝ × ((j : Fin k) → ℝ)) => H (e p)) := rfl
    rwa [this] at h3_comp
  -- Now use integral_prod and integral_integral_swap
  rw [integral_prod _ hint1', integral_prod _ hint2']
  simp
  -- Goal: ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), x * H (e (x, w')) ∂ν ∂γ =
  --       ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), D (e (x, w')) ∂ν ∂γ
  -- Now use integral_integral_swap to swap the order of integration
  have h_swap1 : ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), x * H (e (x, w')) ∂ν ∂γ =
                ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), x * H (e (x, w')) ∂γ ∂ν := by
    have h_uncurry : Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => x * H (e (x, w'))) =
                    (fun (p : ℝ × ((j : Fin k) → ℝ)) => p.1 * H (e p)) := by
      ext p; cases p; simp
    have h_int_uncurry : Integrable (Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => x * H (e (x, w')))) ((γ).prod ν) := by
      rwa [h_uncurry]
    rw [integral_integral_swap h_int_uncurry]
  have h_swap2 : ∫ (x : ℝ), ∫ (w' : (j : Fin k) → ℝ), D (e (x, w')) ∂ν ∂γ =
                ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), D (e (x, w')) ∂γ ∂ν := by
    have h_uncurry : Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => D (e (x, w'))) =
                    (fun (p : ℝ × ((j : Fin k) → ℝ)) => D (e p)) := by
      ext p; cases p; simp
    have h_int_uncurry : Integrable (Function.uncurry (fun (x : ℝ) (w' : (j : Fin k) → ℝ) => D (e (x, w')))) ((γ).prod ν) := by
      rwa [h_uncurry]
    rw [integral_integral_swap h_int_uncurry]
  rw [h_swap1, h_swap2]
  -- Goal: ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), x * H (e (x, w')) ∂γ ∂ν =
  --       ∫ (w' : (j : Fin k) → ℝ), ∫ (x : ℝ), D (e (x, w')) ∂γ ∂ν
  -- Now apply integral_congr_ae: it suffices to show the inner integrals are equal for a.e. w'
  refine integral_congr_ae ?_
  -- Get the a.e. properties from Fubini
  have h_ae1 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => x * H (e (x, w'))) γ := by
    have h := hint1'.prod_left_ae
    simpa using h
  have h_ae2 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => D (e (x, w'))) γ := by
    have h := hint2'.prod_left_ae
    simpa using h
  have h_ae3 : ∀ᵐ (w' : (j : Fin k) → ℝ) ∂ν, Integrable (fun (x : ℝ) => H (e (x, w'))) γ := by
    have h := hint3'.prod_left_ae
    simpa using h
  -- Intersect the a.e. sets
  filter_upwards [h_ae1, h_ae2, h_ae3] with w' h1 h2 h3
  -- For a fixed w', define:
  let H_w' := fun (x : ℝ) => H (e (x, w'))
  let D_w' := fun (x : ℝ) => D (e (x, w'))
  -- Need to show: ∫ x, x * H_w'(x) ∂γ = ∫ x, D_w'(x) ∂γ
  -- Apply gaussian_ibp_1d
  have h_deriv (x : ℝ) : HasDerivAt H_w' (D_w' x) x := by
    have h := hH (e (x, w')) x
    -- h : HasDerivAt (fun v => H (Function.update (e (x, w')) i v)) (D (Function.update (e (x, w')) i x)) x
    -- We need to rewrite using the properties of Fin.insertNth
    -- First, note that e = Fin.insertNthEquiv (fun _ => ℝ) i
    -- And Fin.insertNthEquiv_apply gives: e (x, w') = Fin.insertNth i x w'
    -- So we can work with Fin.insertNth directly
    have h_update1 (v : ℝ) : Function.update (e (x, w')) i v = e (v, w') := by
      -- Rewrite e as Fin.insertNth
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      -- Now we need: Function.update (Fin.insertNth i x w') i v = Fin.insertNth i v w'
      -- This is true by the properties of Fin.insertNth
      -- Let's prove it inline
      ext j
      by_cases hji : j = i
      · subst hji; simp [Fin.insertNth_apply_same]
      · have h := Fin.exists_succAbove_eq hji
        obtain ⟨k, hk⟩ := h
        subst hk
        simp [Fin.insertNth_apply_succAbove]
    have h_update2 : Function.update (e (x, w')) i x = e (x, w') := by
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp
    -- Now rewrite h using h_update1 and h_update2
    simpa [h_update1, h_update2, H_w', D_w'] using h
  -- Apply gaussian_ibp_1d
  exact AdversarialBco.gaussian_ibp_1d H_w' D_w' h_deriv h1 h2 h3

open MeasureTheory in
theorem AdversarialBco.jensen_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure F) [IsProbabilityMeasure μ] (hsym : μ.map (fun w => -w) = μ) (G : F → ℝ)
    (hG : ConvexOn ℝ Set.univ G) (b : F) (hint : Integrable (fun w => G (b + w)) μ) :
    G b ≤ ∫ w, G (b + w) ∂μ := by
  have hmeas_neg : AEMeasurable (fun w : F => -w) μ :=
    (continuous_neg.measurable).aemeasurable
  have h_symm_int : ∫ w, G (b - w) ∂μ = ∫ w, G (b + w) ∂μ := by
    calc
      ∫ w, G (b - w) ∂μ = ∫ w, G (b + (-w)) ∂μ := by simp [sub_eq_add_neg]
      _ = ∫ w, G (b + w) ∂(μ.map (fun w => -w)) := by
        rw [integral_map hmeas_neg (by rw [hsym]; exact hint.aestronglyMeasurable)]
      _ = ∫ w, G (b + w) ∂μ := by rw [hsym]
  have h_neg_inv : μ.IsNegInvariant :=
    Measure.IsNegInvariant.mk hsym
  have h_int2 : Integrable (fun w => G (b - w)) μ := by
    have := hint.comp_neg
    simpa [sub_eq_add_neg] using this
  have h_avg_eq : ∫ w, G (b + w) ∂μ = ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ := by
    calc
      ∫ w, G (b + w) ∂μ = (∫ w, G (b + w) ∂μ + ∫ w, G (b + w) ∂μ) / 2 := by ring
      _ = (∫ w, G (b + w) ∂μ + ∫ w, G (b - w) ∂μ) / 2 := by rw [h_symm_int]
      _ = ((∫ w, G (b + w) ∂μ) + (∫ w, G (b - w) ∂μ)) / 2 := rfl
      _ = (∫ w, (G (b + w) + G (b - w)) ∂μ) / 2 := by rw [integral_add hint h_int2]
      _ = ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ := by rw [integral_div]
  have h_pointwise : ∀ w, G b ≤ (G (b + w) + G (b - w)) / 2 := by
    intro w
    have hx : b + w ∈ Set.univ := Set.mem_univ _
    have hy : b - w ∈ Set.univ := Set.mem_univ _
    have hmid : ((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w)) = b := by
      calc
        ((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w))
            = (1/2 : ℝ) • ((b + w) + (b - w)) := by rw [← smul_add]
        _ = (1/2 : ℝ) • (b + b) := by abel
        _ = (1/2 : ℝ) • ((2 : ℝ) • b) := by simp [two_smul]
        _ = b := by simp
    calc
      G b = G (((1/2 : ℝ) • (b + w) + (1/2 : ℝ) • (b - w))) := by rw [hmid]
      _ ≤ ((1/2 : ℝ) • G (b + w) + (1/2 : ℝ) • G (b - w)) := by
        have h := hG.2 hx hy (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
          (by norm_num : (1/2 : ℝ) + (1/2 : ℝ) = 1)
        simpa [add_comm] using h
      _ = (G (b + w) + G (b - w)) / 2 := by ring
  have h_int_avg : Integrable (fun w => (G (b + w) + G (b - w)) / 2) μ := by
    have h_sum : Integrable (fun w => G (b + w) + G (b - w)) μ :=
      Integrable.add hint h_int2
    exact h_sum.div_const 2
  calc
    G b = ∫ w, G b ∂μ := by
      rw [integral_const]
      have h_measure_univ_real : μ.real Set.univ = (1 : ℝ) := by
        rw [Measure.real_def, measure_univ, ENNReal.toReal_one]
      rw [h_measure_univ_real, one_smul]
    _ ≤ ∫ w, (G (b + w) + G (b - w)) / 2 ∂μ :=
      integral_mono (integrable_const _) h_int_avg h_pointwise
    _ = ∫ w, G (b + w) ∂μ := by rw [h_avg_eq]


open Set Filter in
/-- `∫ x in Ioi 0, x * exp (-x^2/(2 v)) = v` for `v > 0`. -/
theorem AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_var (v : ℝ) (hv : 0 < v) :
    ∫ x in Ioi (0 : ℝ), rexp (-x ^ 2 / (2 * v)) * x = v := by
  set F : ℝ → ℝ := fun x => -v * rexp (-x ^ 2 / (2 * v)) with hF
  set f : ℝ → ℝ := fun x => rexp (-x ^ 2 / (2 * v)) * x with hf
  have h_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (f x) x := by
    intro x hx
    dsimp [F, f]
    have h_deriv_inner : HasDerivAt (fun x : ℝ => -x ^ 2 / (2 * v)) (-x / v) x := by
      have h_neg_sq : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := by
        have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        simpa [show (fun x : ℝ => -x ^ 2) = -(fun x : ℝ => x ^ 2) by ext; simp] using HasDerivAt.neg h_sq
      have h_const_inv : HasDerivAt (fun _ : ℝ => (2 * v)⁻¹) 0 x := by
        exact hasDerivAt_const _ _
      have h_mul : HasDerivAt (fun x : ℝ => (-x ^ 2) * (2 * v)⁻¹)
          ((-(2 * x)) * (2 * v)⁻¹ + (-x ^ 2) * 0) x :=
        HasDerivAt.mul h_neg_sq h_const_inv
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_zero, hv.ne.symm] using h_mul
    have h_exp_deriv : HasDerivAt (fun x : ℝ => rexp (-x ^ 2 / (2 * v)))
        (rexp (-x ^ 2 / (2 * v)) * (-x / v)) x := by
      refine (Real.hasDerivAt_exp _).comp x h_deriv_inner
    have h_final : HasDerivAt (fun x : ℝ => -v * rexp (-x ^ 2 / (2 * v)))
        (-v * (rexp (-x ^ 2 / (2 * v)) * (-x / v))) x :=
      HasDerivAt.const_mul (-v) h_exp_deriv
    have h_simp : -v * (rexp (-x ^ 2 / (2 * v)) * (-x / v)) = rexp (-x ^ 2 / (2 * v)) * x := by
      field_simp [hv.ne.symm]
    simpa [h_simp] using h_final
  have h_cont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    dsimp [F]
    refine Continuous.continuousWithinAt ?_
    continuity
  have h_tendsto : Tendsto F atTop (nhds (0 : ℝ)) := by
    dsimp [F]
    have h_sq_tendsto : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : 2 ≠ 0)
    have h_neg_sq_tendsto : Tendsto (fun x : ℝ => -x ^ 2) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h_sq_tendsto
    have hpos : 0 < 2 * v := by nlinarith
    have h_inner : Tendsto (fun x : ℝ => -x ^ 2 / (2 * v)) atTop atBot :=
      h_neg_sq_tendsto.atBot_div_const hpos
    have h_exp : Tendsto (fun x : ℝ => rexp (-x ^ 2 / (2 * v))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_inner
    have h_mul : Tendsto (fun x : ℝ => -v * rexp (-x ^ 2 / (2 * v))) atTop (nhds (-v * 0)) :=
      tendsto_const_nhds.mul h_exp
    simpa [mul_zero] using h_mul
  have h_integrable : IntegrableOn f (Ioi (0 : ℝ)) volume := by
    dsimp [f]
    have hb : 0 < (2 * v)⁻¹ := by
      refine inv_pos.mpr ?_
      nlinarith [hv]
    have hs : -1 < (1 : ℝ) := by norm_num
    have h_int : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(2 * v)⁻¹ * x ^ 2)) (Ioi 0) volume :=
      integrableOn_rpow_mul_exp_neg_mul_sq hb hs
    simpa [rpow_one, div_eq_inv_mul, mul_comm] using h_int
  rw [integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_integrable h_tendsto]
  dsimp [F]
  simp


open Set Filter in
theorem AdversarialBco.integral_abs_gaussianReal (v : NNReal) :
    ∫ x, |x| ∂(gaussianReal 0 v) = Real.sqrt (2 * v / Real.pi) := by
  by_cases hv : (v : ℝ) = 0
  · have hv' : v = 0 := by exact_mod_cast hv
    subst hv'
    simp [gaussianReal_zero_var]
  · have hv_ne_zero : v ≠ 0 := by
      intro h; apply hv; exact_mod_cast h
    have hv_pos : 0 < (v : ℝ) := by
      by_contra! h
      have h_eq : (v : ℝ) = 0 := by linarith
      exact hv h_eq
    rw [integral_gaussianReal_eq_integral_smul hv_ne_zero]
    simp_rw [smul_eq_mul]
    rw [gaussianPDFReal_def 0 v]
    simp only [sub_zero]
    -- ∫ x, ((√(2πv))⁻¹ * rexp(-x²/(2v))) * |x|
    -- Factor out the constant (√(2πv))⁻¹
    have h_factor : (fun x : ℝ => ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * rexp (-x ^ 2 / (2 * (v : ℝ)))) * |x|) =
        (fun x : ℝ => (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|)) := by
      ext x; ring
    rw [h_factor, integral_const_mul]
    -- Now: (√(2πv))⁻¹ * ∫ x, rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|
    -- Use integral_comp_abs with f(x) = x * rexp(-x²/(2v))
    -- Then f(|x|) = |x| * rexp(-|x|²/(2v)) = |x| * rexp(-x²/(2v))
    -- And ∫_Ioi 0 f(x) dx = ∫_Ioi 0 x * rexp(-x²/(2v)) dx = v
    set f : ℝ → ℝ := fun x => rexp (-x ^ 2 / (2 * (v : ℝ))) * x with hf
    have h_abs_eq : (fun x : ℝ => rexp (-x ^ 2 / (2 * (v : ℝ))) * |x|) = fun x => f |x| := by
      ext x
      dsimp [f]
      simp [sq_abs]
    rw [h_abs_eq, integral_comp_abs]
    -- Now: (√(2πv))⁻¹ * (2 * ∫ x in Ioi 0, f x)
    rw [hf]
    -- (√(2πv))⁻¹ * (2 * ∫ x in Ioi 0, rexp (-x ^ 2 / (2 * (v : ℝ))) * x)
    rw [AdversarialBco.integral_Ioi_mul_exp_neg_sq_div_two_var (v : ℝ) hv_pos]
    -- Now: (√(2πv))⁻¹ * (2 * v) = √(2v/π)
    -- Square both sides
    have h_eq_sq : ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ))) ^ 2 = (Real.sqrt (2 * (v : ℝ) / π)) ^ 2 := by
      calc
        ((Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ))) ^ 2
            = (2 * (v : ℝ)) ^ 2 / ((Real.sqrt (2 * π * (v : ℝ))) ^ 2) := by ring
        _ = (4 * (v : ℝ) ^ 2) / (2 * π * (v : ℝ)) := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * π * (v : ℝ))]
          ring
        _ = 2 * (v : ℝ) / π := by
          field_simp [hv_pos.ne.symm]
          ring
        _ = (Real.sqrt (2 * (v : ℝ) / π)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (v : ℝ) / π)]
    have h_nonneg_left : 0 ≤ (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ)) := by
      positivity
    have h_nonneg_right : 0 ≤ Real.sqrt (2 * (v : ℝ) / π) := by positivity
    -- From equality of squares and nonnegativity, we get equality
    have h_eq : (Real.sqrt (2 * π * (v : ℝ)))⁻¹ * (2 * (v : ℝ)) = Real.sqrt (2 * (v : ℝ) / π) := by
      nlinarith
    rw [h_eq]

open Matrix Polynomial in
theorem AdversarialBco.hasDerivAt_log_det {n : Type*} [Fintype n] [DecidableEq n] (S D : Matrix n n ℝ)
    (hS : 0 < S.det) : HasDerivAt (fun t : ℝ => Real.log (S + t • D).det) (S⁻¹ * D).trace 0 := by
  set M := S⁻¹ * D with hM
  have hS_det_ne_zero : S.det ≠ 0 := by linarith
  have hS_det_unit : IsUnit S.det := IsUnit.mk0 _ hS_det_ne_zero
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det_unit
  -- S + t • D = S * (1 + t • M)
  have h_eq : ∀ t : ℝ, S + t • D = S * (1 + t • M) := by
    intro t
    calc
      S + t • D = S + t • (S * M) := by
        have hD : D = S * M := by
          calc
            D = 1 * D := by simp
            _ = (S * S⁻¹) * D := by rw [hS_mul_inv]
            _ = S * (S⁻¹ * D) := by rw [Matrix.mul_assoc]
            _ = S * M := by rw [hM]
        rw [hD]
      _ = S * 1 + S * (t • M) := by simp
      _ = S * (1 + t • M) := by rw [Matrix.mul_add, Matrix.mul_one]
  -- det(S + t • D) = det S * det(1 + t • M)
  have h_det_eq : ∀ t : ℝ, (S + t • D).det = S.det * (1 + t • M).det := by
    intro t
    rw [h_eq t, Matrix.det_mul]
  -- Key lemma: derivative of det(1 + t • M) at 0 is trace M
  have h_deriv_det_one_add : HasDerivAt (fun t : ℝ => (1 + t • M).det) (M.trace) 0 := by
    -- Use Matrix.det_one_add_smul to express det(1 + t • M) as a polynomial
    let p' := ((1 : Matrix n n (Polynomial ℝ)) + (Polynomial.X : Polynomial ℝ) • (M.map (fun r => (Polynomial.C r : Polynomial ℝ)))).det.divX.divX
    have h_formula : (fun t : ℝ => (1 + t • M).det) = (fun t => 1 + M.trace * t + (Polynomial.eval t p') * t ^ 2) := by
      ext t
      -- Matrix.det_one_add_smul gives the formula
      have h := Matrix.det_one_add_smul t M
      -- h : (1 + t • M).det = 1 + M.trace * t + Polynomial.eval t (...) * t ^ 2
      simpa [p'] using h
    rw [h_formula]
    -- Now compute derivative of 1 + M.trace * t + (eval t p') * t^2 at 0
    have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := by
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    have h_linear : HasDerivAt (fun t : ℝ => M.trace * t) (M.trace) 0 := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
      simpa [mul_comm] using HasDerivAt.const_mul (M.trace) h_id
    have h_sq : HasDerivAt (fun t : ℝ => (Polynomial.eval t p') * t ^ 2) 0 0 := by
      have hQ : HasDerivAt (fun t : ℝ => Polynomial.eval t p') (Polynomial.eval (0 : ℝ) (Polynomial.derivative p')) 0 := by
        simpa using Polynomial.hasDerivAt p' (0 : ℝ)
      have h_sq' : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have h_mul := HasDerivAt.mul hQ h_sq'
      -- h_mul : HasDerivAt ((fun t => Q(t)) * (fun t => t^2)) (Q'(0)*0^2 + Q(0)*0) 0
      -- The derivative simplifies to 0
      have h_mul' : HasDerivAt ((fun t : ℝ => Polynomial.eval t p') * fun t : ℝ => t ^ 2) 0 0 := by
        simpa [add_zero, mul_zero] using h_mul
      -- Now the function is definitionally equal to (fun t => eval t p' * t ^ 2)
      exact h_mul'
    -- Combine: derivative of 1 + M.trace * t + (eval t p') * t^2 is 0 + M.trace + 0 = M.trace
    have h_sum := (h_const.add (h_linear.add h_sq))
    -- h_sum : HasDerivAt ((fun x => 1) + ((fun t => M.trace * t) + fun t => eval t p' * t ^ 2)) (0 + (M.trace + 0)) 0
    -- The derivative simplifies to M.trace
    have h_sum' : HasDerivAt ((fun x : ℝ => (1 : ℝ)) + ((fun t : ℝ => M.trace * t) + fun t : ℝ => (Polynomial.eval t p') * t ^ 2)) (M.trace) 0 := by
      simpa [add_zero] using h_sum
    -- The function is definitionally equal to (fun t => 1 + M.trace * t + eval t p' * t ^ 2)
    -- but we need to use funext to adjust
    have h_goal : (fun t : ℝ => 1 + M.trace * t + (Polynomial.eval t p') * t ^ 2) =
      ((fun x : ℝ => (1 : ℝ)) + ((fun t : ℝ => M.trace * t) + fun t : ℝ => (Polynomial.eval t p') * t ^ 2)) := by
      funext t; simp [mul_comm, add_comm, add_left_comm, add_assoc]
    rw [h_goal]
    exact h_sum'
  -- Now we have HasDerivAt (fun t => det(1 + t • M)) (M.trace) 0
  -- Multiply by det S
  have h_deriv_detS_mul : HasDerivAt (fun t : ℝ => S.det * (1 + t • M).det) (S.det * M.trace) 0 := by
    simpa [mul_comm] using HasDerivAt.const_mul S.det h_deriv_det_one_add
  -- Now apply log
  have h_log_input : (fun t : ℝ => Real.log ((S + t • D).det)) = (fun t => Real.log (S.det * (1 + t • M).det)) := by
    ext t
    rw [h_det_eq t]
  rw [h_log_input]
  have h_log_arg_ne_zero : S.det * (1 + (0 : ℝ) • M).det ≠ 0 := by
    simp [hS_det_ne_zero]
  have h_log_deriv := HasDerivAt.log h_deriv_detS_mul h_log_arg_ne_zero
  -- h_log_deriv : HasDerivAt (fun t => Real.log (S.det * (1 + t • M).det)) ((S.det * M.trace) / (S.det * (1 + 0 • M).det)) 0
  -- Simplify: (1 + 0 • M).det = 1, so the derivative is (S.det * M.trace) / S.det = M.trace
  have h_log_deriv_simp : HasDerivAt (fun t : ℝ => Real.log (S.det * (1 + t • M).det)) (M.trace) 0 := by
    -- rewrite the derivative in h_log_deriv
    have h_deriv_simp : (S.det * M.trace) / (S.det * (1 + (0 : ℝ) • M).det) = M.trace := by
      simp [hS_det_ne_zero]
    -- Now apply this to h_log_deriv
    convert h_log_deriv using 1
    exact h_deriv_simp.symm
  -- Now rewrite back using h_log_input
  simpa [h_log_input] using h_log_deriv_simp


open MeasureTheory in
theorem AdversarialBco.convexOn_convolution {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (hint : ∀ x, Integrable (fun y => F (x - y) * φ y)) :
    ConvexOn ℝ Set.univ (fun x => ∫ y, F (x - y) * φ y) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp at hx hy
  have hkey : ∀ z, (a • x + b • y) - z = a • (x - z) + b • (y - z) := by
    intro z
    calc
      (a • x + b • y) - z = (a • x + b • y) - (a + b) • z := by simp [hab]
      _ = (a • x + b • y) - (a • z + b • z) := by simp [add_smul]
      _ = (a • x - a • z) + (b • y - b • z) := by abel
      _ = a • (x - z) + b • (y - z) := by simp [smul_sub]
  have hpointwise : ∀ z, F ((a • x + b • y) - z) * φ z ≤ (a • F (x - z) + b • F (y - z)) * φ z := by
    intro z
    rw [hkey z]
    have hF_convex := hF.2 (Set.mem_univ (x - z)) (Set.mem_univ (y - z)) ha hb hab
    have h_nonneg := hφ z
    have h_mul := mul_le_mul_of_nonneg_right hF_convex h_nonneg
    exact h_mul
  have hleft_int : Integrable (fun z => F ((a • x + b • y) - z) * φ z) volume := hint (a • x + b • y)
  have hright_int : Integrable (fun z => (a • F (x - z) + b • F (y - z)) * φ z) volume := by
    have h1 : Integrable (fun z => F (x - z) * φ z) volume := hint x
    have h2 : Integrable (fun z => F (y - z) * φ z) volume := hint y
    have h1' : Integrable (fun z => a • (F (x - z) * φ z)) volume := (h1.smul a)
    have h2' : Integrable (fun z => b • (F (y - z) * φ z)) volume := (h2.smul b)
    have hsum : Integrable (fun z => a • (F (x - z) * φ z) + b • (F (y - z) * φ z)) volume :=
      h1'.add h2'
    simpa [smul_eq_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hright_int' : Integrable (fun z => a • (F (x - z) * φ z)) volume := (hint x).smul a
  have hright_int'' : Integrable (fun z => b • (F (y - z) * φ z)) volume := (hint y).smul b
  calc
    (∫ z, F ((a • x + b • y) - z) * φ z) ≤ (∫ z, (a • F (x - z) + b • F (y - z)) * φ z) :=
      integral_mono hleft_int hright_int hpointwise
    _ = (∫ z, a • (F (x - z) * φ z) + b • (F (y - z) * φ z)) := by
      refine integral_congr_ae ?_
      filter_upwards with z
      ring
    _ = (∫ z, a • (F (x - z) * φ z)) + (∫ z, b • (F (y - z) * φ z)) :=
      integral_add hright_int' hright_int''
    _ = a • (∫ z, F (x - z) * φ z) + b • (∫ z, F (y - z) * φ z) := by
      rw [integral_smul, integral_smul]

open MeasureTheory in
theorem AdversarialBco.norm_add_symm_ge {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun w => -w) = μ) (hint : Integrable (fun w => ‖w‖) μ) (b : EuclideanSpace ℝ (Fin d)) :
    ‖b‖ ≤ ∫ w, ‖b + w‖ ∂μ ∧ ∫ w, ‖w‖ ∂μ ≤ ∫ w, ‖b + w‖ ∂μ := by
  have hae_meas_add : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b + w‖) μ :=
    ((continuous_const.add continuous_id).norm).aestronglyMeasurable
  have hae_meas_sub : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b - w‖) μ :=
    ((continuous_const.sub continuous_id).norm).aestronglyMeasurable
  have hmeas_neg : AEMeasurable (fun w : EuclideanSpace ℝ (Fin d) => -w) μ :=
    (measurable_neg.comp measurable_id).aemeasurable
  have hae_meas_add_mapped : AEStronglyMeasurable (fun w : EuclideanSpace ℝ (Fin d) => ‖b + w‖)
      (μ.map (fun w => -w)) :=
    ((continuous_const.add continuous_id).norm).aestronglyMeasurable
  have hint_add : Integrable (fun w => ‖b + w‖) μ := by
    have h_bound : ∀ᵐ w ∂μ, ‖(fun w => ‖b + w‖) w‖ ≤ (fun w => ‖b‖ + ‖w‖) w := by
      filter_upwards [] with w
      simp [norm_add_le]
    have h_int : Integrable (fun w => ‖b‖ + ‖w‖) μ :=
      (integrable_const (‖b‖)).add hint
    exact h_int.mono' hae_meas_add h_bound
  have h_symm_int : ∫ w, ‖b - w‖ ∂μ = ∫ w, ‖b + w‖ ∂μ := by
    calc
      ∫ w, ‖b - w‖ ∂μ = ∫ w, ‖b + (-w)‖ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with w
        simp [sub_eq_add_neg]
      _ = ∫ w, ‖b + w‖ ∂(μ.map (fun w => -w)) := by
        rw [integral_map hmeas_neg hae_meas_add_mapped]
      _ = ∫ w, ‖b + w‖ ∂μ := by rw [hsym]
  have h_int_neg : Integrable (fun w => ‖b - w‖) μ := by
    have h_bound : ∀ᵐ w ∂μ, ‖(fun w => ‖b - w‖) w‖ ≤ (fun w => ‖b‖ + ‖w‖) w := by
      filter_upwards [] with w
      simp [norm_sub_le]
    have h_int : Integrable (fun w => ‖b‖ + ‖w‖) μ :=
      (integrable_const (‖b‖)).add hint
    exact h_int.mono' hae_meas_sub h_bound
  have h_sum_eq : ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ = 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ = (∫ w, ‖b + w‖ ∂μ) + (∫ w, ‖b - w‖ ∂μ) :=
        integral_add hint_add h_int_neg
      _ = (∫ w, ‖b + w‖ ∂μ) + (∫ w, ‖b + w‖ ∂μ) := by rw [h_symm_int]
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by ring
  have h_pointwise_b : ∀ w, 2 * ‖b‖ ≤ ‖b + w‖ + ‖b - w‖ := by
    intro w
    calc
      2 * ‖b‖ = ‖(2 : ℝ) • b‖ := by
        simp [norm_smul]
      _ = ‖(b + w) + (b - w)‖ := by
        have h : (2 : ℝ) • b = (b + w) + (b - w) := by
          simp [two_smul, add_left_comm, add_assoc, sub_eq_add_neg]
        rw [h]
      _ ≤ ‖b + w‖ + ‖b - w‖ := norm_add_le _ _
  have h_pointwise_w : ∀ w, 2 * ‖w‖ ≤ ‖b + w‖ + ‖b - w‖ := by
    intro w
    calc
      2 * ‖w‖ = ‖(2 : ℝ) • w‖ := by
        simp [norm_smul]
      _ = ‖(b + w) - (b - w)‖ := by
        have h : (2 : ℝ) • w = (b + w) - (b - w) := by
          simp [two_smul, add_left_comm, add_assoc, sub_eq_add_neg]
        rw [h]
      _ ≤ ‖b + w‖ + ‖b - w‖ := norm_sub_le _ _
  have h_int_b : 2 * ‖b‖ ≤ 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      2 * ‖b‖ = ∫ w, (2 * ‖b‖) ∂μ := by simp [integral_const]
      _ ≤ ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ :=
        integral_mono (integrable_const _) (hint_add.add h_int_neg) h_pointwise_b
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by rw [h_sum_eq]
  have h_int_w : 2 * (∫ w, ‖w‖ ∂μ) ≤ 2 * ∫ w, ‖b + w‖ ∂μ := by
    calc
      2 * (∫ w, ‖w‖ ∂μ) = ∫ w, (2 * ‖w‖) ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ w, (‖b + w‖ + ‖b - w‖) ∂μ :=
        integral_mono (hint.const_mul 2) (hint_add.add h_int_neg) h_pointwise_w
      _ = 2 * ∫ w, ‖b + w‖ ∂μ := by rw [h_sum_eq]
  constructor
  · linarith
  · linarith

theorem AdversarialBco.bounded_of_linear_le_log (a l C : ℝ) (ha : 0 < a) (hl : 0 ≤ l) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → a * s - l * max (Real.log s) 0 ≤ C → s ≤ M := by
  set K := max 1 (2 * l / a) with hKdef
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < 1 := by norm_num
    have hKge1 : 1 ≤ K := le_max_left _ _
    linarith
  have hK_one : (1 : ℝ) ≤ K := le_max_left _ _
  have hK_2l_div_a : 2 * l / a ≤ K := le_max_right _ _
  have h_two_l_le_aK : 2 * l ≤ a * K := by
    calc
      2 * l = (2 * l / a) * a := by field_simp [ha.ne']
      _ ≤ K * a := by nlinarith
      _ = a * K := by ring
  have h_log_bound : ∀ s : ℝ, 0 < s → Real.log s ≤ Real.log K + s / K := by
    intro s hs
    have hsK : 0 < s / K := div_pos hs hKpos
    have hlog_div : Real.log (s / K) ≤ (s / K) - 1 := Real.log_le_sub_one_of_pos hsK
    calc
      Real.log s = Real.log (K * (s / K)) := by field_simp [hKpos.ne']
      _ = Real.log K + Real.log (s / K) := by rw [Real.log_mul hKpos.ne' hsK.ne']
      _ ≤ Real.log K + ((s / K) - 1) := by nlinarith
      _ = Real.log K + s / K - 1 := by ring
      _ ≤ Real.log K + s / K := by nlinarith
  have h_ineq : ∀ s : ℝ, 0 ≤ s → l * s / K ≤ a * s / 2 := by
    intro s hs
    have h_two_l_s_le_a_K_s : 2 * l * s ≤ a * K * s := by
      nlinarith
    have h_nonneg_2K : 0 ≤ 2 * K := by nlinarith
    calc
      l * s / K = (2 * l * s) / (2 * K) := by ring
      _ ≤ (a * K * s) / (2 * K) := div_le_div_of_nonneg_right h_two_l_s_le_a_K_s h_nonneg_2K
      _ = a * s / 2 := by field_simp [hKpos.ne']
  set M := 2 * (|C| + l * |Real.log K|) / a with hMdef
  have hM_nonneg : 0 ≤ M := by
    have hnum : 0 ≤ 2 * (|C| + l * |Real.log K|) := by
      have h1 : 0 ≤ |C| := abs_nonneg _
      have h2 : 0 ≤ |Real.log K| := abs_nonneg _
      nlinarith
    have ha' : 0 ≤ a := by linarith
    exact div_nonneg hnum ha'
  refine ⟨M, λ s hs hle => ?_⟩
  by_cases hs0 : s = 0
  · rw [hs0]
    exact hM_nonneg
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hlog : Real.log s ≤ 0
    · -- max (Real.log s) 0 = 0
      have hmax : max (Real.log s) 0 = 0 := max_eq_right hlog
      rw [hmax] at hle
      have hle' : a * s ≤ C := by linarith
      have hs_le_C_div_a : s ≤ C / a := by
        calc
          s = (a * s) / a := by field_simp [ha.ne']
          _ ≤ C / a := div_le_div_of_nonneg_right hle' (by linarith)
      have hC_le_absC : C ≤ |C| := by
        by_cases hC : 0 ≤ C
        · rw [abs_of_nonneg hC]
        · rw [abs_of_nonpos (by linarith)]
          linarith
      have h_div_le_M : C / a ≤ M := by
        calc
          C / a ≤ |C| / a := div_le_div_of_nonneg_right hC_le_absC (by linarith)
          _ ≤ 2 * (|C| + l * |Real.log K|) / a := by
            refine div_le_div_of_nonneg_right ?_ (by linarith)
            nlinarith [abs_nonneg (Real.log K), hl]
          _ = M := by rw [hMdef]
      linarith
    · -- Real.log s > 0, so max (Real.log s) 0 = Real.log s
      have hmax : max (Real.log s) 0 = Real.log s := max_eq_left (by linarith)
      rw [hmax] at hle
      have hlogK_nonneg : 0 ≤ Real.log K := Real.log_nonneg hK_one
      have h_logK_abs : Real.log K = |Real.log K| := by
        rw [abs_of_nonneg hlogK_nonneg]
      have h_ineq' : l * Real.log s ≤ l * Real.log K + a * s / 2 := by
        calc
          l * Real.log s ≤ l * (Real.log K + s / K) := by
            nlinarith [h_log_bound s hs_pos]
          _ = l * Real.log K + l * s / K := by ring
          _ ≤ l * Real.log K + a * s / 2 := by
            nlinarith [h_ineq s hs]
      have h_key : a * s / 2 ≤ C + l * Real.log K := by
        linarith
      have hC_plus_logK_le : C + l * Real.log K ≤ |C| + l * |Real.log K| := by
        have hC_le_absC : C ≤ |C| := by
          by_cases hC : 0 ≤ C
          · rw [abs_of_nonneg hC]
          · rw [abs_of_nonpos (by linarith)]
            linarith
        nlinarith
      have hpos_2diva : 0 ≤ 2 / a := div_nonneg (by norm_num) (by linarith)
      have h_mul1 : (a * s / 2) * (2 / a) ≤ (C + l * Real.log K) * (2 / a) :=
        mul_le_mul_of_nonneg_right h_key hpos_2diva
      have h_mul2 : (C + l * Real.log K) * (2 / a) ≤ (|C| + l * |Real.log K|) * (2 / a) :=
        mul_le_mul_of_nonneg_right hC_plus_logK_le hpos_2diva
      calc
        s = (a * s / 2) * (2 / a) := by field_simp [ha.ne']
        _ ≤ (C + l * Real.log K) * (2 / a) := h_mul1
        _ ≤ (|C| + l * |Real.log K|) * (2 / a) := h_mul2
        _ = 2 * (|C| + l * |Real.log K|) / a := by ring
        _ = M := by rw [hMdef]

theorem AdversarialBco.exists_min_of_compact_sublevel {X : Type*} [TopologicalSpace X] (U : Set X) (f : X → ℝ)
    (hf : ContinuousOn f U) (x0 : X) (hx0 : x0 ∈ U) (hK : IsCompact {x | x ∈ U ∧ f x ≤ f x0}) :
    ∃ x ∈ U, ∀ y ∈ U, f x ≤ f y := by
  set K := {x | x ∈ U ∧ f x ≤ f x0} with hKdef
  have hx0K : x0 ∈ K := by
    dsimp [K]
    exact ⟨hx0, le_refl _⟩
  have hK_nonempty : K.Nonempty := ⟨x0, hx0K⟩
  have hK_sub_U : K ⊆ U := by
    intro x hx
    rcases hx with ⟨hxU, _⟩
    exact hxU
  have hfK : ContinuousOn f K :=
    hf.mono hK_sub_U
  rcases IsCompact.exists_isMinOn hK hK_nonempty hfK with ⟨x, hxK, hx_min⟩
  refine ⟨x, hxK.1, ?_⟩
  intro y hy
  by_cases h : f y ≤ f x0
  · have hyK : y ∈ K := ⟨hy, h⟩
    exact hx_min hyK
  · have hfx : f x ≤ f x0 := hxK.2
    linarith


/-- The rotation of a pair of independent standard Gaussian vectors by an angle `θ` preserves their law. -/
theorem AdversarialBco.stdGaussian_prod_rotation (d : ℕ) (θ : ℝ) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          (Real.cos θ • p.1 - Real.sin θ • p.2, Real.sin θ • p.1 + Real.cos θ • p.2)) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set E := EuclideanSpace ℝ (Fin d)
  have hrot : (fun p : E × E => (Real.cos θ • p.1 - Real.sin θ • p.2, Real.sin θ • p.1 + Real.cos θ • p.2)) =
      (ContinuousLinearMap.rotation (-θ) : E × E → E × E) := by
    refine funext fun p => ?_
    simp [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]
  rw [hrot]
  have h_mean_zero : ∀ L : StrongDual ℝ E, (stdGaussian E)[L] = 0 := by
    intro L; simp [ProbabilityTheory.integral_strongDual_stdGaussian]
  exact ProbabilityTheory.IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero h_mean_zero (-θ)

open scoped PiLp in
/-- The mean norm of a standard Gaussian vector of `ℝ^d` is at most `√d`. -/
theorem AdversarialBco.integral_norm_stdGaussian_le (d : ℕ) :
    ∫ w, ‖w‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ √(d : ℝ) := by
  -- Jensen inequality with x^2 on [0, ∞)
  have h_convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ 2) := convexOn_pow 2
  have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Ici (0 : ℝ)) := continuousOn_pow 2
  have h_closed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have h_nonneg : ∀ᵐ (w : EuclideanSpace ℝ (Fin d)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), ‖w‖ ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with w
    exact norm_nonneg _
  have h_int_norm : Integrable (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm
    exact h_mem.integrable (by norm_num : 1 ≤ (2 : ENNReal))
  have h_int_norm_sq : Integrable (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm
    exact h_mem.integrable_sq
  have h_jensen := ConvexOn.map_integral_le h_convex h_cont h_closed h_nonneg h_int_norm h_int_norm_sq
  -- h_jensen : (∫ w, ‖w‖) ^ 2 ≤ ∫ w, ‖w‖ ^ 2
  have h_norm_sq_int : ∫ (w : EuclideanSpace ℝ (Fin d)), ‖w‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) := by
    calc
      ∫ (w : EuclideanSpace ℝ (Fin d)), ‖w‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
          ∫ (w : EuclideanSpace ℝ (Fin d)), ∑ i ∈ Finset.univ, ‖w.ofLp i‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_congr_ae ?_
        filter_upwards with w
        simp [EuclideanSpace.norm_sq_eq]
      _ = ∑ i ∈ Finset.univ, ∫ (w : EuclideanSpace ℝ (Fin d)), ‖w.ofLp i‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_finsetSum]
        intro i hi
        have h_mem : MemLp (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm
        have h_int_sq : Integrable (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          h_mem.integrable_sq
        have h_ae_meas : AEStronglyMeasurable (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w.ofLp i‖ ^ 2)
            (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          have h_cont : Continuous (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w.ofLp i‖) := by
            have h_proj : Continuous (fun (w : EuclideanSpace ℝ (Fin d)) => w.ofLp i) := by
              simpa [EuclideanSpace] using PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
            exact Continuous.comp continuous_norm h_proj
          have h_ae : AEStronglyMeasurable (fun (w : EuclideanSpace ℝ (Fin d)) => ‖w.ofLp i‖)
              (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
            h_cont.aestronglyMeasurable (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
          exact h_ae.pow 2
        have h_bound : ∀ᵐ (w : EuclideanSpace ℝ (Fin d)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))),
            ‖(fun (w : EuclideanSpace ℝ (Fin d)) => ‖w.ofLp i‖ ^ 2) w‖ ≤
            ‖(fun (w : EuclideanSpace ℝ (Fin d)) => ‖w‖ ^ 2) w‖ := by
          filter_upwards with w
          have h := PiLp.norm_apply_le (p := 2) (x := w) (i := i)
          have h_nonneg_ofLp : 0 ≤ ‖w.ofLp i‖ := norm_nonneg _
          have h_nonneg_w : 0 ≤ ‖w‖ := norm_nonneg _
          have h_sq : ‖w.ofLp i‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith
          simpa using h_sq
        exact h_int_sq.mono h_ae_meas h_bound
      _ = ∑ i ∈ Finset.univ, 1 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have h_int_coord_sq : ∫ (w : EuclideanSpace ℝ (Fin d)), ((EuclideanSpace.proj (𝕜 := ℝ) i) w) ^ 2
            ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 1 := by
          have h_int : (stdGaussian (EuclideanSpace ℝ (Fin d)))[(EuclideanSpace.proj (𝕜 := ℝ) i)] = 0 :=
            integral_strongDual_stdGaussian (EuclideanSpace.proj (𝕜 := ℝ) i)
          have h_var : Var[(EuclideanSpace.proj (𝕜 := ℝ) i); stdGaussian (EuclideanSpace ℝ (Fin d))] =
              ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ^ 2 :=
            variance_dual_stdGaussian (EuclideanSpace.proj (𝕜 := ℝ) i)
          have h_norm : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ = 1 := by
            apply le_antisymm
            · rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : 0 ≤ (1 : ℝ))]
              intro x
              have h := PiLp.norm_apply_le (p := 2) (x := x) (i := i)
              simpa [EuclideanSpace.coe_proj] using h
            · have h_single : (EuclideanSpace.proj (𝕜 := ℝ) i) (EuclideanSpace.single i (1 : ℝ)) = (1 : ℝ) := by
                simp
              have h_norm_single : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
                simpa using PiLp.norm_single (p := 2) (i := i) (b := (1 : ℝ))
              have h_le := ContinuousLinearMap.le_opNorm (EuclideanSpace.proj (𝕜 := ℝ) i)
                (EuclideanSpace.single i (1 : ℝ))
              rw [h_single, h_norm_single, mul_one, norm_one] at h_le
              exact h_le
          have h_meas : AEMeasurable (EuclideanSpace.proj (𝕜 := ℝ) i) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
            (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.aemeasurable
          have h_var_eq : Var[(EuclideanSpace.proj (𝕜 := ℝ) i); stdGaussian (EuclideanSpace ℝ (Fin d))] =
              ∫ (w : EuclideanSpace ℝ (Fin d)), ((EuclideanSpace.proj (𝕜 := ℝ) i) w) ^ 2
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
            rw [variance_of_integral_eq_zero h_meas h_int]
          rw [← h_var_eq, h_var, h_norm]
          norm_num
        simpa [EuclideanSpace.coe_proj] using h_int_coord_sq
      _ = (d : ℝ) := by simp
  -- Now h_jensen gives (∫ ‖w‖)^2 ≤ ∫ ‖w‖^2 = d
  -- So (∫ ‖w‖)^2 ≤ d, and taking square roots gives ∫ ‖w‖ ≤ √d
  have h_sq_nonneg : 0 ≤ ∫ (w : EuclideanSpace ℝ (Fin d)), ‖w‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integral_nonneg (fun w => norm_nonneg _)
  have h_d_nonneg : 0 ≤ (d : ℝ) := by exact Nat.cast_nonneg _
  rw [h_norm_sq_int] at h_jensen
  -- h_jensen : (∫ w, ‖w‖) ^ 2 ≤ (d : ℝ)
  -- Using: a ≤ √b ↔ a^2 ≤ b when a ≥ 0, b ≥ 0
  exact ((Real.le_sqrt h_sq_nonneg h_d_nonneg).2 h_jensen)
