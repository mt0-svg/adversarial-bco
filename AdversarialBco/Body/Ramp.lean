/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# One-variable facts on the ramp and the tail parameter

Derivatives and bounds of `χ`, `kr`, `kr'`; the tail parameter `Tfun`; the `cosh`
moment of the standard Gaussian of `ℝ`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal


theorem AdversarialBco.Body.hasDerivAt_chi (t : ℝ) : HasDerivAt AdversarialBco.Body.chi (AdversarialBco.Body.chi' t) t := by
  have hpos : 1 + t ^ 2 ≠ 0 := by nlinarith
  have hpos' : 0 < 1 + t ^ 2 := by nlinarith
  have h_sqrt_deriv : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) (t / Real.sqrt (1 + t ^ 2)) t := by
    have h_inner : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
      have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const _ _
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      convert HasDerivAt.add h1 h2 using 1
      simp
    have h_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (1 + t ^ 2))) (1 + t ^ 2) :=
      Real.hasDerivAt_sqrt hpos
    have h_comp := HasDerivAt.comp t h_sqrt h_inner
    convert h_comp using 1
    · ext x; simp
    · ring
  have h_denom_deriv : HasDerivAt (fun x : ℝ => 4 * Real.sqrt (1 + x ^ 2)) (4 * (t / Real.sqrt (1 + t ^ 2))) t := by
    exact HasDerivAt.const_mul 4 h_sqrt_deriv
  have h_denom_ne_zero : (4 * Real.sqrt (1 + t ^ 2)) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr hpos']
  have h_inv_deriv : HasDerivAt (fun x : ℝ => (4 * Real.sqrt (1 + x ^ 2))⁻¹)
      (-(4 * (t / Real.sqrt (1 + t ^ 2))) / ((4 * Real.sqrt (1 + t ^ 2)) ^ 2)) t :=
    HasDerivAt.inv h_denom_deriv h_denom_ne_zero
  have h_chi_eq : AdversarialBco.Body.chi = fun x : ℝ => (4 * Real.sqrt (1 + x ^ 2))⁻¹ := by
    ext x
    simp [AdversarialBco.Body.chi, div_eq_inv_mul]
  rw [h_chi_eq]
  have h_deriv_eq : -(4 * (t / Real.sqrt (1 + t ^ 2))) / ((4 * Real.sqrt (1 + t ^ 2)) ^ 2) =
      AdversarialBco.Body.chi' t := by
    dsimp [AdversarialBco.Body.chi']
    field_simp
    rw [Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 from by nlinarith)]
  simpa [h_deriv_eq] using h_inv_deriv


theorem AdversarialBco.Body.chi_bounds (t : ℝ) :
    1 / (4 * (1 + |t|)) ≤ AdversarialBco.Body.chi t ∧ AdversarialBco.Body.chi t ≤ 1 / 4 ∧
      |AdversarialBco.Body.chi' t| ≤ 1 / 4 := by
  set s := Real.sqrt (1 + t ^ 2) with hs
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    have : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact Real.sqrt_pos.mpr this
  have hs_sq : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg t] : 0 ≤ 1 + t ^ 2)
  -- s ≥ 1
  have hs_ge_one : 1 ≤ s := by
    have : 1 ^ 2 ≤ s ^ 2 := by
      rw [hs_sq]
      nlinarith [sq_nonneg t]
    nlinarith
  -- s ≤ 1 + |t|
  have hs_le_one_plus_abs : s ≤ 1 + |t| := by
    have h_sq : s ^ 2 ≤ (1 + |t|) ^ 2 := by
      rw [hs_sq]
      calc
        1 + t ^ 2 = 1 + |t| ^ 2 := by simp [sq_abs]
        _ ≤ 1 + 2 * |t| + |t| ^ 2 := by nlinarith [abs_nonneg t]
        _ = (1 + |t|) ^ 2 := by ring
    have h_nonneg : 0 ≤ 1 + |t| := by nlinarith [abs_nonneg t]
    nlinarith
  -- |t| ≤ 1 + t^2
  have habs_le_one_plus_sq : |t| ≤ 1 + t ^ 2 := by
    by_cases h : |t| ≤ 1
    · -- |t| ≤ 1 ≤ 1 + t^2
      nlinarith [sq_nonneg t]
    · -- |t| > 1, then |t| ≤ |t|^2 = t^2 ≤ 1 + t^2
      have h' : 1 ≤ |t| := by linarith
      have hsq : |t| ≤ t ^ 2 := by
        calc
          |t| = |t| * 1 := by ring
          _ ≤ |t| * |t| := by nlinarith
          _ = t ^ 2 := by rw [← sq, sq_abs]
      nlinarith
  have h1 : 1 / (4 * (1 + |t|)) ≤ AdversarialBco.Body.chi t := by
    dsimp [AdversarialBco.Body.chi]
    have hpos : 0 < 4 * (1 + |t|) := by nlinarith [abs_nonneg t]
    have hpos' : 0 < 4 * s := by nlinarith
    refine (one_div_le_one_div hpos hpos').mpr ?_
    nlinarith
  have h2 : AdversarialBco.Body.chi t ≤ 1 / 4 := by
    dsimp [AdversarialBco.Body.chi]
    have hpos' : 0 < 4 * s := by nlinarith
    have hpos4 : (0 : ℝ) < 4 := by norm_num
    refine (one_div_le_one_div hpos' hpos4).mpr ?_
    nlinarith
  have h3 : |AdversarialBco.Body.chi' t| ≤ 1 / 4 := by
    dsimp [AdversarialBco.Body.chi']
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hpos_sq : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    simp_rw [abs_of_pos hpos_sq]
    rw [abs_of_nonneg hs_nonneg]
    have hpos_denom : 0 < 4 * ((1 + t ^ 2) * s) := by positivity
    -- We need: |t| / (4*(1+t^2)*s) ≤ 1/4
    -- Equivalent to: |t| ≤ (1+t^2)*s  (since denominator > 0)
    -- Since s ≥ 1, (1+t^2)*s ≥ 1+t^2 ≥ |t|
    have h_num : |t| ≤ (1 + t ^ 2) * s := by
      calc
        |t| ≤ 1 + t ^ 2 := habs_le_one_plus_sq
        _ ≤ (1 + t ^ 2) * 1 := by
          nlinarith
        _ ≤ (1 + t ^ 2) * s := by
          nlinarith
    -- Now use: a/d ≤ b/d when a ≤ b and d > 0
    have h_div : |t| / (4 * ((1 + t ^ 2) * s)) ≤ ((1 + t ^ 2) * s) / (4 * ((1 + t ^ 2) * s)) := by
      refine (div_le_div_of_nonneg_right h_num ?_)
      positivity
    -- Simplify RHS: ((1+t^2)*s) / (4*(1+t^2)*s) = 1/4
    calc
      |t| / (4 * ((1 + t ^ 2) * s)) ≤ ((1 + t ^ 2) * s) / (4 * ((1 + t ^ 2) * s)) := h_div
      _ = 1 / 4 := by
        field_simp [ne_of_gt hpos_sq, ne_of_gt hs_pos]
  exact And.intro h1 (And.intro h2 h3)


theorem AdversarialBco.Body.hasDerivAt_kr (t : ℝ) : HasDerivAt AdversarialBco.Body.kr (AdversarialBco.Body.kr' t) t := by
  -- expand kr and kr'
  have h_kr_eq : AdversarialBco.Body.kr = fun (x : ℝ) => (1/2 : ℝ) + x * AdversarialBco.Body.chi x - AdversarialBco.Body.chi' x := rfl
  have h_kr'_eq_target : AdversarialBco.Body.kr' t = (2 - t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))) := rfl
  rw [h_kr_eq, h_kr'_eq_target]
  have hpos : 1 + t ^ 2 > 0 := by nlinarith [sq_nonneg t]
  have hpos_ne : 1 + t ^ 2 ≠ 0 := by nlinarith
  have hsqrt_pos : Real.sqrt (1 + t ^ 2) > 0 := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (1 + t ^ 2) ≠ 0 := by linarith
  have hsq_sqrt : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by nlinarith)
  -- Step 1: derivative of chi(t) = 1 / (4 * sqrt(1 + t^2))
  have h_chi : HasDerivAt AdversarialBco.Body.chi (AdversarialBco.Body.chi' t) t := by
    have h_goal : HasDerivAt (fun (x : ℝ) => 1 / (4 * Real.sqrt (1 + x ^ 2)))
      (-t / (4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)))) t := by
      -- derivative of sqrt(1 + t^2)
      have h_inner : HasDerivAt (fun (x : ℝ) => 1 + x ^ 2) (2 * t) t := by
        have h1 : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 t := hasDerivAt_const t 1
        have h2 : HasDerivAt (fun (x : ℝ) => x ^ 2) (2 * t) t := by
          have := hasDerivAt_pow 2 t
          simpa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] using this
        have h := HasDerivAt.add h1 h2
        rw [zero_add] at h
        exact h
      have h_sqrt : HasDerivAt (fun (x : ℝ) => Real.sqrt (1 + x ^ 2)) (t / Real.sqrt (1 + t ^ 2)) t := by
        have h := HasDerivAt.sqrt h_inner hpos_ne
        have h_eq : (2 * t) / (2 * Real.sqrt (1 + t ^ 2)) = t / Real.sqrt (1 + t ^ 2) := by
          field_simp [hsqrt_ne]
        rw [h_eq] at h
        exact h
      have h_denom : HasDerivAt (fun (x : ℝ) => 4 * Real.sqrt (1 + x ^ 2)) (4 * (t / Real.sqrt (1 + t ^ 2))) t :=
        HasDerivAt.const_mul 4 h_sqrt
      have h_denom_ne_zero : 4 * Real.sqrt (1 + t ^ 2) ≠ 0 := by nlinarith
      have h_div := HasDerivAt.div (hasDerivAt_const t 1) h_denom h_denom_ne_zero
      have h_simp : ((0 : ℝ) * (4 * Real.sqrt (1 + t ^ 2)) - (1 : ℝ) * (4 * (t / Real.sqrt (1 + t ^ 2)))) /
        ((4 * Real.sqrt (1 + t ^ 2)) ^ 2) = -t / (4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) := by
        field_simp [hsqrt_ne, hpos_ne]
        ring
        rw [hsq_sqrt]
        ring
      rw [h_simp] at h_div
      exact h_div
    -- h_goal : HasDerivAt (fun x => 1/(4*sqrt(1+x^2))) (-t/(4*((1+t^2)*sqrt(1+t^2)))) t
    -- goal : HasDerivAt chi (chi' t) t
    -- chi expands to the same function, chi' t expands to the same derivative
    have h_chi_eq : AdversarialBco.Body.chi = fun (x : ℝ) => 1 / (4 * Real.sqrt (1 + x ^ 2)) := rfl
    have h_chi'_eq : AdversarialBco.Body.chi' t = -t / (4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) := rfl
    rw [h_chi_eq, h_chi'_eq]
    exact h_goal
  -- Step 2: derivative of chi'(t) = -t / (4 * (1+t^2) * sqrt(1+t^2))
  have h_chi'_deriv : HasDerivAt AdversarialBco.Body.chi'
    (-(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2)))) t := by
    have h_goal : HasDerivAt (fun (x : ℝ) => -x / (4 * ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))))
      (-(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2)))) t := by
      -- derivative of g = 1 + x^2
      have h_g : HasDerivAt (fun (x : ℝ) => 1 + x ^ 2) (2 * t) t := by
        have h1 : HasDerivAt (fun (_ : ℝ) => (1 : ℝ)) 0 t := hasDerivAt_const t 1
        have h2 : HasDerivAt (fun (x : ℝ) => x ^ 2) (2 * t) t := by
          have := hasDerivAt_pow 2 t
          simpa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] using this
        have h := HasDerivAt.add h1 h2
        rw [zero_add] at h
        exact h
      -- derivative of sqrt(1 + x^2)
      have h_s : HasDerivAt (fun (x : ℝ) => Real.sqrt (1 + x ^ 2)) (t / Real.sqrt (1 + t ^ 2)) t := by
        have h := HasDerivAt.sqrt h_g hpos_ne
        have h_eq : (2 * t) / (2 * Real.sqrt (1 + t ^ 2)) = t / Real.sqrt (1 + t ^ 2) := by
          field_simp [hsqrt_ne]
        rw [h_eq] at h
        exact h
      -- derivative of g * s
      have h_gs : HasDerivAt (fun (x : ℝ) => (1 + x ^ 2) * Real.sqrt (1 + x ^ 2))
        ((2 * t) * Real.sqrt (1 + t ^ 2) + (1 + t ^ 2) * (t / Real.sqrt (1 + t ^ 2))) t :=
        HasDerivAt.mul h_g h_s
      -- derivative of 4 * g * s
      have h_den : HasDerivAt (fun (x : ℝ) => 4 * ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2)))
        (4 * ((2 * t) * Real.sqrt (1 + t ^ 2) + (1 + t ^ 2) * (t / Real.sqrt (1 + t ^ 2)))) t :=
        HasDerivAt.const_mul 4 h_gs
      have h_den_ne_zero : 4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) ≠ 0 := by nlinarith
      -- derivative of -x
      have h_num : HasDerivAt (fun (x : ℝ) => -x) (-1) t :=
        (hasDerivAt_id t).neg
      have h_div := HasDerivAt.div h_num h_den h_den_ne_zero
      have h_simp : ((-1 : ℝ) * (4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) -
        (-t) * (4 * ((2 * t) * Real.sqrt (1 + t ^ 2) + (1 + t ^ 2) * (t / Real.sqrt (1 + t ^ 2))))) /
        ((4 * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) ^ 2) =
        -(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))) := by
        field_simp [hsqrt_ne, hpos_ne]
        ring
        rw [hsq_sqrt]
        ring
      rw [h_simp] at h_div
      exact h_div
    have h_chi'_eq : AdversarialBco.Body.chi' = fun (x : ℝ) => -x / (4 * ((1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) := rfl
    rw [h_chi'_eq]
    exact h_goal
  -- Step 3: algebraic identity: chi + t*chi' - chi'' = kr'
  have h_kr'_eq : AdversarialBco.Body.chi t + t * AdversarialBco.Body.chi' t -
    (-(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2)))) =
    (2 - t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))) := by
    simp [AdversarialBco.Body.chi, AdversarialBco.Body.chi']
    field_simp [hsqrt_ne, hpos_ne]
    nlinarith [hsq_sqrt]
  -- Step 4: assemble using derivative rules
  have h_deriv : HasDerivAt (fun (x : ℝ) => (1/2 : ℝ) + x * AdversarialBco.Body.chi x - AdversarialBco.Body.chi' x)
    (AdversarialBco.Body.chi t + t * AdversarialBco.Body.chi' t -
      (-(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))))) t := by
    have h_add := HasDerivAt.add (hasDerivAt_const t ((1 : ℝ)/2))
      (by
        have h_mul := HasDerivAt.mul (hasDerivAt_id t) h_chi
        rw [one_mul] at h_mul
        exact h_mul)
    have h_sub := HasDerivAt.sub h_add h_chi'_deriv
    convert h_sub using 1
    · rfl
    · simp [zero_add, id]
  -- Now combine: the derivative equals kr' t
  have h_final : (AdversarialBco.Body.chi t + t * AdversarialBco.Body.chi' t -
    (-(1 - 2 * t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))))) =
    (2 - t ^ 2) / (4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2))) := h_kr'_eq
  rw [h_final] at h_deriv
  exact h_deriv


theorem AdversarialBco.Body.kr_mem (t : ℝ) : 0 ≤ AdversarialBco.Body.kr t ∧ AdversarialBco.Body.kr t ≤ 1 := by
  set s := Real.sqrt (1 + t ^ 2) with hs_def
  have hs_sq : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by nlinarith : 0 ≤ 1 + t ^ 2)
  have hs_pos : 0 < s := by
    have : 0 < 1 + t ^ 2 := by nlinarith
    exact Real.sqrt_pos.mpr this
  have hs_ge_one : 1 ≤ s := by
    have h : (1 : ℝ) ^ 2 ≤ s ^ 2 := by
      rw [hs_sq]
      nlinarith
    nlinarith
  have h_abs_t_le_s : |t| ≤ s := by
    have h : t ^ 2 ≤ s ^ 2 := by
      rw [hs_sq]
      nlinarith
    nlinarith [sq_abs t]
  have h_abs_t_le_s3 : |t| ≤ s ^ 3 := by
    have h_s_le_s3 : s ≤ s ^ 3 := by
      have : s ^ 3 - s = s * (s - 1) * (s + 1) := by ring
      nlinarith
    nlinarith
  have h_tri : AdversarialBco.Body.kr t = 1/2 + t/(4*s) + t/(4*s^3) := by
    dsimp [AdversarialBco.Body.kr, AdversarialBco.Body.chi, AdversarialBco.Body.chi']
    have h_denom : (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) = s ^ 3 := by
      rw [← hs_def, ← hs_sq]
      ring
    rw [hs_def, h_denom]
    ring
  rw [h_tri]
  have h_bound1 : -(1/4 : ℝ) ≤ t/(4*s) ∧ t/(4*s) ≤ 1/4 := by
    have h1 : -s ≤ t := (abs_le.mp h_abs_t_le_s).1
    have h2 : t ≤ s := (abs_le.mp h_abs_t_le_s).2
    have hpos : 0 ≤ 4*s := by nlinarith
    have h_lower : -(1/4 : ℝ) ≤ t/(4*s) := by
      have h_eq : -(1/4 : ℝ) = (-s)/(4*s) := by field_simp [hs_pos.ne']
      rw [h_eq]
      exact div_le_div_of_nonneg_right h1 hpos
    have h_upper : t/(4*s) ≤ 1/4 := by
      have h_eq : s/(4*s) = (1/4 : ℝ) := by field_simp [hs_pos.ne']
      have h_div : t/(4*s) ≤ s/(4*s) := div_le_div_of_nonneg_right h2 hpos
      linarith
    exact And.intro h_lower h_upper
  have h_bound2 : -(1/4 : ℝ) ≤ t/(4*s^3) ∧ t/(4*s^3) ≤ 1/4 := by
    have hs3_pos : 0 < s ^ 3 := pow_pos hs_pos 3
    have h_abs_denom : |4*s^3| = 4*s^3 := abs_of_pos (by nlinarith)
    have h_abs_bound : |t/(4*s^3)| ≤ 1/4 := by
      calc
        |t/(4*s^3)| = |t| / |4*s^3| := abs_div _ _
        _ = |t| / (4*s^3) := by rw [h_abs_denom]
        _ ≤ (s ^ 3) / (4*s^3) := by
          have hpos : 0 ≤ 4*s^3 := by nlinarith
          exact (div_le_div_of_nonneg_right h_abs_t_le_s3 hpos)
        _ = 1/4 := by field_simp [hs_pos.ne']
    exact abs_le.mp h_abs_bound
  constructor
  · nlinarith
  · nlinarith


theorem AdversarialBco.Body.abs_kr_deriv_le (t : ℝ) : |AdversarialBco.Body.kr' t| ≤ 1 := by
  have hdenom_pos : 0 < 4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2)) := by
    positivity
  have h_sqrt_ge_one : 1 ≤ Real.sqrt (1 + t ^ 2) :=
    (Real.one_le_sqrt (x := 1 + t ^ 2)).mpr (by nlinarith [sq_nonneg t])
  rw [AdversarialBco.Body.kr']
  rw [abs_div]
  rw [abs_of_pos hdenom_pos]
  rw [div_le_iff₀ hdenom_pos]
  simp
  have h_tri : |2 - t ^ 2| ≤ 2 + t ^ 2 := by
    calc
      |2 - t ^ 2| = |2 + (-(t ^ 2))| := by ring
      _ ≤ |2| + |-(t ^ 2)| := abs_add_le _ _
      _ = |2| + |t ^ 2| := by simp
      _ = 2 + |t ^ 2| := by norm_num
      _ = 2 + t ^ 2 := by simp
  calc
    |2 - t ^ 2| ≤ 2 + t ^ 2 := h_tri
    _ ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg t]
    _ ≤ 4 * (1 + t ^ 2) := by nlinarith
    _ ≤ 4 * ((1 + t ^ 2) ^ 2) := by
      have hsq : 1 + t ^ 2 ≤ (1 + t ^ 2) ^ 2 := by
        have hpos' : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
        nlinarith
      nlinarith
    _ ≤ 4 * ((1 + t ^ 2) ^ 2 * Real.sqrt (1 + t ^ 2)) := by
      have hpos_sq : 0 ≤ (1 + t ^ 2) ^ 2 := by positivity
      nlinarith


theorem AdversarialBco.Body.tail_Tfun (L1 lam : ℝ) (hL1 : 0 ≤ L1) (hlam : 0 < lam) :
    4 * (1 + AdversarialBco.Body.Tfun (L1 / lam)) * L1 *
        Real.exp (AdversarialBco.Body.Tfun (L1 / lam) + 1 / 2 - AdversarialBco.Body.Tfun (L1 / lam) ^ 2 / 2) ≤
      lam / 2 := by
  set r := L1 / lam with hr_def
  have hr_nonneg : 0 ≤ r := div_nonneg hL1 (by linarith)
  have h_one_plus_r_pos : 0 < 1 + r := by linarith
  by_cases hL1_zero : L1 = 0
  · subst hL1_zero
    simp [AdversarialBco.Body.Tfun]
    nlinarith
  · have hL1_pos : 0 < L1 := by
      by_contra h
      apply hL1_zero
      linarith
    have hr_pos : 0 < r := div_pos hL1_pos hlam
    set l := Real.log (1 + r) with hl_def
    have hl_nonneg : 0 ≤ l := Real.log_nonneg (by linarith)
    set s := Real.sqrt l with hs_def
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    have hs_sq : s ^ 2 = l := Real.sq_sqrt hl_nonneg
    have hT : AdversarialBco.Body.Tfun r = 5 + 2 * s := by
      dsimp [AdversarialBco.Body.Tfun, s, l]
    have h_exp_arg : (AdversarialBco.Body.Tfun r + 1/2 - (AdversarialBco.Body.Tfun r)^2 / 2) = (-7 - 8*s - 2*l) := by
      dsimp [AdversarialBco.Body.Tfun]
      nlinarith
    have h_exp_eq : Real.exp (AdversarialBco.Body.Tfun r + 1/2 - (AdversarialBco.Body.Tfun r)^2 / 2) =
        Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹ := by
      rw [h_exp_arg]
      have h1 : Real.exp (-7 - 8*s - 2*l) = Real.exp (-7) * Real.exp (-8*s) * Real.exp (-2*l) := by
        calc
          Real.exp (-7 - 8*s - 2*l) = Real.exp ((-7 - 8*s) + (-2*l)) := by ring
          _ = Real.exp (-7 - 8*s) * Real.exp (-2*l) := by rw [Real.exp_add]
          _ = Real.exp ((-7) + (-8*s)) * Real.exp (-2*l) := by ring
          _ = (Real.exp (-7) * Real.exp (-8*s)) * Real.exp (-2*l) := by rw [Real.exp_add]
          _ = Real.exp (-7) * Real.exp (-8*s) * Real.exp (-2*l) := by ring
      have h2 : Real.exp (-2*l) = ((1+r)^2)⁻¹ := by
        calc
          Real.exp (-2*l) = Real.exp (-(2*l)) := by ring
          _ = (Real.exp (2*l))⁻¹ := by rw [Real.exp_neg]
          _ = (Real.exp (l + l))⁻¹ := by ring
          _ = ((Real.exp l) * (Real.exp l))⁻¹ := by rw [Real.exp_add]
          _ = (Real.exp l)⁻¹ * (Real.exp l)⁻¹ := by rw [mul_inv]
          _ = ((1+r)⁻¹) * ((1+r)⁻¹) := by rw [Real.exp_log h_one_plus_r_pos]
          _ = ((1+r)^2)⁻¹ := by rw [← mul_inv, pow_two]
      calc
        Real.exp (-7 - 8*s - 2*l) = Real.exp (-7) * Real.exp (-8*s) * Real.exp (-2*l) := h1
        _ = Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹ := by rw [h2]
    have hL1_eq : L1 = r * lam := by
      dsimp [r]
      field_simp [hlam.ne']
    rw [hr_def, h_exp_eq, hT, hL1_eq]
    -- Goal: 4 * (1 + (5 + 2*s)) * (r * lam) * (exp(-7) * exp(-8s) * ((1+r)^2)⁻¹) ≤ lam / 2
    -- Simplify: 1 + (5 + 2*s) = 6 + 2*s
    have h_simp : 4 * (1 + (5 + 2*s)) * (r * lam) * (Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹) =
        lam * (4 * (6 + 2*s) * r * Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹) := by
      ring
    rw [h_simp]
    -- Goal: lam * (4 * (6 + 2*s) * r * X) ≤ lam / 2  where X = exp(-7)*exp(-8s)*((1+r)^2)⁻¹
    -- Since lam > 0, we can cancel it: divide both sides by lam
    -- Equivalent to: 4 * (6 + 2*s) * r * X ≤ 1/2
    -- Multiply by 2: 8 * (6 + 2*s) * r * X ≤ 1
    have h_goal' : 8 * (6 + 2*s) * r * Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹ ≤ 1 := by
      have h_bound1 : (6 + 2*s) * Real.exp (-8*s) ≤ 6 := by
        have hineq : 1 + s/3 ≤ Real.exp (8*s) := by
          calc
            1 + s/3 ≤ 1 + 8*s := by nlinarith
            _ = 8*s + 1 := by ring
            _ ≤ Real.exp (8*s) := Real.add_one_le_exp (8*s)
        have hpos : 0 < Real.exp (8*s) := Real.exp_pos (8*s)
        have h := mul_le_mul_of_nonneg_right hineq (by
          have : 0 ≤ Real.exp (-8*s) := (Real.exp_pos (-8*s)).le
          exact this)
        -- h: (1 + s/3) * exp(-8s) ≤ exp(8s) * exp(-8s) = 1
        -- But we need (6 + 2s) * exp(-8s) ≤ 6
        -- Note: (6 + 2s) * exp(-8s) = 6 * (1 + s/3) * exp(-8s)
        calc
          (6 + 2*s) * Real.exp (-8*s) = 6 * ((1 + s/3) * Real.exp (-8*s)) := by ring
          _ ≤ 6 * (Real.exp (8*s) * Real.exp (-8*s)) := by
            nlinarith
          _ = 6 * Real.exp (8*s + (-8*s)) := by rw [Real.exp_add]
          _ = 6 * Real.exp 0 := by ring
          _ = 6 * 1 := by rw [Real.exp_zero]
          _ = 6 := by ring
      have h_bound2 : r * ((1+r)^2)⁻¹ ≤ 1 := by
        have h : r ≤ (1+r)^2 := by
          nlinarith
        have hpos_sq : 0 < (1+r)^2 := pow_pos h_one_plus_r_pos 2
        have hpos_inv : 0 ≤ ((1+r)^2)⁻¹ := by positivity
        calc
          r * ((1+r)^2)⁻¹ ≤ (1+r)^2 * ((1+r)^2)⁻¹ := by
            nlinarith
          _ = 1 := by field_simp [hpos_sq.ne']
      have h_bound3 : Real.exp (-7) ≤ (1/1000 : ℝ) := by
        rw [Real.exp_neg]
        have hpos1000 : 0 < (1000 : ℝ) := by norm_num
        have hpos_exp7 : 0 < Real.exp 7 := Real.exp_pos 7
        have h_exp7_gt : (1000 : ℝ) < Real.exp 7 := by
          have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
          have h_pow_lt : (2.7182818283 : ℝ)^7 < (Real.exp 1)^7 := by
            refine pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (7 : ℕ) ≠ 0)
          have h_pow_gt : (1000 : ℝ) < (2.7182818283 : ℝ)^7 := by norm_num
          have h_exp7_eq : (Real.exp 1)^7 = Real.exp 7 := by
            calc
              (Real.exp 1)^7 = Real.exp ((7 : ℕ) * (1 : ℝ)) := by rw [Real.exp_nat_mul 1 7]
              _ = Real.exp 7 := by norm_num
          linarith
        have h : (1000 : ℝ) ≤ Real.exp 7 := by linarith
        have h_inv := (inv_le_inv₀ hpos_exp7 hpos1000).mpr h
        -- h_inv: (Real.exp 7)⁻¹ ≤ 1000⁻¹
        -- We need: (Real.exp 7)⁻¹ ≤ 1/1000
        -- But 1/1000 = 1000⁻¹ by definition
        simpa [div_eq_inv_mul] using h_inv
      have h_nonneg_s : 0 ≤ 6 + 2*s := by nlinarith
      have h_nonneg_r : 0 ≤ r := hr_nonneg
      have h_nonneg_exp7 : 0 ≤ Real.exp (-7) := (Real.exp_pos (-7)).le
      have h_nonneg_exp8s : 0 ≤ Real.exp (-8*s) := (Real.exp_pos (-8*s)).le
      have h_nonneg_inv : 0 ≤ ((1+r)^2)⁻¹ := by positivity
      have h_mul : 8 * ((6 + 2*s) * Real.exp (-8*s)) * (r * ((1+r)^2)⁻¹) * Real.exp (-7) ≤
          8 * 6 * 1 * Real.exp (-7) := by
        have h_nonneg_A : 0 ≤ (6 + 2*s) * Real.exp (-8*s) := by positivity
        have h_nonneg_B : 0 ≤ r * ((1+r)^2)⁻¹ := by positivity
        have h_nonneg_8 : 0 ≤ (8 : ℝ) := by norm_num
        have h_nonneg_C : 0 ≤ Real.exp (-7) := (Real.exp_pos (-7)).le
        set A := (6 + 2*s) * Real.exp (-8*s) with hA
        set B := r * ((1+r)^2)⁻¹ with hB
        set C := Real.exp (-7) with hC
        have h_AC : 8 * A * B ≤ 8 * 6 * 1 := by
          calc
            8 * A * B = 8 * (A * B) := by ring
            _ ≤ 8 * (6 * 1) := by
              apply mul_le_mul_of_nonneg_left ?_ h_nonneg_8
              exact mul_le_mul h_bound1 h_bound2 h_nonneg_B (by norm_num)
            _ = 8 * 6 * 1 := by ring
        calc
          8 * A * B * C ≤ (8 * 6 * 1) * C := mul_le_mul_of_nonneg_right h_AC h_nonneg_C
          _ = 8 * 6 * 1 * C := by ring
      calc
        8 * (6 + 2*s) * r * Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹
            = 8 * ((6 + 2*s) * Real.exp (-8*s)) * (r * ((1+r)^2)⁻¹) * Real.exp (-7) := by ring
        _ ≤ 8 * 6 * 1 * Real.exp (-7) := h_mul
        _ = 48 * Real.exp (-7) := by ring
        _ ≤ 48 * (1/1000 : ℝ) := by nlinarith
        _ = 48/1000 := by ring
        _ ≤ 1 := by norm_num
    -- From h_goal' : 8 * (6 + 2*s) * r * X ≤ 1, we get 4 * (6 + 2*s) * r * X ≤ 1/2
    have h_goal : 4 * (6 + 2*s) * r * Real.exp (-7) * Real.exp (-8*s) * ((1+r)^2)⁻¹ ≤ 1/2 := by
      nlinarith
    -- Now combine with lam
    nlinarith


theorem AdversarialBco.Body.one_add_Tfun_sq_le (r : ℝ) (hr : 0 ≤ r) :
    (1 + AdversarialBco.Body.Tfun r) ^ 2 ≤ 72 + 8 * Real.log (1 + r) := by
  set l := Real.log (1 + r) with hl
  have hl_nonneg : 0 ≤ l := Real.log_nonneg (by linarith)
  set s := Real.sqrt l with hs
  have hs_sq : s ^ 2 = l := Real.sq_sqrt hl_nonneg
  have hTfun : AdversarialBco.Body.Tfun r = 5 + 2 * s := by
    dsimp [AdversarialBco.Body.Tfun, hs, hl]
  calc
    (1 + AdversarialBco.Body.Tfun r) ^ 2 = (1 + (5 + 2 * s)) ^ 2 := by rw [hTfun]
    _ = (6 + 2 * s) ^ 2 := by ring
    _ = 36 + 24 * s + 4 * s ^ 2 := by ring
    _ ≤ 72 + 8 * s ^ 2 := by
      nlinarith [sq_nonneg (s - 3)]
    _ = 72 + 8 * Real.log (1 + r) := by rw [hs_sq, hl]


theorem AdversarialBco.Body.integral_cosh_tail (T : ℝ) (hT : 0 ≤ T) :
    ∫ x, (|x| + T) * Real.cosh (T * x) ∂(gaussianReal 0 1) ≤ 2 * (1 + T) * Real.exp ((T + 1) ^ 2 / 2) := by
  -- |x| ≤ exp(x) + exp(-x)
  have h_abs_bound (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have h := Real.add_one_le_exp x
      have hpos := Real.exp_pos (-x)
      linarith
    · have hx' : x ≤ 0 := by linarith
      rw [abs_of_nonpos hx']
      have h := Real.add_one_le_exp (-x)
      have hpos := Real.exp_pos x
      linarith
  -- integrability of exp(a*x) under N(0,1)
  have h_int (a : ℝ) : Integrable (fun x => Real.exp (a * x)) (gaussianReal 0 1) := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a
  -- integral of exp(a*x) under N(0,1) = exp(a^2/2)
  have h_integral_exp (a : ℝ) : ∫ x, Real.exp (a * x) ∂(gaussianReal 0 1) = Real.exp (a ^ 2 / 2) := by
    calc
      ∫ x, Real.exp (a * x) ∂(gaussianReal 0 1) = mgf id (gaussianReal 0 1) a := by
        rw [mgf]
        simp
      _ = Real.exp (0 * a + 1 * a ^ 2 / 2) := by
        rw [mgf_id_gaussianReal]
        simp
      _ = Real.exp (a ^ 2 / 2) := by ring_nf
  -- integral of exp(-(T*x)) under N(0,1) = exp(T^2/2)
  have h_integral_exp_neg (T : ℝ) : ∫ x, Real.exp (-(T * x)) ∂(gaussianReal 0 1) = Real.exp (T ^ 2 / 2) := by
    calc
      ∫ x, Real.exp (-(T * x)) ∂(gaussianReal 0 1) = ∫ x, Real.exp ((-T) * x) ∂(gaussianReal 0 1) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp
      _ = Real.exp ((-T) ^ 2 / 2) := h_integral_exp (-T)
      _ = Real.exp (T ^ 2 / 2) := by ring
  -- pointwise bound
  have h_pointwise (x : ℝ) : (|x| + T) * Real.cosh (T * x) ≤
      ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 := by
    rw [Real.cosh_eq]
    have h_nonneg_B : 0 ≤ Real.exp (T * x) + Real.exp (-(T * x)) := by positivity
    have h_nonneg_half : 0 ≤ (Real.exp (T * x) + Real.exp (-(T * x))) / 2 := by positivity
    have h_mul : (|x| + T) * ((Real.exp (T * x) + Real.exp (-(T * x))) / 2) ≤
        (Real.exp x + Real.exp (-x) + T) * ((Real.exp (T * x) + Real.exp (-(T * x))) / 2) := by
      apply mul_le_mul_of_nonneg_right
      · nlinarith [h_abs_bound x]
      · exact h_nonneg_half
    simpa [mul_div_assoc] using h_mul
  -- expand the RHS into a sum of 6 exponential terms
  have h_expand (x : ℝ) : ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 =
      (1/2 : ℝ) * Real.exp ((T + 1) * x) + (1/2 : ℝ) * Real.exp ((1 - T) * x) +
      (1/2 : ℝ) * Real.exp ((T - 1) * x) + (1/2 : ℝ) * Real.exp (-(T + 1) * x) +
      (T/2 : ℝ) * Real.exp (T * x) + (T/2 : ℝ) * Real.exp (-(T * x)) := by
    calc
      ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2
          = ((Real.exp x + Real.exp (-x)) * (Real.exp (T * x) + Real.exp (-(T * x))) +
              T * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 := by ring
      _ = ((Real.exp x * Real.exp (T * x) + Real.exp x * Real.exp (-(T * x)) +
            Real.exp (-x) * Real.exp (T * x) + Real.exp (-x) * Real.exp (-(T * x))) +
            T * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 := by ring
      _ = ((Real.exp (x + T * x) + Real.exp (x + (-(T * x))) +
            Real.exp ((-x) + T * x) + Real.exp ((-x) + (-(T * x)))) +
            T * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 := by
            simp [Real.exp_add]
      _ = ((Real.exp ((T + 1) * x) + Real.exp ((1 - T) * x) +
            Real.exp ((T - 1) * x) + Real.exp (-(T + 1) * x)) +
            T * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 := by ring
      _ = (1/2 : ℝ) * Real.exp ((T + 1) * x) + (1/2 : ℝ) * Real.exp ((1 - T) * x) +
          (1/2 : ℝ) * Real.exp ((T - 1) * x) + (1/2 : ℝ) * Real.exp (-(T + 1) * x) +
          (T/2 : ℝ) * Real.exp (T * x) + (T/2 : ℝ) * Real.exp (-(T * x)) := by ring
  -- integrability of the RHS
  have h_int_rhs : Integrable (fun x => ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2)
      (gaussianReal 0 1) := by
    have h_eq : (fun x => ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2) =
        (fun x => (1/2 : ℝ) • Real.exp ((T + 1) * x) + (1/2 : ℝ) • Real.exp ((1 - T) * x) +
          (1/2 : ℝ) • Real.exp ((T - 1) * x) + (1/2 : ℝ) • Real.exp (-(T + 1) * x) +
          (T/2 : ℝ) • Real.exp (T * x) + (T/2 : ℝ) • Real.exp (-(T * x))) := by
      ext x
      rw [h_expand x]
      simp [smul_eq_mul]
    rw [h_eq]
    refine Integrable.add ?_ ?_
    · refine Integrable.add ?_ ?_
      · refine Integrable.add ?_ ?_
        · refine Integrable.add ?_ ?_
          · refine Integrable.add ?_ ?_
            · exact (h_int (T + 1)).smul (1/2 : ℝ)
            · exact (h_int (1 - T)).smul (1/2 : ℝ)
          · exact (h_int (T - 1)).smul (1/2 : ℝ)
        · exact (h_int (-(T + 1))).smul (1/2 : ℝ)
      · exact (h_int T).smul (T/2 : ℝ)
    · -- h_int (-T) gives integrability of exp((-T)*x), we need (T/2) * exp(-(T*x))
      convert (h_int (-T)).smul (T/2 : ℝ) using 1
      ext x
      simp [smul_eq_mul, neg_mul]
  -- integrability of LHS
  have h_int_lhs : Integrable (fun x => (|x| + T) * Real.cosh (T * x)) (gaussianReal 0 1) := by
    have h_cont : Continuous (fun x : ℝ => (|x| + T) * Real.cosh (T * x)) := by
      refine ((continuous_abs.add continuous_const).mul ?_)
      have : Continuous (fun x : ℝ => T * x) := by continuity
      exact Real.continuous_cosh.comp this
    have h_nonneg : ∀ x, 0 ≤ (|x| + T) * Real.cosh (T * x) := by
      intro x; positivity
    refine h_int_rhs.mono_nonneg
      (h_cont.aestronglyMeasurable)
      (ae_of_all _ h_nonneg)
      (ae_of_all _ h_pointwise)
  -- apply integral_mono
  have h_integral_bound : ∫ x, (|x| + T) * Real.cosh (T * x) ∂(gaussianReal 0 1) ≤
      ∫ x, ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 ∂(gaussianReal 0 1) :=
    integral_mono h_int_lhs h_int_rhs h_pointwise
  -- compute the RHS integral
  have h_integral_rhs : ∫ x, ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2
      ∂(gaussianReal 0 1) = Real.exp (((T : ℝ) + 1) ^ 2 / 2) + Real.exp (((T : ℝ) - 1) ^ 2 / 2) + T * Real.exp (T ^ 2 / 2) := by
    have h_integrand_eq : (fun x => ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2) =
        (fun x => (1/2 : ℝ) * Real.exp ((T + 1) * x) + (1/2 : ℝ) * Real.exp ((1 - T) * x) +
          (1/2 : ℝ) * Real.exp ((T - 1) * x) + (1/2 : ℝ) * Real.exp (-(T + 1) * x) +
          (T/2 : ℝ) * Real.exp (T * x) + (T/2 : ℝ) * Real.exp (-(T * x))) := by
      ext x; exact h_expand x
    rw [h_integrand_eq]
    -- Define the 6 integrands for brevity
    set f1 := fun x => (1/2 : ℝ) * Real.exp ((T + 1) * x) with hf1
    set f2 := fun x => (1/2 : ℝ) * Real.exp ((1 - T) * x) with hf2
    set f3 := fun x => (1/2 : ℝ) * Real.exp ((T - 1) * x) with hf3
    set f4 := fun x => (1/2 : ℝ) * Real.exp (-(T + 1) * x) with hf4
    set f5 := fun x => (T/2 : ℝ) * Real.exp (T * x) with hf5
    set f6 := fun x => (T/2 : ℝ) * Real.exp (-(T * x)) with hf6
    have hI1 : Integrable f1 (gaussianReal 0 1) := (h_int (T + 1)).smul (1/2 : ℝ)
    have hI2 : Integrable f2 (gaussianReal 0 1) := (h_int (1 - T)).smul (1/2 : ℝ)
    have hI3 : Integrable f3 (gaussianReal 0 1) := (h_int (T - 1)).smul (1/2 : ℝ)
    have hI4 : Integrable f4 (gaussianReal 0 1) := (h_int (-(T + 1))).smul (1/2 : ℝ)
    have hI5 : Integrable f5 (gaussianReal 0 1) := (h_int T).smul (T/2 : ℝ)
    have hI6 : Integrable f6 (gaussianReal 0 1) := by
      convert (h_int (-T)).smul (T/2 : ℝ) using 1
      ext x
      simp [hf6, smul_eq_mul, neg_mul]
    calc
      ∫ x, (f1 x + f2 x + f3 x + f4 x + f5 x + f6 x) ∂(gaussianReal 0 1)
          = (∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, (f2 x + f3 x + f4 x + f5 x + f6 x) ∂(gaussianReal 0 1)) := by
            simpa [add_assoc] using integral_add hI1 (hI2.add (hI3.add (hI4.add (hI5.add hI6))))
      _ = (∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1)) + (∫ x, (f3 x + f4 x + f5 x + f6 x) ∂(gaussianReal 0 1)) := by
            simpa [add_assoc] using congrArg (fun t => (∫ x, f1 x ∂(gaussianReal 0 1)) + t)
              (integral_add hI2 (hI3.add (hI4.add (hI5.add hI6))))
      _ = (∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1)) + (∫ x, f3 x ∂(gaussianReal 0 1)) + (∫ x, (f4 x + f5 x + f6 x) ∂(gaussianReal 0 1)) := by
            simpa [add_assoc] using congrArg (fun t => ((∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1))) + t)
              (integral_add hI3 (hI4.add (hI5.add hI6)))
      _ = (∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1)) + (∫ x, f3 x ∂(gaussianReal 0 1)) +
          (∫ x, f4 x ∂(gaussianReal 0 1)) + (∫ x, (f5 x + f6 x) ∂(gaussianReal 0 1)) := by
            simpa [add_assoc] using congrArg (fun t => (((∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1))) +
              (∫ x, f3 x ∂(gaussianReal 0 1))) + t)
              (integral_add hI4 (hI5.add hI6))
      _ = (∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1)) + (∫ x, f3 x ∂(gaussianReal 0 1)) +
          (∫ x, f4 x ∂(gaussianReal 0 1)) + (∫ x, f5 x ∂(gaussianReal 0 1)) + (∫ x, f6 x ∂(gaussianReal 0 1)) := by
            simpa [add_assoc] using congrArg (fun t => ((((∫ x, f1 x ∂(gaussianReal 0 1)) + (∫ x, f2 x ∂(gaussianReal 0 1))) +
              (∫ x, f3 x ∂(gaussianReal 0 1))) + (∫ x, f4 x ∂(gaussianReal 0 1))) + t)
              (integral_add hI5 hI6)
      _ = ((1/2 : ℝ) * ∫ x, Real.exp ((T + 1) * x) ∂(gaussianReal 0 1)) +
          ((1/2 : ℝ) * ∫ x, Real.exp ((1 - T) * x) ∂(gaussianReal 0 1)) +
          ((1/2 : ℝ) * ∫ x, Real.exp ((T - 1) * x) ∂(gaussianReal 0 1)) +
          ((1/2 : ℝ) * ∫ x, Real.exp (-(T + 1) * x) ∂(gaussianReal 0 1)) +
          ((T/2 : ℝ) * ∫ x, Real.exp (T * x) ∂(gaussianReal 0 1)) +
          ((T/2 : ℝ) * ∫ x, Real.exp (-(T * x)) ∂(gaussianReal 0 1)) := by
            simp [hf1, hf2, hf3, hf4, hf5, hf6, integral_mul_const, integral_const_mul]
      _ = ((1/2 : ℝ) * Real.exp ((T + 1) ^ 2 / 2)) + ((1/2 : ℝ) * Real.exp ((1 - T) ^ 2 / 2)) +
          ((1/2 : ℝ) * Real.exp ((T - 1) ^ 2 / 2)) + ((1/2 : ℝ) * Real.exp ((-(T + 1)) ^ 2 / 2)) +
          ((T/2 : ℝ) * Real.exp (T ^ 2 / 2)) + ((T/2 : ℝ) * Real.exp (T ^ 2 / 2)) := by
            simp [h_integral_exp, h_integral_exp_neg T]
      _ = Real.exp ((T + 1) ^ 2 / 2) + Real.exp ((T - 1) ^ 2 / 2) + T * Real.exp (T ^ 2 / 2) := by ring
  -- final bound
  have h_final : Real.exp (((T : ℝ) + 1) ^ 2 / 2) + Real.exp (((T : ℝ) - 1) ^ 2 / 2) + T * Real.exp (T ^ 2 / 2) ≤
      2 * (1 + T) * Real.exp ((T + 1) ^ 2 / 2) := by
    have h_sq1 : (T - 1) ^ 2 ≤ (T + 1) ^ 2 := by nlinarith
    have h_sq2 : T ^ 2 ≤ (T + 1) ^ 2 := by nlinarith
    have h_exp1 : Real.exp (((T : ℝ) - 1) ^ 2 / 2) ≤ Real.exp ((T + 1) ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h_exp2 : Real.exp (T ^ 2 / 2) ≤ Real.exp ((T + 1) ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h_nonneg_exp : 0 ≤ Real.exp ((T + 1) ^ 2 / 2) := (Real.exp_pos _).le
    nlinarith
  -- combine everything
  calc
    ∫ x, (|x| + T) * Real.cosh (T * x) ∂(gaussianReal 0 1)
        ≤ ∫ x, ((Real.exp x + Real.exp (-x) + T) * (Real.exp (T * x) + Real.exp (-(T * x)))) / 2 ∂(gaussianReal 0 1) := h_integral_bound
    _ = Real.exp (((T : ℝ) + 1) ^ 2 / 2) + Real.exp (((T : ℝ) - 1) ^ 2 / 2) + T * Real.exp (T ^ 2 / 2) := h_integral_rhs
    _ ≤ 2 * (1 + T) * Real.exp ((T + 1) ^ 2 / 2) := h_final
