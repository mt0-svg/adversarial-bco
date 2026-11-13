/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Poly.Df2PropGTools

@[expose] public section

/-!
# The coupling lemma

The total variation between the dither law `N(m, (r/2)²)` of the computed run and the reference law `N(0, 1/4)`.

* `tv_gauss`: the coupling lemma, `N(m, (r/2)²)(S) ≤ N(0, 1/4)(S) + (|r - 1| + |m|)/min(r, 1)` and the reverse, for
  every
  Borel `S` and `r > 0`; from `gauss_affine_eq` and `gauss_affine_le` (Poly/Df2PropGTools.lean).
* `lintegral_sub_le`: for densities `f, g` with `∫ f = ∫ g = 1`, `∫_S f ≤ ∫_S g + ∫ (f - g)⁺` on every measurable `S`.

Each lemma sits in a namespace
`AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit.Aux_tv_gauss


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.tv_gauss (m r : ℝ) (hr : 0 < r) (S : Set ℝ) (hS : MeasurableSet S) :
    gaussianReal m ((r / 2) ^ 2).toNNReal S ≤
        gaussianReal 0 ((1 / 2 : ℝ) ^ 2).toNNReal S + ENNReal.ofReal ((|r - 1| + |m|) / min r 1) ∧
      gaussianReal 0 ((1 / 2 : ℝ) ^ 2).toNNReal S ≤
        gaussianReal m ((r / 2) ^ 2).toNNReal S + ENNReal.ofReal ((|r - 1| + |m|) / min r 1) := by
  set μ := gaussianReal m ((r / 2) ^ 2).toNNReal with hμ
  set ν := gaussianReal 0 ((1 / 2 : ℝ) ^ 2).toNNReal with hν
  set ε := ENNReal.ofReal ((|r - 1| + |m|) / min r 1) with hε
  have h_prob_le_one_μ : μ S ≤ 1 := prob_le_one
  have h_prob_le_one_ν : ν S ≤ 1 := prob_le_one
  -- Helper: if μ Sᶜ ≤ ν Sᶜ + ε then ν S ≤ μ S + ε
  have h_first_compl_to_second (h : μ Sᶜ ≤ ν Sᶜ + ε) : ν S ≤ μ S + ε := by
    have h_compl_eq_μ : μ Sᶜ = 1 - μ S := prob_compl_eq_one_sub hS
    have h_compl_eq_ν : ν Sᶜ = 1 - ν S := prob_compl_eq_one_sub hS
    rw [h_compl_eq_μ, h_compl_eq_ν] at h
    -- h : 1 - μ S ≤ (1 - ν S) + ε
    rw [tsub_le_iff_left] at h
    -- h : 1 ≤ μ S + ((1 - ν S) + ε)
    have h' : (1 - ν S) + ν S ≤ μ S + ((1 - ν S) + ε) := by
      calc
        (1 - ν S) + ν S = 1 := by rw [tsub_add_cancel_of_le h_prob_le_one_ν]
        _ ≤ μ S + ((1 - ν S) + ε) := h
    have h'' : (1 - ν S) + ν S ≤ (1 - ν S) + (μ S + ε) := by
      simpa [add_comm, add_assoc, add_left_comm] using h'
    have h_finite_sub : 1 - ν S ≠ ⊤ := by
      have hle' : 1 - ν S ≤ 1 := tsub_le_self
      exact ne_of_lt (lt_of_le_of_lt hle' (by norm_num : (1 : ENNReal) < ⊤))
    exact (ENNReal.add_le_add_iff_left h_finite_sub).mp h''
  -- Helper: if ν Sᶜ ≤ μ Sᶜ + ε then μ S ≤ ν S + ε
  have h_second_compl_to_first (h : ν Sᶜ ≤ μ Sᶜ + ε) : μ S ≤ ν S + ε := by
    have h_compl_eq_μ : μ Sᶜ = 1 - μ S := prob_compl_eq_one_sub hS
    have h_compl_eq_ν : ν Sᶜ = 1 - ν S := prob_compl_eq_one_sub hS
    rw [h_compl_eq_μ, h_compl_eq_ν] at h
    -- h : 1 - ν S ≤ (1 - μ S) + ε
    rw [tsub_le_iff_left] at h
    -- h : 1 ≤ ν S + ((1 - μ S) + ε)
    have h' : (1 - μ S) + μ S ≤ ν S + ((1 - μ S) + ε) := by
      calc
        (1 - μ S) + μ S = 1 := by rw [tsub_add_cancel_of_le h_prob_le_one_μ]
        _ ≤ ν S + ((1 - μ S) + ε) := h
    have h'' : (1 - μ S) + μ S ≤ (1 - μ S) + (ν S + ε) := by
      simpa [add_comm, add_assoc, add_left_comm] using h'
    have h_finite_sub : 1 - μ S ≠ ⊤ := by
      have hle' : 1 - μ S ≤ 1 := tsub_le_self
      exact ne_of_lt (lt_of_le_of_lt hle' (by norm_num : (1 : ENNReal) < ⊤))
    exact (ENNReal.add_le_add_iff_left h_finite_sub).mp h''
  -- Main proof: case split on r ≥ 1
  by_cases hr1 : 1 ≤ r
  · -- Case r ≥ 1: prove first conjunct directly, second via complements
    have h_first : μ S ≤ ν S + ε := by
      -- r ≥ 1: min r 1 = 1, |r-1| = r-1
      have h_min : min r 1 = 1 := min_eq_right hr1
      have h_abs : |r - 1| = r - 1 := abs_of_nonneg (sub_nonneg.mpr hr1)
      have h_eps_eq : ε = ENNReal.ofReal (r - 1 + |m|) := by
        dsimp [ε]
        rw [h_min, h_abs]
        simp
      -- Apply gauss_affine_le with a1 = m, a0 = 0, b0 = 1/2, u = r-1
      have h_le := AdversarialBco.Poly.PropG.gauss_affine_le m 0 (1/2 : ℝ) (r - 1) (by norm_num) (by linarith) S hS
      -- Simplify the set in h_le
      have h_set_eq : {z : ℝ | m + (1 + (r - 1)) * ((1 : ℝ) / 2) * z ∈ S} = {z : ℝ | m + (r / 2) * z ∈ S} := by
        ext z
        have hcoeff : (1 + (r - 1)) * ((1 : ℝ) / 2) = r / 2 := by ring
        rw [hcoeff]
      rw [h_set_eq] at h_le
      -- Simplify the error term
      have h_err_eq : ENNReal.ofReal ((r - 1) + |m - 0| / (2 * ((1 : ℝ) / 2))) = ENNReal.ofReal (r - 1 + |m|) := by
        simp
      rw [h_err_eq] at h_le
      -- Apply gauss_affine_eq to convert to μ and ν
      have h_s_ne_zero : r / 2 ≠ 0 := by
        intro hzero
        have : r = 0 := by nlinarith
        linarith
      have h_half_ne_zero : (1/2 : ℝ) ≠ 0 := by norm_num
      have h_eq_LHS : gaussianReal 0 1 {z : ℝ | m + (r / 2) * z ∈ S} = μ S := by
        rw [hμ, AdversarialBco.Poly.PropG.gauss_affine_eq m (r / 2) h_s_ne_zero S hS]
      have h_eq_RHS_base : gaussianReal 0 1 {z : ℝ | (0 : ℝ) + ((1 : ℝ) / 2) * z ∈ S} = ν S := by
        rw [hν, AdversarialBco.Poly.PropG.gauss_affine_eq 0 (1/2) h_half_ne_zero S hS]
      rw [h_eq_LHS, h_eq_RHS_base] at h_le
      -- h_le : μ S ≤ ν S + ENNReal.ofReal (r - 1 + |m|)
      rw [h_eps_eq]
      exact h_le
    have h_second : ν S ≤ μ S + ε := by
      -- Apply h_first_compl_to_second to Sᶜ
      have hS_compl : MeasurableSet (Sᶜ) := hS.compl
      have h_first_compl : μ Sᶜ ≤ ν Sᶜ + ε := by
        -- Same proof as h_first but with S replaced by Sᶜ
        have h_min : min r 1 = 1 := min_eq_right hr1
        have h_abs : |r - 1| = r - 1 := abs_of_nonneg (sub_nonneg.mpr hr1)
        have h_eps_eq : ε = ENNReal.ofReal (r - 1 + |m|) := by
          dsimp [ε]
          rw [h_min, h_abs]
          simp
        have h_le := AdversarialBco.Poly.PropG.gauss_affine_le m 0 (1/2 : ℝ) (r - 1) (by norm_num) (by linarith) (Sᶜ) hS_compl
        have h_set_eq : {z : ℝ | m + (1 + (r - 1)) * ((1 : ℝ) / 2) * z ∈ Sᶜ} = {z : ℝ | m + (r / 2) * z ∈ Sᶜ} := by
          ext z
          have hcoeff : (1 + (r - 1)) * ((1 : ℝ) / 2) = r / 2 := by ring
          rw [hcoeff]
        rw [h_set_eq] at h_le
        have h_err_eq : ENNReal.ofReal ((r - 1) + |m - 0| / (2 * ((1 : ℝ) / 2))) = ENNReal.ofReal (r - 1 + |m|) := by
          simp
        rw [h_err_eq] at h_le
        have h_s_ne_zero : r / 2 ≠ 0 := by
          intro hzero
          have : r = 0 := by nlinarith
          linarith
        have h_half_ne_zero : (1/2 : ℝ) ≠ 0 := by norm_num
        have h_eq_LHS : gaussianReal 0 1 {z : ℝ | m + (r / 2) * z ∈ Sᶜ} = μ Sᶜ := by
          rw [hμ, AdversarialBco.Poly.PropG.gauss_affine_eq m (r / 2) h_s_ne_zero (Sᶜ) hS_compl]
        have h_eq_RHS_base : gaussianReal 0 1 {z : ℝ | (0 : ℝ) + ((1 : ℝ) / 2) * z ∈ Sᶜ} = ν Sᶜ := by
          rw [hν, AdversarialBco.Poly.PropG.gauss_affine_eq 0 (1/2) h_half_ne_zero (Sᶜ) hS_compl]
        rw [h_eq_LHS, h_eq_RHS_base] at h_le
        rw [h_eps_eq]
        exact h_le
      exact h_first_compl_to_second h_first_compl
    exact And.intro h_first h_second
  · -- Case r < 1: prove second conjunct directly, first via complements
    have hr_lt_one : r < 1 := by linarith
    have h_second : ν S ≤ μ S + ε := by
      -- r < 1: min r 1 = r, |r-1| = 1-r
      have h_min : min r 1 = r := min_eq_left (le_of_lt hr_lt_one)
      have h_abs_raw : |r - 1| = -(r - 1) := abs_of_nonpos (sub_nonpos.mpr (le_of_lt hr_lt_one))
      have h_abs : |r - 1| = 1 - r := by
        rw [h_abs_raw]
        ring
      have h_eps_eq : ε = ENNReal.ofReal ((1 - r + |m|) / r) := by
        dsimp [ε]
        rw [h_min, h_abs]
      -- Apply gauss_affine_le with a1 = 0, a0 = m, b0 = r/2, u = 1/r - 1
      have hu_nonneg : 0 ≤ 1/r - 1 := by
        have h_inv_gt_one : 1 < 1/r := one_lt_one_div hr hr_lt_one
        linarith
      have hb0_pos : 0 < r/2 := by linarith
      have h_le := AdversarialBco.Poly.PropG.gauss_affine_le 0 m (r/2) (1/r - 1) hb0_pos hu_nonneg S hS
      -- Simplify the set in h_le
      have h_set_eq : {z : ℝ | (0 : ℝ) + (1 + (1/r - 1)) * (r/2) * z ∈ S} = {z : ℝ | ((1 : ℝ)/2) * z ∈ S} := by
        ext z
        have hcoeff : (1 + (1/r - 1)) * (r/2) = (1/2 : ℝ) := by
          field_simp [ne_of_gt hr]
          ring
        rw [hcoeff]
        simp
      rw [h_set_eq] at h_le
      -- Simplify the error term
      have h_err_eq : ENNReal.ofReal ((1/r - 1) + |(0 : ℝ) - m| / (2 * (r/2))) = ENNReal.ofReal ((1 - r + |m|) / r) := by
        have hcalc : (1/r - 1) + |m| / r = (1 - r + |m|) / r := by
          field_simp [ne_of_gt hr]
        have hsimpl : 2 * (r/2) = r := by ring
        simp [hsimpl]
        simpa using congrArg ENNReal.ofReal hcalc
      rw [h_err_eq] at h_le
      -- Apply gauss_affine_eq to convert to μ and ν
      -- Note: {z | (1/2)*z ∈ S} = {z | 0 + (1/2)*z ∈ S}
      have h_set_eq2 : {z : ℝ | ((1 : ℝ)/2) * z ∈ S} = {z : ℝ | (0 : ℝ) + ((1 : ℝ)/2) * z ∈ S} := by
        ext z; simp
      rw [h_set_eq2] at h_le
      have h_s_ne_zero : r / 2 ≠ 0 := by
        intro hzero
        have : r = 0 := by nlinarith
        linarith
      have h_half_ne_zero : (1/2 : ℝ) ≠ 0 := by norm_num
      have h_eq_LHS : gaussianReal 0 1 {z : ℝ | (0 : ℝ) + ((1 : ℝ)/2) * z ∈ S} = ν S := by
        rw [hν, AdversarialBco.Poly.PropG.gauss_affine_eq 0 (1/2) h_half_ne_zero S hS]
      have h_eq_RHS_base : gaussianReal 0 1 {z : ℝ | m + (r / 2) * z ∈ S} = μ S := by
        rw [hμ, AdversarialBco.Poly.PropG.gauss_affine_eq m (r / 2) h_s_ne_zero S hS]
      rw [h_eq_LHS, h_eq_RHS_base] at h_le
      -- h_le : ν S ≤ μ S + ENNReal.ofReal ((1 - r + |m|) / r)
      rw [h_eps_eq]
      exact h_le
    have h_first : μ S ≤ ν S + ε := by
      -- Apply h_second_compl_to_first to Sᶜ
      have hS_compl : MeasurableSet (Sᶜ) := hS.compl
      have h_second_compl : ν Sᶜ ≤ μ Sᶜ + ε := by
        -- Same proof as h_second but with S replaced by Sᶜ
        have h_min : min r 1 = r := min_eq_left (le_of_lt hr_lt_one)
        have h_abs_raw : |r - 1| = -(r - 1) := abs_of_nonpos (sub_nonpos.mpr (le_of_lt hr_lt_one))
        have h_abs : |r - 1| = 1 - r := by
          rw [h_abs_raw]
          ring
        have h_eps_eq : ε = ENNReal.ofReal ((1 - r + |m|) / r) := by
          dsimp [ε]
          rw [h_min, h_abs]
        have hu_nonneg : 0 ≤ 1/r - 1 := by
          have h_inv_gt_one : 1 < 1/r := one_lt_one_div hr hr_lt_one
          linarith
        have hb0_pos : 0 < r/2 := by linarith
        have h_le := AdversarialBco.Poly.PropG.gauss_affine_le 0 m (r/2) (1/r - 1) hb0_pos hu_nonneg (Sᶜ) hS_compl
        have h_set_eq : {z : ℝ | (0 : ℝ) + (1 + (1/r - 1)) * (r/2) * z ∈ Sᶜ} = {z : ℝ | ((1 : ℝ)/2) * z ∈ Sᶜ} := by
          ext z
          field_simp [ne_of_gt hr]
          ring
        rw [h_set_eq] at h_le
        have h_err_eq : ENNReal.ofReal ((1/r - 1) + |(0 : ℝ) - m| / (2 * (r/2))) = ENNReal.ofReal ((1 - r + |m|) / r) := by
          have hcalc : (1/r - 1) + |m| / r = (1 - r + |m|) / r := by
            field_simp [ne_of_gt hr]
          have hsimpl : 2 * (r/2) = r := by ring
          simp [hsimpl]
          simpa using congrArg ENNReal.ofReal hcalc
        rw [h_err_eq] at h_le
        -- Rewrite {z | (1/2)*z ∈ Sᶜ} as {z | 0 + (1/2)*z ∈ Sᶜ}
        have h_set_eq2 : {z : ℝ | ((1 : ℝ)/2) * z ∈ Sᶜ} = {z : ℝ | (0 : ℝ) + ((1 : ℝ)/2) * z ∈ Sᶜ} := by
          ext z; simp
        rw [h_set_eq2] at h_le
        have h_s_ne_zero : r / 2 ≠ 0 := by
          intro hzero
          have : r = 0 := by nlinarith
          linarith
        have h_half_ne_zero : (1/2 : ℝ) ≠ 0 := by norm_num
        have h_eq_LHS : gaussianReal 0 1 {z : ℝ | (0 : ℝ) + ((1 : ℝ)/2) * z ∈ Sᶜ} = ν Sᶜ := by
          rw [hν, AdversarialBco.Poly.PropG.gauss_affine_eq 0 (1/2) h_half_ne_zero (Sᶜ) hS_compl]
        have h_eq_RHS_base : gaussianReal 0 1 {z : ℝ | m + (r / 2) * z ∈ Sᶜ} = μ Sᶜ := by
          rw [hμ, AdversarialBco.Poly.PropG.gauss_affine_eq m (r / 2) h_s_ne_zero (Sᶜ) hS_compl]
        rw [h_eq_LHS, h_eq_RHS_base] at h_le
        rw [h_eps_eq]
        exact h_le
      exact h_second_compl_to_first h_second_compl
    exact And.intro h_first h_second

end AdversarialBco.Bit.Aux_tv_gauss

namespace AdversarialBco.Bit.Aux_lintegral_sub_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.lintegral_sub_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hgfin : ∫⁻ x, g x ∂μ ≠ ∞) (ε : ℝ≥0∞)
    (hε : ∀ S, MeasurableSet S → μ.withDensity f S ≤ μ.withDensity g S + ε) :
    ∫⁻ x, (f x - g x) ∂μ ≤ ε := by
  set S := {x | g x < f x} with hSdef
  have hS_meas : MeasurableSet S := measurableSet_lt hg hf
  have hS_le : ∀ x ∈ S, g x ≤ f x := by
    intro x hx
    rw [hSdef, Set.mem_ofPred_eq] at hx
    exact hx.le
  have hgfin_S : ∫⁻ x in S, g x ∂μ ≠ ∞ := by
    intro h
    apply hgfin
    have hle : ∫⁻ x in S, g x ∂μ ≤ ∫⁻ x, g x ∂μ := setLIntegral_le_lintegral S g
    rw [h] at hle
    exact top_unique hle
  have h_le_ae : g ≤ᵐ[μ.restrict S] f :=
    ae_restrict_of_forall_mem hS_meas hS_le
  have h_sub_S : ∫⁻ x in S, (f x - g x) ∂μ = (∫⁻ x in S, f x ∂μ) - (∫⁻ x in S, g x ∂μ) := by
    calc
      ∫⁻ x in S, (f x - g x) ∂μ = ∫⁻ x, (f x - g x) ∂(μ.restrict S) := rfl
      _ = (∫⁻ x, f x ∂(μ.restrict S)) - (∫⁻ x, g x ∂(μ.restrict S)) :=
        lintegral_sub hg hgfin_S h_le_ae
      _ = (∫⁻ x in S, f x ∂μ) - (∫⁻ x in S, g x ∂μ) := rfl
  have h_compl_zero : ∫⁻ x in Sᶜ, (f x - g x) ∂μ = 0 := by
    calc
      ∫⁻ x in Sᶜ, (f x - g x) ∂μ = ∫⁻ x in Sᶜ, 0 ∂μ :=
        setLIntegral_congr_fun hS_meas.compl (by
          intro x hx
          rw [Set.mem_compl_iff] at hx
          rw [hSdef, Set.mem_ofPred_eq] at hx
          have hle : f x ≤ g x := by simpa using hx
          exact tsub_eq_zero_of_le hle)
      _ = 0 := by simp
  have h_total : ∫⁻ x, (f x - g x) ∂μ = (∫⁻ x in S, f x ∂μ) - (∫⁻ x in S, g x ∂μ) := by
    calc
      ∫⁻ x, (f x - g x) ∂μ = (∫⁻ x in S, (f x - g x) ∂μ) + (∫⁻ x in Sᶜ, (f x - g x) ∂μ) := by
        rw [lintegral_add_compl _ hS_meas]
      _ = (∫⁻ x in S, (f x - g x) ∂μ) + 0 := by rw [h_compl_zero]
      _ = ∫⁻ x in S, (f x - g x) ∂μ := by simp
      _ = (∫⁻ x in S, f x ∂μ) - (∫⁻ x in S, g x ∂μ) := h_sub_S
  have h_density_f : μ.withDensity f S = ∫⁻ x in S, f x ∂μ := withDensity_apply f hS_meas
  have h_density_g : μ.withDensity g S = ∫⁻ x in S, g x ∂μ := withDensity_apply g hS_meas
  have h_ineq : ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, g x ∂μ + ε := by
    calc
      ∫⁻ x in S, f x ∂μ = μ.withDensity f S := by rw [h_density_f]
      _ ≤ μ.withDensity g S + ε := hε S hS_meas
      _ = (∫⁻ x in S, g x ∂μ) + ε := by rw [h_density_g]
  rw [h_total]
  -- Now we need: (∫⁻_S f) - (∫⁻_S g) ≤ ε
  -- From h_ineq: ∫⁻_S f ≤ ∫⁻_S g + ε
  -- Using tsub_le_iff_left: a - b ≤ c ↔ a ≤ b + c
  rw [tsub_le_iff_left]
  exact h_ineq

end AdversarialBco.Bit.Aux_lintegral_sub_le

