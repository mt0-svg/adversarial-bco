/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Transfer tools for Proposition 2.2

`ext_bounds`, `integral_diluted` and `variance_transfer`, for the transfer half of Proposition 2.2
(`AdversarialBco.Body.Interface`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body.ext_bounds {F : Type*} [NormedAddCommGroup F] (J : Set F) (f : F → ℝ) (n P : ℝ)
    (hn : 0 ≤ n) (hfl : ∀ x ∈ J, ∀ y ∈ J, |f x - f y| ≤ n * dist x y) (x p : F) (hp : p ∈ J)
    (hd : dist x p = Metric.infDist x J) :
    f p + (P - n) * Metric.infDist x J ≤ AdversarialBco.lipExt J f n x + P * Metric.infDist x J ∧
      AdversarialBco.lipExt J f n x + P * Metric.infDist x J ≤ f p + (n + P) * Metric.infDist x J := by
  set δ := Metric.infDist x J with hδ
  have hδ_eq : δ = dist x p := by rw [hδ, hd]
  have hS_nonempty : ((fun y => f y + n * dist x y) '' J).Nonempty := by
    refine ⟨f p + n * dist x p, p, hp, rfl⟩
  have h_lower_bound : ∀ y ∈ J, f p - n * δ ≤ f y + n * dist x y := by
    intro y hy
    have h_abs := hfl p hp y hy
    rcases (abs_le.mp h_abs) with ⟨h_left, h_right⟩
    have h_fy_ge : f p - n * dist p y ≤ f y := by linarith
    have h_triangle : dist p y ≤ dist p x + dist x y := dist_triangle _ _ _
    have h_dist_mul : n * dist p y ≤ n * (dist p x + dist x y) := by
      nlinarith
    have h_combined : f p - n * (dist p x + dist x y) ≤ f y := by
      linarith
    rw [dist_comm p x, ← hδ_eq] at h_combined
    linarith
  have h_bdd_below : BddBelow ((fun y => f y + n * dist x y) '' J) := by
    refine ⟨f p - n * δ, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact h_lower_bound y hy
  have h_upper : sInf ((fun y => f y + n * dist x y) '' J) ≤ f p + n * δ := by
    apply csInf_le h_bdd_below
    refine ⟨p, hp, ?_⟩
    rw [hδ_eq]
  have h_lower : f p - n * δ ≤ sInf ((fun y => f y + n * dist x y) '' J) := by
    apply le_csInf hS_nonempty
    rintro z ⟨y, hy, rfl⟩
    exact h_lower_bound y hy
  constructor
  · have h : f p + (P - n) * δ = (f p - n * δ) + P * δ := by ring
    rw [h]
    dsimp [AdversarialBco.lipExt] at *
    linarith
  · have h : f p + (n + P) * δ = (f p + n * δ) + P * δ := by ring
    rw [h]
    dsimp [AdversarialBco.lipExt] at *
    linarith


theorem AdversarialBco.Body.integral_diluted {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x0 x1 : X) (ν : Measure X) [IsProbabilityMeasure ν] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : X → ℝ)
    (hf : Integrable f ν) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
        ENNReal.ofReal (q / 2) • ν) ∧
      Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
        ENNReal.ofReal (q / 2) • ν) ∧
      ∫ x, f x ∂(ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
        ENNReal.ofReal (q / 2) • ν) = (1 - q) * f x0 + q / 2 * f x1 + q / 2 * ∫ x, f x ∂ν := by
  have h1q_nonneg : 0 ≤ 1 - q := by linarith
  have hq2_nonneg : 0 ≤ q / 2 := by nlinarith
  have hsum : (1 - q) + q / 2 + q / 2 = 1 := by ring
  have h_ofReal_add1 : ENNReal.ofReal ((1 - q) + q / 2) = ENNReal.ofReal (1 - q) + ENNReal.ofReal (q / 2) :=
    ENNReal.ofReal_add h1q_nonneg hq2_nonneg
  have h_ofReal_add2 : ENNReal.ofReal (((1 - q) + q / 2) + q / 2) =
      ENNReal.ofReal ((1 - q) + q / 2) + ENNReal.ofReal (q / 2) :=
    ENNReal.ofReal_add (by nlinarith) hq2_nonneg
  have h_ofReal_total : ENNReal.ofReal (1 - q) + ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) = 1 := by
    calc
      ENNReal.ofReal (1 - q) + ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) =
          (ENNReal.ofReal (1 - q) + ENNReal.ofReal (q / 2)) + ENNReal.ofReal (q / 2) := by ring
      _ = ENNReal.ofReal ((1 - q) + q / 2) + ENNReal.ofReal (q / 2) := by rw [h_ofReal_add1]
      _ = ENNReal.ofReal (((1 - q) + q / 2) + q / 2) := by rw [h_ofReal_add2]
      _ = ENNReal.ofReal 1 := by rw [hsum]
      _ = 1 := ENNReal.ofReal_one
  have hprob : IsProbabilityMeasure (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
      ENNReal.ofReal (q / 2) • ν) := by
    refine ⟨?h⟩
    calc
      (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
        ENNReal.ofReal (q / 2) • ν) Set.univ =
          (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1) Set.univ +
          (ENNReal.ofReal (q / 2) • ν) Set.univ := by
        rw [Measure.add_apply]
      _ = (ENNReal.ofReal (1 - q) • Measure.dirac x0) Set.univ + (ENNReal.ofReal (q / 2) • Measure.dirac x1) Set.univ +
          (ENNReal.ofReal (q / 2) • ν) Set.univ := by
        rw [Measure.add_apply]
      _ = ENNReal.ofReal (1 - q) * (Measure.dirac x0 Set.univ) + ENNReal.ofReal (q / 2) * (Measure.dirac x1 Set.univ) +
          ENNReal.ofReal (q / 2) * (ν Set.univ) := by
        simp [Measure.smul_apply]
      _ = ENNReal.ofReal (1 - q) * 1 + ENNReal.ofReal (q / 2) * 1 + ENNReal.ofReal (q / 2) * 1 := by
        simp [Measure.dirac_apply_of_mem (Set.mem_univ _), measure_univ]
      _ = ENNReal.ofReal (1 - q) + ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) := by ring
      _ = 1 := h_ofReal_total
  have hint_dirac0 : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac x0) := by
    by_cases hc0 : ENNReal.ofReal (1 - q) = 0
    · rw [hc0, zero_smul]
      exact MeasureTheory.integrable_zero_measure
    · have hc_top : ENNReal.ofReal (1 - q) ≠ ⊤ := by
        simp
      rw [MeasureTheory.integrable_smul_measure (hc0) (hc_top)]
      -- now need Integrable f (dirac x0)
      have h_norm : ‖f x0‖ₑ < ⊤ := by
        simp
      exact MeasureTheory.integrable_dirac h_norm
  have hint_dirac1 : Integrable f (ENNReal.ofReal (q / 2) • Measure.dirac x1) := by
    by_cases hc0 : ENNReal.ofReal (q / 2) = 0
    · rw [hc0, zero_smul]
      exact MeasureTheory.integrable_zero_measure
    · have hc_top : ENNReal.ofReal (q / 2) ≠ ⊤ := by
        simp
      rw [MeasureTheory.integrable_smul_measure (hc0) (hc_top)]
      have h_norm : ‖f x1‖ₑ < ⊤ := by
        simp
      exact MeasureTheory.integrable_dirac h_norm
  have hint_ν : Integrable f (ENNReal.ofReal (q / 2) • ν) := by
    by_cases hc0 : ENNReal.ofReal (q / 2) = 0
    · rw [hc0, zero_smul]
      exact MeasureTheory.integrable_zero_measure
    · have hc_top : ENNReal.ofReal (q / 2) ≠ ⊤ := by
        simp
      rw [MeasureTheory.integrable_smul_measure (hc0) (hc_top)]
      exact hf
  have hint : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
      ENNReal.ofReal (q / 2) • ν) := by
    -- combine: first add dirac0 and dirac1, then add ν
    have h12 : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1) :=
      MeasureTheory.Integrable.add_measure hint_dirac0 hint_dirac1
    exact MeasureTheory.Integrable.add_measure h12 hint_ν
  have hint_total : Integrable f (ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
      ENNReal.ofReal (q / 2) • ν) := hint
  have hintegral : ∫ x, f x ∂(ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
      ENNReal.ofReal (q / 2) • ν) = (1 - q) * f x0 + q / 2 * f x1 + q / 2 * ∫ x, f x ∂ν := by
    calc
      ∫ x, f x ∂(ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1 +
        ENNReal.ofReal (q / 2) • ν) =
          ∫ x, f x ∂(ENNReal.ofReal (1 - q) • Measure.dirac x0 + ENNReal.ofReal (q / 2) • Measure.dirac x1) +
          ∫ x, f x ∂(ENNReal.ofReal (q / 2) • ν) := by
        rw [MeasureTheory.integral_add_measure ?_ hint_ν]
        -- need Integrable f (ENNReal.ofReal (1 - q) • dirac x0 + ENNReal.ofReal (q / 2) • dirac x1)
        exact MeasureTheory.Integrable.add_measure hint_dirac0 hint_dirac1
      _ = (∫ x, f x ∂(ENNReal.ofReal (1 - q) • Measure.dirac x0) + ∫ x, f x ∂(ENNReal.ofReal (q / 2) • Measure.dirac x1)) +
          ∫ x, f x ∂(ENNReal.ofReal (q / 2) • ν) := by
        rw [MeasureTheory.integral_add_measure hint_dirac0 hint_dirac1]
      _ = ((ENNReal.ofReal (1 - q)).toReal • ∫ x, f x ∂(Measure.dirac x0) + (ENNReal.ofReal (q / 2)).toReal • ∫ x, f x ∂(Measure.dirac x1)) +
          (ENNReal.ofReal (q / 2)).toReal • ∫ x, f x ∂ν := by
        simp [MeasureTheory.integral_smul_measure]
      _ = ((ENNReal.ofReal (1 - q)).toReal • f x0 + (ENNReal.ofReal (q / 2)).toReal • f x1) + (ENNReal.ofReal (q / 2)).toReal • ∫ x, f x ∂ν := by
        simp [MeasureTheory.integral_dirac]
      _ = ((1 - q) * f x0 + (q / 2) * f x1) + (q / 2) * ∫ x, f x ∂ν := by
        have h1 : (ENNReal.ofReal (1 - q)).toReal = 1 - q := ENNReal.toReal_ofReal h1q_nonneg
        have h2 : (ENNReal.ofReal (q / 2)).toReal = q / 2 := ENNReal.toReal_ofReal hq2_nonneg
        simp [h1, h2, smul_eq_mul]
      _ = (1 - q) * f x0 + q / 2 * f x1 + q / 2 * ∫ x, f x ∂ν := by ring
  exact ⟨hprob, hint_total, hintegral⟩


theorem AdversarialBco.Body.variance_transfer (k : ℕ) (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (a b : Fin k → ℝ) (e : ℝ) (h : ∀ c, |a c - b c| ≤ e) :
    ∑ c, w c * (a c - ∑ c', w c' * a c') ^ 2 ≤ 2 * ∑ c, w c * (b c - ∑ c', w c' * b c') ^ 2 + 8 * e ^ 2 := by
  set δ := fun c => a c - b c with hδ
  set abar := ∑ c' : Fin k, w c' * a c' with habar
  set bbar := ∑ c' : Fin k, w c' * b c' with hbbar
  set δbar := ∑ c' : Fin k, w c' * δ c' with hδbar
  have hδbar_eq : δbar = abar - bbar := by
    dsimp [δbar, abar, bbar, δ]
    simp [Finset.sum_sub_distrib, mul_sub]
  have h_identity (c : Fin k) : a c - abar = (b c - bbar) + (δ c - δbar) := by
    dsimp [δ, abar, bbar, δbar]
    simp [Finset.sum_sub_distrib, mul_sub]
    ring
  have h_sq_bound (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have h_nonneg : (x - y) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  have h_abs_δbar : |δbar| ≤ e := by
    calc
      |δbar| = |∑ c' : Fin k, w c' * δ c'| := rfl
      _ ≤ ∑ c' : Fin k, |w c' * δ c'| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c' : Fin k, |w c'| * |δ c'| := by simp [abs_mul]
      _ = ∑ c' : Fin k, w c' * |δ c'| := by
        refine Finset.sum_congr rfl fun c' hc' => ?_
        rw [abs_of_nonneg (hw c')]
      _ ≤ ∑ c' : Fin k, w c' * e :=
        Finset.sum_le_sum fun c' _ => mul_le_mul_of_nonneg_left (h c') (hw c')
      _ = (∑ c' : Fin k, w c') * e := by simp [Finset.sum_mul]
      _ = 1 * e := by rw [hw1]
      _ = e := by ring
  have h_abs_diff (c : Fin k) : |δ c - δbar| ≤ 2 * e := by
    calc
      |δ c - δbar| ≤ |δ c| + |δbar| := abs_sub _ _
      _ ≤ e + e := by
        nlinarith [h c, h_abs_δbar]
      _ = 2 * e := by ring
  have h_sq_diff (c : Fin k) : (δ c - δbar) ^ 2 ≤ 4 * e ^ 2 := by
    have h_abs := h_abs_diff c
    have h_bound : -(2 * e) ≤ δ c - δbar ∧ δ c - δbar ≤ 2 * e := by
      exact abs_le.mp h_abs
    rcases h_bound with ⟨hl, hr⟩
    nlinarith
  calc
    ∑ c : Fin k, w c * (a c - ∑ c' : Fin k, w c' * a c') ^ 2
        = ∑ c : Fin k, w c * (a c - abar) ^ 2 := by simp [abar]
    _ = ∑ c : Fin k, w c * ((b c - bbar) + (δ c - δbar)) ^ 2 := by
      simp [h_identity]
    _ ≤ ∑ c : Fin k, w c * (2 * ((b c - bbar) ^ 2 + (δ c - δbar) ^ 2)) := by
      refine Finset.sum_le_sum fun c hc => ?_
      have h_sq := h_sq_bound (b c - bbar) (δ c - δbar)
      exact mul_le_mul_of_nonneg_left h_sq (hw c)
    _ = 2 * ∑ c : Fin k, w c * ((b c - bbar) ^ 2 + (δ c - δbar) ^ 2) := by
      calc
        ∑ c : Fin k, w c * (2 * ((b c - bbar) ^ 2 + (δ c - δbar) ^ 2))
            = ∑ c : Fin k, 2 * (w c * ((b c - bbar) ^ 2 + (δ c - δbar) ^ 2)) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              ring
        _ = 2 * ∑ c : Fin k, w c * ((b c - bbar) ^ 2 + (δ c - δbar) ^ 2) := by rw [Finset.mul_sum]
    _ = 2 * (∑ c : Fin k, w c * (b c - bbar) ^ 2 + ∑ c : Fin k, w c * (δ c - δbar) ^ 2) := by
      simp [Finset.sum_add_distrib, mul_add]
    _ = 2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 2 * ∑ c : Fin k, w c * (δ c - δbar) ^ 2 := by ring
    _ ≤ 2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 2 * ∑ c : Fin k, w c * (4 * e ^ 2) := by
      have h_sum : ∑ c : Fin k, w c * (δ c - δbar) ^ 2 ≤ ∑ c : Fin k, w c * (4 * e ^ 2) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h_sq_diff c) (hw c)
      gcongr
    _ = 2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 8 * e ^ 2 := by
      have hsum : ∑ c : Fin k, w c * (4 * e ^ 2) = 4 * e ^ 2 := by
        calc
          ∑ c : Fin k, w c * (4 * e ^ 2) = (∑ c : Fin k, w c) * (4 * e ^ 2) := by simp [Finset.sum_mul]
          _ = 1 * (4 * e ^ 2) := by rw [hw1]
          _ = 4 * e ^ 2 := by ring
      calc
        2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 2 * ∑ c : Fin k, w c * (4 * e ^ 2)
            = 2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 2 * (4 * e ^ 2) := by rw [hsum]
        _ = 2 * ∑ c : Fin k, w c * (b c - bbar) ^ 2 + 8 * e ^ 2 := by ring
    _ = 2 * ∑ c : Fin k, w c * (b c - ∑ c' : Fin k, w c' * b c') ^ 2 + 8 * e ^ 2 := by simp [bbar]
