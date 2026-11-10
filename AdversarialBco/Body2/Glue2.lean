/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Inner
public import AdversarialBco.Gauss.Concentration
public import AdversarialBco.StatementBody

@[expose] public section

/-!
# The projection, the extension and the concentration of the distance in Proposition 2.2

The nearest-point projection onto a convex set is `1`-Lipschitz toward the set, the Lipschitz extension `f̃` is at
least `f ∘ pr`, a positive definite `S` has `‖S‖ > 0`, and the distance to `J` under `N(b, S^2)` concentrates with
the exponent `2/π^2`, its second moment from the tail bound, and the integral under the diluted law.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.proj_nonexp {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJv : Convex ℝ J) (x p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ J) (hpx : dist x p = Metric.infDist x J) (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ J) : dist p y ≤ dist x y := by
  have h_inner : ∀ w ∈ J, inner ℝ (x - p) (w - p) ≤ 0 := by
    have h_eq : ‖x - p‖ = ⨅ (w : J), ‖x - (w : EuclideanSpace ℝ (Fin d))‖ := by
      rw [dist_eq_norm] at hpx
      rw [Metric.infDist_eq_iInf] at hpx
      simpa [dist_eq_norm] using hpx
    have h := (norm_eq_iInf_iff_real_inner_le_zero hJv hp).mp h_eq
    exact h
  have h_inner_y : inner ℝ (x - p) (y - p) ≤ 0 := h_inner y hy
  have h_sq : ‖x - y‖ ^ 2 ≥ ‖y - p‖ ^ 2 := by
    calc
      ‖x - y‖ ^ 2 = ‖(x - p) - (y - p)‖ ^ 2 := by simp
      _ = ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by rw [norm_sub_sq_real]
      _ ≥ ‖y - p‖ ^ 2 := by
        have : 0 ≤ ‖x - p‖ ^ 2 := pow_two_nonneg _
        nlinarith
  rw [dist_comm p y, dist_eq_norm, dist_eq_norm]
  have h_nonneg_xy : 0 ≤ ‖x - y‖ := norm_nonneg _
  have h_nonneg_yp : 0 ≤ ‖y - p‖ := norm_nonneg _
  have h_sq' : ‖y - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := h_sq
  exact ((sq_le_sq₀ h_nonneg_yp h_nonneg_xy).mp h_sq')
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.lipExt_ge {F : Type*} [NormedAddCommGroup F] (J : Set F) (f : F → ℝ) (n : ℝ) (hn : 0 ≤ n) (hfl : ∀ x ∈ J, ∀ y ∈ J, |f x - f y| ≤ n * dist x y) (x p : F) (hp : p ∈ J) (hne : ∀ y ∈ J, dist p y ≤ dist x y) : f p ≤ AdversarialBco.lipExt J f n x := by
  unfold AdversarialBco.lipExt
  refine le_csInf ?_ ?_
  · refine ⟨f p + n * dist x p, p, hp, ?_⟩
    rfl
  · intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h_abs := hfl p hp y hy
    rcases (abs_le.mp h_abs) with ⟨_, hle⟩
    have hdist : n * dist p y ≤ n * dist x y :=
      mul_le_mul_of_nonneg_left (hne y hy) hn
    linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.spd_norm_pos {d : ℕ} (hd : 1 ≤ d) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : AdversarialBco.BodySpec.IsSPD S) : 0 < ‖S‖ := by
  set v := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with hv_def
  have hv : v ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hv_def, PiLp.norm_single (p := 2)]
    norm_num
  have hpos : 0 < ⟪S v, v⟫ := hS.2 v hv
  have hS_ne_zero : S ≠ 0 := by
    intro hSzero
    have hzero : ⟪S v, v⟫ = 0 := by
      simp [hSzero, inner_zero_left]
    linarith
  exact norm_pos_iff.mpr hS_ne_zero
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.conc_r {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : 0 < ‖S‖) (t : ℝ) (ht : 0 ≤ t) : (AdversarialBco.BodySpec.gaussLaw b S).real {x | (∫ y, Metric.infDist y J ∂AdversarialBco.BodySpec.gaussLaw b S) + t ≤ Metric.infDist x J} ≤ Real.exp (-t ^ 2 / (2 * (Real.pi / 2 * ‖S‖) ^ 2)) := by
  have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin d) => Metric.infDist x J) :=
    Metric.lipschitz_infDist_pt J
  have h_gauss := (AdversarialBco.Gauss.gaussConcAt d d b S (fun x => Metric.infDist x J) 1 h_lip).2 t ht
  have h_eq : AdversarialBco.BodySpec.gaussLaw b S = AdversarialBco.Gauss.cloud b S := rfl
  have h_exp_eq : -(((2 : ℝ) / Real.pi ^ 2) * t ^ 2) / (‖S‖ ^ 2) = -t ^ 2 / (2 * (Real.pi / 2 * ‖S‖) ^ 2) := by
    calc
      -(((2 : ℝ) / Real.pi ^ 2) * t ^ 2) / (‖S‖ ^ 2) = (-(2 * t ^ 2)) / (Real.pi ^ 2 * ‖S‖ ^ 2) := by ring
      _ = -t ^ 2 / ((Real.pi ^ 2 / 2) * ‖S‖ ^ 2) := by ring
      _ = -t ^ 2 / (2 * (Real.pi / 2 * ‖S‖) ^ 2) := by ring
  simpa [h_eq, h_exp_eq] using h_gauss
end

/-- The second moment of a nonnegative variable from a sub-Gaussian upper tail around its mean, cut at `t_0`. -/
theorem AdversarialBco.Body2.tail_sq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hXi : Integrable X ν)
    (_hX2 : Integrable (fun ω => X ω ^ 2) ν) (σ : ℝ) (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t → ν.real {ω | (∫ y, X y ∂ν) + t ≤ X ω} ≤ Real.exp (-t ^ 2 / (2 * σ ^ 2)))
    (t0 : ℝ) (ht0 : 0 ≤ t0) :
    ∫ ω, X ω ^ 2 ∂ν ≤ 2 * ((∫ ω, X ω ∂ν) + t0) * (∫ ω, X ω ∂ν) + 2 * σ ^ 2 * Real.exp (-t0 ^ 2 / (2 * σ ^ 2)) :=
  AdversarialBco.integral_sq_le_of_tail ν X hXm hX0 hXi (∫ ω, X ω ∂ν) σ t0 le_rfl hσ ht0 htail

/-- The integral under the diluted law of a continuous function integrable under `N(b, S^2)`, in the coordinates of the
standard Gaussian. -/
theorem AdversarialBco.Body2.diluted_integral {d : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (bstar b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (hfi : Integrable (fun z => f (b + S z)) (stdGaussian (EuclideanSpace ℝ (Fin d)))) : IsProbabilityMeasure (AdversarialBco.BodySpec.dilutedLaw q bstar b S) ∧ Integrable f (AdversarialBco.BodySpec.dilutedLaw q bstar b S) ∧ ∫ x, f x ∂(AdversarialBco.BodySpec.dilutedLaw q bstar b S) = (1 - q) * f bstar + q / 2 * f b + q / 2 * ∫ z, f (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hm : AEMeasurable (fun z : EuclideanSpace ℝ (Fin d) => b + S z) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    fun_prop
  have : IsProbabilityMeasure (AdversarialBco.BodySpec.gaussLaw b S) :=
    inferInstanceAs (IsProbabilityMeasure (AdversarialBco.Gauss.cloud b S))
  have hfi' : Integrable f (AdversarialBco.BodySpec.gaussLaw b S) :=
    (integrable_map_measure hf.aestronglyMeasurable hm).2 hfi
  obtain ⟨h1, h2, h3⟩ := AdversarialBco.Body.integral_diluted bstar b (AdversarialBco.BodySpec.gaussLaw b S) q hq0 hq1 f hfi'
  refine ⟨h1, h2, ?_⟩
  rw [AdversarialBco.BodySpec.dilutedLaw, h3, AdversarialBco.BodySpec.gaussLaw, integral_map hm hf.aestronglyMeasurable]
