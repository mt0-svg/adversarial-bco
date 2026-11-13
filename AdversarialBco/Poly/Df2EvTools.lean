/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Generic tools of the event budgets G and Y

Statements on their own data, no definition of the package:

* the Hessian of a convex function is positive semidefinite at every point, with Mathlib's junk values
  (`fderiv` is `0` where the function is not differentiable), so no `C²` hypothesis is asked;
* the extension, `pip(x) f(x/pip(x)) + c (pip(x) - 1)`, is convex for every coefficient
  `c ≥ (1 - ε)/ε` ((G4) to (G6));
* the Gaussian comparison behind lem:ons:mink: `E F(A g) ≤ E F(s g)` for `F` convex of linear growth and
  `‖A‖ ≤ s` (a Gaussian split and Jensen);
* the freezing bound: an event of `(z, x)` with `z` measurable in `𝒢` and `x` independent of `𝒢` has probability at
  most the supremum over `z` of the probability of its section.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## The Hessian of a convex function -/

/-- The gradient of a convex function is monotone between two points of differentiability. -/
theorem fderiv_mono_of_convex (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    0 ≤ (fderiv ℝ f x - fderiv ℝ f y) (x - y) := by
  have hfx : f y ≥ f x + (fderiv ℝ f x) (y - x) := by
    let φ := f ∘ (AffineMap.lineMap x y : ℝ → EuclideanSpace ℝ (Fin d))
    have hφ_conv : ConvexOn ℝ Set.univ φ :=
      hf.comp_affineMap (AffineMap.lineMap x y)
    have hφ_deriv : HasDerivAt φ ((fderiv ℝ f x) (y - x)) 0 := by
      have h_linMap : HasDerivAt (AffineMap.lineMap x y : ℝ → EuclideanSpace ℝ (Fin d)) (y - x) 0 :=
        AffineMap.hasDerivAt_lineMap
      have h_fderiv : HasFDerivAt f (fderiv ℝ f x) x := hx.hasFDerivAt
      have h_comp := h_fderiv.comp_hasDerivAt_of_eq 0 h_linMap (by simp)
      simpa [φ, Function.comp_def] using h_comp
    have h_slope : (fderiv ℝ f x) (y - x) ≤ slope φ 0 1 :=
      hφ_conv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hφ_deriv
    have h_slope_eq : slope φ 0 1 = f y - f x := by
      simp [φ, slope, Function.comp_def, AffineMap.lineMap_apply]
    linarith
  have hfy : f x ≥ f y + (fderiv ℝ f y) (x - y) := by
    let ψ := f ∘ (AffineMap.lineMap y x : ℝ → EuclideanSpace ℝ (Fin d))
    have hψ_conv : ConvexOn ℝ Set.univ ψ :=
      hf.comp_affineMap (AffineMap.lineMap y x)
    have hψ_deriv : HasDerivAt ψ ((fderiv ℝ f y) (x - y)) 0 := by
      have h_linMap : HasDerivAt (AffineMap.lineMap y x : ℝ → EuclideanSpace ℝ (Fin d)) (x - y) 0 :=
        AffineMap.hasDerivAt_lineMap
      have h_fderiv : HasFDerivAt f (fderiv ℝ f y) y := hy.hasFDerivAt
      have h_comp := h_fderiv.comp_hasDerivAt_of_eq 0 h_linMap (by simp)
      simpa [ψ, Function.comp_def] using h_comp
    have h_slope : (fderiv ℝ f y) (x - y) ≤ slope ψ 0 1 :=
      hψ_conv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hψ_deriv
    have h_slope_eq : slope ψ 0 1 = f x - f y := by
      simp [ψ, slope, Function.comp_def, AffineMap.lineMap_apply]
    linarith
  have h_sum : (fderiv ℝ f x - fderiv ℝ f y) (y - x) ≤ 0 := by
    have h := add_le_add hfx hfy
    have h_neg_y : (fderiv ℝ f y) (x - y) = -((fderiv ℝ f y) (y - x)) := by simp
    have h' : (fderiv ℝ f x) (y - x) + (fderiv ℝ f y) (x - y) ≤ 0 := by linarith
    rw [h_neg_y] at h'
    have h'' : (fderiv ℝ f x) (y - x) - (fderiv ℝ f y) (y - x) ≤ 0 := by linarith
    simpa [sub_apply] using h''
  have h_neg : (fderiv ℝ f x - fderiv ℝ f y) (x - y) = -((fderiv ℝ f x - fderiv ℝ f y) (y - x)) := by
    calc
      (fderiv ℝ f x - fderiv ℝ f y) (x - y) = (fderiv ℝ f x - fderiv ℝ f y) x - (fderiv ℝ f x - fderiv ℝ f y) y := by
        rw [ContinuousLinearMap.map_sub]
      _ = ((fderiv ℝ f x) x - (fderiv ℝ f y) x) - ((fderiv ℝ f x) y - (fderiv ℝ f y) y) := by
        simp
      _ = -(((fderiv ℝ f x) y - (fderiv ℝ f y) y) - ((fderiv ℝ f x) x - (fderiv ℝ f y) x)) := by ring
      _ = -((fderiv ℝ f x - fderiv ℝ f y) y - (fderiv ℝ f x - fderiv ℝ f y) x) := by
        simp
      _ = -((fderiv ℝ f x - fderiv ℝ f y) (y - x)) := by
        rw [ContinuousLinearMap.map_sub]
  rw [h_neg]
  linarith

/-- A convex function on `ℝ^d` has a point of differentiability in every ball. -/
theorem exists_differentiableAt_near_of_convex (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r) : ∃ y, dist y z < r ∧ DifferentiableAt ℝ f y := by
  have h_loc := hf.locallyLipschitz
  rcases h_loc z with ⟨K, t, ht_mem, ht_lip⟩
  -- ht_mem : t ∈ nhds z, ht_lip : LipschitzOnWith K f t
  rw [Metric.mem_nhds_iff] at ht_mem
  rcases ht_mem with ⟨ε, hε_pos, hε_sub⟩
  -- hε_sub : Metric.ball z ε ⊆ t
  set r' := min (ε / 2) (r / 2) with hr'_def
  have hr'_pos : 0 < r' := by
    refine lt_min_iff.mpr ⟨by linarith, by linarith⟩
  have hr'_lt_r : r' < r := by
    calc
      r' ≤ r / 2 := min_le_right _ _
      _ < r := by linarith
  have hr'_lt_ε : r' < ε := by
    calc
      r' ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  have h_ball_sub_t : Metric.ball z r' ⊆ t := by
    intro x hx
    apply hε_sub
    have hx_dist : dist x z < ε := by
      calc
        dist x z < r' := hx
        _ < ε := hr'_lt_ε
    exact hx_dist
  have h_lip_ball : LipschitzOnWith K f (Metric.ball z r') :=
    ht_lip.mono h_ball_sub_t
  have h_meas_ball : MeasurableSet (Metric.ball z r') := measurableSet_ball
  have h_ae_diff : ∀ᵐ x ∂ (volume.restrict (Metric.ball z r')), DifferentiableWithinAt ℝ f (Metric.ball z r') x :=
    h_lip_ball.ae_differentiableWithinAt h_meas_ball
  have h_ball_pos : volume (Metric.ball z r') > 0 := by
    apply Metric.measure_ball_pos volume z hr'_pos
  have h_ball_ne_zero : volume (Metric.ball z r') ≠ 0 := ne_of_gt h_ball_pos
  have h_exists_diff : ∃ y ∈ Metric.ball z r', DifferentiableWithinAt ℝ f (Metric.ball z r') y := by
    rw [MeasureTheory.ae_iff] at h_ae_diff
    by_contra! hne
    -- hne : ∀ y ∈ Metric.ball z r', ¬ DifferentiableWithinAt ℝ f (Metric.ball z r') y
    have h_sub : Metric.ball z r' ⊆ {x | ¬ DifferentiableWithinAt ℝ f (Metric.ball z r') x} := by
      intro x hx
      exact hne x hx
    have h_restrict_nonzero : (volume.restrict (Metric.ball z r')) (Metric.ball z r') ≠ 0 := by
      rw [Measure.restrict_apply_self]
      exact h_ball_ne_zero
    have h_zero : (volume.restrict (Metric.ball z r')) (Metric.ball z r') = 0 := by
      apply le_antisymm ?_ (by simp)
      calc
        (volume.restrict (Metric.ball z r')) (Metric.ball z r') ≤
            (volume.restrict (Metric.ball z r')) {x | ¬ DifferentiableWithinAt ℝ f (Metric.ball z r') x} :=
          measure_mono h_sub
        _ = 0 := h_ae_diff
    exact h_restrict_nonzero h_zero
  rcases h_exists_diff with ⟨y, hy_ball, hy_diff⟩
  have hy_diff_at : DifferentiableAt ℝ f y := by
    apply hy_diff.differentiableAt
    exact Metric.isOpen_ball.mem_nhds hy_ball
  refine ⟨y, ?_, hy_diff_at⟩
  have : dist y z < r' := hy_ball
  linarith

/-- The gradient of a convex function against the derivative `L` of `f'` at `z`: for every `ε > 0` there is `δ > 0`
with `0 ≤ L (y - y') (y - y') + ε (‖y - z‖ + ‖y' - z‖) ‖y - y'‖` at the points `y`, `y'` of differentiability of `f`
within `δ` of `z`. -/
theorem fderiv_quad_lower (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (z : EuclideanSpace ℝ (Fin d)) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hL : HasFDerivAt (fderiv ℝ f) L z) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y y' : EuclideanSpace ℝ (Fin d), DifferentiableAt ℝ f y → DifferentiableAt ℝ f y' →
      ‖y - z‖ < δ → ‖y' - z‖ < δ → 0 ≤ L (y - y') (y - y') + ε * (‖y - z‖ + ‖y' - z‖) * ‖y - y'‖ := by
  set G := fderiv ℝ f with hG
  have hG_diff : HasFDerivAt G L z := hL
  have hisLittleO : (fun w => G w - G z - L (w - z)) =o[nhds z] (fun w => w - z) :=
    hG_diff.isLittleO
  have hbound : ∀ᶠ w in nhds z, ‖G w - G z - L (w - z)‖ ≤ ε * ‖w - z‖ :=
    hisLittleO.def hε
  rcases Metric.mem_nhds_iff.mp hbound with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro y y' hy hy' hylt hylt'
  have hmono : 0 ≤ (G y - G y') (y - y') :=
    fderiv_mono_of_convex f hf y y' hy hy'
  have hδy : ‖G y - G z - L (y - z)‖ ≤ ε * ‖y - z‖ := by
    have : y ∈ Metric.ball z δ := Metric.mem_ball.mpr hylt
    have hmem := hδ this
    simpa using hmem
  have hδy' : ‖G y' - G z - L (y' - z)‖ ≤ ε * ‖y' - z‖ := by
    have : y' ∈ Metric.ball z δ := Metric.mem_ball.mpr hylt'
    have hmem := hδ this
    simpa using hmem
  have hsplit : G y - G y' = L (y - y') + (G y - G z - L (y - z)) - (G y' - G z - L (y' - z)) := by
    calc
      G y - G y' = (G y - G z) - (G y' - G z) := by abel
      _ = ((G y - G z) - L (y - z) + L (y - z)) - ((G y' - G z) - L (y' - z) + L (y' - z)) := by abel
      _ = ((G y - G z - L (y - z)) + L (y - z)) - ((G y' - G z - L (y' - z)) + L (y' - z)) := by abel
      _ = (L (y - z) - L (y' - z)) + (G y - G z - L (y - z)) - (G y' - G z - L (y' - z)) := by abel
      _ = L (y - y') + (G y - G z - L (y - z)) - (G y' - G z - L (y' - z)) := by
        simp [L.map_sub]
  have heval : (G y - G y') (y - y') = L (y - y') (y - y') +
      (G y - G z - L (y - z)) (y - y') - (G y' - G z - L (y' - z)) (y - y') := by
    calc
      (G y - G y') (y - y') = (L (y - y') + (G y - G z - L (y - z)) - (G y' - G z - L (y' - z))) (y - y') := by
        rw [hsplit]
      _ = L (y - y') (y - y') + (G y - G z - L (y - z)) (y - y') - (G y' - G z - L (y' - z)) (y - y') := by
        simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  have hryy' : |(G y - G z - L (y - z)) (y - y')| ≤ ε * ‖y - z‖ * ‖y - y'‖ := by
    have h := ContinuousLinearMap.le_opNorm (G y - G z - L (y - z)) (y - y')
    have hnorm : ‖(G y - G z - L (y - z)) (y - y')‖ = |(G y - G z - L (y - z)) (y - y')| := by
      simpa using Real.norm_eq_abs ((G y - G z - L (y - z)) (y - y'))
    have hle : ‖(G y - G z - L (y - z)) (y - y')‖ ≤ ‖G y - G z - L (y - z)‖ * ‖y - y'‖ := h
    have hle2 : ‖G y - G z - L (y - z)‖ * ‖y - y'‖ ≤ (ε * ‖y - z‖) * ‖y - y'‖ :=
      mul_le_mul_of_nonneg_right hδy (norm_nonneg _)
    calc
      |(G y - G z - L (y - z)) (y - y')| = ‖(G y - G z - L (y - z)) (y - y')‖ := by symm; exact hnorm
      _ ≤ ‖G y - G z - L (y - z)‖ * ‖y - y'‖ := hle
      _ ≤ (ε * ‖y - z‖) * ‖y - y'‖ := hle2
      _ = ε * ‖y - z‖ * ‖y - y'‖ := by ring
  have hry'y : |(G y' - G z - L (y' - z)) (y - y')| ≤ ε * ‖y' - z‖ * ‖y - y'‖ := by
    have h := ContinuousLinearMap.le_opNorm (G y' - G z - L (y' - z)) (y - y')
    have hnorm : ‖(G y' - G z - L (y' - z)) (y - y')‖ = |(G y' - G z - L (y' - z)) (y - y')| := by
      simpa using Real.norm_eq_abs ((G y' - G z - L (y' - z)) (y - y'))
    have hle : ‖(G y' - G z - L (y' - z)) (y - y')‖ ≤ ‖G y' - G z - L (y' - z)‖ * ‖y - y'‖ := h
    have hle2 : ‖G y' - G z - L (y' - z)‖ * ‖y - y'‖ ≤ (ε * ‖y' - z‖) * ‖y - y'‖ :=
      mul_le_mul_of_nonneg_right hδy' (norm_nonneg _)
    calc
      |(G y' - G z - L (y' - z)) (y - y')| = ‖(G y' - G z - L (y' - z)) (y - y')‖ := by symm; exact hnorm
      _ ≤ ‖G y' - G z - L (y' - z)‖ * ‖y - y'‖ := hle
      _ ≤ (ε * ‖y' - z‖) * ‖y - y'‖ := hle2
      _ = ε * ‖y' - z‖ * ‖y - y'‖ := by ring
  have hpos : 0 ≤ L (y - y') (y - y') + ε * (‖y - z‖ + ‖y' - z‖) * ‖y - y'‖ := by
    have heq : (G y - G y') (y - y') = L (y - y') (y - y') +
        ((G y - G z - L (y - z)) (y - y') - (G y' - G z - L (y' - z)) (y - y')) := by
      linarith
    have h_abs1 := abs_le.mp hryy'
    have h_abs2 := abs_le.mp hry'y
    have hB_le : (G y - G z - L (y - z)) (y - y') ≤ ε * ‖y - z‖ * ‖y - y'‖ := h_abs1.2
    have hC_le : (G y' - G z - L (y' - z)) (y - y') ≥ -(ε * ‖y' - z‖ * ‖y - y'‖) := by linarith
    have hub : (G y - G z - L (y - z)) (y - y') - (G y' - G z - L (y' - z)) (y - y') ≤
        ε * (‖y - z‖ + ‖y' - z‖) * ‖y - y'‖ := by
      linarith
    linarith
  exact hpos

/-- The second derivative of a convex function is nonnegative in every direction, at every point. Where `fderiv f`
is not differentiable the left side is `0`. -/
theorem fderiv_fderiv_nonneg_of_convex (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (z v : EuclideanSpace ℝ (Fin d)) : 0 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
  set G := fderiv ℝ f with hGdef
  by_cases hGdiff : DifferentiableAt ℝ G z
  swap
  · rw [fderiv_zero_of_not_differentiableAt hGdiff]
    simp
  set L := fderiv ℝ G z with hLdef
  have hLhas : HasFDerivAt G L z := hGdiff.hasFDerivAt
  by_cases hv0 : v = 0
  · rw [hv0]; simp
  have ha : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set a := ‖v‖ with hadef
  by_contra! hneg
  set q := -(L v v) with hqdef
  have hq : 0 < q := by rw [hqdef]; linarith
  set η := q / (24 * a ^ 2) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨ρ, hρ, hρq⟩ := fderiv_quad_lower f hf z L hLhas η hη
  set t := min 1 (min (ρ / (4 * a)) (q / (40 * (‖L‖ + 1) * a ^ 2))) with htdef
  have ht : 0 < t := lt_min one_pos (lt_min (by positivity) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htρ : t ≤ ρ / (4 * a) := (min_le_right _ _).trans (min_le_left _ _)
  have htq : t ≤ q / (40 * (‖L‖ + 1) * a ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  have h2ta : 2 * t * a < ρ := by
    rw [le_div_iff₀ (by positivity)] at htρ
    nlinarith
  have hLn := norm_nonneg L
  have h20 : 20 * t * ‖L‖ * a ^ 2 < q := by
    rw [le_div_iff₀ (by positivity)] at htq
    nlinarith [sq_nonneg a, mul_pos ht (pow_pos ha 2)]
  have ht2a : 0 < t ^ 2 * a := by positivity
  have htt : t ^ 2 * a ≤ t * a := by nlinarith
  obtain ⟨y, hyd, hyD⟩ := exists_differentiableAt_near_of_convex f hf (z + t • v) (t ^ 2 * a) ht2a
  obtain ⟨y', hy'd, hy'D⟩ := exists_differentiableAt_near_of_convex f hf z (t ^ 2 * a) ht2a
  rw [dist_eq_norm] at hyd hy'd
  have htv : ‖t • v‖ = t * a := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hyz : ‖y - z‖ ≤ 2 * t * a := by
    have : y - z = (y - (z + t • v)) + t • v := by abel
    rw [this]
    nlinarith [norm_add_le (y - (z + t • v)) (t • v)]
  set u := t • v with hudef
  set w := y - y' with hwdef
  have hwu : ‖w - u‖ ≤ 2 * t ^ 2 * a := by
    have : w - u = (y - (z + u)) - (y' - z) := by rw [hwdef]; abel
    rw [this]
    nlinarith [norm_sub_le (y - (z + u)) (y' - z)]
  have hw : ‖w‖ ≤ 4 * t * a := by
    have : w = (y - z) - (y' - z) := by rw [hwdef]; abel
    rw [this]
    nlinarith [norm_sub_le (y - z) (y' - z)]
  have hq0 := hρq y y' hyD hy'D (by linarith) (by linarith)
  rw [← hwdef] at hq0
  clear_value w u t η q a
  have hdiff : L w w - L u u = L (w - u) w + L u (w - u) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  have hb1 : |L (w - u) w| ≤ ‖L‖ * (2 * t ^ 2 * a) * (4 * t * a) := by
    rw [← Real.norm_eq_abs]
    refine (L.le_opNorm₂ _ _).trans ?_
    gcongr
  have hb2 : |L u (w - u)| ≤ ‖L‖ * (t * a) * (2 * t ^ 2 * a) := by
    rw [← Real.norm_eq_abs]
    refine (L.le_opNorm₂ _ _).trans ?_
    rw [htv]
    gcongr
  have hLuu : L u u = -(t ^ 2 * q) := by
    rw [hudef]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hqdef]
    ring
  have hupper : L w w ≤ -(t ^ 2 * q) + 10 * t ^ 3 * ‖L‖ * a ^ 2 := by
    have h1 := (abs_le.1 hb1).2
    have h2 := (abs_le.1 hb2).2
    have e : ‖L‖ * (2 * t ^ 2 * a) * (4 * t * a) + ‖L‖ * (t * a) * (2 * t ^ 2 * a) =
        10 * t ^ 3 * ‖L‖ * a ^ 2 := by ring
    linarith
  have herr : η * (‖y - z‖ + ‖y' - z‖) * ‖w‖ ≤ η * (3 * t * a) * (4 * t * a) := by
    gcongr
    linarith
  have hηq : η * (3 * t * a) * (4 * t * a) = t ^ 2 * q / 2 := by
    rw [hηdef]; field_simp; ring
  have e2 : t ^ 2 * (20 * t * ‖L‖ * a ^ 2) = 20 * t ^ 3 * ‖L‖ * a ^ 2 := by ring
  have key : t ^ 2 * q ≤ t ^ 2 * (20 * t * ‖L‖ * a ^ 2) := by linarith only [hq0, herr, hηq, hupper, e2]
  have hfin := le_of_mul_le_mul_left key (by positivity)
  linarith only [hfin, h20]

/-! ## The extension -/

/-- `pip(x) = max(1, π(x)/(1 - ε))`. -/
noncomputable def pipOf (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max 1 (gauge K x / (1 - ε))

/-- The extension with the coefficient `c`: `pip(x) f(x/pip(x)) + c (pip(x) - 1)`. -/
noncomputable def extOf (K : Set (EuclideanSpace ℝ (Fin d))) (ε c : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  pipOf K ε x * f ((pipOf K ε x)⁻¹ • x) + c * (pipOf K ε x - 1)

/-- (G4) along a ray. -/
theorem ray_bounds (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f) (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (y : EuclideanSpace ℝ (Fin d)) (hy : (1 - ε)⁻¹ • y ∈ K)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    f y - (1 - ε) / ε * (1 - θ) ≤ f (θ • y) ∧ f (θ • y) ≤ f y + (1 - θ) := by
  have hεpos' : 0 ≤ ε := le_of_lt hε0
  have hεlt1' : ε ≤ 1 := le_of_lt hε1
  have h1meps_pos : 0 < 1 - ε := by linarith
  have h1meps_nonneg : 0 ≤ 1 - ε := by linarith
  -- y ∈ K because y = (1 - ε) • y' + ε • 0
  have hy_in_K : y ∈ K := by
    have hy_eq : y = (1 - ε) • ((1 - ε)⁻¹ • y) + ε • (0 : EuclideanSpace ℝ (Fin d)) := by
      simp [h1meps_pos.ne']
    rw [hy_eq]
    exact hK (a := 1 - ε) (b := ε) hy h0 h1meps_nonneg hεpos' (by ring)
  -- θ • y ∈ K by convexity of K
  have hθy_in_K : θ • y ∈ K := by
    have h_eq : θ • y = θ • y + (1 - θ) • (0 : EuclideanSpace ℝ (Fin d)) := by simp
    rw [h_eq]
    exact hK (a := θ) (b := 1 - θ) hy_in_K h0 hθ0 (by linarith) (by ring)
  have hfy_range := hf01 y hy_in_K
  have hf0_range := hf01 0 h0
  rcases hfy_range with ⟨hfy0, hfy1⟩
  rcases hf0_range with ⟨hf00, hf01'⟩
  -- Upper bound: f (θ • y) ≤ f y + (1 - θ)
  have h_upper : f (θ • y) ≤ f y + (1 - θ) := by
    have hconv := hf.2 hy_in_K h0 hθ0 (by linarith) (show θ + (1 - θ) = 1 by ring)
    have h_simp : θ • y + (1 - θ) • (0 : EuclideanSpace ℝ (Fin d)) = θ • y := by simp
    rw [h_simp] at hconv
    -- hconv : f (θ • y) ≤ θ • f y + (1 - θ) • f 0
    have hconv' : f (θ • y) ≤ θ * f y + (1 - θ) * f 0 := by
      simpa [smul_eq_mul] using hconv
    have h1 : θ * f y ≤ f y := by nlinarith
    have h2 : (1 - θ) * f 0 ≤ 1 - θ := by nlinarith
    nlinarith
  -- Lower bound: f y - (1 - ε) / ε * (1 - θ) ≤ f (θ • y)
  have h_lower : f y - (1 - ε) / ε * (1 - θ) ≤ f (θ • y) := by
    set a := ε / (1 - θ * (1 - ε)) with ha_def
    have h_denom_pos : 0 < 1 - θ * (1 - ε) := by
      have : θ * (1 - ε) ≤ 1 - ε := by nlinarith
      nlinarith
    have ha_pos : 0 < a := by
      rw [ha_def]
      exact div_pos hε0 h_denom_pos
    have ha_le_one : a ≤ 1 := by
      rw [ha_def]
      refine (div_le_one ?_).mpr ?_
      · linarith
      · nlinarith
    have h_one_minus_a_nonneg : 0 ≤ 1 - a := by linarith
    set y' := (1 - ε)⁻¹ • y with hy'_def
    have hy'_in_K : y' ∈ K := hy
    -- Key identity: a * θ + (1 - a) / (1 - ε) = 1
    have h_sum_eq_one : a * θ + (1 - a) / (1 - ε) = 1 := by
      rw [ha_def]
      field_simp [h1meps_pos.ne', h_denom_pos.ne']
      ring
    -- y = a • (θ • y) + (1 - a) • y'
    have hy_eq : y = a • (θ • y) + (1 - a) • y' := by
      calc
        y = (1 : ℝ) • y := by simp
        _ = (a * θ + (1 - a) / (1 - ε)) • y := by rw [h_sum_eq_one]
        _ = (a * θ) • y + ((1 - a) / (1 - ε)) • y := by rw [add_smul]
        _ = a • (θ • y) + (1 - a) • ((1 - ε)⁻¹ • y) := by
          simp [smul_smul, div_eq_mul_inv]
        _ = a • (θ • y) + (1 - a) • y' := rfl
    -- Apply convexity of f
    have hconv := hf.2 hθy_in_K hy'_in_K ha_pos.le h_one_minus_a_nonneg (by ring)
    rw [← hy_eq] at hconv
    -- hconv : f y ≤ a • f (θ • y) + (1 - a) • f y'
    have hfy'_range := hf01 y' hy'_in_K
    rcases hfy'_range with ⟨hfy'0, hfy'1⟩
    have h_ineq : (1 - a) • f y' ≤ (1 - a) • (1 : ℝ) :=
      smul_le_smul_of_nonneg_left hfy'1 h_one_minus_a_nonneg
    have h_simp_smul : (1 - a) • (1 : ℝ) = 1 - a := by simp
    rw [h_simp_smul] at h_ineq
    -- Now: f y ≤ a • f (θ • y) + (1 - a)
    have hconv_mul : f y ≤ a * f (θ • y) + (1 - a) := by
      have htemp : f y ≤ a * f (θ • y) + (1 - a) * f y' := by
        simpa [smul_eq_mul] using hconv
      -- h_ineq: (1 - a) * f y' ≤ 1 - a (after smul_eq_mul)
      have h_ineq_mul : (1 - a) * f y' ≤ 1 - a := by
        simpa [smul_eq_mul] using h_ineq
      linarith
    -- Rearranging: a * f (θ • y) ≥ f y - (1 - a)
    have h_ineq2 : a * f (θ • y) ≥ f y - (1 - a) := by linarith
    -- Since a > 0, divide: f (θ • y) ≥ (f y - (1 - a)) / a
    have h_ineq3 : (f y - (1 - a)) / a ≤ f (θ • y) :=
      (div_le_iff₀' ha_pos).mpr h_ineq2
    -- Identity: (1 - a) / a = (1 - ε) / ε * (1 - θ)
    have h_ratio : (1 - a) / a = (1 - ε) / ε * (1 - θ) := by
      rw [ha_def]
      field_simp [hε0.ne', h_denom_pos.ne']
      ring
    -- f y / a ≥ f y because 1/a ≥ 1 (since 0 < a ≤ 1) and f y ≥ 0
    have h_fy_div : f y / a ≥ f y := by
      have h_one_div_a : 1 ≤ 1 / a := (one_le_div ha_pos).mpr ha_le_one
      calc
        f y / a = f y * (1 / a) := by field_simp [ha_pos.ne']
        _ ≥ f y * 1 := by gcongr
        _ = f y := by simp
    -- (f y - (1 - a)) / a = f y / a - (1 - a) / a ≥ f y - (1 - a) / a
    have h_ineq4 : (f y - (1 - a)) / a ≥ f y - ((1 - a) / a) := by
      calc
        (f y - (1 - a)) / a = f y / a - (1 - a) / a := by rw [sub_div]
        _ ≥ f y - (1 - a) / a := by linarith
    rw [h_ratio] at h_ineq4
    -- f (θ • y) ≥ (f y - (1 - a)) / a ≥ f y - ((1 - ε) / ε * (1 - θ))
    linarith
  exact And.intro h_lower h_upper

/-- `x/pip(x)` lies in `K_ε = (1 - ε) K`. -/
theorem pip_play_mem (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (x : EuclideanSpace ℝ (Fin d)) :
    (1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x) ∈ K := by
  have hε_pos : 0 < 1 - ε := by linarith
  have hP_pos : 0 < pipOf K ε x := by
    have h_one_le : 1 ≤ pipOf K ε x := le_max_left _ _
    linarith
  have h_closedBall_nhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Metric.closedBall_mem_nhds 0 (by norm_num : 0 < (1 : ℝ))
  have hK_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset h_closedBall_nhds hball
  have h_gauge_le_one_iff : gauge K ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) ≤ 1 ↔
      (1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x) ∈ closure K :=
    gauge_le_one_iff_mem_closure hK hK_nhds
  have h_inv_nonneg : 0 ≤ (1 - ε)⁻¹ := by positivity
  have h_invP_nonneg : 0 ≤ (pipOf K ε x)⁻¹ := by positivity
  have h_gauge_smul : gauge K ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) =
      (1 - ε)⁻¹ * (pipOf K ε x)⁻¹ * gauge K x := by
    calc
      gauge K ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) =
          (1 - ε)⁻¹ • gauge K ((pipOf K ε x)⁻¹ • x) :=
        gauge_smul_of_nonneg h_inv_nonneg _
      _ = (1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • gauge K x) := by
        rw [gauge_smul_of_nonneg h_invP_nonneg _]
      _ = ((1 - ε)⁻¹ * (pipOf K ε x)⁻¹) • gauge K x := by rw [smul_smul]
      _ = (1 - ε)⁻¹ * (pipOf K ε x)⁻¹ * gauge K x := rfl
  have h_bound : gauge K x / (1 - ε) ≤ pipOf K ε x := le_max_right _ _
  have h_mul : gauge K x ≤ pipOf K ε x * (1 - ε) := by
    calc
      gauge K x = (gauge K x / (1 - ε)) * (1 - ε) := by field_simp [hε_pos.ne']
      _ ≤ pipOf K ε x * (1 - ε) := mul_le_mul_of_nonneg_right h_bound (by linarith)
  have h_nonneg_prod : 0 ≤ (1 - ε)⁻¹ * (pipOf K ε x)⁻¹ := by positivity
  have h_gauge_le_one : gauge K ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) ≤ 1 := by
    rw [h_gauge_smul]
    calc
      (1 - ε)⁻¹ * (pipOf K ε x)⁻¹ * gauge K x ≤
          (1 - ε)⁻¹ * (pipOf K ε x)⁻¹ * (pipOf K ε x * (1 - ε)) :=
        mul_le_mul_of_nonneg_left h_mul h_nonneg_prod
      _ = ((1 - ε)⁻¹ * (1 - ε)) * ((pipOf K ε x)⁻¹ * pipOf K ε x) := by ring
      _ = 1 * 1 := by field_simp [hP_pos.ne', hε_pos.ne']
      _ = 1 := by simp
  have h_mem_closure : (1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x) ∈ closure K :=
    h_gauge_le_one_iff.mp h_gauge_le_one
  rw [IsClosed.closure_eq hKc] at h_mem_closure
  exact h_mem_closure

/-- `pip` is convex. -/
theorem pipOf_convex (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hball : Metric.closedBall 0 1 ⊆ K) (ε : ℝ) (hε1 : ε < 1) : ConvexOn ℝ Set.univ (pipOf K ε) := by
  have hK_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 zero_lt_one) hball
  have ha : Absorbent ℝ K := absorbent_nhds_zero hK_nhds
  have h_gauge_conv : ConvexOn ℝ Set.univ (gauge K) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha_pos hb_pos hab
    have ha_nonneg : 0 ≤ a := ha_pos
    have hb_nonneg : 0 ≤ b := hb_pos
    calc
      gauge K (a • x + b • y) ≤ gauge K (a • x) + gauge K (b • y) := gauge_add_le hK ha _ _
      _ = a • gauge K x + b • gauge K y := by
        simp [gauge_smul_of_nonneg ha_nonneg, gauge_smul_of_nonneg hb_nonneg]
      _ = a * gauge K x + b * gauge K y := by simp
  have h_one_minus_ε_pos : 0 < 1 - ε := by linarith
  have hc_nonneg : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.mpr (by linarith)
  have h_gauge_scaled : ConvexOn ℝ Set.univ (fun x => (1 - ε)⁻¹ • gauge K x) :=
    h_gauge_conv.smul hc_nonneg
  have h_gauge_div : ConvexOn ℝ Set.univ (fun x => gauge K x / (1 - ε)) := by
    simpa [div_eq_inv_mul, smul_eq_mul] using h_gauge_scaled
  have h_const : ConvexOn ℝ Set.univ (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) :=
    convexOn_const 1 convex_univ
  have h_max : ConvexOn ℝ Set.univ ((fun x => gauge K x / (1 - ε)) ⊔ fun _ => (1 : ℝ)) :=
    h_gauge_div.sup h_const
  have h_eq : ((fun x => gauge K x / (1 - ε)) ⊔ fun _ => (1 : ℝ)) = pipOf K ε := by
    ext x
    simp [pipOf, Pi.sup_apply, max_comm]
  rw [h_eq] at h_max
  exact h_max

/-- (G5) the extension is a minimum over `λ ≥ pip(z)`. -/
theorem ext_min (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f)
    (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ)
    (hc : (1 - ε) / ε ≤ c) (z : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : pipOf K ε z ≤ lam) :
    pipOf K ε z * f ((pipOf K ε z)⁻¹ • z) + c * pipOf K ε z ≤ lam * f (lam⁻¹ • z) + c * lam := by
  set P := pipOf K ε z with hPdef
  set m := (1 - ε) / ε with hmdef
  have hP1 : 1 ≤ P := le_max_left _ _
  have hPpos : 0 < P := by linarith
  have hlam_pos : 0 < lam := by linarith
  have hP_le_lam : P ≤ lam := hlam
  set y := P⁻¹ • z with hydef
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    have hball0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      simp
    exact hball hball0
  have hmem : (1 - ε)⁻¹ • y ∈ K := pip_play_mem K hK hKc hball ε hε0 hε1 z
  have hy_mem_K : y ∈ K := by
    have hpos1 : 0 ≤ 1 - ε := by linarith
    have hposε : 0 ≤ ε := by linarith
    have hsum : (1 - ε) + ε = 1 := by ring
    have hy_eq : (1 - ε) • ((1 - ε)⁻¹ • y) + ε • (0 : EuclideanSpace ℝ (Fin d)) = y := by
      have htemp : ((1 - ε) * (1 - ε)⁻¹) = 1 := by
        field_simp [show 1 - ε ≠ 0 from by linarith]
      calc
        (1 - ε) • ((1 - ε)⁻¹ • y) + ε • (0 : EuclideanSpace ℝ (Fin d)) = (1 - ε) • ((1 - ε)⁻¹ • y) + 0 := by simp
        _ = (1 - ε) • ((1 - ε)⁻¹ • y) := by simp
        _ = ((1 - ε) * (1 - ε)⁻¹) • y := by simp [smul_smul]
        _ = 1 • y := by simpa [htemp]
        _ = y := by simp
    have hseg : y ∈ segment ℝ ((1 - ε)⁻¹ • y) (0 : EuclideanSpace ℝ (Fin d)) := by
      rw [segment]
      exact ⟨1 - ε, ε, hpos1, hposε, hsum, hy_eq⟩
    exact hK.segment_subset hmem h0 hseg
  have hfy_low : 0 ≤ f y := by
    have hfy_mem := hf01 y hy_mem_K
    exact hfy_mem.1
  set θ := P / lam with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg hPpos.le hlam_pos.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by linarith)]
    exact hP_le_lam
  have hy_eq2 : lam⁻¹ • z = θ • y := by
    calc
      lam⁻¹ • z = (lam⁻¹ * (P * P⁻¹)) • z := by field_simp [hPpos.ne']
      _ = ((lam⁻¹ * P) * P⁻¹) • z := by ring
      _ = (lam⁻¹ * P) • (P⁻¹ • z) := by simp [smul_smul]
      _ = (P / lam) • (P⁻¹ • z) := by ring
      _ = θ • (P⁻¹ • z) := by rw [hθdef]
      _ = θ • y := by rw [hydef]
  have hray := ray_bounds K hK h0 f hf hf01 ε hε0 hε1 y hmem θ hθ0 hθ1
  have hray_low : f y - m * (1 - θ) ≤ f (θ • y) := by
    rw [hmdef]
    exact hray.1
  have hcalc : lam * (1 - θ) = lam - P := by
    rw [hθdef]
    field_simp [hlam_pos.ne']
  have hineq1 : lam * f y - m * (lam - P) ≤ lam * f (θ • y) := by
    have htemp := mul_le_mul_of_nonneg_left hray_low hlam_pos.le
    have hcalc2 : lam * (f y - m * (1 - θ)) = lam * f y - m * (lam - P) := by
      calc
        lam * (f y - m * (1 - θ)) = lam * f y - lam * m * (1 - θ) := by ring
        _ = lam * f y - m * (lam * (1 - θ)) := by ring
        _ = lam * f y - m * (lam - P) := by rw [hcalc]
    linarith
  calc
    P * f (P⁻¹ • z) + c * P = P * f y + c * P := by rw [hydef]
    _ ≤ P * f y + c * P + (lam - P) * (f y + c - m) := by
      have h_nonneg : 0 ≤ (lam - P) * (f y + c - m) := by
        have h1 : 0 ≤ lam - P := by linarith
        have h2 : 0 ≤ f y + c - m := by
          have : m ≤ c := by
            rw [hmdef]
            exact hc
          linarith
        exact mul_nonneg h1 h2
      linarith
    _ = lam * f y - m * (lam - P) + c * lam := by ring
    _ ≤ lam * f (θ • y) + c * lam := by linarith
    _ = lam * f (lam⁻¹ • z) + c * lam := by rw [hy_eq2]

/-- (G6) the extension is convex on `ℝ^d`. -/
theorem extOf_convex (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f)
    (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ)
    (hc : (1 - ε) / ε ≤ c) : ConvexOn ℝ Set.univ (extOf K ε c f) := by
  have hε0' : 0 < 1 - ε := by linarith
  have h_one_le_pip : ∀ x, 1 ≤ pipOf K ε x := by
    intro x
    unfold pipOf
    exact le_max_left _ _
  have hball_mem_0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall 0 1 := by simp
    exact hball h0
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hsum
  set P₁ := pipOf K ε x with hP₁
  set P₂ := pipOf K ε y with hP₂
  set z := a • x + b • y with hz
  set lam := a * P₁ + b * P₂ with hlam
  have hP₁_pos : 0 < P₁ := by linarith [h_one_le_pip x]
  have hP₂_pos : 0 < P₂ := by linarith [h_one_le_pip y]
  have hlam_pos : 0 < lam := by
    have h_nonneg : 0 ≤ lam := by
      unfold lam
      nlinarith
    by_contra! hle
    have hzero : lam = 0 := by linarith
    unfold lam at hzero
    have hazero : a * P₁ = 0 := by nlinarith
    have hbzero : b * P₂ = 0 := by nlinarith
    have ha0 : a = 0 := by
      nlinarith
    have hb0 : b = 0 := by
      nlinarith
    nlinarith
  have hlam_ne_zero : lam ≠ 0 := by linarith
  have hP₁_ne_zero : P₁ ≠ 0 := by linarith
  have hP₂_ne_zero : P₂ ≠ 0 := by linarith
  have h_pip_z_le_lam : pipOf K ε z ≤ lam := by
    have hconv := (pipOf_convex K hK hball ε hε1).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hsum
    simpa [hP₁, hP₂, hz, hlam, smul_eq_mul] using hconv
  have h_ext_min := ext_min K hK hKc hball f hf hf01 ε hε0 hε1 c hc z lam h_pip_z_le_lam
  -- h_ext_min : pipOf K ε z * f ((pipOf K ε z)⁻¹ • z) + c * pipOf K ε z ≤ lam * f (lam⁻¹ • z) + c * lam
  have h_ext_z_le : extOf K ε c f z ≤ lam * f (lam⁻¹ • z) + c * (lam - 1) := by
    unfold extOf
    linarith
  set y₁ := P₁⁻¹ • x with hy₁
  set y₂ := P₂⁻¹ • y with hy₂
  have h1ε_ne_zero : 1 - ε ≠ 0 := by linarith
  have hy₁_mem_K : y₁ ∈ K := by
    have hmem : (1 - ε)⁻¹ • y₁ ∈ K := by
      simpa [hy₁, hP₁] using pip_play_mem K hK hKc hball ε hε0 hε1 x
    have hconv := hK hmem hball_mem_0 (a := 1 - ε) (b := ε) (by linarith) (by linarith) (by ring)
    have htemp : (1 - ε) * (1 - ε)⁻¹ = 1 := by field_simp [h1ε_ne_zero]
    simpa [smul_zero, add_zero, smul_smul, htemp] using hconv
  have hy₂_mem_K : y₂ ∈ K := by
    have hmem : (1 - ε)⁻¹ • y₂ ∈ K := by
      simpa [hy₂, hP₂] using pip_play_mem K hK hKc hball ε hε0 hε1 y
    have hconv := hK hmem hball_mem_0 (a := 1 - ε) (b := ε) (by linarith) (by linarith) (by ring)
    have htemp : (1 - ε) * (1 - ε)⁻¹ = 1 := by field_simp [h1ε_ne_zero]
    simpa [smul_zero, add_zero, smul_smul, htemp] using hconv
  have h_weights_sum : (a * P₁ / lam) + (b * P₂ / lam) = 1 := by
    field_simp [hlam_ne_zero]
    nlinarith
  have ha_weight_nonneg : 0 ≤ a * P₁ / lam := by
    positivity
  have hb_weight_nonneg : 0 ≤ b * P₂ / lam := by
    positivity
  have h_eq : lam⁻¹ • z = (a * P₁ / lam) • y₁ + (b * P₂ / lam) • y₂ := by
    dsimp [y₁, y₂, z]
    have hcoeff1 : lam⁻¹ * a = (a * P₁ / lam) * P₁⁻¹ := by
      field_simp [hlam_ne_zero, hP₁_ne_zero]
    have hcoeff2 : lam⁻¹ * b = (b * P₂ / lam) * P₂⁻¹ := by
      field_simp [hlam_ne_zero, hP₂_ne_zero]
    calc
      lam⁻¹ • (a • x + b • y) = (lam⁻¹ * a) • x + (lam⁻¹ * b) • y := by
        simp [smul_add, smul_smul]
      _ = ((a * P₁ / lam) * P₁⁻¹) • x + ((b * P₂ / lam) * P₂⁻¹) • y := by simp [hcoeff1, hcoeff2]
      _ = (a * P₁ / lam) • (P₁⁻¹ • x) + (b * P₂ / lam) • (P₂⁻¹ • y) := by simp [smul_smul]
  have h_f_ineq : f (lam⁻¹ • z) ≤ (a * P₁ / lam) • f y₁ + (b * P₂ / lam) • f y₂ := by
    have hconv := hf.2 hy₁_mem_K hy₂_mem_K ha_weight_nonneg hb_weight_nonneg h_weights_sum
    -- hconv : f ((a * P₁ / lam) • y₁ + (b * P₂ / lam) • y₂) ≤ (a * P₁ / lam) • f y₁ + (b * P₂ / lam) • f y₂
    simpa [h_eq] using hconv
  have h_main_ineq : lam * f (lam⁻¹ • z) ≤ a * P₁ * f y₁ + b * P₂ * f y₂ := by
    have h := h_f_ineq
    simp [smul_eq_mul] at h
    -- h: f (lam⁻¹ • z) ≤ (a * P₁ / lam) * f y₁ + (b * P₂ / lam) * f y₂
    have hpos : 0 ≤ lam := by linarith
    have h_mul := mul_le_mul_of_nonneg_left h hpos
    -- h_mul : lam * f (lam⁻¹ • z) ≤ lam * ((a * P₁ / lam) * f y₁ + (b * P₂ / lam) * f y₂)
    have h_simp : lam * ((a * P₁ / lam) * f y₁ + (b * P₂ / lam) * f y₂) = a * P₁ * f y₁ + b * P₂ * f y₂ := by
      field_simp [hlam_ne_zero]
    linarith
  have h_target : lam * f (lam⁻¹ • z) + c * (lam - 1) ≤ a * extOf K ε c f x + b * extOf K ε c f y := by
    calc
      lam * f (lam⁻¹ • z) + c * (lam - 1) ≤ (a * P₁ * f y₁ + b * P₂ * f y₂) + c * (lam - 1) := by
        nlinarith
      _ = a * (P₁ * f y₁) + b * (P₂ * f y₂) + c * (lam - 1) := by ring
      _ = a * (P₁ * f y₁) + b * (P₂ * f y₂) + c * (a * P₁ + b * P₂ - (a + b)) := by
        simp [hlam, hsum]
      _ = a * (P₁ * f y₁ + c * (P₁ - 1)) + b * (P₂ * f y₂ + c * (P₂ - 1)) := by
        nlinarith
      _ = a * extOf K ε c f x + b * extOf K ε c f y := by
        simp [extOf, hy₁, hy₂, hP₁, hP₂]
  -- Now combine everything
  unfold extOf
  calc
    extOf K ε c f z = pipOf K ε z * f ((pipOf K ε z)⁻¹ • z) + c * (pipOf K ε z - 1) := rfl
    _ ≤ (lam * f (lam⁻¹ • z) + c * lam) - c := by
      -- from h_ext_min
      linarith
    _ = lam * f (lam⁻¹ • z) + c * (lam - 1) := by ring
    _ ≤ a * extOf K ε c f x + b * extOf K ε c f y := h_target
    _ = a • extOf K ε c f x + b • extOf K ε c f y := by simp [smul_eq_mul]

/-! ## The Gaussian comparison (lem:ons:mink) -/

open Matrix in
open scoped MatrixOrder Matrix.Norms.L2Operator InnerProduct in
/-- A factor of the complement: `‖A‖ ≤ s` gives `B` with `A A* + B B* = s² I`. -/
theorem exists_compl_factor (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (s : ℝ) (hs : 0 ≤ s)
    (hA : ‖A‖ ≤ s) :
    ∃ B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B =
        (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
  -- helper lemma: adjoint commutes with toEuclideanCLM via star
  have h_adjoint_toEuclideanCLM (M : Matrix (Fin d) (Fin d) ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) M) =
    toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (Mᴴ) := by
    calc
      ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) M) =
        star (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) M) := by
        rw [ContinuousLinearMap.star_eq_adjoint]
      _ = toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (star M) :=
        (toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).map_star' M |>.symm
      _ = toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (Mᴴ) := by simp [star_eq_conjTranspose]
  -- convert A to a matrix via the star algebra equivalence
  let A_mat := (toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).symm A
  have hA_norm : ‖A_mat‖ ≤ s := by
    calc
      ‖A_mat‖ = ‖toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat‖ := by
        rw [l2_opNorm_toEuclideanCLM]
      _ = ‖A‖ := by
        simpa [A_mat] using (toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).norm_map A
      _ ≤ s := hA
  -- T = s^2 * I - A * A^T as a matrix
  let T_mat := (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) - A_mat * A_matᴴ
  have hT_nonneg : 0 ≤ T_mat := by
    apply (Matrix.nonneg_iff_posSemidef (A := T_mat)).mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · -- T_mat is Hermitian
      have h1 : ((s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian :=
        (isHermitian_one (n := Fin d)).smul (IsSelfAdjoint.of_nonneg (by positivity))
      have h2 : (A_mat * A_matᴴ).IsHermitian := by
        have : (A_mat * A_matᴴ)ᴴ = A_mat * A_matᴴ := by simp
        rw [Matrix.IsHermitian]
        exact this
      simpa [T_mat, sub_eq_add_neg] using h1.add h2.neg
    · -- the quadratic form is nonnegative
      intro x
      let x' : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm x
      have h_inner : 0 ≤ inner (𝕜 := ℝ) x'
        ((toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat) x') := by
        -- relate to A via the CLM representation
        have hT_eq : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat =
          (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A := by
          have h1 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
            ext x; simp
          have h2 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat = A := by
            dsimp [A_mat]; simp
          have h3 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_matᴴ) = ContinuousLinearMap.adjoint A := by
            rw [← h_adjoint_toEuclideanCLM A_mat, h2]
          calc
            toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat =
              toEuclideanCLM (𝕜 := ℝ) (n := Fin d) ((s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) - A_mat * A_matᴴ) := rfl
            _ = toEuclideanCLM (𝕜 := ℝ) (n := Fin d) ((s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) -
              toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_mat * A_matᴴ) := by rw [map_sub]
            _ = (s ^ 2) • toEuclideanCLM (𝕜 := ℝ) (n := Fin d) 1 -
              toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat * toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_matᴴ := by
              simp [map_smul, map_mul]
            _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A * ContinuousLinearMap.adjoint A := by
              have h4 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_matᵀ) = ContinuousLinearMap.adjoint A := by
                simpa [star_eq_conjTranspose] using h3
              simp [h1, h2, h4]
            _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A := by
              simp [ContinuousLinearMap.mul_def]
        rw [hT_eq]
        -- compute inner x' (T x') = s^2 ‖x'‖^2 - ‖A† x'‖^2
        have hkey : inner (𝕜 := ℝ) x'
          (A ((ContinuousLinearMap.adjoint A) x')) =
          ‖(ContinuousLinearMap.adjoint A) x'‖ ^ 2 := by
          calc
            inner (𝕜 := ℝ) x'
              (A ((ContinuousLinearMap.adjoint A) x')) =
              inner (𝕜 := ℝ) (A ((ContinuousLinearMap.adjoint A) x')) x' := by rw [real_inner_comm]
            _ = inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A))
                ((ContinuousLinearMap.adjoint A) x')) x' := by rw [ContinuousLinearMap.adjoint_adjoint]
            _ = inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint A) x')
                ((ContinuousLinearMap.adjoint A) x') := by
              rw [ContinuousLinearMap.adjoint_inner_left]
            _ = ‖(ContinuousLinearMap.adjoint A) x'‖ ^ 2 := by
              have hinner := inner_self_eq_norm_sq (𝕜 := ℝ)
                ((ContinuousLinearMap.adjoint A) x')
              have : RCLike.re (inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint A) x')
                ((ContinuousLinearMap.adjoint A) x')) =
                inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint A) x')
                  ((ContinuousLinearMap.adjoint A) x') := by simp
              rw [this] at hinner
              exact hinner
        -- compute the full expression
        calc
          inner (𝕜 := ℝ) x'
            (((s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A) x') =
            inner (𝕜 := ℝ) x'
              ((s ^ 2) • x' - A ((ContinuousLinearMap.adjoint A) x')) := by
            simp
          _ = s ^ 2 * inner (𝕜 := ℝ) x' x' -
            inner (𝕜 := ℝ) x' (A ((ContinuousLinearMap.adjoint A) x')) := by
            rw [inner_sub_right, inner_smul_right]
          _ = s ^ 2 * ‖x'‖ ^ 2 -
            ‖(ContinuousLinearMap.adjoint A) x'‖ ^ 2 := by
            have h_inner_self : inner (𝕜 := ℝ) x' x' = ‖x'‖ ^ 2 := by
              simpa using inner_self_eq_norm_sq (𝕜 := ℝ) x'
            rw [h_inner_self, hkey]
          _ ≥ 0 := by
            have h_norm_bound : ‖(ContinuousLinearMap.adjoint A) x'‖ ≤
              s * ‖x'‖ := by
              calc
                ‖(ContinuousLinearMap.adjoint A) x'‖ ≤
                  ‖ContinuousLinearMap.adjoint A‖ * ‖x'‖ :=
                  ContinuousLinearMap.le_opNorm _ _
                _ = ‖A‖ * ‖x'‖ := by
                  have h : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := by
                    simpa using (ContinuousLinearMap.adjoint (𝕜 := ℝ)
                      (E := EuclideanSpace ℝ (Fin d)) (F := EuclideanSpace ℝ (Fin d))).norm_map A
                  rw [h]
                _ ≤ s * ‖x'‖ := by
                  have h_nonneg_norm : 0 ≤ ‖x'‖ := norm_nonneg _
                  nlinarith
            have h_nonneg : 0 ≤ s ^ 2 * ‖x'‖ ^ 2 - ‖(ContinuousLinearMap.adjoint A) x'‖ ^ 2 := by
              have h_sq : ‖(ContinuousLinearMap.adjoint A) x'‖ ^ 2 ≤ (s * ‖x'‖) ^ 2 := by
                have h_nonneg_norm : 0 ≤ ‖(ContinuousLinearMap.adjoint A) x'‖ := norm_nonneg _
                have h_nonneg_s : 0 ≤ s := hs
                nlinarith
              have h_eq : (s * ‖x'‖) ^ 2 = s ^ 2 * ‖x'‖ ^ 2 := by ring
              rw [h_eq] at h_sq
              nlinarith
            exact h_nonneg
      -- convert to dot product using inner_toEuclideanCLM
      simpa [inner_toEuclideanCLM, PiLp.inner_apply, dotProduct, x', mul_comm] using h_inner
  -- take the square root via CFC
  let B_mat := CFC.sqrt T_mat
  have hB_sq : B_mat ^ 2 = T_mat := by
    rw [CFC.sq_sqrt T_mat hT_nonneg]
  have hB_nonneg : 0 ≤ B_mat := CFC.sqrt_nonneg T_mat
  have hB_selfadjoint : B_matᴴ = B_mat := by
    have : IsSelfAdjoint B_mat := hB_nonneg.isSelfAdjoint
    simpa [star_eq_conjTranspose] using this.star_eq
  have hT_to_CL : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat =
    (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A := by
    calc
      toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat =
        toEuclideanCLM (𝕜 := ℝ) (n := Fin d) ((s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) - A_mat * A_matᴴ) := rfl
      _ = toEuclideanCLM (𝕜 := ℝ) (n := Fin d) ((s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) -
        toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_mat * A_matᴴ) := by rw [map_sub]
      _ = (s ^ 2) • toEuclideanCLM (𝕜 := ℝ) (n := Fin d) 1 -
        toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat * toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_matᴴ := by
        simp [map_smul, map_mul]
      _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A := by
        have h1 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
          ext x; simp
        have h2 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat = A := by
          dsimp [A_mat]
          simp
        have h3 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_matᴴ) = ContinuousLinearMap.adjoint A := by
          calc
            toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_matᴴ) =
              ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat) := by
              rw [h_adjoint_toEuclideanCLM]
            _ = ContinuousLinearMap.adjoint A := by rw [h2]
        have h4 : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (A_matᵀ) = ContinuousLinearMap.adjoint A := by
          simpa [star_eq_conjTranspose] using h3
        calc
          (s ^ 2) • toEuclideanCLM (𝕜 := ℝ) (n := Fin d) 1 -
            toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_mat * toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_matᴴ
            = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) -
              A * toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A_matᴴ := by
            simp [h1, h2, ContinuousLinearMap.mul_def]
          _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) -
              A * ContinuousLinearMap.adjoint A := by
            rw [h3]
          _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A := by
            simp [ContinuousLinearMap.mul_def]
  -- convert back to CLM
  let B := toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B_mat
  refine ⟨B, ?_⟩
  calc
    A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B =
      A ∘L ContinuousLinearMap.adjoint A +
      (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B_mat) ∘L ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B_mat) := rfl
    _ = A ∘L ContinuousLinearMap.adjoint A +
      (toEuclideanCLM (𝕜 := ℝ) (n := Fin d) B_mat) ∘L toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (B_matᴴ) := by
      rw [h_adjoint_toEuclideanCLM]
    _ = A ∘L ContinuousLinearMap.adjoint A +
      toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (B_mat * B_matᴴ) := by
      simp [map_mul, ContinuousLinearMap.mul_def]
    _ = A ∘L ContinuousLinearMap.adjoint A +
      toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (B_mat * B_mat) := by rw [hB_selfadjoint]
    _ = A ∘L ContinuousLinearMap.adjoint A +
      toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (B_mat ^ 2) := by simp [sq]
    _ = A ∘L ContinuousLinearMap.adjoint A + toEuclideanCLM (𝕜 := ℝ) (n := Fin d) T_mat := by rw [hB_sq]
    _ = A ∘L ContinuousLinearMap.adjoint A +
      ((s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) - A ∘L ContinuousLinearMap.adjoint A) := by
      rw [hT_to_CL]
    _ = (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
      abel

open Complex in
open scoped MeasureTheory RealInnerProductSpace InnerProduct in
/-- The Gaussian split: with `A A* + B B* = s² I`, `A g + B h` (independent standard `g`, `h`) has the law of
`s g`. -/
theorem gauss_sum_law (A B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (h : A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B =
      (s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun p => A p.1 + B p.2) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => s • g) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  haveI : BorelSpace E := by infer_instance
  haveI : CompleteSpace E := by infer_instance
  haveI : SecondCountableTopology E := by infer_instance
  apply Measure.ext_of_charFun
  ext t
  -- Lemma: charFun (μ.map L) t = charFun μ (ContinuousLinearMap.adjoint L t)
  have h_charFun_map (μ : Measure E) (L : E →L[ℝ] E) (t : E) : charFun (μ.map L) t = charFun μ ((ContinuousLinearMap.adjoint L) t) := by
    rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    simp [ContinuousLinearMap.adjoint_inner_right]
  -- Rewrite the LHS map using map_prod_map
  have h_measA : Measurable A := by fun_prop
  have h_measB : Measurable B := by fun_prop
  have h_map_eq : ((stdGaussian E).prod (stdGaussian E)).map (fun p => A p.1 + B p.2) =
      (((stdGaussian E).map A).prod ((stdGaussian E).map B)).map (fun p => p.1 + p.2) := by
    calc
      ((stdGaussian E).prod (stdGaussian E)).map (fun p => A p.1 + B p.2)
          = ((stdGaussian E).prod (stdGaussian E)).map ((fun p => p.1 + p.2) ∘ (Prod.map A B)) := by
        have h_eq_fun : (fun (p : E × E) => A p.1 + B p.2) = ((fun p => p.1 + p.2) ∘ Prod.map A B) := by
          ext p; simp
        rw [h_eq_fun]
      _ = (((stdGaussian E).prod (stdGaussian E)).map (Prod.map A B)).map (fun p => p.1 + p.2) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
      _ = (((stdGaussian E).map A).prod ((stdGaussian E).map B)).map (fun p => p.1 + p.2) := by
        rw [Measure.map_prod_map (stdGaussian E) (stdGaussian E) h_measA h_measB]
  rw [h_map_eq]
  rw [charFun_map_add_prod_eq_mul (μ := (stdGaussian E).map A) (ν := (stdGaussian E).map B)]
  rw [Pi.mul_apply]
  rw [charFun_map_smul]
  rw [h_charFun_map (stdGaussian E) A t, h_charFun_map (stdGaussian E) B t]
  rw [charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian]
  rw [← exp_add]
  congr 1
  -- Need to show: (-↑‖A† t‖^2/2) + (-↑‖B† t‖^2/2) = (-↑‖s•t‖^2/2) in ℂ
  have h_norm_sq (L : E →L[ℝ] E) (t : E) : ‖(ContinuousLinearMap.adjoint L) t‖ ^ 2 = ⟪t, (L ∘L ContinuousLinearMap.adjoint L) t⟫ := by
    calc
      ‖(ContinuousLinearMap.adjoint L) t‖ ^ 2 = ⟪(ContinuousLinearMap.adjoint L) t, (ContinuousLinearMap.adjoint L) t⟫ := by simp
      _ = ⟪t, L ((ContinuousLinearMap.adjoint L) t)⟫ := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪t, (L ∘L ContinuousLinearMap.adjoint L) t⟫ := rfl
  have hA := h_norm_sq A t
  have hB := h_norm_sq B t
  have hsum : ‖(ContinuousLinearMap.adjoint A) t‖ ^ 2 + ‖(ContinuousLinearMap.adjoint B) t‖ ^ 2 = ⟪((A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B) t), t⟫ := by
    rw [hA, hB, ← inner_add_right, ← ContinuousLinearMap.add_apply]
    rw [real_inner_comm]
  have h_real : (-‖(ContinuousLinearMap.adjoint A) t‖ ^ 2 / 2) + (-‖(ContinuousLinearMap.adjoint B) t‖ ^ 2 / 2) = (-‖s • t‖ ^ 2 / 2) := by
    have h1 : (-‖(ContinuousLinearMap.adjoint A) t‖ ^ 2 / 2) + (-‖(ContinuousLinearMap.adjoint B) t‖ ^ 2 / 2) =
        (-(‖(ContinuousLinearMap.adjoint A) t‖ ^ 2 + ‖(ContinuousLinearMap.adjoint B) t‖ ^ 2)) / 2 := by
      ring_nf
    rw [h1, hsum, h]
    have h2 : ((s ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) t = (s ^ 2) • t := by simp
    rw [h2]
    simp [inner_smul_left, inner_self_eq_norm_sq_to_K, norm_smul, sq_abs, mul_pow]
  simpa [ofReal_add, ofReal_div, ofReal_neg, ofReal_pow] using congrArg (fun x : ℝ => (x : ℂ)) h_real

theorem evgy_mul_le_abs_mul {b t : ℝ} (ht : 0 ≤ t) : b * t ≤ |b| * t := by
  have hb : b ≤ |b| := le_abs_self b
  nlinarith

/-- Jensen over a centred Gaussian. -/
theorem le_integral_add_gauss (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hFc : Continuous F) (a b : ℝ) (hg : ∀ x, |F x| ≤ a + b * ‖x‖)
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    F x ≤ ∫ g, F (x + B g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_int_id : Integrable (id : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))) μ :=
    IsGaussian.integrable_id
  have h_int_Bg : Integrable (fun g => B g) μ :=
    B.integrable_comp h_int_id
  have h_int_x : Integrable (fun _ => x) μ :=
    integrable_const _
  have h_int_sum : Integrable (fun g => x + B g) μ :=
    h_int_x.add h_int_Bg
  have h_int_norm_Bg : Integrable (fun g => ‖B g‖) μ :=
    h_int_Bg.norm
  have h_bound_norm : ∀ g, ‖x + B g‖ ≤ ‖x‖ + ‖B g‖ := by
    intro g
    exact norm_add_le _ _
  have h_bound_F : ∀ g, |F (x + B g)| ≤ a + b * ‖x + B g‖ := by
    intro g; exact hg (x + B g)
  -- Dominating function for F ∘ (x + B ·)
  -- |F (x + B g)| ≤ a + b * ‖x + B g‖ ≤ a + b * (‖x‖ + ‖B g‖) ≤ a + |b| * (‖x‖ + ‖B g‖)
  have h_bound_dom : ∀ g, |F (x + B g)| ≤ a + |b| * (‖x‖ + ‖B g‖) := by
    intro g
    have h1 : |F (x + B g)| ≤ a + b * ‖x + B g‖ := h_bound_F g
    have h2 : b * ‖x + B g‖ ≤ |b| * ‖x + B g‖ :=
      evgy_mul_le_abs_mul (norm_nonneg _)
    have h3 : a + b * ‖x + B g‖ ≤ a + |b| * ‖x + B g‖ := by nlinarith
    have h4 : |b| * ‖x + B g‖ ≤ |b| * (‖x‖ + ‖B g‖) := by
      have h_nonneg : 0 ≤ |b| := abs_nonneg _
      nlinarith [h_bound_norm g]
    nlinarith
  -- Now show that g ↦ a + |b| * (‖x‖ + ‖B g‖) is integrable
  have h_int_dom : Integrable (fun g => a + |b| * (‖x‖ + ‖B g‖)) μ := by
    have h1 : Integrable (fun _ => a) μ := integrable_const _
    have h2 : Integrable (fun g => |b| * ‖x‖) μ := integrable_const _
    have h3 : Integrable (fun g => |b| * ‖B g‖) μ := by
      simpa [mul_comm] using h_int_norm_Bg.const_mul (|b|)
    have h23 : Integrable (fun g => |b| * ‖x‖ + |b| * ‖B g‖) μ := h2.add h3
    simpa [add_assoc, mul_add] using h1.add h23
  -- F ∘ (x + B ·) is AEStronglyMeasurable (F continuous, x + B · measurable)
  have h_ae_meas : AEStronglyMeasurable (fun g => F (x + B g)) μ := by
    have h_cont : Continuous (fun g => x + B g) := by
      continuity
    have h_meas : Measurable (fun g => x + B g) := h_cont.measurable
    exact (hFc.measurable.comp h_meas).aestronglyMeasurable
  have h_int_F : Integrable (fun g => F (x + B g)) μ := by
    refine Integrable.mono' h_int_dom h_ae_meas ?_
    filter_upwards with g
    simpa using h_bound_dom g
  -- Now apply Jensen's inequality
  have h_jensen : F (∫ g, (x + B g) ∂μ) ≤ ∫ g, F (x + B g) ∂μ := by
    refine ConvexOn.map_integral_le hF ?_ isClosed_univ ?_ h_int_sum h_int_F
    · exact hFc.continuousOn
    · filter_upwards with g
      exact Set.mem_univ _
  -- Compute the integral: ∫ g, (x + B g) ∂μ = x
  have h_integral_sum : (∫ g, (x + B g) ∂μ) = x := by
    calc
      (∫ g, (x + B g) ∂μ) = (∫ g, x ∂μ) + (∫ g, B g ∂μ) := integral_add h_int_x h_int_Bg
      _ = x + (∫ g, B g ∂μ) := by simp
      _ = x + B (∫ g, g ∂μ) := by
        simpa using congrArg (fun t => x + t) (B.integral_comp_comm h_int_id)
      _ = x + B 0 := by rw [integral_id_stdGaussian]
      _ = x := by simp
  -- Combine everything
  rw [h_integral_sum] at h_jensen
  exact h_jensen

/-- lem:ons:mink, the comparison: `E F(A g) ≤ E F(s g)` for `F` convex, continuous, of linear growth, `‖A‖ ≤ s`. -/
theorem gauss_mean_mono (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    (a b : ℝ) (hg : ∀ x, |F x| ≤ a + b * ‖x‖) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (s : ℝ) (hs : 0 ≤ s) (hA : ‖A‖ ≤ s) :
    ∫ g, F (A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, F (s • g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rcases exists_compl_factor A s hs hA with ⟨B, hB⟩
  have h_sum_law := gauss_sum_law A B s hB
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  by_cases hd : Nontrivial (EuclideanSpace ℝ (Fin d))
  · -- d > 0 case: the space is nontrivial
    have h_int_id : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) γ :=
      IsGaussian.integrable_id
    have ha_nonneg : 0 ≤ a := by
      have h0 := hg 0
      simp at h0
      have := abs_nonneg (F 0)
      linarith
    have hb_nonneg : 0 ≤ b := by
      by_contra! hb_neg
      -- hb_neg : b < 0
      -- Since b < 0, a + b * ‖x‖ → -∞ as ‖x‖ → ∞
      -- So there exists x with a + b * ‖x‖ < 0, contradicting |F x| ≤ a + b * ‖x‖
      obtain ⟨x, hx_ne⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin d))
      -- We can scale x to have arbitrarily large norm
      -- Take ‖x‖ > -a / b (note -a/b ≥ 0 since a ≥ 0, b < 0)
      have hdiv : 0 ≤ -a / b := by
        refine div_nonneg_of_nonpos ?_ (by linarith)
        linarith
      set t := -a / b + 1 with ht
      have ht_pos : 0 < t := by linarith
      set y := (t / ‖x‖) • x with hy
      have hy_norm : ‖y‖ = t := by
        rw [hy, norm_smul]
        have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
        rw [Real.norm_eq_abs, abs_div, abs_of_pos ht_pos, abs_of_nonneg (norm_nonneg _)]
        field_simp [hx_norm_pos.ne']
      have hbound := hg y
      have : a + b * ‖y‖ < 0 := by
        rw [hy_norm, ht]
        field_simp [show b ≠ 0 from by linarith]
        nlinarith
      have : |F y| < 0 := by linarith
      linarith [abs_nonneg (F y)]
    have h_bound : ∀ g, |F (A g)| ≤ a + b * s * ‖g‖ := by
      intro g
      have hAg : ‖A g‖ ≤ s * ‖g‖ := by
        calc
          ‖A g‖ ≤ ‖A‖ * ‖g‖ := A.le_opNorm g
          _ ≤ s * ‖g‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      have hgAg := hg (A g)
      have h : a + b * ‖A g‖ ≤ a + b * s * ‖g‖ := by
        nlinarith
      nlinarith
    have h_int_FA : Integrable (F ∘ A) γ := by
      have h_cont : Continuous (F ∘ A) := hFc.comp A.continuous
      have h_ae : AEStronglyMeasurable (F ∘ A) γ := h_cont.aestronglyMeasurable
      have h_int_norm : Integrable (fun g => ‖g‖) γ := h_int_id.norm
      have h_int_bound : Integrable (fun g => a + b * s * ‖g‖) γ := by
        refine (integrable_const a).add ?_
        exact (h_int_norm.const_mul (b * s))
      refine h_int_bound.mono' h_ae ?_
      filter_upwards with g
      have := h_bound g
      -- this : |F (A g)| ≤ a + b * s * ‖g‖
      -- we need: ‖(F ∘ A) g‖ ≤ a + b * s * ‖g‖
      simpa [Function.comp_def] using this
    -- Now we need to prove the main inequality
    -- ∫ F(A g) dγ ≤ ∫ F(s • g) dγ

    -- First, note that for each g, F(A g) ≤ ∫ F(A g + B h) dγ(h)  (by le_integral_add_gauss)
    have h_pointwise : ∀ g, F (A g) ≤ ∫ h, F (A g + B h) ∂γ := by
      intro g
      exact le_integral_add_gauss F hF hFc a b hg B (A g)

    -- We need to show both sides are integrable
    -- LHS: F ∘ A, already proved integrable (h_int_FA)
    -- RHS: fun g => ∫ h, F (A g + B h) ∂γ

    -- To show the RHS is integrable, we use Fubini:
    -- ∫ g, (∫ h, F(A g + B h) ∂γ) ∂γ = ∫ (g,h), F(A g + B h) ∂(γ.prod γ)
    -- So we need integrability of (g,h) ↦ F(A g + B h) on the product

    have h_int_prod : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      F (A p.1 + B p.2)) (γ.prod γ) := by
      have h_cont : Continuous (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        F (A p.1 + B p.2)) :=
        hFc.comp (Continuous.add (A.continuous.comp continuous_fst) (B.continuous.comp continuous_snd))
      have h_ae : AEStronglyMeasurable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        F (A p.1 + B p.2)) (γ.prod γ) := h_cont.aestronglyMeasurable
      have h_int_norm_prod : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
        a + b * s * ‖p.1‖ + b * ‖B‖ * ‖p.2‖) (γ.prod γ) := by
        have h_int_norm1 : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => ‖p.1‖)
          (γ.prod γ) := by
          have h_int_norm_gamma : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) γ :=
            h_int_id.norm
          exact h_int_norm_gamma.comp_fst γ
        have h_int_norm2 : Integrable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => ‖p.2‖)
          (γ.prod γ) := by
          have h_int_norm_gamma : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) γ :=
            h_int_id.norm
          exact h_int_norm_gamma.comp_snd γ
        refine ((integrable_const a).add ?_).add ?_
        · exact (h_int_norm1.const_mul (b * s))
        · exact (h_int_norm2.const_mul (b * ‖B‖))
      refine h_int_norm_prod.mono' h_ae ?_
      filter_upwards with p
      have hF := hg (A p.1 + B p.2)
      have h_norm : ‖A p.1 + B p.2‖ ≤ s * ‖p.1‖ + ‖B‖ * ‖p.2‖ := by
        calc
          ‖A p.1 + B p.2‖ ≤ ‖A p.1‖ + ‖B p.2‖ := norm_add_le _ _
          _ ≤ ‖A‖ * ‖p.1‖ + ‖B‖ * ‖p.2‖ := by
            have h1 : ‖A p.1‖ ≤ ‖A‖ * ‖p.1‖ := A.le_opNorm p.1
            have h2 : ‖B p.2‖ ≤ ‖B‖ * ‖p.2‖ := B.le_opNorm p.2
            nlinarith
          _ ≤ s * ‖p.1‖ + ‖B‖ * ‖p.2‖ := by
            have h_nonneg : 0 ≤ ‖p.1‖ := norm_nonneg _
            nlinarith
      have h_bound' : |F (A p.1 + B p.2)| ≤ a + b * (s * ‖p.1‖ + ‖B‖ * ‖p.2‖) := by
        nlinarith
      have : ‖F (A p.1 + B p.2)‖ = |F (A p.1 + B p.2)| := by
        simp
      rw [this]
      -- Now we need: |F (A p.1 + B p.2)| ≤ a + b * s * ‖p.1‖ + b * ‖B‖ * ‖p.2‖
      -- Since b ≥ 0, we have b * (s * ‖p.1‖ + ‖B‖ * ‖p.2‖) = b * s * ‖p.1‖ + b * ‖B‖ * ‖p.2‖
      -- So the goal follows from h_bound'
      have : a + b * (s * ‖p.1‖ + ‖B‖ * ‖p.2‖) = a + b * s * ‖p.1‖ + b * ‖B‖ * ‖p.2‖ := by ring
      -- h_bound' : |F (A p.1 + B p.2)| ≤ a + b * (s * ‖p.1‖ + ‖B‖ * ‖p.2‖)
      -- We need: |F (A p.1 + B p.2)| ≤ a + b * s * ‖p.1‖ + b * ‖B‖ * ‖p.2‖
      -- Using the equality above, this follows
      linarith

    have h_int_RHS : Integrable (fun g => ∫ h, F (A g + B h) ∂γ) γ :=
      h_int_prod.integral_prod_left

    -- Now apply integral_mono
    have h_ineq : ∫ g, F (A g) ∂γ ≤ ∫ g, (∫ h, F (A g + B h) ∂γ) ∂γ := by
      refine integral_mono h_int_FA h_int_RHS ?_
      intro g
      exact h_pointwise g

    -- Now we need to show that ∫ g, (∫ h, F (A g + B h) ∂γ) ∂γ = ∫ g, F (s • g) ∂γ
    -- Using gauss_sum_law and integral_map and integral_prod
    have h_eq : ∫ g, (∫ h, F (A g + B h) ∂γ) ∂γ = ∫ g, F (s • g) ∂γ := by
      calc
        ∫ g, (∫ h, F (A g + B h) ∂γ) ∂γ = ∫ (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
          F (A p.1 + B p.2) ∂(γ.prod γ) := by
          rw [integral_prod _ h_int_prod]
        _ = ∫ y, F y ∂(Measure.map (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
          A p.1 + B p.2) (γ.prod γ)) := by
          -- Use integral_map with AEMeasurable
          have h_meas : AEMeasurable (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
            A p.1 + B p.2) (γ.prod γ) := by
            refine (Continuous.aemeasurable ?_)
            exact Continuous.add (A.continuous.comp continuous_fst) (B.continuous.comp continuous_snd)
          have h_ae_strong : AEStronglyMeasurable F (Measure.map
            (fun (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
            A p.1 + B p.2) (γ.prod γ)) := by
            -- F is continuous, hence AEStronglyMeasurable w.r.t. any measure
            exact hFc.aestronglyMeasurable
          rw [integral_map h_meas h_ae_strong]
        _ = ∫ g, F (s • g) ∂γ := by
          rw [h_sum_law]
          -- h_sum_law : (γ.prod γ).map (fun p => A p.1 + B p.2) = γ.map (s • ·)
          -- Now we need to rewrite: ∫ y, F y ∂(γ.map (s • ·)) = ∫ g, F (s • g) ∂γ
          -- This is integral_map again
          have h_meas : AEMeasurable (fun g : EuclideanSpace ℝ (Fin d) => s • g) γ := by
            refine (Continuous.aemeasurable ?_)
            exact continuous_const_smul s
          have h_ae_strong : AEStronglyMeasurable F (Measure.map (fun g : EuclideanSpace ℝ (Fin d) => s • g) γ) := by
            exact hFc.aestronglyMeasurable
          rw [integral_map h_meas h_ae_strong]

    -- Combine the inequality and the equality
    linarith

  · -- d = 0 case: the space is trivial
    have h_subsing : Subsingleton (EuclideanSpace ℝ (Fin d)) := not_nontrivial_iff_subsingleton.mp hd
    have h_unique : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := fun x y => Subsingleton.elim x y
    -- In this case, both sides are F(0)
    have hA0 : A 0 = 0 := by
      -- A is linear, so A 0 = 0
      simp
    have hs0 : s • (0 : EuclideanSpace ℝ (Fin d)) = 0 := by simp
    -- Actually, for any g, g = 0, so F(A g) = F(0) and F(s • g) = F(0)
    -- So the inequality is trivially true
    have h_eq : (fun g => F (A g)) = (fun g => F (s • g)) := by
      ext g
      have hg0 : g = 0 := h_unique g 0
      simp [hg0, hA0, hs0]
    rw [h_eq]


/-! ## Freezing -/

/-- An event of `(z, x)`, `z` measurable in `𝒢` and `x` independent of `𝒢`: its probability is at most a bound on
the law of `x` of every section. -/
theorem freeze_le {Ω Z X : Type*} (𝒢 : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace X] (μ : Measure[m0] Ω) [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (z : Ω → Z) (x : Ω → X)
    (hz : Measurable[𝒢] z) (hx : Measurable[m0] x)
    (hind : @Indep Ω (MeasurableSpace.comap x inferInstance) 𝒢 m0 μ) (B : Set (Z × X)) (hB : MeasurableSet B)
    (q : ℝ≥0∞) (hq : ∀ a, (@Measure.map Ω X m0 _ x μ) (Prod.mk a ⁻¹' B) ≤ q) :
    μ {ω | (z ω, x ω) ∈ B} ≤ q := by
  have hz_m0 : Measurable[m0] z := hz.mono h𝒢 (le_refl _)
  have hz_comap_le : MeasurableSpace.comap z ‹_› ≤ 𝒢 := hz.comap_le
  have hind_comap : Indep (MeasurableSpace.comap x inferInstance) (MeasurableSpace.comap z ‹_›) (_mΩ := m0) μ :=
    ProbabilityTheory.indep_of_indep_of_le_right hind hz_comap_le
  have h_indepFun : ProbabilityTheory.IndepFun z x μ := by
    rw [ProbabilityTheory.IndepFun_iff_Indep]
    simpa using hind_comap.symm
  have h_map_eq : Measure.map (fun ω => (z ω, x ω)) μ = (Measure.map z μ).prod (Measure.map x μ) := by
    have hz_aemeas : AEMeasurable z μ := hz_m0.aemeasurable
    have hx_aemeas : AEMeasurable x μ := hx.aemeasurable
    have h := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hz_aemeas hx_aemeas).mp h_indepFun
    simpa using h
  have h_prob_map : IsProbabilityMeasure (Measure.map z μ) := inferInstance
  calc
    μ {ω | (z ω, x ω) ∈ B} = μ ((fun ω => (z ω, x ω)) ⁻¹' B) := rfl
    _ = (Measure.map (fun ω => (z ω, x ω)) μ) B := by
      rw [← Measure.map_apply (hz_m0.prodMk hx) hB]
    _ = ((Measure.map z μ).prod (Measure.map x μ)) B := by rw [h_map_eq]
    _ = ∫⁻ a, (Measure.map x μ) (Prod.mk a ⁻¹' B) ∂(Measure.map z μ) := by
      rw [Measure.prod_apply hB]
    _ ≤ ∫⁻ a, q ∂(Measure.map z μ) := by
      refine lintegral_mono ?_
      intro a
      exact hq a
    _ = q * (Measure.map z μ) Set.univ := by rw [lintegral_const]
    _ = q * 1 := by rw [h_prob_map.measure_univ]
    _ = q := by simp

end AdversarialBco.Poly.EvGY
