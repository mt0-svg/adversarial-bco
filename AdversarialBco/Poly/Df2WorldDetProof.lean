/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetTools
public import AdversarialBco.Poly.Df2RowsProof

@[expose] public section

/-!
# The Gaussian of `Fin d → ℝ` carried to `E d`

The standard Gaussian of `Fin d → ℝ` is carried to that of `E d`, for integrals (`integral_pi_toLp`) and for
integrability (`integrable_pi_toLp`); a function with a linear growth bound composed with an affine map is integrable
under the Gaussian (`integrable_lip_affine`).
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM
open scoped Matrix

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Integrals under the Gaussian -/

/-- The Gaussian of `Fin d → ℝ` carried to `E d`. -/
theorem integral_pi_toLp (F : E d → ℝ) (hF : Continuous F) :
    ∫ z, F (WithLp.toLp 2 z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = ∫ u, F u ∂(stdGaussian (E d)) := by
  rw [← map_pi_eq_stdGaussian, integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    hF.aestronglyMeasurable]

/-- A function with a linear growth bound composed with an affine map is integrable under the Gaussian. -/
theorem integrable_lip_affine (e : E d → ℝ) (L : ℝ) (he : ∀ x y, |e x - e y| ≤ L * ‖x - y‖) (m : E d)
    (B : E d →L[ℝ] E d) : Integrable (fun u => e (m + B u)) (stdGaussian (E d)) := by
  have hlip : LipschitzWith (Real.toNNReal |L|) e := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg L)]
    exact (he x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  have hc : Continuous fun u => e (m + B u) := hlip.continuous.comp (continuous_const.add B.continuous)
  have hg : Integrable (fun u : E d => |e m| + |L| * (‖B‖ * ‖u‖)) (stdGaussian (E d)) :=
    (integrable_const _).add ((IsGaussian.integrable_id.norm.const_mul ‖B‖).const_mul |L|)
  refine hg.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have h1 := he (m + B u) m
  simp only [add_sub_cancel_left] at h1
  rw [Real.norm_eq_abs]
  have h2 : L * ‖B u‖ ≤ |L| * (‖B‖ * ‖u‖) :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm u) (abs_nonneg L))
  have h3 := abs_sub_abs_le_abs_sub (e (m + B u)) (e m)
  linarith

/-- The Gaussian of `Fin d → ℝ` carried to `E d`, for integrability. -/
theorem integrable_pi_toLp (F : E d → ℝ) (hF : Continuous F) (hi : Integrable F (stdGaussian (E d))) :
    Integrable (fun z => F (WithLp.toLp 2 z)) (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian] at hi
  exact (integrable_map_measure hF.aestronglyMeasurable (PiLp.continuous_toLp 2 _).measurable.aemeasurable).mp hi

end Layer2

end AdversarialBco.Poly
