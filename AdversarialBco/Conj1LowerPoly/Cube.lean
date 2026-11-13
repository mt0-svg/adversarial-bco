/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Sanity

@[expose] public section

/-!
# The cube `[-1, 1]^d` between two balls

The body of the lower bound on a polytope: the cube `polytope (cubeA d) (cubeB d)` of
AdversarialBco/Conj1Poly/Sanity.lean contains `B(0, 1/2)` and lies in `B(0, √d)`, with `1 ≤ √d ≤ d` for `d ≥ 1`;
these are the hypotheses of `Lower.Top.lowerBody_of_inputs` with `R0 = √d`.
-/

namespace AdversarialBco.Lower

open RealRAM RealRAM.Conj1PolySanity

theorem cube_norm_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (hx : ∀ j, |x j| ≤ 1) :
    ‖x‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc
    (∑ i : Fin d, ‖x.ofLp i‖ ^ 2) = (∑ i : Fin d, |x.ofLp i| ^ 2) := by
      simp [Real.norm_eq_abs]
    _ ≤ (∑ i : Fin d, (1 : ℝ)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have h := hx i
      have h_nonneg : 0 ≤ |x.ofLp i| := abs_nonneg _
      have h_sq : |x.ofLp i| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ h_nonneg h 2
      simpa using h_sq
    _ = (d : ℝ) := by simp

theorem sqrt_nat_bounds (d : ℕ) (hd : 1 ≤ d) : 1 ≤ Real.sqrt d ∧ Real.sqrt d ≤ d := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h_nonneg : 0 ≤ (d : ℝ) := by linarith
  have h_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    nlinarith
  have h_left : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact hd'
  have h_right : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨h_nonneg, h_sq⟩
  exact And.intro h_left h_right

/-- The cube lies in `B(0, √d)`. -/
theorem cube_subset_ball (d : ℕ) :
    polytope (cubeA d) (cubeB d) ⊆ Metric.closedBall (0 : E d) (Real.sqrt d) := fun x hx =>
  mem_closedBall_zero_iff.2 (cube_norm_le x ((mem_cube_iff x).1 hx))

/-- The cube contains `B(0, 1/2)`. -/
theorem half_ball_subset_cube (d : ℕ) :
    Metric.closedBall (0 : E d) (1 / 2) ⊆ polytope (cubeA d) (cubeB d) :=
  (Metric.closedBall_subset_closedBall (by norm_num)).trans (cube_ball d)

end AdversarialBco.Lower
