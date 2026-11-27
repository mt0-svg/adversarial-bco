/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnifiedLower

@[expose] public section

/-!
# The cube `[-1, 1]^d` as a body of `BodyU`

`bodyU_cube`: the cube `{x | ∀ i, |x i| ≤ 1}` of `E d`, `d ≥ 1`, is compact and convex and lies between the closed
unit ball about `0` and the closed ball of radius `√d`, so `TheoremLowerU` applies to it with `a = 0`, `r0 = 1`,
`R0 = √d` (`theoremLowerU_cube`, UnifiedLower/Main.lean).
-/

namespace AdversarialBco.UnifiedLower.Cube

/-- The cube `[-1, 1]^d` lies between the unit ball about `0` and the ball of radius `√d`: a body of `BodyU` with
`a = 0`, `r0 = 1`, `R0 = √d`. -/
theorem bodyU_cube {d : ℕ} (hd : 1 ≤ d) : BodyU {x : E d | ∀ i, |x i| ≤ 1} 0 1 (Real.sqrt d) := by
  have hsub : {x : E d | ∀ i, |x i| ≤ 1} ⊆ Metric.closedBall 0 (Real.sqrt d) := by
    intro x hx
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, sq_abs]; nlinarith [hx i, abs_nonneg (x i), sq_abs (x i)]
      _ = d := by simp
  have hclosed : IsClosed {x : E d | ∀ i, |x i| ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  refine ⟨one_pos, Real.one_le_sqrt.mpr (by exact_mod_cast hd), ?_, ?_, ?_, hsub⟩
  · exact Metric.isCompact_of_isClosed_isBounded hclosed (Metric.isBounded_closedBall.subset hsub)
  · intro x hx y hy s t hs ht hst i
    have hi : (s • x + t • y) i = s * x i + t * y i := rfl
    rw [hi]
    calc |s * x i + t * y i| ≤ s * |x i| + t * |y i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * 1 + t * 1 := by gcongr <;> [exact hx i; exact hy i]
      _ = 1 := by rw [mul_one, mul_one, hst]
  · intro x hx i
    rw [mem_closedBall_zero_iff] at hx
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le x i).trans hx

end AdversarialBco.UnifiedLower.Cube
