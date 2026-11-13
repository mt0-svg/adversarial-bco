/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Oracle
public import AdversarialBco.Poly.MachVL

@[expose] public section

/-!
# The subroutine AP in VL: the Euclidean norm

`oNorm x = 0 ↔ x = 0` (`oNorm_eq_zero_iff`).
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd}

/-! ## The Euclidean norm -/

theorem oNorm_eq_zero_iff {x : Fin d → ℝ} : oNorm x = 0 ↔ x = 0 := by
  have hnn : (0 : ℝ) ≤ x ⬝ᵥ x := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  unfold oNorm; rw [Real.sqrt_eq_zero hnn, dotProduct_self_eq_zero]

