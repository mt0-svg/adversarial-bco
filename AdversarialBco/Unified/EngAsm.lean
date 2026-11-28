/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngDefs

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the budget of the engine hypothesis

The engine hypothesis for BL-O holds with `κ0 = κ1 = kapO d n k_δ` by Theorem BUD at `k_δ` (`budAK`), with
`n (κ0 + κ1) ≤ 2^{-k_δ}/8 < δ/8` (`kap_k` of BUD, `1/δ < 2^{k_δ}` by `kDel_bounds`). This file holds `two_inv_pow_lt`:
`2^{-k_δ} < δ`.
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK)

/-- `2^{-k_δ} < δ`. -/
theorem two_inv_pow_lt {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) : (2 : ℝ)⁻¹ ^ kDel δ < δ := by
  have hk := (kDel_bounds h0 h1).1
  have hδ : (0 : ℝ) < δ := by exact_mod_cast h0
  rw [one_div] at hk
  rw [inv_pow]
  exact (inv_lt_comm₀ hδ (by positivity)).1 hk

end AdversarialBco.Unified.Eng
