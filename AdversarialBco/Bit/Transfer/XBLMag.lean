/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMagC

@[expose] public section

/-!
# Values on the grid `2^{-p}`

`onG_up`: the rounding `up k x` lies on the grid `2^{-k}`; `qn_bnd`: the numerator on the grid `2^{-p}` of a value at
most `T^a` is at most `T^(a + 2)` when `2^p ≤ T`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ AdversarialBco.Bit.Asm Matrix
open AdversarialBco.BitRAM (toE)
open AdversarialBco.RealRAM (Strategy polytope HeightLE)

variable {d : ℕ}

/-! ## PARAM's fields -/

theorem onG_up (k : ℕ) (x : ℚ) : OnG k (up k x) := by
  unfold OnG; rw [qn_up]; unfold up; field_simp

/-! ## The run -/

/-- The numerator on the grid `2^{-p}` of a value at most `T^a`, for `2^p ≤ T`. -/
theorem qn_bnd {T : ℚ} (hT : 2 ≤ T) {p : ℕ} (hp : (2 : ℚ) ^ p ≤ T) {x : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) :
    |(qn p x : ℚ)| ≤ T ^ (a + 2) := by
  have h1 := Int.floor_le (x * 2 ^ p)
  have h2 := Int.lt_floor_add_one (x * 2 ^ p)
  have h3 : |x * 2 ^ p| ≤ T ^ (a + 1) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ p), pow_succ]
    exact mul_le_mul hx hp (by positivity) ((abs_nonneg _).trans hx)
  have hT1 : 1 ≤ T ^ (a + 1) := one_le_pow₀ (by linarith)
  apply two_mul_pw hT
  unfold qn
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

end AdversarialBco.Bit.Transfer.BLM
