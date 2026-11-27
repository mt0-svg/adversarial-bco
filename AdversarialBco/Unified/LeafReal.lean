/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Leaves of the unified route: the scalar and geometric facts

The leaves of the unified route that need only real arithmetic:

* `uni_clip_len`: the bit length of the clipped reading of UNI-OBS; `uni_clip_read_q`, `uni_clip_len_q`: the clipped
  reading within range and its bit length, for the clip to `[-2^q, 2^q]` of the oracle machine.
-/

open Metric

namespace AdversarialBco.Uni

/-- UNI-OBS: the clipped reading has at most `p + r + 1` bits. -/
theorem uni_clip_len (v : ℤ) (p r : ℕ) :
    (max (-(2 : ℤ) ^ (p + r)) (min v ((2 : ℤ) ^ (p + r)))).natAbs.size ≤ p + r + 1 := by
  have hc : (0 : ℤ) ≤ 2 ^ (p + r) := by positivity
  have h1 : -(2 : ℤ) ^ (p + r) ≤ max (-(2 : ℤ) ^ (p + r)) (min v ((2 : ℤ) ^ (p + r))) := le_max_left _ _
  have h2 : max (-(2 : ℤ) ^ (p + r)) (min v ((2 : ℤ) ^ (p + r))) ≤ 2 ^ (p + r) :=
    max_le (by linarith) (min_le_right _ _)
  generalize max (-(2 : ℤ) ^ (p + r)) (min v ((2 : ℤ) ^ (p + r))) = w at h1 h2 ⊢
  have h3 : w.natAbs ≤ 2 ^ (p + r) := by
    have h : |w| ≤ 2 ^ (p + r) := abs_le.2 ⟨h1, h2⟩
    have : (w.natAbs : ℤ) ≤ ((2 ^ (p + r) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast; exact h
    exact_mod_cast this
  rw [Nat.size_le]
  calc w.natAbs ≤ 2 ^ (p + r) := h3
    _ < 2 ^ (p + r + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- UNI-OBS with the clip `clip_q` of the machine (`[-2^q, 2^q]` with `q` read
from its own cell): when `2^p |o| ≤ 2^q` the clip does not act on `⌊2^p o⌋`, and the reading is within `2^{-p}` of
`o`. -/
theorem uni_clip_read_q (o : ℝ) (p q : ℕ) (ho : (2 : ℝ) ^ p * |o| ≤ 2 ^ q) :
    max (-(2 : ℤ) ^ q) (min ⌊(2 : ℝ) ^ p * o⌋ ((2 : ℤ) ^ q)) = ⌊(2 : ℝ) ^ p * o⌋ ∧
      |(⌊(2 : ℝ) ^ p * o⌋ : ℝ) / 2 ^ p - o| ≤ (2 : ℝ)⁻¹ ^ p := by
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have hv1 : (⌊(2 : ℝ) ^ p * o⌋ : ℝ) ≤ 2 ^ p * o := Int.floor_le _
  have hv2 : 2 ^ p * o < ⌊(2 : ℝ) ^ p * o⌋ + 1 := Int.lt_floor_add_one _
  have hab := abs_le.1 (show |(2 : ℝ) ^ p * o| ≤ 2 ^ q by rw [abs_mul, abs_of_pos h2p]; exact ho)
  have hup : ⌊(2 : ℝ) ^ p * o⌋ ≤ (2 : ℤ) ^ q := by
    have : (⌊(2 : ℝ) ^ p * o⌋ : ℝ) ≤ (2 : ℝ) ^ q := by linarith
    exact_mod_cast this
  have hdown : -(2 : ℤ) ^ q ≤ ⌊(2 : ℝ) ^ p * o⌋ := by
    apply Int.le_floor.2
    push_cast
    linarith
  refine ⟨by rw [min_eq_left hup, max_eq_right hdown], ?_⟩
  generalize ⌊(2 : ℝ) ^ p * o⌋ = v at hv1 hv2 ⊢
  have hA : (v : ℝ) / 2 ^ p ≤ o := by rw [div_le_iff₀ h2p]; linarith
  have hB : o - (2 ^ p)⁻¹ ≤ (v : ℝ) / 2 ^ p := by
    rw [le_div_iff₀ h2p, sub_mul, inv_mul_cancel₀ h2p.ne']; linarith
  rw [inv_pow, abs_le]
  constructor <;> linarith [inv_pos.2 h2p]

/-- UNI-OBS with the clip `clip_q`: the clipped reading has at most `q + 1` bits. `uni_clip_len` is the case
`q = p + r`. -/
theorem uni_clip_len_q (v : ℤ) (q : ℕ) :
    (max (-(2 : ℤ) ^ q) (min v ((2 : ℤ) ^ q))).natAbs.size ≤ q + 1 := by
  have h := uni_clip_len v q 0
  simpa using h

end AdversarialBco.Uni
