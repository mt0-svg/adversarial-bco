/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Bit-length leaves

Arithmetic of bit lengths (`Nat.size` of `Int.natAbs`, the `len` of the bit machine): `size_le_of_abs_lt`, `size_rg`,
`size_natCast_le`, `cell_lt`.
-/

open Matrix
namespace AdversarialBco.Bit.Transfer

theorem size_le_of_abs_lt (z : ℤ) (ℓ : ℕ) (h : |(z : ℝ)| < 2 ^ ℓ) :
    z.natAbs.size ≤ ℓ := by
  rw [Nat.size_le]
  have h1 : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  exact_mod_cast (h1 ▸ h : ((z.natAbs : ℕ) : ℝ) < 2 ^ ℓ)

theorem size_rg (i ℓ : ℕ) (h : i + 4 < 2 ^ ℓ) :
    (-((i : ℤ) + 4)).natAbs.size ≤ ℓ := by
  rw [Nat.size_le, Int.natAbs_neg]
  omega

theorem size_natCast_le (n ℓ : ℕ) (h : n < 2 ^ ℓ) :
    ((n : ℤ)).natAbs.size ≤ ℓ := by
  rw [Int.natAbs_natCast]; exact Nat.size_le.2 h

theorem cell_lt (NS NA S a k B : ℕ) (ha : a < NA) (hk : k < S)
    (hB : NS + 1 + NA * S ≤ B) : NS + 1 + a * S + k < B := by
  have : (a + 1) * S ≤ NA * S := Nat.mul_le_mul_right S ha
  rw [Nat.add_mul, one_mul] at this
  omega

end AdversarialBco.Bit.Transfer
