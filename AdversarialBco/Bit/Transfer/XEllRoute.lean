/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllRule

@[expose] public section

/-!
# The projection routine on the machine: the failure exit and the units of the constants

`xellFail`: the failure exit of the projection routine, `0` into the slot `o`; `ellJU`: the units of `XV.ellJ`, the
constants up to `λ`, at `E = 6 s + d + 4`; `abs_cast_lt`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## The command -/

/-- The failure exit: `0` into the slot `o`. -/
def xellFail (L : Layout) (B : EllBlk) : XCmd := xset L B.o (B.o + 15) (B.o + 15)

/-! ## The units -/

/-- The units of `XV.ellJ` at `E = 6 s + d + 4`. -/
def ellJU (d s : ℕ) : ℕ := 38 * d + 18 + (10 + (32 + (8 * (6 * s + d + 4) + 9)))

/-! ## The result -/

theorem abs_cast_lt {x : ℤ} {s ℓ : ℕ} (h : |x| ≤ 2 ^ s) (hs : s < ℓ) : |(x : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (h.trans_lt (pow_lt_pow_right₀ (by norm_num) hs))

end AdversarialBco.Bit.Transfer
