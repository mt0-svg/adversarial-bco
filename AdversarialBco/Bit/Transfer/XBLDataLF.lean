/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataL
public import AdversarialBco.Bit.Transfer.XBLDataTF

@[expose] public section

/-!
# The data of R14 LINE: two bounds

`dl_le`: the units `dlUnits d` of the data command `xdl` are at most `22 d³ + 50 d² + 100 d + 200`; `s_le2`:
`2 d + 5 E + 12 ≤ 1024 (d + E + 1)³`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

theorem dl_le (d : ℕ) : dlUnits d ≤ 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 := by
  simp only [dlUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, eQD, eL0, eL1, eA2, eA3, eL4,
    eL5]
  ring_nf
  nlinarith [Nat.zero_le (d * d * d)]

theorem s_le2 (d E : ℕ) : 2 * d + 5 * E + 12 ≤ 1024 * (d + E + 1) ^ 3 := by
  have h : d + E + 1 ≤ (d + E + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  linarith

end AdversarialBco.Bit.Transfer.BLM.DataM
