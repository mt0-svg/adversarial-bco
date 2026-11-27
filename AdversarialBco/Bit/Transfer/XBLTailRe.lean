/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRd

@[expose] public section

/-!
# The tail of BL's round, part e: the units of R10, R12 and R13

`r10Units_eq`, `r12Units_eq`, `r13Units_eq`: the unit counts of the lines R10 TRACE, R12 and R13 of BL's round as
polynomials in `d`, which the tail of BL-O's round reads (Unified/TailOTail.lean).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

theorem r10Units_eq (d : ℕ) : r10Units d = 20 * d * d + 4 * d + 25 := by
  unfold r10Units; rw [show ieLQ.units = 11 from rfl]; ring

theorem r12Units_eq (d X : ℕ) : r12Units d X = 10 * d * d + 41 * d + 4 * X + 83 := by
  unfold r12Units; rw [show ieT1.units = 47 from rfl, show ieT2.units = 13 from rfl]; ring

theorem r13Units_eq (d : ℕ) : r13Units d = 31 * d + 30 := by
  unfold r13Units
  rw [show ieWn.units = 15 from rfl, show ieDw.units = 7 from rfl, show ieL13.units = 9 from rfl,
    show ieR13.units = 5 from rfl]
  ring

end AdversarialBco.Bit.Transfer.BLM
