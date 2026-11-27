/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupSL

@[expose] public section

/-!
# BL's setup on the machine: Procedure PARAM as a straight line

The 93 steps of `parSt` compute, from `d` (slot `0`) and `n` (slot `3`), every field of `par d n` on the integers
(Bit/Transfer/XBLSetupPar.lean): the sizes `ℓe`, `ℓd`, the precisions `p`, `q`, `pF`, `B`, the powers of two, the
integer roots, the logarithms `lnQ q N_e` and `lnQ q (2d + 2)` by Mercator's sum, then the numerators of the rational
fields. The region is the slots `30, ..., 122`, the scratch starts at `128`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-! ## Notation for the steps -/

/-- The value of step `j` (the slot `30 + j`). -/
abbrev rv (j : ℕ) : IE := .sc (30 + j)
/-- `d` (slot `0`). -/
abbrev dI : IE := .sc 0
/-- `n` (slot `3`). -/
abbrev nI : IE := .sc 3
/-- Sum. -/
abbrev iA (a c : IE) : IE := .op .add a c
/-- Difference. -/
abbrev iS (a c : IE) : IE := .op .sub a c
/-- Product. -/
abbrev iM (a c : IE) : IE := .op .mul a c
/-- Euclidean quotient. -/
abbrev iD (a c : IE) : IE := .ediv a c

/-! ## The static test of PARAM -/

/-- The pairs of the values of `parSt` at the inputs `d, n ≤ 2^G`. -/
def parEtL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 4), (0, 5), (0, 5), (0, 6), (0, 8), (0, 2), (0, 3), (0, 7), (0, 6), (0, 10),
   (0, 11), (0, 14), (0, 8), (0, 21), (7, 21), (7, 22), (7, 22), (1, 2), (1, 2), (7, 28), (7, 23), (7, 23), (7, 30),
   (7, 31), (2, 4), (2, 4), (7, 32), (7, 33), (7, 33), (7, 39), (1, 0), (1, 0), (1, 0), (1, 0), (7, 31), (1, 0),
   (8, 21), (3, 0), (3, 0), (3, 0), (3, 0), (7, 31), (1, 0), (2, 0), (7, 23), (1, 0), (8, 22), (2, 0), (2, 1), (2, 1),
   (9, 23), (1, 3), (1, 4), (1, 4), (1, 5), (1, 0), (2, 4), (2, 0), (2, 1), (2, 1), (3, 5), (14, 58), (8, 40),
   (14, 65), (14, 65), (75, 343), (29, 141), (17, 66), (14, 70), (45, 206), (58, 288), (29, 143), (8, 41), (9, 41),
   (9, 41), (9, 42), (11, 52), (3, 0), (14, 67), (14, 67), (14, 68), (16, 74), (16, 72), (16, 72), (16, 73),
   (17, 76), (16, 74), (11, 54), (1, 3)]

/-- The pair of the value of step `j`. -/
def parEt (j : ℕ) : ℕ × ℕ := parEtL.getD j (0, 0)

/-- The largest pair over the steps. -/
def parT : ℕ × ℕ := (75, 343)

/-- The cells of PARAM: the region from `30`, the scratch from `128`, `0, 1, 2, 4` in the slots `1, 26, 27, 28`, the
scratch registers `8`, `9`, `1` in the register `rOne = 3`. -/
def parC : SLC := ⟨30, 128, 1, 26, 27, 28, 8, 9, 3⟩

/-- The pairs of the inputs `d`, `n`. -/
def parIn (_ : ℕ) : ℕ × ℕ := (1, 0)

end AdversarialBco.Bit.Transfer.BLM
