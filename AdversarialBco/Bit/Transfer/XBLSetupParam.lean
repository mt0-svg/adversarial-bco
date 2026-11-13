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

/-! ## The steps -/

/-- Procedure PARAM as a straight line; step `k` writes the slot `30 + k`. Constants `0 - 17`; sizes and precisions
`18 - 33`; powers of two `34 - 39`; `Λ`, the roots `40 - 44`; Mercator's sums and the logarithms `45 - 68`; the fields
`69 - 92`. -/
def parSt : List SStep :=
  [ .cst 1, .cst 2, .cst 4, .cst 8, .cst 10, .cst 16, .cst 24, .cst 40, .cst 160, .cst 3,      -- 0 - 9
    .cst 6, .cst 64, .cst 36, .cst 725, .cst 1450, .cst 14500, .cst 134, .cst 1966080,       -- 10 - 17
    -- 18: N_e = 15 2^17 d^3 n^4; 19: N_e + 1; 20: ℓe = size N_e
    .ie (iM (iM (iM (iM (iM (iM (iM (rv 17) dI) dI) dI) nI) nI) nI) nI),
    .ie (iA (rv 18) (rv 0)), .cl 19,
    -- 21: d + 1; 22: ℓd = size d; 23: p = 10 ℓe + 16 ℓd + 160
    .ie (iA dI (rv 0)), .cl 21, .ie (iA (iA (iM (rv 4) (rv 20)) (iM (rv 5) (rv 22))) (rv 8)),
    -- 24: ℓe + 1; 25: size ℓe; 26: q = p + 2 size ℓe + 24; 27: pF = p + 2 ℓe + 4 ℓd + 40
    .ie (iA (rv 20) (rv 0)), .cl 24, .ie (iA (iA (rv 23) (iM (rv 1) (rv 25))) (rv 6)),
    .ie (iA (iA (iA (rv 23) (iM (rv 1) (rv 20))) (iM (rv 2) (rv 22))) (rv 7)),
    -- 28: n (d + 2) + 1; 29: size (n (d + 2)); 30: B = 2 (p + size (n (d + 2)) + 2)
    .ie (iA (iM nI (iA (rv 21) (rv 0))) (rv 0)), .cl 28, .ie (iM (rv 1) (iA (iA (rv 23) (rv 29)) (rv 1))),
    -- 31: B + 1; 32: size B; 33: 2 gsm_prec B = 2 (B + 2 size B + 4)
    .ie (iA (rv 30) (rv 0)), .cl 31, .ie (iM (rv 1) (iA (iA (rv 30) (iM (rv 1) (rv 32))) (rv 2))),
    -- 34: 2^(2 p_B); 35: 2^p; 36: 2^pF; 37: 2^q
    .pw 33, .pw 23, .pw 27, .pw 26,
    -- 38: p - 3 ℓe - 6 ℓd - 64; 39: 1/ê
    .ie (iS (iS (iS (rv 23) (iM (rv 9) (rv 20))) (iM (rv 10) (rv 22))) (rv 11)), .pw 38,
    -- 40: Λ = d N_e; 41: d 4^q; 42: RD; 43: n 4^q; 44: RN
    .ie (iM dI (rv 18)), .ie (iM (iM dI (rv 37)) (rv 37)), .sq 41, .ie (iM (iM nI (rv 37)) (rv 37)), .sq 43,
    -- 45: q - 1; 46: 2^(q - 1); 47: M = gsm_mercq q 2^(q-1) q
    .ie (iS (rv 26) (rv 0)), .pw 45, .mc 26 37 46,
    -- 48: ℓe - 1; 49: 2^(ℓe - 1); 50: X_e; 51: Mercator's sum at X_e; 52, 53: max (M - it, 0); 54: lnQ q N_e at 2^q
    .ie (iS (rv 20) (rv 0)), .pw 48, .ie (iD (iM (iS (rv 18) (rv 49)) (rv 37)) (rv 18)), .mc 26 37 50,
    .ie (iS (rv 47) (rv 51)), .mx 52, .ie (iS (iM (rv 20) (rv 47)) (rv 53)),
    -- 55: 2 d + 2; 56: 2 d + 3; 57: its size s; 58: s - 1; 59: 2^(s - 1); 60: X_1; 61 - 63; 64: lnQ q (2d + 2) at 2^q
    .ie (iA (iM (rv 1) dI) (rv 1)), .ie (iA (rv 55) (rv 0)), .cl 56, .ie (iS (rv 57) (rv 0)), .pw 58,
    .ie (iD (iM (iS (rv 55) (rv 59)) (rv 37)) (rv 55)), .mc 26 37 60,
    .ie (iS (rv 47) (rv 61)), .mx 62, .ie (iS (iM (rv 57) (rv 47)) (rv 63)),
    -- 65: lnErr q N_e at 2^q; 66: lnErr q (2d + 2) at 2^q; 67: Le at 2^q; 68: 36 (L0 + η_e) at 2^q
    .ie (iM (iM (rv 1) (rv 20)) (iA (iM (rv 2) (rv 26)) (rv 0))),
    .ie (iM (iM (rv 1) (rv 57)) (iA (iM (rv 2) (rv 26)) (rv 0))),
    .ie (iM (rv 12) (iS (rv 54) (rv 65))), .ie (iM (rv 12) (iA (rv 54) (rv 65))),
    -- 69: ε'; 70: λ'; 71: η'; 72: sig2'; 73: ρ'; 74: κ_c'; 75: ν' (numerators at 2^pF)
    .ie (ieEps 0 (30 + 42) (30 + 44) (30 + 68) (30 + 36) (30 + 37) (30 + 15) (30 + 0)),
    .ie (iD (iA (iM (iM (rv 1) (iM (rv 37) (rv 37))) (rv 36)) (iM (iM (rv 13) dI) (iM (rv 67) (rv 67))))
      (iM (rv 1) (iM (iM (rv 13) dI) (iM (rv 67) (rv 67))))),
    .ie (iD (iA (iM (iM (rv 1) (iM (rv 42) (rv 37))) (rv 36)) (iM (rv 67) (rv 44)))
      (iM (rv 1) (iM (rv 67) (rv 44)))),
    .ie (iD (iA (iM (iM (rv 1) (rv 37)) (rv 36)) (iM (rv 3) (rv 67))) (iM (rv 1) (iM (rv 3) (rv 67)))),
    .ie (iD (iM (iM (iM (iM (iM (iM (rv 14) dI) dI) (rv 67)) (rv 67)) (rv 67)) (rv 36))
      (iM (iM (rv 37) (rv 37)) (rv 37))),
    .ie (iD (iA (iM (iM (rv 1) (iM (rv 71) (rv 70))) (rv 36))
        (iM (rv 2) (iM (iS (rv 36) (rv 70)) (iS (rv 36) (rv 70)))))
      (iM (rv 1) (iM (rv 2) (iM (iS (rv 36) (rv 70)) (iS (rv 36) (rv 70)))))),
    .ie (iD (iA (iM (iM (rv 1) (rv 36)) (rv 36)) (iS (rv 36) (rv 70))) (iM (rv 1) (iS (rv 36) (rv 70)))),
    -- 76: L1 + η_1 at 2^q; 77: times 2^q; 78: its root; 79: plus one; 80: R'
    .ie (iA (rv 64) (rv 66)), .ie (iM (rv 76) (rv 37)), .sq 77, .ie (iA (rv 78) (rv 0)),
    .ie (iD (iS (iA (iM (iM (iM (rv 16) dI) (rv 79)) (rv 36)) (rv 37)) (rv 0)) (rv 37)),
    -- 81: s'_b
    .ie (iD (iM (iM (rv 36) (rv 36)) (rv 36)) (iM (iM (iM (rv 18) (rv 18)) (rv 80)) (iA (rv 80) (rv 36)))),
    -- 82: N_e 4^q 2^q / Le, rounded up; 83: its root; 84: plus one; 85: W'
    .ie (iD (iS (iA (iM (rv 18) (iM (iM (rv 37) (rv 37)) (rv 37))) (rv 67)) (rv 0)) (rv 67)), .sq 82,
    .ie (iA (rv 83) (rv 0)),
    .ie (iD (iS (iA (iA (iM (rv 80) (rv 37)) (iM (iM (iM (rv 2) dI) (rv 84)) (rv 36))) (rv 37)) (rv 0)) (rv 37)),
    -- 86: sig2' 4^q rounded up; 87: its root; 88: plus one (2^q sqrtUp q sig2'); 89: A_0; 90: B_0 (at 2^p)
    .ie (iD (iS (iA (iM (rv 72) (iM (rv 37) (rv 37))) (rv 36)) (rv 0)) (rv 36)), .sq 86, .ie (iA (rv 87) (rv 0)),
    .ie (iD (iA (iM (iM (rv 1) (rv 88)) (rv 35)) (rv 37)) (iM (rv 1) (rv 37))),
    .ie (iD (iA (iM (iM (rv 1) (rv 37)) (rv 35)) (rv 88)) (iM (rv 1) (rv 88))),
    -- 91: R_int = ⌈R'⌉; 92: nBlk d = (d + 1)/2 + 1
    .ie (iD (iS (iA (rv 80) (rv 36)) (rv 0)) (rv 36)), .ie (iA (iD (rv 21) (rv 1)) (rv 0)) ]

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

theorem parSt_length : parSt.length = 93 := rfl

theorem parSt_chk : SL.chk 30 [0, 3] parIn parEt parT 44 parSt = true := by decide

end AdversarialBco.Bit.Transfer.BLM
