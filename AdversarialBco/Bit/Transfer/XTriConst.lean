/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriStage
public import AdversarialBco.Bit.Transfer.XTriAux
public import AdversarialBco.Bit.Transfer.XTriSh
public import AdversarialBco.Bit.Transfer.XBLSetupParV

@[expose] public section

/-!
# TRI-M, the constants as straight lines

* `tsSt`: the test of the parameter lemma at `s` (the loop of `triSQ d` runs it at `s = 4, 5, ...`), with its static
  test (`tsSt_chk`) and its values (`tsV_k`) in closed form.

The line writes the slots `120, ...` of the block; its inputs are `d`, `n`, `s` in the slots `113`, `114`, `115`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

/-! ## The steps -/

/-- The value of step `j` (the slot `120 + j` of the block). -/
abbrev tcv (j : ℕ) : IE := .sc (120 + j)
/-- `d` (slot `113` of the block). -/
abbrev tdI : IE := .sc 113
/-- `n` (slot `114` of the block). -/
abbrev tnI : IE := .sc 114
/-- `s` (slot `115` of the block). -/
abbrev tsI : IE := .sc 115

/-- The test of the parameter lemma at `s`, as a straight line; step `k` writes the slot `120 + k`: `12` is
`125 (2^{L_a(s)} - 1)^2`, `13` is `2086812 d^2 L_h(s)`. -/
def tsSt : List SStep :=
  [ .cst 5, .cst 7, .cst 50, .cst 68, .cst 69, .cst 1, .cst 125, .cst 2086812,                -- 0 - 7
    -- 8: s^2; 9: L_a = 5 s^2 / 7; 10: L_h = (50 s^2 + 68) / 69; 11: 2^{L_a}
    .ie (iM tsI tsI), .ie (iD (iM (tcv 0) (tcv 8)) (tcv 1)), .ie (iD (iA (iM (tcv 2) (tcv 8)) (tcv 3)) (tcv 4)), .pw 9,
    -- 12: 125 (2^{L_a} - 1)^2; 13: 2086812 d^2 L_h
    .ie (iM (tcv 6) (iM (iS (tcv 11) (tcv 5)) (iS (tcv 11) (tcv 5)))), .ie (iM (iM (iM (tcv 7) tdI) tdI) (tcv 10)) ]

/-! ## The static tests -/

/-- The pairs of the values of `tsSt`. -/
def tsEtL : List (ℕ × ℕ) :=
  [(0, 3), (0, 3), (0, 6), (0, 7), (0, 7), (0, 1), (0, 7), (0, 21), (2, 0), (2, 3), (2, 8), (1, 0), (2, 11), (4, 29)]

/-- The pair of the value of step `j` of the test. -/
def tsEt (j : ℕ) : ℕ × ℕ := tsEtL.getD j (0, 0)

/-- The largest pair a step needs below `ℓ`. -/
def tcT : ℕ × ℕ := (45, 266)

/-- The cells of both lines: the region from `120`, the scratch from `205` (`40` slots), `0, 1, 2, 4` in the slots
`1, 2, 116, 117`, the scratch registers `29`, `30`, `1` in the register `0`. -/
def tcC : SLC := ⟨120, 205, 1, 2, 116, 117, 29, 30, 0⟩

/-- The pairs of the inputs `d`, `n`, `s`. -/
def tcInP (_ : ℕ) : ℕ × ℕ := (1, 0)

theorem tsSt_length : tsSt.length = 14 := rfl

theorem tsSt_chk : SL.chk 120 [113, 115] tcInP tsEt tcT 40 tsSt = true := by decide

theorem tsSt_units : SL.unitsP tsEt tsSt = (4, 44) := by decide

/-! ## The values of the test of the parameter lemma -/

/-- The inputs of the test: `d` in the slot `113`, `s` in the slot `115`. -/
def tsIn (d s : ℕ) : ℕ → ℤ := fun y => if y = 113 then d else if y = 115 then s else 0

/-- The value of step `k` of the test at `d`, `s`. -/
abbrev tsV (d s k : ℕ) : ℤ := SL.val tsSt 120 (tsIn d s) k

theorem tsV_c (d s k : ℕ) :
    tsV d s k = (tsSt.getD k (.cst 0)).sem 120 (tsIn d s) (fun j => if j < k then tsV d s j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the test unfolded. -/
macro "tss" : tactic => `(tactic| (rw [tsV_c]; simp only [tsSt, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, tcv, tdI, tsI, iM, iA, iS, iD, tsIn, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceEqDiff, ↓reduceIte]))

section TsValues

variable (d s : ℕ)

theorem tsV_0 : tsV d s 0 = 5 := by tss
theorem tsV_1 : tsV d s 1 = 7 := by tss
theorem tsV_2 : tsV d s 2 = 50 := by tss
theorem tsV_3 : tsV d s 3 = 68 := by tss
theorem tsV_4 : tsV d s 4 = 69 := by tss
theorem tsV_5 : tsV d s 5 = 1 := by tss
theorem tsV_6 : tsV d s 6 = 125 := by tss
theorem tsV_7 : tsV d s 7 = 2086812 := by tss
theorem tsV_8 : tsV d s 8 = ((s ^ 2 : ℕ) : ℤ) := by tss; push_cast; ring
theorem tsV_9 : tsV d s 9 = (triLa s : ℤ) := by
  tss; rw [tsV_0, tsV_8, tsV_1]; unfold triLa; push_cast; rfl
theorem tsV_10 : tsV d s 10 = (triLh s : ℤ) := by
  tss; rw [tsV_2, tsV_8, tsV_3, tsV_4]; unfold triLh; push_cast; rfl
theorem tsV_11 : tsV d s 11 = ((2 ^ triLa s : ℕ) : ℤ) := by
  tss; rw [tsV_9, Int.toNat_natCast]; push_cast; rfl
theorem tsV_12 : tsV d s 12 = ((125 * (2 ^ triLa s - 1) ^ 2 : ℕ) : ℤ) := by
  tss; rw [tsV_6, tsV_11, tsV_5]
  have : 1 ≤ 2 ^ triLa s := Nat.one_le_two_pow
  push_cast [this]; ring
theorem tsV_13 : tsV d s 13 = ((2086812 * d ^ 2 * triLh s : ℕ) : ℤ) := by
  tss; rw [tsV_7, tsV_10]; push_cast; ring

end TsValues

/-! ## The values of the constants -/

/-- One step of the constants unfolded. -/
macro "tcs" : tactic => `(tactic| (rw [tcV_c]; simp only [tcSt, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, tcv, tdI, tnI, tsI, iM, iA, iS, iD, tcIn, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceEqDiff, ↓reduceIte]))

section TcValues

variable (d n : ℕ)





theorem bvD_pos : 1 ≤ bvD d := by unfold bvD; have := Nat.one_le_pow (triJaQ d) 4 (by norm_num); omega
theorem neD_pos : 1 ≤ neD d := by
  unfold neD; have := Nat.one_le_pow (triBvQ d + triJaQ d) 4 (by norm_num); omega

end TcValues

end AdversarialBco.Bit.Transfer
