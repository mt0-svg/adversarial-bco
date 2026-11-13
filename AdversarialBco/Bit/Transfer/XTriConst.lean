/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriLoop
public import AdversarialBco.Bit.Transfer.XTriSh
public import AdversarialBco.Bit.Transfer.XBLSetupParV

@[expose] public section

/-!
# TRI-M, the constants as straight lines

* `tsSt`: the test of the parameter lemma at `s` (the loop of `triSQ d` runs it at `s = 4, 5, ...`);
* `tcSt`: the constants of TRI-OGD from `d`, `n` and `s = triSQ d`: `L_a`, `L_h`, `j_a`, `k_g`, `B_g`, `p`, `B_v`,
  `m_st`, `ℓ_pos`, `n_e`, `j_s`, `G`, `G_c` and the constants of a draw;
* their static tests (`tsSt_chk`, `tcSt_chk`) and their values (`tsV_k`, `tcV_k`) in closed form.

Both lines write the slots `120, ...` of the block; their inputs are `d`, `n`, `s` in the slots `113`, `114`, `115`.
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

/-- The constants of TRI-OGD from `d`, `n` and `s = triSQ d`, as a straight line; step `k` writes the slot `120 + k`.
Constants `0 - 19`; `L_a`, `L_h`, `r`, `b`, `elo`, `j_a`, `k_g`, `B_g`, `2 p` at `20 - 42`; `Δ²`, `B_v`, `g_u`, `g_b`
at `43 - 55`; `m_st`, `ℓ_pos`, `n_e`, `j_s`, `G`, `G_c` at `56 - 71`; the constants of a draw at `72 - 84`. -/
def tcSt : List SStep :=
  [ .cst 1, .cst 2, .cst 3, .cst 4, .cst 5, .cst 7, .cst 8, .cst 9, .cst 10, .cst 16,                 -- 0 - 9
    .cst 50, .cst 64, .cst 68, .cst 69, .cst 161, .cst 258986112, .cst 400000000, .cst 19999,          -- 10 - 17
    .cst 20000, .cst 1572864,                                                                           -- 18 - 19
    -- 20: s^2; 21: L_a; 22: L_h; 23: L_a - 3; 24: r = 2^{L_a - 3}; 25: L_a - 10; 26: 2^{L_a - 10}; 27: b
    .ie (iM tsI tsI), .ie (iD (iM (tcv 4) (tcv 20)) (tcv 5)), .ie (iD (iA (iM (tcv 10) (tcv 20)) (tcv 12)) (tcv 13)),
    .ie (iS (tcv 21) (tcv 2)), .pw 23, .ie (iS (tcv 21) (tcv 8)), .pw 25, .ie (iM (tcv 14) (tcv 26)),
    -- 28: 2^{L_h}; 29: elo = 258986112 d^2 L_h (2^{L_h} - 1); 30: 9 d s; 31: j_a; 32: 2^{j_a}
    .pw 22, .ie (iM (iM (iM (iM (tcv 15) tdI) tdI) (tcv 22)) (iS (tcv 28) (tcv 0))), .ie (iM (iM (tcv 7) tdI) tsI),
    .cl 30, .pw 31,
    -- 33: kgN = 16 b (d + 1) d (8 d + 2) elo; 34: ⌈kgN / 20000⌉; 35: its lg; 36 - 38: k_g = max 2 lg
    .ie (iM (iM (iM (iM (iM (tcv 9) (tcv 27)) (iA tdI (tcv 0))) tdI) (iA (iM (tcv 6) tdI) (tcv 1))) (tcv 29)),
    .ie (iD (iA (tcv 33) (tcv 17)) (tcv 18)), .cl 34, .ie (iS (tcv 35) (tcv 1)), .mx 36, .ie (iA (tcv 37) (tcv 1)),
    -- 39: B_g = 4 k_g; 40: B_g + 1; 41: size B_g; 42: 2 p = 2 (B_g + 2 size B_g + 4)
    .ie (iM (tcv 3) (tcv 38)), .ie (iA (tcv 39) (tcv 0)), .cl 40,
    .ie (iM (tcv 1) (iA (iA (tcv 39) (iM (tcv 1) (tcv 41))) (tcv 3))),
    -- 43: d2N = 4 d r^2 4^{j_a} + d (b 2^{j_a} - 1)^2 + 2 d (d - 1) b^2 4^{j_a}
    .ie (iA (iA (iM (iM (iM (iM (tcv 3) tdI) (iM (tcv 24) (tcv 24))) (tcv 32)) (tcv 32))
        (iM tdI (iM (iS (iM (tcv 27) (tcv 32)) (tcv 0)) (iS (iM (tcv 27) (tcv 32)) (tcv 0)))))
      (iM (iM (iM (iM (tcv 1) tdI) (iS tdI (tcv 0))) (iM (tcv 27) (tcv 27))) (iM (tcv 32) (tcv 32)))),
    -- 44: bvN = 64 (d + 1)^2 d2N elo^2; 45: bvD = 4^{j_a} 4 10^8; 46: ⌈bvN / bvD⌉; 47: its lg; 48: B_v
    .ie (iM (iM (iM (tcv 11) (iM (iA tdI (tcv 0)) (iA tdI (tcv 0)))) (tcv 43)) (iM (tcv 29) (tcv 29))),
    .ie (iM (iM (tcv 32) (tcv 32)) (tcv 16)), .ie (iD (iS (iA (tcv 44) (tcv 45)) (tcv 0)) (tcv 45)), .cl 46,
    .ie (iD (iA (tcv 47) (tcv 0)) (tcv 1)),
    -- 49: 2^{B_v}; 50: 8 d k_g; 51: its root; 52: j_a - 3; 53: 2^{j_a - 3}; 54: guN; 55: gbN = guN 2^{B_v} + d + 1
    .pw 48, .ie (iM (iM (tcv 6) tdI) (tcv 38)), .sq 50, .ie (iS (tcv 31) (tcv 2)), .pw 52,
    .ie (iA (iA (tcv 51) (tcv 1)) (tcv 53)), .ie (iA (iA (iM (tcv 54) (tcv 49)) tdI) (tcv 0)),
    -- 56: 2 n; 57: m_st = lg (2 n); 58: 3 2^19 (d n)^3 m_st; 59: ℓ_pos
    .ie (iM (tcv 1) tnI), .cl 56, .ie (iM (iM (tcv 19) (iM (iM (iM tdI tnI) (iM tdI tnI)) (iM tdI tnI))) (tcv 57)),
    .cl 58,
    -- 60: neN = 8 d2N elo^2 (9 gbN^2 + 8 guN^2 ℓ_pos 4^{B_v}); 61: neD = 9 4^{B_v + j_a} 4 10^8; 62: ⌈neN / neD⌉;
    -- 63: n_e; 64: 2^{n_e}
    .ie (iM (iM (iM (tcv 6) (tcv 43)) (iM (tcv 29) (tcv 29)))
      (iA (iM (tcv 7) (iM (tcv 55) (tcv 55)))
        (iM (iM (iM (tcv 6) (iM (tcv 54) (tcv 54))) (tcv 59)) (iM (tcv 49) (tcv 49))))),
    .ie (iM (iM (iM (tcv 7) (iM (tcv 49) (tcv 49))) (iM (tcv 32) (tcv 32))) (tcv 16)),
    .ie (iD (iS (iA (tcv 60) (tcv 61)) (tcv 0)) (tcv 61)), .cl 62, .pw 63,
    -- 65: jsN = gbN^2 2^{n_e} 4^{j_a}; 66: jsD = 4^{B_v} d2N; 67: ⌈jsN / jsD⌉; 68: its lg; 69: j_s
    .ie (iM (iM (iM (tcv 55) (tcv 55)) (tcv 64)) (iM (tcv 32) (tcv 32))), .ie (iM (iM (tcv 49) (tcv 49)) (tcv 43)),
    .ie (iD (iS (iA (tcv 65) (tcv 66)) (tcv 0)) (tcv 66)), .cl 67, .ie (iD (iA (tcv 68) (tcv 0)) (tcv 1)),
    -- 70: G = B_v + j_s + j_a; 71: G_c = G + n_e; 72: P_2 = 2^{2p}; 73: P_G = 2^G; 74: L_a - 3 + G; 75: R;
    -- 76: -R; 77: B_v + j_s; 78: A_l; 79: L_a - 10 + G; 80: 2^{L_a - 10 + G}; 81: B_h; 82: -B_h; 83: 8 d;
    -- 84: 2^{G_c}
    .ie (iA (iA (tcv 48) (tcv 69)) (tcv 31)), .ie (iA (tcv 70) (tcv 63)), .pw 42, .pw 70, .ie (iA (tcv 23) (tcv 70)),
    .pw 74, .ie (iM (iS (tcv 0) (tcv 1)) (tcv 75)), .ie (iA (tcv 48) (tcv 69)), .pw 77, .ie (iA (tcv 25) (tcv 70)),
    .pw 79, .ie (iM (tcv 14) (tcv 80)), .ie (iM (iS (tcv 0) (tcv 1)) (tcv 81)), .ie (iM (tcv 6) tdI), .pw 71 ]

/-! ## The static tests -/

/-- The pairs of the values of `tsSt`. -/
def tsEtL : List (ℕ × ℕ) :=
  [(0, 3), (0, 3), (0, 6), (0, 7), (0, 7), (0, 1), (0, 7), (0, 21), (2, 0), (2, 3), (2, 8), (1, 0), (2, 11), (4, 29)]

/-- The pair of the value of step `j` of the test. -/
def tsEt (j : ℕ) : ℕ × ℕ := tsEtL.getD j (0, 0)

/-- The pairs of the values of `tcSt`. -/
def tcEtL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 5), (0, 6), (0, 7), (0, 7), (0, 7),
   (0, 8), (0, 28), (0, 29), (0, 15), (0, 15), (0, 21), (2, 0), (2, 3), (2, 8), (2, 4), (1, 0), (2, 5), (1, 0), (1, 8),
   (1, 0), (5, 38), (2, 4), (2, 4), (1, 0), (9, 58), (9, 59), (9, 59), (9, 60), (9, 60), (9, 61), (9, 64), (9, 65),
   (9, 65), (9, 71), (6, 21), (18, 108), (2, 29), (18, 110), (18, 110), (18, 111), (1, 0), (10, 65), (10, 65), (2, 5),
   (1, 0), (10, 67), (11, 69), (1, 2), (1, 2), (7, 23), (7, 23), (45, 263), (4, 33), (45, 265), (45, 265), (1, 0),
   (25, 138), (8, 21), (25, 140), (25, 140), (25, 141), (25, 143), (45, 266), (1, 0), (1, 0), (25, 144), (1, 0),
   (1, 3), (25, 142), (1, 0), (25, 144), (1, 0), (1, 8), (1, 11), (1, 4), (1, 0)]

/-- The pair of the value of step `j` of the constants. -/
def tcEt (j : ℕ) : ℕ × ℕ := tcEtL.getD j (0, 0)

/-- The largest pair a step needs below `ℓ`. -/
def tcT : ℕ × ℕ := (45, 266)

/-- The cells of both lines: the region from `120`, the scratch from `205` (`40` slots), `0, 1, 2, 4` in the slots
`1, 2, 116, 117`, the scratch registers `29`, `30`, `1` in the register `0`. -/
def tcC : SLC := ⟨120, 205, 1, 2, 116, 117, 29, 30, 0⟩

/-- The pairs of the inputs `d`, `n`, `s`. -/
def tcInP (_ : ℕ) : ℕ × ℕ := (1, 0)

theorem tsSt_length : tsSt.length = 14 := rfl

theorem tcSt_length : tcSt.length = 85 := rfl

theorem tsSt_chk : SL.chk 120 [113, 115] tcInP tsEt tcT 40 tsSt = true := by decide

theorem tcSt_chk : SL.chk 120 [113, 114, 115] tcInP tcEt tcT 40 tcSt = true := by decide

theorem tsSt_units : SL.unitsP tsEt tsSt = (4, 44) := by decide

theorem tcSt_units : SL.unitsP tcEt tcSt = (636, 3897) := by decide

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

/-- The inputs of the constants: `d`, `n`, `triSQ d` in the slots `113`, `114`, `115`. -/
def tcIn (d n : ℕ) : ℕ → ℤ := fun y => if y = 113 then d else if y = 114 then n else if y = 115 then triSQ d else 0

/-- The value of step `k` of the constants at `d`, `n`. -/
abbrev tcV (d n k : ℕ) : ℤ := SL.val tcSt 120 (tcIn d n) k

theorem tcV_c (d n k : ℕ) :
    tcV d n k = (tcSt.getD k (.cst 0)).sem 120 (tcIn d n) (fun j => if j < k then tcV d n j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the constants unfolded. -/
macro "tcs" : tactic => `(tactic| (rw [tcV_c]; simp only [tcSt, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, tcv, tdI, tnI, tsI, iM, iA, iS, iD, tcIn, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceEqDiff, ↓reduceIte]))

section TcValues

variable (d n : ℕ)

theorem tcV_0 : tcV d n 0 = 1 := by tcs
theorem tcV_1 : tcV d n 1 = 2 := by tcs
theorem tcV_2 : tcV d n 2 = 3 := by tcs
theorem tcV_3 : tcV d n 3 = 4 := by tcs
theorem tcV_4 : tcV d n 4 = 5 := by tcs
theorem tcV_5 : tcV d n 5 = 7 := by tcs
theorem tcV_6 : tcV d n 6 = 8 := by tcs
theorem tcV_7 : tcV d n 7 = 9 := by tcs
theorem tcV_8 : tcV d n 8 = 10 := by tcs
theorem tcV_9 : tcV d n 9 = 16 := by tcs
theorem tcV_10 : tcV d n 10 = 50 := by tcs
theorem tcV_11 : tcV d n 11 = 64 := by tcs
theorem tcV_12 : tcV d n 12 = 68 := by tcs
theorem tcV_13 : tcV d n 13 = 69 := by tcs
theorem tcV_14 : tcV d n 14 = 161 := by tcs
theorem tcV_15 : tcV d n 15 = 258986112 := by tcs
theorem tcV_16 : tcV d n 16 = 400000000 := by tcs
theorem tcV_17 : tcV d n 17 = 19999 := by tcs
theorem tcV_18 : tcV d n 18 = 20000 := by tcs
theorem tcV_19 : tcV d n 19 = 1572864 := by tcs




theorem tcV_20 : tcV d n 20 = ((triSQ d ^ 2 : ℕ) : ℤ) := by tcs; push_cast; ring
theorem tcV_21 : tcV d n 21 = (triLa (triSQ d) : ℤ) := by
  tcs; rw [tcV_4, tcV_20, tcV_5]; unfold triLa; push_cast; rfl
theorem tcV_22 : tcV d n 22 = (triLh (triSQ d) : ℤ) := by
  tcs; rw [tcV_10, tcV_20, tcV_12, tcV_13]; unfold triLh; push_cast; rfl
theorem tcV_23 : tcV d n 23 = ((triLa (triSQ d) - 3 : ℕ) : ℤ) := by
  tcs; rw [tcV_21, tcV_2]; have := triLa_ge d; push_cast [show 3 ≤ triLa (triSQ d) by omega]; ring
theorem tcV_24 : tcV d n 24 = (rI d : ℤ) := by
  tcs; rw [tcV_23, Int.toNat_natCast]; unfold rI; push_cast; rfl
theorem tcV_25 : tcV d n 25 = ((triLa (triSQ d) - 10 : ℕ) : ℤ) := by
  tcs; rw [tcV_21, tcV_8]; have := triLa_ge d; push_cast [this]; ring
theorem tcV_26 : tcV d n 26 = ((2 ^ (triLa (triSQ d) - 10) : ℕ) : ℤ) := by
  tcs; rw [tcV_25, Int.toNat_natCast]; norm_cast
theorem tcV_27 : tcV d n 27 = (bI d : ℤ) := by
  tcs; rw [tcV_14, tcV_26]; unfold bI; push_cast; ring
theorem tcV_28 : tcV d n 28 = ((2 ^ triLh (triSQ d) : ℕ) : ℤ) := by
  tcs; rw [tcV_22, Int.toNat_natCast]; norm_cast
theorem tcV_29 : tcV d n 29 = (eloI d : ℤ) := by
  tcs; rw [tcV_15, tcV_22, tcV_28, tcV_0]; unfold eloI
  have : 1 ≤ 2 ^ triLh (triSQ d) := Nat.one_le_two_pow
  push_cast [this]; ring
theorem tcV_30 : tcV d n 30 = ((9 * d * triSQ d : ℕ) : ℤ) := by
  tcs; rw [tcV_7]; push_cast; ring
theorem tcV_31 : tcV d n 31 = (triJaQ d : ℤ) := by
  tcs; rw [tcV_30, Int.toNat_natCast]; rfl
theorem tcV_32 : tcV d n 32 = ((2 ^ triJaQ d : ℕ) : ℤ) := by
  tcs; rw [tcV_31, Int.toNat_natCast]; norm_cast
theorem tcV_33 : tcV d n 33 = (kgN d : ℤ) := by
  tcs; rw [tcV_9, tcV_27, tcV_0, tcV_6, tcV_1, tcV_29]; unfold kgN; push_cast; ring
theorem tcV_34 : tcV d n 34 = (((kgN d + 19999) / 20000 : ℕ) : ℤ) := by
  tcs; rw [tcV_33, tcV_17, tcV_18]; push_cast; rfl
theorem tcV_35 : tcV d n 35 = (Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) := by
  tcs; rw [tcV_34, Int.toNat_natCast]
theorem tcV_36 : tcV d n 36 = (Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) - 2 := by tcs; rw [tcV_35, tcV_1]
theorem tcV_37 : tcV d n 37 = max ((Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) - 2) 0 := by tcs; rw [tcV_36]
theorem tcV_38 (hd : 1 ≤ d) : tcV d n 38 = (triKgQ d : ℤ) := by
  tcs; rw [tcV_37, tcV_1, triKgQ_eq hd]; push_cast; omega
theorem tcV_39 (hd : 1 ≤ d) : tcV d n 39 = (triBgQ d : ℤ) := by
  tcs; rw [tcV_3, tcV_38 d n hd]; unfold triBgQ; push_cast; ring
theorem tcV_40 (hd : 1 ≤ d) : tcV d n 40 = ((triBgQ d + 1 : ℕ) : ℤ) := by
  tcs; rw [tcV_39 d n hd, tcV_0]; push_cast; ring
theorem tcV_41 (hd : 1 ≤ d) : tcV d n 41 = ((triBgQ d).size : ℤ) := by
  tcs; rw [tcV_40 d n hd, Int.toNat_natCast, ← size_eq_clog]
theorem tcV_42 (hd : 1 ≤ d) : tcV d n 42 = ((2 * tzP d : ℕ) : ℤ) := by
  tcs; rw [tcV_1, tcV_39 d n hd, tcV_41 d n hd, tcV_3]; unfold tzP gsm_prec; push_cast; ring
theorem tcV_43 (hd : 1 ≤ d) : tcV d n 43 = (d2N d : ℤ) := by
  tcs; rw [tcV_3, tcV_24, tcV_32, tcV_27, tcV_0, tcV_1]; unfold d2N
  have h1 : 1 ≤ bI d * 2 ^ triJaQ d := Nat.one_le_iff_ne_zero.2 (by unfold bI; positivity)
  push_cast [h1, hd]; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem tcV_44 (hd : 1 ≤ d) : tcV d n 44 = (bvN d : ℤ) := by
  tcs; rw [tcV_11, tcV_0, tcV_43 d n hd, tcV_29]; unfold bvN; push_cast; ring
theorem tcV_45 : tcV d n 45 = (bvD d : ℤ) := by
  tcs; rw [tcV_32, tcV_16]; unfold bvD; push_cast; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem bvD_pos : 1 ≤ bvD d := by unfold bvD; have := Nat.one_le_pow (triJaQ d) 4 (by norm_num); omega
theorem tcV_46 (hd : 1 ≤ d) : tcV d n 46 = (((bvN d + bvD d - 1) / bvD d : ℕ) : ℤ) := by
  have hD := bvD_pos d
  tcs; rw [tcV_44 d n hd, tcV_45, tcV_0]; push_cast [show 1 ≤ bvN d + bvD d by omega]; rfl
theorem tcV_47 (hd : 1 ≤ d) : tcV d n 47 = (Nat.clog 2 ((bvN d + bvD d - 1) / bvD d) : ℤ) := by
  tcs; rw [tcV_46 d n hd, Int.toNat_natCast]
theorem tcV_48 (hd : 1 ≤ d) : tcV d n 48 = (triBvQ d : ℤ) := by
  tcs; rw [tcV_47 d n hd, tcV_0, tcV_1, triBvQ_eq hd, clog4_eq]; push_cast; rfl
theorem tcV_49 (hd : 1 ≤ d) : tcV d n 49 = ((2 ^ triBvQ d : ℕ) : ℤ) := by
  tcs; rw [tcV_48 d n hd, Int.toNat_natCast]; norm_cast
theorem tcV_50 (hd : 1 ≤ d) : tcV d n 50 = ((8 * d * triKgQ d : ℕ) : ℤ) := by
  tcs; rw [tcV_6, tcV_38 d n hd]; push_cast; ring
theorem tcV_51 (hd : 1 ≤ d) : tcV d n 51 = (Nat.sqrt (8 * d * triKgQ d) : ℤ) := by
  tcs; rw [tcV_50 d n hd, Int.toNat_natCast]
theorem tcV_52 (hd : 1 ≤ d) : tcV d n 52 = ((triJaQ d - 3 : ℕ) : ℤ) := by
  tcs; rw [tcV_31, tcV_2]; have := triJaQ_ge hd; push_cast [show 3 ≤ triJaQ d by omega]; ring
theorem tcV_53 (hd : 1 ≤ d) : tcV d n 53 = ((2 ^ (triJaQ d - 3) : ℕ) : ℤ) := by
  tcs; rw [tcV_52 d n hd, Int.toNat_natCast]; norm_cast
theorem tcV_54 (hd : 1 ≤ d) : tcV d n 54 = (guN d : ℤ) := by
  tcs; rw [tcV_51 d n hd, tcV_1, tcV_53 d n hd]; unfold guN; push_cast; ring
theorem tcV_55 (hd : 1 ≤ d) : tcV d n 55 = (gbN d : ℤ) := by
  tcs; rw [tcV_54 d n hd, tcV_49 d n hd, tcV_0]; unfold gbN; push_cast; ring
theorem tcV_56 : tcV d n 56 = ((2 * n : ℕ) : ℤ) := by tcs; rw [tcV_1]; push_cast; ring
theorem tcV_57 : tcV d n 57 = (Nat.clog 2 (2 * n) : ℤ) := by tcs; rw [tcV_56, Int.toNat_natCast]
theorem tcV_58 : tcV d n 58 = ((3 * 2 ^ 19 * (d * n) ^ 3 * Nat.clog 2 (2 * n) : ℕ) : ℤ) := by
  tcs; rw [tcV_19, tcV_57]; push_cast; ring
theorem tcV_59 (hn : 1 ≤ n) : tcV d n 59 = (ellPos d n : ℤ) := by
  tcs; rw [tcV_58, Int.toNat_natCast, ellPos_eq d n hn]
theorem tcV_60 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 60 = (neN d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_6, tcV_43 d n hd, tcV_29, tcV_7, tcV_55 d n hd, tcV_54 d n hd, tcV_59 d n hn, tcV_49 d n hd]
  unfold neN; push_cast; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem tcV_61 (hd : 1 ≤ d) : tcV d n 61 = (neD d : ℤ) := by
  tcs; rw [tcV_7, tcV_49 d n hd, tcV_32, tcV_16]; unfold neD; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem neD_pos : 1 ≤ neD d := by
  unfold neD; have := Nat.one_le_pow (triBvQ d + triJaQ d) 4 (by norm_num); omega
theorem tcV_62 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 62 = (((neN d (ellPos d n) + neD d - 1) / neD d : ℕ) : ℤ) := by
  have hD := neD_pos d
  tcs; rw [tcV_60 d n hd hn, tcV_61 d n hd, tcV_0]; push_cast [show 1 ≤ neN d (ellPos d n) + neD d by omega]; rfl
theorem tcV_63 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 63 = (triNeQ d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_62 d n hd hn, Int.toNat_natCast, triNeQ_eq hd]
theorem tcV_64 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 64 = ((2 ^ triNeQ d (ellPos d n) : ℕ) : ℤ) := by
  tcs; rw [tcV_63 d n hd hn, Int.toNat_natCast]; norm_cast
theorem tcV_65 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 65 = (jsN d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_55 d n hd, tcV_64 d n hd hn, tcV_32]; unfold jsN; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem tcV_66 (hd : 1 ≤ d) : tcV d n 66 = (jsD d : ℤ) := by
  tcs; rw [tcV_49 d n hd, tcV_43 d n hd]; unfold jsD; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem jsD_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ jsD d := by
  unfold jsD; have := Nat.one_le_pow (triBvQ d) 4 (by norm_num); have := d2N_pos hd; nlinarith
theorem tcV_67 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 67 = (((jsN d (ellPos d n) + jsD d - 1) / jsD d : ℕ) : ℤ) := by
  have hD := jsD_pos hd
  tcs; rw [tcV_65 d n hd hn, tcV_66 d n hd, tcV_0]; push_cast [show 1 ≤ jsN d (ellPos d n) + jsD d by omega]; rfl
theorem tcV_68 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 68 = (Nat.clog 2 ((jsN d (ellPos d n) + jsD d - 1) / jsD d) : ℤ) := by
  tcs; rw [tcV_67 d n hd hn, Int.toNat_natCast]
theorem tcV_69 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 69 = (triJsQ d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_68 d n hd hn, tcV_0, tcV_1, triJsQ_eq hd, clog4_eq]; push_cast; rfl
theorem tcV_70 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 70 = (tzG d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_48 d n hd, tcV_69 d n hd hn, tcV_31]; unfold tzG; push_cast; ring
theorem tcV_71 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 71 = (tzGc d (ellPos d n) : ℤ) := by
  tcs; rw [tcV_70 d n hd hn, tcV_63 d n hd hn]; unfold tzGc; push_cast; ring
theorem tcV_72 (hd : 1 ≤ d) : tcV d n 72 = (tzDC d (ellPos d n)).P2 := by
  tcs; rw [tcV_42 d n hd, Int.toNat_natCast]; simp only [tzDC]
theorem tcV_73 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 73 = (tzDC d (ellPos d n)).PG := by
  tcs; rw [tcV_70 d n hd hn, Int.toNat_natCast]; simp only [tzDC]
theorem tcV_74 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 74 = ((triLa (triSQ d) - 3 + tzG d (ellPos d n) : ℕ) : ℤ) := by
  tcs; rw [tcV_23, tcV_70 d n hd hn]; push_cast; ring
theorem tcV_75 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 75 = (tzDC d (ellPos d n)).R := by
  tcs; rw [tcV_74 d n hd hn, Int.toNat_natCast]; simp only [tzDC]
theorem tcV_76 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 76 = -(tzDC d (ellPos d n)).R := by
  tcs; rw [tcV_0, tcV_1, tcV_75 d n hd hn]; ring
theorem tcV_77 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 77 = ((triBvQ d + triJsQ d (ellPos d n) : ℕ) : ℤ) := by
  tcs; rw [tcV_48 d n hd, tcV_69 d n hd hn]; push_cast; ring
theorem tcV_78 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 78 = (tzDC d (ellPos d n)).Al := by
  tcs; rw [tcV_77 d n hd hn, Int.toNat_natCast]; simp only [tzDC]
theorem tcV_79 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 79 = ((triLa (triSQ d) - 10 + tzG d (ellPos d n) : ℕ) : ℤ) := by
  tcs; rw [tcV_25, tcV_70 d n hd hn]; push_cast; ring
theorem tcV_80 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    tcV d n 80 = ((2 ^ (triLa (triSQ d) - 10 + tzG d (ellPos d n)) : ℕ) : ℤ) := by
  tcs; rw [tcV_79 d n hd hn, Int.toNat_natCast]; norm_cast
theorem tcV_81 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 81 = (tzDC d (ellPos d n)).Bh := by
  tcs; rw [tcV_14, tcV_80 d n hd hn]; simp only [tzDC]; push_cast; ring
theorem tcV_82 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 82 = -(tzDC d (ellPos d n)).Bh := by
  tcs; rw [tcV_0, tcV_1, tcV_81 d n hd hn]; ring
theorem tcV_83 : tcV d n 83 = 8 * (tzDC d (ellPos d n)).dd := by
  tcs; rw [tcV_6]; simp only [tzDC]
theorem tcV_84 (hd : 1 ≤ d) (hn : 1 ≤ n) : tcV d n 84 = 2 ^ tzGc d (ellPos d n) := by
  tcs; rw [tcV_71 d n hd hn, Int.toNat_natCast]

end TcValues

end AdversarialBco.Bit.Transfer
