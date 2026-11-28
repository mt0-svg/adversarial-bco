/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriKX
public import AdversarialBco.Bit.Transfer.XTriConstRun

@[expose] public section

/-!
# BL-O's setup: the constants of TRI-OGD-O as a straight line

`poSt`: v2.1's line `tcSt` (Bit/Transfer/XTriConst.lean) up to step `55` (`L_a`, `L_h`, `j_a`, `k_g`, `B_g`, `p`,
`Δ²`, `B_v`, `g_u`, `g_b`), then BL-O's: `m_st = clog₂ (max q 2) = max 1 (clog₂ q)` from `q = ⌈R₀/r₀⌉` (from
the inputs `R₀n, R₀d, r₀n, r₀d`), the confidence integer `ℓ = clog₂ (3 · 2^{19+k} (d n)³ m_st)` from `k = k_δ`,
`n_e' = n_e(ℓ) + 1`, `j_s'` at `G_up' = (65/64) G_up`, `G'`, `G_c'`, the constants of a draw `tzDCO d ℓ`, the
constants of SEP, of the gauge and of the stage test (`e₁`, `e_τ`, `stE1`, `stE`, `stEH`, `stEEta`, `stJ`, `stEu`,
`stK`) and their powers of two; `126` steps on the slots `120, ...` of the block, inputs `k, r₀n, r₀d, d, n, s, R₀n,
R₀d` in the slots `110 - 115, 118, 119`. The static test (`poSt_chk`, pair table `poEt`), the
units (`poSt_units`) and the values `poV_k` in closed form; the integer forms `triJsTQ_eq`, `triE1Q_eq`, `triETauQ_eq`, `stEH_eq` of the new exponents.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO

/-! ## The steps -/

/-- `k = k_δ` (slot `110` of the block). -/
abbrev tkI : IE := .sc 110
/-- `r₀n`, the numerator of `r₀` (slot `111`). -/
abbrev trnI : IE := .sc 111
/-- `r₀d`, the denominator of `r₀` (slot `112`). -/
abbrev trdI : IE := .sc 112
/-- `R₀n`, the numerator of `R₀` (slot `118`). -/
abbrev tRnI : IE := .sc 118
/-- `R₀d`, the denominator of `R₀` (slot `119`). -/
abbrev tRdI : IE := .sc 119

/-- **The constants of TRI-OGD-O for BL-O** as a straight line; step `k` writes the slot `120 + k`. Steps `0 - 55`
are v2.1's `tcSt`; `m_st`, `ℓ`, `n_e'` at `56 - 69`; `j_s'` at `70 - 76`; `G'`, `G_c'` and the constants of a draw at
`77 - 91`; SEP's, the gauge's and the stage test's at `92 - 121`; `stK` at `122 - 125`. -/
def poSt : List SStep :=
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
    -- 56: q - 2, q = ⌈R₀/r₀⌉ = (R₀n r₀d + R₀d r₀n - 1) / (R₀d r₀n); 57: max 0; 58: max q 2; 59: m_st = lg (max q 2);
    -- 60: k; 61: 2^k; 62: 3 2^(19+k) (d n)^3 m_st; 63: ℓ
    .ie (iS (iD (iS (iA (iM tRnI trdI) (iM tRdI trnI)) (tcv 0)) (iM tRdI trnI)) (tcv 1)), .mx 56,
    .ie (iA (tcv 57) (tcv 1)), .cl 58, .ie (iM tkI (tcv 0)), .pw 60,
    .ie (iM (iM (iM (tcv 19) (tcv 61)) (iM (iM (iM tdI tnI) (iM tdI tnI)) (iM tdI tnI))) (tcv 59)), .cl 62,
    -- 64: neN; 65: neD; 66: ceil; 67: n_e; 68: n_e' = n_e + 1; 69: 2^{n_e'}
    .ie (iM (iM (iM (tcv 6) (tcv 43)) (iM (tcv 29) (tcv 29)))
      (iA (iM (tcv 7) (iM (tcv 55) (tcv 55)))
        (iM (iM (iM (tcv 6) (iM (tcv 54) (tcv 54))) (tcv 63)) (iM (tcv 49) (tcv 49))))),
    .ie (iM (iM (iM (tcv 7) (iM (tcv 49) (tcv 49))) (iM (tcv 32) (tcv 32))) (tcv 16)),
    .ie (iD (iS (iA (tcv 64) (tcv 65)) (tcv 0)) (tcv 65)), .cl 66, .ie (iA (tcv 67) (tcv 0)), .pw 68,
    -- 70: 65; 71: gbN' = 65 guN 2^{B_v} + 64 (d + 1); 72: jsN'; 73: jsD' = 4096 4^{B_v} d2N; 74: ceil; 75: lg; 76: j_s'
    .cst 65, .ie (iA (iM (iM (tcv 70) (tcv 54)) (tcv 49)) (iM (tcv 11) (iA tdI (tcv 0)))),
    .ie (iM (iM (iM (tcv 71) (tcv 71)) (tcv 69)) (iM (tcv 32) (tcv 32))),
    .ie (iM (iM (iM (tcv 11) (tcv 11)) (iM (tcv 49) (tcv 49))) (tcv 43)),
    .ie (iD (iS (iA (tcv 72) (tcv 73)) (tcv 0)) (tcv 73)), .cl 74, .ie (iD (iA (tcv 75) (tcv 0)) (tcv 1)),
    -- 77: G'; 78: G_c'; 79: P_2; 80: P_G; 81: L_a - 3 + G'; 82: R; 83: -R; 84: B_v + j_s'; 85: A_l;
    -- 86: L_a - 10 + G'; 87: 2^{85}; 88: B_h; 89: -B_h; 90: 8 d; 91: 2^{G_c'}
    .ie (iA (iA (tcv 48) (tcv 76)) (tcv 31)), .ie (iA (tcv 77) (tcv 68)), .pw 42, .pw 77, .ie (iA (tcv 23) (tcv 77)),
    .pw 81, .ie (iM (iS (tcv 0) (tcv 1)) (tcv 82)), .ie (iA (tcv 48) (tcv 76)), .pw 84, .ie (iA (tcv 25) (tcv 77)),
    .pw 86, .ie (iM (tcv 14) (tcv 87)), .ie (iM (iS (tcv 0) (tcv 1)) (tcv 88)), .ie (iM (tcv 6) tdI), .pw 78,
    -- 92: (64 elo + 19999) / 20000; 93: e_1; 94: eτN; 95: eτD = 20000 4^{j_a}; 96: ceil; 97: e_τ
    .ie (iD (iA (iM (tcv 11) (tcv 29)) (tcv 17)) (tcv 18)), .cl 92,
    .ie (iM (iM (iM (iM (tcv 11) tdI) (iA (tcv 0) (iM (iM (tcv 6) tdI) (tcv 38)))) (iA (tcv 43) (iM (tcv 32) (tcv 32))))
      (tcv 29)),
    .ie (iM (tcv 18) (iM (tcv 32) (tcv 32))), .ie (iD (iS (iA (tcv 94) (tcv 95)) (tcv 0)) (tcv 95)), .cl 96,
    -- 98: stE1; 99: stE = stE1 + 3 d (e_τ + 4); 100: d r + 8 d² k_g b + 1; 101: stEH; 102: stEEta; 103: stJ; 104: stEu
    .ie (iA (tcv 93) (tcv 0)), .ie (iA (tcv 98) (iM (iM (tcv 2) tdI) (iA (tcv 97) (tcv 3)))),
    .ie (iA (iA (iM tdI (tcv 24)) (iM (iM (iM (tcv 6) (iM tdI tdI)) (tcv 38)) (tcv 27))) (tcv 0)), .cl 100,
    .ie (iA (iA (iA (tcv 97) (tcv 98)) (iA (tcv 8) (tcv 0))) (iM (iM (tcv 2) tdI) (iA (tcv 97) (tcv 3)))),
    .ie (iA (iA (tcv 102) (tcv 101)) (tcv 0)), .ie (iA (tcv 102) (tcv 0)),
    -- 105: 2^E; 106: E - e_1; 107: 2^{105}; 108: e_τ + 4; 109: 2^{107}; 110: E + e_τ + 1; 111: 2^{109}; 112: 2^{e_u};
    -- 113: 2^{stEH}; 114: 2^{stJ}; 115: tKZ = G' + 2 p; 116: 2^{tKZ}; 117: stEu + 1; 118: tBb; 119: e_τ + 3;
    -- 120: stEEta + stEH + 2; 121: 2^{L_a}
    .pw 99, .ie (iS (tcv 99) (tcv 98)), .pw 106, .ie (iA (tcv 97) (tcv 3)), .pw 108,
    .ie (iA (iA (tcv 99) (tcv 97)) (tcv 0)), .pw 110, .pw 104, .pw 101, .pw 103, .ie (iA (tcv 77) (tcv 42)), .pw 115,
    .ie (iA (tcv 104) (tcv 0)), .pw 117, .ie (iA (tcv 97) (tcv 2)), .ie (iA (iA (tcv 102) (tcv 101)) (tcv 1)),
    .pw 21,
    -- 122: q' = ⌈6 2^{L_a} R₀ / r₀²⌉ = ⌈6 2^{L_a} R₀n r₀d² / (R₀d r₀n²)⌉; 123: lg; 124: stK; 125: 2^{stK}
    .ie (iD (iS (iA (iM (iM (iM (iM (tcv 1) (tcv 2)) (tcv 121)) tRnI) (iM trdI trdI)) (iM tRdI (iM trnI trnI)))
      (tcv 0)) (iM tRdI (iM trnI trnI))), .cl 122, .ie (iA (tcv 120) (tcv 123)), .pw 124 ]

/-! ## The static test -/

/-- The pairs of the values of `poSt`. -/
def poEtL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 5), (0, 6), (0, 7), (0, 7), (0, 7),
   (0, 8), (0, 28), (0, 29), (0, 15), (0, 15), (0, 21), (2, 0), (2, 3), (2, 8), (2, 4), (1, 0), (2, 5), (1, 0),
   (1, 8), (1, 0), (5, 38), (2, 4), (2, 4), (1, 0), (9, 58), (9, 59), (9, 59), (9, 60), (9, 60), (9, 61), (9, 64),
   (9, 65), (9, 65), (9, 71), (6, 21), (18, 108), (2, 29), (18, 110), (18, 110), (18, 111), (1, 0), (10, 65),
   (10, 65), (2, 5), (1, 0), (10, 67), (11, 69), (2, 3), (2, 3), (2, 4), (2, 4), (1, 1), (1, 0), (9, 25), (9, 25),
   (47, 265), (4, 33), (47, 267), (47, 267), (47, 268), (1, 0), (0, 7), (11, 75), (25, 150), (8, 35), (25, 152),
   (25, 152), (25, 153), (25, 155), (47, 269), (1, 0), (1, 0), (25, 156), (1, 0), (1, 3), (25, 154), (1, 0),
   (25, 156), (1, 0), (1, 8), (1, 11), (1, 4), (1, 0), (5, 46), (5, 46), (22, 133), (2, 15), (22, 135), (22, 135),
   (5, 47), (23, 139), (12, 75), (12, 75), (23, 139), (23, 141), (23, 140), (1, 0), (23, 140), (1, 0), (22, 136),
   (1, 0), (23, 141), (1, 0), (1, 0), (1, 0), (1, 0), (25, 156), (1, 0), (23, 141), (1, 0), (22, 136), (23, 141),
   (1, 0), (4, 6), (4, 6), (23, 142), (1, 0)]

/-- The pair of the value of step `j`. -/
def poEt (j : ℕ) : ℕ × ℕ := poEtL.getD j (0, 0)

/-- The largest pair a step needs below `ℓ`. -/
def poT : ℕ × ℕ := (47, 269)

/-- The pairs of the inputs. -/
def poInP (_ : ℕ) : ℕ × ℕ := (1, 0)

/-- The input slots of the line. -/
def poIns : List ℕ := [110, 111, 112, 113, 114, 115, 118, 119]

theorem poSt_length : poSt.length = 126 := rfl

theorem poSt_chk : SL.chk 120 poIns poInP poEt poT 40 poSt = true := by decide +kernel

theorem poSt_units : SL.unitsP poEt poSt = (876, 5280) := by decide +kernel

/-! ## The new exponents in integers -/

/-- `⌈R₀/r₀⌉` in integers: `(R₀n r₀d + R₀d r₀n - 1) / (R₀d r₀n)`. -/
def qR (r0 R0 : ℚ) : ℕ := (R0.num.natAbs * r0.den + R0.den * r0.num.natAbs - 1) / (R0.den * r0.num.natAbs)

/-- `⌈6 · 2^{L_a} R₀ / r₀²⌉` in integers. -/
def qK (d : ℕ) (r0 R0 : ℚ) : ℕ :=
  (6 * triRaQ d * R0.num.natAbs * (r0.den * r0.den) + R0.den * (r0.num.natAbs * r0.num.natAbs) - 1) /
    (R0.den * (r0.num.natAbs * r0.num.natAbs))

theorem natAbs_num_cast {x : ℚ} (h : 0 < x) : ((x.num.natAbs : ℕ) : ℚ) = x.num := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast Rat.num_pos.2 h)]

theorem ceil_qR {r0 R0 : ℚ} (hr : 0 < r0 ∧ r0 ≤ R0) : ⌈R0 / r0⌉₊ = qR r0 R0 := by
  have hR : 0 < R0 := lt_of_lt_of_le hr.1 hr.2
  have hn : 0 < r0.num.natAbs := Int.natAbs_pos.2 (Rat.num_pos.2 hr.1).ne'
  have hD : 0 < R0.den * r0.num.natAbs := Nat.mul_pos R0.den_pos hn
  have e1 : (R0.num : ℚ) = R0 * R0.den := (Rat.mul_den_eq_num R0).symm
  have e2 : (r0.num : ℚ) = r0 * r0.den := (Rat.mul_den_eq_num r0).symm
  have h : R0 / r0 = ((R0.num.natAbs * r0.den : ℕ) : ℚ) / ((R0.den * r0.num.natAbs : ℕ) : ℚ) := by
    push_cast
    rw [natAbs_num_cast hR, natAbs_num_cast hr.1, e1, e2]
    have : (R0.den : ℚ) ≠ 0 := by exact_mod_cast R0.den_pos.ne'
    have : (r0.den : ℚ) ≠ 0 := by exact_mod_cast r0.den_pos.ne'
    field_simp
  rw [h, ceil_div_nat _ _ hD]
  rfl

theorem mst_qR {r0 R0 : ℚ} (hr : 0 < r0 ∧ r0 ≤ R0) : triMstQ r0 R0 = Nat.clog 2 (max (qR r0 R0) 2) := by
  have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
  unfold triMstQ
  rw [ceil_qR hr, (show Monotone (Nat.clog 2) from fun _ _ h => Nat.clog_mono_right 2 h).map_max, h2, max_comm]

theorem ceil_qK {r0 R0 : ℚ} (hr : 0 < r0 ∧ r0 ≤ R0) (d : ℕ) : ⌈6 * (triRaQ d : ℚ) * R0 / r0 ^ 2⌉₊ = qK d r0 R0 := by
  have hR : 0 < R0 := lt_of_lt_of_le hr.1 hr.2
  have hn : 0 < r0.num.natAbs := Int.natAbs_pos.2 (Rat.num_pos.2 hr.1).ne'
  have hD : 0 < R0.den * (r0.num.natAbs * r0.num.natAbs) := Nat.mul_pos R0.den_pos (Nat.mul_pos hn hn)
  have e1 : (R0.num : ℚ) = R0 * R0.den := (Rat.mul_den_eq_num R0).symm
  have e2 : (r0.num : ℚ) = r0 * r0.den := (Rat.mul_den_eq_num r0).symm
  have h : 6 * (triRaQ d : ℚ) * R0 / r0 ^ 2 =
      ((6 * triRaQ d * R0.num.natAbs * (r0.den * r0.den) : ℕ) : ℚ) /
        ((R0.den * (r0.num.natAbs * r0.num.natAbs) : ℕ) : ℚ) := by
    push_cast
    rw [natAbs_num_cast hR, natAbs_num_cast hr.1, e1, e2]
    have : (R0.den : ℚ) ≠ 0 := by exact_mod_cast R0.den_pos.ne'
    have : (r0.den : ℚ) ≠ 0 := by exact_mod_cast r0.den_pos.ne'
    have : r0 ≠ 0 := hr.1.ne'
    field_simp
  rw [h, ceil_div_nat _ _ hD]
  rfl

/-- The numerator of `G_up' + G_b` over `64 · 2^{B_v}`. -/
def gbT (d : ℕ) : ℕ := 65 * guN d * 2 ^ triBvQ d + 64 * (d + 1)

/-- The numerator of `j_s'`. -/
def jsNT (d ℓ : ℕ) : ℕ := gbT d ^ 2 * 2 ^ triNeTQ d ℓ * 4 ^ triJaQ d

/-- The denominator of `j_s'`. -/
def jsDT (d : ℕ) : ℕ := 4096 * 4 ^ triBvQ d * d2N d

/-- The numerator of `e_τ`. -/
def etN (d : ℕ) : ℕ := 64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 4 ^ triJaQ d) * eloI d

/-- The denominator of `e_τ`. -/
def etD (d : ℕ) : ℕ := 20000 * 4 ^ triJaQ d

/-- `triRzQ` in integers: `d r + 8 d² k_g b`. -/
def rzN (d : ℕ) : ℕ := d * TriM.rI d + 8 * (d * d) * triKgQ d * bI d

theorem triJsTQ_eq {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) :
    triJsTQ d ℓ = Nat.clog 4 ((jsNT d ℓ + jsDT d - 1) / jsDT d) := by
  have hd2N := d2N_pos hd
  have hD : 0 < jsDT d := by unfold jsDT; positivity
  have h_sum : (triGuTQ d + triBuQ d : ℚ) = (gbT d : ℚ) / (64 * 2 ^ triBvQ d) := by
    unfold triGuTQ triBuQ gbT
    rw [triGuQ_eq hd]
    field_simp
    push_cast
    ring
  have h_expr : (triGuTQ d + triBuQ d) ^ 2 * (2 ^ triNeTQ d ℓ : ℚ) / triD2Q d = (jsNT d ℓ : ℚ) / (jsDT d : ℚ) := by
    rw [h_sum, triD2Q_eq hd]
    unfold jsNT jsDT
    have hV : (2 : ℚ) ^ triBvQ d ≠ 0 := pow_ne_zero _ (by norm_num)
    have hD2 : (d2N d : ℚ) ≠ 0 := by exact_mod_cast hd2N.ne'
    have hJ : (4 : ℚ) ^ triJaQ d ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4 : (4 : ℚ) ^ triBvQ d = ((2 : ℚ) ^ triBvQ d) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    push_cast
    rw [h4]
    ring
  unfold triJsTQ
  rw [h_expr, ceil_div_nat _ _ hD]

theorem triE1Q_eq {d : ℕ} (hd : 1 ≤ d) : triE1Q d = Nat.clog 2 ((64 * eloI d + 19999) / 20000) := by
  have he : (eloI d : ℚ) ≠ 0 := by exact_mod_cast (eloI_pos hd).ne'
  have h : (64 : ℚ) / triEloQ d = ((64 * eloI d : ℕ) : ℚ) / ((20000 : ℕ) : ℚ) := by
    rw [triEloQ_eq hd]; field_simp; push_cast; ring
  have h2 : 64 * eloI d + 20000 - 1 = 64 * eloI d + 19999 := by omega
  unfold triE1Q
  rw [h, ceil_div_nat _ _ (by norm_num), h2]

theorem triETauQ_eq {d : ℕ} (hd : 1 ≤ d) : triETauQ d = Nat.clog 2 ((etN d + etD d - 1) / etD d) := by
  have he : (eloI d : ℚ) ≠ 0 := by exact_mod_cast (eloI_pos hd).ne'
  have hD : 0 < etD d := by unfold etD; positivity
  have h : (64 * d * (1 + 8 * d * triKgQ d) * (triD2Q d + 1) / triEloQ d : ℚ) = (etN d : ℚ) / (etD d : ℚ) := by
    rw [triEloQ_eq hd, triD2Q_eq hd]
    unfold etN etD
    have hJ : (4 : ℚ) ^ triJaQ d ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    push_cast
    ring
  unfold triETauQ
  rw [h, ceil_div_nat _ _ hD]

theorem stEH_eq (d : ℕ) : stEH d = Nat.clog 2 (rzN d + 1) := by
  have h : triRzQ d + 1 = ((rzN d + 1 : ℕ) : ℚ) := by
    unfold triRzQ triRQ triBQ rzN TriM.rI bI
    push_cast
    ring
  unfold stEH
  rw [h, Nat.ceil_natCast]

theorem jsDT_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ jsDT d := by
  unfold jsDT; have := Nat.one_le_pow (triBvQ d) 4 (by norm_num); have := d2N_pos hd; nlinarith

theorem etD_pos (d : ℕ) : 1 ≤ etD d := by
  unfold etD; have := Nat.one_le_pow (triJaQ d) 4 (by norm_num); omega

/-! ## The values -/

/-- The inputs: `k`, `r₀n`, `r₀d`, `d`, `n`, `triSQ d`, `R₀n`, `R₀d` in the slots `110 - 115`, `118`, `119`. -/
def poIn (d n k : ℕ) (r0 R0 : ℚ) : ℕ → ℤ := fun y =>
  if y = 110 then k else if y = 111 then r0.num else if y = 112 then r0.den else if y = 113 then d
    else if y = 114 then n else if y = 115 then triSQ d else if y = 118 then R0.num else if y = 119 then R0.den
    else 0

/-- The value of step `j` of the line at `d`, `n`, `k`, `r₀`, `R₀`. -/
abbrev poV (d n k : ℕ) (r0 R0 : ℚ) (j : ℕ) : ℤ := SL.val poSt 120 (poIn d n k r0 R0) j

theorem poV_c (d n k : ℕ) (r0 R0 : ℚ) (j : ℕ) :
    poV d n k r0 R0 j =
      (poSt.getD j (.cst 0)).sem 120 (poIn d n k r0 R0) (fun i => if i < j then poV d n k r0 R0 i else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the line unfolded. -/
local macro "pos" : tactic => `(tactic| (rw [poV_c]; simp only [poSt, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, tcv, tdI, tnI, tsI, tkI, trnI, trdI, tRnI, tRdI, iM, iA, iS, iD, poIn, Nat.reduceAdd,
  Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]))

section PoValues

variable (d n k : ℕ) (r0 R0 : ℚ)

theorem poV_0 : poV d n k r0 R0 0 = 1 := by pos
theorem poV_1 : poV d n k r0 R0 1 = 2 := by pos
theorem poV_2 : poV d n k r0 R0 2 = 3 := by pos
theorem poV_3 : poV d n k r0 R0 3 = 4 := by pos
theorem poV_4 : poV d n k r0 R0 4 = 5 := by pos
theorem poV_5 : poV d n k r0 R0 5 = 7 := by pos
theorem poV_6 : poV d n k r0 R0 6 = 8 := by pos
theorem poV_7 : poV d n k r0 R0 7 = 9 := by pos
theorem poV_8 : poV d n k r0 R0 8 = 10 := by pos
theorem poV_9 : poV d n k r0 R0 9 = 16 := by pos
theorem poV_10 : poV d n k r0 R0 10 = 50 := by pos
theorem poV_11 : poV d n k r0 R0 11 = 64 := by pos
theorem poV_12 : poV d n k r0 R0 12 = 68 := by pos
theorem poV_13 : poV d n k r0 R0 13 = 69 := by pos
theorem poV_14 : poV d n k r0 R0 14 = 161 := by pos
theorem poV_15 : poV d n k r0 R0 15 = 258986112 := by pos
theorem poV_16 : poV d n k r0 R0 16 = 400000000 := by pos
theorem poV_17 : poV d n k r0 R0 17 = 19999 := by pos
theorem poV_18 : poV d n k r0 R0 18 = 20000 := by pos
theorem poV_19 : poV d n k r0 R0 19 = 1572864 := by pos




theorem poV_20 : poV d n k r0 R0 20 = ((triSQ d ^ 2 : ℕ) : ℤ) := by pos; push_cast; ring
theorem poV_21 : poV d n k r0 R0 21 = (triLa (triSQ d) : ℤ) := by
  pos; rw [poV_4, poV_20, poV_5]; unfold triLa; push_cast; rfl
theorem poV_22 : poV d n k r0 R0 22 = (triLh (triSQ d) : ℤ) := by
  pos; rw [poV_10, poV_20, poV_12, poV_13]; unfold triLh; push_cast; rfl
theorem poV_23 : poV d n k r0 R0 23 = ((triLa (triSQ d) - 3 : ℕ) : ℤ) := by
  pos; rw [poV_21, poV_2]; have := triLa_ge d; push_cast [show 3 ≤ triLa (triSQ d) by omega]; ring
theorem poV_24 : poV d n k r0 R0 24 = (rI d : ℤ) := by
  pos; rw [poV_23, Int.toNat_natCast]; unfold TriM.rI; push_cast; rfl
theorem poV_25 : poV d n k r0 R0 25 = ((triLa (triSQ d) - 10 : ℕ) : ℤ) := by
  pos; rw [poV_21, poV_8]; have := triLa_ge d; push_cast [this]; ring
theorem poV_26 : poV d n k r0 R0 26 = ((2 ^ (triLa (triSQ d) - 10) : ℕ) : ℤ) := by
  pos; rw [poV_25, Int.toNat_natCast]; norm_cast
theorem poV_27 : poV d n k r0 R0 27 = (bI d : ℤ) := by
  pos; rw [poV_14, poV_26]; unfold bI; push_cast; ring
theorem poV_28 : poV d n k r0 R0 28 = ((2 ^ triLh (triSQ d) : ℕ) : ℤ) := by
  pos; rw [poV_22, Int.toNat_natCast]; norm_cast
theorem poV_29 : poV d n k r0 R0 29 = (eloI d : ℤ) := by
  pos; rw [poV_15, poV_22, poV_28, poV_0]; unfold eloI
  have : 1 ≤ 2 ^ triLh (triSQ d) := Nat.one_le_two_pow
  push_cast [this]; ring
theorem poV_30 : poV d n k r0 R0 30 = ((9 * d * triSQ d : ℕ) : ℤ) := by
  pos; rw [poV_7]; push_cast; ring
theorem poV_31 : poV d n k r0 R0 31 = (triJaQ d : ℤ) := by
  pos; rw [poV_30, Int.toNat_natCast]; rfl
theorem poV_32 : poV d n k r0 R0 32 = ((2 ^ triJaQ d : ℕ) : ℤ) := by
  pos; rw [poV_31, Int.toNat_natCast]; norm_cast
theorem poV_33 : poV d n k r0 R0 33 = (kgN d : ℤ) := by
  pos; rw [poV_9, poV_27, poV_0, poV_6, poV_1, poV_29]; unfold kgN; push_cast; ring
theorem poV_34 : poV d n k r0 R0 34 = (((kgN d + 19999) / 20000 : ℕ) : ℤ) := by
  pos; rw [poV_33, poV_17, poV_18]; push_cast; rfl
theorem poV_35 : poV d n k r0 R0 35 = (Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) := by
  pos; rw [poV_34, Int.toNat_natCast]
theorem poV_36 : poV d n k r0 R0 36 = (Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) - 2 := by pos; rw [poV_35, poV_1]
theorem poV_37 : poV d n k r0 R0 37 = max ((Nat.clog 2 ((kgN d + 19999) / 20000) : ℤ) - 2) 0 := by pos; rw [poV_36]
theorem poV_38 (hd : 1 ≤ d) : poV d n k r0 R0 38 = (triKgQ d : ℤ) := by
  pos; rw [poV_37, poV_1, triKgQ_eq hd]; push_cast; omega
theorem poV_39 (hd : 1 ≤ d) : poV d n k r0 R0 39 = (triBgQ d : ℤ) := by
  pos; rw [poV_3, poV_38 d n k r0 R0 hd]; unfold triBgQ; push_cast; ring
theorem poV_40 (hd : 1 ≤ d) : poV d n k r0 R0 40 = ((triBgQ d + 1 : ℕ) : ℤ) := by
  pos; rw [poV_39 d n k r0 R0 hd, poV_0]; push_cast; ring
theorem poV_41 (hd : 1 ≤ d) : poV d n k r0 R0 41 = ((triBgQ d).size : ℤ) := by
  pos; rw [poV_40 d n k r0 R0 hd, Int.toNat_natCast, ← size_eq_clog]
theorem poV_42 (hd : 1 ≤ d) : poV d n k r0 R0 42 = ((2 * tzP d : ℕ) : ℤ) := by
  pos; rw [poV_1, poV_39 d n k r0 R0 hd, poV_41 d n k r0 R0 hd, poV_3]; unfold tzP gsm_prec; push_cast; ring
theorem poV_43 (hd : 1 ≤ d) : poV d n k r0 R0 43 = (d2N d : ℤ) := by
  pos; rw [poV_3, poV_24, poV_32, poV_27, poV_0, poV_1]; unfold d2N
  have h1 : 1 ≤ bI d * 2 ^ triJaQ d := Nat.one_le_iff_ne_zero.2 (by unfold bI; positivity)
  push_cast [h1, hd]; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_44 (hd : 1 ≤ d) : poV d n k r0 R0 44 = (bvN d : ℤ) := by
  pos; rw [poV_11, poV_0, poV_43 d n k r0 R0 hd, poV_29]; unfold bvN; push_cast; ring
theorem poV_45 : poV d n k r0 R0 45 = (bvD d : ℤ) := by
  pos; rw [poV_32, poV_16]; unfold bvD; push_cast; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_46 (hd : 1 ≤ d) : poV d n k r0 R0 46 = (((bvN d + bvD d - 1) / bvD d : ℕ) : ℤ) := by
  have hD := bvD_pos d
  pos; rw [poV_44 d n k r0 R0 hd, poV_45, poV_0]; push_cast [show 1 ≤ bvN d + bvD d by omega]; rfl
theorem poV_47 (hd : 1 ≤ d) : poV d n k r0 R0 47 = (Nat.clog 2 ((bvN d + bvD d - 1) / bvD d) : ℤ) := by
  pos; rw [poV_46 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_48 (hd : 1 ≤ d) : poV d n k r0 R0 48 = (triBvQ d : ℤ) := by
  pos; rw [poV_47 d n k r0 R0 hd, poV_0, poV_1, triBvQ_eq hd, clog4_eq]; push_cast; rfl
theorem poV_49 (hd : 1 ≤ d) : poV d n k r0 R0 49 = ((2 ^ triBvQ d : ℕ) : ℤ) := by
  pos; rw [poV_48 d n k r0 R0 hd, Int.toNat_natCast]; norm_cast
theorem poV_50 (hd : 1 ≤ d) : poV d n k r0 R0 50 = ((8 * d * triKgQ d : ℕ) : ℤ) := by
  pos; rw [poV_6, poV_38 d n k r0 R0 hd]; push_cast; ring
theorem poV_51 (hd : 1 ≤ d) : poV d n k r0 R0 51 = (Nat.sqrt (8 * d * triKgQ d) : ℤ) := by
  pos; rw [poV_50 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_52 (hd : 1 ≤ d) : poV d n k r0 R0 52 = ((triJaQ d - 3 : ℕ) : ℤ) := by
  pos; rw [poV_31, poV_2]; have := triJaQ_ge hd; push_cast [show 3 ≤ triJaQ d by omega]; ring
theorem poV_53 (hd : 1 ≤ d) : poV d n k r0 R0 53 = ((2 ^ (triJaQ d - 3) : ℕ) : ℤ) := by
  pos; rw [poV_52 d n k r0 R0 hd, Int.toNat_natCast]; norm_cast
theorem poV_54 (hd : 1 ≤ d) : poV d n k r0 R0 54 = (guN d : ℤ) := by
  pos; rw [poV_51 d n k r0 R0 hd, poV_1, poV_53 d n k r0 R0 hd]; unfold guN; push_cast; ring
theorem poV_55 (hd : 1 ≤ d) : poV d n k r0 R0 55 = (gbN d : ℤ) := by
  pos; rw [poV_54 d n k r0 R0 hd, poV_49 d n k r0 R0 hd, poV_0]; unfold gbN; push_cast; ring


/-! ### `m_st`, `ℓ` and `n_e'` -/

theorem poV_56 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 56 = (qR r0 R0 : ℤ) - 2 := by
  have hR : 0 < R0 := lt_of_lt_of_le hr.1 hr.2
  have e1 : R0.num = (R0.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (Rat.num_pos.2 hR).le).symm
  have e2 : r0.num = (r0.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (Rat.num_pos.2 hr.1).le).symm
  have hp : 1 ≤ R0.num.natAbs * r0.den + R0.den * r0.num.natAbs := by
    have := Nat.mul_pos (Int.natAbs_pos.2 (Rat.num_pos.2 hR).ne') r0.den_pos
    omega
  pos; rw [poV_0, poV_1, e1, e2]; unfold qR; push_cast [hp] <;> rfl
theorem poV_57 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 57 = max ((qR r0 R0 : ℤ) - 2) 0 := by
  pos; rw [poV_56 d n k r0 R0 hr]
theorem poV_58 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 58 = ((max (qR r0 R0) 2 : ℕ) : ℤ) := by
  pos; rw [poV_57 d n k r0 R0 hr, poV_1]; push_cast; omega
theorem poV_59 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 59 = (triMstQ r0 R0 : ℤ) := by
  pos; rw [poV_58 d n k r0 R0 hr, Int.toNat_natCast, mst_qR hr]
theorem poV_60 : poV d n k r0 R0 60 = (k : ℤ) := by pos; rw [poV_0]; ring
theorem poV_61 : poV d n k r0 R0 61 = ((2 ^ k : ℕ) : ℤ) := by
  pos; rw [poV_60, Int.toNat_natCast]; norm_cast
theorem poV_62 (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 62 = ((3 * 2 ^ (19 + k) * (d * n) ^ 3 * triMstQ r0 R0 : ℕ) : ℤ) := by
  pos; rw [poV_19, poV_61, poV_59 d n k r0 R0 hr]; push_cast; ring
theorem poV_63 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 63 = (ellPosO d n k r0 R0 : ℤ) := by
  pos; unfold ellPosO; rw [poV_62 d n k r0 R0 hr, Int.toNat_natCast]
theorem poV_64 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 64 = (neN d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_6, poV_43 d n k r0 R0 hd, poV_29, poV_7, poV_55 d n k r0 R0 hd, poV_54 d n k r0 R0 hd, poV_63 d n k r0 R0 hr, poV_49 d n k r0 R0 hd]
  unfold neN; push_cast; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_65 (hd : 1 ≤ d) : poV d n k r0 R0 65 = (neD d : ℤ) := by
  pos; rw [poV_7, poV_49 d n k r0 R0 hd, poV_32, poV_16]; unfold neD; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_66 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 66 = (((neN d (ellPosO d n k r0 R0) + neD d - 1) / neD d : ℕ) : ℤ) := by
  have hD := neD_pos d
  pos; rw [poV_64 d n k r0 R0 hd hr, poV_65 d n k r0 R0 hd, poV_0]
  push_cast [show 1 ≤ neN d (ellPosO d n k r0 R0) + neD d by omega]; rfl
theorem poV_67 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 67 = (triNeQ d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_66 d n k r0 R0 hd hr, Int.toNat_natCast, triNeQ_eq hd]
theorem poV_68 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 68 = (triNeTQ d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_67 d n k r0 R0 hd hr, poV_0]; unfold triNeTQ; push_cast; ring
theorem poV_69 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 69 = ((2 ^ triNeTQ d (ellPosO d n k r0 R0) : ℕ) : ℤ) := by
  pos; rw [poV_68 d n k r0 R0 hd hr, Int.toNat_natCast]; norm_cast

/-! ### `j_s'` -/

theorem poV_70 : poV d n k r0 R0 70 = 65 := by pos
theorem poV_71 (hd : 1 ≤ d) : poV d n k r0 R0 71 = (gbT d : ℤ) := by
  pos; rw [poV_70, poV_54 d n k r0 R0 hd, poV_49 d n k r0 R0 hd, poV_11, poV_0]; unfold gbT; push_cast; ring
theorem poV_72 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 72 = (jsNT d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_71 d n k r0 R0 hd, poV_69 d n k r0 R0 hd hr, poV_32]; unfold jsNT; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_73 (hd : 1 ≤ d) : poV d n k r0 R0 73 = (jsDT d : ℤ) := by
  pos; rw [poV_11, poV_49 d n k r0 R0 hd, poV_43 d n k r0 R0 hd]; unfold jsDT; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_74 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 74 = (((jsNT d (ellPosO d n k r0 R0) + jsDT d - 1) / jsDT d : ℕ) : ℤ) := by
  have hD := jsDT_pos hd
  pos; rw [poV_72 d n k r0 R0 hd hr, poV_73 d n k r0 R0 hd, poV_0]
  push_cast [show 1 ≤ jsNT d (ellPosO d n k r0 R0) + jsDT d by omega]; rfl
theorem poV_75 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 75 = (Nat.clog 2 ((jsNT d (ellPosO d n k r0 R0) + jsDT d - 1) / jsDT d) : ℤ) := by
  pos; rw [poV_74 d n k r0 R0 hd hr, Int.toNat_natCast]
theorem poV_76 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 76 = (triJsTQ d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_75 d n k r0 R0 hd hr, poV_0, poV_1, triJsTQ_eq hd, clog4_eq]; push_cast; rfl

/-! ### `G'`, `G_c'` and the constants of a draw -/

theorem poV_77 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 77 = (tGT d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_48 d n k r0 R0 hd, poV_76 d n k r0 R0 hd hr, poV_31]; unfold tGT; push_cast; ring
theorem poV_78 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 78 = (tGcT d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_77 d n k r0 R0 hd hr, poV_68 d n k r0 R0 hd hr]; unfold tGcT; push_cast; ring
theorem poV_79 (hd : 1 ≤ d) : poV d n k r0 R0 79 = (tzDCO d (ellPosO d n k r0 R0)).P2 := by
  pos; rw [poV_42 d n k r0 R0 hd, Int.toNat_natCast]; simp only [tzDCO]
theorem poV_80 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 80 = (tzDCO d (ellPosO d n k r0 R0)).PG := by
  pos; rw [poV_77 d n k r0 R0 hd hr, Int.toNat_natCast]; simp only [tzDCO]
theorem poV_81 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 81 = ((triLa (triSQ d) - 3 + tGT d (ellPosO d n k r0 R0) : ℕ) : ℤ) := by
  pos; rw [poV_23, poV_77 d n k r0 R0 hd hr]; push_cast; ring
theorem poV_82 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 82 = (tzDCO d (ellPosO d n k r0 R0)).R := by
  pos; rw [poV_81 d n k r0 R0 hd hr, Int.toNat_natCast]; simp only [tzDCO]
theorem poV_83 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 83 = -(tzDCO d (ellPosO d n k r0 R0)).R := by
  pos; rw [poV_0, poV_1, poV_82 d n k r0 R0 hd hr]; ring
theorem poV_84 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 84 = ((triBvQ d + triJsTQ d (ellPosO d n k r0 R0) : ℕ) : ℤ) := by
  pos; rw [poV_48 d n k r0 R0 hd, poV_76 d n k r0 R0 hd hr]; push_cast; ring
theorem poV_85 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 85 = (tzDCO d (ellPosO d n k r0 R0)).Al := by
  pos; rw [poV_84 d n k r0 R0 hd hr, Int.toNat_natCast]; simp only [tzDCO]
theorem poV_86 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 86 = ((triLa (triSQ d) - 10 + tGT d (ellPosO d n k r0 R0) : ℕ) : ℤ) := by
  pos; rw [poV_25, poV_77 d n k r0 R0 hd hr]; push_cast; ring
theorem poV_87 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    poV d n k r0 R0 87 = ((2 ^ (triLa (triSQ d) - 10 + tGT d (ellPosO d n k r0 R0)) : ℕ) : ℤ) := by
  pos; rw [poV_86 d n k r0 R0 hd hr, Int.toNat_natCast]; norm_cast
theorem poV_88 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 88 = (tzDCO d (ellPosO d n k r0 R0)).Bh := by
  pos; rw [poV_14, poV_87 d n k r0 R0 hd hr]; simp only [tzDCO]; push_cast; ring
theorem poV_89 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 89 = -(tzDCO d (ellPosO d n k r0 R0)).Bh := by
  pos; rw [poV_0, poV_1, poV_88 d n k r0 R0 hd hr]; ring
theorem poV_90 : poV d n k r0 R0 90 = 8 * (tzDCO d (ellPosO d n k r0 R0)).dd := by
  pos; rw [poV_6]; simp only [tzDCO]
theorem poV_91 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 91 = 2 ^ tGcT d (ellPosO d n k r0 R0) := by
  pos; rw [poV_78 d n k r0 R0 hd hr, Int.toNat_natCast]

/-! ### SEP's, the gauge's and the stage test's exponents -/

theorem poV_92 : poV d n k r0 R0 92 = (((64 * eloI d + 19999) / 20000 : ℕ) : ℤ) := by
  pos; rw [poV_11, poV_29, poV_17, poV_18]; push_cast; rfl
theorem poV_93 (hd : 1 ≤ d) : poV d n k r0 R0 93 = (triE1Q d : ℤ) := by
  pos; rw [poV_92, Int.toNat_natCast, triE1Q_eq hd]
theorem poV_94 (hd : 1 ≤ d) : poV d n k r0 R0 94 = (etN d : ℤ) := by
  pos; rw [poV_11, poV_0, poV_6, poV_38 d n k r0 R0 hd, poV_43 d n k r0 R0 hd, poV_32, poV_29]; unfold etN; push_cast
  simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_95 : poV d n k r0 R0 95 = (etD d : ℤ) := by
  pos; rw [poV_18, poV_32]; unfold etD; push_cast; simp only [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
theorem poV_96 (hd : 1 ≤ d) : poV d n k r0 R0 96 = (((etN d + etD d - 1) / etD d : ℕ) : ℤ) := by
  have hD := etD_pos d
  pos; rw [poV_94 d n k r0 R0 hd, poV_95, poV_0]; push_cast [show 1 ≤ etN d + etD d by omega]; rfl
theorem poV_97 (hd : 1 ≤ d) : poV d n k r0 R0 97 = (triETauQ d : ℤ) := by
  pos; rw [poV_96 d n k r0 R0 hd, Int.toNat_natCast, triETauQ_eq hd]
theorem poV_98 (hd : 1 ≤ d) : poV d n k r0 R0 98 = (stE1 d : ℤ) := by
  pos; rw [poV_93 d n k r0 R0 hd, poV_0]; unfold stE1; push_cast; ring
theorem poV_99 (hd : 1 ≤ d) : poV d n k r0 R0 99 = (stE d : ℤ) := by
  pos; rw [poV_98 d n k r0 R0 hd, poV_2, poV_97 d n k r0 R0 hd, poV_3]; unfold stE; push_cast; ring
theorem poV_100 (hd : 1 ≤ d) : poV d n k r0 R0 100 = ((rzN d + 1 : ℕ) : ℤ) := by
  pos; rw [poV_24, poV_6, poV_38 d n k r0 R0 hd, poV_27, poV_0]; unfold rzN; push_cast; ring
theorem poV_101 (hd : 1 ≤ d) : poV d n k r0 R0 101 = (stEH d : ℤ) := by
  pos; rw [poV_100 d n k r0 R0 hd, Int.toNat_natCast, stEH_eq]
theorem poV_102 (hd : 1 ≤ d) : poV d n k r0 R0 102 = (stEEta d : ℤ) := by
  pos; rw [poV_97 d n k r0 R0 hd, poV_98 d n k r0 R0 hd, poV_8, poV_0, poV_2, poV_3]; unfold stEEta; push_cast; ring
theorem poV_103 (hd : 1 ≤ d) : poV d n k r0 R0 103 = (stJ d : ℤ) := by
  pos; rw [poV_102 d n k r0 R0 hd, poV_101 d n k r0 R0 hd, poV_0]; unfold stJ; push_cast; ring
theorem poV_104 (hd : 1 ≤ d) : poV d n k r0 R0 104 = (stEu d : ℤ) := by
  pos; rw [poV_102 d n k r0 R0 hd, poV_0]; unfold stEu; push_cast; ring
theorem poV_105 (hd : 1 ≤ d) : poV d n k r0 R0 105 = 2 ^ stE d := by
  pos; rw [poV_99 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_106 (hd : 1 ≤ d) : poV d n k r0 R0 106 = ((stE d - stE1 d : ℕ) : ℤ) := by
  have h : stE1 d ≤ stE d := by unfold stE; omega
  pos; rw [poV_99 d n k r0 R0 hd, poV_98 d n k r0 R0 hd]; push_cast [h]; ring
theorem poV_107 (hd : 1 ≤ d) : poV d n k r0 R0 107 = 2 ^ (stE d - stE1 d) := by
  pos; rw [poV_106 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_108 (hd : 1 ≤ d) : poV d n k r0 R0 108 = ((triETauQ d + 4 : ℕ) : ℤ) := by
  pos; rw [poV_97 d n k r0 R0 hd, poV_3]; push_cast; ring
theorem poV_109 (hd : 1 ≤ d) : poV d n k r0 R0 109 = 2 ^ (triETauQ d + 4) := by
  pos; rw [poV_108 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_110 (hd : 1 ≤ d) : poV d n k r0 R0 110 = ((stE d + triETauQ d + 1 : ℕ) : ℤ) := by
  pos; rw [poV_99 d n k r0 R0 hd, poV_97 d n k r0 R0 hd, poV_0]; push_cast; ring
theorem poV_111 (hd : 1 ≤ d) : poV d n k r0 R0 111 = 2 ^ (stE d + triETauQ d + 1) := by
  pos; rw [poV_110 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_112 (hd : 1 ≤ d) : poV d n k r0 R0 112 = 2 ^ stEu d := by
  pos; rw [poV_104 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_113 (hd : 1 ≤ d) : poV d n k r0 R0 113 = 2 ^ stEH d := by
  pos; rw [poV_101 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_114 (hd : 1 ≤ d) : poV d n k r0 R0 114 = 2 ^ stJ d := by
  pos; rw [poV_103 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_115 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 115 = (tKZ d (ellPosO d n k r0 R0) : ℤ) := by
  pos; rw [poV_77 d n k r0 R0 hd hr, poV_42 d n k r0 R0 hd]; unfold tKZ; push_cast; ring
theorem poV_116 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 116 = 2 ^ tKZ d (ellPosO d n k r0 R0) := by
  pos; rw [poV_115 d n k r0 R0 hd hr, Int.toNat_natCast]
theorem poV_117 (hd : 1 ≤ d) : poV d n k r0 R0 117 = ((stEu d + 1 : ℕ) : ℤ) := by
  pos; rw [poV_104 d n k r0 R0 hd, poV_0]; push_cast; ring
theorem poV_118 (hd : 1 ≤ d) : poV d n k r0 R0 118 = tBb d := by
  pos; unfold tBb; rw [poV_117 d n k r0 R0 hd, Int.toNat_natCast]
theorem poV_119 (hd : 1 ≤ d) : poV d n k r0 R0 119 = ((triETauQ d + 3 : ℕ) : ℤ) := by
  pos; rw [poV_97 d n k r0 R0 hd, poV_2]; push_cast; ring
theorem poV_120 (hd : 1 ≤ d) : poV d n k r0 R0 120 = ((stEEta d + stEH d + 2 : ℕ) : ℤ) := by
  pos; rw [poV_102 d n k r0 R0 hd, poV_101 d n k r0 R0 hd, poV_1]; push_cast; ring
theorem poV_121 : poV d n k r0 R0 121 = (triRaQ d : ℤ) := by
  pos; rw [poV_21, Int.toNat_natCast]; unfold triRaQ; norm_cast


/-! ### `stK` -/

theorem poV_122 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 122 = (qK d r0 R0 : ℤ) := by
  have hR : 0 < R0 := lt_of_lt_of_le hr.1 hr.2
  have e1 : R0.num = (R0.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (Rat.num_pos.2 hR).le).symm
  have e2 : r0.num = (r0.num.natAbs : ℤ) := (Int.natAbs_of_nonneg (Rat.num_pos.2 hr.1).le).symm
  have hp : 1 ≤ 6 * triRaQ d * R0.num.natAbs * (r0.den * r0.den) + R0.den * (r0.num.natAbs * r0.num.natAbs) := by
    have hn := Int.natAbs_pos.2 (Rat.num_pos.2 hr.1).ne'
    have := Nat.mul_pos R0.den_pos (Nat.mul_pos hn hn)
    omega
  pos; rw [poV_0, poV_1, poV_2, poV_121, e1, e2]; unfold qK; push_cast [hp] <;> ring_nf
theorem poV_123 (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 123 = (Nat.clog 2 (qK d r0 R0) : ℤ) := by
  pos; rw [poV_122 d n k r0 R0 hr, Int.toNat_natCast]
theorem poV_124 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 124 = (stK d r0 R0 : ℤ) := by
  pos; rw [poV_120 d n k r0 R0 hd, poV_123 d n k r0 R0 hr]; unfold stK; rw [ceil_qK hr]; push_cast; ring
theorem poV_125 (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) : poV d n k r0 R0 125 = 2 ^ stK d r0 R0 := by
  pos; rw [poV_124 d n k r0 R0 hd hr, Int.toNat_natCast]

end PoValues

end AdversarialBco.Unified.ProgO.TriO
