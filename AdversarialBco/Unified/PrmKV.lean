/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupLink
public import AdversarialBco.Unified.BudEnc

@[expose] public section

/-!
# PARAM of BL-O on the machine: the straight line at `k_δ`

Bit/Transfer/XBLSetupParam.lean and Bit/Transfer/XBLSetupParV.lean at `parK d n e = parN (NeO d n e) d n`:
`parStK` is v2.1's `parSt` with step `18` reading `N_e = NeO d n e = 15 · 2^{17 + e} d³ n⁴` from the input slot `4`
instead of computing `15 · 2^17 d³ n⁴`; every other step is v2.1's. `pvK d n e k` is the value of step `k` on the inputs
`d` (slot `0`), `n` (slot `3`), `N_e` (slot `4`); `pvK_k` gives it in closed form on PARAM at `parK d n e`, with v2.1's
integer formulas (`lamI`, ..., `loI`).
-/

namespace AdversarialBco.Unified.PrmK

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN)
open AdversarialBco.Unified.BudK (parK)

/-- Procedure PARAM at `N_e` given, as a straight line; step `k` writes the slot `30 + k`. -/
def parStK : List SStep :=
  [ .cst 1, .cst 2, .cst 4, .cst 8, .cst 10, .cst 16, .cst 24, .cst 40, .cst 160, .cst 3,      -- 0 - 9
    .cst 6, .cst 64, .cst 36, .cst 725, .cst 1450, .cst 14500, .cst 134, .cst 1966080,       -- 10 - 17
    -- 18: N_e, read from the input slot 4; 19: N_e + 1; 20: ℓe = size N_e
    .ie (.sc 4),
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

theorem parStK_length : parStK.length = 93 := rfl

/-! ## The values -/


/-- The inputs of PARAM at `k_δ = e`: `d` in slot `0`, `n` in slot `3`, `N_e = NeO d n e` in slot `4`. -/
def parIK (d n e : ℕ) : ℕ → ℤ := fun y => if y = 0 then d else if y = 3 then n else if y = 4 then (NeO d n e : ℤ) else 0

/-- The value of step `k` of PARAM on `d`, `n`. -/
abbrev pvK (d n e : ℕ) (k : ℕ) : ℤ := SL.val parStK 30 (parIK d n e) k

theorem pvK_c (d n e k : ℕ) :
    pvK d n e k = (parStK.getD k (.cst 0)).sem 30 (parIK d n e) (fun j => if j < k then pvK d n e j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of PARAM unfolded: the step, its expression, the reads of the slots. -/
local macro "pvsk" : tactic => `(tactic| (rw [pvK_c]; simp only [parStK, List.getD_cons_succ, List.getD_cons_zero, SStep.sem,
  slZ, rv, dI, nI, iM, iA, iS, iD, parIK, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]))

section Values

variable (d n e : ℕ)

theorem pvK_0 : pvK d n e 0 = 1 := by pvsk
theorem pvK_1 : pvK d n e 1 = 2 := by pvsk
theorem pvK_2 : pvK d n e 2 = 4 := by pvsk
theorem pvK_3 : pvK d n e 3 = 8 := by pvsk
theorem pvK_4 : pvK d n e 4 = 10 := by pvsk
theorem pvK_5 : pvK d n e 5 = 16 := by pvsk
theorem pvK_6 : pvK d n e 6 = 24 := by pvsk
theorem pvK_7 : pvK d n e 7 = 40 := by pvsk
theorem pvK_8 : pvK d n e 8 = 160 := by pvsk
theorem pvK_9 : pvK d n e 9 = 3 := by pvsk
theorem pvK_10 : pvK d n e 10 = 6 := by pvsk
theorem pvK_11 : pvK d n e 11 = 64 := by pvsk
theorem pvK_12 : pvK d n e 12 = 36 := by pvsk
theorem pvK_13 : pvK d n e 13 = 725 := by pvsk
theorem pvK_14 : pvK d n e 14 = 1450 := by pvsk
theorem pvK_15 : pvK d n e 15 = 14500 := by pvsk
theorem pvK_16 : pvK d n e 16 = 134 := by pvsk

theorem pvK_18 : pvK d n e 18 = (NeO d n e : ℤ) := by
  pvsk

theorem pvK_19 : pvK d n e 19 = ((NeO d n e + 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_18, pvK_0]; push_cast; ring

theorem pvK_20 : pvK d n e 20 = ((NeO d n e).size : ℤ) := by
  pvsk; rw [pvK_19, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_21 : pvK d n e 21 = ((d + 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_0]; push_cast; ring

theorem pvK_22 : pvK d n e 22 = (d.size : ℤ) := by
  pvsk; rw [pvK_21, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_23 : pvK d n e 23 = ((parK d n e).p : ℤ) := by
  pvsk; rw [pvK_4, pvK_20, pvK_5, pvK_22, pvK_8]; simp only [parK, parN]; push_cast; ring

theorem pvK_24 : pvK d n e 24 = (((NeO d n e).size + 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_20, pvK_0]; push_cast; ring

theorem pvK_25 : pvK d n e 25 = ((NeO d n e).size.size : ℤ) := by
  pvsk; rw [pvK_24, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_26 : pvK d n e 26 = ((parK d n e).q : ℤ) := by
  pvsk; rw [pvK_23, pvK_1, pvK_25, pvK_6]; simp only [parK, parN]; push_cast; ring

theorem pvK_27 : pvK d n e 27 = ((parK d n e).pF : ℤ) := by
  pvsk; rw [pvK_23, pvK_1, pvK_20, pvK_2, pvK_22, pvK_7]; simp only [parK, parN]; push_cast; ring

theorem pvK_28 : pvK d n e 28 = ((n * (d + 2) + 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_21, pvK_0]; push_cast; ring

theorem pvK_29 : pvK d n e 29 = ((n * (d + 2)).size : ℤ) := by
  pvsk; rw [pvK_28, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_30 : pvK d n e 30 = ((parK d n e).B : ℤ) := by
  pvsk; rw [pvK_1, pvK_23, pvK_29]; simp only [parK, parN]; push_cast; ring

theorem pvK_31 : pvK d n e 31 = (((parK d n e).B + 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_30, pvK_0]; push_cast; ring

theorem pvK_32 : pvK d n e 32 = ((parK d n e).B.size : ℤ) := by
  pvsk; rw [pvK_31, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_33 : pvK d n e 33 = ((2 * gsm_prec (parK d n e).B : ℕ) : ℤ) := by
  pvsk; rw [pvK_1, pvK_30, pvK_32, pvK_2]; unfold gsm_prec; push_cast; ring

theorem pvK_34 : pvK d n e 34 = 2 ^ (2 * gsm_prec (parK d n e).B) := by
  pvsk; rw [pvK_33, Int.toNat_natCast]

theorem pvK_35 : pvK d n e 35 = 2 ^ (parK d n e).p := by
  pvsk; rw [pvK_23, Int.toNat_natCast]

theorem pvK_36 : pvK d n e 36 = 2 ^ (parK d n e).pF := by
  pvsk; rw [pvK_27, Int.toNat_natCast]

theorem pvK_37 : pvK d n e 37 = 2 ^ (parK d n e).q := by
  pvsk; rw [pvK_26, Int.toNat_natCast]

theorem pK_ge (d n e : ℕ) : 3 * (NeO d n e).size + 6 * d.size + 64 ≤ (parK d n e).p := by simp only [parK, parN]; omega

theorem qK_ge (d n e : ℕ) : 24 ≤ (parK d n e).q := by simp only [parK, parN]; omega

theorem pvK_38 : pvK d n e 38 = (((parK d n e).p - 3 * (NeO d n e).size - 6 * d.size - 64 : ℕ) : ℤ) := by
  pvsk; rw [pvK_23, pvK_9, pvK_20, pvK_10, pvK_22, pvK_11]; have := pK_ge d n e; omega

theorem pvK_39 : pvK d n e 39 = 2 ^ ((parK d n e).p - 3 * (NeO d n e).size - 6 * d.size - 64) := by
  pvsk; rw [pvK_38, Int.toNat_natCast]

theorem pvK_40 : pvK d n e 40 = ((d * NeO d n e : ℕ) : ℤ) := by
  pvsk; rw [pvK_18]; push_cast; ring

theorem pvK_41 : pvK d n e 41 = ((d * 4 ^ (parK d n e).q : ℕ) : ℤ) := by
  pvsk; rw [pvK_37, four_pow]; push_cast; ring

theorem pvK_42 : pvK d n e 42 = (Nat.sqrt (d * 4 ^ (parK d n e).q) : ℤ) := by
  pvsk; rw [pvK_41, Int.toNat_natCast]

theorem pvK_43 : pvK d n e 43 = ((n * 4 ^ (parK d n e).q : ℕ) : ℤ) := by
  pvsk; rw [pvK_37, four_pow]; push_cast; ring

theorem pvK_44 : pvK d n e 44 = (Nat.sqrt (n * 4 ^ (parK d n e).q) : ℤ) := by
  pvsk; rw [pvK_43, Int.toNat_natCast]

theorem pvK_45 : pvK d n e 45 = (((parK d n e).q - 1 : ℕ) : ℤ) := by
  pvsk; rw [pvK_26, pvK_0]; have := qK_ge d n e; omega

theorem pvK_46 : pvK d n e 46 = 2 ^ ((parK d n e).q - 1) := by
  pvsk; rw [pvK_45, Int.toNat_natCast]

theorem pvK_47 : pvK d n e 47 = (gsm_mercq (parK d n e).q (2 ^ ((parK d n e).q - 1)) (parK d n e).q : ℤ) := by
  pvsk; rw [pvK_26, pvK_46, Int.toNat_natCast, toNat_two_pow]

end Values

/-! ## The logarithms -/

/-- `N_e ≥ 1`. -/
theorem NeK_pos {d n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ NeO d n e := by
  unfold NeO
  have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h4 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) h3) h4

section Logs

variable {d n e : ℕ}

theorem pvK_48 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 48 = (((NeO d n e).size - 1 : ℕ) : ℤ) := by
  have : 1 ≤ (NeO d n e).size := Nat.size_pos.2 (NeK_pos hd hn)
  pvsk; rw [pvK_20, pvK_0]; omega

theorem pvK_49 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 49 = 2 ^ ((NeO d n e).size - 1) := by
  pvsk; rw [pvK_48 hd hn, Int.toNat_natCast]

theorem pvK_50 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 50 = (xN (parK d n e).q (NeO d n e) : ℤ) := by
  have h1 : 1 ≤ NeO d n e := NeK_pos hd hn
  have h2 := pow_size_le h1
  pvsk; rw [pvK_18, pvK_49 hd hn, pvK_37, xN]; push_cast [Nat.cast_sub h2]; ring_nf

theorem pvK_51 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvK d n e 51 = (gsm_mercq (parK d n e).q (xN (parK d n e).q (NeO d n e)) (parK d n e).q : ℤ) := by
  pvsk; rw [pvK_26, pvK_50 hd hn, Int.toNat_natCast, Int.toNat_natCast]

/-- `L0 = lnQ q N_e` at `2^q`. -/
def L0NK (d n e : ℕ) : ℤ := loI (parK d n e).q (NeO d n e)

theorem pvK_54 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 54 = L0NK d n e := by
  have e52 : pvK d n e 52 = pvK d n e 47 - pvK d n e 51 := by pvsk
  have e53 : pvK d n e 53 = max (pvK d n e 52) 0 := by pvsk
  pvsk; rw [e53, e52, pvK_20, pvK_47, pvK_51 hd hn, L0NK, loI, xN]

theorem pvK_55 : pvK d n e 55 = ((2 * d + 2 : ℕ) : ℤ) := by
  pvsk; rw [pvK_1]; push_cast; ring

theorem pvK_56 : pvK d n e 56 = ((2 * d + 2 + 1 : ℕ) : ℤ) := by pvsk; rw [pvK_55, pvK_0]; push_cast; ring

theorem pvK_57 : pvK d n e 57 = ((2 * d + 2).size : ℤ) := by
  pvsk; rw [pvK_56, Int.toNat_natCast, ← size_eq_clog]

theorem pvK_58 : pvK d n e 58 = (((2 * d + 2).size - 1 : ℕ) : ℤ) := by
  have : 1 ≤ (2 * d + 2).size := Nat.size_pos.2 (by omega)
  pvsk; rw [pvK_57, pvK_0]; omega

theorem pvK_59 : pvK d n e 59 = 2 ^ ((2 * d + 2).size - 1) := by
  pvsk; rw [pvK_58, Int.toNat_natCast]

theorem pvK_60 : pvK d n e 60 = (xN (parK d n e).q (2 * d + 2) : ℤ) := by
  have h2 := pow_size_le (N := 2 * d + 2) (by omega)
  pvsk; rw [pvK_55, pvK_59, pvK_37, xN]; push_cast [Nat.cast_sub h2]; ring_nf

/-- `lnQ q (2d + 2)` at `2^q`. -/
def L1NK (d n e : ℕ) : ℤ := loI (parK d n e).q (2 * d + 2)

theorem pvK_64 : pvK d n e 64 = L1NK d n e := by
  have e61 : pvK d n e 61 = (gsm_mercq (parK d n e).q (xN (parK d n e).q (2 * d + 2)) (parK d n e).q : ℤ) := by
    pvsk; rw [pvK_26, pvK_60, Int.toNat_natCast, Int.toNat_natCast]
  have e62 : pvK d n e 62 = pvK d n e 47 - pvK d n e 61 := by pvsk
  have e63 : pvK d n e 63 = max (pvK d n e 62) 0 := by pvsk
  pvsk; rw [e63, e62, pvK_57, pvK_47, e61, L1NK, loI, xN]

/-- `lnErr q N_e` at `2^q`. -/
def ENK (d n e : ℕ) : ℤ := ((2 * (NeO d n e).size * (4 * (parK d n e).q + 1) : ℕ) : ℤ)

/-- `lnErr q (2d + 2)` at `2^q`. -/
def E1NK (d n e : ℕ) : ℤ := ((2 * (2 * d + 2).size * (4 * (parK d n e).q + 1) : ℕ) : ℤ)

theorem pvK_65 : pvK d n e 65 = ENK d n e := by
  pvsk; rw [pvK_1, pvK_20, pvK_2, pvK_26, pvK_0, ENK]; push_cast; ring

theorem pvK_66 : pvK d n e 66 = E1NK d n e := by
  pvsk; rw [pvK_1, pvK_57, pvK_2, pvK_26, pvK_0, E1NK]; push_cast; ring

/-- `Le` at `2^q`. -/
def LeNK (d n e : ℕ) : ℤ := 36 * (L0NK d n e - ENK d n e)

/-- `36 (L0 + η_e)` at `2^q`. -/
def LhNK (d n e : ℕ) : ℤ := 36 * (L0NK d n e + ENK d n e)

theorem pvK_67 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 67 = LeNK d n e := by
  pvsk; rw [pvK_12, pvK_54 hd hn, pvK_65, LeNK]

theorem pvK_68 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 68 = LhNK d n e := by
  pvsk; rw [pvK_12, pvK_54 hd hn, pvK_65, LhNK]

end Logs

/-! ## The fields -/

/-- `2^q` on the integers. -/
def QZK (d n e : ℕ) : ℤ := 2 ^ (parK d n e).q
/-- `2^pF` on the integers. -/
def PFZK (d n e : ℕ) : ℤ := 2 ^ (parK d n e).pF
/-- `2^p` on the integers. -/
def PZK (d n e : ℕ) : ℤ := 2 ^ (parK d n e).p
/-- `RD = ⌊√(d 4^q)⌋`. -/
def RDZK (d n e : ℕ) : ℤ := Nat.sqrt (d * 4 ^ (parK d n e).q)
/-- `RN = ⌊√(n 4^q)⌋`. -/
def RNZK (d n e : ℕ) : ℤ := Nat.sqrt (n * 4 ^ (parK d n e).q)
/-- `ε'` at `2^pF`. -/
def epsZK (d n e : ℕ) : ℤ := epsI d (RDZK d n e) (RNZK d n e) (LhNK d n e) (PFZK d n e) (QZK d n e)
/-- `λ'` at `2^pF`. -/
def lamZK (d n e : ℕ) : ℤ := lamI d (LeNK d n e) (PFZK d n e) (QZK d n e)
/-- `η'` at `2^pF`. -/
def etaZK (d n e : ℕ) : ℤ := etaI (RDZK d n e) (RNZK d n e) (LeNK d n e) (PFZK d n e) (QZK d n e)
/-- `sig2'` at `2^pF`. -/
def sigZK (d n e : ℕ) : ℤ := sigI (LeNK d n e) (PFZK d n e) (QZK d n e)
/-- `ρ'` at `2^pF`. -/
def rhoZK (d n e : ℕ) : ℤ := rhoI d (LeNK d n e) (PFZK d n e) (QZK d n e)
/-- `κ_c'` at `2^pF`. -/
def kapZK (d n e : ℕ) : ℤ := kapI (etaZK d n e) (lamZK d n e) (PFZK d n e)
/-- `ν'` at `2^pF`. -/
def nuZK (d n e : ℕ) : ℤ := nuI (lamZK d n e) (PFZK d n e)
/-- `2^q sqrtUp q (L1 + η_1)`. -/
def RSZK (d n e : ℕ) : ℤ := (Nat.sqrt ((L1NK d n e + E1NK d n e) * QZK d n e).toNat : ℤ) + 1
/-- `R'` at `2^pF`. -/
def RZK (d n e : ℕ) : ℤ := RI d (RSZK d n e) (PFZK d n e) (QZK d n e)
/-- `s'_b` at `2^pF`. -/
def sbZK (d n e : ℕ) : ℤ := sbI (NeO d n e) (RZK d n e) (PFZK d n e)
/-- `2^q sqrtUp q (N_e / Le')`. -/
def SWZK (d n e : ℕ) : ℤ :=
  (Nat.sqrt (((NeO d n e : ℤ) * QZK d n e ^ 3 + LeNK d n e - 1) / LeNK d n e).toNat : ℤ) + 1
/-- `W'` at `2^pF`. -/
def WZK (d n e : ℕ) : ℤ := WI d (RZK d n e) (SWZK d n e) (PFZK d n e) (QZK d n e)
/-- `2^q sqrtUp q sig2'`. -/
def S1ZK (d n e : ℕ) : ℤ := (Nat.sqrt ((sigZK d n e * QZK d n e ^ 2 + PFZK d n e - 1) / PFZK d n e).toNat : ℤ) + 1
/-- `A_0` at `2^p`. -/
def A0ZK (d n e : ℕ) : ℤ := A0I (S1ZK d n e) (PZK d n e) (QZK d n e)
/-- `B_0` at `2^p`. -/
def B0ZK (d n e : ℕ) : ℤ := B0I (S1ZK d n e) (PZK d n e) (QZK d n e)
/-- `R_int`. -/
def RintZK (d n e : ℕ) : ℤ := rintI (RZK d n e) (PFZK d n e)

section Fields

variable {d n e : ℕ}

theorem pvK_35z : pvK d n e 35 = PZK d n e := pvK_35 d n e
theorem pvK_36z : pvK d n e 36 = PFZK d n e := pvK_36 d n e
theorem pvK_37z : pvK d n e 37 = QZK d n e := pvK_37 d n e
theorem pvK_42z : pvK d n e 42 = RDZK d n e := pvK_42 d n e
theorem pvK_44z : pvK d n e 44 = RNZK d n e := pvK_44 d n e

theorem pvK_69 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 69 = epsZK d n e := by
  rw [pvK_c]; simp only [parStK, List.getD_cons_succ, List.getD_cons_zero, SStep.sem, ieEps, slZ, parIK,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceIte]
  rw [pvK_42z, pvK_44z, pvK_68 hd hn, pvK_36z, pvK_37z, pvK_15, pvK_0, epsZK, epsI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvK_70 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 70 = lamZK d n e := by
  pvsk; rw [pvK_1, pvK_37z, pvK_36z, pvK_13, pvK_67 hd hn, lamZK, lamI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvK_71 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 71 = etaZK d n e := by
  pvsk; rw [pvK_1, pvK_42z, pvK_37z, pvK_36z, pvK_67 hd hn, pvK_44z, etaZK, etaI]

theorem pvK_72 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 72 = sigZK d n e := by
  pvsk; rw [pvK_1, pvK_37z, pvK_36z, pvK_3, pvK_67 hd hn, sigZK, sigI]

theorem pvK_73 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 73 = rhoZK d n e := by
  pvsk; rw [pvK_14, pvK_67 hd hn, pvK_36z, pvK_37z, rhoZK, rhoI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvK_74 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 74 = kapZK d n e := by
  pvsk; rw [pvK_1, pvK_71 hd hn, pvK_70 hd hn, pvK_36z, pvK_2, kapZK, kapI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvK_75 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 75 = nuZK d n e := by
  pvsk; rw [pvK_1, pvK_36z, pvK_70 hd hn, nuZK, nuI]

theorem pvK_76 : pvK d n e 76 = L1NK d n e + E1NK d n e := by pvsk; rw [pvK_64, pvK_66]

theorem pvK_77 : pvK d n e 77 = (L1NK d n e + E1NK d n e) * QZK d n e := by pvsk; rw [pvK_76, pvK_37z]

theorem pvK_78 : pvK d n e 78 = (Nat.sqrt ((L1NK d n e + E1NK d n e) * QZK d n e).toNat : ℤ) := by pvsk; rw [pvK_77]

theorem pvK_79 : pvK d n e 79 = RSZK d n e := by
  pvsk; rw [pvK_78, pvK_0, RSZK]

theorem pvK_80 : pvK d n e 80 = RZK d n e := by
  pvsk; rw [pvK_16, pvK_79, pvK_36z, pvK_37z, pvK_0, RZK, RI]

theorem pvK_81 : pvK d n e 81 = sbZK d n e := by
  pvsk; rw [pvK_36z, pvK_18, pvK_80, sbZK, sbI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvK_82 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvK d n e 82 = ((NeO d n e : ℤ) * QZK d n e ^ 3 + LeNK d n e - 1) / LeNK d n e := by
  pvsk; rw [pvK_18, pvK_37z, pvK_67 hd hn, pvK_0]; ring_nf

theorem pvK_83 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvK d n e 83 = (Nat.sqrt (((NeO d n e : ℤ) * QZK d n e ^ 3 + LeNK d n e - 1) / LeNK d n e).toNat : ℤ) := by
  pvsk; rw [pvK_82 hd hn]

theorem pvK_84 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 84 = SWZK d n e := by
  pvsk; rw [pvK_83 hd hn, pvK_0, SWZK]

theorem pvK_85 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 85 = WZK d n e := by
  pvsk; rw [pvK_80, pvK_37z, pvK_2, pvK_84 hd hn, pvK_36z, pvK_0, WZK, WI]

theorem pvK_86 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 86 = (sigZK d n e * QZK d n e ^ 2 + PFZK d n e - 1) / PFZK d n e := by
  pvsk; rw [pvK_72 hd hn, pvK_37z, pvK_36z, pvK_0]; ring_nf

theorem pvK_87 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvK d n e 87 = (Nat.sqrt ((sigZK d n e * QZK d n e ^ 2 + PFZK d n e - 1) / PFZK d n e).toNat : ℤ) := by
  pvsk; rw [pvK_86 hd hn]

theorem pvK_88 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 88 = S1ZK d n e := by
  pvsk; rw [pvK_87 hd hn, pvK_0, S1ZK]

theorem pvK_89 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 89 = A0ZK d n e := by
  pvsk; rw [pvK_1, pvK_88 hd hn, pvK_35z, pvK_37z, A0ZK, A0I]

theorem pvK_90 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvK d n e 90 = B0ZK d n e := by
  pvsk; rw [pvK_1, pvK_37z, pvK_35z, pvK_88 hd hn, B0ZK, B0I]

theorem pvK_91 : pvK d n e 91 = RintZK d n e := by
  pvsk; rw [pvK_80, pvK_36z, pvK_0, RintZK, rintI]

theorem pvK_92 : pvK d n e 92 = (Bit.Sched.nBlk d : ℤ) := by
  pvsk; rw [pvK_21, pvK_1, pvK_0, Bit.Sched.nBlk]; push_cast; ring_nf

end Fields

end AdversarialBco.Unified.PrmK
