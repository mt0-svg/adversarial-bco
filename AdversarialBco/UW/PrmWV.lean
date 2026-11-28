/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PrmKLink

@[expose] public section

/-!
# PARAM-W on the machine: the straight line

PARAM-W (UW/ProgPure.lean, `parOW`, `b0OW`, `y0OW`) as one straight line `parStW` of 94 steps on PARAM's region
(step `k` writes the slot `30 + k`), run after BL-O's PARAM. Its inputs are `d` (slot `0`), `n` (slot `3`),
`N_e = NeO d n e` (slot `sNe = 7`, written by PARAM) and `k_δ = e` (slot `29`). It recomputes PARAM's precisions
`p, q, pF`, the powers `2^p, 2^pF, 2^q`, the roots `R_d, R_n` and Mercator's constant (steps `17` to `36`, as PARAM's
steps `18` to `47`), then the floor `N_0 = 15 · 2^17 d³ n⁴`, `lnQ q N_0` and `lnErr q N_0` (as PARAM does for `N_e`),
`l_2 = lnQ q 2 + lnErr q 2`, the scaling `u'` and its root `r_u`, `ι⁺`, the fields `ε', λ', η', σ²', ρ', κ_c', ν'`
at `2^pF` and `A_0, B_0` at `2^p`, and ends with `b0` and `y0` at `2^p` in the slots `122` and `123`.

`pvW d n e k` is the value of step `k`; `pvW_k` gives it in closed form (`L00W`, ..., `y0ZW`).
-/

namespace AdversarialBco.UW.PrmW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN)
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.Unified.PrmK

/-- **PARAM-W as a straight line**; step `k` writes the slot `30 + k`. -/
def parStW : List SStep :=
  [ .cst 1, .cst 2, .cst 4, .cst 8, .cst 10, .cst 16, .cst 24, .cst 40, .cst 160, .cst 7,                 -- 0 - 9
    .cst 12, .cst 18, .cst 36, .cst 725, .cst 1450, .cst 14500, .cst 1966080,                             -- 10 - 16
    -- 17: N_e (slot 7); 18: N_e + 1; 19: ℓe = size N_e; 20: d + 1; 21: ℓd; 22: p = 10 ℓe + 16 ℓd + 160
    .ie (.sc 7), .ie (iA (rv 17) (rv 0)), .cl 18, .ie (iA dI (rv 0)), .cl 20,
    .ie (iA (iA (iM (rv 4) (rv 19)) (iM (rv 5) (rv 21))) (rv 8)),
    -- 23: ℓe + 1; 24: size ℓe; 25: q = p + 2 size ℓe + 24; 26: pF = p + 2 ℓe + 4 ℓd + 40
    .ie (iA (rv 19) (rv 0)), .cl 23, .ie (iA (iA (rv 22) (iM (rv 1) (rv 24))) (rv 6)),
    .ie (iA (iA (iA (rv 22) (iM (rv 1) (rv 19))) (iM (rv 2) (rv 21))) (rv 7)),
    -- 27: 2^p; 28: 2^pF; 29: 2^q; 30: d 4^q; 31: RD; 32: n 4^q; 33: RN; 34: q - 1; 35: 2^(q - 1); 36: M
    .pw 22, .pw 26, .pw 25, .ie (iM (iM dI (rv 29)) (rv 29)), .sq 30, .ie (iM (iM nI (rv 29)) (rv 29)), .sq 32,
    .ie (iS (rv 25) (rv 0)), .pw 34, .mc 25 29 35,
    -- 37: N_0; 38: N_0 + 1; 39: ℓ0 = size N_0; 40: ℓ0 - 1; 41: 2^(ℓ0 - 1); 42: X_0; 43: Mercator's sum at X_0
    .ie (iM (iM (iM (iM (iM (iM (iM (rv 16) dI) dI) dI) nI) nI) nI) nI), .ie (iA (rv 37) (rv 0)), .cl 38,
    .ie (iS (rv 39) (rv 0)), .pw 40, .ie (iD (iM (iS (rv 37) (rv 41)) (rv 29)) (rv 37)), .mc 25 29 42,
    -- 44, 45: max (M - it, 0); 46: lnQ q N_0 at 2^q; 47: lnErr q N_0 at 2^q; 48: L_00; 49: L_01
    .ie (iS (rv 36) (rv 43)), .mx 44, .ie (iS (iM (rv 39) (rv 36)) (rv 45)),
    .ie (iM (iM (rv 1) (rv 39)) (iA (iM (rv 2) (rv 25)) (rv 0))), .ie (iS (rv 46) (rv 47)), .ie (iA (rv 46) (rv 47)),
    -- 50: X_2 = 0; 51: Mercator's sum at 0; 52, 53: max (M - it, 0); 54: lnQ q 2 at 2^q; 55: l_2 at 2^q
    .cst 0, .mc 25 29 50, .ie (iS (rv 36) (rv 51)), .mx 52, .ie (iS (iM (rv 1) (rv 36)) (rv 53)),
    .ie (iA (rv 54) (iM (iM (rv 1) (rv 1)) (iA (iM (rv 2) (rv 25)) (rv 0)))),
    -- 56: A = 7 d L_00; 57: u' at 2^p; 58: u' 4^q at 1; 59: RU
    .ie (iM (iM (rv 9) dI) (rv 48)),
    .ie (iD (iS (iA (iM (iA (rv 56) (iM (.sc 29) (rv 55))) (rv 27)) (rv 56)) (rv 0)) (rv 56)),
    .ie (iD (iM (iM (rv 57) (rv 29)) (rv 29)) (rv 27)), .sq 58,
    -- 60: Le at 2^q; 61: 36 L_01 at 2^q; 62: V = 14500 d RD Le^5 RU; 63: (2^q)^6; 64: ι⁺ at 2^p
    .ie (iM (rv 12) (rv 48)), .ie (iM (rv 12) (rv 49)),
    .ie (iM (iM (iM (iM (rv 15) dI) (rv 31)) (iM (iM (iM (iM (rv 60) (rv 60)) (rv 60)) (rv 60)) (rv 60))) (rv 59)),
    .ie (iM (iM (iM (rv 29) (rv 29)) (iM (rv 29) (rv 29))) (iM (rv 29) (rv 29))),
    .ie (iD (iS (iA (iM (iM (iA (rv 33) (rv 0)) (rv 63)) (rv 27)) (rv 62)) (rv 0)) (rv 62)),
    -- 65: ε'; 66: λ'; 67: η'; 68: sig2'; 69: ρ'; 70: κ_c'; 71: ν' (numerators at 2^pF)
    .ie (iD (iS (iA (iM (iM (iM (iM (iM (rv 15) dI) (iA (rv 31) (rv 0)))
        (iM (iM (iM (iM (rv 61) (rv 61)) (rv 61)) (rv 61)) (rv 61))) (iA (rv 59) (rv 0))) (rv 28))
        (iM (rv 63) (rv 33))) (rv 0)) (iM (rv 63) (rv 33))),
    .ie (iD (iA (iM (iM (rv 1) (iM (rv 29) (rv 29))) (rv 28)) (iM (iM (rv 13) dI) (iM (rv 60) (rv 60))))
      (iM (rv 1) (iM (iM (rv 13) dI) (iM (rv 60) (rv 60))))),
    .ie (iD (iA (iM (iM (rv 1) (iM (iM (rv 31) (rv 29)) (rv 29))) (rv 28)) (iM (iM (rv 60) (rv 33)) (rv 59)))
      (iM (rv 1) (iM (iM (rv 60) (rv 33)) (rv 59)))),
    .ie (iD (iA (iM (iM (rv 1) (rv 29)) (rv 28)) (iM (rv 3) (rv 60))) (iM (rv 1) (iM (rv 3) (rv 60)))),
    .ie (iD (iM (iM (iM (iM (iM (iM (rv 14) dI) dI) (rv 60)) (rv 60)) (rv 60)) (rv 28))
      (iM (iM (rv 29) (rv 29)) (rv 29))),
    .ie (iD (iA (iM (iM (rv 1) (iM (rv 67) (rv 66))) (rv 28))
        (iM (rv 2) (iM (iS (rv 28) (rv 66)) (iS (rv 28) (rv 66)))))
      (iM (rv 1) (iM (rv 2) (iM (iS (rv 28) (rv 66)) (iS (rv 28) (rv 66)))))),
    .ie (iD (iA (iM (iM (rv 1) (rv 28)) (rv 28)) (iS (rv 28) (rv 66))) (iM (rv 1) (iS (rv 28) (rv 66)))),
    -- 72: sig2' 4^q rounded up; 73: its root; 74: plus one; 75: A_0; 76: B_0 (at 2^p)
    .ie (iD (iS (iA (iM (rv 68) (iM (rv 29) (rv 29))) (rv 28)) (rv 0)) (rv 28)), .sq 72, .ie (iA (rv 73) (rv 0)),
    .ie (iD (iA (iM (iM (rv 1) (rv 74)) (rv 27)) (rv 29)) (iM (rv 1) (rv 29))),
    .ie (iD (iA (iM (iM (rv 1) (rv 29)) (rv 27)) (rv 74)) (iM (rv 1) (rv 74))),
    -- 77: 12 L_01 2^q; 78: its root; 79: plus one (2^q sqrtUp q (12 L_01))
    .ie (iM (iM (rv 10) (rv 49)) (rv 29)), .sq 77, .ie (iA (rv 78) (rv 0)),
    -- 80 - 91: unused
    .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0, .cst 0,
    -- 92: b0 at 2^p (slot 122); 93: y0 at 2^p (slot 123)
    .ie (iD (iS (iA (iM (iA (iM (iA (iM (rv 1) dI) (rv 1)) (rv 29)) (rv 61)) (rv 27)) (rv 29)) (rv 0)) (rv 29)),
    .ie (iD (iS (iA (iA (iM (iA (iM (rv 4) (rv 27)) (iM (rv 11) (rv 64))) (rv 29)) (iM (iM (rv 4) (rv 79)) (rv 27)))
      (rv 29)) (rv 0)) (rv 29)) ]

theorem parStW_length : parStW.length = 94 := rfl

/-! ## The values -/

/-- The inputs of PARAM-W at `k_δ = e`: `d` in slot `0`, `n` in slot `3`, `N_e` in slot `7`, `e` in slot `29`. -/
def parIW (d n e : ℕ) : ℕ → ℤ := fun y =>
  if y = 0 then d else if y = 3 then n else if y = 7 then (NeO d n e : ℤ) else if y = 29 then e else 0

/-- The value of step `k` of PARAM-W. -/
abbrev pvW (d n e : ℕ) (k : ℕ) : ℤ := SL.val parStW 30 (parIW d n e) k

theorem pvW_c (d n e k : ℕ) :
    pvW d n e k = (parStW.getD k (.cst 0)).sem 30 (parIW d n e) (fun j => if j < k then pvW d n e j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of PARAM-W unfolded: the step, its expression, the reads of the slots. -/
local macro "pvsw" : tactic => `(tactic| (rw [pvW_c]; simp only [parStW, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, rv, dI, nI, iM, iA, iS, iD, parIW, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
  ↓reduceIte]))

section Values

variable (d n e : ℕ)

theorem pvW_0 : pvW d n e 0 = 1 := by pvsw
theorem pvW_1 : pvW d n e 1 = 2 := by pvsw
theorem pvW_2 : pvW d n e 2 = 4 := by pvsw
theorem pvW_3 : pvW d n e 3 = 8 := by pvsw
theorem pvW_4 : pvW d n e 4 = 10 := by pvsw
theorem pvW_5 : pvW d n e 5 = 16 := by pvsw
theorem pvW_6 : pvW d n e 6 = 24 := by pvsw
theorem pvW_7 : pvW d n e 7 = 40 := by pvsw
theorem pvW_8 : pvW d n e 8 = 160 := by pvsw
theorem pvW_9 : pvW d n e 9 = 7 := by pvsw
theorem pvW_10 : pvW d n e 10 = 12 := by pvsw
theorem pvW_11 : pvW d n e 11 = 18 := by pvsw
theorem pvW_12 : pvW d n e 12 = 36 := by pvsw
theorem pvW_13 : pvW d n e 13 = 725 := by pvsw
theorem pvW_14 : pvW d n e 14 = 1450 := by pvsw
theorem pvW_15 : pvW d n e 15 = 14500 := by pvsw
theorem pvW_16 : pvW d n e 16 = 1966080 := by pvsw

theorem pvW_17 : pvW d n e 17 = (NeO d n e : ℤ) := by pvsw

theorem pvW_18 : pvW d n e 18 = ((NeO d n e + 1 : ℕ) : ℤ) := by
  pvsw; rw [pvW_17, pvW_0]; push_cast; ring

theorem pvW_19 : pvW d n e 19 = ((NeO d n e).size : ℤ) := by
  pvsw; rw [pvW_18, Int.toNat_natCast, ← size_eq_clog]

theorem pvW_20 : pvW d n e 20 = ((d + 1 : ℕ) : ℤ) := by
  pvsw; rw [pvW_0]; push_cast; ring

theorem pvW_21 : pvW d n e 21 = (d.size : ℤ) := by
  pvsw; rw [pvW_20, Int.toNat_natCast, ← size_eq_clog]

theorem pvW_22 : pvW d n e 22 = ((parK d n e).p : ℤ) := by
  pvsw; rw [pvW_4, pvW_19, pvW_5, pvW_21, pvW_8]; simp only [parK, parN]; push_cast; ring

theorem pvW_23 : pvW d n e 23 = (((NeO d n e).size + 1 : ℕ) : ℤ) := by
  pvsw; rw [pvW_19, pvW_0]; push_cast; ring

theorem pvW_24 : pvW d n e 24 = ((NeO d n e).size.size : ℤ) := by
  pvsw; rw [pvW_23, Int.toNat_natCast, ← size_eq_clog]

theorem pvW_25 : pvW d n e 25 = ((parK d n e).q : ℤ) := by
  pvsw; rw [pvW_22, pvW_1, pvW_24, pvW_6]; simp only [parK, parN]; push_cast; ring

theorem pvW_26 : pvW d n e 26 = ((parK d n e).pF : ℤ) := by
  pvsw; rw [pvW_22, pvW_1, pvW_19, pvW_2, pvW_21, pvW_7]; simp only [parK, parN]; push_cast; ring

theorem pvW_27 : pvW d n e 27 = 2 ^ (parK d n e).p := by
  pvsw; rw [pvW_22, Int.toNat_natCast]

theorem pvW_28 : pvW d n e 28 = 2 ^ (parK d n e).pF := by
  pvsw; rw [pvW_26, Int.toNat_natCast]

theorem pvW_29 : pvW d n e 29 = 2 ^ (parK d n e).q := by
  pvsw; rw [pvW_25, Int.toNat_natCast]

theorem pvW_30 : pvW d n e 30 = ((d * 4 ^ (parK d n e).q : ℕ) : ℤ) := by
  pvsw; rw [pvW_29, four_pow]; push_cast; ring

theorem pvW_31 : pvW d n e 31 = (Nat.sqrt (d * 4 ^ (parK d n e).q) : ℤ) := by
  pvsw; rw [pvW_30, Int.toNat_natCast]

theorem pvW_32 : pvW d n e 32 = ((n * 4 ^ (parK d n e).q : ℕ) : ℤ) := by
  pvsw; rw [pvW_29, four_pow]; push_cast; ring

theorem pvW_33 : pvW d n e 33 = (Nat.sqrt (n * 4 ^ (parK d n e).q) : ℤ) := by
  pvsw; rw [pvW_32, Int.toNat_natCast]

theorem pvW_34 : pvW d n e 34 = (((parK d n e).q - 1 : ℕ) : ℤ) := by
  pvsw; rw [pvW_25, pvW_0]; have := qK_ge d n e; omega

theorem pvW_35 : pvW d n e 35 = 2 ^ ((parK d n e).q - 1) := by
  pvsw; rw [pvW_34, Int.toNat_natCast]

theorem pvW_36 : pvW d n e 36 = (gsm_mercq (parK d n e).q (2 ^ ((parK d n e).q - 1)) (parK d n e).q : ℤ) := by
  pvsw; rw [pvW_25, pvW_35, Int.toNat_natCast, toNat_two_pow]

/-- The floor `N_0 = NeO d n 0`. -/
theorem pvW_37 : pvW d n e 37 = (NeO d n 0 : ℤ) := by
  pvsw; rw [pvW_16]; simp only [NeO]; push_cast; ring

theorem pvW_38 : pvW d n e 38 = ((NeO d n 0 + 1 : ℕ) : ℤ) := by
  pvsw; rw [pvW_37, pvW_0]; push_cast; ring

theorem pvW_39 : pvW d n e 39 = ((NeO d n 0).size : ℤ) := by
  pvsw; rw [pvW_38, Int.toNat_natCast, ← size_eq_clog]

end Values

/-! ## The logarithms -/

section Logs

variable {d n e : ℕ}

theorem pvW_40 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 40 = (((NeO d n 0).size - 1 : ℕ) : ℤ) := by
  have : 1 ≤ (NeO d n 0).size := Nat.size_pos.2 (NeK_pos hd hn)
  pvsw; rw [pvW_39, pvW_0]; omega

theorem pvW_41 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 41 = 2 ^ ((NeO d n 0).size - 1) := by
  pvsw; rw [pvW_40 hd hn, Int.toNat_natCast]

theorem pvW_42 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 42 = (xN (parK d n e).q (NeO d n 0) : ℤ) := by
  have h1 : 1 ≤ NeO d n 0 := NeK_pos hd hn
  have h2 := pow_size_le h1
  pvsw; rw [pvW_37, pvW_41 hd hn, pvW_29, xN]; push_cast [Nat.cast_sub h2]; ring_nf

theorem pvW_43 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvW d n e 43 = (gsm_mercq (parK d n e).q (xN (parK d n e).q (NeO d n 0)) (parK d n e).q : ℤ) := by
  pvsw; rw [pvW_25, pvW_42 hd hn, Int.toNat_natCast, Int.toNat_natCast]

/-- `lnQ q N_0` at `2^q`. -/
def L0W (d n e : ℕ) : ℤ := loI (parK d n e).q (NeO d n 0)

/-- `lnErr q N_0` at `2^q`. -/
def E0W (d n e : ℕ) : ℤ := ((2 * (NeO d n 0).size * (4 * (parK d n e).q + 1) : ℕ) : ℤ)

/-- `L_00 = lnQ q N_0 - lnErr q N_0` at `2^q`. -/
def L00W (d n e : ℕ) : ℤ := L0W d n e - E0W d n e

/-- `L_01 = lnQ q N_0 + lnErr q N_0` at `2^q`. -/
def L01W (d n e : ℕ) : ℤ := L0W d n e + E0W d n e

theorem pvW_46 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 46 = L0W d n e := by
  have e44 : pvW d n e 44 = pvW d n e 36 - pvW d n e 43 := by pvsw
  have e45 : pvW d n e 45 = max (pvW d n e 44) 0 := by pvsw
  pvsw; rw [e45, e44, pvW_39, pvW_36, pvW_43 hd hn, L0W, loI, xN]

theorem pvW_47 : pvW d n e 47 = E0W d n e := by
  pvsw; rw [pvW_1, pvW_39, pvW_2, pvW_25, pvW_0, E0W]; push_cast; ring

theorem pvW_48 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 48 = L00W d n e := by
  pvsw; rw [pvW_46 hd hn, pvW_47, L00W]

theorem pvW_49 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 49 = L01W d n e := by
  pvsw; rw [pvW_46 hd hn, pvW_47, L01W]

/-- `lnQ q 2 + lnErr q 2` at `2^q`. -/
def L2W (d n e : ℕ) : ℤ := loI (parK d n e).q 2 + ((2 * 2 * (4 * (parK d n e).q + 1) : ℕ) : ℤ)

theorem loI_two (q : ℕ) :
    loI q 2 = 2 * (gsm_mercq q (2 ^ (q - 1)) q : ℤ) - max ((gsm_mercq q (2 ^ (q - 1)) q : ℤ) - gsm_mercq q 0 q) 0 := by
  have h2 : Nat.size 2 = 2 := by decide
  unfold loI
  rw [h2]
  norm_num

theorem pvW_50 : pvW d n e 50 = 0 := by pvsw

theorem pvW_55 : pvW d n e 55 = L2W d n e := by
  have e51 : pvW d n e 51 = (gsm_mercq (parK d n e).q 0 (parK d n e).q : ℤ) := by
    pvsw; rw [pvW_25, pvW_50, Int.toNat_natCast]; rfl
  have e52 : pvW d n e 52 = pvW d n e 36 - pvW d n e 51 := by pvsw
  have e53 : pvW d n e 53 = max (pvW d n e 52) 0 := by pvsw
  have e54 : pvW d n e 54 = pvW d n e 1 * pvW d n e 36 - pvW d n e 53 := by pvsw
  pvsw; rw [e54, e53, e52, e51, pvW_36, pvW_1, pvW_2, pvW_25, pvW_0, L2W, loI_two]; push_cast; ring

end Logs

/-! ## The scaling and `ι⁺` -/

/-- `2^q`, `2^pF`, `2^p` and the roots on the integers (PARAM's). -/
abbrev QW (d n e : ℕ) : ℤ := QZK d n e
abbrev PFW (d n e : ℕ) : ℤ := PFZK d n e
abbrev PW (d n e : ℕ) : ℤ := PZK d n e

/-- `A = 7 d L_00`. -/
def AW (d n e : ℕ) : ℤ := 7 * d * L00W d n e

/-- `u'` at `2^p`: `⌈(1 + k_δ l_2/(7 d L_00)) 2^p⌉`. -/
def UNW (d n e : ℕ) : ℤ := ((AW d n e + e * L2W d n e) * PW d n e + AW d n e - 1) / AW d n e

/-- `r_u` at `2^q`: `⌊√⌊u' 4^q⌋⌋`. -/
def RUW (d n e : ℕ) : ℤ := (Nat.sqrt ((UNW d n e * QW d n e * QW d n e / PW d n e).toNat) : ℤ)

/-- `Le = 36 L_00` at `2^q`. -/
def LeNW (d n e : ℕ) : ℤ := 36 * L00W d n e

/-- `36 L_01` at `2^q`. -/
def LhNW (d n e : ℕ) : ℤ := 36 * L01W d n e

/-- `V = 14500 d RD Le^5 RU`. -/
def VW (d n e : ℕ) : ℤ := 14500 * d * RDZK d n e * LeNW d n e ^ 5 * RUW d n e

/-- `ι⁺` at `2^p`: `⌈(RN + 1) 2^{6q} 2^p / V⌉`. -/
def iotaZW (d n e : ℕ) : ℤ := ((RNZK d n e + 1) * QW d n e ^ 6 * PW d n e + VW d n e - 1) / VW d n e

section Scale

variable {d n e : ℕ}

theorem pvW_56 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 56 = AW d n e := by
  pvsw; rw [pvW_9, pvW_48 hd hn, AW]

theorem pvW_57 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 57 = UNW d n e := by
  pvsw; rw [pvW_56 hd hn, pvW_55, pvW_27, pvW_0, UNW]; rfl

theorem pvW_58 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 58 = UNW d n e * QW d n e * QW d n e / PW d n e := by
  pvsw; rw [pvW_57 hd hn, pvW_29, pvW_27]; rfl

theorem pvW_59 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 59 = RUW d n e := by
  pvsw; rw [pvW_58 hd hn, RUW]

theorem pvW_60 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 60 = LeNW d n e := by
  pvsw; rw [pvW_12, pvW_48 hd hn, LeNW]

theorem pvW_61 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 61 = LhNW d n e := by
  pvsw; rw [pvW_12, pvW_49 hd hn, LhNW]

theorem pvW_62 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 62 = VW d n e := by
  pvsw; rw [pvW_15, pvW_31, pvW_60 hd hn, pvW_59 hd hn, VW, RDZK]; ring

theorem pvW_63 : pvW d n e 63 = QW d n e ^ 6 := by
  pvsw; rw [pvW_29]; simp only [QW, QZK]; ring

theorem pvW_64 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 64 = iotaZW d n e := by
  pvsw; rw [pvW_33, pvW_0, pvW_63, pvW_27, pvW_62 hd hn, iotaZW, RNZK]; rfl

end Scale

/-! ## The fields -/

/-- `ε'` at `2^pF`: `⌈14500 d (RD + 1) Lh^5 (RU + 1) 2^pF/(2^{6q} RN)⌉`. -/
def epsZW (d n e : ℕ) : ℤ :=
  (14500 * d * (RDZK d n e + 1) * LhNW d n e ^ 5 * (RUW d n e + 1) * PFW d n e + QW d n e ^ 6 * RNZK d n e - 1) /
    (QW d n e ^ 6 * RNZK d n e)

/-- `λ'` at `2^pF`. -/
def lamZW (d n e : ℕ) : ℤ := lamI d (LeNW d n e) (PFW d n e) (QW d n e)

/-- `η'` at `2^pF`: `rnd(RD 4^q 2^pF/(Le RN RU))`. -/
def etaZW (d n e : ℕ) : ℤ :=
  (2 * (RDZK d n e * QW d n e * QW d n e) * PFW d n e + LeNW d n e * RNZK d n e * RUW d n e) /
    (2 * (LeNW d n e * RNZK d n e * RUW d n e))

/-- `sig2'` at `2^pF`. -/
def sigZW (d n e : ℕ) : ℤ := sigI (LeNW d n e) (PFW d n e) (QW d n e)

/-- `ρ'` at `2^pF`. -/
def rhoZW (d n e : ℕ) : ℤ := rhoI d (LeNW d n e) (PFW d n e) (QW d n e)

/-- `κ_c'` at `2^pF`. -/
def kapZW (d n e : ℕ) : ℤ := kapI (etaZW d n e) (lamZW d n e) (PFW d n e)

/-- `ν'` at `2^pF`. -/
def nuZW (d n e : ℕ) : ℤ := nuI (lamZW d n e) (PFW d n e)

/-- `2^q sqrtUp q sig2'`. -/
def S1ZW (d n e : ℕ) : ℤ := (Nat.sqrt ((sigZW d n e * QW d n e ^ 2 + PFW d n e - 1) / PFW d n e).toNat : ℤ) + 1

/-- `A_0` at `2^p`. -/
def A0ZW (d n e : ℕ) : ℤ := A0I (S1ZW d n e) (PW d n e) (QW d n e)

/-- `B_0` at `2^p`. -/
def B0ZW (d n e : ℕ) : ℤ := B0I (S1ZW d n e) (PW d n e) (QW d n e)

/-- `2^q sqrtUp q (12 L_01)`. -/
def SUW (d n e : ℕ) : ℤ := (Nat.sqrt (12 * L01W d n e * QW d n e).toNat : ℤ) + 1

/-- `b0` at `2^p`: `⌈(2d + 2 + 36 L_01/2^q) 2^p⌉`. -/
def b0ZW (d n e : ℕ) : ℤ := (((2 * d + 2) * QW d n e + LhNW d n e) * PW d n e + QW d n e - 1) / QW d n e

/-- `y0` at `2^p`: `⌈(10 + 18 ι⁺ + 10 sqrtUp q (12 L_01)) 2^p⌉`. -/
def y0ZW (d n e : ℕ) : ℤ :=
  ((10 * PW d n e + 18 * iotaZW d n e) * QW d n e + 10 * SUW d n e * PW d n e + QW d n e - 1) / QW d n e

section Fields

variable {d n e : ℕ}

set_option maxHeartbeats 1000000 in
theorem pvW_65 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 65 = epsZW d n e := by
  pvsw; rw [pvW_15, pvW_31, pvW_0, pvW_61 hd hn, pvW_59 hd hn, pvW_28, pvW_63, pvW_33, epsZW, RDZK, RNZK]
  simp only [PFW, PFZK]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvW_66 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 66 = lamZW d n e := by
  pvsw; rw [pvW_1, pvW_29, pvW_28, pvW_13, pvW_60 hd hn, lamZW, lamI]; simp only [QW, PFW, QZK, PFZK]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvW_67 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 67 = etaZW d n e := by
  pvsw; rw [pvW_1, pvW_31, pvW_29, pvW_28, pvW_60 hd hn, pvW_33, pvW_59 hd hn, etaZW, RDZK, RNZK]
  congr 1 <;> ring

theorem pvW_68 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 68 = sigZW d n e := by
  pvsw; rw [pvW_1, pvW_29, pvW_28, pvW_3, pvW_60 hd hn, sigZW, sigI]; simp only [QW, PFW, QZK, PFZK]

theorem pvW_69 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 69 = rhoZW d n e := by
  pvsw; rw [pvW_14, pvW_60 hd hn, pvW_28, pvW_29, rhoZW, rhoI]; simp only [QW, PFW, QZK, PFZK]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvW_70 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 70 = kapZW d n e := by
  pvsw; rw [pvW_1, pvW_67 hd hn, pvW_66 hd hn, pvW_28, pvW_2, kapZW, kapI]; simp only [PFW, PFZK]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pvW_71 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 71 = nuZW d n e := by
  pvsw; rw [pvW_1, pvW_28, pvW_66 hd hn, nuZW, nuI]; simp only [PFW, PFZK]

theorem pvW_72 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pvW d n e 72 = (sigZW d n e * QW d n e ^ 2 + PFW d n e - 1) / PFW d n e := by
  pvsw; rw [pvW_68 hd hn, pvW_29, pvW_28, pvW_0]; simp only [QW, PFW, QZK, PFZK]
  exact congrArg₂ (· / ·) (by ring) rfl

theorem pvW_74 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 74 = S1ZW d n e := by
  have e73 : pvW d n e 73 = (Nat.sqrt ((sigZW d n e * QW d n e ^ 2 + PFW d n e - 1) / PFW d n e).toNat : ℤ) := by
    pvsw; rw [pvW_72 hd hn]
  pvsw; rw [e73, pvW_0, S1ZW]

theorem pvW_75 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 75 = A0ZW d n e := by
  pvsw; rw [pvW_1, pvW_74 hd hn, pvW_27, pvW_29, A0ZW, A0I]; simp only [QW, PW, QZK, PZK]

theorem pvW_76 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 76 = B0ZW d n e := by
  pvsw; rw [pvW_1, pvW_29, pvW_27, pvW_74 hd hn, B0ZW, B0I]; simp only [QW, PW, QZK, PZK]

theorem pvW_77 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 77 = 12 * L01W d n e * QW d n e := by
  pvsw; rw [pvW_10, pvW_49 hd hn, pvW_29]; rfl

theorem pvW_79 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 79 = SUW d n e := by
  have e78 : pvW d n e 78 = (Nat.sqrt (12 * L01W d n e * QW d n e).toNat : ℤ) := by
    pvsw; rw [pvW_77 hd hn]
  pvsw; rw [e78, pvW_0, SUW]

theorem pvW_92 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 92 = b0ZW d n e := by
  pvsw; rw [pvW_1, pvW_29, pvW_61 hd hn, pvW_27, pvW_0, b0ZW]
  congr 1 <;> (push_cast; ring)

theorem pvW_93 (hd : 1 ≤ d) (hn : 1 ≤ n) : pvW d n e 93 = y0ZW d n e := by
  pvsw; rw [pvW_4, pvW_27, pvW_11, pvW_64 hd hn, pvW_29, pvW_79 hd hn, pvW_0, y0ZW]
  congr 1 <;> ring

end Fields

end AdversarialBco.UW.PrmW
