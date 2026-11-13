/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupParam

@[expose] public section

/-!
# BL's setup on the machine: the values of PARAM's straight line

`pv d n k` is the value of step `k` of `parSt` on the inputs `d` (slot `0`) and `n` (slot `3`); `pv_k` gives it in
closed form, on the naturals of PARAM (`ℓe`, `ℓd`, `p`, `q`, `pF`, `B`) and the integer formulas of its fields
(`lamI`, ..., `loI`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-! ## PARAM's fields on the integers (`PF = 2^pF`, `Q = 2^q`, `P = 2^p`) -/

/-- `λ'` at `2^pF`. -/
def lamI (d LeN PF Q : ℤ) : ℤ := (2 * Q ^ 2 * PF + 725 * d * LeN ^ 2) / (2 * (725 * d * LeN ^ 2))

/-- `η'` at `2^pF`. -/
def etaI (RD RN LeN PF Q : ℤ) : ℤ := (2 * (RD * Q) * PF + LeN * RN) / (2 * (LeN * RN))

/-- `sig2'` at `2^pF`. -/
def sigI (LeN PF Q : ℤ) : ℤ := (2 * Q * PF + 8 * LeN) / (2 * (8 * LeN))

/-- `ρ'` at `2^pF`. -/
def rhoI (d LeN PF Q : ℤ) : ℤ := 1450 * d ^ 2 * LeN ^ 3 * PF / Q ^ 3

/-- `κ_c'` at `2^pF`. -/
def kapI (EN LN PF : ℤ) : ℤ := (2 * (EN * LN) * PF + 4 * (PF - LN) ^ 2) / (2 * (4 * (PF - LN) ^ 2))

/-- `ν'` at `2^pF`. -/
def nuI (LN PF : ℤ) : ℤ := (2 * PF * PF + (PF - LN)) / (2 * (PF - LN))

/-- `R'` at `2^pF`. -/
def RI (d RS PF Q : ℤ) : ℤ := (134 * d * RS * PF + Q - 1) / Q

/-- `s'_b` at `2^pF`. -/
def sbI (Ne RNp PF : ℤ) : ℤ := PF ^ 3 / (Ne ^ 2 * RNp * (RNp + PF))

/-- `W'` at `2^pF`. -/
def WI (d RNp SW PF Q : ℤ) : ℤ := (RNp * Q + 4 * d * SW * PF + Q - 1) / Q

/-- `A_0` at `2^p`. -/
def A0I (S1 P Q : ℤ) : ℤ := (2 * S1 * P + Q) / (2 * Q)

/-- `B_0` at `2^p`. -/
def B0I (S1 P Q : ℤ) : ℤ := (2 * Q * P + S1) / (2 * S1)

/-- `R_int = ⌈R'⌉`. -/
def rintI (RNp PF : ℤ) : ℤ := (RNp + PF - 1) / PF

/-- `LOGINT` on the integers: `lnQ q N = loI q N / 2^q` (with `Λ = merc(q, 2^(q-1), q)`). -/
def loI (q N : ℕ) : ℤ :=
  (N.size : ℤ) * gsm_mercq q (2 ^ (q - 1)) q -
    max ((gsm_mercq q (2 ^ (q - 1)) q : ℤ) - gsm_mercq q ((N - 2 ^ (N.size - 1)) * 2 ^ q / N) q) 0

theorem size_eq_clog (N : ℕ) : N.size = Nat.clog 2 (N + 1) := by
  apply le_antisymm
  · exact Nat.size_le.2 (Nat.lt_of_succ_le (Nat.le_pow_clog (by norm_num) _))
  · exact Nat.clog_le_of_le_pow (Nat.lt_size_self N)

/-! ## The values -/

/-- The inputs of PARAM: `d` in slot `0`, `n` in slot `3`. -/
def parI (d n : ℕ) : ℕ → ℤ := fun y => if y = 0 then d else if y = 3 then n else 0

/-- The value of step `k` of PARAM on `d`, `n`. -/
abbrev pv (d n : ℕ) (k : ℕ) : ℤ := SL.val parSt 30 (parI d n) k

theorem pv_c (d n k : ℕ) :
    pv d n k = (parSt.getD k (.cst 0)).sem 30 (parI d n) (fun j => if j < k then pv d n j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of PARAM unfolded: the step, its expression, the reads of the slots. -/
macro "pvs" : tactic => `(tactic| (rw [pv_c]; simp only [parSt, List.getD_cons_succ, List.getD_cons_zero, SStep.sem,
  slZ, rv, dI, nI, iM, iA, iS, iD, parI, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]))

section Values

variable (d n : ℕ)

theorem pv_0 : pv d n 0 = 1 := by pvs
theorem pv_1 : pv d n 1 = 2 := by pvs
theorem pv_2 : pv d n 2 = 4 := by pvs
theorem pv_3 : pv d n 3 = 8 := by pvs
theorem pv_4 : pv d n 4 = 10 := by pvs
theorem pv_5 : pv d n 5 = 16 := by pvs
theorem pv_6 : pv d n 6 = 24 := by pvs
theorem pv_7 : pv d n 7 = 40 := by pvs
theorem pv_8 : pv d n 8 = 160 := by pvs
theorem pv_9 : pv d n 9 = 3 := by pvs
theorem pv_10 : pv d n 10 = 6 := by pvs
theorem pv_11 : pv d n 11 = 64 := by pvs
theorem pv_12 : pv d n 12 = 36 := by pvs
theorem pv_13 : pv d n 13 = 725 := by pvs
theorem pv_14 : pv d n 14 = 1450 := by pvs
theorem pv_15 : pv d n 15 = 14500 := by pvs
theorem pv_16 : pv d n 16 = 134 := by pvs
theorem pv_17 : pv d n 17 = 1966080 := by pvs

theorem pv_18 : pv d n 18 = (BLP.Ne d n : ℤ) := by
  pvs; rw [pv_17]; unfold BLP.Ne; push_cast; ring

theorem pv_19 : pv d n 19 = ((BLP.Ne d n + 1 : ℕ) : ℤ) := by
  pvs; rw [pv_18, pv_0]; push_cast; ring

theorem pv_20 : pv d n 20 = ((BLP.Ne d n).size : ℤ) := by
  pvs; rw [pv_19, Int.toNat_natCast, ← size_eq_clog]

theorem pv_21 : pv d n 21 = ((d + 1 : ℕ) : ℤ) := by
  pvs; rw [pv_0]; push_cast; ring

theorem pv_22 : pv d n 22 = (d.size : ℤ) := by
  pvs; rw [pv_21, Int.toNat_natCast, ← size_eq_clog]

theorem pv_23 : pv d n 23 = ((par d n).p : ℤ) := by
  pvs; rw [pv_4, pv_20, pv_5, pv_22, pv_8]; simp only [par]; push_cast; ring

theorem pv_24 : pv d n 24 = (((BLP.Ne d n).size + 1 : ℕ) : ℤ) := by
  pvs; rw [pv_20, pv_0]; push_cast; ring

theorem pv_25 : pv d n 25 = ((BLP.Ne d n).size.size : ℤ) := by
  pvs; rw [pv_24, Int.toNat_natCast, ← size_eq_clog]

theorem pv_26 : pv d n 26 = ((par d n).q : ℤ) := by
  pvs; rw [pv_23, pv_1, pv_25, pv_6]; simp only [par]; push_cast; ring

theorem pv_27 : pv d n 27 = ((par d n).pF : ℤ) := by
  pvs; rw [pv_23, pv_1, pv_20, pv_2, pv_22, pv_7]; simp only [par]; push_cast; ring

theorem pv_28 : pv d n 28 = ((n * (d + 2) + 1 : ℕ) : ℤ) := by
  pvs; rw [pv_21, pv_0]; push_cast; ring

theorem pv_29 : pv d n 29 = ((n * (d + 2)).size : ℤ) := by
  pvs; rw [pv_28, Int.toNat_natCast, ← size_eq_clog]

theorem pv_30 : pv d n 30 = ((par d n).B : ℤ) := by
  pvs; rw [pv_1, pv_23, pv_29]; simp only [par]; push_cast; ring

theorem pv_31 : pv d n 31 = (((par d n).B + 1 : ℕ) : ℤ) := by
  pvs; rw [pv_30, pv_0]; push_cast; ring

theorem pv_32 : pv d n 32 = ((par d n).B.size : ℤ) := by
  pvs; rw [pv_31, Int.toNat_natCast, ← size_eq_clog]

theorem pv_33 : pv d n 33 = ((2 * gsm_prec (par d n).B : ℕ) : ℤ) := by
  pvs; rw [pv_1, pv_30, pv_32, pv_2]; unfold gsm_prec; push_cast; ring

theorem pv_34 : pv d n 34 = 2 ^ (2 * gsm_prec (par d n).B) := by
  pvs; rw [pv_33, Int.toNat_natCast]

theorem pv_35 : pv d n 35 = 2 ^ (par d n).p := by
  pvs; rw [pv_23, Int.toNat_natCast]

theorem pv_36 : pv d n 36 = 2 ^ (par d n).pF := by
  pvs; rw [pv_27, Int.toNat_natCast]

theorem pv_37 : pv d n 37 = 2 ^ (par d n).q := by
  pvs; rw [pv_26, Int.toNat_natCast]

theorem toNat_two_pow (m : ℕ) : ((2 : ℤ) ^ m).toNat = 2 ^ m := by
  rw [show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

theorem four_pow (q : ℕ) : (4 : ℕ) ^ q = 2 ^ q * 2 ^ q := by rw [← mul_pow]; norm_num

theorem p_ge (d n : ℕ) : 3 * (BLP.Ne d n).size + 6 * d.size + 64 ≤ (par d n).p := by simp only [par]; omega

theorem q_ge (d n : ℕ) : 24 ≤ (par d n).q := by simp only [par]; omega

theorem pv_38 : pv d n 38 = (((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64 : ℕ) : ℤ) := by
  pvs; rw [pv_23, pv_9, pv_20, pv_10, pv_22, pv_11]; have := p_ge d n; omega

theorem pv_39 : pv d n 39 = 2 ^ ((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64) := by
  pvs; rw [pv_38, Int.toNat_natCast]

theorem pv_40 : pv d n 40 = ((d * BLP.Ne d n : ℕ) : ℤ) := by
  pvs; rw [pv_18]; push_cast; ring

theorem pv_41 : pv d n 41 = ((d * 4 ^ (par d n).q : ℕ) : ℤ) := by
  pvs; rw [pv_37, four_pow]; push_cast; ring

theorem pv_42 : pv d n 42 = (Nat.sqrt (d * 4 ^ (par d n).q) : ℤ) := by
  pvs; rw [pv_41, Int.toNat_natCast]

theorem pv_43 : pv d n 43 = ((n * 4 ^ (par d n).q : ℕ) : ℤ) := by
  pvs; rw [pv_37, four_pow]; push_cast; ring

theorem pv_44 : pv d n 44 = (Nat.sqrt (n * 4 ^ (par d n).q) : ℤ) := by
  pvs; rw [pv_43, Int.toNat_natCast]

theorem pv_45 : pv d n 45 = (((par d n).q - 1 : ℕ) : ℤ) := by
  pvs; rw [pv_26, pv_0]; have := q_ge d n; omega

theorem pv_46 : pv d n 46 = 2 ^ ((par d n).q - 1) := by
  pvs; rw [pv_45, Int.toNat_natCast]

theorem pv_47 : pv d n 47 = (gsm_mercq (par d n).q (2 ^ ((par d n).q - 1)) (par d n).q : ℤ) := by
  pvs; rw [pv_26, pv_46, Int.toNat_natCast, toNat_two_pow]

end Values

/-! ## The logarithms -/

/-- `2^(size N - 1) ≤ N` for `N ≥ 1`. -/
theorem Ne_pos {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ BLP.Ne d n := by
  unfold BLP.Ne
  have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h4 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
  nlinarith

theorem pow_size_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ (N.size - 1) ≤ N :=
  Nat.lt_size.1 (by have := Nat.size_pos.2 hN; omega)

section Logs

variable {d n : ℕ}

theorem pv_48 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 48 = (((BLP.Ne d n).size - 1 : ℕ) : ℤ) := by
  have : 1 ≤ (BLP.Ne d n).size := Nat.size_pos.2 (Ne_pos hd hn)
  pvs; rw [pv_20, pv_0]; omega

theorem pv_49 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 49 = 2 ^ ((BLP.Ne d n).size - 1) := by
  pvs; rw [pv_48 hd hn, Int.toNat_natCast]

/-- `X_N = (N - 2^(size N - 1)) 2^q / N`. -/
def xN (q N : ℕ) : ℕ := (N - 2 ^ (N.size - 1)) * 2 ^ q / N

theorem pv_50 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 50 = (xN (par d n).q (BLP.Ne d n) : ℤ) := by
  have h1 : 1 ≤ BLP.Ne d n := Ne_pos hd hn
  have h2 := pow_size_le h1
  pvs; rw [pv_18, pv_49 hd hn, pv_37, xN]; push_cast [Nat.cast_sub h2]; ring_nf

theorem pv_51 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pv d n 51 = (gsm_mercq (par d n).q (xN (par d n).q (BLP.Ne d n)) (par d n).q : ℤ) := by
  pvs; rw [pv_26, pv_50 hd hn, Int.toNat_natCast, Int.toNat_natCast]

/-- `L0 = lnQ q N_e` at `2^q`. -/
def L0N (d n : ℕ) : ℤ := loI (par d n).q (BLP.Ne d n)

theorem pv_54 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 54 = L0N d n := by
  have e52 : pv d n 52 = pv d n 47 - pv d n 51 := by pvs
  have e53 : pv d n 53 = max (pv d n 52) 0 := by pvs
  pvs; rw [e53, e52, pv_20, pv_47, pv_51 hd hn, L0N, loI, xN]

theorem pv_55 : pv d n 55 = ((2 * d + 2 : ℕ) : ℤ) := by
  pvs; rw [pv_1]; push_cast; ring

theorem pv_56 : pv d n 56 = ((2 * d + 2 + 1 : ℕ) : ℤ) := by pvs; rw [pv_55, pv_0]; push_cast; ring

theorem pv_57 : pv d n 57 = ((2 * d + 2).size : ℤ) := by
  pvs; rw [pv_56, Int.toNat_natCast, ← size_eq_clog]

theorem pv_58 : pv d n 58 = (((2 * d + 2).size - 1 : ℕ) : ℤ) := by
  have : 1 ≤ (2 * d + 2).size := Nat.size_pos.2 (by omega)
  pvs; rw [pv_57, pv_0]; omega

theorem pv_59 : pv d n 59 = 2 ^ ((2 * d + 2).size - 1) := by
  pvs; rw [pv_58, Int.toNat_natCast]

theorem pv_60 : pv d n 60 = (xN (par d n).q (2 * d + 2) : ℤ) := by
  have h2 := pow_size_le (N := 2 * d + 2) (by omega)
  pvs; rw [pv_55, pv_59, pv_37, xN]; push_cast [Nat.cast_sub h2]; ring_nf

/-- `lnQ q (2d + 2)` at `2^q`. -/
def L1N (d n : ℕ) : ℤ := loI (par d n).q (2 * d + 2)

theorem pv_64 : pv d n 64 = L1N d n := by
  have e61 : pv d n 61 = (gsm_mercq (par d n).q (xN (par d n).q (2 * d + 2)) (par d n).q : ℤ) := by
    pvs; rw [pv_26, pv_60, Int.toNat_natCast, Int.toNat_natCast]
  have e62 : pv d n 62 = pv d n 47 - pv d n 61 := by pvs
  have e63 : pv d n 63 = max (pv d n 62) 0 := by pvs
  pvs; rw [e63, e62, pv_57, pv_47, e61, L1N, loI, xN]

/-- `lnErr q N_e` at `2^q`. -/
def EN (d n : ℕ) : ℤ := ((2 * (BLP.Ne d n).size * (4 * (par d n).q + 1) : ℕ) : ℤ)

/-- `lnErr q (2d + 2)` at `2^q`. -/
def E1N (d n : ℕ) : ℤ := ((2 * (2 * d + 2).size * (4 * (par d n).q + 1) : ℕ) : ℤ)

theorem pv_65 : pv d n 65 = EN d n := by
  pvs; rw [pv_1, pv_20, pv_2, pv_26, pv_0, EN]; push_cast; ring

theorem pv_66 : pv d n 66 = E1N d n := by
  pvs; rw [pv_1, pv_57, pv_2, pv_26, pv_0, E1N]; push_cast; ring

/-- `Le` at `2^q`. -/
def LeN (d n : ℕ) : ℤ := 36 * (L0N d n - EN d n)

/-- `36 (L0 + η_e)` at `2^q`. -/
def LhN (d n : ℕ) : ℤ := 36 * (L0N d n + EN d n)

theorem pv_67 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 67 = LeN d n := by
  pvs; rw [pv_12, pv_54 hd hn, pv_65, LeN]

theorem pv_68 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 68 = LhN d n := by
  pvs; rw [pv_12, pv_54 hd hn, pv_65, LhN]

end Logs

/-! ## The fields -/

/-- `2^q` on the integers. -/
def QZ (d n : ℕ) : ℤ := 2 ^ (par d n).q
/-- `2^pF` on the integers. -/
def PFZ (d n : ℕ) : ℤ := 2 ^ (par d n).pF
/-- `2^p` on the integers. -/
def PZ (d n : ℕ) : ℤ := 2 ^ (par d n).p
/-- `RD = ⌊√(d 4^q)⌋`. -/
def RDZ (d n : ℕ) : ℤ := Nat.sqrt (d * 4 ^ (par d n).q)
/-- `RN = ⌊√(n 4^q)⌋`. -/
def RNZ (d n : ℕ) : ℤ := Nat.sqrt (n * 4 ^ (par d n).q)
/-- `ε'` at `2^pF`. -/
def epsZ (d n : ℕ) : ℤ := epsI d (RDZ d n) (RNZ d n) (LhN d n) (PFZ d n) (QZ d n)
/-- `λ'` at `2^pF`. -/
def lamZ (d n : ℕ) : ℤ := lamI d (LeN d n) (PFZ d n) (QZ d n)
/-- `η'` at `2^pF`. -/
def etaZ (d n : ℕ) : ℤ := etaI (RDZ d n) (RNZ d n) (LeN d n) (PFZ d n) (QZ d n)
/-- `sig2'` at `2^pF`. -/
def sigZ (d n : ℕ) : ℤ := sigI (LeN d n) (PFZ d n) (QZ d n)
/-- `ρ'` at `2^pF`. -/
def rhoZ (d n : ℕ) : ℤ := rhoI d (LeN d n) (PFZ d n) (QZ d n)
/-- `κ_c'` at `2^pF`. -/
def kapZ (d n : ℕ) : ℤ := kapI (etaZ d n) (lamZ d n) (PFZ d n)
/-- `ν'` at `2^pF`. -/
def nuZ (d n : ℕ) : ℤ := nuI (lamZ d n) (PFZ d n)
/-- `2^q sqrtUp q (L1 + η_1)`. -/
def RSZ (d n : ℕ) : ℤ := (Nat.sqrt ((L1N d n + E1N d n) * QZ d n).toNat : ℤ) + 1
/-- `R'` at `2^pF`. -/
def RZ (d n : ℕ) : ℤ := RI d (RSZ d n) (PFZ d n) (QZ d n)
/-- `s'_b` at `2^pF`. -/
def sbZ (d n : ℕ) : ℤ := sbI (BLP.Ne d n) (RZ d n) (PFZ d n)
/-- `2^q sqrtUp q (N_e / Le')`. -/
def SWZ (d n : ℕ) : ℤ :=
  (Nat.sqrt (((BLP.Ne d n : ℤ) * QZ d n ^ 3 + LeN d n - 1) / LeN d n).toNat : ℤ) + 1
/-- `W'` at `2^pF`. -/
def WZ (d n : ℕ) : ℤ := WI d (RZ d n) (SWZ d n) (PFZ d n) (QZ d n)
/-- `2^q sqrtUp q sig2'`. -/
def S1Z (d n : ℕ) : ℤ := (Nat.sqrt ((sigZ d n * QZ d n ^ 2 + PFZ d n - 1) / PFZ d n).toNat : ℤ) + 1
/-- `A_0` at `2^p`. -/
def A0Z (d n : ℕ) : ℤ := A0I (S1Z d n) (PZ d n) (QZ d n)
/-- `B_0` at `2^p`. -/
def B0Z (d n : ℕ) : ℤ := B0I (S1Z d n) (PZ d n) (QZ d n)
/-- `R_int`. -/
def RintZ (d n : ℕ) : ℤ := rintI (RZ d n) (PFZ d n)

section Fields

variable {d n : ℕ}

theorem pv_35z : pv d n 35 = PZ d n := pv_35 d n
theorem pv_36z : pv d n 36 = PFZ d n := pv_36 d n
theorem pv_37z : pv d n 37 = QZ d n := pv_37 d n
theorem pv_42z : pv d n 42 = RDZ d n := pv_42 d n
theorem pv_44z : pv d n 44 = RNZ d n := pv_44 d n

theorem pv_69 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 69 = epsZ d n := by
  rw [pv_c]; simp only [parSt, List.getD_cons_succ, List.getD_cons_zero, SStep.sem, ieEps, slZ, parI,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceIte]
  rw [pv_42z, pv_44z, pv_68 hd hn, pv_36z, pv_37z, pv_15, pv_0, epsZ, epsI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pv_70 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 70 = lamZ d n := by
  pvs; rw [pv_1, pv_37z, pv_36z, pv_13, pv_67 hd hn, lamZ, lamI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pv_71 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 71 = etaZ d n := by
  pvs; rw [pv_1, pv_42z, pv_37z, pv_36z, pv_67 hd hn, pv_44z, etaZ, etaI]

theorem pv_72 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 72 = sigZ d n := by
  pvs; rw [pv_1, pv_37z, pv_36z, pv_3, pv_67 hd hn, sigZ, sigI]

theorem pv_73 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 73 = rhoZ d n := by
  pvs; rw [pv_14, pv_67 hd hn, pv_36z, pv_37z, rhoZ, rhoI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pv_74 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 74 = kapZ d n := by
  pvs; rw [pv_1, pv_71 hd hn, pv_70 hd hn, pv_36z, pv_2, kapZ, kapI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pv_75 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 75 = nuZ d n := by
  pvs; rw [pv_1, pv_36z, pv_70 hd hn, nuZ, nuI]

theorem pv_76 : pv d n 76 = L1N d n + E1N d n := by pvs; rw [pv_64, pv_66]

theorem pv_77 : pv d n 77 = (L1N d n + E1N d n) * QZ d n := by pvs; rw [pv_76, pv_37z]

theorem pv_78 : pv d n 78 = (Nat.sqrt ((L1N d n + E1N d n) * QZ d n).toNat : ℤ) := by pvs; rw [pv_77]

theorem pv_79 : pv d n 79 = RSZ d n := by
  pvs; rw [pv_78, pv_0, RSZ]

theorem pv_80 : pv d n 80 = RZ d n := by
  pvs; rw [pv_16, pv_79, pv_36z, pv_37z, pv_0, RZ, RI]

theorem pv_81 : pv d n 81 = sbZ d n := by
  pvs; rw [pv_36z, pv_18, pv_80, sbZ, sbI]
  exact congrArg₂ (· / ·) (by ring) (by ring)

theorem pv_82 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pv d n 82 = ((BLP.Ne d n : ℤ) * QZ d n ^ 3 + LeN d n - 1) / LeN d n := by
  pvs; rw [pv_18, pv_37z, pv_67 hd hn, pv_0]; ring_nf

theorem pv_83 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pv d n 83 = (Nat.sqrt (((BLP.Ne d n : ℤ) * QZ d n ^ 3 + LeN d n - 1) / LeN d n).toNat : ℤ) := by
  pvs; rw [pv_82 hd hn]

theorem pv_84 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 84 = SWZ d n := by
  pvs; rw [pv_83 hd hn, pv_0, SWZ]

theorem pv_85 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 85 = WZ d n := by
  pvs; rw [pv_80, pv_37z, pv_2, pv_84 hd hn, pv_36z, pv_0, WZ, WI]

theorem pv_86 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 86 = (sigZ d n * QZ d n ^ 2 + PFZ d n - 1) / PFZ d n := by
  pvs; rw [pv_72 hd hn, pv_37z, pv_36z, pv_0]; ring_nf

theorem pv_87 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    pv d n 87 = (Nat.sqrt ((sigZ d n * QZ d n ^ 2 + PFZ d n - 1) / PFZ d n).toNat : ℤ) := by
  pvs; rw [pv_86 hd hn]

theorem pv_88 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 88 = S1Z d n := by
  pvs; rw [pv_87 hd hn, pv_0, S1Z]

theorem pv_89 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 89 = A0Z d n := by
  pvs; rw [pv_1, pv_88 hd hn, pv_35z, pv_37z, A0Z, A0I]

theorem pv_90 (hd : 1 ≤ d) (hn : 1 ≤ n) : pv d n 90 = B0Z d n := by
  pvs; rw [pv_1, pv_37z, pv_35z, pv_88 hd hn, B0Z, B0I]

theorem pv_91 : pv d n 91 = RintZ d n := by
  pvs; rw [pv_80, pv_36z, pv_0, RintZ, rintI]

theorem pv_92 : pv d n 92 = (Sched.nBlk d : ℤ) := by
  pvs; rw [pv_21, pv_1, pv_0, Sched.nBlk]; push_cast; ring_nf

end Fields

end AdversarialBco.Bit.Transfer.BLM
