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

/-- One step of PARAM unfolded: the step, its expression, the reads of the slots. -/
macro "pvs" : tactic => `(tactic| (rw [pv_c]; simp only [parSt, List.getD_cons_succ, List.getD_cons_zero, SStep.sem,
  slZ, rv, dI, nI, iM, iA, iS, iD, parI, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]))

section Values

variable (d n : ℕ)


theorem toNat_two_pow (m : ℕ) : ((2 : ℤ) ^ m).toNat = 2 ^ m := by
  rw [show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

theorem four_pow (q : ℕ) : (4 : ℕ) ^ q = 2 ^ q * 2 ^ q := by rw [← mul_pow]; norm_num

end Values

/-! ## The logarithms -/

theorem pow_size_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ (N.size - 1) ≤ N :=
  Nat.lt_size.1 (by have := Nat.size_pos.2 hN; omega)

section Logs

variable {d n : ℕ}

/-- `X_N = (N - 2^(size N - 1)) 2^q / N`. -/
def xN (q N : ℕ) : ℕ := (N - 2 ^ (N.size - 1)) * 2 ^ q / N

end Logs

end AdversarialBco.Bit.Transfer.BLM
