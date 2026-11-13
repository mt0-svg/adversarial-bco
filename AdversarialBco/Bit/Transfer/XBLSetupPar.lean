/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR5
public import AdversarialBco.Bit.PieceA.Enc

@[expose] public section

/-!
# BL's setup on the machine, PARAM on the integers

Procedure PARAM (`par`, Bit/BLPure.lean) as the program computes it: every field of `BLInv` (its numerator `qn` at its
grid) is an integer formula in `d`, `2^q`, `2^pF`, `2^p`, the integer square roots `RD = ⌊√(d 4^q)⌋`,
`RN = ⌊√(n 4^q)⌋` and the integer logarithms `loI q N` (`lnQ q N = loI q N / 2^q`), with one Euclidean quotient each
(`rnd`, `up`, `dn` of a fraction `U/V`, `V > 0`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-! ## Rounding a fraction -/

theorem ceil_div_int (a b : ℤ) (hb : 0 < b) : ⌈(a : ℚ) / b⌉ = (a + b - 1) / b := by
  rw [Int.ceil_eq_iff]
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have h1 := Int.ediv_mul_le (a + b - 1) hb.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (a + b - 1) hb
  constructor
  · rw [lt_div_iff₀ hb']
    have : ((a + b - 1) / b - 1) * b < a := by nlinarith
    exact_mod_cast this
  · rw [div_le_iff₀ hb']
    have : a ≤ (a + b - 1) / b * b := by nlinarith
    exact_mod_cast this

theorem qn_up (k : ℕ) (x : ℚ) : qn k (up k x) = ⌈x * 2 ^ k⌉ := by
  unfold qn up
  rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

theorem qn_dn (k : ℕ) (x : ℚ) : qn k (dn k x) = ⌊x * 2 ^ k⌋ := by
  unfold qn dn
  rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

theorem qn_rnd (k : ℕ) (x : ℚ) : qn k (rnd k x) = ⌊x * 2 ^ k + 1 / 2⌋ := by
  unfold qn rnd
  rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

/-- `up_k (U/V)` on the integers: `⌈U 2^k / V⌉ = (U 2^k + V - 1)/V`. -/
theorem qn_up_div (k : ℕ) (U V : ℤ) (hV : 0 < V) : qn k (up k ((U : ℚ) / V)) = (U * 2 ^ k + V - 1) / V := by
  rw [qn_up, ← ceil_div_int _ _ hV]
  congr 1; push_cast; ring

/-- `dn_k (U/V)` on the integers: `⌊U 2^k / V⌋`. -/
theorem qn_dn_div (k : ℕ) (U V : ℤ) (hV : 0 < V) : qn k (dn k ((U : ℚ) / V)) = U * 2 ^ k / V := by
  rw [qn_dn, ← floor_div_int _ _ hV]
  congr 1; push_cast; ring

/-- `rnd_k (U/V)` on the integers: `⌊(2 U 2^k + V)/(2V)⌋`. -/
theorem qn_rnd_div (k : ℕ) (U V : ℤ) (hV : 0 < V) :
    qn k (rnd k ((U : ℚ) / V)) = (2 * U * 2 ^ k + V) / (2 * V) := by
  rw [rnd_div k U V hV, qn_div_pow]

/-! ## The square roots -/

theorem sqrtDn_nat (k N : ℕ) : sqrtDn k (N : ℚ) = (Nat.sqrt (N * 4 ^ k) : ℚ) / 2 ^ k := by
  unfold sqrtDn
  congr 3
  exact_mod_cast Nat.floor_natCast (N * 4 ^ k)

/-! ## The field `ε'` -/

/-- `qn pF ε'` as the program computes it: `Q = 2^q`, `PF = 2^pF`, `RD`, `RN` the integer roots, `LhN` the numerator
of `36 (L0 + η_e)` over `2^q`. -/
def epsI (d RD RN LhN PF Q : ℤ) : ℤ :=
  (14500 * d * (RD + 1) * LhN ^ 5 * PF + Q ^ 5 * RN - 1) / (Q ^ 5 * RN)

theorem qn_eps_gen (d n q pF : ℕ) (hn : 1 ≤ n) (LhN : ℤ) :
    qn pF (up pF (14500 * d * (sqrtDn q d + 1 / 2 ^ q) * ((LhN : ℚ) / 2 ^ q) ^ 5 / sqrtDn q n)) =
      epsI d (Nat.sqrt (d * 4 ^ q)) (Nat.sqrt (n * 4 ^ q)) LhN (2 ^ pF) (2 ^ q) := by
  have hRN : 1 ≤ Nat.sqrt (n * 4 ^ q) := by
    rw [Nat.le_sqrt]; have : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by norm_num); nlinarith
  have hV : (0 : ℤ) < 2 ^ q * 2 ^ q * 2 ^ q * 2 ^ q * 2 ^ q * (Nat.sqrt (n * 4 ^ q) : ℤ) := by positivity
  rw [sqrtDn_nat, sqrtDn_nat]
  have hx : 14500 * (d : ℚ) * ((Nat.sqrt (d * 4 ^ q) : ℚ) / 2 ^ q + 1 / 2 ^ q) * ((LhN : ℚ) / 2 ^ q) ^ 5 /
      ((Nat.sqrt (n * 4 ^ q) : ℚ) / 2 ^ q) =
      ((14500 * d * (Nat.sqrt (d * 4 ^ q) + 1) * LhN ^ 5 : ℤ) : ℚ) /
        ((2 ^ q * 2 ^ q * 2 ^ q * 2 ^ q * 2 ^ q * (Nat.sqrt (n * 4 ^ q) : ℤ) : ℤ) : ℚ) := by
    have h1 : ((Nat.sqrt (n * 4 ^ q) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : Nat.sqrt (n * 4 ^ q) ≠ 0)
    push_cast
    field_simp
  rw [hx, qn_up_div _ _ _ hV, epsI]
  congr 1 <;> ring

theorem qn_eps_eq (d n : ℕ) (hn : 1 ≤ n) (LhN : ℤ)
    (hLh : 36 * (PieceA.L0 d n + PieceA.ee d n) = (LhN : ℚ) / 2 ^ (par d n).q) :
    qn (par d n).pF (par d n).eps =
      epsI d (Nat.sqrt (d * 4 ^ (par d n).q)) (Nat.sqrt (n * 4 ^ (par d n).q)) LhN (2 ^ (par d n).pF)
        (2 ^ (par d n).q) := by
  rw [PieceA.par_eps, hLh]
  exact qn_eps_gen d n _ _ hn LhN


/-! ## The expression of `ε'` -/

/-- `epsI` over the slots `sD, sRD, sRN, sLh, sPF, sQ` (`d, RD, RN, LhN, 2^pF, 2^q`), `sC` holding `14500`, `s1`
holding `1`. -/
def ieEps (sD sRD sRN sLh sPF sQ sC s1 : ℕ) : IE :=
  let L2 : IE := .op .mul (.sc sLh) (.sc sLh)
  let U : IE := .op .mul (.op .mul (.op .mul (.op .mul (.sc sC) (.sc sD)) (.op .add (.sc sRD) (.sc s1)))
    (.op .mul (.op .mul L2 L2) (.sc sLh))) (.sc sPF)
  let Q2 : IE := .op .mul (.sc sQ) (.sc sQ)
  let V : IE := .op .mul (.op .mul (.op .mul Q2 Q2) (.sc sQ)) (.sc sRN)
  .ediv (.op .sub (.op .add U V) (.sc s1)) V

end AdversarialBco.Bit.Transfer.BLM
