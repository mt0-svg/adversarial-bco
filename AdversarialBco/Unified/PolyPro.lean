/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolySetup
public import AdversarialBco.Unified.PolyStep
public import AdversarialBco.Unified.PolyLP
public import AdversarialBco.Unified.PolyInst
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# UNI-POLY, part 15: the prologue of the compiled program, and the relation at its end

`proPr = prologue ++ xtr LP 6 ++ rtr SETUP oS`: the language prologue and `LP` compute the frame centre
(`lp_run`, PolyLP.lean), `SETUP` writes `P`'s input into `P`'s cells (`rs_SETUP`).

* `hdr_inputU`: the cells `SETUP` writes are `P`'s input `inputU d n (1/(n+1)) (1/2) n (frameQ ..)`.
* `pro_run`: the compiled program reaches a state related to `P`'s initial state `s0U`, whose cells above `-N0`
  satisfy `FixOK`, within the cost `CpL + Cset`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd Unified
open Bit.Transfer
open AdversarialBco.Bit.Asm (InputOK)
open AdversarialBco.RealRAM (polytope HeightLE)
open AdversarialBco.Poly.Mach (Layout asz)

variable {d : ℕ}

/-! ## The prologue -/

/-- The register holding the address of the frame centre's array. -/
def rFv : ℤ := rg (LPL.rA 16)

theorem rFv_eq : rFv = -387 := by decide

/-- The address of `SETUP`. -/
def oS : ℕ := 6 + xtlen LP

/-- The prologue of the compiled program. -/
def proPr : List Instr := prologue ++ xtr LP 6 ++ rtr (SETUPf rFv) oS

/-- The address of the buffer `Y`. -/
def YBv (d m : ℕ) : ℕ := offOf d m + LPL.base d aY

/-- The bit length bound of `SETUP`. -/
def Lset (d n m M : ℕ) : ℕ := Spl d m M + n.size + 2 + (offOf d m + LPL.base d 16 + d * d + 4 * d + 2000)

/-- The cost bound of `SETUP`. -/
def Cset (d n m M : ℕ) : ℕ := (50 + d * (8 * (2 * Spl d m M + 1) + 22)) * U d (Lset d n m M)

theorem prologue_length : prologue.length = 6 := rfl

theorem proPr_length : proPr.length = oS + rlen (SETUPf rFv) := by
  simp only [proPr, List.length_append, prologue_length, length_xtr, length_rtr, oS]

theorem codeAt_prefix (l₁ l₂ : List Instr) : B.CodeAt (l₁ ++ l₂) 0 l₁ := fun i hi => by
  rw [Nat.zero_add, List.getElem?_append_left hi]

/-! ## `P`'s input -/

/-- The numerators of the frame centre, indexed by `ℕ`. -/
def xOf (x : Fin d → ℤ) (j : ℕ) : ℤ := if h : j < d then x ⟨j, h⟩ else 0

theorem xOf_lt (x : Fin d → ℤ) {j : ℕ} (h : j < d) : xOf x j = x ⟨j, h⟩ := dite_eq_left h

theorem nd_of {p q : ℤ} (hq : 0 < q) (hc : Nat.Coprime p.natAbs q.natAbs) :
    ((p : ℚ) / q).num = p ∧ ((((p : ℚ) / q).den : ℤ) = q) :=
  ⟨Rat.num_div_eq_of_coprime hq hc, Rat.den_div_eq_of_coprime hq hc⟩

/-- `x / D` in lowest terms is `(x / g) / (D / g)`, `g = gcd(x, D)`. -/
theorem num_den_div {xv D : ℤ} (hD : 0 < D) :
    ((xv : ℚ) / D).num = xv / (Int.gcd xv D : ℤ) ∧ ((((xv : ℚ) / D).den : ℤ) = D / (Int.gcd xv D : ℤ)) := by
  have hg : 0 < Int.gcd xv D := Int.gcd_pos_of_ne_zero_right xv hD.ne'
  have hg0 : (0 : ℤ) < (Int.gcd xv D : ℤ) := by exact_mod_cast hg
  have hgx : (Int.gcd xv D : ℤ) ∣ xv := Int.gcd_dvd_left xv D
  have hgD : (Int.gcd xv D : ℤ) ∣ D := Int.gcd_dvd_right xv D
  have hpos : 0 < D / (Int.gcd xv D : ℤ) := Int.ediv_pos_of_pos_of_dvd hD hg0.le hgD
  have hne : ((Int.gcd xv D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hq : (xv : ℚ) / D = ((xv / (Int.gcd xv D : ℤ) : ℤ) : ℚ) / ((D / (Int.gcd xv D : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_div hgx hne, Int.cast_div hgD hne, div_div_div_cancel_right₀ hne]
  have hcop : Nat.Coprime (xv / (Int.gcd xv D : ℤ)).natAbs (D / (Int.gcd xv D : ℤ)).natAbs :=
    Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right hD.ne'
  rw [hq]
  exact nd_of hpos hcop

theorem δK_nd (n : ℕ) : (δK n).num = 1 ∧ ((δK n).den : ℤ) = n + 1 := by
  have h := nd_of (p := 1) (q := (n : ℤ) + 1) (by omega) (by simp)
  push_cast at h
  exact h

theorem half_nd : (1 / 2 : ℚ).num = 1 ∧ ((1 / 2 : ℚ).den : ℤ) = 2 := by
  have h := nd_of (p := 1) (q := 2) (by norm_num) (by decide)
  push_cast at h
  exact h

/-- The cells `SETUP` writes are `P`'s input. -/
theorem hdr_inputU {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {D : ℤ} {x : Fin d → ℤ} (hD0 : 0 < D)
    (hq : ∀ j : Fin d, (x j : ℚ) / D = Bit.RQ.frameQ d n m A b j) (y : ℤ) :
    hdr d n (xOf x) D y = inputU d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b) y := by
  obtain ⟨e1, e2⟩ := δK_nd n
  obtain ⟨e3, e4⟩ := half_nd
  simp only [hdr, inputU]
  rw [e1, e2, e3, e4, Rat.num_natCast, Rat.den_natCast, Nat.cast_one]
  by_cases h8 : 8 ≤ y ∧ y < 8 + 2 * (d : ℤ)
  · have h8' : 8 ≤ y ∧ (y - 8).toNat / 2 < d := ⟨h8.1, by omega⟩
    have h0 : y ≠ 0 := by omega
    have h1 : y ≠ 1 := by omega
    have h2 : y ≠ 2 := by omega
    have h3 : y ≠ 3 := by omega
    have h4 : y ≠ 4 := by omega
    have h5 : y ≠ 5 := by omega
    have h6 : y ≠ 6 := by omega
    have h7 : y ≠ 7 := by omega
    rw [ite_eq_left h8, dite_eq_left h8']
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
    rw [← hq ⟨(y - 8).toNat / 2, h8'.2⟩]
    obtain ⟨n1, n2⟩ := num_den_div (xv := x ⟨(y - 8).toNat / 2, h8'.2⟩) hD0
    rw [n1, n2]
    have ek : ((y - 8) / 2).toNat = (y - 8).toNat / 2 := by omega
    unfold cv
    rw [ek, xOf_lt x h8'.2]
    by_cases hp : (y - 8) % 2 = 0
    · rw [ite_eq_left hp, ite_eq_left (show (y - 8).toNat % 2 = 0 by omega)]
    · rw [ite_eq_right hp, ite_eq_right (show ¬ (y - 8).toNat % 2 = 0 by omega)]
  · have h8' : ¬ (8 ≤ y ∧ (y - 8).toNat / 2 < d) := by omega
    rw [ite_eq_right h8, dite_eq_right h8']

/-! ## The run of the prologue -/

set_option maxHeartbeats 1000000 in
/-- **The prologue**: the compiled program reaches a state related to `P`'s initial state `s0U`, whose cells above
`-N0` satisfy `FixOK` with the buffer at `YBv d m`, within `CpL + Cset`. -/
theorem pro_run (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) (w : World d) :
    ∃ k0, Rel (Fa P proPr.length) (run (compP proPr P) w (initBit d n m A b) k0).mem (s0U d n m A b)
        (run (compP proPr P) w (initBit d n m A b) k0) ∧
      FixOK d m A b (YBv d m) (run (compP proPr P) w (initBit d n m A b) k0).mem ∧
      (run (compP proPr P) w (initBit d n m A b) k0).cost ≤ CpL d n m M + Cset d n m M := by
  have hd := hI.hd
  have hc0' : B.CodeAt (compP proPr P) 0 ((prologue ++ xtr LP 6) ++ rtr (SETUPf rFv) oS) :=
    codeAt_prefix proPr (compB (Fa P proPr.length) P proPr.length)
  obtain ⟨k, t1, D, x, s, e1, p1, c1, r1, cost1, low1, inp1, to1, rf1, -, hD0, hDs, hD1, hx1, hy1, hs1, pt1⟩ :=
    lp_run hI hc0'.append_left w
  have hcS : B.CodeAt (compP proPr P) oS (rtr (SETUPf rFv) oS) := by
    have h := hc0'.append_right
    have e : 0 + (prologue ++ xtr LP 6).length = oS := by
      simp only [List.length_append, prologue_length, length_xtr, oS, Nat.zero_add]
    rwa [e] at h
  have hoff3 : 3 ≤ offOf d m := by unfold offOf; omega
  have hN1 : ∀ c : ℕ, c < offOf d m → t1.mem (c : ℤ) = inputMem d n m A b c := inp1
  have h2L : ∀ z : ℕ, z ≤ Lset d n m M → (z : ℤ) < 2 ^ Lset d n m M := fun z hz => by
    have h : z < 2 ^ Lset d n m M := lt_of_le_of_lt hz Nat.lt_two_pow_self
    exact_mod_cast h
  have hnS : (n : ℤ) + 2 < 2 ^ Lset d n m M := by
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 2 ^ (n.size + 2) ≤ 2 ^ Lset d n m M := Nat.pow_le_pow_right (by norm_num) (by unfold Lset; omega)
    have h4 : 2 ^ (n.size + 2) = 2 ^ n.size * 4 := by rw [pow_add]; norm_num
    have : n + 2 < 2 ^ Lset d n m M := by omega
    exact_mod_cast this
  obtain ⟨n1, t', hX, hn1, hS, hYB, hhigh, hscr, hP⟩ := rs_SETUP (w := w) (L := Lset d n m M) (u := t1) (n := n)
    (off := offOf d m) (bF := LPL.base d 16) (D := D) (s := s) (x := xOf x) (rF := rFv)
    (by rw [rFv_eq]; norm_num) (by rw [rFv_eq]; norm_num)
    ((hN1 0 (by omega)).trans (Conj1BitSanity.inputMem_small (n := n) A b).1)
    ((hN1 1 (by omega)).trans (Conj1BitSanity.inputMem_small (n := n) A b).2.1)
    to1 rf1 hD1 hD0 hDs
    (fun j hj => by rw [xOf_lt x hj]; exact (hx1 ⟨j, hj⟩).2.1)
    (fun j hj => by rw [xOf_lt x hj]; exact (hx1 ⟨j, hj⟩).1)
    low1 (by unfold Lset; omega) hnS
    (by have := h2L (offOf d m + LPL.base d 16 + d + 2) (by unfold Lset; omega); exact_mod_cast this)
    (by have := h2L (offOf d m + d * d + d + 264) (by unfold Lset; omega); exact_mod_cast this)
    (by have := h2L (4 * d + 1020) (by unfold Lset; omega); exact_mod_cast this)
    (by unfold Lset; omega)
  have hrun := rtr_run hX oS hcS
  have ht1 : ({ t1 with pc := oS } : State d) = t1 := by
    have e : oS = t1.pc := p1.symm
    rw [e]
  rw [ht1] at hrun
  have hrunk : run (compP proPr P) w (initBit d n m A b) (k + n1) = { t' with pc := oS + rlen (SETUPf rFv) } := by
    rw [B.run_add, e1, hrun]
  have hN : ∀ c : ℕ, c < offOf d m → t'.mem (c : ℤ) = inputMem d n m A b c := fun c hc =>
    (hhigh c (by omega)).trans (hN1 c hc)
  have hYBs : ((YBv d m : ℕ) : ℤ) = (offOf d m : ℤ) + (LPL.base d aY : ℤ) := by simp only [YBv, Nat.cast_add]
  have hbY : ((LPL.base d aY : ℕ) : ℤ) = 264 + ((d : ℤ) * d + d) := by
    simp only [Layout.base, LPL, aY, asz]; push_cast; ring
  have hoffe : ((offOf d m : ℕ) : ℤ) = 3 + 2 * (((d : ℤ) + 1) * m) := by
    simp only [offOf]; push_cast; ring
  refine ⟨k + n1, ?_, ?_, ?_⟩
  · rw [hrunk]
    refine ⟨?_, fun y => ?_, fun c _ => rfl, ?_, ?_, ?_⟩
    · show oS + rlen (SETUPf rFv) = Fa P proPr.length 0
      rw [Fa_zero, proPr_length]
    · show t'.mem (φ y) = inputU d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b) y
      rw [hP y]
      exact hdr_inputU hD0 (fun j => (hx1 j).2.2) y
    · show t'.coins = 0
      rw [hS.1, c1]
    · show t'.rounds = 0
      rw [hS.2.1, r1]
    · show t'.pts = fun _ _ => 0
      rw [hS.2.2, pt1]
  · rw [hrunk]
    refine ⟨fun c hc => hscr c hc, ?_, ?_, fun c h1 h2 => ?_, ?_, ?_, fun i hi j hj => ?_⟩
    · show t'.mem cYB = ((YBv d m : ℕ) : ℤ)
      rw [hYB, hYBs, hbY]
      ring
    · show 3 + 2 * (((d : ℤ) + 1) * m) ≤ ((YBv d m : ℕ) : ℤ)
      rw [hYBs, hbY, hoffe]
      have : (0 : ℤ) ≤ (d : ℤ) * d + d := by positivity
      linarith
    · show t'.mem c = 0
      have hY0 : (0 : ℤ) ≤ ((YBv d m : ℕ) : ℤ) := Int.natCast_nonneg _
      rw [hhigh c (by omega)]
      have hda : d < asz d := by
        have := Nat.mul_le_mul hd hd
        unfold asz; omega
      have hk : (c - ((YBv d m : ℕ) : ℤ)).toNat < asz d := by omega
      have h := hy1 _ hk
      have ec : (offOf d m : ℤ) + (LPL.base d aY : ℤ) + (((c - ((YBv d m : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c := by
        omega
      rwa [ec] at h
    · show t'.mem (((0 : ℕ) : ℤ)) = d
      rw [hN 0 (by omega)]
      exact (Conj1BitSanity.inputMem_small (n := n) A b).1
    · show t'.mem (((2 : ℕ) : ℤ)) = m
      rw [hN 2 (by omega)]
      exact (Conj1BitSanity.inputMem_small (n := n) A b).2.2
    · have hlt : (d + 1) * i + j < (d + 1) * m := by
        have h1 := Nat.mul_le_mul_left (d + 1) (show i + 1 ≤ m from hi)
        have h2 : (d + 1) * (i + 1) = (d + 1) * i + d + 1 := by ring
        omega
      have e2 : 2 * (d + 1) * m = 2 * ((d + 1) * m) := by ring
      have hc1 : 3 + 2 * ((d + 1) * i + j) < offOf d m := by unfold offOf; omega
      have hc2 : 4 + 2 * ((d + 1) * i + j) < offOf d m := by unfold offOf; omega
      have c1e : (3 + 2 * (((d : ℤ) + 1) * i + j)) = ((3 + 2 * ((d + 1) * i + j) : ℕ) : ℤ) := by push_cast; ring
      have c2e : (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = ((4 + 2 * ((d + 1) * i + j) : ℕ) : ℤ) := by
        push_cast; ring
      refine ⟨?_, ?_⟩
      · show t'.mem (3 + 2 * (((d : ℤ) + 1) * i + j)) = _
        rw [c1e, hN _ hc1]
        exact Conj1BitSanity.inputMem_num (n := n) A b ⟨i, hi⟩ j hj
      · show t'.mem (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = _
        rw [c2e, hN _ hc2]
        exact Conj1BitSanity.inputMem_den (n := n) A b ⟨i, hi⟩ j hj
  · rw [hrunk]
    show t'.cost ≤ CpL d n m M + Cset d n m M
    have h1 := RX.cost_le hX
    have h2 : n1 ≤ 50 + d * (8 * (2 * Spl d m M + 1) + 22) := by
      have : d * (8 * (2 * s + 1) + 22) ≤ d * (8 * (2 * Spl d m M + 1) + 22) := Nat.mul_le_mul_left _ (by omega)
      omega
    have h3 : n1 * U d (Lset d n m M) ≤ Cset d n m M := Nat.mul_le_mul_right _ h2
    omega

end AdversarialBco.UniPoly
