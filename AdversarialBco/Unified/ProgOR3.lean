/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit
public import AdversarialBco.Bit.Transfer.XEllConst
public import AdversarialBco.Bit.Transfer.XIsqrt

@[expose] public section

/-!
# R3, BL-O's clipped reading

After the play of round `t`, R3 reads `clip qO ⌊2^p (f_t(x'_t) + noise_t)⌋` into `sObs` with the leaf `obsR`, the
precision `p` in the register `rP` and the range
`qO = p + clog₂(9 + 4 ⌊√(size(14 n N_e))⌋ + ⌊√(2B)⌋)` (`CfgO.qO`) computed in the round from the persistent cells
(`n` in `sN`, `N_e` in `sNe`, `B` in `rB`): `size m = clog₂(m + 1)` by `xclogS`, the roots by `xisqrt`, in the slots
`256, ..., 271` and the registers `8, 9, 10`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open AdversarialBco.Bit (gsm_prec)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The cells -/

abbrev q0 : ℕ := 256
abbrev q1 : ℕ := 257
abbrev q2 : ℕ := 258
abbrev q3 : ℕ := 259
abbrev q4 : ℕ := 260
abbrev q5 : ℕ := 261
abbrev q6 : ℕ := 262
abbrev q7 : ℕ := 263
abbrev q8 : ℕ := 264
abbrev q9 : ℕ := 265
abbrev q10 : ℕ := 266
abbrev q11 : ℕ := 267
abbrev q12 : ℕ := 268
abbrev q13 : ℕ := 269
abbrev q14 : ℕ := 270
abbrev q15 : ℕ := 271
abbrev rS1 : ℕ := 8
abbrev rS2 : ℕ := 9
abbrev rQO : ℕ := 10

/-- `size m = clog₂(m + 1)`. -/
theorem size_eq_clog (m : ℕ) : m.size = Nat.clog 2 (m + 1) := by
  apply le_antisymm
  · rw [Nat.size_le]
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (m + 1)
    omega
  · exact Nat.clog_le_of_le_pow (Nat.lt_size_self m)

/-! ## The range on the machine -/

/-- Part A: `q0 := 14 n N_e + 1`, `rS1 := clog₂ q0 = size(14 n N_e)`, `q3 := rS1`. -/
def xqA (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L q0 14)) <| .seq (toX (VL.sop2 L .mul q0 q0 sN)) <| .seq (toX (VL.sop2 L .mul q0 q0 sNe)) <|
  .seq (toX (VL.sconst L q1 1)) <| .seq (toX (VL.sop2 L .add q0 q0 q1)) <|
  .seq (xclogS L q2 q0 rS1 rOne) <| toX (VL.ncast L q3 rS1)

/-- Part B: the constants `0, 2, 4` and `q7 := ⌊√q3⌋`. -/
def xqB (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L q4 0)) <| .seq (toX (VL.sconst L q5 2)) <| .seq (toX (VL.sconst L q6 4)) <|
  xisqrt L q3 q7 q8 q9 q10 q4 q1 q5 q6

/-- Part C: `q11 := 2B`, `q12 := ⌊√q11⌋`. -/
def xqC (L : Layout) : XCmd :=
  .seq (toX (VL.ncast L q11 rB)) <| .seq (toX (VL.sop2 L .add q11 q11 q11)) <|
  xisqrt L q11 q12 q8 q9 q10 q4 q1 q5 q6

/-- Part D: `q13 := 9 + 4 q7 + q12`, `rS2 := clog₂ q13`, `rQO := p + rS2`. -/
def xqD (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L q13 9)) <| .seq (toX (VL.sop2 L .mul q14 q6 q7)) <|
  .seq (toX (VL.sop2 L .add q13 q13 q14)) <| .seq (toX (VL.sop2 L .add q13 q13 q12)) <|
  .seq (xclogS L q15 q13 rS2 rOne) <| .prim (.frag (.nadd rQO rP rS2))

/-- The computation of `qO` into the register `rQO`. -/
def xqO (L : Layout) : XCmd := .seq (xqA L) (.seq (xqB L) (.seq (xqC L) (xqD L)))
/-- What the computation keeps: the registers below `8`, the slots below `256`, the arrays, the coins, the rounds,
the points. -/
def TrQ (σ σ' : Env d) : Prop :=
  (∀ j < 8, σ'.nat j = σ.nat j) ∧ (∀ y < 256, σ'.sc y = σ.sc y) ∧ σ'.arr = σ.arr ∧ σ'.draws = σ.draws ∧
    σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts

namespace TrQ

variable {σ σ' σ'' : Env d}

theorem refl (σ : Env d) : TrQ σ σ := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans (h : TrQ σ σ') (h' : TrQ σ' σ'') : TrQ σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun y hy => (h'.2.1 y hy).trans (h.2.1 y hy),
    h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.1.trans h.2.2.2.2.1,
    h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

theorem setSc (h : TrQ σ σ') {y : ℕ} (hy : 256 ≤ y) (v : ℝ) : TrQ σ (σ'.setSc y v) :=
  ⟨h.1, fun z hz => by rw [Env.setSc_sc, ite_eq_right (by omega)]; exact h.2.1 z hz, h.2.2⟩

theorem setNat (h : TrQ σ σ') {j : ℕ} (hj : 8 ≤ j) (v : ℕ) : TrQ σ (σ'.setNat j v) :=
  ⟨fun i hi => by rw [Env.setNat_nat, ite_eq_right (by omega)]; exact h.1 i hi, h.2.1, h.2.2⟩

theorem ofEq (h : TrQ σ σ') (e : σ'' = σ') : TrQ σ σ'' := e ▸ h

theorem ofFrame {S : List ℕ} (h : TrQ σ σ') (hF : Frame S [] σ' σ'') (hS : ∀ y ∈ S, 256 ≤ y) : TrQ σ σ'' :=
  h.trans ⟨fun j _ => hF.1 j (by simp), fun y hy => hF.2.1 y (fun hm => by have := hS y hm; omega), hF.2.2.1,
    hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2⟩

theorem ofFrameP {w c : ℕ} (h : TrQ σ σ') (hF : FrameP (fun y => y = w) (fun j => j = c) σ' σ'')
    (hd : σ''.draws = σ'.draws) (hw : 256 ≤ w) (hc : 8 ≤ c) : TrQ σ σ'' :=
  h.trans ⟨fun j hj => hF.1 j (by omega), fun y hy => hF.2.1 y (by omega), hF.2.2.1, hd, hF.2.2.2.1, hF.2.2.2.2⟩

end TrQ

theorem pow_lt_of_le {a b : ℕ} (h : a < b) : (2 : ℝ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) h

theorem abs_lt_of_nat {v : ℕ} {G ℓ : ℕ} (hv : v ≤ 2 ^ G) (hG : G < ℓ) : |(v : ℝ)| < 2 ^ ℓ := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact lt_of_le_of_lt (by exact_mod_cast hv) (pow_lt_of_le hG)


theorem nat_abs_lt {v G ℓ : ℕ} (hv : v ≤ 2 ^ G) (hG : G < ℓ) : |((v : ℕ) : ℝ)| < 2 ^ ℓ := abs_lt_of_nat hv hG

theorem small_nat_lt {v ℓ : ℕ} (hv : v < ℓ) : |((v : ℕ) : ℝ)| < 2 ^ ℓ :=
  abs_lt_of_nat (G := v) Nat.lt_two_pow_self.le hv

/-- The constant `c` as a rational has the bound of a small natural. -/
theorem small_q_lt {c : ℕ} {ℓ : ℕ} (hv : c < ℓ) : |(((c : ℚ) : ℝ))| < 2 ^ ℓ := by
  rw [Rat.cast_natCast]; exact small_nat_lt hv

set_option maxHeartbeats 1000000 in
theorem XV.qA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {n Ne E : ℕ}
    (hNS : 272 ≤ L.NS) (hNN : 11 ≤ L.NN) (hn : σ.sc sN = n) (hNe : σ.sc sNe = Ne) (h1 : σ.nat rOne = 1)
    (hnE : n ≤ 2 ^ E) (hNeE : Ne ≤ 2 ^ E) (hℓ : 2 * E + 16 ≤ ℓ) (hℓa : 2 * E + 6 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xqA L) σ (1 + (1 + (1 + (1 + (1 + ((4 * (2 * E + 5) + 4) + 1))))))
      (fun σ' => σ'.sc q3 = (((14 * n * Ne).size : ℕ) : ℝ) ∧ σ'.sc q1 = 1 ∧ TrQ σ σ') := by
  have hS : ∀ {y : ℕ}, y < 272 → y < L.NS := fun h => by omega
  have hN : ∀ {j : ℕ}, j < 11 → j < L.NN := fun h => by omega
  have hnNe : n * Ne ≤ 2 ^ (2 * E) := by
    calc n * Ne ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hnE hNeE
      _ = 2 ^ (2 * E) := by rw [← pow_add]; ring_nf
  have h14 : 14 * n * Ne + 1 ≤ 2 ^ (2 * E + 5) := by
    have : 2 ^ (2 * E + 5) = 32 * 2 ^ (2 * E) := by rw [pow_add]; ring
    have := Nat.one_le_two_pow (n := 2 * E)
    nlinarith
  have h14n : 14 * n ≤ 2 ^ (2 * E + 5) := by
    calc 14 * n ≤ 16 * 2 ^ E := by omega
      _ = 2 ^ (E + 4) := by rw [pow_add]; ring
      _ ≤ 2 ^ (2 * E + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h14m : 14 * n * Ne ≤ 2 ^ (2 * E + 5) := by omega
  refine XV.seq (XV.sconst hL (x := q0) (hS (by decide)) 14 rfl (small_q_lt (c := 14) (by omega))) fun σ1 e1 => ?_
  have T1 : TrQ σ σ1 := ((TrQ.refl σ).setSc (by decide) _).ofEq e1
  have v1 : σ1.sc q0 = ((14 : ℕ) : ℝ) := by rw [e1]; simp
  have n1 : σ1.sc sN = n := by rw [T1.2.1 _ (by decide), hn]
  refine XV.seq (XV.sop2 hL (x := q0) (a := q0) (b := sN) (hS (by decide)) (hS (by decide)) (hS (by decide)) .mul
    (by intro h; cases h) (by rw [v1]; exact small_nat_lt (by omega)) (by rw [n1]; exact nat_abs_lt hnE (by omega))
    (by rw [v1, n1]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_mul]; exact nat_abs_lt h14n (by omega)))
    fun σ2 e2 => ?_
  have T2 : TrQ σ σ2 := (T1.setSc (by decide) _).ofEq e2
  have v2 : σ2.sc q0 = ((14 * n : ℕ) : ℝ) := by rw [e2]; simp [RealRAM.Op2.eval, v1, n1]
  have ne2 : σ2.sc sNe = Ne := by rw [T2.2.1 _ (by decide), hNe]
  refine XV.seq (XV.sop2 hL (x := q0) (a := q0) (b := sNe) (hS (by decide)) (hS (by decide)) (hS (by decide)) .mul
    (by intro h; cases h) (by rw [v2]; exact nat_abs_lt h14n (by omega)) (by rw [ne2]; exact nat_abs_lt hNeE (by omega))
    (by rw [v2, ne2]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_mul]; exact nat_abs_lt h14m (by omega)))
    fun σ3 e3 => ?_
  have T3 : TrQ σ σ3 := (T2.setSc (by decide) _).ofEq e3
  have v3 : σ3.sc q0 = ((14 * n * Ne : ℕ) : ℝ) := by rw [e3]; simp [RealRAM.Op2.eval, v2, ne2]
  refine XV.seq (XV.sconst hL (x := q1) (hS (by decide)) 1 rfl (small_q_lt (c := 1) (by omega))) fun σ4 e4 => ?_
  have T4 : TrQ σ σ4 := (T3.setSc (by decide) _).ofEq e4
  have v4 : σ4.sc q1 = 1 := by rw [e4]; simp
  have v4' : σ4.sc q0 = ((14 * n * Ne : ℕ) : ℝ) := by rw [e4]; simp [v3]
  refine XV.seq (XV.sop2 hL (x := q0) (a := q0) (b := q1) (hS (by decide)) (hS (by decide)) (hS (by decide)) .add
    (by intro h; cases h) (by rw [v4']; exact nat_abs_lt h14m (by omega))
    (by rw [v4]; simpa using small_nat_lt (v := 1) (by omega))
    (by rw [v4', v4]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_one, ← Nat.cast_add]; exact nat_abs_lt h14 (by omega)))
    fun σ5 e5 => ?_
  have T5 : TrQ σ σ5 := (T4.setSc (by decide) _).ofEq e5
  have v5 : σ5.sc q0 = (((14 * n * Ne + 1 : ℕ) : ℤ) : ℝ) := by rw [e5]; simp [RealRAM.Op2.eval, v4', v4]
  have v5' : σ5.sc q1 = 1 := by rw [e5]; simp [RealRAM.Op2.eval, v4]
  have o5 : σ5.nat rOne = 1 := by rw [T5.1 _ (by decide), h1]
  refine XV.seq (XV.clogS hL (w := q2) (x := q0) (c := rS1) (one := rOne) (G := 2 * E + 5) (hS (by decide))
    (hS (by decide)) (hN (by decide)) (hN (by decide)) (by decide) (by decide) v5 (by positivity)
    (by exact_mod_cast h14) o5 (by omega) (by omega)) fun σ6 ⟨c6, d6, F6⟩ => ?_
  have T6 : TrQ σ σ6 := T5.ofFrameP F6 d6 (by decide) (by decide)
  have s6 : σ6.nat rS1 = (14 * n * Ne).size := by rw [c6, size_eq_clog, Int.toNat_natCast]
  have w6 : σ6.sc q1 = 1 := by rw [F6.2.1 q1 (by decide), v5']
  have hsz : (14 * n * Ne).size ≤ 2 * E + 5 := by
    rw [Nat.size_le]; exact lt_of_lt_of_le (Nat.lt_succ_self _) h14
  refine XV.mono (XV.ncastI hL (x := q3) (i := rS1) (hS (by decide)) (hN (by decide)) (by rw [s6]; omega)) le_rfl
    fun σ7 e7 => ?_
  exact ⟨by rw [e7]; simp [s6], by rw [e7]; simp [w6], (T6.setSc (by decide) _).ofEq e7⟩

set_option maxHeartbeats 1000000 in
theorem XV.qB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {m : ℕ}
    (hNS : 272 ≤ L.NS) (hm : σ.sc q3 = (m : ℝ)) (h1 : σ.sc q1 = 1) (hℓ : 4 * m + 8 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xqB L) σ (1 + (1 + (1 + (12 * m.size + 8))))
      (fun σ' => σ'.sc q7 = (Nat.sqrt m : ℝ) ∧ σ'.sc q4 = 0 ∧ σ'.sc q1 = 1 ∧ σ'.sc q5 = 2 ∧ σ'.sc q6 = 4 ∧
        TrQ σ σ') := by
  have hS : ∀ {y : ℕ}, y < 272 → y < L.NS := fun h => by omega
  refine XV.seq (XV.sconst hL (x := q4) (hS (by decide)) 0 rfl (by simp)) fun σ1 e1 => ?_
  refine XV.seq (XV.sconst hL (x := q5) (hS (by decide)) 2 rfl (small_q_lt (c := 2) (by omega))) fun σ2 e2 => ?_
  refine XV.seq (XV.sconst hL (x := q6) (hS (by decide)) 4 rfl (small_q_lt (c := 4) (by omega))) fun σ3 e3 => ?_
  have T3 : TrQ σ σ3 := ((((TrQ.refl σ).setSc (by decide) _).ofEq e1).setSc (by decide) _).ofEq e2 |>.setSc
    (by decide) _ |>.ofEq e3
  have c3 : σ3.sc q3 = (m : ℝ) ∧ σ3.sc q4 = 0 ∧ σ3.sc q1 = 1 ∧ σ3.sc q5 = 2 ∧ σ3.sc q6 = 4 := by
    rw [e3, e2, e1]; simp [hm, h1]
  obtain ⟨c3, c4, c1, c5, c6⟩ := c3
  refine XV.mono (XV.isqrt hL (r := q3) (dd := q7) (q := q8) (t := q9) (n1 := q10) (z := q4) (one := q1) (two := q5)
    (four := q6) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide))
    (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (by decide) c3 c4 c1 c5 c6
    (by
      have : 4 * m + 4 < 2 ^ ℓ := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this)) le_rfl fun σ' ⟨r', _, F'⟩ => ?_
  have k : ∀ y, y ∉ [q3, q7, q8, q9, q10] → σ'.sc y = σ3.sc y := F'.2.1
  exact ⟨r', by rw [k _ (by decide), c4], by rw [k _ (by decide), c1], by rw [k _ (by decide), c5],
    by rw [k _ (by decide), c6], T3.ofFrame F' (by decide)⟩

set_option maxHeartbeats 1000000 in
theorem XV.qC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {B E : ℕ}
    (hNS : 272 ≤ L.NS) (hNN : 11 ≤ L.NN) (hB : σ.nat rB = B) (hBE : B ≤ E) (hz : σ.sc q4 = 0) (h1 : σ.sc q1 = 1)
    (h2 : σ.sc q5 = 2) (h4 : σ.sc q6 = 4) (hℓ : 8 * E + 8 ≤ ℓ) (hℓa : 8 * E + 8 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xqC L) σ (1 + (1 + (12 * (2 * B).size + 8)))
      (fun σ' => σ'.sc q12 = (Nat.sqrt (2 * B) : ℝ) ∧ (∀ y, y < q7 ∨ q7 = y ∨ q12 < y → y ≠ q11 → σ'.sc y = σ.sc y) ∧
        TrQ σ σ') := by
  have hS : ∀ {y : ℕ}, y < 272 → y < L.NS := fun h => by omega
  have hN : ∀ {j : ℕ}, j < 11 → j < L.NN := fun h => by omega
  refine XV.seq (XV.ncastI hL (x := q11) (i := rB) (hS (by decide)) (hN (by decide)) (by rw [hB]; omega))
    fun σ1 e1 => ?_
  have v1 : σ1.sc q11 = ((B : ℕ) : ℝ) := by rw [e1]; simp [hB]
  refine XV.seq (XV.sop2 hL (x := q11) (a := q11) (b := q11) (hS (by decide)) (hS (by decide)) (hS (by decide)) .add
    (by intro h; cases h) (by rw [v1]; exact small_nat_lt (by omega)) (by rw [v1]; exact small_nat_lt (by omega))
    (by rw [v1]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_add]; exact small_nat_lt (by omega))) fun σ2 e2 => ?_
  have T2 : TrQ σ σ2 := (((TrQ.refl σ).setSc (by decide) _).ofEq e1 |>.setSc (by decide) _).ofEq e2
  have v2 : σ2.sc q11 = ((2 * B : ℕ) : ℝ) := by rw [e2]; simp [RealRAM.Op2.eval, v1]; ring
  have k2 : ∀ y, y ≠ q11 → σ2.sc y = σ.sc y := fun y hy => by rw [e2, e1]; simp [RealRAM.Op2.eval, hy]
  refine XV.mono (XV.isqrt hL (r := q11) (dd := q12) (q := q8) (t := q9) (n1 := q10) (z := q4) (one := q1)
    (two := q5) (four := q6) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide))
    (hS (by decide)) (hS (by decide)) (hS (by decide)) (hS (by decide)) (by decide) v2
    (by rw [k2 _ (by decide), hz]) (by rw [k2 _ (by decide), h1]) (by rw [k2 _ (by decide), h2])
    (by rw [k2 _ (by decide), h4])
    (by
      have : 4 * (2 * B) + 4 < 2 ^ ℓ :=
        lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this)) le_rfl fun σ' ⟨r', _, F'⟩ => ?_
  refine ⟨r', fun y hy hy' => ?_, T2.ofFrame F' (by decide)⟩
  rw [F'.2.1 y (by simp only [List.mem_cons, List.mem_nil_iff, or_false, q7, q8, q9, q10, q11, q12] at hy ⊢; omega), k2 y hy']

set_option maxHeartbeats 4000000 in
theorem XV.qD {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {s1 s2 p E : ℕ}
    (hNS : 272 ≤ L.NS) (hNN : 11 ≤ L.NN) (h7 : σ.sc q7 = (s1 : ℝ)) (h12 : σ.sc q12 = (s2 : ℝ)) (h4 : σ.sc q6 = 4)
    (hp : σ.nat rP = p) (h1 : σ.nat rOne = 1) (hs1 : s1 ≤ 2 * E + 5) (hs2 : s2 ≤ 2 * E) (hpE : p ≤ E)
    (hℓ : 20 * E + 40 ≤ ℓ) (hℓa : 20 * E + 40 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xqD L) σ (1 + (1 + (1 + (1 + ((4 * (10 * E + 30) + 4) + 1)))))
      (fun σ' => σ'.nat rQO = p + Nat.clog 2 (9 + 4 * s1 + s2) ∧ TrQ σ σ') := by
  have hS : ∀ {y : ℕ}, y < 272 → y < L.NS := fun h => by omega
  have hN : ∀ {j : ℕ}, j < 11 → j < L.NN := fun h => by omega
  refine XV.seq (XV.sconst hL (x := q13) (hS (by decide)) 9 rfl (small_q_lt (c := 9) (by omega))) fun σ1 e1 => ?_
  have a1 : σ1.sc q13 = ((9 : ℕ) : ℝ) ∧ σ1.sc q6 = ((4 : ℕ) : ℝ) ∧ σ1.sc q7 = (s1 : ℝ) ∧ σ1.sc q12 = (s2 : ℝ) := by
    rw [e1]; simp [h4, h7, h12]
  obtain ⟨a1, b1, c1, d1⟩ := a1
  refine XV.seq (XV.sop2 hL (x := q14) (a := q6) (b := q7) (hS (by decide)) (hS (by decide)) (hS (by decide)) .mul
    (by intro h; cases h) (by rw [b1]; exact small_nat_lt (by omega)) (by rw [c1]; exact small_nat_lt (by omega))
    (by rw [b1, c1]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_mul]; exact small_nat_lt (by omega)))
    fun σ2 e2 => ?_
  have a2 : σ2.sc q14 = ((4 * s1 : ℕ) : ℝ) ∧ σ2.sc q13 = ((9 : ℕ) : ℝ) ∧ σ2.sc q12 = (s2 : ℝ) := by
    rw [e2]; simp [RealRAM.Op2.eval, b1, c1, a1, d1]
  obtain ⟨a2, b2, c2⟩ := a2
  refine XV.seq (XV.sop2 hL (x := q13) (a := q13) (b := q14) (hS (by decide)) (hS (by decide)) (hS (by decide)) .add
    (by intro h; cases h) (by rw [b2]; exact small_nat_lt (by omega)) (by rw [a2]; exact small_nat_lt (by omega))
    (by rw [b2, a2]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_add]; exact small_nat_lt (by omega)))
    fun σ3 e3 => ?_
  have a3 : σ3.sc q13 = ((9 + 4 * s1 : ℕ) : ℝ) ∧ σ3.sc q12 = (s2 : ℝ) := by rw [e3]; simp [RealRAM.Op2.eval, b2, a2, c2]
  obtain ⟨a3, b3⟩ := a3
  refine XV.seq (XV.sop2 hL (x := q13) (a := q13) (b := q12) (hS (by decide)) (hS (by decide)) (hS (by decide)) .add
    (by intro h; cases h) (by rw [a3]; exact small_nat_lt (by omega)) (by rw [b3]; exact small_nat_lt (by omega))
    (by rw [a3, b3]; simp only [RealRAM.Op2.eval]; rw [← Nat.cast_add]; exact small_nat_lt (by omega)))
    fun σ4 e4 => ?_
  have v4 : σ4.sc q13 = (((9 + 4 * s1 + s2 : ℕ) : ℤ) : ℝ) := by rw [e4]; simp [RealRAM.Op2.eval, a3, b3]
  have T4 : TrQ σ σ4 := ((((((TrQ.refl σ).setSc (by decide) _).ofEq e1).setSc (by decide) _).ofEq e2 |>.setSc
    (by decide) _).ofEq e3 |>.setSc (by decide) _).ofEq e4
  have o4 : σ4.nat rOne = 1 := by rw [T4.1 _ (by decide), h1]
  have hSG : 9 + 4 * s1 + s2 ≤ 2 ^ (10 * E + 30) := le_trans (by omega) Nat.lt_two_pow_self.le
  have hSGz : ((9 + 4 * s1 + s2 : ℕ) : ℤ) ≤ 2 ^ (10 * E + 30) := by
    have := (Nat.cast_le (α := ℤ)).2 hSG
    rwa [Nat.cast_pow, Nat.cast_ofNat] at this
  refine XV.seq (XV.clogS hL (w := q15) (x := q13) (c := rS2) (one := rOne) (G := 10 * E + 30) (hS (by decide))
    (hS (by decide)) (hN (by decide)) (hN (by decide)) (by decide) (by decide) v4 (Int.natCast_nonneg _)
    hSGz o4 (by omega) (by omega)) fun σ5 ⟨c5, d5, F5⟩ => ?_
  have T5 : TrQ σ σ5 := T4.ofFrameP F5 d5 (by decide) (by decide)
  have p5 : σ5.nat rP = p := by rw [T5.1 _ (by decide), hp]
  have s5 : σ5.nat rS2 = Nat.clog 2 (9 + 4 * s1 + s2) := by rw [c5, Int.toNat_natCast]
  have hclog : Nat.clog 2 (9 + 4 * s1 + s2) ≤ 9 + 4 * s1 + s2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  refine XV.mono (XV.nadd hL (σ := σ5) (i := rQO) (a := rP) (b := rS2) (hN (by decide)) (hN (by decide))
    (hN (by decide)) (by rw [p5]; omega) (by rw [s5]; omega)) le_rfl fun σ' e' => ?_
  subst e'
  exact ⟨by simp [p5, s5], T5.setNat (by decide) _⟩

/-- **The range `qO` on the bit machine's language**: from `n`, `N_e` in `sN`, `sNe` (below `2^E`), `B` in `rB`,
the register `rQO` gets `p + clog₂(9 + 4 ⌊√(size(14 n N_e))⌋ + ⌊√(2B)⌋)`. -/
theorem XV.qO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {n Ne B p E : ℕ}
    (hNS : 272 ≤ L.NS) (hNN : 11 ≤ L.NN) (hn : σ.sc sN = n) (hNe : σ.sc sNe = Ne) (hB : σ.nat rB = B)
    (hp : σ.nat rP = p) (h1 : σ.nat rOne = 1) (hnE : n ≤ 2 ^ E) (hNeE : Ne ≤ 2 ^ E) (hBE : B ≤ E) (hpE : p ≤ E)
    (hℓ : 20 * E + 40 ≤ ℓ) (hℓa : 20 * E + 40 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xqO L) σ (300 * (E + 1))
      (fun σ' => σ'.nat rQO = p + Nat.clog 2 (9 + 4 * Nat.sqrt (14 * n * Ne).size + Nat.sqrt (2 * B)) ∧
        TrQ σ σ') := by
  have hsz : (14 * n * Ne).size ≤ 2 * E + 5 := by
    have hnNe : n * Ne ≤ 2 ^ (2 * E) := by
      calc n * Ne ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hnE hNeE
        _ = 2 ^ (2 * E) := by rw [← pow_add]; ring_nf
    rw [Nat.size_le]
    have h32 : 2 ^ (2 * E + 5) = 32 * 2 ^ (2 * E) := by rw [pow_add]; ring
    have h14 : 14 * n * Ne = 14 * (n * Ne) := by ring
    have := Nat.mul_le_mul_left 14 hnNe
    have := Nat.one_le_two_pow (n := 2 * E)
    omega
  have hsz2 : (14 * n * Ne).size.size ≤ 2 * E + 5 := (Nat.size_le.2 Nat.lt_two_pow_self).trans hsz
  have hsB : (2 * B).size ≤ 2 * E := (Nat.size_le.2 Nat.lt_two_pow_self).trans (by omega)
  refine XV.mono (XV.seq (XV.qA hL (E := E) hNS hNN hn hNe h1 hnE hNeE (by omega) (by omega))
    fun σ1 ⟨a1, b1, T1⟩ => XV.seq (XV.qB hL hNS a1 b1 (by omega)) fun σ2 ⟨a2, z2, o2, t2, f2, T2⟩ =>
      XV.seq (XV.qC hL (E := E) hNS hNN (by rw [T2.1 _ (by decide), T1.1 _ (by decide), hB]) hBE z2 o2 t2 f2
        (by omega) (by omega)) fun σ3 ⟨a3, k3, T3⟩ =>
      XV.mono (XV.qD hL (E := E) hNS hNN (by rw [k3 _ (by decide) (by decide), a2]) a3
        (by rw [k3 _ (by decide) (by decide), f2])
        (by rw [T3.1 _ (by decide), T2.1 _ (by decide), T1.1 _ (by decide), hp])
        (by rw [T3.1 _ (by decide), T2.1 _ (by decide), T1.1 _ (by decide), h1])
        ((Nat.sqrt_le_self _).trans hsz) ((Nat.sqrt_le_self _).trans (by omega)) hpE hℓ hℓa) le_rfl
        fun σ' ⟨h, T⟩ => ⟨h, T1.trans (T2.trans (T3.trans T))⟩)
    (by omega) fun _ h => h


/-! ## The contract -/

/-- R3: the range `qO`, then the clipped reading into `sObs`. -/
def xR3 (L : Layout) : XCmdO := .seq (.base (xqO L)) (xobsRO L sObs rP rQO)

/-- The constants of R3. -/
def kR3 : BlkK := ⟨400, 1, 0, 0, 272, 11, 0⟩

end AdversarialBco.Unified.ProgO
