/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit
public import AdversarialBco.Unified.ProgOSepU
public import AdversarialBco.Bit.Transfer.XEllConst
public import AdversarialBco.Bit.Transfer.XIsqrt

@[expose] public section

/-!
# BL-O's CM test on the machine (shared by the cross check of the setup and by the tail of the round)

BL-O's test `c.T orc k 1 y = cmQ orc a r₀ k (μ_S + A_S y)` (BLOSpec.lean) in two blocks, their scratch cells from the
bases `Q.s` (slots), `Q.n` (registers), `Q.a` (arrays) of a `TstLay`:

* `xcmc`: the constants of the precision `kC`: `r₀` as `num, den` (input cells `4`, `5`) into the slots `Q.s`,
  `Q.s + 1`, `kC = p + clog₂ ⌈6 R R₀/r₀²⌉ + 4` (`R` from the slot `sR` over `2^pF`, `R₀` from the input cells `6`, `7`)
  into the register `Q.n` and `2^kC` into the slot `Q.s + 2`;
* `xtst`: for a point `(D; N)` in an array `ap` (cell `0` the denominator, cells `1 + i` the numerators), the position
  map `z = μ̂_S/D_S + (Â_S/D_S)(N/D)` as `(D_S D; μ̂_S D + Â_S N)`, then the CM block `xcm` at the precision of
  the register `Q.n` with `2^k` in the slot `Q.s + 2`, the centre in `aC`; the answer into the register `nt`.
  `tstOK`: a test block (`TestOK`, SepSpec.lean) for the test `cmQ orc a (rn/rd) k ∘ pmap`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- The bases of the test's cells: slots `s, ..., s + 55`, registers `n, ..., n + 15`, arrays `a, ..., a + 3`. -/
structure TstLay where
  s : ℕ
  n : ℕ
  a : ℕ

/-- The test's cells fit the layout above BL's persistent cells. -/
structure TstLay.OK (Q : TstLay) (L : Layout) : Prop where
  s : 26 ≤ Q.s ∧ Q.s + 56 ≤ L.NS
  n : 8 ≤ Q.n ∧ Q.n + 16 ≤ L.NN
  a : 8 ≤ Q.a ∧ Q.a + 4 ≤ L.NA

theorem pow_le_pow_z {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

theorem pow_lt_pow_z {a b : ℕ} (h : a < b) : (2 : ℤ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) h

/-- An integer below `2^a`, `a < ℓ`, passes the bound of the bounded semantics. -/
theorem int_lt_of_le {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |(z : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (lt_of_le_of_lt h (pow_lt_pow_z ha))

/-! ## The constants of the precision -/

/-- Part A: `r₀`, `R₀` from the input cells into the slots `Q.s`, `Q.s + 1`, `Q.s + 3`, `Q.s + 4`; the constant `6` into `Q.s + 5`. -/
def xcmcA (L : Layout) (Q : TstLay) : XCmd :=
  .seq (.prim (.frag (.nconst (Q.n + 12) 4))) <| .seq (xrdIn L Q.s (Q.n + 12)) <|
  .seq (.prim (.frag (.nconst (Q.n + 12) 5))) <| .seq (xrdIn L (Q.s + 1) (Q.n + 12)) <|
  .seq (.prim (.frag (.nconst (Q.n + 12) 6))) <| .seq (xrdIn L (Q.s + 3) (Q.n + 12)) <|
  .seq (.prim (.frag (.nconst (Q.n + 12) 7))) <| .seq (xrdIn L (Q.s + 4) (Q.n + 12)) <|
  toX (VL.sconst L (Q.s + 5) 6)

/-- `6 R R₀ r_d²` over the slots `Q.s + 5` (`6`), `sR`, `Q.s + 3` (`R₀` num), `Q.s + 1` (`r₀` den). -/
def ieN (Q : TstLay) : IE :=
  .op .mul (.op .mul (.op .mul (.op .mul (.sc (Q.s + 5)) (.sc sR)) (.sc (Q.s + 3))) (.sc (Q.s + 1))) (.sc (Q.s + 1))

/-- `2^pF R₀_d r_n²` over the slots `s2pF`, `Q.s + 4` (`R₀` den), `Q.s` (`r₀` num). -/
def ieD (Q : TstLay) : IE := .op .mul (.op .mul (.op .mul (.sc s2pF) (.sc (Q.s + 4))) (.sc Q.s)) (.sc Q.s)

/-- Part B: `N`, `D`, then `⌈N/D⌉ = -((-N)/D)` into the slot `Q.s + 10`. -/
def xcmcB (L : Layout) (Q : TstLay) : XCmd :=
  .seq ((ieN Q).code L sZ (Q.s + 6) (Q.s + 12)) <| .seq ((ieD Q).code L sZ (Q.s + 7) (Q.s + 12)) <|
  .seq (toX (VL.sop2 L .sub (Q.s + 8) sZ (Q.s + 6))) <| .seq (xsidiv L (Q.s + 9) (Q.s + 8) (Q.s + 7)) <|
  toX (VL.sop2 L .sub (Q.s + 10) sZ (Q.s + 9))

/-- Part C: `k = p + clog₂ ⌈N/D⌉ + 4` into the register `Q.n`, `2^k` into the slot `Q.s + 2`. -/
def xcmcC (L : Layout) (Q : TstLay) : XCmd :=
  .seq (xclogS L (Q.s + 11) (Q.s + 10) (Q.n + 13) rOne) <|
  .seq (.prim (.frag (.nadd Q.n rP (Q.n + 13)))) <| .seq (.prim (.frag (.nconst (Q.n + 14) 4))) <|
  .seq (.prim (.frag (.nadd Q.n Q.n (Q.n + 14)))) <|
  xpow2 L (Q.s + 2) (Q.n + 15) Q.n rOne

/-- The constants of the CM test: `r₀`, `kC`, `2^kC`. -/
def xcmc (L : Layout) (Q : TstLay) : XCmd := .seq (xcmcA L Q) (.seq (xcmcB L Q) (xcmcC L Q))

/-- The precision from the integers `N`, `D` of `6 R R₀/r₀² = N/D`: `p + clog₂ ⌈N/D⌉ + 4`. -/
def cmcK (p : ℕ) (N D : ℤ) : ℕ := p + Nat.clog 2 (0 - (0 - N) / D).toNat + 4

theorem ceil_quot_le {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) : 0 ≤ 0 - (0 - N) / D ∧ 0 - (0 - N) / D ≤ N := by
  have h1 := Int.ediv_mul_le (0 - N) hD.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (0 - N) hD
  constructor
  · by_contra h
    have : 1 ≤ (0 - N) / D := by omega
    nlinarith
  · by_contra h
    have : (0 - N) / D + 1 ≤ 0 - N := by omega
    nlinarith

set_option maxHeartbeats 1000000 in
theorem XV.cmcA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {rn rd Rn0 Rd0 : ℤ} {m : ℕ}
    (i4 : X.inp 4 = rn) (i5 : X.inp 5 = rd) (i6 : X.inp 6 = Rn0) (i7 : X.inp 7 = Rd0) (hoff : 8 ≤ X.off)
    (brn : |rn| ≤ 2 ^ m) (brd : |rd| ≤ 2 ^ m) (bR0n : |Rn0| ≤ 2 ^ m) (bR0d : |Rd0| ≤ 2 ^ m) (hℓ : m + 3 < ℓ) :
    XRunsB L X ℓa ℓ (xcmcA L Q) σ 9 (fun σ' =>
      σ'.sc Q.s = rn ∧ σ'.sc (Q.s + 1) = rd ∧ σ'.sc (Q.s + 3) = Rn0 ∧ σ'.sc (Q.s + 4) = Rd0 ∧
      σ'.sc (Q.s + 5) = 6 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => Q.s ≤ y ∧ y < Q.s + 6) (fun j => j = Q.n + 12) (fun _ _ => False) σ σ') := by
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, -⟩ := hQ
  have hL1 := hL.1
  have hr : ∀ {z : ℤ}, |z| ≤ 2 ^ m → |(z : ℝ)| < 2 ^ ℓ := fun h => int_lt_of_le h (by omega)
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.nconst hL (i := Q.n + 12) (by omega) 4 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.rdIn (X := X) hL (x := Q.s) (i := Q.n + 12) (by omega) (by omega) (by simp; omega)
    (by simp; omega) (by simp only [Env.setNat_nat, ite_eq_left]; rw [i4]; exact hr brn)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := Q.n + 12) (by omega) 5 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.rdIn (X := X) hL (x := Q.s + 1) (i := Q.n + 12) (by omega) (by omega) (by simp; omega)
    (by simp; omega) (by simp only [Env.setNat_nat, ite_eq_left]; rw [i5]; exact hr brd)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nconst hL (i := Q.n + 12) (by omega) 6 (by omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.rdIn (X := X) hL (x := Q.s + 3) (i := Q.n + 12) (by omega) (by omega) (by simp; omega)
    (by simp; omega) (by simp only [Env.setNat_nat, ite_eq_left]; rw [i6]; exact hr bR0n)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.nconst hL (i := Q.n + 12) (by omega) 7 (by omega)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.rdIn (X := X) hL (x := Q.s + 4) (i := Q.n + 12) (by omega) (by omega) (by simp; omega)
    (by simp; omega) (by simp only [Env.setNat_nat, ite_eq_left]; rw [i7]; exact hr bR0d)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.sconst hL (x := Q.s + 5) (by omega) 6 rfl (by
    rw [show ((6 : ℚ) : ℝ) = ((6 : ℤ) : ℝ) by norm_num]
    exact int_lt_of_le (a := 3) (by norm_num) (by omega))) le_rfl fun σ9 e9 => ?_
  subst e9
  refine ⟨by simp [i4], by simp [i5], by simp [i6], by simp [i7], by simp, by simp, ?_⟩
  have hS : ∀ k < 6, Q.s ≤ Q.s + k ∧ Q.s + k < Q.s + 6 := fun k hk => ⟨by omega, by omega⟩
  exact (((((((((FrameA.refl (fun y => Q.s ≤ y ∧ y < Q.s + 6) (fun j => j = Q.n + 12) (fun _ _ => False) σ).setNat rfl _).setSc (hS 0 (by norm_num)) _).setNat rfl _).setSc
    (hS 1 (by norm_num)) _).setNat rfl _).setSc (hS 3 (by norm_num)) _).setNat rfl _).setSc
    (hS 4 (by norm_num)) _).setSc (hS 5 (by norm_num)) _

theorem abs_six_le {E : ℕ} (h : (6 : ℤ) ≤ 2 ^ E) : |(6 : ℤ)| ≤ 2 ^ E := by rw [abs_of_pos (by norm_num)]; exact h

set_option maxHeartbeats 2000000 in
theorem XV.cmcB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {rn rd Rn0 Rd0 Rn PF : ℤ} {E : ℕ}
    (hz : σ.sc sZ = 0) (v0 : σ.sc Q.s = rn) (v1 : σ.sc (Q.s + 1) = rd) (v3 : σ.sc (Q.s + 3) = Rn0)
    (v4 : σ.sc (Q.s + 4) = Rd0) (v5 : σ.sc (Q.s + 5) = 6) (vR : σ.sc sR = Rn) (vF : σ.sc s2pF = PF)
    (brn : |rn| ≤ 2 ^ E) (brd : |rd| ≤ 2 ^ E) (bR0n : |Rn0| ≤ 2 ^ E) (bR0d : |Rd0| ≤ 2 ^ E) (bRn : |Rn| ≤ 2 ^ E)
    (bPF : |PF| ≤ 2 ^ E) (b6 : (6 : ℤ) ≤ 2 ^ E) (hℓ : 5 * E + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xcmcB L Q) σ ((ieN Q).units + ((ieD Q).units + (1 + (1 + 1))))
      (fun σ' => σ'.sc (Q.s + 10) = ((0 - (0 - 6 * Rn * Rn0 * rd * rd) / (PF * Rd0 * rn * rn) : ℤ) : ℝ) ∧
        σ'.draws = σ.draws ∧ FrameP (fun y => Q.s + 6 ≤ y) (fun _ => False) σ σ') := by
  obtain ⟨⟨hs0, hs1⟩, -, -⟩ := hQ
  set Nq := 6 * Rn * Rn0 * rd * rd with hNq
  set Dq := PF * Rd0 * rn * rn with hDq
  have bN : |Nq| ≤ 2 ^ (5 * E) := by
    have := absI_mul_le (absI_mul_le (absI_mul_le (absI_mul_le (abs_six_le b6) bRn) bR0n) brd) brd
    rwa [show E + E + E + E + E = 5 * E by ring] at this
  have bD : |Dq| ≤ 2 ^ (5 * E) := by
    have := absI_mul_le (absI_mul_le (absI_mul_le bPF bR0d) brn) brn
    exact this.trans (pow_le_pow_z (by omega))
  have hlt : ∀ {z : ℤ}, |z| ≤ 2 ^ (5 * E) → |z| < 2 ^ ℓ := fun h => lt_of_le_of_lt h (pow_lt_pow_z (by omega))
  -- `N`
  refine XV.seq (XV.ieRun (X := X) (σ := σ) (E := E) (v := Nq) hL (z := sZ) (x := Q.s + 6) (t := Q.s + 12)
    (e := ieN Q) (by simp only [ieN, IE.WF, sR, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by simp only [sZ]; omega) (by omega) (by simp only [ieN, IE.scr]; omega) hz
    (by simp only [ieN, IE.Leaves]
        exact ⟨⟨⟨⟨⟨6, by rw [v5]; norm_num, abs_six_le b6⟩, ⟨Rn, vR, bRn⟩⟩, ⟨Rn0, v3, bR0n⟩⟩, ⟨rd, v1, brd⟩⟩,
          ⟨rd, v1, brd⟩⟩)
    (by simp only [ieN, IE.top, IE.mag]; omega)
    (by simp only [ieN, IE.eval, RealRAM.Op2.eval, v5, vR, v3, v1, hNq]; push_cast; ring))
    fun σ1 ⟨a1, _, d1, F1⟩ => ?_
  have k1 : ∀ y, y ≠ Q.s + 6 → y < Q.s + 12 → σ1.sc y = σ.sc y := fun y h h' => F1.2.1 y (by omega)
  -- `D`
  refine XV.seq (XV.ieRun (X := X) (σ := σ1) (E := E) (v := Dq) hL (z := sZ) (x := Q.s + 7) (t := Q.s + 12)
    (e := ieD Q) (by simp only [ieD, IE.WF, s2pF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by simp only [sZ]; omega) (by omega) (by simp only [ieD, IE.scr]; omega)
    (by rw [k1 _ (by simp only [sZ]; omega) (by simp only [sZ]; omega), hz])
    (by simp only [ieD, IE.Leaves]
        exact ⟨⟨⟨⟨PF, by rw [k1 _ (by simp only [s2pF]; omega) (by simp only [s2pF]; omega), vF], bPF⟩,
          ⟨Rd0, by rw [k1 _ (by omega) (by omega), v4], bR0d⟩⟩, ⟨rn, by rw [k1 _ (by omega) (by omega), v0], brn⟩⟩,
          ⟨rn, by rw [k1 _ (by omega) (by omega), v0], brn⟩⟩)
    (by simp only [ieD, IE.top, IE.mag]; omega)
    (by simp only [ieD, IE.eval, RealRAM.Op2.eval, k1 s2pF (by simp only [s2pF]; omega) (by simp only [s2pF]; omega),
          k1 Q.s (by omega) (by omega), k1 (Q.s + 4) (by omega) (by omega), vF, v4, v0, hDq]; push_cast; ring))
    fun σ2 ⟨a2, _, d2, F2⟩ => ?_
  have k2 : ∀ y, y ≠ Q.s + 7 → y < Q.s + 12 → σ2.sc y = σ1.sc y := fun y h h' => F2.2.1 y (by omega)
  have z2 : σ2.sc sZ = ((0 : ℤ) : ℝ) := by
    rw [k2 _ (by simp only [sZ]; omega) (by simp only [sZ]; omega), k1 _ (by simp only [sZ]; omega)
      (by simp only [sZ]; omega), hz]; simp
  have n2 : σ2.sc (Q.s + 6) = Nq := by rw [k2 _ (by omega) (by omega), a1]
  -- `-N`, `(-N)/D`, `-((-N)/D)`
  have h0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bNn : |0 - Nq| < 2 ^ ℓ := by rw [zero_sub, abs_neg]; exact hlt bN
  refine XV.seq (XV.subI hL (x := Q.s + 8) (a := sZ) (b := Q.s + 6) (by omega) (by simp only [sZ]; omega) (by omega)
    z2 n2 h0 (hlt bN) bNn) fun σ3 e3 => ?_
  have m3 : σ3.sc (Q.s + 8) = ((0 - Nq : ℤ) : ℝ) := by rw [e3]; simp
  have dd3 : σ3.sc (Q.s + 7) = Dq := by rw [e3, Env.setSc_sc, ite_eq_right (by omega), a2]
  have z3 : σ3.sc sZ = ((0 : ℤ) : ℝ) := by rw [e3, Env.setSc_sc, ite_eq_right (by simp only [sZ]; omega), z2]
  have bq : |(0 - Nq) / Dq| ≤ 2 ^ (5 * E) := (Int.abs_ediv_le_abs _ _).trans (by rw [zero_sub, abs_neg]; exact bN)
  refine XV.seq (XV.divI hL (x := Q.s + 9) (a := Q.s + 8) (b := Q.s + 7) (by omega) (by omega) (by omega)
    m3 dd3 bNn (hlt bD)) fun σ4 e4 => ?_
  have q4 : σ4.sc (Q.s + 9) = (((0 - Nq) / Dq : ℤ) : ℝ) := by rw [e4]; simp
  have z4 : σ4.sc sZ = ((0 : ℤ) : ℝ) := by rw [e4, Env.setSc_sc, ite_eq_right (by simp only [sZ]; omega), z3]
  have bq' : |0 - (0 - Nq) / Dq| < 2 ^ ℓ := by rw [zero_sub, abs_neg]; exact hlt bq
  refine XV.mono (XV.subI hL (x := Q.s + 10) (a := sZ) (b := Q.s + 9) (by omega) (by simp only [sZ]; omega)
    (by omega) z4 q4 h0 (hlt bq) bq') le_rfl fun σ5 e5 => ?_
  have F3 : FrameP (fun y => Q.s + 6 ≤ y) (fun _ => False) σ σ3 := by
    rw [e3]
    exact ((F1.mono (fun y h => by omega) (fun _ h => h)).trans (F2.mono (fun y h => by omega) (fun _ h => h))).setSc
      (by omega) _
  have F4 : FrameP (fun y => Q.s + 6 ≤ y) (fun _ => False) σ σ4 := by rw [e4]; exact F3.setSc (by omega) _
  refine ⟨by rw [e5]; simp, by rw [e5, e4, e3]; simp [d2, d1], ?_⟩
  rw [e5]; exact F4.setSc (by omega) _

theorem XV.cmcC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {v : ℤ} {p G : ℕ} (hv : σ.sc (Q.s + 10) = v) (hv0 : 0 ≤ v) (hvG : v ≤ 2 ^ G) (h1 : σ.nat rOne = 1)
    (hp : σ.nat rP = p) (hGℓ : p + G + 5 < ℓ) (hGa : p + G + 5 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcmcC L Q) σ ((4 * G + 4) + (1 + (1 + (1 + (4 * (p + Nat.clog 2 v.toNat + 4) + 4)))))
      (fun σ' => σ'.nat Q.n = p + Nat.clog 2 v.toNat + 4 ∧ σ'.sc (Q.s + 2) = 2 ^ (p + Nat.clog 2 v.toNat + 4) ∧
        σ'.draws = σ.draws ∧ FrameA (fun y => y = Q.s + 2 ∨ y = Q.s + 11)
          (fun j => j = Q.n ∨ (Q.n + 13 ≤ j ∧ j < Q.n + 16)) (fun _ _ => False) σ σ') := by
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, -⟩ := hQ
  have hL1 := hL.1
  have hcl : Nat.clog 2 v.toNat ≤ G := Nat.clog_le_of_le_pow (by
    have : (v.toNat : ℤ) ≤ 2 ^ G := by rw [Int.toNat_of_nonneg hv0]; exact hvG
    exact_mod_cast this)
  refine XV.seq (XV.clogS hL (w := Q.s + 11) (x := Q.s + 10) (c := Q.n + 13) (one := rOne) (G := G) (by omega)
    (by omega) (by omega) (by simp only [rOne]; omega) (by omega) (by simp only [rOne]; omega) hv hv0 hvG h1
    (by omega) (by omega)) fun σ1 ⟨c1, d1, F1⟩ => ?_
  have o1 : σ1.nat rOne = 1 := by rw [F1.1 _ (by simp only [rOne]; omega), h1]
  have p1 : σ1.nat rP = p := by rw [F1.1 _ (by simp only [rP]; omega), hp]
  have r14 : rOne ≠ Q.n + 14 := by simp only [rOne]; omega
  have r0 : rOne ≠ Q.n := by simp only [rOne]; omega
  have F1' : FrameA (fun y => y = Q.s + 2 ∨ y = Q.s + 11) (fun j => j = Q.n ∨ (Q.n + 13 ≤ j ∧ j < Q.n + 16))
      (fun _ _ => False) σ σ1 := FrameA.ofP (F1.mono (fun y h => Or.inr h) (fun j h => Or.inr ⟨by omega, by omega⟩))
  refine XV.seq (XV.nadd hL (σ := σ1) (i := Q.n) (a := rP) (b := Q.n + 13) (by omega) (by simp only [rP]; omega)
    (by omega) (by rw [p1]; omega) (by rw [c1]; omega)) fun σ2 e2 => ?_
  have n2 : σ2.nat Q.n = p + Nat.clog 2 v.toNat := by rw [e2]; simp [p1, c1]
  have o2 : σ2.nat rOne = 1 := by rw [e2, Env.setNat_nat, ite_eq_right r0, o1]
  have F2 : FrameA (fun y => y = Q.s + 2 ∨ y = Q.s + 11) (fun j => j = Q.n ∨ (Q.n + 13 ≤ j ∧ j < Q.n + 16))
      (fun _ _ => False) σ σ2 := by rw [e2]; exact F1'.setNat (Or.inl rfl) _
  refine XV.seq (XV.nconst hL (i := Q.n + 14) (by omega) 4 (by omega)) fun σ3 e3 => ?_
  have n3 : σ3.nat Q.n = p + Nat.clog 2 v.toNat := by rw [e3]; simp [n2]
  have f3 : σ3.nat (Q.n + 14) = 4 := by rw [e3]; simp
  have o3 : σ3.nat rOne = 1 := by rw [e3, Env.setNat_nat, ite_eq_right r14, o2]
  have F3 : FrameA (fun y => y = Q.s + 2 ∨ y = Q.s + 11) (fun j => j = Q.n ∨ (Q.n + 13 ≤ j ∧ j < Q.n + 16))
      (fun _ _ => False) σ σ3 := by rw [e3]; exact F2.setNat (Or.inr ⟨by omega, by omega⟩) _
  refine XV.seq (XV.nadd hL (i := Q.n) (a := Q.n) (b := Q.n + 14) (by omega) (by omega) (by omega)
    (by rw [n3]; omega) (by rw [f3]; omega)) fun σ4 e4 => ?_
  have n4 : σ4.nat Q.n = p + Nat.clog 2 v.toNat + 4 := by rw [e4]; simp [n3, f3]
  have o4 : σ4.nat rOne = 1 := by rw [e4, Env.setNat_nat, ite_eq_right r0, o3]
  have F4 : FrameA (fun y => y = Q.s + 2 ∨ y = Q.s + 11) (fun j => j = Q.n ∨ (Q.n + 13 ≤ j ∧ j < Q.n + 16))
      (fun _ _ => False) σ σ4 := by rw [e4]; exact F3.setNat (Or.inl rfl) _
  have dd4 : σ4.draws = σ.draws := by rw [e4, e3, e2]; simp [d1]
  refine XV.mono (XV.pow2 hL (p := Q.s + 2) (i := Q.n + 15) (n := Q.n) (one := rOne) (by omega) (by omega) (by omega)
    (by simp only [rOne]; omega) (by omega) (by simp only [rOne]; omega) (W := p + Nat.clog 2 v.toNat + 4)
    n4 o4 (by omega) (by omega)) le_rfl fun σ5 h5 => ?_
  obtain ⟨q5, _, F5⟩ := h5
  refine ⟨by rw [F5.1 _ (by simp), n4], q5, by rw [F5.2.2.2.1, dd4], ?_⟩
  exact F4.trans ⟨fun j hj => F5.1 j (by simp only [List.mem_singleton]; omega), fun y hy => F5.2.1 y (by
    simp only [List.mem_singleton]; omega), fun b k _ => by rw [F5.2.2.1], F5.2.2.2.2.1, F5.2.2.2.2.2⟩


/-! ## The composition of the constants -/

set_option maxHeartbeats 2000000 in
/-- **The constants of the CM test**: `r₀ = rn/rd` (input cells `4`, `5`) into the slots `Q.s`, `Q.s + 1`, the
precision `cmcK p N D` into the register `Q.n` and its power of `2` into the slot `Q.s + 2`, for
`N = 6 R_n R₀ₙ r_d²`, `D = PF R₀_d r_n²`; every input at most `2^m`. -/
theorem XV.cmc {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {rn rd Rn0 Rd0 Rn PF : ℤ} {p m : ℕ}
    (i4 : X.inp 4 = rn) (i5 : X.inp 5 = rd) (i6 : X.inp 6 = Rn0) (i7 : X.inp 7 = Rd0) (hoff : 8 ≤ X.off)
    (hrn : 0 < rn) (hrd : 0 < rd) (hR0n : 0 < Rn0) (hR0d : 0 < Rd0) (hRn : 0 ≤ Rn) (hPF : 0 < PF)
    (hz : σ.sc sZ = 0) (h1 : σ.nat rOne = 1) (hp : σ.nat rP = p) (hR : σ.sc sR = Rn) (hF : σ.sc s2pF = PF)
    (brn : rn ≤ 2 ^ m) (brd : rd ≤ 2 ^ m) (bR0n : Rn0 ≤ 2 ^ m) (bR0d : Rd0 ≤ 2 ^ m) (bRn : Rn ≤ 2 ^ m)
    (bPF : PF ≤ 2 ^ m) (hpm : p ≤ m) (hℓ : 12 * m + 40 ≤ ℓ) (hℓa : 12 * m + 40 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcmc L Q) σ (200 * (m + 1)) (fun σ' =>
      σ'.sc Q.s = rn ∧ σ'.sc (Q.s + 1) = rd ∧
      σ'.nat Q.n = cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) ∧
      σ'.sc (Q.s + 2) = 2 ^ cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => Q.s ≤ y) (fun j => j = Q.n ∨ (Q.n + 12 ≤ j ∧ j < Q.n + 16)) (fun _ _ => False) σ σ') := by
  have hQ' := hQ
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, -⟩ := hQ'
  set E := m + 3 with hE
  have hmE : (2 : ℤ) ^ m ≤ 2 ^ E := pow_le_pow_z (by omega)
  have p6 : (6 : ℤ) ≤ 2 ^ E := by
    calc (6 : ℤ) ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ E := pow_le_pow_z (by omega)
  have ab : ∀ {z : ℤ}, 0 ≤ z → z ≤ 2 ^ m → |z| ≤ 2 ^ m := fun h0 h => by rw [abs_of_nonneg h0]; exact h
  have aE : ∀ {z : ℤ}, 0 ≤ z → z ≤ 2 ^ m → |z| ≤ 2 ^ E := fun h0 h => (ab h0 h).trans hmE
  set Nq := 6 * Rn * Rn0 * rd * rd with hNq
  set Dq := PF * Rd0 * rn * rn with hDq
  have hNq0 : 0 ≤ Nq := by positivity
  have hDq0 : 0 < Dq := by positivity
  have bNq : Nq ≤ 2 ^ (5 * E) := by
    have := absI_mul_le (absI_mul_le (absI_mul_le (absI_mul_le (abs_six_le p6) (aE hRn bRn)) (aE hR0n.le bR0n))
      (aE hrd.le brd)) (aE hrd.le brd)
    rw [abs_of_nonneg hNq0, show E + E + E + E + E = 5 * E by ring] at this
    exact this
  obtain ⟨hv0, hvN⟩ := ceil_quot_le hNq0 hDq0
  refine XV.mono (K := 9 + (((ieN Q).units + ((ieD Q).units + (1 + (1 + 1)))) + ((4 * (5 * E) + 4) +
    (1 + (1 + (1 + (4 * (p + Nat.clog 2 (0 - (0 - Nq) / Dq).toNat + 4) + 4))))))) ?_ ?_ fun _ h => h
  rotate_left
  · have hcl : Nat.clog 2 (0 - (0 - Nq) / Dq).toNat ≤ 5 * E := Nat.clog_le_of_le_pow (by
      have : ((0 - (0 - Nq) / Dq).toNat : ℤ) ≤ 2 ^ (5 * E) := by rw [Int.toNat_of_nonneg hv0]; exact hvN.trans bNq
      exact_mod_cast this)
    simp only [ieN, ieD, IE.units]; omega
  refine XV.seq (XV.cmcA hL hQ i4 i5 i6 i7 hoff (ab hrn.le brn) (ab hrd.le brd) (ab hR0n.le bR0n)
    (ab hR0d.le bR0d) (by omega)) fun σ1 ⟨a0, a1, a3, a4, a5, d1, F1⟩ => ?_
  have k1 : ∀ y, y < Q.s → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  refine XV.seq (XV.cmcB hL hQ (E := E) (by rw [k1 _ (by simp only [sZ]; omega), hz]) a0 a1 a3 a4 a5
    (by rw [k1 _ (by simp only [sR]; omega), hR]) (by rw [k1 _ (by simp only [s2pF]; omega), hF])
    (aE hrn.le brn) (aE hrd.le brd) (aE hR0n.le bR0n) (aE hR0d.le bR0d) (aE hRn bRn) (aE hPF.le bPF) p6
    (by omega)) fun σ2 ⟨b2, d2, F2⟩ => ?_
  have hv5 : 0 - (0 - Nq) / Dq ≤ 2 ^ (5 * E) := hvN.trans bNq
  refine XV.mono (XV.cmcC hL hQ (p := p) (G := 5 * E) b2 hv0 hv5
    (by rw [F2.1 _ (by simp), F1.1 _ (by simp only [rOne]; omega), h1])
    (by rw [F2.1 _ (by simp), F1.1 _ (by simp only [rP]; omega), hp]) (by omega) (by omega)) le_rfl
    fun σ3 ⟨c3, q3, d3, F3⟩ => ?_
  refine ⟨?_, ?_, c3, q3, by rw [d3, d2, d1], ?_⟩
  · rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega), a0]
  · rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega), a1]
  · exact (F1.mono (fun y h => h.1) (fun j h => Or.inr ⟨by omega, by omega⟩) (fun _ _ h => h)).trans
      ((FrameA.ofP (F2.mono (fun y h => by omega) (fun _ h => h.elim))).trans
        (F3.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h)))

/-! ## The position map and the test -/

/-- The copy `aNt[k] := ap[1 + k]`, `k < d`, into the array `Q.a`. -/
def xtCopy (L : Layout) (Q : TstLay) (ap : ℕ) : XCmd :=
  xforN (Q.n + 6) rD rOne (.seq (.prim (.frag (.nadd (Q.n + 7) (Q.n + 6) rOne)))
    (.seq (toX (VL.aget L (Q.s + 16) ap (Q.n + 7))) (toX (VL.aset L Q.a (Q.n + 6) (Q.s + 16)))))

/-- `μ̂_{S,k} D + y_k`, `k` in the register `Q.n + 10`, `D` in the slot `Q.s + 17`, `y = Â_S N` in the array `Q.a + 1`. -/
def ieMap (Q : TstLay) : IE := .op .add (.op .mul (.arr aMuS (Q.n + 10)) (.sc (Q.s + 17))) (.arr (Q.a + 1) (Q.n + 10))

/-- The position map of the point `(D; N)` in the array `ap`: `(D_S D; μ̂_S D + Â_S N)` into the array `Q.a + 2`. -/
def xtMap (L : Layout) (Q : TstLay) (ap : ℕ) : XCmd :=
  .seq (xtCopy L Q ap) <|
  .seq (xmatvec L sZ (Q.s + 19) (Q.s + 20) aAS Q.a (Q.a + 1) (Q.n + 8) (Q.n + 9) (Q.n + 10) rD rOne) <|
  .seq (.prim (.frag (.nconst (Q.n + 6) 0))) <| .seq (toX (VL.aget L (Q.s + 17) ap (Q.n + 6))) <|
  .seq (toX (VL.sop2 L .mul (Q.s + 18) sDS (Q.s + 17))) <| .seq (toX (VL.aset L (Q.a + 2) (Q.n + 6) (Q.s + 18))) <|
  .seq (.prim (.frag (.nconst (Q.n + 9) 1))) <|
  xmapE L sZ (Q.s + 24) (ieMap Q) (Q.a + 2) (Q.n + 9) rOne (Q.n + 10) rD rOne

/-- The cells of the CM block in the test: the centre in `aC`, `r₀` in the slots `Q.s`, `Q.s + 1`, the precision in
the register `Q.n`, its power of `2` in the slot `Q.s + 2`, the point in the array `Q.a + 2`, the answer in the register
`Q.n + 1`, the query point in the array `Q.a + 3`, scratch slots from `Q.s + 40`, registers from `Q.n + 2`. -/
def cmLayQ (Q : TstLay) : CMLay := ⟨aC, Q.s, Q.s + 1, Q.n, Q.s + 2, Q.a + 2, Q.n + 1, Q.a + 3, Q.s + 40, Q.n + 2⟩

/-- **The test block**: the position map, the CM block, the answer into the register `nt`. -/
def xtst (L : Layout) (Q : TstLay) (ap nt : ℕ) : XCmdO :=
  .seq (.base (xtMap L Q ap)) <| .seq (xcmU L (cmLayQ Q)) <|
  .base (.seq (.prim (.frag (.nconst nt 0))) (.prim (.frag (.nadd nt nt (Q.n + 1)))))

/-- The position map on rationals: `(μ̂_S + Â_S y)/D_S`. -/
def pmap (DS : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (y : Fin d → ℚ) : Fin d → ℚ :=
  fun i => ((muS i : ℚ) + ∑ j, (aS i j : ℚ) * y j) / DS

/-- The data the test block reads: `d`, `1`, `0`, the position (`D_S`, `μ̂_S`, `Â_S`) and the CM block's data. -/
structure TstDat (Q : TstLay) (DS : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (Da : ℤ) (Na : Fin d → ℤ)
    (rn rd : ℤ) (k : ℕ) (σ : Env d) : Prop where
  hd : σ.nat rD = d
  h1 : σ.nat rOne = 1
  hz : σ.sc sZ = 0
  hds : σ.sc sDS = DS
  hmu : ∀ i : Fin d, σ.arr aMuS i = muS i
  has : ∀ i j : Fin d, σ.arr aAS (d * i + j) = aS i j
  hcm : CMDat (cmLayQ Q) Da Na rn rd k σ

/-- The units of the test block. -/
def tstK (d : ℕ) : ℕ := (d * (5 + 3) + 3) + ((d * (d * 10 + 9) + 4) + (1 + (2 + (1 + (2 + (1 + (d * (7 + 6) + 3)))))))
  + (cmK d + (1 + 1))

theorem pmap_eq (DS D : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (Nv : Fin d → ℤ) (hDS : DS ≠ 0)
    (hD : D ≠ 0) :
    ptDN (DS * D) (fun i => muS i * D + (aS *ᵥ Nv) i) = pmap DS muS aS (ptDN D Nv) := by
  funext i
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hs : ∑ j, (aS i j : ℚ) * ((Nv j : ℚ) / D) = (∑ j, (aS i j : ℚ) * Nv j) / D := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  simp only [ptDN, pmap, mulVec, dotProduct, hs]
  push_cast
  field_simp


theorem le_asz' {j : ℕ} (hd : 1 ≤ d) (hj : j ≤ d) : j < asz d := by unfold asz; nlinarith

set_option maxHeartbeats 2000000 in
/-- The copy of the numerators `ap[1 + k]`, `k < d`, into the array `Q.a`. -/
theorem XV.tCopy {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {ap : ℕ} (hap : ap < L.NA) (hapQ : ap ≠ Q.a) (hd1 : 1 ≤ d) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1)
    {Nv : Fin d → ℤ} (hNv : ∀ i : Fin d, σ.arr ap (1 + (i : ℕ)) = Nv i) (bN : ∀ i, |(Nv i : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xtCopy L Q ap) σ (d * (1 + (2 + 2) + 3) + 3) (fun σ' =>
      (∀ i : Fin d, σ'.arr Q.a i = Nv i) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = Q.s + 16) (fun j => j = Q.n + 6 ∨ j = Q.n + 7) (fun b _ => b = Q.a) σ σ') := by
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, ⟨ha0, ha1⟩⟩ := hQ
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdasz : d ≤ asz d := by unfold asz; nlinarith
  let J : ℕ → Env d → Prop := fun k σ' => (∀ k' (h : k' < k) (hd : k' < d), σ'.arr Q.a k' = Nv ⟨k', hd⟩) ∧
    σ'.draws = σ.draws ∧
    FrameA (fun y => y = Q.s + 16) (fun j => j = Q.n + 6 ∨ j = Q.n + 7) (fun b _ => b = Q.a) σ σ'
  refine XV.mono (XV.forN hL (i := Q.n + 6) (n := rD) (one := rOne) (by omega) (by simp only [rD]; omega)
    (by simp only [rOne]; omega) (by simp only [rD]; omega) (by simp only [rOne]; omega) d (1 + (2 + 2))
    (by unfold asz at hda; nlinarith) J σ hD h1
    ⟨fun k' h => absurd h (Nat.not_lt_zero _), by simp, (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' h => ⟨fun i => h.1.1 i i.2 i.2, h.1.2.1, h.1.2.2⟩
  intro k hk σ' hJ hkk hkn hk1
  obtain ⟨hc, hdr, F⟩ := hJ
  have eA : ∀ j, σ'.arr ap j = σ.arr ap j := fun j => F.2.2.1 ap j hapQ
  have hr1 : rOne ≠ Q.n + 7 := by simp only [rOne]; omega
  have hrD : rD ≠ Q.n + 7 := by simp only [rD]; omega
  refine XV.seq (XV.nadd hL (σ := σ') (i := Q.n + 7) (a := Q.n + 6) (b := rOne) (by omega) (by omega)
    (by simp only [rOne]; omega) (by rw [hkk]; omega) (by rw [hk1]; omega)) fun σ1 e1 => ?_
  have r7 : σ1.nat (Q.n + 7) = 1 + k := by rw [e1, Env.setNat_nat, ite_eq_left rfl, hkk, hk1]; omega
  have v1 : σ1.arr ap (1 + k) = Nv ⟨k, hk⟩ := by rw [e1, Env.setNat_arr, eA]; exact hNv ⟨k, hk⟩
  refine XV.seq (XV.aget hL (σ := σ1) (x := Q.s + 16) (a := ap) (i := Q.n + 7) (by omega) hap (by omega)
    (by rw [r7]; exact le_asz' hd1 (by omega)) (by rw [r7, v1]; exact bN _)) fun σ2 e2 => ?_
  have v2 : σ2.sc (Q.s + 16) = Nv ⟨k, hk⟩ := by rw [e2]; simp [r7, v1]
  have n2 : σ2.nat (Q.n + 6) = k := by rw [e2, e1]; simp [hkk]
  refine XV.mono (XV.aset hL (σ := σ2) (a := Q.a) (i := Q.n + 6) (x := Q.s + 16) (by omega) (by omega) (by omega)
    (by rw [n2]; exact le_asz' hd1 (by omega)) (by rw [v2]; exact bN _)) le_rfl fun σ3 e3 => ?_
  have F2 : FrameA (fun y => y = Q.s + 16) (fun j => j = Q.n + 6 ∨ j = Q.n + 7) (fun b _ => b = Q.a) σ σ2 := by
    rw [e2, e1]; exact (F.setNat (Or.inr rfl) _).setSc rfl _
  subst e3
  refine ⟨by rw [Env.setArr_nat, e2, e1]; simp [hkk], by rw [Env.setArr_nat, e2, e1]; simp [hkn, hrD],
    by rw [Env.setArr_nat, e2, e1]; simp [hk1, hr1], fun k' hk' hd' => ?_, by
      rw [Env.setNat_draws, Env.setArr_draws, e2, e1]; simp [hdr], ?_⟩
  · simp only [Env.setNat_arr, Env.setArr_arr, n2]
    by_cases hkj : k' = k
    · subst hkj; simp [v2]
    · rw [ite_eq_right (fun h => hkj h.2), e2, e1]
      simp only [Env.setSc_arr, Env.setNat_arr]
      exact hc k' (by omega) hd'
  · exact (F2.setArr rfl _).setNat (Or.inl rfl) _

set_option maxHeartbeats 4000000 in
/-- **The position map**: for the point `(D; N)` in the array `ap`, the array `Q.a + 2` gets `D_S D` in cell `0` and
`μ̂_S D + Â_S N` in the cells `1, ..., d`. -/
theorem XV.tMap {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L)
    {ap : ℕ} (hap : ap < L.NA) (hapQ : ap < Q.a ∨ Q.a + 4 ≤ ap) (hd1 : 1 ≤ d)
    {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {D : ℤ} {Nv : Fin d → ℤ} {m bt : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hds : σ.sc sDS = DS)
    (hmu : ∀ i : Fin d, σ.arr aMuS i = muS i) (has : ∀ i j : Fin d, σ.arr aAS (d * i + j) = aS i j)
    (hap0 : σ.arr ap 0 = D) (hNv : ∀ i : Fin d, σ.arr ap (1 + (i : ℕ)) = Nv i)
    (bDS : |DS| ≤ 2 ^ m) (bmu : ∀ i, |muS i| ≤ 2 ^ m) (baS : ∀ i j, |aS i j| ≤ 2 ^ m) (hdm : d ≤ 2 ^ m)
    (bD : |D| ≤ 2 ^ bt) (bNv : ∀ i, |Nv i| ≤ 2 ^ bt) (hℓ : 4 * m + 2 * bt + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xtMap L Q ap) σ ((d * (1 + (2 + 2) + 3) + 3) + ((d * (d * 10 + 9) + 4) +
      (1 + (2 + (1 + (2 + (1 + (d * ((ieMap Q).units + 6) + 3))))))))
      (fun σ' => σ'.arr (Q.a + 2) 0 = DS * D ∧
        (∀ i : Fin d, σ'.arr (Q.a + 2) (1 + (i : ℕ)) = muS i * D + (aS *ᵥ Nv) i) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => Q.s + 16 ≤ y) (fun j => Q.n + 6 ≤ j ∧ j < Q.n + 11) (fun b _ => Q.a ≤ b ∧ b < Q.a + 3)
          σ σ') := by
  have hQ' := hQ
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, ⟨ha0, ha1⟩⟩ := hQ'
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdasz : d ≤ asz d := by unfold asz; nlinarith
  have hdl : ∀ k < d, k < asz d := fun k hk => le_asz' hd1 hk.le
  set S : ℕ → Prop := fun y => Q.s + 16 ≤ y with hS
  set N : ℕ → Prop := fun j => Q.n + 6 ≤ j ∧ j < Q.n + 11 with hN
  set Ar : ℕ → ℕ → Prop := fun b _ => Q.a ≤ b ∧ b < Q.a + 3 with hAr
  have hlt : ∀ {z : ℤ} {a : ℕ}, |z| ≤ 2 ^ a → a < ℓ → |(z : ℝ)| < 2 ^ ℓ := fun h ha => int_lt_of_le h ha
  -- the copy
  refine XV.seq (XV.tCopy hL hQ hap (by omega) hd1 hD h1 hNv (fun i => hlt (bNv i) (by omega)))
    fun σ1 ⟨c1, d1, F1⟩ => ?_
  have G1 : FrameA S N Ar σ σ1 := F1.mono (fun y h => by simp only [hS]; omega)
    (fun j h => by simp only [hN]; omega) (fun b _ h => by simp only [hAr]; omega)
  -- `y = Â_S N`
  set E := m + bt with hE
  have bM : ∀ i k, |aS i k| ≤ 2 ^ E := fun i k => (baS i k).trans (pow_le_pow_z (by omega))
  have bx : ∀ k, |Nv k| ≤ 2 ^ E := fun k => (bNv k).trans (pow_le_pow_z (by omega))
  have hdℓ : d * 2 ^ (2 * E) < 2 ^ ℓ := by
    calc d * 2 ^ (2 * E) ≤ 2 ^ m * 2 ^ (2 * E) := Nat.mul_le_mul_right _ hdm
      _ = 2 ^ (m + 2 * E) := by rw [pow_add]
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine XV.seq (XV.matvec hL (z := sZ) (r := Q.s + 19) (t := Q.s + 20) (aM := aAS) (ax := Q.a) (ay := Q.a + 1)
    (ni := Q.n + 8) (nr := Q.n + 9) (nk := Q.n + 10) (nd := rD) (none := rOne) (E := E) (M := aS) (x := Nv)
    (by simp only [sZ]; omega) (by omega) (by simp only [sZ]; omega) (by omega)
    (by rw [G1.2.1 _ (by simp only [hS, sZ]; omega), hz]) (by simp only [aAS]; omega) (by omega) (by omega)
    (by simp only [aAS]; omega) (by omega) (by omega) (by omega) (by omega) (by simp only [rD]; omega)
    (by simp only [rOne]; omega)
    (by simp only [rD, rOne]
        exact List.nodup_cons.2 ⟨by simp, List.nodup_cons.2 ⟨by simp, List.nodup_cons.2 ⟨by simp,
          List.nodup_cons.2 ⟨by simp, List.nodup_singleton _⟩⟩⟩⟩)
    (by rw [G1.1 _ (by simp only [hN, rD]; omega), hD]) (by rw [G1.1 _ (by simp only [hN, rOne]; omega), h1])
    (fun i k => by rw [G1.2.2.1 _ _ (by simp only [hAr, aAS]; omega), has]) c1 bM bx (by omega) hdℓ)
    fun σ2 ⟨y2, d2, F2⟩ => ?_
  have G2 : FrameA S N Ar σ σ2 := G1.trans (F2.mono (fun y h => by simp only [hS]; omega)
    (fun j h => by simp only [hN]; omega) (fun b _ h => by simp only [hAr]; omega))
  have eap : ∀ j, σ2.arr ap j = σ.arr ap j := fun j => G2.2.2.1 ap j (by simp only [hAr]; omega)
  -- `D`, `D_S D`
  refine XV.seq (XV.nconst hL (σ := σ2) (i := Q.n + 6) (by omega) 0 (by omega)) fun σ3 e3 => ?_
  have n3 : σ3.nat (Q.n + 6) = 0 := by rw [e3]; simp
  refine XV.seq (XV.aget hL (σ := σ3) (x := Q.s + 17) (a := ap) (i := Q.n + 6) (by omega) hap (by omega)
    (by rw [n3]; exact hdl 0 (by omega)) (by rw [n3, e3, Env.setNat_arr, eap, hap0]; exact hlt bD (by omega)))
    fun σ4 e4 => ?_
  have v4 : σ4.sc (Q.s + 17) = D := by rw [e4, n3, e3]; simp [eap, hap0]
  have s4 : σ4.sc sDS = DS := by
    rw [e4, Env.setSc_sc, ite_eq_right (by simp only [sDS]; omega), e3, Env.setNat_sc, G2.2.1 _ (by simp only [hS, sDS]; omega),
      hds]
  have bDSD : |DS * D| ≤ 2 ^ (m + bt) := absI_mul_le bDS bD
  refine XV.seq (XV.mulI hL (σ := σ4) (x := Q.s + 18) (a := sDS) (b := Q.s + 17) (by omega)
    (by simp only [sDS]; omega) (by omega) s4 v4 (lt_of_le_of_lt bDS (pow_lt_pow_z (by omega)))
    (lt_of_le_of_lt bD (pow_lt_pow_z (by omega))) (lt_of_le_of_lt bDSD (pow_lt_pow_z (by omega)))) fun σ5 e5 => ?_
  have n5 : σ5.nat (Q.n + 6) = 0 := by rw [e5, e4]; simp [n3]
  have hv5 : |σ5.sc (Q.s + 18)| < 2 ^ ℓ := by rw [e5]; simp only [Env.setSc_sc, ite_eq_left]; exact hlt bDSD (by omega)
  refine XV.seq (XV.aset hL (σ := σ5) (a := Q.a + 2) (i := Q.n + 6) (x := Q.s + 18) (by omega) (by omega)
    (by omega) (by rw [n5]; exact hdl 0 (by omega)) hv5) fun σ6 e6 => ?_
  have a6 : σ6.arr (Q.a + 2) 0 = DS * D := by rw [e6, n5, e5]; simp
  refine XV.seq (XV.nconst hL (σ := σ6) (i := Q.n + 9) (by omega) 1 (by omega)) fun σ7 e7 => ?_
  have G7 : FrameA S N Ar σ σ7 := by
    rw [e7, e6, e5, e4, e3]
    exact (((((G2.setNat (by simp only [hN]; omega) _).setSc (by simp only [hS]; omega) _).setSc
      (by simp only [hS]; omega) _).setArr (by simp only [hAr]; omega) _).setNat (by simp only [hN]; omega) _)
  have dd7 : σ7.draws = σ.draws := by rw [e7, e6, e5, e4, e3]; simp [d2, d1]
  have q7 : σ7.sc (Q.s + 17) = D := by rw [e7, e6, e5]; simp [v4]
  have y7 : ∀ k : Fin d, σ7.arr (Q.a + 1) k = (aS *ᵥ Nv) k := fun k => by
    rw [e7, e6]; simp only [Env.setNat_arr, Env.setArr_arr]
    rw [ite_eq_right (by omega), e5, e4, e3]; simp only [Env.setSc_arr, Env.setNat_arr]; exact y2 k
  have mu7 : ∀ k : Fin d, σ7.arr aMuS k = muS k := fun k => by
    rw [G7.2.2.1 _ _ (by simp only [hAr, aMuS]; omega), hmu]
  -- the numerators
  set E2 := 2 * m + bt with hE2
  have by7 : ∀ k : Fin d, |(aS *ᵥ Nv) k| ≤ 2 ^ E2 := fun k => by
    have := mulVec_abs_le (a := m) (b := bt) (c := m) baS bNv hdm k
    exact this.trans (pow_le_pow_z (by omega))
  set F : ℕ → ℤ := fun k => if h : k < d then muS ⟨k, h⟩ * D + (aS *ᵥ Nv) ⟨k, h⟩ else 0 with hF
  refine XV.mono (XV.mapE hL (σ := σ7) (z := sZ) (t := Q.s + 24) (e := ieMap Q) (aB := Q.a + 2) (nr := Q.n + 9)
    (nst := rOne) (nk := Q.n + 10) (nn := rD) (none := rOne) (E := E2) (N := d) (base := 1) (st := 1) (F := F)
    (by simp only [ieMap, IE.WF, aMuS, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by simp only [sZ]; omega) (by simp only [ieMap, IE.scr]; omega)
    (by rw [G7.2.1 _ (by simp only [hS, sZ]; omega), hz]) (by omega) (by omega) (by simp only [rOne]; omega)
    (by omega) (by simp only [rD]; omega) (by simp only [rOne]; omega)
    (by simp only [rD, rOne]
        exact List.nodup_cons.2 ⟨by simp, List.nodup_cons.2 ⟨by simp,
          List.nodup_cons.2 ⟨by simp, List.nodup_singleton _⟩⟩⟩)
    (by simp only [rOne]; omega) (by simp only [rOne]; omega)
    (by rw [G7.1 _ (by simp only [hN, rD]; omega), hD]) (by rw [G7.1 _ (by simp only [hN, rOne]; omega), h1])
    (by rw [e7]; simp) (by rw [G7.1 _ (by simp only [hN, rOne]; omega), h1]) one_pos
    (fun k hk => le_asz' hd1 (by omega)) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by omega) (by simp only [ieMap, IE.top, IE.mag]; omega) ?_) (le_refl _) fun σ8 ⟨a8, _, d8, F8⟩ => ?_
  · intro k hk σ' F' dd' hk' hr'
    have hk1 : 1 + 1 * k < asz d := le_asz' hd1 (by omega)
    have eD : σ'.sc (Q.s + 17) = D := by rw [F'.2.1 _ (by omega), q7]
    have eMu : σ'.arr aMuS k = muS ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by simp only [aMuS]; omega)]; exact mu7 ⟨k, hk⟩
    have eY : σ'.arr (Q.a + 1) k = (aS *ᵥ Nv) ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega)]; exact y7 ⟨k, hk⟩
    refine ⟨⟨⟨⟨by rw [hk']; exact hdl k hk, muS ⟨k, hk⟩, by rw [hk', eMu],
      (bmu _).trans (pow_le_pow_z (by omega))⟩, D, eD, bD.trans (pow_le_pow_z (by omega))⟩,
      by rw [hk']; exact hdl k hk, (aS *ᵥ Nv) ⟨k, hk⟩, by rw [hk', eY], by7 _⟩, ?_⟩
    simp only [IE.eval, ieMap, RealRAM.Op2.eval, hk', eMu, eD, eY, hF, dite_eq_left hk]
    push_cast; ring
  · refine ⟨by rw [F8.2.2.1 _ _ (by omega), e7, Env.setNat_arr, a6], fun i => ?_, by rw [d8, dd7], ?_⟩
    · have := a8 i i.2
      simp only [one_mul, hF, dite_eq_left i.2] at this
      rw [this]; push_cast; simp only [Fin.eta]
    · exact G7.trans (F8.mono (fun y h => by simp only [hS]; omega) (fun j h => by simp only [hN, rD, rOne] at *; omega)
        (fun b _ h => by simp only [hAr]; omega))

theorem cmLayQ_OK {L : Layout} {Q : TstLay} (hQ : Q.OK L) : CMLay.OKU L (cmLayQ Q) := by
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, ⟨ha0, ha1⟩⟩ := hQ
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_⟩ <;>
    simp only [cmLayQ, aC] <;> omega

set_option maxHeartbeats 4000000 in
/-- **The test block** (`TestOK`): from the data `TstDat` (the position `D_S, μ̂_S, Â_S`, the centre `Na/Da` in `aC`,
`r₀ = rn/rd`, the precision `k` and `2^k`), for every point `(D; N)` in the array `ap` below `2^bt`, `xtst` writes
into the register `nt` the CM test at the position map of `N/D`; every datum below `2^m`. -/
theorem tstOK {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {Q : TstLay} (hQ : Q.OK L) {ap nt : ℕ}
    (hap : ap < L.NA) (hapQ : ap < Q.a ∨ Q.a + 4 ≤ ap) (hnt : nt < L.NN) (hnt8 : 8 ≤ nt)
    (hntQ : nt < Q.n ∨ Q.n + 16 ≤ nt) (hd1 : 1 ≤ d)
    {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {k m bt : ℕ}
    (hDS : 0 < DS) (bDS : DS ≤ 2 ^ m) (bmu : ∀ i, |muS i| ≤ 2 ^ m) (baS : ∀ i j, |aS i j| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hDa : 0 < Da) (bDa : Da < 2 ^ m) (bNa : ∀ i, |Na i| < 2 ^ m) (hrn : 0 < rn)
    (brn : rn < 2 ^ m) (hrd : 0 < rd) (brd : rd < 2 ^ m) (hℓ : 6 * m + 2 * bt + k + 12 ≤ ℓ) (hk : k < 2 ^ ℓa) :
    Uni.TestOK L XO ℓa ℓ (xtst L Q ap nt) (TstDat Q DS muS aS Da Na rn rd k) ap nt bt
      (fun y => cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (pmap DS muS aS y)) (tstK d)
      (fun y => Q.s + 16 ≤ y) (fun j => j = nt ∨ (Q.n + 1 ≤ j ∧ j < Q.n + 11))
      (fun b _ => Q.a ≤ b ∧ b < Q.a + 4) := by
  intro σ D Nv hdat hD0 hDb hNvb hD hNv
  have hQ' := hQ
  obtain ⟨⟨hs0, hs1⟩, ⟨hn0, hn1⟩, ⟨ha0, ha1⟩⟩ := hQ'
  have hL1 := hL.1
  have bD : |D| ≤ 2 ^ bt := by rw [abs_of_pos hD0]; exact hDb.le
  have bNv : ∀ i, |Nv i| ≤ 2 ^ bt := fun i => (hNvb i).le
  have bDS' : |DS| ≤ 2 ^ m := by rw [abs_of_pos hDS]; exact bDS
  refine XVO.mono (K := ((d * (1 + (2 + 2) + 3) + 3) + ((d * (d * 10 + 9) + 4) +
      (1 + (2 + (1 + (2 + (1 + (d * ((ieMap Q).units + 6) + 3)))))))) + (cmK d + (1 + 1))) ?_
    (by unfold tstK; simp only [ieMap, IE.units]; omega) fun _ h => h
  refine XVO.seq (XVO.ofX (XV.tMap hL hQ hap hapQ hd1 (m := m) (bt := bt) hdat.hd hdat.h1 hdat.hz hdat.hds hdat.hmu
    hdat.has hD hNv bDS' bmu baS hdm bD bNv (by omega))) fun σ1 h1 => ?_
  obtain ⟨a0, a1, d1, F1⟩ := h1
  -- the CM block
  set bt' := 2 * m + bt + 2 with hbt'
  set Nz : Fin d → ℤ := fun i => muS i * D + (aS *ᵥ Nv) i with hNz
  have hDD : 0 < DS * D := mul_pos hDS hD0
  have bDD : DS * D < 2 ^ bt' := by
    calc DS * D ≤ 2 ^ m * 2 ^ bt := mul_le_mul bDS hDb.le hD0.le (by positivity)
      _ = 2 ^ (m + bt) := by rw [pow_add]
      _ < 2 ^ bt' := pow_lt_pow_z (by omega)
  have bNz : ∀ i, |Nz i| < 2 ^ bt' := fun i => by
    have h1 : |muS i * D| ≤ 2 ^ (2 * m + bt) := (absI_mul_le (bmu i) bD).trans (pow_le_pow_z (by omega))
    have h2 : |(aS *ᵥ Nv) i| ≤ 2 ^ (2 * m + bt) := by
      have := mulVec_abs_le (a := m) (b := bt) (c := m) baS bNv hdm i
      exact this.trans (pow_le_pow_z (by omega))
    calc |Nz i| ≤ |muS i * D| + |(aS *ᵥ Nv) i| := abs_add_le _ _
      _ ≤ 2 ^ (2 * m + bt) + 2 ^ (2 * m + bt) := add_le_add h1 h2
      _ = 2 ^ (2 * m + bt + 1) := by ring
      _ < 2 ^ bt' := pow_lt_pow_z (by omega)
  have hcm : CMDatU (cmLayQ Q) Da Na rn rd k σ1 := by
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hdat.hcm
    refine ⟨⟨?_, fun i => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [F1.2.2.1 _ _ (by simp only [cmLayQ, aC]; omega)]; exact c0
    · rw [F1.2.2.1 _ _ (by simp only [cmLayQ, aC]; omega)]; exact c1 i
    · rw [F1.2.1 _ (by simp only [cmLayQ]; omega)]; exact c2
    · rw [F1.2.1 _ (by simp only [cmLayQ]; omega)]; exact c3
    · rw [F1.1 _ (by simp only [cmLayQ]; omega)]; exact c4
    · rw [F1.2.1 _ (by simp only [cmLayQ]; omega)]; exact c5
    · rw [F1.1 _ (by omega)]; exact hdat.hd
  refine XVO.seq (cmBlockOKU L XO ℓa ℓ (cmLayQ Q) Da Na rn rd k m bt' hL (cmLayQ_OK hQ) hd1 hDa hrn hrd bDa bNa brn
    brd (by omega) hk σ1 (DS * D) Nz hcm hDD bDD bNz (by simpa [cmLayQ] using a0)
    (fun i => by show σ1.arr (Q.a + 2) (1 + (i : ℕ)) = _; rw [a1 i, hNz]; push_cast; ring)) fun σ2 h2 => ?_
  obtain ⟨t2, F2, d2⟩ := h2
  -- the answer
  have hn1' : Q.n + 1 ≠ nt := by omega
  have ht2 : σ2.nat (Q.n + 1) = if cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (ptDN (DS * D) Nz) then 1 else 0 :=
    t2
  have t2b : σ2.nat (Q.n + 1) ≤ 1 := by rw [ht2]; split_ifs <;> omega
  refine XVO.ofX (XV.seq (XV.nconst hL (σ := σ2) (i := nt) hnt 0 (by omega)) fun σ3 e3 => ?_)
  subst e3
  have hva : (σ2.setNat nt 0).nat nt < 2 ^ ℓa := by rw [Env.setNat_nat, ite_eq_left rfl]; positivity
  have hvb : (σ2.setNat nt 0).nat (Q.n + 1) < 2 ^ ℓa := by rw [Env.setNat_nat, ite_eq_right hn1']; omega
  refine XV.mono (XV.nadd hL (i := nt) (a := nt) (b := Q.n + 1) hnt hnt (by omega) hva hvb) le_rfl
    fun σ4 e4 => ?_
  subst e4
  refine ⟨?_, ?_, ?_⟩
  · simp only [Env.setNat_nat, ite_eq_left, ite_eq_right hn1', ht2, zero_add]
    rw [hNz, pmap_eq DS D muS aS Nv hDS.ne' hD0.ne']
  · have G2 : FrameA (fun y => Q.s + 16 ≤ y) (fun j => j = nt ∨ (Q.n + 1 ≤ j ∧ j < Q.n + 11))
        (fun b _ => Q.a ≤ b ∧ b < Q.a + 4) σ σ2 :=
      (F1.mono (fun y h => h) (fun j h => Or.inr ⟨by omega, by omega⟩) (fun b _ h => ⟨h.1, by omega⟩)).trans
        (F2.mono (fun y h => by simp only [cmS, cmLayQ] at h; omega)
          (fun j h => by simp only [cmN, cmLayQ] at h; omega) (fun b _ h => by simp only [cmAr, cmLayQ] at h; omega))
    exact (G2.setNat (Or.inl rfl) _).setNat (Or.inl rfl) _
  · simp [d2, d1]

/-! ## The link with BL-O's test and precision -/

/-- The CM test at the position map is BL-O's test `c.T orc k 1` when the cells hold `c`'s position, centre and
`r₀`. -/
theorem pmap_T (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) {DS : ℤ} {muS : Fin d → ℤ}
    {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} (hDS : 0 < DS)
    (hmu : ∀ j, (muS j : ℚ) / DS = c.μS j) (haS : ∀ i j, (aS i j : ℚ) / DS = c.AS i j)
    (ha : ptDN Da Na = c.a) (hr : (rn : ℚ) / rd = c.r0) (k : ℕ) (y : Fin d → ℚ) :
    cmQ orc (ptDN Da Na) ((rn : ℚ) / rd) k (pmap DS muS aS y) = c.T orc k 1 y := by
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have e : pmap DS muS aS y = c.μS + c.AS *ᵥ ((1 : ℚ) • y) := by
    funext i
    simp only [pmap, Pi.add_apply, one_smul, mulVec, dotProduct, ← hmu, ← haS]
    rw [add_div, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, ha, hr]
  rfl

/-- `⌈N/D⌉ = -((-N) div D)` for `D > 0`. -/
theorem ceil_div_int {N D : ℤ} (hD : 0 < D) : ⌈(N : ℚ) / D⌉ = 0 - (0 - N) / D := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hD.le
  rw [Int.cast_natCast, Rat.ceil_intCast_div_natCast, zero_sub, zero_sub]

/-- BL-O's CM precision `kC` is `cmcK` at the integers of `R' = R̂/2^pF`, `R₀` and `r₀`. -/
theorem kC_eq (c : CfgO d) (hR : OnG c.par.pF c.par.R) (hr0 : 0 < c.r0) :
    c.kC = cmcK c.par.p (6 * qn c.par.pF c.par.R * c.R0.num * c.r0.den * c.r0.den)
      (2 ^ c.par.pF * c.R0.den * c.r0.num * c.r0.num) := by
  have hn : 0 < c.r0.num := Rat.num_pos.2 hr0
  have hD : (0 : ℤ) < 2 ^ c.par.pF * c.R0.den * c.r0.num * c.r0.num := by positivity
  have hx : 6 * c.par.R * c.R0 / c.r0 ^ 2 =
      ((6 * qn c.par.pF c.par.R * c.R0.num * c.r0.den * c.r0.den : ℤ) : ℚ) /
        ((2 ^ c.par.pF * c.R0.den * c.r0.num * c.r0.num : ℤ) : ℚ) := by
    have h1 : (c.r0.num : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have h2 : (c.R0.den : ℚ) ≠ 0 := by positivity
    have h3 : (c.r0.den : ℚ) ≠ 0 := by positivity
    conv_lhs => rw [eq_qn_div _ hR, ← Rat.num_div_den c.R0, ← Rat.num_div_den c.r0]
    push_cast
    field_simp
  unfold CfgO.kC CfgO.kK cmcK
  rw [hx, ← Int.ceil_toNat, ceil_div_int hD]

end AdversarialBco.Unified.ProgO
