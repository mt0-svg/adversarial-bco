/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk4
public import AdversarialBco.Unified.PolyRowMem

@[expose] public section

/-!
# UNI-POLY, part 8: the body and the loop of `ROWMEM`

* `rs_ROWBODY`: one row, `cR := 0` if its test `S dn_d ≤ nm_d Q Y_0` fails.
* `rs_ROWMEM`: `cR := rowR`, `1` if every row passes, `0` otherwise.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

/-- The entry `num/den` of the last column. -/
theorem rowD1 {u : State d} {E a1 a2 : ℤ} (fE : u.mem cE = E) (fOne : u.mem cOne = 1)
    (fN : u.mem E = a1) (fD : u.mem (E + 1) = a2) (hE3 : 3 ≤ E)
    (lE : len E ≤ L) (lE1 : len (E + 1) ≤ L) (l1 : len a1 ≤ L) (l2 : len a2 ≤ L) (h10 : 10 ≤ L) :
    OKI w L [.load cN cE, .add cE1 cE cOne, .load cDD cE1] u ∧
      (runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1] u).mem =
        Function.update (Function.update (Function.update u.mem cN a1) cE1 (E + 1)) cDD a2 := by
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [fE]; exact lE,
      by rw [fE, fN]; exact l1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fE]; exact lE, by evl; rw [fOne]; exact h1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fE, fOne]; exact lE1, by evl; rw [fE, fOne, fD]; exact l2⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_load_mem, stepI_add_mem]
  evl
  simp only [fE, fOne, fN, fD]

/-- `Y_0`, `L := S dn_d`, `Rt := nm_d Q Y_0`. -/
theorem rowD2 {u : State d} {YB y0 S Q a1 a2 : ℤ} (fYB : u.mem cYB = YB) (fY0 : u.mem YB = y0)
    (fS : u.mem cS = S) (fD : u.mem cDD = a2) (fN : u.mem cN = a1) (fQ : u.mem cQ = Q) (hYB0 : 0 ≤ YB)
    (lYB : len YB ≤ L) (ly0 : len y0 ≤ L) (lS : len S ≤ L) (l2 : len a2 ≤ L) (l1 : len a1 ≤ L) (lQ : len Q ≤ L)
    (l1Q : len (a1 * Q) ≤ L) (h10 : 10 ≤ L) :
    OKI w L [.load cY0 cYB, .mul cL cS cDD, .mul cRt cN cQ, .mul cRt cRt cY0] u ∧
      (runI w [.load cY0 cYB, .mul cL cS cDD, .mul cRt cN cQ, .mul cRt cRt cY0] u).mem =
        Function.update (Function.update (Function.update (Function.update u.mem cY0 y0) cL (S * a2)) cRt (a1 * Q))
          cRt (a1 * Q * y0) := by
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [fYB]; exact lYB,
      by rw [fYB, fY0]; exact ly0⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fS]; exact lS, by evl; rw [fD]; exact l2⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fN]; exact l1, by evl; rw [fQ]; exact lQ⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fN, fQ]; exact l1Q, by evl; rw [fYB, fY0]; exact ly0⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_load_mem, stepI_mul_mem]
  evl
  simp only [fYB, fY0, fS, fD, fN, fQ]

set_option maxHeartbeats 1000000 in
/-- The body of `ROWMEM` on row `i`: `cR := 0` if the row fails, the row pointer and the row counter move on. -/
theorem rs_ROWBODY {v0 : State d} {i : ℕ} {YB M B r : ℤ} {nm dn Y : ℕ → ℤ} (hYB0 : 0 ≤ YB)
    (hYB : v0.mem cYB = YB) (hE : v0.mem cE = 3 + 2 * (((d : ℤ) + 1) * i)) (hOne : v0.mem cOne = 1)
    (hI : v0.mem cI = i) (hR : v0.mem cR = r) (hd : v0.mem 0 = d)
    (hS : v0.mem cS = 0) (hQ : v0.mem cQ = 0) (hJ : v0.mem cJ = 0) (hYP : v0.mem cYP = 0)
    (hN : v0.mem cN = 0) (hE1 : v0.mem cE1 = 0) (hDD : v0.mem cDD = 0) (hY : v0.mem cY = 0) (hT : v0.mem cT = 0)
    (hY0 : v0.mem cY0 = 0) (hL : v0.mem cL = 0) (hRt : v0.mem cRt = 0)
    (hnm : ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j)) = nm j)
    (hdn : ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = dn j)
    (hYv : ∀ j : ℕ, j ≤ d → v0.mem (YB + j) = Y j)
    (hM1 : 1 ≤ M) (hB : 1 ≤ B) (hMb : ∀ j : ℕ, j ≤ d → |nm j| ≤ M ∧ 0 < dn j ∧ dn j ≤ M)
    (hYb : ∀ j : ℕ, j ≤ d → |Y j| ≤ B)
    (hLV : ((d : ℤ) + 1) * M ^ (d + 1) * B < 2 ^ L)
    (hLA : 3 + 2 * (((d : ℤ) + 1) * i + d) + 2 < 2 ^ L) (hLY : YB + d + 1 < 2 ^ L) (hLi : (i : ℤ) + 1 < 2 ^ L)
    (h10 : 10 ≤ L) :
    RS w L ROWBODY v0 (fun n v => n ≤ d * 19 + 27 ∧
      v.mem = Function.update (Function.update (Function.update v0.mem cR
        (if rowT d nm dn Y then r else 0)) cE (3 + 2 * (((d : ℤ) + 1) * (i + 1)))) cI (i + 1) ∧ Same' v0 v) := by
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hnat : ∀ x : ℤ, 0 ≤ x → x < 2 ^ L → len x ≤ L := fun x h0 hx =>
    len_of_abs (by rw [abs_of_nonneg h0]) hx
  have hX : (0 : ℤ) ≤ ((d : ℤ) + 1) * i := by positivity
  set Ed : ℤ := 3 + 2 * (((d : ℤ) + 1) * i + d) with hEdd
  have hEd3 : 3 ≤ Ed := by rw [hEdd]; omega
  have hpow : ∀ j ≤ d + 1, M ^ j ≤ M ^ (d + 1) := fun j hj => pow_le_pow_right₀ hM1 hj
  set V : ℤ := ((d : ℤ) + 1) * M ^ (d + 1) * B with hVd
  have hV : ∀ (a e : ℕ), a ≤ d + 1 → e ≤ d + 1 → (a : ℤ) * M ^ e * B ≤ V := fun a e ha he => by
    have h1 : (a : ℤ) ≤ (d : ℤ) + 1 := by omega
    have h2 := hpow e he
    have : (a : ℤ) * M ^ e ≤ ((d : ℤ) + 1) * M ^ (d + 1) := mul_le_mul h1 h2 (by positivity) (by omega)
    exact mul_le_mul_of_nonneg_right this (by omega)
  have lV : ∀ x : ℤ, |x| ≤ V → len x ≤ L := fun x hx => len_of_abs hx hLV
  set Sd := (rowSQ nm dn Y d).1 with hSd
  set Qd := (rowSQ nm dn Y d).2 with hQd
  obtain ⟨bS, bQ0, bQ⟩ := rowSQ_bound (nm := nm) (dn := dn) (Y := Y) (j := d) hM1 (by omega)
    (fun k hk => hMb k (by omega)) (fun k hk => hYb (1 + k) (by omega))
  obtain ⟨bn, bd0, bd⟩ := hMb d le_rfl
  have bY := hYb 0 (by omega)
  have lS : len Sd ≤ L := lV _ (bS.trans (hV d d (by omega) (by omega)))
  have lQ : len Qd ≤ L := lV _ (by
    rw [abs_of_pos bQ0]
    have := hV 1 d (by omega) (by omega)
    have : M ^ d ≤ (1 : ℕ) * M ^ d * B := by
      simp only [Nat.cast_one, one_mul]; exact le_mul_of_one_le_right (by positivity) hB
    omega)
  have bM : M ≤ V := by
    have := hV 1 1 (by omega) (by omega)
    have : M ≤ (1 : ℕ) * M ^ 1 * B := by simp only [Nat.cast_one, one_mul, pow_one]; nlinarith
    omega
  have lN : len (nm d) ≤ L := lV _ (bn.trans bM)
  have lD : len (dn d) ≤ L := lV _ (by rw [abs_of_pos bd0]; exact bd.trans bM)
  have lY0 : len (Y 0) ≤ L := lV _ (bY.trans (by
    have := hV 1 0 (by omega) (by omega); simp only [Nat.cast_one, one_mul, pow_zero] at this; exact this))
  have bD : |dn d| ≤ M := by rw [abs_of_pos bd0]; exact bd
  have bQ' : |Qd| ≤ M ^ d := by rw [abs_of_pos bQ0]; exact bQ
  have bSD : |Sd * dn d| ≤ V := (abs_mul_le bS bD).trans (by
    have := hV d (d + 1) (by omega) (by omega)
    calc (d : ℤ) * M ^ d * B * M = (d : ℤ) * M ^ (d + 1) * B := by ring
      _ ≤ V := this)
  have bNQ : |nm d * Qd| ≤ V := (abs_mul_le bn bQ').trans (by
    have := hV 1 (d + 1) (by omega) (by omega)
    have hMB : M * M ^ d ≤ M * M ^ d * B := le_mul_of_one_le_right (by positivity) hB
    calc M * M ^ d ≤ M * M ^ d * B := hMB
      _ = ((1 : ℕ) : ℤ) * M ^ (d + 1) * B := by push_cast; ring
      _ ≤ V := this)
  have bNQY : |nm d * Qd * Y 0| ≤ V := (abs_mul_le (abs_mul_le bn bQ') bY).trans (by
    have := hV 1 (d + 1) (by omega) (by omega)
    calc M * M ^ d * B = ((1 : ℕ) : ℤ) * M ^ (d + 1) * B := by push_cast; ring
      _ ≤ V := this)
  have lEd : len Ed ≤ L := hnat Ed (by omega) (by omega)
  have lEd1 : len (Ed + 1) ≤ L := hnat _ (by omega) (by omega)
  have lYB : len YB ≤ L := hnat _ hYB0 (by omega)
  have li : len (i : ℤ) ≤ L := hnat _ (by omega) (by omega)
  unfold ROWBODY; simp only [seqL]
  -- `cS := 0`, `cQ := 1`, `cJ := 0`, `cYP := YB + 1`
  refine RS.seq (rs_seqI (is := [.const cS 0, .const cQ 1, .const cJ 0, .add cYP cYB cOne]) (t := v0)
    ⟨⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, h1⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [hYB]; exact lYB, by evl; rw [hOne]; exact h1⟩, trivial⟩) ?_
  rintro n₁ t₁ ⟨hn₁, rfl⟩
  have m1 : (runI w [.const cS 0, .const cQ 1, .const cJ 0, .add cYP cYB cOne] v0).mem =
      Function.update (Function.update (Function.update (Function.update v0.mem cS 0) cQ 1) cJ 0) cYP (YB + 1) := by
    simp only [runI, stepI_add_mem, stepI_const_mem]; evl; rw [hYB, hOne]
  have s1 : Same' v0 (runI w [.const cS 0, .const cQ 1, .const cJ 0, .add cYP cYB cOne] v0) :=
    runI_same (by simp [Plain, NJ])
  set t₁ := runI w [.const cS 0, .const cQ 1, .const cJ 0, .add cYP cYB cOne] v0 with ht₁
  -- the columns
  refine RS.seq (rs_ROWIN (v0 := t₁) (i := i) (YB := YB) (M := M) (B := B) (nm := nm) (dn := dn) (Y := Y) hYB0
    (by rw [m1]; evl) (by rw [m1]; evl) (by rw [m1]; evl) (by rw [m1]; evl)
    (by rw [m1]; evl; exact hE) (by rw [m1]; evl; exact hOne) (by rw [m1]; evl; exact hd)
    (by rw [m1]; evl; exact hN) (by rw [m1]; evl; exact hE1) (by rw [m1]; evl; exact hDD)
    (by rw [m1]; evl; exact hY) (by rw [m1]; evl; exact hT)
    (fun j hj => by rw [m1]; evl; exact hnm j hj) (fun j hj => by rw [m1]; evl; exact hdn j hj)
    (fun j hj => by
      rw [m1]; evl
      have := hYv (1 + j) (by omega)
      rw [show YB + 1 + (j : ℤ) = YB + ((1 + j : ℕ) : ℤ) by push_cast; ring]; exact this)
    hM1 hB (fun j hj => hMb j hj) (fun j hj => hYb (1 + j) (by omega)) hLV hLA hLY h10) ?_
  rintro n₂ t₂ ⟨hn₂, hm₂, hs₂⟩
  rw [m1] at hm₂
  -- the test values
  have e1 : t₂.mem cE = Ed := by rw [hm₂]; evl; try rfl
  have e2 : t₂.mem Ed = nm d := by rw [hm₂]; evl; exact hnm d le_rfl
  have e3 : t₂.mem (Ed + 1) = dn d := by rw [hm₂]; evl; exact hdn d le_rfl
  have e4 : t₂.mem cOne = 1 := by rw [hm₂]; evl; exact hOne
  have e5 : t₂.mem cYB = YB := by rw [hm₂]; evl; exact hYB
  have e6 : t₂.mem cS = Sd := by rw [hm₂]; evl; try rfl
  have e7 : t₂.mem cQ = Qd := by rw [hm₂]; evl; try rfl
  have fY0 : t₂.mem YB = Y 0 := by
    rw [hm₂]; evl; have := hYv 0 (by omega); simp only [Nat.cast_zero, add_zero] at this; exact this
  obtain ⟨ok1, m1'⟩ := rowD1 (w := w) e1 e4 e2 e3 hEd3 lEd lEd1 lN lD h10
  set u1 := runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1] t₂ with hu1
  obtain ⟨ok2, m2'⟩ := rowD2 (w := w) (u := u1) (by rw [m1']; evl; exact e5) (by rw [m1']; evl; exact fY0)
    (by rw [m1']; evl; exact e6) (by rw [m1']; evl) (by rw [m1']; evl) (by rw [m1']; evl; exact e7) hYB0 lYB lY0
    lS lD lN lQ (lV _ bNQ) h10
  refine RS.seq (rs_seqI (OKI_append ok1 ok2)) ?_
  rintro n₃ t₃ ⟨hn₃, rfl⟩
  set F3 : ℤ → ℤ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update t₂.mem cN (nm d)) cE1 (Ed + 1)) cDD (dn d)) cY0 (Y 0)) cL (Sd * dn d))
    cRt (nm d * Qd)) cRt (nm d * Qd * Y 0) with hF3
  have m3 : (runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY0 cYB, .mul cL cS cDD,
      .mul cRt cN cQ, .mul cRt cRt cY0] t₂).mem = F3 := by
    rw [show ([.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY0 cYB, .mul cL cS cDD, .mul cRt cN cQ,
      .mul cRt cRt cY0] : List Instr) = [.load cN cE, .add cE1 cE cOne, .load cDD cE1] ++ [.load cY0 cYB,
      .mul cL cS cDD, .mul cRt cN cQ, .mul cRt cRt cY0] from rfl, runI_append, ← hu1, m2', m1']
  have s3 : Same' t₂ (runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY0 cYB, .mul cL cS cDD,
      .mul cRt cN cQ, .mul cRt cRt cY0] t₂) := runI_same (by simp [Plain, NJ])
  set t₃ := runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY0 cYB, .mul cL cS cDD,
      .mul cRt cN cQ, .mul cRt cRt cY0] t₂ with ht₃
  have e3R : t₃.mem cR = r := by rw [m3, hF3]; evl; rw [hm₂]; evl; exact hR
  have hTst : TestOK L cRt cL t₃ := ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
    by rw [m3, hF3]; evl; exact lV _ bNQY, by rw [m3, hF3]; evl; exact lV _ bSD⟩
  have e3Rt : t₃.mem cRt = nm d * Qd * Y 0 := by rw [m3, hF3]; evl
  have e3L : t₃.mem cL = Sd * dn d := by rw [m3, hF3]; evl
  -- the test
  refine RS.seq (Q₁ := fun n t₄ => n ≤ 2 ∧ t₄.mem = Function.update F3 cR (if rowT d nm dn Y then r else 0) ∧
    Same' t₃ t₄) ?_ ?_
  · by_cases hok : rowT d nm dn Y
    · refine RS.ifF hTst (by rw [e3Rt, e3L]; exact not_lt.2 hok) (RS.skip ?_)
      refine ⟨by omega, ?_, (Same'.addC _ _).trans (Same'.addC _ 1)⟩
      rw [addC_mem, addC_mem, ← m3, ite_eq_left hok, ← e3R, Function.update_eq_self]
    · refine RS.ifT hTst (by rw [e3Rt, e3L]; exact not_le.1 hok) ?_
      refine RS.ins ⟨len_scr (by decide) (by decide) h10, l0⟩
        ⟨by omega, ?_, (Same'.addC _ _).trans (stepI_same (by simp [Plain]) (by simp [NJ]))⟩
      rw [stepI_const_mem, addC_mem, m3, ite_eq_right hok]
  rintro n₄ t₄ ⟨hn₄, m4, hs₄⟩
  -- the pointers move on, the scratch cells end at `0`
  have e4E1 : t₄.mem cE1 = Ed + 1 := by rw [m4, hF3]; evl
  have e4One : t₄.mem cOne = 1 := by rw [m4, hF3]; evl; rw [hm₂]; evl; exact hOne
  have e4I : t₄.mem cI = i := by rw [m4, hF3]; evl; rw [hm₂]; evl; exact hI
  refine (rs_seqI (is := [.add cE cE1 cOne, .add cI cI cOne, .const cN 0, .const cE1 0, .const cDD 0, .const cY0 0,
      .const cL 0, .const cRt 0, .const cS 0, .const cQ 0, .const cJ 0, .const cYP 0]) (t := t₄)
    ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [e4E1]; exact lEd1, by rw [e4One]; exact h1⟩,
     ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [e4I]; exact li, by evl; rw [e4One]; exact h1⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
  rintro n v' ⟨hn, rfl⟩
  refine ⟨by simp at hn hn₁ hn₃; omega, ?_, ((((s1.trans hs₂).trans s3).trans hs₄).trans
    (runI_same (by simp [Plain, NJ])))⟩
  funext c
  simp only [runI, stepI_add_mem, stepI_const_mem]
  evl
  simp only [e4E1, e4One, e4I]
  rw [m4, hF3, hm₂]
  by_cases hc : -627 ≤ c ∧ c ≤ -600
  · obtain ⟨hc1, hc2⟩ := hc
    interval_cases c <;> evl <;> first | rfl | (symm; assumption) | (rw [hEdd]; ring)
  · evl

set_option maxHeartbeats 1000000 in
/-- `ROWMEM`: `cR := 1` if the point `Y` passes the test of every row `i < m`, `0` otherwise. -/
theorem rs_ROWMEM {v0 : State d} {m : ℕ} {YB M B : ℤ} {nm dn : ℕ → ℕ → ℤ} {Y : ℕ → ℤ} (hYB0 : 0 ≤ YB)
    (hYB : v0.mem cYB = YB) (hd : v0.mem 0 = d) (hm : v0.mem 2 = m)
    (hR : v0.mem cR = 0) (hOne : v0.mem cOne = 0) (hE : v0.mem cE = 0) (hI : v0.mem cI = 0)
    (hS : v0.mem cS = 0) (hQ : v0.mem cQ = 0) (hJ : v0.mem cJ = 0) (hYP : v0.mem cYP = 0)
    (hN : v0.mem cN = 0) (hE1 : v0.mem cE1 = 0) (hDD : v0.mem cDD = 0) (hY : v0.mem cY = 0) (hT : v0.mem cT = 0)
    (hY0 : v0.mem cY0 = 0) (hL : v0.mem cL = 0) (hRt : v0.mem cRt = 0)
    (hnm : ∀ i < m, ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j)) = nm i j)
    (hdn : ∀ i < m, ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = dn i j)
    (hYv : ∀ j : ℕ, j ≤ d → v0.mem (YB + j) = Y j)
    (hM1 : 1 ≤ M) (hB : 1 ≤ B) (hMb : ∀ i < m, ∀ j : ℕ, j ≤ d → |nm i j| ≤ M ∧ 0 < dn i j ∧ dn i j ≤ M)
    (hYb : ∀ j : ℕ, j ≤ d → |Y j| ≤ B)
    (hLV : ((d : ℤ) + 1) * M ^ (d + 1) * B < 2 ^ L)
    (hLA : 3 + 2 * (((d : ℤ) + 1) * m) < 2 ^ L) (hLY : YB + d + 1 < 2 ^ L) (hLm : (m : ℤ) + 1 < 2 ^ L)
    (h10 : 10 ≤ L) :
    RS w L ROWMEM v0 (fun n v => n ≤ m * (d * 19 + 29) + 8 ∧
      v.mem = Function.update v0.mem cR (rowR d m nm dn Y) ∧ Same' v0 v) := by
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hnat : ∀ x : ℤ, 0 ≤ x → x < 2 ^ L → len x ≤ L := fun x h0 hx =>
    len_of_abs (by rw [abs_of_nonneg h0]) hx
  unfold ROWMEM; simp only [seqL]
  refine RS.seq (rs_seqI (is := [.const cR 1, .const cOne 1, .const cE 3]) (t := v0)
    ⟨⟨len_scr (by decide) (by decide) h10, h1⟩, ⟨len_scr (by decide) (by decide) h10, h1⟩,
     ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10⟩, trivial⟩) ?_
  rintro n₁ t₁ ⟨hn₁, rfl⟩
  have m1 : (runI w [.const cR 1, .const cOne 1, .const cE 3] v0).mem =
      Function.update (Function.update (Function.update (Function.update v0.mem cR (rowR d 0 nm dn Y)) cOne 1) cE
        (3 + 2 * (((d : ℤ) + 1) * (0 : ℕ)))) cI (0 : ℕ) := by
    have r0 : rowR d 0 nm dn Y = 1 := rowR_zero
    rw [r0]; simp only [runI, stepI_const_mem, Nat.cast_zero, mul_zero, add_zero]
    funext c; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | exact hI | exact hI.symm
  have s1 : Same' v0 (runI w [.const cR 1, .const cOne 1, .const cE 3] v0) := runI_same (by simp [Plain, NJ])
  set t₁ := runI w [.const cR 1, .const cOne 1, .const cE 3] v0 with ht₁
  refine RS.seq (Q₁ := fun n u => n ≤ m * (d * 19 + 29) + 2 ∧ u.mem = Function.update (Function.update
      (Function.update (Function.update v0.mem cR (rowR d m nm dn Y)) cOne 1) cE
      (3 + 2 * (((d : ℤ) + 1) * (m : ℕ)))) cI (m : ℕ) ∧ Same' v0 u)
    (RS.loop (fun k u => k ≤ m ∧ u.mem = Function.update (Function.update (Function.update
      (Function.update v0.mem cR (rowR d k nm dn Y)) cOne 1) cE (3 + 2 * (((d : ℤ) + 1) * (k : ℕ)))) cI (k : ℕ) ∧
      Same' v0 u) m (d * 19 + 27) ⟨Nat.zero_le m, m1, s1⟩ ?_ ?_ ?_) ?_
  · rintro k u ⟨hk, hu, -⟩
    have e1 : u.mem cI = k := by rw [hu]; evl
    have e2 : u.mem 2 = m := by rw [hu]; evl; exact hm
    refine ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, ?_, ?_⟩, ?_⟩
    · rw [e1]; exact hnat _ (by omega) (by omega)
    · rw [e2]; exact hnat _ (by omega) (by omega)
    · rw [e1, e2]; omega
  · rintro k u ⟨hk, hu, hsu⟩ hkm
    have hA : 3 + 2 * (((d : ℤ) + 1) * k + d) + 2 < 2 ^ L := by
      have : ((d : ℤ) + 1) * (k + 1) ≤ ((d : ℤ) + 1) * m :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hkm) (by positivity)
      have e : ((d : ℤ) + 1) * k + d + 1 = ((d : ℤ) + 1) * (k + 1) := by ring
      omega
    refine (rs_ROWBODY (v0 := addC u _) (i := k) (YB := YB) (M := M) (B := B) (r := rowR d k nm dn Y)
      (nm := nm k) (dn := dn k) (Y := Y) hYB0
      (by rw [addC_mem, hu]; evl; exact hYB) (by rw [addC_mem, hu]; evl) (by rw [addC_mem, hu]; evl)
      (by rw [addC_mem, hu]; evl) (by rw [addC_mem, hu]; evl) (by rw [addC_mem, hu]; evl; exact hd)
      (by rw [addC_mem, hu]; evl; exact hS) (by rw [addC_mem, hu]; evl; exact hQ)
      (by rw [addC_mem, hu]; evl; exact hJ) (by rw [addC_mem, hu]; evl; exact hYP)
      (by rw [addC_mem, hu]; evl; exact hN) (by rw [addC_mem, hu]; evl; exact hE1)
      (by rw [addC_mem, hu]; evl; exact hDD) (by rw [addC_mem, hu]; evl; exact hY)
      (by rw [addC_mem, hu]; evl; exact hT) (by rw [addC_mem, hu]; evl; exact hY0)
      (by rw [addC_mem, hu]; evl; exact hL) (by rw [addC_mem, hu]; evl; exact hRt)
      (fun j hj => by
        have : (0 : ℤ) ≤ ((d : ℤ) + 1) * k := by positivity
        rw [addC_mem, hu]; evl; exact hnm k hkm j hj)
      (fun j hj => by
        have : (0 : ℤ) ≤ ((d : ℤ) + 1) * k := by positivity
        rw [addC_mem, hu]; evl; exact hdn k hkm j hj)
      (fun j hj => by rw [addC_mem, hu]; evl; exact hYv j hj)
      hM1 hB (hMb k hkm) hYb hLV hA hLY (by omega) h10).mono ?_
    rintro n v ⟨hn, hv, hsv⟩
    refine ⟨hn, by omega, ?_, (hsu.trans (Same'.addC _ _)).trans (hsv.trans (Same'.addC _ 1))⟩
    rw [addC_mem, hv, addC_mem, hu, ← rowR_succ]
    funext c; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | (push_cast; ring)
  · rintro n u ⟨-, hu, hsu⟩ hn
    exact ⟨by omega, by rw [addC_mem]; exact hu, hsu.trans (Same'.addC _ _)⟩
  · rintro n₂ t₂ ⟨hn₂, hm₂, hs₂⟩
    refine (rs_seqI (is := rowClr) (t := t₂) ⟨⟨len_scr (by decide) (by decide) h10, l0⟩,
      ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
    rintro n v ⟨hn, rfl⟩
    refine ⟨by simp [rowClr] at hn hn₁; omega, ?_, hs₂.trans (runI_same (by simp [rowClr, Plain, NJ]))⟩
    simp only [rowClr, runI, stepI_const_mem]; rw [hm₂]
    funext c; simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | exact hOne.symm | exact hE.symm | exact hI.symm

end AdversarialBco.UniPoly
