/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR10
public import AdversarialBco.Bit.Transfer.XBLSetupPrm
public import AdversarialBco.Bit.Transfer.XFrameE0

@[expose] public section

/-!
# BL's round on the machine: R12 FIRE's test values

From the point `x/2^X` of the projection routine (`X` in the slot `769`, `x` in the array `32`): `2^X` into the slot
`92`, `B̂'ᵀ x` into the array `30`, `(B̂'ᵀx)·(B̂'ᵀx)`, `b̂'·x`, `Ĝ'·x` into the slots `93`, `94`, `95`, and the two
sides of R12's test (`r12_mach`) into the slots `86` and `87`: BL starts a new epoch when `sc 86 ≤ sc 87`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The left side of R12's test:
`η̂ (l̂ D - Ĝ·x) Q D H - F H ((B̂ᵀx)·(B̂ᵀx) - (b̂·x) Q D - (b̂·x) Q D + k̂ Q D D + k̂ Q D D)`. -/
def ieT1 : IE :=
  .op .sub (.op .mul (.op .mul (.op .mul (.op .mul (.sc sEta) (.op .sub (.op .mul (.sc 63) (.sc 92)) (.sc 95)))
      (.sc s2p)) (.sc 92)) (.sc s2eh))
    (.op .mul (.op .mul (.sc s2pF) (.sc s2eh))
      (.op .add (.op .add (.op .sub (.op .sub (.sc 93) (.op .mul (.op .mul (.sc 94) (.sc s2p)) (.sc 92)))
        (.op .mul (.op .mul (.sc 94) (.sc s2p)) (.sc 92)))
        (.op .mul (.op .mul (.op .mul (.sc 59) (.sc s2p)) (.sc 92)) (.sc 92)))
        (.op .mul (.op .mul (.op .mul (.sc 59) (.sc s2p)) (.sc 92)) (.sc 92))))

/-- The right side of R12's test: `(F - ρ̂ H) Q Q D D`. -/
def ieT2 : IE :=
  .op .mul (.op .mul (.op .mul (.op .mul (.op .sub (.sc s2pF) (.op .mul (.sc sRho) (.sc s2eh))) (.sc s2p))
    (.sc s2p)) (.sc 92)) (.sc 92)

theorem ieT1_top : topL ieT1 = (6, 5) := by simp [ieT1, topL, magL]
theorem ieT2_top : topL ieT2 = (6, 1) := by simp [ieT2, topL, magL]

/-- R12's values. -/
def xR12 (L : Layout) : XCmd :=
  .seq (xrtoN L 19 769) (.seq (xpowS L 92 42 20 19 rOne)
    (.seq (xmatvecT L sZ 30 tR 27 32 30 24 22 23 rD rOne)
      (.seq (xdot L sZ 93 tR 30 30 22 23 rD rOne) (.seq (xdot L sZ 94 tR 28 32 22 23 rD rOne)
        (.seq (xdot L sZ 95 tR 29 32 22 23 rD rOne) (.seq (ieT1.code L sZ 86 tR) (ieT2.code L sZ 87 tR)))))))

/-- The units of `xR12`. -/
def r12Units (d X : ℕ) : ℕ :=
  1 + ((1 + (X * (1 + 3) + 3)) + ((d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3) +
    ((d * 10 + 5) + ((d * 10 + 5) + ((d * 10 + 5) + (ieT1.units + ieT2.units))))))

/-- The cells that `xR12` changes. -/
def S12 (y : ℕ) : Prop := y = 30 ∨ y = 86 ∨ y = 87 ∨ (92 ≤ y ∧ y < 96) ∨ tR ≤ y
def N12 (j : ℕ) : Prop := j = 19 ∨ j = 20 ∨ j = 22 ∨ j = 23 ∨ j = 24
def A12 (b c : ℕ) : Prop := b = 30 ∧ c < d

set_option maxHeartbeats 2000000 in
/-- **R12's test values on the machine.** -/
theorem XV.r12 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Bh : Matrix (Fin d) (Fin d) ℤ} {bh Gh x : Fin d → ℤ} {F Q H eh lh kh rh : ℤ} {Xe Gu : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (c2 : σ.sc 42 = 2)
    (eX : σ.sc 769 = ((Xe : ℤ) : ℝ)) (ex : ∀ j : Fin d, σ.arr 32 j = x j)
    (eB : ∀ i j : Fin d, σ.arr 27 (d * i + j) = Bh i j) (eb : ∀ j : Fin d, σ.arr 28 j = bh j)
    (eG : ∀ j : Fin d, σ.arr 29 j = Gh j)
    (eF : σ.sc s2pF = F) (eQ : σ.sc s2p = Q) (eH : σ.sc s2eh = H) (eE : σ.sc sEta = eh) (eL : σ.sc 63 = lh)
    (eK : σ.sc 59 = kh) (eR : σ.sc sRho = rh)
    (bB : ∀ i j, |Bh i j| ≤ 2 ^ Gu) (bx : ∀ j, |x j| ≤ 2 ^ Gu) (bb : ∀ j, |bh j| ≤ 2 ^ Gu)
    (bG : ∀ j, |Gh j| ≤ 2 ^ Gu) (bBx : ∀ j, |(Bhᵀ *ᵥ x) j| ≤ 2 ^ Gu)
    (bF : |F| ≤ 2 ^ Gu) (bQ : |Q| ≤ 2 ^ Gu) (bH : |H| ≤ 2 ^ Gu) (bE : |eh| ≤ 2 ^ Gu) (bL : |lh| ≤ 2 ^ Gu)
    (bK : |kh| ≤ 2 ^ Gu) (bR : |rh| ≤ 2 ^ Gu) (bD : (2 : ℤ) ^ Xe ≤ 2 ^ Gu)
    (bBB : |(Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x)| ≤ 2 ^ Gu) (bbx : |bh ⬝ᵥ x| ≤ 2 ^ Gu) (bGx : |Gh ⬝ᵥ x| ≤ 2 ^ Gu)
    (hE : 2 * Gu < ℓ) (hℓ : d * 2 ^ (2 * Gu) < 2 ^ ℓ) (hT : 6 * Gu + 5 < ℓ) (hXa : Xe < 2 ^ ℓa)
    (hXl : Xe < ℓ) :
    XRunsB L X ℓa ℓ (xR12 L) σ (r12Units d Xe) (fun σ' =>
      σ'.sc 92 = (((2 : ℤ) ^ Xe : ℤ) : ℝ) ∧
      σ'.sc 86 = ((eh * (lh * 2 ^ Xe - Gh ⬝ᵥ x) * Q * 2 ^ Xe * H -
          F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * 2 ^ Xe - (bh ⬝ᵥ x) * Q * 2 ^ Xe +
            kh * Q * 2 ^ Xe * 2 ^ Xe + kh * Q * 2 ^ Xe * 2 ^ Xe) : ℤ) : ℝ) ∧
      σ'.sc 87 = (((F - rh * H) * Q * Q * 2 ^ Xe * 2 ^ Xe : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA S12 N12 (A12 (d := d)) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hℓ1 : 1 ≤ ℓ := by omega
  -- X into the register 19
  refine XV.seq (XV.rtoNat hL (i := 19) (x := 769) (v := Xe) (by romega) (by romega) eX hXa
    (lt_of_lt_of_le hXl (Nat.lt_two_pow_self).le)) fun σ0 e0 => ?_
  subst e0
  -- 2^X into the slot 92
  refine XV.seq (XV.powS hL (σ := σ.setNat 19 Xe) (r := 92) (x := 42) (i := 20) (n := 19) (one := rOne) (E := 1)
    (k := Xe) (v := 2) (by romega) (by romega) (by decide) (by romega) (by romega) (by romega) (by decide)
    (by decide) (by simpa using c2) (by norm_num) (by norm_num) (by simp) (by simpa [rOne] using h1) hXa
    (by omega)) fun σ1 ⟨v1, d1, F1⟩ => ?_
  have s1 : ∀ y, y ≠ 92 → σ1.sc y = σ.sc y := fun y h => by rw [F1.2.1 y h]; simp
  have n1 : ∀ j, j ≠ 19 → j ≠ 20 → σ1.nat j = σ.nat j := fun j a b => by
    rw [F1.1 j b]; simp [a]
  have r1 : ∀ b k, σ1.arr b k = σ.arr b k := fun b k => by rw [F1.2.2.1 b k id]; simp
  -- B̂ᵀ x into the array 30
  refine XV.seq (XV.matvecT hL (σ := σ1) (z := sZ) (r := 30) (t := tR) (aM := 27) (ax := 32) (ay := 30) (ni := 24)
    (nr := 22) (nk := 23) (nd := rD) (none := rOne) (E := Gu) (M := Bh) (x := x) (by romega) (by romega)
    (by romega) (by romega) (by rw [s1 _ (by decide), hz]) (by romega) (by romega) (by romega) (by decide)
    (by decide) (by romega) (by romega) (by romega) (by romega) (by romega) (by decide)
    (by rw [n1 _ (by decide) (by decide), hD]) (by rw [n1 _ (by decide) (by decide), h1])
    (fun i j => by rw [r1, eB]) (fun j => by rw [r1, ex]) bB bx hE hℓ) fun σ2 ⟨v2, d2, F2⟩ => ?_
  have s2 : ∀ y, y < tR → y ≠ 30 → y ≠ 92 → σ2.sc y = σ.sc y := fun y h h' h'' => by
    rw [F2.2.1 y (by omega), s1 y h'']
  have n2 : ∀ j, j ≠ 19 → j ≠ 20 → j ≠ 22 → j ≠ 23 → j ≠ 24 → σ2.nat j = σ.nat j := fun j a b c e f => by
    rw [F2.1 j (by omega), n1 j a b]
  have r2 : ∀ b k, b ≠ 30 → σ2.arr b k = σ.arr b k := fun b k hb => by
    rw [F2.2.2.1 b k (fun h => hb h.1), r1]
  -- (B̂ᵀx)·(B̂ᵀx)
  refine XV.seq (XV.dot hL (σ := σ2) (z := sZ) (r := 93) (t := tR) (ax := 30) (ay := 30) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := Gu) (x := Bhᵀ *ᵥ x) (y := Bhᵀ *ᵥ x) (by romega) (by romega) (by romega)
    (by romega) (by rw [s2 _ (by romega) (by decide) (by decide), hz]) (by romega) (by romega) (by romega)
    (by romega) (by romega) (by romega) (by decide)
    (by rw [n2 _ (by decide) (by decide) (by decide) (by decide) (by decide), hD])
    (by rw [n2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h1]) v2 v2 bBx bBx hE hℓ)
    fun σ3 ⟨v3, d3, F3⟩ => ?_
  have s3 : ∀ y, y < tR → y ≠ 30 → y ≠ 92 → y ≠ 93 → σ3.sc y = σ.sc y := fun y h h' h'' h''' => by
    rw [F3.2.1 y (by omega), s2 y h h' h'']
  have n3 : ∀ j, j ≠ 19 → j ≠ 20 → j ≠ 22 → j ≠ 23 → j ≠ 24 → σ3.nat j = σ.nat j := fun j a b c e f => by
    rw [F3.1 j (by omega), n2 j a b c e f]
  have r3 : ∀ b k, b ≠ 30 → σ3.arr b k = σ.arr b k := fun b k hb => by rw [F3.2.2.1 b k id, r2 b k hb]
  -- b̂·x
  refine XV.seq (XV.dot hL (σ := σ3) (z := sZ) (r := 94) (t := tR) (ax := 28) (ay := 32) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := Gu) (x := bh) (y := x) (by romega) (by romega) (by romega)
    (by romega) (by rw [s3 _ (by romega) (by decide) (by decide) (by decide), hz]) (by romega) (by romega)
    (by romega) (by romega) (by romega) (by romega) (by decide)
    (by rw [n3 _ (by decide) (by decide) (by decide) (by decide) (by decide), hD])
    (by rw [n3 _ (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (fun j => by rw [r3 _ _ (by decide), eb]) (fun j => by rw [r3 _ _ (by decide), ex]) bb bx hE hℓ)
    fun σ4 ⟨v4, d4, F4⟩ => ?_
  have s4 : ∀ y, y < tR → y ≠ 30 → y ≠ 92 → y ≠ 93 → y ≠ 94 → σ4.sc y = σ.sc y := fun y h h' h'' h''' h4 => by
    rw [F4.2.1 y (by omega), s3 y h h' h'' h''']
  have n4 : ∀ j, j ≠ 19 → j ≠ 20 → j ≠ 22 → j ≠ 23 → j ≠ 24 → σ4.nat j = σ.nat j := fun j a b c e f => by
    rw [F4.1 j (by omega), n3 j a b c e f]
  have r4 : ∀ b k, b ≠ 30 → σ4.arr b k = σ.arr b k := fun b k hb => by rw [F4.2.2.1 b k id, r3 b k hb]
  -- Ĝ·x
  refine XV.seq (XV.dot hL (σ := σ4) (z := sZ) (r := 95) (t := tR) (ax := 29) (ay := 32) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := Gu) (x := Gh) (y := x) (by romega) (by romega) (by romega)
    (by romega) (by rw [s4 _ (by romega) (by decide) (by decide) (by decide) (by decide), hz]) (by romega)
    (by romega) (by romega) (by romega) (by romega) (by romega) (by decide)
    (by rw [n4 _ (by decide) (by decide) (by decide) (by decide) (by decide), hD])
    (by rw [n4 _ (by decide) (by decide) (by decide) (by decide) (by decide), h1])
    (fun j => by rw [r4 _ _ (by decide), eG]) (fun j => by rw [r4 _ _ (by decide), ex]) bG bx hE hℓ)
    fun σ5 ⟨v5, d5, F5⟩ => ?_
  have s5 : ∀ y, y < tR → y ≠ 30 → y ≠ 92 → y ≠ 93 → y ≠ 94 → y ≠ 95 → σ5.sc y = σ.sc y :=
    fun y h h' h'' h''' h4 h5 => by rw [F5.2.1 y (by omega), s4 y h h' h'' h''' h4]
  have n5 : ∀ j, j ≠ 19 → j ≠ 20 → j ≠ 22 → j ≠ 23 → j ≠ 24 → σ5.nat j = σ.nat j := fun j a b c e f => by
    rw [F5.1 j (by omega), n4 j a b c e f]
  have r5 : ∀ b k, b ≠ 30 → σ5.arr b k = σ.arr b k := fun b k hb => by rw [F5.2.2.1 b k id, r4 b k hb]
  have e92 : σ5.sc 92 = (((2 : ℤ) ^ Xe : ℤ) : ℝ) := by
    rw [F5.2.1 92 (by romega), F4.2.1 92 (by romega), F3.2.1 92 (by romega), F2.2.1 92 (by romega), v1]
  have e93 : σ5.sc 93 = (((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) : ℤ) : ℝ) := by
    rw [F5.2.1 93 (by romega), F4.2.1 93 (by romega), v3]
  have e94 : σ5.sc 94 = ((bh ⬝ᵥ x : ℤ) : ℝ) := by rw [F5.2.1 94 (by romega), v4]
  have sv : ∀ y, y < 30 ∨ (63 ≤ y ∧ y < 64) ∨ y = 59 → σ5.sc y = σ.sc y := fun y hy => by
    apply s5 <;> (try simp only [tR]) <;> omega
  have q13 : σ5.sc sEta = eh := by rw [sv _ (Or.inl (by decide)), eE]
  have q63 : σ5.sc 63 = lh := by rw [sv _ (Or.inr (Or.inl ⟨le_rfl, by norm_num⟩)), eL]
  have q59 : σ5.sc 59 = kh := by rw [sv _ (Or.inr (Or.inr rfl)), eK]
  have q4 : σ5.sc s2p = Q := by rw [sv _ (Or.inl (by decide)), eQ]
  have q5 : σ5.sc s2pF = F := by rw [sv _ (Or.inl (by decide)), eF]
  have q10 : σ5.sc s2eh = H := by rw [sv _ (Or.inl (by decide)), eH]
  have q14 : σ5.sc sRho = rh := by rw [sv _ (Or.inl (by decide)), eR]
  have q0 : σ5.sc sZ = 0 := by rw [sv _ (Or.inl (by decide)), hz]
  have hD2 : |(2 : ℤ) ^ Xe| ≤ 2 ^ Gu := by rw [abs_of_nonneg (by positivity)]; exact bD
  -- the left side
  refine XV.seq (XV.ieRun hL (σ := σ5) (z := sZ) (x := 86) (t := tR) (E := Gu) (e := ieT1)
    (v := eh * (lh * 2 ^ Xe - Gh ⬝ᵥ x) * Q * 2 ^ Xe * H -
      F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * 2 ^ Xe - (bh ⬝ᵥ x) * Q * 2 ^ Xe +
        kh * Q * 2 ^ Xe * 2 ^ Xe + kh * Q * 2 ^ Xe * 2 ^ Xe))
    (by simp only [ieT1, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieT1, IE.scr, tR]; omega) q0
    (by
      simp only [ieT1, IE.Leaves, q13, q63, q59, q4, q5, q10, e92, e93, e94, v5, Int.cast_inj,
        exists_eq_left', bE, bL, bK, bQ, bF, bH, hD2, bBB, bbx, bGx, and_self])
    (top_lt ieT1_top (by omega))
    (by
      simp only [ieT1, IE.eval, RealRAM.Op2.eval, q13, q63, q59, q4, q5, q10, e92, e93, e94, v5]
      push_cast; ring)) fun σ6 ⟨v6, _, d6, F6⟩ => ?_
  have s6 : ∀ y, y ≠ 86 → y < tR → σ6.sc y = σ5.sc y := fun y h h' => F6.2.1 y (by omega)
  have t14 : σ6.sc sRho = rh := by rw [s6 _ (by decide) (by decide), q14]
  have t4 : σ6.sc s2p = Q := by rw [s6 _ (by decide) (by decide), q4]
  have t5 : σ6.sc s2pF = F := by rw [s6 _ (by decide) (by decide), q5]
  have t10 : σ6.sc s2eh = H := by rw [s6 _ (by decide) (by decide), q10]
  have t92 : σ6.sc 92 = (((2 : ℤ) ^ Xe : ℤ) : ℝ) := by rw [s6 _ (by decide) (by decide), e92]
  have t0 : σ6.sc sZ = 0 := by rw [s6 _ (by decide) (by decide), q0]
  -- the right side
  refine XV.mono (XV.ieRun hL (σ := σ6) (z := sZ) (x := 87) (t := tR) (E := Gu) (e := ieT2)
    (v := (F - rh * H) * Q * Q * 2 ^ Xe * 2 ^ Xe)
    (by simp only [ieT2, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieT2, IE.scr, tR]; omega) t0
    (by
      simp only [ieT2, IE.Leaves, t14, t4, t5, t10, t92, Int.cast_inj, exists_eq_left', bR, bQ, bF, bH, hD2, and_self])
    (top_lt ieT2_top (by omega))
    (by
      simp only [ieT2, IE.eval, RealRAM.Op2.eval, t14, t4, t5, t10, t92]
      push_cast; ring)) le_rfl fun σ7 ⟨v7, _, d7, F7⟩ => ?_
  refine ⟨by rw [F7.2.1 92 (by romega), t92],
    by rw [F7.2.1 86 (by romega), v6], v7, by rw [d7, d6, d5, d4, d3, d2, d1]; rfl, ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_, ?_, ?_⟩
  · simp only [N12, not_or] at hj
    rw [F7.1 j id, F6.1 j id, n5 j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2]
  · simp only [S12, not_or, not_and, not_le, not_lt] at hy
    rw [F7.2.1 y (by omega), s6 y (by omega) (by omega), s5 y (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  · simp only [A12, not_and, not_lt] at hb
    rw [F7.2.2.1, F6.2.2.1]
    by_cases h30 : b = 30
    · subst h30
      rw [F5.2.2.1 _ _ id, F4.2.2.1 _ _ id, F3.2.2.1 _ _ id, F2.2.2.1 _ _ (fun h => by have := hb rfl; omega), r1]
    · exact r5 b k h30
  · rw [F7.2.2.2.1, F6.2.2.2.1, F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]; rfl
  · rw [F7.2.2.2.2, F6.2.2.2.2, F5.2.2.2.2, F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]; rfl

end AdversarialBco.Bit.Transfer.BLM
