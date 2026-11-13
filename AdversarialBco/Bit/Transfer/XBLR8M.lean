/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR8

@[expose] public section

/-!
# BL's round on the machine: the matrices of R8

`u = B̂ Γ` into the array `30`, then `A'` into the array `26` and `B'` into the array `27`, entry by entry (`xmap2E`):
the entry `(i, j)` of `A'` is `rnd_p` of `(ŝ1 Â_ij G² - ŝ2 (ÂΓ)_i Γ_j)/(Q² G²)` on the integers, that of `B'` the same
with `ŝ3`, `B̂`, `ŝ4`, `u` and a sum.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The arrays of R8: `A'`, `B'`, `u = B̂ Γ`. -/
abbrev aAp : ℕ := 26
abbrev aBp : ℕ := 27
abbrev aU : ℕ := 30

/-- `rnd_p (u/v)` on the integers as the machine computes it, `Q = 2^p`. -/
def rndZ (u v Q : ℤ) : ℤ := (u * Q + u * Q + v) / (v + v)

/-- A binary operation on the integers (`0` for the division). -/
def opZ : RealRAM.Op2 → ℤ → ℤ → ℤ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, _, _ => 0

theorem rndE_eval {σ : Env d} {U V : IE} {u v Q : ℤ} (hU : U.eval σ = u) (hV : V.eval σ = v)
    (hQ : σ.sc s2p = Q) : (rndE U V).eval σ = (rndZ u v Q : ℝ) := by
  simp only [rndE, IE.eval, RealRAM.Op2.eval, hU, hV, hQ, rndZ]
  norm_cast
  rw [Int.floor_intCast, Int.floor_intCast]

/-- The entry of R8: `rnd_p ((ŝ_a M_ij G² ∘ ŝ_b W_i Γ_j)/(Q² G²))`, the cell `d i + j` in the register `22`, the row `i`
in `24`, the column `j` in `23`, `G²` in the slot `49`. -/
def ieR8 (o : RealRAM.Op2) (s1 s2 aM aW : ℕ) : IE :=
  rndE (.op o (.op .mul (.op .mul (.sc s1) (.arr aM 22)) (.sc 49))
      (.op .mul (.op .mul (.sc s2) (.arr aW 24)) (.arr aGam 23)))
    (.op .mul (.op .mul (.sc s2p) (.sc s2p)) (.sc 49))

section ieR8

variable {o : RealRAM.Op2} {s1 s2 aM aW : ℕ}

theorem ieR8_scr : (ieR8 o s1 s2 aM aW).scr = 44 := rfl

theorem ieR8_units (ho : o = .add ∨ o = .sub) : (ieR8 o s1 s2 aM aW).units = 51 := by
  rcases ho with rfl | rfl <;> rfl

theorem ieR8_top (ho : o = .add ∨ o = .sub) (E : ℕ) : (ieR8 o s1 s2 aM aW).top E = 4 * E + 3 := by
  rcases ho with rfl | rfl <;> simp only [ieR8, rndE, IE.top, IE.mag] <;> omega

theorem ieR8_WF {L : Layout} (ho : o = .add ∨ o = .sub) (h1 : s1 < tR) (h2 : s2 < tR) (hM : aM < L.NA)
    (hW : aW < L.NA) (hG : aGam < L.NA) (hN : 25 ≤ L.NN) : (ieR8 o s1 s2 aM aW).WF L tR := by
  have ho' : o ≠ .div := by rcases ho with rfl | rfl <;> simp
  simp only [ieR8, rndE, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, ho', hM, hW, hG, h1,
    h2]
  simp only [s2p, tR]
  omega

theorem ieR8_eval {σ : Env d} (ho : o = .add ∨ o = .sub) {Q G2 a1 a2 M W X : ℤ} (eQ : σ.sc s2p = Q)
    (eG : σ.sc 49 = G2) (e1 : σ.sc s1 = a1) (e2 : σ.sc s2 = a2) (eM : σ.arr aM (σ.nat 22) = M)
    (eW : σ.arr aW (σ.nat 24) = W) (eX : σ.arr aGam (σ.nat 23) = X) :
    (ieR8 o s1 s2 aM aW).eval σ = (rndZ (opZ o (a1 * M * G2) (a2 * W * X)) (Q * Q * G2) Q : ℝ) := by
  refine rndE_eval ?_ ?_ eQ
  · rcases ho with rfl | rfl <;> simp only [IE.eval, RealRAM.Op2.eval, opZ, eG, e1, e2, eM, eW, eX] <;> push_cast <;>
      ring
  · simp only [IE.eval, RealRAM.Op2.eval, eQ, eG]; push_cast; ring

theorem ieR8_leaves {σ : Env d} {E : ℕ} {Q G2 a1 a2 M W X : ℤ} (hr : σ.nat 22 < asz d) (hi : σ.nat 24 < asz d)
    (hk : σ.nat 23 < asz d) (eQ : σ.sc s2p = Q) (eG : σ.sc 49 = G2) (e1 : σ.sc s1 = a1) (e2 : σ.sc s2 = a2)
    (eM : σ.arr aM (σ.nat 22) = M) (eW : σ.arr aW (σ.nat 24) = W) (eX : σ.arr aGam (σ.nat 23) = X)
    (bQ : |Q| ≤ 2 ^ E) (bG : |G2| ≤ 2 ^ E) (b1 : |a1| ≤ 2 ^ E) (b2 : |a2| ≤ 2 ^ E) (bM : |M| ≤ 2 ^ E)
    (bW : |W| ≤ 2 ^ E) (bX : |X| ≤ 2 ^ E) : (ieR8 o s1 s2 aM aW).Leaves E σ := by
  simp only [ieR8, rndE, IE.Leaves, eQ, eG, e1, e2, eM, eW, eX, Int.cast_inj, exists_eq_left', hr, hi, hk, bQ, bG,
    b1, b2, bM, bW, bX, and_self]

end ieR8

set_option maxHeartbeats 1000000 in
/-- **One matrix of R8 on the machine**: the cells `d i + j` of the array `aY` get
`rnd_p ((a1 M_ij G² ∘ a2 W_i Γ_j)/(Q² G²))` on the integers (`∘` a sum or a difference), from `a1, a2` in the slots
`s1, s2`, `M` in `aM`, `W` in `aW`, `Γ` in `aGam`, `Q = 2^p`, `G²` in the slot `49`. -/
theorem XV.r8m {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {o : RealRAM.Op2} (ho : o = .add ∨ o = .sub) {s1 s2 aM aW aY E : ℕ} (hs1 : s1 < tR) (hs2 : s2 < tR)
    (hM : aM < aWE) (hW : aW < aWE) (hY : aY < aWE) (hYM : aY ≠ aM) (hYW : aY ≠ aW) (hYG : aY ≠ aGam)
    {Q G2 a1 a2 : ℤ} {M : Matrix (Fin d) (Fin d) ℤ} {W Xg : Fin d → ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (eQ : σ.sc s2p = Q) (eG : σ.sc 49 = G2)
    (e1 : σ.sc s1 = a1) (e2 : σ.sc s2 = a2) (eM : ∀ i j : Fin d, σ.arr aM (d * i + j) = M i j)
    (eW : ∀ i : Fin d, σ.arr aW i = W i) (eX : ∀ j : Fin d, σ.arr aGam j = Xg j)
    (bQ : |Q| ≤ 2 ^ E) (bG : |G2| ≤ 2 ^ E) (b1 : |a1| ≤ 2 ^ E) (b2 : |a2| ≤ 2 ^ E) (bM : ∀ i j, |M i j| ≤ 2 ^ E)
    (bW : ∀ i, |W i| ≤ 2 ^ E) (bX : ∀ j, |Xg j| ≤ 2 ^ E) (hT : 4 * E + 3 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xmap2E L sZ tR (ieR8 o s1 s2 aM aW) aY 22 24 23 rD rOne) σ (map2Units d 51) (fun σ' =>
      (∀ i j : Fin d, σ'.arr aY (d * i + j) = rndZ (opZ o (a1 * M i j * G2) (a2 * W i * Xg j)) (Q * Q * G2) Q) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => tR ≤ y) (fun r => r = 23 ∨ r = 22 ∨ r = 24) (fun b c => b = aY ∧ c < d * d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hA hM hW hY
  rw [← ieR8_units (s1 := s1) (s2 := s2) (aM := aM) (aW := aW) ho]
  refine XV.mono (XV.map2E (E := E) (F := fun i j => if h : i < d ∧ j < d then
      rndZ (opZ o (a1 * M ⟨i, h.1⟩ ⟨j, h.2⟩ * G2) (a2 * W ⟨i, h.1⟩ * Xg ⟨j, h.2⟩)) (Q * Q * G2) Q else 0)
    hL (σ := σ) (z := sZ) (t := tR) (aB := aY) (nr := 22) (ri := 24) (nk := 23) (nn := rD) (none := rOne)
    (ieR8_WF ho hs1 hs2 (by omega) (by omega) (by simp only [aGam]; omega) (by omega)) (by simp [sZ, tR])
    (by rw [ieR8_scr]; simp only [tR]; omega) hz (by omega) (by omega) (by omega) (by omega)
    (by simp only [rD]; omega) (by simp only [rOne]; omega) (by decide) (by decide) hD h1 hda
    (by rw [ieR8_top ho]; exact hT) ?_) le_rfl fun σ' ⟨v', d', F'⟩ =>
      ⟨fun i j => by rw [v' i j]; simp [i.2, j.2], d', F'⟩
  intro i hi j hj σ' F' d' hri hnk hnr
  have hc : d * i + j < asz d := by
    unfold asz; have : d * i + d ≤ d * d := by nlinarith
    omega
  have hsc : ∀ y, y < tR → σ'.sc y = σ.sc y := fun y hy => F'.2.1 y (by omega)
  have har : ∀ b k, b ≠ aY → σ'.arr b k = σ.arr b k := fun b k hb => F'.2.2.1 b k (fun h => hb h.1)
  have eM' : σ'.arr aM (σ'.nat 22) = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    rw [hnr, har _ _ (Ne.symm hYM)]; exact eM ⟨i, hi⟩ ⟨j, hj⟩
  have eW' : σ'.arr aW (σ'.nat 24) = W ⟨i, hi⟩ := by
    rw [hri, har _ _ (Ne.symm hYW)]; exact eW ⟨i, hi⟩
  have eX' : σ'.arr aGam (σ'.nat 23) = Xg ⟨j, hj⟩ := by
    rw [hnk, har _ _ (Ne.symm hYG)]; exact eX ⟨j, hj⟩
  have eQ' : σ'.sc s2p = Q := by rw [hsc _ (by simp [s2p, tR]), eQ]
  have eG' : σ'.sc 49 = G2 := by rw [hsc _ (by simp [tR]), eG]
  have e1' : σ'.sc s1 = a1 := by rw [hsc _ hs1, e1]
  have e2' : σ'.sc s2 = a2 := by rw [hsc _ hs2, e2]
  refine ⟨ieR8_leaves (by rw [hnr]; exact hc) (by rw [hri]; unfold asz; nlinarith)
    (by rw [hnk]; unfold asz; nlinarith) eQ' eG' e1' e2' eM' eW' eX' bQ bG b1 b2 (bM _ _) (bW _) (bX _), ?_⟩
  rw [ieR8_eval ho eQ' eG' e1' e2' eM' eW' eX']
  simp [hi, hj]

/-! ## R8 -/

/-- R8: `u = B̂ Γ` into `30` (the slot `30` as the accumulator), `A'` into `26`, `B'` into `27`. -/
def xR8 (L : Layout) : XCmd :=
  .seq (xmatvec L sZ 30 tR aB aGam aU 24 22 23 rD rOne)
    (.seq (xmap2E L sZ tR (ieR8 .sub 74 81 aA aWv) aAp 22 24 23 rD rOne)
      (xmap2E L sZ tR (ieR8 .add 76 83 aB aU) aBp 22 24 23 rD rOne))

/-- The units of `xR8`. -/
def r8Units (d : ℕ) : ℕ := (d * (d * 10 + 9) + 4) + (map2Units d 51 + map2Units d 51)

/-- The cells that `xR8` changes. -/
def S8 (y : ℕ) : Prop := y = 30 ∨ tR ≤ y
def N8 (j : ℕ) : Prop := j = 22 ∨ j = 23 ∨ j = 24
def A8 (b c : ℕ) : Prop := (b = aU ∧ c < d) ∨ (b = aAp ∧ c < d * d) ∨ (b = aBp ∧ c < d * d)

set_option maxHeartbeats 1000000 in
/-- **R8 on the machine**: with `ŝ1, ŝ2, ŝ3, ŝ4` in the slots `74, 81, 76, 83`, `Â`, `B̂` in `aA`, `aB`, `Â Γ` in
`aWv`, `Γ` in `aGam`: `u = B̂ Γ` in `30`, the numerators of `A'` and `B'` (`rndZ`) in `26` and `27`. -/
theorem XV.r8 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q G2 a1 a2 a3 a4 : ℤ} {Ah Bh : Matrix (Fin d) (Fin d) ℤ} {Γ : Fin d → ℤ} {E : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (eQ : σ.sc s2p = Q) (eG : σ.sc 49 = G2)
    (e1 : σ.sc 74 = a1) (e2 : σ.sc 81 = a2) (e3 : σ.sc 76 = a3) (e4 : σ.sc 83 = a4)
    (eA : ∀ i j : Fin d, σ.arr aA (d * i + j) = Ah i j) (eB : ∀ i j : Fin d, σ.arr aB (d * i + j) = Bh i j)
    (eW : ∀ i : Fin d, σ.arr aWv i = (Ah *ᵥ Γ) i) (eX : ∀ j : Fin d, σ.arr aGam j = Γ j)
    (bQ : |Q| ≤ 2 ^ E) (bG : |G2| ≤ 2 ^ E) (b1 : |a1| ≤ 2 ^ E) (b2 : |a2| ≤ 2 ^ E) (b3 : |a3| ≤ 2 ^ E)
    (b4 : |a4| ≤ 2 ^ E) (bA : ∀ i j, |Ah i j| ≤ 2 ^ E) (bB : ∀ i j, |Bh i j| ≤ 2 ^ E) (bX : ∀ j, |Γ j| ≤ 2 ^ E)
    (bW : ∀ i, |(Ah *ᵥ Γ) i| ≤ 2 ^ E) (bU : ∀ i, |(Bh *ᵥ Γ) i| ≤ 2 ^ E) (hT : 4 * E + 3 < ℓ)
    (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR8 L) σ (r8Units d) (fun σ' =>
      (∀ i : Fin d, σ'.arr aU i = (Bh *ᵥ Γ) i) ∧
      (∀ i j : Fin d, σ'.arr aAp (d * i + j) = rndZ (a1 * Ah i j * G2 - a2 * (Ah *ᵥ Γ) i * Γ j) (Q * Q * G2) Q) ∧
      (∀ i j : Fin d, σ'.arr aBp (d * i + j) = rndZ (a3 * Bh i j * G2 + a4 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * G2) Q) ∧
      σ'.draws = σ.draws ∧ FrameA S8 N8 (A8 (d := d)) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  refine XV.seq (XV.matvec hL (σ := σ) (z := sZ) (r := 30) (t := tR) (aM := aB) (ax := aGam) (ay := aU) (ni := 24)
    (nr := 22) (nk := 23) (nd := rD) (none := rOne) (E := E) (M := Bh) (x := Γ) (by simp [sZ, tR])
    (by simp [tR]) (by simp [sZ]) (by simp only [tR]; omega) hz (by simp only [aB]; omega)
    (by simp only [aGam]; omega) (by simp only [aU]; omega) (by decide) (by decide) (by omega) (by omega)
    (by omega) (by simp only [rD]; omega) (by simp only [rOne]; omega) (by decide) hD h1 eB eX bB bX
    (by omega) hℓ) fun σ1 ⟨u1, d1, F1⟩ => ?_
  have s1 : ∀ y, y < tR → y ≠ 30 → σ1.sc y = σ.sc y := fun y h h' => F1.2.1 y (by omega)
  have n1 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ1.nat j = σ.nat j := fun j a b c => F1.1 j (by omega)
  have r1 : ∀ b k, b ≠ aU → σ1.arr b k = σ.arr b k := fun b k hb => F1.2.2.1 b k (fun h => hb h.1)
  refine XV.seq (XV.r8m hL hlay (σ := σ1) (Or.inr rfl) (s1 := 74) (s2 := 81) (aM := aA) (aW := aWv) (aY := aAp)
    (E := E) (by simp [tR]) (by simp [tR]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [n1 _ (by decide) (by decide) (by decide), hD])
    (by rw [n1 _ (by decide) (by decide) (by decide), h1]) (by rw [s1 _ (by simp [sZ, tR]) (by decide), hz])
    (by rw [s1 _ (by simp [s2p, tR]) (by decide), eQ]) (by rw [s1 _ (by simp [tR]) (by decide), eG])
    (by rw [s1 _ (by simp [tR]) (by decide), e1]) (by rw [s1 _ (by simp [tR]) (by decide), e2])
    (fun i j => by rw [r1 _ _ (by decide), eA]) (fun i => by rw [r1 _ _ (by decide), eW])
    (fun j => by rw [r1 _ _ (by decide), eX]) bQ bG b1 b2 bA bW bX hT hda) fun σ2 ⟨v2, d2, F2⟩ => ?_
  have s2 : ∀ y, y < tR → σ2.sc y = σ1.sc y := fun y h => F2.2.1 y (by omega)
  have n2 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ2.nat j = σ1.nat j := fun j a b c => F2.1 j (by omega)
  have r2 : ∀ b k, b ≠ aAp → σ2.arr b k = σ1.arr b k := fun b k hb => F2.2.2.1 b k (fun h => hb h.1)
  refine XV.mono (XV.r8m hL hlay (σ := σ2) (Or.inl rfl) (s1 := 76) (s2 := 83) (aM := aB) (aW := aU) (aY := aBp)
    (E := E) (by simp [tR]) (by simp [tR]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by rw [n2 _ (by decide) (by decide) (by decide), n1 _ (by decide) (by decide) (by decide), hD])
    (by rw [n2 _ (by decide) (by decide) (by decide), n1 _ (by decide) (by decide) (by decide), h1])
    (by rw [s2 _ (by simp [sZ, tR]), s1 _ (by simp [sZ, tR]) (by decide), hz])
    (by rw [s2 _ (by simp [s2p, tR]), s1 _ (by simp [s2p, tR]) (by decide), eQ])
    (by rw [s2 _ (by simp [tR]), s1 _ (by simp [tR]) (by decide), eG])
    (by rw [s2 _ (by simp [tR]), s1 _ (by simp [tR]) (by decide), e3])
    (by rw [s2 _ (by simp [tR]), s1 _ (by simp [tR]) (by decide), e4])
    (fun i j => by rw [r2 _ _ (by decide), r1 _ _ (by decide), eB]) (fun i => by rw [r2 _ _ (by decide), u1])
    (fun j => by rw [r2 _ _ (by decide), r1 _ _ (by decide), eX]) bQ bG b3 b4 bB bU bX hT hda)
    le_rfl fun σ3 ⟨v3, d3, F3⟩ => ?_
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, by rw [d3, d2, d1], ?_⟩
  · rw [F3.2.2.1 _ _ (fun h => absurd h.1 (by decide)), r2 _ _ (by decide), u1]
  · rw [F3.2.2.1 _ _ (fun h => absurd h.1 (by decide)), v2 i j]; rfl
  · rw [v3 i j]; rfl
  · refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_, ?_, ?_⟩
    · simp only [N8, not_or] at hj
      rw [F3.1 j (by omega), n2 j hj.1 hj.2.1 hj.2.2, n1 j hj.1 hj.2.1 hj.2.2]
    · simp only [S8, not_or, not_le] at hy
      rw [F3.2.1 y (by omega), s2 y hy.2, s1 y hy.2 hy.1]
    · simp only [A8, not_or, not_and, not_lt] at hb
      rw [F3.2.2.1 b k (fun h => by have := hb.2.2 h.1; omega),
        F2.2.2.1 b k (fun h => by have := hb.2.1 h.1; omega), F1.2.2.1 b k (fun h => by have := hb.1 h.1; omega)]
    · rw [F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]
    · rw [F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]

end AdversarialBco.Bit.Transfer.BLM
