/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR12

@[expose] public section

/-!
# BL's round on the machine: R13 WMU's values

The numerators `ŵ_j = μ̂_j Q Q G - ŝ5 w_j D_μ` of `w_μ` into the array `31` (`w = Â Γ` in the array `25`, `ŝ5` in the
slot `72`), their denominator `D_w = D_μ Q Q G` into the slot `91`, `ŵ·ŵ` into `84`, and the two sides of R13's test
(`r13_s5w`), `4 Ŵ Ŵ D_w D_w` into `85` and `(ŵ·ŵ) F F` into `86`: BL leaves for `guard` when `sc 85 < sc 86`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- `ŵ_k = μ̂_k Q Q G - ŝ5 w_k D_μ`, the cell `k` in the register `22`. -/
def ieWn : IE :=
  .op .sub (.op .mul (.op .mul (.op .mul (.arr aMu 22) (.sc s2p)) (.sc s2p)) (.sc s2g))
    (.op .mul (.op .mul (.sc 72) (.arr aWv 22)) (.sc sDmu))

/-- `D_w = D_μ Q Q G`. -/
def ieDw : IE := .op .mul (.op .mul (.op .mul (.sc sDmu) (.sc s2p)) (.sc s2p)) (.sc s2g)

/-- `4 Ŵ Ŵ D_w D_w`. -/
def ieL13 : IE := .op .mul (.op .mul (.op .mul (.op .mul (.sc 43) (.sc sW)) (.sc sW)) (.sc 91)) (.sc 91)

/-- `(ŵ·ŵ) F F`. -/
def ieR13 : IE := .op .mul (.op .mul (.sc 84) (.sc s2pF)) (.sc s2pF)

theorem ieWn_top : topL ieWn = (4, 1) := by simp [ieWn, topL, magL]
theorem ieDw_top : topL ieDw = (4, 0) := by simp [ieDw, topL, magL]
theorem ieL13_top : topL ieL13 = (5, 0) := by simp [ieL13, topL, magL]
theorem ieR13_top : topL ieR13 = (3, 0) := by simp [ieR13, topL, magL]

/-- R13's values. -/
def xR13 (L : Layout) : XCmd :=
  .seq (xmapV L ieWn 31) (.seq (ieDw.code L sZ 91 tR) (.seq (xdot L sZ 84 tR 31 31 22 23 rD rOne)
    (.seq (ieL13.code L sZ 85 tR) (ieR13.code L sZ 86 tR))))

/-- The units of `xR13`. -/
def r13Units (d : ℕ) : ℕ :=
  (1 + (d * (ieWn.units + 6) + 3)) + (ieDw.units + ((d * 10 + 5) + (ieL13.units + ieR13.units)))

/-- The cells that `xR13` changes. -/
def S13 (y : ℕ) : Prop := (84 ≤ y ∧ y < 87) ∨ y = 91 ∨ tR ≤ y
def N13 (j : ℕ) : Prop := j = 22 ∨ j = 23
def A13 (b c : ℕ) : Prop := b = 31 ∧ c < d

set_option maxHeartbeats 2000000 in
/-- **R13's values on the machine.** -/
theorem XV.r13 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {mu w : Fin d → ℤ} {F Q G Dm s5 Wh : ℤ} {Gu G2 : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (c4 : σ.sc 43 = 4)
    (eMu : ∀ j : Fin d, σ.arr aMu j = mu j) (eW : ∀ j : Fin d, σ.arr aWv j = w j)
    (eF : σ.sc s2pF = F) (eQ : σ.sc s2p = Q) (eG : σ.sc s2g = G) (eD : σ.sc sDmu = Dm) (eS : σ.sc 72 = s5)
    (eWh : σ.sc sW = Wh)
    (bMu : ∀ j, |mu j| ≤ 2 ^ Gu) (bW : ∀ j, |w j| ≤ 2 ^ Gu) (bQ : |Q| ≤ 2 ^ Gu) (bG : |G| ≤ 2 ^ Gu)
    (bD : |Dm| ≤ 2 ^ Gu) (bS : |s5| ≤ 2 ^ Gu)
    (bn : ∀ j, |mu j * Q * Q * G - s5 * w j * Dm| ≤ 2 ^ G2) (bDw : |Dm * Q * Q * G| ≤ 2 ^ G2)
    (bF : |F| ≤ 2 ^ G2) (bWh : |Wh| ≤ 2 ^ G2) (b4 : (4 : ℤ) ≤ 2 ^ G2)
    (bnn : |(fun j => mu j * Q * Q * G - s5 * w j * Dm) ⬝ᵥ (fun j => mu j * Q * Q * G - s5 * w j * Dm)| ≤ 2 ^ G2)
    (hT1 : 4 * Gu + 1 < ℓ) (hT2 : 5 * G2 < ℓ) (hℓ : d * 2 ^ (2 * G2) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR13 L) σ (r13Units d) (fun σ' =>
      (∀ j : Fin d, σ'.arr 31 j = ((mu j * Q * Q * G - s5 * w j * Dm : ℤ) : ℝ)) ∧
      σ'.sc 91 = ((Dm * Q * Q * G : ℤ) : ℝ) ∧
      σ'.sc 85 = ((4 * Wh * Wh * (Dm * Q * Q * G) * (Dm * Q * Q * G) : ℤ) : ℝ) ∧
      σ'.sc 86 = (((fun j => mu j * Q * Q * G - s5 * w j * Dm) ⬝ᵥ (fun j => mu j * Q * Q * G - s5 * w j * Dm) *
        F * F : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA S13 N13 (A13 (d := d)) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  set wn : Fin d → ℤ := fun j => mu j * Q * Q * G - s5 * w j * Dm with hwn
  set Dw : ℤ := Dm * Q * Q * G with hDw
  -- ŵ into the array 31
  refine XV.seq (XV.mapV hL hlay (σ := σ) (e := ieWn) (aY := 31) (E := Gu)
    (F := fun k => if h : k < d then wn ⟨k, h⟩ else 0)
    (by simp only [ieWn, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, aWv]; romega)
    (by decide) (by decide) hz hD h1 hda (top_lt ieWn_top (by omega)) ?_) fun σ1 ⟨v1, d1, F1⟩ => ?_
  · intro k hk σ' F' d' hk' hr
    have hs : ∀ y, y < tR → σ'.sc y = σ.sc y := fun y hy => F'.2.1 y (by omega)
    have ha : ∀ b, b ≠ 31 → σ'.arr b k = σ.arr b k := fun b hb => F'.2.2.1 b k (fun h => hb h.1)
    have hc : k < asz d := by unfold asz; nlinarith
    have eQ' : σ'.sc s2p = Q := by rw [hs _ (by simp [s2p, tR]), eQ]
    have eG' : σ'.sc s2g = G := by rw [hs _ (by simp [s2g, tR]), eG]
    have eD' : σ'.sc sDmu = Dm := by rw [hs _ (by simp [sDmu, tR]), eD]
    have eS' : σ'.sc 72 = s5 := by rw [hs _ (by simp [tR]), eS]
    have em' : σ'.arr aMu (σ'.nat 22) = mu ⟨k, hk⟩ := by rw [hr, ha _ (by decide)]; exact eMu ⟨k, hk⟩
    have ew' : σ'.arr aWv (σ'.nat 22) = w ⟨k, hk⟩ := by rw [hr, ha _ (by decide)]; exact eW ⟨k, hk⟩
    have hc' : σ'.nat 22 < asz d := by rw [hr]; exact hc
    refine ⟨by simp only [ieWn, IE.Leaves, em', ew', eQ', eG', eD', eS', hc', Int.cast_inj, exists_eq_left', bMu, bW,
      bQ, bG, bD, bS, and_self], ?_⟩
    simp only [ieWn, IE.eval, RealRAM.Op2.eval, eQ', eG', eD', eS', em', ew', hk, dite_true, hwn]
    push_cast; ring
  have sc1 : ∀ y, y < tR → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have nt1 : ∀ j, j ≠ 22 → j ≠ 23 → σ1.nat j = σ.nat j := fun j a b => F1.1 j (by omega)
  have w1 : ∀ j : Fin d, σ1.arr 31 j = wn j := fun j => by rw [v1 j j.2]; simp
  -- D_w into the slot 91
  have eD1 : σ1.sc sDmu = Dm := by rw [sc1 _ (by simp [sDmu, tR]), eD]
  have eQ1 : σ1.sc s2p = Q := by rw [sc1 _ (by simp [s2p, tR]), eQ]
  have eG1 : σ1.sc s2g = G := by rw [sc1 _ (by simp [s2g, tR]), eG]
  refine XV.seq (XV.ieRun hL (σ := σ1) (z := sZ) (x := 91) (t := tR) (E := Gu) (e := ieDw) (v := Dw)
    (by simp only [ieDw, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieDw, IE.scr, tR]; omega) (by rw [sc1 _ (by simp [sZ, tR]), hz])
    (by simp only [ieDw, IE.Leaves, eD1, eQ1, eG1, Int.cast_inj, exists_eq_left', bD, bQ, bG, and_self])
    (top_lt ieDw_top (by omega))
    (by simp only [ieDw, IE.eval, RealRAM.Op2.eval, eD1, eQ1, eG1, hDw]; push_cast; ring))
    fun σ2 ⟨v2, _, d2, F2⟩ => ?_
  have sc2 : ∀ y, y < tR → y ≠ 91 → σ2.sc y = σ.sc y := fun y hy h => by rw [F2.2.1 y (by omega), sc1 y hy]
  -- ŵ·ŵ into the slot 84
  refine XV.seq (XV.dot hL (σ := σ2) (z := sZ) (r := 84) (t := tR) (ax := 31) (ay := 31) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := G2) (x := wn) (y := wn) (by romega) (by romega) (by romega)
    (by romega) (by rw [sc2 _ (by simp [sZ, tR]) (by simp [sZ]), hz]) (by romega) (by romega) (by romega)
    (by romega) (by romega) (by romega) (by decide)
    (by rw [F2.1 _ id, nt1 _ (by decide) (by decide), hD]) (by rw [F2.1 _ id, nt1 _ (by decide) (by decide), h1])
    (fun j => by rw [F2.2.2.1, w1]) (fun j => by rw [F2.2.2.1, w1]) bn bn (by omega) hℓ)
    fun σ3 ⟨v3, d3, F3⟩ => ?_
  have sc3 : ∀ y, y < tR → y ≠ 91 → y ≠ 84 → σ3.sc y = σ.sc y := fun y hy h h' => by
    rw [F3.2.1 y (by omega), sc2 y hy h]
  have e91 : σ3.sc 91 = ((Dw : ℤ) : ℝ) := by rw [F3.2.1 91 (by simp [tR]), v2]
  have e43 : σ3.sc 43 = ((4 : ℤ) : ℝ) := by rw [sc3 _ (by simp [tR]) (by decide) (by decide), c4]; simp
  have eW3 : σ3.sc sW = Wh := by rw [sc3 _ (by simp [sW, tR]) (by simp [sW]) (by simp [sW]), eWh]
  -- 4 Ŵ Ŵ D_w D_w into the slot 85
  refine XV.seq (XV.ieRun hL (σ := σ3) (z := sZ) (x := 85) (t := tR) (E := G2) (e := ieL13)
    (v := 4 * Wh * Wh * Dw * Dw)
    (by simp only [ieL13, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieL13, IE.scr, tR]; omega)
    (by rw [sc3 _ (by simp [sZ, tR]) (by simp [sZ]) (by simp [sZ]), hz])
    (by
      have b4' : |(4 : ℤ)| ≤ 2 ^ G2 := by rw [abs_of_pos (by norm_num)]; exact b4
      simp only [ieL13, IE.Leaves, e43, eW3, e91, Int.cast_inj, exists_eq_left', b4', bWh, bDw, and_self])
    (top_lt ieL13_top (by omega))
    (by simp only [ieL13, IE.eval, RealRAM.Op2.eval, e43, eW3, e91]; push_cast; ring))
    fun σ4 ⟨v4, _, d4, F4⟩ => ?_
  have sc4 : ∀ y, y < tR → y ≠ 85 → σ4.sc y = σ3.sc y := fun y hy h => F4.2.1 y (by omega)
  have e84 : σ4.sc 84 = ((wn ⬝ᵥ wn : ℤ) : ℝ) := by rw [sc4 _ (by simp [tR]) (by decide), v3]
  have eF4 : σ4.sc s2pF = F := by
    rw [sc4 _ (by simp [s2pF, tR]) (by simp [s2pF]), sc3 _ (by simp [s2pF, tR]) (by simp [s2pF]) (by simp [s2pF]),
      eF]
  -- (ŵ·ŵ) F F into the slot 86
  refine XV.mono (XV.ieRun hL (σ := σ4) (z := sZ) (x := 86) (t := tR) (E := G2) (e := ieR13)
    (v := wn ⬝ᵥ wn * F * F)
    (by simp only [ieR13, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieR13, IE.scr, tR]; omega)
    (by rw [sc4 _ (by simp [sZ, tR]) (by simp [sZ]), sc3 _ (by simp [sZ, tR]) (by simp [sZ]) (by simp [sZ]), hz])
    (by simp only [ieR13, IE.Leaves, e84, eF4, Int.cast_inj, exists_eq_left', bnn, bF, and_self])
    (top_lt ieR13_top (by omega))
    (by simp only [ieR13, IE.eval, RealRAM.Op2.eval, e84, eF4]; push_cast; ring)) le_rfl
    fun σ5 ⟨v5, _, d5, F5⟩ => ?_
  refine ⟨fun j => ?_, ?_, ?_, v5, by rw [d5, d4, d3, d2, d1], ?_⟩
  · rw [F5.2.2.1, F4.2.2.1, F3.2.2.1 _ _ id, F2.2.2.1, w1]
  · rw [F5.2.1 91 (by simp [tR]), F4.2.1 91 (by simp [tR]), e91]
  · rw [F5.2.1 85 (by simp [tR]), v4]
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_, ?_, ?_⟩
  · simp only [N13, not_or] at hj
    rw [F5.1 j id, F4.1 j id, F3.1 j (by omega), F2.1 j id, nt1 j hj.1 hj.2]
  · simp only [S13, not_or, not_and, not_le, not_lt] at hy
    rw [F5.2.1 y (by omega), sc4 y (by omega) (by omega), sc3 y (by omega) (by omega) (by omega)]
  · rw [F5.2.2.1, F4.2.2.1, F3.2.2.1 b k id, F2.2.2.1, F1.2.2.1 b k hb]
  · rw [F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]
  · rw [F5.2.2.2.2, F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]

end AdversarialBco.Bit.Transfer.BLM
