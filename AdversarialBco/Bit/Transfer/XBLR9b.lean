/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR9

@[expose] public section

/-!
# BL's round on the machine: R9's vectors

With the products and scalars of `XV.r9a` in place: `b'` into the array `28` (in place of `B̂ v̂`), `ĝ` into the array
`31` (in place of `v̂`), `G' = Ĝ + ĝ` into the array `29`, `ĝ·μ̂` into the slot `62`, the numerator of `l'` into the
slot `63`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## A vector filled entry by entry -/

/-- `nr := 0; for k < d: aY[k] := e`, the index in the registers `22` and `23`. -/
def xmapV (L : Layout) (e : IE) (aY : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst 22 0))) (xmapE L sZ tR e aY 22 rOne 23 rD rOne)

set_option maxHeartbeats 1000000 in
/-- The rule of `xmapV`: the cells `k < d` of `aY` get `F k`. -/
theorem XV.mapV {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {e : IE} {aY E : ℕ} {F : ℕ → ℤ} (hw : e.WF L tR) (hscr : e.scr ≤ 400) (hY : aY < aWE) (hz : σ.sc sZ = 0)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hda : d * d + d < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hF : ∀ k < d, ∀ σ' : Env d, FrameA (fun y => tR ≤ y) (fun j => j = 23 ∨ j = 22)
        (fun b c => b = aY ∧ c < k) σ σ' → σ'.draws = σ.draws → σ'.nat 23 = k → σ'.nat 22 = k →
        e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xmapV L e aY) σ (1 + (d * (e.units + 6) + 3)) (fun σ' =>
      (∀ k < d, σ'.arr aY k = F k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => tR ≤ y) (fun j => j = 23 ∨ j = 22) (fun b c => b = aY ∧ c < d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hA hY
  have hd : d < 2 ^ ℓa := by nlinarith
  refine XV.seq (XV.nconst hL (σ := σ) (i := 22) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  have F0 : FrameA (fun y => tR ≤ y) (fun j => j = 23 ∨ j = 22) (fun b c => b = aY ∧ c < 0) σ (σ.setNat 22 0) :=
    (FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0
  refine XV.mono (XV.mapE hL (σ := σ.setNat 22 0) (z := sZ) (t := tR) (aB := aY) (nr := 22) (nst := rOne)
    (nk := 23) (nn := rD) (none := rOne) (E := E) (N := d) (base := 0) (st := 1) (e := e) (F := F) hw
    (by simp [sZ, tR]) (by simp only [tR]; omega) (by simpa using hz) (by omega) (by omega)
    (by simp only [rOne]; omega) (by omega) (by simp only [rD]; omega) (by simp only [rOne]; omega) (by decide)
    (by decide) (by decide) (by simpa [rD] using hD) (by simpa [rOne] using h1) (by simp)
    (by simpa [rOne] using h1) one_pos (fun k hk => by unfold asz; nlinarith) hd (by omega)
    (by have := hL.1; omega) htop ?_)
    le_rfl fun σ' ⟨v', _, d', F'⟩ => ⟨fun k hk => by simpa using v' k hk, by simpa using d', ?_⟩
  · intro k hk σ' Fk dk hk' hr
    refine hF k hk σ' ((F0.mono (fun y h => h) (fun j h => h) (fun b c h => ⟨h.1, by omega⟩)).trans
      (Fk.mono (fun y h => h) (fun j h => h) (fun b c h => ⟨h.1, by omega⟩))) (by simpa using dk) hk'
      (by simpa using hr)
  · exact (F0.mono (fun y h => h) (fun j h => h) (fun b c h => ⟨h.1, by omega⟩)).trans
      (F'.mono (fun y h => h) (fun j h => h) (fun b c h => ⟨h.1, by omega⟩))

/-! ## The expressions of R9 -/

/-- `b'_k = b̂_k + rnd(κ̂Ŷ (s_uμ u_k - G² (B̂v̂)_k) / V_b)`. -/
def ieBp : IE :=
  .op .add (.arr ab 22)
    (rndE (.op .mul (.sc 46) (.op .sub (.op .mul (.sc 54) (.arr aU 22)) (.op .mul (.sc 49) (.arr 28 22)))) (.sc 56))

/-- `ĝ_k = rnd(Ŷν̂ u_k / V_g)`. -/
def ieGh : IE := rndE (.op .mul (.sc 60) (.arr aU 22)) (.sc 61)

/-- `G'_k = Ĝ_k + ĝ_k`. -/
def ieGp : IE := .op .add (.arr aG 22) (.arr 31 22)

/-- `l̂' = l̂ + rnd(ĝ·μ̂ / (Q D))`. -/
def ieLp : IE := .op .add (.sc sL) (rndE (.sc 62) (.op .mul (.sc s2p) (.sc sDmu)))

theorem ieBp_eval {σ : Env d} {Q kY su G2 Vb b u w : ℤ} (eQ : σ.sc s2p = Q) (eK : σ.sc 46 = kY)
    (eS : σ.sc 54 = su) (eG : σ.sc 49 = G2) (eV : σ.sc 56 = Vb) (eb : σ.arr ab (σ.nat 22) = b)
    (eu : σ.arr aU (σ.nat 22) = u) (ew : σ.arr 28 (σ.nat 22) = w) :
    ieBp.eval σ = ((b + rndZ (kY * (su * u - G2 * w)) Vb Q : ℤ) : ℝ) := by
  have h := rndE_eval (σ := σ) (U := .op .mul (.sc 46) (.op .sub (.op .mul (.sc 54) (.arr aU 22))
    (.op .mul (.sc 49) (.arr 28 22)))) (V := .sc 56) (u := kY * (su * u - G2 * w)) (v := Vb) (Q := Q)
    (by simp only [IE.eval, RealRAM.Op2.eval, eK, eS, eG, eu, ew]; push_cast; ring) (by simp [IE.eval, eV]) eQ
  simp only [ieBp, IE.eval, RealRAM.Op2.eval, eb] at h ⊢
  rw [h]; push_cast; ring

theorem ieGh_eval {σ : Env d} {Q yv Vg u : ℤ} (eQ : σ.sc s2p = Q) (eY : σ.sc 60 = yv) (eV : σ.sc 61 = Vg)
    (eu : σ.arr aU (σ.nat 22) = u) : ieGh.eval σ = (rndZ (yv * u) Vg Q : ℝ) :=
  rndE_eval (by simp only [IE.eval, RealRAM.Op2.eval, eY, eu]; push_cast; ring) (by simp [IE.eval, eV]) eQ

theorem ieGp_eval {σ : Env d} {Gh g : ℤ} (eG : σ.arr aG (σ.nat 22) = Gh) (eg : σ.arr 31 (σ.nat 22) = g) :
    ieGp.eval σ = ((Gh + g : ℤ) : ℝ) := by
  simp only [ieGp, IE.eval, RealRAM.Op2.eval, eG, eg]; push_cast; ring

theorem ieLp_eval {σ : Env d} {Q D lh s : ℤ} (eQ : σ.sc s2p = Q) (eD : σ.sc sDmu = D) (eL : σ.sc sL = lh)
    (eS : σ.sc 62 = s) : ieLp.eval σ = ((lh + rndZ s (Q * D) Q : ℤ) : ℝ) := by
  have h := rndE_eval (σ := σ) (U := .sc 62) (V := .op .mul (.sc s2p) (.sc sDmu)) (u := s) (v := Q * D) (Q := Q)
    (by simp [IE.eval, eS]) (by simp only [IE.eval, RealRAM.Op2.eval, eQ, eD]; push_cast; ring) eQ
  simp only [ieLp, IE.eval, RealRAM.Op2.eval, eL] at h ⊢
  rw [h]; push_cast; ring

theorem ieBp_leaves {σ : Env d} {E : ℕ} {Q kY su G2 Vb b u w : ℤ} (hr : σ.nat 22 < asz d) (eQ : σ.sc s2p = Q)
    (eK : σ.sc 46 = kY) (eS : σ.sc 54 = su) (eG : σ.sc 49 = G2) (eV : σ.sc 56 = Vb) (eb : σ.arr ab (σ.nat 22) = b)
    (eu : σ.arr aU (σ.nat 22) = u) (ew : σ.arr 28 (σ.nat 22) = w) (bQ : |Q| ≤ 2 ^ E) (bK : |kY| ≤ 2 ^ E)
    (bS : |su| ≤ 2 ^ E) (bG : |G2| ≤ 2 ^ E) (bV : |Vb| ≤ 2 ^ E) (bb : |b| ≤ 2 ^ E) (bu : |u| ≤ 2 ^ E)
    (bw : |w| ≤ 2 ^ E) : ieBp.Leaves E σ := by
  simp only [ieBp, rndE, IE.Leaves, eQ, eK, eS, eG, eV, eb, eu, ew, Int.cast_inj, exists_eq_left', hr, bQ, bK, bS,
    bG, bV, bb, bu, bw, and_self]

theorem ieGh_leaves {σ : Env d} {E : ℕ} {Q yv Vg u : ℤ} (hr : σ.nat 22 < asz d) (eQ : σ.sc s2p = Q)
    (eY : σ.sc 60 = yv) (eV : σ.sc 61 = Vg) (eu : σ.arr aU (σ.nat 22) = u) (bQ : |Q| ≤ 2 ^ E) (bY : |yv| ≤ 2 ^ E)
    (bV : |Vg| ≤ 2 ^ E) (bu : |u| ≤ 2 ^ E) : ieGh.Leaves E σ := by
  simp only [ieGh, rndE, IE.Leaves, eQ, eY, eV, eu, Int.cast_inj, exists_eq_left', hr, bQ, bY, bV, bu, and_self]

theorem ieGp_leaves {σ : Env d} {E : ℕ} {Gh g : ℤ} (hr : σ.nat 22 < asz d) (eG : σ.arr aG (σ.nat 22) = Gh)
    (eg : σ.arr 31 (σ.nat 22) = g) (bG : |Gh| ≤ 2 ^ E) (bg : |g| ≤ 2 ^ E) : ieGp.Leaves E σ := by
  simp only [ieGp, IE.Leaves, eG, eg, Int.cast_inj, exists_eq_left', hr, bG, bg, and_self]

theorem ieLp_leaves {σ : Env d} {E : ℕ} {Q D lh s : ℤ} (eQ : σ.sc s2p = Q) (eD : σ.sc sDmu = D)
    (eL : σ.sc sL = lh) (eS : σ.sc 62 = s) (bQ : |Q| ≤ 2 ^ E) (bD : |D| ≤ 2 ^ E) (bL : |lh| ≤ 2 ^ E)
    (bS : |s| ≤ 2 ^ E) : ieLp.Leaves E σ := by
  simp only [ieLp, rndE, IE.Leaves, eQ, eD, eL, eS, Int.cast_inj, exists_eq_left', bQ, bD, bL, bS, and_self]

/-! ## R9, second part -/

/-- `b'` into `28`, `ĝ` into `31`, `G'` into `29`, `ĝ·μ̂` into `62`, `l̂'` into `63`. -/
def xR9b (L : Layout) : XCmd :=
  .seq (xmapV L ieBp 28) (.seq (xmapV L ieGh 31) (.seq (xmapV L ieGp 29)
    (.seq (xdot L sZ 62 tR 31 aMu 22 23 rD rOne) (ieLp.code L sZ 63 tR))))

/-- The units of `xR9b`. -/
def r9bUnits (d : ℕ) : ℕ :=
  (1 + (d * (ieBp.units + 6) + 3)) + ((1 + (d * (ieGh.units + 6) + 3)) + ((1 + (d * (ieGp.units + 6) + 3)) +
    ((d * 10 + 5) + ieLp.units)))

/-- The cells that `xR9b` changes. -/
def S9b (y : ℕ) : Prop := y = 62 ∨ y = 63 ∨ tR ≤ y
def N9b (j : ℕ) : Prop := j = 22 ∨ j = 23
def A9b (b c : ℕ) : Prop := (b = 28 ∧ c < d) ∨ (b = 31 ∧ c < d) ∨ (b = 29 ∧ c < d)

set_option maxHeartbeats 2000000 in
/-- **R9's vectors on the machine.** -/
theorem XV.r9b {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q kY su G2 Vb yv Vg lh D : ℤ} {bh u w Gh mu : Fin d → ℤ} {E : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (eQ : σ.sc s2p = Q) (eK : σ.sc 46 = kY)
    (eS : σ.sc 54 = su) (eG2 : σ.sc 49 = G2) (eV : σ.sc 56 = Vb) (eY : σ.sc 60 = yv) (eVg : σ.sc 61 = Vg)
    (eL : σ.sc sL = lh) (eD : σ.sc sDmu = D) (eb : ∀ j : Fin d, σ.arr ab j = bh j)
    (eU : ∀ j : Fin d, σ.arr aU j = u j) (eW : ∀ j : Fin d, σ.arr 28 j = w j) (eG : ∀ j : Fin d, σ.arr aG j = Gh j)
    (eMu : ∀ j : Fin d, σ.arr aMu j = mu j)
    (bQ : |Q| ≤ 2 ^ E) (bK : |kY| ≤ 2 ^ E) (bS : |su| ≤ 2 ^ E) (bG2 : |G2| ≤ 2 ^ E) (bV : |Vb| ≤ 2 ^ E)
    (bY : |yv| ≤ 2 ^ E) (bVg : |Vg| ≤ 2 ^ E) (bL : |lh| ≤ 2 ^ E) (bD : |D| ≤ 2 ^ E) (bb : ∀ j, |bh j| ≤ 2 ^ E)
    (bU : ∀ j, |u j| ≤ 2 ^ E) (bW : ∀ j, |w j| ≤ 2 ^ E) (bG : ∀ j, |Gh j| ≤ 2 ^ E) (bMu : ∀ j, |mu j| ≤ 2 ^ E)
    (bg : ∀ j, |rndZ (yv * u j) Vg Q| ≤ 2 ^ E) (bgm : |(fun j => rndZ (yv * u j) Vg Q) ⬝ᵥ mu| ≤ 2 ^ E)
    (hT : 4 * E + 4 < ℓ) (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR9b L) σ (r9bUnits d) (fun σ' =>
      (∀ j : Fin d, σ'.arr 28 j = bh j + rndZ (kY * (su * u j - G2 * w j)) Vb Q) ∧
      (∀ j : Fin d, σ'.arr 31 j = rndZ (yv * u j) Vg Q) ∧
      (∀ j : Fin d, σ'.arr 29 j = Gh j + rndZ (yv * u j) Vg Q) ∧
      σ'.sc 62 = (((fun j => rndZ (yv * u j) Vg Q) ⬝ᵥ mu : ℤ) : ℝ) ∧
      σ'.sc 63 = ((lh + rndZ ((fun j => rndZ (yv * u j) Vg Q) ⬝ᵥ mu) (Q * D) Q : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA S9b N9b (A9b (d := d)) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hE : 2 * E < ℓ := by omega
  set gv : Fin d → ℤ := fun j => rndZ (yv * u j) Vg Q with hgv
  have sc0 : ∀ (σ' : Env d) (y : ℕ), y < tR → (∀ y, ¬ tR ≤ y → σ'.sc y = σ.sc y) → σ'.sc y = σ.sc y :=
    fun σ' y hy h => h y (by omega)
  -- b'
  refine XV.seq (XV.mapV hL hlay (σ := σ) (e := ieBp) (aY := 28) (E := E)
    (F := fun k => if h : k < d then bh ⟨k, h⟩ + rndZ (kY * (su * u ⟨k, h⟩ - G2 * w ⟨k, h⟩)) Vb Q else 0)
    (by simp only [ieBp, rndE, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, aU]; romega)
    (by decide) (by decide) hz hD h1 hda (by simp only [ieBp, rndE, IE.top, IE.mag]; omega) ?_)
    fun σ1 ⟨v1, d1, F1⟩ => ?_
  · intro k hk σ' F' d' hk' hr
    have hs : ∀ y, y < tR → σ'.sc y = σ.sc y := fun y hy => F'.2.1 y (by omega)
    have ha : ∀ b, b ≠ 28 → σ'.arr b k = σ.arr b k := fun b hb => F'.2.2.1 b k (fun h => hb h.1)
    have e28 : σ'.arr 28 k = σ.arr 28 k := F'.2.2.1 28 k (fun h => by omega)
    have hc : k < asz d := by unfold asz; nlinarith
    have eQ' : σ'.sc s2p = Q := by rw [hs _ (by simp [s2p, tR]), eQ]
    have eK' : σ'.sc 46 = kY := by rw [hs _ (by simp [tR]), eK]
    have eS' : σ'.sc 54 = su := by rw [hs _ (by simp [tR]), eS]
    have eG' : σ'.sc 49 = G2 := by rw [hs _ (by simp [tR]), eG2]
    have eV' : σ'.sc 56 = Vb := by rw [hs _ (by simp [tR]), eV]
    have eb' : σ'.arr ab (σ'.nat 22) = bh ⟨k, hk⟩ := by rw [hr, ha _ (by decide)]; exact eb ⟨k, hk⟩
    have eu' : σ'.arr aU (σ'.nat 22) = u ⟨k, hk⟩ := by rw [hr, ha _ (by decide)]; exact eU ⟨k, hk⟩
    have ew' : σ'.arr 28 (σ'.nat 22) = w ⟨k, hk⟩ := by rw [hr, e28]; exact eW ⟨k, hk⟩
    refine ⟨ieBp_leaves (by rw [hr]; exact hc) eQ' eK' eS' eG' eV' eb' eu' ew' bQ bK bS bG2 bV (bb _) (bU _) (bW _), ?_⟩
    rw [ieBp_eval eQ' eK' eS' eG' eV' eb' eu' ew']
    simp [hk]

  have sc1 : ∀ y, y < tR → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have nt1 : ∀ j, j ≠ 22 → j ≠ 23 → σ1.nat j = σ.nat j := fun j a b => F1.1 j (by omega)
  have ar1 : ∀ b k, b ≠ 28 → σ1.arr b k = σ.arr b k := fun b k hb => F1.2.2.1 b k (fun h => hb h.1)
  -- ĝ
  refine XV.seq (XV.mapV hL hlay (σ := σ1) (e := ieGh) (aY := 31) (E := E)
    (F := fun k => if h : k < d then gv ⟨k, h⟩ else 0)
    (by simp only [ieGh, rndE, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, aU]; romega)
    (by decide) (by decide) (by rw [sc1 _ (by simp [sZ, tR]), hz]) (by rw [nt1 _ (by decide) (by decide), hD])
    (by rw [nt1 _ (by decide) (by decide), h1]) hda (by simp only [ieGh, rndE, IE.top, IE.mag]; omega) ?_)
    fun σ2 ⟨v2, d2, F2⟩ => ?_
  · intro k hk σ' F' d' hk' hr
    have hs : ∀ y, y < tR → σ'.sc y = σ.sc y := fun y hy => by rw [F'.2.1 y (by omega), sc1 y hy]
    have hc : k < asz d := by unfold asz; nlinarith
    have eQ' : σ'.sc s2p = Q := by rw [hs _ (by simp [s2p, tR]), eQ]
    have eY' : σ'.sc 60 = yv := by rw [hs _ (by simp [tR]), eY]
    have eV' : σ'.sc 61 = Vg := by rw [hs _ (by simp [tR]), eVg]
    have eu' : σ'.arr aU (σ'.nat 22) = u ⟨k, hk⟩ := by
      rw [hr, F'.2.2.1 _ _ (fun h => absurd h.1 (by decide)), ar1 _ _ (by decide)]; exact eU ⟨k, hk⟩
    refine ⟨ieGh_leaves (by rw [hr]; exact hc) eQ' eY' eV' eu' bQ bY bVg (bU _), ?_⟩
    rw [ieGh_eval eQ' eY' eV' eu']
    simp [hk, hgv]
  have sc2 : ∀ y, y < tR → σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 y (by omega), sc1 y hy]
  have nt2 : ∀ j, j ≠ 22 → j ≠ 23 → σ2.nat j = σ.nat j := fun j a b => by rw [F2.1 j (by omega), nt1 j a b]
  have ar2 : ∀ b k, b ≠ 28 → b ≠ 31 → σ2.arr b k = σ.arr b k := fun b k hb hb' => by
    rw [F2.2.2.1 b k (fun h => hb' h.1), ar1 b k hb]
  have g2 : ∀ j : Fin d, σ2.arr 31 j = gv j := fun j => by rw [v2 j j.2]; simp
  -- G'
  refine XV.seq (XV.mapV hL hlay (σ := σ2) (e := ieGp) (aY := 29) (E := E)
    (F := fun k => if h : k < d then Gh ⟨k, h⟩ + gv ⟨k, h⟩ else 0)
    (by simp only [ieGp, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega)
    (by decide) (by decide) (by rw [sc2 _ (by simp [sZ, tR]), hz]) (by rw [nt2 _ (by decide) (by decide), hD])
    (by rw [nt2 _ (by decide) (by decide), h1]) hda (by simp only [ieGp, IE.top, IE.mag]; omega) ?_)
    fun σ3 ⟨v3, d3, F3⟩ => ?_
  · intro k hk σ' F' d' hk' hr
    have hc : k < asz d := by unfold asz; nlinarith
    have eG' : σ'.arr aG (σ'.nat 22) = Gh ⟨k, hk⟩ := by
      rw [hr, F'.2.2.1 _ _ (fun h => absurd h.1 (by decide)), ar2 _ _ (by decide) (by decide)]; exact eG ⟨k, hk⟩
    have eg' : σ'.arr 31 (σ'.nat 22) = gv ⟨k, hk⟩ := by
      rw [hr, F'.2.2.1 _ _ (fun h => absurd h.1 (by decide))]; exact g2 ⟨k, hk⟩
    refine ⟨ieGp_leaves (by rw [hr]; exact hc) eG' eg' (bG _) (bg _), ?_⟩
    rw [ieGp_eval eG' eg']
    simp [hk]
  have sc3 : ∀ y, y < tR → σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), sc2 y hy]
  have nt3 : ∀ j, j ≠ 22 → j ≠ 23 → σ3.nat j = σ.nat j := fun j a b => by rw [F3.1 j (by omega), nt2 j a b]
  have ar3 : ∀ b k, b ≠ 29 → σ3.arr b k = σ2.arr b k := fun b k hb => F3.2.2.1 b k (fun h => hb h.1)
  -- ĝ·μ̂
  refine XV.seq (XV.dot hL (σ := σ3) (z := sZ) (r := 62) (t := tR) (ax := 31) (ay := aMu) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := E) (x := gv) (y := mu) (by romega) (by romega) (by romega) (by romega)
    (by rw [sc3 _ (by simp [sZ, tR]), hz]) (by romega) (by romega) (by romega) (by romega) (by romega)
    (by romega) (by decide) (by rw [nt3 _ (by decide) (by decide), hD]) (by rw [nt3 _ (by decide) (by decide), h1])
    (fun k => by rw [ar3 _ _ (by decide), g2]) (fun k => by rw [ar3 _ _ (by decide), ar2 _ _ (by decide)
      (by decide), eMu]) bg bMu hE hℓ) fun σ4 ⟨v4, d4, F4⟩ => ?_
  have sc4 : ∀ y, y < tR → y ≠ 62 → σ4.sc y = σ.sc y := fun y hy hy' => by
    rw [F4.2.1 y (by omega), sc3 y hy]
  -- l̂'
  have eQ4 : σ4.sc s2p = Q := by rw [sc4 _ (by simp [s2p, tR]) (by simp [s2p]), eQ]
  have eD4 : σ4.sc sDmu = D := by rw [sc4 _ (by simp [sDmu, tR]) (by simp [sDmu]), eD]
  have eL4 : σ4.sc sL = lh := by rw [sc4 _ (by simp [sL, tR]) (by simp [sL]), eL]
  refine XV.mono (XV.ieRun hL (σ := σ4) (z := sZ) (x := 63) (t := tR) (E := E) (e := ieLp)
    (v := lh + rndZ (gv ⬝ᵥ mu) (Q * D) Q)
    (by simp only [ieLp, rndE, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega)
    (by romega) (by simp only [ieLp, rndE, IE.scr, tR]; omega) (by rw [sc4 _ (by simp [sZ, tR]) (by simp [sZ]), hz])
    (ieLp_leaves eQ4 eD4 eL4 v4 bQ bD bL bgm) (by simp only [ieLp, rndE, IE.top, IE.mag]; omega)
    (ieLp_eval eQ4 eD4 eL4 v4)) le_rfl fun σ5 ⟨v5, _, d5, F5⟩ => ?_
  have ar5 : ∀ b k, σ5.arr b k = σ3.arr b k := fun b k => by rw [F5.2.2.1, F4.2.2.1 b k id]
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, ?_, v5, by rw [d5, d4, d3, d2, d1], ?_⟩
  · rw [ar5, ar3 _ _ (by decide), F2.2.2.1 _ _ (fun h => absurd h.1 (by decide)), v1 j j.2]; simp
  · rw [ar5, ar3 _ _ (by decide), g2]
  · rw [ar5, v3 j j.2]; simp [hgv]
  · rw [F5.2.1 62 (by simp [tR]), v4]
  · refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_, ?_, ?_⟩
    · simp only [N9b, not_or] at hj
      rw [F5.1 j id, F4.1 j (by omega), nt3 j hj.1 hj.2]
    · simp only [S9b, not_or, not_le] at hy
      rw [F5.2.1 y (by omega), sc4 y hy.2.2 hy.1]
    · simp only [A9b, not_or, not_and, not_lt] at hb
      rw [ar5, F3.2.2.1 b k (fun h => by have := hb.2.2 h.1; omega),
        F2.2.2.1 b k (fun h => by have := hb.2.1 h.1; omega), F1.2.2.1 b k (fun h => by have := hb.1 h.1; omega)]
    · rw [F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]
    · rw [F5.2.2.2.2, F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]

end AdversarialBco.Bit.Transfer.BLM
