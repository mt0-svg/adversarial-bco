/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriZ
public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# TRI-M, the update of the iterate

`X̂ := tzUpd c X̂ A Y |β̃|` in place: the arrays `aXm` (`μ̂`, cells `i < d`) and `aXt` (`T̂`, cells `d i + l`) of the
iterate, from the arrays `aA` (`A = T̂_Pᵀ row`) and `aY` (the draw) and the constants in slots.

* `xent`, `XV.ent`: an expression into a slot, its clip, the store (any expression through its leaves).
* `ieMu`, `ieLow`, `ieDiag`: the three kinds of entries as expressions, with their packages.
* `xupdMu`, `XV.updMu`: the loop over `μ̂`; `xupdRow`, `XV.updRow`: row `i` of `T̂`; `xtupdT`, `XV.tupdT`: all rows.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM

variable {d : ℕ}

/-- `v := e; v := clip(lo, hi, v); a[nr] := v` (`z` holds `0`, scratch from `t`). -/
def xent (L : Layout) (z v lo hi t a nr : ℕ) (e : IE) : XCmd :=
  .seq (e.code L z v t) (.seq (xclip L v lo hi z) (toX (VL.aset L a nr v)))

theorem XV.ent {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z v lo hi t a nr E : ℕ}
    {e : IE} {val lov hiv : ℤ} (hw : e.WF L t) (hz : z < t) (hv : v < t) (hlo : lo < t) (hhi : hi < t)
    (hvl : v ≠ lo) (hvh : v ≠ hi) (hvz : v ≠ z) (hS : t + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hl : e.Leaves E σ)
    (htop : e.top E < ℓ) (hval : e.eval σ = val) (elo : σ.sc lo = lov) (ehi : σ.sc hi = hiv)
    (blo : |lov| < 2 ^ ℓ) (bhi : |hiv| < 2 ^ ℓ) (ha : a < L.NA) (hnr : nr < L.NN) (hk : σ.nat nr < asz d) :
    XRunsB L X ℓa ℓ (xent L z v lo hi t a nr e) σ (e.units + (4 + 2)) (fun σ' =>
      σ'.arr a (σ.nat nr) = (clipZ lov hiv val : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = v ∨ t ≤ y) (fun _ => False) (fun b k => b = a ∧ k = σ.nat nr) σ σ') := by
  have hvS : v < L.NS := by omega
  refine XV.seq (XV.ieRun (E := E) hL hw hz hv hS hz0 hl htop hval) fun σ1 ⟨v1, b1, d1, P1⟩ => ?_
  have k1 : ∀ y, y < t → y ≠ v → σ1.sc y = σ.sc y := fun y hy hyv => P1.2.1 y (by omega)
  refine XV.seq (XV.clip hL hvS (by omega) (by omega) (by omega) hvl hvz v1 (by rw [k1 lo hlo hvl.symm, elo])
    (by rw [k1 hi hhi hvh.symm, ehi]) (by rw [k1 z hz hvz.symm, hz0]) b1 blo bhi) fun σ2 ⟨v2, b2, d2, P2'⟩ => ?_
  have n2 : σ2.nat = σ.nat := funext fun j => (P2'.1 j not_false).trans (P1.1 j not_false)
  refine XV.mono (XV.aset hL ha hnr hvS (by rw [n2]; exact hk) (by rw [v2]; exact XV.abs_int_lt b2)) le_rfl
    fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [n2, v2], by simp [d2, d1], fun j _ => by simp [n2], fun y hy => ?_, fun b k hb => ?_,
    by simp [P2'.2.2.2.1, P1.2.2.2.1], by simp [P2'.2.2.2.2, P1.2.2.2.2]⟩
  · simp only [Env.setArr_sc]
    rw [P2'.2.1 y (by omega), P1.2.1 y (by omega)]
  · simp only [Env.setArr_arr, n2, hb, ↓reduceIte, P2'.2.2.1, P1.2.2.1]

/-! ## The three kinds of entries -/

/-- `X - (A P_B / β) P_j` with `X = aXm[ni]`, `A = aA[ni]`, the slots `sPB`, `sBb`, `sPj`. -/
def ieMu (aXm aA ni sPB sBb sPj : ℕ) : IE :=
  .op .sub (.arr aXm ni) (.op .mul (.ediv (.op .mul (.arr aA ni) (.sc sPB)) (.sc sBb)) (.sc sPj))

/-- `X - (A Y P_B / (β P_2)) P_j` with `X = aXt[nr]`, `A = aA[ni]`, `Y = aY[nl]`. -/
def ieLow (aXt aA aY nr ni nl sPB sBb sP2 sPj : ℕ) : IE :=
  .op .sub (.arr aXt nr) (.op .mul (.ediv (.op .mul (.op .mul (.arr aA ni) (.arr aY nl)) (.sc sPB))
    (.op .mul (.sc sBb) (.sc sP2))) (.sc sPj))

/-- `X - ((A Y (8d X) - P_G β P_2) P_B / (β P_2 (8d X))) P_j` with `X = aXt[nr]`, `A = aA[ni]`, `Y = aY[ni]`, the slot
`sD8` holding `8 d`. -/
def ieDiag (aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8 : ℕ) : IE :=
  .op .sub (.arr aXt nr) (.op .mul (.ediv
    (.op .mul (.op .sub (.op .mul (.op .mul (.arr aA ni) (.arr aY ni)) (.op .mul (.sc sD8) (.arr aXt nr)))
      (.op .mul (.op .mul (.sc sPG) (.sc sBb)) (.sc sP2))) (.sc sPB))
    (.op .mul (.op .mul (.sc sBb) (.sc sP2)) (.op .mul (.sc sD8) (.arr aXt nr)))) (.sc sPj))

theorem ieMu_scr (aXm aA ni sPB sBb sPj : ℕ) : (ieMu aXm aA ni sPB sBb sPj).scr = 8 := rfl
theorem ieLow_units (aXt aA aY nr ni nl sPB sBb sP2 sPj : ℕ) :
    (ieLow aXt aA aY nr ni nl sPB sBb sP2 sPj).units = 16 := rfl
theorem ieLow_scr (aXt aA aY nr ni nl sPB sBb sP2 sPj : ℕ) :
    (ieLow aXt aA aY nr ni nl sPB sBb sP2 sPj).scr = 12 := rfl
theorem ieDiag_units (aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8 : ℕ) :
    (ieDiag aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8).units = 32 := rfl
theorem ieDiag_scr (aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8 : ℕ) :
    (ieDiag aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8).scr = 26 := rfl

/-! ## The loop over `μ̂` -/

/-- `for i < d: aXm[i] := clip(-R, R, X - (A P_B / β) P_j)`. -/
def xupdMu (L : Layout) (z v t aXm aA sPB sBb sPj sR sMR ni nd none : ℕ) : XCmd :=
  xforN ni nd none (xent L z v sMR sR t aXm ni (ieMu aXm aA ni sPB sBb sPj))

set_option maxHeartbeats 1000000 in
theorem XV.updMu {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z v t aXm aA sPB sBb sPj sR sMR ni nd none E : ℕ} {c : DC} {Xp : PosZ d} {A Y : Fin d → ℤ} {Bb : ℤ}
    (hz : z < t) (hv : v < t) (h1 : sPB < t) (h2 : sBb < t) (h3 : sPj < t) (h4 : sR < t) (h5 : sMR < t)
    (hvR : v ≠ sR) (hvM : v ≠ sMR) (hvz : v ≠ z) (hv1 : v ≠ sPB) (hv2 : v ≠ sBb) (hv3 : v ≠ sPj)
    (hS : t + 8 ≤ L.NS) (hz0 : σ.sc z = 0) (hXm : aXm < L.NA) (hA : aA < L.NA) (hAX : aA ≠ aXm)
    (hni : ni < L.NN) (hnd : nd < L.NN) (hno : none < L.NN) (hid : ni ≠ nd) (hio : ni ≠ none)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d < 2 ^ ℓa)
    (eX : ∀ i : Fin d, σ.arr aXm i = Xp.1 i) (eA : ∀ i : Fin d, σ.arr aA i = A i)
    (ePB : σ.sc sPB = c.PB) (eBb : σ.sc sBb = Bb) (ePj : σ.sc sPj = c.Pj) (eR : σ.sc sR = c.R)
    (eMR : σ.sc sMR = -c.R) (bX : ∀ i, |Xp.1 i| ≤ 2 ^ E) (bA : ∀ i, |A i| ≤ 2 ^ E) (bPB : |c.PB| ≤ 2 ^ E)
    (bBb : |Bb| ≤ 2 ^ E) (bPj : |c.Pj| ≤ 2 ^ E) (bR : |c.R| ≤ 2 ^ E) (hE : 3 * E + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xupdMu L z v t aXm aA sPB sBb sPj sR sMR ni nd none) σ (d * (11 + (4 + 2) + 3) + 3)
      (fun σ' => (∀ i : Fin d, σ'.arr aXm i = (tzUpd c Xp A Y Bb).1 i) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni) (fun b k => b = aXm ∧ k < d) σ σ') := by
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hEl : (2 : ℤ) ^ E < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have bR' : |c.R| < 2 ^ ℓ := lt_of_le_of_lt bR hEl
  have bMR : |-c.R| < 2 ^ ℓ := by rw [abs_neg]; exact bR'
  let J : ℕ → Env d → Prop := fun k σ' => σ'.draws = σ.draws ∧
    (∀ i' (h : i' < k) (hd : i' < d), σ'.arr aXm i' = (tzUpd c Xp A Y Bb).1 ⟨i', hd⟩) ∧
    FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni) (fun b k' => b = aXm ∧ k' < k) σ σ'
  refine XV.mono (XV.forN hL hni hnd hno hid hio d (11 + (4 + 2)) hda J σ hσd hσ1
    ⟨rfl, fun i' h => absurd h (Nat.not_lt_zero _), (FrameA.refl (fun y => y = v ∨ t ≤ y) (fun j => j = ni) (fun b k' => b = aXm ∧ k' < 0) σ).setNat rfl 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd', hy, hF⟩, _⟩ => ⟨fun i => hy i i.2 i.2, hd', hF⟩
  intro k hk σ' ⟨hd', hy, hF⟩ hkt hkd hk1
  have sk : ∀ y, y < t → y ≠ v → σ'.sc y = σ.sc y := fun y hy hyv => hF.2.1 y (by omega)
  have eXk : σ'.arr aXm k = Xp.1 ⟨k, hk⟩ := by
    rw [hF.2.2.1 aXm k (fun h => by omega), eX ⟨k, hk⟩]
  have eAk : σ'.arr aA k = A ⟨k, hk⟩ := by
    rw [hF.2.2.1 aA k (fun h => hAX h.1), eA ⟨k, hk⟩]
  refine XV.mono (XV.ent (E := E) hL (e := ieMu aXm aA ni sPB sBb sPj)
    (val := Xp.1 ⟨k, hk⟩ - tzRMu A Bb c.PB ⟨k, hk⟩ * c.Pj) (lov := -c.R) (hiv := c.R)
    (by simp only [ieMu, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, and_true, hXm, hA, hni]; omega)
    hz hv h5 h4 hvM hvR hvz (by rw [ieMu_scr]; exact hS) (by rw [sk z hz hvz.symm, hz0])
    (by simp only [ieMu, IE.Leaves, eXk, eAk, sk sPB h1 hv1.symm, sk sBb h2 hv2.symm, sk sPj h3 hv3.symm, ePB, eBb,
      ePj, Int.cast_inj, exists_eq_left', hkt, hdl k hk, bX, bA, bPB, bBb, bPj, and_self])
    (by simp only [ieMu, IE.top, IE.mag]; omega)
    (by
      simp only [ieMu, IE.eval, RealRAM.Op2.eval, hkt, eXk, eAk, sk sPB h1 hv1.symm, sk sBb h2 hv2.symm,
        sk sPj h3 hv3.symm, ePB, eBb, ePj, tzRMu]
      norm_cast; rw [Int.floor_intCast, Int.floor_intCast])
    (by rw [sk sMR h5 hvM.symm, eMR]; push_cast; ring) (by rw [sk sR h4 hvR.symm, eR]) bMR bR' hXm hni
    (by rw [hkt]; exact hdl k hk)) le_rfl fun σ'' ⟨e1, d1, F1⟩ => ?_
  have n1 : σ''.nat = σ'.nat := funext fun j => F1.1 j not_false
  refine ⟨by rw [n1, hkt], by rw [n1, hkd], by rw [n1, hk1], ⟨by simp [d1, hd'], fun i' hi' hd => ?_, ?_⟩⟩
  · simp only [Env.setNat_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · rw [F1.2.2.1 aXm i' (fun h => by rw [hkt] at h; omega)]; exact hy i' hlt hd
    · rw [hkt] at e1; rw [e1]; simp [tzUpd]
  · have F1' : FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni) (fun b k' => b = aXm ∧ k' < k + 1) σ' σ'' :=
      F1.mono (fun _ h => h) (fun _ h => h.elim) (fun b k' h => ⟨h.1, by rw [h.2, hkt]; omega⟩)
    exact ((hF.mono (fun _ h => h) (fun _ h => h) (fun b k' h => ⟨h.1, by omega⟩)).trans F1').setNat rfl _

/-! ## The rows of `T̂` -/

/-- Row `i` of `T̂`: for `l < d`, `r := d i + l`, then the lower entry if `l < i`, `0` if `i < l`, the diagonal entry
if `l = i`. -/
def xupdRow (L : Layout) (z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none : ℕ) : XCmd :=
  xforN nl nd none (.seq (xnmul nr nd ni) (.seq (.prim (.frag (.nadd nr nr nl)))
    (.ifN nl ni (xent L z v sMB sBh t aXt nr (ieLow aXt aA aY nr ni nl sPB sBb sP2 sPj))
      (.ifN ni nl (toX (VL.aset L aXt nr z))
        (xent L z v sAl sBh t aXt nr (ieDiag aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8))))))

set_option maxHeartbeats 4000000 in
theorem XV.updRow {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none E : ℕ} {c : DC} {Xp : PosZ d}
    {A Y : Fin d → ℤ} {Bb : ℤ} {i : ℕ} (hi : i < d)
    (hz : z < t) (hv : v < t) (h1 : sPB < t) (h2 : sBb < t) (h3 : sP2 < t) (h4 : sPj < t) (h5 : sPG < t)
    (h6 : sD8 < t) (h7 : sAl < t) (h8 : sBh < t) (h9 : sMB < t)
    (hvs : [v, z, sPB, sBb, sP2, sPj, sPG, sD8, sAl, sBh, sMB].Nodup)
    (hS : t + 26 ≤ L.NS) (hz0 : σ.sc z = 0) (hXt : aXt < L.NA) (hA : aA < L.NA) (hY : aY < L.NA)
    (hAX : aA ≠ aXt) (hYX : aY ≠ aXt)
    (hni : ni < L.NN) (hnl : nl < L.NN) (hnr : nr < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [ni, nl, nr, nd, none].Nodup) (hσi : σ.nat ni = i)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eX : ∀ l : Fin d, σ.arr aXt (d * i + l) = Xp.2 ⟨i, hi⟩ l) (eA : ∀ l : Fin d, σ.arr aA l = A l)
    (eY : ∀ l : Fin d, σ.arr aY l = Y l)
    (ePB : σ.sc sPB = c.PB) (eBb : σ.sc sBb = Bb) (eP2 : σ.sc sP2 = c.P2) (ePj : σ.sc sPj = c.Pj)
    (ePG : σ.sc sPG = c.PG) (eD8 : σ.sc sD8 = ((8 * c.dd : ℤ) : ℝ)) (eAl : σ.sc sAl = c.Al)
    (eBh : σ.sc sBh = c.Bh) (eMB : σ.sc sMB = ((-c.Bh : ℤ) : ℝ))
    (bX : ∀ l, |Xp.2 ⟨i, hi⟩ l| ≤ 2 ^ E) (bA : ∀ l, |A l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E)
    (bPB : |c.PB| ≤ 2 ^ E) (bBb : |Bb| ≤ 2 ^ E) (bP2 : |c.P2| ≤ 2 ^ E) (bPj : |c.Pj| ≤ 2 ^ E)
    (bPG : |c.PG| ≤ 2 ^ E) (bD8 : |8 * c.dd| ≤ 2 ^ E) (bAl : |c.Al| ≤ 2 ^ E) (bBh : |c.Bh| ≤ 2 ^ E)
    (hE : 6 * E + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xupdRow L z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none) σ
      (d * (44 + 3) + 3)
      (fun σ' => (∀ l : Fin d, σ'.arr aXt (d * i + l) = (tzUpd c Xp A Y Bb).2 ⟨i, hi⟩ l) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = nl ∨ j = nr)
          (fun b k => b = aXt ∧ d * i ≤ k ∧ k < d * i + d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hvs hne
  obtain ⟨⟨vz, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩, -⟩ := hvs
  obtain ⟨⟨il, ir, id, io⟩, ⟨lr, ld, lo⟩, ⟨rd, ro⟩, dO⟩ := hne
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hcell : ∀ l < d, d * i + l < asz d := fun l hl => by unfold asz; nlinarith
  have hdi : d * i < 2 ^ ℓa := by nlinarith
  have hEl : (2 : ℤ) ^ E < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have bBh' : |c.Bh| < 2 ^ ℓ := lt_of_le_of_lt bBh hEl
  have bMB : |-c.Bh| < 2 ^ ℓ := by rw [abs_neg]; exact bBh'
  have bAl' : |c.Al| < 2 ^ ℓ := lt_of_le_of_lt bAl hEl
  let Fr : ℕ → ℕ → ℕ → Prop := fun k b c' => b = aXt ∧ d * i ≤ c' ∧ c' < d * i + k
  let J : ℕ → Env d → Prop := fun k σ' => σ'.draws = σ.draws ∧
    (∀ l' (_ : l' < k) (hd : l' < d), σ'.arr aXt (d * i + l') = (tzUpd c Xp A Y Bb).2 ⟨i, hi⟩ ⟨l', hd⟩) ∧
    FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = nl ∨ j = nr) (Fr k) σ σ'
  refine XV.mono (XV.forN hL hnl hnd hno ld lo d 44 (by omega) J σ hσd hσ1
    ⟨rfl, fun l' h => absurd h (Nat.not_lt_zero _),
      (FrameA.refl (fun y => y = v ∨ t ≤ y) (fun j => j = nl ∨ j = nr) (Fr 0) σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd', hy, hF⟩, _⟩ => ⟨fun l => hy l l.2 l.2, hd', hF⟩
  intro k hk σ' ⟨hd', hy, hF⟩ hkt hkd hk1
  have sk : ∀ y, y < t → y ≠ v → σ'.sc y = σ.sc y := fun y hy hyv => hF.2.1 y (by omega)
  have ei : σ'.nat ni = i := by rw [hF.1 ni (by omega), hσi]
  refine XV.mono (K := 1 + (1 + 42)) (XV.seq (XV.nmul hL (i := nr) (a := nd) (b := ni) hnr hnd hni
    (by rw [hkd]; omega) (by rw [ei]; omega) (by rw [hkd, ei]; exact hdi)) fun σ1 e1 => ?_) (by norm_num)
    fun _ h => h
  have n1 : σ1.nat nr = d * i := by rw [e1, Env.setNat_nat, ite_eq_left_of_eq_true _ _ (eq_self _), hkd, ei]
  have n1' : ∀ j, j ≠ nr → σ1.nat j = σ'.nat j := fun j hj => by rw [e1, Env.setNat_nat, ite_eq_right_of_eq_false _ _ (eq_false hj)]
  refine XV.seq (XV.nadd hL (i := nr) (a := nr) (b := nl) hnr hnr hnl (by rw [n1]; exact hdi)
    (by rw [n1' nl lr, hkt]; omega)) fun σ2 e2 => ?_
  have r2 : σ2.nat nr = d * i + k := by rw [e2, Env.setNat_nat, ite_eq_left_of_eq_true _ _ (eq_self _), n1, n1' nl lr, hkt]
  have l2 : σ2.nat nl = k := by rw [e2, Env.setNat_nat, ite_eq_right_of_eq_false _ _ (eq_false lr), n1' nl lr, hkt]
  have i2 : σ2.nat ni = i := by rw [e2, Env.setNat_nat, ite_eq_right_of_eq_false _ _ (eq_false ir), n1' ni ir, ei]
  have d2 : σ2.nat nd = d := by
    rw [e2, Env.setNat_nat, ite_eq_right_of_eq_false _ _ (eq_false fun h => rd h.symm), n1' nd (fun h => rd h.symm), hkd]
  have o2 : σ2.nat none = 1 := by
    rw [e2, Env.setNat_nat, ite_eq_right_of_eq_false _ _ (eq_false fun h => ro h.symm), n1' none (fun h => ro h.symm), hk1]
  have s2 : σ2.sc = σ'.sc := by rw [e2, e1]; rfl
  have a2 : σ2.arr = σ'.arr := by rw [e2, e1]; rfl
  have dr2 : σ2.draws = σ'.draws := by rw [e2, e1]; rfl
  have F2 : FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = nl ∨ j = nr) (Fr k) σ σ2 := by
    rw [e2, e1]; exact (hF.setNat (Or.inr rfl) _).setNat (Or.inr rfl) _
  have eXk : σ2.arr aXt (d * i + k) = Xp.2 ⟨i, hi⟩ ⟨k, hk⟩ := by
    rw [a2, hF.2.2.1 aXt (d * i + k) (fun h => by omega), eX ⟨k, hk⟩]
  have eAi : σ2.arr aA i = A ⟨i, hi⟩ := by rw [a2, hF.2.2.1 aA i (fun h => hAX h.1), eA ⟨i, hi⟩]
  have eYk : σ2.arr aY k = Y ⟨k, hk⟩ := by rw [a2, hF.2.2.1 aY k (fun h => hYX h.1), eY ⟨k, hk⟩]
  have eYi : σ2.arr aY i = Y ⟨i, hi⟩ := by rw [a2, hF.2.2.1 aY i (fun h => hYX h.1), eY ⟨i, hi⟩]
  have sk2 : ∀ y, y < t → y ≠ v → σ2.sc y = σ.sc y := fun y hy hyv => by rw [s2]; exact sk y hy hyv
  have z2 : σ2.sc z = 0 := by rw [sk2 z hz (fun h => vz h.symm), hz0]
  have hk2 : σ2.nat nr < asz d := by rw [r2]; exact hcell k hk
  -- the closing step, common to the three branches
  have close : ∀ σ3 : Env d, ∀ w : ℤ, w = (tzUpd c Xp A Y Bb).2 ⟨i, hi⟩ ⟨k, hk⟩ →
      σ3.arr aXt (σ2.nat nr) = (w : ℝ) → σ3.draws = σ2.draws →
      FrameA (fun y => y = v ∨ t ≤ y) (fun _ => False) (fun b k' => b = aXt ∧ k' = σ2.nat nr) σ2 σ3 →
      σ3.nat nl = k ∧ σ3.nat nd = d ∧ σ3.nat none = 1 ∧ J (k + 1) (σ3.setNat nl (k + 1)) := by
    intro σ3 w hw e3 dd3 F3
    have n3 : σ3.nat = σ2.nat := funext fun j => F3.1 j not_false
    refine ⟨by rw [n3, l2], by rw [n3, d2], by rw [n3, o2], by rw [Env.setNat_draws, dd3, dr2, hd'],
      fun l' hl' hd => ?_, ?_⟩
    · rw [Env.setNat_arr]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with hlt | rfl
      · rw [F3.2.2.1 aXt _ (fun h => by rw [r2] at h; omega), a2]; exact hy l' hlt hd
      · rw [r2] at e3; rw [e3, hw]
    · have F3' : FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = nl ∨ j = nr) (Fr (k + 1)) σ2 σ3 :=
        F3.mono (fun _ h => h) (fun _ h => h.elim) (fun b k' h => ⟨h.1, by rw [h.2, r2]; omega,
          by rw [h.2, r2]; omega⟩)
      exact ((F2.mono (fun _ h => h) (fun _ h => h) (fun b k' h => ⟨h.1, h.2.1, by omega⟩)).trans F3').setNat
        (Or.inl rfl) _
  rcases lt_trichotomy k i with hki | hki | hki
  · -- the lower entry
    refine XV.mono (XV.ifN_t hL hnl hni (by rw [l2]; omega) (by rw [i2]; omega) (by rw [l2, i2]; exact hki)
      (XV.ent (E := E) hL (e := ieLow aXt aA aY nr ni nl sPB sBb sP2 sPj)
        (val := Xp.2 ⟨i, hi⟩ ⟨k, hk⟩ - tzRLow A Y Bb c.PB c.P2 ⟨i, hi⟩ ⟨k, hk⟩ * c.Pj) (lov := -c.Bh) (hiv := c.Bh)
        (by simp only [ieLow, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, and_true, hXt, hA, hY, hni,
          hnl, hnr]; omega)
        hz hv h9 h8 v9 v8 vz (by rw [ieLow_scr]; omega) z2
        (by simp only [ieLow, IE.Leaves, r2, i2, l2, eXk, eAi, eYk, sk2 sPB h1 (Ne.symm v1),
          sk2 sBb h2 (Ne.symm v2), sk2 sP2 h3 (Ne.symm v3), sk2 sPj h4 (Ne.symm v4), ePB, eBb, eP2, ePj,
          Int.cast_inj, exists_eq_left', hcell k hk, hdl i hi, hdl k hk, bX, bA, bY, bPB, bBb, bP2, bPj, and_self])
        (by simp only [ieLow, IE.top, IE.mag]; omega)
        (by
          simp only [ieLow, IE.eval, RealRAM.Op2.eval, r2, i2, l2, eXk, eAi, eYk, sk2 sPB h1 (Ne.symm v1),
            sk2 sBb h2 (Ne.symm v2), sk2 sP2 h3 (Ne.symm v3), sk2 sPj h4 (Ne.symm v4), ePB, eBb, eP2, ePj, tzRLow]
          norm_cast; rw [Int.floor_intCast, Int.floor_intCast])
        (by rw [sk2 sMB h9 (Ne.symm v9), eMB]) (by rw [sk2 sBh h8 (Ne.symm v8), eBh]) bMB bBh' hXt hnr hk2))
      (by rw [ieLow_units]; norm_num) fun σ3 ⟨e3, dd3, F3⟩ => close σ3 _ ?_ e3 dd3 F3
    simp [tzUpd, hki]
  · -- the diagonal entry
    have eXi : σ2.arr aXt (d * i + k) = Xp.2 ⟨i, hi⟩ ⟨i, hi⟩ := by
      rw [eXk, show (⟨k, hk⟩ : Fin d) = ⟨i, hi⟩ from Fin.ext hki]
    refine XV.mono (XV.ifN_f hL hnl hni (by rw [l2]; omega) (by rw [i2]; omega) (by rw [l2, i2]; omega)
      (XV.ifN_f hL hni hnl (by rw [i2]; omega) (by rw [l2]; omega) (by rw [l2, i2]; omega)
      (XV.ent (E := E) hL (e := ieDiag aXt aA aY nr ni sPB sBb sP2 sPj sPG sD8)
        (val := Xp.2 ⟨i, hi⟩ ⟨i, hi⟩ - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (Xp.2 ⟨i, hi⟩ ⟨i, hi⟩) ⟨i, hi⟩ * c.Pj)
        (lov := c.Al) (hiv := c.Bh)
        (by simp only [ieDiag, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, and_true, hXt, hA, hY, hni,
          hnr]; omega)
        hz hv h7 h8 v7 v8 vz (by rw [ieDiag_scr]; omega) z2
        (by simp only [ieDiag, IE.Leaves, r2, i2, eXi, eAi, eYi, sk2 sPB h1 (Ne.symm v1),
          sk2 sBb h2 (Ne.symm v2), sk2 sP2 h3 (Ne.symm v3), sk2 sPj h4 (Ne.symm v4), sk2 sPG h5 (Ne.symm v5),
          sk2 sD8 h6 (Ne.symm v6), ePB, eBb, eP2, ePj, ePG, eD8,
          Int.cast_inj, exists_eq_left', hcell k hk, hdl i hi, bX, bA, bY, bPB, bBb, bP2, bPj, bPG, bD8, and_self])
        (by simp only [ieDiag, IE.top, IE.mag]; omega)
        (by
          simp only [ieDiag, IE.eval, RealRAM.Op2.eval, r2, i2, eXi, eAi, eYi, sk2 sPB h1 (Ne.symm v1),
            sk2 sBb h2 (Ne.symm v2), sk2 sP2 h3 (Ne.symm v3), sk2 sPj h4 (Ne.symm v4), sk2 sPG h5 (Ne.symm v5),
            sk2 sD8 h6 (Ne.symm v6), ePB, eBb, eP2, ePj, ePG, eD8, tzRDiag]
          norm_cast; rw [Int.floor_intCast, Int.floor_intCast])
        (by rw [sk2 sAl h7 (Ne.symm v7), eAl]) (by rw [sk2 sBh h8 (Ne.symm v8), eBh]) bAl' bBh' hXt hnr hk2)))
      (by rw [ieDiag_units]) fun σ3 ⟨e3, dd3, F3⟩ => close σ3 _ ?_ e3 dd3 F3
    have hfk : (⟨k, hk⟩ : Fin d) = ⟨i, hi⟩ := Fin.ext hki
    rw [hfk]; simp [tzUpd]
  · -- above the diagonal: `0`
    refine XV.mono (XV.ifN_f hL hnl hni (by rw [l2]; omega) (by rw [i2]; omega) (by rw [l2, i2]; omega)
      (XV.ifN_t hL hni hnl (by rw [i2]; omega) (by rw [l2]; omega) (by rw [l2, i2]; exact hki)
        (XV.aset hL hXt hnr (by omega : z < L.NS) hk2 (by rw [z2]; simp)))) (by norm_num)
      fun σ3 e3 => ?_
    subst e3
    refine close _ 0 (by simp [tzUpd, Fin.ext_iff, hki.ne', not_lt.2 hki.le]) (by simp [z2]) (by simp)
      ((FrameA.refl (fun y => y = v ∨ t ≤ y) (fun _ => False) (fun b k' => b = aXt ∧ k' = σ2.nat nr) σ2).setArr
        ⟨rfl, rfl⟩ _)

/-! ## All rows of `T̂` -/

/-- `for i < d`: row `i` of `T̂`. -/
def xtupdT (L : Layout) (z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none : ℕ) : XCmd :=
  xforN ni nd none (xupdRow L z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none)

set_option maxHeartbeats 2000000 in
theorem XV.tupdT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none E : ℕ} {c : DC} {Xp : PosZ d}
    {A Y : Fin d → ℤ} {Bb : ℤ}
    (hz : z < t) (hv : v < t) (h1 : sPB < t) (h2 : sBb < t) (h3 : sP2 < t) (h4 : sPj < t) (h5 : sPG < t)
    (h6 : sD8 < t) (h7 : sAl < t) (h8 : sBh < t) (h9 : sMB < t)
    (hvs : [v, z, sPB, sBb, sP2, sPj, sPG, sD8, sAl, sBh, sMB].Nodup)
    (hS : t + 26 ≤ L.NS) (hz0 : σ.sc z = 0) (hXt : aXt < L.NA) (hA : aA < L.NA) (hY : aY < L.NA)
    (hAX : aA ≠ aXt) (hYX : aY ≠ aXt)
    (hni : ni < L.NN) (hnl : nl < L.NN) (hnr : nr < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [ni, nl, nr, nd, none].Nodup)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eX : ∀ i l : Fin d, σ.arr aXt (d * i + l) = Xp.2 i l) (eA : ∀ l : Fin d, σ.arr aA l = A l)
    (eY : ∀ l : Fin d, σ.arr aY l = Y l)
    (ePB : σ.sc sPB = c.PB) (eBb : σ.sc sBb = Bb) (eP2 : σ.sc sP2 = c.P2) (ePj : σ.sc sPj = c.Pj)
    (ePG : σ.sc sPG = c.PG) (eD8 : σ.sc sD8 = ((8 * c.dd : ℤ) : ℝ)) (eAl : σ.sc sAl = c.Al)
    (eBh : σ.sc sBh = c.Bh) (eMB : σ.sc sMB = ((-c.Bh : ℤ) : ℝ))
    (bX : ∀ i l, |Xp.2 i l| ≤ 2 ^ E) (bA : ∀ l, |A l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E)
    (bPB : |c.PB| ≤ 2 ^ E) (bBb : |Bb| ≤ 2 ^ E) (bP2 : |c.P2| ≤ 2 ^ E) (bPj : |c.Pj| ≤ 2 ^ E)
    (bPG : |c.PG| ≤ 2 ^ E) (bD8 : |8 * c.dd| ≤ 2 ^ E) (bAl : |c.Al| ≤ 2 ^ E) (bBh : |c.Bh| ≤ 2 ^ E)
    (hE : 6 * E + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xtupdT L z v t aXt aA aY sPB sBb sP2 sPj sPG sD8 sAl sBh sMB ni nl nr nd none) σ
      (d * (d * (44 + 3) + 3 + 3) + 3)
      (fun σ' => (∀ i l : Fin d, σ'.arr aXt (d * i + l) = (tzUpd c Xp A Y Bb).2 i l) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni ∨ j = nl ∨ j = nr) (fun b k => b = aXt ∧ k < d * d)
          σ σ') := by
  have hvs' := hvs
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hvs' hne'
  obtain ⟨⟨vz, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩, -⟩ := hvs'
  obtain ⟨⟨il, ir, id, io⟩, ⟨lr, ld, lo⟩, ⟨rd, ro⟩, dO⟩ := hne'
  let J : ℕ → Env d → Prop := fun k σ' => σ'.draws = σ.draws ∧
    (∀ i' (_ : i' < k) (hd : i' < d) (l : Fin d), σ'.arr aXt (d * i' + l) = (tzUpd c Xp A Y Bb).2 ⟨i', hd⟩ l) ∧
    FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni ∨ j = nl ∨ j = nr) (fun b c' => b = aXt ∧ c' < d * k) σ σ'
  refine XV.mono (XV.forN hL hni hnd hno id io d (d * (44 + 3) + 3) (by omega) J σ hσd hσ1
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      (FrameA.refl (fun y => y = v ∨ t ≤ y) (fun j => j = ni ∨ j = nl ∨ j = nr)
        (fun b c' => b = aXt ∧ c' < d * 0) σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd', hy, hF⟩, _⟩ => ⟨fun i l => hy i i.2 i.2 l, hd', hF⟩
  intro k hk σ' ⟨hd', hy, hF⟩ hkt hkd hk1
  have sk : ∀ y, y < t → y ≠ v → σ'.sc y = σ.sc y := fun y hy hyv => hF.2.1 y (by omega)
  have ea : ∀ b c', b ≠ aXt → σ'.arr b c' = σ.arr b c' := fun b c' hb => hF.2.2.1 b c' (fun h => hb h.1)
  refine XV.mono (XV.updRow (E := E) hL (i := k) (c := c) (Xp := Xp) (A := A) (Y := Y) (Bb := Bb) hk hz hv h1 h2
    h3 h4 h5 h6 h7 h8 h9 hvs hS (by rw [sk z hz (fun h => vz h.symm), hz0]) hXt hA hY hAX hYX hni hnl hnr hnd hno
    hne hkt hkd hk1 hda (fun l => by rw [hF.2.2.1 aXt _ (fun h => by omega), eX ⟨k, hk⟩ l])
    (fun l => by rw [ea aA l hAX, eA l]) (fun l => by rw [ea aY l hYX, eY l])
    (by rw [sk sPB h1 (Ne.symm v1), ePB]) (by rw [sk sBb h2 (Ne.symm v2), eBb])
    (by rw [sk sP2 h3 (Ne.symm v3), eP2]) (by rw [sk sPj h4 (Ne.symm v4), ePj])
    (by rw [sk sPG h5 (Ne.symm v5), ePG]) (by rw [sk sD8 h6 (Ne.symm v6), eD8])
    (by rw [sk sAl h7 (Ne.symm v7), eAl]) (by rw [sk sBh h8 (Ne.symm v8), eBh])
    (by rw [sk sMB h9 (Ne.symm v9), eMB]) (bX ⟨k, hk⟩) bA bY bPB bBb bP2 bPj bPG bD8 bAl bBh hE) le_rfl
    fun σ'' ⟨e1, d1, F1⟩ => ?_
  have n1 : ∀ j, j ≠ nl → j ≠ nr → σ''.nat j = σ'.nat j := fun j g1 g2 => F1.1 j (by tauto)
  refine ⟨by rw [n1 ni il ir, hkt], by rw [n1 nd (fun h => ld h.symm) (fun h => rd h.symm), hkd],
    by rw [n1 none (fun h => lo h.symm) (fun h => ro h.symm), hk1], by rw [Env.setNat_draws, d1, hd'],
    fun i' hi' hd l => ?_, ?_⟩
  · rw [Env.setNat_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · have g1 := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hlt)
      have g2 := l.2
      rw [Nat.mul_succ] at g1
      rw [F1.2.2.1 aXt _ (fun h => by omega)]; exact hy i' hlt hd l
    · exact e1 l
  · have F1' : FrameA (fun y => y = v ∨ t ≤ y) (fun j => j = ni ∨ j = nl ∨ j = nr)
        (fun b c' => b = aXt ∧ c' < d * (k + 1)) σ' σ'' :=
      F1.mono (fun _ h => h) (fun _ h => Or.inr h) (fun b c' h => ⟨h.1, by rw [Nat.mul_succ]; omega⟩)
    have g : d * k ≤ d * (k + 1) := Nat.mul_le_mul_left d (Nat.le_succ k)
    exact ((hF.mono (fun _ h => h) (fun _ h => h) (fun b c' h => ⟨h.1, by omega⟩)).trans F1').setNat
      (Or.inl rfl) _

end AdversarialBco.Bit.Transfer
