/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriStep
public import AdversarialBco.Bit.Transfer.XTriDraw
public import AdversarialBco.Bit.Transfer.XTriSem
public import AdversarialBco.Bit.Transfer.XBLR1

@[expose] public section

/-!
# TRI-M, the pieces of the core of a stage on the machine

* `xfill`, `XV.fill`: a value into the cells `st k`, `k < N`; `xacc`, `XV.acc`: `a_B[k] += a_X[k]`, `k < N`.
* `tmext`: a matrix on the cells `d i + l`; the cells of vectors and matrices (`vec_cells`, `mat_cells`).
* `xscalI`, `XV.scalI`: `a_B := v I`; `XV.mapExT`: `xmapE` with the frame of exactly the cells written.
* `tzYc`: draw `t` of the core, read from the coins at `c`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-! ## Two array loops -/

/-- `nr := 0`; for `k < N`: `a_B[st k] := s`. -/
def xfill (L : Layout) (z t s aB nr nst nk nn none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (.sc s) aB nr nst nk nn none)

theorem XV.fill {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t s aB nr nst nk nn none N st E : ℕ} {v : ℤ}
    (hz : z < t) (hs : s < t) (hS : t + 1 ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσs : σ.nat nst = st) (hst : 0 < st)
    (hcell : ∀ k < N, st * k < asz d) (hNa : N < 2 ^ ℓa) (hra : st * N < 2 ^ ℓa) (hsa : st < 2 ^ ℓa)
    (hv : σ.sc s = v) (hvE : |v| ≤ 2 ^ E) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xfill L z t s aB nr nst nk nn none) σ (1 + (N * (1 + 6) + 3)) (fun σ' =>
      (∀ k < N, σ'.arr aB (st * k) = v) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < st * N) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne'
  refine XV.seq (XV.nconst hL hnr 0 (by positivity)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.mapE hL (z := z) (t := t) (e := .sc s) (aB := aB) (nr := nr) (nst := nst) (nk := nk)
    (nn := nn) (none := none) (E := E) (N := N) (base := 0) (st := st) (F := fun _ => v)
    (by simp only [IE.WF]; exact hs) hz (by simp only [IE.scr]; omega) (by rw [Env.setNat_sc, hz0]) hB hnr hnst
    hnk hnn hno hne hsr hsk (by rw [nat_setNat_ne _ (Ne.symm rn), hσn]) (by rw [nat_setNat_ne _ (Ne.symm ro), hσ1])
    (by rw [nat_setNat_eq]) (by rw [nat_setNat_ne _ hsr, hσs]) hst (by simpa using hcell) hNa (by simpa using hra)
    hsa (by simp only [IE.top]; exact hE) (fun k hk σ' F' _ _ _ => ?_)) (by simp only [IE.units]; omega) ?_
  · have : σ'.sc s = v := by rw [F'.2.1 _ (by omega), Env.setNat_sc, hv]
    exact ⟨⟨v, this, hvE⟩, by simp only [IE.eval, this]⟩
  · rintro σ' ⟨h1, -, h3, h4⟩
    exact ⟨fun k hk => by simpa using h1 k hk, h3,
      ((FrameA.refl (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < st * N) σ).setNat
        (Or.inr rfl) 0).trans (h4.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩))⟩

/-- `a_B[k] + a_X[k]`. -/
def ieAcc (aB aX nr : ℕ) : IE := .op .add (.arr aB nr) (.arr aX nr)

/-- `nr := 0`; for `k < N`: `a_B[k] := a_B[k] + a_X[k]`. -/
def xacc (L : Layout) (z t aB aX nr nst nk nn none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (ieAcc aB aX nr) aB nr nst nk nn none)

theorem XV.acc {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t aB aX nr nst nk nn none N E : ℕ} {U V : ℕ → ℤ}
    (hz : z < t) (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA) (hX : aX < L.NA)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσs : σ.nat nst = 1)
    (hcell : ∀ k < N, k < asz d) (hNa : N < 2 ^ ℓa)
    (eU : ∀ k < N, σ.arr aB k = U k) (eV : ∀ k < N, σ.arr aX k = V k)
    (bU : ∀ k < N, |U k| ≤ 2 ^ E) (bV : ∀ k < N, |V k| ≤ 2 ^ E) (hE : E + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xacc L z t aB aX nr nst nk nn none) σ (1 + (N * (5 + 6) + 3)) (fun σ' =>
      (∀ k < N, σ'.arr aB k = U k + V k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < N) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne'
  have h1a : 1 < 2 ^ ℓa := by have := hL.1; omega
  refine XV.seq (XV.nconst hL hnr 0 (by positivity)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.mapE hL (z := z) (t := t) (e := ieAcc aB aX nr) (aB := aB) (nr := nr) (nst := nst) (nk := nk)
    (nn := nn) (none := none) (E := E) (N := N) (base := 0) (st := 1) (F := fun k => U k + V k)
    (by simp only [ieAcc, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; exact ⟨⟨hB, hnr⟩, hX, hnr⟩)
    hz (by simp only [ieAcc, IE.scr]; omega) (by rw [Env.setNat_sc, hz0]) hB hnr hnst
    hnk hnn hno hne hsr hsk (by rw [nat_setNat_ne _ (Ne.symm rn), hσn]) (by rw [nat_setNat_ne _ (Ne.symm ro), hσ1])
    (by rw [nat_setNat_eq]) (by rw [nat_setNat_ne _ hsr, hσs]) one_pos (by simpa using hcell) hNa
    (by simpa using hNa) h1a (by simp only [ieAcc, IE.top, IE.mag]; omega) (fun k hk σ' F' _ _ hr => ?_))
    (by simp only [ieAcc, IE.units]; omega) ?_
  · have hr' : σ'.nat nr = k := by omega
    have u : σ'.arr aB k = U k := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, eU k hk]
    have v : σ'.arr aX k = V k := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, eV k hk]
    refine ⟨⟨⟨by rw [hr']; exact hcell k hk, U k, by rw [hr', u], bU k hk⟩,
      ⟨by rw [hr']; exact hcell k hk, V k, by rw [hr', v], bV k hk⟩⟩, ?_⟩
    simp only [ieAcc, IE.eval, RealRAM.Op2.eval, hr', u, v]
    push_cast; ring
  · rintro σ' ⟨h1, -, h3, h4⟩
    exact ⟨fun k hk => by simpa using h1 k hk, h3,
      ((FrameA.refl (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < N) σ).setNat
        (Or.inr rfl) 0).trans (h4.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩))⟩

/-! ## Matrices on the cells -/

/-- The matrix `M` on the cells `d i + l` (`0` past `d²`). -/
def tmext (M : Matrix (Fin d) (Fin d) ℤ) (k : ℕ) : ℤ :=
  if h : k < d * d then
    M ⟨k / d, Nat.div_lt_of_lt_mul h⟩ ⟨k % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))⟩
  else 0

theorem tmext_cell (M : Matrix (Fin d) (Fin d) ℤ) (i l : Fin d) : tmext M (d * i + l) = M i l := by
  have hd : 0 < d := Fin.pos i
  have h : d * i + l < d * d := by
    have := i.2; have := l.2
    calc d * i + l < d * i + d := by omega
      _ = d * (i + 1) := by ring
      _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)
  have e1 : (d * i + l) / d = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt l.2, zero_add]
  have e2 : (d * i + l) % d = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l.2]
  unfold tmext
  rw [dif_pos h]
  congr 1 <;> ext <;> simp [e1, e2]

theorem tmext_abs_le {M : Matrix (Fin d) (Fin d) ℤ} {B : ℤ} (hB : 0 ≤ B) (h : ∀ i l, |M i l| ≤ B) (k : ℕ) :
    |tmext M k| ≤ B := by
  unfold tmext; split_ifs
  · exact h _ _
  · simpa using hB

theorem cell_sq {k : ℕ} (hk : k < d * d) : k < asz d := by unfold asz; nlinarith

theorem cell_dil (i l : Fin d) : d * (i : ℕ) + l < d * d := by
  have := i.2; have := l.2
  calc d * (i : ℕ) + l < d * i + d := by omega
    _ = d * (i + 1) := by ring
    _ ≤ d * d := Nat.mul_le_mul_left _ (by omega)

theorem vec_cells {f : ℕ → ℝ} {x : Fin d → ℤ} (h : ∀ l : Fin d, f l = x l) : ∀ k < d, f k = vext x k :=
  fun k hk => by rw [vext_lt _ hk]; exact h ⟨k, hk⟩

theorem mat_cells {f : ℕ → ℝ} {M : Matrix (Fin d) (Fin d) ℤ} (h : ∀ i l : Fin d, f (d * i + l) = M i l) :
    ∀ k < d * d, f k = tmext M k := fun k hk => by
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have := h ⟨k / d, Nat.div_lt_of_lt_mul hk⟩ ⟨k % d, Nat.mod_lt _ hd⟩
  rw [← tmext_cell M] at this
  simpa only [Nat.div_add_mod] using this

/-! ## The exact frame of `xmapE` (the rule `XV.mapEx`, restated here) -/

set_option maxHeartbeats 1000000 in
/-- `xmapE` with the frame of exactly the cells written. -/
theorem XV.mapExT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t aB nr nst nk nn none E N base st : ℕ} {e : IE} {F : ℕ → ℤ}
    (hw : e.WF L t) (hz : z < t) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st) (hst : 0 < st)
    (hcell : ∀ k < N, base + st * k < asz d) (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa)
    (hsa : st < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr)
        (fun b c => b = aB ∧ ∃ k' < k, c = base + st * k') σ σ' → σ'.draws = σ.draws →
        σ'.nat nk = k → σ'.nat nr = base + st * k → e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xmapE L z t e aB nr nst nk nn none) σ (N * (e.units + 6) + 3) (fun σ' =>
      (∀ k < N, σ'.arr aB (base + st * k) = F k) ∧ σ'.nat nr = base + st * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ ∃ k' < N, c = base + st * k')
        σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (e.units + (2 + 1)) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      (∀ k' < k, σ'.arr aB (base + st * k') = F k') ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ ∃ k' < k, c = base + st * k') σ σ')
    σ hσn hσ1 ⟨by simp [rk, hσr], rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) (by ring_nf; omega)
    fun σ' ⟨⟨hr, hd, hk, hF'⟩, _⟩ => ⟨hk, hr, hd, hF'⟩
  intro k hk σ' ⟨hr, hd, hkk, hF'⟩ hkt hkn hk1
  obtain ⟨hl, hv⟩ := hF k hk σ' hF' hd hkt hr
  have hst' : σ'.nat nst = st := by rw [hF'.1 nst (by omega), hσs]
  refine XV.seq (XV.ieRun (E := E) hL (x := t) (t := t + 1) (hw.mono (by omega)) (by omega) (by omega) hS
    (by rw [hF'.2.1 z (by omega), hz0]) hl htop hv) fun σ1 ⟨v1, b1, d1, P1⟩ => ?_
  have n1 : σ1.nat = σ'.nat := funext fun j => P1.1 j not_false
  have hkN : base + st * k < base + st * N := by
    have := Nat.mul_lt_mul_of_pos_left hk hst; omega
  refine XV.seq (XV.aset hL (a := aB) (i := nr) (x := t) hB hnr (by omega)
    (by rw [n1, hr]; exact hcell k hk) (by rw [v1]; exact XV.abs_int_lt b1)) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := nst) hnr hnr hnst
    (by simp only [Env.setArr_nat, n1, hr]; omega) (by simp only [Env.setArr_nat, n1, hst']; exact hsa)) le_rfl
    fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [Ne.symm rk, hkt, n1], by simp [Ne.symm rn, hkn, n1], by simp [Ne.symm ro, hk1, n1], ?_, ?_, ?_,
    ?_⟩
  · simp [rk, hr, hst', n1]; ring
  · simp [d1, hd]
  · intro k' hk'
    simp only [Env.setNat_arr, Env.setArr_arr, Env.setArr_nat, n1, hr, P1.2.2.1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
    · have : base + st * k' ≠ base + st * k := by
        have := Nat.mul_lt_mul_of_pos_left hlt hst; omega
      simp only [this, and_false, ite_false]; exact hkk k' hlt
    · simp only [and_self, ite_true, v1]
  · have hP : FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr)
        (fun b c => b = aB ∧ ∃ k' < k + 1, c = base + st * k') σ' σ1 :=
      FrameA.ofP (P1.mono (fun y hy => by omega) (fun _ h => h.elim))
    refine (((hF'.mono (fun _ h => h) (fun _ h => h)
      (fun b c h => ⟨h.1, h.2.imp fun k' hk' => ⟨Nat.lt_succ_of_lt hk'.1, hk'.2⟩⟩)).trans
      hP).setArr ⟨rfl, k, Nat.lt_succ_self k, by simp only [n1, hr]⟩ _ |>.setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

theorem diag_cellT {d i k k' : ℕ} (_hi : i < d) (hk : k < d) (hk' : k' < d) (e : d * i + k = 0 + (d + 1) * k') :
    i = k := by
  have h1 : (d * i + k) % d = k := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk
  have h2 : (0 + (d + 1) * k') % d = k' := by
    rw [show 0 + (d + 1) * k' = d * k' + k' by ring, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk'
  have hkk : k = k' := by rw [← h1, ← h2, e]
  subst hkk
  have : d * i = d * k := by
    have : d * i + k = d * k + k := by rw [e]; ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-! ## A scalar matrix -/

/-- `a_B := v I` (`v` in the slot `s`): zero the `d²` cells, then the diagonal with the stride `d + 1`. -/
def xscalI (L : Layout) (z t s aB nr n1 nd1 nk nd ndd none : ℕ) : XCmd :=
  .seq (xfill L z t z aB nr n1 nk ndd none)
  (.seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (.sc s) aB nr nd1 nk nd none))

set_option maxHeartbeats 1000000 in
theorem XV.scalI {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t s aB nr n1 nd1 nk nd ndd none E : ℕ} {v : ℤ}
    (hz : z < t) (hs : s < t) (hS : t + 1 ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hn1 : n1 < L.NN) (hnd1 : nd1 < L.NN) (hnk : nk < L.NN) (hnd : nd < L.NN)
    (hndd : ndd < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nd, ndd, none].Nodup) (h1r : n1 ≠ nr) (h1k : n1 ≠ nk) (hd1r : nd1 ≠ nr) (hd1k : nd1 ≠ nk)
    (hσd : σ.nat nd = d) (hσdd : σ.nat ndd = d * d) (hσ1 : σ.nat none = 1) (hσ1' : σ.nat n1 = 1)
    (hσd1 : σ.nat nd1 = d + 1) (hda : d * d + d < 2 ^ ℓa)
    (hv : σ.sc s = v) (hvE : |v| ≤ 2 ^ E) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xscalI L z t s aB nr n1 nd1 nk nd ndd none) σ
      (1 + (d * d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3))) (fun σ' =>
      (∀ i l : Fin d, σ'.arr aB (d * i + l) = ((v • (1 : Matrix (Fin d) (Fin d) ℤ)) i l : ℤ)) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < d * d) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨rk, rd, rdd, ro⟩, ⟨kd, kdd, ko⟩, ⟨ddd, dno⟩, ddo⟩ := hne'
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  refine XV.seq (XV.fill hL (z := z) (t := t) (s := z) (aB := aB) (nr := nr) (nst := n1) (nk := nk) (nn := ndd)
    (none := none) (N := d * d) (st := 1) (E := E) (v := 0) hz hz hS hz0 hB hnr hn1 hnk hndd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) h1r h1k hσdd hσ1 hσ1' one_pos
    (fun k hk => by rw [one_mul]; exact cell_sq hk) (by omega) (by omega) hsa (by rw [hz0]; simp)
    (by simp) hE) fun σ1 ⟨z1, d1, F1⟩ => ?_
  refine XV.seq (XV.nconst hL hnr 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  have n2 : ∀ j, j ≠ nr → j ≠ nk → (σ1.setNat nr 0).nat j = σ.nat j := fun j h h' => by
    rw [nat_setNat_ne _ h, F1.1 _ (by omega)]
  have s2 : ∀ y, y < t → (σ1.setNat nr 0).sc y = σ.sc y := fun y hy => by
    rw [Env.setNat_sc, F1.2.1 _ (by omega)]
  refine XV.mono (XV.mapExT (E := E) (N := d) (base := 0) (st := d + 1) (F := fun _ => v) hL (z := z) (t := t)
    (e := .sc s) (aB := aB) (nr := nr) (nst := nd1) (nk := nk) (nn := nd) (none := none)
    (by simp only [IE.WF]; omega) hz (by simp only [IE.scr]; omega) (by rw [s2 _ hz, hz0]) hB hnr hnd1 hnk hnd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) hd1r hd1k (by rw [n2 _ (Ne.symm rd) (Ne.symm kd), hσd])
    (by rw [n2 _ (Ne.symm ro) (Ne.symm ko), hσ1]) (by rw [nat_setNat_eq]) (by rw [n2 _ hd1r hd1k, hσd1])
    (by omega) (fun k hk => by unfold asz; nlinarith [Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ d by omega)])
    (by nlinarith) (by nlinarith) (by nlinarith) (by simp only [IE.top]; exact hE)
    (fun k _ σ' hF _ _ _ => ⟨⟨v, by rw [hF.2.1 _ (by omega), s2 _ hs, hv], hvE⟩,
      by simp only [IE.eval]; rw [hF.2.1 _ (by omega), s2 _ hs, hv]⟩)) (by simp only [IE.units]; omega) ?_
  rintro σ3 ⟨z3, -, d3, F3⟩
  refine ⟨fun i l => ?_, by rw [d3, Env.setNat_draws, d1], ?_⟩
  · by_cases hil : i = l
    · subst hil
      have := z3 i i.isLt
      rw [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      rw [this]; simp [Matrix.smul_apply]
    · rw [F3.2.2.1 _ _ (fun h => by
          obtain ⟨_, k', hk', e⟩ := h
          exact hil (Fin.ext (diag_cellT i.isLt l.isLt hk' e))), Env.setNat_arr]
      have := z1 _ (cell_dil i l)
      rw [one_mul] at this
      rw [this]; simp [Matrix.smul_apply, hil]
  · exact (F1.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by rw [one_mul] at h; exact h.2⟩)).trans
      (((FrameA.refl (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ c < d * d) σ1).setNat
        (Or.inr rfl) 0).trans (F3.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by
          obtain ⟨_, k', hk', e⟩ := h
          rw [e]; nlinarith [Nat.mul_le_mul_left (d + 1) (show k' + 1 ≤ d by omega)]⟩)))

/-! ## The core -/

theorem gsAt_abs_le (cs : ℕ → Bool) (B c i : ℕ) : |gsAt cs B c i| ≤ 2 ^ (4 * gsm_prec B) := by
  unfold gsAt
  exact (BLM.gsSpec_abs_le B _ _ (by
    obtain ⟨h0, h1⟩ := readCoins_bounds cs (c + 2 * B * i) B
    rw [Int.toNat_lt h0]; exact_mod_cast h1)).1

/-- Draw `t` of the core, read from the coins at `c`. -/
def tzYc (cs : ℕ → Bool) (B c : ℕ) (t : ℕ) : Fin d → ℤ := fun i => gsAt cs B (c + 2 * B * d * t) i

end AdversarialBco.Bit.Transfer
