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
# TRI-M, the core of a stage on the machine

* `xfill`, `XV.fill`: a value into the cells `st k`, `k < N`; `xacc`, `XV.acc`: `a_B[k] += a_X[k]`, `k < N`.
* `tmext`: a matrix on the cells `d i + l`.
* `xcore`, `XV.core`: the start `X̂_0 = (0, P_G I)`, `Ŝ = 0`, then `2^{n_e}` times: `Ŝ += X̂`, a draw, a step
  (`XV.step1`); the sum `Ŝ` of the iterates (`tzSum`) in two arrays.
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

/-- The slots the core may change. -/
abbrev coS (o : ℕ) (y : ℕ) : Prop := o + 16 ≤ y ∧ y < o + 35 ∨ o + 40 ≤ y

/-- The registers the core may change (not `r + 12`, the bits of a coordinate of a draw). -/
abbrev coN (r : ℕ) (j : ℕ) : Prop := r + 3 ≤ j ∧ j < r + 12 ∨ r + 13 ≤ j ∧ j < r + 24

/-- The cells the core may change. -/
abbrev coA (d a : ℕ) (b k : ℕ) : Prop := a + 2 ≤ b ∧ b < a + 12 ∧ k < d * d + d

/-- One draw of the core: `Ŝ += X̂`, the draw, the step. -/
def xcoreBody (L : Layout) (row : XCmd) (o r a nd : ℕ) : XCmd :=
  .seq (xacc L (o + 1) (o + 40) (a + 4) (a + 2) (r + 4) r (r + 5) nd r)
  (.seq (xacc L (o + 1) (o + 40) (a + 5) (a + 3) (r + 4) r (r + 5) (r + 25) r)
  (.seq (xdraw L (o + 70) (r + 12) (a + 6) (r + 7) nd r) (xstep1 L row o r a nd)))

/-- The core: `X̂ := (0, P_G I)`, `Ŝ := 0`, then `N` draws (`N` in `r + 24`). -/
def xcore (L : Layout) (row : XCmd) (o r a nd : ℕ) : XCmd :=
  .seq (xfill L (o + 1) (o + 40) (o + 1) (a + 2) (r + 4) r (r + 5) nd r)
  (.seq (xscalI L (o + 1) (o + 40) (o + 6) (a + 3) (r + 4) r (r + 1) (r + 5) nd (r + 25) r)
  (.seq (xfill L (o + 1) (o + 40) (o + 1) (a + 4) (r + 4) r (r + 5) nd r)
  (.seq (xfill L (o + 1) (o + 40) (o + 1) (a + 5) (r + 4) r (r + 5) (r + 25) r)
  (xforN (r + 11) (r + 24) r (xcoreBody L row o r a nd)))))

/-- The units of one draw of the core. -/
abbrev coreBK (d M B : ℕ) : ℕ :=
  1 + (d * (5 + 6) + 3) + (1 + (d * d * (5 + 6) + 3) + (d * (bmUnits B + 2 + 3) + 3 + step1K d M))

/-- The units of the core. -/
abbrev coreK (d M N B : ℕ) : ℕ :=
  1 + (d * (1 + 6) + 3) + (1 + (d * d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3)) + (1 + (d * (1 + 6) + 3) +
    (1 + (d * d * (1 + 6) + 3) + (N * (coreBK d M B + 3) + 3))))

set_option maxHeartbeats 4000000 in
theorem XV.core {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {row : XCmd}
    {o r a nd M N B E : ℕ} {c : DC} {T : Matrix (Fin d) (Fin d) ℤ} {mu : Fin d → ℤ} {ra : ℕ → Fin d → ℤ}
    {rb : ℕ → ℤ}
    (hS : o + 113 ≤ L.NS) (hN : r + 26 ≤ L.NN) (hA : a + 12 ≤ L.NA) (hnd : nd < r)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσd1 : σ.nat (r + 1) = d + 1) (hσM : σ.nat (r + 2) = M)
    (hσB : σ.nat (r + 12) = B) (hσN : σ.nat (r + 24) = N) (hσdd : σ.nat (r + 25) = d * d)
    (hda : d * d + d < 2 ^ ℓa) (hMa : M < 2 ^ ℓa) (hNa : N < 2 ^ ℓa)
    (hB1 : 1 ≤ B) (hBa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (eZ : σ.sc (o + 1) = 0) (eO : σ.sc (o + 2) = 1) (eM : σ.sc (o + 3) = -1)
    (ePB : σ.sc (o + 4) = c.PB) (eP2 : σ.sc (o + 5) = c.P2) (ePG : σ.sc (o + 6) = c.PG)
    (ePj : σ.sc (o + 7) = c.Pj) (eR : σ.sc (o + 8) = c.R) (eMR : σ.sc (o + 9) = -c.R)
    (eAl : σ.sc (o + 10) = c.Al) (eBh : σ.sc (o + 11) = c.Bh) (eMB : σ.sc (o + 12) = ((-c.Bh : ℤ) : ℝ))
    (eD8 : σ.sc (o + 13) = ((8 * c.dd : ℤ) : ℝ))
    (eMu : ∀ l : Fin d, σ.arr a l = mu l) (eT : ∀ i l : Fin d, σ.arr (a + 1) (d * i + l) = T i l)
    (hrow : ∀ k < M, ∀ σ' : Env d, FrameA (coS o) (coN r) (coA d a) σ σ' → σ'.nat (r + 3) = k →
      XRunsB L X ℓa ℓ row σ' (18 * d + 29) (fun σ'' => (∀ l : Fin d, σ''.arr (a + 9) l = ra k l) ∧
        σ''.sc (o + 19) = rb k ∧ σ''.draws = σ'.draws ∧
        FrameA (rwS o) (rwN r) (fun b k' => b = a + 9 ∧ k' < d) σ' σ''))
    (hR : 0 ≤ c.R) (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al) (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG)
    (hPGB : c.PG ≤ c.Bh)
    (bT : ∀ i l, |T i l| ≤ 2 ^ E) (bMu : ∀ l, |mu l| ≤ 2 ^ E) (bR : ∀ k < M, ∀ l, |ra k l| ≤ 2 ^ E)
    (bB : ∀ k < M, |rb k| ≤ 2 ^ E) (bPB : |c.PB| ≤ 2 ^ E) (bP2 : |c.P2| ≤ 2 ^ E) (bPj : |c.Pj| ≤ 2 ^ E)
    (bBh : c.Bh ≤ 2 ^ E) (bD8 : |8 * c.dd| ≤ 2 ^ E) (b4p : 4 * gsm_prec B ≤ E) (bN : N ≤ 2 ^ E)
    (hE : 48 * E + 42 * d + 32 < ℓ) :
    XRunsB L X ℓa ℓ (xcore L row o r a nd) σ (coreK d M N B) (fun σ' =>
      (∀ l : Fin d, σ'.arr (a + 4) l = (tzSum c T mu ra rb M (tzYc X.wb.cs B σ.draws) N).1 l) ∧
      (∀ i l : Fin d, σ'.arr (a + 5) (d * i + l) = (tzSum c T mu ra rb M (tzYc X.wb.cs B σ.draws) N).2 i l) ∧
      σ'.draws = σ.draws + 2 * B * d * N ∧ FrameA (coS o) (coN r) (coA d a) σ σ') := by
  have hNA : ∀ k, k < 12 → a + k < L.NA := fun k h => by omega
  have hNN : ∀ k, k < 26 → r + k < L.NN := fun k h => by omega
  have hndN : nd < L.NN := by omega
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hE1 : E < ℓ := by omega
  have hBh0 : 0 ≤ c.Bh := hR.trans hRB
  have bBh' : |c.Bh| ≤ 2 ^ E := by rw [abs_of_nonneg hBh0]; exact bBh
  have bPG : |c.PG| ≤ 2 ^ E := by rw [abs_of_nonneg hPG]; exact hPGB.trans bBh
  have bRR : |c.R| ≤ 2 ^ E := by rw [abs_of_nonneg hR]; exact hRB.trans bBh
  have bAl : |c.Al| ≤ 2 ^ E := by rw [abs_of_pos hAl]; exact hAB.trans bBh
  have hcd : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  set Y := tzYc (d := d) X.wb.cs B σ.draws with hY
  -- `X̂_μ := 0`
  refine XV.seq (XV.fill hL (z := o + 1) (t := o + 40) (s := o + 1) (aB := a + 2) (nr := r + 4) (nst := r)
    (nk := r + 5) (nn := nd) (none := r) (N := d) (st := 1) (E := E) (v := 0) (by omega) (by omega) (by omega) eZ
    (hNA 2 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN
    (hNN 0 (by norm_num)) (by simp; omega) (by omega) (by omega) hσd hσ1 hσ1 one_pos
    (fun k hk => by rw [one_mul]; exact hcd k hk) (by omega) (by omega) hsa (by rw [eZ]; simp) (by simp) hE1)
    fun σ1 ⟨x1, d1, F1⟩ => ?_
  have G1 : FrameA (coS o) (coN r) (coA d a) σ σ1 := F1.mono (fun y h => by simp only [coS]; omega)
    (fun j h => by simp only [coN]; omega) (fun b k h => by simp only [coA]; omega)
  -- `X̂_T := P_G I`
  refine XV.seq (XV.scalI hL (z := o + 1) (t := o + 40) (s := o + 6) (aB := a + 3) (nr := r + 4) (n1 := r)
    (nd1 := r + 1) (nk := r + 5) (nd := nd) (ndd := r + 25) (none := r) (E := E) (v := c.PG) (by omega) (by omega)
    (by omega) (by rw [G1.2.1 _ (by simp only [coS]; omega), eZ]) (hNA 3 (by norm_num)) (hNN 4 (by norm_num))
    (hNN 0 (by norm_num)) (hNN 1 (by norm_num)) (hNN 5 (by norm_num)) hndN (hNN 25 (by norm_num))
    (hNN 0 (by norm_num)) (by simp; omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [G1.1 _ (by simp only [coN]; omega), hσd]) (by rw [G1.1 _ (by simp only [coN]; omega), hσdd])
    (by rw [G1.1 _ (by simp only [coN]; omega), hσ1]) (by rw [G1.1 _ (by simp only [coN]; omega), hσ1])
    (by rw [G1.1 _ (by simp only [coN]; omega), hσd1]) hda (by rw [G1.2.1 _ (by simp only [coS]; omega), ePG])
    bPG hE1) fun σ2 ⟨x2, d2, F2⟩ => ?_
  have G2 : FrameA (coS o) (coN r) (coA d a) σ σ2 := G1.trans (F2.mono (fun y h => by simp only [coS]; omega)
    (fun j h => by simp only [coN]; omega) (fun b k h => by simp only [coA]; omega))
  -- `Ŝ_μ := 0`
  refine XV.seq (XV.fill hL (z := o + 1) (t := o + 40) (s := o + 1) (aB := a + 4) (nr := r + 4) (nst := r)
    (nk := r + 5) (nn := nd) (none := r) (N := d) (st := 1) (E := E) (v := 0) (by omega) (by omega) (by omega)
    (by rw [G2.2.1 _ (by simp only [coS]; omega), eZ])
    (hNA 4 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN
    (hNN 0 (by norm_num)) (by simp; omega) (by omega) (by omega) (by rw [G2.1 _ (by simp only [coN]; omega), hσd])
    (by rw [G2.1 _ (by simp only [coN]; omega), hσ1]) (by rw [G2.1 _ (by simp only [coN]; omega), hσ1]) one_pos
    (fun k hk => by rw [one_mul]; exact hcd k hk) (by omega) (by omega) hsa
    (by rw [G2.2.1 _ (by simp only [coS]; omega), eZ]; simp) (by simp) hE1) fun σ3 ⟨x3, d3, F3⟩ => ?_
  have G3 : FrameA (coS o) (coN r) (coA d a) σ σ3 := G2.trans (F3.mono (fun y h => by simp only [coS]; omega)
    (fun j h => by simp only [coN]; omega) (fun b k h => by simp only [coA]; omega))
  -- `Ŝ_T := 0`
  refine XV.seq (XV.fill hL (z := o + 1) (t := o + 40) (s := o + 1) (aB := a + 5) (nr := r + 4) (nst := r)
    (nk := r + 5) (nn := r + 25) (none := r) (N := d * d) (st := 1) (E := E) (v := 0) (by omega) (by omega)
    (by omega) (by rw [G3.2.1 _ (by simp only [coS]; omega), eZ])
    (hNA 5 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) (hNN 25 (by norm_num))
    (hNN 0 (by norm_num)) (by simp) (by omega) (by omega) (by rw [G3.1 _ (by simp only [coN]; omega), hσdd])
    (by rw [G3.1 _ (by simp only [coN]; omega), hσ1]) (by rw [G3.1 _ (by simp only [coN]; omega), hσ1]) one_pos
    (fun k hk => by rw [one_mul]; exact cell_sq hk) (by omega) (by omega) hsa
    (by rw [G3.2.1 _ (by simp only [coS]; omega), eZ]; simp) (by simp) hE1) fun σ4 ⟨x4, d4, F4⟩ => ?_
  have G4 : FrameA (coS o) (coN r) (coA d a) σ σ4 := G3.trans (F4.mono (fun y h => by simp only [coS]; omega)
    (fun j h => by simp only [coN]; omega) (fun b k h => by simp only [coA]; omega))
  -- the draws
  have x2' : ∀ i l : Fin d, σ4.arr (a + 3) (d * i + l) = (tzIter c T mu ra rb M Y 0).2 i l := fun i l => by
    rw [F4.2.2.1 _ _ (by omega), F3.2.2.1 _ _ (by omega), x2]; rfl
  have x1' : ∀ l : Fin d, σ4.arr (a + 2) l = (tzIter c T mu ra rb M Y 0).1 l := fun l => by
    rw [F4.2.2.1 _ _ (by omega), F3.2.2.1 _ _ (by omega), F2.2.2.1 _ _ (by omega)]
    have := x1 l l.2; rw [one_mul] at this; rw [this]; rfl
  have s3' : ∀ l : Fin d, σ4.arr (a + 4) l = (tzSum c T mu ra rb M Y 0).1 l := fun l => by
    rw [F4.2.2.1 _ _ (by omega)]
    have := x3 l l.2; rw [one_mul] at this; rw [this]; simp [tzSum]
  have s4' : ∀ i l : Fin d, σ4.arr (a + 5) (d * i + l) = (tzSum c T mu ra rb M Y 0).2 i l := fun i l => by
    have := x4 _ (cell_dil i l); rw [one_mul] at this; rw [this]; simp [tzSum]
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ l : Fin d, σ'.arr (a + 2) l = (tzIter c T mu ra rb M Y t).1 l) ∧
    (∀ i l : Fin d, σ'.arr (a + 3) (d * i + l) = (tzIter c T mu ra rb M Y t).2 i l) ∧
    (∀ l : Fin d, σ'.arr (a + 4) l = (tzSum c T mu ra rb M Y t).1 l) ∧
    (∀ i l : Fin d, σ'.arr (a + 5) (d * i + l) = (tzSum c T mu ra rb M Y t).2 i l) ∧
    σ'.draws = σ.draws + 2 * B * d * t ∧ FrameA (coS o) (coN r) (coA d a) σ σ'
  refine XV.mono (XV.forN (L := L) (X := X) (ℓ := ℓ) (i := r + 11) (n := r + 24) (one := r)
    (body := xcoreBody L row o r a nd) hL (hNN 11 (by norm_num))
    (hNN 24 (by norm_num)) (hNN 0 (by norm_num)) (by omega) (by omega) N (coreBK d M B) hNa J σ4
    (by rw [G4.1 _ (by simp only [coN]; omega), hσN]) (by rw [G4.1 _ (by simp only [coN]; omega), hσ1])
    ⟨fun l => by rw [Env.setNat_arr, x1' l], fun i l => by rw [Env.setNat_arr, x2' i l],
      fun l => by rw [Env.setNat_arr, s3' l], fun i l => by rw [Env.setNat_arr, s4' i l],
      by rw [Env.setNat_draws, d4, d3, d2, d1]; ring, G4.setNat (by simp only [coN]; omega) _⟩ ?_) le_rfl ?_
  · intro t ht σ' ⟨jx1, jx2, js1, js2, jd, jG⟩ hkt hkn hk1
    obtain ⟨bI1, bI2⟩ := tzIter_bound (M := M) c T mu ra rb Y hR hRB hAl hAB hPG hPGB t
    obtain ⟨bS1, bS2⟩ := tzSum_bound (M := M) c T mu ra rb Y hR hRB hAl hAB hPG hPGB t
    have hEE : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
    have bI : ∀ x : ℤ, |x| ≤ c.Bh → |x| ≤ 2 ^ (2 * E) := fun x h => (h.trans bBh).trans hEE
    have bS : ∀ x : ℤ, |x| ≤ t * c.Bh → |x| ≤ 2 ^ (2 * E) := fun x h => by
      have ht' : (t : ℤ) ≤ 2 ^ E := by
        have : (t : ℤ) ≤ N := by exact_mod_cast ht.le
        exact this.trans (by exact_mod_cast bN)
      calc |x| ≤ t * c.Bh := h
        _ ≤ 2 ^ E * 2 ^ E := mul_le_mul ht' bBh hBh0 (by positivity)
        _ = 2 ^ (2 * E) := by rw [← pow_add]; ring_nf
    -- `Ŝ_μ += X̂_μ`
    refine XV.seq (XV.acc hL (z := o + 1) (t := o + 40) (aB := a + 4) (aX := a + 2) (nr := r + 4) (nst := r)
      (nk := r + 5) (nn := nd) (none := r) (N := d) (E := 2 * E)
      (U := vext (tzSum c T mu ra rb M Y t).1) (V := vext (tzIter c T mu ra rb M Y t).1)
      (by omega) (by omega) (by rw [jG.2.1 _ (by simp only [coS]; omega), eZ]) (hNA 4 (by norm_num))
      (hNA 2 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN
      (hNN 0 (by norm_num)) (by simp; omega) (by omega) (by omega)
      (by rw [jG.1 _ (by simp only [coN]; omega), hσd]) hk1 hk1 hcd (by omega) (vec_cells js1) (vec_cells jx1)
      (fun k hk => by rw [vext_lt _ hk]; exact bS _ (bS1 _)) (fun k hk => by rw [vext_lt _ hk]; exact bI _ (bI1 _))
      (by omega)) fun σa ⟨xa, da, Fa⟩ => ?_
    -- `Ŝ_T += X̂_T`
    refine XV.seq (XV.acc hL (z := o + 1) (t := o + 40) (aB := a + 5) (aX := a + 3) (nr := r + 4) (nst := r)
      (nk := r + 5) (nn := r + 25) (none := r) (N := d * d) (E := 2 * E)
      (U := tmext (tzSum c T mu ra rb M Y t).2) (V := tmext (tzIter c T mu ra rb M Y t).2)
      (by omega) (by omega) (by rw [Fa.2.1 _ (by omega), jG.2.1 _ (by simp only [coS]; omega), eZ])
      (hNA 5 (by norm_num)) (hNA 3 (by norm_num)) (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num))
      (hNN 25 (by norm_num)) (hNN 0 (by norm_num)) (by simp) (by omega) (by omega)
      (by rw [Fa.1 _ (by omega), jG.1 _ (by simp only [coN]; omega), hσdd]) (by rw [Fa.1 _ (by omega), hk1])
      (by rw [Fa.1 _ (by omega), hk1]) (fun k hk => cell_sq hk) (by omega)
      (mat_cells fun i l => by rw [Fa.2.2.1 _ _ (by omega)]; exact js2 i l)
      (mat_cells fun i l => by rw [Fa.2.2.1 _ _ (by omega)]; exact jx2 i l)
      (fun k _ => tmext_abs_le (by positivity) (fun i l => bS _ (bS2 i l)) k)
      (fun k _ => tmext_abs_le (by positivity) (fun i l => bI _ (bI2 i l)) k) (by omega)) fun σb ⟨xb, db, Fb⟩ => ?_
    have Gb : FrameA (coS o) (coN r) (coA d a) σ σb := (jG.trans (Fa.mono
      (fun y h => by simp only [coS]; omega) (fun j h => by simp only [coN]; omega)
      (fun b k h => by simp only [coA]; omega))).trans (Fb.mono
      (fun y h => by simp only [coS]; omega) (fun j h => by simp only [coN]; omega)
      (fun b k h => by simp only [coA]; omega))
    -- the draw
    refine XV.seq (XV.draw hL (o := o + 70) (on := r + 12) (aY := a + 6) (ni := r + 7) (nd := nd) (none := r)
      (B := B) (by omega) (by omega) hB1 (by rw [Gb.1 _ (by simp only [coN]; omega), hσB]) hBa (by omega)
      (hNA 6 (by norm_num)) (hNN 7 (by norm_num)) hndN (hNN 0 (by norm_num)) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by rw [Gb.1 _ (by simp only [coN]; omega), hσd])
      (by rw [Gb.1 _ (by simp only [coN]; omega), hσ1]) hda
      (fun U W hU _ => XV.abs_int_lt (lt_of_le_of_lt (BLM.gsSpec_abs_le B U W hU).1
        (pow_lt_pow_right₀ (by norm_num) (by omega))))) fun σc ⟨yc, dc, Fc⟩ => ?_
    have Gc : FrameA (coS o) (coN r) (coA d a) σ σc := Gb.trans (Fc.mono
      (fun y h => by simp only [coS]; omega) (fun j h => by simp only [coN]; omega)
      (fun b k h => by simp only [coA]; omega))
    have sc : ∀ k, 1 ≤ k → k < 16 → σc.sc (o + k) = σ.sc (o + k) := fun k h1 h2 =>
      Gc.2.1 _ (by simp only [coS]; omega)
    have dσc : σc.draws = σ.draws + 2 * B * d * t + 2 * B * d := by rw [dc, db, da, jd]
    -- the step
    refine XV.mono (XV.step1 hL (row := row) (o := o) (r := r) (a := a) (nd := nd) (M := M) (E := E) (c := c)
      (T := T) (mu := mu) (ra := ra) (rb := rb) (Xp := tzIter c T mu ra rb M Y t) (Y := Y t)
      (by omega) (by omega) (by omega) hnd (by rw [Gc.1 _ (by simp only [coN]; omega), hσd])
      (by rw [Gc.1 _ (by simp only [coN]; omega), hσ1]) (by rw [Gc.1 _ (by simp only [coN]; omega), hσM]) hda hMa
      (by rw [sc 1 (by norm_num) (by norm_num), eZ]) (by rw [sc 2 (by norm_num) (by norm_num), eO])
      (by rw [sc 3 (by norm_num) (by norm_num), eM]) (by rw [sc 4 (by norm_num) (by norm_num), ePB])
      (by rw [sc 5 (by norm_num) (by norm_num), eP2]) (by rw [sc 6 (by norm_num) (by norm_num), ePG])
      (by rw [sc 7 (by norm_num) (by norm_num), ePj]) (by rw [sc 8 (by norm_num) (by norm_num), eR])
      (by rw [sc 9 (by norm_num) (by norm_num), eMR]) (by rw [sc 10 (by norm_num) (by norm_num), eAl])
      (by rw [sc 11 (by norm_num) (by norm_num), eBh]) (by rw [sc 12 (by norm_num) (by norm_num), eMB])
      (by rw [sc 13 (by norm_num) (by norm_num), eD8])
      (fun l => by rw [Gc.2.2.1 _ _ (by simp only [coA]; omega), eMu])
      (fun i l => by rw [Gc.2.2.1 _ _ (by simp only [coA]; omega), eT])
      (fun l => by rw [Fc.2.2.1 _ _ (by omega), Fb.2.2.1 _ _ (by omega), Fa.2.2.1 _ _ (by omega), jx1 l])
      (fun i l => by rw [Fc.2.2.1 _ _ (by omega), Fb.2.2.1 _ _ (by omega), Fa.2.2.1 _ _ (by omega), jx2 i l])
      (fun l => by rw [yc l, db, da, jd]; rfl)
      (fun k hk σ'' F'' _ hk' => hrow k hk σ'' (Gc.trans (F''.mono
        (fun y h => by simp only [stS, coS] at h ⊢; omega) (fun j h => by simp only [stN, coN] at h ⊢; omega)
        (fun b k h => by simp only [stA, coA] at h ⊢; omega))) hk')
      (fun i => (bI1 i).trans bBh) (fun i l => (bI2 i l).trans bBh)
      (fun l => (gsAt_abs_le _ _ _ _).trans (pow_le_pow_right₀ (by norm_num) b4p)) bT bMu bR bB bPB bP2 bPG bPj
      bRR bAl bBh' bD8 hE) le_rfl ?_
    rintro σd ⟨xd1, xd2, dd, Fd⟩
    have Gd : FrameA (coS o) (coN r) (coA d a) σ σd := Gc.trans (Fd.mono
      (fun y h => by simp only [stS, coS] at h ⊢; omega) (fun j h => by simp only [stN, coN] at h ⊢; omega)
      (fun b k h => by simp only [stA, coA] at h ⊢; omega))
    have hsucc : tzSum c T mu ra rb M Y (t + 1) = tzSum c T mu ra rb M Y t + tzIter c T mu ra rb M Y t :=
      Finset.sum_range_succ _ _
    refine ⟨by rw [Fd.1 _ (by simp only [stN]; omega), Fc.1 _ (by omega), Fb.1 _ (by omega), Fa.1 _ (by omega), hkt],
      by rw [Gd.1 _ (by simp only [coN]; omega), hσN], by rw [Gd.1 _ (by simp only [coN]; omega), hσ1],
      fun l => by rw [Env.setNat_arr, xd1 l]; rfl, fun i l => by rw [Env.setNat_arr, xd2 i l]; rfl,
      fun l => ?_, fun i l => ?_, by rw [Env.setNat_draws, dd, dσc]; ring,
      Gd.setNat (by simp only [coN]; omega) _⟩
    · rw [Env.setNat_arr, Fd.2.2.1 _ _ (by simp only [stA]; omega), Fc.2.2.1 _ _ (by omega),
        Fb.2.2.1 _ _ (by omega), xa l l.2, vext_lt _ l.2, vext_lt _ l.2, hsucc]
      simp
    · rw [Env.setNat_arr, Fd.2.2.1 _ _ (by simp only [stA]; omega), Fc.2.2.1 _ _ (by omega),
        xb _ (cell_dil i l), tmext_cell, tmext_cell, hsucc]
      simp
  · rintro σ' ⟨⟨_, _, js1, js2, jd, jG⟩, -, -, -⟩
    exact ⟨js1, js2, jd, jG⟩

end AdversarialBco.Bit.Transfer
