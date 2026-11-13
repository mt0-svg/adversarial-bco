/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XExpr

@[expose] public section

/-!
# Loops over arrays by expressions

Three loops whose body is the code of an expression (`IE`, through the package `XV.ieRun`), for the vector steps of
ELL-R, BIS-R and FRAME. At turn `k` the register `nk` holds `k` and the register `nr` holds `base + st k`; the caller
gives the leaves and the value `F k` of the expression at every environment the loop can reach at turn `k` (a
`FrameA` of what the loop changed so far, the count of draws kept).

* `xmapE`: `aB[nr] := e`: the cells `base + st k` get `F k`, for `k < N`;
* `xfoldE`: `r := ∑_{k < N} F k`;
* `xanyE`: `f := 1` if `F₁ k < F₂ k` at some turn, else `f` kept.

On top: `xdot` (`r := x ⬝ᵥ y`) and `xmatvec` (`y := M *ᵥ x`, the matrix row-major in an array).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach Matrix

variable {d : ℕ}

theorem asz_lt {L : Layout} {ℓa : ℕ} (hL : LayOK L d ℓa) {a : ℕ} (ha : a < L.NA) : asz d < 2 ^ ℓa := by
  have h := hL.2
  unfold Layout.base at h
  have : asz d ≤ L.NA * asz d := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem FrameA.ofP {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameP S N σ σ') :
    FrameA S N Ar σ σ' :=
  ⟨h.1, h.2.1, fun b k _ => by rw [h.2.2.1], h.2.2.2.1, h.2.2.2.2⟩

theorem FrameA.mono {S N S' N' : ℕ → Prop} {Ar Ar' : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → S' y) (hN : ∀ j, N j → N' j) (hA : ∀ b k, Ar b k → Ar' b k) : FrameA S' N' Ar' σ σ' :=
  ⟨fun j hj => h.1 j fun h' => hj (hN j h'), fun y hy => h.2.1 y fun h' => hy (hS y h'),
    fun b k hb => h.2.2.1 b k fun h' => hb (hA b k h'), h.2.2.2.1, h.2.2.2.2⟩

/-! ## The map -/

/-- `for k < nat nn: aB[nr] := e; nr := nr + nst`; the value of `e` in the slot `t`, scratch from `t + 1`, `z` a slot
holding `0`. -/
def xmapE (L : Layout) (z t : ℕ) (e : IE) (aB nr nst nk nn none : ℕ) : XCmd :=
  xforN nk nn none (.seq (e.code L z t (t + 1))
    (.seq (toX (VL.aset L aB nr t)) (.prim (.frag (.nadd nr nr nst)))))

set_option maxHeartbeats 1000000 in
/-- The rule of `xmapE`: the cells `base + st k`, `k < N`, of the array `aB` get the values `F k`. -/
theorem XV.mapE {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t aB nr nst nk nn none E N base st : ℕ} {e : IE} {F : ℕ → ℤ}
    (hw : e.WF L t) (hz : z < t) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st) (hst : 0 < st)
    (hcell : ∀ k < N, base + st * k < asz d) (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa)
    (hsa : st < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr)
        (fun b c => b = aB ∧ base ≤ c ∧ c < base + st * k) σ σ' → σ'.draws = σ.draws →
        σ'.nat nk = k → σ'.nat nr = base + st * k → e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xmapE L z t e aB nr nst nk nn none) σ (N * (e.units + 6) + 3) (fun σ' =>
      (∀ k < N, σ'.arr aB (base + st * k) = F k) ∧ σ'.nat nr = base + st * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ base ≤ c ∧ c < base + st * N)
        σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (e.units + (2 + 1)) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      (∀ k' < k, σ'.arr aB (base + st * k') = F k') ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ base ≤ c ∧ c < base + st * k) σ σ')
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
        (fun b c => b = aB ∧ base ≤ c ∧ c < base + st * (k + 1)) σ' σ1 :=
      FrameA.ofP (P1.mono (fun y hy => by omega) (fun _ h => h.elim))
    refine (((hF'.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, h.2.1, by nlinarith [h.2.2]⟩)).trans
      hP).setArr ⟨rfl, by simp only [n1, hr]; omega, by simp only [n1, hr]; nlinarith⟩ _ |>.setNat
      (Or.inr rfl) _).setNat (Or.inl rfl) _

/-! ## The sum -/

/-- `r := 0; for k < nat nn: r := r + e; nr := nr + nst`; the value of `e` in the slot `t`, scratch from `t + 1`. -/
def xfoldE (L : Layout) (z r t : ℕ) (e : IE) (nr nst nk nn none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add r z z)) (xforN nk nn none (.seq (e.code L z t (t + 1))
    (.seq (toX (VL.sop2 L .add r r t)) (.prim (.frag (.nadd nr nr nst))))))

set_option maxHeartbeats 1000000 in
/-- The rule of `xfoldE`: the slot `r` gets `∑_{k < N} F k`, every partial sum below `2^ℓ`. -/
theorem XV.foldE {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t nr nst nk nn none E N base st : ℕ} {e : IE} {F : ℕ → ℤ}
    (hw : e.WF L t) (hz : z < t) (hrt : r < t) (hrz : r ≠ z) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st)
    (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa) (hsa : st < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hsum : ∀ k ≤ N, |∑ j ∈ Finset.range k, F j| < 2 ^ ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False)
        σ σ' → σ'.draws = σ.draws → σ'.nat nk = k → σ'.nat nr = base + st * k → e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xfoldE L z r t e nr nst nk nn none) σ (N * (e.units + 5) + 4) (fun σ' =>
      σ'.sc r = ((∑ k ∈ Finset.range N, F k : ℤ) : ℝ) ∧ σ'.nat nr = base + st * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  refine XV.mono (XV.seq (XV.sop2 hL (x := r) (a := z) (b := z) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [hz0]; exact h0) (by rw [hz0]; exact h0)
    (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact h0)) fun σ0 e0 => ?_) (K := 1 + (N * (e.units +
      (1 + 1) + 3) + 3)) (by ring_nf; omega) fun _ h => h
  subst e0
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (e.units + (1 + 1)) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      σ'.sc r = ((∑ j ∈ Finset.range k, F j : ℤ) : ℝ) ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ')
    _ (by simpa using hσn) (by simpa using hσ1) ⟨by simp [rk, hσr], rfl, by simp [RealRAM.Op2.eval, hz0],
      ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hr, hd, hs, hF'⟩, _⟩ => ⟨hs, hr, hd, hF'⟩
  intro k hk σ' ⟨hr, hd, hs, hF'⟩ hkt hkn hk1
  obtain ⟨hl, hv⟩ := hF k hk σ' hF' hd hkt hr
  have hst' : σ'.nat nst = st := by rw [hF'.1 nst (by omega), hσs]
  have hz' : σ'.sc z = 0 := by rw [hF'.2.1 z (by omega), hz0]
  refine XV.seq (XV.ieRun (E := E) hL (x := t) (t := t + 1) (hw.mono (by omega)) (by omega) (by omega) hS
    hz' hl htop hv) fun σ1 ⟨v1, b1, d1, P1⟩ => ?_
  have n1 : σ1.nat = σ'.nat := funext fun j => P1.1 j not_false
  have r1 : σ1.sc r = σ'.sc r := P1.2.1 r (by omega)
  have hsum1 : ((∑ j ∈ Finset.range (k + 1), F j : ℤ) : ℝ) = (σ1.sc r) + σ1.sc t := by
    rw [r1, hs, v1, Finset.sum_range_succ]; push_cast; ring
  refine XV.seq (XV.sop2 hL (x := r) (a := r) (b := t) (by omega) (by omega) (by omega) .add (by intro h; cases h)
    (by rw [r1, hs]; exact XV.abs_int_lt (hsum k hk.le)) (by rw [v1]; exact XV.abs_int_lt b1)
    (by simp only [RealRAM.Op2.eval]; rw [← hsum1]; exact XV.abs_int_lt (hsum (k + 1) hk))) fun σ2 e2 => ?_
  subst e2
  have hkN : base + st * k ≤ base + st * N := by have := Nat.mul_le_mul_left st hk.le; omega
  refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := nst) hnr hnr hnst
    (by simp only [Env.setSc_nat, n1, hr]; omega) (by simp only [Env.setSc_nat, n1, hst']; exact hsa)) le_rfl
    fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [Ne.symm rk, hkt, n1], by simp [Ne.symm rn, hkn, n1], by simp [Ne.symm ro, hk1, n1], ?_, ?_, ?_,
    ?_⟩
  · simp [rk, hr, hst', n1]; ring
  · simp [d1, hd]
  · simp only [Env.setNat_sc, Env.setSc_sc, ite_true, RealRAM.Op2.eval]; rw [← hsum1]
  · have hP : FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ' σ1 :=
      FrameA.ofP (P1.mono (fun y hy => by omega) (fun _ h => h.elim))
    exact (((hF'.trans hP).setSc (Or.inl rfl) _).setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

/-! ## The test over a range -/

/-- `for k < nat nn: if e₁ < e₂ then f := one + z; nr := nr + nst`; the values in the slots `t`, `t + 1`, scratch from
`t + 2`. -/
def xanyE (L : Layout) (z f one t : ℕ) (e1 e2 : IE) (nr nst nk nn none : ℕ) : XCmd :=
  xforN nk nn none (.seq (e1.code L z t (t + 2)) (.seq (e2.code L z (t + 1) (t + 2))
    (.seq (xifS L t (t + 1) (toX (VL.sop2 L .add f one z)) .skip) (.prim (.frag (.nadd nr nr nst))))))

set_option maxHeartbeats 1000000 in
/-- The rule of `xanyE`: the slot `f` gets `1` if `F₁ k < F₂ k` for some `k < N`, else keeps its value. -/
theorem XV.anyE {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z f one t nr nst nk nn none E N base st : ℕ} {e1 e2 : IE} {F1 F2 : ℕ → ℤ}
    (hw1 : e1.WF L t) (hw2 : e2.WF L t) (hz : z < t) (hft : f < t) (hot : one < t) (hfz : f ≠ z) (hfo : f ≠ one)
    (hS1 : t + 2 + e1.scr ≤ L.NS) (hS2 : t + 2 + e2.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hone : σ.sc one = 1)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st)
    (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa) (hsa : st < 2 ^ ℓa) (htop1 : e1.top E < ℓ)
    (htop2 : e2.top E < ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False)
        σ σ' → σ'.draws = σ.draws → σ'.nat nk = k → σ'.nat nr = base + st * k →
        (e1.Leaves E σ' ∧ e1.eval σ' = F1 k) ∧ (e2.Leaves E σ' ∧ e2.eval σ' = F2 k)) :
    XRunsB L X ℓa ℓ (xanyE L z f one t e1 e2 nr nst nk nn none) σ (N * (e1.units + e2.units + 6) + 3) (fun σ' =>
      ((∃ k < N, F1 k < F2 k) → σ'.sc f = 1) ∧ ((∀ k < N, ¬ F1 k < F2 k) → σ'.sc f = σ.sc f) ∧
      σ'.nat nr = base + st * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  have hℓ : 0 < ℓ := by have := IE.mag_le_top E e1; omega
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (e1.units + (e2.units + (2 + 1))) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      ((∃ k' < k, F1 k' < F2 k') → σ'.sc f = 1) ∧ ((∀ k' < k, ¬ F1 k' < F2 k') → σ'.sc f = σ.sc f) ∧
      FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ')
    σ hσn hσ1 ⟨by simp [rk, hσr], rfl, fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k), fun _ => rfl,
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) (by ring_nf; omega)
    fun σ' ⟨⟨hr, hd, hy, hn, hF'⟩, _⟩ => ⟨hy, hn, hr, hd, hF'⟩
  intro k hk σ' ⟨hr, hd, hy, hn, hF'⟩ hkt hkn hk1
  obtain ⟨⟨hl1, hv1⟩, -⟩ := hF k hk σ' hF' hd hkt hr
  have hst' : σ'.nat nst = st := by rw [hF'.1 nst (by omega), hσs]
  have hz' : σ'.sc z = 0 := by rw [hF'.2.1 z (by omega), hz0]
  refine XV.seq (XV.ieRun (E := E) hL (x := t) (t := t + 2) (hw1.mono (by omega)) (by omega) (by omega) hS1
    hz' hl1 htop1 hv1) fun σ1 ⟨v1, b1, d1, P1⟩ => ?_
  have n1 : σ1.nat = σ'.nat := funext fun j => P1.1 j not_false
  have hF1 : FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ1 :=
    hF'.trans (FrameA.ofP (P1.mono (fun y hy => by omega) (fun _ h => h.elim)))
  obtain ⟨-, ⟨hl2, hv2⟩⟩ := hF k hk σ1 hF1 (by rw [d1, hd]) (by rw [n1, hkt]) (by rw [n1, hr])
  have hz1 : σ1.sc z = 0 := by rw [P1.2.1 z (by omega), hz']
  refine XV.seq (XV.ieRun (E := E) hL (x := t + 1) (t := t + 2) (hw2.mono (by omega)) (by omega) (by omega) hS2
    hz1 hl2 htop2 hv2) fun σ2 ⟨v2, b2, d2, P2⟩ => ?_
  have n2 : σ2.nat = σ'.nat := by rw [← n1]; exact funext fun j => P2.1 j not_false
  have t2 : σ2.sc t = F1 k := by rw [P2.2.1 t (by omega), v1]
  have hF2 : FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ2 :=
    hF1.trans (FrameA.ofP (P2.mono (fun y hy => by omega) (fun _ h => h.elim)))
  have o2 : σ2.sc one = 1 := by rw [hF2.2.1 one (by omega), hone]
  have z2 : σ2.sc z = 0 := by rw [hF2.2.1 z (by omega), hz0]
  -- the test, then the step of `nr`
  have hstep : ∀ σ3 : Env d, σ3.nat = σ2.nat → σ3.draws = σ2.draws →
      FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ3 →
      ((∃ k' < k + 1, F1 k' < F2 k') → σ3.sc f = 1) → ((∀ k' < k + 1, ¬ F1 k' < F2 k') → σ3.sc f = σ.sc f) →
      XRunsB L X ℓa ℓ (.prim (.frag (.nadd nr nr nst))) σ3 1 (fun σ'' => σ''.nat nk = k ∧ σ''.nat nn = N ∧
        σ''.nat none = 1 ∧ (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
          ((∃ k' < k, F1 k' < F2 k') → σ'.sc f = 1) ∧ ((∀ k' < k, ¬ F1 k' < F2 k') → σ'.sc f = σ.sc f) ∧
          FrameA (fun y => y = f ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ') (k + 1)
          (σ''.setNat nk (k + 1))) := by
    intro σ3 n3 d3 hF3 hy3 hn3
    have hkN : base + st * k ≤ base + st * N := by have := Nat.mul_le_mul_left st hk.le; omega
    refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := nst) hnr hnr hnst
      (by rw [n3, n2, hr]; omega) (by rw [n3, n2, hst']; exact hsa)) le_rfl fun σ4 e4 => ?_
    subst e4
    refine ⟨by simp [Ne.symm rk, hkt, n3, n2], by simp [Ne.symm rn, hkn, n3, n2],
      by simp [Ne.symm ro, hk1, n3, n2], ?_, by simp [d3, d2, d1, hd], ?_, ?_, ?_⟩
    · simp [rk, hr, hst', n3, n2]; ring
    · simpa using hy3
    · simpa using hn3
    · exact (hF3.setNat (Or.inr rfl) _).setNat (Or.inl rfl) _
  by_cases hc : F1 k < F2 k
  · have hrun := XV.ifS_t (X := X) (c₂ := .skip) (Q := fun σ3 => σ3 = σ2.setSc f
        (RealRAM.Op2.eval .add (σ2.sc one) (σ2.sc z))) hL (x := t) (y := t + 1) (by omega) (by omega)
      (by rw [t2]; exact XV.abs_int_lt b1) (by rw [v2]; exact XV.abs_int_lt b2) (by rw [t2, v2]; exact_mod_cast hc)
      (XV.sop2 hL (by omega) (by omega) (by omega) .add (by intro h; cases h) (by rw [o2]; exact h1)
        (by rw [z2, abs_zero]; positivity) (by simp only [RealRAM.Op2.eval, o2, z2, add_zero]; exact h1))
    refine XV.mono (XV.seq (K₂ := 1) hrun fun σ3 e3 => ?_) (by omega) fun _ h => h
    subst e3
    exact hstep _ rfl rfl (hF2.setSc (Or.inl rfl) _)
      (fun _ => by simp [RealRAM.Op2.eval, o2, z2]) (fun h => absurd hc (h k (by omega)))
  · have hrun := XV.ifS_f (c₁ := toX (VL.sop2 L .add f one z)) (c₂ := .skip) hL (x := t) (y := t + 1) (by omega)
      (by omega) (by rw [t2]; exact XV.abs_int_lt b1) (by rw [v2]; exact XV.abs_int_lt b2)
      (by rw [t2, v2]; exact_mod_cast hc) (XV.skip (L := L) (X := X) (ℓa := ℓa) (ℓ := ℓ) σ2)
    refine XV.mono (XV.seq (K₂ := 1) hrun fun σ3 e3 => ?_) (by omega) fun _ h => h
    subst σ3
    have f2 : σ2.sc f = σ'.sc f := by rw [P2.2.1 f (by omega), P1.2.1 f (by omega)]
    refine hstep _ rfl rfl hF2 (fun ⟨k', hk', hc'⟩ => ?_) (fun h => ?_)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
      · rw [f2]; exact hy ⟨k', hlt, hc'⟩
      · exact absurd hc' hc
    · rw [f2]; exact hn fun k' hk' => h k' (by omega)


/-! ## Dot product and matrix-vector product -/

/-- A vector `Fin d → ℤ` extended by `0` to the naturals. -/
def vext (x : Fin d → ℤ) (k : ℕ) : ℤ := if h : k < d then x ⟨k, h⟩ else 0

theorem vext_lt (x : Fin d → ℤ) {k : ℕ} (h : k < d) : vext x k = x ⟨k, h⟩ := by unfold vext; simp [h]

theorem sum_vext (x y : Fin d → ℤ) : ∑ k ∈ Finset.range d, vext x k * vext y k = x ⬝ᵥ y := by
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun k => vext x k * vext y k) d]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vext_lt x k.2, vext_lt y k.2]

theorem abs_partial_le {F : ℕ → ℤ} {B N : ℕ} (hF : ∀ k < N, |F k| ≤ B) :
    ∀ k ≤ N, |∑ j ∈ Finset.range k, F j| ≤ k * B := by
  intro k hk
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => |F j|) (B : ℤ)
    (fun j hj => hF j (by rw [Finset.mem_range] at hj; omega))
  simpa using this

theorem abs_vext_mul_le {x y : Fin d → ℤ} {E : ℕ} (bx : ∀ k, |x k| ≤ 2 ^ E) (by' : ∀ k, |y k| ≤ 2 ^ E) (k : ℕ) :
    |vext x k * vext y k| ≤ ((2 ^ (2 * E) : ℕ) : ℤ) := by
  unfold vext
  split_ifs with h
  · rw [abs_mul]; push_cast
    calc |x ⟨k, h⟩| * |y ⟨k, h⟩| ≤ 2 ^ E * 2 ^ E :=
          mul_le_mul (bx _) (by' _) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  · simp

/-- `r := x ⬝ᵥ y`, `x` in the cells `0, ..., d - 1` of the array `ax`, `y` in those of `ay`; `nd` holds `d`, `none`
holds `1`. -/
def xdot (L : Layout) (z r t ax ay nr nk nd none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xfoldE L z r t (.op .mul (.arr ax nr) (.arr ay nk)) nr none nk nd none)

set_option maxHeartbeats 1000000 in
/-- The rule of `xdot`, entries below `2^E`, `d 2^(2E) < 2^ℓ`. -/
theorem XV.dot {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t ax ay nr nk nd none E : ℕ} {x y : Fin d → ℤ} (hz : z < t) (hrt : r < t) (hrz : r ≠ z)
    (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0) (hax : ax < L.NA) (hay : ay < L.NA) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnd : nd < L.NN) (hno : none < L.NN) (hne : [nr, nk, nd, none].Nodup) (hσd : σ.nat nd = d)
    (hσ1 : σ.nat none = 1) (hx : ∀ k : Fin d, σ.arr ax k = x k) (hy : ∀ k : Fin d, σ.arr ay k = y k)
    (bx : ∀ k, |x k| ≤ 2 ^ E) (by' : ∀ k, |y k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xdot L z r t ax ay nr nk nd none) σ (d * 10 + 5) (fun σ' =>
      σ'.sc r = ((x ⬝ᵥ y : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne'
  have hda := asz_lt hL hax
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.mono (K := 1 + (d * 10 + 4)) (XV.seq (XV.nconst hL hnr 0 (by positivity)) fun σ0 e0 => ?_) (by omega)
    fun _ h => h
  subst e0
  refine XV.mono (XV.foldE (E := E) (N := d) (base := 0) (st := 1) (F := fun k => vext x k * vext y k) hL
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; exact ⟨⟨hax, hnr⟩, hay, hnk⟩) hz hrt
    hrz (by simp only [IE.scr]; omega) (by simpa using hz0) hnr hno hnk hnd hno hne (Ne.symm ro) (Ne.symm ko)
    (by simp [Ne.symm rn, hσd]) (by simp [Ne.symm ro, hσ1]) (by simp) (by simp [Ne.symm ro, hσ1])
    (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith) (by have := hL.1; omega)
    (by simp only [IE.top, IE.mag]; omega) ?_ ?_) (by simp only [IE.units]; omega) fun σ' ⟨h1, _, h3, h4⟩ => ⟨by rw [h1, sum_vext], ?_, ?_⟩
  · intro k hk
    exact lt_of_le_of_lt (abs_partial_le (fun j _ => abs_vext_mul_le bx by' j) k hk)
      (by have := Nat.mul_le_mul_right (2 ^ (2 * E)) hk; exact_mod_cast lt_of_le_of_lt this hℓ)
  · intro k hk σ' hF hd hkt hkr
    have hr' : σ'.nat nr = k := by simpa using hkr
    have ax' : σ'.arr ax k = x ⟨k, hk⟩ := by rw [hF.2.2.1 ax k id]; exact hx ⟨k, hk⟩
    have ay' : σ'.arr ay k = y ⟨k, hk⟩ := by rw [hF.2.2.1 ay k id]; exact hy ⟨k, hk⟩
    refine ⟨⟨⟨by rw [hr']; exact hdl k hk, x ⟨k, hk⟩, by rw [hr', ax'], bx _⟩,
      ⟨by rw [hkt]; exact hdl k hk, y ⟨k, hk⟩, by rw [hkt, ay'], by' _⟩⟩, ?_⟩
    simp only [IE.eval, RealRAM.Op2.eval, hr', hkt, ax', ay', vext_lt x hk, vext_lt y hk]; push_cast; ring
  · exact h3
  · exact FrameA.trans ((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0) h4

/-- `y := M *ᵥ x`, `M` row-major in the array `aM` (entry `(i, k)` in the cell `d i + k`), `x` and `y` in the cells
`0, ..., d - 1` of the arrays `ax`, `ay`. -/
def xmatvec (L : Layout) (z r t aM ax ay ni nr nk nd none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xforN ni nd none
    (.seq (xfoldE L z r t (.op .mul (.arr aM nr) (.arr ax nk)) nr none nk nd none) (toX (VL.aset L ay ni r))))

set_option maxHeartbeats 2000000 in
/-- The rule of `xmatvec`, entries below `2^E`, `d 2^(2E) < 2^ℓ`. -/
theorem XV.matvec {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t aM ax ay ni nr nk nd none E : ℕ} {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} (hz : z < t)
    (hrt : r < t) (hrz : r ≠ z) (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0) (haM : aM < L.NA) (hax : ax < L.NA)
    (hay : ay < L.NA) (hyM : ay ≠ aM) (hyx : ay ≠ ax) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnd : nd < L.NN) (hno : none < L.NN) (hne : [ni, nr, nk, nd, none].Nodup) (hσd : σ.nat nd = d)
    (hσ1 : σ.nat none = 1) (hM : ∀ i k : Fin d, σ.arr aM (d * i + k) = M i k) (hx : ∀ k : Fin d, σ.arr ax k = x k)
    (bM : ∀ i k, |M i k| ≤ 2 ^ E) (bx : ∀ k, |x k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xmatvec L z r t aM ax ay ni nr nk nd none) σ (d * (d * 10 + 9) + 4) (fun σ' =>
      (∀ i : Fin d, σ'.arr ay i = (M *ᵥ x) i) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr) (fun b c => b = ay ∧ c < d) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨ir, ik, id, io⟩, ⟨rk, rd, ro⟩, ⟨kd, ko⟩, dO⟩ := hne'
  have hda := asz_lt hL hax
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.mono (K := 1 + (d * (d * 10 + 4 + 2 + 3) + 3)) (XV.seq (XV.nconst hL hnr 0 (by positivity))
    fun σ0 e0 => ?_) (by ring_nf; omega) fun _ h => h
  subst e0
  let J : ℕ → Env d → Prop := fun i σ' => σ'.nat nr = d * i ∧ σ'.draws = σ.draws ∧
    (∀ i' (h : i' < i) (hd : i' < d), σ'.arr ay i' = (M *ᵥ x) ⟨i', hd⟩) ∧
    FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr) (fun b c => b = ay ∧ c < i) σ σ'
  refine XV.mono (XV.forN hL hni hnd hno id io d (d * 10 + 4 + 2) (by unfold asz at hda; nlinarith) J _
    (by simp [Ne.symm rd, hσd]) (by simp [Ne.symm ro, hσ1])
    ⟨by simp [Ne.symm ir], rfl, fun i' h => absurd h (Nat.not_lt_zero _),
      ((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inr rfl)) 0).setNat (Or.inl rfl) 0⟩ ?_) (by ring_nf; omega)
    fun σ' ⟨⟨_, hd, hy, hF⟩, _⟩ => ⟨fun i => hy i i.2 i.2, hd, hF.mono (fun _ h => h) (fun _ h => h)
      (fun b c h => ⟨h.1, h.2⟩)⟩
  intro i hi σ' ⟨hr, hd, hy, hF⟩ hit hid hi1
  let row : Fin d → ℤ := fun k => M ⟨i, hi⟩ k
  have hsk : none ≠ nk := Ne.symm ko
  refine XV.seq (XV.foldE (E := E) (N := d) (base := d * i) (st := 1) (F := fun k => vext row k * vext x k) hL
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; exact ⟨⟨haM, hnr⟩, hax, hnk⟩) hz hrt
    hrz (by simp only [IE.scr]; omega) (by rw [hF.2.1 z (by omega), hz0]) hnr hno hnk hnd hno
    (by simp [rk, rd, ro, kd, ko, dO]) (Ne.symm ro) hsk (by rw [hF.1 nd (by omega), hσd])
    (by rw [hF.1 none (by omega), hσ1]) hr (by rw [hF.1 none (by omega), hσ1])
    (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith) (by have := hL.1; omega)
    (by simp only [IE.top, IE.mag]; omega) ?_ ?_) fun σ1 ⟨s1, r1, d1, F1⟩ => ?_
  · intro k hk
    exact lt_of_le_of_lt (abs_partial_le (fun j _ => abs_vext_mul_le (fun _ => bM _ _) bx j) k hk)
      (by have := Nat.mul_le_mul_right (2 ^ (2 * E)) hk; exact_mod_cast lt_of_le_of_lt this hℓ)
  · intro k hk σ2 hF2 hd2 hkt hkr
    have hFF := hF.trans (hF2.mono (fun _ h => h) (fun _ h => by tauto) (fun _ _ h => h.elim))
    have hr' : σ2.nat nr = d * i + k := by simpa using hkr
    have hcell : d * i + k < d * d := by nlinarith
    have aM' : σ2.arr aM (d * i + k) = M ⟨i, hi⟩ ⟨k, hk⟩ := by
      rw [hFF.2.2.1 aM _ (fun h => hyM h.1.symm)]; exact hM ⟨i, hi⟩ ⟨k, hk⟩
    have ax' : σ2.arr ax k = x ⟨k, hk⟩ := by
      rw [hFF.2.2.1 ax k (fun h => hyx h.1.symm)]; exact hx ⟨k, hk⟩
    refine ⟨⟨⟨by rw [hr']; unfold asz; omega, M ⟨i, hi⟩ ⟨k, hk⟩, by rw [hr', aM'], bM _ _⟩,
      ⟨by rw [hkt]; exact hdl k hk, x ⟨k, hk⟩, by rw [hkt, ax'], bx _⟩⟩, ?_⟩
    simp only [IE.eval, RealRAM.Op2.eval, hr', hkt, aM', ax', vext_lt row hk, vext_lt x hk, row]; push_cast; ring
  · have hFF := hF.trans (F1.mono (fun _ h => h) (fun _ h => by tauto) (fun _ _ h => h.elim))
    have n1 : σ1.nat ni = i := by rw [F1.1 ni (by omega), hit]
    refine XV.mono (XV.aset hL (a := ay) (i := ni) (x := r) hay hni (by omega) (by rw [n1]; exact hdl i hi)
      (by rw [s1]; exact XV.abs_int_lt (lt_of_le_of_lt (abs_partial_le (fun j _ => abs_vext_mul_le
        (fun _ => bM _ _) bx j) d le_rfl) (by exact_mod_cast hℓ)))) le_rfl fun σ2 e2 => ?_
    subst e2
    have hval : ((∑ k ∈ Finset.range d, vext row k * vext x k : ℤ) : ℝ) = ((M *ᵥ x) ⟨i, hi⟩ : ℤ) := by
      rw [sum_vext]; rfl
    refine ⟨by simp [n1], by rw [Env.setArr_nat, F1.1 nd (by omega), hid],
      by rw [Env.setArr_nat, F1.1 none (by omega), hi1], ?_, ?_, ?_, ?_⟩
    · simp [Ne.symm ir, r1]; ring
    · simp [d1, hd]
    · intro i' hi' hd'
      simp only [Env.setNat_arr, Env.setArr_arr, n1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · rw [ite_eq_right (by omega), F1.2.2.1 ay i' (fun h => h)]; exact hy i' hlt hd'
      · rw [ite_eq_left (by simp), s1, hval]
    · exact ((hFF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩)).setArr
        ⟨rfl, by simp only [n1]; omega⟩ _).setNat (Or.inl rfl) _

end AdversarialBco.Bit.Transfer
