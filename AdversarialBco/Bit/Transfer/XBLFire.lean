/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCommit
public import AdversarialBco.Bit.Transfer.XBLSetupEpoch
public import AdversarialBco.Bit.Transfer.XBLSetupFacts

@[expose] public section

/-!
# R12 FIRE on the machine

`xfire L`: the cells of `μ'` (`d`), `A'`, `B'` (`d²`), `b'`, `G'` (`d`), `k'`, `l'` to `0` (`xfireZ`), then the epoch
start of the setup (`xepoch`: `first := 1`, `D_μ := 1`, the diagonals of `A'`, `B'` from `sA0`, `sB0`).
`fireBL : FireBL` with `C = 64`, `k = 2`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ} {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

/-- `dst[k] := 0` for `k < nat nn` (the slot `z` holds `0`); `nr` walks the cells, `nk` counts, `one` holds `1`. -/
def xzeroN (L : Layout) (z t dst nr nk nn one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (.sc z) dst nr one nk nn one)

set_option maxHeartbeats 1000000 in
/-- The first `N` cells of the array `dst` to `0` (`nn` holds `N`, `one` holds `1`). -/
theorem XV.zeroN (hL : LayOK L d ℓa) {σ : Env d} {z t dst nr nk nn one E N : ℕ} (hz : z < t)
    (hS : t + 1 ≤ L.NS) (hz0 : σ.sc z = 0) (hdst : dst < L.NA) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnn : nn < L.NN) (hone : one < L.NN) (hne : [nr, nk, nn, one].Nodup) (hσn : σ.nat nn = N)
    (hσ1 : σ.nat one = 1) (hN : N ≤ asz d) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xzeroN L z t dst nr nk nn one) σ (1 + (N * (1 + 6) + 3)) (fun σ' =>
      (∀ k < N, σ'.arr dst k = 0) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = dst ∧ c < N) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL hdst
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true]
    at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne
  refine XV.seq (XV.nconstA hL (i := nr) hnr 0 (by positivity)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have e1 : ∀ j, j ≠ nr → σ1.nat j = σ.nat j := fun j h => G1.1 j h
  refine XV.mono (XV.mapEx (E := E) (N := N) (base := 0) (st := 1) (F := fun _ => 0) hL (z := z) (t := t)
    (e := .sc z) (aB := dst) (nr := nr) (nst := one) (nk := nk) (nn := nn) (none := one)
    (by simp only [IE.WF]; omega) hz (by simp only [IE.scr]; omega) (by rw [G1.2.1 _ id, hz0]) hdst hnr hone
    hnk hnn hone (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; omega) (Ne.symm ro) (Ne.symm ko)
    (by rw [e1 _ (Ne.symm rn), hσn]) (by rw [e1 _ (Ne.symm ro), hσ1]) v1 (by rw [e1 _ (Ne.symm ro), hσ1]) one_pos
    (fun k hk => by omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' hF _ _ _ => ?_)) le_rfl fun σ2 ⟨z2, _, d2, F2⟩ => ?_
  · have h0 : σ'.sc z = ((0 : ℤ) : ℝ) := by rw [hF.2.1 _ (by omega), G1.2.1 _ id, hz0]; simp
    exact ⟨⟨0, h0, by simp⟩, by simp only [IE.eval]; exact h0⟩
  · refine ⟨fun k hk => ?_, by rw [d2, d1], ?_⟩
    · have := z2 k hk
      rw [zero_add, one_mul] at this
      rw [this]; simp
    · exact (G1.mono (fun _ h => h.elim) (fun j h => Or.inr h) (fun _ _ h => h.elim)).trans
        (F2.mono (fun y h => h) (fun j h => h) (fun b c h => by
          obtain ⟨hb, k', hk', e⟩ := h
          exact ⟨hb, by omega⟩))

/-- R12, the cells of the state to `0`. -/
def xfireZ (L : Layout) : XCmd :=
  .seq (xnmul 12 rD rD) (.seq (xzeroN L sZ 128 aMu 10 11 rD rOne) (.seq (xzeroN L sZ 128 aA 10 11 12 rOne)
    (.seq (xzeroN L sZ 128 aB 10 11 12 rOne) (.seq (xzeroN L sZ 128 ab 10 11 rD rOne)
    (.seq (xzeroN L sZ 128 aG 10 11 rD rOne) (.seq (toX (VL.sconst L sK 0)) (toX (VL.sconst L sL 0))))))))

/-- **R12 FIRE.** -/
def xfire (L : Layout) : XCmd := .seq (xfireZ L) (xepoch L)

/-- The arrays `xfireZ` changes. -/
def AFz (d b c : ℕ) : Prop := (b = aMu ∧ c < d) ∨ ACom d b c

set_option maxHeartbeats 4000000 in
/-- The rule of `xfireZ`. -/
theorem XV.fireZ (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d} {E : ℕ} (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hE : E < ℓ) (hdd : d * d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xfireZ L) σ (14 * (d * d) + 21 * d + 23) (fun σ' =>
      (∀ b k, AFz d b k → σ'.arr b k = 0) ∧ σ'.sc sK = 0 ∧ σ'.sc sL = 0 ∧ σ'.draws = σ.draws ∧
      FrameA SCom NCom (AFz d) σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by omega)
  have hd0 : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; omega) hda
  have hNd : d * d ≤ asz d := by unfold asz; omega
  have hNd' : d ≤ asz d := by unfold asz; omega
  have h0l : |((0 : ℚ) : ℝ)| < 2 ^ ℓ := by simp
  refine XV.mono (K := 1 + ((1 + (d * (1 + 6) + 3)) + ((1 + (d * d * (1 + 6) + 3)) + ((1 + (d * d * (1 + 6) + 3)) +
      ((1 + (d * (1 + 6) + 3)) + ((1 + (d * (1 + 6) + 3)) + (1 + 1)))))))
    (XV.seq (XV.nmul hL (i := 12) (a := rD) (b := rD) (by omega) (by bomega) (by bomega) (by rw [hD]; exact hd0)
      (by rw [hD]; exact hd0) (by rw [hD]; exact hdd)) fun σ1 e1 => ?_) (by omega) fun _ h => h
  subst e1
  have n1 : ∀ j, j ≠ 12 → (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat j = σ.nat j := fun j h => by
    rw [Env.setNat_nat, if_neg h]
  have m1 : (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat 12 = d * d := by rw [Env.setNat_nat, if_pos rfl, hD]
  -- `μ'`
  refine XV.seq (XV.zeroN hL (z := sZ) (t := 128) (dst := aMu) (nr := 10) (nk := 11) (nn := rD) (one := rOne)
    (E := E) (N := d) (by bomega) (by omega) (by rw [Env.setNat_sc, hz]) (by bomega) (by omega) (by omega)
    (by bomega) (by bomega) (by decide) (by rw [n1 _ (by decide), hD]) (by rw [n1 _ (by decide), h1]) hNd' hE)
    fun σ2 ⟨c2, d2, F2⟩ => ?_
  have n2 : ∀ j, j ≠ 10 → j ≠ 11 → σ2.nat j = (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat j := fun j h h' =>
    F2.1 j fun e => e.elim h' h
  have s2 : ∀ y < 128, σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 y (by omega), Env.setNat_sc]
  -- `A'`
  refine XV.seq (XV.zeroN hL (z := sZ) (t := 128) (dst := aA) (nr := 10) (nk := 11) (nn := 12) (one := rOne)
    (E := E) (N := d * d) (by bomega) (by omega) (by rw [s2 _ (by bomega), hz]) (by bomega) (by omega) (by omega)
    (by omega) (by bomega) (by decide) (by rw [n2 _ (by decide) (by decide), m1])
    (by rw [n2 _ (by decide) (by decide), n1 _ (by decide), h1]) hNd hE) fun σ3 ⟨c3, d3, F3⟩ => ?_
  have n3 : ∀ j, j ≠ 10 → j ≠ 11 → σ3.nat j = σ2.nat j := fun j h h' => F3.1 j fun e => e.elim h' h
  have s3 : ∀ y < 128, σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), s2 y hy]
  -- `B'`
  refine XV.seq (XV.zeroN hL (z := sZ) (t := 128) (dst := aB) (nr := 10) (nk := 11) (nn := 12) (one := rOne)
    (E := E) (N := d * d) (by bomega) (by omega) (by rw [s3 _ (by bomega), hz]) (by bomega) (by omega) (by omega)
    (by omega) (by bomega) (by decide) (by rw [n3 _ (by decide) (by decide), n2 _ (by decide) (by decide), m1])
    (by rw [n3 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), h1]) hNd hE)
    fun σ4 ⟨c4, d4, F4⟩ => ?_
  have n4 : ∀ j, j ≠ 10 → j ≠ 11 → σ4.nat j = σ2.nat j := fun j h h' => by
    rw [F4.1 j fun e => e.elim h' h, n3 j h h']
  have s4 : ∀ y < 128, σ4.sc y = σ.sc y := fun y hy => by rw [F4.2.1 y (by omega), s3 y hy]
  -- `b'`
  refine XV.seq (XV.zeroN hL (z := sZ) (t := 128) (dst := ab) (nr := 10) (nk := 11) (nn := rD) (one := rOne)
    (E := E) (N := d) (by bomega) (by omega) (by rw [s4 _ (by bomega), hz]) (by bomega) (by omega) (by omega)
    (by bomega) (by bomega) (by decide) (by rw [n4 _ (by decide) (by decide), n2 _ (by decide) (by decide),
      n1 _ (by decide), hD]) (by rw [n4 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), h1])
    hNd' hE) fun σ5 ⟨c5, d5, F5⟩ => ?_
  have n5 : ∀ j, j ≠ 10 → j ≠ 11 → σ5.nat j = σ2.nat j := fun j h h' => by
    rw [F5.1 j fun e => e.elim h' h, n4 j h h']
  have s5 : ∀ y < 128, σ5.sc y = σ.sc y := fun y hy => by rw [F5.2.1 y (by omega), s4 y hy]
  -- `G'`
  refine XV.seq (XV.zeroN hL (z := sZ) (t := 128) (dst := aG) (nr := 10) (nk := 11) (nn := rD) (one := rOne)
    (E := E) (N := d) (by bomega) (by omega) (by rw [s5 _ (by bomega), hz]) (by bomega) (by omega) (by omega)
    (by bomega) (by bomega) (by decide) (by rw [n5 _ (by decide) (by decide), n2 _ (by decide) (by decide),
      n1 _ (by decide), hD]) (by rw [n5 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), h1])
    hNd' hE) fun σ6 ⟨c6, d6, F6⟩ => ?_
  -- `k'`, `l'`
  refine XV.seq (XV.sconst hL (x := sK) (by bomega) 0 rfl h0l) fun σ7 e7 => ?_
  subst e7
  refine XV.mono (XV.sconst hL (x := sL) (by bomega) 0 rfl h0l) le_rfl fun σ8 e8 => ?_
  subst e8
  have a6 : ∀ b k, ((σ6.setSc sK ((0 : ℚ) : ℝ)).setSc sL ((0 : ℚ) : ℝ)).arr b k = σ6.arr b k := fun b k => by
    simp only [Env.setSc_arr]
  refine ⟨fun b k h => ?_, by simp, by simp, ?_, ?_⟩
  · rw [a6]
    rcases h with ⟨rfl, hk⟩ | ⟨rfl | rfl, hk⟩ | ⟨rfl | rfl, hk⟩
    · rw [F6.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)),
        F4.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F3.2.2.1 _ _ (fun e => absurd e.1 (by decide)), c2 k hk]
    · rw [F6.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)),
        F4.2.2.1 _ _ (fun e => absurd e.1 (by decide)), c3 k hk]
    · rw [F6.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)),
        c4 k hk]
    · rw [F6.2.2.1 _ _ (fun e => absurd e.1 (by decide)), c5 k hk]
    · rw [c6 k hk]
  · simp only [Env.setSc_draws]; rw [d6, d5, d4, d3, d2, Env.setNat_draws]
  · have G1 : FrameA SCom NCom (AFz d) σ (σ.setNat 12 (σ.nat rD * σ.nat rD)) :=
      (FrameA.refl _ _ _ σ).setNat (show NCom 12 by simp only [NCom]; omega) _
    have G2 := F2.mono (S' := SCom) (N' := NCom) (Ar' := AFz d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inl h)
    have G3 := F3.mono (S' := SCom) (N' := NCom) (Ar' := AFz d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr (Or.inl ⟨Or.inl h.1, h.2⟩))
    have G4 := F4.mono (S' := SCom) (N' := NCom) (Ar' := AFz d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr (Or.inl ⟨Or.inr h.1, h.2⟩))
    have G5 := F5.mono (S' := SCom) (N' := NCom) (Ar' := AFz d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr (Or.inr ⟨Or.inl h.1, h.2⟩))
    have G6 := F6.mono (S' := SCom) (N' := NCom) (Ar' := AFz d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr (Or.inr ⟨Or.inr h.1, h.2⟩))
    exact (((((((G1.trans G2).trans G3).trans G4).trans G5).trans G6).setSc (Or.inl rfl) _).setSc
      (Or.inr (Or.inl rfl)) _)


end AdversarialBco.Bit.Transfer.BLM
