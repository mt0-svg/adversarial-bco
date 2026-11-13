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


set_option maxHeartbeats 4000000 in
/-- **R12 FIRE on the machine** (`FireBL`, frozen in XBLEnd.lean). -/
theorem fireBL : FireBL := by
  refine ⟨xfire, 64, 2, ?_⟩
  intro d L X ℓa ℓ n m K0 E t cfg st σ hd hn hpar hL hlay hI hCl hCa
  have hsq : d * d + d + E + 1 ≤ (d + E + 1) ^ 2 := by
    have h2 : (d + E + 1) ^ 2 = d * d + (2 * d * E + E * E + 2 * d + 2 * E + 1) := by ring
    omega
  have hE : E < ℓ := by omega
  have hdd : d * d < 2 ^ ℓa := by omega
  obtain ⟨hS, hN, hAr⟩ := id hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  obtain ⟨r0, -, -, r3, -, -, -, -⟩ := hI.regs
  have c0 : σ.sc sZ = 0 := hI.consts.1
  have p9 : σ.sc sA0 = qn cfg.par.p cfg.par.A0 := hI.par.2.2.2.2.2.2.2.2.2.1
  have p10 : σ.sc sB0 = qn cfg.par.p cfg.par.B0 := hI.par.2.2.2.2.2.2.2.2.2.2
  have hE0 : (0 : ℤ) ≤ 2 ^ E := by positivity
  have ba : |qn cfg.par.p cfg.par.A0| ≤ 2 ^ E := by
    obtain ⟨z, hz, hzE⟩ := hI.bnd.1 sA0 (by decide)
    have : z = qn cfg.par.p cfg.par.A0 := by exact_mod_cast hz.symm.trans p9
    rwa [← this]
  have bb : |qn cfg.par.p cfg.par.B0| ≤ 2 ^ E := by
    obtain ⟨z, hz, hzE⟩ := hI.bnd.1 sB0 (by decide)
    have : z = qn cfg.par.p cfg.par.B0 := by exact_mod_cast hz.symm.trans p10
    rwa [← this]
  refine XV.mono (K := (14 * (d * d) + 21 * d + 23) + epochUnits d)
    (XV.seq (XV.fireZ hL hlay r0 r3 c0 hE hdd) fun σ1 ⟨z1, k1, l1, d1, F1⟩ => ?_) (by unfold epochUnits; omega)
    fun _ h => h
  have n1 : ∀ j < 8, σ1.nat j = σ.nat j := fun j hj => F1.1 j fun h => by simp only [NCom] at h; omega
  have s1 : ∀ y < 128, y ≠ sK → y ≠ sL → σ1.sc y = σ.sc y := fun y hy h h' => F1.2.1 y (not_sCom hy h h')
  refine XV.mono (XV.epoch (a0 := qn cfg.par.p cfg.par.A0) (b0 := qn cfg.par.p cfg.par.B0) (E := E) hL (by omega)
    (by omega) (by omega) (by rw [n1 _ (by decide), r0]) (by rw [n1 _ (by decide), r3])
    (by rw [s1 _ (by decide) (by decide) (by decide), c0]) (by rw [s1 _ (by decide) (by decide) (by decide), p9])
    (by rw [s1 _ (by decide) (by decide) (by decide), p10]) ba bb hE) le_rfl
    fun σ2 ⟨f2, m2, dA, dB, d2, F2⟩ => ?_
  have s2 : ∀ y < 128, y ≠ sFirst → y ≠ sDmu → σ2.sc y = σ1.sc y := fun y hy h h' =>
    F2.2.1 y fun e => by rcases e with e | e | e <;> [exact h e; exact h' e; omega]
  have a2 : ∀ b k, ¬ AE (d := d) b k → σ2.arr b k = σ1.arr b k := fun b k h => F2.2.2.1 b k h
  have hF : FrameA SEnd NEnd AEnd σ σ2 := by
    refine (F1.mono (fun y h => ?_) (fun j h => h.1) (fun b c h => ?_)).trans
      (F2.mono (fun y h => ?_) (fun j h => ?_) (fun b c h => ?_))
    · rcases h with h | h | h
      exacts [Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · show aMu ≤ b
      rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> subst h <;> decide
    · rcases h with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · show 8 ≤ j
      rcases h with h | h | h <;> omega
    · show aMu ≤ b
      rcases h with ⟨h | h, -⟩ <;> subst h <;> decide
  have hA0 : OnG cfg.par.p cfg.par.A0 := by rw [hpar, PieceA.par_A0]; exact onG_rnd_s _ _
  have hB0 : OnG cfg.par.p cfg.par.B0 := by rw [hpar, PieceA.par_B0]; exact onG_rnd_s _ _
  obtain ⟨g0, q0⟩ := onG_zero cfg.par.p
  have nAE : ∀ b k, b ≠ aA → b ≠ aB → ¬ AE (d := d) b k := fun b k h h' e => by
    rcases e.1 with e | e
    exacts [h e, h' e]
  have hst : StRep σ2 cfg.par.p (init cfg.par d) := by
    refine ⟨by rw [f2]; simp [init], ⟨1, one_pos,
      by rw [m2]; simp, fun j => ⟨0, ?_, by simp [init]⟩⟩, fun i j => ?_, fun i j => ?_, fun j => ?_, ?_,
      fun j => ?_, ?_⟩
    · rw [a2 _ _ (nAE _ _ (by decide) (by decide)), z1 aMu j (Or.inl ⟨rfl, j.2⟩)]; simp
    · show σ2.arr aA (d * i + j) = qn cfg.par.p ((cfg.par.A0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
      refine ⟨?_, onG_smul_one _ _ hA0 i j⟩
      rw [qn_smul_one]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have := dA i i.2
        rwa [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      · rw [if_neg hij, a2 _ _ (fun h => hij ((diag_iff i j).1 h.2)),
          z1 aA _ (Or.inr (Or.inl ⟨Or.inl rfl, cell_lt i j⟩))]
        simp
    · show σ2.arr aB (d * i + j) = qn cfg.par.p ((cfg.par.B0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
      refine ⟨?_, onG_smul_one _ _ hB0 i j⟩
      rw [qn_smul_one]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have := dB i i.2
        rwa [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      · rw [if_neg hij, a2 _ _ (fun h => hij ((diag_iff i j).1 h.2)),
          z1 aB _ (Or.inr (Or.inl ⟨Or.inr rfl, cell_lt i j⟩))]
        simp
    · show σ2.arr ab j = qn cfg.par.p ((0 : Fin d → ℚ) j) ∧ OnG cfg.par.p ((0 : Fin d → ℚ) j)
      rw [Pi.zero_apply, q0, a2 _ _ (nAE _ _ (by decide) (by decide)), z1 ab j (Or.inr (Or.inr ⟨Or.inl rfl, j.2⟩))]
      exact ⟨by simp, g0⟩
    · show σ2.sc sK = qn cfg.par.p 0 ∧ OnG cfg.par.p 0
      rw [q0, s2 _ (by decide) (by decide) (by decide), k1]
      exact ⟨by simp, g0⟩
    · show σ2.arr aG j = qn cfg.par.p ((0 : Fin d → ℚ) j) ∧ OnG cfg.par.p ((0 : Fin d → ℚ) j)
      rw [Pi.zero_apply, q0, a2 _ _ (nAE _ _ (by decide) (by decide)), z1 aG j (Or.inr (Or.inr ⟨Or.inr rfl, j.2⟩))]
      exact ⟨by simp, g0⟩
    · show σ2.sc sL = qn cfg.par.p 0 ∧ OnG cfg.par.p 0
      rw [q0, s2 _ (by decide) (by decide) (by decide), l1]
      exact ⟨by simp, g0⟩
  refine ⟨BLInv.setSt hI hF (by rw [d2, d1]) hst (fun y hy => ?_) (fun a ha k hk => ?_), by rw [d2, d1], hF⟩
  · simp only [nSP] at hy
    by_cases e1 : y = sFirst
    · subst e1
      exact Or.inr ⟨1, by rw [f2]; simp, one_le_two_pow E⟩
    by_cases e2 : y = sDmu
    · subst e2
      exact Or.inr ⟨1, by rw [m2]; simp, one_le_two_pow E⟩
    by_cases e3 : y = sK
    · subst e3
      exact Or.inr ⟨0, by rw [s2 _ (by decide) (by decide) (by decide), k1]; simp, by simp⟩
    by_cases e4 : y = sL
    · subst e4
      exact Or.inr ⟨0, by rw [s2 _ (by decide) (by decide) (by decide), l1]; simp, by simp⟩
    exact Or.inl (by rw [s2 y (by omega) e1 e2, s1 y (by omega) e3 e4])
  · by_cases hAE : AE (d := d) a k
    · obtain ⟨ha' | ha', j, hj, rfl⟩ := hAE
      · subst ha'; exact Or.inr ⟨_, dA j hj, ba⟩
      · subst ha'; exact Or.inr ⟨_, dB j hj, bb⟩
    rw [a2 _ _ hAE]
    by_cases hZ : AFz d a k
    · exact Or.inr ⟨0, by rw [z1 a k hZ]; simp, by simp⟩
    · exact Or.inl (F1.2.2.1 a k hZ)

end AdversarialBco.Bit.Transfer.BLM
