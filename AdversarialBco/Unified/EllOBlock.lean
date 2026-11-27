/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllORoute

@[expose] public section

/-!
# UNI-ELL (c): the start and the output of the ELL-O block

`XV.startO`: the start `xstartO` writes `0`, `1` into the slots `o + 95`, `o + 96`, `1` into the register `rE + 69`,
`0` into the slot `o + 77` and the register `rE + 2`, `lg d` into the register `rE + 58`. `XVO.ellO`: the block
`xellO` writes `ellOI I T` over `2^{ellExpO I}` (`EllOOut`), keeps the draws and writes only its own cells and the
test's.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

/-- The rule of the start `xstartO`. -/
theorem XV.startO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    (hB : B.OK L 215 112 14) (hd : 1 ≤ d) (vd : σ.nat B.rd = d) (hda : d < 2 ^ ℓa) (hdl : d < ℓ) :
    XRunsB L X ℓa ℓ (xstartO L B) σ (startOU d) (fun σ' =>
      σ'.sc (B.o + 95) = 0 ∧ σ'.sc (B.o + 96) = 1 ∧ σ'.nat (B.rE + 69) = 1 ∧ σ'.sc (B.o + 77) = 0 ∧
      σ'.nat (B.rE + 2) = 0 ∧ σ'.nat (B.rE + 58) = Nat.clog 2 d ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o + 77 ≤ y ∧ y ≤ B.o + 96) (fun j => B.rE + 2 ≤ j ∧ j ≤ B.rE + 69)
        (fun _ _ => False) σ σ') := by
  obtain ⟨hoS, hrN, -, -, -, -, hrd, -⟩ := hB
  have h1a : 1 < 2 ^ ℓa := by omega
  have hl0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have hl1 : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  unfold xstartO startOU
  refine XV.seq (XV.sconstA hL (x := B.o + 95) (by omega) 0 hl0) fun σ1 ⟨v1, d1, F1⟩ => ?_
  refine XV.seq (XV.sconstA hL (x := B.o + 96) (by omega) 1 hl1) fun σ2 ⟨v2, d2, F2⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := B.rE + 69) (by omega) 1 h1a) fun σ3 ⟨v3, d3, F3⟩ => ?_
  refine XV.seq (XV.sconstA hL (x := B.o + 77) (by omega) 0 hl0) fun σ4 ⟨v4, d4, F4⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := B.rE + 2) (by omega) 0 (by positivity)) fun σ5 ⟨v5, d5, F5⟩ => ?_
  have vd5 : σ5.nat B.rd = d := by
    rw [F5.1 _ (by omega), F4.1 _ id, F3.1 _ (by omega), F2.1 _ id, F1.1 _ id, vd]
  refine XV.seq (XV.ncastA hL (x := B.o + 78) (i := B.rd) (by omega) (by omega) vd5 hda) fun σ6 ⟨v6, d6, F6⟩ => ?_
  have one6 : σ6.nat (B.rE + 69) = 1 := by rw [F6.1 _ id, F5.1 _ (by omega), F4.1 _ id, v3]
  refine XV.mono (XV.clogS hL (w := B.o + 79) (x := B.o + 78) (c := B.rE + 58) (one := B.rE + 69) (G := d)
    (v := (d : ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) v6 (by positivity)
    (by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le) one6 hda hdl) le_rfl fun σ7 ⟨v7, d7, F7'⟩ => ?_
  have F7 := FrameA.ofP (Ar := fun _ _ => False) F7'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), F5.2.1 _ id, F4.2.1 _ (by omega), F3.2.1 _ id,
      F2.2.1 _ (by omega), v1, Int.cast_zero]
  · rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), F5.2.1 _ id, F4.2.1 _ (by omega), F3.2.1 _ id, v2, Int.cast_one]
  · rw [F7.1 _ (by omega), one6]
  · rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), F5.2.1 _ id, v4, Int.cast_zero]
  · rw [F7.1 _ (by omega), F6.1 _ id, v5]
  · rw [v7, Int.toNat_natCast]
  · rw [d7, d6, d5, d4, d3, d2, d1]
  · exact (((((((F1.mono (fun y h => ⟨by omega, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h)).trans
      (F2.mono (fun y h => ⟨by omega, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h))).trans
      (F3.mono (fun _ h => h.elim) (fun j h => ⟨by omega, by omega⟩) (fun _ _ h => h))).trans
      (F4.mono (fun y h => ⟨by omega, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h))).trans
      (F5.mono (fun _ h => h.elim) (fun j h => ⟨by omega, by omega⟩) (fun _ _ h => h))).trans
      (F6.mono (fun y h => ⟨by omega, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h))).trans
      (F7.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => ⟨by omega, by omega⟩) (fun _ _ h => h)))

set_option maxHeartbeats 4000000 in
/-- **The rule of the ELL-O block** `xellO`: from ELL-O's inputs, the block writes `ellOI I T` over `2^{ellExpO I}`
into its output (`EllOOut`) within `ellOU I κ Kt` units, keeps the draws and writes only its own cells and the
test's. -/
theorem XVO.ellO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOK L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hTD : TDat σ) (hin : EllOIn B I κ σ)
    (hbt : 0 < I.r → 0 < I.e → bigO I κ ≤ bt) (hℓ : bt + 4 ≤ ℓ) (hℓa : 0 < I.r → 0 < I.e → bigO I κ < 2 ^ ℓa)
    (hsl : ellOSz I + d + 2 < ℓ) (hℓa3 : 1000 * (d + ellOSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xellO L B sepc gc TB) σ (ellOU I κ Kt) (fun σ' =>
      EllOOut B (ellOI I T) (ellExpO I) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, -, -, -, -, hrd, hrK, hrκ, -⟩ := hB'
  have hpw : d + ellOSz I + 1 ≤ (d + ellOSz I + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold xellO ellOU
  refine XVO.seq (XVO.ofX (XV.startO hL hB hd hin.1 (by omega) (by omega)))
    fun σ1 ⟨z1, o1, n1, s1, r1, c1, d1, F1⟩ => ?_
  have G1 : FrameA (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k) σ σ1 :=
    F1.mono (fun y h => Or.inl (show B.o ≤ y by omega)) (fun j h => Or.inl (show B.rE ≤ j by omega))
      (fun _ _ h => h.elim)
  have hin1 : EllOIn B I κ σ1 := EllOIn.frame hB hin F1 (fun y h => by omega) (fun j h => by omega)
    (fun _ _ h => h.elim)
  have hTD1 : TDat σ1 := hst σ σ1 hTD G1 d1
  refine XVO.seq (XVO.ellOMain hL hd hB hDc hS hG hTB hav hst hTD1 hin1 z1 o1 n1 r1 c1 s1 hbt hℓ hℓa (by omega)
    hℓa3) fun σ2 ⟨out2, e2, z2, d2, F2⟩ => ?_
  have h00 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have h01 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h77 : |σ2.sc (B.o + 77)| < 2 ^ ℓ := by rw [z2]; exact h00
  have b80 : |σ2.sc (B.o + 80)| < 2 ^ ℓ := by
    rcases hr : ellOI I T with _ | x
    · rw [hr] at out2; rw [show σ2.sc (B.o + 80) = 0 from out2]; exact h00
    · rw [hr] at out2; rw [show σ2.sc (B.o + 80) = 1 from out2.1]; exact h01
  have ev : RealRAM.Op2.eval .add (σ2.sc (B.o + 80)) (σ2.sc (B.o + 77)) = σ2.sc (B.o + 80) := by
    simp [RealRAM.Op2.eval, z2]
  refine XVO.mono (XVO.ofX (XV.sop2 hL (x := B.o) (a := B.o + 80) (b := B.o + 77) (by omega) (by omega)
    (by omega) .add (by intro h; cases h) b80 h77 (by rw [ev]; exact b80))) le_rfl ?_
  rintro σ3 rfl
  refine ⟨?_, by simp [d2, d1], ?_⟩
  · rw [ev]
    rcases hr : ellOI I T with _ | x
    · rw [hr] at out2
      have o80 : σ2.sc (B.o + 80) = 0 := out2
      simp [EllOOut, o80]
    · rw [hr] at out2 e2
      have e2' := e2 (by simp)
      obtain ⟨o80, -, oa⟩ := out2
      have o80' : σ2.sc (B.o + 80) = 1 := o80
      have oa' : ∀ j : Fin d, σ2.arr B.aW j = x j := oa
      simp [EllOOut, o80', e2', oa']
  · refine (G1.trans (F2.mono (fun y h => ?_) (fun j h => ?_) (fun b k h => ?_))).trans
      ((FrameA.refl _ _ _ σ2).setSc (Or.inl (show B.o ≤ B.o from le_rfl)) _)
    · rcases h with h | h
      · exact Or.inl (show B.o ≤ y by omega)
      · exact Or.inr h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h

end AdversarialBco.Uni.EllO
