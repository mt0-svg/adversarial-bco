/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOBlock
public import AdversarialBco.Unified.EllOURoute

@[expose] public section

/-!
# The ELL-O block with the blocks uniform in `d`

`XVO.ellO` (EllOBlock.lean) on `XVO.ellOMainD`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 4000000 in
/-- **The rule of the ELL-O block** `xellO`: from ELL-O's inputs, the block writes `ellOI I T` over `2^{ellExpO I}`
into its output (`EllOOut`) within `ellOU I κ Kt` units, keeps the draws and writes only its own cells and the
test's. -/
theorem XVO.ellOD {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOKU L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOKU L XO ℓa ℓ (gaugeLayO B) gc)
    (hT0 : ∀ τ : Env d, TDat τ → τ.nat 0 = d) (hNt0 : ∀ j, Nt j → j ≠ 0)
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
  refine XVO.seq (XVO.ellOMainD hL hd hB hDc hS hG hT0 hNt0 hTB hav hst hTD1 hin1 z1 o1 n1 r1 c1 s1 hbt hℓ hℓa (by omega)
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
