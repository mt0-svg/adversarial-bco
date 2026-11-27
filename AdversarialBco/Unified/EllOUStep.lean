/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOStep
public import AdversarialBco.Unified.EllOUSep

@[expose] public section

/-!
# A test step of ELL-O with the blocks uniform in `d`

`XVO.testStepO` (EllOStep.lean) on `sepCallOD`: `SepBlockOKU`, `GaugeBlockOKU`, `d` in the register `0` in the
test's data (`hT0`), the register `0` kept by the test block (`hNt0`).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 16000000 in
/-- **A test of ELL-O in its block**: `xtestOB` computes `tfO I.base T s (sepO I T s) a kept`, from the context
`CxO` at the scale `2^s` and the centre `a` in the array `aW + 3`, for a SEP block, a gauge block and a test block
meeting their contracts. -/
theorem XVO.testStepOD {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {k Kt bt s F : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop} {a : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOKU L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOKU L XO ℓa ℓ (gaugeLayO B) gc)
    (hT0 : ∀ τ : Env d, TDat τ → τ.nat 0 = d) (hNt0 : ∀ j, Nt j → j ≠ 0)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat k) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hC : CxO B I TDat k s σ) (hK : KeptIn (B.o + 83) (B.aW + 8) kept σ)
    (bW : ∀ b W, kept = some (b, W) → |W| ≤ 2 ^ (6 * F + 1))
    (ha : ∀ k : Fin d, σ.arr (B.aW + 3) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F)
    (hσF : ellOSz I ≤ F) (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hEs : I.sepEx s - s ≤ F) (hFb : F < bt)
    (hbt : 3 * (I.sepEx s + F + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx s + I.eτ + I.eu + (I.sepEx s - s + F + 1) + (I.jg + 1) + 8 ≤ ℓ)
    (hℓa : I.sepEx s + I.eτ + 8 < 2 ^ ℓa) (hja : I.jg + 1 < 2 ^ ℓa) (hGl : I.sepEx s + I.jg + 1 < ℓ)
    (hℓF : 64 * F + 16 < ℓ) :
    XRunsBO L XO ℓa ℓ (xtestOB L B sepc gc TB) σ (stepU I Kt) (fun σ' =>
      TestOut (B.o + 83) (B.aW + 2) (B.aW + 2 + 6) (tfO I.base T s (sepO I T s) a kept) σ' ∧
      σ'.draws = σ.draws ∧
      FrameA (tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)) (tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt))
        (taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art)) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB'
  have hav' := hav
  obtain ⟨avS, avN, avA⟩ := hav'
  have stS : ∀ y, St y → y < B.o := fun y h => by
    have := (avS y h).1; simp only [EllOBlk.ownS] at this; omega
  have ntN : ∀ j, Nt j → j ≤ B.rE := fun j h => by
    rcases (avN j h).1 with h' | h'
    · simp only [EllOBlk.ownN] at h'; omega
    · omega
  have arA : ∀ b k, Art b k → b < B.aW := fun b k h => by
    have := (avA b k h).1; simp only [EllOBlk.ownA] at this; omega
  refine XVO.testO hL (B := B.inner) (Ib := I.base) (s := s) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := F) (G := I.sepEx s + I.jg + 1) (tp := B.aW + 1) (ans := B.rE) (zr := B.rE + 2)
    (cF := B.o + 76) (E := I.sepEx s) (Kt := Kt) (Ks := sepK d (I.eL + I.eτ + 3) (gaugeK d I.jg Kt)) (bt := bt)
    (TB := TB) (SC := sepc (gc TB)) (sl := sepLayO B) (T := T) (sepF := sepO I T s) (Cx := CxO B I TDat k s)
    (Dat := TDatK B TDat k) (St := St) (Nt := Nt) (SS := sSO B St) (SN := sNO B Nt) (Art := Art)
    (SA := sAO B Art) hd (inner_OK hB) rfl
    ⟨by simp only [EllOBlk.inner]; omega, by omega, by omega, by simp only [EllOBlk.inner]; omega, rfl, by omega,
      by simp only [EllOBlk.inner]; omega, rfl, rfl, by omega⟩
    (by omega) (Or.inl (by omega)) (by simp only [sepLayO]; omega) (Or.inr (by simp only [sepLayO]; omega))
    (by simp only [sepLayO]; omega) (by simp only [sepLayO]; omega) (by simp only [sepLayO, EllOBlk.inner]; omega)
    (by simp only [EllOBlk.inner]; omega) (by simp only [EllOBlk.inner]; omega)
    (by simp only [EllOBlk.inner]; omega)
    (fun y h => by have := stS y h; simp only [EllOBlk.inner]; omega)
    (fun j h => by have := ntN j h; simp only [EllOBlk.inner]; omega)
    (fun b k h => Or.inl (by have := arA b k h; omega))
    (fun y h => by
      simp only [EllOBlk.inner]
      rcases h with h | h | h
      · have := sepS_le (Or.inl h); omega
      · have := sepS_le (Or.inr h); omega
      · have := stS y h; omega)
    (fun j h => by
      simp only [EllOBlk.inner]
      rcases h with h | h | h
      · have := sepN_le (Or.inl h); omega
      · have := sepN_le (Or.inr h); omega
      · have := ntN j h; omega)
    (fun b k h => by
      rcases h with h | h | h
      · have := sepA_le (Or.inl h); omega
      · have := sepA_le (Or.inr h); omega
      · have := arA b k h; omega)
    (fun σ' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun σa σb hCa hdab hF => CxO.frame hB hav hst hCa hdab hF (fun y hy => ?_) (fun j hj => ?_)
      (fun b k hb => ?_))
    hTB
    (fun σ' hC' hY => sepCallOD hL hd hB hDc hS hG hT0 hNt0 hTB hav hst hC'.2.2.2.1 hC'.2.2.2.2 hY ba hbt hℓ hℓS hℓa hja)
    (fun Y Gv h k => sepO_G_le I T s a h k) hC hK bW ha ba ((ellSz_base_le I).trans hσF) hsF hdF hEs hFb hGl hℓF
  · simp only [tsO, EllOBlk.inner] at hy
    rcases hy with h | h | h
    · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · simp only [tnO, EllOBlk.inner] at hj
    rcases hj with h | h | h
    · rcases h with h | h | h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inr (Or.inl (by simp only [gaugeN, gaugeLayO]; omega)))
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · simp only [taO, EllOBlk.inner, sepLayO] at hb
    rcases hb with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
    · rcases h with h | h | h
      · exact Or.inl (by have := sepA_le (Or.inl h); omega)
      · exact Or.inl (by have := sepA_le (Or.inr h); omega)
      · exact Or.inr h

end AdversarialBco.Uni.EllO
