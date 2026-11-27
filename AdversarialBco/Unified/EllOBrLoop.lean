/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOBrPre

@[expose] public section

/-!
# UNI-ELL (c): the loop of the ELL-O branch on the oracle machine

`XVO.ellLoopBrO`: from ELL-R's start state and the constants of step 2 (the tests' data `CxO`, the update's data
`UpdEnv`, the start of the loop `LoopSt`), `xloopT` with the test command `xtestOB` runs ELL-O's loop (`loopT` over
the test `tfO`, Unified/EllOLoop.lean) and keeps the tests' data of the inner block.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 32000000 in
/-- **The loop of the ELL-O branch** (`d ≥ 2`): from the state after the constants of step 2, the loop of ELL-O over
`N` iterations; the result in the loop's output, the tests' data of the inner block kept. -/
theorem XVO.ellLoopBrO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : 2 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOK L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hr : 0 < I.r) (he : 0 < I.e)
    (hC : CxO B I TDat (I.eK + κ) I.base.p σ ∧ UpdEnv (B.o + 95) I.base.p I.base.q I.base.j
      ((2 : ℤ) ^ I.base.p * I.base.Lam) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) σ)
    (hS1 : LoopSt (B.o + 83) (B.aW + 2) (B.aW + 2 + 6) ((2 : ℤ) ^ I.base.p * I.base.Lam)
      ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) (ellF d (ellSz I.base))
      ⟨((2 : ℤ) ^ I.base.p * I.base.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩ σ)
    (hN : σ.nat (B.rE + 65 + 7) = I.base.N)
    (hbt : 3 * (I.sepEx I.base.p + ellOF I I.base.p + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx I.base.p + I.eτ + I.eu + (I.sepEx I.base.p - I.base.p + ellOF I I.base.p + 1) + (I.jg + 1) + 8
      ≤ ℓ)
    (hℓE : 64 * ellOE I I.base.p + 16 < ℓ) (hXa : cstX I I.base.p κ < 2 ^ ℓa)
    (hℓa0 : 1000 * (d + I.base.m + ellSz I.base + 1) ^ 3 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xloopT L B.inner (xtestOB L B sepc gc TB) (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65)) σ
      (I.base.N * (kbT d (ellOE I I.base.p) (stepU I Kt) + 2) + 4) (fun σ' =>
      LoopOut (B.o + 83) (B.aW + 2) (B.aW + 2 + 6) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH))
        (ellF d (ellSz I.base)) (EllO.loopT (tfO I.base T I.base.p (sepO I T I.base.p)) I.base.p I.base.q
          I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) I.base.N
          ⟨((2 : ℤ) ^ I.base.p * I.base.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩) σ' ∧
      σ'.draws = σ.draws ∧ TestEnv B.inner I.base I.base.p (B.o + 83) (B.o + 95) (B.rE + 69) σ' ∧
      FrameA (lpS (B.o + 83) (B.o + 95) (tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)))
        (lpN (B.rE + 65) (tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt)))
        (lpA (B.aW + 2) (taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art))) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB'
  have hBi := inner_OK hB
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
  have hd1 : 1 ≤ d := by omega
  have hr' : 0 < I.base.r := hr
  have he' : 0 < I.base.e := he
  obtain ⟨blam, bp, bq, -⟩ := ellLam_le I.base hd1 hr' he'
  obtain ⟨rN, -, -, -, -⟩ := ell_regs (m := I.base.m) blam hℓa0
  have hsz := ellSz_base_le I
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I I.base.p
  have hX : cstX I I.base.p κ = I.sepEx I.base.p + I.eτ + I.eK + κ + 12 := rfl
  have hOE : ellOE I I.base.p = ellE d (ellOSz I) + I.sepEx I.base.p + I.jg + 1 := rfl
  have hOF : ellOF I I.base.p = ellF d (ellOSz I) + I.sepEx I.base.p := rfl
  have hEE : ellE d (ellSz I.base) ≤ ellE d (ellOSz I) := by unfold ellE; omega
  have hFF : ellF d (ellSz I.base) ≤ ellF d (ellOSz I) := by unfold ellF; omega
  have hFE : ellF d (ellOSz I) ≤ ellE d (ellOSz I) := by unfold ellF ellE; omega
  have eN : I.base.N = 2 * d * (d + 1) * I.base.lam + 1 := rfl
  have hRb0 : (0 : ℤ) ≤ I.base.Rb := by positivity
  have hRbs : (I.base.Rb : ℤ) ≤ 2 ^ ellSz I.base := by exact_mod_cast (ellRb_lt I.base).le
  obtain ⟨-, -, -, -, -, pcA, pca⟩ := ell_pows (lam := I.base.lam) (p := I.base.p) hRb0 hRbs
  have eA : (2 : ℤ) ^ I.base.p * (I.base.Rb * I.base.Rb * 2 ^ (6 * I.base.lam + 2)) =
      2 ^ I.base.p * (I.base.Lam : ℤ) := by
    unfold EllI.Lam; push_cast; ring
  have ea : (2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.Rb * 2 ^ (3 * I.base.lam + 1)) =
      2 ^ I.base.p * ((I.base.Rb : ℤ) + (I.base.LamH : ℤ)) := by
    unfold EllI.LamH; push_cast; ring
  have hpE : I.base.p + (2 * ellSz I.base + (6 * I.base.lam + 2)) ≤ ellE d (ellSz I.base) := by unfold ellE; omega
  have hFO : ellF d (ellSz I.base) ≤ ellOF I I.base.p := by omega
  have hdO : d ≤ ellOF I I.base.p := by unfold ellF at hOF; omega
  have bcA : (2 : ℤ) ^ I.base.p * I.base.Lam ≤ 2 ^ ellOE I I.base.p := by
    rw [← eA]; exact pcA.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bca : (2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH) ≤ 2 ^ ellF d (ellSz I.base) := by
    rw [← ea]; exact pca.trans (pow_le_pow_right₀ (by norm_num) (by unfold ellF; omega))
  have cA0 : (0 : ℤ) ≤ 2 ^ I.base.p * (I.base.Lam : ℤ) := mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  have ca0 : (0 : ℤ) ≤ 2 ^ I.base.p * ((I.base.Rb : ℤ) + (I.base.LamH : ℤ)) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have bkE : 3 * d + 2 ≤ ellOE I I.base.p := by unfold ellE at hOE; omega
  -- the loop
  have lay : LoopLay L B.inner (B.o + 83) (B.o + 95) (B.aW + 2) (B.aW + 2 + 6) (B.rE + 65) :=
    ⟨⟨by simp only [EllOBlk.inner]; omega, by omega, by omega, by simp only [EllOBlk.inner]; omega, rfl, by omega,
      by simp only [EllOBlk.inner]; omega, rfl, rfl, by omega⟩, by omega, by omega⟩
  have henv : ∀ σa σb : Env d, (CxO B I TDat (I.eK + κ) I.base.p σa ∧
      UpdEnv (B.o + 95) I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
        ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) σa) → σb.draws = σa.draws →
      FrameA (lpS (B.o + 83) (B.o + 95) (tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)))
        (lpN (B.rE + 65) (tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt)))
        (lpA (B.aW + 2) (taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art))) σa σb →
      (CxO B I TDat (I.eK + κ) I.base.p σb ∧
      UpdEnv (B.o + 95) I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
        ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) σb) := fun σa σb hCa hdab hF => by
    refine ⟨CxO.frame hB hav hst hCa.1 hdab hF (fun y hy => ?_) (fun j hj => ?_) (fun b k hb => ?_),
      hCa.2.frame hF (fun y hy => ?_)⟩
    · rcases hy with h | h
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
      · rcases tsO_cases h with h | ⟨-, -, h⟩ | h
        · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
        · exact Or.inr (h.elim Or.inl (fun h => Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr h))
    · rcases hj with h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · rcases tnO_cases h with h | ⟨-, -, h⟩ | h
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr (h.elim Or.inl (fun h => Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr h))
    · rcases hb with h | h
      · exact Or.inl (by omega)
      · rcases taO_cases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
    · rcases hy with h | h
      · omega
      · rcases tsO_cases h with h | ⟨-, h, -⟩ | h
        · omega
        · omega
        · have := stS _ h; omega
  have nTS : ∀ y, tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St) y →
      (y = B.o + 82 ∨ y = B.o + 83 ∨ y = B.o + 84 ∨ y = B.o + 85 ∨ y = B.o + 90 ∨ B.o + 108 ≤ y) ∨
        (B.o + 3 ≤ y ∧ y < B.o + 76) ∨ y < B.o := fun y h => by
    rcases tsO_cases h with h | ⟨h1, h2, -⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (stS _ h))
  have nTN : ∀ j, tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt) j →
      (j = B.rE + 64 ∨ (B.rE + 65 ≤ j ∧ j ≤ B.rE + 67) ∨ j = B.rE + 70) ∨ j < B.rE + 26 := fun j h => by
    rcases tnO_cases h with h | ⟨-, h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h
    · have := ntN _ h; exact Or.inr (by omega)
  have nTA : ∀ b k, taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art) b k →
      b = B.aW + 1 ∨ B.aW + 4 ≤ b ∨ b < B.aW := fun b k h => by
    rcases taO_cases h with h | h
    · omega
    · exact Or.inr (Or.inr (arA _ _ h))
  have hσF : ellOSz I ≤ ellOF I I.base.p := by unfold ellF at hOF; omega
  have hpF : 2 * I.base.p + 1 ≤ ellOF I I.base.p := by unfold ellF at hOF; omega
  refine XVO.mono (XVO.loopT hL (B := B.inner) (I := I.base) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := ellF d (ellSz I.base)) (E := ellOE I I.base.p) (N := I.base.N) (Kt := stepU I Kt)
    (p := I.base.p) (q := I.base.q) (j := I.base.j) (tc := xtestOB L B sepc gc TB)
    (tf := tfO I.base T I.base.p (sepO I T I.base.p))
    (Ctx := fun σ' => CxO B I TDat (I.eK + κ) I.base.p σ' ∧ UpdEnv (B.o + 95) I.base.p I.base.q I.base.j
      ((2 : ℤ) ^ I.base.p * I.base.Lam) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) σ')
    (TS := tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)) (TN := tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt))
    (TA := taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art))
    (capA := (2 : ℤ) ^ I.base.p * I.base.Lam) (capa := (2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH))
    (st := ⟨((2 : ℤ) ^ I.base.p * I.base.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩)
    hBi lay (fun σ' h => ⟨h.1.1, h.2⟩) henv
    (fun h => by rcases nTS _ h with h | h | h <;> omega)
    (fun h => by rcases nTN _ h with h | h <;> omega)
    (fun h => by rcases nTN _ h with h | h <;> omega)
    (fun k => ⟨fun h => by rcases nTA _ _ h with h | h | h <;> omega,
      fun h => by rcases nTA _ _ h with h | h | h <;> omega⟩)
    (fun σ' a kept hC' hK' bK' ha' ba' => XVO.testStepO hL (F := ellOF I I.base.p) hd1 hB hDc hS hG hTB hav hst
      hC'.1 hK' (fun b W h => (bK' b W h).2.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
      ha' (fun k => (ba' k).trans (bca.trans (pow_le_pow_right₀ (by norm_num) (by omega)))) hσF hpF (by omega)
      (by omega) (by omega) hbt hℓ hℓS (by omega) (by omega) (by omega) (by omega))
    (fun a kept x h => tfO_ret h)
    (fun a kept c kept' ha' bK' h => tfO_cut (F := ellF d (ellSz I.base)) (G := I.sepEx I.base.p + I.jg + 1)
      ha' bca bK' (fun Y Gv hY k => sepO_G_le I T I.base.p a hY k) (by unfold ellF; omega) (by unfold ellF; omega)
      (by unfold ellF; omega) (by unfold ellF ellE at *; omega) (by omega) h)
    hC hS1 hN (by rw [eN]; omega) cA0 ca0 bcA
    (bca.trans (pow_le_pow_right₀ (by norm_num) (by omega))) (by omega) (by omega)
    (by unfold ellE at hOE; omega) (by omega) ((kapN_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE))
    ((kapD_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE)) hℓE) le_rfl
    fun σ3 ⟨o3, d3, F3⟩ => ⟨o3, d3, (henv σ σ3 hC d3 F3).1.1, F3⟩

end AdversarialBco.Uni.EllO
