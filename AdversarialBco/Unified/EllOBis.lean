/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOBrPre

@[expose] public section

/-!
# UNI-ELL (c): the BIS-O branch on the oracle machine

`d = 1`, after the constants up to `λ` of ELL-R's inner block (`XV.ellJ`): BIS-R's constants (`xbisSet`), the
constants of step 2 at the scale `2^{λ+1}` (`xconstO`), the loop of BIS-O (`xbisLoopT` with the test command
`xtestOB`) and ELL-R's output (`xellOut`) into the inner block.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

/-- The BIS-O branch: BIS-R's constants, the constants of step 2, the loop, ELL-R's output. -/
def xbisBrO (L : Layout) (B : EllOBlk) (sepc gc : XCmdO → XCmdO) (TB : XCmdO) : XCmdO :=
  .seq (.base (xbisSet L B.inner (B.o + 83) (B.o + 95) (B.o + 155) (B.rE + 65)))
  (.seq (.base (xconstO L B (B.rE + 73) (B.rE + 74) (B.rE + 58) (B.rE + 72) (B.rE + 69)))
  (.seq (xbisLoopT L B.inner (xtestOB L B sepc gc TB) (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65))
    (.base (xellOut L B.inner (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65)))))

/-- The units of the BIS-O branch with a test block of `Kt` units. -/
def bisBrOU (I : EllOI d) (κ Kt : ℕ) : ℕ :=
  (24 * I.base.lam + 57) + (constOU (cstX I (I.base.lam + 1) κ) +
    (((I.base.lam + 1) * (bkbT d (stepU I Kt) + 2) + 4) + (8 * d + 8)))

set_option maxHeartbeats 32000000 in
/-- **The BIS-O branch on the oracle machine** (`d = 1`), from the constants up to `λ` of the inner block: the
result `bisO I T` over `2^{λ+1}` in the inner block's output, `λ + 1` in the slot `o + 1`. -/
theorem XVO.bisBrO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : d = 1) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOK L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hTD : TDat σ) (hin : EllIn B.inner I.base σ) (vK : σ.nat B.rK = I.erK) (vκ : σ.nat B.rκ = κ)
    (vc : σ.arr B.ac 0 = I.Dc ∧ ∀ j : Fin d, σ.arr B.ac (1 + (j : ℕ)) = I.Nc j)
    (hz : σ.sc (B.o + 95) = 0) (h1 : σ.sc (B.o + 96) = 1) (hone : σ.nat (B.rE + 69) = 1)
    (hRb : σ.sc (B.o + 155) = ((I.base.Rb : ℤ) : ℝ)) (hj : σ.nat (B.rE + 73) = I.base.j)
    (hcR : σ.nat (B.rE + 74) = Nat.clog 2 I.base.Rb) (hl : σ.nat (B.rE + 75) = I.base.lam)
    (hcd : σ.nat (B.rE + 58) = Nat.clog 2 d) (hzr : σ.nat (B.rE + 2) = 0) (hr : 0 < I.r) (he : 0 < I.e)
    (hbt : 3 * (I.sepEx (I.base.lam + 1) + ellOF I (I.base.lam + 1) + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt)
    (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx (I.base.lam + 1) + I.eτ + I.eu +
      (I.sepEx (I.base.lam + 1) - (I.base.lam + 1) + ellOF I (I.base.lam + 1) + 1) + (I.jg + 1) + 8 ≤ ℓ)
    (hℓE : 64 * ellOE I (I.base.lam + 1) + 16 < ℓ) (hXl : cstX I (I.base.lam + 1) κ < ℓ)
    (hXa : cstX I (I.base.lam + 1) κ < 2 ^ ℓa)
    (hℓ0 : 4500 * (ellSz I.base + d + 2) ≤ ℓ) (hℓa0 : 1000 * (d + I.base.m + ellSz I.base + 1) ^ 3 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xbisBrO L B sepc gc TB) σ (bisBrOU I κ Kt) (fun σ' =>
      EllOut B.inner (bisO I T) (I.base.lam + 1) σ' ∧ σ'.sc (B.o + 1) = ((I.base.lam + 1 : ℕ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
        (fun b k => B.aW ≤ b ∨ Art b k) σ σ') := by
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
  obtain ⟨blam, -, -, bcR⟩ := ellLam_le I.base hd1 hr' he'
  obtain ⟨-, rW, -, -, -⟩ := ell_regs (m := I.base.m) blam hℓa0
  have hsz := ellSz_base_le I
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I (I.base.lam + 1)
  have hX : cstX I (I.base.lam + 1) κ = I.sepEx (I.base.lam + 1) + I.eτ + I.eK + κ + 12 := rfl
  have hOE : ellOE I (I.base.lam + 1) = ellE d (ellOSz I) + I.sepEx (I.base.lam + 1) + I.jg + 1 := rfl
  have hOF : ellOF I (I.base.lam + 1) = ellF d (ellOSz I) + I.sepEx (I.base.lam + 1) := rfl
  have hFF : ellF d (ellSz I.base) ≤ ellF d (ellOSz I) := by unfold ellF; omega
  have hFE : ellF d (ellOSz I) ≤ ellE d (ellOSz I) := by unfold ellF ellE; omega
  have hFO : ellF d (ellSz I.base) ≤ ellOF I (I.base.lam + 1) := by omega
  have hdO : d ≤ ellOF I (I.base.lam + 1) := by unfold ellF at hOF; omega
  have hRb0 : (0 : ℤ) ≤ I.base.Rb := by positivity
  have hRbs : (I.base.Rb : ℤ) ≤ 2 ^ ellSz I.base := by exact_mod_cast (ellRb_lt I.base).le
  have hM0 : (0 : ℤ) ≤ I.base.Rb * 2 ^ (I.base.lam + 1) := by positivity
  have bM : (I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1) ≤ 2 ^ ellF d (ellSz I.base) := by
    have : (I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1) ≤ 2 ^ (ellSz I.base + (I.base.lam + 1)) := by
      rw [pow_add (2 : ℤ) (ellSz I.base) (I.base.lam + 1)]; exact mul_le_mul_of_nonneg_right hRbs (by positivity)
    exact this.trans (pow_le_pow_right₀ (by norm_num) (by unfold ellF; omega))
  unfold bisBrOU
  -- BIS-R's constants
  refine XVO.seq (XVO.ofX (XV.bisSet hL (B := B.inner) (P := B.o + 83) (u := B.o + 95) (c := B.o + 155)
    (n0 := B.rE + 65) (lam := I.base.lam) (E := ellSz I.base) (Rb := I.base.Rb)
    (by simp only [EllOBlk.inner]; omega) (by omega) (by omega) (by omega) (by omega) hz hl hone hRb hRb0 hRbs
    (by omega) (by omega))) fun σ1 ⟨n71, o11, t3, t4, t5, t6, u21, lo1, hi1, k1, d1, F1⟩ => ?_
  have F1' : FrameA (fun y => B.o + 80 ≤ y) (fun j => B.rE + 64 ≤ j) (fun _ _ => False) σ σ1 :=
    F1.mono (fun y h => by simp only [bisSetS, EllOBlk.inner] at h; omega) (fun j h => by omega) (fun _ _ h => h)
  have hin1 : EllIn B.inner I.base σ1 := EllIn.frame hBi hin F1'
    (fun y h => by simp only [EllOBlk.inner]; omega) (fun j h => by simp only [EllOBlk.inner]; omega)
    (fun _ _ h => h.elim)
  have s1 : ∀ y, ¬ bisSetS B.inner (B.o + 83) (B.o + 95) y → σ1.sc y = σ.sc y := fun y h => F1.2.1 y h
  have hT1 : TestEnv B.inner I.base (I.base.lam + 1) (B.o + 83) (B.o + 95) (B.rE + 65 + 4) σ1 :=
    ⟨hin1, by rw [s1 _ (by simp only [bisSetS, EllOBlk.inner]; omega), hz],
      by rw [s1 _ (by simp only [bisSetS, EllOBlk.inner]; omega), h1], by rw [F1.1 _ (by omega)]; exact hone,
      t3, t4, t5, t6⟩
  -- the constants of step 2
  refine XVO.seq (XVO.ofX (XV.constO hL (B := B) (I := I) (s := I.base.lam + 1) (κ := κ) hB
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨Or.inr (Or.inl rfl), by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩⟩ (by rw [F1.1 _ (by omega)]; exact hj) (by rw [F1.1 _ (by omega)]; exact hcR)
    (by rw [F1'.1 _ (by omega), hcd]) n71 hT1.2.2.2.1 hT1.1.1
    (by rw [F1'.1 _ (by omega), vK]) (by rw [F1'.1 _ (by omega), vκ])
    ⟨by rw [F1'.2.2.1 _ _ id, vc.1], fun j => by rw [F1'.2.2.1 _ _ id, vc.2 j]⟩ hXl hXa))
    fun σ2 ⟨hE2, k2, kk2, cF2, o12, d2, F2⟩ => ?_
  have D2 : σ2.draws = σ.draws := d2.trans d1
  have hC2 : CxO B I TDat (I.eK + κ) (I.base.lam + 1) σ2 ∧ σ2.sc (B.o + 95 + 2) = 2 := by
    refine ⟨⟨TestEnv.below hB hT1 F2 (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h) (by omega)
      (by omega) (by omega), by rw [F2.1 _ (by omega), F1'.1 _ (by omega), hzr], cF2,
      ⟨hst σ σ2 hTD ((F1'.mono (fun y h => Or.inl (by simp only [EllOBlk.ownS]; omega))
        (fun j h => Or.inl (by simp only [EllOBlk.ownN]; omega)) (fun b k h => h.elim)).trans
        (F2.mono (fun y h => Or.inl (by simp only [EllOBlk.ownS]; omega))
        (fun j h => Or.inl (by simp only [EllOBlk.ownN]; omega)) (fun b k h => h.elim))) D2, k2, kk2⟩, hE2⟩,
      by rw [F2.2.1 _ (by omega)]; exact u21⟩
  -- the loop
  have lay : BisLay L B.inner (B.o + 83) (B.o + 95) (B.aW + 2) (B.aW + 2 + 6) (B.rE + 65) :=
    ⟨⟨⟨by simp only [EllOBlk.inner]; omega, by omega, by omega, by simp only [EllOBlk.inner]; omega, rfl, by omega,
      by simp only [EllOBlk.inner]; omega, rfl, rfl, by omega⟩, by omega, by omega⟩, by omega⟩
  have henv : ∀ σa σb : Env d, (CxO B I TDat (I.eK + κ) (I.base.lam + 1) σa ∧ σa.sc (B.o + 95 + 2) = 2) →
      σb.draws = σa.draws →
      FrameA (bpS (B.o + 83) (B.o + 95) (tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)))
        (lpN (B.rE + 65) (tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt)))
        (bpA (B.aW + 2) (taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art))) σa σb →
      (CxO B I TDat (I.eK + κ) (I.base.lam + 1) σb ∧ σb.sc (B.o + 95 + 2) = 2) := fun σa σb hCa hdab hF => by
    refine ⟨CxO.frame hB hav hst hCa.1 hdab hF (fun y hy => ?_) (fun j hj => ?_) (fun b k hb => ?_), ?_⟩
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
    · rw [hF.2.1 _ (fun hy => by
        rcases hy with h | h
        · omega
        · rcases tsO_cases h with h | ⟨-, h, -⟩ | h
          · omega
          · omega
          · have := stS _ h; omega)]
      exact hCa.2
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
  have hσF : ellOSz I ≤ ellOF I (I.base.lam + 1) := by unfold ellF at hOF; omega
  have hpF : 2 * (I.base.lam + 1) + 1 ≤ ellOF I (I.base.lam + 1) := by unfold ellF at hOF; omega
  refine XVO.seq (XVO.bisLoopT hL (B := B.inner) (I := I.base) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := ellF d (ellSz I.base)) (G := ellOE I (I.base.lam + 1)) (N := I.base.lam + 1)
    (Kt := stepU I Kt) (s := I.base.lam + 1) (tc := xtestOB L B sepc gc TB)
    (tf := tfO I.base T (I.base.lam + 1) (sepO I T (I.base.lam + 1)))
    (Ctx := fun σ' => CxO B I TDat (I.eK + κ) (I.base.lam + 1) σ' ∧ σ'.sc (B.o + 95 + 2) = 2)
    (TS := tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)) (TN := tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt))
    (TA := taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art))
    (M := I.base.Rb * 2 ^ (I.base.lam + 1)) (lo0 := -(I.base.Rb * 2 ^ (I.base.lam + 1)))
    (hi0 := I.base.Rb * 2 ^ (I.base.lam + 1)) (kept0 := none)
    hBi lay hd (fun σ' h => ⟨h.1.1, h.2⟩) henv
    (fun y hy1 hy2 h => by rcases nTS _ h with h | h | h <;> omega)
    (fun j hj1 hj2 hj3 h => by rcases nTN _ h with h | h <;> omega)
    (fun k h => by rcases nTA _ _ h with h | h | h <;> omega)
    (fun σ' a kept hC' hK' bK' ha' ba' => XVO.testStepO hL (F := ellOF I (I.base.lam + 1)) hd1 hB hDc hS hG hTB
      hav hst hC'.1 hK'
      (fun b W h => (bK' b W h).2.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
      ha' (fun k => (ba' k).trans (bM.trans (pow_le_pow_right₀ (by norm_num) (by omega)))) hσF hpF (by omega)
      (by omega) (by omega) hbt hℓ hℓS (by omega) (by omega) (by omega) (by omega))
    (fun a kept x h => tfO_ret h)
    (fun a kept c kept' ha' bK' h => tfO_cut (F := ellF d (ellSz I.base))
      (G := I.sepEx (I.base.lam + 1) + I.jg + 1) ha' bM bK'
      (fun Y Gv hY k => sepO_G_le I T (I.base.lam + 1) a hY k) (by unfold ellF; omega) (by unfold ellF; omega)
      (by unfold ellF; omega) (by unfold ellF ellE at *; omega) (by omega) h)
    hC2 (by rw [F2.2.1 _ (by omega)]; exact lo1) (by rw [F2.2.1 _ (by omega)]; exact hi1)
    (by rw [abs_neg, abs_of_nonneg hM0]) (by rw [abs_of_nonneg hM0])
    (by show σ2.sc (B.o + 83 + 1) = 0; rw [F2.2.1 _ (by omega)]; exact k1) (fun b W h => by cases h)
    (by rw [F2.1 _ (by omega)]; exact n71) (by omega) bM (by unfold ellF; omega)
    (by omega) hℓE) fun σ3 ⟨o3, d3, F3⟩ => ?_
  have hC3 := henv σ2 σ3 hC2 d3 F3
  have hT3 := hC3.1.1
  -- ELL-R's output into the inner block
  have s3 : ∀ y, B.o ≤ y ∧ y < B.o + 82 ∧ (y < B.o + 3 ∨ B.o + 76 ≤ y) → σ3.sc y = σ2.sc y :=
    fun y hy => F3.2.1 y (by
    rintro (h | h)
    · omega
    · rcases nTS _ h with h | h | h <;> omega)
  refine XVO.mono (XVO.ofX (XV.ellOut hL (B := B.inner) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := ellF d (ellSz I.base)) (e := I.base.lam + 1) (by simp only [EllOBlk.inner]; omega)
    (by omega) (by omega) (by simp only [EllOBlk.inner]; omega) (by omega) (by simp only [EllOBlk.inner]; omega)
    (by omega) hT3.1.1 hT3.2.2.2.1 hT3.2.1 hT3.2.2.1
    (by rw [show B.inner.o + 1 = B.o + 81 from rfl, s3 _ (by omega), F2.2.1 _ (by omega)]; exact o11) o3 bM
    (by omega))) le_rfl fun σ4 ⟨o4, d4, F4⟩ => ?_
  refine ⟨by rw [show bisO I T = _ from bisLoopO_eq I T _ _ _ _]; exact o4,
    by rw [F4.2.1 _ (by simp only [EllOBlk.inner]; omega), s3 _ (by omega), o12],
    d4.trans (d3.trans D2), ?_⟩
  refine ((F1'.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inl (by omega))
    (fun b k h => h.elim)).trans (F2.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inl (by omega))
    (fun b k h => h.elim))).trans ((F3.mono (fun y h => ?_) (fun j h => ?_) (fun b k h => ?_)).trans
    (F4.mono (fun y h => Or.inl ⟨by simp only [EllOBlk.inner] at h; omega, by simp only [EllOBlk.inner] at h; omega⟩)
      (fun j h => Or.inl (by omega)) (fun b k h => Or.inl (by simp only [EllOBlk.inner] at h; omega))))
  · rcases h with h | h
    · exact Or.inl ⟨by omega, by omega⟩
    · rcases tsO_cases h with h | ⟨h1, h2, -⟩ | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr h
  · rcases h with h | h
    · exact Or.inl (by omega)
    · rcases tnO_cases h with h | ⟨h1, -, -⟩ | h
      · exact Or.inl (by omega)
      · exact Or.inl h1
      · exact Or.inr h
  · rcases h with h | h
    · exact Or.inl (by omega)
    · rcases taO_cases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h

end AdversarialBco.Uni.EllO
