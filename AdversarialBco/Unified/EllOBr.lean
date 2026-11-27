/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOBrLoop

@[expose] public section

/-!
# UNI-ELL (c): the ELL-O branch on the oracle machine

`d ≥ 2`, after the constants up to `λ` of ELL-R's inner block (`XV.ellJ`): ELL-R's start state (`xellPre`, the first
four parts of `xellBr`, Bit/Transfer/XEllRule.lean), the constants of step 2 (`xconstO`), the loop of ELL-O
(`xloopT` with the test command `xtestOB`, `XVO.ellLoopBrO`) and ELL-R's output (`xellOut`) into the inner block.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 32000000 in
/-- **The ELL-O branch on the oracle machine** (`d ≥ 2`), from the constants up to `λ` of the inner block: the
result `ellO I T` over `2^p` in the inner block's output, `p` in the slot `o + 1`. -/
theorem XVO.ellBrO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : 2 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
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
    (hbt : 3 * (I.sepEx I.base.p + ellOF I I.base.p + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx I.base.p + I.eτ + I.eu + (I.sepEx I.base.p - I.base.p + ellOF I I.base.p + 1) + (I.jg + 1) + 8
      ≤ ℓ)
    (hℓE : 64 * ellOE I I.base.p + 16 < ℓ) (hXl : cstX I I.base.p κ < ℓ) (hXa : cstX I I.base.p κ < 2 ^ ℓa)
    (hℓ0 : 4500 * (ellSz I.base + d + 2) ≤ ℓ) (hℓa0 : 1000 * (d + I.base.m + ellSz I.base + 1) ^ 3 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xellBrO L B sepc gc TB) σ (ellBrOU I κ Kt) (fun σ' =>
      EllOut B.inner (ellO I T) I.base.p σ' ∧ σ'.sc (B.o + 1) = I.base.p ∧ σ'.draws = σ.draws ∧
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
  obtain ⟨blam, bp, bq, bcR⟩ := ellLam_le I.base hd1 hr' he'
  obtain ⟨-, -, -, -, -⟩ := ell_regs (m := I.base.m) blam hℓa0
  have hsz := ellSz_base_le I
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I I.base.p
  have hOE : ellOE I I.base.p = ellE d (ellOSz I) + I.sepEx I.base.p + I.jg + 1 := rfl
  have hOF : ellOF I I.base.p = ellF d (ellOSz I) + I.sepEx I.base.p := rfl
  have hEE : ellE d (ellSz I.base) ≤ ellE d (ellOSz I) := by unfold ellE; omega
  have hFF : ellF d (ellSz I.base) ≤ ellF d (ellOSz I) := by unfold ellF; omega
  have hFE : ellF d (ellOSz I) ≤ ellE d (ellOSz I) := by unfold ellF ellE; omega
  have hRb0 : (0 : ℤ) ≤ I.base.Rb := by positivity
  have hRbs : (I.base.Rb : ℤ) ≤ 2 ^ ellSz I.base := by exact_mod_cast (ellRb_lt I.base).le
  obtain ⟨-, -, -, -, -, -, pca⟩ := ell_pows (lam := I.base.lam) (p := I.base.p) hRb0 hRbs
  have ea : (2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.Rb * 2 ^ (3 * I.base.lam + 1)) =
      2 ^ I.base.p * ((I.base.Rb : ℤ) + (I.base.LamH : ℤ)) := by
    unfold EllI.LamH; push_cast; ring
  have bca : (2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH) ≤ 2 ^ ellF d (ellSz I.base) := by
    rw [← ea]; exact pca.trans (pow_le_pow_right₀ (by norm_num) (by unfold ellF; omega))
  unfold ellBrOU
  -- ELL-R's start state
  refine XVO.seq (XVO.ofX (XV.ellPre hL (B := B.inner) (I := I.base) (P := B.o + 83) (u := B.o + 95)
    (c := B.o + 155) (a0 := B.aW + 2) (n0 := B.rE + 65) hBi (by simp only [EllOBlk.inner]) rfl rfl
    (by simp only [EllOBlk.inner]) (by simp only [EllOBlk.inner]) (by omega) (by omega) (by omega) hin hz h1 hone
    hRb hj hcR hl hd hr' he' hℓ0 hℓa0)) fun σ1 ⟨hT1, hU1, hS1, n71, j1, cR1, p1, o11, d1, F1⟩ => ?_
  have F1' : FrameA (fun y => B.o + 80 ≤ y) (fun j => B.rE + 64 ≤ j) (fun b _ => B.aW ≤ b) σ σ1 := F1
  -- the constants of step 2
  refine XVO.seq (XVO.ofX (XV.constO hL (B := B) (I := I) (s := I.base.p) (κ := κ) hB
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨Or.inr (Or.inl rfl), by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩⟩ j1 cR1 (by rw [F1'.1 _ (by omega), hcd]) p1 hT1.2.2.2.1 hT1.1.1
    (by rw [F1'.1 _ (by omega), vK]) (by rw [F1'.1 _ (by omega), vκ])
    ⟨by rw [F1'.2.2.1 _ _ (by omega), vc.1], fun j => by rw [F1'.2.2.1 _ _ (by omega), vc.2 j]⟩ hXl hXa))
    fun σ2 ⟨hE2, k2, kk2, cF2, o12, d2, F2⟩ => ?_
  have D2 : σ2.draws = σ.draws := d2.trans d1
  have hC2 : CxO B I TDat (I.eK + κ) I.base.p σ2 ∧
      UpdEnv (B.o + 95) I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
        ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) σ2 := by
    refine ⟨⟨TestEnv.below hB hT1 F2 (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h) (by omega)
      (by omega) (by omega), by rw [F2.1 _ (by omega), F1'.1 _ (by omega), hzr], cF2,
      ⟨hst σ σ2 hTD ((F1'.mono (fun y h => Or.inl (by simp only [EllOBlk.ownS]; omega))
        (fun j h => Or.inl (by simp only [EllOBlk.ownN]; omega))
        (fun b k h => Or.inl (by simp only [EllOBlk.ownA]; omega))).trans
        (F2.mono (fun y h => Or.inl (by simp only [EllOBlk.ownS]; omega))
        (fun j h => Or.inl (by simp only [EllOBlk.ownN]; omega)) (fun b k h => h.elim))) D2, k2, kk2⟩, hE2⟩,
      hU1.frame F2 (fun y h => by omega)⟩
  refine XVO.seq (XVO.ellLoopBrO hL hd hB hDc hS hG hTB hav hst hr he hC2
    (hS1.frame (fun k => F2.2.2.1 _ _ id) (fun k => F2.2.2.1 _ _ id) (F2.2.1 _ (by omega)) (F2.2.1 _ (by omega))
      (fun k => F2.2.2.1 _ _ id))
    (by rw [F2.1 _ (by omega)]; exact n71) hbt hℓ hℓS hℓE hXa hℓa0) fun σ3 ⟨o3, d3, hT3, F3⟩ => ?_
  have nTS : ∀ y, tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St) y →
      (y = B.o + 82 ∨ y = B.o + 83 ∨ y = B.o + 84 ∨ y = B.o + 85 ∨ y = B.o + 90 ∨ B.o + 108 ≤ y) ∨
        (B.o + 3 ≤ y ∧ y < B.o + 76) ∨ y < B.o := fun y h => by
    rcases tsO_cases h with h | ⟨h1, h2, -⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (stS _ h))
  -- ELL-R's output into the inner block
  have s3 : ∀ y, B.o ≤ y ∧ y < B.o + 82 ∧ (y < B.o + 3 ∨ B.o + 76 ≤ y) → σ3.sc y = σ2.sc y :=
    fun y hy => F3.2.1 y (by
    rintro (h | h)
    · omega
    · rcases nTS _ h with h | h | h <;> omega)
  refine XVO.mono (XVO.ofX (XV.ellOut hL (B := B.inner) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := ellF d (ellSz I.base)) (e := I.base.p) (by simp only [EllOBlk.inner]; omega) (by omega)
    (by omega) (by simp only [EllOBlk.inner]; omega) (by omega) (by simp only [EllOBlk.inner]; omega) (by omega)
    hT3.1.1 hT3.2.2.2.1 hT3.2.1 hT3.2.2.1
    (by rw [show B.inner.o + 1 = B.o + 81 from rfl, s3 _ (by omega), F2.2.1 _ (by omega)]; exact o11) o3 bca
    (by omega))) le_rfl fun σ4 ⟨o4, d4, F4⟩ => ?_
  refine ⟨by rw [show ellO I T = _ from ellLoopO_eq I T _ _]; exact o4,
    by rw [F4.2.1 _ (by simp only [EllOBlk.inner]; omega), s3 _ (by omega), o12],
    d4.trans (d3.trans D2), ?_⟩
  refine ((F1'.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inl (by omega))
    (fun b k h => Or.inl h)).trans (F2.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inl (by omega))
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
