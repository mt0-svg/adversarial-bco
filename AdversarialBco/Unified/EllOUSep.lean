/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOSep
public import AdversarialBco.Unified.ProgOSepU
public import AdversarialBco.Unified.ProgOSepUS

@[expose] public section

/-!
# ELL-O's SEP call with the blocks uniform in `d`

`sepCallOD` is `sepCallO` (EllOSep.lean) on a SEP block meeting `SepBlockOKU` and a gauge block meeting
`GaugeBlockOKU` (ProgOSepUS.lean, ProgOSepU.lean), whose texts do not depend on `d`: they read `d` in the register
`0`. The test's data gives `d` there (`hT0`) and the test block keeps the register `0` (`hNt0`).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The gauge layout of the block meets `GaugeLay.OKU`. -/
theorem gaugeLayO_OKU {L : Layout} {B : EllOBlk} (hB : B.OK L 215 112 14) : GaugeLay.OKU L (gaugeLayO B) := by
  have h := hB.2.2.2.2.2.2.1
  exact ⟨gaugeLayO_OK hB, by simp only [gaugeLayO]; omega, by simp only [gaugeLayO]; omega⟩

set_option maxHeartbeats 4000000 in
/-- **The SEP call of ELL-O**: the SEP block on the gauge block (about the centre `c`, `H = 2^{eH}`, `jg` steps) on the
test block computes `sepO I T s a` from `Y₀ = 2^{E-s} a` in SEP's array, `E = sepEx s`, and writes only the cells of
the three blocks. -/
theorem sepCallOD {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {B : EllOBlk} {I : EllOI d}
    {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool} {k Kt bt s F : ℕ}
    {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop} {σ : Env d} {a : Fin d → ℤ}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOKU L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOKU L XO ℓa ℓ (gaugeLayO B) gc)
    (hT0 : ∀ τ : Env d, TDat τ → τ.nat 0 = d) (hNt0 : ∀ j, Nt j → j ≠ 0)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat k) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hT : TDatK B TDat k σ) (hE : SepEnvO B I s σ)
    (hY : ∀ i : Fin d, σ.arr (B.aW + 9) i = ((2 : ℤ) ^ (I.sepEx s - s) • a) i) (ba : ∀ i, |a i| ≤ 2 ^ F)
    (hbt : 3 * (I.sepEx s + F + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx s + I.eτ + I.eu + (I.sepEx s - s + F + 1) + (I.jg + 1) + 8 ≤ ℓ)
    (hℓa : I.sepEx s + I.eτ + 8 < 2 ^ ℓa) (hja : I.jg + 1 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (sepc (gc TB)) σ (sepK d (I.eL + I.eτ + 3) (gaugeK d I.jg Kt)) (fun σ' =>
      SepOut (sepLayO B) (sepO I T s a) σ' ∧
      FrameA (fun y => sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
        (fun j => sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
        (fun b k => sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k) σ σ' ∧ σ'.draws = σ.draws) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB'
  have hav' := hav
  obtain ⟨avS, avN, avA⟩ := hav'
  -- the frames of the inner blocks
  have mT : ∀ σa σb : Env d, FrameA (fun y => sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
      (fun j => sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k) σa σb →
      FrameA (fun y => (B.ownS y ∧ y ≠ B.o + 2) ∨ St y) (fun j => (B.ownN j ∧ j ≠ B.rE + 1) ∨ Nt j)
        (fun b k => B.ownA b k ∨ Art b k) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h
      · left; simp only [sepS, sepLayO, EllOBlk.ownS] at h ⊢; omega
      · left; simp only [gaugeS, gaugeLayO, EllOBlk.ownS] at h ⊢; omega
      · exact Or.inr h) (fun j h => by
      rcases h with h | h | h
      · left; simp only [sepN, sepLayO, EllOBlk.ownN] at h ⊢; omega
      · left; simp only [gaugeN, gaugeLayO, EllOBlk.ownN] at h ⊢; omega
      · exact Or.inr h) (fun b k h => by
      rcases h with h | h | h
      · left; simp only [sepAr, sepLayO, EllOBlk.ownA] at h ⊢; omega
      · left; simp only [gaugeAr, gaugeLayO, EllOBlk.ownA] at h ⊢; omega
      · exact Or.inr h)
  have stT : Stable (TDatK B TDat k) (fun y => gaugeS (gaugeLayO B) y ∨ St y)
      (fun j => gaugeN (gaugeLayO B) j ∨ Nt j) (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) :=
    fun σa σb h hF hd' => TDatK.frame hav hst h hd' (mT σa σb (hF.mono (fun y h => Or.inr h) (fun j h => Or.inr h)
      (fun b k h => Or.inr h)))
  have gdisj : GaugeDisj (gaugeLayO B) St Nt Art := by
    refine ⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩
    · have := (avS y h).1; simp only [EllOBlk.ownS] at this; simp only [gaugeLayO]; omega
    · rcases (avN j h).1 with h' | h'
      · simp only [EllOBlk.ownN] at h'; simp only [gaugeLayO]; omega
      · simp only [gaugeLayO]; omega
    · have := (avA b k h).1; have := (avA b k h).2.2.2.2.2; simp only [EllOBlk.ownA] at *
      simp only [gaugeLayO]; omega
  have sdisj : SepDisj (sepLayO B) (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) := by
    refine ⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩
    · rcases h with h | h
      · simp only [gaugeS, gaugeLayO] at h; simp only [sepLayO]; omega
      · have := (avS y h).1; simp only [EllOBlk.ownS] at this; simp only [sepLayO]; omega
    · rcases h with h | h
      · simp only [gaugeN, gaugeLayO] at h; simp only [sepLayO]; omega
      · rcases (avN j h).1 with h' | h'
        · simp only [EllOBlk.ownN] at h'; simp only [sepLayO]; omega
        · simp only [sepLayO]; omega
    · rcases h with h | h
      · simp only [gaugeAr, gaugeLayO] at h; simp only [sepLayO]; omega
      · have := (avA b k h).1; simp only [EllOBlk.ownA] at this; simp only [sepLayO]; omega
  -- the evaluator: the gauge block on the test block
  set E := I.sepEx s with hEdef
  set b := E + F + I.eH + ellOSz I + 3 with hb
  have bY : ∀ i, |((2 : ℤ) ^ (E - s) • a) i| ≤ 2 ^ (E - s + F) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by positivity), pow_add]
    exact mul_le_mul_of_nonneg_left (ba i) (by positivity)
  obtain ⟨mDc, mNc⟩ := ellOMx_le I
  have hpow : ∀ m, m ≤ b → (2 : ℤ) ^ m ≤ 2 ^ b := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hEV : EvalOK L XO ℓa ℓ (gc TB) (fun σ' => TDatK B TDat k σ' ∧ SepEnvO B I s σ') (sepLayO B).aev
      (sepLayO B).vout E (SepDom ((2 : ℤ) ^ (E - s) • a) E I.e1) (I.evO T E) (gaugeK d I.jg Kt)
      (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) := by
    intro σ' X ⟨hT', hE'⟩ hX h0 hXi
    obtain ⟨-, -, -, -, -, -, e7, e8, e9, e10, e11, e12⟩ := hE'
    have bX : ∀ i, |X i| < 2 ^ b := fun i => by
      have h1 := hX i
      have h2 := bY i
      have h3 : (2 : ℤ) ^ (E - s + F) ≤ 2 ^ (b - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : 2 * (2 : ℤ) ^ (E - I.e1) ≤ 2 ^ (b - 2) := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h5 : (2 : ℤ) ^ b = 4 * 2 ^ (b - 2) := by
        have hb2 : b = 2 + (b - 2) := by omega
        conv_lhs => rw [hb2, pow_add]
        norm_num
      have h6 : 0 < (2 : ℤ) ^ (b - 2) := by positivity
      rw [abs_le] at h2; rw [abs_le] at h1; rw [abs_lt]; constructor <;> linarith
    have bDc : I.Dc < 2 ^ b := lt_of_le_of_lt (le_abs_self _)
      ((abs_lt_ellOSz mDc).trans_le (hpow _ (by omega)))
    have bNc : ∀ i, |I.Nc i| < 2 ^ b := fun i => (abs_lt_ellOSz (mNc i)).trans_le (hpow _ (by omega))
    refine XVO.mono (hG TB (TDatK B TDat k) T Kt bt St Nt Art σ' (2 ^ E) X I.Dc I.Nc (2 ^ I.eH) 1 I.jg b hL
      (gaugeLayO_OKU hB) hd hTB ⟨gdisj, hNt0⟩ stT hT' (hT0 _ hT'.1) (by push_cast; exact h0) hXi e11 e12 e7 e8 e9 e10 (by positivity) hDc
      (by positivity) one_pos (pow_lt_pow_right₀ (by norm_num) (by omega)) bX bDc bNc
      (pow_lt_pow_right₀ (by norm_num) (by omega)) (one_lt_pow₀ (by norm_num) (by omega)) hbt hℓ hja) le_rfl ?_
    rintro σ'' ⟨v, Fv, dv⟩
    refine ⟨?_, Fv, dv⟩
    have hH : ((2 ^ I.eH : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = (2 : ℚ) ^ I.eH := by push_cast; ring
    show σ''.sc (B.o + 3) = ((I.evO T E X : ℤ) : ℝ)
    rw [show B.o + 3 = (gaugeLayO B).gout from rfl, v, hH]
    unfold EllOI.evO EllOI.c
    push_cast
    rfl
  refine hS (gc TB) (fun σ' => TDatK B TDat k σ' ∧ SepEnvO B I s σ') (I.evO T E) (gaugeK d I.jg Kt) (I.jg + 1)
    (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
    (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) σ ((2 : ℤ) ^ (E - s) • a) E I.e1 I.eτ I.eL I.eu
    (E - s + F + 1) hL (sepLayO_OK hB) hd hEV ?_ sdisj ?_ ⟨hT, hE⟩ (hT0 _ hT.1) hY ?_ hE.1 hE.2.1 hE.2.2.1 hE.2.2.2.1
    hE.2.2.2.2.1 hE.2.2.2.2.2.1 ?_ hℓS hℓa
  · intro X _
    obtain ⟨h0, h1⟩ := evO_lt I T E X
    rw [abs_of_nonneg h0]; exact h1
  · intro σa σb ⟨h1, h2⟩ hF hd'
    exact ⟨TDatK.frame hav hst h1 hd' (mT σa σb hF), SepEnvO.frame hac hav h2 hF⟩
  · intro i; exact (bY i).trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  · rw [hEdef]; unfold EllOI.sepEx; omega


end AdversarialBco.Uni.EllO
