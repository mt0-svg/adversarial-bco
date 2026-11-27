/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllORoute
public import AdversarialBco.Unified.EllOUBr
public import AdversarialBco.Unified.EllOUBis

@[expose] public section

/-!
# The route of ELL-O with the blocks uniform in `d`

`XVO.ellOMain` (EllORoute.lean) on `XVO.ellBrOD` and `XVO.bisBrOD`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 16000000 in
/-- The rule of `xellOMain`, from the start: the inner block's output holds `ellOI I T` over `2^{ellExpO I}` (the
exponent also in the slot `o + 1` when there is a point), the slot `o + 77` keeps its `0`. -/
theorem XVO.ellOMainD {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {κ Kt bt : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOKU L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOKU L XO ℓa ℓ (gaugeLayO B) gc)
    (hT0 : ∀ τ : Env d, TDat τ → τ.nat 0 = d) (hNt0 : ∀ j, Nt j → j ≠ 0)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hTD : TDat σ) (hin : EllOIn B I κ σ) (hz : σ.sc (B.o + 95) = 0) (h1 : σ.sc (B.o + 96) = 1)
    (hone : σ.nat (B.rE + 69) = 1) (hzr : σ.nat (B.rE + 2) = 0) (hcd : σ.nat (B.rE + 58) = Nat.clog 2 d)
    (h77 : σ.sc (B.o + 77) = 0)
    (hbt : 0 < I.r → 0 < I.e → bigO I κ ≤ bt) (hℓ : bt + 4 ≤ ℓ) (hℓa : 0 < I.r → 0 < I.e → bigO I κ < 2 ^ ℓa)
    (hsl : ellOSz I + 2 < ℓ) (hℓa3 : 1000 * (d + ellOSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xellOMain L B sepc gc TB) σ (ellOMUc I κ Kt) (fun σ' =>
      EllOut B.inner (ellOI I T) (ellExpO I) σ' ∧ (ellOI I T ≠ none → σ'.sc (B.o + 1) = ellExpO I) ∧
      σ'.sc (B.o + 77) = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
        (fun b k => B.aW ≤ b ∨ Art b k) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, hsl, hsDf, hsRn, hsRd, hsrn, hsrd, hsen, hsed, haH, hag, haP, haf,
    hac⟩ := hB'
  have hBi := inner_OK hB
  have hinI : EllIn B.inner I.base σ := ellIn_inner hin hzr
  have hin' := hin
  obtain ⟨e_d, e_K, e_κ, -, -, e_Rn, e_Rd, e_rn, -, e_en, -, -, -, -, -, e_c0, e_c⟩ := hin'
  have hsz := ellSz_base_le I
  have hbig : bigO I κ = 64 * (ellOE I I.base.p + ellOE I (I.base.lam + 1) + ellOF I I.base.p +
      ellOF I (I.base.lam + 1) + cstX I I.base.p κ + cstX I (I.base.lam + 1) κ + I.eu + I.eτ + I.jg + I.eH +
      ellOSz I + d) + 4500 * (ellSz I.base + d + 2) + 100 := rfl
  have eFp : ellOF I I.base.p = ellF d (ellOSz I) + I.sepEx I.base.p := rfl
  have eFl : ellOF I (I.base.lam + 1) = ellF d (ellOSz I) + I.sepEx (I.base.lam + 1) := rfl
  have eXp : cstX I I.base.p κ = I.sepEx I.base.p + I.eτ + I.eK + κ + 12 := rfl
  have eXl : cstX I (I.base.lam + 1) κ = I.sepEx (I.base.lam + 1) + I.eτ + I.eK + κ + 12 := rfl
  have hs : ellSz I.base < ℓ := by omega
  have h3 : 1000 * (d + I.base.m + ellSz I.base + 1) ^ 3 < 2 ^ ℓa := by
    have : (d + I.base.m + ellSz I.base + 1) ^ 3 ≤ (d + ellOSz I + 1) ^ 3 :=
      Nat.pow_le_pow_left (by have : I.base.m = 0 := rfl; omega) 3
    omega
  have bRn : |σ.sc B.sRn| < 2 ^ ℓ := by rw [e_Rn]; exact abs_cast_lt (ellRn_le (I := I.base) le_rfl) hs
  have bRd : |σ.sc B.sRd| < 2 ^ ℓ := by
    have := abs_cast_lt (ellRd_le (I := I.base) le_rfl) hs
    rw [e_Rd]; simp at this ⊢; exact this
  have bz : |σ.sc (B.o + 95)| < 2 ^ ℓ := by rw [hz, abs_zero]; positivity
  have brn : |σ.sc B.srn| < 2 ^ ℓ := by
    rw [e_rn]; exact abs_cast_lt (abs_le_sz (ellMx_le I.base).2.2.2.2.2.2.2.2.2.2.1) hs
  have ben : |σ.sc B.sen| < 2 ^ ℓ := by
    rw [e_en]; exact abs_cast_lt (abs_le_sz (ellMx_le I.base).2.2.2.2.2.2.2.2.2.2.2.2.1) hs
  have fail : ∀ σ' : Env d, σ'.sc (B.o + 80) = 0 → σ'.draws = σ.draws →
      FrameA (fun y => y = B.o + 80) (fun _ => False) (fun _ _ => False) σ σ' → ellOI I T = none →
      EllOut B.inner (ellOI I T) (ellExpO I) σ' ∧ (ellOI I T ≠ none → σ'.sc (B.o + 1) = ellExpO I) ∧
        σ'.sc (B.o + 77) = 0 ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
          (fun b k => B.aW ≤ b ∨ Art b k) σ σ' :=
    fun σ' v dr F hn => by
      rw [hn]
      exact ⟨v, fun h => (h rfl).elim, by rw [F.2.1 _ (by omega)]; exact h77, dr,
        F.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h.elim)⟩
  -- `R < 1`
  by_cases hR : I.R < 1
  · have hc : σ.sc B.sRn < σ.sc B.sRd := by
      rw [e_Rn, e_Rd]; exact_mod_cast (ellRI_cond I.base).1.1 hR
    refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) bRn bRd hc
      (XVO.ofX (XV.setZ hL (x := B.o + 80) (z := B.o + 95) (by omega) (by omega) hz))) (by unfold ellOMUc; split_ifs <;> (try unfold ellOMU) <;> omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellOI_none (Or.inl hR))
  have hc : ¬ σ.sc B.sRn < σ.sc B.sRd := by
    rw [e_Rn, e_Rd]; intro h; exact hR ((ellRI_cond I.base).1.2 (by exact_mod_cast h))
  -- `r ≤ 0`
  by_cases hr : I.r ≤ 0
  · have hc2 : ¬ σ.sc (B.o + 95) < σ.sc B.srn := by
      rw [hz, e_rn]; intro h
      have h' : (0 : ℤ) < I.r.num := by exact_mod_cast h
      have : I.r.num ≤ 0 := (ellRI_cond I.base).2.1.1 hr; omega
    refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) bRn bRd hc (XVO.ifS_f hL (by omega) (by omega) bz brn hc2
      (XVO.ofX (XV.setZ hL (x := B.o + 80) (z := B.o + 95) (by omega) (by omega) hz)))) (by unfold ellOMUc; split_ifs <;> (try unfold ellOMU) <;> omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellOI_none (Or.inr (Or.inl hr)))
  have hc2 : σ.sc (B.o + 95) < σ.sc B.srn := by
    rw [hz, e_rn]
    have h' : ¬ I.r.num ≤ 0 := fun h => hr ((ellRI_cond I.base).2.1.2 h)
    have : (0 : ℤ) < I.r.num := by omega
    exact_mod_cast this
  -- `e ≤ 0`
  by_cases he : I.e ≤ 0
  · have hc3 : ¬ σ.sc (B.o + 95) < σ.sc B.sen := by
      rw [hz, e_en]; intro h
      have h' : (0 : ℤ) < I.e.num := by exact_mod_cast h
      have : I.e.num ≤ 0 := (ellRI_cond I.base).2.2.1 he; omega
    refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) bRn bRd hc (XVO.ifS_t hL (by omega) (by omega) bz brn hc2
      (XVO.ifS_f hL (by omega) (by omega) bz ben hc3
      (XVO.ofX (XV.setZ hL (x := B.o + 80) (z := B.o + 95) (by omega) (by omega) hz))))) (by unfold ellOMUc; split_ifs <;> (try unfold ellOMU) <;> omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellOI_none (Or.inr (Or.inr he)))
  have hc3 : σ.sc (B.o + 95) < σ.sc B.sen := by
    rw [hz, e_en]
    have h' : ¬ I.e.num ≤ 0 := fun h => he ((ellRI_cond I.base).2.2.2 h)
    have : (0 : ℤ) < I.e.num := by omega
    exact_mod_cast this
  have hr0 : 0 < I.r := not_le.1 hr
  have he0 : 0 < I.e := not_le.1 he
  have hbt0 := hbt hr0 he0
  have hℓa0 := hℓa hr0 he0
  rw [show ellOMUc I κ Kt = ellOMU I κ Kt by simp [ellOMUc, hr0, he0]]
  -- the constants up to `λ`
  refine XVO.mono (K := (((ellJU d (ellSz I.base) + (ellBrOU I κ Kt + bisBrOU I κ Kt + 2)) + 1) + 1) + 2) ?_
    (by unfold ellOMU; omega) (fun _ h => h)
  refine XVO.ifS_f hL (by omega) (by omega) bRn bRd hc ?_
  refine XVO.ifS_t hL (by omega) (by omega) bz brn hc2 ?_
  refine XVO.ifS_t hL (by omega) (by omega) bz ben hc3 ?_
  refine XVO.seq (XVO.ofX (XV.ellJ hL (B := B.inner) (I := I.base) (u := B.o + 95) (c := B.o + 155)
    (n0 := B.rE + 65) (E := 6 * ellSz I.base + d + 4) hBi (by simp only [EllOBlk.inner]; omega) (by omega)
    (by omega) (by simp only [EllOBlk.inner]; omega) (by omega) hinI hz h1 hone hd hR hr0 he0 le_rfl (by omega)
    (by omega))) fun σ4 ⟨c4, j4, cR4, l4, d4, F4⟩ => ?_
  have G4 : FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
      (fun b k => B.aW ≤ b ∨ Art b k) σ σ4 :=
    F4.mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have hin4 : EllOIn B I κ σ4 := EllOIn.frame hB hin F4 (fun y h => by omega) (fun j h => by omega)
    (fun _ _ h => h.elim)
  have hTD4 : TDat σ4 := hst σ σ4 hTD (F4.mono (fun y h => Or.inl (by simp only [EllOBlk.ownS]; omega))
    (fun j h => Or.inl (by simp only [EllOBlk.ownN]; omega)) (fun _ _ h => h.elim)) d4
  have hzr4 : σ4.nat (B.rE + 2) = 0 := by rw [F4.1 _ (by omega), hzr]
  have hinI4 : EllIn B.inner I.base σ4 := ellIn_inner hin4 hzr4
  have hz4 : σ4.sc (B.o + 95) = 0 := by rw [F4.2.1 _ (by omega), hz]
  have h14 : σ4.sc (B.o + 96) = 1 := by rw [F4.2.1 _ (by omega), h1]
  have hone4 : σ4.nat (B.rE + 69) = 1 := by rw [F4.1 _ (by omega), hone]
  have hcd4 : σ4.nat (B.rE + 58) = Nat.clog 2 d := by rw [F4.1 _ (by omega), hcd]
  have h774 : σ4.sc (B.o + 77) = 0 := by rw [F4.2.1 _ (by omega), h77]
  have hd4 : σ4.nat B.rd = d := hin4.1
  have hsa : 1 < 2 ^ ℓa := by omega
  have post : ∀ σ' : Env d, ∀ r : Option (Fin d → ℤ), ∀ e : ℕ, ellOI I T = r → ellExpO I = e →
      EllOut B.inner r e σ' ∧ σ'.sc (B.o + 1) = (e : ℝ) ∧ σ'.draws = σ4.draws ∧
        FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
          (fun b k => B.aW ≤ b ∨ Art b k) σ4 σ' →
      EllOut B.inner (ellOI I T) (ellExpO I) σ' ∧ (ellOI I T ≠ none → σ'.sc (B.o + 1) = ellExpO I) ∧
        σ'.sc (B.o + 77) = 0 ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => (B.o + 1 ≤ y ∧ y ≠ B.o + 77) ∨ St y) (fun j => B.rE ≤ j ∨ Nt j)
          (fun b k => B.aW ≤ b ∨ Art b k) σ σ' :=
    fun σ' r e hr he ⟨out, s1, dr, F⟩ => by
      rw [hr, he]
      refine ⟨out, fun _ => s1, ?_, dr.trans d4, G4.trans F⟩
      rw [F.2.1 _ (fun h => by
        rcases h with h | h
        · omega
        · have := (hav.1 _ h).1; simp only [EllOBlk.ownS] at this; omega), h774]
  by_cases hd2 : 2 ≤ d
  · -- ELL-O
    obtain ⟨eR, eE⟩ := ellOI_ell (T := T) hR hr0 he0 hd2
    refine XVO.mono (XVO.ifN_t hL (by omega) (by omega) (by rw [hone4]; exact hsa) (by rw [hd4]; omega)
      (by rw [hone4, hd4]; omega)
      (XVO.ellBrOD hL hd2 hB hDc hS hG hT0 hNt0 hTB hav hst hTD4 hinI4 hin4.2.1 hin4.2.2.1 ⟨hin4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hin4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ hz4 h14 hone4 c4 j4 cR4 l4 hcd4 hzr4 hr0 he0 (by omega) hℓ
        (by omega) (by omega) (by omega) (by omega) (by omega) h3)) (by omega) ?_
    exact fun σ' h => post σ' _ _ eR eE h
  · -- BIS-O
    have hd1 : d = 1 := by omega
    obtain ⟨eR, eE⟩ := ellOI_bis (T := T) hR hr0 he0 hd1
    refine XVO.mono (XVO.ifN_f hL (by omega) (by omega) (by rw [hone4]; exact hsa) (by rw [hd4]; omega)
      (by rw [hone4, hd4]; omega)
      (XVO.bisBrOD hL hd1 hB hDc hS hG hT0 hNt0 hTB hav hst hTD4 hinI4 hin4.2.1 hin4.2.2.1 ⟨hin4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hin4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩ hz4 h14 hone4 c4 j4 cR4 l4 hcd4 hzr4 hr0 he0 (by omega) hℓ
        (by omega) (by omega) (by omega) (by omega) (by omega) h3)) (by omega) ?_
    exact fun σ' h => post σ' _ _ eR eE h


end AdversarialBco.Uni.EllO
