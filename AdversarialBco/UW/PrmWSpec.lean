/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.PrmWLink
public import AdversarialBco.Unified.ProgOSetupParam

@[expose] public section

/-!
# PARAM-W on the machine: the contract

`xparW`: BL-O's PARAM at `k_δ` (`xparO`, Unified/ProgOSetupParam.lean), then the straight line `parStW` (UW/PrmWV.lean,
inputs `d, n, N_e, k_δ` in the slots `0, 3, 7, 29`, which PARAM leaves) and the copies of PARAM-W's eight fields
`ε', λ', η', ρ', κ_c', ν', A_0, B_0` into BL's slots; the line writes `2^p b0` and `2^p y0` into the slots `122`, `123`
itself. `paramSpecW : ParamWSpec xparW 8000000 1 172 48 0`: PARAM's contract, the run `XV.paramW`, the magnitudes
`pvW_abs` (every value of the line at most `2^{63 G + 301}`, `G ≤ 6000 W`) and the links of UW/PrmWLink.lean.
`ParamWSpec` is the contract `ParamWSpecS` of UW/ProgMachSetup.lean, word for word.
-/

namespace AdversarialBco.UW.PrmW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Unified.PrmK
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.BitRAM (len)
open AdversarialBco.UW.BLOW (b0OW y0OW parOW)
open AdversarialBco.Bit.BLP (Cfg Mode St Par init up rnd)
open BitRAM BitRAMO

/-- **PARAM-W**: from what PARAM at `k_δ` reads, `xpw L` writes PARAM-W's values at `parOW d n δ` (`ParO`), `2^p b0` and
`2^p y0` into the slots `122`, `123`, integers at most `2^{C (W + 1)^k}`, within `C (W + 1)^k` units, in PARAM's
frame; it reads no coin. -/
def ParamWSpec (xpw : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    σ.nat rD = d → σ.nat rOne = 1 → σ.sc 0 = d → σ.sc sMode = 0 → σ.sc sN = n → σ.sc 26 = 1 → σ.sc 27 = 2 →
    σ.sc 28 = 4 → σ.sc sKd = kDel δ →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpw L) σ (C * (wU d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      ParO σ' (parOW d n δ) ∧ SlotBnd σ' 4 22 (C * (wU d n δ r0 R0 a + 1) ^ k) ∧
      σ'.sc 122 = ((qn (parO d n δ).p (b0OW d n δ) : ℤ) : ℝ) ∧
      σ'.sc 123 = ((qn (parO d n δ).p (y0OW d n δ) : ℤ) : ℝ) ∧
      |qn (parO d n δ).p (b0OW d n δ)| ≤ 2 ^ (C * (wU d n δ r0 R0 a + 1) ^ k) ∧
      |qn (parO d n δ).p (y0OW d n δ)| ≤ 2 ^ (C * (wU d n δ r0 R0 a + 1) ^ k) ∧ σ'.draws = σ.draws ∧
      FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ σ')

/-- The copies of PARAM-W's fields from the line (step `k` in the slot `30 + k`) into BL's slots. -/
def prmCopiesW : List (ℕ × ℕ) :=
  [(sEps, 95), (sLamb, 96), (sEta, 97), (sRho, 99), (sKapc, 100), (sNu, 101), (sA0, 105), (sB0, 106)]

theorem prmCopiesW_ok : (∀ p ∈ prmCopiesW, p.1 < 30 ∧ p.1 ≠ sMode ∧ 30 ≤ p.2 ∧ p.2 < 124) ∧
    (prmCopiesW.map Prod.fst).Nodup ∧ (∀ p ∈ prmCopiesW, ∀ q ∈ prmCopiesW, p.1 ≠ q.2) ∧
    (∀ p ∈ prmCopiesW, 4 ≤ p.1 ∧ p.1 < 22) := by decide

/-- **PARAM-W of BL-OW**: PARAM at `k_δ`, the line `parStW`, the copies. -/
def xparW (L : Layout) : XCmdO :=
  .seq (xparO L) (.base (.seq (SL.code L parC parStW) (xcopyS L sMode prmCopiesW)))

/-- Every value of the line is at most `2^{63 G + 301}`, `G = parGK d n e`. -/
theorem pvW_abs {d n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {k : ℕ} (hk : k < 94) :
    |pvW d n e k| ≤ 2 ^ (63 * parGK d n e + 301) := by
  have h := SL.val_bound parStW 30 (parIW d n e) [0, 3, 7, 29] parInW parEtW parTW 44 (parGK d n e)
    (SL.chk_get parStW_chk).2 (par_semW hd hn) (parIn_okW hd hn) k (by rw [parStW_length]; exact hk)
  have hle : ∀ k < 94, (parEtW k).1 ≤ 63 ∧ (parEtW k).2 ≤ 301 := by decide
  obtain ⟨h1, h2⟩ := hle k hk
  refine h.trans (pow_le_pow_right₀ (by norm_num) ?_)
  unfold ev
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **PARAM-W on the machine.** -/
theorem paramSpecW : ParamWSpec xparW 8000000 1 172 48 0 := by
  intro d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hrD hrOne h0 hMode hN h26 h27 h28 hKd hℓ hℓa
  have hO := paramSpecO d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hrD hrOne h0 hMode hN h26 h27 h28 hKd
    (by simp only [pow_one] at hℓ ⊢; omega) (by simp only [pow_one] at hℓa ⊢; omega)
  obtain ⟨hNS, hNN, -⟩ := hR
  simp only [pow_one] at hℓ hℓa hO ⊢
  have hd := hI.hd
  have hn := hI.hn
  have hk := kDel_le_size hI.hδ0
  have hS : len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  have hW : wU d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  have hGb := parGK_le d n (kDel δ)
  have hGW : parGK d n (kDel δ) ≤ 6000 * wU d n δ r0 R0 a := by omega
  have hTl : 63 * parGK d n (kDel δ) + 301 < ℓ := by omega
  have hTa : 63 * parGK d n (kDel δ) + 301 < 2 ^ ℓa := by omega
  have hTs : 63 * parGK d n (kDel δ) + 301 ≤ 8000000 * (wU d n δ r0 R0 a + 1) := by omega
  have hOs : 4200000 * (wU d n δ r0 R0 a + 1) ≤ 8000000 * (wU d n δ r0 R0 a + 1) := by omega
  have h2ℓ : (2 : ℤ) ^ (63 * parGK d n (kDel δ) + 301) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hTl
  have hK : 4200000 * (wU d n δ r0 R0 a + 1) + ((564 * parGK d n (kDel δ) + 2472) + prmCopiesW.length) ≤
      8000000 * (wU d n δ r0 R0 a + 1) := by
    have g1 : 564 * parGK d n (kDel δ) ≤ 564 * (6000 * wU d n δ r0 R0 a) := Nat.mul_le_mul_left _ hGW
    have hl : prmCopiesW.length = 8 := rfl
    rw [hl]
    linarith
  obtain ⟨ok1, ok2, ok3, ok4⟩ := prmCopiesW_ok
  refine XVO.mono (XVO.seq hO fun σ1 ⟨hP1, hB1, hD1, hF1⟩ => XVO.ofX ?_) hK fun _ h => h
  -- what PARAM leaves
  have k1 : ∀ y, ¬ SPar y → σ1.sc y = σ.sc y := hF1.2.1
  have r1 : ∀ j, j < rP → σ1.nat j = σ.nat j := fun j hj => hF1.1 j (show ¬ (rP ≤ j) by omega)
  have k1' : ∀ y, y < 4 ∨ (22 ≤ y ∧ y ≤ 29) → σ1.sc y = σ.sc y := fun y hy => k1 y (by unfold SPar; omega)
  refine XV.seq (XV.paramW (e := kDel δ) hL hNS (by omega) hd hn hTl hTa
    (by rw [k1' 0 (by norm_num), h0]) (by rw [k1' 3 (by norm_num)]; exact hN)
    (by rw [k1' 1 (by norm_num)]; exact hMode) hP1.consts.2.2.2.2.1
    (by rw [k1' 29 (by norm_num)]; exact hKd) (by rw [k1' 26 (by norm_num), h26])
    (by rw [k1' 27 (by norm_num), h27]) (by rw [k1' 28 (by norm_num), h28])
    (by rw [r1 3 (by decide)]; exact hrOne)) fun σ2 ⟨hv, d2, F2⟩ => ?_
  have k2 : ∀ y, y < 30 → σ2.sc y = σ1.sc y := fun y hy =>
    F2.2.1 y (show ¬ ((30 ≤ y ∧ y < 124) ∨ 128 ≤ y) by omega)
  have hv2 : ∀ y, 30 ≤ y → y < 124 → σ2.sc y = pvW d n (kDel δ) (y - 30) := fun y h1 h2 => by
    have := hv (y - 30) (by omega)
    rwa [show 30 + (y - 30) = y by omega] at this
  refine XV.mono (XV.copyS hL (z := sMode) (by bomega) prmCopiesW σ2
    (by rw [k2 sMode (by decide), k1' sMode (by decide)]; exact hMode)
    (fun p hp => ?_) ok2 ok3) le_rfl fun σ3 ⟨hc, dc, Fc⟩ => ?_
  · obtain ⟨q1, q2, q3, q4⟩ := ok1 p hp
    refine ⟨by omega, by omega, q2, ?_⟩
    rw [hv2 _ q3 q4]
    have := (pvW_abs (e := kDel δ) hd hn (k := p.2 - 30) (by omega)).trans_lt h2ℓ
    exact_mod_cast this
  -- the slots after the copies
  have cz : ∀ y, y ∉ prmCopiesW.map Prod.fst → σ3.sc y = σ2.sc y := Fc.2.1
  have keep : ∀ y, y < 30 → y ∉ prmCopiesW.map Prod.fst → σ3.sc y = σ1.sc y := fun y h1 h2 => by
    rw [cz y h2, k2 y h1]
  have cp : ∀ y k, (y, k) ∈ prmCopiesW → σ3.sc y = pvW d n (kDel δ) (k - 30) := fun y k h => by
    obtain ⟨-, -, q3, q4⟩ := ok1 _ h
    rw [hc _ h, hv2 _ q3 q4]
  have natK : ∀ j, j < 8 → σ3.nat j = σ1.nat j := fun j hj => by
    rw [Fc.1 j (fun h => h), F2.1 j (show ¬ (j = 8 ∨ j = 9) by omega)]
  refine ⟨⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    fun y h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the registers
  · rw [natK rP (by decide), natK rPF (by decide), natK rNb (by decide), natK rB (by decide)]
    exact hP1.regs
  -- the constants
  · rw [keep s2p (by decide) (by decide)]; exact hP1.consts.1
  · rw [keep s2pF (by decide) (by decide)]; exact hP1.consts.2.1
  · rw [keep s2g (by decide) (by decide)]; exact hP1.consts.2.2.1
  · rw [keep s2eh (by decide) (by decide)]; exact hP1.consts.2.2.2.1
  · rw [keep sNe (by decide) (by decide)]; exact hP1.consts.2.2.2.2.1
  · rw [keep sLam (by decide) (by decide)]; exact hP1.consts.2.2.2.2.2.1
  · rw [keep sRint (by decide) (by decide)]; exact hP1.consts.2.2.2.2.2.2
  -- PARAM-W's fields
  · rw [cp _ 95 (by decide), show 95 - 30 = 65 from rfl, pvW_65 hd hn, ← qn_parOW_eps hd hn]; rfl
  · rw [cp _ 96 (by decide), show 96 - 30 = 66 from rfl, pvW_66 hd hn, ← qn_parOW_lam hd hn]; rfl
  · rw [cp _ 97 (by decide), show 97 - 30 = 67 from rfl, pvW_67 hd hn, ← qn_parOW_eta hd hn]; rfl
  · rw [cp _ 99 (by decide), show 99 - 30 = 69 from rfl, pvW_69 hd hn, ← qn_parOW_rho hd hn]; rfl
  · rw [cp _ 100 (by decide), show 100 - 30 = 70 from rfl, pvW_70 hd hn, ← qn_parOW_kapc hd hn]; rfl
  · rw [cp _ 101 (by decide), show 101 - 30 = 71 from rfl, pvW_71 hd hn, ← qn_parOW_nu hd hn]; rfl
  · rw [keep sR (by decide) (by decide)]; exact hP1.par.2.2.2.2.2.2.1
  · rw [keep sSb (by decide) (by decide)]; exact hP1.par.2.2.2.2.2.2.2.1
  · rw [keep sW (by decide) (by decide)]; exact hP1.par.2.2.2.2.2.2.2.2.1
  · rw [cp _ 105 (by decide), show 105 - 30 = 75 from rfl, pvW_75 hd hn, ← qn_parOW_A0 hd hn]; rfl
  · rw [cp _ 106 (by decide), show 106 - 30 = 76 from rfl, pvW_76 hd hn, ← qn_parOW_B0 hd hn]; rfl
  -- the bounds of the slots `4, ..., 21`
  · by_cases hy : y ∈ prmCopiesW.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      obtain ⟨-, -, q3, q4⟩ := ok1 p hp
      exact ⟨pvW d n (kDel δ) (p.2 - 30), by rw [hc p hp, hv2 _ q3 q4],
        (pvW_abs hd hn (by omega)).trans (pow_le_pow_right₀ (by norm_num) hTs)⟩
    · obtain ⟨z, hz, hzb⟩ := hB1 y h1 h2
      exact ⟨z, by rw [keep y (by omega) hy, hz], hzb.trans (pow_le_pow_right₀ (by norm_num) hOs)⟩
  -- `2^p b0`, `2^p y0`
  · rw [cz 122 (by decide), hv2 122 (by norm_num) (by norm_num), show 122 - 30 = 92 from rfl, pvW_92 hd hn,
      ← qn_b0OW hd hn]; rfl
  · rw [cz 123 (by decide), hv2 123 (by norm_num) (by norm_num), show 123 - 30 = 93 from rfl, pvW_93 hd hn,
      ← qn_y0OW hd hn]; rfl
  · have h := pvW_abs (e := kDel δ) hd hn (k := 92) (by norm_num)
    rw [pvW_92 hd hn, ← qn_b0OW hd hn] at h
    exact h.trans (pow_le_pow_right₀ (by norm_num) hTs)
  · have h := pvW_abs (e := kDel δ) hd hn (k := 93) (by norm_num)
    rw [pvW_93 hd hn, ← qn_y0OW hd hn] at h
    exact h.trans (pow_le_pow_right₀ (by norm_num) hTs)
  -- no coin, the frame
  · rw [dc, d2, hD1]
  · have G2 : FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ1 σ2 :=
      (FrameA.ofP (Ar := fun _ _ => False) F2).mono (fun y h => by unfold SPar; omega)
        (fun j h => by simp only [rP]; omega) (fun _ _ h => h.elim)
    have G3 : FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ2 σ3 :=
      Fc.mono (fun y h => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
          have := ok4 p hp
          exact Or.inl this) (fun _ h => h.elim) (fun _ _ h => h.elim)
    exact (hF1.trans G2).trans G3

/-- **PARAM-W's contract** (`ParamWSpecS`, UW/ProgMachSetup.lean). -/
theorem progParamW : ∃ xpw C k nS nN nA, ParamWSpec xpw C k nS nN nA :=
  ⟨xparW, 8000000, 1, 172, 48, 0, paramSpecW⟩

end AdversarialBco.UW.PrmW
