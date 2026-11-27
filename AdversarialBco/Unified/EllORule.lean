/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOBlock

@[expose] public section

/-!
# UNI-ELL (c): statement (c), the rule of ELL-O on the oracle machine

The magnitudes of the block (`bigO`) are at most `160000 W^2` and its units (`ellOU`) at most `10^10 (W + Kt)^8`,
`W = d + ellOSz I + κ + 1`, from ELL-R's size bounds (`ellLam_le`, `ellJ_le`). With `XVO.ellO` this gives `ellORule`:
`xellO` with the SEP layout `sepLayO B` and the gauge layout `gaugeLayO B` meets `EllOBlockOK` with `C = 10^10`,
`k₀ = 8` and the block sizes `215`, `112`, `14`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

/-! ## The sizes -/

/-- ELL-R's size bounds, in the size of the call. -/
theorem ellO_sizes (I : EllOI d) (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e) :
    I.base.lam ≤ 7 * ellOSz I + d + 3 ∧ I.base.p ≤ 12 * ellOSz I + 5 * d + 12 ∧
      I.base.q ≤ 34 * ellOSz I + 6 * d + 24 ∧ Nat.clog 2 I.base.Rb ≤ ellOSz I ∧
      I.base.j ≤ 6 * ellOSz I + d + 3 ∧ I.erK ≤ ellOSz I ∧ Nat.clog 2 d ≤ d ∧ ellSz I.base ≤ ellOSz I := by
  have hs := ellSz_base_le I
  have hr' : 0 < I.base.r := hr
  have he' : 0 < I.base.e := he
  obtain ⟨b1, b2, b3, b4⟩ := ellLam_le I.base hd hr' he'
  have b5 := ellJ_le I.base hd hr' he'
  have b6 : I.erK ≤ ellOSz I := by unfold ellOSz; omega
  have b7 : Nat.clog 2 d ≤ d := by
    rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]; exact (Nat.lt_two_pow_self (n := d)).le
  exact ⟨by omega, by omega, by omega, by omega, by omega, b6, b7, hs⟩

/-- The exponents of ELL-O, linear or quadratic in any `Y ≥ d + ellOSz I + 1`. -/
theorem ellO_expos (I : EllOI d) {Y : ℕ} (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e)
    (hY : d + ellOSz I + 1 ≤ Y) :
    I.eL + I.eτ + 4 ≤ 26 * Y ∧ I.e1 ≤ 19 * Y ∧ I.eτ ≤ 21 * Y ∧ I.eH ≤ 4 * Y ∧
      3 * d * (I.eL + I.eτ + 4) ≤ 78 * Y ^ 2 ∧ I.eη ≤ 129 * Y ^ 2 ∧ I.jg ≤ 134 * Y ^ 2 ∧ I.eu ≤ 130 * Y ^ 2 ∧
      I.eK ≤ 135 * Y ^ 2 ∧ I.sepEx I.base.p ≤ 126 * Y ^ 2 ∧ I.sepEx (I.base.lam + 1) ≤ 109 * Y ^ 2 := by
  obtain ⟨b1, b2, -, b4, b5, b6, b7, -⟩ := ellO_sizes I hd hr he
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hEp⟩ := expo_eqs I I.base.p
  have hEl := (expo_eqs I (I.base.lam + 1)).2.2.2.2.2.2.2.2.2
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  have hL : I.eL + I.eτ + 4 ≤ 26 * Y := by omega
  have hP : 3 * d * (I.eL + I.eτ + 4) ≤ 78 * Y ^ 2 :=
    calc 3 * d * (I.eL + I.eτ + 4) ≤ (3 * Y) * (26 * Y) := Nat.mul_le_mul (by omega) hL
      _ = 78 * Y ^ 2 := by ring
  exact ⟨hL, by omega, by omega, by omega, hP, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The magnitudes -/

/-- The magnitudes of the block, quadratic in `W = d + ellOSz I + κ + 1`. -/
theorem bigO_le (I : EllOI d) (κ : ℕ) (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e) :
    bigO I κ ≤ 160000 * (d + ellOSz I + κ + 1) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, hs⟩ := ellO_sizes I hd hr he
  obtain ⟨hL, h1, hτ, hH, hP, hη, hjg, heu, hK, hSp, hSl⟩ :=
    ellO_expos I (Y := d + ellOSz I + κ + 1) hd hr he (by omega)
  set W := d + ellOSz I + κ + 1 with hW
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
  unfold bigO ellOE ellOF cstX ellE ellF
  omega

/-! ## The units -/

/-- The units of one test step, quintic in `Y ≥ d + ellOSz I + Kt + 1`. -/
theorem stepU_le (I : EllOI d) {Kt Y : ℕ} (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e)
    (hY : d + ellOSz I + Kt + 1 ≤ Y) : stepU I Kt ≤ 22100000 * Y ^ 5 := by
  obtain ⟨hL, -, -, -, -, -, hjg, -, -, -, -⟩ := ellO_expos I (Y := Y) hd hr he (by omega)
  have hY1 : 1 ≤ Y := by omega
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  have hY3 : Y ^ 2 ≤ Y ^ 3 := pow_le_pow_right₀ hY1 (by norm_num)
  have hY5 : Y ^ 3 ≤ Y ^ 5 := pow_le_pow_right₀ hY1 (by norm_num)
  have hdd : d * (d * 10 + 9) ≤ 19 * Y ^ 2 :=
    calc d * (d * 10 + 9) ≤ Y * (19 * Y) := Nat.mul_le_mul (by omega) (by omega)
      _ = 19 * Y ^ 2 := by ring
  have hKev : 2 * (I.jg + 1) * (Kt + 32 * d + 64) ≤ 26190 * Y ^ 3 :=
    calc 2 * (I.jg + 1) * (Kt + 32 * d + 64) ≤ (270 * Y ^ 2) * (97 * Y) := Nat.mul_le_mul (by omega) (by omega)
      _ = 26190 * Y ^ 3 := by ring
  have hKs : 16 * (d + 1) * (I.eL + I.eτ + 3 + 1) * (2 * (I.jg + 1) * (Kt + 32 * d + 64) + 64 * d + 256) ≤
      22056320 * Y ^ 5 :=
    calc 16 * (d + 1) * (I.eL + I.eτ + 3 + 1) * (2 * (I.jg + 1) * (Kt + 32 * d + 64) + 64 * d + 256)
        ≤ (32 * Y) * (26 * Y) * (26510 * Y ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = 22056320 * Y ^ 5 := by ring
  unfold stepU testOU tORest testK tE1 tKR tE2 tKQ tE3 tKV tKK tKE tKA sepK gaugeK
  omega

/-- The units of the block, of degree `8` in `Y = d + ellOSz I + κ + Kt + 1`. -/
theorem ellOU_le (I : EllOI d) (κ Kt : ℕ) (hd : 1 ≤ d) :
    ellOU I κ Kt ≤ 10000000000 * (d + ellOSz I + κ + Kt + 1) ^ 8 := by
  set Y := d + ellOSz I + κ + Kt + 1 with hYd
  have hY1 : 1 ≤ Y := by omega
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  have hY3 : Y ^ 2 ≤ Y ^ 3 := pow_le_pow_right₀ hY1 (by norm_num)
  have hY4 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ hY1 (by norm_num)
  have hY5 : Y ^ 4 ≤ Y ^ 5 := pow_le_pow_right₀ hY1 (by norm_num)
  have hY6 : Y ^ 5 ≤ Y ^ 6 := pow_le_pow_right₀ hY1 (by norm_num)
  have hY8 : Y ^ 6 ≤ Y ^ 8 := pow_le_pow_right₀ hY1 (by norm_num)
  unfold ellOU startOU ellOMUc
  split_ifs with hc
  swap
  · omega
  obtain ⟨hr, he⟩ := hc
  obtain ⟨b1, b2, b3, -, -, -, -, hs⟩ := ellO_sizes I hd hr he
  obtain ⟨-, -, hτ, -, -, -, hjg, -, hK, hSp, hSl⟩ := ellO_expos I (Y := Y) hd hr he (by omega)
  have hst := stepU_le I (Kt := Kt) (Y := Y) hd hr he (by omega)
  have hdd : d * d ≤ Y ^ 2 :=
    calc d * d ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
      _ = Y ^ 2 := by ring
  have hOE : ellOE I I.base.p + 1 ≤ 442 * Y ^ 2 := by unfold ellOE ellE; omega
  have hE2 : (ellOE I I.base.p + 1) ^ 2 ≤ 195364 * Y ^ 4 :=
    calc (ellOE I I.base.p + 1) ^ 2 ≤ (442 * Y ^ 2) ^ 2 := Nat.pow_le_pow_left hOE 2
      _ = 195364 * Y ^ 4 := by ring
  have hkb : kbT d (ellOE I I.base.p) (stepU I Kt) + 2 ≤ 61200000 * Y ^ 5 := by
    unfold kbT tKE; omega
  have eN : I.base.N = 2 * d * (d + 1) * I.base.lam + 1 := rfl
  have hN0 : 2 * d * (d + 1) * I.base.lam ≤ 44 * Y ^ 3 :=
    calc 2 * d * (d + 1) * I.base.lam ≤ (2 * Y) * (2 * Y) * (11 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = 44 * Y ^ 3 := by ring
  have hNK : I.base.N * (kbT d (ellOE I I.base.p) (stepU I Kt) + 2) ≤ 2754000000 * Y ^ 8 :=
    calc I.base.N * (kbT d (ellOE I I.base.p) (stepU I Kt) + 2) ≤ (45 * Y ^ 3) * (61200000 * Y ^ 5) :=
        Nat.mul_le_mul (by rw [eN]; omega) hkb
      _ = 2754000000 * Y ^ 8 := by ring
  have hLK : (I.base.lam + 1) * (bkbT d (stepU I Kt) + 2) ≤ 265202400 * Y ^ 6 :=
    calc (I.base.lam + 1) * (bkbT d (stepU I Kt) + 2) ≤ (12 * Y) * (22100200 * Y ^ 5) :=
        Nat.mul_le_mul (by omega) (by unfold bkbT tKE; omega)
      _ = 265202400 * Y ^ 6 := by ring
  unfold ellOMU ellJU ellBrOU bisBrOU ellPreU constOU cstX
  omega

/-! ## Statement (c) -/

/-- **Statement (c), the rule of ELL-O on the oracle machine**: `xellO` with the layouts `sepLayO B` and
`gaugeLayO B` meets `EllOBlockOK` with `C = 10^10`, `k₀ = 8` and the block sizes `215`, `112`, `14`. -/
theorem ellORule : EllORule := by
  refine ⟨xellO, sepLayO, gaugeLayO, 10000000000, 8, 215, 112, 14, ?_⟩
  intro d L XO ℓa ℓ B sepc gc hS hG I κ TB TDat T Kt bt St Nt Art σ hL hB hd hDc hTB hav hst hTD hin hbt hℓ hℓa
  set W := d + ellOSz I + κ + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have hW2 : W ^ 2 ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW3 : W ^ 3 ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW1' : W ≤ W ^ 8 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have h3 : (d + ellOSz I + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hB' : ∀ hr : 0 < I.r, ∀ he : 0 < I.e, bigO I κ ≤ 10000000000 * W ^ 8 := fun hr he => by
    have := bigO_le I κ hd hr he
    rw [← hW] at this
    omega
  refine XVO.mono (XVO.ellO hL hd hB hDc hS hG hTB hav hst hTD hin (fun hr he => (hB' hr he).trans hbt) hℓ
    (fun hr he => (hB' hr he).trans_lt hℓa) (by omega) (by omega)) (ellOU_le I κ Kt hd) (fun _ h => h)

end AdversarialBco.Uni.EllO
