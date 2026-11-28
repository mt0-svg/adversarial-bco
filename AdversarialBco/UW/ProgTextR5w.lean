/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgLinkStep
public import AdversarialBco.Bit.Transfer.XBLR8

@[expose] public section

/-!
# BL-OW's R5w on the machine: the weighted, clipped observation

R5w (UW/ProgPure.lean, `ywQ`): `Y'^w = rnd_p(φ' clip(Y', y0))`, `φ' = min(1, max(0, b0 + 1 - |ξ'|²))`,
`clip(Y', y0) = max(-y0, min(y0, Y'))`. On the machine, with `Q = 2^p`, `G = 2^{2 p_B}` (`ξ' = Γ/G`), `Γ·Γ`, and the
numerators `Ŷ = 2^p Y'`, `b̂0 = 2^p b0`, `ŷ0 = 2^p y0`:

  `cl = max(-ŷ0, min(ŷ0, Ŷ))`, `φ_N = min(Q G², max(0, (b̂0 + Q) G² - Q Γ·Γ))`, `Ŷ^w = ⌊(2 φ_N cl + Q G²)/(2 Q G²)⌋`,

so that `Ŷ^w/2^p = Y'^w` (`ywI_eq`). The straight line `slW` (region from slot `bW`) computes `cl`, `φ_N`, `Ŷ^w` and
`2 Ŷ^w` with the steps `ie` and `mx` only, from `Ŷ` in slot `45` (left there by BL-O's first line), `Γ·Γ` in slot
`40`, `Q`, `G`, `0` in BL's slots and `b̂0`, `ŷ0` in the slots `sB0w`, `sY0w`.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.UW.BLOW (ywQ)
open AdversarialBco.Bit.BLP (rnd)
open Matrix

variable {d : ℕ}

/-! ## The integers of R5w -/

/-- `cl = max(-ŷ0, min(ŷ0, Ŷ))` as the line computes it. -/
def clI (Y Yn : ℤ) : ℤ := (Y - max (Y - Yn) 0) + max ((0 - Yn) - (Y - max (Y - Yn) 0)) 0

/-- `φ_N = min(Q G², max(0, (b̂0 + Q) G² - Q Γ·Γ))` as the line computes it. -/
def phI (Bn Q G GG : ℤ) : ℤ :=
  max ((Bn + Q) * G * G - GG * Q) 0 - max (max ((Bn + Q) * G * G - GG * Q) 0 - Q * G * G) 0

/-- `Ŷ^w = ⌊(2 φ_N cl + Q G²)/(2 Q G²)⌋`. -/
def ywI (Y Bn Yn Q G GG : ℤ) : ℤ :=
  (phI Bn Q G GG * clI Y Yn + phI Bn Q G GG * clI Y Yn + Q * G * G) / (Q * G * G + Q * G * G)

theorem clI_eq (Y Yn : ℤ) : clI Y Yn = max (-Yn) (min Yn Y) := by
  unfold clI
  rcases le_total (Y - Yn) 0 with h | h
  · rw [max_eq_right h, sub_zero, min_eq_right (by linarith)]
    rcases le_total (0 - Yn - Y) 0 with h' | h'
    · rw [max_eq_right h', add_zero, max_eq_right (by linarith)]
    · rw [max_eq_left h', max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]
    rcases le_total (0 - Yn - (Y - (Y - Yn))) 0 with h' | h'
    · rw [max_eq_right h', add_zero, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h', max_eq_left (by linarith)]; ring

theorem phI_eq (Bn Q G GG : ℤ) :
    phI Bn Q G GG = min (Q * G * G) (max 0 ((Bn + Q) * G * G - GG * Q)) := by
  unfold phI
  rw [max_comm 0]
  set r := max ((Bn + Q) * G * G - GG * Q) 0
  rcases le_total (r - Q * G * G) 0 with h | h
  · rw [max_eq_right h, sub_zero, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

/-- **R5w on the integers**: `Ŷ^w/2^p = ywQ p b0 y0 ξ Y'` for `Y' = Ŷ/2^p`, `b0 = b̂0/2^p`, `y0 = ŷ0/2^p` and
`ξ = Γ/G`, `G > 0`. -/
theorem ywI_eq (p : ℕ) (Y Bn Yn G : ℤ) (Γ : Fin d → ℤ) (hG : 0 < G) :
    ((ywI Y Bn Yn (2 ^ p) G (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / 2 ^ p =
      ywQ p ((Bn : ℚ) / 2 ^ p) ((Yn : ℚ) / 2 ^ p) (fun i => (Γ i : ℚ) / G) ((Y : ℚ) / 2 ^ p) := by
  set Q : ℤ := 2 ^ p with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hQq : ((Q : ℤ) : ℚ) = 2 ^ p := by rw [hQ]; push_cast; rfl
  have hGq : (0 : ℚ) < G := by exact_mod_cast hG
  have hQG : 0 < Q * G * G := by positivity
  have hQGq : (0 : ℚ) < (Q : ℚ) * G * G := by exact_mod_cast hQG
  -- the weight
  have hφ : min (1 : ℚ) (max 0 ((Bn : ℚ) / 2 ^ p + 1 - (fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G)) =
      ((phI Bn Q G (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / ((Q * G * G : ℤ) : ℚ) := by
    rw [phI_eq]
    have e1 : (Bn : ℚ) / 2 ^ p + 1 - (fun i => (Γ i : ℚ) / G) ⬝ᵥ (fun i => (Γ i : ℚ) / G) =
        (((Bn + Q) * G * G - (Γ ⬝ᵥ Γ) * Q : ℤ) : ℚ) / ((Q * G * G : ℤ) : ℚ) := by
      have hd : (fun i => (Γ i : ℚ) / G) ⬝ᵥ (fun i => (Γ i : ℚ) / G) = ((Γ ⬝ᵥ Γ : ℤ) : ℚ) / ((G : ℚ) * G) := by
        simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [hd, ← hQq]
      push_cast
      field_simp
    rw [e1]
    have e2 : (1 : ℚ) = ((Q * G * G : ℤ) : ℚ) / ((Q * G * G : ℤ) : ℚ) := by
      rw [div_self]; exact_mod_cast hQG.ne'
    have e0 : (0 : ℚ) = ((0 : ℤ) : ℚ) / ((Q * G * G : ℤ) : ℚ) := by simp
    have hpos : (0 : ℚ) ≤ ((Q * G * G : ℤ) : ℚ) := by exact_mod_cast hQG.le
    rw [e2, e0, max_div_div_right hpos, min_div_div_right hpos]
    push_cast
    rfl
  -- the clip
  have hcl : max (-((Yn : ℚ) / 2 ^ p)) (min ((Yn : ℚ) / 2 ^ p) ((Y : ℚ) / 2 ^ p)) =
      ((clI Y Yn : ℤ) : ℚ) / 2 ^ p := by
    rw [clI_eq]
    have hpos : (0 : ℚ) ≤ 2 ^ p := by positivity
    rw [← neg_div, min_div_div_right hpos, max_div_div_right hpos]
    push_cast
    rfl
  unfold ywQ
  rw [hφ, hcl]
  have e3 : ((phI Bn Q G (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / ((Q * G * G : ℤ) : ℚ) * (((clI Y Yn : ℤ) : ℚ) / 2 ^ p) =
      ((phI Bn Q G (Γ ⬝ᵥ Γ) * clI Y Yn : ℤ) : ℚ) / ((Q * G * G * Q : ℤ) : ℚ) := by
    rw [← hQq]; push_cast; field_simp
  rw [e3, rnd_div p _ _ (by positivity)]
  congr 2
  unfold ywI
  rw [← hQ]
  have e4 : 2 * (phI Bn Q G (Γ ⬝ᵥ Γ) * clI Y Yn) * Q + Q * G * G * Q =
      Q * (phI Bn Q G (Γ ⬝ᵥ Γ) * clI Y Yn + phI Bn Q G (Γ ⬝ᵥ Γ) * clI Y Yn + Q * G * G) := by ring
  have e5 : 2 * (Q * G * G * Q) = Q * (Q * G * G + Q * G * G) := by ring
  rw [e4, e5, Int.mul_ediv_mul_of_pos _ _ hQ0]

/-! ## The straight line -/

/-- The slots of `b̂0`, `ŷ0` during R5w, and the region of the line. -/
abbrev sB0w : ℕ := 150
abbrev sY0w : ℕ := 151
abbrev bW : ℕ := 152

/-- The value of step `j` of the line (slot `bW + j`). -/
abbrev wv (j : ℕ) : IE := .sc (bW + j)

/-- **R5w as a straight line**: steps `0` to `5` the clip, `6` to `10` the weight, `11` `Ŷ^w`, `12` `2 Ŷ^w`. -/
def slW : List SStep :=
  let Yh : IE := .sc 45
  let Yn : IE := .sc sY0w
  let Bn : IE := .sc sB0w
  let Q : IE := .sc s2p
  let G : IE := .sc s2g
  let GG : IE := .sc sGG
  let Z : IE := .sc sZ
  let QGG : IE := .op .mul (.op .mul Q G) G
  [ .ie (.op .sub Yh Yn), .mx 0, .ie (.op .sub Yh (wv 1)), .ie (.op .sub (.op .sub Z Yn) (wv 2)), .mx 3,
    .ie (.op .add (wv 2) (wv 4)),
    .ie (.op .sub (.op .mul (.op .mul (.op .add Bn Q) G) G) (.op .mul GG Q)), .mx 6,
    .ie (.op .sub (wv 7) QGG), .mx 8, .ie (.op .sub (wv 7) (wv 9)),
    .ie (.ediv (.op .add (.op .add (.op .mul (wv 10) (wv 5)) (.op .mul (wv 10) (wv 5))) QGG) (.op .add QGG QGG)),
    .ie (.op .add (wv 11) (wv 11)) ]

/-- The input slots of the line. -/
def slWIns : List ℕ := [45, sY0w, sB0w, s2p, s2g, sGG, sZ]

/-- The pairs of the inputs: `Ŷ` below `2^(5G + 7)`, `Γ·Γ` below `2^(3G)`, the others below `2^G`. -/
def slWIn (y : ℕ) : ℕ × ℕ := if y = 45 then (5, 7) else if y = sGG then (3, 0) else (1, 0)

/-- The pairs of the steps. -/
def slWEt (j : ℕ) : ℕ × ℕ :=
  [(5, 8), (5, 8), (5, 9), (5, 10), (5, 10), (5, 11), (4, 2), (4, 2), (4, 3), (4, 3), (4, 4), (9, 17),
    (9, 18)].getD j (0, 0)

/-- The largest pair. -/
def slWT : ℕ × ℕ := (9, 18)

/-- The cells of the line: the region from `bW`, the scratch from `256`, `0, 1, 2, 4` in the slots `0, 41, 42, 43`,
the scratch registers `19`, `20`, `1` in the register `rOne`. -/
def slWC : SLC := ⟨bW, 256, sZ, 41, 42, 43, 19, 20, rOne⟩

theorem slW_length : slW.length = 13 := rfl

theorem slW_chk : SL.chk bW slWIns slWIn slWEt slWT 112 slW = true := by decide

/-- The inputs of the line. -/
def slWI (Y Yn Bn Q G GG : ℤ) : ℕ → ℤ := fun y =>
  if y = 45 then Y else if y = sY0w then Yn else if y = sB0w then Bn else if y = s2p then Q else if y = s2g then G
  else if y = sGG then GG else 0

section Values

variable (Y Yn Bn Q G GG : ℤ)

/-- The value of step `k`. -/
abbrev vW (k : ℕ) : ℤ := SL.val slW bW (slWI Y Yn Bn Q G GG) k

theorem vW_c (k : ℕ) : vW Y Yn Bn Q G GG k =
    (slW.getD k (.cst 0)).sem bW (slWI Y Yn Bn Q G GG)
      (fun j => if j < k then vW Y Yn Bn Q G GG j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the line unfolded. -/
macro "vws" : tactic => `(tactic| (rw [vW_c]; simp only [slW, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, wv, slWI, sY0w, sB0w, bW, s2p, s2g, sGG, sZ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceEqDiff, ↓reduceIte]))

theorem vW_0 : vW Y Yn Bn Q G GG 0 = Y - Yn := by vws
theorem vW_1 : vW Y Yn Bn Q G GG 1 = max (Y - Yn) 0 := by vws; rw [vW_0]
theorem vW_2 : vW Y Yn Bn Q G GG 2 = Y - max (Y - Yn) 0 := by vws; rw [vW_1]
theorem vW_3 : vW Y Yn Bn Q G GG 3 = (0 - Yn) - (Y - max (Y - Yn) 0) := by vws; rw [vW_2]
theorem vW_4 : vW Y Yn Bn Q G GG 4 = max ((0 - Yn) - (Y - max (Y - Yn) 0)) 0 := by vws; rw [vW_3]
theorem vW_5 : vW Y Yn Bn Q G GG 5 = clI Y Yn := by vws; rw [vW_2, vW_4]; rfl
theorem vW_6 : vW Y Yn Bn Q G GG 6 = (Bn + Q) * G * G - GG * Q := by vws
theorem vW_7 : vW Y Yn Bn Q G GG 7 = max ((Bn + Q) * G * G - GG * Q) 0 := by vws; rw [vW_6]
theorem vW_8 : vW Y Yn Bn Q G GG 8 = max ((Bn + Q) * G * G - GG * Q) 0 - Q * G * G := by vws; rw [vW_7]
theorem vW_9 : vW Y Yn Bn Q G GG 9 = max (max ((Bn + Q) * G * G - GG * Q) 0 - Q * G * G) 0 := by vws; rw [vW_8]
theorem vW_10 : vW Y Yn Bn Q G GG 10 = phI Bn Q G GG := by vws; rw [vW_7, vW_9]; rfl
theorem vW_11 : vW Y Yn Bn Q G GG 11 = ywI Y Bn Yn Q G GG := by vws; rw [vW_10, vW_5]; rfl
theorem vW_12 : vW Y Yn Bn Q G GG 12 = 2 * ywI Y Bn Yn Q G GG := by vws; rw [vW_11]; ring

end Values

/-! ## BL-O's first line at the re-encoded reading -/

/-- With the scale `pN/pD = 1/1`, the dither `0` and the reading `2y`, BL-O's R5 integer `yHat` is `y`. -/
theorem yHat_reenc (Q F G eN y : ℤ) (hQ : 0 < Q) (hG : 0 < G) (he : 0 < eN) : yHat Q F G 1 1 (2 * y) 0 eN = y := by
  unfold yHat yU yV
  have hV : 0 < 1 * Q * (G + G + (G + G)) * eN := by positivity
  have e1 : (1 * (2 * y * (G + G) + 0 * Q) * eN + (1 - 1 + (1 - 1)) * F * Q * (G + G + (G + G))) * Q +
      (1 * (2 * y * (G + G) + 0 * Q) * eN + (1 - 1 + (1 - 1)) * F * Q * (G + G + (G + G))) * Q +
      1 * Q * (G + G + (G + G)) * eN = y * (1 * Q * (G + G + (G + G)) * eN + 1 * Q * (G + G + (G + G)) * eN) +
        1 * Q * (G + G + (G + G)) * eN := by ring
  rw [e1]
  generalize 1 * Q * (G + G + (G + G)) * eN = W at hV ⊢
  rw [add_comm (y * _) W, Int.add_mul_ediv_right _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega),
    zero_add]

/-! ## The run of R5w -/

/-- R5w after BL-O's first line: `b̂0` from `aMuS[d]` into `sB0w`, `d·d` into the register `rD1`, `ŷ0` from
`aAS[d·d]` into `sY0w`, the line `slW`, then the re-encoded reading: `sObs := 2 Ŷ^w`, `sPtN := 1`, `sPtD := 1`,
`sZeta := 0`. -/
def xR5w (L : Layout) : XCmd :=
  .seq (toX (VL.aget L sB0w aMuS rD))
  (.seq (xnmul rD1 rD rD)
  (.seq (toX (VL.aget L sY0w aAS rD1))
  (.seq (SL.code L slWC slW)
  (.seq (toX (VL.sop2 L .add sObs (bW + 12) sZ))
  (.seq (toX (VL.sconst L sPtN 1)) (.seq (toX (VL.sconst L sPtD 1)) (toX (VL.sconst L sZeta 0))))))))

/-- The units of `xR5w`. -/
def r5wUnits (U : ℕ) : ℕ := 2 + (1 + (2 + (ev U (SL.unitsP slWEt slW) + (1 + (1 + (1 + 1))))))

/-- The slots that `xR5w` changes. -/
def S5w (y : ℕ) : Prop := y = sZeta ∨ y = sPtN ∨ y = sPtD ∨ y = sObs ∨ (sB0w ≤ y ∧ y < bW + 13) ∨ tR ≤ y

/-- The registers that `xR5w` changes. -/
def N5w (j : ℕ) : Prop := j = rD1 ∨ j = 19 ∨ j = 20

theorem slWC_ok {L : Layout} (hlay : BLLay L) : slWC.OK L 112 := by
  obtain ⟨hS, hN, -⟩ := hlay
  simp only [oE, rEE] at hS hN
  exact ⟨by simp only [slWC, bW]; omega, by simp only [slWC, bW]; omega, by simp only [slWC, bW]; omega,
    by simp only [slWC, bW, rOne]; omega, by simp only [slWC, bW]; omega, by simp only [slWC, bW, rOne]; omega,
    by simp only [slWC, bW, rOne]; omega, by simp only [slWC, bW, sZ]; omega, by simp only [slWC, bW]; omega,
    by simp only [slWC, bW]; omega, by simp only [slWC, bW]; omega, by simp [slWC, sZ], by simp only [slWC, bW]; omega⟩

theorem absR_lt {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |(z : ℝ)| < 2 ^ ℓ := by
  have h2 : (2 : ℤ) ^ a < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) ha
  rw [← Int.cast_abs]; exact_mod_cast h.trans_lt h2

theorem absZ_lt {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |z| < 2 ^ ℓ :=
  h.trans_lt (pow_lt_pow_right₀ (by norm_num) ha)

set_option maxHeartbeats 1600000 in
/-- **R5w on the machine**: from `Ŷ` in slot `45` (BL-O's first line), `Γ·Γ` in `sGG`, `2^p`, `2^{2 p_B}` in their
slots, the constants `1, 2, 4` in the slots `41, 42, 43`, and `b̂0`, `ŷ0` in `aMuS[d]`, `aAS[d·d]`: the reading slot
holds `2 Ŷ^w`, the scale `pt_N/pt_D` is `1/1` and the dither `0`; only the slots of `S5w` and the registers of `N5w`
change, no array, no coin. -/
theorem XV.r5w {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Y Bn Yn Q G GG : ℤ} {U : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2) (c4 : σ.sc 43 = 4)
    (eY : σ.sc 45 = Y) (eQ : σ.sc s2p = Q) (eG : σ.sc s2g = G) (eGG : σ.sc sGG = GG)
    (eB : σ.arr aMuS d = Bn) (eYn : σ.arr aAS (d * d) = Yn)
    (bY : |Y| ≤ 2 ^ (5 * U + 7)) (bB : |Bn| ≤ 2 ^ U) (bYn : |Yn| ≤ 2 ^ U) (bQ : |Q| ≤ 2 ^ U) (bG : |G| ≤ 2 ^ U)
    (bGG : |GG| ≤ 2 ^ (3 * U)) (hd : 1 ≤ d) (hda : d * d + d < 2 ^ ℓa) (hT : 9 * U + 18 < ℓ)
    (hTa : 9 * U + 18 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR5w L) σ (r5wUnits U) (fun σ' =>
      σ'.sc sObs = ((2 * ywI Y Bn Yn Q G GG : ℤ) : ℝ) ∧ σ'.sc sPtN = 1 ∧ σ'.sc sPtD = 1 ∧ σ'.sc sZeta = 0 ∧
      σ'.draws = σ.draws ∧ FrameA S5w N5w (fun _ _ => False) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d hd
  -- `b̂0`
  refine XV.seq (XV.aget hL (x := sB0w) (a := aMuS) (i := rD) (by simp only [sB0w]; omega)
    (by simp only [aMuS]; omega) (by simp only [rD]; omega)
    (by rw [hD]; unfold asz; omega) (by rw [hD, eB]; exact absR_lt bB (by omega))) fun σ1 e1 => ?_
  subst e1
  -- `d·d`
  have n1 : (σ.setSc sB0w (σ.arr aMuS (σ.nat rD))).nat rD = d := by simp only [Env.setSc_nat]; exact hD
  refine XV.seq (XV.nmul hL (i := rD1) (a := rD) (b := rD) (by simp only [rD1]; omega) (by simp only [rD]; omega)
    (by simp only [rD]; omega) (by rw [n1]; omega) (by rw [n1]; omega) (by rw [n1]; omega)) fun σ2 e2 => ?_
  subst e2
  -- `ŷ0`
  set σ2 := (σ.setSc sB0w (σ.arr aMuS (σ.nat rD))).setNat rD1
    ((σ.setSc sB0w (σ.arr aMuS (σ.nat rD))).nat rD * (σ.setSc sB0w (σ.arr aMuS (σ.nat rD))).nat rD) with hσ2
  have n2 : σ2.nat rD1 = d * d := by rw [hσ2, nat_setNat_eq, n1]
  have a2 : σ2.arr = σ.arr := by simp only [hσ2, Env.setNat_arr, Env.setSc_arr]
  refine XV.seq (XV.aget hL (x := sY0w) (a := aAS) (i := rD1) (by simp only [sY0w]; omega)
    (by simp only [aAS]; omega) (by simp only [rD1]; omega)
    (by rw [n2]; unfold asz; omega) (by rw [n2, a2, eYn]; exact absR_lt bYn (by omega))) fun σ3 e3 => ?_
  subst e3
  set σ3 := σ2.setSc sY0w (σ2.arr aAS (σ2.nat rD1)) with hσ3
  have s3 : ∀ y, y ≠ sB0w → y ≠ sY0w → σ3.sc y = σ.sc y := fun y h h' => by
    rw [hσ3, sc_setSc_ne _ h', hσ2, Env.setNat_sc, sc_setSc_ne _ h]
  have n3 : ∀ j, j ≠ rD1 → σ3.nat j = σ.nat j := fun j h => by
    rw [hσ3, Env.setSc_nat, hσ2, nat_setNat_ne _ h, Env.setSc_nat]
  -- the line
  have hin : ∀ y ∈ slWIns, σ3.sc y = slWI Y Yn Bn Q G GG y := by
    intro y hy
    simp only [slWIns, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [s3 _ (by decide) (by decide), eY]; simp [slWI]
    · rw [hσ3, sc_setSc_eq, n2, a2, eYn]; simp [slWI, sY0w]
    · rw [hσ3, sc_setSc_ne _ (by decide), hσ2, Env.setNat_sc, sc_setSc_eq, hD, eB]
      simp [slWI, sY0w, sB0w]
    · rw [s3 _ (by decide) (by decide), eQ]; simp [slWI, sY0w, sB0w, s2p]
    · rw [s3 _ (by decide) (by decide), eG]; simp [slWI, sY0w, sB0w, s2p, s2g]
    · rw [s3 _ (by decide) (by decide), eGG]; simp [slWI, sY0w, sB0w, s2p, s2g, sGG]
    · rw [s3 _ (by decide) (by decide), hz]; simp [slWI, sY0w, sB0w, s2p, s2g, sGG, sZ]
  have hinB : ∀ y ∈ slWIns, |slWI Y Yn Bn Q G GG y| ≤ 2 ^ ev U (slWIn y) := by
    intro y hy
    simp only [slWIns, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [slWI, slWIn, ev, sY0w, sB0w, s2p, s2g, sGG, sZ, bY, bB, bYn, bQ, bG, bGG]
  have hsem : ∀ k < slW.length, (slW.getD k (.cst 0)).Sem (SL.val slW slWC.b (slWI Y Yn Bn Q G GG)) U := by
    intro k hk; simp only [slW_length] at hk; interval_cases k <;> trivial
  have hbnd := SL.val_bound slW slWC.b (slWI Y Yn Bn Q G GG) slWIns slWIn slWEt slWT 112 U
    (SL.chk_get slW_chk).2 hsem hinB
  refine XV.seq (XV.sl hL (slWC_ok hlay) slW_chk hsem (by simp [slWC, slW_length, bW])
    (by simp only [ev, slWT]; omega) (by simp only [ev, slWT]; omega) hinB (σ := σ3) hin
    (by simp only [slWC]; rw [s3 _ (by decide) (by decide), hz])
    (by simp only [slWC]; rw [s3 _ (by decide) (by decide), c1])
    (by simp only [slWC]; rw [s3 _ (by decide) (by decide), c2])
    (by simp only [slWC]; rw [s3 _ (by decide) (by decide), c4])
    (by simp only [slWC]; rw [n3 _ (by decide), h1])) fun σ4 ⟨v4, d4, F4⟩ => ?_
  have e12 : σ4.sc (bW + 12) = ((2 * ywI Y Bn Yn Q G GG : ℤ) : ℝ) := by
    have := v4 12 (by simp [slW_length])
    rw [show slWC.b = bW from rfl] at this
    rw [this, show SL.val slW bW (slWI Y Yn Bn Q G GG) 12 = vW Y Yn Bn Q G GG 12 from rfl, vW_12]
  have b12 : |2 * ywI Y Bn Yn Q G GG| ≤ 2 ^ (9 * U + 18) := by
    have := hbnd 12 (by simp [slW_length])
    rw [show SL.val slW slWC.b (slWI Y Yn Bn Q G GG) 12 = vW Y Yn Bn Q G GG 12 from rfl, vW_12] at this
    simpa [ev, slWEt] using this
  have z4 : σ4.sc sZ = ((0 : ℤ) : ℝ) := by
    rw [F4.2.1 _ (by simp only [slWC, slW_length, sZ, bW]; omega), s3 _ (by decide) (by decide), hz]; simp
  -- the re-encoded reading
  have c1R : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have c0R : |((0 : ℚ) : ℝ)| < 2 ^ ℓ := by rw [Rat.cast_zero, abs_zero]; positivity
  refine XV.seq (XV.addI hL (x := sObs) (a := bW + 12) (b := sZ) (by simp only [sObs]; omega)
    (by simp only [bW]; omega) (by simp only [sZ]; omega) e12 z4 (absZ_lt b12 (by omega)) (by simp)
    (by rw [add_zero]; exact absZ_lt b12 (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.sconst hL (x := sPtN) (by simp only [sPtN]; omega) 1 rfl c1R) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.sconst hL (x := sPtD) (by simp only [sPtD]; omega) 1 rfl c1R) fun σ7 e7 => ?_
  subst e7
  refine XV.mono (XV.sconst hL (x := sZeta) (by simp only [sZeta]; omega) 0 rfl c0R) le_rfl
    fun σ8 e8 => ?_
  subst e8
  refine ⟨by simp [sObs, sPtN, sPtD, sZeta], by simp [sPtN, sPtD, sZeta], by simp [sPtD, sZeta], by simp, ?_, ?_⟩
  · simp only [Env.setSc_draws, d4, hσ3, hσ2, Env.setNat_draws]
  · have F3 : FrameA S5w N5w (fun _ _ => False) σ σ3 :=
      (((FrameA.refl _ _ _ σ).setSc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, by decide⟩)))))
        _).setNat (Or.inl rfl) _).setSc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩))))) _
    have F4' : FrameA S5w N5w (fun _ _ => False) σ3 σ4 :=
      (FrameA.ofP F4).mono (fun y h => by
        simp only [slWC, slW_length, bW] at h; simp only [S5w, sZeta, sPtN, sPtD, sObs, sB0w, bW, tR]; omega)
        (fun j h => by simp only [slWC] at h; simp only [N5w, rD1]; omega) (fun _ _ h => h)
    exact ((((F3.trans F4').setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc
      (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inl rfl))) _).setSc (Or.inl rfl) _

end AdversarialBco.UW.ProgW
