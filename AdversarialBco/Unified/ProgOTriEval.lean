/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriTest
public import AdversarialBco.Unified.ProgOSepUS

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: SEP's evaluator in a stage

SEP's evaluator of the core step: the gauge block `xgaugeU` (Unified/ProgOSepU.lean) on the stage test
`xtstT` about the centre `0 = (1; 0)` of `aKg`, at the grid point `(2^E; X)` of SEP's array `aev = aT + 22` (read in
place), `H = 2^{stEH}/1`, `stJ` steps; its counter goes straight into SEP's value slot `oT + 16`.
`evalT_OK : EvalOK .. (stEv orc a r₀ R₀ j (posZ P))` on SEP's domain around `Y₀`, with the data `DatS` (the constants
`TriKXAt`, `d`, `1`, `0` and the stage `P`). Also the bound of SEP's vector (`sepE_G_le`, `gvO_le`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The data -/

/-- The data the evaluator and SEP read: the constants of the core step, `d`, `1`, `0` and the stage `j` at `P`. -/
structure DatS (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (j : ℕ) (P : StZ d)
    (σ : Env d) : Prop where
  kx : TriKXAt d n δ r0 R0 a Da Na rn rd σ
  hd : σ.nat rD = d
  h1 : σ.nat rT = 1
  hz : σ.sc (oT + 1) = 0
  st : StAtO σ j P

theorem DatS.frame {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ}
    {P : StZ d} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : DatS d n δ r0 R0 a Da Na rn rd j P σ)
    (hF : FrameA S N Ar σ σ') (hS : ∀ y, S y → oT + 16 ≤ y ∧ y ≠ oT + 36) (hN : ∀ j, N j → rT + 33 ≤ j)
    (hA : ∀ b k, Ar b k → aT + 18 ≤ b) : DatS d n δ r0 R0 a Da Na rn rd j P σ' := by
  obtain ⟨st0, st1, st2, st3⟩ := h.st
  have nS : ∀ y, y < oT + 16 → ¬ S y := fun y hy h' => by have := hS y h'; omega
  have nN : ∀ j, j < rT + 33 → ¬ N j := fun j hj h' => by have := hN j h'; omega
  have nA : ∀ b k, b < aT + 18 → ¬ Ar b k := fun b k hb h' => by have := hA b k h'; omega
  refine ⟨h.kx.frame hF (fun y h1 h2 => nS y (by simp only [oT]; omega))
    ⟨nN _ (by simp only [rNJ]; omega), nN _ (by simp only [rNj]; omega), nN _ (by simp only [rNk]; omega)⟩
    (fun k => ⟨nA _ _ (by simp only [aKa]; omega), nA _ _ (by simp only [aKg]; omega)⟩), ?_, ?_, ?_, ?_⟩
  · rw [hF.1 _ (nN _ (by simp only [rD]; omega)), h.hd]
  · rw [hF.1 _ (nN _ (by omega)), h.h1]
  · rw [hF.2.1 _ (nS _ (by omega)), h.hz]
  · refine ⟨fun l => ?_, fun i l => ?_, ?_, ?_⟩
    · rw [hF.2.2.1 _ _ (nA _ _ (by omega)), st0]
    · rw [hF.2.2.1 _ _ (nA _ _ (by omega)), st1]
    · rw [hF.2.1 _ (nS _ (by omega)), st2]
    · rw [hF.2.1 _ fun h' => (hS _ h').2 rfl, st3]

theorem DatS.tdat {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ}
    {P : StZ d} {σ : Env d} (h : DatS d n δ r0 R0 a Da Na rn rd j P σ) :
    TDatT P j Da Na rn rd (stK d r0 R0) σ :=
  ⟨h.hd, h.h1, h.hz, h.st, ⟨⟨h.kx.ka0, h.kx.ka, h.kx.r0n, h.kx.r0d, h.kx.nk, by show σ.sc sC2k = _; rw [h.kx.c2k]; norm_num⟩,
    h.hd⟩⟩

theorem TestOK.dat {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {TB : XCmdO} {D1 D2 : Env d → Prop} {ap nt bt : ℕ}
    {T : (Fin d → ℚ) → Bool} {K : ℕ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (h : TestOK L XO ℓa ℓ TB D1 ap nt bt T K S N Ar) (h12 : ∀ σ, D2 σ → D1 σ) :
    TestOK L XO ℓa ℓ TB D2 ap nt bt T K S N Ar := fun σ D Nv hd => h σ D Nv (h12 σ hd)

/-! ## The layouts -/

/-- The gauge of the stage: the point in SEP's `aev = aT + 22`, the centre `(1; 0)` in `aKg`, `H` in `sHn`, `sHd`,
`stJ` in `rNj`, `2^{stJ}` in `sC2j`, the test point in `aT + 24`, the answer in `rT + 34`, the counter into SEP's
value slot `oT + 16`, scratch slots from `oT + 260`, registers from `rT + 56`. -/
def gLT : GaugeLay := ⟨aT + 22, aKg, sHn, sHd, rNj, sC2j, aT + 24, rT + 34, oT + 16, oT + 260, rT + 56⟩

/-- SEP in the stage: `Y₀` in `aT + 18`, `Y`, `G`, `Δ` in `aT + 19`, `aT + 20`, `aT + 21`, the evaluator's point in
`aT + 22`, its value in `oT + 16`, the constants of `TriKXAt`, the flag in `rT + 33`, scratch slots from `oT + 200`,
registers from `rT + 40`. -/
def sLT : SepLay :=
  ⟨aT + 18, aT + 19, aT + 20, aT + 21, aT + 22, oT + 16, sCE, sCL1, sCSh, sCA, sCB, rNJ, rT + 33, oT + 200, rT + 40⟩

theorem gLT_OK {L : Layout} (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) :
    GaugeLay.OKU L gLT := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩,
    ?_, ?_⟩ <;> simp only [gLT, aKg, sHn, sHd, rNj, sC2j, oT, rT, aT] at * <;> omega

theorem sLT_OK {L : Layout} (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) :
    SepLay.OK L sLT := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩ <;> simp only [sLT, sCE, sCL1, sCSh, sCA, sCB, rNJ, oT, rT, aT] at * <;> first | omega | decide

theorem gLT_disj : GaugeDisjU gLT tsS tsN tsA := by
  refine ⟨⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩, fun j h => ?_⟩ <;>
    simp only [gLT, tsS, tsN, tsA, aKg, sHn, sHd, rNj, sC2j, oT, rT, aT] at * <;> omega

/-- The slots the evaluator writes. -/
abbrev evSt (y : ℕ) : Prop := gaugeS gLT y ∨ tsS y

/-- The registers the evaluator writes. -/
abbrev evNt (j : ℕ) : Prop := gaugeN gLT j ∨ tsN j

/-- The arrays the evaluator writes. -/
abbrev evAt (b k : ℕ) : Prop := gaugeAr gLT b k ∨ tsA b k

theorem sLT_disj : SepDisj sLT evSt evNt evAt := by
  refine ⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩ <;>
    simp only [evSt, evNt, evAt, gaugeS, gaugeN, gaugeAr, gLT, sLT, tsS, tsN, tsA, sCE, sCL1, sCSh, sCA, sCB, rNJ, oT,
      rT, aT] at * <;> omega

theorem datS_stable_g {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ}
    {P : StZ d} : Stable (DatS d n δ r0 R0 a Da Na rn rd j P) evSt evNt evAt := fun σ σ' h hF _ =>
  h.frame hF (fun y hy => by simp only [evSt, gaugeS, gLT, tsS] at hy; omega)
    (fun j hj => by simp only [evNt, gaugeN, gLT, tsN] at hj; omega)
    (fun b k hb => by simp only [evAt, gaugeAr, gLT, tsA] at hb; omega)

theorem datS_stable_s {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ}
    {P : StZ d} : Stable (DatS d n δ r0 R0 a Da Na rn rd j P) (fun y => sepS sLT y ∨ evSt y)
      (fun j => sepN sLT j ∨ evNt j) (fun b k => sepAr sLT b k ∨ evAt b k) := fun σ σ' h hF _ =>
  h.frame hF (fun y hy => by simp only [sepS, sLT, evSt, gaugeS, gLT, tsS] at hy; omega)
    (fun j hj => by simp only [sepN, sLT, evNt, gaugeN, gLT, tsN] at hj; omega)
    (fun b k hb => by simp only [sepAr, sLT, evAt, gaugeAr, gLT, tsA] at hb; omega)

/-! ## The evaluator -/

/-- The evaluator of SEP in a stage: the gauge block on the stage test. -/
def xevT (L : Layout) : XCmdO := xgaugeU L gLT (xtstT L)

/-- The units of the evaluator. -/
abbrev evK (d : ℕ) : ℕ := gaugeK d (stJ d) (tstTK d)

theorem ptDN_zero : ptDN (d := d) 1 0 = 0 := by funext i; simp [ptDN]

set_option maxHeartbeats 4000000 in
/-- **SEP's evaluator in a stage** (`EvalOK`): at the grid point `(2^E; X)` of `aT + 22`, `X` within SEP's domain
about `Y₀` (below `2^bY`), `xevT` writes `stEv orc a r₀ R₀ j (posZ P) X` into `oT + 16`; the constants below `2^m`. -/
theorem evalT_OK {L : Layout} {w : WorldO d} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ} {P : StZ d} {m bY : ℕ} {Y0 : Fin d → ℤ} (hY0 : ∀ i, |Y0 i| < 2 ^ bY)
    (hP : P0OK d n δ r0 R0 a Da Na rn rd) (hW : WT d n δ r0 R0 a ≤ m)
    (hPD : 0 < P.D) (bPD : P.D ≤ 2 ^ m) (bmu : ∀ i, |P.mu i| ≤ 2 ^ m) (bT : ∀ i l, |P.T i l| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hj : j + 1 ≤ m)
    (hℓ : 8 * m + 2 * (3 * (bY + stE d + stEH d + 2) + stJ d + 2) + stK d r0 R0 + 16 ≤ ℓ)
    (hk : stK d r0 R0 < 2 ^ ℓa) (hJa : stJ d + 1 < 2 ^ ℓa) :
    EvalOK L (ctxU w n δ r0 R0 a) ℓa ℓ (xevT L) (DatS d n δ r0 R0 a Da Na rn rd j P) (aT + 22) (oT + 16) (stE d)
      (SepDom Y0 (stE d) (stE1 d)) (stEv w.orc a r0 R0 j (posZ P)) (evK d) evSt evNt evAt := by
  intro σ X hdat hdom h0 hX
  obtain ⟨hDa, bDa, bNa, ha, hrn, brn, hrd, brd, hr⟩ := hP
  have hWm : (2 : ℤ) ^ WT d n δ r0 R0 a ≤ 2 ^ m := powZ_le hW
  set b := bY + stE d + stEH d + 2 with hb
  set bt := 3 * b + stJ d + 2 with hbt
  have hT : TestOK L (ctxU w n δ r0 R0 a) ℓa ℓ (xtstT L) (DatS d n δ r0 R0 a Da Na rn rd j P) (aT + 24) (rT + 34) bt
      (stTest (ctxU w n δ r0 R0 a).w.orc a r0 R0 j (posZ P)) (tstTK d) tsS tsN tsA :=
    TestOK.dat (tstT_OK (XO := ctxU w n δ r0 R0 a) hL hS hN hA hd1 (P := P) (j := j) (a := a) (r0 := r0) (R0 := R0) (Da := Da) (Na := Na) (rn := rn)
      (rd := rd) (m := m) (bt := bt) hPD bPD bmu bT hdm hDa (lt_of_lt_of_le bDa hWm)
      (fun i => lt_of_lt_of_le (bNa i) hWm) hrn (lt_of_lt_of_le brn hWm) hrd (lt_of_lt_of_le brd hWm) ha hr hj
      (by omega) hk) fun σ h => h.tdat
  have bX : ∀ i, |X i| < 2 ^ b := fun i => by
    have h1 : |X i - Y0 i| ≤ 2 ^ (bY + stE d + 1) := by
      refine (hdom i).trans ?_
      have hp := powZ_le (a := stE d - stE1 d) (b := bY + stE d) (by omega)
      rw [pow_succ]
      linarith
    have h2 : |Y0 i| < 2 ^ (bY + stE d + 1) := lt_of_lt_of_le (hY0 i) (powZ_le (by omega))
    calc |X i| = |(X i - Y0 i) + Y0 i| := by rw [sub_add_cancel]
      _ ≤ |X i - Y0 i| + |Y0 i| := abs_add_le _ _
      _ < 2 ^ (bY + stE d + 1) + 2 ^ (bY + stE d + 1) := by linarith
      _ = 2 ^ (bY + stE d + 2) := by ring
      _ ≤ 2 ^ b := powZ_le (by omega)
  refine XVO.mono (gaugeBlockOKU L (ctxU w n δ r0 R0 a) ℓa ℓ gLT (xtstT L) (DatS d n δ r0 R0 a Da Na rn rd j P)
    (stTest (ctxU w n δ r0 R0 a).w.orc a r0 R0 j (posZ P)) (tstTK d) bt tsS tsN tsA σ (2 ^ stE d) X 1 0
    (2 ^ stEH d) 1 (stJ d) b hL (gLT_OK hS hN hA) hd1 hT gLT_disj datS_stable_g hdat hdat.hd
    (by show σ.arr (aT + 22) 0 = _; rw [h0]; norm_num) hX
    (by show σ.arr aKg 0 = _; rw [hdat.kx.kg0]; norm_num)
    (fun i => by show σ.arr aKg (1 + (i : ℕ)) = _; rw [hdat.kx.kg i]; norm_num) hdat.kx.hn
    (by show σ.sc sHd = _; rw [hdat.kx.hd]; norm_num) hdat.kx.nj (by show σ.sc sC2j = _; rw [hdat.kx.c2j]; norm_num)
    (by positivity) one_pos (by positivity) one_pos (powZ_lt (by omega)) bX (by rw [← pow_zero 2]; exact powZ_lt (by omega))
    (fun i => by simp) (powZ_lt (by omega)) (by rw [← pow_zero 2]; exact powZ_lt (by omega)) le_rfl (by omega) hJa)
    le_rfl fun σ' h => ⟨?_, h.2.1, h.2.2⟩
  have e1 : (((2 : ℤ) ^ stEH d : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = (2 : ℚ) ^ stEH d := by push_cast; ring
  have hv := h.1
  rw [ptDN_zero, e1] at hv
  show σ'.sc (oT + 16) = _
  rw [show σ'.sc (oT + 16) = σ'.sc gLT.gout from rfl, hv, stEv, Int.cast_natCast]
  rfl

end AdversarialBco.Unified.ProgO.TriO
