/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStepB

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the core step

`xstepO L`, the core step of a stage, one program text for every `d`:

1. the base point `ẑ = tzZ X̂ Y P₂` into `aT + 7` and its rounding `Y₀ = rndZ E K ẑ` into `aT + 18` (`xzO`);
2. SEP (`xsepU`, Unified/ProgOSepUS.lean) from `Y₀` on the evaluator `xevT` (the gauge of the stage test,
   Unified/ProgOTriEval.lean), its vector `G` into `aT + 20`;
3. on failure (flag `rT + 33` at `0`) `G := 0` (v2.1's `xfill`), so that `aT + 20` holds `gvO .. j P ẑ`;
4. the update `X̂ := tzUpd c X̂ G Y 2^{stEu + 1}` (v2.1's `xupdMu`, `xtupdT`).

`triStepSpec : TriStepSpec xstepO TriKX (2^920) 105 (oT + 340) (rT + 72) (aT + 29)`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix
open BitRAM BitRAMO

variable {d : ℕ}

/-- **The core step of TRI-OGD-O.** -/
def xstepO (L : Layout) : XCmdO :=
  .seq (.base (xzO L)) <|
  .seq (xsepU L sLT (xevT L)) <|
  .seq (.ifN (rT + 33) rT (.base (xfill L (oT + 1) (oT + 40) (oT + 1) (aT + 20) (rT + 4) rT (rT + 5) rD rT))
    (.base .skip)) <|
  .seq (.base (xupdMu L (oT + 1) (oT + 34) (oT + 40) (aT + 2) (aT + 20) (oT + 4) sBb (oT + 7) (oT + 8) (oT + 9)
    (rT + 7) rD rT)) <|
  .base (xtupdT L (oT + 1) (oT + 34) (oT + 40) (aT + 3) (aT + 20) (aT + 6) (oT + 4) sBb (oT + 5) (oT + 7) (oT + 6)
    (oT + 13) (oT + 10) (oT + 11) (oT + 12) (rT + 7) (rT + 6) (rT + 4) rD rT)

/-- The slots the core step writes. -/
abbrev sxS (y : ℕ) : Prop := (oT + 16 ≤ y ∧ y < oT + 35) ∨ oT + 40 ≤ y

/-- The registers the core step writes. -/
abbrev sxN (j : ℕ) : Prop := (rT + 3 ≤ j ∧ j < rT + 11) ∨ j = rT + 33 ∨ j = rT + 34 ∨ j = rT + 35 ∨ rT + 40 ≤ j

/-- The arrays the core step writes before the update. -/
abbrev sxA' (b _k : ℕ) : Prop := b = aT + 7 ∨ aT + 18 ≤ b

/-- The arrays the core step writes. -/
abbrev sxA (b _k : ℕ) : Prop := b = aT + 2 ∨ b = aT + 3 ∨ b = aT + 7 ∨ aT + 18 ≤ b

theorem keepS {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {j : ℕ} {P : StZ d}
    {Y : Fin d → ℤ} {σ σ' : Env d} (hKV : TriKV d n δ r0 R0 σ) (hK : TriKXAt d n δ r0 R0 a Da Na rn rd σ)
    (hSt : StAtO σ j P) (h1 : σ.nat rT = 1) (hY : ∀ l : Fin d, σ.arr (aT + 6) l = Y l)
    (G : FrameA sxS sxN sxA σ σ') :
    TriKV d n δ r0 R0 σ' ∧ TriKXAt d n δ r0 R0 a Da Na rn rd σ' ∧ StAtO σ' j P ∧ σ'.nat rT = 1 ∧
      (∀ l : Fin d, σ'.arr (aT + 6) l = Y l) := by
  obtain ⟨st0, st1, st2, st3⟩ := hSt
  refine ⟨hKV.frame G (fun k hk => by simp only [sxS]; omega) (by simp only [sxN, rD]; omega),
    hK.frame G (fun y h1 h2 => by simp only [sxS, oT]; omega) (by simp only [sxN, rNJ, rNj, rNk]; omega)
      (fun k => by simp only [sxA, aKa, aKg]; omega), ⟨fun l => ?_, fun i l => ?_, ?_, ?_⟩, ?_, fun l => ?_⟩
  · rw [G.2.2.1 _ _ (by simp only [sxA]; omega), st0]
  · rw [G.2.2.1 _ _ (by simp only [sxA]; omega), st1]
  · rw [G.2.1 _ (by simp only [sxS]; omega), st2]
  · rw [G.2.1 _ (by simp only [sxS]; omega), st3]
  · rw [G.1 _ (by simp only [sxN]; omega), h1]
  · rw [G.2.2.1 _ _ (by simp only [sxA]; omega), hY]

theorem step_arith {W B Z : ℕ} (hZ : Z ≤ 2 ^ 171 * (W + B + 1) ^ 21) :
    200 * Z ≤ 2 ^ 920 * (W + B + 1) ^ 105 ∧ 2 ^ 60 * Z ^ 5 ≤ 2 ^ 920 * (W + B + 1) ^ 105 := by
  have hV : 1 ≤ W + B + 1 := by omega
  generalize W + B + 1 = V at hZ hV ⊢
  have h1 : V ^ 21 ≤ V ^ 105 := Nat.pow_le_pow_right hV (by norm_num)
  constructor
  · calc 200 * Z ≤ 200 * (2 ^ 171 * V ^ 21) := Nat.mul_le_mul_left _ hZ
      _ = (200 * 2 ^ 171) * V ^ 21 := by ring
      _ ≤ 2 ^ 920 * V ^ 105 := by
        refine Nat.mul_le_mul ?_ h1
        calc 200 * 2 ^ 171 ≤ 2 ^ 8 * 2 ^ 171 := Nat.mul_le_mul_right _ (by norm_num)
          _ = 2 ^ 179 := by rw [← pow_add]
          _ ≤ 2 ^ 920 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · calc 2 ^ 60 * Z ^ 5 ≤ 2 ^ 60 * (2 ^ 171 * V ^ 21) ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ 5)
      _ = 2 ^ 915 * V ^ 105 := by rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
      _ ≤ 2 ^ 920 * V ^ 105 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem abs_two_pow_le {a b : ℕ} (h : a ≤ b) : |(2 : ℤ) ^ a| ≤ 2 ^ b := by
  rw [abs_of_pos (by positivity)]; exact powZ_le h

set_option maxHeartbeats 16000000 in
/-- **The core step** meets its contract. -/
theorem triStepSpec : TriStepSpec xstepO TriKX (2 ^ 920) 105 (oT + 340) (rT + 72) (aT + 29) := by
  intro d L w n δ r0 R0 a ℓa ℓ σ j B P X Y hI hL hR hKV hKX hSt hB hj h1 hX1 hX2 hY bX1 bX2 bY hℓ hℓa
  obtain ⟨Da, Na, rn, rd, hK⟩ := hKX
  obtain ⟨hS, hN, hA⟩ := hR
  have hd1 := hI.hd
  have hz := zok_of a B hI
  have hZa := step_arith (stZ_le d n δ r0 R0 a B)
  have hZ1 := hz.one
  have hdZ := hz.dZ
  have hℓZ : 200 * stZ d n δ r0 R0 a B ≤ ℓ := hZa.1.trans hℓ
  have hℓaZ : 200 * stZ d n δ r0 R0 a B < 2 ^ ℓa := lt_of_le_of_lt hZa.1 hℓa
  generalize stZ d n δ r0 R0 a B = Z at hz hZa hℓZ hℓaZ hZ1 hdZ
  refine XVO.mono (K := zOK d + stepRK d (triETauQ d) (stJ d)) ?_ ((stepK_le hZ1 hdZ hz.tauZ hz.jZ).trans hZa.2)
    fun _ h => h
  clear hZa hℓ hℓa
  have hda : d * d + d < 2 ^ ℓa := by have := asz_lt hL (a := aT) (by omega); unfold asz at this; exact this
  obtain ⟨hR0, hRB, hAl0, hAlB, hPG0, hPGB⟩ := tzDCO_ok d (ellO d n δ r0 R0)
  have hBh : (tzDCO d (ellO d n δ r0 R0)).Bh ≤ 2 ^ Z :=
    (tzDCO_Bh_le d (ellO d n δ r0 R0)).trans (powZ_le hz.laZ)
  have hBh0 : 0 ≤ (tzDCO d (ellO d n δ r0 R0)).Bh := hR0.trans hRB
  have bX1' : ∀ i, |X.1 i| ≤ 2 ^ (2 * Z) := fun i => (bX1 i).trans (hBh.trans (powZ_le (by omega)))
  have bX2' : ∀ i l, |X.2 i l| ≤ 2 ^ (2 * Z) := fun i l => (bX2 i l).trans (hBh.trans (powZ_le (by omega)))
  have bY' : ∀ l, |Y l| ≤ 2 ^ (2 * Z) := fun l => (bY l).trans (powZ_le (by have := hz.pZ; omega))
  have bP2 : |(tzDCO d (ellO d n δ r0 R0)).P2| ≤ 2 ^ (2 * Z) := abs_two_pow_le (by have := hz.pZ; omega)
  obtain ⟨hPD, bPD, bmu, bT⟩ := hB
  have hWZ := hz.wZ
  have hjZ : j + 1 ≤ Z := by have := hz.mst; omega
  have hdm : d ≤ 2 ^ Z := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) hdZ)
  -- 1. the base point and its rounding
  refine XVO.seq (XVO.ofX (XV.zO hL (E := 2 * Z) (F := 6 * Z) (Es := stE d) (K := tKZ d (ellO d n δ r0 R0))
    (P2 := (tzDCO d (ellO d n δ r0 R0)).P2) (Xp := X) (Y := Y) (by omega) (by omega) (by omega) hKV.rd h1 hda
    hKV.z hKV.p2 hK.cE hK.c2K hX1 hX2 hY bX1' bX2' bY' bP2 (by omega) (by have := hz.eZ; omega)
    (by have := hz.kzZ; omega) (by omega))) fun σ1 h1' => ?_
  obtain ⟨z1, y1, dr1, F1⟩ := h1'
  have G1 : FrameA sxS sxN sxA' σ σ1 := F1.mono (fun y h => by simp only [zS] at h; simp only [sxS]; omega)
    (fun j h => by simp only [zN] at h; simp only [sxN]; omega)
    (fun b k h => by simp only [zA] at h; simp only [sxA']; omega)
  obtain ⟨kv1, kx1, st1, n1, y61⟩ := keepS hKV hK hSt h1 hY (G1.mono (fun _ h => h) (fun _ h => h)
    (fun b k h => by simp only [sxA'] at h; simp only [sxA]; omega))
  have hdat1 : DatS d n δ r0 R0 a Da Na rn rd j P σ1 := ⟨kx1, kv1.rd, n1, kv1.z, st1⟩
  -- the rounded base point
  have bz : ∀ i, |tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2 i| ≤ 2 ^ (2 * (2 * Z) + d + 1) :=
    abs_tzZ_le bX1' bX2' bY' bP2
  have bY0 : ∀ i, |rndZ (stE d) (tKZ d (ellO d n δ r0 R0)) (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2) i| <
      2 ^ (6 * Z + 3) := fun i => by
    have h := abs_rndZ_le (E := stE d) (K := tKZ d (ellO d n δ r0 R0)) bz i
    have e1 : (2 : ℤ) ^ (2 * (2 * Z) + d + 1 + stE d + 1) ≤ 2 ^ (6 * Z + 2) :=
      powZ_le (by have := hz.eZ; omega)
    have e2 : (2 : ℤ) ^ tKZ d (ellO d n δ r0 R0) < 2 ^ (6 * Z + 2) := powZ_lt (by have := hz.kzZ; omega)
    have e3 : (2 : ℤ) ^ (6 * Z + 3) = 2 ^ (6 * Z + 2) + 2 ^ (6 * Z + 2) := by ring
    rw [e3]; exact lt_of_le_of_lt h (by linarith only [e1, e2])
  -- 2. SEP
  refine XVO.seq (sepBlockOKU L (ctxU w n δ r0 R0 a) ℓa ℓ sLT (xevT L) (DatS d n δ r0 R0 a Da Na rn rd j P)
    (stEv w.orc a r0 R0 j (posZ P)) (evK d) (stJ d + 1) evSt evNt evAt σ1
    (rndZ (stE d) (tKZ d (ellO d n δ r0 R0)) (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2)) (stE d) (stE1 d)
    (triETauQ d) 0 (stEu d) (6 * Z + 3) hL (sLT_OK (by omega) (by omega) (by omega)) hd1
    (evalT_OK hL (by omega) (by omega) (by omega) hd1 (m := Z) bY0 kx1.rep hWZ hPD
      (bPD.trans (powZ_le hz.bZ)) (fun i => (bmu i).trans (powZ_le hz.bZ))
      (fun i l => (bT i l).trans (powZ_le hz.bZ)) hdm hjZ
      (by have := hz.eZ; have := hz.hZ; have := hz.jZ; have := hz.kZ; omega)
      (by have := hz.kZ; omega) (by have := hz.jZ; omega))
    (fun X _ => lt_of_le_of_lt (stEv_le w.orc a r0 R0 j (posZ P) X) (powZ_lt (Nat.lt_succ_self _)))
    sLT_disj datS_stable_s hdat1 kv1.rd y1 bY0
    (by show σ1.sc sCE = _; rw [kx1.cE]; norm_num) (by show σ1.sc sCL1 = _; rw [kx1.cL1]; norm_num)
    (by show σ1.sc sCSh = _; rw [kx1.cSh]; norm_num) (by show σ1.sc sCA = _; rw [kx1.cA]; norm_num)
    (by show σ1.sc sCB = _; rw [kx1.cB]; norm_num) (by show σ1.nat rNJ = _; rw [kx1.nJ]; omega)
    (by simp [stE]) (by have := hz.eZ; have := hz.tauZ; have := hz.uZ; have := hz.jZ; omega)
    (by have := hz.eZ; have := hz.tauZ; omega)) fun σ2 h2' => ?_
  obtain ⟨out2, F2, d2⟩ := h2'
  have G2 : FrameA sxS sxN sxA' σ σ2 := G1.trans (F2.mono
    (fun y h => by simp only [sepS, sLT, evSt, gaugeS, gLT, tsS] at h; simp only [sxS]; omega)
    (fun j h => by simp only [sepN, sLT, evNt, gaugeN, gLT, tsN] at h; simp only [sxN]; omega)
    (fun b k h => by simp only [sepAr, sLT, evAt, gaugeAr, gLT, tsA] at h; simp only [sxA']; omega))
  obtain ⟨kv2, kx2, st2, n2, y62⟩ := keepS hKV hK hSt h1 hY (G2.mono (fun _ h => h) (fun _ h => h)
    (fun b k h => by simp only [sxA'] at h; simp only [sxA]; omega))
  -- 3. `G := 0` on failure
  have h3 : XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ
      (.ifN (rT + 33) rT (.base (xfill L (oT + 1) (oT + 40) (oT + 1) (aT + 20) (rT + 4) rT (rT + 5) rD rT))
        (.base .skip)) σ2 ((1 + (d * (1 + 6) + 3)) + 2)
      (fun σ3 => (∀ i : Fin d, σ3.arr (aT + 20) i =
          gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2) i) ∧
        σ3.draws = σ2.draws ∧
        FrameA (fun y => oT + 40 ≤ y) (fun j => j = rT + 5 ∨ j = rT + 4) (fun b _ => b = aT + 20) σ2 σ3) := by
    rcases hr : sepE (stEv w.orc a r0 R0 j (posZ P))
      (rndZ (stE d) (tKZ d (ellO d n δ r0 R0)) (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2)) (stE d) (stE1 d)
      (triETauQ d) 0 (stEu d) with _ | ⟨Yr, Gr⟩
    · have hnok : σ2.nat (rT + 33) = 0 := by rw [hr] at out2; exact out2
      refine XVO.ifN hL (by omega) (by omega) (by rw [hnok]; positivity) (by rw [n2]; have := hL.1; omega)
        (fun _ => ?_) (fun hc => absurd (by rw [hnok, n2]; omega) hc)
      refine XVO.ofX (XV.mono (XV.fill hL (z := oT + 1) (t := oT + 40) (s := oT + 1) (aB := aT + 20) (nr := rT + 4)
        (nst := rT) (nk := rT + 5) (nn := rD) (none := rT) (N := d) (st := 1) (E := 0) (v := 0) (by omega)
        (by omega) (by omega) kv2.z (by omega) (by omega) (by omega) (by omega) (by simp only [rD]; omega)
        (by omega) (by simp only [rD, rT]; decide) (by omega) (by omega) kv2.rd n2 n2 one_pos
        (fun k hk => by unfold asz; omega) (by omega) (by omega) (by have := hL.1; omega) (by rw [kv2.z]; simp)
        (by simp) (by omega)) le_rfl fun σ3 ⟨f3, d3, F3⟩ => ⟨fun i => ?_, d3, F3.mono (fun _ h => h)
          (fun _ h => h) (fun b _ h => h.1)⟩)
      have := f3 i i.2
      rw [one_mul] at this
      rw [this]
      unfold gvO sepGZ
      rw [hr]
      simp
    · have hok : σ2.nat (rT + 33) = 1 ∧ ∀ i : Fin d, σ2.arr (aT + 19) i = Yr i ∧ σ2.arr (aT + 20) i = Gr i := by
        rw [hr] at out2; exact out2
      refine XVO.ifN hL (by omega) (by omega) (by rw [hok.1]; have := hL.1; omega) (by rw [n2]; have := hL.1; omega)
        (fun hc => absurd hc (by rw [hok.1, n2]; omega)) (fun _ => XVO.mono (XVO.ofX (XV.skip σ2)) (by omega)
          fun σ3 e3 => ?_)
      subst e3
      refine ⟨fun i => ?_, rfl, FrameA.refl _ _ _ _⟩
      rw [(hok.2 i).2]
      unfold gvO sepGZ
      rw [hr]
  refine XVO.seq h3 fun σ3 h3' => ?_
  obtain ⟨g3, d3, F3⟩ := h3'
  have G3 : FrameA sxS sxN sxA' σ σ3 := G2.trans (F3.mono (fun y h => by simp only [sxS]; omega)
    (fun j h => by simp only [sxN]; omega) (fun b k h => by simp only [sxA']; omega))
  obtain ⟨kv3, kx3, st3, n3, y63⟩ := keepS hKV hK hSt h1 hY (G3.mono (fun _ h => h) (fun _ h => h)
    (fun b k h => by simp only [sxA'] at h; simp only [sxA]; omega))
  have eX3 : ∀ i : Fin d, σ3.arr (aT + 2) i = X.1 i := fun i => by
    rw [G3.2.2.1 _ _ (by simp only [sxA']; omega), hX1]
  have eT3 : ∀ i l : Fin d, σ3.arr (aT + 3) (d * i + l) = X.2 i l := fun i l => by
    rw [G3.2.2.1 _ _ (by simp only [sxA']; omega), hX2]
  -- 4. the update
  have bA : ∀ i, |gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2) i| ≤
      2 ^ (2 * Z + 3) := fun i => (gvO_le _ _ _ _ _ _ _ _ i).trans (powZ_le (by have := hz.eZ; have := hz.jZ; omega))
  have bR' : |(tzDCO d (ellO d n δ r0 R0)).R| ≤ 2 ^ (2 * Z + 3) := by
    rw [abs_of_nonneg hR0]; exact hRB.trans (hBh.trans (powZ_le (by omega)))
  have bBh' : |(tzDCO d (ellO d n δ r0 R0)).Bh| ≤ 2 ^ (2 * Z + 3) := by
    rw [abs_of_nonneg hBh0]; exact hBh.trans (powZ_le (by omega))
  have bAl' : |(tzDCO d (ellO d n δ r0 R0)).Al| ≤ 2 ^ (2 * Z + 3) := by
    rw [abs_of_pos hAl0]; exact hAlB.trans (hBh.trans (powZ_le (by omega)))
  have bPG' : |(tzDCO d (ellO d n δ r0 R0)).PG| ≤ 2 ^ (2 * Z + 3) := by
    rw [abs_of_nonneg hPG0]; exact hPGB.trans (hBh.trans (powZ_le (by omega)))
  have bPB' : |(tzDCO d (ellO d n δ r0 R0)).PB| ≤ 2 ^ (2 * Z + 3) :=
    abs_two_pow_le (by have := hz.bvZ; omega)
  have bPj' : |(tzDCO d (ellO d n δ r0 R0)).Pj| ≤ 2 ^ (2 * Z + 3) :=
    abs_two_pow_le (by have := hz.jaZ; omega)
  have bBb' : |tBb d| ≤ 2 ^ (2 * Z + 3) := abs_two_pow_le (by have := hz.uZ; omega)
  have bD8' : |8 * (tzDCO d (ellO d n δ r0 R0)).dd| ≤ 2 ^ (2 * Z + 3) := by
    show |8 * (d : ℤ)| ≤ _
    have h8 : (8 : ℤ) * d ≤ 2 ^ (2 * Z + 3) := by
      have : (d : ℤ) ≤ 2 ^ Z := by exact_mod_cast hdm
      calc (8 : ℤ) * d ≤ 8 * 2 ^ Z := by linarith only [this]
        _ = 2 ^ (Z + 3) := by ring
        _ ≤ 2 ^ (2 * Z + 3) := powZ_le (by omega)
    rw [abs_of_nonneg (by positivity)]; exact h8
  refine XVO.seq (XVO.ofX (XV.updMu hL (z := oT + 1) (v := oT + 34) (t := oT + 40) (aXm := aT + 2) (aA := aT + 20)
    (sPB := oT + 4) (sBb := sBb) (sPj := oT + 7) (sR := oT + 8) (sMR := oT + 9) (ni := rT + 7) (nd := rD) (none := rT)
    (E := 2 * Z + 3) (c := tzDCO d (ellO d n δ r0 R0)) (Xp := X) (Y := Y) (Bb := tBb d)
    (by omega) (by omega) (by omega) (by simp only [sBb, oT]; omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by simp only [sBb, oT]; omega) (by omega)
    (by omega) kv3.z (by omega) (by omega) (by omega) (by omega) (by simp only [rD]; omega) (by omega)
    (by simp only [rD]; omega) (by omega) kv3.rd n3 (lt_of_le_of_lt (Nat.le_add_left d (d * d)) hda) eX3 g3
    kv3.pb kx3.bb kv3.pj kv3.r kv3.mr
    (fun i => (bX1' i).trans (powZ_le (by omega))) bA bPB' bBb' bPj' bR' (by omega))) fun σ4 h4' => ?_
  obtain ⟨u4, d4, F4⟩ := h4'
  have G4 : FrameA sxS sxN sxA σ σ4 := (G3.mono (fun _ h => h) (fun _ h => h)
    (fun b k h => by simp only [sxA'] at h; simp only [sxA]; omega)).trans
    (F4.mono (fun y h => by simp only [sxS]; omega) (fun j h => by simp only [sxN]; omega)
      (fun b k h => by simp only [sxA]; omega))
  obtain ⟨kv4, kx4, st4, n4, y64⟩ := keepS hKV hK hSt h1 hY G4
  have eA4 : ∀ l : Fin d, σ4.arr (aT + 20) l =
      gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2) l := fun l => by
    rw [F4.2.2.1 _ _ (by omega), g3]
  have eT4 : ∀ i l : Fin d, σ4.arr (aT + 3) (d * i + l) = X.2 i l := fun i l => by
    rw [F4.2.2.1 _ _ (by omega), eT3]
  refine XVO.mono (XVO.ofX (XV.tupdT hL (z := oT + 1) (v := oT + 34) (t := oT + 40) (aXt := aT + 3) (aA := aT + 20)
    (aY := aT + 6) (sPB := oT + 4) (sBb := sBb) (sP2 := oT + 5) (sPj := oT + 7) (sPG := oT + 6) (sD8 := oT + 13)
    (sAl := oT + 10) (sBh := oT + 11) (sMB := oT + 12) (ni := rT + 7) (nl := rT + 6) (nr := rT + 4) (nd := rD)
    (none := rT) (E := 2 * Z + 3) (c := tzDCO d (ellO d n δ r0 R0)) (Xp := X) (Y := Y) (Bb := tBb d)
    (by omega) (by omega) (by omega) (by simp only [sBb, oT]; omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp only [sBb, oT]; decide) (by omega) kv4.z (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [rD]; omega) (by omega)
    (by simp only [rD, rT]; decide) kv4.rd n4 hda eT4 eA4 y64 kv4.pb kx4.bb kv4.p2 kv4.pj kv4.pg kv4.d8 kv4.al kv4.bh
    kv4.mb (fun i l => (bX2' i l).trans (powZ_le (by omega))) bA (fun l => (bY' l).trans (powZ_le (by omega)))
    bPB' bBb' (bP2.trans (powZ_le (by omega))) bPj' bPG' bD8' bAl' bBh' (by omega)))
    le_rfl fun σ5 h5' => ?_
  obtain ⟨t5, d5, F5⟩ := h5'
  have G5 : FrameA sxS sxN sxA σ σ5 := G4.trans (F5.mono (fun y h => by simp only [sxS]; omega)
    (fun j h => by simp only [sxN]; omega) (fun b k h => by simp only [sxA]; omega))
  obtain ⟨_, kx5, _, _, _⟩ := keepS hKV hK hSt h1 hY G5
  refine ⟨fun l => by rw [F5.2.2.1 _ _ (by omega)]; exact u4 l, t5, ⟨Da, Na, rn, rd, kx5⟩,
    by rw [d5, d4, d3, d2, dr1], G5.mono (fun y h => by simp only [sxS] at h; simp only [stpS]; omega)
      (fun j h => by simp only [sxN] at h; simp only [stpN]; omega)
      (fun b k h => by simp only [sxA] at h; simp only [stpA]; omega)⟩

end AdversarialBco.Unified.ProgO.TriO
