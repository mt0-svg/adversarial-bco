/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOCallM

@[expose] public section

/-!
# The test block of BL-O's ELL-O calls

`xtstC`: the scaled map `xmapC`, the precision `k` and `2^k` copied from the ELL-O block's cells (the register
`rE + 1 = 65`, the slot `o + 2 = 770` of the block `blkC`) into the CM block's cells, the CM block `xcmU`, its
answer into the register `rE = 64`. `tstC_ok`: a test block (`TestOK`) for `cmQ orc a r₀ k ∘ pmapC` whose cells are
the slots `104` to `135`, the registers `40` to `51` and `64`, the arrays `13` to `15`, all below the block's bases.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open Matrix

variable {d : ℕ}

/-- The ELL-O block of BL-O's calls: `d` in the register `0`, `erK` in `32`, `κ` in `33`; the inputs of v2.1's block
`blkBL` (slots `80` to `87`, arrays `8` to `11`) but the radius `r/2` in the slots `96`, `97`; the centre in the array
`12`; its own cells from the slot `768`, the register `64`, the array `32` (those of `blkBL`). -/
def blkC : EllOBlk :=
  { rd := 0, rK := 32, rκ := 33, sl := 80, sDf := 81, sRn := 82, sRd := 83, srn := 96, srd := 97, sen := 86,
    sed := 87, aH := 8, ag := 9, aP := 10, af := 11, ac := 12, o := 768, rE := 64, aW := 32 }

/-- The CM block's cells in the test: the centre in `aC`, `r₀` in the slots `98`, `99`, the precision in the register
`46`, `2^k` in the slot `112`, the point in the array `14`, the answer in the register `47`, the query point in the
array `15`, scratch slots `120` to `135`, registers `48` to `51`. -/
def cmC : CMLay := ⟨aC, 98, 99, 46, 112, 14, 47, 15, 120, 48⟩

theorem cmC_ok {L : Layout} (hS : 136 ≤ L.NS) (hN : 52 ≤ L.NN) (hA : 16 ≤ L.NA) : CMLay.OKU L cmC := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_⟩ <;>
    simp only [cmC, aC] <;> omega

/-- The test of the call. -/
def xtstC (L : Layout) : XCmdO :=
  .seq (.base (.seq (xmapC L) (.seq (.prim (.frag (.nconst 46 0))) (.seq (.prim (.frag (.nadd 46 46 65)))
    (toX (VL.sop2 L .add 112 770 sZ)))))) <|
  .seq (xcmU L cmC) <|
  .base (.seq (.prim (.frag (.nconst 64 0))) (.prim (.frag (.nadd 64 64 47))))

/-- The units of the test. -/
def tstCK (d : ℕ) : ℕ := (mapCK d + (1 + (1 + 1))) + (cmK d + (1 + 1))

/-- The scaled position map on rationals: `(μ̂_S + (2^pF/D') Â_S y)/D_S`. -/
def pmapC (DS Dp PF : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (y : Fin d → ℚ) : Fin d → ℚ :=
  fun i => ((muS i : ℚ) + (PF : ℚ) / Dp * ∑ j, (aS i j : ℚ) * y j) / DS

theorem pmapC_eq (DS Dp PF D : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (Nv : Fin d → ℤ)
    (hDS : DS ≠ 0) (hDp : Dp ≠ 0) (hD : D ≠ 0) :
    ptDN (DS * Dp * D) (fun i => muS i * (Dp * D) + (aS *ᵥ Nv) i * PF) = pmapC DS Dp PF muS aS (ptDN D Nv) := by
  funext i
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS
  have hDp' : (Dp : ℚ) ≠ 0 := by exact_mod_cast hDp
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hs : ∑ j, (aS i j : ℚ) * ((Nv j : ℚ) / D) = (∑ j, (aS i j : ℚ) * Nv j) / D := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  simp only [ptDN, pmapC, mulVec, dotProduct, hs]
  push_cast
  field_simp

/-- The data the test reads: `d`, `1`, `0`, `2^pF`, `D'`, `D_S D'`, the position, the centre `(Da; Na)` in `aC` and
`r₀ = rn/rd` in the slots `98`, `99`. -/
structure TDatC (DS Dp PF : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (Da : ℤ) (Na : Fin d → ℤ)
    (rn rd : ℤ) (σ : Env d) : Prop where
  hd : σ.nat rD = d
  h1 : σ.nat rOne = 1
  hz : σ.sc sZ = 0
  hpf : σ.sc 103 = PF
  hDp : σ.sc 100 = Dp
  hDSp : σ.sc 101 = ((DS * Dp : ℤ) : ℝ)
  hmu : ∀ i : Fin d, σ.arr aMuS i = muS i
  has : ∀ i j : Fin d, σ.arr aAS (d * i + j) = aS i j
  hDa : σ.arr aC 0 = Da
  hNa : ∀ i : Fin d, σ.arr aC (1 + (i : ℕ)) = Na i
  hrn : σ.sc 98 = rn
  hrd : σ.sc 99 = rd

set_option maxHeartbeats 4000000 in
/-- **The test block of the calls.** -/
theorem tstC_ok {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hS : 771 ≤ L.NS) (hN : 66 ≤ L.NN)
    (hA : 34 ≤ L.NA) (hd1 : 1 ≤ d) {DS Dp PF : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ}
    {Na : Fin d → ℤ} {rn rd : ℤ} {k m bt : ℕ} (hDS : 0 < DS) (hDp : 0 < Dp) (bDS : |DS| ≤ 2 ^ m)
    (bDp : |Dp| ≤ 2 ^ m) (bmu : ∀ j, |muS j| ≤ 2 ^ m) (baS : ∀ j k, |aS j k| ≤ 2 ^ m) (bPF : |PF| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hDa : 0 < Da) (bDa : Da < 2 ^ m) (bNa : ∀ i, |Na i| < 2 ^ m) (hrn : 0 < rn)
    (brn : rn < 2 ^ m) (hrd : 0 < rd) (brd : rd < 2 ^ m) (hℓ : 5 * m + 2 * bt + k + 8 ≤ ℓ) (hk : k < 2 ^ ℓa) :
    TestOK L XO ℓa ℓ (xtstC L) (TDatK blkC (TDatC DS Dp PF muS aS Da Na rn rd) k) 33 64 bt
      (fun y => cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (pmapC DS Dp PF muS aS y)) (tstCK d)
      (fun y => 104 ≤ y ∧ y < 136) (fun j => (40 ≤ j ∧ j < 52) ∨ j = 64) (fun b _ => 13 ≤ b ∧ b < 16) := by
  intro σ D Nv hdat hD0 hDb hNvb hap hNv
  obtain ⟨hT, hk65, h770⟩ := hdat
  have hk65' : σ.nat 65 = k := hk65
  have h770' : σ.sc 770 = ((2 : ℝ) ^ k) := h770
  have hL1 := hL.1
  have bD : |D| ≤ 2 ^ bt := by rw [abs_of_pos hD0]; exact hDb.le
  have bNv : ∀ i, |Nv i| ≤ 2 ^ bt := fun i => (hNvb i).le
  refine XVO.mono (K := (mapCK d + (1 + (1 + 1))) + (cmK d + (1 + 1))) ?_ (by unfold tstCK; omega) fun _ h => h
  -- the map and the precision
  have hpre : XRunsB L XO.X ℓa ℓ (.seq (xmapC L) (.seq (.prim (.frag (.nconst 46 0)))
      (.seq (.prim (.frag (.nadd 46 46 65))) (toX (VL.sop2 L .add 112 770 sZ))))) σ (mapCK d + (1 + (1 + 1)))
      (fun σ' => σ'.arr 14 0 = ((DS * Dp * D : ℤ) : ℝ) ∧
        (∀ i : Fin d, σ'.arr 14 (1 + (i : ℕ)) = ((muS i * (Dp * D) + (aS *ᵥ Nv) i * PF : ℤ) : ℝ)) ∧
        σ'.nat 46 = k ∧ σ'.sc 112 = ((2 : ℝ) ^ k) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => 104 ≤ y ∧ y ≤ 112) (fun j => 40 ≤ j ∧ j ≤ 46) (fun b _ => 13 ≤ b ∧ b ≤ 14) σ σ') := by
    refine XV.seq (XV.mapC hL (by omega) (by omega) hA hd1 (m := m) (bt := bt) hT.hd hT.h1 hT.hz hT.hpf hT.hDp
      hT.hDSp hT.hmu hT.has hap hNv bDS bDp bmu baS bPF hdm bD bNv (by omega)) fun σ1 ⟨z1, n1, d1, F1⟩ => ?_
    refine XV.seq (XV.nconst hL (σ := σ1) (i := 46) (by omega) 0 (by omega)) fun σ2 e2 => ?_
    have r65 : σ2.nat 65 = k := by rw [e2, Env.setNat_nat, if_neg (by omega), F1.1 _ (by omega), hk65']
    refine XV.seq (XV.nadd hL (σ := σ2) (i := 46) (a := 46) (b := 65) (by omega) (by omega) (by omega)
      (by rw [e2]; simp) (by rw [r65]; exact hk)) fun σ3 e3 => ?_
    have s770 : σ3.sc 770 = ((2 : ℝ) ^ k) := by
      rw [e3, e2, Env.setNat_sc, Env.setNat_sc, F1.2.1 _ (by omega), h770']
    have s0 : σ3.sc sZ = 0 := by
      rw [e3, e2, Env.setNat_sc, Env.setNat_sc, F1.2.1 _ (by simp only [sZ]; omega), hT.hz]
    have hpk : |((2 : ℤ) ^ k : ℤ)| < 2 ^ ℓ := by
      rw [abs_of_pos (by positivity)]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
    refine XV.mono (XV.addI hL (σ := σ3) (x := 112) (a := 770) (b := sZ) (u := 2 ^ k) (v := 0) (by omega) (by omega)
      (by simp only [sZ]; omega) (by rw [s770]; push_cast; ring) (by rw [s0]; simp) hpk (by simp)
      (by simpa using hpk)) le_rfl fun σ4 e4 => ?_
    subst e4
    refine ⟨?_, fun i => ?_, ?_, by simp, ?_, ?_⟩
    · rw [Env.setSc_arr, e3, e2, Env.setNat_arr, Env.setNat_arr, z1]
    · rw [Env.setSc_arr, e3, e2, Env.setNat_arr, Env.setNat_arr, n1 i]
    · rw [Env.setSc_nat, e3, e2]; simp [F1.1 65 (by omega), hk65']
    · rw [Env.setSc_draws, e3, e2]; simp [d1]
    · rw [e3, e2]
      exact (((F1.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => h)).setNat (by omega) _).setNat
        (by omega) _).setSc (by omega) _
  refine XVO.seq (XVO.ofX hpre) fun σ1 ⟨z1, n1, k1, p1, d1, F1⟩ => ?_
  -- the CM block
  set bt' := 3 * m + bt + 2 with hbt'
  set Nz : Fin d → ℤ := fun i => muS i * (Dp * D) + (aS *ᵥ Nv) i * PF with hNz
  have hDz : 0 < DS * Dp * D := mul_pos (mul_pos hDS hDp) hD0
  have bDz : DS * Dp * D < 2 ^ bt' := by
    have h := absI_mul_le (absI_mul_le bDS bDp) bD
    rw [abs_of_pos hDz] at h
    exact lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) (by omega))
  have bNz : ∀ i, |Nz i| < 2 ^ bt' := fun i => by
    have h1 : |muS i * (Dp * D)| ≤ 2 ^ (3 * m + bt) :=
      (absI_mul_le (bmu i) (absI_mul_le bDp bD)).trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have h2 : |(aS *ᵥ Nv) i * PF| ≤ 2 ^ (3 * m + bt) :=
      (absI_mul_le (mulVec_abs_le (a := m) (b := bt) (c := m) baS bNv hdm i) bPF).trans
        (pow_le_pow_right₀ (by norm_num) (by omega))
    exact lt_of_le_of_lt (absI_add_le h1 h2) (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hcm : CMDatU cmC Da Na rn rd k σ1 := by
    refine ⟨⟨?_, fun i => ?_, ?_, ?_, k1, p1⟩, ?_⟩
    · rw [F1.2.2.1 _ _ (by simp only [cmC, aC]; omega)]; exact hT.hDa
    · rw [F1.2.2.1 _ _ (by simp only [cmC, aC]; omega)]; exact hT.hNa i
    · rw [F1.2.1 _ (by simp only [cmC]; omega)]; exact hT.hrn
    · rw [F1.2.1 _ (by simp only [cmC]; omega)]; exact hT.hrd
    · rw [F1.1 _ (by omega)]; exact hT.hd
  refine XVO.seq (cmBlockOKU L XO ℓa ℓ cmC Da Na rn rd k m bt' hL (cmC_ok (by omega) (by omega) (by omega)) hd1 hDa
    hrn hrd bDa bNa brn brd (by omega) hk σ1 (DS * Dp * D) Nz hcm hDz bDz bNz (by simpa [cmC] using z1)
    (fun i => by show σ1.arr 14 (1 + (i : ℕ)) = _; rw [n1 i])) fun σ2 h2 => ?_
  obtain ⟨t2, F2, d2⟩ := h2
  have ht2 : σ2.nat 47 = if cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (ptDN (DS * Dp * D) Nz) then 1 else 0 := t2
  have t2b : σ2.nat 47 ≤ 1 := by rw [ht2]; split_ifs <;> omega
  -- the answer
  refine XVO.ofX (XV.seq (XV.nconst hL (σ := σ2) (i := 64) (by omega) 0 (by omega)) fun σ3 e3 => ?_)
  subst e3
  refine XV.mono (XV.nadd hL (i := 64) (a := 64) (b := 47) (by omega) (by omega) (by omega)
    (by rw [Env.setNat_nat, if_pos rfl]; positivity) (by rw [Env.setNat_nat, if_neg (by omega)]; omega)) le_rfl
    fun σ4 e4 => ?_
  subst e4
  refine ⟨?_, ?_, ?_⟩
  · simp only [Env.setNat_nat, if_pos rfl, if_neg (show (47 : ℕ) ≠ 64 by omega), ht2, zero_add]
    rw [hNz, pmapC_eq DS Dp PF D muS aS Nv hDS.ne' hDp.ne' hD0.ne']
    simp
  · have G2 : FrameA (fun y => 104 ≤ y ∧ y < 136) (fun j => (40 ≤ j ∧ j < 52) ∨ j = 64)
        (fun b _ => 13 ≤ b ∧ b < 16) σ σ2 :=
      (F1.mono (fun y h => by omega) (fun j h => Or.inl (by omega)) (fun b _ h => by omega)).trans
        (F2.mono (fun y h => by simp only [cmS, cmC] at h; omega)
          (fun j h => by simp only [cmN, cmC] at h; omega) (fun b _ h => by simp only [cmAr, cmC] at h; omega))
    exact (G2.setNat (Or.inr rfl) _).setNat (Or.inr rfl) _
  · simp [d2, d1]

end AdversarialBco.Unified.ProgO
