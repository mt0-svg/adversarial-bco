/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOCallSz
public import AdversarialBco.Unified.EllOURule

@[expose] public section

/-!
# The main branch of BL-O's ELL-O call

`XVO.callMain`: from the cells after v2.1's preparation (the inputs of `blkBL` for a call `I` with `I.r = r/2`,
`D_c = 1`, `N_c = 0`, `erK = 1`, `r > 0`, `e > 0`) and BL's persistent cells (the position, the centre, `2^pF`, `ε̂`,
`R̂`), `xpreC1; xpreC2` then the ELL-O block `xellOU L blkC` with the test `xtstC` write ELL-O's answer on `I` for
the test `cmQ a r₀ k ∘ pmapC` at the precision `eK + κ`, `κ = kC - p - 4`, within
`preC1K + preC2K + 10^10 (d + ellOSz I + κ + tstCK d + 1)^8` units. Integer data only: the link with BL-O's
configuration is in TailOCall.lean.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Uni.EllO (xellOU ellOBlockOKU)
open Matrix

variable {d : ℕ}

/-- The main branch of the call. -/
def xmainC (L : Layout) : XCmdO := .seq (.base (.seq (xpreC1 L) (xpreC2 L))) (xellOU L blkC (xtstC L))

/-- The test function of the call at the integer data of the cells. -/
def tstF (XO : XCtxO d) (DS PF eh Da : ℤ) (muS : Fin d → ℤ) (aS : Matrix (Fin d) (Fin d) ℤ) (Na : Fin d → ℤ)
    (rn rd : ℤ) (k : ℕ) (y : Fin d → ℚ) : Bool :=
  cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (pmapC DS (dpp (PF - eh)) (pfp (PF - eh) PF) muS aS y)

set_option maxHeartbeats 8000000 in
/-- **The main branch of BL-O's call.** -/
theorem XVO.callMain {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 983 ≤ L.NS)
    (hN : 176 ≤ L.NN) (hA : 46 ≤ L.NA) (hd1 : 1 ≤ d) {I : EllOI d} {rq : ℚ}
    {DS PF eh Rn Da rn rd Rn0 Rd0 : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {Na : Fin d → ℤ}
    {p m κ : ℕ}
    (i4 : XO.X.inp 4 = rn) (i5 : XO.X.inp 5 = rd) (i6 : XO.X.inp 6 = Rn0) (i7 : XO.X.inp 7 = Rd0)
    (hoff : 8 ≤ XO.X.off)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hp : σ.nat rP = p) (hz : σ.sc sZ = 0) (hF : σ.sc s2pF = PF)
    (heh : σ.sc sEps = eh) (hR : σ.sc sR = Rn) (hDS : σ.sc sDS = DS) (hmu : ∀ j : Fin d, σ.arr aMuS j = muS j)
    (has : ∀ i j : Fin d, σ.arr aAS (d * i + j) = aS i j) (hDa : σ.arr aC 0 = Da)
    (hNa : ∀ j : Fin d, σ.arr aC (1 + (j : ℕ)) = Na j)
    (hin : σ.sc 80 = I.ℓ ∧ σ.sc 81 = I.Df ∧ σ.sc 82 = I.R.num ∧ σ.sc 83 = I.R.den ∧ σ.sc 84 = rq.num ∧
      σ.sc 85 = rq.den ∧ σ.sc 86 = I.e.num ∧ σ.sc 87 = I.e.den ∧
      (∀ i j : Fin d, σ.arr 8 (d * i + j) = I.H i j) ∧ (∀ j : Fin d, σ.arr 9 j = I.g j) ∧
      (∀ i j : Fin d, σ.arr 10 (d * i + j) = I.P i j) ∧ (∀ j : Fin d, σ.arr 11 j = I.f j))
    (hIr : I.r = rq / 2) (hDc : I.Dc = 1) (hNc : I.Nc = 0) (herK : I.erK = 1)
    (hκ : κ = cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) - p - 4)
    (hrn : 0 < rn) (hrd : 0 < rd) (hR0n : 0 < Rn0) (hR0d : 0 < Rd0) (hRn : 0 ≤ Rn) (hPF : 0 < PF)
    (hDS0 : 0 < DS) (hDa0 : 0 < Da)
    (brn : rn ≤ 2 ^ m) (brd : rd ≤ 2 ^ m) (bR0n : Rn0 ≤ 2 ^ m) (bR0d : Rd0 ≤ 2 ^ m) (bRn : Rn ≤ 2 ^ m)
    (bPF : PF ≤ 2 ^ m) (beh : |eh| ≤ 2 ^ m) (bDS : |DS| ≤ 2 ^ m) (bmu : ∀ j, |muS j| ≤ 2 ^ m)
    (baS : ∀ i j, |aS i j| ≤ 2 ^ m) (bDa : |Da| ≤ 2 ^ m) (bNa : ∀ j, |Na j| ≤ 2 ^ m)
    (brq : |rq.num| ≤ 2 ^ m) (brqd : (rq.den : ℤ) ≤ 2 ^ m) (hdm : d ≤ 2 ^ m) (hpm : p ≤ m)
    (hℓ1 : 12 * m + 40 ≤ ℓ)
    (hℓ2 : 5 * (m + 2) + 2 * (10000000000 * (d + ellOSz I + κ + 1) ^ 8) + (I.eK + κ) + 8 ≤ ℓ)
    (hℓa : 10000000000 * (d + ellOSz I + κ + 1) ^ 8 + 12 * m + 40 + (I.eK + κ) < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xmainC L) σ
      ((preC1K d m + preC2K m) + 10000000000 * (d + ellOSz I + κ + tstCK d + 1) ^ 8) (fun σ' =>
        EllOOut blkC (ellOI I (tstF XO DS PF eh Da muS aS Na rn rd (I.eK + κ))) (ellExpO I) σ' ∧
          σ'.draws = σ.draws ∧
          FrameA (fun y => (96 ≤ y ∧ y < 256) ∨ 768 ≤ y) (fun j => 32 ≤ j)
            (fun b _ => (12 ≤ b ∧ b < 16) ∨ 32 ≤ b) σ σ') := by
  obtain ⟨i80, i81, i82, i83, i84, i85, i86, i87, iH, ig, iP, i_f⟩ := hin
  have hL1 := hL.1
  have hrqd : (0 : ℤ) < rq.den := by exact_mod_cast rq.den_pos
  -- the preparation
  have hpre : XRunsB L XO.X ℓa ℓ (.seq (xpreC1 L) (xpreC2 L)) σ (preC1K d m + preC2K m) (fun σ2 =>
      σ2.sc 96 = (I.r.num : ℝ) ∧ σ2.sc 97 = (I.r.den : ℝ) ∧ σ2.nat 32 = 1 ∧
        σ2.arr 12 0 = 1 ∧ (∀ j : Fin d, σ2.arr 12 (1 + (j : ℕ)) = 0) ∧
        σ2.sc 100 = ((dpp (PF - eh) : ℤ) : ℝ) ∧ σ2.sc 103 = ((pfp (PF - eh) PF : ℤ) : ℝ) ∧
        σ2.sc 101 = ((DS * dpp (PF - eh) : ℤ) : ℝ) ∧ σ2.sc 98 = rn ∧ σ2.sc 99 = rd ∧ σ2.nat 33 = κ ∧
        σ2.draws = σ.draws ∧
        FrameA (fun y => (96 ≤ y ∧ y ≤ 116) ∨ 800 ≤ y) (fun j => (32 ≤ j ∧ j ≤ 34) ∨ j = 64 ∨ (76 ≤ j ∧ j < 80))
          (fun b _ => b = 12) σ σ2) := by
    refine XV.seq (XV.preC1 hL (by omega) (by omega) (by omega) hd1 (m := m) hD h1 hz i84 i85
      hrqd brq brqd (by omega)) fun σ1 ⟨a96, a97, a32, a12, a12', d1, F1⟩ => ?_
    have k1 : ∀ y, y < 96 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
    have n1 : ∀ j, j < 32 → σ1.nat j = σ.nat j := fun j hj => F1.1 j (by omega)
    refine XV.mono (XV.preC2 hL (by omega) (by omega) (by omega) i4 i5 i6 i7 hoff hrn hrd hR0n hR0d hRn hPF
      (by rw [k1 _ (by simp only [sZ]; omega), hz]) (by rw [n1 _ (by simp only [rOne]; omega), h1])
      (by rw [n1 _ (by simp only [rP]; omega), hp]) (by rw [k1 _ (by simp only [sR]; omega), hR])
      (by rw [k1 _ (by simp only [s2pF]; omega), hF]) (by rw [k1 _ (by simp only [sEps]; omega), heh])
      (by rw [k1 _ (by simp only [sDS]; omega), hDS]) brn brd bR0n bR0d bRn bPF beh bDS hpm hℓ1 (by omega))
      le_rfl ?_
    rintro σ2 ⟨b100, b103, b101, b98, b99, b33, d2, F2⟩
    obtain ⟨hn, hd'⟩ := half_numden rq
    refine ⟨?_, ?_, ?_, ?_, fun j => ?_, b100, b103, b101, b98, b99, by rw [b33, hκ], by rw [d2, d1], ?_⟩
    · rw [F2.2.1 _ (by omega), a96, hIr, hn]
    · rw [F2.2.1 _ (by omega), a97, hIr]
      have : (((rq / 2).den : ℕ) : ℤ) = ((rq.den : ℤ) + rq.den) / (Int.gcd rq.num ((rq.den : ℤ) + rq.den) : ℤ) := hd'
      rw [← this]; push_cast; rfl
    · rw [F2.1 _ (by omega), a32]
    · rw [F2.2.2.1 _ _ (fun h => h), a12]
    · rw [F2.2.2.1 _ _ (fun h => h), a12' j]
    · exact (F1.mono (fun y h => Or.inl h) (fun j h => Or.inl h) (fun _ _ h => h)).trans
        (F2.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim))
  refine XVO.seq (XVO.ofX hpre) fun σ2 h2 => ?_
  obtain ⟨c96, c97, c32, c12, c12', c100, c103, c101, c98, c99, c33, d2, F2⟩ := h2
  -- the data of the block and of the test at `σ2`
  have kS : ∀ y, y < 96 → σ2.sc y = σ.sc y := fun y hy => F2.2.1 y (by omega)
  have kN : ∀ j, j < 32 → σ2.nat j = σ.nat j := fun j hj => F2.1 j (by omega)
  have kA : ∀ b k, b < 12 → σ2.arr b k = σ.arr b k := fun b k hb => F2.2.2.1 b k (by omega)
  have hTD : TDatC DS (dpp (PF - eh)) (pfp (PF - eh) PF) muS aS Da Na rn rd σ2 :=
    { hd := by rw [kN _ (by simp only [rD]; omega), hD]
      h1 := by rw [kN _ (by simp only [rOne]; omega), h1]
      hz := by rw [kS _ (by simp only [sZ]; omega), hz]
      hpf := c103
      hDp := c100
      hDSp := c101
      hmu := fun i => by rw [kA _ _ (by simp only [aMuS]; omega), hmu]
      has := fun i j => by rw [kA _ _ (by simp only [aAS]; omega), has]
      hDa := by rw [kA _ _ (by simp only [aC]; omega), hDa]
      hNa := fun i => by rw [kA _ _ (by simp only [aC]; omega), hNa]
      hrn := c98
      hrd := c99 }
  have hin2 : EllOIn blkC I κ σ2 := by
    refine ⟨hTD.hd, by show σ2.nat 32 = _; rw [c32, herK], c33, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i j => ?_, fun j => ?_,
      fun i j => ?_, fun j => ?_, by show σ2.arr 12 0 = _; rw [c12, hDc]; simp,
      fun j => by show σ2.arr 12 (1 + (j : ℕ)) = _; rw [c12' j, hNc]; simp⟩
    · show σ2.sc 80 = _; rw [kS _ (by omega), i80]
    · show σ2.sc 81 = _; rw [kS _ (by omega), i81]
    · show σ2.sc 82 = _; rw [kS _ (by omega), i82]
    · show σ2.sc 83 = _; rw [kS _ (by omega), i83]
    · exact c96
    · exact c97
    · show σ2.sc 86 = _; rw [kS _ (by omega), i86]
    · show σ2.sc 87 = _; rw [kS _ (by omega), i87]
    · show σ2.arr 8 _ = _; rw [kA _ _ (by omega), iH]
    · show σ2.arr 9 _ = _; rw [kA _ _ (by omega), ig]
    · show σ2.arr 10 _ = _; rw [kA _ _ (by omega), iP]
    · show σ2.arr 11 _ = _; rw [kA _ _ (by omega), i_f]
  -- the test
  set Y := d + ellOSz I + κ + 1 with hY
  set bt := 10000000000 * Y ^ 8 with hbt
  have hℓt : 5 * (m + 1) + 2 * bt + (I.eK + κ) + 8 ≤ ℓ := by omega
  have hkt : I.eK + κ < 2 ^ ℓa := by omega
  have hbt4 : bt + 4 ≤ ℓ := by omega
  have hbta : 10000000000 * Y ^ 8 < 2 ^ ℓa := by omega
  have pm : ∀ {z : ℤ}, |z| ≤ 2 ^ m → |z| ≤ 2 ^ (m + 1) := fun h => h.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have pl : ∀ {z : ℤ}, |z| ≤ 2 ^ m → |z| < 2 ^ (m + 1) := fun h => lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) (by omega))
  have aPF : |PF| ≤ 2 ^ m := by rw [abs_of_pos hPF]; exact bPF
  have hTB := tstC_ok (XO := XO) hL (by omega) (by omega) (by omega) hd1 (DS := DS) (Dp := dpp (PF - eh))
    (PF := pfp (PF - eh) PF) (muS := muS) (aS := aS) (Da := Da) (Na := Na) (rn := rn) (rd := rd) (k := I.eK + κ)
    (m := m + 1) (bt := bt) hDS0 (dpp_pos _) (pm bDS) (dpp_abs _ (absI_sub_le aPF beh)) (fun j => pm (bmu j))
    (fun i j => pm (baS i j)) (pm (pfp_abs _ _ aPF)) (hdm.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    hDa0 (by have := pl bDa; rwa [abs_of_pos hDa0] at this) (fun j => pl (bNa j)) hrn
    (by have := pl (show |rn| ≤ 2 ^ m by rw [abs_of_pos hrn]; exact brn); rwa [abs_of_pos hrn] at this) hrd
    (by have := pl (show |rd| ≤ 2 ^ m by rw [abs_of_pos hrd]; exact brd); rwa [abs_of_pos hrd] at this)
    (by omega) (by omega)
  have hav : blkC.TestAvoid (fun y => 104 ≤ y ∧ y < 136) (fun j => (40 ≤ j ∧ j < 52) ∨ j = 64)
      (fun b _ => 13 ≤ b ∧ b < 16) := by
    refine ⟨fun y hy => ?_, fun j hj => ?_, fun b k hb => ?_⟩ <;>
      simp only [EllOBlk.ownS, EllOBlk.ownN, EllOBlk.ownA, blkC] at * <;> omega
  have hst : Stable (TDatC DS (dpp (PF - eh)) (pfp (PF - eh) PF) muS aS Da Na rn rd)
      (fun y => blkC.ownS y ∨ (104 ≤ y ∧ y < 136)) (fun j => blkC.ownN j ∨ ((40 ≤ j ∧ j < 52) ∨ j = 64))
      (fun b k => blkC.ownA b k ∨ (13 ≤ b ∧ b < 16)) := by
    intro τ τ' hτ F _
    simp only [EllOBlk.ownS, EllOBlk.ownN, EllOBlk.ownA, blkC] at F
    exact { hd := by rw [F.1 _ (by simp only [rD]; omega)]; exact hτ.hd
            h1 := by rw [F.1 _ (by simp only [rOne]; omega)]; exact hτ.h1
            hz := by rw [F.2.1 _ (by simp only [sZ]; omega)]; exact hτ.hz
            hpf := by rw [F.2.1 _ (by omega)]; exact hτ.hpf
            hDp := by rw [F.2.1 _ (by omega)]; exact hτ.hDp
            hDSp := by rw [F.2.1 _ (by omega)]; exact hτ.hDSp
            hmu := fun i => by rw [F.2.2.1 _ _ (by simp only [aMuS]; omega)]; exact hτ.hmu i
            has := fun i j => by rw [F.2.2.1 _ _ (by simp only [aAS]; omega)]; exact hτ.has i j
            hDa := by rw [F.2.2.1 _ _ (by simp only [aC]; omega)]; exact hτ.hDa
            hNa := fun i => by rw [F.2.2.1 _ _ (by simp only [aC]; omega)]; exact hτ.hNa i
            hrn := by rw [F.2.1 _ (by omega)]; exact hτ.hrn
            hrd := by rw [F.2.1 _ (by omega)]; exact hτ.hrd }
  have hB : blkC.OK L 215 112 14 := by simp only [EllOBlk.OK, blkC]; omega
  refine XVO.mono (ellOBlockOKU L XO ℓa ℓ blkC I κ (xtstC L)
    (TDatC DS (dpp (PF - eh)) (pfp (PF - eh) PF) muS aS Da Na rn rd)
    (fun k y => tstF XO DS PF eh Da muS aS Na rn rd k y) (tstCK d) bt
    (fun y => 104 ≤ y ∧ y < 136) (fun j => (40 ≤ j ∧ j < 52) ∨ j = 64) (fun b _ => 13 ≤ b ∧ b < 16) σ2
    hL hB hd1 (by rw [hDc]; norm_num) hTB hav hst (fun τ h => h.hd) (fun j hj => by omega) hTD hin2 le_rfl
    hbt4 hbta) le_rfl ?_
  rintro σ3 ⟨o3, d3, F3⟩
  refine ⟨o3, by rw [d3, d2], ?_⟩
  exact (F2.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => by omega)).trans
    (F3.mono (fun y h => by simp only [EllOBlk.ownS, blkC] at h; omega)
      (fun j h => by simp only [EllOBlk.ownN, blkC] at h; omega)
      (fun b _ h => by simp only [EllOBlk.ownA, blkC] at h; omega))

end AdversarialBco.Unified.ProgO
