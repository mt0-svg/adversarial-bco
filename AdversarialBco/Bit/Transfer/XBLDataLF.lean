/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataL
public import AdversarialBco.Bit.Transfer.XBLDataTF

@[expose] public section

/-!
# `DataL` holds

`xdl` from the state of `BLInv` in mode `run`, `k'` in the slot `59` on the grid `2^{-p}`, the numerators `ŵ` of
`w_μ` in the array `31` over `D_w` in the slot `91`. Beyond the slots of `DataT`: `n` in `sN`, `R'` on the grid
`2^{-pF}` in `sR`, positive (PARAM rounds it up from a positive value).
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

theorem dl_le (d : ℕ) : dlUnits d ≤ 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 := by
  simp only [dlUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, eQD, eL0, eL1, eA2, eA3, eL4,
    eL5]
  ring_nf
  nlinarith [Nat.zero_le (d * d * d)]

theorem s_le2 (d E : ℕ) : 2 * d + 5 * E + 12 ≤ 1024 * (d + E + 1) ^ 3 := by
  have h : d + E + 1 ≤ (d + E + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  linarith

set_option maxHeartbeats 8000000 in
/-- **`DataL` holds.** -/
theorem dataL : DataL := by
  refine ⟨xdl, 1024, 3, ?_⟩
  intro d L X ℓa ℓ n m K0 E t cfg st Bp bp kp wh Dw σ hd hn hpar hL hlay hI h27 h28 h59 hkon bkp hDw0 bDw h91 h31
    hC hCa
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  obtain ⟨rD', -, rMk', rOne', -, -, -, -⟩ := hI.regs
  obtain ⟨cZ, cN, c2p, c2pF, -, c2eh, -, cLam, cRint⟩ := hI.consts
  obtain ⟨pEps, -, -, pRho, -, -, pR, pSb, -, -, -⟩ := hI.par
  obtain ⟨bsc, -⟩ := hI.bnd
  -- the bounds
  have hs := s_le2 d E
  have hℓ := DataP.l_lt d E ℓ hC
  have hda : d * d + d < 2 ^ ℓa := DataP.a_lt d E ℓa hCa
  -- the integer constants
  have hQ : σ.sc s2p = ((2 ^ cfg.par.p : ℤ) : ℝ) := by rw [c2p]; push_cast; rfl
  have hF : σ.sc s2pF = ((2 ^ cfg.par.pF : ℤ) : ℝ) := by rw [c2pF]; push_cast; rfl
  have hpE : cfg.par.p ≤ E := DataP.slot_pow_le _ _ _ (bsc s2p (by dgo)) c2p
  have hpFE : cfg.par.pF ≤ E := DataP.slot_pow_le _ _ _ (bsc s2pF (by dgo)) c2pF
  have hLam : σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) := by rw [cLam]; push_cast; rfl
  have bLam : |(cfg.par.Lam : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sLam (by dgo)) hLam
  have hN : σ.sc sN = ((n : ℤ) : ℝ) := by rw [cN]; push_cast; rfl
  have bn : |(n : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sN (by dgo)) hN
  have hLamE : cfg.par.Lam = d * cfg.par.Ne := by rw [hpar]; rfl
  have hNe : 1 ≤ cfg.par.Ne := by rw [hpar]; exact Ne_pos hd hn
  have hRi : σ.sc sRint = (((cfg.par.Rint : ℕ) : ℤ) : ℝ) := by rw [cRint]; push_cast; rfl
  have bRi : |((cfg.par.Rint : ℕ) : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sRint (by dgo)) hRi
  obtain ⟨Hh, eHq, hH, bH⟩ := DataP.slot_rat _ _ _ (bsc s2eh (by dgo)) c2eh
  have ePos : (0 : ℚ) < cfg.par.eHat⁻¹ := by
    rw [hpar, show (par d n).eHat = 1 / 2 ^ ((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64) from rfl]
    positivity
  obtain ⟨hH0, heHat⟩ := DataP.eHat_int _ _ eHq ePos
  -- the fields on the grids
  have oEps : OnG cfg.par.pF cfg.par.eps := by rw [hpar, PieceA.par_eps]; exact onG_up' _ _
  have oRho : OnG cfg.par.pF cfg.par.rho := by rw [hpar, PieceA.par_rho]; exact onG_dn' _ _
  have oSb : OnG cfg.par.pF cfg.par.sb := by rw [hpar, PieceA.par_sb]; exact onG_dn' _ _
  have oR : OnG cfg.par.pF cfg.par.R := by rw [hpar, PieceA.par_R]; exact onG_up' _ _
  have hR0q : 0 < cfg.par.R := by rw [hpar, PieceA.par_R]; exact DataP.up_pos _ _ d _ hd
  have hR0 : 0 < qn cfg.par.pF cfg.par.R := DataP.floor_pos_of_grid _ _ hR0q oR
  have bEps := bnd_sc (bsc sEps (by dgo)) pEps
  have bRho := bnd_sc (bsc sRho (by dgo)) pRho
  have bSb := bnd_sc (bsc sSb (by dgo)) pSb
  have bR := bnd_sc (bsc sR (by dgo)) pR
  -- the run
  refine XV.mono (XV.dl hL hlay (E := E) (p := cfg.par.p) (pF := cfg.par.pF) (s := 1024 * (d + E + 1) ^ 3)
    (Ne := cfg.par.Ne) (Lam := cfg.par.Lam) (nn := n) (B := Bp) (b := bp) (wh := wh) (rho := cfg.par.rho)
    (eHat := cfg.par.eHat) (kp := kp) (eps := cfg.par.eps) (sb := cfg.par.sb) (R := cfg.par.R) hd hn rD' rOne' cZ
    hQ hF hH pRho h59 pEps pSb hLam hN pR h91 hpE hpFE bH bRho bkp bEps bSb bLam bn bR bDw hDw0 hH0 hR0 hLamE hNe
    (grid_div oRho) heHat (grid_div hkon) (grid_div oEps) (grid_div oSb) (grid_div oR) h27 h28 h31 hs hℓ hda)
    ((dl_le d).trans (DataP.units_le d E hd)) fun σ' ⟨hH', hg', hP', hf', pl, pr, pe, dd, F⟩ => ?_
  have Ft : FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
      (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ' :=
    F.mono (fun y h => by simp only [sPl]; omega) (fun j h => by omega) (fun b c h => Or.inl h)
  refine ⟨⟨by rw [Ft.1 _ (by dgo)]; exact rD', by rw [Ft.1 _ (by dgo)]; exact rMk',
    by rw [Ft.1 _ (by dgo)]; exact rOne', by rw [Ft.2.1 _ (by dgo)]; exact cZ,
    by rw [Ft.2.1 _ (by dgo)]; exact cRint, (le_abs_self _).trans (wk bRi (by omega)), hH', hg', hP', hf', pl, pr,
    pe⟩, dd, Ft⟩

end AdversarialBco.Bit.Transfer.BLM.DataM
