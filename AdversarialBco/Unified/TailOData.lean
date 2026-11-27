/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPar
public import AdversarialBco.Bit.Transfer.XBLDataLF

@[expose] public section

/-!
# The data of R11 TEST and R14 LINE at BL-O's PARAM

The data commands `xdt`, `xdl` of R11 TEST and R14 LINE (Bit/Transfer/XBLDataTF.lean, XBLDataL.lean) at
`cfg.par = parN ne d n`, `1 ≤ ne`, with the constants `1024`, `3`. The proofs read PARAM only through `Λ = d N_e`,
`1 ≤ N_e`, `0 < 1/ê`, the rounding of its fields onto the grid `2^{-pF}` and `0 < R'`; each holds at `parN` as at
`par d n = parN (Ne d n) d n`.
-/

namespace AdversarialBco.Unified.ProgO.TailD

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.Bit AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM AdversarialBco.Bit.Transfer.BLM.DataM
open AdversarialBco.Unified.BLO (parN)

variable {d : ℕ}

/-! ## PARAM's fields at `parN` -/

theorem parN_onG_sb (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).sb := onG_dn' _ _

theorem parN_onG_R (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).R := onG_up' _ _

theorem parN_R_pos (ne d n : ℕ) (hd : 1 ≤ d) : 0 < (parN ne d n).R := DataP.up_pos _ _ d _ hd

theorem parN_eHat_pos (ne d n : ℕ) : (0 : ℚ) < (parN ne d n).eHat⁻¹ := by
  rw [tlN_eHat, one_div, inv_inv]; exact_mod_cast tlHN_pos ne d n

set_option maxHeartbeats 8000000 in
/-- **`DataTO` holds**: the data of R11 TEST at `parN ne d n`. -/
theorem dataTO_holds : DataTO := by
  refine ⟨xdt, 1024, 3, ?_⟩
  intro d L X ℓa ℓ n m K0 E t ne cfg st Bp bp Gp σ hd hn hne hpar hL hlay hI h27 h28 h29 hC hCa
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  obtain ⟨rD', -, rMk', rOne', -, -, -, -⟩ := hI.regs
  obtain ⟨cZ, -, c2p, c2pF, -, c2eh, -, cLam, cRint⟩ := hI.consts
  obtain ⟨pEps, -, pEta, pRho, -, -, -, pSb, -, -, -⟩ := hI.par
  have hmo := hI.mode
  simp only [ModeRep, StRep] at hmo
  obtain ⟨-, sF, -, -, hBst, hbst, ⟨hKs, hKon⟩, -, -⟩ := hmo
  obtain ⟨bsc, barr⟩ := hI.bnd
  -- the bounds
  have hs : d + 5 * E + 12 ≤ 1024 * (d + E + 1) ^ 3 := DataP.s_le d E
  have hℓ' := DataP.l_lt d E ℓ hC
  have hℓ : d + 8 * E + 80 < ℓ := by omega
  have hda : d * d + d < 2 ^ ℓa := DataP.a_lt d E ℓa hCa
  -- the integer constants
  have hQ : σ.sc s2p = ((2 ^ cfg.par.p : ℤ) : ℝ) := by rw [c2p]; push_cast; rfl
  have hF : σ.sc s2pF = ((2 ^ cfg.par.pF : ℤ) : ℝ) := by rw [c2pF]; push_cast; rfl
  have hpE : cfg.par.p ≤ E := DataP.slot_pow_le _ _ _ (bsc s2p (by dgo)) c2p
  have hpFE : cfg.par.pF ≤ E := DataP.slot_pow_le _ _ _ (bsc s2pF (by dgo)) c2pF
  have hLam : σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) := by rw [cLam]; push_cast; rfl
  have bLam : |(cfg.par.Lam : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sLam (by dgo)) hLam
  have hLamE : cfg.par.Lam = d * cfg.par.Ne := by rw [hpar]; rfl
  have hNe : 1 ≤ cfg.par.Ne := by rw [hpar]; exact hne
  have hRi : σ.sc sRint = (((cfg.par.Rint : ℕ) : ℤ) : ℝ) := by rw [cRint]; push_cast; rfl
  have bRi : |((cfg.par.Rint : ℕ) : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sRint (by dgo)) hRi
  obtain ⟨Hh, eHq, hH, bH⟩ := DataP.slot_rat _ _ _ (bsc s2eh (by dgo)) c2eh
  have ePos : (0 : ℚ) < cfg.par.eHat⁻¹ := by rw [hpar]; exact parN_eHat_pos ne d n
  obtain ⟨hH0, heHat⟩ := DataP.eHat_int _ _ eHq ePos
  -- the fields on the grids
  have oEps : OnG cfg.par.pF cfg.par.eps := by rw [hpar]; exact tlN_onG_eps ne d n
  have oEta : OnG cfg.par.pF cfg.par.eta := by rw [hpar]; exact tlN_onG_eta ne d n
  have oRho : OnG cfg.par.pF cfg.par.rho := by rw [hpar]; exact tlN_onG_rho ne d n
  have oSb : OnG cfg.par.pF cfg.par.sb := by rw [hpar]; exact parN_onG_sb ne d n
  have bEps := bnd_sc (bsc sEps (by dgo)) pEps
  have bEta := bnd_sc (bsc sEta (by dgo)) pEta
  have bRho := bnd_sc (bsc sRho (by dgo)) pRho
  have bSb := bnd_sc (bsc sSb (by dgo)) pSb
  have bK := bnd_sc (bsc sK (by dgo)) hKs
  -- the state
  have hBs : ∀ i j : Fin d, σ.arr aB (d * i + j) = qn cfg.par.p (st.B i j) ∧ OnG cfg.par.p (st.B i j) ∧
      |qn cfg.par.p (st.B i j)| ≤ 2 ^ E := fun i j =>
    ⟨(hBst i j).1, (hBst i j).2,
      bnd_arr (barr aB (by dgo) _ (by unfold asz; nlinarith [i.2, j.2])) (hBst i j).1⟩
  have hbs : ∀ j : Fin d, σ.arr ab j = qn cfg.par.p (st.b j) ∧ OnG cfg.par.p (st.b j) ∧ |qn cfg.par.p (st.b j)| ≤ 2 ^ E := fun j =>
    ⟨(hbst j).1, (hbst j).2, bnd_arr (barr ab (by dgo) _ (by unfold asz; nlinarith [j.2])) (hbst j).1⟩
  -- the run
  refine XV.mono ?_ ((dt_le d).trans (DataP.units_le d E hd)) (fun _ h => h)
  unfold xdt
  refine XV.seq (XV.dtC hL hlay rD' rOne' cZ hQ hF pEta oEta bEta hpE hpFE h27 h28 h29 hs hℓ hda)
    fun σ1 ⟨c260, c262, c263, c264, c265, c266, c267, hPP, hPf, d1, F1⟩ => ?_
  have k1 : ∀ y < 256, σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have n1 : ∀ j < 19, σ1.nat j = σ.nat j := fun j hj => F1.1 j (by omega)
  have a1 : ∀ b k, b < 8 → σ1.arr b k = σ.arr b k := fun b k hb =>
    F1.2.2.1 b k (fun h => by simp only [aPPn] at h; omega)
  have z1 : σ1.sc sZ = 0 := by rw [k1 _ (by dgo)]; exact cZ
  have hz0 : |σ1.sc sZ| < 2 ^ ℓ := by rw [z1]; simp
  have hf1 : |σ1.sc sFirst| < 2 ^ ℓ := by
    rw [k1 _ (by dgo), sF]
    have : (1 : ℝ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
    split_ifs <;> simp <;> linarith
  -- what both branches keep, and the end
  have fin : ∀ σ2 : Env d, σ2.draws = σ1.draws →
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ (256 ≤ y ∧ y ≤ 258) ∨ 300 ≤ y)
        (fun j => (19 ≤ j ∧ j ≤ 26) ∨ (29 ≤ j ∧ j ≤ 31)) (fun b _ => aPHn ≤ b ∧ b ≤ aPgd) σ1 σ2 →
      σ2.draws = σ.draws ∧
      FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
        (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ2 ∧
      σ2.nat rD = d ∧ σ2.nat rMk = cfg.m ∧ σ2.nat rOne = 1 ∧ σ2.sc sZ = 0 ∧ σ2.sc sRint = cfg.par.Rint ∧
      (cfg.par.Rint : ℤ) ≤ 2 ^ (1024 * (d + E + 1) ^ 3) ∧
      (∀ i j : Fin d, PairA σ2 aPPn aPPd (d * i + j) (1024 * (d + E + 1) ^ 3) ((Bp * Bpᵀ) i j)) ∧
      (∀ j : Fin d, PairA σ2 aPfn aPfd j (1024 * (d + E + 1) ^ 3) ((bp - (cfg.par.eta / 2) • Gp) j)) := by
    intro σ2 d2 F2
    have Ft : FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
        (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ2 := (F1.mono (fun y h => by simp only [sPl]; omega) (fun j h => by omega)
      (fun b c h => by simp only [aPHn, aPPn, aPfd] at h ⊢; omega)).trans
      (F2.mono (fun y h => by simp only [sPl]; omega) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPgd, aPfd] at h ⊢; omega))
    have kA : ∀ b k, ¬(aPHn ≤ b ∧ b ≤ aPgd) → σ2.arr b k = σ1.arr b k := fun b k h => F2.2.2.1 b k h
    refine ⟨by rw [d2, d1], Ft, by rw [Ft.1 _ (by dgo)]; exact rD', by rw [Ft.1 _ (by dgo)]; exact rMk',
      by rw [Ft.1 _ (by dgo)]; exact rOne', by rw [Ft.2.1 _ (by dgo)]; exact cZ,
      by rw [Ft.2.1 _ (by dgo)]; exact cRint, ?_, fun i j => ?_, fun j => ?_⟩
    · exact (le_abs_self _).trans (wk bRi (by omega))
    · exact PairA.keep (hPP i j) (kA _ _ (by simp only [aPHn, aPgd, aPPn]; omega))
        (kA _ _ (by simp only [aPHn, aPgd, aPPd]; omega))
    · exact PairA.keep (hPf j) (kA _ _ (by simp only [aPHn, aPgd, aPfn]; omega))
        (kA _ _ (by simp only [aPHn, aPgd, aPfd]; omega))
  cases hfs : st.first
  · -- after the first round: `xdtA`
    have t0 : ¬σ1.sc sZ < σ1.sc sFirst := by rw [z1, k1 _ (by dgo), sF, hfs]; simp
    refine XV.ifS_f hL (by dgo) (by dgo) hz0 hf1 t0 (XV.mono (XV.dtA hL hlay (E := E) (p := cfg.par.p) (pF := cfg.par.pF)
      (Ne := cfg.par.Ne) (Lam := cfg.par.Lam) (B := st.B) (b := st.b) (rho := cfg.par.rho) (eHat := cfg.par.eHat) (k := st.k)
      (eps := cfg.par.eps) (sb := cfg.par.sb) hd
      (by rw [n1 _ (by dgo)]; exact rD') (by rw [n1 _ (by dgo)]; exact rOne') z1 c262 c263 c265 c266 c267
      (by rw [k1 _ (by dgo)]; exact hQ) (by rw [k1 _ (by dgo)]; exact hF) (by rw [k1 _ (by dgo)]; exact hH)
      (by rw [k1 _ (by dgo)]; exact pRho) (by rw [k1 _ (by dgo)]; exact hKs) (by rw [k1 _ (by dgo)]; exact pEps)
      (by rw [k1 _ (by dgo)]; exact pSb) (by rw [k1 _ (by dgo)]; exact hLam) hpE hpFE bH bRho bK bEps bSb bLam hH0
      hLamE hNe (grid_div oRho) heHat (grid_div hKon) (grid_div oEps) (grid_div oSb)
      (fun i j => by rw [a1 _ _ (by dgo)]; exact hBs i j) (fun j => by rw [a1 _ _ (by dgo)]; exact hbs j)
      hs hℓ hda) le_rfl fun σ2 ⟨hH2, hg2, pl, pr, pe, d2, F2⟩ => ?_)
    obtain ⟨dd, Ft, e1, e2, e3, e4, e5, e6, e7, e8⟩ := fin σ2 d2 F2
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨⟨e1, e2, e3, e4, e5, e6, hH2, hg2, e7, e8, pl, pr, pe⟩, dd, Ft⟩
  · -- the first round of an epoch: `xdtF`
    have t1 : σ1.sc sZ < σ1.sc sFirst := by rw [z1, k1 _ (by dgo), sF, hfs]; simp
    refine XV.mono (XV.ifS_t hL (by dgo) (by dgo) hz0 hf1 t1 (XV.mono (XV.dtF hL hlay (E := E) (P := cfg.par) hd
      (by rw [n1 _ (by dgo)]; exact rD') (by rw [n1 _ (by dgo)]; exact rOne') z1 c260 c262
      (by rw [k1 _ (by dgo)]; exact hF) (by rw [k1 _ (by dgo)]; exact pEps) (by rw [k1 _ (by dgo)]; exact hLam)
      hpFE bEps bLam hLamE hNe (grid_div oEps) hs hℓ hda) le_rfl fun σ2 h => h)) (by have := dtF_le d; omega)
      fun σ2 ⟨hH2, hg2, pl, pr, pe, d2, F2⟩ => ?_
    obtain ⟨dd, Ft, e1, e2, e3, e4, e5, e6, e7, e8⟩ := fin σ2 d2 (F2.mono (fun y h => by omega) (fun j h => by omega)
      (fun b c h => h))
    simp only [ite_true]
    exact ⟨⟨e1, e2, e3, e4, e5, e6, hH2, hg2, e7, e8, pl, pr, pe⟩, dd, Ft⟩

set_option maxHeartbeats 8000000 in
/-- **`DataLO` holds**: the data of R14 LINE at `parN ne d n`. -/
theorem dataLO_holds : DataLO := by
  refine ⟨xdl, 1024, 3, ?_⟩
  intro d L X ℓa ℓ n m K0 E t ne cfg st Bp bp kp wh Dw σ hd hn hne hpar hL hlay hI h27 h28 h59 hkon bkp hDw0
    bDw h91 h31 hC hCa
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
  have hNe : 1 ≤ cfg.par.Ne := by rw [hpar]; exact hne
  have hRi : σ.sc sRint = (((cfg.par.Rint : ℕ) : ℤ) : ℝ) := by rw [cRint]; push_cast; rfl
  have bRi : |((cfg.par.Rint : ℕ) : ℤ)| ≤ 2 ^ E := bnd_sc (bsc sRint (by dgo)) hRi
  obtain ⟨Hh, eHq, hH, bH⟩ := DataP.slot_rat _ _ _ (bsc s2eh (by dgo)) c2eh
  have ePos : (0 : ℚ) < cfg.par.eHat⁻¹ := by rw [hpar]; exact parN_eHat_pos ne d n
  obtain ⟨hH0, heHat⟩ := DataP.eHat_int _ _ eHq ePos
  -- the fields on the grids
  have oEps : OnG cfg.par.pF cfg.par.eps := by rw [hpar]; exact tlN_onG_eps ne d n
  have oRho : OnG cfg.par.pF cfg.par.rho := by rw [hpar]; exact tlN_onG_rho ne d n
  have oSb : OnG cfg.par.pF cfg.par.sb := by rw [hpar]; exact parN_onG_sb ne d n
  have oR : OnG cfg.par.pF cfg.par.R := by rw [hpar]; exact parN_onG_R ne d n
  have hR0q : 0 < cfg.par.R := by rw [hpar]; exact parN_R_pos ne d n hd
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

end AdversarialBco.Unified.ProgO.TailD
