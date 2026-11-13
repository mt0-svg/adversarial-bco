/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataU
public import AdversarialBco.Bit.Transfer.XBLDataQ
public import AdversarialBco.Bit.Transfer.XBLData
public import AdversarialBco.Bit.Transfer.XBLSetupParV
public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.PieceA.Enc

@[expose] public section

/-!
# `DataT` holds

`xdt`: `xdtC` (the constants, `P`, `f`), then `xdtF` at the first round of an epoch (the slot `sFirst` holds `1`),
else `xdtA`. The values of the slots come from `BLInv` in mode `run`: the fields of PARAM on the grid `2^{-pF}`
(`ε'`, `η'`, `ρ'`, `s'_b`, rounded by PARAM), `k'` on the grid `2^{-p}`, `1/ê` an integer, `Λ = d N_e`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The call data of R11 TEST. -/
def xdt (L : Layout) : XCmd := .seq (xdtC L) (xifS L sZ sFirst (xdtF L) (xdtA L))

theorem dtF_le (d : ℕ) : dtFUnits d + 1 ≤ dtAUnits d + 2 := by
  simp only [dtFUnits, dtAUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, eF2, eF5, eA0, eA1,
    eA2, eA3, eA5]
  nlinarith [Nat.zero_le (d * d * d)]

theorem dt_le (d : ℕ) : dtCUnits d + (dtAUnits d + 2) ≤ 22 * d ^ 3 + 50 * d ^ 2 + 100 * d + 200 := by
  simp only [dtCUnits, dtAUnits, gramUnits, gOut, gIn, dot2Units, vecUnits, sixUnits, IE.units, ieF, eA0, eA1, eA2,
    eA3, eA5]
  ring_nf
  nlinarith [Nat.zero_le (d * d * d)]

/-- An integer slot value within the bound of `BLInv`. -/
theorem bnd_sc {σ : Env d} {y E : ℕ} {w : ℤ} (hb : ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ E) (hv : σ.sc y = w) :
    |w| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb
  have : w = z := by rw [hv] at hz; exact_mod_cast hz
  rw [this]; exact bz

/-- An integer cell within the bound of `BLInv`. -/
theorem bnd_arr {σ : Env d} {a k E : ℕ} {w : ℤ} (hb : ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E) (hv : σ.arr a k = w) :
    |w| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb
  have : w = z := by rw [hv] at hz; exact_mod_cast hz
  rw [this]; exact bz

/-- An integer over `2^k` lies on the grid `2^{-k}`. -/
theorem onG_int_div (k : ℕ) (z : ℤ) : OnG k ((z : ℚ) / 2 ^ k) := by
  unfold OnG qn; rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

theorem onG_up' (k : ℕ) (x : ℚ) : OnG k (up k x) := onG_int_div k _

theorem onG_dn' (k : ℕ) (x : ℚ) : OnG k (dn k x) := onG_int_div k _

/-- A field on the grid `2^{-k}` as its numerator over `2^k`. -/
theorem grid_div {k : ℕ} {x : ℚ} (h : OnG k x) : x = (qn k x : ℚ) / ((2 ^ k : ℤ) : ℚ) := by
  rw [Int.cast_pow, Int.cast_ofNat]; exact eq_qn_div k h

set_option maxHeartbeats 8000000 in
/-- **`DataT` holds.** -/
theorem dataT : DataT := by
  refine ⟨xdt, 1024, 3, ?_⟩
  intro d L X ℓa ℓ n m K0 E t cfg st Bp bp Gp σ hd hn hpar hL hlay hI h27 h28 h29 hC hCa
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
  have oEta : OnG cfg.par.pF cfg.par.eta := by rw [hpar, PieceA.par_eta]; exact onG_rnd_s _ _
  have oRho : OnG cfg.par.pF cfg.par.rho := by rw [hpar, PieceA.par_rho]; exact onG_dn' _ _
  have oSb : OnG cfg.par.pF cfg.par.sb := by rw [hpar, PieceA.par_sb]; exact onG_dn' _ _
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

end AdversarialBco.Bit.Transfer.BLM.DataM
