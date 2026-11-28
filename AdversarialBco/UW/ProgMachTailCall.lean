/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailSpec
public import AdversarialBco.UW.ProgMachR2
public import AdversarialBco.Unified.TailOCall

@[expose] public section

/-!
# One ELL-O call of BL-OW

The BL-OW copy of BL-O's ELL-O call (Unified/TailOCall.lean): the same command `xcallC xprep` and constants, at BL-OW's
configuration `cfgWW`. The call reads three facts of PARAM: `R'` on the grid `2^{-pF}` and `qn R' ≥ 0` (BL-O's `R'`,
which PARAM-W keeps) and `ε'` on the grid `2^{-pF}` (`parOW_onG_eps`). The main branch (Unified/TailOCallA.lean to
TailOCallT.lean) is generic in the configuration and reused.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Bit.Transfer.CallSz (pair_bound)
open AdversarialBco.Uni.EllO (abs_lt_ellOSz ellO_expos)
open AdversarialBco.Bit.RQ (clearQ)
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Unified (inputU)
open AdversarialBco.UW.BLOW (cfgWW)
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ callOf)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

set_option maxHeartbeats 16000000 in
/-- **One ELL-O call of BL-OW** (`CallW`). -/
theorem callW_holds : CallW := by
  obtain ⟨xprep, C2, k2, H2⟩ := PrepM.callPrepBL
  refine ⟨xcallC xprep, C2 + 10 ^ 31, k2 + 24, 983, 176, 46, ?_⟩
  intro d L w n δ r0 R0 a K0 E ℓa ℓ s t mo H g ℓq r P f e σ hIn hL hroom hInv hPrep hℓ hℓa
  obtain ⟨hS, hN, hA⟩ := hroom
  have hd1 := hIn.hd
  obtain ⟨wu, hwu⟩ : ∃ x, x = wU d n δ r0 R0 a := ⟨_, rfl⟩
  have hdw : d + 1 ≤ wu := by rw [hwu]; unfold wU; omega
  have hsw : sizeN δ r0 R0 a ≤ wu := by rw [hwu]; unfold wU; omega
  rw [← hwu] at hℓ hℓa ⊢
  obtain ⟨W, hW⟩ : ∃ x, x = wu + E + s + 1 := ⟨_, rfl⟩
  rw [← hW] at hℓ hℓa ⊢
  have hW1 : 1 ≤ W := by omega
  obtain ⟨V, hV⟩ : ∃ x, x = W ^ (k2 + 24) := ⟨_, rfl⟩
  rw [← hV] at hℓ hℓa ⊢
  have hCV : (C2 + 10 ^ 31) * V = C2 * V + 10000000000000000000000000000000 * V := by ring
  rw [hCV] at hℓ hℓa
  have hW24V : W ^ 24 ≤ V := hV ▸ Nat.pow_le_pow_right hW1 (by omega)
  have hWW24 : W ≤ W ^ 24 := Nat.le_self_pow (by norm_num) W
  have hW3 : W ≤ W ^ 3 := Nat.le_self_pow (by norm_num) W
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
  have hW324 : W ^ 3 ≤ W ^ 24 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hW23 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hprep : C2 * (d + s + 1) ^ k2 ≤ C2 * V :=
    Nat.mul_le_mul_left _ (hV ▸ (Nat.pow_le_pow_left (by omega) k2).trans (Nat.pow_le_pow_right hW1 (by omega)))
  set c := cfgWW d n δ r0 R0 a w with hc
  set XO := ctxU w n δ r0 R0 a with hXO
  -- BL's invariant
  have hI : BLInv L n 0 K0 E (cfgV c) mo t σ := hInv
  obtain ⟨vD, -, -, v1, vP, -, -, -⟩ := hI.regs
  obtain ⟨c0, -, c2, c3, -, -, -, -, -⟩ := hI.consts
  obtain ⟨p0, -, -, -, -, -, p6, -, -, -, -⟩ := hI.par
  obtain ⟨DS, hDS0, hDS, hmuS, hAS⟩ := hI.pos
  choose muS hmuS1 hmuS2 using hmuS
  choose aS haS1 haS2 using hAS
  obtain ⟨Da, hDa0, hDa, hctr⟩ := hI.ctr
  choose Na hNa1 hNa2 using hctr
  have scB : ∀ y < nSP, ∀ z : ℤ, σ.sc y = z → |z| ≤ 2 ^ E := fun y hy z hz => by
    obtain ⟨z', e', b'⟩ := hI.bnd.1 y hy
    have : z = z' := by exact_mod_cast hz.symm.trans e'
    rw [this]; exact b'
  have arrB : ∀ b < nAP, ∀ k < asz d, ∀ z : ℤ, σ.arr b k = z → |z| ≤ 2 ^ E := fun b hb k hk z hz => by
    obtain ⟨z', e', b'⟩ := hI.bnd.2 b hb k hk
    have : z = z' := by exact_mod_cast hz.symm.trans e'
    rw [this]; exact b'
  have bDS : |DS| ≤ 2 ^ E := scB sDS (by decide) _ hDS
  have bPF : |(2 : ℤ) ^ c.par.pF| ≤ 2 ^ E := scB s2pF (by decide) _ (by rw [c3]; push_cast; rfl)
  have bPq : |(2 : ℤ) ^ c.par.p| ≤ 2 ^ E := scB s2p (by decide) _ (by rw [c2]; push_cast; rfl)
  have beh : |qn c.par.pF c.par.eps| ≤ 2 ^ E := scB sEps (by decide) _ p0
  have bRn : |qn c.par.pF c.par.R| ≤ 2 ^ E := scB sR (by decide) _ p6
  have hpE : c.par.p ≤ E := pow_two_le bPq
  have bAS : ∀ i k, |aS i k| ≤ 2 ^ E := fun i k => arrB aAS (by decide) _ (idx_lt i k) _ (haS1 i k)
  have bmuS : ∀ k, |muS k| ≤ 2 ^ E := fun k => arrB aMuS (by decide) _ (idx1_lt k) _ (hmuS1 k)
  have bDa : |Da| ≤ 2 ^ E := arrB aC (by decide) 0 (le_asz' hd1 (by omega)) _ hDa
  have bNa : ∀ k, |Na k| ≤ 2 ^ E := fun k => arrB aC (by decide) _ (le_asz' hd1 k.2) _ (hNa1 k)
  -- the inputs
  have hr0 : 0 < r0 := hIn.hr0
  have hR0 : 0 < R0 := lt_of_lt_of_le hr0 hIn.hR0
  have hrn : 0 < r0.num := Rat.num_pos.2 hr0
  have hR0n : 0 < R0.num := Rat.num_pos.2 hR0
  have hrd : (0 : ℤ) < r0.den := by exact_mod_cast r0.den_pos
  have hR0d : (0 : ℤ) < R0.den := by exact_mod_cast R0.den_pos
  have lenB : ∀ z : ℤ, len z ≤ wu → z ≤ 2 ^ wu := fun z hz =>
    le_of_abs_le ((abs_lt_two_pow_len z).le.trans (pow_le_pow_E hz))
  have brn : r0.num ≤ 2 ^ wu := lenB _ (by unfold sizeN at hsw; omega)
  have brd : (r0.den : ℤ) ≤ 2 ^ wu := lenB _ (by unfold sizeN at hsw; omega)
  have bR0n : R0.num ≤ 2 ^ wu := lenB _ (by unfold sizeN at hsw; omega)
  have bR0d : (R0.den : ℤ) ≤ 2 ^ wu := lenB _ (by unfold sizeN at hsw; omega)
  have i4 : XO.X.inp 4 = r0.num := by show inputU d n δ r0 R0 a ((4 : ℕ) : ℤ) = r0.num; simp [inputU]
  have i5 : XO.X.inp 5 = r0.den := by show inputU d n δ r0 R0 a ((5 : ℕ) : ℤ) = r0.den; simp [inputU]
  have i6 : XO.X.inp 6 = R0.num := by show inputU d n δ r0 R0 a ((6 : ℕ) : ℤ) = R0.num; simp [inputU]
  have i7 : XO.X.inp 7 = R0.den := by show inputU d n δ r0 R0 a ((7 : ℕ) : ℤ) = R0.den; simp [inputU]
  have hoff : 8 ≤ XO.X.off := by show 8 ≤ offU d; unfold offU; omega
  -- PARAM on its grid
  have hRg : OnG c.par.pF c.par.R := by
    show OnG (Unified.BudK.parK d n (kDel δ)).pF (Unified.BudK.parK d n (kDel δ)).R
    rw [Unified.PrmK.parK_R_eq]; exact onG_div_pow _ _
  have hRn0 : 0 ≤ qn c.par.pF c.par.R := by
    show 0 ≤ qn (Unified.BudK.parK d n (kDel δ)).pF (Unified.BudK.parK d n (kDel δ)).R
    rw [Unified.PrmK.qn_parK_R]; exact Unified.PrmK.RZK_nonneg
  have heps : OnG c.par.pF c.par.eps := parOW_onG_eps d n δ
  -- the band offset `κ = kK`
  have hκ : c.kK = cmcK c.par.p (6 * qn c.par.pF c.par.R * R0.num * r0.den * r0.den)
      (2 ^ c.par.pF * R0.den * r0.num * r0.num) - c.par.p - 4 := by
    have e1 : c.kC = cmcK c.par.p (6 * qn c.par.pF c.par.R * R0.num * r0.den * r0.den)
        (2 ^ c.par.pF * R0.den * r0.num * r0.num) := kC_eq c hRg hr0
    have e2 : c.kC = c.par.p + c.kK + 4 := rfl
    omega
  have p2 : ∀ {z : ℤ} {a : ℕ}, z ≤ 2 ^ a → a ≤ W → z ≤ 2 ^ W := fun h ha => h.trans (pow_le_pow_E ha)
  have a2 : ∀ {z : ℤ} {a : ℕ}, |z| ≤ 2 ^ a → a ≤ W → |z| ≤ 2 ^ W := fun h ha => h.trans (pow_le_pow_E ha)
  have hκle : c.kK ≤ 4 * W + 3 := by
    have hN0 : 0 ≤ 6 * qn c.par.pF c.par.R * R0.num * (r0.den : ℤ) * r0.den :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hRn0) hR0n.le) hrd.le) hrd.le
    have hD0 : (0 : ℤ) < 2 ^ c.par.pF * R0.den * r0.num * r0.num :=
      mul_pos (mul_pos (mul_pos (by positivity) hR0d) hrn) hrn
    have h6 : |(6 : ℤ)| ≤ 2 ^ 3 := by norm_num
    have aR0n : |R0.num| ≤ 2 ^ W := by rw [abs_of_pos hR0n]; exact p2 bR0n (by omega)
    have ard : |(r0.den : ℤ)| ≤ 2 ^ W := by rw [abs_of_pos hrd]; exact p2 brd (by omega)
    have hNG := le_of_abs_le ((abs_mul_pow (abs_mul_pow (abs_mul_pow (abs_mul_pow h6 bRn) aR0n) ard) ard).trans
      (pow_le_pow_E (show 3 + E + W + W + W ≤ 4 * W + 3 by omega)))
    have := cmcK_leC (p := c.par.p) hN0 hD0 hNG
    omega
  -- the call
  obtain ⟨fH, fg, fl, fP, ff, fDf, fR, fr, fe, fDc, fNc, ferK⟩ := clearO_fields c H g ℓq r P f e
  set D := callO c H g ℓq r P f e with hDd
  set I := clearO D with hId
  have hsz : ellOSz I ≤ 2 * (d + 1) ^ 2 * (s + 1) + 2 := ellOSz_callO (L := L) hPrep
  have pr : r.den ≤ 2 ^ s ∧ r.num.natAbs ≤ 2 ^ s ∧ |r| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := hPrep.2.2.2.2.2.2.2.2.2.2.2.1
    exact pair_bound u v _ hv hu hvs huv
  -- the magnitudes
  have hds3 : 2 * (d + 1) ^ 2 * (s + 1) ≤ 2 * W ^ 3 :=
    calc 2 * (d + 1) ^ 2 * (s + 1) ≤ 2 * W ^ 2 * W :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)) (by omega)
      _ = 2 * W ^ 3 := by ring
  have hY16 : d + ellOSz I + c.kK + 1 ≤ 16 * W ^ 3 := by omega
  have hY8 : (d + ellOSz I + c.kK + 1) ^ 8 ≤ 4294967296 * W ^ 24 :=
    calc (d + ellOSz I + c.kK + 1) ^ 8 ≤ (16 * W ^ 3) ^ 8 := Nat.pow_le_pow_left hY16 8
      _ = 4294967296 * W ^ 24 := by ring
  have hY2 : (d + ellOSz I + c.kK + 1) ^ 2 ≤ 256 * W ^ 24 :=
    calc (d + ellOSz I + c.kK + 1) ^ 2 ≤ (16 * W ^ 3) ^ 2 := Nat.pow_le_pow_left hY16 2
      _ = 256 * W ^ 6 := by ring
      _ ≤ 256 * W ^ 24 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by norm_num))
  have hKt : tstCK d ≤ 151 * W ^ 2 := by
    have hdd : d * d ≤ W ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    rw [tstCK_eq]; omega
  have hZ8 : (d + ellOSz I + c.kK + tstCK d + 1) ^ 8 ≤ 1000000000000000000 * W ^ 24 :=
    calc (d + ellOSz I + c.kK + tstCK d + 1) ^ 8 ≤ (167 * W ^ 3) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      _ = 167 ^ 8 * W ^ 24 := by ring
      _ ≤ 1000000000000000000 * W ^ 24 := Nat.mul_le_mul_right _ (by norm_num)
  have hP1 : preC1K d W ≤ 60 * W := by unfold preC1K redUnits gcdUnits; omega
  have hP2 : preC2K W ≤ 413 * W := by unfold preC2K; omega
  have hsℓ : s < ℓ := by omega
  -- the preparation
  have hBL : BLLay L := ⟨by simp only [oE]; omega, by simp only [rEE]; omega, by simp only [aWE]; omega⟩
  refine XVO.mono (K := C2 * (d + s + 1) ^ k2 +
      ((preC1K d W + preC2K W + 10000000000 * (d + ellOSz I + c.kK + tstCK d + 1) ^ 8) + 4)) ?_
    (by rw [hCV]; omega) fun _ h => h
  refine XVO.seq (XVO.ofX (H2 d L XO.X ℓa ℓ s (cfgV c) H g ℓq r P f e σ hd1 hL hBL hPrep (by omega)
    (by omega))) fun σ1 ⟨hE1, d1, F1⟩ => ?_
  obtain ⟨-, -, e80, e81, e82, e83, e84, e85, e86, e87, eH, eg, eP, ef⟩ := hE1
  have kS : ∀ y, y < 80 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by simp only [SPrep, SRow, sEl]; omega)
  have kN : ∀ j, j < 32 → σ1.nat j = σ.nat j := fun j hj => F1.1 j (by simp only [NPrep, NRow]; omega)
  have kA : ∀ b k, b < 8 → σ1.arr b k = σ.arr b k := fun b k hb =>
    F1.2.2.1 b k (by simp only [APrep, ARow, aEH, aEf]; omega)
  have F1' : FrameA SCall NCall ACall σ σ1 :=
    F1.mono (fun _ h => Or.inr h) (fun _ h => Or.inr h) (fun _ _ h => Or.inr h)
  have z1 : σ1.sc sZ = 0 := by rw [kS _ (by decide), c0]
  have b0 : |σ1.sc sZ| < 2 ^ ℓ := by rw [z1, abs_zero]; positivity
  have v84 : σ1.sc 84 = (r.num : ℝ) := e84
  have b84 : |σ1.sc 84| < 2 ^ ℓ := by
    rw [v84]
    exact Unified.ProgO.absZ_lt (show |r.num| ≤ 2 ^ s by rw [Int.abs_eq_natAbs]; exact_mod_cast pr.2.1) hsℓ
  have v86 : σ1.sc 86 = (I.e.num : ℝ) := by rw [fe]; exact e86
  have b86 : |σ1.sc 86| < 2 ^ ℓ := by
    rw [v86]
    exact XV.abs_int_lt (lt_of_lt_of_le (abs_lt_ellOSz (e_num_le_mx I))
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  -- the output of a failed call
  have hfail : ∀ (_ : I.r ≤ 0 ∨ I.e ≤ 0), XRunsBO L XO ℓa ℓ (.base (toX (VL.sconst L oE ((0 : ℤ) : ℚ)))) σ1 1
      (fun σ' => EllOut blkBL (apI w.orc c D) (ellExpO I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA SCall NCall ACall σ σ') := fun h => by
    refine XVO.ofX (XV.mono (XV.constI hL (x := oE) (by simp only [oE]; omega) 0 (by rw [abs_zero]; positivity))
      le_rfl ?_)
    intro σ' e'
    subst e'
    have hn : apI w.orc c D = none := ellOI_none _ h
    refine ⟨by rw [hn]; show (σ1.setSc oE _).sc blkBL.o = 0; simp [blkBL], by simp [d1], ?_⟩
    exact F1'.setSc (x := oE) (Or.inl le_rfl) _
  by_cases hrp : 0 < r.num
  · by_cases hep : 0 < I.e.num
    · -- the main branch
      have hrpos : 0 < I.r := by
        rw [fr]; show 0 < r / 2; have := Rat.num_pos.1 hrp; linarith
      have hepos : 0 < I.e := Rat.num_pos.1 hep
      have heK : I.eK ≤ 135 * (d + ellOSz I + c.kK + 1) ^ 2 :=
        (ellO_expos I hd1 hrpos hepos (Y := d + ellOSz I + c.kK + 1) (by omega)).2.2.2.2.2.2.2.2.1
      have hc84 : σ1.sc sZ < σ1.sc 84 := by rw [z1, v84]; exact_mod_cast hrp
      have hc86 : σ1.sc sZ < σ1.sc 86 := by rw [z1, v86]; exact_mod_cast hep
      have hrq : |r.num| ≤ 2 ^ W := by
        rw [Int.abs_eq_natAbs]
        exact (show ((r.num.natAbs : ℕ) : ℤ) ≤ 2 ^ s by exact_mod_cast pr.2.1).trans (pow_le_pow_E (by omega))
      have hrqd : (r.den : ℤ) ≤ 2 ^ W :=
        (show (r.den : ℤ) ≤ 2 ^ s by exact_mod_cast pr.1).trans (pow_le_pow_E (by omega))
      have hmain := XVO.callMain (XO := XO) (ℓa := ℓa) (ℓ := ℓ) (σ := σ1) hL (by omega) (by omega) (by omega) hd1
        (I := I) (rq := r)
        (DS := DS) (PF := 2 ^ c.par.pF) (eh := qn c.par.pF c.par.eps) (Rn := qn c.par.pF c.par.R)
        (Da := Da) (rn := r0.num) (rd := r0.den) (Rn0 := R0.num) (Rd0 := R0.den) (muS := muS) (aS := aS) (Na := Na)
        (p := c.par.p) (m := W) (κ := c.kK) i4 i5 i6 i7 hoff
        (by rw [kN _ (by decide)]; exact vD) (by rw [kN _ (by decide)]; exact v1)
        (by rw [kN _ (by decide)]; exact vP) z1
        (by rw [kS _ (by decide), c3]; push_cast; rfl)
        (by rw [kS _ (by decide)]; exact p0) (by rw [kS _ (by decide)]; exact p6)
        (by rw [kS _ (by decide)]; exact hDS)
        (fun j => by rw [kA _ _ (by decide)]; exact hmuS1 j)
        (fun i j => by rw [kA _ _ (by decide)]; exact haS1 i j)
        (by rw [kA _ _ (by decide)]; exact hDa)
        (fun j => by rw [kA _ _ (by decide), add_comm]; exact hNa1 j)
        ⟨by rw [fl]; exact e80, by rw [fDf]; exact e81, by rw [fR]; exact e82, by rw [fR]; exact e83, e84, e85,
          by rw [fe]; exact e86, by rw [fe]; exact e87, fun i j => by rw [fH]; exact eH i j,
          fun j => by rw [fg]; exact eg j, fun i j => by rw [fP]; exact eP i j, fun j => by rw [ff]; exact ef j⟩
        fr fDc fNc ferK hκ hrn hrd hR0n hR0d hRn0 (by positivity) hDS0 hDa0
        (p2 brn (by omega)) (p2 brd (by omega)) (p2 bR0n (by omega)) (p2 bR0d (by omega))
        (p2 (le_of_abs_le bRn) (by omega)) (p2 (le_of_abs_le bPF) (by omega)) (a2 beh (by omega))
        (a2 bDS (by omega)) (fun j => a2 (bmuS j) (by omega)) (fun i j => a2 (bAS i j) (by omega))
        (a2 bDa (by omega)) (fun j => a2 (bNa j) (by omega)) hrq hrqd
        ((show d ≤ W by omega).trans Nat.lt_two_pow_self.le) (by omega) (by omega) (by omega) (by omega)
      refine XVO.mono (XVO.ifS_t hL (by simp only [sZ]; omega) (by omega) b0 b84 hc84
        (XVO.ifS_t hL (by simp only [sZ]; omega) (by omega) b0 b86 hc86 hmain)) (by omega) ?_
      rintro σ' ⟨o', d', F'⟩
      have hT : tstF XO DS (2 ^ c.par.pF) (qn c.par.pF c.par.eps) Da muS aS Na r0.num r0.den (I.eK + c.kK) =
          tstO w.orc c D := by
        funext y
        unfold tstF tstO
        exact pmapC_T w.orc c hDS0 hmuS2 haS2 (funext fun j => hNa2 j)
          (by push_cast; exact Rat.num_div_den r0) (scale_eq heps) _ y
      rw [hT] at o'
      refine ⟨eout_of o', by rw [d', d1], F1'.trans (F'.mono ?_ ?_ ?_)⟩
      · exact fun _ h => Or.elim h (fun h => Or.inr (Or.inr h)) Or.inl
      · intro j h; simp only [NCall, NPrep, NRow, rEE]; omega
      · exact fun _ _ h => Or.elim h (fun h => Or.inr (Or.inr h)) Or.inl
    · -- `e ≤ 0`
      have hc84 : σ1.sc sZ < σ1.sc 84 := by rw [z1, v84]; exact_mod_cast hrp
      have hc86 : ¬ σ1.sc sZ < σ1.sc 86 := by rw [z1, v86]; exact_mod_cast hep
      exact XVO.mono (XVO.ifS_t hL (by simp only [sZ]; omega) (by omega) b0 b84 hc84
        (XVO.ifS_f hL (by simp only [sZ]; omega) (by omega) b0 b86 hc86
          (hfail (Or.inr (Rat.num_nonpos.1 (not_lt.1 hep)))))) (by omega) fun _ h => h
  · -- `r ≤ 0`
    have hc84 : ¬ σ1.sc sZ < σ1.sc 84 := by rw [z1, v84]; exact_mod_cast hrp
    have hr0' : I.r ≤ 0 := by
      rw [fr]; show r / 2 ≤ 0; have := Rat.num_nonpos.1 (not_lt.1 hrp); linarith
    exact XVO.mono (XVO.ifS_f hL (by simp only [sZ]; omega) (by omega) b0 b84 hc84 (hfail (Or.inl hr0')))
      (by omega) fun _ h => h

end AdversarialBco.UW.ProgW
