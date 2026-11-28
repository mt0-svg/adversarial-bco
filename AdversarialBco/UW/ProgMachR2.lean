/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachSplit
public import AdversarialBco.Unified.ProgOR2s

@[expose] public section

/-!
# R2 in mode `run` at BL-OW's round

The BL-OW copy of the specification of R2 (Unified/ProgOR2s.lean): the same command `xR2` and constants `kR2`, the proof
read at `RdW`. R2 reads four facts of PARAM: `R'` and `ε'`, `λ'` on the grid `2^{-pF}`, `qn R' ≥ 0`, and `ε' < 1` in
mode `run`. `R'` is BL-O's; `ε'` is rounded up and `λ'` to the nearest on the grid (`parOW_onG_eps`, `parOW_onG_lam`);
`ε' ≤ 1/2` in mode `run` by P5 MODE (`mode0O_run`).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Unified (inputU)
open AdversarialBco.UW.BLOW (parOW cfgWW modeOW_run)
open AdversarialBco.Bit.BLP (Cfg Mode St)
open AdversarialBco.Bit (gsm_prec)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- `ε'` of PARAM-W on the grid `2^{-pF}` (rounded up). -/
theorem parOW_onG_eps (d n : ℕ) (δ : ℚ) : OnG (parOW d n δ).pF (parOW d n δ).eps := onG_up _ _

/-- `λ'` of PARAM-W on the grid `2^{-pF}` (rounded to the nearest). -/
theorem parOW_onG_lam (d n : ℕ) (δ : ℚ) : OnG (parOW d n δ).pF (parOW d n δ).lam := onG_rnd_s _ _

set_option maxHeartbeats 40000000 in
/-- **R2 in mode `run`** at BL-OW's round. -/
theorem specR2W : SpecR2W (fun L => xR2 L) kR2 := by
  intro d R st σ0 σ hH hI hmo hA
  -- the layout
  have hNS : 771 ≤ R.L.NS := hH.room.1
  have hNN : 65 ≤ R.L.NN := hH.room.2.1
  have hNA : 52 ≤ R.L.NA := hH.room.2.2
  have hlay : BLLay R.L := ⟨by simp only [oE]; omega, by simp only [rEE]; omega, by simp only [aWE]; omega⟩
  have hL : LayOK R.L d R.ℓa := hH.lay
  have hd1 : 1 ≤ d := hH.inU.hd
  have hQ : qLay.OK R.L := ⟨⟨by simp [qLay], by simp only [qLay]; omega⟩, ⟨by simp [qLay], by simp only [qLay]; omega⟩,
    ⟨by simp [qLay], by simp only [qLay]; omega⟩⟩
  -- the exponents
  have hb : R.bud kR2 = 4000 * (R.W + R.E + 1) ^ 3 := by simp [RdW.bud, kR2]
  have hWE : R.W + R.E0 + 1 ≤ R.E := by have := hH.hE; simpa [kR2] using this
  have hdW : d ≤ R.W := by show d ≤ wU d R.n R.δ R.r0 R.R0 R.a; unfold wU; omega
  have hsW : sizeN R.δ R.r0 R.R0 R.a ≤ R.W := by show _ ≤ wU d R.n R.δ R.r0 R.R0 R.a; unfold wU; omega
  have hdE : d ≤ R.E := by omega
  have hE1 : 1 ≤ R.E := by omega
  have hℓ0 : 4000 * (R.W + R.E + 1) ^ 3 ≤ R.ℓ := hb ▸ hH.hℓ
  have hℓa0 : 4000 * (R.W + R.E + 1) ^ 3 < 2 ^ R.ℓa := hb ▸ hH.hℓa
  obtain ⟨x, hx⟩ : ∃ x, x = R.W + R.E + 1 := ⟨_, rfl⟩
  rw [← hx] at hℓ0 hℓa0
  have hEx : R.E + 2 ≤ x := by omega
  have hdx : d ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hxx : x ≤ x * x := Nat.le_mul_of_pos_left x hx1
  have hx3 : x * x ≤ x ^ 3 := by rw [show x ^ 3 = x * x * x by ring]; exact Nat.le_mul_of_pos_right _ hx1
  have hEd : R.E * d ≤ x * x := Nat.mul_le_mul (by omega) hdx
  have hLx : 1000 * (x * x) ≤ R.ℓ := by omega
  have hLa : 1000 * (x * x) < 2 ^ R.ℓa := by omega
  have hEpow : R.E < 2 ^ R.E := Nat.lt_two_pow_self
  -- the invariant before the round, through R1a
  obtain ⟨r0, -, -, r3, r4, -, -, -⟩ := hI.regs
  obtain ⟨c0, -, c2, c3, c4, -, -, -, c8⟩ := hI.consts
  obtain ⟨p0, p1, -, -, -, -, p6, -, -, -, -⟩ := hI.par
  obtain ⟨DS, hDS0, hDS, hmuS, hAS⟩ := hI.pos
  choose muS hmuS1 hmuS2 using hmuS
  choose aS haS1 haS2 using hAS
  obtain ⟨Dc, hDc0, hDc, hctr⟩ := hI.ctr
  choose Nc hNc1 hNc2 using hctr
  have hmode := hI.mode
  rw [hmo] at hmode
  obtain ⟨-, ⟨Dm, hDm0, hDm, hmu⟩, hAst, -⟩ := hmode.2
  choose mh hmh1 hmh2 using hmu
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hA.pers.1
  have eS : ∀ y < nSP, σ.sc y = σ0.sc y := hA.pers.2.1
  have eA : ∀ a < nAP, ∀ k, σ.arr a k = σ0.arr a k := hA.pers.2.2
  have scB : ∀ y < nSP, ∀ z : ℤ, σ0.sc y = z → |z| ≤ 2 ^ R.E := fun y hy z hz => by
    obtain ⟨z', e', b'⟩ := hI.bnd.1 y hy
    have : z = z' := by exact_mod_cast hz.symm.trans e'
    rw [this]; exact b'
  have arrB : ∀ a < nAP, ∀ k < asz d, ∀ z : ℤ, σ0.arr a k = z → |z| ≤ 2 ^ R.E := fun a ha k hk z hz => by
    obtain ⟨z', e', b'⟩ := hI.bnd.2 a ha k hk
    have : z = z' := by exact_mod_cast hz.symm.trans e'
    rw [this]; exact b'
  have hdl : ∀ i k : Fin d, d * i + k < asz d := idx_lt
  have hdl1 : ∀ k : Fin d, (k : ℕ) < asz d := idx1_lt
  have hdl2 : ∀ k : Fin d, (k : ℕ) + 1 < asz d := fun k => le_asz' hd1 k.2
  -- the values at R1a's end
  have vD : σ.nat rD = d := by rw [eN _ (by decide), r0]
  have v1 : σ.nat rOne = 1 := by rw [eN _ (by decide), r3]
  have vP : σ.nat rP = R.c.par.p := by rw [eN _ (by decide), r4]; rfl
  have vz : σ.sc sZ = 0 := by rw [eS _ (by decide), c0]
  have vA : ∀ i k : Fin d, σ.arr aA (d * i + k) = ((qn R.c.par.p (st.A i k) : ℤ) : ℝ) := fun i k => by
    rw [eA _ (by decide)]; exact (hAst i k).1
  have vAS : ∀ i k : Fin d, σ.arr aAS (d * i + k) = aS i k := fun i k => by rw [eA _ (by decide)]; exact haS1 i k
  have vmu : ∀ k : Fin d, σ.arr aMu k = mh k := fun k => by rw [eA _ (by decide)]; exact hmh1 k
  have vDm : σ.sc sDmu = Dm := by rw [eS _ (by decide), hDm]
  have vPF : σ.sc s2pF = ((2 ^ R.c.par.pF : ℤ) : ℝ) := by rw [eS _ (by decide), c3]; push_cast; rfl
  have vPq : σ.sc s2p = ((2 ^ R.c.par.p : ℤ) : ℝ) := by rw [eS _ (by decide), c2]; push_cast; rfl
  have vGs : σ.sc s2g = ((2 ^ (2 * gsm_prec R.c.par.B) : ℤ) : ℝ) := by rw [eS _ (by decide), c4]; push_cast; rfl
  have vlh : σ.sc sLamb = qn R.c.par.pF R.c.par.lam := by rw [eS _ (by decide)]; exact p1
  have veh : σ.sc sEps = qn R.c.par.pF R.c.par.eps := by rw [eS _ (by decide)]; exact p0
  have vR : σ.sc sR = qn R.c.par.pF R.c.par.R := by rw [eS _ (by decide)]; exact p6
  have vRi : σ.sc sRint = (R.c.par.Rint : ℝ) := by rw [eS _ (by decide)]; exact c8
  have vDS : σ.sc sDS = DS := by rw [eS _ (by decide), hDS]
  have vmuS : ∀ k : Fin d, σ.arr aMuS k = muS k := fun k => by rw [eA _ (by decide)]; exact hmuS1 k
  -- the bounds
  have bDS : |DS| ≤ 2 ^ R.E := scB sDS (by decide) _ hDS
  have bDm : |Dm| ≤ 2 ^ R.E := scB sDmu (by decide) _ hDm
  have bPF : |(2 : ℤ) ^ R.c.par.pF| ≤ 2 ^ R.E := scB s2pF (by decide) _ (by rw [c3]; push_cast; rfl)
  have bPq : |(2 : ℤ) ^ R.c.par.p| ≤ 2 ^ R.E := scB s2p (by decide) _ (by rw [c2]; push_cast; rfl)
  have bGs : |(2 : ℤ) ^ (2 * gsm_prec R.c.par.B)| ≤ 2 ^ R.E := scB s2g (by decide) _ (by rw [c4]; push_cast; rfl)
  have blh : |qn R.c.par.pF R.c.par.lam| ≤ 2 ^ R.E := scB sLamb (by decide) _ p1
  have beh : |qn R.c.par.pF R.c.par.eps| ≤ 2 ^ R.E := scB sEps (by decide) _ p0
  have bRn : |qn R.c.par.pF R.c.par.R| ≤ 2 ^ R.E := scB sR (by decide) _ p6
  have bRi : |(R.c.par.Rint : ℤ)| ≤ 2 ^ R.E := scB sRint (by decide) _ (by rw [c8]; push_cast; rfl)
  have hpE : R.c.par.p ≤ R.E := pow_two_le bPq
  have hgE : 2 * gsm_prec R.c.par.B ≤ R.E := pow_two_le bGs
  have bAh : ∀ i k, |qn R.c.par.p (st.A i k)| ≤ 2 ^ R.E := fun i k =>
    arrB aA (by decide) _ (hdl i k) _ (hAst i k).1
  have bAS : ∀ i k, |aS i k| ≤ 2 ^ R.E := fun i k => arrB aAS (by decide) _ (hdl i k) _ (haS1 i k)
  have bmh : ∀ k, |mh k| ≤ 2 ^ R.E := fun k => arrB aMu (by decide) _ (hdl1 k) _ (hmh1 k)
  have bmuS : ∀ k, |muS k| ≤ 2 ^ R.E := fun k => arrB aMuS (by decide) _ (hdl1 k) _ (hmuS1 k)
  have bDc : |Dc| ≤ 2 ^ R.E := arrB aC (by decide) 0 (le_asz' hd1 (by omega)) _ hDc
  have bNc : ∀ k, |Nc k| ≤ 2 ^ R.E := fun k => arrB aC (by decide) _ (hdl2 k) _ (hNc1 k)
  -- the inputs
  have hr0 : 0 < R.r0 := hH.inU.hr0
  have hR0 : 0 < R.R0 := lt_of_lt_of_le hr0 hH.inU.hR0
  have hrn : 0 < R.r0.num := Rat.num_pos.2 hr0
  have hR0n : 0 < R.R0.num := Rat.num_pos.2 hR0
  have hrd : (0 : ℤ) < R.r0.den := by exact_mod_cast R.r0.den_pos
  have hR0d : (0 : ℤ) < R.R0.den := by exact_mod_cast R.R0.den_pos
  have lenB : ∀ z : ℤ, len z ≤ R.E → z ≤ 2 ^ R.E := fun z hz =>
    le_of_abs_le ((abs_lt_two_pow_len z).le.trans (pow_le_pow_E hz))
  have hsE : sizeN R.δ R.r0 R.R0 R.a ≤ R.E := by omega
  have brn : R.r0.num ≤ 2 ^ R.E := lenB _ (by unfold sizeN at hsE; omega)
  have brd : (R.r0.den : ℤ) ≤ 2 ^ R.E := lenB _ (by unfold sizeN at hsE; omega)
  have bR0n : R.R0.num ≤ 2 ^ R.E := lenB _ (by unfold sizeN at hsE; omega)
  have bR0d : (R.R0.den : ℤ) ≤ 2 ^ R.E := lenB _ (by unfold sizeN at hsE; omega)
  have i4 : R.ctx.X.inp 4 = R.r0.num := by
    show inputU d R.n R.δ R.r0 R.R0 R.a ((4 : ℕ) : ℤ) = R.r0.num; simp [inputU]
  have i5 : R.ctx.X.inp 5 = R.r0.den := by
    show inputU d R.n R.δ R.r0 R.R0 R.a ((5 : ℕ) : ℤ) = R.r0.den; simp [inputU]
  have i6 : R.ctx.X.inp 6 = R.R0.num := by
    show inputU d R.n R.δ R.r0 R.R0 R.a ((6 : ℕ) : ℤ) = R.R0.num; simp [inputU]
  have i7 : R.ctx.X.inp 7 = R.R0.den := by
    show inputU d R.n R.δ R.r0 R.R0 R.a ((7 : ℕ) : ℤ) = R.R0.den; simp [inputU]
  have hoff : 8 ≤ R.ctx.X.off := by show 8 ≤ offU d; unfold offU; omega
  -- the parameters on their grids
  have hRg : OnG R.c.par.pF R.c.par.R := by
    show OnG (Unified.BudK.parK d R.n (kDel R.δ)).pF (Unified.BudK.parK d R.n (kDel R.δ)).R
    rw [Unified.PrmK.parK_R_eq]; exact onG_div_pow _ _
  have hRn0 : 0 ≤ qn R.c.par.pF R.c.par.R := by
    show 0 ≤ qn (Unified.BudK.parK d R.n (kDel R.δ)).pF (Unified.BudK.parK d R.n (kDel R.δ)).R
    rw [Unified.PrmK.qn_parK_R]; exact Unified.PrmK.RZK_nonneg
  have heps : OnG R.c.par.pF R.c.par.eps := parOW_onG_eps d R.n R.δ
  have hlam : OnG R.c.par.pF R.c.par.lam := parOW_onG_lam d R.n R.δ
  have he1 : R.c.par.eps < 1 := by
    obtain ⟨st0, h0⟩ := modeOW_run d R.n R.δ R.r0 R.R0 R.a R.w R.t st hmo
    have := (mode0O_run h0).2
    show (cfgWW d R.n R.δ R.r0 R.R0 R.a R.w).par.eps < 1
    linarith
  -- the exponents of the round
  have hdE2 : d ≤ 2 ^ R.E := hdE.trans hEpow.le
  have hRiN : R.c.par.Rint ≤ 2 ^ R.E := by
    have : ((R.c.par.Rint : ℕ) : ℤ) ≤ 2 ^ R.E := le_of_abs_le bRi
    exact_mod_cast this
  have bΓ : ∀ k, |R.Γ k| ≤ 2 ^ (2 * R.E) := fun k =>
    (gamI_abs_le _ _ _ _ _ _).trans (pow_le_pow_E (show 4 * gsm_prec R.c.par.B ≤ 2 * R.E by omega))
  obtain ⟨jG, hjGd⟩ : ∃ j, j = jGv R.c.par.p d R.c.par.Rint := ⟨_, rfl⟩
  have hjGle : jG ≤ 3 * R.E + 5 := by rw [hjGd]; exact jGv_le hdE hEpow hRiN hpE
  have hjGc : R.c.jG = jG := by
    rw [hjGd]; show R.c.par.p + 4 + Nat.clog 2 (2 * d * R.c.par.Rint) = _; unfold jGv; omega
  obtain ⟨kC', hkCd⟩ : ∃ k, k = cmcK R.c.par.p (6 * qn R.c.par.pF R.c.par.R * R.R0.num * R.r0.den * R.r0.den)
      (2 ^ R.c.par.pF * R.R0.den * R.r0.num * R.r0.num) := ⟨_, rfl⟩
  have hkCc : R.c.kC = kC' := (kC_eq R.c hRg hr0).trans hkCd.symm
  have aR0n : |R.R0.num| ≤ 2 ^ R.E := by rw [abs_of_pos hR0n]; exact bR0n
  have ard : |(R.r0.den : ℤ)| ≤ 2 ^ R.E := by rw [abs_of_pos hrd]; exact brd
  have hkCle : kC' ≤ 5 * R.E + 7 := by
    have hN : 0 ≤ 6 * qn R.c.par.pF R.c.par.R * R.R0.num * (R.r0.den : ℤ) * R.r0.den :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hRn0) hR0n.le) hrd.le) hrd.le
    have hD : (0 : ℤ) < 2 ^ R.c.par.pF * R.R0.den * R.r0.num * R.r0.num :=
      mul_pos (mul_pos (mul_pos (by positivity) hR0d) hrn) hrn
    have h6 : |(6 : ℤ)| ≤ 2 ^ 3 := by norm_num
    have hNG := le_of_abs_le ((abs_mul_pow (abs_mul_pow (abs_mul_pow (abs_mul_pow h6 bRn) aR0n) ard) ard).trans
      (pow_le_pow_E (show 3 + R.E + R.E + R.E + R.E ≤ 4 * R.E + 3 by omega)))
    have := cmcK_le (p := R.c.par.p) hN hD hNG
    rw [hkCd]; omega
  -- `D_X`, `X̂`, `Σ |X̂_k|`
  obtain ⟨DX, hDXd⟩ : ∃ D : ℤ, D = Dm * 2 ^ R.c.par.pF * 2 ^ R.c.par.p * 2 ^ (2 * gsm_prec R.c.par.B) :=
    ⟨_, rfl⟩
  have hDX0 : 0 < DX := by
    rw [hDXd]; exact mul_pos (mul_pos (mul_pos hDm0 (by positivity)) (by positivity)) (by positivity)
  have bDX : |DX| ≤ 2 ^ (4 * R.E) := by
    rw [hDXd]; exact (abs_mul_pow (abs_mul_pow (abs_mul_pow bDm bPF) bPq) bGs).trans (pow_le_pow_E (by omega))
  obtain ⟨xh, hxhd⟩ : ∃ x : Fin d → ℤ, x = xhI mh (fun i k => qn R.c.par.p (st.A i k)) R.Γ Dm (2 ^ R.c.par.pF)
      (2 ^ R.c.par.p) (2 ^ (2 * gsm_prec R.c.par.B)) (qn R.c.par.pF R.c.par.lam) := ⟨_, rfl⟩
  have up2 : ∀ {z : ℤ}, |z| ≤ 2 ^ R.E → |z| ≤ 2 ^ (2 * R.E) := fun h => h.trans (pow_le_pow_E (by omega))
  have hdE4 : d ≤ 2 ^ (2 * R.E) := hdE2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have bxh : ∀ k, |xh k| ≤ 2 ^ (5 * (2 * R.E) + 2) := fun k => by
    rw [hxhd]
    exact xhI_abs (fun i k => up2 (bAh i k)) bΓ (fun k => up2 (bmh k)) (up2 bDm) (up2 bPF) (up2 bPq) (up2 bGs)
      (up2 blh) hdE4 k
  have bS : |(∑ k, |xh k|)| ≤ 2 ^ (2 * (5 * (2 * R.E) + 2)) :=
    sum_abs_le bxh (hdE4.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hS0 : 0 ≤ ∑ k, |xh k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have b2S : |2 * (∑ k, |xh k|)| ≤ 2 ^ (20 * R.E + 5) :=
    (abs_mul_pow (show |(2 : ℤ)| ≤ 2 ^ 1 by norm_num) bS).trans (pow_le_pow_E (by omega))
  -- the test of the gauge
  obtain ⟨T, hTd⟩ : ∃ T : (Fin d → ℚ) → Bool, T = fun y => cmQ R.ctx.w.orc (ptDN Dc Nc)
      ((R.r0.num : ℚ) / ((R.r0.den : ℤ) : ℚ)) kC' (pmap DS muS aS y) := ⟨_, rfl⟩
  have hT : T = R.c.T R.w.orc R.c.kC 1 := by
    rw [hTd, hkCc]; funext y
    exact pmap_T R.w.orc R.c hDS0 (fun j => hmuS2 j) (fun i j => haS2 i j) (funext fun j => hNc2 j)
      (by push_cast; exact Rat.num_div_den R.r0) kC' y
  have hTB : Uni.TestOK R.L R.ctx R.ℓa R.ℓ (xtst R.L qLay aTP rGt)
      (TstDat qLay DS muS aS Dc Nc R.r0.num R.r0.den kC') aTP rGt (63 * R.E + 25) T (tstK d)
      (fun y => qLay.s + 16 ≤ y) (fun j => j = rGt ∨ (qLay.n + 1 ≤ j ∧ j < qLay.n + 11))
      (fun b _ => qLay.a ≤ b ∧ b < qLay.a + 4) := by
    rw [hTd]
    exact tstOK hL hQ (by show 34 < R.L.NA; omega) (by decide) (by show 41 < R.L.NN; omega) (by decide)
      (by decide) hd1 (m := R.E + 1) hDS0 ((le_of_abs_le bDS).trans (pow_le_pow_E (by omega)))
      (fun i => (bmuS i).trans (pow_le_pow_E (by omega))) (fun i j => (bAS i j).trans (pow_le_pow_E (by omega)))
      (hdE2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))) hDc0
      (lt_of_le_of_lt (le_of_abs_le bDc) (pow_lt_pow_E (by omega)))
      (fun i => lt_of_le_of_lt (bNc i) (pow_lt_pow_E (by omega)))
      hrn (lt_of_le_of_lt brn (pow_lt_pow_E (by omega))) hrd (lt_of_le_of_lt brd (pow_lt_pow_E (by omega)))
      (by omega) (by omega)
  have hgU : GaugeLay.OKU R.L gLay :=
    ⟨⟨by simp only [gLay, aXD, aA0, aTP]; omega, by decide, by simp only [gLay]; omega, by decide,
      by simp only [gLay, rJG, rGt]; omega, by decide⟩, by decide, by decide⟩
  have hDisj : GaugeDisjU gLay (fun y => qLay.s + 16 ≤ y) (fun j => j = rGt ∨ (qLay.n + 1 ≤ j ∧ j < qLay.n + 11))
      (fun b _ => qLay.a ≤ b ∧ b < qLay.a + 4) :=
    ⟨⟨fun y hy => by simp only [gLay, qLay] at hy ⊢; omega,
      fun j hj => by simp only [gLay, qLay, rGt, rJG] at hj ⊢; omega,
      fun b k hb => by simp only [gLay, qLay, aXD, aA0, aTP] at hb ⊢; omega⟩,
     fun j hj => by simp only [qLay, rGt] at hj; omega⟩
  have hStab := tstDat_stable (Q := qLay) (DS := DS) (muS := muS) (aS := aS) (Da := Dc) (Na := Nc)
    (rn := R.r0.num) (rd := R.r0.den) (k := kC') (S := fun y => gaugeS gLay y ∨ qLay.s + 16 ≤ y)
    (N := fun j => gaugeN gLay j ∨ (j = rGt ∨ (qLay.n + 1 ≤ j ∧ j < qLay.n + 11)))
    (Ar := fun b k => gaugeAr gLay b k ∨ (qLay.a ≤ b ∧ b < qLay.a + 4))
    (fun y hy => by simp only [gaugeS, gLay, qLay, sZ, sDS] at hy ⊢; omega)
    (fun j hj => by simp only [gaugeN, gLay, qLay, rGt, rD, rOne] at hj ⊢; omega)
    (fun b k hb => by simp only [gaugeAr, gLay, qLay, aTP, aMuS, aAS, aC] at hb ⊢; omega)
  -- the bounds of R2's last part
  have htG : tG d (6 * R.E) = 6 * (R.E * d) + 60 * R.E + 2 := by unfold tG; ring
  have bP2j : |(2 : ℤ) ^ jG| ≤ 2 ^ jG := by rw [abs_of_pos (by positivity)]
  have bF6 : |(2 : ℤ) ^ R.c.par.pF| ≤ 2 ^ (6 * R.E) := bPF.trans (pow_le_pow_E (by omega))
  have beh6 : |qn R.c.par.pF R.c.par.eps| ≤ 2 ^ (6 * R.E) := beh.trans (pow_le_pow_E (by omega))
  have bDS6 : |DS| ≤ 2 ^ (6 * R.E) := bDS.trans (pow_le_pow_E (by omega))
  have bDX6 : |DX| ≤ 2 ^ (4 * (6 * R.E)) := bDX.trans (pow_le_pow_E (by omega))
  have byv0 : ∀ k, |(aS *ᵥ xh) k| ≤ 2 ^ (R.E + (5 * (2 * R.E) + 2) + R.E) := fun k => mulVec_abs_le bAS bxh hdE2 k
  have byv : ∀ k, |(aS *ᵥ xh) k| ≤ 2 ^ (7 * (6 * R.E) + 2) := fun k => (byv0 k).trans (pow_le_pow_E (by omega))
  have bmu6 : ∀ k, |muS k| ≤ 2 ^ (6 * R.E) := fun k => (bmuS k).trans (pow_le_pow_E (by omega))
  have hℓp : 3 * (6 * R.E * d) + 33 * (6 * R.E) + 11 ≤ R.ℓ := by
    have : 6 * R.E * d = 6 * (R.E * d) := by ring
    rw [this]; omega
  have hξ : R.ξ = fun i => ((R.Γ i : ℤ) : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) :=
    congrArg Prod.fst (draw_eq R.w.cs R.K0 R.pB R.t)
  have hXpt : XO R.c st R.ξ = ptDN DX xh := by
    funext j
    show Bit.BLP.XQ (cfgV R.c) st R.ξ j = _
    rw [hξ, hDXd, hxhd]
    exact XQ_mach (cfgV R.c) st Dm mh R.Γ (2 * gsm_prec R.c.par.B) hDm0 (fun j => hmh2 j)
      (fun i k => (hAst i k).2) hlam j
  have hplay : R.play = playPtO R.w.orc R.c (.run st) R.ξ := by
    show playPtO R.w.orc R.c R.mo R.ξ = _; rw [hmo]
  -- the run
  unfold RdW.RunsO
  refine XVO.mono (K := (r2xUnits d + (200 * (R.E + 1) + ((20 * R.E + 40) + ((13 * d + 10) + 5)))) +
      (gaugeK d jG (tstK d) + (1 + (1 + r2pUnits d))))
    (XVO.seq (K₂ := gaugeK d jG (tstK d) + (1 + (1 + r2pUnits d))) (XVO.ofX (XV.r2pre (X := R.ctx.X) (σ := σ)
      (E := R.E) (Ah := fun i k => qn R.c.par.p (st.A i k)) (ASh := aS) (Γ := R.Γ) (mh := mh) (Dm := Dm)
      (PF := 2 ^ R.c.par.pF) (P := 2 ^ R.c.par.p) (G := 2 ^ (2 * gsm_prec R.c.par.B))
      (lh := qn R.c.par.pF R.c.par.lam) (Rn := qn R.c.par.pF R.c.par.R) (rn := R.r0.num) (rd := R.r0.den)
      (Rn0 := R.R0.num) (Rd0 := R.R0.den) (p := R.c.par.p) (Ri := R.c.par.Rint)
      hL hlay (by omega) (by omega) (by omega) vD v1 vz vP vA vAS hA.gam vmu vDm vPF vPq vGs vlh vR vRi
      i4 i5 i6 i7 hoff (by positivity) hrn hrd hR0n hR0d hRn0 bAh bAS bΓ bmh bDm bPF bPq bGs blh
      (le_of_abs_le bRn) brn brd bR0n bR0d hRiN hpE hdE hd1 (by omega) (by omega))) ?_)
    (by rw [hb, ← hx]; exact r2K_le hdx hEx hjGle) (fun _ h => h)
  intro σ1 hσ1
  obtain ⟨w1, x1, y1, q0, q1, q2, q3, j1, j2, v0, vX, vA0, vAz, hn1, hg1, hd1', d1, F1⟩ := hσ1
  have hdat : TstDat qLay DS muS aS Dc Nc R.r0.num R.r0.den kC' σ1 :=
    ⟨(F1.1 rD (by fdec)).trans vD, (F1.1 rOne (by fdec)).trans v1, (F1.2.1 sZ (by fdec)).trans vz,
      (F1.2.1 sDS (by fdec)).trans vDS, fun i => (F1.2.2.1 aMuS i (by fdec)).trans (vmuS i),
      fun i j => (F1.2.2.1 aAS _ (by fdec)).trans (vAS i j),
      ⟨(F1.2.2.1 aC 0 (by fdec)).trans (by rw [eA _ (by decide)]; exact hDc),
        fun i => (F1.2.2.1 aC _ (by fdec)).trans (by rw [eA _ (by decide), add_comm]; exact hNc1 i),
        q0, q1, q2.trans hkCd.symm, by rw [hkCd]; exact q3⟩⟩
  have h0 : σ1.nat 0 = d := (F1.1 0 (by fdec)).trans vD
  have hgr := gaugeBlockOKU R.L R.ctx R.ℓa R.ℓ gLay (xtst R.L qLay aTP rGt)
    (TstDat qLay DS muS aS Dc Nc R.r0.num R.r0.den kC') T (tstK d) (63 * R.E + 25)
    (fun y => qLay.s + 16 ≤ y) (fun j => j = rGt ∨ (qLay.n + 1 ≤ j ∧ j < qLay.n + 11))
    (fun b _ => qLay.a ≤ b ∧ b < qLay.a + 4) σ1 DX xh 1 0 (hnG (2 * ∑ k, |xh k|)) DX jG (20 * R.E + 6)
    hL hgU hd1 hTB hDisj hStab hdat h0 (by rw [hDXd]; exact v0) (fun i => by rw [hxhd]; exact vX i)
    (by rw [Int.cast_one]; exact vA0) (fun i => by rw [Pi.zero_apply, Int.cast_zero]; exact vAz i)
    (by rw [hxhd]; exact hg1) (by rw [hDXd]; exact hd1') (by rw [hjGd]; exact j1) (by rw [hjGd]; exact j2)
    hDX0 one_pos (hnG_pos _) hDX0 (lt_of_le_of_lt (le_of_abs_le bDX) (pow_lt_pow_E (by omega)))
    (fun i => lt_of_le_of_lt (bxh i) (pow_lt_pow_E (by omega))) (one_lt_pow₀ (by norm_num) (by omega))
    (fun i => by simp)
    (lt_of_le_of_lt (hnG_le (le_of_abs_le b2S)) (pow_lt_pow_E (by omega)))
    (lt_of_le_of_lt (le_of_abs_le bDX) (pow_lt_pow_E (by omega))) (by omega) (by omega) (by omega)
  refine XVO.seq hgr fun σ2 hσ2 => ?_
  obtain ⟨g1, F2, d2⟩ := hσ2
  obtain ⟨u, hud⟩ : ∃ u : ℤ, u = ((gaugeIt T (ptDN 1 0) (ptDN DX xh)
      (((hnG (2 * ∑ k, |xh k|) : ℤ) : ℚ) / (DX : ℚ)) jG jG).2 : ℤ) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hud]; positivity
  have hu1 : u ≤ 2 ^ jG := by rw [hud]; exact_mod_cast (gaugeIt_le T _ _ _ jG jG le_rfl).2
  have buj : |u| ≤ 2 ^ jG := by rw [abs_of_nonneg hu0]; exact hu1
  have hu2 : σ2.sc 303 = (u : ℝ) := by rw [hud, Int.cast_natCast]; exact g1
  have bHn : |2 * (∑ k, |xh k|)| ≤ 2 ^ tG d (6 * R.E) := b2S.trans (pow_le_pow_E (by omega))
  have bu : |u| ≤ 2 ^ tG d (6 * R.E) := buj.trans (pow_le_pow_E (by omega))
  have bP2 : |(2 : ℤ) ^ jG| ≤ 2 ^ tG d (6 * R.E) := bP2j.trans (pow_le_pow_E (by omega))
  have bN : |(2 * ∑ k, |xh k|) * u| ≤ 2 ^ tG d (6 * R.E) := (abs_mul_pow b2S buj).trans (pow_le_pow_E (by omega))
  have bDP : |DX * 2 ^ jG| ≤ 2 ^ tG d (6 * R.E) := (abs_mul_pow bDX bP2j).trans (pow_le_pow_E (by omega))
  refine XVO.mono (XVO.ofX (XV.r2post (X := R.ctx.X) hL hlay (σ := σ2) (Ep := 6 * R.E)
    (Hn := 2 * ∑ k, |xh k|) (u := u) (DX := DX) (P2 := 2 ^ jG) (F := 2 ^ R.c.par.pF)
    (eh := qn R.c.par.pF R.c.par.eps) (DS := DS) (yv := aS *ᵥ xh) (muS := muS)
    ((F2.1 _ (by fdec)).trans ((F1.1 _ (by fdec)).trans vD))
    ((F2.1 _ (by fdec)).trans ((F1.1 _ (by fdec)).trans v1))
    ((F2.2.1 _ (by fdec)).trans ((F1.2.1 _ (by fdec)).trans vz))
    ((F2.2.1 _ (by fdec)).trans (by rw [hxhd]; exact hn1))
    hu2
    ((F2.2.1 _ (by fdec)).trans (by rw [hDXd]; exact x1))
    ((F2.2.1 _ (by fdec)).trans (by rw [hjGd]; push_cast; exact j2))
    ((F2.2.1 _ (by fdec)).trans ((F1.2.1 _ (by fdec)).trans vPF))
    ((F2.2.1 _ (by fdec)).trans ((F1.2.1 _ (by fdec)).trans veh))
    ((F2.2.1 _ (by fdec)).trans ((F1.2.1 _ (by fdec)).trans vDS))
    (fun k => (F2.2.2.1 _ _ (by fdec)).trans (by rw [hxhd]; exact y1 k))
    (fun k => (F2.2.2.1 _ _ (by fdec)).trans ((F1.2.2.1 _ _ (by fdec)).trans (vmuS k)))
    bHn bu bP2 bN bDP bF6 beh6 bDS6 bDX6 byv bmu6 hd1 hℓp)) le_rfl fun σ3 hσ3 => ?_
  obtain ⟨p1, p2, p3, p4, d3, F3⟩ := hσ3
  -- BL-O's values
  have hg : ((((2 * ∑ k, |xh k|) * u : ℤ)) : ℚ) / ((DX * 2 ^ jG : ℤ) : ℚ) =
      gaugeP R.w.orc R.c (XO R.c st R.ξ) := by
    rw [hXpt, gaugeP_mach R.w.orc R.c hDX0 xh T hT, hjGc, hud]
  obtain ⟨hpN, hpD, hpt, hpl⟩ := playPtO_mach R.w.orc R.c st R.ξ DS DX ((2 * ∑ k, |xh k|) * u) (DX * 2 ^ jG)
    muS xh aS hDS0 hDX0 (mul_pos hDX0 (by positivity)) (fun j => hmuS2 j) (fun i j => haS2 i j)
    (fun j => congrFun hXpt j) hg heps he1
  have bpt := ptPair_abs (T := tG d (6 * R.E)) (E := 6 * R.E) bN bDP bF6 beh6
  -- the frames
  have sp1 : SamePers σ σ1 := SamePers.ofFrame F1 (fun y h => by simp only [SPre, sZeta, tR, nSP] at h ⊢; omega)
    (fun j h => by simp only [NPre, rD2] at h ⊢; omega) (fun a k h => by simp only [APre, aGam, nAP] at h ⊢; omega)
  have sp2 : SamePers σ1 σ2 := SamePers.ofFrame F2
    (fun y h => by simp only [gaugeS, gLay, qLay, nSP] at h ⊢; omega)
    (fun j h => by simp only [gaugeN, gLay, qLay, rGt] at h ⊢; omega)
    (fun a k h => by simp only [gaugeAr, gLay, qLay, aTP, nAP] at h ⊢; omega)
  have sp3 : SamePers σ2 σ3 := SamePers.ofFrame F3
    (fun y h => by simp only [SP, sBN, sBD, sPtN, sPtD, sC1, sC2, tR, nSP] at h ⊢; omega)
    (fun j h => by simp only [NP, rr, rk] at h ⊢; omega) (fun a k h => by simp only [AP, aPl, nAP] at h ⊢; omega)
  refine ⟨⟨⟨hA.pers.trans (sp1.trans (sp2.trans sp3)), by rw [F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1, hA.rounds],
      by rw [d3, d2, d1, hA.draws], fun i => (F3.2.2.1 _ _ (by fdec)).trans ((F2.2.2.1 _ _ (by fdec)).trans
        ((F1.2.2.1 _ _ (by fdec)).trans (hA.gam i)))⟩, ?_, ?_⟩, ⟨_, _, hpN, hpD, p1, p2, hpt,
      bpt.1.trans (pow_le_pow_E ?_), bpt.2.trans (pow_le_pow_E ?_)⟩,
    fun i => (F3.2.2.1 _ _ (by fdec)).trans ((F2.2.2.1 _ _ (by fdec)).trans (w1 i))⟩
  · refine ⟨_, mul_pos (mul_pos hDS0 hDX0) hpN, p3, fun j => ⟨_, by rw [add_comm]; exact p4 j, ?_⟩⟩
    rw [hplay]; exact (hpl j).symm
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [p3]
      exact int_lt_of_le ((abs_mul_pow (abs_mul_pow bDS bDX) bpt.1)) (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k : Fin d, 1 + (k : ℕ) = j := ⟨⟨j - 1, by omega⟩, by show 1 + (j - 1) = j; omega⟩
      rw [p4 k]
      have e1 := (abs_mul_pow (abs_mul_pow (bmuS k) bDX) bpt.1).trans
        (pow_le_pow_E (show R.E + 4 * R.E + (tG d (6 * R.E) + 6 * R.E + 1) ≤
          R.E + (5 * (2 * R.E) + 2) + R.E + (tG d (6 * R.E) + 6 * R.E + 1) by omega))
      exact int_lt_of_le (abs_add_pow e1 (abs_mul_pow (byv0 k) bpt.2)) (by omega)
  · rw [hb, ← hx]; omega
  · rw [hb, ← hx]; omega

theorem progR2W : ProgR2W := ⟨_, _, specR2W⟩

end AdversarialBco.UW.ProgW
