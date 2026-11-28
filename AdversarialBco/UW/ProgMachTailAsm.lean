/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailHead
public import AdversarialBco.UW.ProgTextR5w
public import AdversarialBco.Unified.TailOAsm

@[expose] public section

/-!
# `ProgTailW` from the tail's sub-block contracts

The BL-OW copy of BL-O's tail (Unified/TailOAsm.lean). The tail command `xtailFW`: BL-O's first line `xR57` at the
reading, R5w (`xR5w`, UW/ProgTextR5w.lean), which reads `b̂0`, `ŷ0` from the cells `CellsW` and re-encodes the
reading as `(ζ, pt_N, pt_D, obs) = (0, 1, 1, 2Ŷ^w)`, then `xR57` again at the re-encoded reading, R7's tests, R7 to R9
and the tail (`xRunTO`). By `yHat_reenc` the second line holds `Ŷ^w` where BL-O's holds `Ŷ`, and by `stepOW_dither`
the step `stepO` at the dither `ζ_W` of UW/ProgLinkStep.lean is BL-OW's `stepOW`, so `XVO.runTW` ends in BL-OW's
invariant before round `t + 1`; the cells pass every block (`Keep01` and the frames).

* `ywI_abs`: `|Ŷ^w| ≤ |ŷ0|`;
* `rY_cfgH`: R5 of the head is `yObs` at the gauge play's scale;
* `tl_newW`: the hypothesis `hnew` of `XVO.runTW` from `MagBLW`, `ExpBLW`, at any dither where `stepO` is `modeOW`;
* `asm_arithW`: the budget of `xtailFW`;
* `progTailW_of`: `ProgTailW` from `MagBLW`, `ExpBLW` and the four sub-block contracts.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (parOW cfgWW modeOW modeOW_succ b0OW y0OW ywQ)
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- **R5 to R15 of BL-OW in mode `run`**: BL-O's first line at the reading, R5w, the first line at the re-encoded
reading, then R7's tests, R7 to R9 and the tail. -/
def xtailFW (xdt : Layout → XCmd) (xcall : Layout → XCmdO) (xfire xdl xcom : Layout → XCmd) (L : Layout) :
    XCmdO :=
  .seq (.base (xR57 L)) (.seq (.base (xR5w L)) (.seq (.base (xR57 L)) (xRunTO (xtailO xdt xcall xfire xdl xcom) L)))

/-- `|Ŷ^w| ≤ |ŷ0|`: the weight lies in `[0, 1]` and the clip in `[-|ŷ0|, |ŷ0|]`. -/
theorem ywI_abs (Y Bn Yn Q G GG : ℤ) (h : 0 < Q * G * G) : |ywI Y Bn Yn Q G GG| ≤ |Yn| := by
  unfold ywI
  have hφ := phI_eq Bn Q G GG
  have hφ0 : 0 ≤ phI Bn Q G GG := by rw [hφ]; exact le_min h.le (le_max_left _ _)
  have hφM : phI Bn Q G GG ≤ Q * G * G := by rw [hφ]; exact min_le_left _ _
  have hcl : |clI Y Yn| ≤ |Yn| := by
    rw [clI_eq, abs_le]
    exact ⟨le_max_of_le_left (neg_le_neg (le_abs_self Yn)),
      max_le (neg_le_abs Yn) ((min_le_left _ _).trans (le_abs_self Yn))⟩
  generalize phI Bn Q G GG = φ at hφ0 hφM ⊢
  generalize clI Y Yn = c at hcl ⊢
  generalize Q * G * G = M at h hφM ⊢
  have hA : 0 ≤ |Yn| := abs_nonneg _
  obtain ⟨hc1, hc2⟩ := abs_le.1 hcl
  have u1 : φ * c ≤ M * |Yn| := by
    nlinarith [mul_le_mul_of_nonneg_left hc2 hφ0, mul_le_mul_of_nonneg_right hφM hA]
  have u2 : -(M * |Yn|) ≤ φ * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc1 hφ0, mul_le_mul_of_nonneg_right hφM hA]
  rw [abs_le]
  constructor
  · exact Int.le_ediv_of_mul_le (by omega) (by nlinarith)
  · have := Int.ediv_lt_of_lt_mul (by omega : 0 < M + M)
      (show φ * c + φ * c + M < (|Yn| + 1) * (M + M) by nlinarith)
    omega

/-- R5 of the head at `cfgH` is `yObs` at the gauge play's scale `pt'`. -/
theorem rY_cfgH (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    rY (cfgH orc c st ξ) st ξ ζ obs = yObs c.par (ptO orc c (XO c st ξ)) ζ obs := by
  rw [ptO_eq]; rfl

set_option maxHeartbeats 4000000 in
/-- **The bounds of the new state and of R14's point** for `XVO.runTW`, at any dither `ζ` where `stepO` is BL-OW's
next mode. -/
theorem tl_newW {Cm km Cx kx : ℕ}
    (hM : ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 → ∀ w : WorldO d,
      PosBnd (cfgV (cfgWW d n δ r0 R0 a w)) E0 → ∀ (t : ℕ) (st : St d), t ≤ n →
        modeOW d n δ r0 R0 a w t = .run st →
          StBnd (parOW d n δ).p (Cm * (wU d n δ r0 R0 a + E0 + 1) ^ km) (parOW d n δ).Rint st)
    (hX : ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ)
      (g : Fin d → ℚ) (ℓq : ℚ) (Bp : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (r e : ℚ),
      InU d n δ r0 R0 → c.par = parOW d n δ → (∀ i j, OnG (parOW d n δ).p (Bp i j)) →
      frob2 Bp ≤ 2 * (parOW d n δ).Lam → (∀ j, |f j| ≤ 2 ^ E0) → (r, e) ∈ callRE (parOW d n δ) d n →
        ellExpO (clearO (callO c H g ℓq r (Bp * Bpᵀ) f e)) ≤ Cx * (wU d n δ r0 R0 a + E0 + 1) ^ kx)
    {R : RdW d} {st : St d} {ζ : ℚ} (hIn : InU d R.n R.δ R.r0 R.R0) (hpos : PosBnd (cfgV R.c) R.E0)
    (ht : R.t < R.n)
    (e : modeOW d R.n R.δ R.r0 R.R0 R.a R.w (R.t + 1) =
      Unified.BLO.stepO R.w.orc R.c R.n (.run st) R.ξ ζ R.obs)
    (hE1 : Cm * (R.W + R.E0 + 1) ^ km ≤ R.E)
    (hE2 : Cx * (R.W + (5 * (2 * Unified.MagO.Ku d R.n (kDel R.δ) + 10) + 5) + 1) ^ kx +
      Unified.MagO.Ku d R.n (kDel R.δ) ≤ R.E) :
    ∀ mu' : Fin d → ℚ, Unified.BLO.stepO R.w.orc R.c R.n (.run st) R.ξ ζ R.obs =
        .run ⟨false, mu', rA' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs, rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs,
          rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs, rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs,
          rG' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs, rl' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs⟩ →
      StBnd R.c.par.p R.E R.c.par.Rint ⟨false, mu', rA' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs,
          rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs, rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs,
          rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs, rG' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs,
          rl' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs⟩ ∧
      ∀ x, apI R.w.orc R.c (callLO R.c R.n (rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs)
          (rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs) (rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs)
          (rwmu (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs)) = some x →
        (∀ j, |x j| ≤ 2 ^ R.E) ∧ ellExpO (clearO (callLO R.c R.n
          (rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs) (rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs)
          (rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs)
          (rwmu (cfgH R.w.orc R.c st R.ξ) st R.ξ ζ R.obs))) ≤ R.E := by
  intro mu' hs
  have hd := hIn.hd
  have hn := hIn.hn
  refine ⟨StBnd_mono (hM d R.n R.E0 R.δ R.r0 R.R0 R.a hIn R.w hpos (R.t + 1) _ ht (e.trans hs)) hE1, ?_⟩
  intro x hx
  set H := cfgH R.w.orc R.c st R.ξ with hH
  obtain ⟨hF, hWm⟩ := run_factsO hs rfl
  obtain ⟨-, hdT, -, -, -, -, -, -, -, hLam, -, -, hRint, -⟩ := Unified.MagO.fld_unit d R.n (kDel R.δ) hd hn
  obtain ⟨hW0, hW1⟩ := W_bndK d R.n (kDel R.δ) hd hn
  set K := Unified.MagO.Ku d R.n (kDel R.δ) with hK
  have pK : (2 : ℚ) ^ K ≤ 2 ^ (2 * K + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf : ∀ j, |((rB' H st R.ξ ζ R.obs * (rB' H st R.ξ ζ R.obs)ᵀ) *ᵥ rwmu H st R.ξ ζ R.obs) j| ≤
      2 ^ (5 * (2 * K + 10) + 5) :=
    f_abs _ _ R.c.par.Lam R.c.par.W (2 * K + 10) hF (hLam.trans pK) (fun j => hb_wmu _ _ hWm j)
      ((le_of_eq (abs_of_nonneg hW0)).trans hW1) (hdT.trans pK)
  have hexp : ellExpO (clearO (callLO R.c R.n (rB' H st R.ξ ζ R.obs) (rb' H st R.ξ ζ R.obs)
      (rk' H st R.ξ ζ R.obs) (rwmu H st R.ξ ζ R.obs))) ≤
      Cx * (R.W + (5 * (2 * K + 10) + 5) + 1) ^ kx :=
    hX d R.n (5 * (2 * K + 10) + 5) R.δ R.r0 R.R0 R.a R.c _ _ _ (rB' H st R.ξ ζ R.obs) _ _ _ hIn rfl
      (fun i j => onG_rnd_s _ _) hF hf
      (by unfold callRE; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))
  have hle : ellExpO (clearO (callLO R.c R.n (rB' H st R.ξ ζ R.obs) (rb' H st R.ξ ζ R.obs)
      (rk' H st R.ξ ζ R.obs) (rwmu H st R.ξ ζ R.obs))) + K ≤ R.E := by omega
  refine ⟨fun j => (apI_abs hx (E := K) (by show ((R.c.par.Rint : ℕ) : ℚ) ≤ 2 ^ K; exact hRint) j).trans
    (pow_le_pow_right₀ (by norm_num) hle), by omega⟩

/-- `r5wUnits` is the constant `84`. -/
theorem r5wUnits_eq (U : ℕ) : r5wUnits U = 84 := by
  unfold r5wUnits
  rw [show SL.unitsP slWEt slW = (0, 75) from rfl]
  simp only [ev]
  omega

/-- The budget of `xtailFW` and the conditions of `XV.r57`, `XV.r5w` and `XVO.runTW` below `C (W + E + U + 1)^k`. -/
theorem asm_arithW (Ct kt W E U d : ℕ) (hdW : d ≤ W) :
    r57Units d (2 * E + U + 8) + (r5wUnits (2 * E + U + 8) + (r57Units d (2 * E + U + 8) +
      (2 + (2 + (midUnits d (2 * E + U + 8) + Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt))))) ≤
        (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    130 * (2 * E + U + 8) + 120 < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    d * d + d < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) := by
  obtain ⟨-, h2, h3, h4⟩ := asm_arith Ct kt W E U d hdW
  refine ⟨?_, h2, h3, h4⟩
  set X := W + E + U + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hX2 : X ^ 2 ≤ X ^ (kt + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hXk : X ^ kt ≤ X ^ (kt + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have h9 : d + (2 * E + U + 8) + 1 ≤ 9 * X := by omega
  have h400 : W + (36 * (2 * E + U + 8) + 30) + 1 ≤ 400 * X := by omega
  have h57 := units_r57 d (2 * E + U + 8)
  have hmid : midUnits d (2 * E + U + 8) ≤ 81000 * X ^ 2 := by
    have := (units_mid d (2 * E + U + 8)).trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left h9 2))
    calc midUnits d (2 * E + U + 8) ≤ 1000 * (9 * X) ^ 2 := this
      _ = 81000 * X ^ 2 := by ring
  have hct : Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ Ct * 400 ^ kt * X ^ (kt + 2) := by
    calc Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ Ct * (400 * X) ^ kt :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h400 _)
      _ = Ct * 400 ^ kt * X ^ kt := by rw [mul_pow, mul_assoc]
      _ ≤ Ct * 400 ^ kt * X ^ (kt + 2) := Nat.mul_le_mul_left _ hXk
  have hK : (10 ^ 6 + Ct * 400 ^ kt) * X ^ (kt + 2) = 10 ^ 6 * X ^ (kt + 2) + Ct * 400 ^ kt * X ^ (kt + 2) := by
    ring
  rw [hK, r5wUnits_eq]
  omega

set_option maxHeartbeats 16000000 in
/-- **`ProgTailW`**: R5 to R15 of BL-OW's round in mode `run`, from BL-OW's magnitudes, its exponent contract and the
tail's sub-block contracts. -/
theorem progTailW_of (hM : MagBLW) (hX : ExpBLW) (hdt : DataTW) (hdl : DataLW) (hfi : FireW) (hca : CallW) :
    ProgTailW := by
  obtain ⟨Cm, km, hM⟩ := hM
  obtain ⟨Cx, kx, hX'⟩ := id hX
  obtain ⟨xdt, Ct, kt, hdt⟩ := hdt
  obtain ⟨xdl, Cl, kl, hdl⟩ := hdl
  obtain ⟨xfire, Cf, kf, hfire⟩ := hfi
  obtain ⟨xcall, Ca, ka, nS, nN, nA, hcall⟩ := hca
  obtain ⟨xcom, Cc, kc, hcom⟩ := commitBL
  obtain ⟨Ct', kt', hTail⟩ := tailOKW_of hX hdt hfire hdl hcall hcom
  refine ⟨xtailFW xdt xcall xfire xdl xcom,
    ⟨10 ^ 6 + Ct' * 400 ^ kt', kt' + 2, Cm + Cx * 5400 ^ kx + 600, km + kx + 1, nS + 771, nN + 65, nA + 34⟩, ?_⟩
  intro d R st U σ0 σ hH hI hC hmo hP
  obtain ⟨hIn, ht, hL, hroom, hpos, hE, hℓ, hℓa⟩ := hH
  dsimp only at hE hℓ hℓa hroom
  have hd := hIn.hd
  have hdW := d_le_WW R
  have hP' := parT_rd R hIn
  have hKW : Unified.MagO.Ku d R.n (kDel R.δ) ≤ 528 * R.W :=
    Unified.MagO.Ku_le d R.n R.δ R.r0 R.R0 R.a hIn.hδ0
  obtain ⟨hE1, hE2, hdE⟩ := asm_E Cm km Cx kx R.W R.E0 R.E (Unified.MagO.Ku d R.n (kDel R.δ)) d hdW hKW hE
  obtain ⟨hB1, hB2, hB3, hB4⟩ := asm_arithW Ct' kt' R.W R.E U d hdW
  obtain ⟨hr1, hr2, hr3⟩ := hroom
  have hlay : BLLay R.L := by
    unfold BLLay; simp only [oE, rEE, aWE]; omega
  have hroom' : RoomO R.L nS nN nA := ⟨by omega, by omega, by omega⟩
  have hI0 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) R.t σ0 := by
    have h := hI; unfold RdW.Inv BLOInv at h; rw [hmo] at h; exact h
  have hI1 := hI0.ofPers hP.pers hP.rounds hP.draws
  have hC1 : CellsW σ R.n R.δ :=
    hC.congr (hP.pers.2.2 aMuS (by decide) d) (hP.pers.2.2 aAS (by decide) (d * d))
  obtain ⟨r0', -, -, r3', -⟩ := hI1.regs
  obtain ⟨c0', -, c2p', c2pF', c2g', -⟩ := hI1.consts
  obtain ⟨p0', -, -, -, p4', -⟩ := hI1.par
  obtain ⟨⟨pN, pD, hpN, hpD, epN, epD, hpt, bpN, bpD⟩, aWv1⟩ := hP.dat
  -- the bounds, at `G' = 2E + U + 8`
  have hU2 : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hEU : R.E ≤ 2 * R.E + U + 8 := by omega
  have bsc : ∀ {y : ℕ} {z : ℤ}, y < nSP → σ.sc y = z → |z| ≤ 2 ^ (2 * R.E + U + 8) := fun hy hz =>
    (hI1.sc_abs hy hz).trans (hU2 hEU)
  have hpE : R.c.par.p ≤ R.E :=
    pow_two_le (hI1.sc_abs (y := s2p) (by decide) (by rw [c2p']; push_cast; rfl))
  have hpFE : R.c.par.pF ≤ R.E :=
    pow_two_le (hI1.sc_abs (y := s2pF) (by decide) (by rw [c2pF']; push_cast; rfl))
  have hgE : 2 * gsm_prec R.pB ≤ R.E :=
    pow_two_le (hI1.sc_abs (y := s2g) (by decide) (by rw [c2g']; push_cast; rfl))
  have bQ : |(2 : ℤ) ^ R.c.par.p| ≤ 2 ^ (2 * R.E + U + 8) :=
    bsc (y := s2p) (by decide) (by rw [c2p']; push_cast; rfl)
  have bF : |(2 : ℤ) ^ R.c.par.pF| ≤ 2 ^ (2 * R.E + U + 8) :=
    bsc (y := s2pF) (by decide) (by rw [c2pF']; push_cast; rfl)
  have bG : |(2 : ℤ) ^ (2 * gsm_prec R.c.par.B)| ≤ 2 ^ (2 * R.E + U + 8) :=
    bsc (y := s2g) (by decide) (by rw [c2g']; push_cast; rfl)
  have bE : |qn R.c.par.pF R.c.par.eps| ≤ 2 ^ (2 * R.E + U + 8) := bsc (by decide) p0'
  have bK : |qn R.c.par.pF R.c.par.kapc| ≤ 2 ^ (2 * R.E + U + 8) := bsc (by decide) p4'
  have bΓ : ∀ i : Fin d, |R.Γ i| ≤ 2 ^ (2 * R.E + U + 8) := fun i =>
    (gamI_abs_le _ _ _ _ _ _).trans (hU2 (by omega))
  have bZ : |R.gz| ≤ 2 ^ (2 * R.E + U + 8) := (zetI_abs_le _ _ _ _ _).trans (hU2 (by omega))
  have hq : R.c.qO ≤ 2 * R.E + U + 8 := by
    have h1 := Unified.MagO.qO_le (d := d) { R.c with par := parO d R.n R.δ } d R.n (kDel R.δ) hd rfl rfl
    have h2 : Unified.MagO.Ku d R.n (kDel R.δ) = R.c.par.pF + 8 := rfl
    have h3 : ({ R.c with par := parO d R.n R.δ } : CfgO d).qO = R.c.qO := rfl
    have h4 : ({ R.c with par := parO d R.n R.δ } : CfgO d).par.p = R.c.par.p := rfl
    omega
  have bO : |R.obs| ≤ 2 ^ (2 * R.E + U + 8) := (Unified.MagO.clip_abs _ _).trans (hU2 hq)
  have bN : |pN| ≤ 2 ^ (2 * R.E + U + 8) := bpN.trans (hU2 (by omega))
  have bD : |pD| ≤ 2 ^ (2 * R.E + U + 8) := bpD.trans (hU2 (by omega))
  have hdU : d ≤ 2 ^ (2 * R.E + U + 8) :=
    (hdE.trans hEU).trans (Nat.lt_two_pow_self (n := 2 * R.E + U + 8)).le
  have hdE' : (d : ℤ) * 2 ^ (2 * (2 * R.E + U + 8)) ≤ 2 ^ (3 * (2 * R.E + U + 8)) := by
    have : (d : ℤ) ≤ 2 ^ (2 * R.E + U + 8) := by exact_mod_cast hdU
    calc (d : ℤ) * 2 ^ (2 * (2 * R.E + U + 8)) ≤ 2 ^ (2 * R.E + U + 8) * 2 ^ (2 * (2 * R.E + U + 8)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ (3 * (2 * R.E + U + 8)) := by rw [← pow_add]; ring_nf
  have bGG : |R.Γ ⬝ᵥ R.Γ| ≤ 2 ^ (3 * (2 * R.E + U + 8)) := by
    have := BLM.dot_abs_le bΓ bΓ hdU
    rwa [show 2 * R.E + U + 8 + (2 * R.E + U + 8) + (2 * R.E + U + 8) = 3 * (2 * R.E + U + 8) by ring] at this
  have b0 : |(0 : ℤ)| ≤ 2 ^ (2 * R.E + U + 8) := by rw [abs_zero]; positivity
  have b1 : |(1 : ℤ)| ≤ 2 ^ (2 * R.E + U + 8) := by rw [abs_one]; exact one_le_pow₀ (by norm_num)
  have hdd : 1 ≤ d * d := Nat.mul_le_mul hd hd
  have bB0 : |qn R.c.par.p (b0OW d R.n R.δ)| ≤ 2 ^ R.E :=
    hI1.arr_abs (a := aMuS) (by decide) (by unfold asz; omega) hC1.1
  have bY0 : |qn R.c.par.p (y0OW d R.n R.δ)| ≤ 2 ^ R.E :=
    hI1.arr_abs (a := aAS) (by decide) (by unfold asz; omega) hC1.2
  have hξ : R.ξ = fun i => (R.Γ i : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) :=
    congrArg Prod.fst (draw_eq (d := d) R.w.cs R.K0 R.pB R.t)
  have hζ : (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).2 = (R.gz : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) / 2 :=
    congrArg Prod.snd (draw_eq (d := d) R.w.cs R.K0 R.pB R.t)
  have hQ0 : (0 : ℤ) < 2 ^ R.c.par.p := by positivity
  have hG0 : (0 : ℤ) < 2 ^ (2 * gsm_prec R.c.par.B) := by positivity
  have heN : 0 < qn R.c.par.pF R.c.par.eps := by
    have h := eq_qn_div R.c.par.pF hP'.eps
    have : (0 : ℚ) < (qn R.c.par.pF R.c.par.eps : ℚ) / 2 ^ R.c.par.pF := h ▸ hP'.eps0
    have : (0 : ℚ) < (qn R.c.par.pF R.c.par.eps : ℚ) := by
      rwa [div_pos_iff_of_pos_right (by positivity)] at this
    exact_mod_cast this
  -- R5's value at the reading
  obtain ⟨Yt, hYt⟩ : ∃ y : ℤ, yHat (2 ^ R.c.par.p) (2 ^ R.c.par.pF) (2 ^ (2 * gsm_prec R.c.par.B)) pN pD R.obs R.gz
      (qn R.c.par.pF R.c.par.eps) = y := ⟨_, rfl⟩
  have hy5 : (Yt : ℚ) / 2 ^ R.c.par.p = yObs R.c.par (ptO R.w.orc R.c (XO R.c st R.ξ))
      (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).2 R.obs := by
    rw [← hYt]
    exact (r57_pure R.c.par _ _ R.ξ R.obs pN pD R.gz R.Γ (2 * gsm_prec R.c.par.B) hpD hpt hζ hξ hP'.eps
      hP'.eps0 hP'.kapc).1.symm
  have bY : |Yt| ≤ 2 ^ (5 * (2 * R.E + U + 8) + 7) := by
    rw [← hYt, ← v1_0 (2 ^ R.c.par.p) (2 ^ R.c.par.pF) (2 ^ (2 * gsm_prec R.c.par.B)) (qn R.c.par.pF R.c.par.eps)
      (qn R.c.par.pF R.c.par.kapc) R.gz pN pD (R.Γ ⬝ᵥ R.Γ) R.obs]
    exact (v1_bound bQ bF bG bE bK bZ bN bD bO bGG 0 (by norm_num)).trans (hU2 (by simp [ev, sl1Et]))
  -- the first line at the reading
  refine XVO.mono (XVO.seq (XVO.ofX (XV.r57 hL hlay (X := R.ctx.X) (σ := σ) (Q := 2 ^ R.c.par.p)
    (F := 2 ^ R.c.par.pF) (G := 2 ^ (2 * gsm_prec R.c.par.B)) (eN := qn R.c.par.pF R.c.par.eps)
    (kN := qn R.c.par.pF R.c.par.kapc) (gz := R.gz) (pN := pN) (pD := pD) (obs := R.obs) (Γ := R.Γ)
    (Gu := 2 * R.E + U + 8) (E1 := 2 * R.E + U + 8) r0' r3' c0' (by rw [c2p']; push_cast; rfl)
    (by rw [c2pF']; push_cast; rfl) (by rw [c2g']; push_cast; rfl) p0' p4' hP.zeta epN epD hP.obs hP.gam
    bQ bF bG bE bK bZ bN bD bO bΓ hdE' (by omega) (d_pow_lt hdU (by omega)) (by omega) (by omega)))
    fun σ2 ⟨v1s, gg2, ⟨c41, c42, c43⟩, d2, F2⟩ => ?_) hB1 fun _ h => h
  have hI2 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ2 :=
    hI1.frame F2 (fun y h => by simp only [S57, sGG, nSP, tR] at h ⊢; omega)
      (fun j h => by simp only [N57, rD1, rK] at h; omega) (fun _ _ h => h.elim) d2
  obtain ⟨r0'', -, -, r3'', -⟩ := hI2.regs
  obtain ⟨c0'', -, c2p'', -, c2g'', -⟩ := hI2.consts
  have eY : σ2.sc 45 = ((Yt : ℤ) : ℝ) := by
    have h := v1s 0 (by norm_num); rw [v1_0, hYt] at h; exact h
  -- R5w
  refine XVO.seq (XVO.ofX (XV.r5w hL hlay (X := R.ctx.X) (σ := σ2) (Y := Yt)
    (Bn := qn R.c.par.p (b0OW d R.n R.δ)) (Yn := qn R.c.par.p (y0OW d R.n R.δ)) (Q := 2 ^ R.c.par.p)
    (G := 2 ^ (2 * gsm_prec R.c.par.B)) (GG := R.Γ ⬝ᵥ R.Γ) (U := 2 * R.E + U + 8) r0'' r3'' c0'' c41 c42 c43 eY
    (by rw [c2p'']; push_cast; rfl) (by rw [c2g'']; push_cast; rfl) gg2
    (by rw [F2.2.2.1 _ _ id]; exact hC1.1) (by rw [F2.2.2.1 _ _ id]; exact hC1.2) bY
    (bB0.trans (hU2 hEU)) (bY0.trans (hU2 hEU)) bQ bG bGG hd (by omega) (by omega) (by omega)))
    fun σ3 ⟨o3, n3, d3, z3, dr3, F3⟩ => ?_
  obtain ⟨yw, hyw0⟩ : ∃ y : ℤ, ywI Yt (qn R.c.par.p (b0OW d R.n R.δ)) (qn R.c.par.p (y0OW d R.n R.δ))
      (2 ^ R.c.par.p) (2 ^ (2 * gsm_prec R.c.par.B)) (R.Γ ⬝ᵥ R.Γ) = y := ⟨_, rfl⟩
  rw [hyw0] at o3
  have hI3 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ3 :=
    hI2.frame F3 (fun y h => by simp only [S5w, sZeta, sPtN, sPtD, sObs, sB0w, bW, nSP, tR] at h ⊢; omega)
      (fun j h => by simp only [N5w, rD1] at h; omega) (fun _ _ h => h.elim) dr3
  obtain ⟨r0₃, -, -, r3₃, -⟩ := hI3.regs
  obtain ⟨c0₃, -, c2p₃, c2pF₃, c2g₃, -⟩ := hI3.consts
  obtain ⟨p0₃, -, -, -, p4₃, -⟩ := hI3.par
  have eΓ3 : ∀ i : Fin d, σ3.arr aGam i = R.Γ i := fun i => by
    rw [F3.2.2.1 _ _ id, F2.2.2.1 _ _ id]; exact hP.gam i
  -- R5w's value: BL-OW's weighted observation
  have hb0 : OnG R.c.par.p (b0OW d R.n R.δ) := onG_up _ _
  have hy0 : OnG R.c.par.p (y0OW d R.n R.δ) := onG_up _ _
  have hξ' : (fun i => (R.Γ i : ℚ) / ((2 ^ (2 * gsm_prec R.c.par.B) : ℤ) : ℚ)) = R.ξ := by
    rw [hξ]; funext i; push_cast; rfl
  have hyw : (yw : ℚ) / 2 ^ R.c.par.p = ywQ R.c.par.p (b0OW d R.n R.δ) (y0OW d R.n R.δ) R.ξ
      (yObs R.c.par (ptO R.w.orc R.c (XO R.c st R.ξ)) (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).2 R.obs) := by
    rw [← hyw0, ywI_eq R.c.par.p _ _ _ _ R.Γ hG0, hξ', hy5, ← eq_qn_div _ hb0, ← eq_qn_div _ hy0]
  have bO2 : |2 * yw| ≤ 2 ^ (2 * R.E + U + 8) := by
    have h1 := ywI_abs Yt (qn R.c.par.p (b0OW d R.n R.δ)) (qn R.c.par.p (y0OW d R.n R.δ)) (2 ^ R.c.par.p)
      (2 ^ (2 * gsm_prec R.c.par.B)) (R.Γ ⬝ᵥ R.Γ) (by positivity)
    rw [hyw0] at h1
    rw [abs_mul, abs_two]
    calc 2 * |yw| ≤ 2 * 2 ^ R.E := by linarith
      _ = 2 ^ (R.E + 1) := by ring
      _ ≤ 2 ^ (2 * R.E + U + 8) := hU2 (by omega)
  -- the step at the dither `ζ_W` is BL-OW's
  have e : modeOW d R.n R.δ R.r0 R.R0 R.a R.w (R.t + 1) = Unified.BLO.stepO R.w.orc R.c R.n (.run st) R.ξ
      (zetaW R.c.par (ptO R.w.orc R.c (XO R.c st R.ξ)) ((yw : ℚ) / 2 ^ R.c.par.p) R.obs) R.obs := by
    rw [modeOW_succ, show modeOW d R.n R.δ R.r0 R.R0 R.a R.w R.t = .run st from hmo]
    refine (stepOW_dither (b0OW d R.n R.δ) (y0OW d R.n R.δ) R.w.orc R.c R.n st R.ξ
      (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).2 R.obs).trans ?_
    rw [hyw]
  have hYW : rY (cfgH R.w.orc R.c st R.ξ) st R.ξ
      (zetaW R.c.par (ptO R.w.orc R.c (XO R.c st R.ξ)) ((yw : ℚ) / 2 ^ R.c.par.p) R.obs) R.obs =
        (yw : ℚ) / 2 ^ R.c.par.p := by
    rw [rY_cfgH]
    exact yObs_zetaW R.c.par R.obs (ne_of_gt (lt_of_lt_of_le one_pos (ptO_ge_one _ _ _)))
      (by rw [hyw]; exact ywQ_onG _ _ _ _ _)
  -- the first line at the re-encoded reading `(0, 1, 1, 2 Ŷ^w)`
  refine XVO.seq (XVO.ofX (XV.r57 hL hlay (X := R.ctx.X) (σ := σ3) (Q := 2 ^ R.c.par.p)
    (F := 2 ^ R.c.par.pF) (G := 2 ^ (2 * gsm_prec R.c.par.B)) (eN := qn R.c.par.pF R.c.par.eps)
    (kN := qn R.c.par.pF R.c.par.kapc) (gz := 0) (pN := 1) (pD := 1) (obs := 2 * yw) (Γ := R.Γ)
    (Gu := 2 * R.E + U + 8) (E1 := 2 * R.E + U + 8) r0₃ r3₃ c0₃ (by rw [c2p₃]; push_cast; rfl)
    (by rw [c2pF₃]; push_cast; rfl) (by rw [c2g₃]; push_cast; rfl) p0₃ p4₃ (by rw [z3]; norm_num)
    (by rw [n3]; norm_num) (by rw [d3]; norm_num) o3 eΓ3
    bQ bF bG bE bK b0 b1 b1 bO2 bΓ hdE' (by omega) (d_pow_lt hdU (by omega)) (by omega) (by omega)))
    fun σ4 ⟨v1s4, _, ⟨c41', c42', c43'⟩, d4, F4⟩ => ?_
  have hI4 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ4 :=
    hI3.frame F4 (fun y h => by simp only [S57, sGG, nSP, tR] at h ⊢; omega)
      (fun j h => by simp only [N57, rD1, rK] at h; omega) (fun _ _ h => h.elim) d4
  have hC4 : CellsW σ4 R.n R.δ :=
    hC1.congr (by rw [F4.2.2.1 _ _ id, F3.2.2.1 _ _ id, F2.2.2.1 _ _ id])
      (by rw [F4.2.2.1 _ _ id, F3.2.2.1 _ _ id, F2.2.2.1 _ _ id])
  -- R7's tests, R7 to R9, the tail
  exact XVO.mono (XVO.runTW hTail (R := R) (U := 2 * R.E + U + 8) (σ := σ4) (P0 := σ4.pts) (ξ := R.ξ)
    (ζ := zetaW R.c.par (ptO R.w.orc R.c (XO R.c st R.ξ)) ((yw : ℚ) / 2 ^ R.c.par.p) R.obs) (obs := R.obs)
    (gz := 0) (pN := 1) (pD := 1) (obs' := 2 * yw) (yh := yw) (Γ := R.Γ) hIn hL hlay hroom' hI4 rfl c41' c42'
    c43' v1s4 (fun i => by rw [F4.2.2.1 _ _ id, F3.2.2.1 _ _ id, F2.2.2.1 _ _ id]; exact aWv1 i)
    (fun j => by rw [F4.2.2.1 _ _ id]; exact eΓ3 j) hξ (yHat_reenc _ _ _ _ _ hQ0 hG0 heN) hYW hEU hdU b0 b1 b1 bO2
    bΓ (tl_newW hM hX' hIn hpos ht e hE1 hE2) (by omega) (by omega) (by omega) (hB4.trans hℓ)
    (lt_of_le_of_lt hB4 hℓa)) le_rfl fun σ' h =>
      ⟨by unfold RdW.Inv1 BLOInv; rw [e]; exact h.1.1, hC4.congr (h.2 d).1 (h.2 (d * d)).2⟩

end AdversarialBco.UW.ProgW
