/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOMag
public import AdversarialBco.Unified.MagRun
public import AdversarialBco.Unified.MagExp
public import AdversarialBco.Bit.Transfer.XBLCommit

@[expose] public section

/-!
# `ProgTail` from the tail's sub-block contracts

`xtailFO`: R5 and R7's scalars (`xR57`), then `xRunTO` with the tail `xtailO` (R10 to R15 with the two ELL-O calls).
`progTail_of`: `ProgTail` (Unified/ProgOSplit.lean) from the magnitudes `MagBLO`, the exponent contract `ExpBLO`, the
data of R11 and R14 (`DataTO`, `DataLO`), R12's fire (`FireO`) and the ELL-O call (`CallO`), with v2.1's
`commitBL`. `progTail_of'` uses `magBLO` (MagRun.lean) and `expBLO` (MagExp.lean).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

/-- **R5 to R15 of BL-O in mode `run`**: R5 and R7's scalars, R7's tests, R7 to R9, the tail. -/
def xtailFO (xdt : Layout → XCmd) (xcall : Layout → XCmdO) (xfire xdl xcom : Layout → XCmd) (L : Layout) :
    XCmdO :=
  .seq (.base (xR57 L)) (xRunTO (xtailO xdt xcall xfire xdl xcom) L)

/-- The budget of `xtailFO` and the conditions of `XV.r57` and `XVO.runTO` below `C (W + E + U + 1)^k`. -/
theorem asm_arith (Ct kt W E U d : ℕ) (hdW : d ≤ W) :
    r57Units d (2 * E + U + 8) + (2 + (2 + (midUnits d (2 * E + U + 8) +
      Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt))) ≤
        (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    130 * (2 * E + U + 8) + 120 < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    d * d + d < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) := by
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
  have hdd : d * d ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hK : (10 ^ 6 + Ct * 400 ^ kt) * X ^ (kt + 2) = 10 ^ 6 * X ^ (kt + 2) + Ct * 400 ^ kt * X ^ (kt + 2) := by
    ring
  rw [hK]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The exponent condition of the round from `Cn (W + E₀ + 1)^kn ≤ E`. -/
theorem asm_E (Cm km Cx kx W E0 E K d : ℕ) (hdW : d ≤ W) (hKW : K ≤ 528 * W)
    (hE : (Cm + Cx * 5400 ^ kx + 600) * (W + E0 + 1) ^ (km + kx + 1) ≤ E) :
    Cm * (W + E0 + 1) ^ km ≤ E ∧ Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx + K ≤ E ∧ d ≤ E := by
  set Y := W + E0 + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hm : Y ^ km ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have hx : Y ^ kx ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have h1 : Y ≤ Y ^ (km + kx + 1) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have hb : W + (5 * (2 * K + 10) + 5) + 1 ≤ 5400 * Y := by omega
  have hcx : Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx ≤ Cx * 5400 ^ kx * Y ^ (km + kx + 1) := by
    calc Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx ≤ Cx * (5400 * Y) ^ kx :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _ = Cx * 5400 ^ kx * Y ^ kx := by rw [mul_pow, mul_assoc]
      _ ≤ Cx * 5400 ^ kx * Y ^ (km + kx + 1) := Nat.mul_le_mul_left _ hx
  have hcm : Cm * Y ^ km ≤ Cm * Y ^ (km + kx + 1) := Nat.mul_le_mul_left _ hm
  have hK' : (Cm + Cx * 5400 ^ kx + 600) * Y ^ (km + kx + 1) =
      Cm * Y ^ (km + kx + 1) + Cx * 5400 ^ kx * Y ^ (km + kx + 1) + 600 * Y ^ (km + kx + 1) := by ring
  rw [hK'] at hE
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 16000000 in
/-- **`ProgTail`**: R5 to R15 of BL-O's round in mode `run`, from the magnitudes, the exponent contract and the
tail's sub-block contracts. -/
theorem progTail_of (hM : MagBLO) (hX : ExpBLO) (hdt : DataTO) (hdl : DataLO) (hfi : FireO) (hca : CallO) :
    ProgTail := by
  obtain ⟨Cm, km, hM⟩ := hM
  obtain ⟨Cx, kx, hX'⟩ := id hX
  obtain ⟨xdt, Ct, kt, hdt⟩ := hdt
  obtain ⟨xdl, Cl, kl, hdl⟩ := hdl
  obtain ⟨xfire, Cf, kf, hfire⟩ := hfi
  obtain ⟨xcall, Ca, ka, nS, nN, nA, hcall⟩ := hca
  obtain ⟨xcom, Cc, kc, hcom⟩ := commitBL
  obtain ⟨Ct', kt', hTail⟩ := tailOKO_of hX hdt hfire hdl hcall hcom
  refine ⟨xtailFO xdt xcall xfire xdl xcom,
    ⟨10 ^ 6 + Ct' * 400 ^ kt', kt' + 2, Cm + Cx * 5400 ^ kx + 600, km + kx + 1, nS + 771, nN + 65, nA + 34⟩, ?_⟩
  intro d R st U σ0 σ hH hI hmo hP
  obtain ⟨hIn, ht, hL, hroom, hpos, hE, hℓ, hℓa⟩ := hH
  dsimp only at hE hℓ hℓa hroom
  have hd := hIn.hd
  have hdW := d_le_W R
  have hKW : MagO.Ku d R.n (kDel R.δ) ≤ 528 * R.W := MagO.Ku_le d R.n R.δ R.r0 R.R0 R.a hIn.hδ0
  obtain ⟨hE1, hE2, hdE⟩ := asm_E Cm km Cx kx R.W R.E0 R.E (MagO.Ku d R.n (kDel R.δ)) d hdW hKW hE
  obtain ⟨hB1, hB2, hB3, hB4⟩ := asm_arith Ct' kt' R.W R.E U d hdW
  obtain ⟨hr1, hr2, hr3⟩ := hroom
  have hlay : BLLay R.L := by
    unfold BLLay; simp only [oE, rEE, aWE]; omega
  have hroom' : RoomO R.L nS nN nA := ⟨by omega, by omega, by omega⟩
  have hI0 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) R.t σ0 := by
    have h := hI; unfold RdO.Inv BLOInv at h; rw [hmo] at h; exact h
  have hI1 := hI0.ofPers hP.pers hP.rounds hP.draws
  obtain ⟨r0', -, -, r3', -⟩ := hI1.regs
  obtain ⟨c0', -, c2p', c2pF', c2g', -⟩ := hI1.consts
  obtain ⟨p0', -, -, -, p4', -⟩ := hI1.par
  obtain ⟨⟨pN, pD, hpN, hpD, epN, epD, hpt, bpN, bpD⟩, aWv1⟩ := hP.dat
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
  have bΓ : ∀ i : Fin d, |R.Γ i| ≤ 2 ^ (2 * R.E + U + 8) := fun i =>
    (gamI_abs_le _ _ _ _ _ _).trans (hU2 (by omega))
  have bZ : |R.gz| ≤ 2 ^ (2 * R.E + U + 8) := (zetI_abs_le _ _ _ _ _).trans (hU2 (by omega))
  have hq : R.c.qO ≤ 2 * R.E + U + 8 := by
    have h1 := MagO.qO_le R.c d R.n (kDel R.δ) hd rfl rfl
    have h2 : MagO.Ku d R.n (kDel R.δ) = R.c.par.pF + 8 := rfl
    omega
  have bO : |R.obs| ≤ 2 ^ (2 * R.E + U + 8) := (MagO.clip_abs _ _).trans (hU2 hq)
  have bN : |pN| ≤ 2 ^ (2 * R.E + U + 8) := bpN.trans (hU2 (by omega))
  have bD : |pD| ≤ 2 ^ (2 * R.E + U + 8) := bpD.trans (hU2 (by omega))
  have hdU : d ≤ 2 ^ (2 * R.E + U + 8) :=
    (hdE.trans hEU).trans (Nat.lt_two_pow_self (n := 2 * R.E + U + 8)).le
  have hdE' : (d : ℤ) * 2 ^ (2 * (2 * R.E + U + 8)) ≤ 2 ^ (3 * (2 * R.E + U + 8)) := by
    have : (d : ℤ) ≤ 2 ^ (2 * R.E + U + 8) := by exact_mod_cast hdU
    calc (d : ℤ) * 2 ^ (2 * (2 * R.E + U + 8)) ≤ 2 ^ (2 * R.E + U + 8) * 2 ^ (2 * (2 * R.E + U + 8)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ (3 * (2 * R.E + U + 8)) := by rw [← pow_add]; ring_nf
  have hξ : R.ξ = fun i => (R.Γ i : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) :=
    congrArg Prod.fst (draw_eq (d := d) R.w.cs R.K0 R.pB R.t)
  have hζ : zetaO R = (R.gz : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) / 2 :=
    congrArg Prod.snd (draw_eq (d := d) R.w.cs R.K0 R.pB R.t)
  have e : modeO d R.n R.δ R.r0 R.R0 R.a R.w (R.t + 1) =
      BLO.stepO R.w.orc R.c R.n (.run st) R.ξ (zetaO R) R.obs := by
    rw [modeO_succ, show modeO d R.n R.δ R.r0 R.R0 R.a R.w R.t = .run st from hmo]
    rfl
  -- R5 and R7's scalars
  refine XVO.mono (XVO.seq (XVO.ofX (XV.r57 hL hlay (X := R.ctx.X) (σ := σ) (Q := 2 ^ R.c.par.p)
    (F := 2 ^ R.c.par.pF) (G := 2 ^ (2 * gsm_prec R.c.par.B)) (eN := qn R.c.par.pF R.c.par.eps)
    (kN := qn R.c.par.pF R.c.par.kapc) (gz := R.gz) (pN := pN) (pD := pD) (obs := R.obs) (Γ := R.Γ)
    (Gu := 2 * R.E + U + 8) (E1 := 2 * R.E + U + 8) r0' r3' c0' (by rw [c2p']; push_cast; rfl)
    (by rw [c2pF']; push_cast; rfl) (by rw [c2g']; push_cast; rfl) p0' p4' hP.zeta epN epD hP.obs hP.gam
    (bsc (y := s2p) (by decide) (by rw [c2p']; push_cast; rfl))
    (bsc (y := s2pF) (by decide) (by rw [c2pF']; push_cast; rfl))
    (bsc (y := s2g) (by decide) (by rw [c2g']; push_cast; rfl)) (bsc (by decide) p0') (bsc (by decide) p4') bZ bN bD
    bO bΓ hdE' (by omega) (d_pow_lt hdU (by omega)) (by omega) (by omega)))
    fun σ2 ⟨v1s, _, ⟨c41, c42, c43⟩, d2, F2⟩ => ?_) hB1 fun _ h => h
  have hI2 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ2 :=
    hI1.frame F2 (fun y h => by simp only [S57, sGG, nSP, tR] at h ⊢; omega)
      (fun j h => by simp only [N57, rD1, rK] at h; omega) (fun _ _ h => h.elim) d2
  -- R7's tests, R7 to R9, the tail
  exact XVO.mono (XVO.runTO hTail (R := R) (U := 2 * R.E + U + 8) (σ := σ2) (P0 := σ2.pts) (ξ := R.ξ)
    (ζ := zetaO R) (obs := R.obs) (gz := R.gz) (pN := pN) (pD := pD) (Γ := R.Γ) hIn hL hlay hroom' hI2 rfl c41 c42
    c43 v1s (fun i => by rw [F2.2.2.1 _ _ id]; exact aWv1 i) (fun j => by rw [F2.2.2.1 _ _ id]; exact hP.gam j) hξ
    hζ hpt hpD hEU hdU bZ bN bD bO bΓ (tl_newO hM hX' hIn hpos ht hmo hE1 hE2) (by omega) (by omega) (by omega)
    (hB4.trans hℓ) (lt_of_le_of_lt hB4 hℓa)) le_rfl fun σ' h => by
      unfold RdO.Inv1 BLOInv; rw [e]; exact h.1

/-- **`ProgTail`** from the tail's sub-block contracts, with `magBLO` and `expBLO`. -/
theorem progTail_of' (hdt : DataTO) (hdl : DataLO) (hfi : FireO) (hca : CallO) : ProgTail :=
  progTail_of MagO.magBLO MagO.expBLO hdt hdl hfi hca

end AdversarialBco.Unified.ProgO
