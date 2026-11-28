/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailT14
public import AdversarialBco.Unified.TailOT12

@[expose] public section

/-!
# BL-OW's tail, R11 and R12 on the machine

The BL-OW copies of BL-O's runs for R11 and R12 (Unified/TailOT12.lean): the same commands `xT12O`, `xT11O` and units,
at BL-OW's round `RdW`, with the data of R11 and the fire under `ParT` (`DTSpecW`, `FireSpecW`) and the call at `cfgWW`
(`CallSpecW`), keeping the arrays 0 and 1 (`Keep01`).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (parOW cfgWW)
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

theorem nA_12 : ∀ k, ¬ A12 (d := d) aMuS k ∧ ¬ A12 (d := d) aAS k :=
  fun _ => ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩

set_option maxHeartbeats 4000000 in
/-- **R12 FIRE of BL-OW on the machine**, keeping the arrays 0 and 1. -/
theorem XVO.t12W {xfire xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO} {Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hfire : FireSpecW xfire Cf kf) (hdl : DLSpecW xdl Cl kl) (hcall : CallSpecW xcall Ca ka nS nN nA)
    (hcom : ComSpec xcom Cc kc)
    {R : RdW d} {E1 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {x : Fin d → ℤ} {Xe Xb : ℕ}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hT : TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hO : EllOut blkBL (some x) Xe σ) (hx : ∀ j, |x j| ≤ 2 ^ (Xe + E1)) (hXb : Xe ≤ Xb)
    (hpost : TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
      (m12O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) fun i => (x i : ℚ) / 2 ^ Xe))
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < R.ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ R.ℓ) (hXa : Xb < 2 ^ R.ℓa)
    (hℓf : Cf * (d + R.E + 1) ^ kf ≤ R.ℓ) (hℓaf : Cf * (d + R.E + 1) ^ kf < 2 ^ R.ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < R.ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < R.ℓ)
    (hℓc : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ R.ℓ) (hda : d * d + d < 2 ^ R.ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ R.ℓ)
    (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ R.ℓa)
    (hℓ2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ R.ℓ)
    (hℓa2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ R.ℓa)
    (hℓ3 : Cc * (d + R.E + 1) ^ kc ≤ R.ℓ) (hℓa3 : Cc * (d + R.E + 1) ^ kc < 2 ^ R.ℓa) :
    R.RunsO (xT12O xfire xdl xcall xcom R.L) σ (u12O Cf kf Cl kl Ca ka Cc kc d R.W R.E E1 Xb)
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (m12O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) fun i => (x i : ℚ) / 2 ^ Xe) (R.t + 1)
        P0 σ' ∧ Keep01 σ σ') := by
  have hP := parT_rd R hIn
  set Gu := 4 * E1 + 2 * Xe + 3 * d with hGu
  have hGub : Gu ≤ 4 * E1 + 2 * Xb + 3 * d := by omega
  have pE : (2 : ℤ) ^ R.E ≤ 2 ^ Gu := pow_le_pow_right₀ (by norm_num) (by have := hT.hE; omega)
  obtain ⟨eQ, bQ, eF, bF, -, -, eH, bH, -, -, -, bR, eE, bE, eR, bRh, -, -⟩ := tl_constsW hP hT.inv
  set Bh : Matrix (Fin d) (Fin d) ℤ := fun i j => qn R.c.par.p (Bp i j) with hBh
  set bh : Fin d → ℤ := fun j => qn R.c.par.p (bp j) with hbh
  set Gh : Fin d → ℤ := fun j => qn R.c.par.p (Gp j) with hGh
  obtain ⟨bB, bx, bb, bG, bBx, bBB, bbx, bGx, bD⟩ := tl_r12_bnds Bh bh Gh x E1 Xe (fun i j => (hT.hB i j).2.2)
    (fun j => (hT.hb j).2.2) (fun j => (hT.hG j).2.2) hx
  have pE1 : (2 : ℤ) ^ E1 ≤ 2 ^ Gu := pow_le_pow_right₀ (by norm_num) (by omega)
  have hg2' : d * 2 ^ (2 * Gu) < 2 ^ R.ℓ :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))) hg2
  have eX : σ.sc 769 = ((Xe : ℤ) : ℝ) := by rw [Int.cast_natCast]; exact hO.2.1
  refine XVO.mono (K := r12Units d Xe + (u13O Cl kl Ca ka Cc kc d R.W R.E E1 + Cf * (d + R.E + 1) ^ kf + 2)) ?_
    (Nat.add_le_add_right (r12Units_mono d hXb) _) fun _ h => h
  -- R12's values
  refine XVO.seq (XVO.ofX (XV.r12 hL hlay (σ := σ) (Bh := Bh) (bh := bh) (Gh := Gh) (x := x) (Xe := Xe) (Gu := Gu)
    hT.inv.regs.1 hT.inv.regs.2.2.2.1 hT.inv.consts.1 hT.c2 eX hO.2.2 (fun i j => (hT.hB i j).1)
    (fun j => (hT.hb j).1) (fun j => (hT.hG j).1) eF eQ eH eE hT.hl hT.hk eR bB bx bb bG bBx (bF.trans pE)
    (bQ.trans pE) (bH.trans pE) (bE.trans pE) (hT.hlb.trans pE1) (hT.hkb.trans pE1) (bRh.trans pE) bD bBB bbx bGx
    (by omega) hg2' (by omega) (by omega) (by omega))) fun σ1 ⟨_, v86, v87, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [S12, tR, nSP] at hy ⊢; omega)
    (fun j hj => by simp only [N12] at hj; omega) (fun a k hk => by simp only [A12, nAP] at hk ⊢; omega) d1
  have k1 : Keep01 σ σ1 := Keep01.ofA F1 nA_12
  obtain ⟨t86, t87⟩ := tl_r12_test_abs (2 ^ R.c.par.pF) (2 ^ R.c.par.p) (2 ^ Xe) (tlHN (NeO d R.n (kDel R.δ)) d R.n)
    (qn R.c.par.pF R.c.par.eta) (qn R.c.par.p lp) (qn R.c.par.p kp) (qn R.c.par.pF R.c.par.rho) Bh Gh bh x
    Gu R.ℓ (bF.trans pE) (bQ.trans pE) (by rw [abs_of_nonneg (by positivity)]; exact bD) (bH.trans pE)
    (bE.trans pE) (hT.hlb.trans pE1) (hT.hkb.trans pE1) (bRh.trans pE) bB bG bb bx (by omega)
  have hdec := tl_r12_dec R.c.par Bp bp Gp (fun i => (x i : ℚ) / 2 ^ Xe) kp lp (2 ^ R.c.par.pF) (2 ^ R.c.par.p)
    (2 ^ Xe) (tlHN (NeO d R.n (kDel R.δ)) d R.n) (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.rho)
    (qn R.c.par.p lp) (qn R.c.par.p kp) Bh bh Gh x (by positivity) (by positivity) (by positivity) (tlHN_pos _ _ _)
    (tl_grid _ hP.eta) (tl_grid _ hP.rho) (tlW_eHat hP)
    (by ext i j; exact tl_grid _ (hT.hB i j).2.1) (by funext j; exact tl_grid _ (hT.hb j).2.1)
    (by funext j; exact tl_grid _ (hT.hG j).2.1) (tl_grid _ hT.hkg) (tl_grid _ hT.hlg) (by funext i; push_cast; rfl)
  have hS := hlay.1
  by_cases hc : σ1.sc 87 < σ1.sc 86
  · -- no fire: R13 to R15
    have hc' : ¬ (R.c.par.eta * (lp - Gp ⬝ᵥ fun i => (x i : ℚ) / 2 ^ Xe) -
        2 * ((fun i => (x i : ℚ) / 2 ^ Xe) ⬝ᵥ ((Bp * Bpᵀ) *ᵥ fun i => (x i : ℚ) / 2 ^ Xe) / 2 -
          bp ⬝ᵥ (fun i => (x i : ℚ) / 2 ^ Xe) + kp) ≤ -R.c.par.rho + R.c.par.eHat) := by
      rw [v86, v87, Int.cast_lt] at hc
      exact fun h => absurd (hdec.1 h) (not_le.2 hc)
    have em : m12O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) (fun i => (x i : ℚ) / 2 ^ Xe) =
        m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) := by
      unfold m12O; simp only [hc', ↓reduceIte]
    rw [em] at hpost ⊢
    exact XVO.mono (XVO.ifS_t hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v87]; exact t87) (by rw [v86]; exact t86) hc
      (XVO.t13W hdl hcall hcom hIn hL hlay hroom hT1 hpost hℓa hℓb hℓc hda hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3))
      (by omega) fun _ h => ⟨h.1, k1.trans h.2⟩
  · -- the fire: a new epoch
    have hc' : R.c.par.eta * (lp - Gp ⬝ᵥ fun i => (x i : ℚ) / 2 ^ Xe) -
        2 * ((fun i => (x i : ℚ) / 2 ^ Xe) ⬝ᵥ ((Bp * Bpᵀ) *ᵥ fun i => (x i : ℚ) / 2 ^ Xe) / 2 -
          bp ⬝ᵥ (fun i => (x i : ℚ) / 2 ^ Xe) + kp) ≤ -R.c.par.rho + R.c.par.eHat := by
      rw [v86, v87, Int.cast_lt] at hc
      exact hdec.2 (not_lt.1 hc)
    have em : m12O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) (fun i => (x i : ℚ) / 2 ^ Xe) =
        .run (init R.c.par d) := by
      unfold m12O; simp only [hc', ↓reduceIte]
    rw [em]
    exact XVO.mono (XVO.ifS_f hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v87]; exact t87) (by rw [v86]; exact t86) hc
      (XVO.ofX (hfire d R.L R.ctx.X R.ℓa R.ℓ R.n 0 R.K0 R.E (R.t + 1) (NeO d R.n (kDel R.δ)) (cfgV R.c) st σ1
        hIn.hd hIn.hn (NeO_pos _ hIn.hd hIn.hn) hP hL hlay hT1.inv hℓf hℓaf)))
      (by omega) fun σ' ⟨hI', _, hF'⟩ => ⟨⟨hI', by rw [hF'.2.2.2.2, hT1.pts]⟩, k1.trans (Keep01.ofA hF' nA_end)⟩

set_option maxHeartbeats 2000000 in
/-- **R11 TEST of BL-OW on the machine**, keeping the arrays 0 and 1. -/
theorem XVO.t11W {xdt xfire xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO}
    {Ct kt Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdt : DTSpecW xdt Ct kt) (hfire : FireSpecW xfire Cf kf) (hdl : DLSpecW xdl Cl kl)
    (hcall : CallSpecW xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdW d} {E1 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {Xb : ℕ}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hT : TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hX : ellExpO (clearO (callTO R.c st Bp bp Gp)) ≤ Xb)
    (hpost : TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
      (m11O R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)))
    (hℓt : Ct * (d + E1 + 1) ^ kt ≤ R.ℓ) (hℓat : Ct * (d + E1 + 1) ^ kt < 2 ^ R.ℓa)
    (hℓc : Ca * (R.W + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ R.ℓ)
    (hℓac : Ca * (R.W + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka < 2 ^ R.ℓa)
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < R.ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ R.ℓ) (hXa : Xb < 2 ^ R.ℓa)
    (hℓf : Cf * (d + R.E + 1) ^ kf ≤ R.ℓ) (hℓaf : Cf * (d + R.E + 1) ^ kf < 2 ^ R.ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < R.ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < R.ℓ)
    (hℓc' : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ R.ℓ) (hda : d * d + d < 2 ^ R.ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ R.ℓ)
    (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ R.ℓa)
    (hℓ2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ R.ℓ)
    (hℓa2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ R.ℓa)
    (hℓ3 : Cc * (d + R.E + 1) ^ kc ≤ R.ℓ) (hℓa3 : Cc * (d + R.E + 1) ^ kc < 2 ^ R.ℓa) :
    R.RunsO (xT11O xdt xcall xfire xdl xcom R.L) σ (u11O Ct kt Cf kf Cl kl Ca ka Cc kc d R.W R.E E1 Xb)
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (m11O R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) (R.t + 1) P0 σ' ∧ Keep01 σ σ') := by
  have hℓ : 1 ≤ R.ℓ := by omega
  have hP := parT_rd R hIn
  -- the data of R11
  refine XVO.seq (XVO.ofX (hdt d R.L R.ctx.X R.ℓa R.ℓ R.n 0 R.K0 E1 (R.t + 1) (NeO d R.n (kDel R.δ)) (cfgV R.c) st
    Bp bp Gp σ hIn.hd hIn.hn (NeO_pos _ hIn.hd hIn.hn) hP hL hlay (hT.inv.mono hT.hE) hT.hB hT.hb hT.hG hℓt
    hℓat)) fun σ1 ⟨hP1, d1, F1⟩ => ?_
  have hT1 := hT.data F1 d1
  have k1 : Keep01 σ σ1 := Keep01.ofA F1 nA_dat
  -- the call
  refine XVO.seq (hcall d R.L R.w R.n R.δ R.r0 R.R0 R.a R.K0 E1 R.ℓa R.ℓ _ (R.t + 1) (.run st) _ _ _ _ _ _ _ σ1 hIn
    hL hroom (hT1.inv.mono hT.hE) hP1 hℓc hℓac) fun σ2 ⟨hO2, d2, F2⟩ => ?_
  have hT2 := hT1.call F2 d2
  have k2 : Keep01 σ σ2 := k1.trans (Keep01.ofA F2 nA_call)
  have hO : EllOut blkBL (apI R.w.orc R.c (callTO R.c st Bp bp Gp))
      (ellExpO (clearO (callTO R.c st Bp bp Gp))) σ2 := by
    rw [callTO_eq]; exact hO2
  have hS := hlay.1
  have hz : σ2.sc sZ = 0 := hT2.inv.consts.1
  have h0 : |σ2.sc sZ| < 2 ^ R.ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  rcases hr : apI R.w.orc R.c (callTO R.c st Bp bp Gp) with _ | x
  · rw [hr] at hO
    have hf : σ2.sc oE = 0 := hO
    have em : m11O R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) = .guard := by
      unfold m11O; rw [apO_none hr]
    rw [em]
    exact XVO.mono (XVO.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XVO.ofX (XV.guardK hL hT2.inv hT2.pts hℓ))) (by unfold u12O r12Units; omega)
      fun _ h => ⟨h.1, k2.trans h.2⟩
  · rw [hr] at hO
    have hf : σ2.sc oE = 1 := hO.1
    have em : m11O R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) =
        m12O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
          (fun i => (x i : ℚ) / 2 ^ ellExpO (clearO (callTO R.c st Bp bp Gp))) := by
      unfold m11O; rw [apO_some hr]
    rw [em] at hpost ⊢
    have hR : ((R.c.par.Rint : ℤ) : ℚ) ≤ 2 ^ E1 := by
      have h := (le_abs_self _).trans ((tl_constsW hP hT.inv).2.2.2.2.2.2.2.2.2.2.2.1.trans
        (pow_le_pow_right₀ (by norm_num) hT.hE))
      exact_mod_cast h
    have hx : ∀ j, |x j| ≤ 2 ^ (ellExpO (clearO (callTO R.c st Bp bp Gp)) + E1) :=
      apI_abs hr (by rw [callTO_eq]; show ((R.c.par.Rint : ℕ) : ℚ) ≤ _; exact_mod_cast hR)
    exact XVO.mono (XVO.ifS_t hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 1) hℓ (by norm_num)) (by rw [hz, hf]; exact one_pos)
      (XVO.t12W hfire hdl hcall hcom hIn hL hlay hroom hT2 hO hx hX hpost hg1 hg2 hXa hℓf hℓaf hℓa hℓb hℓc' hda
        hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3)) (by omega) fun _ h => ⟨h.1, k2.trans h.2⟩

end AdversarialBco.UW.ProgW
