/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPar

@[expose] public section

/-!
# BL-O's tail, R13 to R15 on the machine

R13 to R15 for BL-O's rowless configuration `cfgV c` and its ELL-O call (`CallSpecO`):

* `xT14O`: the data of R14 (`DLSpecO`), the call, then the flag of the block: `0` leaves for `guard`, `1` commits
  the new state (v2.1's `XV.tCom` with `commitBL`). It ends in `RPost` with the mode `m14O`.
* `xT13O`: R13's values (`xR13`), R13's guard `sc 85 < sc 86`, else `xT14O`. It ends in `RPost` with `m13O`.

`TPostO`: the bounds the caller gives on BL-O's calls when a stage's mode is the new state.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- The bounds the caller gives when the mode `mo` of a stage is the new state. -/
def TPostO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n E : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ)
    (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) (mo : Mode d) : Prop :=
  ∀ mu' : Fin d → ℚ, mo = .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ →
    StBnd c.par.p E c.par.Rint ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ ∧
    ∀ x, apI orc c (callLO c n Bp bp kp wmu) = some x →
      (∀ j, |x j| ≤ 2 ^ E) ∧ ellExpO (clearO (callLO c n Bp bp kp wmu)) ≤ E

/-- R14 and R15: the data, the call, the flag. -/
def xT14O (xdl : Layout → XCmd) (xcall : Layout → XCmdO) (xcom : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xdl L)) (.seq (xcall L) (.base (xifS L sZ oE (xcom L) (xG L))))

/-- The units of `xT14O`. -/
def u14O (Cl kl Ca ka Cc kc d W E E1 G2 : ℕ) : ℕ :=
  Cl * (d + G2 + 1) ^ kl + (Ca * (W + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka + (Cc * (d + E + 1) ^ kc + 3))

set_option maxHeartbeats 2000000 in
/-- **R14 LINE and R15 COMMIT of BL-O on the machine.** -/
theorem XVO.t14O {xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpecO xdl Cl kl) (hcall : CallSpecO xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdO d} {E1 G2 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {wh : Fin d → ℤ} {Dw : ℤ}
    {wmu : Fin d → ℚ}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hT : TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hG2 : E1 ≤ G2) (hDw : 0 < Dw) (hDwb : Dw ≤ 2 ^ G2) (h91 : σ.sc 91 = Dw)
    (h31 : ∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ G2) (hwmu : (fun j => (wh j : ℚ) / Dw) = wmu)
    (hpost : TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp wmu (m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp wmu))
    (hℓ1 : Cl * (d + G2 + 1) ^ kl ≤ R.ℓ) (hℓa1 : Cl * (d + G2 + 1) ^ kl < 2 ^ R.ℓa)
    (hℓ2 : Ca * (R.W + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka ≤ R.ℓ)
    (hℓa2 : Ca * (R.W + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka < 2 ^ R.ℓa)
    (hℓ3 : Cc * (d + R.E + 1) ^ kc ≤ R.ℓ) (hℓa3 : Cc * (d + R.E + 1) ^ kc < 2 ^ R.ℓa) (hℓ : 1 ≤ R.ℓ) :
    R.RunsO (xT14O xdl xcall xcom R.L) σ (u14O Cl kl Ca ka Cc kc d R.W R.E E1 G2)
      (RPost R.L R.n 0 R.K0 R.E (cfgV R.c) (m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp wmu) (R.t + 1) P0) := by
  have hEG : R.E ≤ G2 := hT.hE.trans hG2
  have pG : (2 : ℤ) ^ E1 ≤ 2 ^ G2 := pow_le_pow_right₀ (by norm_num) hG2
  -- the data of R14
  refine XVO.seq (XVO.ofX (hdl d R.L R.ctx.X R.ℓa R.ℓ R.n 0 R.K0 G2 (R.t + 1) (NeO d R.n (kDel R.δ)) (cfgV R.c) st
    Bp bp kp wh Dw σ hIn.hd hIn.hn (NeO_pos _ hIn.hd hIn.hn) rfl hL hlay (hT.inv.mono hEG)
    (fun i j => ⟨(hT.hB i j).1, (hT.hB i j).2.1, (hT.hB i j).2.2.trans pG⟩)
    (fun j => ⟨(hT.hb j).1, (hT.hb j).2.1, (hT.hb j).2.2.trans pG⟩) hT.hk hT.hkg (hT.hkb.trans pG) hDw hDwb h91 h31
    hℓ1 hℓa1)) fun σ1 ⟨hP1, d1, F1⟩ => ?_
  have hT1 := hT.data F1 d1
  -- the call
  refine XVO.seq (hcall d R.L R.w R.n R.δ R.r0 R.R0 R.a R.K0 E1 R.ℓa R.ℓ _ (R.t + 1) (.run st) _ _ _ _ _ _ _ σ1 hIn
    hL hroom (hT1.inv.mono hT.hE) hP1 hℓ2 hℓa2) fun σ2 ⟨hO2, d2, F2⟩ => ?_
  have hT2 := hT1.call F2 d2
  have ecall : callO R.c (Bp * Bpᵀ) bp (Lmu (cfgV R.c).par - kp) (Bit.BLP.rB (cfgV R.c).par / 2) (Bp * Bpᵀ)
      ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL (cfgV R.c).par d R.n) = callLO R.c R.n Bp bp kp wmu := by
    rw [hwmu]; rfl
  rw [show cfgW d R.n R.δ R.r0 R.R0 R.a R.w = R.c from rfl, ecall] at hO2
  have hS := hlay.1
  have hz : σ2.sc sZ = 0 := hT2.inv.consts.1
  have h0 : |σ2.sc sZ| < 2 ^ R.ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  -- the flag
  rcases hr : apI R.w.orc R.c (callLO R.c R.n Bp bp kp wmu) with _ | x
  · rw [hr] at hO2
    have hf : σ2.sc oE = 0 := hO2
    have em : m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp wmu = .guard := by
      unfold m14O; rw [apO_none hr]
    rw [em]
    exact XVO.mono (XVO.ofX (XV.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      h0 (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XV.guard hL hT2.inv hT2.pts hℓ))) (by omega) fun _ h => h
  · have em : m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp wmu =
        .run ⟨false, fun j => (x j : ℚ) / 2 ^ ellExpO (clearO (callLO R.c R.n Bp bp kp wmu)), Ap, Bp, bp, kp, Gp,
          lp⟩ := by
      unfold m14O; rw [apO_some hr]
    obtain ⟨hB, hx⟩ := hpost _ em
    obtain ⟨bA, bB, bb, bk, bG, bl, -⟩ := hB
    obtain ⟨bx, be⟩ := hx x hr
    rw [em]
    have hO2' : EllOut blkBL (some x) (ellExpO (clearO (callLO R.c R.n Bp bp kp wmu))) σ2 := by
      rw [← hr]; exact hO2
    exact XVO.mono (XVO.ofX (XV.tCom hcom (r := some x) hIn.hd hL hlay hT2.inv hT2.pts
      (fun i j => ⟨(hT2.hA i j).1, (hT2.hA i j).2.1, bA i j⟩) (fun i j => ⟨(hT2.hB i j).1, (hT2.hB i j).2.1, bB i j⟩)
      (fun j => ⟨(hT2.hb j).1, (hT2.hb j).2.1, bb j⟩) (fun j => ⟨(hT2.hG j).1, (hT2.hG j).2.1, bG j⟩)
      hT2.hk hT2.hkg bk hT2.hl hT2.hlg bl hO2' (fun x' hx' => by cases hx'; exact ⟨bx, be⟩) hℓ3 hℓa3 hℓ))
      le_rfl fun _ h => h

/-- R13, then its guard, then R14 and R15. -/
def xT13O (xdl : Layout → XCmd) (xcall : Layout → XCmdO) (xcom : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xR13 L)) (xifSO L 85 86 (.base (xG L)) (xT14O xdl xcall xcom L))

/-- The units of `xT13O`. -/
def u13O (Cl kl Ca ka Cc kc d W E E1 : ℕ) : ℕ :=
  r13Units d + (u14O Cl kl Ca ka Cc kc d W E E1 (8 * E1 + 3 * d + 2) + 2)

set_option maxHeartbeats 4000000 in
/-- **R13 WMU of BL-O on the machine.** -/
theorem XVO.t13O {xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpecO xdl Cl kl) (hcall : CallSpecO xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdO d} {E1 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hT : TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hpost : TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
      (m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)))
    (hℓa : 4 * (2 * E1 + d) + 1 < R.ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < R.ℓ)
    (hℓc : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ R.ℓ) (hda : d * d + d < 2 ^ R.ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ R.ℓ)
    (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ R.ℓa)
    (hℓ2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ R.ℓ)
    (hℓa2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ R.ℓa)
    (hℓ3 : Cc * (d + R.E + 1) ^ kc ≤ R.ℓ) (hℓa3 : Cc * (d + R.E + 1) ^ kc < 2 ^ R.ℓa) :
    R.RunsO (xT13O xdl xcall xcom R.L) σ (u13O Cl kl Ca ka Cc kc d R.W R.E E1)
      (RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) (R.t + 1) P0) := by
  have hℓ : 1 ≤ R.ℓ := by omega
  have pE : (2 : ℤ) ^ R.E ≤ 2 ^ E1 := pow_le_pow_right₀ (by norm_num) hT.hE
  have hpar : (cfgV R.c).par = parN (NeO d R.n (kDel R.δ)) d R.n := rfl
  obtain ⟨Dm, mu, hDm, eD, bD, hmu, hAst⟩ := tl_runVals hT.inv
  obtain ⟨eQ, bQ, eF, bF, eG, bG, -, -, -, -, -, -, -, -, -, -, eW, bW⟩ := tl_constsO hpar hT.inv
  set Ah : Matrix (Fin d) (Fin d) ℤ := fun i j => qn R.c.par.p (st.A i j) with hAh
  obtain ⟨bw, bn, bDw, bF2, bW2, b4, bnn⟩ := tl_r13_bnds (2 ^ R.c.par.p) (2 ^ (2 * gsm_prec R.c.par.B)) Dm s5
    (2 ^ R.c.par.pF) (qn R.c.par.pF R.c.par.W) mu Γ Ah E1 (bQ.trans pE) (bG.trans pE) (bD.trans pE) hT.hsb
    (bF.trans pE) (bW.trans pE) (fun j => (hmu j).2.1.trans pE) (fun i j => (hAst i j).2.trans pE) hT.hΓ
  have pG : (2 : ℤ) ^ E1 ≤ 2 ^ (2 * E1 + d) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- R13's values
  refine XVO.seq (XVO.ofX (XV.r13 hL hlay (σ := σ) (mu := mu) (w := Ah *ᵥ Γ) (Gu := 2 * E1 + d)
    (G2 := 8 * E1 + 3 * d + 2) hT.inv.regs.1 hT.inv.regs.2.2.2.1 hT.inv.consts.1 hT.c4 (fun j => (hmu j).1) hT.hw
    eF eQ eG eD hT.hs eW (fun j => ((hmu j).2.1.trans pE).trans pG) bw ((bQ.trans pE).trans pG)
    ((bG.trans pE).trans pG) ((bD.trans pE).trans pG) (hT.hsb.trans pG) bn bDw bF2 bW2 b4 bnn hℓa hℓb hℓc hda))
    fun σ1 ⟨v31, v91, v85, v86, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [S13, tR, nSP] at hy ⊢; omega)
    (fun j hj => by simp only [N13] at hj; omega) (fun a k hk => by simp only [A13, nAP] at hk ⊢; omega) d1
  obtain ⟨t85, t86⟩ := tl_r13_test_abs (qn R.c.par.pF R.c.par.W) (Dm * 2 ^ R.c.par.p * 2 ^ R.c.par.p *
    2 ^ (2 * gsm_prec R.c.par.B)) (2 ^ R.c.par.pF) _ (8 * E1 + 3 * d + 2) R.ℓ bW2 bDw bF2 b4 bnn hℓb
  have hdec := tl_r13_dec R.c.par st s5 Γ mu Dm (2 ^ R.c.par.pF) (qn R.c.par.pF R.c.par.W) Ah hDm
    (by positivity) (fun j => (hmu j).2.2) (fun i j => (hAst i j).1) (fun _ _ => rfl)
    (tl_grid _ (tlN_onG_W (NeO d R.n (kDel R.δ)) d R.n))
  have hS := hlay.1
  have hNS : 91 < R.L.NS := by simp only [oE] at hS; omega
  by_cases hc : σ1.sc 85 < σ1.sc 86
  · -- the guard
    have hc' : (2 * R.c.par.W) ^ 2 < wmuOf R.c.par st s5 Γ ⬝ᵥ wmuOf R.c.par st s5 Γ := by
      rw [v85, v86, Int.cast_lt] at hc; exact hdec.2 hc
    have em : m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) = .guard := by
      unfold m13O; simp only [hc', ↓reduceIte]
    rw [em]
    exact XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [v85]; exact t85) (by rw [v86]; exact t86) hc
      (XVO.ofX (XV.guard hL hT1.inv hT1.pts hℓ))) (by unfold u14O; omega) fun _ h => h
  · -- R14 and R15
    have hc' : ¬ (2 * R.c.par.W) ^ 2 < wmuOf R.c.par st s5 Γ ⬝ᵥ wmuOf R.c.par st s5 Γ := by
      rw [v85, v86, Int.cast_lt] at hc; exact fun h => hc (hdec.1 h)
    have em : m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) =
        m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) := by
      unfold m13O; simp only [hc', ↓reduceIte]
    rw [em] at hpost ⊢
    have hDw : 0 < Dm * (2 : ℤ) ^ R.c.par.p * 2 ^ R.c.par.p * 2 ^ (2 * gsm_prec R.c.par.B) := by positivity
    exact XVO.ifS_f hL (by omega) (by omega) (by rw [v85]; exact t85) (by rw [v86]; exact t86) hc
      (XVO.t14O hdl hcall hcom hIn hL hlay hroom hT1 (by omega) hDw (le_of_abs_le bDw) v91 (fun j => ⟨v31 j, bn j⟩)
        (tl_wmu R.c.par st s5 Γ mu Dm Ah hDm (fun j => (hmu j).2.2) (fun i j => (hAst i j).1)
          (fun _ _ => rfl)).symm hpost hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3 hℓ)

end AdversarialBco.Unified.ProgO
