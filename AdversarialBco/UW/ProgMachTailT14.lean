/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailSpec
public import AdversarialBco.Unified.TailOT14

@[expose] public section

/-!
# BL-OW's tail, R13 to R15 on the machine

The BL-OW copies of BL-O's runs for R13 to R15 (Unified/TailOT14.lean): the same commands `xT14O`, `xT13O` and units, at
BL-OW's round `RdW`, with the data of R14 under `ParT` (`DLSpecW`) and the call at `cfgWW` (`CallSpecW`). Each run also
keeps the arrays `aMuS`, `aAS` (`Keep01`), where BL-OW stores its thresholds `b0`, `y0`: every leaf frame of the tail
(the data, the call, R13, the commit, the guard's `setSc`) avoids the arrays 0 and 1.

* `Keep01`: the arrays 0 and 1 unchanged; `Keep01.ofC`, `Keep01.ofA` from a frame whose arrays avoid them;
* `tl_constsW`: BL-O's tail constants under `ParT`, whose `ê` is BL-O's;
* `XV.guardK`, `XV.tComK`: v2.1's guard and R15 behind its flag, with `Keep01`.
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

/-! ## The arrays of the thresholds -/

/-- The arrays `aMuS`, `aAS` (0 and 1) unchanged from `σ` to `σ'`. -/
def Keep01 (σ σ' : Env d) : Prop := ∀ k, σ'.arr aMuS k = σ.arr aMuS k ∧ σ'.arr aAS k = σ.arr aAS k

theorem Keep01.trans {σ σ' σ'' : Env d} (h : Keep01 σ σ') (h' : Keep01 σ' σ'') : Keep01 σ σ'' :=
  fun k => ⟨(h' k).1.trans (h k).1, (h' k).2.trans (h k).2⟩

/-- A frame whose arrays avoid 0 and 1 keeps them. -/
theorem Keep01.ofC {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameC S N Ar σ σ')
    (hA : ∀ k, ¬ Ar aMuS k ∧ ¬ Ar aAS k) : Keep01 σ σ' :=
  fun k => ⟨h.2.2 _ _ (hA k).1, h.2.2 _ _ (hA k).2⟩

theorem Keep01.ofA {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameA S N Ar σ σ')
    (hA : ∀ k, ¬ Ar aMuS k ∧ ¬ Ar aAS k) : Keep01 σ σ' :=
  Keep01.ofC (FrameC.ofA h) hA

/-- A scalar write keeps the arrays. -/
theorem Keep01.setSc (σ : Env d) (y : ℕ) (v : ℝ) : Keep01 σ (σ.setSc y v) := fun _ => ⟨rfl, rfl⟩

theorem nA_dat : ∀ k, ¬ ADat aMuS k ∧ ¬ ADat aAS k := fun _ => by unfold ADat; decide
theorem nA_call : ∀ k, ¬ ACall aMuS k ∧ ¬ ACall aAS k := fun _ => by unfold ACall APrep ARow; decide
theorem nA_end : ∀ k, ¬ AEnd aMuS k ∧ ¬ AEnd aAS k := fun _ => by unfold AEnd; decide
theorem nA_13 : ∀ k, ¬ A13 (d := d) aMuS k ∧ ¬ A13 (d := d) aAS k :=
  fun _ => ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩

/-! ## PARAM's constants under `ParT` -/

/-- **The integer constants of `BLInv` that the tail reads**, under `ParT ne d n cfg.par`. -/
theorem tl_constsW {L : Layout} {n m K0 E ne : ℕ} {cfg : Cfg d} (hP : ParT ne d n cfg.par) {mo : Mode d}
    {t : ℕ} {σ : Env d} (h : BLInv L n m K0 E cfg mo t σ) :
    σ.sc s2p = (((2 : ℤ) ^ cfg.par.p : ℤ) : ℝ) ∧ |(2 : ℤ) ^ cfg.par.p| ≤ 2 ^ E ∧
    σ.sc s2pF = (((2 : ℤ) ^ cfg.par.pF : ℤ) : ℝ) ∧ |(2 : ℤ) ^ cfg.par.pF| ≤ 2 ^ E ∧
    σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec cfg.par.B) : ℤ) : ℝ) ∧ |(2 : ℤ) ^ (2 * gsm_prec cfg.par.B)| ≤ 2 ^ E ∧
    σ.sc s2eh = ((tlHN ne d n : ℤ) : ℝ) ∧ |tlHN ne d n| ≤ 2 ^ E ∧
    σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) ∧ |(cfg.par.Lam : ℤ)| ≤ 2 ^ E ∧
    σ.sc sRint = ((cfg.par.Rint : ℤ) : ℝ) ∧ |(cfg.par.Rint : ℤ)| ≤ 2 ^ E ∧
    σ.sc sEta = ((qn cfg.par.pF cfg.par.eta : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.eta| ≤ 2 ^ E ∧
    σ.sc sRho = ((qn cfg.par.pF cfg.par.rho : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.rho| ≤ 2 ^ E ∧
    σ.sc sW = ((qn cfg.par.pF cfg.par.W : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.W| ≤ 2 ^ E := by
  obtain ⟨-, -, c2, c3, c4, c5, -, c7, c8⟩ := h.consts
  obtain ⟨-, -, p2, p3, -, -, -, -, p8, -⟩ := h.par
  have e2 : σ.sc s2p = (((2 : ℤ) ^ cfg.par.p : ℤ) : ℝ) := by rw [c2]; push_cast; rfl
  have e3 : σ.sc s2pF = (((2 : ℤ) ^ cfg.par.pF : ℤ) : ℝ) := by rw [c3]; push_cast; rfl
  have e4 : σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec cfg.par.B) : ℤ) : ℝ) := by rw [c4]; push_cast; rfl
  have e5 : σ.sc s2eh = ((tlHN ne d n : ℤ) : ℝ) := by rw [c5, hP.eHat]; exact tlHN_eq ne d n
  have e7 : σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) := by rw [c7]; push_cast; rfl
  have e8 : σ.sc sRint = ((cfg.par.Rint : ℤ) : ℝ) := by rw [c8]; push_cast; rfl
  exact ⟨e2, h.slot_abs (by decide) e2, e3, h.slot_abs (by decide) e3, e4, h.slot_abs (by decide) e4, e5,
    h.slot_abs (by decide) e5, e7, h.slot_abs (by decide) e7, e8, h.slot_abs (by decide) e8, p2,
    h.slot_abs (by decide) p2, p3, h.slot_abs (by decide) p3, p8, h.slot_abs (by decide) p8⟩

/-- `ê = 1/tlHN` under `ParT`. -/
theorem tlW_eHat {ne n : ℕ} {P : BLP.Par} (hP : ParT ne d n P) : P.eHat = 1 / ((tlHN ne d n : ℤ) : ℚ) := by
  rw [hP.eHat]; exact tlN_eHat ne d n

/-- BL-OW's PARAM meets `ParT` on its round. -/
theorem parT_rd (R : RdW d) (hIn : InU d R.n R.δ R.r0 R.R0) :
    ParT (NeO d R.n (kDel R.δ)) d R.n (cfgV R.c).par :=
  parOW_parT d R.n R.δ hIn.hd hIn.hn

/-! ## The guard and the commit, with the arrays 0 and 1 -/

/-- **The guard on the machine**, keeping the arrays. -/
theorem XV.guardK {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {n m K0 E : ℕ} {cfg : Cfg d}
    {st : St d} {t : ℕ} {σ : Env d} {P0 : ℕ → EuclideanSpace ℝ (Fin d)}
    (hI : BLInv L n m K0 E cfg (.run st) t σ) (hp : σ.pts = P0) (hℓ : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xG L) σ 1 (fun σ' => RPost L n m K0 E cfg .guard t P0 σ' ∧ Keep01 σ σ') := by
  have hS := hI.lay.2.1
  refine XV.mono (XV.sconst hL (x := sMode) (by simp only [nS0, sMode] at hS ⊢; omega) (1 : ℚ) rfl
    (by rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))) le_rfl fun σ' e => ?_
  subst e
  exact ⟨⟨hI.toGuard, by simp [hp]⟩, Keep01.setSc _ _ _⟩

/-- **R15 behind the routine's flag**, keeping the arrays: v2.1's R15 run. -/
theorem XV.tComK {xcom : Layout → XCmd} {Cc kc : ℕ} (hcom : ComSpec xcom Cc kc) {L : Layout} {X : XCtx d}
    {ℓa ℓ n m K0 E t : ℕ} {cfg : Cfg d} {st : St d} {σ : Env d} {P0 : ℕ → EuclideanSpace ℝ (Fin d)}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {r : Option (Fin d → ℤ)} {e : ℕ}
    (hd1 : 1 ≤ d) (hL : LayOK L d ℓa) (hlay : BLLay L) (hI : BLInv L n m K0 E cfg (.run st) t σ)
    (hp : σ.pts = P0)
    (hA : ∀ i j : Fin d, σ.arr 26 (d * i + j) = qn cfg.par.p (Ap i j) ∧ OnG cfg.par.p (Ap i j) ∧
      |qn cfg.par.p (Ap i j)| ≤ 2 ^ E)
    (hB : ∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E)
    (hb : ∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E)
    (hG : ∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E)
    (hk : σ.sc 59 = qn cfg.par.p kp) (hkg : OnG cfg.par.p kp) (hkb : |qn cfg.par.p kp| ≤ 2 ^ E)
    (hl : σ.sc 63 = qn cfg.par.p lp) (hlg : OnG cfg.par.p lp) (hlb : |qn cfg.par.p lp| ≤ 2 ^ E)
    (hout : EllOut blkBL r e σ) (hx : ∀ x, r = some x → (∀ j, |x j| ≤ 2 ^ E) ∧ e ≤ E)
    (hT : Cc * (d + E + 1) ^ kc ≤ ℓ) (hTa : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) (hℓ : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xifS L sZ oE (xcom L) (xG L)) σ (Cc * (d + E + 1) ^ kc + 3)
      (fun σ' => RPost L n m K0 E cfg (match r with
        | none => .guard
        | some x => .run ⟨false, fun j => (x j : ℚ) / 2 ^ e, Ap, Bp, bp, kp, Gp, lp⟩) t P0 σ' ∧ Keep01 σ σ') := by
  have hz : σ.sc sZ = 0 := hI.consts.1
  have hS := hlay.1
  have h0 : |σ.sc sZ| < 2 ^ ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  cases r with
  | none =>
    have hf : σ.sc oE = 0 := hout
    exact XV.mono (XV.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XV.guardK hL hI hp hℓ)) (by omega) fun _ h => h
  | some x =>
    have hf : σ.sc oE = 1 := hout.1
    obtain ⟨bx, he⟩ := hx x rfl
    exact XV.mono (XV.ifS_t hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 1) hℓ (by norm_num)) (by rw [hz, hf]; exact one_pos)
      (hcom d L X ℓa ℓ n m K0 E t cfg st Ap Bp bp Gp kp lp x e σ hd1 hL hlay hI hA hB hb hG hk hkg hkb
        hl hlg hlb hout bx he hT hTa)) (by omega)
      fun σ' ⟨hI', _, hF'⟩ => ⟨⟨hI', by rw [hF'.2.2.2.2, hp]⟩, Keep01.ofA hF' nA_end⟩

/-! ## R14 and R15 -/

set_option maxHeartbeats 2000000 in
/-- **R14 LINE and R15 COMMIT of BL-OW on the machine**, keeping the arrays 0 and 1. -/
theorem XVO.t14W {xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpecW xdl Cl kl) (hcall : CallSpecW xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdW d} {E1 G2 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
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
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c) (m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp wmu) (R.t + 1) P0 σ' ∧
        Keep01 σ σ') := by
  have hP := parT_rd R hIn
  have hEG : R.E ≤ G2 := hT.hE.trans hG2
  have pG : (2 : ℤ) ^ E1 ≤ 2 ^ G2 := pow_le_pow_right₀ (by norm_num) hG2
  -- the data of R14
  refine XVO.seq (XVO.ofX (hdl d R.L R.ctx.X R.ℓa R.ℓ R.n 0 R.K0 G2 (R.t + 1) (NeO d R.n (kDel R.δ)) (cfgV R.c) st
    Bp bp kp wh Dw σ hIn.hd hIn.hn (NeO_pos _ hIn.hd hIn.hn) hP hL hlay (hT.inv.mono hEG)
    (fun i j => ⟨(hT.hB i j).1, (hT.hB i j).2.1, (hT.hB i j).2.2.trans pG⟩)
    (fun j => ⟨(hT.hb j).1, (hT.hb j).2.1, (hT.hb j).2.2.trans pG⟩) hT.hk hT.hkg (hT.hkb.trans pG) hDw hDwb h91 h31
    hℓ1 hℓa1)) fun σ1 ⟨hP1, d1, F1⟩ => ?_
  have hT1 := hT.data F1 d1
  have k1 : Keep01 σ σ1 := Keep01.ofA F1 nA_dat
  -- the call
  refine XVO.seq (hcall d R.L R.w R.n R.δ R.r0 R.R0 R.a R.K0 E1 R.ℓa R.ℓ _ (R.t + 1) (.run st) _ _ _ _ _ _ _ σ1 hIn
    hL hroom (hT1.inv.mono hT.hE) hP1 hℓ2 hℓa2) fun σ2 ⟨hO2, d2, F2⟩ => ?_
  have hT2 := hT1.call F2 d2
  have k2 : Keep01 σ σ2 := k1.trans (Keep01.ofA F2 nA_call)
  have ecall : callO R.c (Bp * Bpᵀ) bp (Lmu (cfgV R.c).par - kp) (Bit.BLP.rB (cfgV R.c).par / 2) (Bp * Bpᵀ)
      ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL (cfgV R.c).par d R.n) = callLO R.c R.n Bp bp kp wmu := by
    rw [hwmu]; rfl
  rw [show cfgWW d R.n R.δ R.r0 R.R0 R.a R.w = R.c from rfl, ecall] at hO2
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
      (XV.guardK hL hT2.inv hT2.pts hℓ))) (by omega) fun _ h => ⟨h.1, k2.trans h.2⟩
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
    exact XVO.mono (XVO.ofX (XV.tComK hcom (r := some x) hIn.hd hL hlay hT2.inv hT2.pts
      (fun i j => ⟨(hT2.hA i j).1, (hT2.hA i j).2.1, bA i j⟩) (fun i j => ⟨(hT2.hB i j).1, (hT2.hB i j).2.1, bB i j⟩)
      (fun j => ⟨(hT2.hb j).1, (hT2.hb j).2.1, bb j⟩) (fun j => ⟨(hT2.hG j).1, (hT2.hG j).2.1, bG j⟩)
      hT2.hk hT2.hkg bk hT2.hl hT2.hlg bl hO2' (fun x' hx' => by cases hx'; exact ⟨bx, be⟩) hℓ3 hℓa3 hℓ))
      le_rfl fun _ h => ⟨h.1, k2.trans h.2⟩

/-! ## R13 -/

set_option maxHeartbeats 4000000 in
/-- **R13 WMU of BL-OW on the machine**, keeping the arrays 0 and 1. -/
theorem XVO.t13W {xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpecW xdl Cl kl) (hcall : CallSpecW xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdW d} {E1 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
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
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) (R.t + 1) P0 σ' ∧ Keep01 σ σ') := by
  have hℓ : 1 ≤ R.ℓ := by omega
  have pE : (2 : ℤ) ^ R.E ≤ 2 ^ E1 := pow_le_pow_right₀ (by norm_num) hT.hE
  have hP := parT_rd R hIn
  obtain ⟨Dm, mu, hDm, eD, bD, hmu, hAst⟩ := tl_runVals hT.inv
  obtain ⟨eQ, bQ, eF, bF, eG, bG, -, -, -, -, -, -, -, -, -, -, eW, bW⟩ := tl_constsW hP hT.inv
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
  have k1 : Keep01 σ σ1 := Keep01.ofA F1 nA_13
  obtain ⟨t85, t86⟩ := tl_r13_test_abs (qn R.c.par.pF R.c.par.W) (Dm * 2 ^ R.c.par.p * 2 ^ R.c.par.p *
    2 ^ (2 * gsm_prec R.c.par.B)) (2 ^ R.c.par.pF) _ (8 * E1 + 3 * d + 2) R.ℓ bW2 bDw bF2 b4 bnn hℓb
  have hdec := tl_r13_dec R.c.par st s5 Γ mu Dm (2 ^ R.c.par.pF) (qn R.c.par.pF R.c.par.W) Ah hDm
    (by positivity) (fun j => (hmu j).2.2) (fun i j => (hAst i j).1) (fun _ _ => rfl) (tl_grid _ hP.W)
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
      (XVO.ofX (XV.guardK hL hT1.inv hT1.pts hℓ))) (by unfold u14O; omega) fun _ h => ⟨h.1, k1.trans h.2⟩
  · -- R14 and R15
    have hc' : ¬ (2 * R.c.par.W) ^ 2 < wmuOf R.c.par st s5 Γ ⬝ᵥ wmuOf R.c.par st s5 Γ := by
      rw [v85, v86, Int.cast_lt] at hc; exact fun h => hc (hdec.1 h)
    have em : m13O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) =
        m14O R.w.orc R.c R.n Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) := by
      unfold m13O; simp only [hc', ↓reduceIte]
    rw [em] at hpost ⊢
    have hDw : 0 < Dm * (2 : ℤ) ^ R.c.par.p * 2 ^ R.c.par.p * 2 ^ (2 * gsm_prec R.c.par.B) := by positivity
    exact XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [v85]; exact t85) (by rw [v86]; exact t86) hc
      (XVO.t14W hdl hcall hcom hIn hL hlay hroom hT1 (by omega) hDw (le_of_abs_le bDw) v91 (fun j => ⟨v31 j, bn j⟩)
        (tl_wmu R.c.par st s5 Γ mu Dm Ah hDm (fun j => (hmu j).2.2) (fun i j => (hAst i j).1)
          (fun _ _ => rfl)).symm hpost hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3 hℓ)) le_rfl fun _ h => ⟨h.1, k1.trans h.2⟩

end AdversarialBco.UW.ProgW
