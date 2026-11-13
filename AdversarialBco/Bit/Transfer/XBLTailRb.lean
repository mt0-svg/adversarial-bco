/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRa

@[expose] public section

/-!
# The tail of BL's round, part b: R14 LINE and R15 COMMIT on the machine

`xT14`: the data of R14 (`DataL`), the call (`CallBL`), then the routine's flag: `0` leaves for `guard`, `1` commits
the new state (`CommitBL`). From `TIn` and `ŵ` over `D_w` in the array `31` and the slot `91` (`w_μ = ŵ/D_w`), it
ends in `RPost` with the mode `m14`. `TPost`: the caller's bounds of the new state, asked when a stage's mode is the
new state.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The bounds that the caller gives when the mode `mo` of a stage is the new state. -/
def TPost (cfg : Cfg d) (n E : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (wmu : Fin d → ℚ) (mo : Mode d) : Prop :=
  ∀ mu' : Fin d → ℚ, mo = .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ →
    StBnd cfg.par.p E cfg.par.Rint ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ ∧
    ∀ x, ellRI (clearQ (callLOf cfg n Bp bp kp wmu)) = some x →
      (∀ j, |x j| ≤ 2 ^ E) ∧ ellExp (clearQ (callLOf cfg n Bp bp kp wmu)) ≤ E

/-- The frame of `DataT` and `DataL` keeps `TIn`. -/
theorem TIn.data {L : Layout} {n m K0 E E1 : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {σ σ' : Env d}
    (h : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hF : FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
      (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ') (hd : σ'.draws = σ.draws) :
    TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ' :=
  h.frame hF (fun y hy => by simp only [sPl, nSP] at hy ⊢; omega) (fun j hj => by omega)
    (fun a k hk => by simp only [aPHn, aPfd, nAP] at hk ⊢; omega) hd

/-- The frame of a call keeps `TIn`. -/
theorem TIn.call {L : Layout} {n m K0 E E1 : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {σ σ' : Env d}
    (h : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hF : FrameA (fun y => oE ≤ y ∨ SPrep y) (fun j => rEE ≤ j ∨ NPrep j) (fun a _ => aWE ≤ a ∨ APrep a) σ σ')
    (hd : σ'.draws = σ.draws) : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ' :=
  h.frame hF (fun y hy => by simp only [oE, SPrep, SRow, sEl, nSP] at hy ⊢; omega)
    (fun j hj => by simp only [rEE, NPrep, NRow] at hj; omega)
    (fun a k hk => by simp only [aWE, APrep, ARow, aEH, aEf, nAP] at hk ⊢; omega) hd

/-- R14 and R15: the data, the call, the flag. -/
def xT14 (xdl xcall xcom : Layout → XCmd) (L : Layout) : XCmd :=
  .seq (xdl L) (.seq (xcall L) (xifS L sZ oE (xcom L) (xG L)))

/-- The units of `xT14`. -/
def u14 (Cl kl Ca ka Cc kc d m Ms E E1 G2 : ℕ) : ℕ :=
  Cl * (d + G2 + 1) ^ kl + (Ca * (d + m + Ms + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka + (Cc * (d + E + 1) ^ kc + 3))

set_option maxHeartbeats 1000000 in
/-- **R14 LINE and R15 COMMIT on the machine.** -/
theorem XV.t14 {xdl xcall xcom : Layout → XCmd} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpec xdl Cl kl) (hcall : CallSpec xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E E1 G2 ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {s5 : ℤ} {Γ : Fin d → ℤ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {wh : Fin d → ℤ} {Dw : ℤ} {wmu : Fin d → ℚ}
    (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hok : blkBL.OK L nS nN nA)
    (hM : RealRAM.HeightLE A b M) (he : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1)
    (hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hG2 : E1 ≤ G2) (hDw : 0 < Dw) (hDwb : Dw ≤ 2 ^ G2) (h91 : σ.sc 91 = Dw)
    (h31 : ∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ G2) (hwmu : (fun j => (wh j : ℚ) / Dw) = wmu)
    (hpost : TPost (mkCfg d n m A b c S) n E Ap Bp bp Gp kp lp wmu (m14 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp wmu))
    (hℓ1 : Cl * (d + G2 + 1) ^ kl ≤ ℓ) (hℓa1 : Cl * (d + G2 + 1) ^ kl < 2 ^ ℓa)
    (hℓ2 : Ca * (d + m + M.size + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka ≤ ℓ)
    (hℓa2 : Ca * (d + m + M.size + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka < 2 ^ ℓa)
    (hℓ3 : Cc * (d + E + 1) ^ kc ≤ ℓ) (hℓa3 : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) (hℓ : 1 ≤ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xT14 xdl xcall xcom L) σ (u14 Cl kl Ca ka Cc kc d m M.size E E1 G2)
      (RPost L n m K0 E (mkCfg d n m A b c S) (m14 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp wmu) t P0) := by
  set cfg := mkCfg d n m A b c S with hcfg
  have hEG : E ≤ G2 := hT.hE.trans hG2
  have pG : (2 : ℤ) ^ E1 ≤ 2 ^ G2 := pow_le_pow_right₀ (by norm_num) hG2
  -- the data of R14
  refine XV.seq (hdl d L (ctxOf w n m A b) ℓa ℓ n m K0 G2 t cfg st Bp bp kp wh Dw σ hd1 hn rfl hL hlay
    (hT.inv.mono hEG) (fun i j => ⟨(hT.hB i j).1, (hT.hB i j).2.1, (hT.hB i j).2.2.trans pG⟩)
    (fun j => ⟨(hT.hb j).1, (hT.hb j).2.1, (hT.hb j).2.2.trans pG⟩) hT.hk hT.hkg (hT.hkb.trans pG) hDw hDwb h91 h31
    hℓ1 hℓa1) fun σ1 ⟨hP1, d1, F1⟩ => ?_
  have hT1 := hT.data F1 d1
  -- the call
  refine XV.seq (hcall d L w n m M E1 ℓa ℓ _ A b c S _ _ _ _ _ _ _ σ1 hd1 hL hok hM he he0 he1
    ((hT1.inv.mono hT.hE).rowCtx hlay) hP1 hℓ2 hℓa2) fun σ2 ⟨hO2, d2, F2⟩ => ?_
  have hT2 := hT1.call F2 d2
  have ecall : callOf cfg (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (BLP.rB cfg.par / 2) (Bp * Bpᵀ)
      ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL cfg.par d n) = callLOf cfg n Bp bp kp wmu := by
    rw [hwmu]; rfl
  rw [ecall] at hO2
  have hS := hlay.1
  have hz : σ2.sc sZ = 0 := hT2.inv.consts.1
  have h0 : |σ2.sc sZ| < 2 ^ ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  -- the flag
  rcases hr : ellRI (clearQ (callLOf cfg n Bp bp kp wmu)) with _ | x
  · rw [hr] at hO2
    have hf : σ2.sc oE = 0 := hO2
    have em : m14 cfg n Ap Bp bp Gp kp lp wmu = .guard := by
      unfold m14; rw [tl_ap_none _ hr]
    rw [em]
    exact XV.mono (XV.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XV.guard hL hT2.inv hT2.pts hℓ)) (by omega) fun _ h => h
  · have em : m14 cfg n Ap Bp bp Gp kp lp wmu =
        .run ⟨false, fun j => (x j : ℚ) / 2 ^ ellExp (clearQ (callLOf cfg n Bp bp kp wmu)), Ap, Bp, bp, kp, Gp, lp⟩ := by
      unfold m14; rw [tl_ap_some _ x hr]
    obtain ⟨hB, hx⟩ := hpost _ em
    obtain ⟨bA, bB, bb, bk, bG, bl, -⟩ := hB
    obtain ⟨bx, be⟩ := hx x hr
    rw [em]
    have hO2' : EllOut blkBL (some x) (ellExp (clearQ (callLOf cfg n Bp bp kp wmu))) σ2 := by rw [← hr]; exact hO2
    exact XV.mono (XV.tCom hcom (r := some x) hd1 hL hlay hT2.inv hT2.pts
      (fun i j => ⟨(hT2.hA i j).1, (hT2.hA i j).2.1, bA i j⟩) (fun i j => ⟨(hT2.hB i j).1, (hT2.hB i j).2.1, bB i j⟩)
      (fun j => ⟨(hT2.hb j).1, (hT2.hb j).2.1, bb j⟩) (fun j => ⟨(hT2.hG j).1, (hT2.hG j).2.1, bG j⟩)
      hT2.hk hT2.hkg bk hT2.hl hT2.hlg bl hO2' (fun x' hx' => by cases hx'; exact ⟨bx, be⟩) hℓ3 hℓa3 hℓ)
      (by omega) fun _ h => h

end AdversarialBco.Bit.Transfer.BLM
