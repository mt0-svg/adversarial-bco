/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRb
public import AdversarialBco.Bit.Transfer.XBLTailRf

@[expose] public section

/-!
# The tail of BL's round, part c: R13 WMU on the machine

`xT13`: R13's values (`xR13`), then R13's guard `sc 85 < sc 86`, else R14 and R15 (`xT14`). From `TIn`, it ends in
`RPost` with the mode `m13` at `w_μ = wmuOf`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The state's numerators of `μ'` and `A'` from `BLInv` in mode `run`. -/
theorem tl_runVals {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg (.run st) t σ) :
    ∃ (Dm : ℤ) (mu : Fin d → ℤ), 0 < Dm ∧ σ.sc sDmu = Dm ∧ |Dm| ≤ 2 ^ E ∧
      (∀ j : Fin d, σ.arr aMu j = mu j ∧ |mu j| ≤ 2 ^ E ∧ (mu j : ℚ) / Dm = st.mu j) ∧
      (∀ i j : Fin d, OnG cfg.par.p (st.A i j) ∧ |qn cfg.par.p (st.A i j)| ≤ 2 ^ E) := by
  obtain ⟨-, -, ⟨Dm, hDm, hDm', hmu⟩, hAst, -⟩ := h.mode
  choose mu hmu1 hmu2 using hmu
  have hdi : ∀ i j : Fin d, d * i + j < asz d := fun i j => by
    unfold asz
    have := i.2; have := j.2
    nlinarith
  refine ⟨Dm, mu, hDm, hDm', h.slot_abs (by decide) hDm', fun j => ⟨hmu1 j, h.arr_abs (by decide) ?_ (hmu1 j),
    hmu2 j⟩, fun i j => ⟨(hAst i j).2, h.arr_abs (by decide) (hdi i j) (hAst i j).1⟩⟩
  unfold asz; have := j.2; nlinarith

/-- The integer constants of `BLInv` that the tail reads. -/
theorem tl_consts {L : Layout} {n m K0 E : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E (mkCfg d n m A b c S) mo t σ) :
    σ.sc s2p = (((2 : ℤ) ^ (par d n).p : ℤ) : ℝ) ∧ |(2 : ℤ) ^ (par d n).p| ≤ 2 ^ E ∧
    σ.sc s2pF = (((2 : ℤ) ^ (par d n).pF : ℤ) : ℝ) ∧ |(2 : ℤ) ^ (par d n).pF| ≤ 2 ^ E ∧
    σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec (par d n).B) : ℤ) : ℝ) ∧ |(2 : ℤ) ^ (2 * gsm_prec (par d n).B)| ≤ 2 ^ E ∧
    σ.sc s2eh = ((tlH d n : ℤ) : ℝ) ∧ |tlH d n| ≤ 2 ^ E ∧
    σ.sc sLam = (((par d n).Lam : ℤ) : ℝ) ∧ |((par d n).Lam : ℤ)| ≤ 2 ^ E ∧
    σ.sc sRint = (((par d n).Rint : ℤ) : ℝ) ∧ |((par d n).Rint : ℤ)| ≤ 2 ^ E ∧
    σ.sc sEta = ((qn (par d n).pF (par d n).eta : ℤ) : ℝ) ∧ |qn (par d n).pF (par d n).eta| ≤ 2 ^ E ∧
    σ.sc sRho = ((qn (par d n).pF (par d n).rho : ℤ) : ℝ) ∧ |qn (par d n).pF (par d n).rho| ≤ 2 ^ E ∧
    σ.sc sW = ((qn (par d n).pF (par d n).W : ℤ) : ℝ) ∧ |qn (par d n).pF (par d n).W| ≤ 2 ^ E := by
  obtain ⟨-, -, c2, c3, c4, c5, -, c7, c8⟩ := h.consts
  obtain ⟨-, -, p2, p3, -, -, -, -, p8, -⟩ := h.par
  have e2 : σ.sc s2p = (((2 : ℤ) ^ (par d n).p : ℤ) : ℝ) := by rw [c2]; push_cast; rfl
  have e3 : σ.sc s2pF = (((2 : ℤ) ^ (par d n).pF : ℤ) : ℝ) := by rw [c3]; push_cast; rfl
  have e4 : σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec (par d n).B) : ℤ) : ℝ) := by rw [c4]; push_cast; rfl
  have e5 : σ.sc s2eh = ((tlH d n : ℤ) : ℝ) := by rw [c5]; exact tlH_eq d n
  have e7 : σ.sc sLam = (((par d n).Lam : ℤ) : ℝ) := by rw [c7]; push_cast; rfl
  have e8 : σ.sc sRint = (((par d n).Rint : ℤ) : ℝ) := by rw [c8]; push_cast; rfl
  exact ⟨e2, h.slot_abs (by decide) e2, e3, h.slot_abs (by decide) e3, e4, h.slot_abs (by decide) e4, e5,
    h.slot_abs (by decide) e5, e7, h.slot_abs (by decide) e7, e8, h.slot_abs (by decide) e8, p2,
    h.slot_abs (by decide) p2, p3, h.slot_abs (by decide) p3, p8, h.slot_abs (by decide) p8⟩

/-- R13, then its guard, then R14 and R15. -/
def xT13 (xdl xcall xcom : Layout → XCmd) (L : Layout) : XCmd :=
  .seq (xR13 L) (xifS L 85 86 (xG L) (xT14 xdl xcall xcom L))

/-- The units of `xT13`. -/
def u13 (Cl kl Ca ka Cc kc d m Ms E E1 : ℕ) : ℕ :=
  r13Units d + (u14 Cl kl Ca ka Cc kc d m Ms E E1 (8 * E1 + 3 * d + 2) + 2)

set_option maxHeartbeats 2000000 in
/-- **R13 WMU on the machine.** -/
theorem XV.t13 {xdl xcall xcom : Layout → XCmd} {Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdl : DLSpec xdl Cl kl) (hcall : CallSpec xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E E1 ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {s5 : ℤ} {Γ : Fin d → ℤ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d}
    (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hok : blkBL.OK L nS nN nA)
    (hM : RealRAM.HeightLE A b M) (he : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1)
    (hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hpost : TPost (mkCfg d n m A b c S) n E Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)
      (m13 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)))
    (hℓa : 4 * (2 * E1 + d) + 1 < ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < ℓ)
    (hℓc : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ ℓ) (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ ℓa)
    (hℓ2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ ℓ)
    (hℓa2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ ℓa)
    (hℓ3 : Cc * (d + E + 1) ^ kc ≤ ℓ) (hℓa3 : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xT13 xdl xcall xcom L) σ (u13 Cl kl Ca ka Cc kc d m M.size E E1)
      (RPost L n m K0 E (mkCfg d n m A b c S)
        (m13 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)) t P0) := by
  set cfg := mkCfg d n m A b c S with hcfg
  have hℓ : 1 ≤ ℓ := by omega
  have pE : (2 : ℤ) ^ E ≤ 2 ^ E1 := pow_le_pow_right₀ (by norm_num) hT.hE
  obtain ⟨Dm, mu, hDm, eD, bD, hmu, hAst⟩ := tl_runVals hT.inv
  obtain ⟨eQ, bQ, eF, bF, eG, bG, -, -, -, -, -, -, -, -, -, -, eW, bW⟩ := tl_consts hT.inv
  set Ah : Matrix (Fin d) (Fin d) ℤ := fun i j => qn (par d n).p (st.A i j) with hAh
  obtain ⟨bw, bn, bDw, bF2, bW2, b4, bnn⟩ := tl_r13_bnds (2 ^ (par d n).p) (2 ^ (2 * gsm_prec (par d n).B)) Dm s5
    (2 ^ (par d n).pF) (qn (par d n).pF (par d n).W) mu Γ Ah E1 (bQ.trans pE) (bG.trans pE) (bD.trans pE) hT.hsb
    (bF.trans pE) (bW.trans pE) (fun j => (hmu j).2.1.trans pE) (fun i j => (hAst i j).2.trans pE) hT.hΓ
  have pG : (2 : ℤ) ^ E1 ≤ 2 ^ (2 * E1 + d) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- R13's values
  refine XV.seq (XV.r13 hL hlay (σ := σ) (mu := mu) (w := Ah *ᵥ Γ) (Gu := 2 * E1 + d) (G2 := 8 * E1 + 3 * d + 2)
    hT.inv.regs.1 hT.inv.regs.2.2.2.1 hT.inv.consts.1 hT.c4 (fun j => (hmu j).1) hT.hw eF eQ eG eD hT.hs eW
    (fun j => ((hmu j).2.1.trans pE).trans pG) bw ((bQ.trans pE).trans pG) ((bG.trans pE).trans pG)
    ((bD.trans pE).trans pG) (hT.hsb.trans pG) bn bDw bF2 bW2 b4 bnn hℓa hℓb hℓc hda) fun σ1 ⟨v31, v91, v85, v86, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [S13, tR, nSP] at hy ⊢; omega) (fun j hj => by simp only [N13] at hj; omega)
    (fun a k hk => by simp only [A13, nAP] at hk ⊢; omega) d1
  obtain ⟨t85, t86⟩ := tl_r13_test_abs (qn (par d n).pF (par d n).W) (Dm * 2 ^ (par d n).p * 2 ^ (par d n).p *
    2 ^ (2 * gsm_prec (par d n).B)) (2 ^ (par d n).pF) _ (8 * E1 + 3 * d + 2) ℓ bW2 bDw bF2 b4 bnn hℓb
  have hdec := tl_r13_dec (par d n) st s5 Γ mu Dm (2 ^ (par d n).pF) (qn (par d n).pF (par d n).W) Ah hDm
    (by positivity) (fun j => (hmu j).2.2) (fun i j => (hAst i j).1) (fun _ _ => rfl) (tl_grid _ (tl_onG_W d n))
  have hS := hlay.1
  by_cases hc : σ1.sc 85 < σ1.sc 86
  · -- the guard
    have hc' : (2 * cfg.par.W) ^ 2 < wmuOf (par d n) st s5 Γ ⬝ᵥ wmuOf (par d n) st s5 Γ := by
      rw [v85, v86, Int.cast_lt] at hc; exact hdec.2 hc
    have em : m13 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) = .guard := by unfold m13; simp only [hc', ↓reduceIte]
    rw [em]
    exact XV.mono (XV.ifS_t hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v85]; exact t85) (by rw [v86]; exact t86) hc (XV.guard hL hT1.inv hT1.pts hℓ))
      (by unfold u14; omega) fun _ h => h
  · -- R14 and R15
    have hc' : ¬ (2 * cfg.par.W) ^ 2 < wmuOf (par d n) st s5 Γ ⬝ᵥ wmuOf (par d n) st s5 Γ := by
      rw [v85, v86, Int.cast_lt] at hc; exact fun h => hc (hdec.1 h)
    have em : m13 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) =
        m14 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) := by unfold m13; simp only [hc', ↓reduceIte]
    rw [em] at hpost ⊢
    have hDw : 0 < Dm * (2 : ℤ) ^ (par d n).p * 2 ^ (par d n).p * 2 ^ (2 * gsm_prec (par d n).B) := by positivity
    exact XV.ifS_f hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v85]; exact t85) (by rw [v86]; exact t86) hc
      (XV.t14 hdl hcall hcom hd1 hn hL hlay hok hM he he0 he1 hT1 (by omega) hDw
        (le_of_abs_le bDw) v91 (fun j => ⟨v31 j, bn j⟩)
        (tl_wmu (par d n) st s5 Γ mu Dm Ah hDm (fun j => (hmu j).2.2) (fun i j => (hAst i j).1) (fun _ _ => rfl)).symm
        hpost hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3 hℓ)

end AdversarialBco.Bit.Transfer.BLM
