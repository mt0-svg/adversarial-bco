/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRc

@[expose] public section

/-!
# The tail of BL's round, part d: R12 FIRE and R11 TEST on the machine

* `xT12`: R12's values (`xR12`) at the test point `x/2^X` that R11's call left in its block, then the test
  `sc 87 < sc 86` (no fire: R13 to R15, `xT13`), else the new epoch (`FireBL`). It ends in `RPost` with `m12`.
* `xT11`: the data of R11 (`DataT`), the call (`CallBL`), then the routine's flag: `0` leaves for `guard`, `1` goes on
  with `xT12`. It ends in `RPost` with `m11`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- R12, then the fire or R13 to R15. -/
def xT12 (xfire xdl xcall xcom : Layout → XCmd) (L : Layout) : XCmd :=
  .seq (xR12 L) (xifS L 87 86 (xT13 xdl xcall xcom L) (xfire L))

/-- The units of `xT12`. -/
def u12 (Cf kf Cl kl Ca ka Cc kc d m Ms E E1 X : ℕ) : ℕ :=
  r12Units d X + (u13 Cl kl Ca ka Cc kc d m Ms E E1 + Cf * (d + E + 1) ^ kf + 2)

theorem r12Units_mono (d : ℕ) {X X' : ℕ} (h : X ≤ X') : r12Units d X ≤ r12Units d X' := by
  unfold r12Units; gcongr

set_option maxHeartbeats 4000000 in
/-- **R12 FIRE on the machine.** -/
theorem XV.t12 {xfire xdl xcall xcom : Layout → XCmd} {Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hfire : FireSpec xfire Cf kf) (hdl : DLSpec xdl Cl kl) (hcall : CallSpec xcall Ca ka nS nN nA)
    (hcom : ComSpec xcom Cc kc)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E E1 ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {s5 : ℤ} {Γ : Fin d → ℤ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {x : Fin d → ℤ} {Xe Xb : ℕ}
    (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hok : blkBL.OK L nS nN nA)
    (hM : RealRAM.HeightLE A b M) (he : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1)
    (hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hO : EllOut blkBL (some x) Xe σ) (hx : ∀ j, |x j| ≤ 2 ^ (Xe + E1)) (hXb : Xe ≤ Xb)
    (hpost : TPost (mkCfg d n m A b c S) n E Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)
      (m12 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) fun i => (x i : ℚ) / 2 ^ Xe))
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ ℓ) (hXa : Xb < 2 ^ ℓa)
    (hℓf : Cf * (d + E + 1) ^ kf ≤ ℓ) (hℓaf : Cf * (d + E + 1) ^ kf < 2 ^ ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < ℓ)
    (hℓc : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ ℓ) (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ ℓa)
    (hℓ2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ ℓ)
    (hℓa2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ ℓa)
    (hℓ3 : Cc * (d + E + 1) ^ kc ≤ ℓ) (hℓa3 : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xT12 xfire xdl xcall xcom L) σ (u12 Cf kf Cl kl Ca ka Cc kc d m M.size E E1 Xb)
      (RPost L n m K0 E (mkCfg d n m A b c S)
        (m12 (mkCfg d n m A b c S) n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) fun i => (x i : ℚ) / 2 ^ Xe) t P0) := by
  set cfg := mkCfg d n m A b c S with hcfg
  set Gu := 4 * E1 + 2 * Xe + 3 * d with hGu
  have hGub : Gu ≤ 4 * E1 + 2 * Xb + 3 * d := by omega
  have pE : (2 : ℤ) ^ E ≤ 2 ^ Gu := pow_le_pow_right₀ (by norm_num) (by have := hT.hE; omega)
  obtain ⟨eQ, bQ, eF, bF, -, -, eH, bH, -, -, -, bR, eE, bE, eR, bRh, -, -⟩ := tl_consts hT.inv
  set Bh : Matrix (Fin d) (Fin d) ℤ := fun i j => qn (par d n).p (Bp i j) with hBh
  set bh : Fin d → ℤ := fun j => qn (par d n).p (bp j) with hbh
  set Gh : Fin d → ℤ := fun j => qn (par d n).p (Gp j) with hGh
  obtain ⟨bB, bx, bb, bG, bBx, bBB, bbx, bGx, bD⟩ := tl_r12_bnds Bh bh Gh x E1 Xe (fun i j => (hT.hB i j).2.2)
    (fun j => (hT.hb j).2.2) (fun j => (hT.hG j).2.2) hx
  have pE1 : (2 : ℤ) ^ E1 ≤ 2 ^ Gu := pow_le_pow_right₀ (by norm_num) (by omega)
  have hg2' : d * 2 ^ (2 * Gu) < 2 ^ ℓ :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))) hg2
  have eX : σ.sc 769 = ((Xe : ℤ) : ℝ) := by rw [Int.cast_natCast]; exact hO.2.1
  refine XV.mono (K := r12Units d Xe + (u13 Cl kl Ca ka Cc kc d m M.size E E1 + Cf * (d + E + 1) ^ kf + 2)) ?_
    (Nat.add_le_add_right (r12Units_mono d hXb) _) fun _ h => h
  -- R12 values
  refine XV.seq (XV.r12 hL hlay (σ := σ) (Bh := Bh) (bh := bh) (Gh := Gh) (x := x) (Xe := Xe) (Gu := Gu) hT.inv.regs.1
    hT.inv.regs.2.2.2.1 hT.inv.consts.1 hT.c2 eX hO.2.2 (fun i j => (hT.hB i j).1) (fun j => (hT.hb j).1)
    (fun j => (hT.hG j).1) eF eQ eH eE hT.hl hT.hk eR bB bx bb bG bBx (bF.trans pE) (bQ.trans pE) (bH.trans pE)
    (bE.trans pE) (hT.hlb.trans pE1) (hT.hkb.trans pE1) (bRh.trans pE) bD bBB bbx bGx (by omega) hg2' (by omega)
    (by omega) (by omega)) fun σ1 ⟨_, v86, v87, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [S12, tR, nSP] at hy ⊢; omega)
    (fun j hj => by simp only [N12] at hj; omega) (fun a k hk => by simp only [A12, nAP] at hk ⊢; omega) d1
  obtain ⟨t86, t87⟩ := tl_r12_test_abs (2 ^ (par d n).pF) (2 ^ (par d n).p) (2 ^ Xe) (tlH d n)
    (qn (par d n).pF (par d n).eta) (qn (par d n).p lp) (qn (par d n).p kp) (qn (par d n).pF (par d n).rho) Bh Gh bh x
    Gu ℓ (bF.trans pE) (bQ.trans pE) (by rw [abs_of_nonneg (by positivity)]; exact bD) (bH.trans pE) (bE.trans pE)
    (hT.hlb.trans pE1) (hT.hkb.trans pE1) (bRh.trans pE) bB bG bb bx (by omega)
  have hdec := tl_r12_dec (par d n) Bp bp Gp (fun i => (x i : ℚ) / 2 ^ Xe) kp lp (2 ^ (par d n).pF) (2 ^ (par d n).p)
    (2 ^ Xe) (tlH d n) (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).rho) (qn (par d n).p lp)
    (qn (par d n).p kp) Bh bh Gh x (by positivity) (by positivity) (by positivity) (tlH_pos d n)
    (tl_grid _ (tl_onG_eta d n)) (tl_grid _ (tl_onG_rho d n)) (tl_eHat d n)
    (by ext i j; exact tl_grid _ (hT.hB i j).2.1) (by funext j; exact tl_grid _ (hT.hb j).2.1)
    (by funext j; exact tl_grid _ (hT.hG j).2.1) (tl_grid _ hT.hkg) (tl_grid _ hT.hlg) (by funext i; push_cast; rfl)
  have hS := hlay.1
  by_cases hc : σ1.sc 87 < σ1.sc 86
  · -- no fire: R13 to R15
    have hc' : ¬ (cfg.par.eta * (lp - Gp ⬝ᵥ fun i => (x i : ℚ) / 2 ^ Xe) -
        2 * ((fun i => (x i : ℚ) / 2 ^ Xe) ⬝ᵥ ((Bp * Bpᵀ) *ᵥ fun i => (x i : ℚ) / 2 ^ Xe) / 2 -
          bp ⬝ᵥ (fun i => (x i : ℚ) / 2 ^ Xe) + kp) ≤ -cfg.par.rho + cfg.par.eHat) := by
      rw [v86, v87, Int.cast_lt] at hc
      exact fun h => absurd (hdec.1 h) (not_le.2 hc)
    have em : m12 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) (fun i => (x i : ℚ) / 2 ^ Xe) =
        m13 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) := by unfold m12; simp only [hc', ↓reduceIte]
    rw [em] at hpost ⊢
    exact XV.mono (XV.ifS_t hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v87]; exact t87) (by rw [v86]; exact t86) hc
      (XV.t13 hdl hcall hcom hd1 hn hL hlay hok hM he he0 he1 hT1 hpost hℓa hℓb hℓc hda hℓ1 hℓa1 hℓ2 hℓa2 hℓ3
        hℓa3)) (by omega) fun _ h => h
  · -- the fire: a new epoch
    have hc' : cfg.par.eta * (lp - Gp ⬝ᵥ fun i => (x i : ℚ) / 2 ^ Xe) -
        2 * ((fun i => (x i : ℚ) / 2 ^ Xe) ⬝ᵥ ((Bp * Bpᵀ) *ᵥ fun i => (x i : ℚ) / 2 ^ Xe) / 2 -
          bp ⬝ᵥ (fun i => (x i : ℚ) / 2 ^ Xe) + kp) ≤ -cfg.par.rho + cfg.par.eHat := by
      rw [v86, v87, Int.cast_lt] at hc
      exact hdec.2 (not_lt.1 hc)
    have em : m12 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) (fun i => (x i : ℚ) / 2 ^ Xe) =
        .run (init cfg.par d) := by unfold m12; simp only [hc', ↓reduceIte]
    rw [em]
    exact XV.mono (XV.ifS_f hL (by simp only [oE] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega)
      (by rw [v87]; exact t87) (by rw [v86]; exact t86) hc
      (hfire d L (ctxOf w n m A b) ℓa ℓ n m K0 E t cfg st σ1 hd1 hn rfl hL hlay hT1.inv hℓf hℓaf))
      (by omega) fun σ' ⟨hI', _, hF'⟩ => ⟨hI', by rw [hF'.2.2.2.2, hT1.pts]⟩

/-- R11's data, the call, the flag, then R12. -/
def xT11 (xdt xcall xfire xdl xcom : Layout → XCmd) (L : Layout) : XCmd :=
  .seq (xdt L) (.seq (xcall L) (xifS L sZ oE (xT12 xfire xdl xcall xcom L) (xG L)))

/-- The units of `xT11`. -/
def u11 (Ct kt Cf kf Cl kl Ca ka Cc kc d m Ms E E1 X : ℕ) : ℕ :=
  Ct * (d + E1 + 1) ^ kt + (Ca * (d + m + Ms + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka +
    (u12 Cf kf Cl kl Ca ka Cc kc d m Ms E E1 X + 2))

set_option maxHeartbeats 2000000 in
/-- **R11 TEST on the machine.** -/
theorem XV.t11 {xdt xfire xdl xcall xcom : Layout → XCmd} {Ct kt Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdt : DTSpec xdt Ct kt) (hfire : FireSpec xfire Cf kf) (hdl : DLSpec xdl Cl kl)
    (hcall : CallSpec xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E E1 ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {s5 : ℤ} {Γ : Fin d → ℤ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {Xb : ℕ}
    (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hok : blkBL.OK L nS nN nA)
    (hM : RealRAM.HeightLE A b M) (he : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1)
    (hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hX : ellExp (clearQ (callTOf (mkCfg d n m A b c S) st Bp bp Gp)) ≤ Xb)
    (hpost : TPost (mkCfg d n m A b c S) n E Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)
      (m11 (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)))
    (hℓt : Ct * (d + E1 + 1) ^ kt ≤ ℓ) (hℓat : Ct * (d + E1 + 1) ^ kt < 2 ^ ℓa)
    (hℓc : Ca * (d + m + M.size + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ ℓ)
    (hℓac : Ca * (d + m + M.size + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka < 2 ^ ℓa)
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ ℓ) (hXa : Xb < 2 ^ ℓa)
    (hℓf : Cf * (d + E + 1) ^ kf ≤ ℓ) (hℓaf : Cf * (d + E + 1) ^ kf < 2 ^ ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < ℓ)
    (hℓc' : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ ℓ) (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ ℓa)
    (hℓ2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ ℓ)
    (hℓa2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ ℓa)
    (hℓ3 : Cc * (d + E + 1) ^ kc ≤ ℓ) (hℓa3 : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xT11 xdt xcall xfire xdl xcom L) σ
      (u11 Ct kt Cf kf Cl kl Ca ka Cc kc d m M.size E E1 Xb)
      (RPost L n m K0 E (mkCfg d n m A b c S)
        (m11 (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)) t P0) := by
  set cfg := mkCfg d n m A b c S with hcfg
  have hℓ : 1 ≤ ℓ := by omega
  -- the data of R11
  refine XV.seq (hdt d L (ctxOf w n m A b) ℓa ℓ n m K0 E1 t cfg st Bp bp Gp σ hd1 hn rfl hL hlay
    (hT.inv.mono hT.hE) hT.hB hT.hb hT.hG hℓt hℓat) fun σ1 ⟨hP1, d1, F1⟩ => ?_
  have hT1 := hT.data F1 d1
  -- the call
  refine XV.seq (hcall d L w n m M E1 ℓa ℓ _ A b c S _ _ _ _ _ _ _ σ1 hd1 hL hok hM he he0 he1
    ((hT1.inv.mono hT.hE).rowCtx hlay) hP1 hℓc hℓac) fun σ2 ⟨hO2, d2, F2⟩ => ?_
  have hT2 := hT1.call F2 d2
  rw [← tl_callT] at hO2
  have hS := hlay.1
  have hz : σ2.sc sZ = 0 := hT2.inv.consts.1
  have h0 : |σ2.sc sZ| < 2 ^ ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  rcases hr : ellRI (clearQ (callTOf cfg st Bp bp Gp)) with _ | x
  · rw [hr] at hO2
    have hf : σ2.sc oE = 0 := hO2
    have em : m11 cfg n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) = .guard := by
      unfold m11; rw [tl_ap_none _ hr]
    rw [em]
    exact XV.mono (XV.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XV.guard hL hT2.inv hT2.pts hℓ)) (by unfold u12 r12Units; omega) fun _ h => h
  · rw [hr] at hO2
    have hf : σ2.sc oE = 1 := hO2.1
    have em : m11 cfg n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) =
        m12 cfg n Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)
          (fun i => (x i : ℚ) / 2 ^ ellExp (clearQ (callTOf cfg st Bp bp Gp))) := by
      unfold m11; rw [tl_ap_some _ x hr]
    rw [em] at hpost ⊢
    have hR : (cfg.par.Rint : ℤ) ≤ 2 ^ E1 :=
      (le_abs_self _).trans ((tl_consts hT.inv).2.2.2.2.2.2.2.2.2.2.2.1.trans
        (pow_le_pow_right₀ (by norm_num) hT.hE))
    have hx : ∀ j, |x j| ≤ 2 ^ (ellExp (clearQ (callTOf cfg st Bp bp Gp)) + E1) := by
      intro j
      have hr' := hr
      rw [tl_callT] at hr' ⊢
      exact tl_pt_abs cfg _ _ _ _ _ _ _ x E1 hr' hR j
    exact XV.mono (XV.ifS_t hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 1) hℓ (by norm_num)) (by rw [hz, hf]; exact one_pos)
      (XV.t12 hfire hdl hcall hcom hd1 hn hL hlay hok hM he he0 he1 hT2 hO2 hx hX hpost hg1 hg2 hXa hℓf hℓaf
        hℓa hℓb hℓc' hda hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3)) (by omega) fun _ h => h

end AdversarialBco.Bit.Transfer.BLM
