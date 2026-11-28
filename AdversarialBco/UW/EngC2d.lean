/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC2c
public import AdversarialBco.UW.EngC2w

@[expose] public section

/-!
# Piece C for BL-OW, part C2 (d): line μ, `C2OW` and the round

Unified/EngC2d.lean for BL-OW at BUD-W: E16w, BL-OW's Newton point of line μ against P°'s on the weighted path, split
by Lemma WR (on a weighted round the bound reads `Ξ_w` and `Δ^w_u`; on the other rounds both observations vanish and
both Newton points are the centre), BL-OW's guard `W` does not act (E18w), P°'s line μ under the advice returns
BL-OW's point `μ'` (Lemma VAL at the level `δ_e = 1/N_e`), and `c2OW : C2OW`, `roundCOW : RoundCOW`.
-/

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.EngC (callTO fireO wmuO callMO regO obj_M)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.Bit.BLP (refTest selT muOf)
open AdversarialBco.Bit.Cpl (apAdv advOK advPick)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-! ### E16w: the Newton point of line μ -/

/-- E16w on a weighted round: `|w'_μ - w°_μ| ≤ Δ_w`. -/
theorem wmu_err_w (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    (hwt : H.Wt) :
    oNorm (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) -
      (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Dw := by
  have S := H.sett
  have hη : 0 < (rW d c.n δ).eta := H.det.rows.pos_eta
  have htp := H.tp_small
  have htp0 := H.tp0
  have hq0 := H.qq_ge
  have hq : 99 / 100 ≤ (ctxOW K c δ ap).qq (pwOW K c δ ap π) s := by linarith
  have hDq := H.Dq_small
  have hq' : 99 / 100 ≤ (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) := by
    have := (abs_le.1 O.eq).1; linarith
  have hl0 : 0 ≤ (rW d c.n δ).lam := S.lam_pos.le
  have hl1 : (rW d c.n δ).lam ≤ 1 / 1000 := S.lam_le
  set x : ℚ := c.par.eta * (rvHW orc c δ st ξ' ζ' ε f).Y * c.par.nu / (rvHW orc c δ st ξ' ζ' ε f).q with hx
  set a' : ℚ := rnd c.par.p x with ha'
  set a : ℝ := (rW d c.n δ).eta * (ctxOW K c δ ap).Y (pwOW K c δ ap π) s /
    ((1 - (rW d c.n δ).lam) * (ctxOW K c δ ap).qq (pwOW K c δ ap π) s) with ha
  have hs5 := s5_err (rW d c.n δ).eta (c.par.eta : ℝ) ((ctxOW K c δ ap).Y (pwOW K c δ ap π) s)
    (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) (c.par.nu : ℝ) (rW d c.n δ).lam
    ((ctxOW K c δ ap).qq (pwOW K c δ ap π) s) (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) (rW d c.n δ).tp
    (rW d c.n δ).eYw (rW d c.n δ).y0 (rW d c.n δ).Dq hη.le H.eta_err H.nu_relH hl0 hl1 htp0 htp S.Y_le O.eY hq hq'
    O.eq
  have hrnd := rnd_err_real c.par.p x
  have htpe : (1 : ℝ) / 2 ^ (c.par.p + 1) = (rW d c.n δ).tp / 2 := H.tp_halfH
  rw [htpe] at hrnd
  have hxc : ((x : ℚ) : ℝ) = (c.par.eta : ℝ) * (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) *
      (c.par.nu : ℝ) / (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) := by rw [hx]; push_cast; ring
  rw [hxc] at hrnd
  have hda : |(a' : ℝ) - a| ≤ (rW d c.n δ).Ds5 := by
    have := abs_sub_le (a' : ℝ) ((c.par.eta : ℝ) * (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) *
      (c.par.nu : ℝ) / (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ)) a
    unfold RegW.Ds5; linarith
  have hA1 := s5_abs (rW d c.n δ).eta ((ctxOW K c δ ap).Y (pwOW K c δ ap π) s) (rW d c.n δ).y0
    (rW d c.n δ).lam ((ctxOW K c δ ap).qq (pwOW K c δ ap π) s) a (a' : ℝ) (rW d c.n δ).Ds5 (rW d c.n δ).tp
    (rW d c.n δ).eYw (rW d c.n δ).Dq hη.le S.Y_le hl0 hl1 hq rfl hda rfl htp0 H.tp_eta H.eY_small hDq htp
  have hw : oNorm ((ctxOW K c δ ap).w (pwOW K c δ ap π) s) ≤ Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw := by
    refine (oNorm_mulVec_le _ _).trans ?_
    exact mul_le_mul S.opN_A0 (H.wr hwt).1 (oNorm_nonneg _) (Real.sqrt_nonneg _)
  have h := dw_err ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).mu ((ctxOW K c δ ap).w (pwOW K c δ ap π) s)
    (cV (st.A *ᵥ ξ')) a (a' : ℝ) (rW d c.n δ).Ds5 (rW d c.n δ).Duw
    (Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw) (103 / 100 * (rW d c.n δ).eta * (rW d c.n δ).y0)
    hda hA1 hw (O.ew hwt)
  have e1 : cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) =
      ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).mu - (a' : ℝ) • cV (st.A *ᵥ ξ') := by
    unfold wmuO; rw [cV_sub, cV_smul, H.track.mu]
  have e2 : (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s =
      ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).mu - a • (ctxOW K c δ ap).w (pwOW K c δ ap π) s := rfl
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  unfold RegW.Dw; ring

/-- E16w: `|w'_μ - w°_μ| ≤ Δ_w`; on an unweighted round both Newton points are the centre. -/
theorem wmu_err (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    oNorm (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) -
      (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Dw := by
  by_cases hwt : H.Wt
  · exact H.wmu_err_w O hwt
  · have hw := hwt
    unfold Wt at hw
    rw [not_or, not_not, not_not] at hw
    have hY : (rvHW orc c δ st ξ' ζ' ε f).Y = 0 := by exact_mod_cast hw.1
    have e1 : wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f) = st.mu := by
      unfold wmuO; rw [hY, mul_zero, zero_mul, zero_div, rnd_zero, zero_smul, sub_zero]
    have e2 : (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s = ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).mu := by
      unfold Df2Ctx.wmu; rw [hw.2, mul_zero, zero_div, zero_smul, sub_zero]
    rw [e1, e2, H.track.mu, sub_self]
    have h0 : oNorm (0 : Fin d → ℝ) = 0 := by
      show Real.sqrt _ = 0; simp only [dotProduct_zero, Real.sqrt_zero]
    rw [h0]
    exact (H.R.Dw_le).2.1

/-- E18w, BL-OW's guard of line μ does not act: `|w'_μ| ≤ W° + Δ_w ≤ 2 W'`. -/
theorem guardW (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    ¬ (2 * c.par.W) ^ 2 < wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f) ⬝ᵥ
      wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f) := by
  rw [not_lt]
  have h1 := H.wmu_err O
  have h2 := H.wmu0_le
  have h3 := H.R.guard.2.1
  have h4 : (rW d c.n δ).W0 ≤ ((c.par.W : ℚ) : ℝ) := by rw [H.par]; exact H.enc.W_le
  have h5 : oNorm (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f))) ≤ 2 * (c.par.W : ℝ) := by
    have := oNorm_add_le (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) -
      (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s)
    rw [sub_add_cancel] at this
    linarith
  have h6 : cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) ⬝ᵥ
      cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)) ≤ (2 * (c.par.W : ℝ)) ^ 2 := by
    rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h5 2
  rw [← cV_dot] at h6
  exact_mod_cast h6

/-- E16w, Lemma VAL at the level, and P°'s line μ under the advice: it returns BL-OW's point `μ'`. -/
theorem mcall_eq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    (hap : ap s = apAdv (advCW K orc c δ ap π s st ξ' ζ' Z ε f))
    {mu' : Fin d → ℚ}
    (hmreg : cV mu' ∈ regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)))
    (hmmin : ∀ x ∈ regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)),
        (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).obj (cV mu') ≤
          (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).obj x +
            ((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ))
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s)
    (hXi : ¬ (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s pt ≤ -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho))
    (hmuOf : muOf (stepOW (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε)) = mu') :
    (ctxOW K c δ ap).mcall (pwOW K c δ ap π) s ((1 - (ctxOW K c δ ap).p.sb) • pt)
      ((ctxOW K c δ ap).p.sb * (1 - (ctxOW K c δ ap).p.eps)) = some (cV mu') := by
  have S := H.sett
  have hs := S.hs'
  obtain ⟨hgA, -, hgC⟩ := H.gapM O hpt hXi
  have hRpR : ∀ y ∈ (ctxOW K c δ ap).Rp (pwOW K c δ ap π) s, oNorm y ≤ (ctxOW K c δ ap).p.R := fun y hy => by
    have h := (H.det.Rp_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctxOW K c δ ap).p.R := h
    rwa [sub_zero] at h'
  have hmRp := hgC hmreg
  have hmR := hRpR _ hmRp
  have hR1 : 1 ≤ (rW d c.n δ).R := H.R_ge
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ c.n := by exact_mod_cast H.hn
  have hdeL := H.deL_pos
  have hdeL1 := H.deL_le_one
  have hLam := H.opN_Pn
  have hw0 := H.wmu0_le
  have hDw : oNorm ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s -
      cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f))) ≤ (rW d c.n δ).Dw := by
    rw [oNorm_sub_comm]; exact H.wmu_err O
  have hPp := (H.Pp_err O).1
  -- the accuracy: `e_BL + 2 Δ_F + L_F h ≤ e_M`, at the level `δ_e = 1/N_e`
  have hacc : (((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e : ℚ) : ℝ) +
      (rW d c.n δ).val ≤ (ctxOW K c δ ap).eM (pwOW K c δ ap π) s := by
    have h1 := H.R.val_le
    have hNe : ((c.par.Ne : ℕ) : ℝ) = 1 / (rW d c.n δ).de := by
      rw [show ((c.par.Ne : ℕ) : ℝ) = (rW d c.n δ).Ne by rw [H.par]; exact H.enc.Ne_eq]
      rw [H.R.hde, one_div_one_div]
    have hR' : (rW d c.n δ).R ≤ (c.par.R : ℝ) := by rw [H.par]; exact H.enc.R_le
    have h2 : (((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e : ℚ) : ℝ) ≤ (rW d c.n δ).valR := by
      have e : (((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e : ℚ) : ℝ) =
          1 / (((c.par.Ne : ℕ) : ℝ) * (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d)) := by
        show ((eBL c.par d c.n : ℚ) : ℝ) = _
        unfold eBL; push_cast; ring
      rw [e, hNe]
      unfold RegW.valR
      change _ ≤ (rW d c.n δ).de / (128 * (c.n : ℝ) ^ 2 * (rW d c.n δ).R ^ 2 * d)
      have hRR : (rW d c.n δ).R ^ 2 ≤ (c.par.R : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hR' 2
      have hX : 0 < 128 * (c.n : ℝ) ^ 2 * (rW d c.n δ).R ^ 2 * d := by positivity
      have e2 : 1 / (1 / (rW d c.n δ).de * (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d)) =
          (rW d c.n δ).de / (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d) := by
        have : 0 < (c.par.R : ℝ) := by linarith
        field_simp
      rw [e2]
      apply div_le_div_of_nonneg_left hdeL.le hX
      have : 0 ≤ (c.n : ℝ) ^ 2 * d := by positivity
      nlinarith
    have hdL : (d : ℝ) / (rW d c.n δ).de = (rW d c.n δ).Lam := by
      rw [H.R.hde, div_div_eq_mul_div, div_one]; rfl
    have h3 := eM_ge c.n (rW d c.n δ).R ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s).trace d (rW d c.n δ).de hn1 hR1
      hd1 hdeL hdeL1 ((H.det.r1_le_tau hs).1.posSemidef.trace_nonneg) (by rw [hdL]; exact S.trn.1)
    have e : (ctxOW K c δ ap).eM (pwOW K c δ ap π) s = 1 / (16 * (c.n : ℝ) ^ 2 *
        max 1 (4 * (rW d c.n δ).R ^ 2 * ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s).trace)) := rfl
    rw [e]
    have e2 : (rW d c.n δ).de / (64 * (c.n : ℝ) ^ 2 * (rW d c.n δ).R ^ 2 * d) = 2 * (rW d c.n δ).valR := by
      unfold RegW.valR; change _ = 2 * ((rW d c.n δ).de / (128 * (c.n : ℝ) ^ 2 * (rW d c.n δ).R ^ 2 * d))
      have : 0 < (c.n : ℝ) ^ 2 * (rW d c.n δ).R ^ 2 * d := by positivity
      field_simp; ring
    linarith
  have hval : advOK ((ctxOW K c δ ap).Rp (pwOW K c δ ap π) s) (ctxOW K c δ ap).p.R
      ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s)
      ((ctxOW K c δ ap).eM (pwOW K c δ ap π) s) (cV mu') := by
    refine ⟨hmRp, hmR, fun q0 hq => ?_⟩
    set q : Fin d → ℝ := fun i => (q0 i : ℝ) with hqdef
    obtain ⟨y', hy'Q, hqy'⟩ := hgA _ hq
    have hy'R := hRpR _ (hgC hy'Q)
    have hm := hmmin y' hy'Q
    rw [obj_M, obj_M] at hm
    have E1 := abs_le.1 (ellF_err ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s)
      (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ)
      ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)))
      (cV mu') (rW d c.n δ).DP (rW d c.n δ).Dw (rW d c.n δ).Lam (rW d c.n δ).R (rW d c.n δ).W0 hPp hDw hLam hmR hw0)
    have E2 := abs_le.1 (ellF_err ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s)
      (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ)
      ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) (cV (wmuO c st ξ' (rvHW orc c δ st ξ' ζ' ε f)))
      y' (rW d c.n δ).DP (rW d c.n δ).Dw (rW d c.n δ).Lam (rW d c.n δ).R (rW d c.n δ).W0 hPp hDw hLam hy'R hw0)
    have E3 := ellF_lip ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) (Pn_symmW H.det hs) (Pn_psdW H.det hs)
      ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) q y'
    have hL : oNorm ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s *ᵥ (y' - (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s)) ≤
        (rW d c.n δ).LF := by
      refine (oNorm_mulVec_le _ _).trans ?_
      have := oNorm_sub_le y' ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s)
      have hy'R' : oNorm y' ≤ (rW d c.n δ).R := hy'R
      unfold RegW.LF
      exact mul_le_mul hLam (by linarith) (oNorm_nonneg _) (by have := S.Lam_pos; linarith)
    have hh : oNorm (y' - q) ≤ (rW d c.n δ).h := by rw [oNorm_sub_comm]; exact hqy'
    have hLF0 : 0 ≤ (rW d c.n δ).LF := (oNorm_nonneg _).trans hL
    have E4 : oNorm ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s *ᵥ (y' - (ctxOW K c δ ap).wmu (pwOW K c δ ap π) s)) *
        oNorm (y' - q) ≤ (rW d c.n δ).LF * (rW d c.n δ).h := mul_le_mul hL hh (oNorm_nonneg _) hLF0
    have e5 : (rW d c.n δ).val = 2 * (rW d c.n δ).DF + (rW d c.n δ).LF * (rW d c.n δ).h := rfl
    unfold RegW.DF at e5
    obtain ⟨E1a, E1b⟩ := E1
    obtain ⟨E2a, E2b⟩ := E2
    linarith
  have heM : (ctxOW K c δ ap).eM (pwOW K c δ ap π) s < 1 / 2 := by
    have := H.det.eM_pos s
    have e : (ctxOW K c δ ap).eM (pwOW K c δ ap π) s = 1 / (16 * (c.n : ℝ) ^ 2 *
        max 1 (4 * (rW d c.n δ).R ^ 2 * ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s).trace)) := rfl
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ max 1 (4 * (rW d c.n δ).R ^ 2 * ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s).trace) :=
      le_max_left _ _
    nlinarith
  have hpick : advPick (advCW K orc c δ ap π s st ξ' ζ' Z ε f) ((ctxOW K c δ ap).eM (pwOW K c δ ap π) s) =
      cV mu' := by
    unfold advPick
    rw [ite_eq_right (by linarith)]
    show cV (muOf (stepOW (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε))) = _
    rw [hmuOf]
  unfold Df2Ctx.mcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick]
  exact ite_eq_left hval

end AdversarialBco.UW.Eng.RCHypOW

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (obsO)
open AdversarialBco.Unified.EngC (fireO)
open AdversarialBco.UW AdversarialBco.UW.BLOW AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (St cV)
open RCHypOW

/-- **C2 for BL-OW**: one round of BL-OW against P°'s round `s` on the weighted path, from C1's conclusions. -/
theorem c2OW : C2OW := by
  intro d K orc c δ ap π s st ξ' ζ' Z ε f H hap O
  have hs := H.sett.hs'
  have hm := H.det.mode_run hs
  obtain ⟨p', hp', htc, hv1Q, hiff, heq⟩ := H.tcall_eq O hap
  have hA := H.det.not_gdA hs
  have hT := H.det.not_gdT hs
  have hZ := H.det.not_gdZ hs
  by_cases hf : fireO c (rvHW orc c δ st ξ' ζ' ε f) p'
  · left
    exact ⟨stepOW_fire (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt hp' hf,
      ((ctxOW K c δ ap).fire_iff (pwOW K c δ ap π) s hm).2 ⟨hA, hT, hZ, _, htc, hiff.2 hf⟩⟩
  · right
    have hv1 := heq hf
    rw [hv1] at htc hv1Q hiff
    have hXi : ¬ (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s (cV p') ≤
        -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho) := fun h => hf (hiff.1 h)
    obtain ⟨mu', hmu', hmreg, hmmin⟩ := H.muCall O hv1Q hXi
    have hstep := stepOW_cont (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt
      hp' hf (H.guardW O) hmu'
    have hmc := H.mcall_eq O hap hmreg hmmin hv1Q hXi (by rw [hstep]; rfl)
    have hcont := (ctxOW K c δ ap).cont_of (pwOW K c δ ap π) s hm hA hT hZ htc hXi (H.det.not_gdW hs) hmc
    refine ⟨_, hstep, hcont, ?_⟩
    obtain ⟨pt, mu'', htc'', -, hmc'', -, hst⟩ := (ctxOW K c δ ap).st_succ_of_cont (pwOW K c δ ap π) s hm hcont
    rw [htc] at htc''
    have e1 : cV p' = pt := Option.some.inj htc''
    rw [← e1, hmc] at hmc''
    have e2 : cV mu' = mu'' := Option.some.inj hmc''
    rw [hst, ← e1, ← e2]
    have hr1 := H.det.r1_le_tau hs
    refine ⟨rfl, rfl, hr1.2.2.1.symm, mul_eq_one_comm.1 hr1.2.1, O.hA, O.hB, ?_, ?_, ?_, ?_⟩
    · have := O.errb; push_cast; exact this
    · have := O.errk; push_cast; exact this
    · have := O.errG; push_cast; exact this
    · have := O.errl; push_cast; exact this

end AdversarialBco.UW.Eng
