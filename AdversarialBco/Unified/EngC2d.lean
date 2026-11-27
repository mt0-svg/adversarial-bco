/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngC2c

@[expose] public section

/-!
# Piece C for BL-O, part C2 (d): line μ, `C2O` and the round

Bit/BLRoundC2.lean (E16, E18, Lemma VAL, C2) for BL-O at `k`: BL-O's Newton point of line μ against P°'s, BL-O's guard
`W` does not act, P°'s line μ under the advice returns BL-O's point `μ'` (its call through `apSpecO` on `regO`), and
`c2O : C2O`, `roundCO : RoundCO`.
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.Asm
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

/-- The objective of BL's line μ, `ellF(P'_+, w'_μ, ·)` up to a constant. -/
theorem obj_M (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (r : RV d) (y : Fin d → ℝ) :
    (callMO c n st ξ r).obj y = ellF (cM r.B * (cM r.B)ᵀ) (cV (wmuO c st ξ r)) y -
      cV (wmuO c st ξ r) ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ cV (wmuO c st ξ r)) / 2 := by
  have hs : (cM r.B * (cM r.B)ᵀ)ᵀ = cM r.B * (cM r.B)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← obj_ellF _ hs]
  unfold CallQ.obj
  change y ⬝ᵥ (cM (r.B * r.Bᵀ) *ᵥ y) / 2 - cV ((r.B * r.Bᵀ) *ᵥ wmuO c st ξ r) ⬝ᵥ y = _
  rw [cM_mulVec, cM_mul, cM_transpose]


end AdversarialBco.Unified.EngC

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.Bit.BLP (refTest selT muOf)
open AdversarialBco.Bit.Cpl (apAdv advOK advPick)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-! ### E16: the Newton point of line μ -/

theorem nu_relH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |((c.par.nu : ℚ) : ℝ) * (1 - BudK.lam d c.n k) - 1| ≤ BudK.tp d c.n k / 16 := by
  rw [H.par]; exact H.bud.enc.nu_rel

theorem qq_ge (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 999 / 1000 ≤ (ctxO K c k ap).qq π s := by
  have S := H.sett
  rw [H.qq_eq]
  have h1 := S.cc_le
  have h2 := S.xi_le1
  have hx : π.xi s ⬝ᵥ π.xi s ≤ BudK.Xi1 d c.n k ^ 2 := by
    rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h2 2
  have hx0 : 0 ≤ π.xi s ⬝ᵥ π.xi s := by rw [← oNorm_sq]; positivity
  have h3 := H.bud.cb_le
  have hcb := H.cb0
  have h4 : |(ctxO K c k ap).cc π s * (π.xi s ⬝ᵥ π.xi s - 1)| ≤ BudK.cb d c.n k * (1 + BudK.Xi1 d c.n k ^ 2) := by
    rw [abs_mul]
    apply mul_le_mul h1 _ (abs_nonneg _) hcb
    rw [abs_le]; constructor <;> nlinarith
  have := (abs_le.1 h4).1
  nlinarith

theorem Dq_small (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : BudK.Dq d c.n k ≤ 1 / 1000 := by
  have S := H.sett
  have h1 := NK.Dc_small H.bud S.eps_pos S.eps_le H.kc_pos.le
  have h2 := H.bud.cb_le
  have hcb := H.cb0
  have hX := NK.Xi1_pos d c.n k
  have hexi := S.exi_le_one
  have hexi0 : 0 ≤ BudK.exi d c.n k := by unfold BudK.exi; positivity
  have h3 : BudK.cb d c.n k * BudK.Xi1 d c.n k ≤ BudK.cb d c.n k * (1 + BudK.Xi1 d c.n k ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hcb
  have h4 : BudK.cb d c.n k * BudK.Xi1 d c.n k * BudK.exi d c.n k ≤ BudK.cb d c.n k * BudK.Xi1 d c.n k :=
    by have : 0 ≤ BudK.cb d c.n k * BudK.Xi1 d c.n k := by positivity
       nlinarith
  unfold BudK.Dq
  nlinarith

theorem eY_small (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : BudK.eY d c.n k ≤ BudK.Yb d c.n k / 1000 := by
  have S := H.sett
  have h1 := NK.ezt_le H.hd H.hn H.bud
  have h2 := NK.Yb_ge H.bud S.eps_pos S.eps_le
  have h3 := NK.sqrtLe_ge H.bud
  have h4 := NK.tp_small d c.n k
  have h5 := (NK.tp_pos d c.n k).le
  have h6 : 0 ≤ BudK.ezt d c.n k := by unfold BudK.ezt; positivity
  unfold BudK.eY BudK.Pb
  nlinarith

theorem tp_eta (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.tp d c.n k ≤ 1 / 100 * BudK.eta d c.n k * BudK.Yb d c.n k := by
  have S := H.sett
  have hNe : 0 < BudK.Ne d c.n k := by
    have h := H.bud.enc.de_eq
    have hde : 0 < BudK.de d c.n k := S.de_pos
    rw [h] at hde; exact one_div_pos.1 hde
  have hLe := H.bud.Le_ge
  have hLeNe := Le_le_Ne (BudK.Ne d c.n k) (BudK.Le d c.n k) hNe H.bud.enc.Le_eq hLe
  have htp0 := (NK.tp_pos d c.n k).le
  have hx := H.bud.x_le
  have heN : BudK.tp d c.n k ≤ BudK.eN d c.n k := by
    have hDc := NK.Dc_nonneg H.bud S.eps_pos S.eps_le H.kc_pos.le
    have hcb := H.cb0
    have hexi0 : 0 ≤ BudK.exi d c.n k := by unfold BudK.exi; positivity
    have hX := NK.Xi1_pos d c.n k
    unfold BudK.eN
    have : 0 ≤ 143 / 100 * (1 + BudK.Xi1 d c.n k ^ 2) * BudK.Dc d c.n k := by positivity
    have : 0 ≤ 285 / 100 * BudK.cb d c.n k * BudK.Xi1 d c.n k * BudK.exi d c.n k := by positivity
    have : BudK.tp d c.n k ≤ BudK.tp d c.n k * (1001 / 1000 + 51 / 100 * BudK.Xi1 d c.n k ^ 2) := by nlinarith
    linarith
  have hn : (1 : ℝ) ≤ c.n := by exact_mod_cast H.hn
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have htp : (c.n : ℝ) * (d * BudK.Ne d c.n k) * BudK.tp d c.n k ≤ 1 := by
    unfold BudK.x BudK.Lam at hx
    have : (c.n : ℝ) * (d * BudK.Ne d c.n k) * BudK.tp d c.n k ≤ c.n * (d * BudK.Ne d c.n k) * BudK.eN d c.n k :=
      mul_le_mul_of_nonneg_left heN (by positivity)
    linarith
  exact tp_small_gen (BudK.tp d c.n k) c.n d (BudK.Ne d c.n k) (BudK.Le d c.n k) (BudK.eta d c.n k) (BudK.Yb d c.n k) hn hd hNe (by linarith)
    hLeNe htp htp0 rfl (NK.Yb_ge H.bud S.eps_pos S.eps_le)

/-- E16: `|w'_μ - w°_μ| ≤ Δ_w`. -/
theorem wmu_err (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s) :
    oNorm (cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)) -
      (ctxO K c k ap).wmu π s) ≤ BudK.Dw d c.n k := by
  have S := H.sett
  have hη : 0 < BudK.eta d c.n k := H.det.rows.pos_eta
  have htp := NK.tp_small d c.n k
  have htp0 := (NK.tp_pos d c.n k).le
  have hq0 := H.qq_ge
  have hq : 99 / 100 ≤ (ctxO K c k ap).qq π s := by linarith
  have hDq := H.Dq_small
  have hq' : 99 / 100 ≤ (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) := by
    have := (abs_le.1 O.eq).1; linarith
  set x : ℚ := c.par.eta * (rvH orc c st ξ' ζ' ε f).Y * c.par.nu / (rvH orc c st ξ' ζ' ε f).q
    with hx
  set a' : ℚ := rnd c.par.p x with ha'
  set a : ℝ := BudK.eta d c.n k * (ctxO K c k ap).Y π s / ((1 - BudK.lam d c.n k) * (ctxO K c k ap).qq π s)
    with ha
  have hs5 := s5_err (BudK.eta d c.n k) (c.par.eta : ℝ) ((ctxO K c k ap).Y π s)
    (((rvH orc c st ξ' ζ' ε f).Y : ℚ) : ℝ) (c.par.nu : ℝ) (BudK.lam d c.n k) ((ctxO K c k ap).qq π s)
    (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) (BudK.tp d c.n k) (BudK.eY d c.n k) (BudK.Yb d c.n k) (BudK.Dq d c.n k) hη.le H.eta_err
    H.nu_relH S.lam_pos.le S.lam_small htp0 htp S.Y_le O.eY hq hq' O.eq
  have hrnd := rnd_err_real c.par.p x
  have htpe : (1 : ℝ) / 2 ^ (c.par.p + 1) = BudK.tp d c.n k / 2 := H.tp_halfH
  rw [htpe] at hrnd
  have hxc : ((x : ℚ) : ℝ) = (c.par.eta : ℝ) * (((rvH orc c st ξ' ζ' ε f).Y : ℚ) : ℝ) *
      (c.par.nu : ℝ) / (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) := by rw [hx]; push_cast; ring
  rw [hxc] at hrnd
  have hda : |(a' : ℝ) - a| ≤ BudK.Ds5 d c.n k := by
    have := abs_sub_le (a' : ℝ) ((c.par.eta : ℝ) * (((rvH orc c st ξ' ζ' ε f).Y : ℚ) : ℝ) *
      (c.par.nu : ℝ) / (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ)) a
    unfold BudK.Ds5; linarith
  have hA1 := s5_abs (BudK.eta d c.n k) ((ctxO K c k ap).Y π s) (BudK.Yb d c.n k) (BudK.lam d c.n k)
    ((ctxO K c k ap).qq π s) a (a' : ℝ) (BudK.Ds5 d c.n k) (BudK.tp d c.n k) (BudK.eY d c.n k) (BudK.Dq d c.n k) hη.le S.Y_le
    S.lam_pos.le S.lam_small hq rfl hda rfl htp0 H.tp_eta H.eY_small hDq htp
  have hw : oNorm ((ctxO K c k ap).w π s) ≤ Real.sqrt (BudK.Lam d c.n k) * BudK.Xi d c.n k := by
    refine (oNorm_mulVec_le _ _).trans ?_
    exact mul_le_mul S.opN_A0 S.xi_le (oNorm_nonneg _) (Real.sqrt_nonneg _)
  have h := dw_err ((ctxO K c k ap).st π s).mu ((ctxO K c k ap).w π s) (cV (st.A *ᵥ ξ')) a (a' : ℝ)
    (BudK.Ds5 d c.n k) (BudK.Du d c.n k) (Real.sqrt (BudK.Lam d c.n k) * BudK.Xi d c.n k) (103 / 100 * BudK.eta d c.n k * BudK.Yb d c.n k)
    hda hA1 hw O.ew
  have e1 : cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)) =
      ((ctxO K c k ap).st π s).mu - (a' : ℝ) • cV (st.A *ᵥ ξ') := by
    unfold wmuO; rw [cV_sub, cV_smul, H.track.mu]
  have e2 : (ctxO K c k ap).wmu π s = ((ctxO K c k ap).st π s).mu - a • (ctxO K c k ap).w π s := rfl
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  unfold BudK.Dw; ring


theorem opN_Pn (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    opN ((ctxO K c k ap).Pn π s) ≤ BudK.Lam d c.n k := by
  have S := H.sett
  have h := opN_mul_le ((ctxO K c k ap).Pn π s * (ctxO K c k ap).An π s)
    ((ctxO K c k ap).Pn π s * (ctxO K c k ap).An π s)ᵀ
  rw [S.PnAn_sq, opN_transpose] at h
  have h2 := S.opN_PnAn
  have h0 := opN_nonneg ((ctxO K c k ap).Pn π s * (ctxO K c k ap).An π s)
  have : Real.sqrt (BudK.Lam d c.n k) * Real.sqrt (BudK.Lam d c.n k) = BudK.Lam d c.n k := Real.mul_self_sqrt S.Lam_pos.le
  nlinarith

/-- `|w°_μ| ≤ W° = R + 4d (N_e/Le)^{1/2}` (the guard W of P° does not act, `not_gdW`). -/
theorem wmu0_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm ((ctxO K c k ap).wmu π s) ≤ BudK.W0 d c.n k := by
  have S := H.sett
  have h := H.det.not_gdW S.hs'
  unfold Df2Ctx.GdW at h
  rw [not_lt] at h
  have hNe : 0 < BudK.Ne d c.n k := by
    have h := H.bud.enc.de_eq
    have hde : 0 < BudK.de d c.n k := S.de_pos
    rw [h] at hde; exact one_div_pos.1 hde
  have hLe : 0 < BudK.Le d c.n k := by have := H.bud.Le_ge; linarith
  have e := w0_eq (BudK.eta d c.n k) d c.n (BudK.Le d c.n k) (BudK.de d c.n k) (BudK.Ne d c.n k) (by exact_mod_cast H.hd)
    (by exact_mod_cast H.hn) hLe hNe H.bud.enc.de_eq rfl
  change oNorm _ ≤ BudK.R d c.n k + BudK.eta d c.n k * Real.sqrt (16 * d * c.n * BudK.Le d c.n k / BudK.de d c.n k) at h
  rw [e] at h
  exact h

/-- E18, BL's guard of line μ does not act: `|w'_μ| ≤ W° + Δ_w ≤ 2 W'`. -/
theorem guardW (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s) :
    ¬ (2 * c.par.W) ^ 2 < wmuO c st ξ' (rvH orc c st ξ' ζ' ε f) ⬝ᵥ
      wmuO c st ξ' (rvH orc c st ξ' ζ' ε f) := by
  rw [not_lt]
  have h1 := H.wmu_err O
  have h2 := H.wmu0_le
  have h3 := H.bud.gW
  have h4 : BudK.W0 d c.n k ≤ ((c.par.W : ℚ) : ℝ) := by rw [H.par]; exact H.bud.enc.W_le
  have h5 : oNorm (cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f))) ≤
      2 * (c.par.W : ℝ) := by
    have := oNorm_add_le (cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)) -
      (ctxO K c k ap).wmu π s) ((ctxO K c k ap).wmu π s)
    rw [sub_add_cancel] at this
    linarith
  have h6 : cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)) ⬝ᵥ
      cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)) ≤ (2 * (c.par.W : ℝ)) ^ 2 := by
    rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h5 2
  rw [← cV_dot] at h6
  exact_mod_cast h6
/-- E16, Lemma VAL, and P°'s line μ under the advice: it returns BL's point `μ'`. -/
theorem mcall_eq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    (hap : ap s = apAdv (advC K orc c k ap π s st ξ' ζ' ε f))
    {mu' : Fin d → ℚ}
    (hmreg : cV mu' ∈ (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f))))
    (hmmin : ∀ x ∈ (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f))),
        (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).obj (cV mu') ≤
          (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).obj x +
            ((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e : ℝ))
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxO K c k ap).Rm π s)
    (hXi : ¬ (ctxO K c k ap).Xi π s pt ≤ -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho))
    (hmuOf : muOf (stepO orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε)) = mu') :
    (ctxO K c k ap).mcall π s ((1 - (ctxO K c k ap).p.sb) • pt)
      ((ctxO K c k ap).p.sb * (1 - (ctxO K c k ap).p.eps)) = some (cV mu') := by
  have S := H.sett
  have hs := S.hs'
  obtain ⟨hgA, -, hgC⟩ := H.gapM O hpt hXi
  have hRpR : ∀ y ∈ (ctxO K c k ap).Rp π s, oNorm y ≤ (ctxO K c k ap).p.R := fun y hy => by
    have h := (H.det.Rp_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctxO K c k ap).p.R := h
    rwa [sub_zero] at h'
  have hmRp := hgC hmreg
  have hmR := hRpR _ hmRp
  have hR1 := H.R_ge
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ c.n := by exact_mod_cast H.hn
  have hde := S.de_pos
  have hde1 : (poK d c.n k).δe < 1 := H.det.rows.de_lt
  have hLam := H.opN_Pn
  have hw0 := H.wmu0_le
  have hDw : oNorm ((ctxO K c k ap).wmu π s -
      cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f))) ≤ BudK.Dw d c.n k := by
    rw [oNorm_sub_comm]; exact H.wmu_err O
  have hPp := (H.Pp_err O).1
  have hW00 : 0 ≤ BudK.W0 d c.n k := (oNorm_nonneg _).trans hw0
  -- the accuracy: `e_BL + 2 Δ_F + L_F h ≤ e_M`
  have hacc : (((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e : ℚ) : ℝ) +
      BudK.val d c.n k ≤ (ctxO K c k ap).eM π s := by
    have h1 := H.bud.val_le
    have hNe : ((c.par.Ne : ℕ) : ℝ) = 1 / (poK d c.n k).δe := by
      rw [show ((c.par.Ne : ℕ) : ℝ) = BudK.Ne d c.n k by rw [H.par]; exact H.bud.enc.Ne_eq]
      have := H.bud.enc.de_eq
      change (poK d c.n k).δe = 1 / BudK.Ne d c.n k at this
      rw [this, one_div_one_div]
    have hR' : BudK.R d c.n k ≤ (c.par.R : ℝ) := by rw [H.par]; exact H.bud.enc.R_le
    have h2 : (((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e : ℚ) : ℝ) ≤ BudK.valR d c.n k := by
      have e : (((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e : ℚ) : ℝ) =
          1 / (((c.par.Ne : ℕ) : ℝ) * (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d)) := by
        show ((eBL c.par d c.n : ℚ) : ℝ) = _
        unfold eBL; push_cast; ring
      rw [e, hNe]
      unfold BudK.valR
      change _ ≤ (poK d c.n k).δe / (128 * (c.n : ℝ) ^ 2 * BudK.R d c.n k ^ 2 * d)
      have hRR : BudK.R d c.n k ^ 2 ≤ (c.par.R : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hR' 2
      have hX : 0 < 128 * (c.n : ℝ) ^ 2 * BudK.R d c.n k ^ 2 * d := by positivity
      have e2 : 1 / (1 / (poK d c.n k).δe * (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d)) =
          (poK d c.n k).δe / (128 * (c.n : ℝ) ^ 2 * (c.par.R : ℝ) ^ 2 * d) := by
        have : 0 < (c.par.R : ℝ) := by linarith
        field_simp
      rw [e2]
      apply div_le_div_of_nonneg_left hde.le hX
      have : 0 ≤ (c.n : ℝ) ^ 2 * d := by positivity
      nlinarith
    have h3 := eM_ge c.n (BudK.R d c.n k) ((ctxO K c k ap).Pn π s).trace d (poK d c.n k).δe hn1 hR1 hd1 hde hde1.le
      ((H.det.r1_le_tau hs).1.posSemidef.trace_nonneg) (by have hdc := S.de_c; change (d : ℝ) / (poK d c.n k).δe = _ at hdc; rw [hdc]; exact S.trn.1)
    have e : (ctxO K c k ap).eM π s =
        1 / (16 * (c.n : ℝ) ^ 2 * max 1 (4 * BudK.R d c.n k ^ 2 * ((ctxO K c k ap).Pn π s).trace)) := rfl
    rw [e]
    have e2 : (poK d c.n k).δe / (64 * (c.n : ℝ) ^ 2 * BudK.R d c.n k ^ 2 * d) = 2 * BudK.valR d c.n k := by
      unfold BudK.valR; change _ = 2 * ((poK d c.n k).δe / _); field_simp; ring
    linarith
  have hval : advOK ((ctxO K c k ap).Rp π s) (ctxO K c k ap).p.R ((ctxO K c k ap).Pn π s)
      ((ctxO K c k ap).wmu π s) ((ctxO K c k ap).eM π s) (cV mu') := by
    refine ⟨hmRp, hmR, fun q0 hq => ?_⟩
    set q : Fin d → ℝ := fun i => (q0 i : ℝ) with hqdef
    obtain ⟨y', hy'Q, hqy'⟩ := hgA _ hq
    have hy'R := hRpR _ (hgC hy'Q)
    have hm := hmmin y' hy'Q
    rw [obj_M, obj_M] at hm
    have E1 := abs_le.1 (ellF_err ((ctxO K c k ap).Pn π s)
      (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ)
      ((ctxO K c k ap).wmu π s) (cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)))
      (cV mu') (BudK.DP d c.n k) (BudK.Dw d c.n k) (BudK.Lam d c.n k) (BudK.R d c.n k) (BudK.W0 d c.n k) hPp hDw hLam hmR hw0)
    have E2 := abs_le.1 (ellF_err ((ctxO K c k ap).Pn π s)
      (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ)
      ((ctxO K c k ap).wmu π s) (cV (wmuO c st ξ' (rvH orc c st ξ' ζ' ε f)))
      y' (BudK.DP d c.n k) (BudK.Dw d c.n k) (BudK.Lam d c.n k) (BudK.R d c.n k) (BudK.W0 d c.n k) hPp hDw hLam hy'R hw0)
    have E3 := ellF_lip ((ctxO K c k ap).Pn π s) (Pn_symm H.det hs) (Pn_psd H.det hs)
      ((ctxO K c k ap).wmu π s) q y'
    have hL : oNorm ((ctxO K c k ap).Pn π s *ᵥ (y' - (ctxO K c k ap).wmu π s)) ≤ BudK.LF d c.n k := by
      refine (oNorm_mulVec_le _ _).trans ?_
      have := oNorm_sub_le y' ((ctxO K c k ap).wmu π s)
      have hy'R' : oNorm y' ≤ BudK.R d c.n k := hy'R
      unfold BudK.LF
      exact mul_le_mul hLam (by linarith) (oNorm_nonneg _) (by have := S.Lam_pos; linarith)
    have hh : oNorm (y' - q) ≤ BudK.h d c.n k := by rw [oNorm_sub_comm]; exact hqy'
    have hLF0 : 0 ≤ BudK.LF d c.n k := (oNorm_nonneg _).trans hL
    have E4 : oNorm ((ctxO K c k ap).Pn π s *ᵥ (y' - (ctxO K c k ap).wmu π s)) * oNorm (y' - q) ≤
        BudK.LF d c.n k * BudK.h d c.n k := mul_le_mul hL hh (oNorm_nonneg _) hLF0
    have e5 : BudK.val d c.n k = 2 * BudK.DF d c.n k + BudK.LF d c.n k * BudK.h d c.n k := rfl
    unfold BudK.DF at e5
    obtain ⟨E1a, E1b⟩ := E1
    obtain ⟨E2a, E2b⟩ := E2
    linarith
  have heM : (ctxO K c k ap).eM π s < 1 / 2 := by
    have := H.det.eM_pos s
    have e : (ctxO K c k ap).eM π s =
        1 / (16 * (c.n : ℝ) ^ 2 * max 1 (4 * BudK.R d c.n k ^ 2 * ((ctxO K c k ap).Pn π s).trace)) := rfl
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ max 1 (4 * BudK.R d c.n k ^ 2 * ((ctxO K c k ap).Pn π s).trace) := le_max_left _ _
    nlinarith
  have hpick : advPick (advQO orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε)
      (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s))
      ((ctxO K c k ap).eM π s) = cV mu' := by
    unfold advPick
    rw [ite_eq_right (by linarith)]
    show cV (muOf (stepO orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε))) = _
    rw [hmuOf]
  unfold Df2Ctx.mcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick]
  exact ite_eq_left hval


end AdversarialBco.Unified.Eng.RCHypO

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Unified.BLO AdversarialBco.Unified.EngC AdversarialBco.Unified.Asm
open AdversarialBco.Bit.BLP (St cV)
open RCHypO

/-- **C2 for BL-O**: one round of BL-O against P°'s round `s`, from C1's conclusions. -/
theorem c2O : C2O := by
  intro d K orc c k ap π s st ξ' ζ' Z ε f H hap O
  have hs := H.sett.hs'
  have hm := H.det.mode_run hs
  obtain ⟨p', hp', htc, hv1Q, hiff, heq⟩ := H.tcall_eq O hap
  have hA := H.det.not_gdA hs
  have hT := H.det.not_gdT hs
  have hZ := H.det.not_gdZ hs
  by_cases hf : fireO c (rvH orc c st ξ' ζ' ε f) p'
  · left
    exact ⟨stepO_fire orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt hp' hf,
      ((ctxO K c k ap).fire_iff π s hm).2 ⟨hA, hT, hZ, _, htc, hiff.2 hf⟩⟩
  · right
    have hv1 := heq hf
    rw [hv1] at htc hv1Q hiff
    have hXi : ¬ (ctxO K c k ap).Xi π s (cV p') ≤
        -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho) := fun h => hf (hiff.1 h)
    obtain ⟨mu', hmu', hmreg, hmmin⟩ := H.muCall O hv1Q hXi
    have hstep := stepO_cont orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt
      hp' hf (H.guardW O) hmu'
    have hmc := H.mcall_eq O hap hmreg hmmin hv1Q hXi (by rw [hstep]; rfl)
    have hcont := (ctxO K c k ap).cont_of π s hm hA hT hZ htc hXi (H.det.not_gdW hs) hmc
    refine ⟨_, hstep, hcont, ?_⟩
    obtain ⟨pt, mu'', htc'', -, hmc'', -, hst⟩ := (ctxO K c k ap).st_succ_of_cont π s hm hcont
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

/-- Piece C for BL-O, the round. -/
theorem roundCO : RoundCO := roundCO_of c1O c2O

end AdversarialBco.Unified.Eng
