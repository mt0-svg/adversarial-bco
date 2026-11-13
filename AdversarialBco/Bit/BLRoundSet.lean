/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundCtx
public import AdversarialBco.Bit.BLRoundAlg

@[expose] public section

/-!
# Piece C: the setting of round `s` and P°'s bounds

`Sett` bundles what C1 reads of `RCHyp` (the regime, DET at `s + 1` with `τ(s + 1) = s`, `Track` at `s`, the draw
`ξ'`). From it, P°'s bounds at round `s`: `|A°|, |P° A°|, |A'|, |P' A'| ≤ Λ^{1/2}`,
`|P°| ≤ Λ`, `|ξ| ≤ Ξ`, `|ξ'| ≤ Ξ₁`, `|Y°| ≤ Ȳ`, `|c°| ≤ c̄`, the factor identities `A' = A° N°`,
`P' A' = (P° A°) N°⁻¹` and the inverses `A' (A'ᵀ P') = 1`, `(P' A') A'ᵀ = 1`; and the numerical facts on the constants
of `BudOK` that C1 uses.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open AdversarialBco.Poly.Layer2 (psd_trans)
open AdversarialBco.Bit.Asm (RunCase)
open Matrix

variable {d : ℕ}

/-! ## Numerical facts on the constants -/

namespace Bud

open AdversarialBco.Bit.BLP.Bud

theorem tp_small (d n : ℕ) : tp d n ≤ 1 / 1000 := by
  unfold tp
  have hp : 160 ≤ (par d n).p := by unfold par; simp only; omega
  have h1 : (2 : ℝ) ^ 160 ≤ 2 ^ (par d n).p := pow_le_pow_right₀ (by norm_num) hp
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (1000 : ℝ) ≤ 2 ^ 160 := by norm_num
  linarith

theorem Le_pos {d n : ℕ} (h : BudOK d n) : 0 < Le d n := by linarith [h.Le_ge]

theorem sqrtLe_ge {d n : ℕ} (h : BudOK d n) : 1 ≤ Real.sqrt (Le d n) := by
  rw [Real.le_sqrt (by norm_num) (Le_pos h).le]; linarith [h.Le_ge]

theorem Lgb_ge (d n : ℕ) (h : BudOK d n) : 1 / 4 ≤ Lgb d n := by
  unfold Lgb
  have h14 : (1 : ℝ) ≤ Real.log 14 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have := Le_pos h
  nlinarith

theorem Yb_ge {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) :
    16 * Real.sqrt (Le d n) ≤ Yb d n := by
  unfold Yb
  have hs := sqrtLe_ge h
  have hx := Real.sqrt_nonneg (Lgb d n)
  have h4 : 16 * Real.sqrt (Le d n) ≤ 4 * Real.sqrt (Le d n) / eps d n := by
    rw [le_div_iff₀ he0]; nlinarith
  nlinarith

theorem Yb_pos {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) : 0 < Yb d n := by
  linarith [Yb_ge h he0 he, sqrtLe_ge h]

theorem kc_pos {d n : ℕ} (hl : 0 < (po d n).lam) (hη : 0 < (po d n).eta)
    (hk : (po d n).kap = 1 / 4) (hk0 : 0 < (po d n).k0) : 0 < kc d n := by
  unfold kc; rw [hk]; positivity

theorem Dc_le_cb {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) (hkc : 0 ≤ kc d n) :
    Dc d n ≤ cb d n := by
  have hY := Yb_ge h he0 he
  have hY0 := Yb_pos h he0 he
  have hs := sqrtLe_ge h
  have htp := tp_small d n
  have htp0 := (tp_pos d n).le
  have hcb : 0 ≤ cb d n := by unfold cb; positivity
  have hq : (Pb d n + 1) / Yb d n ≤ 1 / 4 := by
    rw [div_le_iff₀ hY0]; unfold Pb; nlinarith
  have hf : 11 / 10 * (Pb d n + 1) / Yb d n + 1 / 16 ≤ 1 := by
    have : 11 / 10 * (Pb d n + 1) / Yb d n = 11 / 10 * ((Pb d n + 1) / Yb d n) := by ring
    rw [this]; linarith
  have hf0 : 0 ≤ 11 / 10 * (Pb d n + 1) / Yb d n + 1 / 16 := by
    have : 0 ≤ Pb d n + 1 := by unfold Pb; positivity
    positivity
  unfold Dc
  calc cb d n * tp d n * (11 / 10 * (Pb d n + 1) / Yb d n + 1 / 16) ≤ cb d n * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hcb) hf hf0 (by positivity)
    _ = cb d n := by ring

theorem Dc_small {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) (hkc : 0 ≤ kc d n) :
    Dc d n * (1 + Xi1 d n ^ 2) ≤ 1 / 10 ^ 30 :=
  (mul_le_mul_of_nonneg_right (Dc_le_cb h he0 he hkc) (by positivity)).trans h.cb_le

theorem Dc_nonneg {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) (hkc : 0 ≤ kc d n) :
    0 ≤ Dc d n := by
  have := Yb_pos h he0 he
  have : 0 ≤ Pb d n := by unfold Pb; positivity
  have := tp_pos d n
  unfold Dc cb; positivity

theorem cb_nonneg {d n : ℕ} (h : BudOK d n) (he0 : 0 < eps d n) (he : eps d n ≤ 1 / 4) (hkc : 0 ≤ kc d n) :
    0 ≤ cb d n := by
  have := Yb_pos h he0 he; unfold cb; positivity

theorem Xi_nonneg (d n : ℕ) : 0 ≤ Xi d n := Real.sqrt_nonneg _

theorem Xi1_pos (d n : ℕ) : 0 < Xi1 d n := by unfold Xi1; linarith [Xi_nonneg d n]

theorem Lam_pos {d n : ℕ} (hd : 1 ≤ d) (h : BudOK d n) (hde : 0 < (po d n).δe) : 0 < Lam d n := by
  have e := h.enc.de_eq
  unfold de at e
  have hN : 0 < AdversarialBco.Bit.BLP.Bud.Ne d n := by
    rw [e] at hde; exact one_div_pos.1 hde
  unfold Lam; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

/-- `d/δe = Λ`. -/
theorem d_de {d n : ℕ} (h : BudOK d n) : (d : ℝ) / (po d n).δe = Lam d n := by
  have e := h.enc.de_eq
  unfold de at e
  rw [e]; unfold Lam; rw [div_div_eq_mul_div, div_one]

end Bud

/-! ## The setting -/

/-- What C1 reads of `RCHyp`, for a general context `c` with P°'s parameters. -/
structure Sett (d n : ℕ) (c : Df2Ctx d) (δ : ℝ) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hc : RunCase d n
  bud : Bud.BudOK d n
  hs : s < n
  det : DetHyp c δ π (s + 1)
  tau : c.tau π (s + 1) = s
  hp : c.p = po d n
  hcn : c.n = n
  track : Track d n st (c.st π s) s
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ eXi0 d n

namespace Sett

variable {n : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hs' (S : Sett d n c δ π s st ξ') : s ≤ c.tau π (s + 1) := tau_le S.tau

theorem inv (S : Sett d n c δ π s st ξ') : c.StInv π s := S.det.stInv_le_tau s S.hs'

theorem de_pos (S : Sett d n c δ π s st ξ') : 0 < (po d n).δe := by
  have := S.det.rows.pos_de; rwa [S.hp] at this

theorem eps_pos (S : Sett d n c δ π s st ξ') : 0 < Bud.eps d n := by
  have := S.det.rows.pos_eps; rw [S.hp] at this; exact this

theorem eps_le (S : Sett d n c δ π s st ξ') : Bud.eps d n ≤ 1 / 4 := S.hc

theorem lam_pos (S : Sett d n c δ π s st ξ') : 0 < (po d n).lam := by
  have := S.det.rows.pos_lam; rwa [S.hp] at this

theorem lam_small (S : Sett d n c δ π s st ξ') : (po d n).lam ≤ 1 / 1000 := by
  have h := S.det.rows.r11; rw [S.hp] at h
  have hL := S.bud.Le_ge
  unfold Bud.Le at hL
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast S.hd
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem kc_pos (S : Sett d n c δ π s st ξ') : 0 < Bud.kc d n := by
  have hk := S.det.kap; have hk0 := S.det.k0_pos; have hη := S.det.rows.pos_eta
  rw [S.hp] at hk hk0 hη
  have := S.lam_small
  exact Bud.kc_pos S.lam_pos hη hk hk0

theorem Lam_pos (S : Sett d n c δ π s st ξ') : 0 < Bud.Lam d n := Bud.Lam_pos S.hd S.bud S.de_pos

theorem de_c (S : Sett d n c δ π s st ξ') : (d : ℝ) / c.p.δe = Bud.Lam d n := by
  rw [S.hp]; exact Bud.d_de S.bud

/-! ### The draw -/

theorem xi_le (S : Sett d n c δ π s st ξ') : oNorm (π.xi s) ≤ Bud.Xi d n :=
  xi_norm S.det S.hs' S.hp S.hcn S.bud

theorem dxi_le (S : Sett d n c δ π s st ξ') : oNorm (cV ξ' - π.xi s) ≤ Bud.exi d n := dxi_norm ξ' (π.xi s) S.xi

theorem exi_le_one (S : Sett d n c δ π s st ξ') : Bud.exi d n ≤ 1 :=
  (Bud.exi_le S.hd S.hn S.bud).trans (Bud.tp_le_one d n)

theorem xi'_le (S : Sett d n c δ π s st ξ') : oNorm (cV ξ') ≤ Bud.Xi1 d n := by
  have := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
  rw [add_sub_cancel] at this
  unfold Bud.Xi1; linarith [S.xi_le, S.dxi_le, S.exi_le_one]

theorem xi_le1 (S : Sett d n c δ π s st ξ') : oNorm (π.xi s) ≤ Bud.Xi1 d n := by
  unfold Bud.Xi1; linarith [S.xi_le]

/-! ### P°'s matrices at round `s` -/

theorem P_sym (S : Sett d n c δ π s st ξ') : (c.st π s).Pᵀ = (c.st π s).P := by
  have := S.inv.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem PS (S : Sett d n c δ π s st ξ') : (c.st π s).P * (c.st π s).S = 1 := mul_eq_one_comm.1 S.inv.SP

/-- `Aᵀ (P A) = 1`. -/
theorem APA (S : Sett d n c δ π s st ξ') : (c.st π s).Aᵀ * ((c.st π s).P * (c.st π s).A) = 1 := by
  have h : ((c.st π s).P * (c.st π s).A) * (c.st π s).Aᵀ = 1 := by
    rw [Matrix.mul_assoc, S.inv.AA, S.PS]
  exact mul_eq_one_comm.1 h

/-- `(P A)(P A)ᵀ = P`. -/
theorem PA_sq (S : Sett d n c δ π s st ξ') :
    ((c.st π s).P * (c.st π s).A) * ((c.st π s).P * (c.st π s).A)ᵀ = (c.st π s).P := by
  rw [Matrix.transpose_mul, S.P_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st π s).A, S.inv.AA, ← Matrix.mul_assoc,
    S.PS, Matrix.one_mul]

theorem trP_le (S : Sett d n c δ π s st ξ') : (c.st π s).P.trace ≤ Bud.Lam d n := by
  have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le S.hs')
  rwa [inv_inv, S.de_c] at this

theorem opN_A0 (S : Sett d n c δ π s st ξ') : opN (c.st π s).A ≤ Real.sqrt (Bud.Lam d n) :=
  (opN_A_sq S.det S.hs').trans (Real.sqrt_le_sqrt (by rw [S.hp]; exact inv_de_le_Lam S.hd S.bud))

theorem opN_PA0 (S : Sett d n c δ π s st ξ') :
    opN ((c.st π s).P * (c.st π s).A) ≤ Real.sqrt (Bud.Lam d n) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PA_sq]; exact S.trP_le

theorem opN_P0 (S : Sett d n c δ π s st ξ') : opN (c.st π s).P ≤ Bud.Lam d n := by
  have h := opN_mul_le ((c.st π s).P * (c.st π s).A) ((c.st π s).P * (c.st π s).A)ᵀ
  rw [S.PA_sq, opN_transpose] at h
  have h2 := S.opN_PA0
  have h0 := opN_nonneg ((c.st π s).P * (c.st π s).A)
  have : Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n) = Bud.Lam d n := Real.mul_self_sqrt S.Lam_pos.le
  nlinarith

/-! ### P°'s update of round `s` -/

theorem R1 (S : Sett d n c δ π s st ξ') :
    (c.Pn π s).PosDef ∧ c.Sn π s * c.Pn π s = 1 ∧ c.An π s * (c.An π s)ᵀ = c.Sn π s ∧ (c.An π s).det ≠ 0 :=
  S.det.r1_le_tau S.hs'

theorem Pn_sym (S : Sett d n c δ π s st ξ') : (c.Pn π s)ᵀ = c.Pn π s := by
  have := S.R1.1.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem trn (S : Sett d n c δ π s st ξ') : (c.Pn π s).trace ≤ Bud.Lam d n ∧ (c.Sn π s).trace ≤ Bud.Lam d n := by
  have h := S.det.not_gdT S.hs'
  unfold Df2Ctx.GdT at h
  rw [not_or, not_lt, not_lt, S.de_c] at h
  exact h

/-- `A' (A'ᵀ P') = 1`. -/
theorem An_inv (S : Sett d n c δ π s st ξ') : c.An π s * ((c.An π s)ᵀ * c.Pn π s) = 1 := by
  rw [← Matrix.mul_assoc, S.R1.2.2.1, S.R1.2.1]

/-- `(P' A') A'ᵀ = 1`. -/
theorem PnAn_inv (S : Sett d n c δ π s st ξ') : (c.Pn π s * c.An π s) * (c.An π s)ᵀ = 1 := by
  rw [Matrix.mul_assoc, S.R1.2.2.1]; exact mul_eq_one_comm.1 S.R1.2.1

theorem opN_An (S : Sett d n c δ π s st ξ') : opN (c.An π s) ≤ Real.sqrt (Bud.Lam d n) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.R1.2.2.1]; exact S.trn.2

theorem PnAn_sq (S : Sett d n c δ π s st ξ') :
    (c.Pn π s * c.An π s) * (c.Pn π s * c.An π s)ᵀ = c.Pn π s := by
  rw [Matrix.transpose_mul, S.Pn_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.An π s), S.R1.2.2.1,
    ← Matrix.mul_assoc, mul_eq_one_comm.1 S.R1.2.1, Matrix.one_mul]

theorem opN_PnAn (S : Sett d n c δ π s st ξ') : opN (c.Pn π s * c.An π s) ≤ Real.sqrt (Bud.Lam d n) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PnAn_sq]; exact S.trn.1

theorem opN_AnPn (S : Sett d n c δ π s st ξ') : opN ((c.An π s)ᵀ * c.Pn π s) ≤ Real.sqrt (Bud.Lam d n) := by
  have : (c.An π s)ᵀ * c.Pn π s = (c.Pn π s * c.An π s)ᵀ := by rw [Matrix.transpose_mul, S.Pn_sym]
  rw [this, opN_transpose]; exact S.opN_PnAn

theorem aq (S : Sett d n c δ π s st ξ') : 1 / 2 ≤ c.aa π s ∧ 1 / 4 ≤ c.qq π s := S.det.aq S.hs'

/-- `A' = A° N°`, `N° = a^{-1/2} I - (a^{-1/2} c') ξ ξᵀ`. -/
theorem An_fac (S : Sett d n c δ π s st ξ') :
    c.An π s = (c.st π s).A * ((Real.sqrt (c.aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (-(c.cc π s / (Real.sqrt (c.aa π s) * Real.sqrt (c.qq π s) *
        (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))))) • vecMulVec (π.xi s) (π.xi s)) := by
  have ha : 0 < c.aa π s := by linarith [S.aq.1]
  have hq : 0 < c.qq π s := by linarith [S.aq.2]
  unfold Df2Ctx.An Df2Ctx.w
  rw [An_eq_mul, ← coef_eq _ _ _ ha hq]
  rfl

/-- `P' A' = (P° A°) N°⁻¹`, `N°⁻¹ = a^{1/2} I + (c/(a^{1/2} + q^{1/2})) ξ ξᵀ`. -/
theorem PnAn_fac (S : Sett d n c δ π s st ξ') :
    c.Pn π s * c.An π s = ((c.st π s).P * (c.st π s).A) * (Real.sqrt (c.aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (c.cc π s / (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))) • vecMulVec (π.xi s) (π.xi s)) := by
  have ha : 0 < c.aa π s := by linarith [S.aq.1]
  have hq : 0 < c.qq π s := by linarith [S.aq.2]
  exact PnAn_eq (c.st π s).P (c.st π s).A (π.xi s) (c.cc π s) (c.aa π s) (c.qq π s) ha hq rfl S.APA S.P_sym

/-! ### `|Y°| ≤ Ȳ` and `|c°| ≤ c̄` -/

theorem Y_le (S : Sett d n c δ π s st ξ') : |c.Y π s| ≤ Bud.Yb d n := by
  obtain ⟨he, hg, -⟩ := S.det.evG s S.hs'
  have hgv := (S.det.adm s (S.det.le_tau_lt S.hs')).2 _ (S.det.play_keps s).2
  have hLg := S.bud.Lg_le
  have hLgb := Bud.Lgb_ge d n S.bud
  have h := ybar_real (c.pip π s) (gauge c.Kt (WithLp.toLp 2 (c.X π s))) (π.g s (WithLp.toLp 2 (c.play π s)))
    (π.e s) c.p.Le (Bud.Lgb d n) c.p.eps S.det.rows.pos_eps (by rw [S.hp]; exact S.eps_le) rfl (gauge_nonneg _) hg
    hgv.1 hgv.2 (he.trans (Real.sqrt_le_sqrt (by rw [S.hp, S.hcn]; exact hLg))) hLgb S.det.one_le_Le
  unfold Df2Ctx.Y
  rw [S.hp] at h ⊢
  unfold Bud.Yb Bud.Le Bud.eps
  exact h

theorem cc_eq (S : Sett d n c δ π s st ξ') : c.cc π s = Bud.kc d n * c.Y π s := by
  unfold Df2Ctx.cc Bud.kc; rw [S.hp]

theorem cc_le (S : Sett d n c δ π s st ξ') : |c.cc π s| ≤ Bud.cb d n := by
  rw [S.cc_eq, abs_mul, abs_of_pos S.kc_pos]
  unfold Bud.cb
  exact mul_le_mul_of_nonneg_left S.Y_le S.kc_pos.le

end Sett

end AdversarialBco.Bit.BLP.RC
