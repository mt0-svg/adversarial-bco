/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngDefs
public import AdversarialBco.UW.DetGuard
public import AdversarialBco.Bit.BLRoundSet

@[expose] public section

/-!
# Piece C for BL-OW: the setting of round `s`

Unified/EngCSet.lean for BL-OW: `SettW` (`SettK` with the constants of Theorem BUD-W at `rW d n δ`, DET with sure
ranges `DetHypW` on the weighted path `πw` and event (a) at the level `EvGW`), and P°'s bounds at round `s`. Three
changes against Theorem U:

* the caps are read at the level: P°'s floor `δ_0 = 1/N_0` gives `d/δ_0 ≤ Λ = d N_e`
  (`de_c`, an inequality where Theorem U has an equality);
* `|Y°| ≤ y0` and `|c°| ≤ c̄_w = κ_c y0` hold surely (`Y_le`, `cc_le`, from the clip);
* Lemma WR (ii): on a weighted round of P° (`Y° ≠ 0`), `|ξ| ≤ (b0 + 1)^{1/2} ≤ Ξ_w` (`xi_w`).
-/

namespace AdversarialBco.UW.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (inv_norm_le psd_trans)
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open AdversarialBco.Unified.BLO
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng
open AdversarialBco.Bit.BLP (Par St cV cM opN)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

/-! ## Facts on the constants and on P°'s context -/

namespace NW

theorem n0O_leN (d n k : ℕ) : n0O d n ≤ NeO d n k := by
  unfold n0O NeO
  have : 2 ^ (17 + 0) ≤ 2 ^ (17 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  gcongr

/-- The regime record of BUD-W at the input. -/
theorem okW {d n : ℕ} {δ : ℚ} (h : RegimeW d n (refW d n δ)) : (rW d n δ).OK := reg_okW d n (kDel δ) _ h

theorem tp_eq (d n : ℕ) (δ : ℚ) : (rW d n δ).tp = 1 / 2 ^ (parOW d n δ).p := rfl

/-- `|A°_u|² ≤ 1/δe` at a round `u ≤ τ` (Bit/BLRoundCtx.lean's `opN_A_sq` on `DetBase`). -/
theorem opN_A_sq {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ} (H : DetBase c δ π m) {u : ℕ}
    (hu : u ≤ c.tau π m) : opN (c.st π u).A ≤ Real.sqrt (1 / c.p.δe) := by
  have hI := H.stInv_le_tau u hu
  have hde := H.rows.pos_de
  have hP : ((c.st π u).P - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := psd_trans hI.pbl hI.pbd
  rw [← opN_transpose]
  refine opN_le_of_mulVec _ _ (Real.sqrt_nonneg _) fun v => ?_
  have hS := inv_norm_le _ _ c.p.δe hde hP hI.SP v
  have e : (c.st π u).Aᵀ *ᵥ v ⬝ᵥ (c.st π u).Aᵀ *ᵥ v = v ⬝ᵥ ((c.st π u).S *ᵥ v) := by
    rw [← hI.AA, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, ← Matrix.mulVec_transpose]
  have h2 : oNorm ((c.st π u).Aᵀ *ᵥ v) ^ 2 ≤ (Real.sqrt (1 / c.p.δe) * oNorm v) ^ 2 := by
    rw [oNorm_sq, e, mul_pow, Real.sq_sqrt (by positivity)]
    calc v ⬝ᵥ ((c.st π u).S *ᵥ v) ≤ oNorm v * oNorm ((c.st π u).S *ᵥ v) := (le_abs_self _).trans (abs_dot_le _ _)
      _ ≤ oNorm v * (oNorm v / c.p.δe) := mul_le_mul_of_nonneg_left hS (oNorm_nonneg _)
      _ = 1 / c.p.δe * oNorm v ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (oNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (oNorm_nonneg _)) two_ne_zero).1 h2

/-- P°'s floor `δ_0 = 1/N_0` against the level: `1/δ_0 ≤ N_e`. -/
theorem inv_de_le_Ne (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (poW d n δ).δe ≤ (rW d n δ).Ne := by
  show 1 / (1 / (n0W d n : ℝ)) ≤ ((NeO d n (kDel δ) : ℕ) : ℝ)
  rw [one_div_one_div]
  exact_mod_cast n0O_leN d n (kDel δ)

/-- `d/δ_0 ≤ Λ = d N_e` (the level reading of the trace cap). -/
theorem d_de_le (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (d : ℝ) / (poW d n δ).δe ≤ (rW d n δ).Lam := by
  have h := inv_de_le_Ne d n δ hd hn
  have e : (d : ℝ) / (poW d n δ).δe = d * (1 / (poW d n δ).δe) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg d)

/-- `1/δ_0 ≤ Λ`. -/
theorem inv_de_le_Lam (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (poW d n δ).δe ≤ (rW d n δ).Lam := by
  have h := inv_de_le_Ne d n δ hd hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN : 0 ≤ (rW d n δ).Ne := by show (0 : ℝ) ≤ ((NeO d n (kDel δ) : ℕ) : ℝ); positivity
  have : (rW d n δ).Ne ≤ (rW d n δ).Lam := by
    show (rW d n δ).Ne ≤ (rW d n δ).d * (rW d n δ).Ne
    exact le_mul_of_one_le_left hN hd'
  linarith

/-- Event (a)'s level against BUD-W's `L_g⁺`: `ln(14 n/δ_c) ≤ ln 14 + 5 L_e/144`. -/
theorem lg_le (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    lgW n (refW d n δ).δc ≤ (rW d n δ).Lgb := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := ((NeO d n (kDel δ) : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast Unified.BudK.NeO_pos d n (kDel δ) hd hn
  have hN0 : (0 : ℝ) < N := by linarith
  have hn4 : (n : ℝ) ^ 4 ≤ N := by
    have h1 : (n0W d n : ℝ) ≤ N := by rw [hN]; exact_mod_cast n0O_leN d n (kDel δ)
    have h2 : (n : ℝ) ^ 4 ≤ (n0W d n : ℝ) := by
      show (n : ℝ) ^ 4 ≤ ((15 * 2 ^ (17 + 0) * d ^ 3 * n ^ 4 : ℕ) : ℝ)
      push_cast
      have : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd'
      nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
    linarith
  have hlog : 4 * Real.log n ≤ Real.log N := by
    have e := Real.log_pow (n : ℝ) 4; push_cast at e
    rw [← e]; exact Real.log_le_log (by positivity) hn4
  have hLe : (rW d n δ).Le = 36 * Real.log N := Unified.BudK.Le_eq d n (kDel δ) hd hn
  show Real.log (14 * n / (1 / N)) ≤ Real.log 14 + 5 * (rW d n δ).Le / 144
  rw [hLe, show (14 : ℝ) * n / (1 / N) = 14 * n * N by field_simp,
    Real.log_mul (by positivity) hN0.ne', Real.log_mul (by norm_num) (by positivity)]
  linarith

/-- `|ξ_s| ≤ Ξ` from event (a). -/
theorem xi_norm {c : Df2Ctx d} {π πw : Df2Path d} {m n : ℕ} {δ : ℚ} {s : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (H : EvGW c π πw (lgW n (refW d n δ).δc) (leW (refW d n δ).δc) m) (hs : s ≤ c.tau πw m) :
    oNorm (π.xi s) ≤ (rW d n δ).Xi := by
  obtain ⟨-, -, hx⟩ := H s hs
  have := lg_le d n δ hd hn
  unfold oNorm RegW.Xi
  apply Real.sqrt_le_sqrt
  calc π.xi s ⬝ᵥ π.xi s ≤ 8 * d / 3 * lgW n (refW d n δ).δc := hx
    _ ≤ 8 * (rW d n δ).d / 3 * (rW d n δ).Lgb := by
        show 8 * (d : ℝ) / 3 * lgW n (refW d n δ).δc ≤ 8 * (d : ℝ) / 3 * (rW d n δ).Lgb
        gcongr

/-- E1: `|ξ' - ξ| ≤ e_ξ`. -/
theorem dxi_norm {n : ℕ} {δ : ℚ} (ξ' : Fin d → ℚ) (ξ : Fin d → ℝ)
    (h : ∀ i, |(ξ' i : ℝ) - ξ i| ≤ 4 / 2 ^ ((parOW d n δ).B / 2)) : oNorm (cV ξ' - ξ) ≤ (rW d n δ).exi := by
  show oNorm (cV ξ' - ξ) ≤ Real.sqrt d * (4 / 2 ^ ((Unified.BudK.parK d n (kDel δ)).B / 2))
  exact oNorm_le_of_abs_le _ _ fun i => h i

end NW

/-! ## The setting -/

/-- What C1 reads of `RCHypOW`, for a general context `c` with P°'s parameters at PARAM-W's reference (`SettK` at
BUD-W). `π` is the unweighted path, `πw` the weighted one, with the same draws. -/
structure SettW (d n : ℕ) (δ : ℚ) (c : Df2Ctx d) (π πw : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) :
    Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hc : RunCaseUW d n δ
  reg : RegimeW d n (refW d n δ)
  bud : BudOKW d n (kDel δ) (refW d n δ)
  enc : EncOKW d n δ
  hs : s < n
  det : DetHypW c πw (s + 1) (refW d n δ)
  tau : c.tau πw (s + 1) = s
  evG : EvGW c π πw (lgW n (refW d n δ).δc) (leW (refW d n δ).δc) (s + 1)
  hp : c.p = poW d n δ
  hcn : c.n = n
  hxi : πw.xi = π.xi
  track : TrackW d n δ st (c.st πw s) s
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ ((parOW d n δ).B / 2)

namespace SettW

variable {n : ℕ} {δ : ℚ} {c : Df2Ctx d} {π πw : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hs' (S : SettW d n δ c π πw s st ξ') : s ≤ c.tau πw (s + 1) := tau_le S.tau

theorem inv (S : SettW d n δ c π πw s st ξ') : c.StInv πw s := S.det.stInv_le_tau s S.hs'

theorem R (S : SettW d n δ c π πw s st ξ') : (rW d n δ).OK := NW.okW S.reg

theorem de_pos (S : SettW d n δ c π πw s st ξ') : 0 < (poW d n δ).δe := by
  have := S.det.rows.pos_de; rwa [S.hp] at this

theorem eps_pos (S : SettW d n δ c π πw s st ξ') : 0 < (rW d n δ).eps := by
  have := S.det.rows.pos_eps; rw [S.hp] at this; exact this

theorem eps_le (S : SettW d n δ c π πw s st ξ') : (rW d n δ).eps ≤ 1 / 4 := S.reg.heps

theorem lam_pos (S : SettW d n δ c π πw s st ξ') : 0 < (poW d n δ).lam := by
  have := S.det.rows.pos_lam; rwa [S.hp] at this

theorem kc_pos (S : SettW d n δ c π πw s st ξ') : 0 < (rW d n δ).kc := by
  have hl := S.lam_pos
  have hη : 0 < (poW d n δ).eta := by have := S.det.rows.pos_eta; rwa [S.hp] at this
  have hk0 : 0 < (poW d n δ).k0 := by have := S.det.k0_pos; rwa [S.hp] at this
  show 0 < (poW d n δ).eta * (poW d n δ).kap * (poW d n δ).lam * (poW d n δ).k0
  rw [show (poW d n δ).kap = 1 / 4 from rfl]
  positivity

theorem Lam_pos (S : SettW d n δ c π πw s st ξ') : 0 < (rW d n δ).Lam := by
  have := NW.inv_de_le_Lam d n δ S.hd S.hn
  have h0 : 0 < 1 / (poW d n δ).δe := one_div_pos.2 S.de_pos
  linarith

/-- `d/δe ≤ Λ`. -/
theorem de_c (S : SettW d n δ c π πw s st ξ') : (d : ℝ) / c.p.δe ≤ (rW d n δ).Lam := by
  rw [S.hp]; exact NW.d_de_le d n δ S.hd S.hn

theorem inv_de_c (S : SettW d n δ c π πw s st ξ') : 1 / c.p.δe ≤ (rW d n δ).Lam := by
  rw [S.hp]; exact NW.inv_de_le_Lam d n δ S.hd S.hn

/-! ### The draw -/

theorem xi_le (S : SettW d n δ c π πw s st ξ') : oNorm (π.xi s) ≤ (rW d n δ).Xi :=
  NW.xi_norm S.hd S.hn S.evG S.hs'

theorem dxi_le (S : SettW d n δ c π πw s st ξ') : oNorm (cV ξ' - π.xi s) ≤ (rW d n δ).exi :=
  NW.dxi_norm ξ' (π.xi s) S.xi

theorem exi_le (S : SettW d n δ c π πw s st ξ') : (rW d n δ).exi ≤ (rW d n δ).tp / 2 := (S.R.ezt_exi).2.2.2

theorem exi_le_one (S : SettW d n δ c π πw s st ξ') : (rW d n δ).exi ≤ 1 := by
  have h1 := S.exi_le
  have h2 := S.R.htp0
  have h3 : (rW d n δ).tp ≤ 1 := by
    rw [NW.tp_eq, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  linarith

theorem xi'_le (S : SettW d n δ c π πw s st ξ') : oNorm (cV ξ') ≤ (rW d n δ).Xi1 := by
  have := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
  rw [add_sub_cancel] at this
  unfold RegW.Xi1; linarith [S.xi_le, S.dxi_le, S.exi_le_one]

theorem xi_le1 (S : SettW d n δ c π πw s st ξ') : oNorm (π.xi s) ≤ (rW d n δ).Xi1 := by
  unfold RegW.Xi1; linarith [S.xi_le]

/-! ### P°'s matrices at round `s` -/

theorem P_sym (S : SettW d n δ c π πw s st ξ') : (c.st πw s).Pᵀ = (c.st πw s).P := by
  have := S.inv.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem PS (S : SettW d n δ c π πw s st ξ') : (c.st πw s).P * (c.st πw s).S = 1 := mul_eq_one_comm.1 S.inv.SP

/-- `Aᵀ (P A) = 1`. -/
theorem APA (S : SettW d n δ c π πw s st ξ') : (c.st πw s).Aᵀ * ((c.st πw s).P * (c.st πw s).A) = 1 := by
  have h : ((c.st πw s).P * (c.st πw s).A) * (c.st πw s).Aᵀ = 1 := by
    rw [Matrix.mul_assoc, S.inv.AA, S.PS]
  exact mul_eq_one_comm.1 h

/-- `(P A)(P A)ᵀ = P`. -/
theorem PA_sq (S : SettW d n δ c π πw s st ξ') :
    ((c.st πw s).P * (c.st πw s).A) * ((c.st πw s).P * (c.st πw s).A)ᵀ = (c.st πw s).P := by
  rw [Matrix.transpose_mul, S.P_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st πw s).A, S.inv.AA, ← Matrix.mul_assoc,
    S.PS, Matrix.one_mul]

theorem trP_le (S : SettW d n δ c π πw s st ξ') : (c.st πw s).P.trace ≤ (rW d n δ).Lam := by
  have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le S.hs')
  rw [inv_inv] at this
  have e : (d : ℝ) * c.p.δe⁻¹ = d / c.p.δe := by ring
  linarith [S.de_c]

theorem opN_A0 (S : SettW d n δ c π πw s st ξ') : opN (c.st πw s).A ≤ Real.sqrt (rW d n δ).Lam :=
  (NW.opN_A_sq S.det.toDetBase S.hs').trans (Real.sqrt_le_sqrt S.inv_de_c)

theorem opN_PA0 (S : SettW d n δ c π πw s st ξ') :
    opN ((c.st πw s).P * (c.st πw s).A) ≤ Real.sqrt (rW d n δ).Lam := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PA_sq]; exact S.trP_le

theorem opN_P0 (S : SettW d n δ c π πw s st ξ') : opN (c.st πw s).P ≤ (rW d n δ).Lam := by
  have h := opN_mul_le ((c.st πw s).P * (c.st πw s).A) ((c.st πw s).P * (c.st πw s).A)ᵀ
  rw [S.PA_sq, opN_transpose] at h
  have h2 := S.opN_PA0
  have h0 := opN_nonneg ((c.st πw s).P * (c.st πw s).A)
  have : Real.sqrt (rW d n δ).Lam * Real.sqrt (rW d n δ).Lam = (rW d n δ).Lam := Real.mul_self_sqrt S.Lam_pos.le
  nlinarith

/-! ### P°'s update of round `s` -/

theorem R1 (S : SettW d n δ c π πw s st ξ') :
    (c.Pn πw s).PosDef ∧ c.Sn πw s * c.Pn πw s = 1 ∧ c.An πw s * (c.An πw s)ᵀ = c.Sn πw s ∧ (c.An πw s).det ≠ 0 :=
  S.det.r1_le_tau S.hs'

theorem Pn_sym (S : SettW d n δ c π πw s st ξ') : (c.Pn πw s)ᵀ = c.Pn πw s := by
  have := S.R1.1.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem trn (S : SettW d n δ c π πw s st ξ') :
    (c.Pn πw s).trace ≤ (rW d n δ).Lam ∧ (c.Sn πw s).trace ≤ (rW d n δ).Lam := by
  have h := S.det.not_gdT S.hs'
  unfold Df2Ctx.GdT at h
  rw [not_or, not_lt, not_lt] at h
  exact ⟨h.1.trans S.de_c, h.2.trans S.de_c⟩

/-- `A' (A'ᵀ P') = 1`. -/
theorem An_inv (S : SettW d n δ c π πw s st ξ') : c.An πw s * ((c.An πw s)ᵀ * c.Pn πw s) = 1 := by
  rw [← Matrix.mul_assoc, S.R1.2.2.1, S.R1.2.1]

/-- `(P' A') A'ᵀ = 1`. -/
theorem PnAn_inv (S : SettW d n δ c π πw s st ξ') : (c.Pn πw s * c.An πw s) * (c.An πw s)ᵀ = 1 := by
  rw [Matrix.mul_assoc, S.R1.2.2.1]; exact mul_eq_one_comm.1 S.R1.2.1

theorem opN_An (S : SettW d n δ c π πw s st ξ') : opN (c.An πw s) ≤ Real.sqrt (rW d n δ).Lam := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.R1.2.2.1]; exact S.trn.2

theorem PnAn_sq (S : SettW d n δ c π πw s st ξ') :
    (c.Pn πw s * c.An πw s) * (c.Pn πw s * c.An πw s)ᵀ = c.Pn πw s := by
  rw [Matrix.transpose_mul, S.Pn_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.An πw s), S.R1.2.2.1,
    ← Matrix.mul_assoc, mul_eq_one_comm.1 S.R1.2.1, Matrix.one_mul]

theorem opN_PnAn (S : SettW d n δ c π πw s st ξ') :
    opN (c.Pn πw s * c.An πw s) ≤ Real.sqrt (rW d n δ).Lam := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PnAn_sq]; exact S.trn.1

theorem opN_AnPn (S : SettW d n δ c π πw s st ξ') :
    opN ((c.An πw s)ᵀ * c.Pn πw s) ≤ Real.sqrt (rW d n δ).Lam := by
  have : (c.An πw s)ᵀ * c.Pn πw s = (c.Pn πw s * c.An πw s)ᵀ := by rw [Matrix.transpose_mul, S.Pn_sym]
  rw [this, opN_transpose]; exact S.opN_PnAn

theorem aq (S : SettW d n δ c π πw s st ξ') : 1 / 2 ≤ c.aa πw s ∧ 1 / 4 ≤ c.qq πw s := S.det.aq S.hs'

/-- `A' = A° N°`, `N° = a^{-1/2} I - (a^{-1/2} c') ξ ξᵀ`. -/
theorem An_fac (S : SettW d n δ c π πw s st ξ') :
    c.An πw s = (c.st πw s).A * ((Real.sqrt (c.aa πw s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (-(c.cc πw s / (Real.sqrt (c.aa πw s) * Real.sqrt (c.qq πw s) *
        (Real.sqrt (c.aa πw s) + Real.sqrt (c.qq πw s))))) • vecMulVec (πw.xi s) (πw.xi s)) := by
  have ha : 0 < c.aa πw s := by linarith [S.aq.1]
  have hq : 0 < c.qq πw s := by linarith [S.aq.2]
  unfold Df2Ctx.An Df2Ctx.w
  rw [An_eq_mul, ← coef_eq _ _ _ ha hq]
  rfl

/-- `P' A' = (P° A°) N°⁻¹`, `N°⁻¹ = a^{1/2} I + (c/(a^{1/2} + q^{1/2})) ξ ξᵀ`. -/
theorem PnAn_fac (S : SettW d n δ c π πw s st ξ') :
    c.Pn πw s * c.An πw s = ((c.st πw s).P * (c.st πw s).A) * (Real.sqrt (c.aa πw s) •
      (1 : Matrix (Fin d) (Fin d) ℝ) +
      (c.cc πw s / (Real.sqrt (c.aa πw s) + Real.sqrt (c.qq πw s))) • vecMulVec (πw.xi s) (πw.xi s)) := by
  have ha : 0 < c.aa πw s := by linarith [S.aq.1]
  have hq : 0 < c.qq πw s := by linarith [S.aq.2]
  exact PnAn_eq (c.st πw s).P (c.st πw s).A (πw.xi s) (c.cc πw s) (c.aa πw s) (c.qq πw s) ha hq rfl S.APA S.P_sym

/-! ### `|Y°| ≤ y0`, `|c°| ≤ c̄_w` and Lemma WR (ii) -/

theorem Y_le (S : SettW d n δ c π πw s st ξ') : |c.Y πw s| ≤ (rW d n δ).y0 := S.det.Ybd s S.hs'

theorem cc_eq (S : SettW d n δ c π πw s st ξ') : c.cc πw s = (rW d n δ).kc * c.Y πw s := by
  unfold Df2Ctx.cc; rw [S.hp]; rfl

theorem cc_le (S : SettW d n δ c π πw s st ξ') : |c.cc πw s| ≤ (rW d n δ).cbw := by
  rw [S.cc_eq, abs_mul, abs_of_pos S.kc_pos]
  exact mul_le_mul_of_nonneg_left S.Y_le S.kc_pos.le

/-- Lemma WR (ii) for P°: on a weighted round, `|ξ| ≤ (b0 + 1)^{1/2} ≤ Ξ_w`. -/
theorem xi_w (S : SettW d n δ c π πw s st ξ') (hY : c.Y πw s ≠ 0) : oNorm (π.xi s) ≤ (rW d n δ).Xw := by
  have h := S.det.Ywt s S.hs' hY
  rw [S.hxi] at h
  have h1 : oNorm (π.xi s) ≤ Real.sqrt ((rW d n δ).b0 + 1) := by
    unfold oNorm; exact Real.sqrt_le_sqrt h
  have := S.R.htp0
  unfold RegW.Xw; linarith

end SettW

end AdversarialBco.UW.EngC
