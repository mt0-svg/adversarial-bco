/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngDefs
public import AdversarialBco.Bit.BLRoundSet

@[expose] public section

/-!
# Piece C for BL-O: the setting of round `s` at `k`

Bit/BLRoundCtx.lean and Bit/BLRoundSet.lean at the constants of Theorem BUD at `k` (Unified/BudDefs.lean): the
numerical facts on the constants (namespace `NK`), the facts of DET at `s + 1` with `τ(s + 1) = s` at round `s`, and
`SettK` (`Sett` at `k`) with P°'s bounds at round `s`. The real lemmas that do not read the constants are those of
Bit/BLRoundBasic.lean and Bit/BLRoundAlg.lean.
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (inv_norm_le psd_trans)
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St cV cM opN)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

/-! ## Numerical facts on the constants -/

namespace NK

open AdversarialBco.Unified.BudK

theorem tp_pos (d n k : ℕ) : 0 < tp d n k := by unfold tp; positivity

theorem tp_le_one (d n k : ℕ) : tp d n k ≤ 1 := by
  unfold tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

/-- The coin bound gives `2^{-B/2} ≤ 2^{-p-2}/(n (⌈d/2⌉ + 1))`; hence `e_ξ ≤ 2^{-p}` and `e_ζ ≤ 2^{-p-1}`. -/
theorem exi_le {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : BudOK d n k) : exi d n k ≤ tp d n k := by
  have hc := h.coins
  set z : ℝ := 1 / 2 ^ ((parK d n k).B / 2) with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  set m : ℕ := (d + 1) / 2 + 1 with hm
  have hk2 : (d : ℝ) + 1 ≤ 2 * m := by
    have : d + 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hsd : Real.sqrt d ≤ m := by
    have hk0 : (0 : ℝ) ≤ m := by positivity
    rw [show (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) from (Real.sqrt_sq hk0).symm]
    apply Real.sqrt_le_sqrt
    have h2 : ((d : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hk2 2
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ m := by positivity
  have h1 : (m : ℝ) * z ≤ n * m * z := by
    have := mul_le_mul_of_nonneg_right hn1 (mul_nonneg hk0 hz0.le)
    linarith [show (n : ℝ) * m * z = n * (m * z) by ring]
  unfold exi dbits at *
  have e : (4 : ℝ) / 2 ^ ((parK d n k).B / 2) = 4 * z := by rw [hz]; ring
  rw [e]
  have : Real.sqrt d * (4 * z) ≤ 4 * (m * z) := by nlinarith [Real.sqrt_nonneg (d : ℝ)]
  nlinarith

theorem ezt_le {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : BudOK d n k) : ezt d n k ≤ tp d n k / 2 := by
  have hc := h.coins
  set z : ℝ := 1 / 2 ^ ((parK d n k).B / 2) with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  have hk : (2 : ℝ) ≤ (((d + 1) / 2 + 1 : ℕ) : ℝ) := by
    have : 2 ≤ (d + 1) / 2 + 1 := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ezt dbits at *
  have e : (2 : ℝ) / 2 ^ ((parK d n k).B / 2) = 2 * z := by rw [hz]; ring
  rw [e]
  have hnk : (2 : ℝ) ≤ n * (((d + 1) / 2 + 1 : ℕ) : ℝ) := by nlinarith
  have : (2 : ℝ) * z ≤ n * (((d + 1) / 2 + 1 : ℕ) : ℝ) * z := mul_le_mul_of_nonneg_right hnk hz0.le
  linarith

theorem ha_nonneg (d n k : ℕ) : 0 ≤ ha d n k := by
  unfold ha; have := tp_pos d n k; positivity

theorem hb_nonneg {d n k : ℕ} (h : BudOK d n k) : 0 ≤ hb d n k := by
  have := h.hTr_le 0 (Nat.zero_le n)
  unfold hTr at this; simp at this
  linarith [ha_nonneg d n k]

theorem tp_small (d n k : ℕ) : tp d n k ≤ 1 / 1000 := by
  rw [tp_eq]
  have hp : 160 ≤ pK d n k := by unfold pK; omega
  have h1 : (2 : ℝ) ^ 160 ≤ 2 ^ pK d n k := pow_le_pow_right₀ (by norm_num) hp
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (1000 : ℝ) ≤ 2 ^ 160 := by norm_num
  linarith

theorem Le_pos {d n k : ℕ} (h : BudOK d n k) : 0 < Le d n k := by linarith [h.Le_ge]

theorem sqrtLe_ge {d n k : ℕ} (h : BudOK d n k) : 1 ≤ Real.sqrt (Le d n k) := by
  rw [Real.le_sqrt (by norm_num) (Le_pos h).le]; linarith [h.Le_ge]

theorem Lgb_ge (d n k : ℕ) (h : BudOK d n k) : 1 / 4 ≤ Lgb d n k := by
  unfold Lgb
  have h14 : (1 : ℝ) ≤ Real.log 14 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have := Le_pos h
  nlinarith

theorem Yb_ge {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4) :
    16 * Real.sqrt (Le d n k) ≤ Yb d n k := by
  unfold Yb
  have hs := sqrtLe_ge h
  have hx := Real.sqrt_nonneg (Lgb d n k)
  have h4 : 16 * Real.sqrt (Le d n k) ≤ 4 * Real.sqrt (Le d n k) / eps d n k := by
    rw [le_div_iff₀ he0]; nlinarith
  nlinarith

theorem Yb_pos {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4) : 0 < Yb d n k := by
  linarith [Yb_ge h he0 he, sqrtLe_ge h]

theorem kc_pos {d n k : ℕ} (hl : 0 < (poK d n k).lam) (hη : 0 < (poK d n k).eta)
    (hk : (poK d n k).kap = 1 / 4) (hk0 : 0 < (poK d n k).k0) : 0 < kc d n k := by
  unfold kc; rw [hk]; positivity

theorem Dc_le_cb {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4)
    (hkc : 0 ≤ kc d n k) : Dc d n k ≤ cb d n k := by
  have hY := Yb_ge h he0 he
  have hY0 := Yb_pos h he0 he
  have hs := sqrtLe_ge h
  have htp := tp_small d n k
  have htp0 := (tp_pos d n k).le
  have hcb : 0 ≤ cb d n k := by unfold cb; positivity
  have hq : (Pb d n k + 1) / Yb d n k ≤ 1 / 4 := by
    rw [div_le_iff₀ hY0]; unfold Pb; nlinarith
  have hf : 11 / 10 * (Pb d n k + 1) / Yb d n k + 1 / 16 ≤ 1 := by
    have : 11 / 10 * (Pb d n k + 1) / Yb d n k = 11 / 10 * ((Pb d n k + 1) / Yb d n k) := by ring
    rw [this]; linarith
  have hf0 : 0 ≤ 11 / 10 * (Pb d n k + 1) / Yb d n k + 1 / 16 := by
    have : 0 ≤ Pb d n k + 1 := by unfold Pb; positivity
    positivity
  unfold Dc
  calc cb d n k * tp d n k * (11 / 10 * (Pb d n k + 1) / Yb d n k + 1 / 16) ≤ cb d n k * 1 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hcb) hf hf0 (by positivity)
    _ = cb d n k := by ring

theorem Dc_small {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4)
    (hkc : 0 ≤ kc d n k) : Dc d n k * (1 + Xi1 d n k ^ 2) ≤ 1 / 10 ^ 30 :=
  (mul_le_mul_of_nonneg_right (Dc_le_cb h he0 he hkc) (by positivity)).trans h.cb_le

theorem Dc_nonneg {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4)
    (hkc : 0 ≤ kc d n k) : 0 ≤ Dc d n k := by
  have := Yb_pos h he0 he
  have : 0 ≤ Pb d n k := by unfold Pb; positivity
  have := tp_pos d n k
  unfold Dc cb; positivity

theorem cb_nonneg {d n k : ℕ} (h : BudOK d n k) (he0 : 0 < eps d n k) (he : eps d n k ≤ 1 / 4)
    (hkc : 0 ≤ kc d n k) : 0 ≤ cb d n k := by
  have := Yb_pos h he0 he; unfold cb; positivity

theorem Xi_nonneg (d n k : ℕ) : 0 ≤ Xi d n k := Real.sqrt_nonneg _

theorem Xi1_pos (d n k : ℕ) : 0 < Xi1 d n k := by unfold Xi1; linarith [Xi_nonneg d n k]

theorem Lam_pos {d n k : ℕ} (hd : 1 ≤ d) (h : BudOK d n k) (hde : 0 < (poK d n k).δe) : 0 < Lam d n k := by
  have e := h.enc.de_eq
  unfold de at e
  have hN : 0 < BudK.Ne d n k := by
    rw [e] at hde; exact one_div_pos.1 hde
  unfold Lam; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

/-- `d/δe = Λ`. -/
theorem d_de {d n k : ℕ} (h : BudOK d n k) : (d : ℝ) / (poK d n k).δe = Lam d n k := by
  have e := h.enc.de_eq
  unfold de at e
  rw [e]; unfold Lam; rw [div_div_eq_mul_div, div_one]

/-- `1/δe ≤ Λ`. -/
theorem inv_de_le_Lam {d n k : ℕ} (hd : 1 ≤ d) (h : BudOK d n k) : 1 / (poK d n k).δe ≤ Lam d n k := by
  have e := h.enc.de_eq
  unfold de at e
  rw [e, one_div_one_div]
  unfold Lam
  have hN : 0 ≤ BudK.Ne d n k := by unfold BudK.Ne; positivity
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- `|ξ_s| ≤ Ξ` on G. -/
theorem xi_norm {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m n k s : ℕ} (H : DetHyp c δ π m) (hs : s ≤ c.tau π m)
    (hp : c.p = poK d n k) (hcn : c.n = n) (h : BudOK d n k) : oNorm (π.xi s) ≤ Xi d n k := by
  obtain ⟨-, -, hx⟩ := H.evG s hs
  rw [hp, hcn] at hx
  have := h.Lg_le
  unfold oNorm Xi
  apply Real.sqrt_le_sqrt
  calc π.xi s ⬝ᵥ π.xi s ≤ 8 * d / 3 * df2Lg (poK d n k) n := hx
    _ ≤ 8 * d / 3 * Lgb d n k := by gcongr

/-- E1: `|ξ' - ξ| ≤ e_ξ`. -/
theorem dxi_norm {n k : ℕ} (ξ' : Fin d → ℚ) (ξ : Fin d → ℝ)
    (h : ∀ i, |(ξ' i : ℝ) - ξ i| ≤ 4 / 2 ^ ((parK d n k).B / 2)) : oNorm (cV ξ' - ξ) ≤ exi d n k := by
  unfold exi
  exact oNorm_le_of_abs_le _ _ fun i => by simpa [cV] using h i

/-- `λ'` within `2^{-p-4} λ` of `λ`. -/
theorem lam_err {d n k : ℕ} (h : BudOK d n k) (hl : 0 < (poK d n k).lam) :
    |((parK d n k).lam : ℝ) - (poK d n k).lam| ≤ tp d n k / 16 * (poK d n k).lam := by
  have := h.enc.lam_rel
  unfold lam at this
  have e : ((parK d n k).lam : ℝ) - (poK d n k).lam =
      (poK d n k).lam * (((parK d n k).lam : ℝ) / (poK d n k).lam - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hl]
  nlinarith

end NK

/-! ## The setting -/

/-- What C1 reads of `RCHypO`, for a general context `c` with P°'s parameters at `k` (`Sett` at `k`). -/
structure SettK (d n k : ℕ) (c : Df2Ctx d) (δ : ℝ) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) :
    Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hc : RunCaseK d n k
  bud : BudOK d n k
  hs : s < n
  det : DetHyp c δ π (s + 1)
  tau : c.tau π (s + 1) = s
  hp : c.p = poK d n k
  hcn : c.n = n
  track : TrackK d n k st (c.st π s) s
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ ((parK d n k).B / 2)

namespace SettK

variable {n k : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hs' (S : SettK d n k c δ π s st ξ') : s ≤ c.tau π (s + 1) := tau_le S.tau

theorem inv (S : SettK d n k c δ π s st ξ') : c.StInv π s := S.det.stInv_le_tau s S.hs'

theorem de_pos (S : SettK d n k c δ π s st ξ') : 0 < (poK d n k).δe := by
  have := S.det.rows.pos_de; rwa [S.hp] at this

theorem eps_pos (S : SettK d n k c δ π s st ξ') : 0 < BudK.eps d n k := by
  have := S.det.rows.pos_eps; rw [S.hp] at this; exact this

theorem eps_le (S : SettK d n k c δ π s st ξ') : BudK.eps d n k ≤ 1 / 4 := S.hc

theorem lam_pos (S : SettK d n k c δ π s st ξ') : 0 < (poK d n k).lam := by
  have := S.det.rows.pos_lam; rwa [S.hp] at this

theorem lam_small (S : SettK d n k c δ π s st ξ') : (poK d n k).lam ≤ 1 / 1000 := by
  have h := S.det.rows.r11; rw [S.hp] at h
  have hL := S.bud.Le_ge
  unfold BudK.Le at hL
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast S.hd
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem kc_pos (S : SettK d n k c δ π s st ξ') : 0 < BudK.kc d n k := by
  have hk := S.det.kap; have hk0 := S.det.k0_pos; have hη := S.det.rows.pos_eta
  rw [S.hp] at hk hk0 hη
  have := S.lam_small
  exact NK.kc_pos S.lam_pos hη hk hk0

theorem Lam_pos (S : SettK d n k c δ π s st ξ') : 0 < BudK.Lam d n k := NK.Lam_pos S.hd S.bud S.de_pos

theorem de_c (S : SettK d n k c δ π s st ξ') : (d : ℝ) / c.p.δe = BudK.Lam d n k := by
  rw [S.hp]; exact NK.d_de S.bud

/-! ### The draw -/

theorem xi_le (S : SettK d n k c δ π s st ξ') : oNorm (π.xi s) ≤ BudK.Xi d n k :=
  NK.xi_norm S.det S.hs' S.hp S.hcn S.bud

theorem dxi_le (S : SettK d n k c δ π s st ξ') : oNorm (cV ξ' - π.xi s) ≤ BudK.exi d n k := NK.dxi_norm ξ' (π.xi s) S.xi

theorem exi_le_one (S : SettK d n k c δ π s st ξ') : BudK.exi d n k ≤ 1 :=
  (NK.exi_le S.hd S.hn S.bud).trans (NK.tp_le_one d n k)

theorem xi'_le (S : SettK d n k c δ π s st ξ') : oNorm (cV ξ') ≤ BudK.Xi1 d n k := by
  have := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
  rw [add_sub_cancel] at this
  unfold BudK.Xi1; linarith [S.xi_le, S.dxi_le, S.exi_le_one]

theorem xi_le1 (S : SettK d n k c δ π s st ξ') : oNorm (π.xi s) ≤ BudK.Xi1 d n k := by
  unfold BudK.Xi1; linarith [S.xi_le]

/-! ### P°'s matrices at round `s` -/

theorem P_sym (S : SettK d n k c δ π s st ξ') : (c.st π s).Pᵀ = (c.st π s).P := by
  have := S.inv.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem PS (S : SettK d n k c δ π s st ξ') : (c.st π s).P * (c.st π s).S = 1 := mul_eq_one_comm.1 S.inv.SP

/-- `Aᵀ (P A) = 1`. -/
theorem APA (S : SettK d n k c δ π s st ξ') : (c.st π s).Aᵀ * ((c.st π s).P * (c.st π s).A) = 1 := by
  have h : ((c.st π s).P * (c.st π s).A) * (c.st π s).Aᵀ = 1 := by
    rw [Matrix.mul_assoc, S.inv.AA, S.PS]
  exact mul_eq_one_comm.1 h

/-- `(P A)(P A)ᵀ = P`. -/
theorem PA_sq (S : SettK d n k c δ π s st ξ') :
    ((c.st π s).P * (c.st π s).A) * ((c.st π s).P * (c.st π s).A)ᵀ = (c.st π s).P := by
  rw [Matrix.transpose_mul, S.P_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st π s).A, S.inv.AA, ← Matrix.mul_assoc,
    S.PS, Matrix.one_mul]

theorem trP_le (S : SettK d n k c δ π s st ξ') : (c.st π s).P.trace ≤ BudK.Lam d n k := by
  have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le S.hs')
  rwa [inv_inv, S.de_c] at this

theorem opN_A0 (S : SettK d n k c δ π s st ξ') : opN (c.st π s).A ≤ Real.sqrt (BudK.Lam d n k) :=
  (opN_A_sq S.det S.hs').trans (Real.sqrt_le_sqrt (by rw [S.hp]; exact NK.inv_de_le_Lam S.hd S.bud))

theorem opN_PA0 (S : SettK d n k c δ π s st ξ') :
    opN ((c.st π s).P * (c.st π s).A) ≤ Real.sqrt (BudK.Lam d n k) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PA_sq]; exact S.trP_le

theorem opN_P0 (S : SettK d n k c δ π s st ξ') : opN (c.st π s).P ≤ BudK.Lam d n k := by
  have h := opN_mul_le ((c.st π s).P * (c.st π s).A) ((c.st π s).P * (c.st π s).A)ᵀ
  rw [S.PA_sq, opN_transpose] at h
  have h2 := S.opN_PA0
  have h0 := opN_nonneg ((c.st π s).P * (c.st π s).A)
  have : Real.sqrt (BudK.Lam d n k) * Real.sqrt (BudK.Lam d n k) = BudK.Lam d n k := Real.mul_self_sqrt S.Lam_pos.le
  nlinarith

/-! ### P°'s update of round `s` -/

theorem R1 (S : SettK d n k c δ π s st ξ') :
    (c.Pn π s).PosDef ∧ c.Sn π s * c.Pn π s = 1 ∧ c.An π s * (c.An π s)ᵀ = c.Sn π s ∧ (c.An π s).det ≠ 0 :=
  S.det.r1_le_tau S.hs'

theorem Pn_sym (S : SettK d n k c δ π s st ξ') : (c.Pn π s)ᵀ = c.Pn π s := by
  have := S.R1.1.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem trn (S : SettK d n k c δ π s st ξ') : (c.Pn π s).trace ≤ BudK.Lam d n k ∧ (c.Sn π s).trace ≤ BudK.Lam d n k := by
  have h := S.det.not_gdT S.hs'
  unfold Df2Ctx.GdT at h
  rw [not_or, not_lt, not_lt, S.de_c] at h
  exact h

/-- `A' (A'ᵀ P') = 1`. -/
theorem An_inv (S : SettK d n k c δ π s st ξ') : c.An π s * ((c.An π s)ᵀ * c.Pn π s) = 1 := by
  rw [← Matrix.mul_assoc, S.R1.2.2.1, S.R1.2.1]

/-- `(P' A') A'ᵀ = 1`. -/
theorem PnAn_inv (S : SettK d n k c δ π s st ξ') : (c.Pn π s * c.An π s) * (c.An π s)ᵀ = 1 := by
  rw [Matrix.mul_assoc, S.R1.2.2.1]; exact mul_eq_one_comm.1 S.R1.2.1

theorem opN_An (S : SettK d n k c δ π s st ξ') : opN (c.An π s) ≤ Real.sqrt (BudK.Lam d n k) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.R1.2.2.1]; exact S.trn.2

theorem PnAn_sq (S : SettK d n k c δ π s st ξ') :
    (c.Pn π s * c.An π s) * (c.Pn π s * c.An π s)ᵀ = c.Pn π s := by
  rw [Matrix.transpose_mul, S.Pn_sym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.An π s), S.R1.2.2.1,
    ← Matrix.mul_assoc, mul_eq_one_comm.1 S.R1.2.1, Matrix.one_mul]

theorem opN_PnAn (S : SettK d n k c δ π s st ξ') : opN (c.Pn π s * c.An π s) ≤ Real.sqrt (BudK.Lam d n k) := by
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [S.PnAn_sq]; exact S.trn.1

theorem opN_AnPn (S : SettK d n k c δ π s st ξ') : opN ((c.An π s)ᵀ * c.Pn π s) ≤ Real.sqrt (BudK.Lam d n k) := by
  have : (c.An π s)ᵀ * c.Pn π s = (c.Pn π s * c.An π s)ᵀ := by rw [Matrix.transpose_mul, S.Pn_sym]
  rw [this, opN_transpose]; exact S.opN_PnAn

theorem aq (S : SettK d n k c δ π s st ξ') : 1 / 2 ≤ c.aa π s ∧ 1 / 4 ≤ c.qq π s := S.det.aq S.hs'

/-- `A' = A° N°`, `N° = a^{-1/2} I - (a^{-1/2} c') ξ ξᵀ`. -/
theorem An_fac (S : SettK d n k c δ π s st ξ') :
    c.An π s = (c.st π s).A * ((Real.sqrt (c.aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (-(c.cc π s / (Real.sqrt (c.aa π s) * Real.sqrt (c.qq π s) *
        (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))))) • vecMulVec (π.xi s) (π.xi s)) := by
  have ha : 0 < c.aa π s := by linarith [S.aq.1]
  have hq : 0 < c.qq π s := by linarith [S.aq.2]
  unfold Df2Ctx.An Df2Ctx.w
  rw [An_eq_mul, ← coef_eq _ _ _ ha hq]
  rfl

/-- `P' A' = (P° A°) N°⁻¹`, `N°⁻¹ = a^{1/2} I + (c/(a^{1/2} + q^{1/2})) ξ ξᵀ`. -/
theorem PnAn_fac (S : SettK d n k c δ π s st ξ') :
    c.Pn π s * c.An π s = ((c.st π s).P * (c.st π s).A) * (Real.sqrt (c.aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (c.cc π s / (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))) • vecMulVec (π.xi s) (π.xi s)) := by
  have ha : 0 < c.aa π s := by linarith [S.aq.1]
  have hq : 0 < c.qq π s := by linarith [S.aq.2]
  exact PnAn_eq (c.st π s).P (c.st π s).A (π.xi s) (c.cc π s) (c.aa π s) (c.qq π s) ha hq rfl S.APA S.P_sym

/-! ### `|Y°| ≤ Ȳ` and `|c°| ≤ c̄` -/

theorem Y_le (S : SettK d n k c δ π s st ξ') : |c.Y π s| ≤ BudK.Yb d n k := by
  obtain ⟨he, hg, -⟩ := S.det.evG s S.hs'
  have hgv := (S.det.adm s (S.det.le_tau_lt S.hs')).2 _ (S.det.play_keps s).2
  have hLg := S.bud.Lg_le
  have hLgb := NK.Lgb_ge d n k S.bud
  have h := ybar_real (c.pip π s) (gauge c.Kt (WithLp.toLp 2 (c.X π s))) (π.g s (WithLp.toLp 2 (c.play π s)))
    (π.e s) c.p.Le (BudK.Lgb d n k) c.p.eps S.det.rows.pos_eps (by rw [S.hp]; exact S.eps_le) rfl (gauge_nonneg _) hg
    hgv.1 hgv.2 (he.trans (Real.sqrt_le_sqrt (by rw [S.hp, S.hcn]; exact hLg))) hLgb S.det.one_le_Le
  unfold Df2Ctx.Y
  rw [S.hp] at h ⊢
  unfold BudK.Yb BudK.Le BudK.eps
  exact h

theorem cc_eq (S : SettK d n k c δ π s st ξ') : c.cc π s = BudK.kc d n k * c.Y π s := by
  unfold Df2Ctx.cc BudK.kc; rw [S.hp]

theorem cc_le (S : SettK d n k c δ π s st ξ') : |c.cc π s| ≤ BudK.cb d n k := by
  rw [S.cc_eq, abs_mul, abs_of_pos S.kc_pos]
  unfold BudK.cb
  exact mul_le_mul_of_nonneg_left S.Y_le S.kc_pos.le

end SettK

end AdversarialBco.Unified.EngC
