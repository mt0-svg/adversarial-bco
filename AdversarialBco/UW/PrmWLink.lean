/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.PrmWRun
public import AdversarialBco.UW.ProgPure

@[expose] public section

/-!
# PARAM-W on the machine: the values of the line are PARAM-W's numerators

At `e = k_δ`, `parO d n δ = parK d n e` (by definition), and the closed forms of UW/PrmWV.lean are the numerators of
PARAM-W's values (UW/ProgPure.lean): `lf0 = L_00/2^q`, `lf1 = L_01/2^q`, `l2O = l_2/2^q`, `qn p u' = UNW`,
`r_u = RU/2^q`, `qn p ι⁺ = ι`, `qn p b0 = b0ZW`, `qn p y0 = y0ZW`, and `qn` of the eight fields of `parOW` that BL
reads from its slots (`ε', λ', η', ρ', κ_c', ν'` at `pF`, `A_0, B_0` at `p`). The generic identities are v2.1's
(`qn_lam_gen`, ..., `qn_B0_gen`, Bit/Transfer/XBLSetupLink.lean); `ε'` and `η'` carry the factor `r_u`, so their
identities are written here.
-/

namespace AdversarialBco.UW.PrmW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN parO kDel)
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.Unified.PrmK
open AdversarialBco.UW.BLOW (lf0 lf1 l2O uOW ruOW iotaOW b0OW y0OW parOW n0O)

/-! ## Facts on the variable `e` -/

section Gen

variable {d n e : ℕ}

/-- `L_00 2^{-q} ≥ 1`: `ln N_0 ≥ 20 ln 2` and `lnErr_q N_0 ≤ 2^{-16}`. -/
theorem one_le_L00W_div (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ ((L00W d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q := by
  have hq1 : 1 ≤ (parK d n e).q := by have := qK_ge d n e; omega
  have hL0 := PieceA.lnQ_err (parK d n e).q (NeO d n 0) hq1 (NeO0_pos hd hn)
  have hee := Unified.BudK.lnErr_le d n e (NeO d n 0) hd hn size_N0_le
  have hu : Unified.BudK.tp d n e ≤ 1 := by
    rw [Unified.BudK.tp_eq, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hN20 : (2 : ℝ) ^ 20 ≤ (NeO d n 0 : ℝ) := by
    have h1 := (Unified.BudK.NeO_ge d n 0 hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 2 ^ 20 ≤ NeO d n 0 := le_trans (by nlinarith) h1
    exact_mod_cast h2
  have hlog : 20 * Real.log 2 ≤ Real.log (NeO d n 0) := by
    have h20 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [Real.log_le_log (by positivity) hN20]
  have h2 := Real.log_two_gt_d9
  obtain ⟨hA, -⟩ := abs_le.mp hL0
  have h : (1 : ℝ) ≤ (((lnQ (parK d n e).q (NeO d n 0) - lnErr (parK d n e).q (NeO d n 0) : ℚ)) : ℝ) := by
    push_cast
    have : (Unified.BudK.tp d n e) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  rw [L00W_div hd hn]
  exact_mod_cast h

theorem VW_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < VW d n e := by
  have h1 := RDZK_pos (n := n) (e := e) hd
  have h2 := LeNW_pos (e := e) hd hn
  have h3 := RUW_pos (e := e) hd hn
  have hd' : (0 : ℤ) < 14500 * d := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd
    omega
  unfold VW
  exact mul_pos (mul_pos (mul_pos hd' h1) (pow_pos h2 5)) h3

theorem UQQ_div (d n e : ℕ) :
    UNW d n e * QW d n e * QW d n e / PW d n e = UNW d n e * 2 ^ (2 * (parK d n e).q - (parK d n e).p) := by
  rw [mul_assoc, Q2_div_P, ← mul_assoc, mul_comm (UNW d n e) (PW d n e), mul_assoc]
  exact Int.mul_ediv_cancel_left _ PW_pos.ne'

theorem UNW_scale (d n e : ℕ) :
    ((UNW d n e : ℤ) : ℚ) / 2 ^ (parK d n e).p * 4 ^ (parK d n e).q =
      ((UNW d n e * QW d n e * QW d n e / PW d n e : ℤ) : ℚ) := by
  have hpq := p_le_q d n e
  rw [UQQ_div]
  push_cast
  have h4 : (4 : ℚ) ^ (parK d n e).q = 2 ^ (parK d n e).p * 2 ^ (2 * (parK d n e).q - (parK d n e).p) := by
    have he : 2 * (parK d n e).q = (parK d n e).p + (2 * (parK d n e).q - (parK d n e).p) := by omega
    calc (4 : ℚ) ^ (parK d n e).q = 2 ^ (2 * (parK d n e).q) := by rw [pow_mul]; norm_num
      _ = 2 ^ ((parK d n e).p + (2 * (parK d n e).q - (parK d n e).p)) := by rw [← he]
      _ = _ := pow_add _ _ _
  rw [h4]
  field_simp

end Gen

section Link

variable {d n : ℕ} {δ : ℚ}

/-! ## The logarithms and the scaling -/

theorem lf0_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    lf0 d n δ = ((L00W d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q :=
  (L00W_div hd hn).symm

theorem lf1_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    lf1 d n δ = ((L01W d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q :=
  (L01W_div hd hn).symm

theorem l2O_eq : l2O d n δ = ((L2W d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q :=
  L2W_div.symm

theorem one_le_lf0 (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ lf0 d n δ := by
  rw [lf0_eq hd hn]; exact one_le_L00W_div hd hn

theorem LeOW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    36 * lf0 d n δ = ((LeNW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  rw [lf0_eq hd hn]; unfold LeNW; push_cast; ring

theorem LhOW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    36 * lf1 d n δ = ((LhNW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  rw [lf1_eq hd hn]; unfold LhNW; push_cast; ring

theorem qn_uOW (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n (kDel δ)).p (uOW d n δ) = UNW d n (kDel δ) := by
  have hA := AW_pos (e := kDel δ) hd hn
  have hL : ((L00W d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (L00W_pos (e := kDel δ) hd hn).ne'
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hx : 1 + (kDel δ : ℚ) * l2O d n δ / (7 * d * lf0 d n δ) =
      ((AW d n (kDel δ) + kDel δ * L2W d n (kDel δ) : ℤ) : ℚ) / ((AW d n (kDel δ) : ℤ) : ℚ) := by
    rw [l2O_eq, lf0_eq hd hn]; unfold AW; push_cast; field_simp
  show qn _ (up (parK d n (kDel δ)).p (1 + (kDel δ : ℚ) * l2O d n δ / (7 * d * lf0 d n δ))) = _
  rw [hx, qn_up_div _ _ _ hA]
  rfl

theorem uOW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    uOW d n δ = ((UNW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).p := by
  rw [← qn_uOW hd hn]; exact up_eq_qn _ _

theorem ruOW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ruOW d n δ = ((RUW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  show sqrtDn (parK d n (kDel δ)).q (uOW d n δ) = _
  unfold sqrtDn RUW
  rw [uOW_eq hd hn, UNW_scale, ← Int.floor_toNat, Int.floor_intCast, Int.cast_natCast]

/-! ## `ι⁺`, `b0` and `y0` -/

theorem sqrtDn_n : sqrtDn (parK d n (kDel δ)).q (n : ℚ) =
    ((RNZK d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  rw [sqrtDn_nat, RNZK, Int.cast_natCast]

theorem sqrtDn_d : sqrtDn (parK d n (kDel δ)).q (d : ℚ) =
    ((RDZK d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  rw [sqrtDn_nat, RDZK, Int.cast_natCast]

theorem qn_iotaOW (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).p (iotaOW d n δ) = iotaZW d n (kDel δ) := by
  have hV := VW_pos (e := kDel δ) hd hn
  have hRD : ((RDZK d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (RDZK_pos (n := n) (e := kDel δ) hd).ne'
  have hLe : ((LeNW d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (LeNW_pos (e := kDel δ) hd hn).ne'
  have hRU : ((RUW d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (RUW_pos (e := kDel δ) hd hn).ne'
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hx : (sqrtDn (parK d n (kDel δ)).q (n : ℚ) + 1 / 2 ^ (parK d n (kDel δ)).q) /
      (14500 * d * sqrtDn (parK d n (kDel δ)).q (d : ℚ) * (36 * lf0 d n δ) ^ 5 * ruOW d n δ) =
      (((RNZK d n (kDel δ) + 1) * QW d n (kDel δ) ^ 6 : ℤ) : ℚ) / ((VW d n (kDel δ) : ℤ) : ℚ) := by
    rw [sqrtDn_n, sqrtDn_d, LeOW_eq hd hn, ruOW_eq hd hn]
    simp only [VW, QW, QZK]
    push_cast
    field_simp
  show qn _ (up (parK d n (kDel δ)).p ((sqrtDn (parK d n (kDel δ)).q (n : ℚ) + 1 / 2 ^ (parK d n (kDel δ)).q) /
      (14500 * d * sqrtDn (parK d n (kDel δ)).q (d : ℚ) * (36 * lf0 d n δ) ^ 5 * ruOW d n δ))) = _
  rw [hx, qn_up_div _ _ _ hV]
  rfl

theorem iotaOW_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    iotaOW d n δ = ((iotaZW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).p := by
  rw [← qn_iotaOW hd hn]; exact up_eq_qn _ _

theorem qn_b0OW (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n (kDel δ)).p (b0OW d n δ) = b0ZW d n (kDel δ) := by
  have hQ := QW_pos (d := d) (n := n) (e := kDel δ)
  have hx : 2 * (d : ℚ) + 2 + 36 * lf1 d n δ =
      ((((2 * d + 2) * QW d n (kDel δ) + LhNW d n (kDel δ)) : ℤ) : ℚ) / ((QW d n (kDel δ) : ℤ) : ℚ) := by
    rw [LhOW_eq hd hn]; simp only [QW, QZK]; push_cast; field_simp
  show qn _ (up (parK d n (kDel δ)).p (2 * (d : ℚ) + 2 + 36 * lf1 d n δ)) = _
  rw [hx, qn_up_div _ _ _ hQ]
  rfl

theorem sqrtUp_lf1 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    sqrtUp (parK d n (kDel δ)).q (12 * lf1 d n δ) =
      ((SUW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).q := by
  have hx : 12 * lf1 d n δ * 4 ^ (parK d n (kDel δ)).q = ((12 * L01W d n (kDel δ) * QW d n (kDel δ) : ℤ) : ℚ) := by
    rw [lf1_eq hd hn, show (4 : ℚ) ^ (parK d n (kDel δ)).q = 2 ^ (parK d n (kDel δ)).q * 2 ^ (parK d n (kDel δ)).q by
      rw [← mul_pow]; norm_num]
    simp only [QW, QZK]; push_cast
    field_simp
  unfold sqrtUp SUW
  rw [hx, ← Int.ceil_toNat, Int.ceil_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]

theorem qn_y0OW (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n (kDel δ)).p (y0OW d n δ) = y0ZW d n (kDel δ) := by
  have hQ := QW_pos (d := d) (n := n) (e := kDel δ)
  have hx : (10 + 18 * iotaOW d n δ + 10 * sqrtUp (parK d n (kDel δ)).q (12 * lf1 d n δ)) *
      2 ^ (parK d n (kDel δ)).p =
      (((10 * PW d n (kDel δ) + 18 * iotaZW d n (kDel δ)) * QW d n (kDel δ) +
        10 * SUW d n (kDel δ) * PW d n (kDel δ) : ℤ) : ℚ) / ((QW d n (kDel δ) : ℤ) : ℚ) := by
    rw [iotaOW_eq hd hn, sqrtUp_lf1 hd hn]
    simp only [QW, PW, QZK, PZK]
    push_cast
    field_simp
  show qn _ (up (parK d n (kDel δ)).p
    (10 + 18 * iotaOW d n δ + 10 * sqrtUp (parK d n (kDel δ)).q (12 * lf1 d n δ))) = _
  rw [qn_up, hx, ceil_div_int _ _ hQ]
  rfl

/-! ## The fields of `parOW` -/

theorem qn_parOW_eps (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).eps = epsZW d n (kDel δ) := by
  have hRN := RNZK_pos (d := d) (e := kDel δ) hn
  have hQ := QW_pos (d := d) (n := n) (e := kDel δ)
  have hV : 0 < QW d n (kDel δ) ^ 6 * RNZK d n (kDel δ) := mul_pos (pow_pos hQ 6) hRN
  have hRN' : ((RNZK d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hRN.ne'
  have hx : 14500 * (d : ℚ) * (sqrtDn (parK d n (kDel δ)).q (d : ℚ) + 1 / 2 ^ (parK d n (kDel δ)).q) *
      (36 * lf1 d n δ) ^ 5 * (ruOW d n δ + 1 / 2 ^ (parK d n (kDel δ)).q) /
      sqrtDn (parK d n (kDel δ)).q (n : ℚ) =
      ((14500 * d * (RDZK d n (kDel δ) + 1) * LhNW d n (kDel δ) ^ 5 * (RUW d n (kDel δ) + 1) : ℤ) : ℚ) /
        ((QW d n (kDel δ) ^ 6 * RNZK d n (kDel δ) : ℤ) : ℚ) := by
    rw [sqrtDn_n, sqrtDn_d, LhOW_eq hd hn, ruOW_eq hd hn]
    simp only [QW, QZK]
    push_cast
    field_simp
  rw [BLOW.parOW_eps]
  show qn _ (up (parK d n (kDel δ)).pF (14500 * (d : ℚ) *
    (sqrtDn (parK d n (kDel δ)).q (d : ℚ) + 1 / 2 ^ (parK d n (kDel δ)).q) *
    (36 * lf1 d n δ) ^ 5 * (ruOW d n δ + 1 / 2 ^ (parK d n (kDel δ)).q) / sqrtDn (parK d n (kDel δ)).q (n : ℚ))) = _
  rw [hx, qn_up_div _ _ _ hV]
  rfl

theorem qn_parOW_lam (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).lam = lamZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).pF (1 / (725 * (d : ℚ) * (36 * lf0 d n δ) ^ 2))) = _
  rw [LeOW_eq hd hn]
  exact qn_lam_gen d _ _ hd (LeNW d n (kDel δ)) (LeNW_pos hd hn).ne'

theorem qn_parOW_eta (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).eta = etaZW d n (kDel δ) := by
  have hRN := RNZK_pos (d := d) (e := kDel δ) hn
  have hLe := LeNW_pos (e := kDel δ) hd hn
  have hRU := RUW_pos (e := kDel δ) hd hn
  have hV : 0 < LeNW d n (kDel δ) * RNZK d n (kDel δ) * RUW d n (kDel δ) := mul_pos (mul_pos hLe hRN) hRU
  have hRN' : ((RNZK d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hRN.ne'
  have hLe' : ((LeNW d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hLe.ne'
  have hRU' : ((RUW d n (kDel δ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hRU.ne'
  have hx : sqrtDn (parK d n (kDel δ)).q (d : ℚ) /
      (36 * lf0 d n δ * sqrtDn (parK d n (kDel δ)).q (n : ℚ) * ruOW d n δ) =
      ((RDZK d n (kDel δ) * QW d n (kDel δ) * QW d n (kDel δ) : ℤ) : ℚ) /
        ((LeNW d n (kDel δ) * RNZK d n (kDel δ) * RUW d n (kDel δ) : ℤ) : ℚ) := by
    rw [sqrtDn_n, sqrtDn_d, LeOW_eq hd hn, ruOW_eq hd hn]
    simp only [QW, QZK]
    push_cast
    field_simp
  show qn _ (rnd (parK d n (kDel δ)).pF (sqrtDn (parK d n (kDel δ)).q (d : ℚ) /
    (36 * lf0 d n δ * sqrtDn (parK d n (kDel δ)).q (n : ℚ) * ruOW d n δ))) = _
  rw [hx, qn_rnd_div _ _ _ hV]
  rfl

theorem qn_parOW_sig (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).sig2 = sigZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).pF (1 / (8 * (36 * lf0 d n δ)))) = _
  rw [LeOW_eq hd hn]
  exact qn_sig_gen _ _ (LeNW d n (kDel δ)) (LeNW_pos hd hn)

theorem qn_parOW_rho (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).rho = rhoZW d n (kDel δ) := by
  show qn _ (dn (parK d n (kDel δ)).pF (1450 * (d : ℚ) ^ 2 * (36 * lf0 d n δ) ^ 3)) = _
  rw [LeOW_eq hd hn]
  exact qn_rho_gen d _ _ (LeNW d n (kDel δ))

theorem parOW_lam_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (parOW d n δ).lam = ((lamZW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).pF := by
  rw [← qn_parOW_lam hd hn]; exact rnd_eq_qn _ _

theorem parOW_eta_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (parOW d n δ).eta = ((etaZW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).pF := by
  rw [← qn_parOW_eta hd hn]; exact rnd_eq_qn _ _

theorem parOW_sig_eq (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (parOW d n δ).sig2 = ((sigZW d n (kDel δ) : ℤ) : ℚ) / 2 ^ (parK d n (kDel δ)).pF := by
  rw [← qn_parOW_sig hd hn]; exact rnd_eq_qn _ _

theorem qn_parOW_kapc (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).kapc = kapZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).pF ((parOW d n δ).eta * (parOW d n δ).lam /
    (4 * (1 - (parOW d n δ).lam) ^ 2))) = _
  rw [parOW_eta_eq hd hn, parOW_lam_eq hd hn]
  exact qn_kapc_gen _ (etaZW d n (kDel δ)) (lamZW d n (kDel δ))

/-- `λ' < 1`: `qn pF λ' < 2^pF`. -/
theorem lamZW_lt (hd : 1 ≤ d) (hn : 1 ≤ n) : lamZW d n (kDel δ) < 2 ^ (parK d n (kDel δ)).pF := by
  have hL : (36 : ℚ) ≤ 36 * lf0 d n δ := by have := one_le_lf0 (δ := δ) hd hn; linarith
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℚ) ≤ 2 ^ (parK d n (kDel δ)).pF := one_le_pow₀ (by norm_num)
  have h1 : (1 : ℚ) ≤ d * (36 * lf0 d n δ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hd' (one_le_pow₀ (by linarith))
  have hx : 1 / (725 * (d : ℚ) * (36 * lf0 d n δ) ^ 2) ≤ 1 / 725 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hx2 := mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℚ) ≤ 2 ^ (parK d n (kDel δ)).pF)
  rw [← qn_parOW_lam hd hn]
  show qn _ (rnd (parK d n (kDel δ)).pF (1 / (725 * (d : ℚ) * (36 * lf0 d n δ) ^ 2))) < _
  rw [qn_rnd, Int.floor_lt]
  push_cast
  linarith

theorem qn_parOW_nu (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).pF (parOW d n δ).nu = nuZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).pF (1 / (1 - (parOW d n δ).lam))) = _
  rw [parOW_lam_eq hd hn]
  exact qn_nu_gen _ (lamZW d n (kDel δ)) (lamZW_lt hd hn)

theorem qn_parOW_A0 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).p (parOW d n δ).A0 = A0ZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).p (sqrtUp (parK d n (kDel δ)).q (parOW d n δ).sig2)) = _
  rw [parOW_sig_eq hd hn]
  exact qn_A0_gen _ _ _ (sigZW d n (kDel δ))

theorem qn_parOW_B0 (hd : 1 ≤ d) (hn : 1 ≤ n) :
    qn (parK d n (kDel δ)).p (parOW d n δ).B0 = B0ZW d n (kDel δ) := by
  show qn _ (rnd (parK d n (kDel δ)).p (1 / sqrtUp (parK d n (kDel δ)).q (parOW d n δ).sig2)) = _
  rw [parOW_sig_eq hd hn]
  exact qn_B0_gen _ _ _ (sigZW d n (kDel δ))

end Link

end AdversarialBco.UW.PrmW
