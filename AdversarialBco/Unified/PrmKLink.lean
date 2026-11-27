/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PrmKRun

@[expose] public section

/-!
# PARAM of BL-O on the machine: the values of the line are the numerators of `BLInv`

The second part of Bit/Transfer/XBLSetupLink.lean at `parK d n e`: `qn` of every rounded field of
`parK d n e` is the integer formula the line computes (`qn_parK_eps`, ..., `RintK_eq`), from v2.1's generic identities
(`qn_lam_gen`, ...) and the field equations of `parK` (Unified/BudEnc.lean).
-/

namespace AdversarialBco.Unified.PrmK

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN)
open AdversarialBco.Unified.BudK (parK)

theorem parK_Lam (d n e : ℕ) : (parK d n e).Lam = d * NeO d n e := rfl

theorem parK_Rint (d n e : ℕ) : (parK d n e).Rint = ⌈(parK d n e).R⌉₊ := rfl

theorem parK_eHat (d n e : ℕ) :
    (parK d n e).eHat = 1 / 2 ^ ((parK d n e).p - 3 * (NeO d n e).size - 6 * d.size - 64) := rfl

theorem parK_eHat_inv (d n e : ℕ) :
    (parK d n e).eHat⁻¹ = 2 ^ ((parK d n e).p - 3 * (NeO d n e).size - 6 * d.size - 64) := by
  rw [parK_eHat, one_div, inv_inv]

section Par

variable {d n e : ℕ}

theorem parK_Le_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (parK d n e).Le = (LeNK d n e : ℚ) / 2 ^ (parK d n e).q :=
  (LeN_divK hd hn).symm

theorem parK_Lh (hd : 1 ≤ d) (hn : 1 ≤ n) :
    36 * (BudK.L0 d n e + BudK.ee d n e) = (LhNK d n e : ℚ) / 2 ^ (parK d n e).q := by
  rw [BudK.L0, BudK.ee, lnQ_eq _ _ (NeK_pos hd hn), LhNK, L0NK, ENK, lnErr]
  push_cast; field_simp

theorem LeK_ge_one (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ (parK d n e).Le := by
  have hq1 : 1 ≤ (parK d n e).q := by have := qK_ge d n e; omega
  have hL0 := PieceA.lnQ_err (parK d n e).q (NeO d n e) hq1 (NeK_pos hd hn)
  have hee := BudK.lnErr_le d n e (NeO d n e) hd hn le_rfl
  have hu : BudK.tp d n e ≤ 1 := by
    rw [BudK.tp_eq, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hN20 : (2 : ℝ) ^ 20 ≤ (NeO d n e : ℝ) := by
    have h1 := (BudK.NeO_ge d n e hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 2 ^ 20 ≤ NeO d n e := le_trans (by nlinarith) h1
    exact_mod_cast h2
  have hlog : 20 * Real.log 2 ≤ Real.log (NeO d n e) := by
    have h20 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [Real.log_le_log (by positivity) hN20]
  have h2 := Real.log_two_gt_d9
  obtain ⟨hA, -⟩ := abs_le.mp hL0
  have hLe : (((parK d n e).Le : ℚ) : ℝ) = 36 * (((lnQ (parK d n e).q (NeO d n e) : ℚ) : ℝ) -
      ((lnErr (parK d n e).q (NeO d n e) : ℚ) : ℝ)) := by
    rw [BudK.parK_Le, BudK.L0, BudK.ee]; push_cast; ring
  have hpos : (1 : ℝ) ≤ (((parK d n e).Le : ℚ) : ℝ) := by
    rw [hLe]
    have : (BudK.tp d n e) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  exact_mod_cast hpos

theorem qn_parK_eps (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).eps = epsZK d n e := by
  rw [BudK.parK_eps, parK_Lh hd hn]; exact qn_eps_gen d n _ _ hn (LhNK d n e)

theorem qn_parK_lam (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).lam = lamZK d n e := by
  rw [BudK.parK_lam, parK_Le_eq hd hn]
  exact qn_lam_gen d _ _ hd (LeNK d n e) (LeN_posK hd hn).ne'

theorem qn_parK_eta (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).eta = etaZK d n e := by
  rw [BudK.parK_eta, parK_Le_eq hd hn]
  exact qn_eta_gen d n _ _ hn (LeNK d n e) (LeN_posK hd hn)

theorem qn_parK_sig (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).sig2 = sigZK d n e := by
  rw [BudK.parK_sig2, parK_Le_eq hd hn]
  exact qn_sig_gen _ _ (LeNK d n e) (LeN_posK hd hn)

theorem qn_parK_rho (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).rho = rhoZK d n e := by
  rw [BudK.parK_rho, parK_Le_eq hd hn]
  exact qn_rho_gen d _ _ (LeNK d n e)

theorem parK_lam_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (parK d n e).lam = (lamZK d n e : ℚ) / 2 ^ (parK d n e).pF := by
  rw [← qn_parK_lam hd hn, BudK.parK_lam]; exact rnd_eq_qn _ _

theorem parK_eta_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (parK d n e).eta = (etaZK d n e : ℚ) / 2 ^ (parK d n e).pF := by
  rw [← qn_parK_eta hd hn, BudK.parK_eta]; exact rnd_eq_qn _ _

theorem parK_sig_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (parK d n e).sig2 = (sigZK d n e : ℚ) / 2 ^ (parK d n e).pF := by
  rw [← qn_parK_sig hd hn, BudK.parK_sig2]; exact rnd_eq_qn _ _

theorem qn_parK_kapc (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).kapc = kapZK d n e := by
  rw [BudK.parK_kapc, parK_eta_eq hd hn, parK_lam_eq hd hn]
  exact qn_kapc_gen _ (etaZK d n e) (lamZK d n e)

/-- `λ' < 1`: `qn pF λ' < 2^pF`. -/
theorem lamZK_lt (hd : 1 ≤ d) (hn : 1 ≤ n) : lamZK d n e < 2 ^ (parK d n e).pF := by
  have hL := LeK_ge_one (e := e) hd hn
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℚ) ≤ 2 ^ (parK d n e).pF := one_le_pow₀ (by norm_num)
  have h1 : (1 : ℚ) ≤ d * (parK d n e).Le ^ 2 := one_le_mul_of_one_le_of_one_le hd' (one_le_pow₀ hL)
  have hx : 1 / (725 * (d : ℚ) * (parK d n e).Le ^ 2) ≤ 1 / 725 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hx2 := mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℚ) ≤ 2 ^ (parK d n e).pF)
  rw [← qn_parK_lam hd hn, BudK.parK_lam, qn_rnd, Int.floor_lt]
  push_cast
  linarith

theorem qn_parK_nu (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).nu = nuZK d n e := by
  rw [BudK.parK_nu, parK_lam_eq hd hn]
  exact qn_nu_gen _ (lamZK d n e) (lamZK_lt hd hn)

theorem qn_parK_A0 (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).p (parK d n e).A0 = A0ZK d n e := by
  rw [BudK.parK_A0, parK_sig_eq hd hn]
  exact qn_A0_gen _ _ _ (sigZK d n e)


theorem l1QK_eq : BudK.l1Q d n e = ((L1NK d n e + E1NK d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q := by
  rw [BudK.l1Q, lnQ_eq _ _ (by omega : 1 ≤ 2 * d + 2), L1NK, E1NK, lnErr]
  push_cast; field_simp

theorem qn_parK_R : qn (parK d n e).pF (parK d n e).R = RZK d n e := by
  rw [BudK.parK_R, l1QK_eq]
  unfold RZK RSZK PFZK QZK
  exact qn_R_gen d _ _ _

theorem parK_R_eq : (parK d n e).R = (RZK d n e : ℚ) / 2 ^ (parK d n e).pF := by
  rw [← qn_parK_R, BudK.parK_R]; exact up_eq_qn _ _

theorem RZK_nonneg : 0 ≤ RZK d n e := RI_nonneg d _ _ _

theorem qn_parK_sb : qn (parK d n e).pF (parK d n e).sb = sbZK d n e := by
  rw [BudK.parK_sb, parK_R_eq]
  unfold sbZK PFZK
  exact qn_sb_gen _ _ _ RZK_nonneg

theorem qn_parK_W (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).pF (parK d n e).W = WZK d n e := by
  rw [BudK.parK_W, parK_R_eq, parK_Le_eq hd hn]
  unfold WZK SWZK PFZK QZK
  exact qn_W_gen d _ _ _ (RZK d n e) (LeNK d n e) (LeN_posK hd hn)

theorem qn_parK_B0 (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (parK d n e).p (parK d n e).B0 = B0ZK d n e := by
  rw [BudK.parK_B0, parK_sig_eq hd hn]
  unfold B0ZK S1ZK PZK QZK PFZK
  exact qn_B0_gen _ _ _ (sigZK d n e)

theorem RintK_eq : ((parK d n e).Rint : ℤ) = RintZK d n e := by
  rw [parK_Rint, parK_R_eq]
  unfold RintZK rintI PFZK
  exact rint_gen _ _ RZK_nonneg
end Par
