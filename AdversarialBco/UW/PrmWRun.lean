/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.PrmWV

@[expose] public section

/-!
# PARAM-W on the machine: the run of the straight line

The static test of `parStW` (`parStW_chk`, the pairs `parEtW`, the inputs `d, n, N_e, k_δ` at most `2^G`), its units,
the side conditions of its non-expression steps at PARAM's magnitude `G = parGK d n e` (Unified/PrmKRun.lean) and the
run `XV.paramW`: from `d, n, N_e, k_δ` in the slots `0, 3, 7, 29`, slot `30 + k` ends holding `pvW d n e k`. The signs
it needs: `L_00 > 0` (from `lnQ_err` and `lnErr_le` at `N_0 ≤ N_e`, as PARAM's `LeN_posK`), `u' ≥ 1` at `2^p`, `r_u ≥ 1`
at `2^q`, `sig2' ≥ 0`.
-/

namespace AdversarialBco.UW.PrmW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN)
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.Unified.PrmK

/-- The pairs of the values of `parStW` at the inputs `d, n, N_e, k_δ ≤ 2^G`. -/
def parEtWL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 4), (0, 5), (0, 5), (0, 6), (0, 8), (0, 3), (0, 4), (0, 5), (0, 6), (0, 10),
   (0, 11), (0, 14), (0, 21), (1, 0), (1, 2), (1, 2), (1, 2), (1, 2), (1, 9), (1, 3), (1, 3), (1, 11), (1, 12),
   (1, 0), (1, 0), (1, 0), (3, 0), (3, 0), (3, 0), (3, 0), (1, 12), (1, 0), (2, 0), (7, 21), (7, 22), (7, 22),
   (7, 23), (1, 0), (8, 22), (2, 0), (2, 1), (2, 1), (9, 23), (8, 39), (9, 40), (9, 40), (0, 1), (2, 0), (2, 1),
   (2, 1), (2, 3), (2, 20), (10, 43), (11, 46), (13, 46), (13, 46), (9, 46), (9, 46), (62, 290), (6, 0), (62, 292),
   (63, 295), (19, 103), (25, 93), (9, 51), (30, 149), (45, 212), (19, 105), (11, 53), (11, 53), (11, 54), (12, 57),
   (11, 55), (10, 44), (10, 44), (10, 45), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1),
   (0, 1), (0, 1), (0, 1), (10, 49), (63, 301)]

/-- The pair of the value of step `j`. -/
def parEtW (j : ℕ) : ℕ × ℕ := parEtWL.getD j (0, 0)

/-- The largest pair over the steps. -/
def parTW : ℕ × ℕ := (63, 301)

/-- The pairs of the inputs `d, n, N_e, k_δ`. -/
def parInW (_ : ℕ) : ℕ × ℕ := (1, 0)

theorem parStW_chk : SL.chk 30 [0, 3, 7, 29] parInW parEtW parTW 44 parStW = true := by decide

theorem parUnitsW : SL.unitsP parEtW parStW = (564, 2472) := by decide

/-! ## The signs -/

section Bounds

variable {d n e : ℕ}

theorem NeO0_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ NeO d n 0 := NeK_pos hd hn

theorem NeO0_le (d n e : ℕ) : NeO d n 0 ≤ NeO d n e := by
  unfold NeO
  have : 2 ^ (17 + 0) ≤ 2 ^ (17 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  gcongr

theorem size_N0_le : (NeO d n 0).size ≤ (NeO d n e).size := Nat.size_le_size (NeO0_le d n e)

/-- `L_00 2^{-q} = lnQ q N_0 - lnErr q N_0`. -/
theorem L00W_div (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ((L00W d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q = lnQ (parK d n e).q (NeO d n 0) - lnErr (parK d n e).q (NeO d n 0) := by
  rw [lnQ_eq _ _ (NeO0_pos hd hn), L00W, L0W, E0W, lnErr]
  push_cast; field_simp

/-- `L_01 2^{-q} = lnQ q N_0 + lnErr q N_0`. -/
theorem L01W_div (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ((L01W d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q = lnQ (parK d n e).q (NeO d n 0) + lnErr (parK d n e).q (NeO d n 0) := by
  rw [lnQ_eq _ _ (NeO0_pos hd hn), L01W, L0W, E0W, lnErr]
  push_cast; field_simp

/-- `l_2 2^{-q} = lnQ q 2 + lnErr q 2`. -/
theorem L2W_div : ((L2W d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q = lnQ (parK d n e).q 2 + lnErr (parK d n e).q 2 := by
  have h2 : Nat.size 2 = 2 := by decide
  rw [lnQ_eq _ _ (by norm_num), L2W, lnErr, h2]
  push_cast; field_simp; ring

theorem L00W_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < L00W d n e := by
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
  have hpos : (0 : ℝ) < (((lnQ (parK d n e).q (NeO d n 0) - lnErr (parK d n e).q (NeO d n 0) : ℚ)) : ℝ) := by
    push_cast
    have : (Unified.BudK.tp d n e) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  have hpos' : (0 : ℚ) < ((L00W d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q := by
    rw [L00W_div hd hn]; exact_mod_cast hpos
  have h2q : (0 : ℚ) < 2 ^ (parK d n e).q := by positivity
  have : (0 : ℚ) < ((L00W d n e : ℤ) : ℚ) := by
    have := mul_pos hpos' h2q; rwa [div_mul_cancel₀ _ h2q.ne'] at this
  exact_mod_cast this

theorem E0W_nonneg : 0 ≤ E0W d n e := Int.natCast_nonneg _

theorem L01W_nonneg (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ L01W d n e := by
  have h1 := L00W_pos (e := e) hd hn
  have h2 := E0W_nonneg (d := d) (n := n) (e := e)
  unfold L00W at h1; unfold L01W; linarith

theorem L2W_nonneg : 0 ≤ L2W d n e := by
  have h1 := loI_nonneg (parK d n e).q 2 (by norm_num)
  have h2 : (0 : ℤ) ≤ ((2 * 2 * (4 * (parK d n e).q + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold L2W; linarith

theorem LeNW_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < LeNW d n e := by
  have := L00W_pos (e := e) hd hn; unfold LeNW; omega

theorem AW_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < AW d n e := by
  have h1 := L00W_pos (e := e) hd hn
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  unfold AW; positivity

theorem PW_pos : 0 < PW d n e := by unfold PW PZK; positivity
theorem QW_pos : 0 < QW d n e := by unfold QW QZK; positivity
theorem PFW_pos : 0 < PFW d n e := by unfold PFW PFZK; positivity

/-- `u' 2^p ≥ 2^p`. -/
theorem P_le_UNW (hd : 1 ≤ d) (hn : 1 ≤ n) : PW d n e ≤ UNW d n e := by
  have hA := AW_pos (e := e) hd hn
  have hl := L2W_nonneg (d := d) (n := n) (e := e)
  have hP := PW_pos (d := d) (n := n) (e := e)
  have he : (0 : ℤ) ≤ e := Int.natCast_nonneg e
  unfold UNW
  rw [Int.le_ediv_iff_mul_le hA]
  have : 0 ≤ (e : ℤ) * L2W d n e * PW d n e := mul_nonneg (mul_nonneg he hl) hP.le
  nlinarith

theorem UNW_nonneg (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ UNW d n e :=
  PW_pos.le.trans (P_le_UNW hd hn)

/-- `p ≤ 2q`: `⌊u' 4^q⌋ = u' 2^{2q-p}` exactly. -/
theorem p_le_q (d n e : ℕ) : (parK d n e).p ≤ (parK d n e).q := by simp only [parK, parN]; omega

theorem Q2_div_P (d n e : ℕ) : QW d n e * QW d n e = PW d n e * 2 ^ (2 * (parK d n e).q - (parK d n e).p) := by
  have h := p_le_q d n e
  unfold QW PW QZK PZK
  rw [← pow_add, ← pow_add, show (parK d n e).q + (parK d n e).q = (parK d n e).p + (2 * (parK d n e).q - (parK d n e).p) by omega]

/-- `r_u 2^q ≥ 2^q`. -/
theorem RUW_ge_Q (hd : 1 ≤ d) (hn : 1 ≤ n) : QW d n e ≤ RUW d n e := by
  have hP := PW_pos (d := d) (n := n) (e := e)
  have hQ := QW_pos (d := d) (n := n) (e := e)
  have hU := P_le_UNW (e := e) hd hn
  have hT : QW d n e * QW d n e ≤ UNW d n e * QW d n e * QW d n e / PW d n e := by
    rw [Int.le_ediv_iff_mul_le hP]
    have : PW d n e * (QW d n e * QW d n e) ≤ UNW d n e * (QW d n e * QW d n e) :=
      mul_le_mul_of_nonneg_right hU (mul_pos hQ hQ).le
    nlinarith
  unfold RUW
  have hT0 : 0 ≤ UNW d n e * QW d n e * QW d n e / PW d n e := le_trans (mul_pos hQ hQ).le hT
  have hQn : QW d n e = ((2 ^ (parK d n e).q : ℕ) : ℤ) := by unfold QW QZK; push_cast; rfl
  rw [hQn] at hT ⊢
  have hT' : 2 ^ (parK d n e).q * 2 ^ (parK d n e).q ≤ (UNW d n e * QW d n e * QW d n e / PW d n e).toNat := by
    have := Int.toNat_le_toNat hT
    rwa [show ((2 ^ (parK d n e).q : ℕ) : ℤ) * ((2 ^ (parK d n e).q : ℕ) : ℤ) =
      ((2 ^ (parK d n e).q * 2 ^ (parK d n e).q : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast] at this
  exact_mod_cast Nat.le_sqrt.2 hT'

theorem RUW_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < RUW d n e := QW_pos.trans_le (RUW_ge_Q hd hn)

theorem RDZK_pos (hd : 1 ≤ d) : 0 < RDZK d n e := by
  unfold RDZK
  have : 1 ≤ Nat.sqrt (d * 4 ^ (parK d n e).q) := by
    rw [Nat.le_sqrt]; have : 1 ≤ 4 ^ (parK d n e).q := Nat.one_le_pow _ _ (by norm_num); nlinarith
  exact_mod_cast this

theorem RNZK_pos (hn : 1 ≤ n) : 0 < RNZK d n e := by
  unfold RNZK
  have : 1 ≤ Nat.sqrt (n * 4 ^ (parK d n e).q) := by
    rw [Nat.le_sqrt]; have : 1 ≤ 4 ^ (parK d n e).q := Nat.one_le_pow _ _ (by norm_num); nlinarith
  exact_mod_cast this

theorem sigZW_nonneg (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ sigZW d n e := by
  have hL := LeNW_pos (e := e) hd hn
  have hQ := QW_pos (d := d) (n := n) (e := e)
  have hP := PFW_pos (d := d) (n := n) (e := e)
  unfold sigZW sigI
  apply Int.ediv_nonneg <;> nlinarith

/-- `k_δ ≤ size N_e ≤ G`. -/
theorem e_le_GK (hd : 1 ≤ d) (hn : 1 ≤ n) : e ≤ parGK d n e := by
  have h1 : 2 ^ (17 + e) ≤ NeO d n e := by
    unfold NeO
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h4 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    have : 2 ^ (17 + e) ≤ 15 * 2 ^ (17 + e) := by omega
    calc 2 ^ (17 + e) ≤ 15 * 2 ^ (17 + e) := this
      _ ≤ 15 * 2 ^ (17 + e) * d ^ 3 := Nat.le_mul_of_pos_right _ h3
      _ ≤ 15 * 2 ^ (17 + e) * d ^ 3 * n ^ 4 := Nat.le_mul_of_pos_right _ h4
  have h2 : 17 + e < (NeO d n e).size := Nat.lt_size.2 h1
  have := (parG_geK (d := d) (n := n) (e := e)).2.2.2.2
  omega

end Bounds

/-! ## The side conditions -/

section Sem

variable {d n e : ℕ}

/-- The side condition of step `k` of PARAM-W. -/
abbrev PSemW (d n e k : ℕ) : Prop := (parStW.getD k (.cst 0)).Sem (pvW d n e) (parGK d n e)

theorem mc_parW {vX : ℤ} (h0 : 0 ≤ vX) (h1 : vX ≤ 2 ^ (parK d n e).q) :
    0 ≤ pvW d n e 25 ∧ pvW d n e 25 ≤ ((parGK d n e : ℕ) : ℤ) ∧ pvW d n e 29 = 2 ^ (pvW d n e 25).toNat ∧ 0 ≤ vX ∧
      vX ≤ pvW d n e 29 :=
  mc_of_eq (pvW_25 (d := d) (n := n) (e := e)) (pvW_29 (d := d) (n := n) (e := e)) parG_geK.1 h0 h1

theorem semW_19 : PSemW d n e 19 := nn_of_eq (pvW_18 (d := d) (n := n) (e := e))
theorem semW_21 : PSemW d n e 21 := nn_of_eq (pvW_20 (d := d) (n := n) (e := e))
theorem semW_24 : PSemW d n e 24 := nn_of_eq (pvW_23 (d := d) (n := n) (e := e))
theorem semW_27 : PSemW d n e 27 := pw_of_eq (pvW_22 (d := d) (n := n) (e := e)) parG_geK.2.2.2.1
theorem semW_28 : PSemW d n e 28 := pw_of_eq (pvW_26 (d := d) (n := n) (e := e)) parG_geK.2.1
theorem semW_29 : PSemW d n e 29 := pw_of_eq (pvW_25 (d := d) (n := n) (e := e)) parG_geK.1
theorem semW_31 : PSemW d n e 31 := nn_of_eq (pvW_30 (d := d) (n := n) (e := e))
theorem semW_33 : PSemW d n e 33 := nn_of_eq (pvW_32 (d := d) (n := n) (e := e))
theorem semW_35 : PSemW d n e 35 := pw_of_eq (pvW_34 (d := d) (n := n) (e := e)) ((Nat.sub_le _ _).trans parG_geK.1)
theorem semW_36 : PSemW d n e 36 :=
  mc_parW ((by positivity : (0 : ℤ) ≤ 2 ^ ((parK d n e).q - 1)).trans_eq (pvW_35 (d := d) (n := n) (e := e)).symm)
    ((pvW_35 (d := d) (n := n) (e := e)).trans_le (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)))
theorem semW_39 : PSemW d n e 39 := nn_of_eq (pvW_38 (d := d) (n := n) (e := e))
theorem semW_41 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemW d n e 41 :=
  pw_of_eq (pvW_40 hd hn) ((Nat.sub_le _ _).trans (size_N0_le.trans parG_geK.2.2.2.2))
theorem semW_43 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemW d n e 43 :=
  mc_parW (nn_of_eq (pvW_42 hd hn)) ((pvW_42 hd hn).trans_le (by exact_mod_cast xN_le (parK d n e).q (NeO d n 0)))
theorem semW_51 : PSemW d n e 51 :=
  mc_parW (le_of_eq (pvW_50 (d := d) (n := n) (e := e)).symm)
    ((pvW_50 (d := d) (n := n) (e := e)).trans_le (by positivity))
theorem semW_59 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemW d n e 59 := by
  have hP := PW_pos (d := d) (n := n) (e := e)
  have hU := UNW_nonneg (e := e) hd hn
  have hQ := QW_pos (d := d) (n := n) (e := e)
  show 0 ≤ pvW d n e 58
  rw [pvW_58 hd hn]
  exact Int.ediv_nonneg (mul_nonneg (mul_nonneg hU hQ.le) hQ.le) hP.le
theorem semW_73 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemW d n e 73 := by
  have hP := PFW_pos (d := d) (n := n) (e := e)
  have : 0 ≤ sigZW d n e * QW d n e ^ 2 := mul_nonneg (sigZW_nonneg hd hn) (sq_nonneg _)
  show 0 ≤ pvW d n e 72
  rw [pvW_72 hd hn]
  exact Int.ediv_nonneg (by linarith) hP.le
theorem semW_78 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemW d n e 78 := by
  have hL := L01W_nonneg (e := e) hd hn
  have hQ := QW_pos (d := d) (n := n) (e := e)
  show 0 ≤ pvW d n e 77
  rw [pvW_77 hd hn]
  exact mul_nonneg (mul_nonneg (by norm_num) hL) hQ.le

theorem par_semW (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ k < parStW.length, (parStW.getD k (.cst 0)).Sem (pvW d n e) (parGK d n e) := by
  intro k hk
  rw [parStW_length] at hk
  interval_cases k
  all_goals try exact True.intro
  exacts [semW_19, semW_21, semW_24, semW_27, semW_28, semW_29, semW_31, semW_33, semW_35, semW_36, semW_39,
    semW_41 hd hn, semW_43 hd hn, semW_51, semW_59 hd hn, semW_73 hd hn, semW_78 hd hn]

end Sem

/-! ## The run -/

theorem parIn_okW {d n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ y ∈ [0, 3, 7, 29], |parIW d n e y| ≤ 2 ^ ev (parGK d n e) (parInW y) := by
  intro y hy
  have hev : ev (parGK d n e) (parInW y) = parGK d n e := by simp [ev, parInW]
  simp only [hev]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · show |(d : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast d_le_GK)
  · show |(n : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast n_le_GK hd hn)
  · show |(NeO d n e : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast NeO_le_GK)
  · show |(e : ℤ)| ≤ 2 ^ parGK d n e
    have h := (e_le_GK (e := e) hd hn).trans (Nat.lt_two_pow_self).le
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast h)

/-- **PARAM-W on the machine**: from `d` in slot `0`, `n` in slot `3`, `N_e = NeO d n e` in slot `7`, `e` in slot
`29`, `0, 1, 2, 4` in the slots `1, 26, 27, 28` and `1` in register `3`, the 94 steps of `parStW` leave `pvW d n e k`
in slot `30 + k`, within `564 G + 2472` units (`G = parGK d n e`); only the slots `30..123`, the slots from `128` and
the registers `8`, `9` change. -/
theorem XV.paramW {d e : ℕ} {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 10 ≤ L.NN) {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hT : 63 * parGK d n e + 301 < ℓ)
    (hTa : 63 * parGK d n e + 301 < 2 ^ ℓa) {σ : Env d} (h0 : σ.sc 0 = d) (h3 : σ.sc 3 = n) (hz : σ.sc 1 = 0)
    (hNe : σ.sc 7 = NeO d n e) (hk : σ.sc 29 = e) (h1 : σ.sc 26 = 1) (h2 : σ.sc 27 = 2) (h4 : σ.sc 28 = 4)
    (hn1 : σ.nat 3 = 1) :
    XRunsB L X ℓa ℓ (SL.code L parC parStW) σ (564 * parGK d n e + 2472) (fun σ' =>
      (∀ k < 94, σ'.sc (30 + k) = pvW d n e k) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => (30 ≤ y ∧ y < 124) ∨ 128 ≤ y) (fun j => j = 8 ∨ j = 9) σ σ') := by
  have hin : ∀ y ∈ [0, 3, 7, 29], σ.sc y = ((parIW d n e y : ℤ) : ℝ) := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [h0]; simp [parIW]
    · rw [h3]; simp [parIW]
    · rw [hNe]; simp [parIW]
    · rw [hk]; simp [parIW]
  have h := XV.sl (X := X) hL (parC_okK hNS hNN) (ι := parIW d n e) parStW_chk (par_semW hd hn)
    (by rw [parStW_length]; decide) hT hTa (parIn_okW hd hn) hin hz h1 h2 h4 hn1
  refine XV.mono h (by rw [parUnitsW]; simp [ev]) fun σ' ⟨hA, hD, hF⟩ => ⟨fun k hk => hA k (by
    rw [parStW_length]; exact hk), hD, hF.mono (fun y hy => ?_) (fun j hj => hj)⟩
  simp only [parC, parStW_length] at hy
  omega

end AdversarialBco.UW.PrmW
