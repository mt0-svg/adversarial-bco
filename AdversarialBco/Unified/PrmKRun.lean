/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PrmKV

@[expose] public section

/-!
# PARAM of BL-O on the machine: the run of the straight line at `k_δ`

Bit/Transfer/XBLSetupParRun.lean at `parK d n e`: the side conditions of the non-expression steps of
`parStK` hold at the magnitude `parGK d n e = q + pF + 2 gsm_prec B`; v2.1's table of pairs `parEt` still passes the
static test with the input `N_e ≤ 2^G` in slot `4` (`parStK_chk`); `XV.paramK` runs PARAM from `d`, `n`, `N_e` and
slot `30 + k` ends holding `pvK d n e k`. The positivity of `Le'` comes from `lnQ_err` and `lnErr_le` at
`parK` (Unified/BudEnc.lean).
-/

namespace AdversarialBco.Unified.PrmK

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (NeO parN)
open AdversarialBco.Unified.BudK (parK)

/-- The magnitude of PARAM's pairs at `k_δ = e`. -/
def parGK (d n e : ℕ) : ℕ := (parK d n e).q + (parK d n e).pF + 2 * gsm_prec (parK d n e).B

theorem parStK_chk : SL.chk 30 [0, 3, 4] parIn parEt parT 44 parStK = true := by decide

theorem parUnitsK : SL.unitsP parEt parStK = (696, 3177) := by decide

section Bounds

variable {d n e : ℕ}

theorem size_Ne_le_pFK : (NeO d n e).size ≤ (parK d n e).pF := by simp only [parK, parN]; omega

theorem size_d_le_pFK : d.size ≤ (parK d n e).pF := by simp only [parK, parN]; omega

theorem n_le_NeK (hd : 1 ≤ d) (_hn : 1 ≤ n) : n ≤ NeO d n e := by
  unfold NeO
  have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h4 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  exact h4.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) h3))

theorem d_le_GK : d ≤ 2 ^ parGK d n e :=
  (Nat.lt_size_self d).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold parGK; have := size_d_le_pFK (d := d) (n := n) (e := e); omega))

theorem n_le_GK (hd : 1 ≤ d) (hn : 1 ≤ n) : n ≤ 2 ^ parGK d n e := by
  have h1 : n.size ≤ (NeO d n e).size := Nat.size_le_size (n_le_NeK hd hn)
  exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold parGK; have := size_Ne_le_pFK (d := d) (n := n) (e := e); omega))

theorem NeO_le_GK : NeO d n e ≤ 2 ^ parGK d n e :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold parGK; have := size_Ne_le_pFK (d := d) (n := n) (e := e); omega))

/-- `Le' 2^q = LeNK`. -/
theorem LeN_divK (hd : 1 ≤ d) (hn : 1 ≤ n) : ((LeNK d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q = (parK d n e).Le := by
  rw [BudK.parK_Le, BudK.L0, BudK.ee, lnQ_eq _ _ (NeK_pos hd hn), LeNK, L0NK, ENK, lnErr]
  push_cast; field_simp

theorem LeN_posK (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < LeNK d n e := by
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
  have hpos : (0 : ℝ) < (((parK d n e).Le : ℚ) : ℝ) := by
    rw [hLe]
    have : (BudK.tp d n e) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  have hpos' : (0 : ℚ) < ((LeNK d n e : ℤ) : ℚ) / 2 ^ (parK d n e).q := by rw [LeN_divK hd hn]; exact_mod_cast hpos
  have h2q : (0 : ℚ) < 2 ^ (parK d n e).q := by positivity
  have : (0 : ℚ) < ((LeNK d n e : ℤ) : ℚ) := by
    have := mul_pos hpos' h2q; rwa [div_mul_cancel₀ _ h2q.ne'] at this
  exact_mod_cast this

theorem sigZ_nonnegK (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ sigZK d n e := by
  have hL := LeN_posK (e := e) hd hn
  have hQ : 0 < QZK d n e := by unfold QZK; positivity
  have hP : 0 < PFZK d n e := by unfold PFZK; positivity
  unfold sigZK sigI
  apply Int.ediv_nonneg <;> nlinarith

end Bounds

/-! ## The side conditions -/

section Sem

variable {d n e : ℕ}

/-- The side condition of step `k` of PARAM. -/
abbrev PSemK (d n e k : ℕ) : Prop := (parStK.getD k (.cst 0)).Sem (pvK d n e) (parGK d n e)

theorem parG_geK : (parK d n e).q ≤ parGK d n e ∧ (parK d n e).pF ≤ parGK d n e ∧ 2 * gsm_prec (parK d n e).B ≤ parGK d n e ∧
    (parK d n e).p ≤ parGK d n e ∧ (NeO d n e).size ≤ parGK d n e := by
  have hG := size_Ne_le_pFK (d := d) (n := n) (e := e)
  have hpq : (parK d n e).p ≤ (parK d n e).q := by simp only [parK, parN]; omega
  unfold parGK; omega

theorem mc_parK {vX : ℤ} (h0 : 0 ≤ vX) (h1 : vX ≤ 2 ^ (parK d n e).q) :
    0 ≤ pvK d n e 26 ∧ pvK d n e 26 ≤ ((parGK d n e : ℕ) : ℤ) ∧ pvK d n e 37 = 2 ^ (pvK d n e 26).toNat ∧ 0 ≤ vX ∧
      vX ≤ pvK d n e 37 :=
  mc_of_eq (pvK_26 (d := d) (n := n) (e := e)) (pvK_37 (d := d) (n := n) (e := e)) parG_geK.1 h0 h1

theorem semK_20 : PSemK d n e 20 := nn_of_eq (pvK_19 (d := d) (n := n) (e := e))
theorem semK_22 : PSemK d n e 22 := nn_of_eq (pvK_21 (d := d) (n := n) (e := e))
theorem semK_25 : PSemK d n e 25 := nn_of_eq (pvK_24 (d := d) (n := n) (e := e))
theorem semK_29 : PSemK d n e 29 := nn_of_eq (pvK_28 (d := d) (n := n) (e := e))
theorem semK_32 : PSemK d n e 32 := nn_of_eq (pvK_31 (d := d) (n := n) (e := e))
theorem semK_34 : PSemK d n e 34 := pw_of_eq (pvK_33 (d := d) (n := n) (e := e)) parG_geK.2.2.1
theorem semK_35 : PSemK d n e 35 := pw_of_eq (pvK_23 (d := d) (n := n) (e := e)) parG_geK.2.2.2.1
theorem semK_36 : PSemK d n e 36 := pw_of_eq (pvK_27 (d := d) (n := n) (e := e)) parG_geK.2.1
theorem semK_37 : PSemK d n e 37 := pw_of_eq (pvK_26 (d := d) (n := n) (e := e)) parG_geK.1
theorem semK_39 : PSemK d n e 39 := pw_of_eq (pvK_38 (d := d) (n := n) (e := e))
  ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans parG_geK.2.2.2.1)))
theorem semK_42 : PSemK d n e 42 := nn_of_eq (pvK_41 (d := d) (n := n) (e := e))
theorem semK_44 : PSemK d n e 44 := nn_of_eq (pvK_43 (d := d) (n := n) (e := e))
theorem semK_46 : PSemK d n e 46 := pw_of_eq (pvK_45 (d := d) (n := n) (e := e)) ((Nat.sub_le _ _).trans parG_geK.1)
theorem semK_47 : PSemK d n e 47 :=
  mc_parK ((by positivity : (0 : ℤ) ≤ 2 ^ ((parK d n e).q - 1)).trans_eq (pvK_46 (d := d) (n := n) (e := e)).symm)
    ((pvK_46 (d := d) (n := n) (e := e)).trans_le (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)))
theorem semK_49 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemK d n e 49 :=
  pw_of_eq (pvK_48 hd hn) ((Nat.sub_le _ _).trans parG_geK.2.2.2.2)
theorem semK_51 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemK d n e 51 :=
  mc_parK (nn_of_eq (pvK_50 hd hn)) ((pvK_50 hd hn).trans_le (by exact_mod_cast xN_le (parK d n e).q (NeO d n e)))
theorem semK_57 : PSemK d n e 57 := nn_of_eq (pvK_56 (d := d) (n := n) (e := e))
theorem semK_59 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemK d n e 59 :=
  pw_of_eq (pvK_58 (d := d) (n := n) (e := e))
    ((Nat.sub_le _ _).trans ((BudK.size_facts d n e hd hn).2.2.2.2.2.2.trans parG_geK.2.2.2.2))
theorem semK_61 : PSemK d n e 61 :=
  mc_parK (nn_of_eq (pvK_60 (d := d) (n := n) (e := e)))
    ((pvK_60 (d := d) (n := n) (e := e)).trans_le (by exact_mod_cast xN_le (parK d n e).q (2 * d + 2)))

theorem semK_78 : PSemK d n e 78 := by
  have h1 := loI_nonneg (parK d n e).q (2 * d + 2) (by omega)
  have h2 : 0 ≤ E1NK d n e := Int.natCast_nonneg _
  have hQ : 0 ≤ QZK d n e := by unfold QZK; positivity
  exact (mul_nonneg (by unfold L1NK; linarith) hQ).trans_eq (pvK_77 (d := d) (n := n) (e := e)).symm

theorem semK_83 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemK d n e 83 := by
  have hL := LeN_posK (e := e) hd hn
  have : 0 ≤ (NeO d n e : ℤ) * QZK d n e ^ 3 := mul_nonneg (Int.natCast_nonneg _) (by unfold QZK; positivity)
  exact (Int.ediv_nonneg (by linarith) hL.le).trans_eq (pvK_82 hd hn).symm

theorem semK_87 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSemK d n e 87 := by
  have hP : 0 < PFZK d n e := by unfold PFZK; positivity
  have : 0 ≤ sigZK d n e * QZK d n e ^ 2 := mul_nonneg (sigZ_nonnegK hd hn) (sq_nonneg _)
  exact (Int.ediv_nonneg (by linarith) hP.le).trans_eq (pvK_86 hd hn).symm

end Sem

theorem par_semK {d n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ k < parStK.length, (parStK.getD k (.cst 0)).Sem (pvK d n e) (parGK d n e) := by
  intro k hk
  rw [parStK_length] at hk
  interval_cases k
  all_goals try exact True.intro
  exacts [semK_20, semK_22, semK_25, semK_29, semK_32, semK_34, semK_35, semK_36, semK_37, semK_39, semK_42, semK_44, semK_46,
    semK_47, semK_49 hd hn, semK_51 hd hn, semK_57, semK_59 hd hn, semK_61, semK_78, semK_83 hd hn, semK_87 hd hn]

/-! ## The run -/

theorem parC_okK {L : Layout} (hNS : 172 ≤ L.NS) (hNN : 10 ≤ L.NN) : parC.OK L 44 where
  hS := by show 128 + 44 ≤ L.NS; omega
  hr1 := by show 8 < L.NN; omega
  hr2 := by show 9 < L.NN; omega
  hn1 := by show 3 < L.NN; omega
  r12 := by decide
  r1n := by decide
  r2n := by decide
  zb := by decide
  ob := by decide
  tb := by decide
  fb := by decide
  nd := by decide
  bt := by decide

theorem parIn_okK {d n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ y ∈ [0, 3, 4], |parIK d n e y| ≤ 2 ^ ev (parGK d n e) (parIn y) := by
  intro y hy
  have hev : ev (parGK d n e) (parIn y) = parGK d n e := by simp [ev, parIn]
  simp only [hev]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · show |(d : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast d_le_GK)
  · show |(n : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast n_le_GK hd hn)
  · show |(NeO d n e : ℤ)| ≤ 2 ^ parGK d n e
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast NeO_le_GK)

/-- **PARAM at `k_δ = e` on the machine**: from `d` in slot `0`, `n` in slot `3`, `N_e = NeO d n e` in slot `4`, `0, 1, 2, 4` in the slots `1, 26, 27, 28` and `1`
in register `3`, the 93 steps of `parStK` leave `pvK d n e k` in slot `30 + k`, within `696 G + 3177` units
(`G = parGK d n e`); only the slots `30..122`, the slots from `128` and the registers `8`, `9` change. -/
theorem XV.paramK {d e : ℕ} {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 10 ≤ L.NN) {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hT : 75 * parGK d n e + 343 < ℓ)
    (hTa : 75 * parGK d n e + 343 < 2 ^ ℓa) {σ : Env d} (h0 : σ.sc 0 = d) (h3 : σ.sc 3 = n) (hz : σ.sc 1 = 0)
    (hNe : σ.sc 4 = NeO d n e) (h1 : σ.sc 26 = 1) (h2 : σ.sc 27 = 2) (h4 : σ.sc 28 = 4) (hn1 : σ.nat 3 = 1) :
    XRunsB L X ℓa ℓ (SL.code L parC parStK) σ (696 * parGK d n e + 3177) (fun σ' =>
      (∀ k < 93, σ'.sc (30 + k) = pvK d n e k) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => (30 ≤ y ∧ y < 123) ∨ 128 ≤ y) (fun j => j = 8 ∨ j = 9) σ σ') := by
  have hin : ∀ y ∈ [0, 3, 4], σ.sc y = ((parIK d n e y : ℤ) : ℝ) := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · rw [h0]; simp [parIK]
    · rw [h3]; simp [parIK]
    · rw [hNe]; simp [parIK]
  have h := XV.sl (X := X) hL (parC_okK hNS hNN) (ι := parIK d n e) parStK_chk (par_semK hd hn)
    (by rw [parStK_length]; decide) hT hTa (parIn_okK hd hn) hin hz h1 h2 h4 hn1
  refine XV.mono h (by rw [parUnitsK]; simp [ev]) fun σ' ⟨hA, hD, hF⟩ => ⟨fun k hk => hA k (by
    rw [parStK_length]; exact hk), hD, hF.mono (fun y hy => ?_) (fun j hj => hj)⟩
  simp only [parC, parStK_length] at hy
  omega

end AdversarialBco.Unified.PrmK
