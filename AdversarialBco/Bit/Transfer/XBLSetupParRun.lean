/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupParV

@[expose] public section

/-!
# BL's setup on the machine: the run of PARAM

The side conditions of the 22 steps of `parSt` that are not expressions (integer roots, powers, logarithms, Mercator
sums) hold at the magnitude `parG d n = q + pF + 2 gsm_prec B`; with them `XV.sl` runs PARAM from `d` (slot `0`) and
`n` (slot `3`), and slot `30 + k` ends holding `pv d n k`. The positivity of `Le'` (`LeN d n > 0`) comes from the
error bound of `LOGINT` (`PieceA.lnQ_err`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-- The magnitude of PARAM's pairs: every value of step `k` is at most `2^(a G + b)`, `(a, b) = parEt k`. -/
def parG (d n : ℕ) : ℕ := (par d n).q + (par d n).pF + 2 * gsm_prec (par d n).B

theorem parUnits : SL.unitsP parEt parSt = (696, 3191) := by decide

/-! ## `LOGINT` on the integers -/

theorem lnQ_eq (q N : ℕ) (hN : 1 ≤ N) : lnQ q N = (loI q N : ℚ) / 2 ^ q := by
  have hgsm0 : ∀ i, gsm_powq q 0 i = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => unfold gsm_powq; rw [ih]; simp
  have hmercq0 : gsm_mercq q 0 q = 0 := by
    unfold gsm_mercq
    simp [hgsm0]
  have hlog1 : Nat.log 2 1 = 0 := by
    simp
  have hNpos : 0 < N := by omega
  have hpos_size : 0 < N.size := by
    rw [Nat.size_pos]
    exact hNpos
  have hsize_log_nat : N.size = Nat.log 2 N + 1 := by
    have hle : 2 ^ (N.size - 1) ≤ N := by
      have hlt : N.size - 1 < N.size := by omega
      rw [← Nat.lt_size]
      exact hlt
    have hlt : N < 2 ^ N.size := Nat.lt_size_self N
    have hsize_eq : N.size = (N.size - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ N.size)).symm
    rw [hsize_eq] at hlt
    have hlog := Nat.log_eq_of_pow_le_of_lt_pow hle hlt
    omega
  have hlog_eq : Nat.log 2 N = N.size - 1 := by omega
  unfold lnQ loI gsm_LLq
  push_cast
  have h2q : (2 ^ q : ℚ) ≠ 0 := by positivity
  field_simp [h2q]
  -- Simplify N - 1 + 1 = N
  have hNsub_nat : N - 1 + 1 = N := by omega
  rw [hNsub_nat]
  -- Simplify Nat.log 2 N = N.size - 1
  rw [hlog_eq]
  -- Now simplify using hlog1 and hmercq0
  simp [hlog1, hmercq0]
  have hsub : (N.size : ℚ) - ((N.size - 1 : ℕ) : ℚ) = 1 := by
    have h : 1 ≤ N.size := by omega
    push_cast [h]
    ring
  rw [hsub, mul_one]

theorem loI_nonneg (q N : ℕ) (hN : 1 ≤ N) : 0 ≤ loI q N := by
  have hs : (1 : ℤ) ≤ N.size := by exact_mod_cast Nat.size_pos.2 hN
  have hΛ := Int.natCast_nonneg (gsm_mercq q (2 ^ (q - 1)) q)
  have hS := Int.natCast_nonneg (gsm_mercq q ((N - 2 ^ (N.size - 1)) * 2 ^ q / N) q)
  have hm : max ((gsm_mercq q (2 ^ (q - 1)) q : ℤ) - gsm_mercq q ((N - 2 ^ (N.size - 1)) * 2 ^ q / N) q) 0 ≤
      (gsm_mercq q (2 ^ (q - 1)) q : ℤ) := max_le (by linarith) hΛ
  have h1 := mul_le_mul_of_nonneg_right hs hΛ
  unfold loI
  linarith

section Bounds

variable {d n : ℕ}

theorem size_Ne_le_pF : (BLP.Ne d n).size ≤ (par d n).pF := by simp only [par]; omega

theorem size_d_le_pF : d.size ≤ (par d n).pF := by simp only [par]; omega

theorem n_le_Ne (hd : 1 ≤ d) (hn : 1 ≤ n) : n ≤ BLP.Ne d n := by
  unfold BLP.Ne
  have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h4 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  nlinarith

theorem d_le_G : d ≤ 2 ^ parG d n :=
  (Nat.lt_size_self d).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold parG; have := size_d_le_pF (d := d) (n := n); omega))

theorem n_le_G (hd : 1 ≤ d) (hn : 1 ≤ n) : n ≤ 2 ^ parG d n := by
  have h1 : n.size ≤ (BLP.Ne d n).size := Nat.size_le_size (n_le_Ne hd hn)
  exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold parG; have := size_Ne_le_pF (d := d) (n := n); omega))

/-- `Le' 2^q = LeN`. -/
theorem LeN_div (hd : 1 ≤ d) (hn : 1 ≤ n) : ((LeN d n : ℤ) : ℚ) / 2 ^ (par d n).q = (par d n).Le := by
  rw [PieceA.par_Le, PieceA.L0, PieceA.ee, lnQ_eq _ _ (Ne_pos hd hn), LeN, L0N, EN, lnErr]
  push_cast; field_simp

theorem LeN_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < LeN d n := by
  have hq1 : 1 ≤ (par d n).q := by have := q_ge d n; omega
  have hL0 := PieceA.lnQ_err (par d n).q (BLP.Ne d n) hq1 (Ne_pos hd hn)
  have hee := PieceA.lnErr_le d n (BLP.Ne d n) hd hn le_rfl
  have hu : PieceA.u d n ≤ 1 := by
    unfold PieceA.u; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hN20 : (2 : ℝ) ^ 20 ≤ (BLP.Ne d n : ℝ) := by
    have h1 := (PieceA.NeN_ge d n hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 2 ^ 20 ≤ BLP.Ne d n := le_trans (by nlinarith) h1
    exact_mod_cast h2
  have hlog : 20 * Real.log 2 ≤ Real.log (BLP.Ne d n) := by
    have h20 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [Real.log_le_log (by positivity) hN20]
  have h2 := Real.log_two_gt_d9
  obtain ⟨hA, -⟩ := abs_le.mp hL0
  have hLe : (((par d n).Le : ℚ) : ℝ) = 36 * (((lnQ (par d n).q (BLP.Ne d n) : ℚ) : ℝ) -
      ((lnErr (par d n).q (BLP.Ne d n) : ℚ) : ℝ)) := by
    rw [PieceA.par_Le, PieceA.L0, PieceA.ee]; push_cast; ring
  have hpos : (0 : ℝ) < (((par d n).Le : ℚ) : ℝ) := by
    rw [hLe]
    have : (PieceA.u d n) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  have hpos' : (0 : ℚ) < ((LeN d n : ℤ) : ℚ) / 2 ^ (par d n).q := by rw [LeN_div hd hn]; exact_mod_cast hpos
  have h2q : (0 : ℚ) < 2 ^ (par d n).q := by positivity
  have : (0 : ℚ) < ((LeN d n : ℤ) : ℚ) := by
    have := mul_pos hpos' h2q; rwa [div_mul_cancel₀ _ h2q.ne'] at this
  exact_mod_cast this

theorem sigZ_nonneg (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ sigZ d n := by
  have hL := LeN_pos hd hn
  have hQ : 0 < QZ d n := by unfold QZ; positivity
  have hP : 0 < PFZ d n := by unfold PFZ; positivity
  unfold sigZ sigI
  apply Int.ediv_nonneg <;> nlinarith

theorem xN_le (q N : ℕ) : xN q N ≤ 2 ^ q :=
  Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

end Bounds

/-! ## The side conditions -/

theorem nn_of_eq {v : ℤ} {a : ℕ} (h : v = a) : 0 ≤ v := h ▸ Int.natCast_nonneg a

theorem pw_of_eq {v : ℤ} {a G : ℕ} (h : v = a) (ha : a ≤ G) : 0 ≤ v ∧ v ≤ G := by
  subst h; exact ⟨Int.natCast_nonneg a, by exact_mod_cast ha⟩

theorem mc_of_eq {vq vQ vX : ℤ} {q G : ℕ} (hq : vq = q) (hQ : vQ = 2 ^ q) (hqG : q ≤ G) (hX0 : 0 ≤ vX)
    (hXq : vX ≤ 2 ^ q) : 0 ≤ vq ∧ vq ≤ G ∧ vQ = 2 ^ vq.toNat ∧ 0 ≤ vX ∧ vX ≤ vQ := by
  subst hq hQ
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hqG, by rw [Int.toNat_natCast], hX0, hXq⟩

section Sem

variable {d n : ℕ}

/-- The side condition of step `k` of PARAM. -/
abbrev PSem (d n k : ℕ) : Prop := (parSt.getD k (.cst 0)).Sem (pv d n) (parG d n)

theorem parG_ge : (par d n).q ≤ parG d n ∧ (par d n).pF ≤ parG d n ∧ 2 * gsm_prec (par d n).B ≤ parG d n ∧
    (par d n).p ≤ parG d n ∧ (BLP.Ne d n).size ≤ parG d n := by
  have hG := size_Ne_le_pF (d := d) (n := n)
  have hpq : (par d n).p ≤ (par d n).q := by simp only [par]; omega
  unfold parG; omega

theorem mc_par {vX : ℤ} (h0 : 0 ≤ vX) (h1 : vX ≤ 2 ^ (par d n).q) :
    0 ≤ pv d n 26 ∧ pv d n 26 ≤ ((parG d n : ℕ) : ℤ) ∧ pv d n 37 = 2 ^ (pv d n 26).toNat ∧ 0 ≤ vX ∧
      vX ≤ pv d n 37 :=
  mc_of_eq (pv_26 (d := d) (n := n)) (pv_37 (d := d) (n := n)) parG_ge.1 h0 h1

theorem sem_20 : PSem d n 20 := nn_of_eq (pv_19 (d := d) (n := n))
theorem sem_22 : PSem d n 22 := nn_of_eq (pv_21 (d := d) (n := n))
theorem sem_25 : PSem d n 25 := nn_of_eq (pv_24 (d := d) (n := n))
theorem sem_29 : PSem d n 29 := nn_of_eq (pv_28 (d := d) (n := n))
theorem sem_32 : PSem d n 32 := nn_of_eq (pv_31 (d := d) (n := n))
theorem sem_34 : PSem d n 34 := pw_of_eq (pv_33 (d := d) (n := n)) parG_ge.2.2.1
theorem sem_35 : PSem d n 35 := pw_of_eq (pv_23 (d := d) (n := n)) parG_ge.2.2.2.1
theorem sem_36 : PSem d n 36 := pw_of_eq (pv_27 (d := d) (n := n)) parG_ge.2.1
theorem sem_37 : PSem d n 37 := pw_of_eq (pv_26 (d := d) (n := n)) parG_ge.1
theorem sem_39 : PSem d n 39 := pw_of_eq (pv_38 (d := d) (n := n))
  ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans parG_ge.2.2.2.1)))
theorem sem_42 : PSem d n 42 := nn_of_eq (pv_41 (d := d) (n := n))
theorem sem_44 : PSem d n 44 := nn_of_eq (pv_43 (d := d) (n := n))
theorem sem_46 : PSem d n 46 := pw_of_eq (pv_45 (d := d) (n := n)) ((Nat.sub_le _ _).trans parG_ge.1)
theorem sem_47 : PSem d n 47 :=
  mc_par ((by positivity : (0 : ℤ) ≤ 2 ^ ((par d n).q - 1)).trans_eq (pv_46 (d := d) (n := n)).symm)
    ((pv_46 (d := d) (n := n)).trans_le (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)))
theorem sem_49 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSem d n 49 :=
  pw_of_eq (pv_48 hd hn) ((Nat.sub_le _ _).trans parG_ge.2.2.2.2)
theorem sem_51 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSem d n 51 :=
  mc_par (nn_of_eq (pv_50 hd hn)) ((pv_50 hd hn).trans_le (by exact_mod_cast xN_le (par d n).q (BLP.Ne d n)))
theorem sem_57 : PSem d n 57 := nn_of_eq (pv_56 (d := d) (n := n))
theorem sem_59 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSem d n 59 :=
  pw_of_eq (pv_58 (d := d) (n := n))
    ((Nat.sub_le _ _).trans ((PieceA.size_facts d n hd hn).2.2.2.2.2.2.trans parG_ge.2.2.2.2))
theorem sem_61 : PSem d n 61 :=
  mc_par (nn_of_eq (pv_60 (d := d) (n := n)))
    ((pv_60 (d := d) (n := n)).trans_le (by exact_mod_cast xN_le (par d n).q (2 * d + 2)))

theorem sem_78 : PSem d n 78 := by
  have h1 := loI_nonneg (par d n).q (2 * d + 2) (by omega)
  have h2 : 0 ≤ E1N d n := Int.natCast_nonneg _
  have hQ : 0 ≤ QZ d n := by unfold QZ; positivity
  exact (mul_nonneg (by unfold L1N; linarith) hQ).trans_eq (pv_77 (d := d) (n := n)).symm

theorem sem_83 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSem d n 83 := by
  have hL := LeN_pos hd hn
  have : 0 ≤ (BLP.Ne d n : ℤ) * QZ d n ^ 3 := mul_nonneg (Int.natCast_nonneg _) (by unfold QZ; positivity)
  exact (Int.ediv_nonneg (by linarith) hL.le).trans_eq (pv_82 hd hn).symm

theorem sem_87 (hd : 1 ≤ d) (hn : 1 ≤ n) : PSem d n 87 := by
  have hP : 0 < PFZ d n := by unfold PFZ; positivity
  have : 0 ≤ sigZ d n * QZ d n ^ 2 := mul_nonneg (sigZ_nonneg hd hn) (sq_nonneg _)
  exact (Int.ediv_nonneg (by linarith) hP.le).trans_eq (pv_86 hd hn).symm

end Sem

theorem par_sem {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ k < parSt.length, (parSt.getD k (.cst 0)).Sem (pv d n) (parG d n) := by
  intro k hk
  rw [parSt_length] at hk
  interval_cases k
  all_goals try exact True.intro
  exacts [sem_20, sem_22, sem_25, sem_29, sem_32, sem_34, sem_35, sem_36, sem_37, sem_39, sem_42, sem_44, sem_46,
    sem_47, sem_49 hd hn, sem_51 hd hn, sem_57, sem_59 hd hn, sem_61, sem_78, sem_83 hd hn, sem_87 hd hn]

/-! ## The run -/

theorem parC_ok {L : Layout} (hNS : 172 ≤ L.NS) (hNN : 10 ≤ L.NN) : parC.OK L 44 where
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

theorem parIn_ok {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ y ∈ [0, 3], |parI d n y| ≤ 2 ^ ev (parG d n) (parIn y) := by
  intro y hy
  have hev : ev (parG d n) (parIn y) = parG d n := by simp [ev, parIn]
  simp only [hev]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl
  · show |(d : ℤ)| ≤ 2 ^ parG d n
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast d_le_G)
  · show |(n : ℤ)| ≤ 2 ^ parG d n
    exact (abs_of_nonneg (Int.natCast_nonneg _)).trans_le (by exact_mod_cast n_le_G hd hn)

/-- **PARAM on the machine**: from `d` in slot `0`, `n` in slot `3`, `0, 1, 2, 4` in the slots `1, 26, 27, 28` and `1`
in register `3`, the 93 steps of `parSt` leave `pv d n k` in slot `30 + k`, within `696 G + 3191` units
(`G = parG d n`); only the slots `30..122`, the slots from `128` and the registers `8`, `9` change. -/
theorem XV.param {d : ℕ} {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 10 ≤ L.NN) {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hT : 75 * parG d n + 343 < ℓ)
    (hTa : 75 * parG d n + 343 < 2 ^ ℓa) {σ : Env d} (h0 : σ.sc 0 = d) (h3 : σ.sc 3 = n) (hz : σ.sc 1 = 0)
    (h1 : σ.sc 26 = 1) (h2 : σ.sc 27 = 2) (h4 : σ.sc 28 = 4) (hn1 : σ.nat 3 = 1) :
    XRunsB L X ℓa ℓ (SL.code L parC parSt) σ (696 * parG d n + 3191) (fun σ' =>
      (∀ k < 93, σ'.sc (30 + k) = pv d n k) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => (30 ≤ y ∧ y < 123) ∨ 128 ≤ y) (fun j => j = 8 ∨ j = 9) σ σ') := by
  have hin : ∀ y ∈ [0, 3], σ.sc y = ((parI d n y : ℤ) : ℝ) := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · rw [h0]; simp [parI]
    · rw [h3]; simp [parI]
  have h := XV.sl (X := X) hL (parC_ok hNS hNN) (ι := parI d n) parSt_chk (par_sem hd hn)
    (by rw [parSt_length]; decide) hT hTa (parIn_ok hd hn) hin hz h1 h2 h4 hn1
  refine XV.mono h (by rw [parUnits]; simp [ev]) fun σ' ⟨hA, hD, hF⟩ => ⟨fun k hk => hA k (by
    rw [parSt_length]; exact hk), hD, hF.mono (fun y hy => ?_) (fun j hj => hj)⟩
  simp only [parC, parSt_length] at hy
  omega

end AdversarialBco.Bit.Transfer.BLM
