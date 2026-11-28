/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.BudInst
public import AdversarialBco.UW.BudMaj
public import AdversarialBco.Unified.BudEnc
public import AdversarialBco.UW.ProgPure

@[expose] public section

/-!
# Lemma ENC-W: PARAM-W's values against the reference of Theorem UW

BL-OW keeps BL-O's level fields (`R`, `s_b`, `W`, `Λ`, `N_e`, at `parO d n δ =
parK d n (kDel δ)`) and recomputes the parameters of the floor (`L`, `λ`, `σ²`, `ρ`, `ε`, `η`, `κ_c`, `ν`, `A_0`,
`B_0`) from PARAM-W's logarithm of `N_0` and the root of `u'` (UW/ProgPure.lean, `parOW`).

* `encR_okW`: Theorem U's `encR d n k` (Unified/BudEnc.lean) satisfies `EncR.OK` in the regime of the reference alone,
  without Theorem U's case (the level facts it reads are those of `reg_okW`); so the level enclosures of Lemma ENC
  (`R_le`, `R_rel`, `sb_le`, `sb_rel`, `W_le`, `W_rel`, ...) hold for BL-OW at every `k`.
-/

namespace AdversarialBco.UW.BudW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (lnQ lnErr sqrtDn sqrtUp rnd up dn)
open AdversarialBco.Bit.PieceA (ld lnQ_err sqrtDn_le_sqrt sqrt_le_sqrtDn_add one_le_sqrtDn sqrt_le_sqrtUp sqrtUp_le
  rnd_errR le_upR upR_le dnR_le sub_le_dnR)
open AdversarialBco.Unified.BudR (EncR)
open AdversarialBco.UW

/-- Lemma ENC's leaves at BL-O's level fields, in the regime of the reference (no level case). -/
theorem encR_okW (d n k : ℕ) (ρ : RefW) (hρ : RegimeW d n ρ) : (encR d n k).OK := by
  have hd := hρ.hd
  have hn := hρ.hn
  have hR := reg_okW d n k ρ hρ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLeq : (regW d n k ρ).Le = Le d n k := rfl
  have hL1 : 17467 ≤ Le d n k := hLeq ▸ hR.hL1
  have hq1 : 1 ≤ (parK d n k).q := by rw [parK_q]; unfold pK; omega
  have hsz := size_facts d n k hd hn
  have hNe1 : 1 ≤ NeO d n k := NeO_pos d n k hd hn
  -- the logarithms
  have hL0 : |(L0 d n k : ℝ) - Real.log (Ne d n k)| ≤ (ee d n k : ℝ) := lnQ_err _ _ hq1 hNe1
  have hee : (ee d n k : ℝ) ≤ tp d n k / 2 ^ 16 := lnErr_le d n k _ hd hn le_rfl
  have hL1q : |(lnQ (parK d n k).q (2 * d + 2) : ℝ) - Real.log (2 * d + 2)| ≤
      (lnErr (parK d n k).q (2 * d + 2) : ℝ) := by
    have := lnQ_err (parK d n k).q (2 * d + 2) hq1 (by omega); push_cast at this; exact this
  have he1 : (lnErr (parK d n k).q (2 * d + 2) : ℝ) ≤ tp d n k / 2 ^ 16 := lnErr_le d n k _ hd hn hsz.2.2.2.2.2.2
  have hLpR : ((parK d n k).Le : ℝ) = 36 * ((L0 d n k : ℝ) - (ee d n k : ℝ)) := by rw [parK_Le]; push_cast; ring
  have hl1R : ((l1Q d n k : ℚ) : ℝ) = (lnQ (parK d n k).q (2 * d + 2) : ℝ) + (lnErr (parK d n k).q (2 * d + 2) : ℝ) := by
    unfold l1Q; push_cast; ring
  have hLeR : Le d n k = 36 * Real.log (Ne d n k) := Le_eq d n k hd hn
  have h9 : tp d n k / 2 ^ 9 = 128 * (tp d n k / 2 ^ 16) := by ring
  have h15 : tp d n k / 2 ^ 15 = 2 * (tp d n k / 2 ^ 16) := by ring
  obtain ⟨hA1, hA2⟩ := abs_le.mp hL0
  obtain ⟨hB1, hB2⟩ := abs_le.mp hL1q
  have hu0 : 0 < tp d n k := by rw [tp_eq]; positivity
  -- the regime fact `Le^4 d n ≤ N_e`
  obtain ⟨hQ17, hQL, hQn, -, -, hQd⟩ := hR.Q_bd
  have hQ1 : (1 : ℝ) ≤ (regW d n k ρ).Q := le_trans (by norm_num) hQ17
  have hsm : Le d n k ^ 4 * d * n ≤ Ne d n k := by
    have hLQ : Le d n k ≤ (regW d n k ρ).Q := by rw [← hLeq]; linarith
    have hnQ : (n : ℝ) ≤ (regW d n k ρ).Q ^ 10 := by
      have : (regW d n k ρ).n = n := rfl
      linarith
    have hdQ : (d : ℝ) ≤ (regW d n k ρ).Q ^ 3 := hQd
    calc Le d n k ^ 4 * d * n ≤ (regW d n k ρ).Q ^ 4 * (regW d n k ρ).Q ^ 3 * (regW d n k ρ).Q ^ 10 := by
          gcongr
      _ = (regW d n k ρ).Q ^ 17 := by ring
      _ ≤ (regW d n k ρ).Q ^ 40 := pow_le_pow_right₀ hQ1 (by norm_num)
      _ = Ne d n k := hR.hQ
  refine
    { hd := hd'
      hn := hn'
      hNe := hR.hNe
      hLe := hL1
      hsm := hsm
      hla1 := ?_
      hla2 := ?_
      htp0 := hu0
      htp1 := ?_
      heq0 := by show (0 : ℝ) < 1 / 2 ^ (parK d n k).q; positivity
      heq1 := eq_le d n k hd hn
      heF0 := by show (0 : ℝ) < 1 / 2 ^ (parK d n k).pF; positivity
      heF1 := eF_le d n k hd hn
      hLp1 := ?_
      hLp2 := ?_
      hLh1 := ?_
      hLh2 := ?_
      hl1a := ?_
      hl1b := ?_
      hrd0 := one_le_sqrtDn _ (by exact_mod_cast hd)
      hrd1 := ?_
      hrd2 := ?_
      hrn0 := one_le_sqrtDn _ (by exact_mod_cast hn)
      hrn1 := ?_
      hrn2 := ?_
      hsR1 := sqrt_le_sqrtUp _ _
      hsR2 := ?_
      hsW1 := ?_
      hsW2 := ?_
      hsU1 := sqrt_le_sqrtUp _ _
      hsU2 := ?_
      hep1 := ?_
      hep2 := ?_
      hlm := ?_
      het := ?_
      hsg := ?_
      hro1 := ?_
      hro2 := ?_
      hkp := ?_
      hnu := ?_
      hRp1 := ?_
      hRp2 := ?_
      hsb1 := ?_
      hsb2 := ?_
      hWp1 := ?_
      hWp2 := ?_
      hA0 := ?_
      hB0 := ?_ }
  · show 1 ≤ Real.log (2 * (d : ℝ) + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ 2 * d + 1
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d + 2 by positivity)
    linarith
  · show tp d n k ≤ 1 / 2 ^ 160
    rw [tp_eq]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by unfold pK; omega))
  · show Le d n k - tp d n k / 2 ^ 9 ≤ ((parK d n k).Le : ℝ)
    rw [hLpR, hLeR]; linarith
  · show ((parK d n k).Le : ℝ) ≤ Le d n k
    rw [hLpR, hLeR]; have : (0 : ℝ) ≤ ee d n k := le_trans (abs_nonneg _) hL0; linarith
  · show Le d n k ≤ ((36 * (L0 d n k + ee d n k) : ℚ) : ℝ)
    push_cast; rw [hLeR]; linarith
  · show ((36 * (L0 d n k + ee d n k) : ℚ) : ℝ) ≤ Le d n k + tp d n k / 2 ^ 9
    push_cast; rw [hLeR]; linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ ((l1Q d n k : ℚ) : ℝ)
    rw [hl1R]; linarith
  · show ((l1Q d n k : ℚ) : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) + tp d n k / 2 ^ 15
    rw [hl1R]; linarith
  · show (sqrtDn (parK d n k).q (d : ℚ) : ℝ) ≤ Real.sqrt (d : ℝ)
    have := sqrtDn_le_sqrt (parK d n k).q (x := (d : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (d : ℝ) ≤ (sqrtDn (parK d n k).q (d : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q
    have := sqrt_le_sqrtDn_add (parK d n k).q (d : ℚ); push_cast at this; exact this
  · show (sqrtDn (parK d n k).q (n : ℚ) : ℝ) ≤ Real.sqrt (n : ℝ)
    have := sqrtDn_le_sqrt (parK d n k).q (x := (n : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (n : ℝ) ≤ (sqrtDn (parK d n k).q (n : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q
    have := sqrt_le_sqrtDn_add (parK d n k).q (n : ℚ); push_cast at this; exact this
  · show (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) ≤ Real.sqrt ((l1Q d n k : ℚ) : ℝ) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q (l1Q d n k); rw [mul_one_div]; exact this
  · show Real.sqrt (Ne d n k / ((parK d n k).Le : ℝ)) ≤ (sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le) : ℝ)
    have := sqrt_le_sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le); push_cast at this; exact this
  · show (sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le) : ℝ) ≤
      Real.sqrt (Ne d n k / ((parK d n k).Le : ℝ)) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le); push_cast at this; rw [mul_one_div]; exact this
  · show (sqrtUp (parK d n k).q (parK d n k).sig2 : ℝ) ≤ Real.sqrt ((parK d n k).sig2 : ℝ) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q (parK d n k).sig2; rw [mul_one_div]; exact this
  · show 14500 * (d : ℝ) * ((sqrtDn (parK d n k).q (d : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q) *
      ((36 * (L0 d n k + ee d n k) : ℚ) : ℝ) ^ 5 / (sqrtDn (parK d n k).q (n : ℚ) : ℝ) ≤ ((parK d n k).eps : ℝ)
    have := le_upR (parK d n k).pF (14500 * d * (sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q) *
      (36 * (L0 d n k + ee d n k)) ^ 5 / sqrtDn (parK d n k).q n)
    rw [← parK_eps] at this; push_cast at this ⊢; exact this
  · show ((parK d n k).eps : ℝ) ≤ 14500 * (d : ℝ) * ((sqrtDn (parK d n k).q (d : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q) *
      ((36 * (L0 d n k + ee d n k) : ℚ) : ℝ) ^ 5 / (sqrtDn (parK d n k).q (n : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).pF
    have := upR_le (parK d n k).pF (14500 * d * (sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q) *
      (36 * (L0 d n k + ee d n k)) ^ 5 / sqrtDn (parK d n k).q n)
    rw [← parK_eps] at this; push_cast at this ⊢; exact this
  · show |((parK d n k).lam : ℝ) - 1 / (725 * (d : ℝ) * ((parK d n k).Le : ℝ) ^ 2)| ≤ 1 / 2 ^ (parK d n k).pF / 2
    have := rnd_errR (parK d n k).pF (1 / (725 * d * (parK d n k).Le ^ 2))
    rw [← parK_lam] at this; push_cast at this; exact this
  · show |((parK d n k).eta : ℝ) - (sqrtDn (parK d n k).q (d : ℚ) : ℝ) / (((parK d n k).Le : ℝ) *
      (sqrtDn (parK d n k).q (n : ℚ) : ℝ))| ≤ 1 / 2 ^ (parK d n k).pF / 2
    have := rnd_errR (parK d n k).pF (sqrtDn (parK d n k).q d / ((parK d n k).Le * sqrtDn (parK d n k).q n))
    rw [← parK_eta] at this; push_cast at this; exact this
  · show |((parK d n k).sig2 : ℝ) - 1 / (8 * ((parK d n k).Le : ℝ))| ≤ 1 / 2 ^ (parK d n k).pF / 2
    have := rnd_errR (parK d n k).pF (1 / (8 * (parK d n k).Le))
    rw [← parK_sig2] at this; push_cast at this; exact this
  · show 1450 * (d : ℝ) ^ 2 * ((parK d n k).Le : ℝ) ^ 3 - 1 / 2 ^ (parK d n k).pF ≤ ((parK d n k).rho : ℝ)
    have := sub_le_dnR (parK d n k).pF (1450 * d ^ 2 * (parK d n k).Le ^ 3)
    rw [← parK_rho] at this; push_cast at this; exact this
  · show ((parK d n k).rho : ℝ) ≤ 1450 * (d : ℝ) ^ 2 * ((parK d n k).Le : ℝ) ^ 3
    have := dnR_le (parK d n k).pF (1450 * d ^ 2 * (parK d n k).Le ^ 3)
    rw [← parK_rho] at this; push_cast at this; exact this
  · show |((parK d n k).kapc : ℝ) - ((parK d n k).eta : ℝ) * ((parK d n k).lam : ℝ) / (4 * (1 - ((parK d n k).lam : ℝ)) ^ 2)| ≤
      1 / 2 ^ (parK d n k).pF / 2
    have := rnd_errR (parK d n k).pF ((parK d n k).eta * (parK d n k).lam / (4 * (1 - (parK d n k).lam) ^ 2))
    rw [← parK_kapc] at this; push_cast at this; exact this
  · show |((parK d n k).nu : ℝ) - 1 / (1 - ((parK d n k).lam : ℝ))| ≤ 1 / 2 ^ (parK d n k).pF / 2
    have := rnd_errR (parK d n k).pF (1 / (1 - (parK d n k).lam))
    rw [← parK_nu] at this; push_cast at this; exact this
  · show 134 * (d : ℝ) * (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) ≤ ((parK d n k).R : ℝ)
    have := le_upR (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
    rw [← parK_R] at this; push_cast at this; exact this
  · show ((parK d n k).R : ℝ) ≤ 134 * (d : ℝ) * (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) + 1 / 2 ^ (parK d n k).pF
    have := upR_le (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
    rw [← parK_R] at this; push_cast at this; exact this
  · show 1 / (Ne d n k ^ 2 * ((parK d n k).R : ℝ) * (((parK d n k).R : ℝ) + 1)) - 1 / 2 ^ (parK d n k).pF ≤ ((parK d n k).sb : ℝ)
    have := sub_le_dnR (parK d n k).pF (1 / ((NeO d n k : ℚ) ^ 2 * (parK d n k).R * ((parK d n k).R + 1)))
    rw [← parK_sb] at this; push_cast at this; exact this
  · show ((parK d n k).sb : ℝ) ≤ 1 / (Ne d n k ^ 2 * ((parK d n k).R : ℝ) * (((parK d n k).R : ℝ) + 1))
    have := dnR_le (parK d n k).pF (1 / ((NeO d n k : ℚ) ^ 2 * (parK d n k).R * ((parK d n k).R + 1)))
    rw [← parK_sb] at this; push_cast at this; exact this
  · show ((parK d n k).R : ℝ) + 4 * (d : ℝ) * (sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le) : ℝ) ≤
      ((parK d n k).W : ℝ)
    have := le_upR (parK d n k).pF ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le))
    rw [← parK_W] at this; push_cast at this; exact this
  · show ((parK d n k).W : ℝ) ≤ ((parK d n k).R : ℝ) + 4 * (d : ℝ) *
      (sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le) : ℝ) + 1 / 2 ^ (parK d n k).pF
    have := upR_le (parK d n k).pF ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le))
    rw [← parK_W] at this; push_cast at this; exact this
  · show |((parK d n k).A0 : ℝ) - (sqrtUp (parK d n k).q (parK d n k).sig2 : ℝ)| ≤ tp d n k / 2
    have := rnd_errR (parK d n k).p (sqrtUp (parK d n k).q (parK d n k).sig2)
    rw [← parK_A0] at this; exact this
  · show |((parK d n k).B0 : ℝ) - 1 / (sqrtUp (parK d n k).q (parK d n k).sig2 : ℝ)| ≤ tp d n k / 2
    have := rnd_errR (parK d n k).p (1 / sqrtUp (parK d n k).q (parK d n k).sig2)
    rw [← parK_B0] at this; push_cast at this; exact this


/-! ## The floor fields of PARAM-W as an `EncR` at `N_0` with BL-O's precisions -/

section Floor

open AdversarialBco.UW.BLOW (n0O lf0 lf1 parOW)

/-- PARAM-W's floor fields at `(d, n, δ)` as an `EncR` at `N_0` with BL-O's precisions `p, q, pF` at `k_δ`. The
fields BL-OW computes from the floor are PARAM-W's (`L'`, `λ'`, `σ²'`, `ρ'`, `ν'`, `A_0`, `B_0`); `ε'`, `η'`, `κ_c'`
here are PARAM's formulas at `N_0` without the root of `u'` and `s_b`, `W` PARAM's at `N_0`: no lemma read below
uses them for BL-OW. -/
noncomputable def encF (d n : ℕ) (δ : ℚ) : EncR where
  d := d
  n := n
  Ne := (n0O d n : ℝ)
  Le := Bit.PieceA.Le d n
  la := Real.log (2 * d + 2)
  tp := Unified.BudK.tp d n (kDel δ)
  eq := 1 / 2 ^ (parO d n δ).q
  eF := 1 / 2 ^ (parO d n δ).pF
  Lp := ((parOW d n δ).Le : ℝ)
  Lh := ((36 * lf1 d n δ : ℚ) : ℝ)
  l1 := l1Q d n (kDel δ)
  rd := sqrtDn (parO d n δ).q d
  rn := sqrtDn (parO d n δ).q n
  sR := sqrtUp (parO d n δ).q (l1Q d n (kDel δ))
  sW := sqrtUp (parO d n δ).q ((n0O d n : ℚ) / (parOW d n δ).Le)
  sU := sqrtUp (parO d n δ).q (parOW d n δ).sig2
  ep := up (parO d n δ).pF (14500 * d * (sqrtDn (parO d n δ).q d + 1 / 2 ^ (parO d n δ).q) *
    (36 * lf1 d n δ) ^ 5 / sqrtDn (parO d n δ).q n)
  lm := (parOW d n δ).lam
  et := rnd (parO d n δ).pF (sqrtDn (parO d n δ).q d / ((parOW d n δ).Le * sqrtDn (parO d n δ).q n))
  sg := (parOW d n δ).sig2
  ro := (parOW d n δ).rho
  kp := rnd (parO d n δ).pF (rnd (parO d n δ).pF (sqrtDn (parO d n δ).q d /
    ((parOW d n δ).Le * sqrtDn (parO d n δ).q n)) * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2))
  nu := (parOW d n δ).nu
  Rp := (parO d n δ).R
  sb := dn (parO d n δ).pF (1 / ((n0O d n : ℚ) ^ 2 * (parO d n δ).R * ((parO d n δ).R + 1)))
  Wp := up (parO d n δ).pF ((parO d n δ).R + 4 * d * sqrtUp (parO d n δ).q ((n0O d n : ℚ) / (parOW d n δ).Le))
  A0 := (parOW d n δ).A0
  B0 := (parOW d n δ).B0

theorem n0O_cast (d n : ℕ) : (n0O d n : ℝ) = Bit.PieceA.Ne d n := by
  unfold n0O NeO Bit.PieceA.Ne Bit.PieceA.NeN; push_cast; ring

/-- At `k = 0` the level is the floor: `Le(0) = L_f`. -/
theorem Le_zero (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Unified.BudK.Le d n 0 = Bit.PieceA.Le d n := by
  rw [Le_eq d n 0 hd hn, Bit.PieceA.Le]
  congr 2
  all_goals show (NeO d n 0 : ℝ) = Bit.PieceA.Ne d n
  all_goals exact n0O_cast d n

/-- Lemma ENC's leaves at PARAM-W's floor fields, in the regime of the reference. -/
theorem encF_ok (d n : ℕ) (δ : ℚ) (ρ : RefW) (hρ : RegimeW d n ρ) : (encF d n δ).OK := by
  set k := kDel δ with hk
  have hd := hρ.hd
  have hn := hρ.hn
  have hR := reg_okW d n k ρ hρ
  have hR0 := reg_okW d n 0 ρ hρ
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLf1 : 17467 ≤ Bit.PieceA.Le d n := hR.hLf1
  have hLfLe : Bit.PieceA.Le d n ≤ Unified.BudK.Le d n k := hR.hLfLe
  have hq1 : 1 ≤ (parK d n k).q := by rw [parK_q]; unfold pK; omega
  have hsz := size_facts d n k hd hn
  have hN01 : 1 ≤ n0O d n := NeO_pos d n 0 hd hn
  have hN0k : n0O d n ≤ NeO d n k := by
    unfold n0O NeO
    have : 2 ^ (17 + 0) ≤ 2 ^ (17 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    gcongr
  have hN0kR : (n0O d n : ℝ) ≤ Unified.BudK.Ne d n k := by show (n0O d n : ℝ) ≤ (NeO d n k : ℝ); exact_mod_cast hN0k
  have hN0s : (n0O d n).size ≤ leK d n k := Nat.size_le_size hN0k
  have hLf_eq : Bit.PieceA.Le d n = 36 * Real.log (n0O d n : ℝ) := by rw [n0O_cast]; rfl
  -- the logarithm of `N_0`
  have hL0 : |((lnQ (parK d n k).q (n0O d n) : ℚ) : ℝ) - Real.log (n0O d n : ℝ)| ≤
      ((lnErr (parK d n k).q (n0O d n) : ℚ) : ℝ) := lnQ_err _ _ hq1 hN01
  have hee : ((lnErr (parK d n k).q (n0O d n) : ℚ) : ℝ) ≤ Unified.BudK.tp d n k / 2 ^ 16 :=
    lnErr_le d n k _ hd hn hN0s
  have hL1q : |(lnQ (parK d n k).q (2 * d + 2) : ℝ) - Real.log (2 * d + 2)| ≤
      (lnErr (parK d n k).q (2 * d + 2) : ℝ) := by
    have := lnQ_err (parK d n k).q (2 * d + 2) hq1 (by omega); push_cast at this; exact this
  have he1 : (lnErr (parK d n k).q (2 * d + 2) : ℝ) ≤ Unified.BudK.tp d n k / 2 ^ 16 :=
    lnErr_le d n k _ hd hn hsz.2.2.2.2.2.2
  have hLpR : ((parOW d n δ).Le : ℝ) = 36 * (((lnQ (parK d n k).q (n0O d n) : ℚ) : ℝ) -
      ((lnErr (parK d n k).q (n0O d n) : ℚ) : ℝ)) := by
    show ((36 * lf0 d n δ : ℚ) : ℝ) = _
    unfold lf0; push_cast; rw [show parO d n δ = parK d n k from rfl]
  have hLhR : ((36 * lf1 d n δ : ℚ) : ℝ) = 36 * (((lnQ (parK d n k).q (n0O d n) : ℚ) : ℝ) +
      ((lnErr (parK d n k).q (n0O d n) : ℚ) : ℝ)) := by
    unfold lf1; push_cast; rw [show parO d n δ = parK d n k from rfl]
  have hl1R : ((l1Q d n k : ℚ) : ℝ) = (lnQ (parK d n k).q (2 * d + 2) : ℝ) + (lnErr (parK d n k).q (2 * d + 2) : ℝ) := by
    unfold l1Q; push_cast; ring
  have h9 : Unified.BudK.tp d n k / 2 ^ 9 = 128 * (Unified.BudK.tp d n k / 2 ^ 16) := by ring
  have h15 : Unified.BudK.tp d n k / 2 ^ 15 = 2 * (Unified.BudK.tp d n k / 2 ^ 16) := by ring
  obtain ⟨hA1, hA2⟩ := abs_le.mp hL0
  obtain ⟨hB1, hB2⟩ := abs_le.mp hL1q
  have hu0 : 0 < Unified.BudK.tp d n k := by rw [tp_eq]; positivity
  -- the regime fact `L_f^4 d n ≤ N_0`, from the record at `k = 0`
  obtain ⟨hQ17, hQL, hQn, -, -, hQd⟩ := hR0.Q_bd
  have hQ1 : (1 : ℝ) ≤ (regW d n 0 ρ).Q := le_trans (by norm_num) hQ17
  have hsm : Bit.PieceA.Le d n ^ 4 * d * n ≤ (n0O d n : ℝ) := by
    have hLQ : Bit.PieceA.Le d n ≤ (regW d n 0 ρ).Q := by
      have : (regW d n 0 ρ).Le = Bit.PieceA.Le d n := Le_zero d n hd hn
      rw [← this]; linarith
    have hnQ : (n : ℝ) ≤ (regW d n 0 ρ).Q ^ 10 := by
      have : (regW d n 0 ρ).n = n := rfl
      linarith
    have hdQ : (d : ℝ) ≤ (regW d n 0 ρ).Q ^ 3 := hQd
    have hLf0 : 0 ≤ Bit.PieceA.Le d n := by linarith
    calc Bit.PieceA.Le d n ^ 4 * d * n ≤ (regW d n 0 ρ).Q ^ 4 * (regW d n 0 ρ).Q ^ 3 * (regW d n 0 ρ).Q ^ 10 := by
          gcongr
      _ = (regW d n 0 ρ).Q ^ 17 := by ring
      _ ≤ (regW d n 0 ρ).Q ^ 40 := pow_le_pow_right₀ hQ1 (by norm_num)
      _ = (regW d n 0 ρ).Ne := hR0.hQ
      _ = (n0O d n : ℝ) := rfl
  have hNe : 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 ≤ (n0O d n : ℝ) := by
    unfold n0O NeO; push_cast; ring_nf; exact le_refl _
  refine
    { hd := hd'
      hn := hn'
      hNe := hNe
      hLe := hLf1
      hsm := hsm
      hla1 := ?_
      hla2 := ?_
      htp0 := hu0
      htp1 := ?_
      heq0 := by show (0 : ℝ) < 1 / 2 ^ (parO d n δ).q; positivity
      heq1 := ?_
      heF0 := by show (0 : ℝ) < 1 / 2 ^ (parO d n δ).pF; positivity
      heF1 := ?_
      hLp1 := ?_
      hLp2 := ?_
      hLh1 := ?_
      hLh2 := ?_
      hl1a := ?_
      hl1b := ?_
      hrd0 := one_le_sqrtDn _ (by exact_mod_cast hd)
      hrd1 := ?_
      hrd2 := ?_
      hrn0 := one_le_sqrtDn _ (by exact_mod_cast hn)
      hrn1 := ?_
      hrn2 := ?_
      hsR1 := sqrt_le_sqrtUp _ _
      hsR2 := ?_
      hsW1 := ?_
      hsW2 := ?_
      hsU1 := sqrt_le_sqrtUp _ _
      hsU2 := ?_
      hep1 := ?_
      hep2 := ?_
      hlm := ?_
      het := ?_
      hsg := ?_
      hro1 := ?_
      hro2 := ?_
      hkp := ?_
      hnu := ?_
      hRp1 := ?_
      hRp2 := ?_
      hsb1 := ?_
      hsb2 := ?_
      hWp1 := ?_
      hWp2 := ?_
      hA0 := ?_
      hB0 := ?_ }
  · show 1 ≤ Real.log (2 * (d : ℝ) + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ 2 * d + 1
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d + 2 by positivity)
    linarith
  · show Unified.BudK.tp d n k ≤ 1 / 2 ^ 160
    rw [tp_eq]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by unfold pK; omega))
  · show 1 / (2 : ℝ) ^ (parK d n k).q * (1 + Bit.PieceA.Le d n) ≤ Unified.BudK.tp d n k / 2 ^ 18
    have h := eq_le d n k hd hn
    have : 0 ≤ 1 / (2 : ℝ) ^ (parK d n k).q := by positivity
    nlinarith
  · show 1 / (2 : ℝ) ^ (parK d n k).pF * (2 ^ 40 * (n0O d n : ℝ) ^ 2 * (d : ℝ) ^ 4) ≤ Unified.BudK.tp d n k
    have h := eF_le d n k hd hn
    have h0 : (0 : ℝ) ≤ n0O d n := by positivity
    have h2 : (n0O d n : ℝ) ^ 2 ≤ Unified.BudK.Ne d n k ^ 2 := pow_le_pow_left₀ h0 hN0kR 2
    have : 0 ≤ 1 / (2 : ℝ) ^ (parK d n k).pF * (2 ^ 40 * (d : ℝ) ^ 4) := by positivity
    nlinarith
  · show Bit.PieceA.Le d n - Unified.BudK.tp d n k / 2 ^ 9 ≤ ((parOW d n δ).Le : ℝ)
    rw [hLpR, hLf_eq]; linarith
  · show ((parOW d n δ).Le : ℝ) ≤ Bit.PieceA.Le d n
    rw [hLpR, hLf_eq]
    have : (0 : ℝ) ≤ ((lnErr (parK d n k).q (n0O d n) : ℚ) : ℝ) := le_trans (abs_nonneg _) hL0
    linarith
  · show Bit.PieceA.Le d n ≤ ((36 * lf1 d n δ : ℚ) : ℝ)
    rw [hLhR, hLf_eq]; linarith
  · show ((36 * lf1 d n δ : ℚ) : ℝ) ≤ Bit.PieceA.Le d n + Unified.BudK.tp d n k / 2 ^ 9
    rw [hLhR, hLf_eq]; linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ ((l1Q d n k : ℚ) : ℝ)
    rw [hl1R]; linarith
  · show ((l1Q d n k : ℚ) : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) + Unified.BudK.tp d n k / 2 ^ 15
    rw [hl1R]; linarith
  · show (sqrtDn (parK d n k).q (d : ℚ) : ℝ) ≤ Real.sqrt (d : ℝ)
    have := sqrtDn_le_sqrt (parK d n k).q (x := (d : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (d : ℝ) ≤ (sqrtDn (parK d n k).q (d : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q
    have := sqrt_le_sqrtDn_add (parK d n k).q (d : ℚ); push_cast at this; exact this
  · show (sqrtDn (parK d n k).q (n : ℚ) : ℝ) ≤ Real.sqrt (n : ℝ)
    have := sqrtDn_le_sqrt (parK d n k).q (x := (n : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (n : ℝ) ≤ (sqrtDn (parK d n k).q (n : ℚ) : ℝ) + 1 / 2 ^ (parK d n k).q
    have := sqrt_le_sqrtDn_add (parK d n k).q (n : ℚ); push_cast at this; exact this
  · show (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) ≤ Real.sqrt ((l1Q d n k : ℚ) : ℝ) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q (l1Q d n k); rw [mul_one_div]; exact this
  · show Real.sqrt ((n0O d n : ℝ) / ((parOW d n δ).Le : ℝ)) ≤
      (sqrtUp (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le) : ℝ)
    have := sqrt_le_sqrtUp (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le); push_cast at this; exact this
  · show (sqrtUp (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le) : ℝ) ≤
      Real.sqrt ((n0O d n : ℝ) / ((parOW d n δ).Le : ℝ)) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le); push_cast at this; rw [mul_one_div]; exact this
  · show (sqrtUp (parK d n k).q (parOW d n δ).sig2 : ℝ) ≤ Real.sqrt ((parOW d n δ).sig2 : ℝ) + 2 * (1 / 2 ^ (parK d n k).q)
    have := sqrtUp_le (parK d n k).q (parOW d n δ).sig2; rw [mul_one_div]; exact this
  · dsimp only [encF]
    have := le_upR (parK d n k).pF (14500 * d * (sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q) *
      (36 * lf1 d n δ) ^ 5 / sqrtDn (parK d n k).q n)
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := upR_le (parK d n k).pF (14500 * d * (sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q) *
      (36 * lf1 d n δ) ^ 5 / sqrtDn (parK d n k).q n)
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := rnd_errR (parK d n k).pF (1 / (725 * d * (parOW d n δ).Le ^ 2))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := rnd_errR (parK d n k).pF (sqrtDn (parK d n k).q d / ((parOW d n δ).Le * sqrtDn (parK d n k).q n))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := rnd_errR (parK d n k).pF (1 / (8 * (parOW d n δ).Le))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := sub_le_dnR (parK d n k).pF (1450 * d ^ 2 * (parOW d n δ).Le ^ 3)
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := dnR_le (parK d n k).pF (1450 * d ^ 2 * (parOW d n δ).Le ^ 3)
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := rnd_errR (parK d n k).pF (rnd (parK d n k).pF (sqrtDn (parK d n k).q d /
      ((parOW d n δ).Le * sqrtDn (parK d n k).q n)) * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := rnd_errR (parK d n k).pF (1 / (1 - (parOW d n δ).lam))
    push_cast at this ⊢; exact this
  · show 134 * (d : ℝ) * (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) ≤ ((parK d n k).R : ℝ)
    have := le_upR (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
    rw [← parK_R] at this; push_cast at this; exact this
  · show ((parK d n k).R : ℝ) ≤ 134 * (d : ℝ) * (sqrtUp (parK d n k).q (l1Q d n k) : ℝ) + 1 / 2 ^ (parK d n k).pF
    have := upR_le (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
    rw [← parK_R] at this; push_cast at this; exact this
  · dsimp only [encF]
    have := sub_le_dnR (parK d n k).pF (1 / ((n0O d n : ℚ) ^ 2 * (parK d n k).R * ((parK d n k).R + 1)))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := dnR_le (parK d n k).pF (1 / ((n0O d n : ℚ) ^ 2 * (parK d n k).R * ((parK d n k).R + 1)))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := le_upR (parK d n k).pF ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le))
    push_cast at this ⊢; exact this
  · dsimp only [encF]
    have := upR_le (parK d n k).pF ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((n0O d n : ℚ) / (parOW d n δ).Le))
    push_cast at this ⊢; exact this
  · show |((parOW d n δ).A0 : ℝ) - (sqrtUp (parK d n k).q (parOW d n δ).sig2 : ℝ)| ≤ Unified.BudK.tp d n k / 2
    have := rnd_errR (parK d n k).p (sqrtUp (parK d n k).q (parOW d n δ).sig2)
    exact this
  · show |((parOW d n δ).B0 : ℝ) - 1 / (sqrtUp (parK d n k).q (parOW d n δ).sig2 : ℝ)| ≤ Unified.BudK.tp d n k / 2
    have := rnd_errR (parK d n k).p (1 / sqrtUp (parK d n k).q (parOW d n δ).sig2)
    push_cast at this; exact this

end Floor

end AdversarialBco.UW.BudW
