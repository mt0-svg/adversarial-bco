/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudInst
public import AdversarialBco.Unified.BudMaj
public import AdversarialBco.Unified.BudEncR
public import AdversarialBco.Bit.PieceA.Enc

@[expose] public section

/-!
# Lemma ENC of BL-O: PARAM at `k` as an `EncR`

Bit/PieceA/Enc.lean at `parK d n k`, `N_e(k) = 15 · 2^{17+k} d³ n⁴`: the precisions `η_e, η_1 ≤ 2^{-p-16}`,
`2^{-q}(1 + Le) ≤ 2^{-p-18}`, `2^{-pF} 2^40 N_e^2 d^4 ≤ 2^{-p}` (generic in `N_e` through its bit length,
`size_facts`), `encR d n k` reads PARAM's values at `parK d n k`, and `encR_ok` proves `EncR.OK (encR d n k)`
(Unified/BudEncR.lean) in `RunCaseK`. The leaves (`lnQ_err`, the roots, the roundings) are those of
Bit/PieceA/Enc.lean.
-/

namespace AdversarialBco.Unified.BudK

open AdversarialBco AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (lnQ lnErr sqrtDn sqrtUp rnd up dn)
open AdversarialBco.Bit.PieceA (ld lnQ_err sqrtDn_le_sqrt sqrt_le_sqrtDn_add one_le_sqrtDn sqrt_le_sqrtUp sqrtUp_le
  rnd_errR le_upR upR_le dnR_le sub_le_dnR)
open AdversarialBco.Unified.BudR (EncR)

/-! ## The precisions of PARAM -/

theorem parK_q (d n k : ℕ) : (parK d n k).q = pK d n k + 2 * (leK d n k).size + 24 := rfl

theorem parK_pF (d n k : ℕ) : (parK d n k).pF = pK d n k + 2 * leK d n k + 4 * ld d + 40 := rfl

theorem NeO_ge (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 2 ^ 20 * d ^ 3 ≤ NeO d n k ∧ 4 * d ≤ NeO d n k := by
  have h0 := Bit.PieceA.NeN_ge d n hd hn
  have hle : Bit.PieceA.NeN d n ≤ NeO d n k := by
    unfold Bit.PieceA.NeN NeO
    have : 2 ^ 17 ≤ 2 ^ (17 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    gcongr
  exact ⟨h0.1.trans hle, h0.2.trans hle⟩

theorem size_facts (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    21 ≤ leK d n k ∧ 3 * ld d + 18 ≤ leK d n k ∧ NeO d n k < 2 ^ leK d n k ∧ d < 2 ^ ld d ∧ (leK d n k).size ≤ leK d n k ∧
      leK d n k < 2 ^ (leK d n k).size ∧ (2 * d + 2).size ≤ leK d n k := by
  obtain ⟨h1, h2⟩ := NeO_ge d n k hd hn
  have hN := Nat.lt_size_self (NeO d n k)
  have hl1 : 1 ≤ ld d := Nat.size_pos.mpr hd
  have hld : 2 ^ (ld d - 1) ≤ d := Nat.lt_size.mp (by unfold ld at hl1 ⊢; omega)
  refine ⟨?_, ?_, hN, Nat.lt_size_self d, Nat.size_le.mpr Nat.lt_two_pow_self, Nat.lt_size_self _, ?_⟩
  · have h20 : 2 ^ 20 ≤ 2 ^ 20 * d ^ 3 := by
      have : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
      calc 2 ^ 20 = 2 ^ 20 * 1 := by ring
        _ ≤ 2 ^ 20 * d ^ 3 := by gcongr
    have : 20 < (NeO d n k).size := Nat.lt_size.mpr (le_trans h20 h1)
    unfold leK; omega
  · have h3 : 2 ^ (3 * ld d + 17) ≤ NeO d n k := by
      calc 2 ^ (3 * ld d + 17) = 2 ^ 20 * (2 ^ (ld d - 1)) ^ 3 := by
            rw [← pow_mul, ← pow_add]; congr 1; omega
        _ ≤ 2 ^ 20 * d ^ 3 := by gcongr
        _ ≤ NeO d n k := h1
    have : 3 * ld d + 17 < (NeO d n k).size := Nat.lt_size.mpr h3
    unfold leK; omega
  · apply Nat.size_le.mpr
    calc 2 * d + 2 ≤ 4 * d := by omega
      _ ≤ NeO d n k := h2
      _ < 2 ^ leK d n k := hN

/-- `2 s (4q + 1) 2^{p+16} ≤ 2^q` for `s ≤ ℓe`. -/
theorem lnErr_nat (d n k s : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hs : s ≤ leK d n k) :
    2 * s * (4 * (parK d n k).q + 1) * (2 ^ pK d n k * 2 ^ 16) ≤ 2 ^ (parK d n k).q := by
  obtain ⟨h21, hld, -, -, hls, hlX, -⟩ := size_facts d n k hd hn
  rw [parK_q] at *
  have hq : 4 * (pK d n k + 2 * (leK d n k).size + 24) + 1 ≤ 128 * leK d n k := by unfold pK; omega
  set X := 2 ^ (leK d n k).size with hXd
  have hX : 2 ^ (pK d n k + 2 * (leK d n k).size + 24) = 2 ^ pK d n k * 2 ^ 16 * (2 ^ 8 * X * X) := by
    rw [hXd, show pK d n k + 2 * (leK d n k).size + 24 = pK d n k + 16 + 8 + (leK d n k).size + (leK d n k).size by ring]
    simp only [pow_add]; ring
  rw [hX]
  have h1 : 2 * s * (4 * (pK d n k + 2 * (leK d n k).size + 24) + 1) ≤ 2 ^ 8 * X * X := by
    calc 2 * s * (4 * (pK d n k + 2 * (leK d n k).size + 24) + 1) ≤ 2 * leK d n k * (128 * leK d n k) := by gcongr
      _ = 2 ^ 8 * leK d n k * leK d n k := by ring
      _ ≤ 2 ^ 8 * X * X := by gcongr
  calc 2 * s * (4 * (pK d n k + 2 * (leK d n k).size + 24) + 1) * (2 ^ pK d n k * 2 ^ 16)
      = (2 ^ pK d n k * 2 ^ 16) * (2 * s * (4 * (pK d n k + 2 * (leK d n k).size + 24) + 1)) := by ring
    _ ≤ 2 ^ pK d n k * 2 ^ 16 * (2 ^ 8 * X * X) := by gcongr

theorem lnErr_le (d n k N : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hN : N.size ≤ leK d n k) :
    ((lnErr (parK d n k).q N : ℚ) : ℝ) ≤ tp d n k / 2 ^ 16 := by
  have h := lnErr_nat d n k N.size hd hn hN
  have h' : (2 * N.size * (4 * (parK d n k).q + 1) * (2 ^ pK d n k * 2 ^ 16) : ℝ) ≤ 2 ^ (parK d n k).q := by
    exact_mod_cast h
  simp only [lnErr, tp_eq]
  push_cast
  rw [div_le_iff₀ (by positivity), div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem Le_le_size (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Le d n k ≤ 25 * leK d n k := by
  obtain ⟨-, -, hN, -⟩ := size_facts d n k hd hn
  have hN0 : (0 : ℝ) < Ne d n k := by
    have : (1 : ℝ) ≤ Ne d n k := by unfold Ne; exact_mod_cast NeO_pos d n k hd hn
    linarith
  have hlt : Ne d n k < 2 ^ leK d n k := by unfold Ne; exact_mod_cast hN
  have hlog : Real.log (Ne d n k) < leK d n k * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_lt_log hN0 hlt
  have h2 := Real.log_two_lt_d9
  have hl0 : (0 : ℝ) ≤ leK d n k := by positivity
  rw [Le_eq d n k hd hn]; nlinarith

theorem eq_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (2 : ℝ) ^ (parK d n k).q * (1 + Le d n k) ≤ tp d n k / 2 ^ 18 := by
  obtain ⟨h21, -, -, -, -, hlX, -⟩ := size_facts d n k hd hn
  have hL := Le_le_size d n k hd hn
  have hX : (2 : ℝ) ^ (parK d n k).q =
      2 ^ pK d n k * 2 ^ 18 * (2 ^ 6 * (2 : ℝ) ^ (leK d n k).size * (2 : ℝ) ^ (leK d n k).size) := by
    rw [parK_q, show pK d n k + 2 * (leK d n k).size + 24 = pK d n k + 18 + 6 + (leK d n k).size + (leK d n k).size by ring]
    simp only [pow_add]; ring
  have hlX' : (leK d n k : ℝ) + 1 ≤ (2 : ℝ) ^ (leK d n k).size := by exact_mod_cast hlX
  have h21' : (21 : ℝ) ≤ leK d n k := by exact_mod_cast h21
  set X : ℝ := (2 : ℝ) ^ (leK d n k).size
  have hXX : (leK d n k : ℝ) + 1 ≤ X * X := by nlinarith
  have hnum : 1 + Le d n k ≤ 2 ^ 6 * X * X := by nlinarith
  have hX0 : 0 < X * X := by positivity
  rw [hX, tp_eq]
  calc 1 / (2 ^ pK d n k * 2 ^ 18 * (2 ^ 6 * X * X)) * (1 + Le d n k)
      ≤ 1 / (2 ^ pK d n k * 2 ^ 18 * (2 ^ 6 * X * X)) * (2 ^ 6 * X * X) := by gcongr
    _ = 1 / 2 ^ pK d n k / 2 ^ 18 := by
      have : X ≠ 0 := by positivity
      field_simp

theorem eF_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (2 : ℝ) ^ (parK d n k).pF * (2 ^ 40 * Ne d n k ^ 2 * (d : ℝ) ^ 4) ≤ tp d n k := by
  obtain ⟨-, -, hN, hdl, -⟩ := size_facts d n k hd hn
  have hN' : Ne d n k ≤ 2 ^ leK d n k := by unfold Ne; exact_mod_cast hN.le
  have hd' : (d : ℝ) ≤ 2 ^ ld d := by exact_mod_cast hdl.le
  have hN0 : (0 : ℝ) ≤ Ne d n k := by unfold Ne; positivity
  have hX : (2 : ℝ) ^ (parK d n k).pF = 2 ^ pK d n k * (2 ^ 40 * (2 ^ leK d n k) ^ 2 * (2 ^ ld d) ^ 4) := by
    rw [parK_pF]; simp only [pow_add, ← pow_mul]; ring
  rw [hX, tp_eq, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have : 2 ^ 40 * Ne d n k ^ 2 * (d : ℝ) ^ 4 ≤ 2 ^ 40 * (2 ^ leK d n k) ^ 2 * (2 ^ ld d) ^ 4 := by gcongr
  have h0 : (0 : ℝ) < 2 ^ pK d n k := by positivity
  nlinarith
/-! ## PARAM's values as an `EncR` -/

/-- `L0 = LOGINT_q(N_e)/2^q`, `η_e`, `L1 + η_1`. -/
def L0 (d n k : ℕ) : ℚ := lnQ (parK d n k).q (NeO d n k)
def ee (d n k : ℕ) : ℚ := lnErr (parK d n k).q (NeO d n k)
def l1Q (d n k : ℕ) : ℚ := lnQ (parK d n k).q (2 * d + 2) + lnErr (parK d n k).q (2 * d + 2)

theorem parK_Le (d n k : ℕ) : (parK d n k).Le = 36 * (L0 d n k - ee d n k) := rfl
theorem parK_eps (d n k : ℕ) : (parK d n k).eps = up (parK d n k).pF (14500 * d * (sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q) *
    (36 * (L0 d n k + ee d n k)) ^ 5 / sqrtDn (parK d n k).q n) := rfl
theorem parK_lam (d n k : ℕ) : (parK d n k).lam = rnd (parK d n k).pF (1 / (725 * d * (parK d n k).Le ^ 2)) := rfl
theorem parK_eta (d n k : ℕ) :
    (parK d n k).eta = rnd (parK d n k).pF (sqrtDn (parK d n k).q d / ((parK d n k).Le * sqrtDn (parK d n k).q n)) := rfl
theorem parK_sig2 (d n k : ℕ) : (parK d n k).sig2 = rnd (parK d n k).pF (1 / (8 * (parK d n k).Le)) := rfl
theorem parK_rho (d n k : ℕ) : (parK d n k).rho = dn (parK d n k).pF (1450 * d ^ 2 * (parK d n k).Le ^ 3) := rfl
theorem parK_kapc (d n k : ℕ) :
    (parK d n k).kapc = rnd (parK d n k).pF ((parK d n k).eta * (parK d n k).lam / (4 * (1 - (parK d n k).lam) ^ 2)) := rfl
theorem parK_nu (d n k : ℕ) : (parK d n k).nu = rnd (parK d n k).pF (1 / (1 - (parK d n k).lam)) := rfl
theorem parK_R (d n k : ℕ) : (parK d n k).R = up (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k)) := rfl
theorem parK_sb (d n k : ℕ) :
    (parK d n k).sb = dn (parK d n k).pF (1 / ((NeO d n k : ℚ) ^ 2 * (parK d n k).R * ((parK d n k).R + 1))) := rfl
theorem parK_W (d n k : ℕ) :
    (parK d n k).W = up (parK d n k).pF ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le)) := rfl
theorem parK_A0 (d n k : ℕ) : (parK d n k).A0 = rnd (parK d n k).p (sqrtUp (parK d n k).q (parK d n k).sig2) := rfl
theorem parK_B0 (d n k : ℕ) : (parK d n k).B0 = rnd (parK d n k).p (1 / sqrtUp (parK d n k).q (parK d n k).sig2) := rfl

/-- PARAM's values at `(d, n)` and their references. -/
noncomputable def encR (d n k : ℕ) : EncR where
  d := d
  n := n
  Ne := Ne d n k
  Le := Le d n k
  la := Real.log (2 * d + 2)
  tp := tp d n k
  eq := 1 / 2 ^ (parK d n k).q
  eF := 1 / 2 ^ (parK d n k).pF
  Lp := (parK d n k).Le
  Lh := ((36 * (L0 d n k + ee d n k) : ℚ) : ℝ)
  l1 := l1Q d n k
  rd := sqrtDn (parK d n k).q d
  rn := sqrtDn (parK d n k).q n
  sR := sqrtUp (parK d n k).q (l1Q d n k)
  sW := sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le)
  sU := sqrtUp (parK d n k).q (parK d n k).sig2
  ep := (parK d n k).eps
  lm := (parK d n k).lam
  et := (parK d n k).eta
  sg := (parK d n k).sig2
  ro := (parK d n k).rho
  kp := (parK d n k).kapc
  nu := (parK d n k).nu
  Rp := (parK d n k).R
  sb := (parK d n k).sb
  Wp := (parK d n k).W
  A0 := (parK d n k).A0
  B0 := (parK d n k).B0
theorem encR_ok (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCaseK d n k) : (encR d n k).OK := by
  have hR := reg_okK d n k hd hn h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLeq : (regK d n k).Le = Le d n k := rfl
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
  have hQ1 : (1 : ℝ) ≤ (regK d n k).Q := le_trans (by norm_num) hQ17
  have hsm : Le d n k ^ 4 * d * n ≤ Ne d n k := by
    have hLQ : Le d n k ≤ (regK d n k).Q := by rw [← hLeq]; linarith
    have hnQ : (n : ℝ) ≤ (regK d n k).Q ^ 10 := by
      have : (regK d n k).n = n := rfl
      linarith
    have hdQ : (d : ℝ) ≤ (regK d n k).Q ^ 3 := hQd
    calc Le d n k ^ 4 * d * n ≤ (regK d n k).Q ^ 4 * (regK d n k).Q ^ 3 * (regK d n k).Q ^ 10 := by
          gcongr
      _ = (regK d n k).Q ^ 17 := by ring
      _ ≤ (regK d n k).Q ^ 40 := pow_le_pow_right₀ hQ1 (by norm_num)
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

end AdversarialBco.Unified.BudK
