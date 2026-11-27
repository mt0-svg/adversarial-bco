/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudDefs
public import AdversarialBco.Unified.BudReg
public import AdversarialBco.Bit.PieceA.Regime

@[expose] public section

/-!
# Theorem BUD of BL-O: the base constants at `k` as a `Reg`

`regK d n k` reads the base constants of Unified/BudDefs.lean at `(d, n, k)`; every derived constant there is the one
of `Reg` (Unified/BudReg.lean) at `regK d n k` by definition. `reg_okK` proves `Reg.OK (regK d n k)` in the case
`RunCaseK d n k`, after Bit/PieceA/Inst.lean:

* the reference at `δ_BL = 2^{-19-k}/(dn)³`: `δ₁ = δ_BL/3`, `δe = 1/N_e(k)`, `Le = 36 ln N_e(k)` and the formulas of
  `λ, η, ε, ρ, κ_c` (`poK_de`, `Le_eq`, ...);
* the regime facts by monotonicity in `N_e`: `N_e(k) = 2^k N_e(0)` (`NeO_cast`), so `Le(k) ≥ Le(0)` and
  `ε(k) ≥ ε(0)`; in the case `ε(0) ≤ 1/4`, and Bit/PieceA/Regime.lean gives `N_e(0) > 2^700`, `Le(0) ≥ 17467`,
  `d^15 ≤ N_e(0)`, `32⁴ n⁴ ≤ N_e(0)`; `n ≥ 29000² d³ Le(k)^10` from `ε(k) ≤ 1/2` (`n_ge_of_eps`), hence
  `(10 Le(k))^40 ≤ N_e(k)`;
* the precision facts generic in `N_e` through its bit length (`gen_u`, `gen_eh`, `t2_tpK`).
-/

namespace AdversarialBco.Unified.BudK

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.BLO
open AdversarialBco.Unified.BudR (Reg)

/-- BL-O's base constants at `(d, n, k)`. -/
noncomputable def regK (d n k : ℕ) : Reg where
  d := d
  n := n
  Ne := Ne d n k
  de := de d n k
  Le := Le d n k
  lam := lam d n k
  eta := eta d n k
  eps := eps d n k
  rho := rho d n k
  R := R d n k
  kc := kc d n k
  tp := tp d n k
  eh := eh d n k
  t2 := 2 ^ ((parK d n k).B / 2)
  Q := Ne d n k ^ ((1 : ℝ) / 40)

example (d n k : ℕ) : sel d n k = (regK d n k).sel := rfl
example (d n k : ℕ) : val d n k = (regK d n k).val := rfl
example (d n k : ℕ) : hTr d n k 3 = (regK d n k).hTr 3 := rfl
example (d n k : ℕ) : kapO d n k = (regK d n k).kapO := rfl
example (d n k : ℕ) : regO d n k = (regK d n k).regO := rfl

/-! ## The precision -/

/-- `ℓe = len N_e(k)`. -/
def leK (d n k : ℕ) : ℕ := (NeO d n k).size

/-- `p = 10 ℓe + 16 ℓd + 160`. -/
def pK (d n k : ℕ) : ℕ := 10 * leK d n k + 16 * Bit.PieceA.ld d + 160

theorem parK_p (d n k : ℕ) : (parK d n k).p = pK d n k := rfl

theorem tp_eq (d n k : ℕ) : tp d n k = 1 / 2 ^ pK d n k := rfl

theorem eh_eq (d n k : ℕ) : eh d n k = 1 / 2 ^ (pK d n k - 3 * leK d n k - 6 * Bit.PieceA.ld d - 64) := by
  simp only [eh, parK, parN, pK, leK, Bit.PieceA.ld]
  push_cast
  rfl

theorem NeO_pos (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ NeO d n k := by
  unfold NeO
  have h1 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h2 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
  have h3 : 1 ≤ 2 ^ (17 + k) := Nat.one_le_two_pow
  calc 1 = 1 * 1 * 1 * 1 := by ring
    _ ≤ 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := by gcongr; norm_num

/-- `2^160 N^10 d^16 2^{-p} ≤ 1` at `p = 10 len N + 16 len d + 160`. -/
theorem gen_u (N d : ℕ) :
    (2 : ℝ) ^ 160 * (N : ℝ) ^ 10 * (d : ℝ) ^ 16 * (1 / 2 ^ (10 * N.size + 16 * d.size + 160)) ≤ 1 := by
  have hN : (N : ℝ) ≤ 2 ^ N.size := by exact_mod_cast (Nat.lt_size_self N).le
  have hd : (d : ℝ) ≤ 2 ^ d.size := by exact_mod_cast (Nat.lt_size_self d).le
  have h : (2 : ℝ) ^ (10 * N.size + 16 * d.size + 160) = (2 ^ N.size) ^ 10 * (2 ^ d.size) ^ 16 * 2 ^ 160 := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; ring_nf
  rw [h, mul_one_div, div_le_one (by positivity)]
  have h1 : (N : ℝ) ^ 10 ≤ (2 ^ N.size) ^ 10 := pow_le_pow_left₀ (by positivity) hN 10
  have h2 : (d : ℝ) ^ 16 ≤ (2 ^ d.size) ^ 16 := pow_le_pow_left₀ (by positivity) hd 16
  calc (2 : ℝ) ^ 160 * (N : ℝ) ^ 10 * (d : ℝ) ^ 16 ≤ 2 ^ 160 * (2 ^ N.size) ^ 10 * (2 ^ d.size) ^ 16 := by gcongr
    _ = _ := by ring

/-- The slack: `2^64 d^6 N³ 2^{-p} ≤ 2^{-(p - 3 len N - 6 len d - 64)} ≤ 2^73 d^6 N³ 2^{-p}`. -/
theorem gen_eh (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * (N : ℝ) ^ 3 * (1 / 2 ^ (10 * N.size + 16 * d.size + 160)) ≤
        1 / 2 ^ (10 * N.size + 16 * d.size + 160 - 3 * N.size - 6 * d.size - 64) ∧
      1 / (2 : ℝ) ^ (10 * N.size + 16 * d.size + 160 - 3 * N.size - 6 * d.size - 64) ≤
        (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * (N : ℝ) ^ 3 * (1 / 2 ^ (10 * N.size + 16 * d.size + 160)) := by
  set a := N.size with ha
  set b := d.size with hb
  have ha1 : 1 ≤ a := Nat.size_pos.mpr hN
  have hb1 : 1 ≤ b := Nat.size_pos.mpr hd
  have hNu : (N : ℝ) ≤ 2 ^ a := by exact_mod_cast (Nat.lt_size_self N).le
  have hdu : (d : ℝ) ≤ 2 ^ b := by exact_mod_cast (Nat.lt_size_self d).le
  have hNl : (2 : ℝ) ^ (a - 1) ≤ N := by exact_mod_cast Nat.lt_size.mp (by omega)
  have hdl : (2 : ℝ) ^ (b - 1) ≤ d := by exact_mod_cast Nat.lt_size.mp (by omega)
  have hsub : 10 * a + 16 * b + 160 - 3 * a - 6 * b - 64 = 7 * a + 10 * b + 96 := by omega
  rw [hsub]
  have e1 : (2 : ℝ) ^ (10 * a + 16 * b + 160) = 2 ^ (7 * a + 10 * b + 96) * (2 ^ a) ^ 3 * (2 ^ b) ^ 6 * 2 ^ 64 := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  have ea : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  have eb : (2 : ℝ) ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ']; congr 1; omega
  have hP : (0 : ℝ) < 2 ^ (7 * a + 10 * b + 96) := by positivity
  rw [e1]
  constructor
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) hP, one_mul]
    have h1 : (N : ℝ) ^ 3 ≤ (2 ^ a) ^ 3 := pow_le_pow_left₀ (by positivity) hNu 3
    have h2 : (d : ℝ) ^ 6 ≤ (2 ^ b) ^ 6 := pow_le_pow_left₀ (by positivity) hdu 6
    calc (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * (N : ℝ) ^ 3 * 2 ^ (7 * a + 10 * b + 96)
        ≤ 2 ^ 64 * (2 ^ b) ^ 6 * (2 ^ a) ^ 3 * 2 ^ (7 * a + 10 * b + 96) := by gcongr
      _ = _ := by ring
  · rw [mul_one_div, div_le_div_iff₀ hP (by positivity), one_mul, ea, eb]
    have h1 : (2 ^ (a - 1) : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hNl 3
    have h2 : (2 ^ (b - 1) : ℝ) ^ 6 ≤ (d : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) hdl 6
    calc 2 ^ (7 * a + 10 * b + 96) * (2 * 2 ^ (a - 1)) ^ 3 * (2 * 2 ^ (b - 1)) ^ 6 * (2 : ℝ) ^ 64
        = 2 ^ 73 * (2 ^ (b - 1)) ^ 6 * (2 ^ (a - 1)) ^ 3 * 2 ^ (7 * a + 10 * b + 96) := by ring
      _ ≤ 2 ^ 73 * (d : ℝ) ^ 6 * (N : ℝ) ^ 3 * 2 ^ (7 * a + 10 * b + 96) := by gcongr

/-- `2^{B/2} 2^{-p} = 4 · 2^{len(n(d + 2))} > 4 n (d + 2)`. -/
theorem t2_tpK (d n k : ℕ) : 4 * (n : ℝ) * ((d : ℝ) + 2) ≤ (2 : ℝ) ^ ((parK d n k).B / 2) * tp d n k := by
  have hB : (parK d n k).B / 2 = pK d n k + (n * (d + 2)).size + 2 := by
    show 2 * (pK d n k + (n * (d + 2)).size + 2) / 2 = _
    omega
  have hlt := Nat.lt_size_self (n * (d + 2))
  have hlt' : ((n * (d + 2) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n * (d + 2)).size := by
    exact_mod_cast hlt
  rw [hB, tp_eq, pow_add, pow_add]
  push_cast at hlt'
  have h2p : (0 : ℝ) < 2 ^ pK d n k := by positivity
  field_simp
  nlinarith

/-! ## The reference at `δ_BL = 2^{-19-k}/(dn)³` -/

theorem NeO_cast (d n k : ℕ) : (NeO d n k : ℝ) = 2 ^ k * Bit.PieceA.Ne d n := by
  unfold NeO Bit.PieceA.Ne Bit.PieceA.NeN; push_cast; ring

theorem Ne0_pos (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ Bit.PieceA.Ne d n := by
  have : 1 ≤ NeO d n 0 := NeO_pos d n 0 hd hn
  have h := NeO_cast d n 0
  rw [pow_zero, one_mul] at h
  rw [← h]; exact_mod_cast this

theorem Ne_ge0 (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Bit.PieceA.Ne d n ≤ Ne d n k := by
  show _ ≤ (NeO d n k : ℝ)
  rw [NeO_cast]
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h0 := Ne0_pos d n hd hn
  nlinarith

theorem deltaO_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : deltaO d n k ≤ Bit.Asm.deltaBL d n := by
  unfold deltaO Bit.Asm.deltaBL
  have h0 : (0 : ℝ) < ((d : ℝ) * n) ^ 3 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  apply div_le_div_of_nonneg_right _ h0.le
  rw [pow_add]
  have : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 19 := by positivity
  nlinarith

theorem deltaO_third_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    deltaO d n k / 3 ≤ Real.exp (-14) / ((d : ℝ) * n) ^ 3 :=
  le_trans (div_le_div_of_nonneg_right (deltaO_le d n k hd hn) (by norm_num))
    (Bit.PieceA.deltaBL_third_le d n hd hn)

theorem poK_de (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : (poK d n k).δe = 1 / Ne d n k := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [poK, AdversarialBco.Poly.df2oPar]
  rw [min_eq_left (deltaO_third_le d n k hd hn)]
  simp only [deltaO, Ne, NeO]
  push_cast
  rw [inv_pow]
  field_simp
  ring

theorem de_eq (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : de d n k = 1 / Ne d n k := poK_de d n k hd hn

theorem Le_eq (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Le d n k = 36 * Real.log (Ne d n k) := by
  have h : (poK d n k).Le = AdversarialBco.Poly.df2C0 * Real.log (1 / (poK d n k).δe) := rfl
  rw [Le, h, poK_de d n k hd hn, one_div_one_div, AdversarialBco.Poly.df2C0]

theorem lam_eq (d n k : ℕ) : lam d n k = 1 / (725 * d * Le d n k ^ 2) := by
  have h : (poK d n k).lam = 1 / (AdversarialBco.Poly.df2oClam * d * (poK d n k).Le ^ 2) := rfl
  rw [lam, h, ← Le, AdversarialBco.Poly.df2oClam]

theorem eta_eq (d n k : ℕ) : eta d n k = Real.sqrt d / (Le d n k * Real.sqrt n) := rfl

theorem eps_eq (d n k : ℕ) : eps d n k = 14500 * d * Real.sqrt d * Le d n k ^ 5 / Real.sqrt n := by
  have h : (poK d n k).eps =
      20 * AdversarialBco.Poly.df2oClam * (d * Real.sqrt d) * (poK d n k).Le ^ 5 / Real.sqrt n := rfl
  rw [eps, h, ← Le, AdversarialBco.Poly.df2oClam]
  ring

theorem rho_eq (d n k : ℕ) : rho d n k = 1450 * d ^ 2 * Le d n k ^ 3 := by
  have h : (poK d n k).rho = 2 * AdversarialBco.Poly.df2oClam * d ^ 2 * (poK d n k).Le ^ 3 := rfl
  rw [rho, h, ← Le, AdversarialBco.Poly.df2oClam]
  ring

theorem kc_eq (d n k : ℕ) : kc d n k = eta d n k * lam d n k / (4 * (1 - lam d n k) ^ 2) := by
  have hk : (poK d n k).kap = 1 / 4 := rfl
  have hk0 : (poK d n k).k0 = ((1 - (poK d n k).lam) ^ 2)⁻¹ := rfl
  rw [kc, hk, hk0, ← eta, ← lam, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem Le_ge0 (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Bit.PieceA.Le d n ≤ Le d n k := by
  rw [Le_eq d n k hd hn, Bit.PieceA.Le]
  have h0 : (0 : ℝ) < Bit.PieceA.Ne d n := lt_of_lt_of_le one_pos (Ne0_pos d n hd hn)
  have := Real.log_le_log h0 (Ne_ge0 d n k hd hn)
  linarith

theorem Le0_nonneg (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ Bit.PieceA.Le d n := by
  unfold Bit.PieceA.Le
  have := Real.log_nonneg (Ne0_pos d n hd hn)
  linarith

theorem eps_ge0 (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Bit.PieceA.eps d n ≤ eps d n k := by
  rw [eps_eq, Bit.PieceA.eps]
  have h0 := Le0_nonneg d n hd hn
  have h1 := Le_ge0 d n k hd hn
  have hn' : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  apply div_le_div_of_nonneg_right _ hn'.le
  have : Bit.PieceA.Le d n ^ 5 ≤ Le d n k ^ 5 := pow_le_pow_left₀ h0 h1 5
  have : (0 : ℝ) ≤ 14500 * d * Real.sqrt d := by positivity
  nlinarith

/-- From `ε ≤ 1/2`: `n ≥ 29000² d³ L^10`. -/
theorem n_ge_of_eps (d n : ℕ) (L : ℝ) (hn : 1 ≤ n) (h : 14500 * d * Real.sqrt d * L ^ 5 / Real.sqrt n ≤ 1 / 2)
    (hL : 0 ≤ L) : (29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * L ^ 10 ≤ n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have h2 : 29000 * (d : ℝ) * Real.sqrt d * L ^ 5 ≤ Real.sqrt n := by
    rw [div_le_iff₀ hs] at h; linarith
  have h0 : 0 ≤ 29000 * (d : ℝ) * Real.sqrt d * L ^ 5 := by positivity
  have hsq := pow_le_pow_left₀ h0 h2 2
  rw [Real.sq_sqrt hnpos.le] at hsq
  have e : (29000 * (d : ℝ) * Real.sqrt d * L ^ 5) ^ 2 = 29000 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 := by
    have : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
    calc (29000 * (d : ℝ) * Real.sqrt d * L ^ 5) ^ 2 = 29000 ^ 2 * (d : ℝ) ^ 2 * Real.sqrt d ^ 2 * L ^ 10 := by ring
      _ = _ := by rw [this]; ring
  linarith

/-! ## `Reg.OK` at `k` -/

/-- `Reg.OK` at BL-O's constants in the case `RunCaseK d n k`. -/
theorem reg_okK (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCaseK d n k) : (regK d n k).OK := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he4 : eps d n k ≤ 1 / 4 := h
  have he0 : Bit.PieceA.eps d n ≤ 1 / 2 := by linarith [eps_ge0 d n k hd hn]
  have hN0 := Ne_ge0 d n k hd hn
  have hN700 : (2 : ℝ) ^ 700 < Ne d n k := lt_of_lt_of_le (Bit.PieceA.regime_N hd hn he0) hN0
  have hNpos : (0 : ℝ) < Ne d n k := lt_trans (by positivity) hN700
  have hL1 : 17467 ≤ Le d n k :=
    le_trans (Bit.PieceA.regime_Le hd hn (Bit.PieceA.regime_N hd hn he0)) (Le_ge0 d n k hd hn)
  have hLpos : 0 ≤ Le d n k := by linarith
  have hnge : (29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n k ^ 10 ≤ n :=
    n_ge_of_eps d n (Le d n k) hn (by rw [← eps_eq]; linarith) hLpos
  have hNe : 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 ≤ Ne d n k := by
    refine le_trans (le_of_eq ?_) hN0
    unfold Bit.PieceA.Ne Bit.PieceA.NeN; push_cast; ring
  refine
    { hd := hd'
      hn := hn'
      hNe := hNe
      hde := de_eq d n k hd hn
      hLe := Le_eq d n k hd hn
      hlam := lam_eq d n k
      heta := eta_eq d n k
      heps := eps_eq d n k
      hrho := rho_eq d n k
      hkc := kc_eq d n k
      heps4 := he4
      hN700 := hN700
      hL1 := hL1
      hd15 := le_trans (Bit.PieceA.regime_d15 hd hn he0) hN0
      hn4 := le_trans (Bit.PieceA.regime_n4 hd) hN0
      hnge := hnge
      hL40 := ?_
      hQ0 := Real.rpow_pos_of_pos hNpos _
      hQ := ?_
      htp0 := by show (0 : ℝ) < tp d n k; rw [tp_eq]; positivity
      htp := ?_
      heh1 := ?_
      heh2 := ?_
      hR1 := Bit.PieceA.ref_R_lower hd
      hR2 := Bit.PieceA.ref_R_upper hd
      ht20 := by show (0 : ℝ) < 2 ^ ((parK d n k).B / 2); positivity
      ht2 := t2_tpK d n k }
  · show (10 * Le d n k) ^ 40 ≤ Ne d n k
    have h4 : ((29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n k ^ 10) ^ 4 ≤ (n : ℝ) ^ 4 := by gcongr
    have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 15 := one_le_pow₀ hd'
    have hL40 : 0 ≤ Le d n k ^ 40 := by positivity
    calc (10 * Le d n k) ^ 40 ≤ 15 * 2 ^ 17 * 29000 ^ 8 * Le d n k ^ 40 * (d : ℝ) ^ 15 := by
          rw [mul_pow]; nlinarith
      _ = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * ((29000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Le d n k ^ 10) ^ 4 := by ring
      _ ≤ 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by gcongr
      _ ≤ Ne d n k := hNe
  · show (Ne d n k ^ ((1 : ℝ) / 40)) ^ 40 = Ne d n k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
  · show (2 : ℝ) ^ 160 * Ne d n k ^ 10 * (d : ℝ) ^ 16 * tp d n k ≤ 1
    exact gen_u (NeO d n k) d
  · show (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Ne d n k ^ 3 * tp d n k ≤ eh d n k
    rw [eh_eq]; exact (gen_eh (NeO d n k) d (NeO_pos d n k hd hn) hd).1
  · show eh d n k ≤ (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Ne d n k ^ 3 * tp d n k
    rw [eh_eq]; exact (gen_eh (NeO d n k) d (NeO_pos d n k hd hn) hd).2

end AdversarialBco.Unified.BudK
