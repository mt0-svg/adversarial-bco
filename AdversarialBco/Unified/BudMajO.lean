/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudMaj

@[expose] public section

/-!
# Theorem BUD of BL-O: the majorants of the terms BL-O adds

Over a `Reg` with `Reg.OK` (Unified/BudReg.lean), the terms of the gauge band, the shift with the noise and the regret
transfer (`gb`, `band`, `S`, `kapO`, `regO`) are bounded by monomials `C d^a Q^b u` as in Unified/BudMaj.lean, and
with `2^k ≤ N_e` the budgets in `δ` hold: `2^{-p-2} ≤ 2^{-k}/8` (`bits_k`) and
`n (κ0 + κ1) ≤ 2^{-k}/8` (`kap_k`). This file depends on Mathlib only.
-/

namespace AdversarialBco.Unified.BudR.Reg.OK

open AdversarialBco.Unified.BudR AdversarialBco.Unified.BudR.Reg

variable {r : Reg}

theorem pibQ (h : r.OK) : 0 ≤ r.pib ∧ r.pib ≤ r.Q := by
  obtain ⟨-, hQL, -, -, -, -⟩ := h.Q_bd
  obtain ⟨-, -, hpib0, hpib⟩ := h.Pb_pib
  have hLe1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hL1
  have hsL : Real.sqrt r.Le ≤ r.Le := by
    have : Real.sqrt r.Le ≤ Real.sqrt (r.Le ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  exact ⟨hpib0, by linarith⟩

theorem gb_bd (h : r.OK) : 0 ≤ r.gb ∧ r.gb ≤ r.Q * r.tp := by
  obtain ⟨-, -, -, -, -, -, htp0, -⟩ := h.pos
  obtain ⟨hp0, hpQ⟩ := h.pibQ
  refine ⟨by unfold Reg.gb; positivity, ?_⟩
  unfold Reg.gb
  nlinarith

theorem band_bd (h : r.OK) : 0 ≤ r.band ∧ r.band ≤ 400 * r.d ^ 2 * r.Q ^ 7 * r.tp := by
  obtain ⟨hd0, -, -, -, he0, -, htp0, -⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  obtain ⟨hgb0, hgb⟩ := h.gb_bd
  obtain ⟨hp0, hpQ⟩ := h.pibQ
  obtain ⟨hRd, -⟩ := h.R_bd
  have hie := h.inv_eps
  have hR0 : 0 ≤ r.R := by linarith [h.hR1]
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hd1 : (1 : ℝ) ≤ r.d ^ 2 := one_le_pow₀ h.hd
  have hRp : r.R * r.pib + 4 ≤ 194 * r.d ^ 2 * r.Q := by
    have : r.R * r.pib ≤ 190 * r.d ^ 2 * r.Q := mul_le_mul hRd hpQ hp0 (by positivity)
    have : (4 : ℝ) ≤ 4 * r.d ^ 2 * r.Q := by nlinarith
    linarith
  have hfrac : (r.R * r.pib + 4) / r.eps ≤ 194 * r.d ^ 2 * r.Q * (r.Q ^ 5 / 72500) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hRp hie (by positivity) (by positivity)
  have hfac0 : 0 ≤ 2 + (r.R * r.pib + 4) / r.eps := by positivity
  have hQ6 : (1 : ℝ) ≤ r.Q ^ 6 := one_le_pow₀ hQ1
  have hfac : 2 + (r.R * r.pib + 4) / r.eps ≤ 4 * r.d ^ 2 * r.Q ^ 6 := by
    have e : 194 * r.d ^ 2 * r.Q * (r.Q ^ 5 / 72500) = 194 / 72500 * (r.d ^ 2 * r.Q ^ 6) := by ring
    have : (1 : ℝ) ≤ r.d ^ 2 * r.Q ^ 6 := by nlinarith
    nlinarith
  refine ⟨mul_nonneg hgb0 hfac0, ?_⟩
  unfold Reg.band
  calc r.gb * (2 + (r.R * r.pib + 4) / r.eps) ≤ (r.Q * r.tp) * (4 * r.d ^ 2 * r.Q ^ 6) :=
        mul_le_mul hgb hfac hfac0 (by positivity)
    _ = 4 * r.d ^ 2 * r.Q ^ 7 * r.tp := by ring
    _ ≤ 400 * r.d ^ 2 * r.Q ^ 7 * r.tp := by
        have : (0 : ℝ) ≤ r.d ^ 2 * r.Q ^ 7 * r.tp := by positivity
        nlinarith

theorem S_bd (h : r.OK) : 0 ≤ r.S ∧ r.S ≤ 52 * r.d ^ 4 * r.Q ^ 77 * r.tp := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  obtain ⟨hXb0, hXb, -, -⟩ := h.Xb_Du
  obtain ⟨hp0, hpQ⟩ := h.pibQ
  obtain ⟨hRd, -⟩ := h.R_bd
  have hie := h.inv_eps
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hQ5 : (2 : ℝ) ^ 85 ≤ r.Q ^ 5 := by
    calc (2 : ℝ) ^ 85 = (2 ^ 17) ^ 5 := by rw [← pow_mul]
      _ ≤ r.Q ^ 5 := pow_le_pow_left₀ (by norm_num) hQ17 5
  have h16 : 2 + 16 / r.eps ≤ r.Q ^ 5 := by
    have : 16 / r.eps = 16 * (1 / r.eps) := by ring
    rw [this]; nlinarith
  have h16' : 0 ≤ 2 + 16 / r.eps := by positivity
  have hR10 : r.R + 10 ≤ 200 * r.d ^ 2 := by
    have : (1 : ℝ) ≤ r.d ^ 2 := one_le_pow₀ hd
    linarith
  have hmpar : r.mpar ≤ 50 * r.d ^ 2 * r.Q ^ 6 * r.tp := by
    simp only [Reg.mpar]
    have e : r.tp / 4 * r.pib * (r.R + 10) / r.eps = r.tp / 4 * r.pib * (r.R + 10) * (1 / r.eps) := by ring
    rw [e]
    calc r.tp / 4 * r.pib * (r.R + 10) * (1 / r.eps) ≤ r.tp / 4 * r.Q * (200 * r.d ^ 2) * (r.Q ^ 5 / 72500) := by
          have : 0 ≤ r.R + 10 := by linarith [h.hR1]
          gcongr
      _ ≤ 50 * r.d ^ 2 * r.Q ^ 6 * r.tp := by
          have : (0 : ℝ) ≤ r.d ^ 2 * r.Q ^ 6 * r.tp := by positivity
          nlinarith
  have hmpar0 : 0 ≤ r.mpar := by
    simp only [Reg.mpar]; have : 0 ≤ r.R + 10 := by linarith [h.hR1]
    positivity
  have hX : (2 + 16 / r.eps) * r.Xb ≤ r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) :=
    mul_le_mul h16 hXb hXb0 (by positivity)
  have hd24 : r.d ^ 2 * r.Q ^ 6 ≤ r.d ^ 4 * r.Q ^ 77 :=
    mul_le_mul (pow_le_pow_right₀ hd (by norm_num)) (pow_le_pow_right₀ hQ1 (by norm_num)) (by positivity)
      (by positivity)
  refine ⟨by unfold Reg.S; positivity, ?_⟩
  unfold Reg.S
  have e : r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) = 2 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by ring
  have : r.d ^ 2 * r.Q ^ 6 * r.tp ≤ r.d ^ 4 * r.Q ^ 77 * r.tp := mul_le_mul_of_nonneg_right hd24 htp0.le
  nlinarith

theorem kapO_bd (h : r.OK) : 0 ≤ r.kapO ∧ r.kapO ≤ 1000 * r.d ^ 4 * r.Q ^ 77 * r.tp := by
  obtain ⟨-, -, -, -, -, -, htp0, -⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  obtain ⟨hS0, hS⟩ := h.S_bd
  obtain ⟨hb0, hb⟩ := h.band_bd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hd27 : r.d ^ 2 * r.Q ^ 7 ≤ r.d ^ 4 * r.Q ^ 77 :=
    mul_le_mul (pow_le_pow_right₀ h.hd (by norm_num)) (pow_le_pow_right₀ hQ1 (by norm_num)) (by positivity)
      (by positivity)
  have : r.d ^ 2 * r.Q ^ 7 * r.tp ≤ r.d ^ 4 * r.Q ^ 77 * r.tp := mul_le_mul_of_nonneg_right hd27 htp0.le
  refine ⟨by unfold Reg.kapO; positivity, ?_⟩
  unfold Reg.kapO
  nlinarith

theorem S_le (h : r.OK) : r.S + r.band ≤ 1 / 4 := by
  obtain ⟨-, -, -, -, -, -, htp0, -⟩ := h.pos
  obtain ⟨hk0, hk⟩ := h.kapO_bd
  have t := h.tiny 4 77 (by norm_num) (by norm_num)
  have e : r.kapO = 2 * (r.S + r.band) := rfl
  have : (1000 : ℝ) / 2 ^ 160 ≤ 1 / 2 := by norm_num
  nlinarith

theorem bits_k (h : r.OK) {K2 : ℝ} (hK0 : 0 < K2) (hK : K2 ≤ r.Ne) : r.dbits ≤ 1 / K2 / 8 := by
  obtain ⟨-, -, hN0, -, -, -, htp0, -⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  have t := h.tiny 0 40 (by norm_num) (by norm_num)
  rw [pow_zero, one_mul, h.hQ] at t
  unfold Reg.dbits
  rw [div_div, le_div_iff₀ (by positivity)]
  have h1 : r.tp * K2 ≤ r.tp * r.Ne := mul_le_mul_of_nonneg_left hK htp0.le
  have : (8 : ℝ) / 2 ^ 160 ≤ 4 := by norm_num
  nlinarith

theorem kap_k (h : r.OK) {K2 : ℝ} (hK0 : 0 < K2) (hK : K2 ≤ r.Ne) : r.n * (r.kapO + r.kapO) ≤ 1 / K2 / 8 := by
  obtain ⟨-, hn0, hN0, -, -, -, htp0, -⟩ := h.pos
  obtain ⟨hQ17, -, hQn, -, -, -⟩ := h.Q_bd
  obtain ⟨hk0, hk⟩ := h.kapO_bd
  have t := h.tiny 4 127 (by norm_num) (by norm_num)
  have hn : r.n ≤ r.Q ^ 10 := by
    have : (0 : ℝ) ≤ r.Q ^ 10 := by positivity
    linarith
  have hQ : r.Q ^ 40 = r.Ne := h.hQ
  rw [div_div, le_div_iff₀ (by positivity)]
  have h1 : r.n * (r.kapO + r.kapO) ≤ r.Q ^ 10 * (2000 * r.d ^ 4 * r.Q ^ 77 * r.tp) :=
    mul_le_mul hn (by linarith) (by linarith) (by positivity)
  have h2 : r.n * (r.kapO + r.kapO) * (K2 * 8) ≤ r.Q ^ 10 * (2000 * r.d ^ 4 * r.Q ^ 77 * r.tp) * (r.Q ^ 40 * 8) := by
    rw [hQ]
    exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)
  have e : r.Q ^ 10 * (2000 * r.d ^ 4 * r.Q ^ 77 * r.tp) * (r.Q ^ 40 * 8) = 16000 * (r.d ^ 4 * r.Q ^ 127 * r.tp) := by
    ring
  have : (16000 : ℝ) / 2 ^ 160 ≤ 1 := by norm_num
  nlinarith

theorem regO_le (h : r.OK) : r.regO ≤ 1 := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, -, hQn, -, -, -⟩ := h.Q_bd
  obtain ⟨hXb0, hXb, -, -⟩ := h.Xb_Du
  obtain ⟨hp0, hpQ⟩ := h.pibQ
  obtain ⟨hRd, -⟩ := h.R_bd
  obtain ⟨hgb0, hgb⟩ := h.gb_bd
  obtain ⟨-, -, hwe0, hwe⟩ := h.wr_we
  have hie := h.inv_eps
  have hd := h.hd
  have hR0 : 0 ≤ r.R := by linarith [h.hR1]
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hne : r.n / r.eps ≤ r.Q ^ 15 := by
    have hn_le : r.n ≤ r.Q ^ 10 / 32 := by linarith
    calc r.n / r.eps = r.n * (1 / r.eps) := by ring
      _ ≤ (r.Q ^ 10 / 32) * (r.Q ^ 5 / 72500) := mul_le_mul hn_le hie (by positivity) (by positivity)
      _ = r.Q ^ 15 / (32 * 72500) := by ring
      _ ≤ r.Q ^ 15 := div_le_self (by positivity) (by norm_num)
  have hd2 : (1 : ℝ) ≤ r.d ^ 2 := one_le_pow₀ hd
  have hd26 : r.d ^ 2 ≤ r.d ^ 6 := pow_le_pow_right₀ hd (by norm_num)
  have hQ72 : r.Q ≤ r.Q ^ 72 := le_self_pow₀ hQ1 (by norm_num)
  have h1 : (1 + 2 * r.R) * r.Xb ≤ 381 * r.d ^ 2 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) :=
    mul_le_mul (by linarith) hXb hXb0 (by positivity)
  have h2 : 4 * r.R * r.pib * r.we ≤ 4 * (190 * r.d ^ 2) * r.Q * (r.tp / 64) := by gcongr
  have h3 : r.R * r.gb ≤ 190 * r.d ^ 2 * (r.Q * r.tp) := mul_le_mul hRd hgb hgb0 (by positivity)
  have hdQ : r.d ^ 2 * r.Q * r.tp ≤ r.d ^ 6 * r.Q ^ 72 * r.tp :=
    mul_le_mul_of_nonneg_right (mul_le_mul hd26 hQ72 (by positivity) (by positivity)) htp0.le
  have hsum : (1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we + r.R * r.gb ≤ 2000 * (r.d ^ 6 * r.Q ^ 72 * r.tp) := by
    nlinarith
  have hsum0 : 0 ≤ (1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we + r.R * r.gb := by positivity
  have t := h.tiny 6 87 (by norm_num) (by norm_num)
  unfold Reg.regO
  calc r.n / r.eps * ((1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we + r.R * r.gb)
      ≤ r.Q ^ 15 * (2000 * (r.d ^ 6 * r.Q ^ 72 * r.tp)) := mul_le_mul hne hsum hsum0 (by positivity)
    _ = 2000 * (r.d ^ 6 * r.Q ^ 87 * r.tp) := by ring
    _ ≤ 2000 * (1 / 2 ^ 160) := by gcongr
    _ ≤ 1 := by norm_num

end AdversarialBco.Unified.BudR.Reg.OK
