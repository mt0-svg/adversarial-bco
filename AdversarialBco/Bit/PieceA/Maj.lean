/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Reg

@[expose] public section

/-!
# Piece A: the majorants of the precision theorem over a `Reg`

Under `Reg.OK`, every constant is bounded by a monomial `C d^a Q^b u` (`u = 2^{-p}`,
`Q = N_e^{1/40}`), coarser than the table of 5.2 but enough: `u ≤ 2^{-160} Q^{-400} d^{-16}` (`tp_le`) makes every
condition of the precision theorem that does not involve the slack `ê` hold with room (`tiny`), and the conditions on
`ê` keep
the factor `d^6` of `ê ≥ 2^64 d^6 Q^120 u` (slack, `ePhi_le_eh`, `eX_le_eh`) or the exact powers of `R` and `d`
(SEL, `sel_le`: `64.16 R^4 (R + 1)^2 ≤ 3 · 2^87 d^9`). This file depends on Mathlib only.
-/

namespace AdversarialBco.Bit.PieceA.Reg.OK

open AdversarialBco.Bit.PieceA AdversarialBco.Bit.PieceA.Reg

variable {r : Reg}

/-! ## The base constants -/

theorem pos (h : r.OK) : 0 < r.d ∧ 0 < r.n ∧ 0 < r.Ne ∧ 0 < r.Le ∧ 0 < r.eps ∧ 0 < r.de ∧ 0 < r.tp ∧ 0 < r.eh := by
  have hd_pos : 0 < r.d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hd
  have hn_pos : 0 < r.n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hn
  have hNe_pos : 0 < r.Ne := lt_trans (by norm_num : (0 : ℝ) < 2 ^ 700) h.hN700
  have hLe_pos : 0 < r.Le := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17467) h.hL1
  have heps_pos : 0 < r.eps := by
    rw [h.heps]
    positivity
  have hde_pos : 0 < r.de := by
    rw [h.hde]
    positivity
  have htp_pos : 0 < r.tp := h.htp0
  have hpos : 0 < 2 ^ 64 * r.d ^ 6 * r.Ne ^ 3 * r.tp := by positivity
  have heh_pos : 0 < r.eh := lt_of_lt_of_le hpos h.heh1
  exact ⟨hd_pos, hn_pos, hNe_pos, hLe_pos, heps_pos, hde_pos, htp_pos, heh_pos⟩

theorem Q_bd (h : r.OK) : 2 ^ 17 ≤ r.Q ∧ 10 * r.Le ≤ r.Q ∧ 32 * r.n ≤ r.Q ^ 10 ∧ r.d ^ 3 ≤ r.Q ^ 8 ∧
    Real.sqrt r.n ≤ r.Q ^ 5 ∧ r.d ≤ r.Q ^ 3 := by
  have hQpos : 0 ≤ r.Q := by linarith [h.hQ0]
  have hQpos' : 0 < r.Q := h.hQ0
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have hn_nonneg : 0 ≤ r.n := by linarith [h.hn]
  have hLe_nonneg : 0 ≤ r.Le := by linarith [h.hL1]
  have h10Le_nonneg : 0 ≤ 10 * r.Le := by nlinarith
  have h32n_nonneg : 0 ≤ 32 * r.n := by nlinarith
  have hd3_nonneg : 0 ≤ r.d ^ 3 := by
    positivity
  have hQ8_nonneg : 0 ≤ r.Q ^ 8 := by
    positivity
  have hQ10_nonneg : 0 ≤ r.Q ^ 10 := by
    positivity
  have hQ3_nonneg : 0 ≤ r.Q ^ 3 := by
    positivity
  have hQ5_nonneg : 0 ≤ r.Q ^ 5 := by
    positivity
  have h_one_le_Q : 1 ≤ r.Q := by
    have hQ40_gt_one : (1 : ℝ) < r.Q ^ 40 := by
      rw [h.hQ]
      have h_one_lt_two_pow_700 : (1 : ℝ) < (2 : ℝ) ^ 700 := by
        have h_nat : 1 < (2 : ℕ) ^ 700 :=
          Nat.one_lt_pow (by norm_num : 700 ≠ 0) (by norm_num : 1 < 2)
        exact_mod_cast h_nat
      exact lt_trans h_one_lt_two_pow_700 h.hN700
    have h_one_pow_lt : (1 : ℝ) ^ 40 < r.Q ^ 40 := by
      simpa [one_pow] using hQ40_gt_one
    have h := (pow_lt_pow_iff_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hQpos (by norm_num : (40 : ℕ) ≠ 0)).mp
    exact le_of_lt (h h_one_pow_lt)
  -- (1) 2^17 ≤ Q
  have h1 : 2 ^ 17 ≤ r.Q := by
    have h_pow_lt : (2 ^ 17) ^ 40 < r.Q ^ 40 := by
      calc
        (2 ^ 17) ^ 40 = (2 : ℝ) ^ (17 * 40) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (680 : ℕ) := by norm_num
        _ < (2 : ℝ) ^ (700 : ℕ) := by
          have h_nat : (2 : ℕ) ^ (680 : ℕ) < (2 : ℕ) ^ (700 : ℕ) :=
            Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by decide : (680 : ℕ) < 700)
          exact_mod_cast h_nat
        _ = (2 : ℝ) ^ 700 := by norm_num
        _ < r.Ne := h.hN700
        _ = r.Q ^ 40 := by rw [h.hQ]
    have h_nonneg_2pow : 0 ≤ (2 : ℝ) ^ 17 := by positivity
    have h_40_ne_zero : (40 : ℕ) ≠ 0 := by norm_num
    have h_lt : (2 : ℝ) ^ 17 < r.Q :=
      ((pow_lt_pow_iff_left₀ h_nonneg_2pow hQpos h_40_ne_zero).mp h_pow_lt)
    linarith
  -- (2) 10 * Le ≤ Q
  have h2 : 10 * r.Le ≤ r.Q := by
    have h_pow_le : (10 * r.Le) ^ 40 ≤ r.Q ^ 40 := by
      calc
        (10 * r.Le) ^ 40 ≤ r.Ne := h.hL40
        _ = r.Q ^ 40 := by rw [h.hQ]
    have h_40_ne_zero : (40 : ℕ) ≠ 0 := by norm_num
    exact ((pow_le_pow_iff_left₀ h10Le_nonneg hQpos h_40_ne_zero).mp h_pow_le)
  -- (3) 32 * n ≤ Q^10
  have h3 : 32 * r.n ≤ r.Q ^ 10 := by
    have h_pow_le : (32 * r.n) ^ 4 ≤ (r.Q ^ 10) ^ 4 := by
      calc
        (32 * r.n) ^ 4 = 32 ^ 4 * r.n ^ 4 := by ring
        _ ≤ r.Ne := h.hn4
        _ = r.Q ^ 40 := by rw [h.hQ]
        _ = (r.Q ^ 10) ^ 4 := by rw [← pow_mul, show (10 : ℕ) * 4 = 40 by norm_num]
    have h_4_ne_zero : (4 : ℕ) ≠ 0 := by norm_num
    exact ((pow_le_pow_iff_left₀ h32n_nonneg hQ10_nonneg h_4_ne_zero).mp h_pow_le)
  -- (4) d^3 ≤ Q^8
  have h4 : r.d ^ 3 ≤ r.Q ^ 8 := by
    have h_pow_le : (r.d ^ 3) ^ 5 ≤ (r.Q ^ 8) ^ 5 := by
      calc
        (r.d ^ 3) ^ 5 = r.d ^ (3 * 5) := by rw [pow_mul]
        _ = r.d ^ 15 := by norm_num
        _ ≤ r.Ne := h.hd15
        _ = r.Q ^ 40 := by rw [h.hQ]
        _ = (r.Q ^ 8) ^ 5 := by rw [← pow_mul, show (8 : ℕ) * 5 = 40 by norm_num]
    have h_5_ne_zero : (5 : ℕ) ≠ 0 := by norm_num
    exact ((pow_le_pow_iff_left₀ hd3_nonneg hQ8_nonneg h_5_ne_zero).mp h_pow_le)
  -- (5) √n ≤ Q^5
  have h5 : Real.sqrt r.n ≤ r.Q ^ 5 := by
    have hn_le_Q10 : r.n ≤ r.Q ^ 10 := by
      -- from h3: 32*n ≤ Q^10, so n ≤ Q^10/32 ≤ Q^10
      have h := h3
      linarith
    have h_sqrt_n_le_sqrt_Q10 : Real.sqrt r.n ≤ Real.sqrt (r.Q ^ 10) :=
      Real.sqrt_le_sqrt hn_le_Q10
    have h_sqrt_Q10_eq_Q5 : Real.sqrt (r.Q ^ 10) = r.Q ^ 5 := by
      calc
        Real.sqrt (r.Q ^ 10) = Real.sqrt ((r.Q ^ 5) ^ 2) := by
          rw [← pow_mul, show (5 : ℕ) * 2 = 10 by norm_num]
        _ = r.Q ^ 5 := Real.sqrt_sq hQ5_nonneg
    rw [h_sqrt_Q10_eq_Q5] at h_sqrt_n_le_sqrt_Q10
    exact h_sqrt_n_le_sqrt_Q10
  -- (6) d ≤ Q^3
  have h6 : r.d ≤ r.Q ^ 3 := by
    have h_d3_le_Q9 : r.d ^ 3 ≤ (r.Q ^ 3) ^ 3 := by
      calc
        r.d ^ 3 ≤ r.Q ^ 8 := h4
        _ ≤ r.Q ^ 9 := by
          have : r.Q ^ 8 * 1 ≤ r.Q ^ 8 * r.Q := by
            nlinarith [h_one_le_Q]
          calc
            r.Q ^ 8 = r.Q ^ 8 * 1 := by ring
            _ ≤ r.Q ^ 8 * r.Q := this
            _ = r.Q ^ 9 := by ring
        _ = (r.Q ^ 3) ^ 3 := by rw [← pow_mul, show (3 : ℕ) * 3 = 9 by norm_num]
    have h_3_ne_zero : (3 : ℕ) ≠ 0 := by norm_num
    exact ((pow_le_pow_iff_left₀ hd_nonneg hQ3_nonneg h_3_ne_zero).mp h_d3_le_Q9)
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 h6))))

theorem tp_le (h : r.OK) : r.tp ≤ 1 / (2 ^ 160 * r.Q ^ 400 * r.d ^ 16) := by
  have hpos : 0 < 2 ^ 160 * r.Q ^ 400 * r.d ^ 16 := by
    have hdpos : 0 < r.d := by
      have h01 : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le h01 h.hd
    have hQpos : 0 < r.Q := h.hQ0
    have h2pos : 0 < (2 : ℝ) ^ 160 := by norm_num
    have hQpow : 0 < r.Q ^ 400 := pow_pos hQpos 400
    have hdpow : 0 < r.d ^ 16 := pow_pos hdpos 16
    apply mul_pos
    · apply mul_pos
      · exact h2pos
      · exact hQpow
    · exact hdpow
  have hQ400 : r.Q ^ 400 = (r.Q ^ 40) ^ 10 := by
    calc
      r.Q ^ 400 = r.Q ^ (40 * 10) := by ring
      _ = (r.Q ^ 40) ^ 10 := by rw [pow_mul]
  have hineq : r.tp * (2 ^ 160 * r.Q ^ 400 * r.d ^ 16) ≤ 1 := by
    calc
      r.tp * (2 ^ 160 * r.Q ^ 400 * r.d ^ 16) = 2 ^ 160 * r.Q ^ 400 * r.d ^ 16 * r.tp := by ring
      _ = 2 ^ 160 * ((r.Q ^ 40) ^ 10) * r.d ^ 16 * r.tp := by rw [hQ400]
      _ = 2 ^ 160 * r.Ne ^ 10 * r.d ^ 16 * r.tp := by rw [h.hQ]
      _ ≤ 1 := h.htp
  rw [le_div_iff₀ hpos]
  exact hineq

/-- The scale of every `u`-small condition. -/
theorem tiny (h : r.OK) (a b : ℕ) (ha : a ≤ 16) (hb : b ≤ 400) : r.d ^ a * r.Q ^ b * r.tp ≤ 1 / 2 ^ 160 := by
  have hQ_ge_one : 1 ≤ r.Q := by
    have hQ_bd := Q_bd h
    have h2pow : (2 : ℝ) ^ 17 ≤ r.Q := hQ_bd.1
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ 17 := by norm_num
    exact le_trans hone h2pow
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num : (0 : ℝ) ≤ 1) h.hd
  have hQ_nonneg : 0 ≤ r.Q := le_of_lt h.hQ0
  have hd_pow : r.d ^ a ≤ r.d ^ 16 := pow_le_pow_right₀ h.hd ha
  have hQ_pow : r.Q ^ b ≤ r.Q ^ 400 := pow_le_pow_right₀ hQ_ge_one hb
  have hNe_eq : r.Ne ^ 10 = r.Q ^ 400 := by
    calc
      r.Ne ^ 10 = (r.Q ^ 40) ^ 10 := by rw [h.hQ]
      _ = r.Q ^ (40 * 10) := by rw [pow_mul]
      _ = r.Q ^ 400 := by norm_num
  have hpos : 0 < (2 : ℝ) ^ 160 := by norm_num
  have htp_bound : r.d ^ 16 * r.Q ^ 400 * r.tp ≤ 1 / (2 : ℝ) ^ 160 := by
    have h1 : (2 : ℝ) ^ 160 * r.Q ^ 400 * r.d ^ 16 * r.tp ≤ 1 := by
      calc
        (2 : ℝ) ^ 160 * r.Q ^ 400 * r.d ^ 16 * r.tp = (2 : ℝ) ^ 160 * r.Ne ^ 10 * r.d ^ 16 * r.tp := by rw [hNe_eq]
        _ ≤ 1 := h.htp
    have h1' : (r.d ^ 16 * r.Q ^ 400 * r.tp) * (2 : ℝ) ^ 160 ≤ 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1
    exact (le_div_iff₀ hpos).mpr h1'
  have htp_nonneg : 0 ≤ r.tp := le_of_lt h.htp0
  calc
    r.d ^ a * r.Q ^ b * r.tp ≤ r.d ^ 16 * r.Q ^ 400 * r.tp := by
      have h1 : r.d ^ a * r.Q ^ b ≤ r.d ^ 16 * r.Q ^ 400 :=
        mul_le_mul hd_pow hQ_pow (pow_nonneg hQ_nonneg b) (pow_nonneg hd_nonneg 16)
      exact mul_le_mul_of_nonneg_right h1 htp_nonneg
    _ ≤ 1 / (2 : ℝ) ^ 160 := htp_bound

theorem eh_bd (h : r.OK) : 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp ≤ r.eh ∧ r.eh ≤ 1 / (2 ^ 87 * r.Q ^ 280 * r.d ^ 10) := by
  have hpos_d : 0 < r.d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hd
  have hpos_Q : 0 < r.Q := h.hQ0
  have hpos_tp : 0 < r.tp := h.htp0
  have hNe3_eq_Q120 : r.Ne ^ 3 = r.Q ^ 120 := by
    calc
      r.Ne ^ 3 = (r.Q ^ 40) ^ 3 := by rw [← h.hQ]
      _ = r.Q ^ 120 := by ring
  have htp_le := tp_le h
  constructor
  · -- left inequality
    calc
      2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp = 2 ^ 64 * r.d ^ 6 * (r.Ne ^ 3) * r.tp := by rw [hNe3_eq_Q120]
      _ ≤ r.eh := h.heh1
  · -- right inequality
    have h_nonneg : 0 ≤ 2 ^ 73 * r.d ^ 6 * r.Q ^ 120 := by positivity
    calc
      r.eh ≤ 2 ^ 73 * r.d ^ 6 * r.Ne ^ 3 * r.tp := h.heh2
      _ = 2 ^ 73 * r.d ^ 6 * (r.Q ^ 120) * r.tp := by rw [hNe3_eq_Q120]
      _ = (2 ^ 73 * r.d ^ 6 * r.Q ^ 120) * r.tp := by ring
      _ ≤ (2 ^ 73 * r.d ^ 6 * r.Q ^ 120) * (1 / (2 ^ 160 * r.Q ^ 400 * r.d ^ 16)) := by
        gcongr
      _ = 1 / (2 ^ 87 * r.Q ^ 280 * r.d ^ 10) := by
        field_simp

theorem sqrtL_ge (h : r.OK) : 132 ≤ Real.sqrt r.Le := by
  have hsq : (132 : ℝ)^2 ≤ r.Le := by
    have h132sq : (132 : ℝ)^2 = 17424 := by norm_num
    have h17424_17467 : (17424 : ℝ) ≤ 17467 := by norm_num
    have h17467_Le : (17467 : ℝ) ≤ r.Le := h.hL1
    calc
      (132 : ℝ)^2 = 17424 := h132sq
      _ ≤ 17467 := h17424_17467
      _ ≤ r.Le := h17467_Le
  have h132pos : (0 : ℝ) ≤ 132 := by norm_num
  calc
    (132 : ℝ) = Real.sqrt ((132 : ℝ)^2) := by rw [Real.sqrt_sq h132pos]
    _ ≤ Real.sqrt r.Le := Real.sqrt_le_sqrt hsq

theorem sqrt_d_le (h : r.OK) : 1 ≤ Real.sqrt r.d ∧ Real.sqrt r.d ≤ r.d := by
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num) h.hd
  have h1 : 1 ≤ Real.sqrt r.d := by
    calc
      1 = Real.sqrt 1 := by rw [Real.sqrt_one]
      _ ≤ Real.sqrt r.d := Real.sqrt_le_sqrt h.hd
  have h2 : Real.sqrt r.d ≤ r.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hd_nonneg
    · calc
        r.d = r.d * 1 := by ring
        _ ≤ r.d * r.d := mul_le_mul_of_nonneg_left h.hd hd_nonneg
        _ = r.d ^ 2 := by ring
  exact And.intro h1 h2

theorem lam_bd (h : r.OK) : 0 < r.lam ∧ r.lam ≤ 1 / (725 * 17467 ^ 2) := by
  rcases h with ⟨hd, hn, hNe, hde, hLe, hlam, heta, heps, hrho, hkc, heps4, hN700, hL1, hd15, hn4, hnge, hL40, hQ0, hQ, htp0, htp, heh1, heh2, hR1, hR2, ht20, ht2⟩
  have hpos_denom : 0 < 725 * r.d * r.Le ^ 2 := by
    have hdpos : 0 < r.d := by linarith
    have hLpos : 0 < r.Le := by linarith
    positivity
  have hpos_ref : 0 < 725 * (17467 : ℝ) ^ 2 := by
    norm_num
  have hle_denom : 725 * (17467 : ℝ) ^ 2 ≤ 725 * r.d * r.Le ^ 2 := by
    nlinarith
  have hpos_lam : 0 < r.lam := by
    rw [hlam]
    exact (one_div_pos.mpr hpos_denom)
  have hle_lam : r.lam ≤ 1 / (725 * 17467 ^ 2) := by
    rw [hlam]
    exact (one_div_le_one_div_of_le hpos_ref hle_denom)
  exact And.intro hpos_lam hle_lam

theorem eta_bd (h : r.OK) : 0 < r.eta ∧ r.eta ≤ 1 := by
  rcases h with ⟨hd, hn, hNe, hde, hLe, hlam, heta, heps, hrho, hkc, heps4, hN700, hL1, hd15, hn4, hnge, hL40, hQ0, hQ, htp0, htp, heh1, heh2, hR1, hR2, ht20, ht2⟩
  have hdpos : 0 < r.d := by linarith
  have hnpos : 0 < r.n := by linarith
  have hsqrtdpos : 0 < Real.sqrt r.d := Real.sqrt_pos.mpr hdpos
  have hsqrtnpos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr hnpos
  have hLpos : 0 < r.Le := by linarith
  have hLe1 : 1 ≤ r.Le := by linarith
  have hd_le_n : r.d ≤ r.n := by
    have hsq : 1 ≤ r.d ^ 2 := by nlinarith
    have hLe10 : 1 ≤ r.Le ^ 10 := by
      have hLe0 : 0 ≤ r.Le := by linarith
      exact ((one_le_pow_iff_of_nonneg hLe0 (by norm_num : (10 : ℕ) ≠ 0)).mpr hLe1)
    have hfactor : 1 ≤ 29000 ^ 2 * r.d ^ 2 * r.Le ^ 10 := by
      have h29000sq : 1 ≤ (29000 : ℝ) ^ 2 := by norm_num
      nlinarith
    have hineq : r.d ≤ 29000 ^ 2 * r.d ^ 3 * r.Le ^ 10 := by
      calc
        r.d = r.d * 1 := by ring
        _ ≤ r.d * (29000 ^ 2 * r.d ^ 2 * r.Le ^ 10) := by
          nlinarith
        _ = 29000 ^ 2 * r.d ^ 3 * r.Le ^ 10 := by ring
    linarith
  have hsqrtd_le_sqrtn : Real.sqrt r.d ≤ Real.sqrt r.n :=
    Real.sqrt_le_sqrt hd_le_n
  have hpos : 0 < r.eta := by
    rw [heta]
    exact div_pos hsqrtdpos (mul_pos hLpos hsqrtnpos)
  have hle1 : r.eta ≤ 1 := by
    rw [heta]
    have hdiv1 : Real.sqrt r.d / (r.Le * Real.sqrt r.n) ≤ Real.sqrt r.d / Real.sqrt r.n :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hsqrtnpos (by
        nlinarith)
    have hdiv2 : Real.sqrt r.d / Real.sqrt r.n ≤ 1 :=
      (div_le_one hsqrtnpos).mpr hsqrtd_le_sqrtn
    linarith
  exact And.intro hpos hle1

theorem inv_eps (h : r.OK) : 1 / r.eps ≤ r.Q ^ 5 / 72500 := by
  have hQ_bd := OK.Q_bd h
  rcases hQ_bd with ⟨hQ17, hQLe, h32n, hdQ8, hsqrt_n_le, hd_le⟩
  have hQpos : 0 < r.Q := by linarith
  have hQ_nonneg : 0 ≤ r.Q := by linarith
  have hsqrt_d_le := OK.sqrt_d_le h
  rcases hsqrt_d_le with ⟨hsqrt_d_ge1, hsqrt_d_le_d⟩
  have hd_ge1 : 1 ≤ r.d := h.hd
  have hLe_ge1 : 1 ≤ r.Le := le_trans (by norm_num : (1 : ℝ) ≤ 17467) h.hL1
  have h_sqrt_n_nonneg : 0 ≤ Real.sqrt r.n := Real.sqrt_nonneg _
  have hQ_pow_nonneg : 0 ≤ r.Q ^ 10 := by positivity
  have h_denom_pos : 0 < 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by positivity
  have h_14500_pos : 0 < (14500 : ℝ) := by norm_num
  have hLe5_ge1 : 1 ≤ r.Le ^ 5 := one_le_pow₀ hLe_ge1 (n := 5)
  have h_denom_ge_14500 : 14500 ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by
    have hprod : 1 ≤ r.d * Real.sqrt r.d * r.Le ^ 5 := by
      have hd_nonneg : 0 ≤ r.d := by linarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt r.d := Real.sqrt_nonneg _
      have hLe5_nonneg : 0 ≤ r.Le ^ 5 := by positivity
      have h12 : (1 : ℝ) * 1 ≤ r.d * Real.sqrt r.d :=
        mul_le_mul hd_ge1 hsqrt_d_ge1 (by norm_num) hd_nonneg
      have h123 : ((1 : ℝ) * 1) * 1 ≤ (r.d * Real.sqrt r.d) * r.Le ^ 5 :=
        mul_le_mul h12 hLe5_ge1 (by norm_num) (by positivity)
      linarith
    nlinarith
  have h_one_div : 1 / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) ≤ 1 / (14500 : ℝ) := by
    exact ((one_div_le_one_div h_denom_pos h_14500_pos).mpr h_denom_ge_14500)
  have hn_le : r.n ≤ r.Q ^ 10 / 25 := by
    have h : r.n ≤ r.Q ^ 10 / 32 := by linarith
    have hdiv : r.Q ^ 10 / 32 ≤ r.Q ^ 10 / 25 := by
      calc
        r.Q ^ 10 / 32 = r.Q ^ 10 * ((1 : ℝ) / 32) := by ring
        _ ≤ r.Q ^ 10 * ((1 : ℝ) / 25) := by
          have h32_25 : (1 : ℝ) / 32 ≤ (1 : ℝ) / 25 := by norm_num
          nlinarith
        _ = r.Q ^ 10 / 25 := by ring
    linarith
  have h_sqrt_n_le : Real.sqrt r.n ≤ r.Q ^ 5 / 5 := by
    calc
      Real.sqrt r.n ≤ Real.sqrt (r.Q ^ 10 / 25) := Real.sqrt_le_sqrt hn_le
      _ = Real.sqrt (r.Q ^ 10) / Real.sqrt 25 := by rw [Real.sqrt_div hQ_pow_nonneg]
      _ = Real.sqrt ((r.Q ^ 5) ^ 2) / Real.sqrt 25 := by ring
      _ = r.Q ^ 5 / Real.sqrt 25 := by rw [Real.sqrt_sq (by positivity : 0 ≤ r.Q ^ 5)]
      _ = r.Q ^ 5 / 5 := by norm_num
  calc
    1 / r.eps = 1 / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n) := by rw [h.heps]
    _ = Real.sqrt r.n / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) := by rw [one_div_div]
    _ = Real.sqrt r.n * (1 / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5)) := by ring
    _ ≤ Real.sqrt r.n * (1 / (14500 : ℝ)) := by
      nlinarith
    _ = Real.sqrt r.n / 14500 := by ring
    _ ≤ (r.Q ^ 5 / 5) / 14500 := by
      refine div_le_div_of_nonneg_right h_sqrt_n_le (by norm_num : 0 ≤ (14500 : ℝ))
    _ = r.Q ^ 5 / 72500 := by ring

theorem kc_bd (h : r.OK) : 0 ≤ r.kc ∧ r.kc ≤ 1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
  have hdpos : 0 < r.d := by
    have := h.hd
    linarith
  have hnpos : 0 < r.n := by
    have := h.hn
    linarith
  have hLepos : 0 < r.Le := by
    have := h.hL1
    linarith
  have hsqrt_d_pos : 0 < Real.sqrt r.d := Real.sqrt_pos.mpr hdpos
  have hsqrt_n_pos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr hnpos
  have h_eta_nonneg : 0 ≤ r.eta := by
    rw [h.heta]
    refine div_nonneg (Real.sqrt_nonneg _) (by nlinarith)
  have hlampos : 0 < r.lam := by
    rw [h.hlam]
    refine div_pos (by norm_num) (by
      have hd1 : 1 ≤ r.d := h.hd
      have hLe17467 : 17467 ≤ r.Le := h.hL1
      nlinarith)
  have hlam_le : r.lam ≤ 1 / 5800 := by
    rw [h.hlam]
    refine (one_div_le_one_div ?_ (by norm_num)).mpr ?_
    · have hd1 : 1 ≤ r.d := h.hd
      have hLe17467 : 17467 ≤ r.Le := h.hL1
      nlinarith
    · have hd1 : 1 ≤ r.d := h.hd
      have hLe17467 : 17467 ≤ r.Le := h.hL1
      nlinarith
  have h_first : 0 ≤ r.kc := by
    rw [h.hkc]
    refine div_nonneg (mul_nonneg h_eta_nonneg (by linarith)) (by nlinarith)
  have h_eta_lam : r.eta * r.lam = 1 / (725 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
    rw [h.heta, h.hlam]
    field_simp [hsqrt_d_pos.ne', hsqrt_n_pos.ne', hLepos.ne']
    nlinarith [Real.sq_sqrt hdpos.le]
  have hDpos : 0 < 725 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n := by
    refine mul_pos (mul_pos (mul_pos (by norm_num) hsqrt_d_pos) (pow_pos hLepos 3)) hsqrt_n_pos
  have hDpos2899 : 0 < 2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n := by
    refine mul_pos (mul_pos (mul_pos (by norm_num) hsqrt_d_pos) (pow_pos hLepos 3)) hsqrt_n_pos
  have h_one_div : 1 / (4 * (1 - r.lam)^2) ≤ 1 / (4 * (1 - 2 * r.lam)) := by
    refine (one_div_le_one_div ?_ ?_).mpr ?_
    · nlinarith
    · nlinarith
    · nlinarith
  have h_num_nonneg : 0 ≤ r.eta * r.lam := mul_nonneg h_eta_nonneg (by linarith)
  have h_kc_le_intermediate : r.kc ≤ r.eta * r.lam / (4 * (1 - 2 * r.lam)) := by
    rw [h.hkc]
    calc
      r.eta * r.lam / (4 * (1 - r.lam)^2) = (r.eta * r.lam) * (1 / (4 * (1 - r.lam)^2)) := by rw [div_eq_mul_one_div]
      _ ≤ (r.eta * r.lam) * (1 / (4 * (1 - 2 * r.lam))) := mul_le_mul_of_nonneg_left h_one_div h_num_nonneg
      _ = r.eta * r.lam / (4 * (1 - 2 * r.lam)) := by rw [← div_eq_mul_one_div]
  have h_final : r.eta * r.lam / (4 * (1 - 2 * r.lam)) ≤ 1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
    rw [h_eta_lam]
    rw [div_div]
    refine (one_div_le_one_div ?_ hDpos2899).mpr ?_
    · have hpos : 0 < 1 - 2 * r.lam := by nlinarith
      apply mul_pos hDpos
      nlinarith [hpos]
    · nlinarith
  have h_second : r.kc ≤ 1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
    linarith
  exact And.intro h_first h_second

theorem R_bd (h : r.OK) : r.R ≤ 190 * r.d ^ 2 ∧ (r.R + 1) ^ 2 ≤ (158 / 157) ^ 2 * 190 ^ 2 * r.d ^ 3 := by
  rcases h with ⟨hd, hn, hNe, hde, hLe, hlam, heta, heps, hrho, hkc, heps4, hN700, hL1, hd15, hn4, hnge, hL40, hQ0, hQ, htp0, htp, heh1, heh2, hR1, hR2, ht20, ht2⟩
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num : (0 : ℝ) ≤ 1) hd
  have hR_nonneg : 0 ≤ r.R := le_trans (by norm_num : (0 : ℝ) ≤ 157) hR1
  have hR_sq_le' : r.R ^ 2 ≤ (190 * r.d ^ 2) ^ 2 := by
    calc
      r.R ^ 2 ≤ 190 ^ 2 * r.d ^ 3 := hR2
      _ ≤ 190 ^ 2 * r.d ^ 4 := by
        have h_pow : r.d ^ 3 ≤ r.d ^ 4 := by
          have h_eq : r.d ^ 4 - r.d ^ 3 = r.d ^ 3 * (r.d - 1) := by ring
          have h_nonneg_prod : 0 ≤ r.d ^ 3 * (r.d - 1) := by
            apply mul_nonneg
            · exact pow_nonneg hd_nonneg 3
            · linarith
          linarith
        nlinarith
      _ = (190 * r.d ^ 2) ^ 2 := by ring
  have hR_le : r.R ≤ 190 * r.d ^ 2 := by
    nlinarith
  have h_bound : r.R + 1 ≤ (158 / 157 : ℝ) * r.R := by
    have h_mul : (r.R + 1) * (157 : ℝ) ≤ (158 : ℝ) * r.R := by
      linarith
    have h_nonneg_157 : (0 : ℝ) ≤ 157 := by norm_num
    calc
      r.R + 1 = ((r.R + 1) * (157 : ℝ)) / (157 : ℝ) := by field_simp
      _ ≤ ((158 : ℝ) * r.R) / (157 : ℝ) :=
        div_le_div_of_nonneg_right h_mul h_nonneg_157
      _ = (158 / 157 : ℝ) * r.R := by ring
  have hR_plus_one_sq_le : (r.R + 1) ^ 2 ≤ ((158 / 157 : ℝ) * r.R) ^ 2 := by
    have h_nonneg_sum : 0 ≤ r.R + 1 := by linarith
    have h_nonneg_mul : 0 ≤ (158 / 157 : ℝ) * r.R := by
      have hpos : (0 : ℝ) ≤ 158 / 157 := by norm_num
      exact mul_nonneg hpos hR_nonneg
    nlinarith
  have h_final : (r.R + 1) ^ 2 ≤ (158 / 157 : ℝ) ^ 2 * 190 ^ 2 * r.d ^ 3 := by
    calc
      (r.R + 1) ^ 2 ≤ ((158 / 157 : ℝ) * r.R) ^ 2 := hR_plus_one_sq_le
      _ = ((158 / 157 : ℝ) ^ 2) * (r.R ^ 2) := by ring
      _ ≤ ((158 / 157 : ℝ) ^ 2) * (190 ^ 2 * r.d ^ 3) := by
        have h_nonneg_sq : 0 ≤ (158 / 157 : ℝ) ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left hR2 h_nonneg_sq
      _ = (158 / 157 : ℝ) ^ 2 * 190 ^ 2 * r.d ^ 3 := by ring
  exact And.intro hR_le h_final

theorem Lgb_bd (h : r.OK) : 5 * r.Le / 144 ≤ r.Lgb ∧ r.Lgb ≤ 349 / 10000 * r.Le := by
  have hL14 : 1 ≤ (14 : ℝ) := by norm_num
  have hlog14_nonneg : 0 ≤ Real.log 14 := Real.log_nonneg hL14
  have h_left : 5 * r.Le / 144 ≤ r.Lgb := by
    dsimp [Reg.Lgb]
    nlinarith
  have h_right : r.Lgb ≤ 349 / 10000 * r.Le := by
    dsimp [Reg.Lgb]
    have hcoeff_nonneg : 0 ≤ (349 : ℝ) / 10000 - 5 / 144 := by norm_num
    have h_mul : (3 : ℝ) ≤ ((349 : ℝ) / 10000 - 5 / 144) * (17467 : ℝ) := by norm_num
    have h_mul_le : ((349 : ℝ) / 10000 - 5 / 144) * (17467 : ℝ) ≤ ((349 : ℝ) / 10000 - 5 / 144) * r.Le := by
      nlinarith [h.hL1, hcoeff_nonneg]
    have h_log14_lt_three : Real.log 14 < 3 := by
      calc
        Real.log 14 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
        _ = Real.log ((2 : ℝ) ^ 4) := by norm_num
        _ = 4 * Real.log 2 := Real.log_pow 2 4
        _ < 4 * (0.6931471808 : ℝ) := by nlinarith [Real.log_two_lt_d9]
        _ = 2.7725887232 := by norm_num
        _ < 3 := by norm_num
    nlinarith
  exact And.intro h_left h_right

theorem Xi_bd (h : r.OK) : 402 / 10 ≤ r.Xi ∧ 1 + r.Xi1 ^ 2 ≤ r.d * r.Le / 9 ∧ r.Xi1 ^ 2 ≤ r.d * r.Le / 10 := by
  have hLgb := h.Lgb_bd
  rcases hLgb with ⟨hLgb_low, hLgb_high⟩
  have hLe := h.hL1
  have hd := h.hd
  set s := r.Xi with hs
  have hs_sq : s ^ 2 = 8 * r.d / 3 * r.Lgb := by
    dsimp [s, Xi]
    have hS_nonneg : 0 ≤ 8 * r.d / 3 * r.Lgb := by
      have hd_nonneg : 0 ≤ r.d := by linarith
      have hLgb_nonneg : 0 ≤ r.Lgb := by nlinarith
      nlinarith
    exact Real.sq_sqrt hS_nonneg
  have hs_ge : 402 / 10 ≤ s := by
    dsimp [s, Xi]
    have hS_nonneg : 0 ≤ 8 * r.d / 3 * r.Lgb := by
      have hd_nonneg : 0 ≤ r.d := by linarith
      have hLgb_nonneg : 0 ≤ r.Lgb := by nlinarith
      nlinarith
    have h402 : 0 ≤ (402 : ℝ) / 10 := by norm_num
    rw [Real.le_sqrt h402 hS_nonneg]
    nlinarith
  have hXi1 : r.Xi1 = s + 1 := by
    dsimp [s, Xi1]
  rw [hXi1]
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · nlinarith

theorem Xi1_le (h : r.OK) : 0 ≤ r.Xi ∧ r.Xi ≤ r.Xi1 ∧ r.Xi1 ≤ r.d * r.Q := by
  have hXi_nonneg : 0 ≤ r.Xi := Real.sqrt_nonneg _
  have hXi_le_Xi1 : r.Xi ≤ r.Xi1 := by
    dsimp [Reg.Xi1]
    nlinarith
  have hQ_pos : 0 < r.Q := h.hQ0
  have hd_pos : 0 < r.d := by linarith [h.hd]
  have hQ_ge_one : 1 ≤ r.Q := by
    have : 2 ^ 17 ≤ r.Q := (h.Q_bd).left
    linarith
  have hd_ge_one : 1 ≤ r.d := h.hd
  have h_dQ_ge_one : 1 ≤ r.d * r.Q := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ r.d * r.Q := mul_le_mul hd_ge_one hQ_ge_one (by linarith) (by linarith)
  have h_dQ_nonneg : 0 ≤ r.d * r.Q := by linarith
  have hXi1_nonneg : 0 ≤ r.Xi1 := by
    dsimp [Reg.Xi1]
    nlinarith
  have h_Xi1_sq_le_dQ_sq : r.Xi1 ^ 2 ≤ (r.d * r.Q) ^ 2 := by
    have hXi1_sq_le : r.Xi1 ^ 2 ≤ r.d * r.Le / 10 := (h.Xi_bd).right.right
    have hLe_bound : r.Le ≤ r.Q / 10 := by
      have : 10 * r.Le ≤ r.Q := (h.Q_bd).right.left
      linarith
    have h_intermediate : r.d * r.Le / 10 ≤ r.d * r.Q / 100 := by
      nlinarith
    have h_dQ_div_100_le_dQ_sq : r.d * r.Q / 100 ≤ (r.d * r.Q) ^ 2 := by
      nlinarith
    nlinarith
  have h_Xi1_le_dQ : r.Xi1 ≤ r.d * r.Q := by
    nlinarith
  exact ⟨hXi_nonneg, hXi_le_Xi1, h_Xi1_le_dQ⟩

theorem sqrtLam (h : r.OK) : 0 ≤ Real.sqrt r.Lam ∧ Real.sqrt r.Lam ≤ r.d * r.Q ^ 20 := by
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have hQ_nonneg : 0 ≤ r.Q := by linarith [h.hQ0]
  have hQ_pow_nonneg : 0 ≤ r.Q ^ 20 := pow_nonneg hQ_nonneg 20
  have h_sqrt_d_le_d : Real.sqrt r.d ≤ r.d := (sqrt_d_le h).right
  have hLam_eq : r.Lam = r.d * r.Q ^ 40 := by
    dsimp [Reg.Lam]
    rw [h.hQ]
  have h_sqrt_Q40 : Real.sqrt (r.Q ^ 40) = r.Q ^ 20 := by
    calc
      Real.sqrt (r.Q ^ 40) = Real.sqrt ((r.Q ^ 20) ^ 2) := by
        rw [← pow_mul, show (20 : ℕ) * 2 = 40 by norm_num]
      _ = r.Q ^ 20 := Real.sqrt_sq hQ_pow_nonneg
  have h_sqrt_Lam_eq : Real.sqrt r.Lam = Real.sqrt r.d * r.Q ^ 20 := by
    rw [hLam_eq, Real.sqrt_mul hd_nonneg, h_sqrt_Q40]
  have h_first : 0 ≤ Real.sqrt r.Lam := Real.sqrt_nonneg _
  have h_second : Real.sqrt r.Lam ≤ r.d * r.Q ^ 20 := by
    rw [h_sqrt_Lam_eq]
    exact mul_le_mul_of_nonneg_right h_sqrt_d_le_d hQ_pow_nonneg
  exact And.intro h_first h_second

/-! ## The E-terms (coarser) -/

theorem ezt_exi (h : r.OK) : 0 ≤ r.ezt ∧ r.ezt ≤ r.tp / 6 ∧ 0 ≤ r.exi ∧ r.exi ≤ r.tp / 2 := by
  have ht2pos : 0 < r.t2 := h.ht20
  have hd1 : 1 ≤ r.d := h.hd
  have hn1 : 1 ≤ r.n := h.hn
  have hezt_nonneg : 0 ≤ r.ezt := by
    rw [AdversarialBco.Bit.PieceA.Reg.ezt]
    positivity
  have hexi_nonneg : 0 ≤ r.exi := by
    rw [AdversarialBco.Bit.PieceA.Reg.exi]
    positivity
  have hezt_le : r.ezt ≤ r.tp / 6 := by
    rw [AdversarialBco.Bit.PieceA.Reg.ezt]
    have hlow : 12 ≤ 4 * r.n * (r.d + 2) := by nlinarith
    have h12 : 12 ≤ r.t2 * r.tp := le_trans hlow h.ht2
    field_simp [ht2pos.ne.symm]
    norm_num
    exact h12
  have hexi_le : r.exi ≤ r.tp / 2 := by
    rw [AdversarialBco.Bit.PieceA.Reg.exi]
    have hd_nonneg : 0 ≤ r.d := by linarith
    have hsqrt_d : Real.sqrt (r.d) ≤ (r.d + 2) / 2 := by
      have h_sq_nonneg : (Real.sqrt (r.d) - 1) ^ 2 ≥ 0 := by positivity
      have h_sq_expand : (Real.sqrt (r.d)) ^ 2 = r.d := Real.sq_sqrt hd_nonneg
      have h_expanded : r.d - 2 * Real.sqrt (r.d) + 1 ≥ 0 := by nlinarith
      have h_ineq : Real.sqrt (r.d) ≤ (r.d + 1) / 2 := by linarith
      linarith
    have h_mul : Real.sqrt (r.d) * (4 / r.t2) ≤ ((r.d + 2) / 2) * (4 / r.t2) := by
      have hpos : 0 ≤ 4 / r.t2 := by positivity
      exact mul_le_mul_of_nonneg_right hsqrt_d hpos
    have h_mid : 2 * (r.d + 2) / r.t2 ≤ 2 * r.n * (r.d + 2) / r.t2 := by
      field_simp [ht2pos.ne.symm]
      nlinarith
    have h_last : 2 * r.n * (r.d + 2) / r.t2 ≤ r.tp / 2 := by
      field_simp [ht2pos.ne.symm]
      norm_num
      exact h.ht2
    calc
      Real.sqrt (r.d) * (4 / r.t2) ≤ ((r.d + 2) / 2) * (4 / r.t2) := h_mul
      _ = 2 * (r.d + 2) / r.t2 := by ring
      _ ≤ 2 * r.n * (r.d + 2) / r.t2 := h_mid
      _ ≤ r.tp / 2 := h_last
  exact And.intro hezt_nonneg (And.intro hezt_le (And.intro hexi_nonneg hexi_le))

theorem Pb_pib (h : r.OK) : 1 ≤ r.Pb ∧ r.Pb ≤ 201 / 100 * Real.sqrt r.Le ∧ 0 ≤ r.pib ∧
    r.pib ≤ 101 / 100 * Real.sqrt r.Le := by
  have hsqrt : (132 : ℝ) ≤ Real.sqrt r.Le := by
    have hsq : (132 : ℝ)^2 ≤ r.Le := by
      calc
        (132 : ℝ)^2 = (17424 : ℝ) := by norm_num
        _ ≤ (17467 : ℝ) := by norm_num
        _ ≤ r.Le := hL1 h
    have h_nonneg : 0 ≤ (132 : ℝ) := by norm_num
    calc
      (132 : ℝ) = Real.sqrt ((132 : ℝ)^2) := by rw [Real.sqrt_sq h_nonneg]
      _ ≤ Real.sqrt r.Le := Real.sqrt_le_sqrt hsq
  have hPb_def : r.Pb = 2 * Real.sqrt r.Le + 1 := rfl
  have hpib_def : r.pib = Real.sqrt r.Le + 1 / 8 := rfl
  have h1 : 1 ≤ r.Pb := by
    rw [hPb_def]
    have hsqrt_nonneg : 0 ≤ Real.sqrt r.Le := Real.sqrt_nonneg _
    nlinarith
  have h2 : r.Pb ≤ 201 / 100 * Real.sqrt r.Le := by
    rw [hPb_def]
    have h100 : (100 : ℝ) ≤ Real.sqrt r.Le := by nlinarith
    nlinarith
  have h3 : 0 ≤ r.pib := by
    rw [hpib_def]
    have hsqrt_nonneg : 0 ≤ Real.sqrt r.Le := Real.sqrt_nonneg _
    nlinarith
  have h4 : r.pib ≤ 101 / 100 * Real.sqrt r.Le := by
    rw [hpib_def]
    have h125 : (12.5 : ℝ) ≤ Real.sqrt r.Le := by nlinarith
    nlinarith
  exact ⟨h1, h2, h3, h4⟩

theorem eY_le (h : r.OK) : 0 ≤ r.eY ∧ r.eY ≤ 118 / 100 * Real.sqrt r.Le * r.tp := by
  have htp0 : 0 < r.tp := h.htp0
  have hsqrtLe_nonneg : 0 ≤ Real.sqrt r.Le := Real.sqrt_nonneg _
  have hLe1 : 17467 ≤ r.Le := h.hL1
  have hsqrtLe_ge_132 : 132 ≤ Real.sqrt r.Le := by
    have hsq : (132 : ℝ) ^ 2 = 17424 := by norm_num
    have h17424 : (132 : ℝ) ^ 2 ≤ r.Le := by
      -- 132^2 = 17424 ≤ 17467 ≤ r.Le
      have : (17424 : ℝ) ≤ 17467 := by norm_num
      linarith
    calc
      132 = Real.sqrt ((132 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt r.Le := Real.sqrt_le_sqrt h17424
  have hPb_pos : 0 ≤ r.Pb := by
    dsimp [Reg.Pb]
    nlinarith
  have hPb_le : r.Pb ≤ 201/100 * Real.sqrt r.Le := by
    dsimp [Reg.Pb]
    have h100 : (100 : ℝ) ≤ Real.sqrt r.Le := by linarith
    nlinarith
  have hezt_nonneg : 0 ≤ r.ezt := by
    dsimp [Reg.ezt]
    have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    exact div_nonneg h2_nonneg (by linarith [h.ht20])
  have hezt_le : r.ezt ≤ r.tp / 6 := by
    dsimp [Reg.ezt]
    have ht2pos : 0 < r.t2 := h.ht20
    have h6pos : (0 : ℝ) < 6 := by norm_num
    have hnum : (12 : ℝ) ≤ r.tp * r.t2 := by
      have hbound : 4 * r.n * (r.d + 2) ≤ r.tp * r.t2 := by
        -- h.t2 : 4 * r.n * (r.d + 2) ≤ r.t2 * r.tp
        simpa [mul_comm] using h.ht2
      have hlower : (12 : ℝ) ≤ 4 * r.n * (r.d + 2) := by
        have hn1 : 1 ≤ r.n := h.hn
        have hd1 : 1 ≤ r.d := h.hd
        nlinarith
      linarith
    have hpos_prod : 0 < r.t2 * 6 := by positivity
    apply le_of_mul_le_mul_right ?_ hpos_prod
    calc
      2 / r.t2 * (r.t2 * 6) = 2 * 6 := by field_simp [ne_of_gt ht2pos]
      _ = (12 : ℝ) := by norm_num
      _ ≤ r.tp * r.t2 := hnum
      _ = r.tp / 6 * (r.t2 * 6) := by field_simp [ne_of_gt h6pos]
  have h_main : r.eY ≤ 118 / 100 * Real.sqrt r.Le * r.tp := by
    dsimp [Reg.eY]
    have h1 : r.tp / 2 + r.Pb / 2 * (r.tp + r.ezt) ≤ r.tp / 2 + (201/100 * Real.sqrt r.Le) / 2 * (r.tp + r.tp / 6) := by
      nlinarith
    have h2 : r.tp / 2 + (201/100 * Real.sqrt r.Le) / 2 * (r.tp + r.tp / 6) = r.tp * (1/2 + 1407/1200 * Real.sqrt r.Le) := by
      ring
    have h3 : r.tp * (1/2 + 1407/1200 * Real.sqrt r.Le) ≤ 118/100 * Real.sqrt r.Le * r.tp := by
      have hcoeff : 1/2 ≤ (3/400) * Real.sqrt r.Le := by
        have hsqrtLe_ge_200_3 : (200/3 : ℝ) ≤ Real.sqrt r.Le := by linarith
        nlinarith
      nlinarith
    nlinarith
  have h_nonneg : 0 ≤ r.eY := by
    dsimp [Reg.eY]
    have hsum_nonneg : 0 ≤ r.tp + r.ezt := by nlinarith
    nlinarith
  exact And.intro h_nonneg h_main

set_option maxHeartbeats 800000 in
theorem Yb_bd (h : r.OK) : 8 * Real.sqrt r.Le ≤ r.Yb ∧ r.Yb ≤ r.Q ^ 5 := by
  have hd_pos : 0 < r.d := by linarith [h.hd]
  have hn_pos : 0 < r.n := by linarith [h.hn]
  have hLe_pos : 0 < r.Le := by linarith [h.hL1]
  have hLe_nonneg : 0 ≤ r.Le := by linarith
  have hQ_pos : 0 < r.Q := h.hQ0
  have hQ_nonneg : 0 ≤ r.Q := by linarith
  have hsqrt_Le_nonneg : 0 ≤ Real.sqrt r.Le := Real.sqrt_nonneg _
  have hsqrt_d_nonneg : 0 ≤ Real.sqrt r.d := Real.sqrt_nonneg _
  have hsqrt_n_nonneg : 0 ≤ Real.sqrt r.n := Real.sqrt_nonneg _
  have hd_ge_one : 1 ≤ r.d := h.hd
  have hn_ge_one : 1 ≤ r.n := h.hn
  have hLe_ge_one : 1 ≤ r.Le := by linarith [h.hL1]
  have hLgb_bd := Lgb_bd h
  rcases hLgb_bd with ⟨hLgb_low, hLgb_high⟩
  have hQ_bd := Q_bd h
  rcases hQ_bd with ⟨hQ_low, hLe_bound, hn_bound, hd3_bound, hsqrt_n_bound, hd_bound⟩
  have hsqrtL_ge := sqrtL_ge h
  have heps_pos : 0 < r.eps := by
    rw [h.heps]
    positivity
  have hYb_def : r.Yb = 2 * Real.sqrt r.Le * (1/2 + Real.sqrt r.Lgb) + 4 * Real.sqrt r.Le / r.eps := rfl
  have h_lower : 8 * Real.sqrt r.Le ≤ r.Yb := by
    rw [hYb_def]
    have h_nonneg_rest : 0 ≤ 2 * Real.sqrt r.Le * (1/2) + 4 * Real.sqrt r.Le / r.eps := by
      have h1 : 0 ≤ 2 * Real.sqrt r.Le * (1/2) := by nlinarith
      have h2 : 0 ≤ 4 * Real.sqrt r.Le / r.eps := by positivity
      nlinarith
    have h_main : 2 * Real.sqrt r.Le * Real.sqrt r.Lgb ≤
        2 * Real.sqrt r.Le * (1/2 + Real.sqrt r.Lgb) + 4 * Real.sqrt r.Le / r.eps := by
      nlinarith
    have h_sqrt_Lgb_ge : Real.sqrt (5 * r.Le / 144) ≤ Real.sqrt r.Lgb :=
      Real.sqrt_le_sqrt hLgb_low
    have h_sqrt_expr : Real.sqrt (5 * r.Le / 144) = Real.sqrt r.Le * Real.sqrt 5 / 12 := by
      calc
        Real.sqrt (5 * r.Le / 144) = Real.sqrt (5 * r.Le) / Real.sqrt 144 := Real.sqrt_div (by nlinarith) _
        _ = Real.sqrt (5 * r.Le) / 12 := by norm_num
        _ = (Real.sqrt 5 * Real.sqrt r.Le) / 12 := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (5 : ℝ))]
        _ = Real.sqrt r.Le * Real.sqrt 5 / 12 := by ring
    have h_sqrt_Lgb_gt_4 : 4 < Real.sqrt r.Lgb := by
      have h_low : 11 * Real.sqrt 5 ≤ Real.sqrt r.Lgb := by
        calc
          11 * Real.sqrt 5 = (132 * Real.sqrt 5) / 12 := by ring
          _ ≤ (Real.sqrt r.Le * Real.sqrt 5) / 12 := by
            have h : 132 * Real.sqrt 5 ≤ Real.sqrt r.Le * Real.sqrt 5 :=
              mul_le_mul_of_nonneg_right hsqrtL_ge (by positivity)
            exact div_le_div_of_nonneg_right h (by norm_num : 0 ≤ (12 : ℝ))
          _ = Real.sqrt r.Le * Real.sqrt 5 / 12 := by ring
          _ = Real.sqrt (5 * r.Le / 144) := by rw [h_sqrt_expr]
          _ ≤ Real.sqrt r.Lgb := Real.sqrt_le_sqrt hLgb_low
      have h_11_5_gt_4 : 4 < 11 * Real.sqrt 5 := by
        have h_sq : (4 : ℝ) ^ 2 < (11 * Real.sqrt 5) ^ 2 := by
          calc
            (4 : ℝ) ^ 2 = 16 := by norm_num
            _ < 605 := by norm_num
            _ = 121 * 5 := by norm_num
            _ = (11 : ℝ) ^ 2 * 5 := by norm_num
            _ = (11 : ℝ) ^ 2 * ((Real.sqrt 5) ^ 2) := by rw [Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))]
            _ = (11 * Real.sqrt 5) ^ 2 := by ring
        have h_nonneg : 0 ≤ 11 * Real.sqrt 5 := by positivity
        nlinarith
      linarith
    have h_ineq : 8 * Real.sqrt r.Le ≤ 2 * Real.sqrt r.Le * Real.sqrt r.Lgb := by
      nlinarith
    exact le_trans h_ineq h_main
  have h_upper : r.Yb ≤ r.Q ^ 5 := by
    rw [hYb_def]
    have hYb_eq : 2 * Real.sqrt r.Le * (1/2 + Real.sqrt r.Lgb) + 4 * Real.sqrt r.Le / r.eps =
        Real.sqrt r.Le + 2 * Real.sqrt r.Le * Real.sqrt r.Lgb + 4 * Real.sqrt r.Le / r.eps := by ring
    rw [hYb_eq]
    have h_sqrt_Le_mul_self : Real.sqrt r.Le * Real.sqrt r.Le = r.Le := Real.mul_self_sqrt hLe_nonneg
    have h_sqrt_Le_le_Le : Real.sqrt r.Le ≤ r.Le := by
      calc
        Real.sqrt r.Le = Real.sqrt r.Le * 1 := by ring
        _ ≤ Real.sqrt r.Le * Real.sqrt r.Le := by nlinarith
        _ = r.Le := h_sqrt_Le_mul_self
    have h_sqrt_Lgb_bound : Real.sqrt r.Lgb ≤ (19/100) * Real.sqrt r.Le := by
      have h_349_lt_361 : (349 : ℝ) < 361 := by norm_num
      have h_sqrt_349_lt_19 : Real.sqrt (349 : ℝ) < 19 := by
        calc
          Real.sqrt (349 : ℝ) < Real.sqrt (361 : ℝ) := Real.sqrt_lt_sqrt (by norm_num) h_349_lt_361
          _ = 19 := by norm_num
      calc
        Real.sqrt r.Lgb ≤ Real.sqrt ((349/10000) * r.Le) := Real.sqrt_le_sqrt hLgb_high
        _ = Real.sqrt (349/10000) * Real.sqrt r.Le := Real.sqrt_mul (by norm_num : 0 ≤ (349/10000 : ℝ)) _
        _ = (Real.sqrt 349 / Real.sqrt 10000) * Real.sqrt r.Le := by rw [Real.sqrt_div (by norm_num : 0 ≤ (349 : ℝ)) (10000 : ℝ)]
        _ = (Real.sqrt 349 / 100) * Real.sqrt r.Le := by norm_num
        _ ≤ (19/100) * Real.sqrt r.Le := by nlinarith
    have h_first_bound : Real.sqrt r.Le + 2 * Real.sqrt r.Le * Real.sqrt r.Lgb ≤ (138/100) * r.Q / 10 := by
      calc
        Real.sqrt r.Le + 2 * Real.sqrt r.Le * Real.sqrt r.Lgb ≤
            Real.sqrt r.Le + 2 * Real.sqrt r.Le * ((19/100) * Real.sqrt r.Le) := by nlinarith
        _ = Real.sqrt r.Le + (38/100) * (Real.sqrt r.Le * Real.sqrt r.Le) := by ring
        _ = Real.sqrt r.Le + (38/100) * r.Le := by rw [h_sqrt_Le_mul_self]
        _ ≤ r.Le + (38/100) * r.Le := by nlinarith
        _ = (138/100) * r.Le := by ring
        _ ≤ (138/100) * (r.Q / 10) := by nlinarith
        _ = (138/100) * r.Q / 10 := by ring
    have h_second_bound : 4 * Real.sqrt r.Le / r.eps ≤ r.Q ^ 5 / 3625 := by
      rw [h.heps]
      have h_denom_pos : 0 < 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by positivity
      have h_denom_nonneg : 0 ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by positivity
      have h_num_nonneg : 0 ≤ 4 * Real.sqrt r.Le * Real.sqrt r.n := by positivity
      have h_d_sqrt_d_ge_one : r.d * Real.sqrt r.d ≥ 1 := by
        have hsqrt_d_ge_one : Real.sqrt r.d ≥ 1 := by
          calc
            Real.sqrt r.d ≥ Real.sqrt 1 := Real.sqrt_le_sqrt hd_ge_one
            _ = 1 := by norm_num
        nlinarith
      have h_Le_pow2_ge_one : r.Le ^ 2 ≥ 1 := by nlinarith
      have h_Le_pow4_ge_one : r.Le ^ 4 ≥ 1 := by
        calc
          r.Le ^ 4 = (r.Le ^ 2) ^ 2 := by ring
          _ ≥ 1 ^ 2 := by nlinarith
          _ = 1 := by norm_num
      have h_denom_ge : (14500 : ℝ) ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 4 := by
        nlinarith
      calc
        4 * Real.sqrt r.Le / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n) =
            4 * Real.sqrt r.Le * Real.sqrt r.n / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) := by
          rw [div_div_eq_mul_div]
        _ ≤ 4 * r.Le * Real.sqrt r.n / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = 4 * Real.sqrt r.n * r.Le / (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) := by ring
        _ = 4 * Real.sqrt r.n / (14500 * r.d * Real.sqrt r.d * r.Le ^ 4) := by
          have h_denom1 : 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 ≠ 0 := by positivity
          have h_denom2 : 14500 * r.d * Real.sqrt r.d * r.Le ^ 4 ≠ 0 := by positivity
          rw [div_eq_div_iff h_denom1 h_denom2]
          ring
        _ ≤ 4 * Real.sqrt r.n / 14500 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num : 0 < (14500 : ℝ)) h_denom_ge
        _ = Real.sqrt r.n / 3625 := by ring
        _ ≤ r.Q ^ 5 / 3625 := div_le_div_of_nonneg_right hsqrt_n_bound (by norm_num : 0 ≤ (3625 : ℝ))
    have h_total : Real.sqrt r.Le + 2 * Real.sqrt r.Le * Real.sqrt r.Lgb + 4 * Real.sqrt r.Le / r.eps ≤
        (138/100) * r.Q / 10 + r.Q ^ 5 / 3625 := by nlinarith
    have h_final : (138/100) * r.Q / 10 + r.Q ^ 5 / 3625 ≤ r.Q ^ 5 := by
      have hQ_ge_two : 2 ≤ r.Q := by linarith
      have hQ_pow2_ge_four : r.Q ^ 2 ≥ 4 := by nlinarith
      have hQ_pow4_ge_sixteen : 16 ≤ r.Q ^ 4 := by
        calc
          r.Q ^ 4 = (r.Q ^ 2) ^ 2 := by ring
          _ ≥ 4 ^ 2 := by nlinarith
          _ = 16 := by norm_num
      have h1 : (138/100) * r.Q / 10 ≤ r.Q ^ 5 / 2 := by
        have hineq : (138/100) / 10 ≤ r.Q ^ 4 / 2 := by nlinarith
        calc
          (138/100) * r.Q / 10 = ((138/100) / 10) * r.Q := by ring
          _ ≤ (r.Q ^ 4 / 2) * r.Q := by nlinarith
          _ = r.Q ^ 5 / 2 := by ring
      have h2 : r.Q ^ 5 / 3625 ≤ r.Q ^ 5 / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≤ 3625)
      nlinarith
    nlinarith
  exact And.intro h_lower h_upper

theorem cb_le (h : r.OK) : 0 ≤ r.cb ∧ r.cb ≤ 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := by
  have hpos := pos h
  rcases hpos with ⟨hd_pos, hn_pos, hNe_pos, hLe_pos, heps_pos, hde_pos, htp_pos, heh_pos⟩
  have hd_nonneg : 0 ≤ r.d := by linarith
  have hn_nonneg : 0 ≤ r.n := by linarith
  have hLe_nonneg : 0 ≤ r.Le := by linarith
  have hsqrtLe_nonneg : 0 ≤ Real.sqrt r.Le := Real.sqrt_nonneg _
  have hsqrtLe_pos : 0 < Real.sqrt r.Le := Real.sqrt_pos.mpr hLe_pos
  have hsqrt_d_pos : 0 < Real.sqrt r.d := Real.sqrt_pos.mpr hd_pos
  have hsqrt_d_nonneg : 0 ≤ Real.sqrt r.d := Real.sqrt_nonneg _
  have hsqrt_n_pos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr hn_pos
  -- 0 ≤ r.cb
  have hcb_nonneg : 0 ≤ r.cb := by
    rw [Reg.cb]
    have hkc_nonneg : 0 ≤ r.kc := by
      rw [h.hkc]
      have hlam_pos : 0 < r.lam := by
        rw [h.hlam]
        have hpos : 0 < 725 * r.d * r.Le ^ 2 := by positivity
        exact div_pos (by norm_num) hpos
      have hlam_lt_one : r.lam < 1 := by
        rw [h.hlam]
        have hdenom : 1 < 725 * r.d * r.Le ^ 2 := by
          have hd1 : 1 ≤ r.d := h.hd
          have hL1 : 17467 ≤ r.Le := h.hL1
          nlinarith
        exact (div_lt_one (by positivity)).mpr hdenom
      have h_one_minus_lam_pos : 0 < 1 - r.lam := by linarith
      have h_num_nonneg : 0 ≤ r.eta * r.lam := by
        have heta_nonneg : 0 ≤ r.eta := by
          rw [h.heta]
          positivity
        positivity
      have h_denom_pos : 0 < 4 * (1 - r.lam)^2 := by positivity
      apply div_nonneg
      · exact h_num_nonneg
      · positivity
    have hYb_nonneg : 0 ≤ r.Yb := by
      rw [Reg.Yb]
      positivity
    nlinarith
  -- Upper bound
  have hcb_upper : r.cb ≤ 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := by
    have hkc_bd := kc_bd h
    rcases hkc_bd with ⟨hkc_nonneg, hkc_bound⟩
    have hsqrtL_ge := sqrtL_ge h
    have hLgb_bd := Lgb_bd h
    rcases hLgb_bd with ⟨hLgb_low, hLgb_high⟩
    -- bound √(Lgb) ≤ √(349/10000) * √(Le)
    have h_sqrtLgb_bound : Real.sqrt (r.Lgb) ≤ Real.sqrt (349/10000) * Real.sqrt r.Le := by
      calc
        Real.sqrt (r.Lgb) ≤ Real.sqrt (349/10000 * r.Le) := Real.sqrt_le_sqrt hLgb_high
        _ = Real.sqrt (349/10000) * Real.sqrt r.Le := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (349/10000 : ℝ))]
    have h_sqrt349_lt : Real.sqrt 349 < (187 : ℝ)/10 := by
      have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (349 : ℝ)) (by norm_num : (349 : ℝ) < ((187 : ℝ)/10)^2)
      simpa [Real.sqrt_sq (by norm_num : 0 ≤ (187/10 : ℝ))] using h
    -- first part of Yb: 2*√Le*(1/2 + √(Lgb)) ≤ (383/1000)*Le
    have h_first_part : 2 * Real.sqrt r.Le * (1/2 + Real.sqrt (r.Lgb)) ≤ (383/1000 : ℝ) * r.Le := by
      have htemp : Real.sqrt (r.Lgb) ≤ (Real.sqrt 349 / 100) * Real.sqrt r.Le := by
        have hdiv : Real.sqrt (349/10000) = Real.sqrt 349 / 100 := by
          rw [Real.sqrt_div (by norm_num : 0 ≤ (349 : ℝ)) (10000 : ℝ)]
          norm_num
        -- h_sqrtLgb_bound : √(r.Lgb) ≤ √(349/10000) * √(r.Le)
        -- hdiv : √(349/10000) = √349 / 100
        -- So √(r.Lgb) ≤ (√349 / 100) * √(r.Le)
        calc
          Real.sqrt (r.Lgb) ≤ Real.sqrt (349/10000) * Real.sqrt r.Le := h_sqrtLgb_bound
          _ = (Real.sqrt 349 / 100) * Real.sqrt r.Le := by rw [hdiv]
      have htemp2 : 2 * Real.sqrt r.Le * (1/2 + Real.sqrt (r.Lgb)) ≤
                   2 * Real.sqrt r.Le * (1/2 + (Real.sqrt 349 / 100) * Real.sqrt r.Le) := by
        nlinarith
      have htemp3 : 2 * Real.sqrt r.Le * (1/2 + (Real.sqrt 349 / 100) * Real.sqrt r.Le) =
                   Real.sqrt r.Le + (Real.sqrt 349 / 50) * r.Le := by
        ring_nf
        rw [Real.sq_sqrt hLe_nonneg]
        ring
      have htemp4 : Real.sqrt r.Le + (Real.sqrt 349 / 50) * r.Le ≤ Real.sqrt r.Le + ((187/10)/50) * r.Le := by
        nlinarith
      have htemp5 : Real.sqrt r.Le + ((187/10)/50) * r.Le = Real.sqrt r.Le + (187/500) * r.Le := by ring
      have htemp6 : Real.sqrt r.Le + (187/500) * r.Le ≤ (383/1000) * r.Le := by
        have hineq : Real.sqrt r.Le ≤ (9/1000 : ℝ) * r.Le := by
          have h1000 : (1000/9 : ℝ) ≤ Real.sqrt r.Le := by linarith
          have h1 : (1 : ℝ) ≤ (9/1000 : ℝ) * Real.sqrt r.Le := by linarith
          calc
            Real.sqrt r.Le = Real.sqrt r.Le * 1 := by ring
            _ ≤ Real.sqrt r.Le * ((9/1000 : ℝ) * Real.sqrt r.Le) :=
              mul_le_mul_of_nonneg_left h1 hsqrtLe_nonneg
            _ = (9/1000 : ℝ) * ((Real.sqrt r.Le)^2) := by ring
            _ = (9/1000 : ℝ) * r.Le := by rw [Real.sq_sqrt hLe_nonneg]
        linarith
      linarith
    -- bound r.Yb
    have hYb_bound : r.Yb ≤ (383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps := by
      rw [Reg.Yb]
      linarith
    -- combine with kc bound
    have h_main : r.cb ≤ ((383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps) / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
      rw [Reg.cb]
      have hpos_denom : 0 < 2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n := by positivity
      have h1 : r.kc * r.Yb ≤ (1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n)) * r.Yb :=
        mul_le_mul_of_nonneg_right hkc_bound (by
          rw [Reg.Yb]
          positivity)
      have h2 : (1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n)) * r.Yb ≤
                (1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n)) * ((383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps) := by
        refine mul_le_mul_of_nonneg_left hYb_bound ?_
        positivity
      have h3 : (1 / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n)) * ((383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps) =
                ((383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps) / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) := by
        field_simp
      linarith
    -- split into two terms
    have h_split : ((383/1000 : ℝ) * r.Le + 4 * Real.sqrt r.Le / r.eps) / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n) =
                   (383/1000 : ℝ) / (2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n) +
                   4 * Real.sqrt r.Le / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n * r.eps) := by
      field_simp
    -- bound the first term using hnge
    have h_term1 : (383/1000 : ℝ) / (2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n) ≤
                   (383/1000 : ℝ) / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7) := by
      have h_denom : 2899 * 29000 * r.d ^ 2 * r.Le ^ 7 ≤ 2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n := by
        -- From hnge: n ≥ 29000^2 * d^3 * Le^10
        -- Need: 29000 * d * √d * Le^5 ≤ √n
        have h_sqrt_n_ge : 29000 * r.d * Real.sqrt r.d * r.Le ^ 5 ≤ Real.sqrt r.n := by
          have h_sq : (29000 * r.d * Real.sqrt r.d * r.Le ^ 5)^2 ≤ r.n := by
            have hcalc : (29000 * r.d * Real.sqrt r.d * r.Le ^ 5)^2 = (29000 : ℝ)^2 * r.d ^ 3 * r.Le ^ 10 := by
              calc
                (29000 * r.d * Real.sqrt r.d * r.Le ^ 5)^2 = (29000 : ℝ)^2 * (r.d)^2 * ((Real.sqrt r.d)^2) * (r.Le ^ 5)^2 := by ring
                _ = (29000 : ℝ)^2 * r.d ^ 2 * r.d * r.Le ^ 10 := by rw [Real.sq_sqrt hd_nonneg]; ring
                _ = (29000 : ℝ)^2 * r.d ^ 3 * r.Le ^ 10 := by ring
            rw [hcalc]
            exact h.hnge
          have h_nonneg : 0 ≤ 29000 * r.d * Real.sqrt r.d * r.Le ^ 5 := by positivity
          have h_sq' : (29000 * r.d * Real.sqrt r.d * r.Le ^ 5)^2 ≤ (Real.sqrt r.n)^2 := by
            rw [Real.sq_sqrt hn_nonneg]
            exact h_sq
          nlinarith
        -- Now: 29000 * r.d * √d * Le^5 ≤ √n
        -- Multiply by √d: 29000 * r.d * (√d)^2 * Le^5 ≤ √d * √n
        -- = 29000 * r.d^2 * Le^5 ≤ √d * √n
        -- Multiply by Le^2: 29000 * r.d^2 * Le^7 ≤ √d * Le^2 * √n
        -- Multiply by 2899: 2899 * 29000 * r.d^2 * Le^7 ≤ 2899 * √d * Le^2 * √n
        have h_mid : 29000 * r.d ^ 2 * r.Le ^ 5 ≤ Real.sqrt r.d * Real.sqrt r.n := by
          have htemp := mul_le_mul_of_nonneg_right h_sqrt_n_ge hsqrt_d_nonneg
          -- htemp: (29000 * r.d * √d * Le^5) * √d ≤ √n * √d
          -- = 29000 * r.d * (√d)^2 * Le^5 ≤ √d * √n
          -- = 29000 * r.d * r.d * Le^5 ≤ √d * √n
          -- = 29000 * r.d^2 * Le^5 ≤ √d * √n
          calc
            29000 * r.d ^ 2 * r.Le ^ 5 = 29000 * (r.d * r.d) * r.Le ^ 5 := by ring
            _ = 29000 * r.d * r.d * r.Le ^ 5 := by ring
            _ = 29000 * r.d * ((Real.sqrt r.d)^2) * r.Le ^ 5 := by rw [Real.sq_sqrt hd_nonneg]
            _ = (29000 * r.d * Real.sqrt r.d * r.Le ^ 5) * Real.sqrt r.d := by ring
            _ ≤ Real.sqrt r.n * Real.sqrt r.d := htemp
            _ = Real.sqrt r.d * Real.sqrt r.n := mul_comm _ _
        have h_mid2 : 29000 * r.d ^ 2 * r.Le ^ 7 ≤ Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n := by
          -- multiply h_mid by r.Le^2 (nonnegative)
          have htemp := mul_le_mul_of_nonneg_right h_mid (by positivity : 0 ≤ r.Le ^ 2)
          -- htemp: 29000 * r.d^2 * r.Le^5 * r.Le^2 ≤ (√d * √n) * r.Le^2
          -- = 29000 * r.d^2 * r.Le^7 ≤ √d * r.Le^2 * √n
          simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using htemp
        -- multiply by 2899
        have htemp := mul_le_mul_of_nonneg_right h_mid2 (by norm_num : 0 ≤ (2899 : ℝ))
        -- htemp: 2899 * (29000 * r.d^2 * r.Le^7) ≤ 2899 * (√d * r.Le^2 * √n)
        simpa [mul_comm, mul_left_comm, mul_assoc] using htemp
      have h_posA : 0 < 2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n := by positivity
      have h_posB : 0 < 2899 * 29000 * r.d ^ 2 * r.Le ^ 7 := by positivity
      have h_one_div : 1 / (2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n) ≤
                       1 / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7) :=
        (one_div_le_one_div h_posA h_posB).mpr h_denom
      have h_num_nonneg : 0 ≤ (383/1000 : ℝ) := by norm_num
      calc
        (383/1000 : ℝ) / (2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n) =
            (383/1000 : ℝ) * (1 / (2899 * Real.sqrt r.d * r.Le ^ 2 * Real.sqrt r.n)) := by ring
        _ ≤ (383/1000 : ℝ) * (1 / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7)) :=
            mul_le_mul_of_nonneg_left h_one_div h_num_nonneg
        _ = (383/1000 : ℝ) / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7) := by ring
    -- bound the second term using heps and sqrtL_ge
    have h_term2 : 4 * Real.sqrt r.Le / (2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n * r.eps) ≤
                   4 / (2899 * 14500 * 132 * r.d ^ 2 * r.Le ^ 7) := by
      have h_sqrt_n_eps : Real.sqrt r.n * r.eps = 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by
        rw [h.heps]
        field_simp [ne_of_gt hsqrt_n_pos]
      have h_denom_eq : 2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n * r.eps =
                        2899 * 14500 * r.d ^ 2 * r.Le ^ 8 := by
        calc
          2899 * Real.sqrt r.d * r.Le ^ 3 * Real.sqrt r.n * r.eps =
            2899 * Real.sqrt r.d * r.Le ^ 3 * (Real.sqrt r.n * r.eps) := by ring
          _ = 2899 * Real.sqrt r.d * r.Le ^ 3 * (14500 * r.d * Real.sqrt r.d * r.Le ^ 5) := by rw [h_sqrt_n_eps]
          _ = 2899 * 14500 * ((Real.sqrt r.d)^2) * r.d * r.Le ^ 8 := by ring
          _ = 2899 * 14500 * r.d * r.d * r.Le ^ 8 := by rw [Real.sq_sqrt hd_nonneg]
          _ = 2899 * 14500 * r.d ^ 2 * r.Le ^ 8 := by ring
      have h_sqrtLe_bound : Real.sqrt r.Le ≤ r.Le / 132 := by
        have h132 : (132 : ℝ) ≤ Real.sqrt r.Le := hsqrtL_ge
        have h_one_div : 1 / Real.sqrt r.Le ≤ 1 / (132 : ℝ) :=
          (one_div_le_one_div hsqrtLe_pos (by norm_num : 0 < (132 : ℝ))).mpr h132
        calc
          Real.sqrt r.Le = (Real.sqrt r.Le)^2 / Real.sqrt r.Le := by field_simp [ne_of_gt hsqrtLe_pos]
          _ = r.Le / Real.sqrt r.Le := by rw [Real.sq_sqrt hLe_nonneg]
          _ = r.Le * (1 / Real.sqrt r.Le) := by ring
          _ ≤ r.Le * (1 / (132 : ℝ)) := mul_le_mul_of_nonneg_left h_one_div hLe_nonneg
          _ = r.Le / 132 := by ring
      rw [h_denom_eq]
      have h_pos : 0 < 2899 * 14500 * r.d ^ 2 * r.Le ^ 8 := by positivity
      have h_num : 4 * Real.sqrt r.Le ≤ 4 * (r.Le / 132) := by nlinarith
      calc
        4 * Real.sqrt r.Le / (2899 * 14500 * r.d ^ 2 * r.Le ^ 8) ≤
            4 * (r.Le / 132) / (2899 * 14500 * r.d ^ 2 * r.Le ^ 8) :=
          div_le_div_of_nonneg_right h_num (by positivity)
        _ = 4 / (2899 * 14500 * 132 * r.d ^ 2 * r.Le ^ 7) := by
          field_simp
    -- combine the two bounds
    have h_sum : (383/1000 : ℝ) / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7) +
                 4 / (2899 * 14500 * 132 * r.d ^ 2 * r.Le ^ 7) ≤
                 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := by
      have h_factor : (383/1000 : ℝ) / (2899 * 29000 * r.d ^ 2 * r.Le ^ 7) +
                      4 / (2899 * 14500 * 132 * r.d ^ 2 * r.Le ^ 7) =
                      ((383/1000 : ℝ) / (2899 * 29000) + 4 / (2899 * 14500 * 132)) / (r.d ^ 2 * r.Le ^ 7) := by
        field_simp
      rw [h_factor]
      have h_num : (383/1000 : ℝ) / (2899 * 29000) + 4 / (2899 * 14500 * 132) ≤ 54 / 10 ^ 10 := by
        norm_num
      have h_denom_nonneg : 0 ≤ r.d ^ 2 * r.Le ^ 7 := by positivity
      exact div_le_div_of_nonneg_right h_num h_denom_nonneg
    -- put everything together
    linarith
  exact And.intro hcb_nonneg hcb_upper

theorem Dc_le (h : r.OK) : 0 ≤ r.Dc ∧ r.Dc ≤ 35 / 100 * r.cb * r.tp := by
  have htp_nonneg : 0 ≤ r.tp := le_of_lt h.htp0
  have hcb_nonneg : 0 ≤ r.cb := (cb_le h).1
  have hPb_lower : 1 ≤ r.Pb := (Pb_pib h).1
  have hPb_upper : r.Pb ≤ 201 / 100 * Real.sqrt r.Le := (Pb_pib h).2.1
  have hYb_lower : 8 * Real.sqrt r.Le ≤ r.Yb := (Yb_bd h).1
  have hsqrtL_ge : 132 ≤ Real.sqrt r.Le := sqrtL_ge h
  have hsqrtL_pos : 0 < Real.sqrt r.Le := by linarith
  have hYb_pos : 0 < r.Yb := by linarith
  have h_bound : (r.Pb + 1) / r.Yb ≤ ((201 : ℝ) / 100 + 1 / 132) / 8 := by
    have h_num : r.Pb + 1 ≤ 201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132 := by
      have h1 : 1 ≤ Real.sqrt r.Le / 132 := by linarith
      linarith
    have h_nonneg_num : 0 ≤ r.Pb + 1 := by linarith
    have h_nonneg_denom : 0 < 8 * Real.sqrt r.Le := by nlinarith
    have h_nonneg_c : 0 ≤ 201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132 := by nlinarith
    have h_div1 : (r.Pb + 1) / r.Yb ≤ (201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132) / r.Yb :=
      div_le_div_of_nonneg_right h_num (by linarith)
    have h_div2 : (201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132) / r.Yb ≤
        (201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132) / (8 * Real.sqrt r.Le) :=
      div_le_div_of_nonneg_left h_nonneg_c h_nonneg_denom hYb_lower
    have h_div : (r.Pb + 1) / r.Yb ≤ (201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132) / (8 * Real.sqrt r.Le) :=
      le_trans h_div1 h_div2
    have h_simplify : (201 / 100 * Real.sqrt r.Le + Real.sqrt r.Le / 132) / (8 * Real.sqrt r.Le) = ((201 : ℝ) / 100 + 1 / 132) / 8 := by
      field_simp [hsqrtL_pos.ne']
    rw [h_simplify] at h_div
    exact h_div
  have h_inner : 11 / 10 * ((r.Pb + 1) / r.Yb) + 1 / 16 ≤ 35 / 100 := by
    have h_mul : 11 / 10 * ((r.Pb + 1) / r.Yb) ≤ 11 / 10 * (((201 : ℝ) / 100 + 1 / 132) / 8) := by
      nlinarith
    have h_total : 11 / 10 * (((201 : ℝ) / 100 + 1 / 132) / 8) + 1 / 16 ≤ 35 / 100 := by
      norm_num
    linarith
  constructor
  · unfold Dc
    rw [mul_div_assoc]
    have h_inner_nonneg : 0 ≤ 11 / 10 * ((r.Pb + 1) / r.Yb) + 1 / 16 := by
      have hdiv : 0 ≤ (r.Pb + 1) / r.Yb := div_nonneg (by linarith) (by linarith)
      nlinarith
    have h_prod1 : 0 ≤ r.cb * r.tp := mul_nonneg hcb_nonneg htp_nonneg
    exact mul_nonneg h_prod1 h_inner_nonneg
  · unfold Dc
    rw [mul_div_assoc]
    have h_main : r.cb * r.tp * (11 / 10 * ((r.Pb + 1) / r.Yb) + 1 / 16) ≤ r.cb * r.tp * (35 / 100) := by
      apply mul_le_mul_of_nonneg_left h_inner
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_main

theorem eN_le (h : r.OK) : 0 ≤ r.eN ∧ r.eN ≤ 58 / 1000 * r.d * r.Le * r.tp := by
  have htp0' : 0 ≤ r.tp := le_of_lt h.htp0
  have hd0 : 0 ≤ r.d := le_trans (by norm_num : (0:ℝ) ≤ 1) h.hd
  have hLe0 : 0 ≤ r.Le := le_trans (by norm_num : (0:ℝ) ≤ 17467) h.hL1
  have hDc_nonneg : 0 ≤ r.Dc := (h.Dc_le).1
  have hcb_nonneg : 0 ≤ r.cb := (h.cb_le).1
  have hXi_nonneg : 0 ≤ r.Xi := (h.Xi1_le).1
  have hXi_le_Xi1 : r.Xi ≤ r.Xi1 := (h.Xi1_le).2.1
  have hXi1_nonneg : 0 ≤ r.Xi1 := by linarith
  have hex_nonneg : 0 ≤ r.exi := (h.ezt_exi).2.2.1
  have h_one_plus_sq_le : 1 + r.Xi1 ^ 2 ≤ r.d * r.Le / 9 := (h.Xi_bd).2.1
  have hXi_lo : 402/10 ≤ r.Xi := (h.Xi_bd).1
  have hXi1_sq_ge : 1697 ≤ r.Xi1 ^ 2 := by
    have hXi1_eq : r.Xi1 = r.Xi + 1 := rfl
    nlinarith
  have h_term1_coeff : 1001/1000 + 51/100 * r.Xi1 ^ 2 ≤ 5199/10000 * (1 + r.Xi1 ^ 2) := by
    nlinarith
  have hDc_le' : r.Dc ≤ 35/100 * r.cb * r.tp := (h.Dc_le).2
  have hex_le' : r.exi ≤ r.tp / 2 := (h.ezt_exi).2.2.2
  have hXi1_le_one_plus_sq : r.Xi1 ≤ 1 + r.Xi1 ^ 2 := by
    nlinarith
  have hXi1_le_dLe9 : r.Xi1 ≤ r.d * r.Le / 9 := by
    linarith
  have hd_pos : 0 < r.d := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) h.hd
  have hLe_pos : 0 < r.Le := lt_of_lt_of_le (by norm_num : (0:ℝ) < 17467) h.hL1
  have hpos_denom : 0 < r.d ^ 2 * r.Le ^ 7 := by
    positivity
  have hcb_le' : r.cb ≤ 54/10^10 / (r.d ^ 2 * r.Le ^ 7) := (h.cb_le).2
  have h_denom_ge : (17467 : ℝ)^7 ≤ r.d ^ 2 * r.Le ^ 7 := by
    have hd_sq : (1 : ℝ)^2 ≤ r.d^2 := pow_le_pow_left₀ (by linarith) h.hd 2
    have hLe_pow : (17467 : ℝ)^7 ≤ r.Le^7 := pow_le_pow_left₀ (by linarith) h.hL1 7
    calc
      (17467 : ℝ)^7 = (1 : ℝ)^2 * (17467 : ℝ)^7 := by norm_num
      _ ≤ r.d^2 * r.Le^7 := mul_le_mul hd_sq hLe_pow (by positivity) (by positivity)
  have hcb_le_denom : r.cb ≤ 54/10^10 / ((17467 : ℝ)^7) := by
    apply le_trans hcb_le'
    have h17467pos : 0 < (17467 : ℝ)^7 := by norm_num
    have h_one_div : 1 / (r.d ^ 2 * r.Le ^ 7) ≤ 1 / ((17467 : ℝ)^7) := by
      refine ((one_div_le_one_div hpos_denom h17467pos).mpr h_denom_ge)
    have hpos : 0 ≤ (54/10^10 : ℝ) := by norm_num
    have h := mul_le_mul_of_nonneg_left h_one_div hpos
    simpa [div_eq_mul_inv] using h
  have hcb_small : r.cb ≤ 21/192550 := by
    apply le_trans hcb_le_denom
    have h_one_le : (1 : ℝ) ≤ (17467 : ℝ)^7 := by
      have h17467 : (1 : ℝ) ≤ (17467 : ℝ) := by norm_num
      calc
        (1 : ℝ) = (1 : ℝ)^7 := by norm_num
        _ ≤ (17467 : ℝ)^7 := pow_le_pow_left₀ (by norm_num) h17467 7
    have h_div1 : (54 : ℝ)/10^10 / ((17467 : ℝ)^7) ≤ (54 : ℝ)/10^10 := by
      have ha : 0 ≤ ((54 : ℝ)/10^10) := by norm_num
      exact div_le_self ha h_one_le
    have h_div2 : (54 : ℝ)/10^10 ≤ (21 : ℝ)/192550 := by norm_num
    exact le_trans h_div1 h_div2
  have h_nonneg : 0 ≤ r.eN := by
    rw [AdversarialBco.Bit.PieceA.Reg.eN]
    positivity
  have h_bound : r.eN ≤ 58 / 1000 * r.d * r.Le * r.tp := by
    rw [AdversarialBco.Bit.PieceA.Reg.eN]
    have h1 : r.tp * (1001/1000 + 51/100 * r.Xi1 ^ 2) ≤ r.tp * (5199/10000) * (1 + r.Xi1 ^ 2) := by
      nlinarith
    have h2 : 143/100 * (1 + r.Xi1 ^ 2) * r.Dc ≤ 143/100 * (1 + r.Xi1 ^ 2) * (35/100 * r.cb * r.tp) := by
      nlinarith
    have h3 : 285/100 * r.cb * r.Xi1 * r.exi ≤ 285/100 * r.cb * r.Xi1 * (r.tp / 2) := by
      have h_nonneg_coeff : 0 ≤ 285/100 * r.cb * r.Xi1 := by positivity
      apply mul_le_mul_of_nonneg_left hex_le' h_nonneg_coeff
    have hsum : r.tp * (1001/1000 + 51/100 * r.Xi1 ^ 2) + 143/100 * (1 + r.Xi1 ^ 2) * r.Dc + 285/100 * r.cb * r.Xi1 * r.exi
      ≤ r.tp * (5199/10000) * (1 + r.Xi1 ^ 2) + 143/100 * (1 + r.Xi1 ^ 2) * (35/100 * r.cb * r.tp) + 285/100 * r.cb * r.Xi1 * (r.tp / 2) := by
      nlinarith
    have hfinal : r.tp * (5199/10000) * (1 + r.Xi1 ^ 2) + 143/100 * (1 + r.Xi1 ^ 2) * (35/100 * r.cb * r.tp) + 285/100 * r.cb * r.Xi1 * (r.tp / 2)
      ≤ 58 / 1000 * r.d * r.Le * r.tp := by
      have hineq : (5199/10000 : ℝ) * (1 + r.Xi1 ^ 2) + (143*35/10000 : ℝ) * (1 + r.Xi1 ^ 2) * r.cb + (285/200 : ℝ) * r.cb * r.Xi1
        ≤ (58/1000 : ℝ) * r.d * r.Le := by
        have h_sq_le : 1 + r.Xi1 ^ 2 ≤ r.d * r.Le / 9 := h_one_plus_sq_le
        have h_Xi1_le : r.Xi1 ≤ r.d * r.Le / 9 := hXi1_le_dLe9
        have h_cb_le : r.cb ≤ 21/192550 := hcb_small
        have h_nonneg_coeff1 : 0 ≤ (5199/10000 : ℝ) := by norm_num
        have h_nonneg_coeff2 : 0 ≤ (143*35/10000 : ℝ) := by norm_num
        have h_nonneg_coeff3 : 0 ≤ (285/200 : ℝ) := by norm_num
        have h_term1 : (5199/10000 : ℝ) * (1 + r.Xi1 ^ 2) ≤ (5199/10000 : ℝ) * (r.d * r.Le / 9) := by
          apply mul_le_mul_of_nonneg_left h_sq_le h_nonneg_coeff1
        have h_term2 : (143*35/10000 : ℝ) * (1 + r.Xi1 ^ 2) * r.cb ≤ (143*35/10000 : ℝ) * (r.d * r.Le / 9) * r.cb := by
          have h := mul_le_mul_of_nonneg_left h_sq_le (mul_nonneg h_nonneg_coeff2 hcb_nonneg)
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have h_term3 : (285/200 : ℝ) * r.cb * r.Xi1 ≤ (285/200 : ℝ) * r.cb * (r.d * r.Le / 9) := by
          have h := mul_le_mul_of_nonneg_left h_Xi1_le (mul_nonneg h_nonneg_coeff3 hcb_nonneg)
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have h_sum : (5199/10000 : ℝ) * (1 + r.Xi1 ^ 2) + (143*35/10000 : ℝ) * (1 + r.Xi1 ^ 2) * r.cb + (285/200 : ℝ) * r.cb * r.Xi1
          ≤ (5199/10000 : ℝ) * (r.d * r.Le / 9) + (143*35/10000 : ℝ) * (r.d * r.Le / 9) * r.cb + (285/200 : ℝ) * r.cb * (r.d * r.Le / 9) := by
          linarith
        have h_factor : (5199/10000 : ℝ) * (r.d * r.Le / 9) + (143*35/10000 : ℝ) * (r.d * r.Le / 9) * r.cb + (285/200 : ℝ) * r.cb * (r.d * r.Le / 9)
          = (r.d * r.Le / 9) * ((5199/10000 : ℝ) + (143*35/10000 : ℝ) * r.cb + (285/200 : ℝ) * r.cb) := by
          ring
        rw [h_factor] at h_sum
        have h_coeff : (5199/10000 : ℝ) + (143*35/10000 : ℝ) * r.cb + (285/200 : ℝ) * r.cb ≤ (5199/10000 : ℝ) + (21/100000 : ℝ) := by
          have h_cb_term : (143*35/10000 : ℝ) * r.cb + (285/200 : ℝ) * r.cb ≤
            (143*35/10000 : ℝ) * (21/192550 : ℝ) + (285/200 : ℝ) * (21/192550 : ℝ) := by
            have h_nonneg1 : 0 ≤ (143*35/10000 : ℝ) := by norm_num
            have h_nonneg2 : 0 ≤ (285/200 : ℝ) := by norm_num
            nlinarith
          have h_const : (143*35/10000 : ℝ) * (21/192550 : ℝ) + (285/200 : ℝ) * (21/192550 : ℝ) = (21/100000 : ℝ) := by
            norm_num
          linarith
        have h_final : (r.d * r.Le / 9) * ((5199/10000 : ℝ) + (21/100000 : ℝ)) ≤ (58/1000 : ℝ) * r.d * r.Le := by
          have h_left : (r.d * r.Le / 9) * ((5199/10000 : ℝ) + (21/100000 : ℝ)) = (r.d * r.Le) * (52011/900000 : ℝ) := by
            ring
          have h_right : (58/1000 : ℝ) * r.d * r.Le = (r.d * r.Le) * (52200/900000 : ℝ) := by
            ring
          rw [h_left, h_right]
          have hdLe_nonneg : 0 ≤ r.d * r.Le := mul_nonneg hd0 hLe0
          have h_frac : (52011/900000 : ℝ) ≤ (52200/900000 : ℝ) := by norm_num
          exact mul_le_mul_of_nonneg_left h_frac hdLe_nonneg
        apply le_trans h_sum
        calc
          (r.d * r.Le / 9) * ((5199/10000 : ℝ) + (143*35/10000 : ℝ) * r.cb + (285/200 : ℝ) * r.cb)
          ≤ (r.d * r.Le / 9) * ((5199/10000 : ℝ) + (21/100000 : ℝ)) := by
            have h_nonneg_dLe : 0 ≤ r.d * r.Le / 9 := by
              have hdLe_nonneg : 0 ≤ r.d * r.Le := mul_nonneg hd0 hLe0
              nlinarith
            apply mul_le_mul_of_nonneg_left h_coeff h_nonneg_dLe
          _ ≤ (58/1000 : ℝ) * r.d * r.Le := h_final
      have hgoal_eq : r.tp * (5199/10000) * (1 + r.Xi1 ^ 2) + 143/100 * (1 + r.Xi1 ^ 2) * (35/100 * r.cb * r.tp) + 285/100 * r.cb * r.Xi1 * (r.tp / 2)
        = r.tp * ((5199/10000 : ℝ) * (1 + r.Xi1 ^ 2) + (143*35/10000 : ℝ) * (1 + r.Xi1 ^ 2) * r.cb + (285/200 : ℝ) * r.cb * r.Xi1) := by
        ring
      have hRHS_eq : 58 / 1000 * r.d * r.Le * r.tp = r.tp * ((58/1000 : ℝ) * r.d * r.Le) := by ring
      rw [hgoal_eq, hRHS_eq]
      exact mul_le_mul_of_nonneg_left hineq htp0'
    exact le_trans hsum hfinal
  exact And.intro h_nonneg h_bound

theorem ha_le (h : r.OK) : r.tp ≤ r.ha ∧ r.ha ≤ 284 / 100 * Real.sqrt r.Le * r.tp := by
  have htp_pos : 0 < r.tp := h.htp0
  have hsqrtL_ge : 132 ≤ Real.sqrt r.Le := by
    have hsq : (132 : ℝ) ^ 2 = 17424 := by norm_num
    have hle : (132 : ℝ) ^ 2 ≤ r.Le := by
      have : 17467 ≤ r.Le := h.hL1
      linarith
    calc
      132 = Real.sqrt ((132 : ℝ) ^ 2) := by
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (132 : ℝ))]
      _ ≤ Real.sqrt r.Le := Real.sqrt_le_sqrt hle
  have hsqrt8 : Real.sqrt 8 ≤ 28285/10000 := by
    have hsq : (8 : ℝ) ≤ ((28285 : ℝ) / 10000) ^ 2 := by norm_num
    calc
      Real.sqrt 8 ≤ Real.sqrt (((28285 : ℝ) / 10000) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 28285/10000 := Real.sqrt_sq (by norm_num : 0 ≤ (28285/10000 : ℝ))
  have h_sqrt_mul : Real.sqrt (8 * r.Le) = Real.sqrt 8 * Real.sqrt r.Le := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (8 : ℝ)) r.Le]
  have h_lower : r.tp ≤ r.ha := by
    dsimp [AdversarialBco.Bit.PieceA.Reg.ha]
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (8 * r.Le) := Real.sqrt_nonneg _
    nlinarith
  have h_upper : r.ha ≤ 284 / 100 * Real.sqrt r.Le * r.tp := by
    dsimp [AdversarialBco.Bit.PieceA.Reg.ha]
    rw [h_sqrt_mul]
    have h_diff : (284/100 : ℝ) - Real.sqrt 8 ≥ 115/10000 := by
      linarith
    have h_prod : (17/16 : ℝ) ≤ ((284/100 : ℝ) - Real.sqrt 8) * Real.sqrt r.Le := by
      have h1 : ((284/100 : ℝ) - Real.sqrt 8) * Real.sqrt r.Le ≥ (115/10000 : ℝ) * 132 := by
        nlinarith
      have h2 : (115/10000 : ℝ) * 132 = 15180/10000 := by norm_num
      have h3 : (17/16 : ℝ) ≤ 15180/10000 := by norm_num
      linarith
    nlinarith
  exact And.intro h_lower h_upper

theorem x_bd (h : r.OK) : 0 ≤ r.x ∧ r.x ≤ r.d ^ 2 * r.Q ^ 51 * r.tp / 500 := by
  have hd0 : 0 ≤ r.d := le_trans (by norm_num : (0:ℝ) ≤ 1) h.hd
  have hn0 : 0 ≤ r.n := le_trans (by norm_num : (0:ℝ) ≤ 1) h.hn
  have hQ0' : 0 ≤ r.Q := h.hQ0.le
  have htp0' : 0 ≤ r.tp := h.htp0.le
  have hNe0 : 0 ≤ r.Ne := by
    rw [h.hNe]
    positivity
  have heN0 : 0 ≤ r.eN := (eN_le h).left
  have hx_nonneg : 0 ≤ r.x := by
    rw [AdversarialBco.Bit.PieceA.Reg.x]
    unfold AdversarialBco.Bit.PieceA.Reg.Lam
    positivity
  have h_bound : r.x ≤ r.d ^ 2 * r.Q ^ 51 * r.tp / 500 := by
    have hQbd := Q_bd h
    have hn_bound : 32 * r.n ≤ r.Q ^ 10 := hQbd.right.right.left
    have hLe_bound : 10 * r.Le ≤ r.Q := hQbd.right.left
    have heN_bound : r.eN ≤ 58 / 1000 * r.d * r.Le * r.tp := (eN_le h).right
    have hn_bound' : r.n ≤ r.Q ^ 10 / 32 := by linarith
    have hLe_bound' : r.Le ≤ r.Q / 10 := by linarith
    have hx_eq : r.x = r.n * r.d * r.Ne * r.eN := by
      rw [AdversarialBco.Bit.PieceA.Reg.x, AdversarialBco.Bit.PieceA.Reg.Lam]
      ring
    rw [hx_eq, ← h.hQ]
    have h_mul : r.n * r.d * (r.Q ^ 40) * r.eN ≤ (r.Q ^ 10 / 32) * r.d * (r.Q ^ 40) * (58 / 1000 * r.d * r.Le * r.tp) := by
      have h_n_nonneg : 0 ≤ r.n := hn0
      have h_d_nonneg : 0 ≤ r.d := hd0
      have h_Q40_nonneg : 0 ≤ r.Q ^ 40 := by positivity
      have h_eN_nonneg : 0 ≤ r.eN := heN0
      have h1 : r.n * r.d * (r.Q ^ 40) * r.eN ≤ (r.Q ^ 10 / 32) * r.d * (r.Q ^ 40) * r.eN := by
        apply mul_le_mul_of_nonneg_right ?_ h_eN_nonneg
        apply mul_le_mul_of_nonneg_right ?_ h_Q40_nonneg
        apply mul_le_mul_of_nonneg_right hn_bound' h_d_nonneg
      have h2 : (r.Q ^ 10 / 32) * r.d * (r.Q ^ 40) * r.eN ≤ (r.Q ^ 10 / 32) * r.d * (r.Q ^ 40) * (58 / 1000 * r.d * r.Le * r.tp) := by
        apply mul_le_mul_of_nonneg_left heN_bound
        positivity
      exact le_trans h1 h2
    calc
      r.n * r.d * (r.Q ^ 40) * r.eN ≤ (r.Q ^ 10 / 32) * r.d * (r.Q ^ 40) * (58 / 1000 * r.d * r.Le * r.tp) := h_mul
      _ = (58 / 32000) * r.d ^ 2 * r.Q ^ 50 * r.Le * r.tp := by ring
      _ ≤ (58 / 32000) * r.d ^ 2 * r.Q ^ 50 * (r.Q / 10) * r.tp := by
        have hpos : 0 ≤ (58 / 32000) * r.d ^ 2 * r.Q ^ 50 * r.tp := by positivity
        have htemp : ((58 / 32000) * r.d ^ 2 * r.Q ^ 50 * r.tp) * r.Le ≤ ((58 / 32000) * r.d ^ 2 * r.Q ^ 50 * r.tp) * (r.Q / 10) :=
          mul_le_mul_of_nonneg_left hLe_bound' hpos
        simpa [mul_comm, mul_left_comm, mul_assoc] using htemp
      _ = (58 / 320000) * r.d ^ 2 * r.Q ^ 51 * r.tp := by ring
      _ ≤ (1 / 500) * r.d ^ 2 * r.Q ^ 51 * r.tp := by
        have hcoeff : (58 : ℝ) / 320000 ≤ (1 : ℝ) / 500 := by norm_num
        have hpos2 : 0 ≤ r.d ^ 2 * r.Q ^ 51 * r.tp := by positivity
        have htemp := mul_le_mul_of_nonneg_right hcoeff hpos2
        simpa [mul_comm, mul_left_comm, mul_assoc] using htemp
      _ = r.d ^ 2 * r.Q ^ 51 * r.tp / 500 := by ring
  exact And.intro hx_nonneg h_bound

theorem V_bd (h : r.OK) : 0 ≤ r.V ∧ r.V ≤ r.d ^ 2 * r.Q ^ 30 * r.tp := by
  unfold Reg.V Reg.nu
  rcases h.sqrtLam with ⟨hsqrt_nonneg, hsqrt_le⟩
  rcases h.Q_bd with ⟨_, _, hnQ, _, _, _⟩
  have hn_nonneg : 0 ≤ r.n := by linarith [h.hn]
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have htp_nonneg : 0 ≤ r.tp := by linarith [h.htp0]
  have hQ_nonneg : 0 ≤ r.Q := by
    have : 0 < r.Q := h.hQ0
    linarith
  constructor
  · -- 0 ≤ r.n * Real.sqrt (Lam r) * (r.d * r.tp / 2)
    apply mul_nonneg (mul_nonneg hn_nonneg hsqrt_nonneg)
    apply div_nonneg (mul_nonneg hd_nonneg htp_nonneg)
    norm_num
  · -- r.n * Real.sqrt (Lam r) * (r.d * r.tp / 2) ≤ r.d ^ 2 * r.Q ^ 30 * r.tp
    have hprod_nonneg : 0 ≤ r.n * Real.sqrt (Lam r) * (r.d * r.tp / 2) := by
      apply mul_nonneg (mul_nonneg hn_nonneg hsqrt_nonneg)
      apply div_nonneg (mul_nonneg hd_nonneg htp_nonneg)
      norm_num
    have htarget_nonneg : 0 ≤ r.d ^ 2 * r.Q ^ 30 * r.tp := by
      apply mul_nonneg (mul_nonneg (pow_two_nonneg _) (pow_nonneg hQ_nonneg _))
      exact htp_nonneg
    have h1 : r.n * Real.sqrt (Lam r) * (r.d * r.tp / 2) ≤ (r.Q ^ 10 / 32) * (r.d * r.Q ^ 20) * (r.d * r.tp / 2) := by
      have h_n_le : r.n ≤ r.Q ^ 10 / 32 := by linarith
      have h_sqrt_le : Real.sqrt (Lam r) ≤ r.d * r.Q ^ 20 := hsqrt_le
      have h_d_tp_div2_nonneg : 0 ≤ r.d * r.tp / 2 := by
        apply div_nonneg (mul_nonneg hd_nonneg htp_nonneg)
        norm_num
      have h_mid_nonneg : 0 ≤ Real.sqrt (Lam r) := hsqrt_nonneg
      have h_mid2_nonneg : 0 ≤ r.n * (r.d * r.tp / 2) := mul_nonneg hn_nonneg h_d_tp_div2_nonneg
      calc
        r.n * Real.sqrt (Lam r) * (r.d * r.tp / 2) = (r.n * (r.d * r.tp / 2)) * Real.sqrt (Lam r) := by ring
        _ ≤ (r.n * (r.d * r.tp / 2)) * (r.d * r.Q ^ 20) := by
          apply mul_le_mul_of_nonneg_left h_sqrt_le h_mid2_nonneg
        _ = r.n * (r.d * r.Q ^ 20) * (r.d * r.tp / 2) := by ring
        _ ≤ (r.Q ^ 10 / 32) * (r.d * r.Q ^ 20) * (r.d * r.tp / 2) := by
          apply mul_le_mul_of_nonneg_right ?_ h_d_tp_div2_nonneg
          apply mul_le_mul_of_nonneg_right h_n_le
          apply mul_nonneg hd_nonneg (pow_nonneg hQ_nonneg _)
    have h2 : (r.Q ^ 10 / 32) * (r.d * r.Q ^ 20) * (r.d * r.tp / 2) = r.d ^ 2 * r.Q ^ 30 * r.tp / 64 := by
      ring
    have h3 : r.d ^ 2 * r.Q ^ 30 * r.tp / 64 ≤ r.d ^ 2 * r.Q ^ 30 * r.tp := by
      have h64one : (1 : ℝ) ≤ 64 := by norm_num
      exact div_le_self htarget_nonneg h64one
    nlinarith

theorem hb_bd (h : r.OK) : 0 ≤ r.hb ∧ r.hb ≤ r.d ^ 2 * r.Q ^ 51 * r.tp := by
  have hd : 1 ≤ r.d := h.hd
  have htp0 : 0 < r.tp := h.htp0
  have htp_nonneg : 0 ≤ r.tp := le_of_lt htp0
  have hQ0 : 0 < r.Q := h.hQ0
  have hQ17 : (2:ℝ)^17 ≤ r.Q := (Q_bd h).1
  have hQ_ge_1 : 1 ≤ r.Q := by
    have h_one_le_2pow17 : (1:ℝ) ≤ (2:ℝ)^17 := by norm_num
    linarith
  have hLe_nonneg : 0 ≤ r.Le := by linarith [h.hL1]
  have hLe_ge_1 : 1 ≤ r.Le := by linarith [h.hL1]
  have hLQ : 10 * r.Le ≤ r.Q := (Q_bd h).2.1
  have ha_le := ha_le h
  have ha_nonneg : 0 ≤ r.ha := by
    have : r.tp ≤ r.ha := ha_le.1
    linarith
  have ha_le_val : r.ha ≤ 284/100 * Real.sqrt r.Le * r.tp := ha_le.2
  have sqrtL_ge := sqrtL_ge h
  have sqrtL_le_Le : Real.sqrt r.Le ≤ r.Le := by
    simpa using (Real.sqrt_le_self_iff.mpr (Or.inr hLe_ge_1))
  have sqrtL_le_Q_div_10 : Real.sqrt r.Le ≤ r.Q / 10 := by
    calc
      Real.sqrt r.Le ≤ r.Le := sqrtL_le_Le
      _ ≤ r.Q / 10 := by linarith
  have ha_le_Q_tp : r.ha ≤ 284/100 * (r.Q / 10) * r.tp := by
    nlinarith
  -- prove ha ≤ 1 using tiny h 0 1
  have ha_le_one : r.ha ≤ 1 := by
    have h_tiny := tiny h 0 1 (by omega) (by omega)
    -- h_tiny : r.d ^ 0 * r.Q ^ 1 * r.tp ≤ 1 / 2 ^ 160
    have hQtp_le : r.Q * r.tp ≤ 1 / ((2:ℝ) ^ 160) := by
      simpa [pow_zero, pow_one] using h_tiny
    have ha_le_284_1000_Q_tp : r.ha ≤ 284/1000 * r.Q * r.tp := by
      nlinarith
    have h_bound : 284/1000 * (1 / ((2:ℝ) ^ 160)) ≤ 1 := by
      have h2pow_pos : (0:ℝ) < (2:ℝ)^160 := by norm_num
      have h_ineq : (284/1000 : ℝ) ≤ (2:ℝ)^160 := by norm_num
      nlinarith
    calc
      r.ha ≤ 284/1000 * r.Q * r.tp := ha_le_284_1000_Q_tp
      _ ≤ 284/1000 * (1 / ((2:ℝ) ^ 160)) := by nlinarith
      _ ≤ 1 := h_bound
  have ha_le_0_01_d2_Q51_tp : r.ha ≤ 1/100 * r.d ^ 2 * r.Q ^ 51 * r.tp := by
    have hd2 : 1 ≤ r.d ^ 2 := by nlinarith
    have hQ_ge_2 : (2:ℝ) ≤ r.Q := by linarith
    have hQ50_ge_284_10 : (284/10 : ℝ) ≤ r.Q ^ 50 := by
      have h2_50 : (2:ℝ)^50 ≤ r.Q ^ 50 := pow_le_pow_left₀ (by norm_num) hQ_ge_2 50
      have h_const : (284/10 : ℝ) ≤ (2:ℝ)^50 := by norm_num
      linarith
    have h_ineq : 284/10 * r.Q ≤ r.d ^ 2 * r.Q ^ 51 := by
      have hQpos : 0 ≤ r.Q := le_of_lt hQ0
      calc
        284/10 * r.Q ≤ (r.Q ^ 50) * r.Q := by
          nlinarith
        _ = r.Q ^ 51 := by ring
        _ = 1 * r.Q ^ 51 := by ring
        _ ≤ r.d ^ 2 * r.Q ^ 51 :=
          mul_le_mul_of_nonneg_right hd2 (pow_nonneg (by linarith) 51)
    calc
      r.ha ≤ 284/100 * (r.Q / 10) * r.tp := ha_le_Q_tp
      _ = 284/1000 * r.Q * r.tp := by ring
      _ = (284/10) * (1/100) * r.Q * r.tp := by ring
      _ ≤ (r.d ^ 2 * r.Q ^ 51) * (1/100) * r.tp := by nlinarith
      _ = 1/100 * r.d ^ 2 * r.Q ^ 51 * r.tp := by ring
  have V_bd := V_bd h
  have x_bd := x_bd h
  have h_nonneg : 0 ≤ r.hb := by
    dsimp [Reg.hb]
    have hx_nonneg : 0 ≤ r.x := x_bd.1
    have hV_nonneg : 0 ≤ r.V := V_bd.1
    nlinarith
  have h_upper : r.hb ≤ r.d ^ 2 * r.Q ^ 51 * r.tp := by
    dsimp [Reg.hb]
    have hV : r.V ≤ r.d ^ 2 * r.Q ^ 30 * r.tp := V_bd.2
    have hx : r.x ≤ r.d ^ 2 * r.Q ^ 51 * r.tp / 500 := x_bd.2
    have hx_nonneg : 0 ≤ r.x := x_bd.1
    have h_2x2ha : 2 * r.x * (2 + r.ha) ≤ 6 * r.x := by
      nlinarith
    have hx_final : 6 * r.x ≤ 3/250 * r.d ^ 2 * r.Q ^ 51 * r.tp := by
      nlinarith
    have hQ21_ge_100 : (100 : ℝ) ≤ r.Q ^ 21 := by
      have hQ_ge_2 : (2:ℝ) ≤ r.Q := by linarith
      have h2_21 : (2:ℝ)^21 ≤ r.Q ^ 21 := pow_le_pow_left₀ (by norm_num) hQ_ge_2 21
      have h_const : (100 : ℝ) ≤ (2:ℝ)^21 := by norm_num
      linarith
    have hQ30_le : r.d ^ 2 * r.Q ^ 30 * r.tp ≤ 1/100 * r.d ^ 2 * r.Q ^ 51 * r.tp := by
      have hd2_nonneg : 0 ≤ r.d ^ 2 := pow_two_nonneg r.d
      have hQ_nonneg : 0 ≤ r.Q := le_of_lt hQ0
      have hQ30_nonneg : 0 ≤ r.Q ^ 30 := pow_nonneg hQ_nonneg 30
      have h_ineq' : r.Q ^ 30 ≤ 1/100 * r.Q ^ 51 := by
        have hdiv : (1 : ℝ) ≤ r.Q ^ 21 / 100 := by linarith
        calc
          r.Q ^ 30 = 1 * r.Q ^ 30 := by ring
          _ ≤ (r.Q ^ 21 / 100) * r.Q ^ 30 :=
            mul_le_mul_of_nonneg_right hdiv hQ30_nonneg
          _ = (r.Q ^ 21 * r.Q ^ 30) / 100 := by ring
          _ = r.Q ^ 51 / 100 := by ring
          _ = 1/100 * r.Q ^ 51 := by ring
      nlinarith
    nlinarith
  exact And.intro h_nonneg h_upper

theorem p1 (h : r.OK) : r.x ≤ 1 ∧ r.V ≤ 1 ∧ r.hb ≤ 1 / 100 := by
  rcases OK.x_bd h with ⟨hx_nonneg, hx⟩
  rcases OK.V_bd h with ⟨hV_nonneg, hV⟩
  rcases OK.hb_bd h with ⟨hb_nonneg, hb⟩
  have htiny51 := OK.tiny h 2 51 (by norm_num) (by norm_num)
  have htiny30 := OK.tiny h 2 30 (by norm_num) (by norm_num)
  have hpos2 : 0 < (2 : ℝ) ^ 160 := by norm_num
  have hx' : r.x ≤ 1 := by
    apply le_trans hx
    rw [div_le_one (by norm_num : 0 < (500 : ℝ))]
    have : (1 : ℝ) / 2 ^ 160 ≤ 500 := by
      have : (1 : ℝ) / 2 ^ 160 ≤ 1 := (div_le_one hpos2).mpr (by norm_num)
      linarith
    linarith
  have hV' : r.V ≤ 1 := by
    apply le_trans hV
    have : (1 : ℝ) / 2 ^ 160 ≤ 1 := (div_le_one hpos2).mpr (by norm_num)
    linarith
  have hb' : r.hb ≤ 1 / 100 := by
    apply le_trans hb
    have : (1 : ℝ) / 2 ^ 160 ≤ 1 / 100 := by norm_num
    linarith
  exact ⟨hx', hV', hb'⟩

theorem hTr_le (h : r.OK) : ∀ k : ℕ, (k : ℝ) ≤ r.n → r.hTr k ≤ r.hb := by
  have htp_pos : 0 < r.tp := h.htp0
  have hd_pos : 0 < r.d := by linarith [h.hd]
  have hn_pos : 0 < r.n := by linarith [h.hn]
  have hNe_pos : 0 < r.Ne := by
    have hN700 : (2 : ℝ) ^ 700 < r.Ne := h.hN700
    have h_pos : 0 < (2 : ℝ) ^ 700 := pow_pos (by norm_num) 700
    exact lt_trans h_pos hN700
  have hLam_nonneg : 0 ≤ r.Lam := by
    dsimp [Reg.Lam]
    have hd_nonneg : 0 ≤ r.d := by linarith
    exact mul_nonneg hd_nonneg hNe_pos.le
  have hLam_pos : 0 < r.Lam := by
    dsimp [Reg.Lam]
    exact mul_pos hd_pos hNe_pos
  have hsqrtLam_nonneg : 0 ≤ Real.sqrt r.Lam := (Reg.OK.sqrtLam h).1
  have heN_nonneg : 0 ≤ r.eN := (Reg.OK.eN_le h).1
  have ha_nonneg : 0 ≤ r.ha := by
    have htp_le_ha : r.tp ≤ r.ha := (Reg.OK.ha_le h).1
    linarith
  have hnu_nonneg : 0 ≤ r.nu := by
    dsimp [Reg.nu]
    have hd_nonneg : 0 ≤ r.d := by linarith
    have htp_nonneg : 0 ≤ r.tp := by linarith
    nlinarith
  have hV_nonneg : 0 ≤ r.V := by
    dsimp [Reg.V]
    have h_mul1 : 0 ≤ r.n * Real.sqrt r.Lam := mul_nonneg hn_pos.le hsqrtLam_nonneg
    exact mul_nonneg h_mul1 hnu_nonneg
  have hx_nonneg : 0 ≤ r.x := by
    dsimp [Reg.x]
    have h_mul1 : 0 ≤ r.n * r.Lam := mul_nonneg hn_pos.le hLam_nonneg
    exact mul_nonneg h_mul1 heN_nonneg
  have hx_le_one : r.x ≤ 1 := (Reg.OK.p1 h).1
  have hV_le_one : r.V ≤ 1 := (Reg.OK.p1 h).2.1
  intro k hk
  have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  set a := r.Lam * r.eN with ha_def
  have ha_nonneg' : 0 ≤ a := mul_nonneg hLam_nonneg heN_nonneg
  set y := (k : ℝ) * a with hy_def
  have hy_nonneg : 0 ≤ y := mul_nonneg hk_nonneg ha_nonneg'
  have hy_le_x : y ≤ r.x := by
    dsimp [y, a, Reg.x]
    calc
      (k : ℝ) * (r.Lam * r.eN) = ((k : ℝ) * r.Lam) * r.eN := by ring
      _ ≤ (r.n * r.Lam) * r.eN := by
        apply mul_le_mul_of_nonneg_right ?_ heN_nonneg
        apply mul_le_mul_of_nonneg_right hk hLam_nonneg
      _ = r.n * r.Lam * r.eN := by ring
  have hy_le_one : y ≤ 1 := by linarith
  have h_abs_y_le_one : |y| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have h_pow_exp : (1 + a) ^ k ≤ 1 + 2 * y := by
    have h1 : 1 + a ≤ Real.exp a := by
      simpa [add_comm] using Real.add_one_le_exp a
    have h_pow : (1 + a) ^ k ≤ (Real.exp a) ^ k :=
      pow_le_pow_left₀ (by linarith) h1 k
    have h_exp_pow : (Real.exp a) ^ k = Real.exp y := by
      rw [← Real.exp_nat_mul a k, hy_def]
    have h_exp_y_bound : Real.exp y ≤ 1 + 2 * y := by
      have h_abs := Real.abs_exp_sub_one_sub_id_le h_abs_y_le_one
      have h_le : Real.exp y - 1 - y ≤ y ^ 2 := (abs_le.mp h_abs).2
      have h_sq_le_y : y ^ 2 ≤ y := sq_le hy_nonneg hy_le_one
      linarith
    calc
      (1 + a) ^ k ≤ (Real.exp a) ^ k := h_pow
      _ = Real.exp y := h_exp_pow
      _ ≤ 1 + 2 * y := h_exp_y_bound
  dsimp [Reg.hTr]
  have h_sqrt_term : (k : ℝ) * Real.sqrt r.Lam * r.nu ≤ r.V := by
    dsimp [Reg.V]
    calc
      (k : ℝ) * Real.sqrt r.Lam * r.nu = ((k : ℝ) * Real.sqrt r.Lam) * r.nu := by ring
      _ ≤ (r.n * Real.sqrt r.Lam) * r.nu := by
        apply mul_le_mul_of_nonneg_right ?_ hnu_nonneg
        apply mul_le_mul_of_nonneg_right hk hsqrtLam_nonneg
      _ = r.n * Real.sqrt r.Lam * r.nu := by ring
  have h_term1 : 1 + r.ha + (k : ℝ) * Real.sqrt r.Lam * r.nu ≤ 1 + r.ha + r.V := by linarith
  have h_sqrt_term_nonneg : 0 ≤ (k : ℝ) * Real.sqrt r.Lam * r.nu :=
    mul_nonneg (mul_nonneg hk_nonneg hsqrtLam_nonneg) hnu_nonneg
  have h_nonneg_term1 : 0 ≤ 1 + r.ha + (k : ℝ) * Real.sqrt r.Lam * r.nu := by nlinarith
  have h_nonneg_term2 : 0 ≤ 1 + r.ha + r.V := by nlinarith
  have h_nonneg_pow : 0 ≤ (1 + a) ^ k := pow_nonneg (by linarith) k
  have h_bound : (1 + r.ha + (k : ℝ) * Real.sqrt r.Lam * r.nu) * (1 + a) ^ k - 1 ≤
      (1 + r.ha + r.V) * (1 + 2 * y) - 1 := by
    have h_mul : (1 + r.ha + (k : ℝ) * Real.sqrt r.Lam * r.nu) * (1 + a) ^ k ≤
        (1 + r.ha + r.V) * (1 + 2 * y) :=
      mul_le_mul h_term1 h_pow_exp h_nonneg_pow h_nonneg_term2
    linarith
  have h_final : (1 + r.ha + r.V) * (1 + 2 * y) - 1 ≤ r.hb := by
    dsimp [Reg.hb]
    have h_eq : (1 + r.ha + r.V) * (1 + 2 * y) - 1 = r.ha + r.V + 2 * y * (1 + r.ha + r.V) := by ring
    rw [h_eq]
    have h_factor : 1 + r.ha + r.V ≤ 2 + r.ha := by linarith
    have h_nonneg_factor : 0 ≤ 1 + r.ha + r.V := by nlinarith
    have h_calc : 2 * y * (1 + r.ha + r.V) ≤ 2 * r.x * (2 + r.ha) := by
      calc
        2 * y * (1 + r.ha + r.V) = 2 * (y * (1 + r.ha + r.V)) := by ring
        _ ≤ 2 * (r.x * (1 + r.ha + r.V)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
          apply mul_le_mul_of_nonneg_right hy_le_x h_nonneg_factor
        _ ≤ 2 * (r.x * (2 + r.ha)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
          apply mul_le_mul_of_nonneg_left h_factor hx_nonneg
        _ = 2 * r.x * (2 + r.ha) := by ring
    linarith
  linarith

set_option maxHeartbeats 800000 in
theorem Xb_Du (h : r.OK) : 0 ≤ r.Xb ∧ r.Xb ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp ∧ 0 ≤ r.Du ∧
    r.Du ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp := by
  -- Extract bounds from the lemmas above
  have h_sqrtLam := sqrtLam h
  have h_hb_bd := hb_bd h
  have h_p1 := p1 h
  have h_Xi1_le := Xi1_le h
  have h_ezt_exi := ezt_exi h
  have h_lam_bd := lam_bd h
  have h_Q_bd := Q_bd h
  -- Unpack individual inequalities
  -- h_Xi1_le: 0 ≤ r.Xi ∧ r.Xi ≤ r.Xi1 ∧ r.Xi1 ≤ r.d * r.Q
  have h_Xi_nonneg : 0 ≤ r.Xi := h_Xi1_le.1
  have h_Xi1_le' : r.Xi1 ≤ r.d * r.Q := h_Xi1_le.2.2
  have h_Xi1_nonneg : 0 ≤ r.Xi1 := by linarith
  have h_sqrtLam_nonneg : 0 ≤ Real.sqrt r.Lam := h_sqrtLam.1
  have h_sqrtLam_le : Real.sqrt r.Lam ≤ r.d * r.Q ^ 20 := h_sqrtLam.2
  have h_hb_nonneg : 0 ≤ r.hb := h_hb_bd.1
  have h_hb_le : r.hb ≤ r.d ^ 2 * r.Q ^ 51 * r.tp := h_hb_bd.2
  have h_hb_le_100 : r.hb ≤ 1 / 100 := h_p1.2.2
  have h_exi_nonneg : 0 ≤ r.exi := h_ezt_exi.2.2.1
  have h_exi_le : r.exi ≤ r.tp / 2 := h_ezt_exi.2.2.2
  have h_lam_nonneg : 0 ≤ r.lam := by linarith [h_lam_bd.1]
  have h_lam_le_one : r.lam ≤ 1 := by linarith [h_lam_bd.2]
  have h_d_ge_one : 1 ≤ r.d := h.hd
  have h_d_nonneg : 0 ≤ r.d := by linarith
  have h_Q_nonneg : 0 ≤ r.Q := by linarith [h_Q_bd.1]
  have h_tp_nonneg : 0 ≤ r.tp := by linarith [h.htp0]
  -- Helper: 1 ≤ x^n when 1 ≤ x (by induction)
  have h_pow_ge_one {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : 1 ≤ x ^ n := by
    induction' n with k ih
    · norm_num
    · rw [pow_succ]
      have hx_nonneg : 0 ≤ x := by linarith
      have h_mul : 1 * 1 ≤ x * x ^ k := mul_le_mul hx ih (by norm_num) hx_nonneg
      simpa [mul_comm] using h_mul
  -- Key inequality: d * Q^20 * tp ≤ d^4 * Q^72 * tp
  have h_dQ20_le_d4Q72 : r.d * r.Q ^ 20 * r.tp ≤ r.d ^ 4 * r.Q ^ 72 * r.tp := by
    have h_d3Q52_ge_one : 1 ≤ r.d ^ 3 * r.Q ^ 52 := by
      have h_d3_ge_one : 1 ≤ r.d ^ 3 := h_pow_ge_one h_d_ge_one 3
      have h_Q52_ge_one : 1 ≤ r.Q ^ 52 := h_pow_ge_one (by linarith) 52
      nlinarith
    have h_nonneg : 0 ≤ r.d * r.Q ^ 20 * r.tp := by
      have h1 : 0 ≤ r.d := h_d_nonneg
      have h2 : 0 ≤ r.Q ^ 20 := pow_nonneg h_Q_nonneg 20
      have h3 : 0 ≤ r.tp := h_tp_nonneg
      positivity
    calc
      r.d * r.Q ^ 20 * r.tp = (r.d * r.Q ^ 20 * r.tp) * 1 := by ring
      _ ≤ (r.d * r.Q ^ 20 * r.tp) * (r.d ^ 3 * r.Q ^ 52) := by nlinarith
      _ = r.d ^ 4 * r.Q ^ 72 * r.tp := by ring
  -- Now prove the four conjuncts
  have h_Du_nonneg : 0 ≤ r.Du := by
    have h_sum_nonneg : 0 ≤ r.hb * r.Xi1 + r.exi := by
      have h_hb_Xi1_nonneg : 0 ≤ r.hb * r.Xi1 := mul_nonneg h_hb_nonneg h_Xi1_nonneg
      nlinarith
    have h_Du_eq : r.Du = Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) := rfl
    rw [h_Du_eq]
    exact mul_nonneg h_sqrtLam_nonneg h_sum_nonneg
  -- First bound for Du: Du ≤ d^4 * Q^72 * tp + d * Q^20 * tp / 2
  have h_Du_bound1 : r.Du ≤ r.d ^ 4 * r.Q ^ 72 * r.tp + r.d * r.Q ^ 20 * r.tp / 2 := by
    have h_Du_unfolded : r.Du = Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) := rfl
    rw [h_Du_unfolded]
    have h_sum_nonneg : 0 ≤ r.hb * r.Xi1 + r.exi := by
      have h_hb_Xi1_nonneg : 0 ≤ r.hb * r.Xi1 := mul_nonneg h_hb_nonneg h_Xi1_nonneg
      nlinarith
    have h_sqrt_mul : Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) ≤ (r.d * r.Q ^ 20) * (r.hb * r.Xi1 + r.exi) :=
      mul_le_mul_of_nonneg_right h_sqrtLam_le h_sum_nonneg
    have h_bound_sum : r.hb * r.Xi1 + r.exi ≤ (r.d ^ 2 * r.Q ^ 51 * r.tp) * (r.d * r.Q) + r.tp / 2 := by
      have h_prod : r.hb * r.Xi1 ≤ (r.d ^ 2 * r.Q ^ 51 * r.tp) * (r.d * r.Q) := by
        nlinarith
      nlinarith
    have h_factor_nonneg : 0 ≤ r.d * r.Q ^ 20 := by
      have h1 : 0 ≤ r.d := h_d_nonneg
      have h2 : 0 ≤ r.Q ^ 20 := pow_nonneg h_Q_nonneg 20
      positivity
    have h_mul_bound : (r.d * r.Q ^ 20) * (r.hb * r.Xi1 + r.exi) ≤
        r.d * r.Q ^ 20 * ((r.d ^ 2 * r.Q ^ 51 * r.tp) * (r.d * r.Q) + r.tp / 2) :=
      mul_le_mul_of_nonneg_left h_bound_sum h_factor_nonneg
    have h_ring : r.d * r.Q ^ 20 * ((r.d ^ 2 * r.Q ^ 51 * r.tp) * (r.d * r.Q) + r.tp / 2) =
        r.d ^ 4 * r.Q ^ 72 * r.tp + r.d * r.Q ^ 20 * r.tp / 2 := by ring
    rw [h_ring] at h_mul_bound
    linarith
  have h_Du_le : r.Du ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp := by
    linarith
  have h_Xb_nonneg : 0 ≤ r.Xb := by
    have h_Xb_unfolded : r.Xb = Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) + r.tp / 16 * r.lam * (1 + r.hb) * Real.sqrt r.Lam * r.Xi1 := rfl
    rw [h_Xb_unfolded]
    have h_extra_nonneg : 0 ≤ r.tp / 16 * r.lam * (1 + r.hb) * Real.sqrt r.Lam * r.Xi1 := by
      have h_one_plus_hb_nonneg : 0 ≤ 1 + r.hb := by linarith
      have h_tp_div_nonneg : 0 ≤ r.tp / 16 := by nlinarith
      have h_sqrt_nonneg : 0 ≤ Real.sqrt r.Lam := h_sqrtLam_nonneg
      have h_prod : 0 ≤ (r.tp / 16) * r.lam * (1 + r.hb) * Real.sqrt r.Lam :=
        mul_nonneg (mul_nonneg (mul_nonneg h_tp_div_nonneg h_lam_nonneg) h_one_plus_hb_nonneg) h_sqrt_nonneg
      exact mul_nonneg h_prod h_Xi1_nonneg
    have h_sqrt_sum_nonneg : 0 ≤ Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) := by
      have h_hb_Xi1_nonneg : 0 ≤ r.hb * r.Xi1 := mul_nonneg h_hb_nonneg h_Xi1_nonneg
      have h_sum_nonneg : 0 ≤ r.hb * r.Xi1 + r.exi := by nlinarith
      exact mul_nonneg h_sqrtLam_nonneg h_sum_nonneg
    linarith
  -- extra ≤ d^4 * Q^72 * tp / 2
  have h_extra_le_half : r.tp / 16 * r.lam * (1 + r.hb) * Real.sqrt r.Lam * r.Xi1 ≤ r.d ^ 4 * r.Q ^ 72 * r.tp / 2 := by
    have h_nonneg_tp : 0 ≤ r.tp / 16 := by nlinarith
    have h_nonneg_hb_sum : 0 ≤ 1 + r.hb := by linarith
    -- Bound each factor using mul_le_mul
    have h_bound : r.tp / 16 * r.lam * (1 + r.hb) * Real.sqrt r.Lam * r.Xi1 ≤
        r.tp / 16 * 1 * (1 + (1 / 100)) * (r.d * r.Q ^ 20) * (r.d * r.Q) := by
      apply mul_le_mul ?_ ?_ ?_ ?_
      · apply mul_le_mul ?_ ?_ ?_ ?_
        · apply mul_le_mul ?_ ?_ ?_ ?_
          · exact mul_le_mul_of_nonneg_left h_lam_le_one h_nonneg_tp
          · linarith
          · exact h_nonneg_hb_sum
          · exact mul_nonneg h_nonneg_tp (by norm_num)
        · exact h_sqrtLam_le
        · exact h_sqrtLam_nonneg
        · positivity
      · exact h_Xi1_le'
      · exact h_Xi1_nonneg
      · positivity
    have h_simplify : r.tp / 16 * 1 * (1 + (1 / 100)) * (r.d * r.Q ^ 20) * (r.d * r.Q) =
        r.tp / 16 * (101 / 100) * r.d ^ 2 * r.Q ^ 21 := by ring
    rw [h_simplify] at h_bound
    -- Show tp/16 * 101/100 * d^2 * Q^21 ≤ d^4 * Q^72 * tp / 2
    have h_final : r.tp / 16 * (101 / 100) * r.d ^ 2 * r.Q ^ 21 ≤ r.d ^ 4 * r.Q ^ 72 * r.tp / 2 := by
      have h_d2Q51_ge : (101 : ℝ) / 800 ≤ r.d ^ 2 * r.Q ^ 51 := by
        have h_d2_ge_one : 1 ≤ r.d ^ 2 := h_pow_ge_one h_d_ge_one 2
        have h_Q51_ge_one : 1 ≤ r.Q ^ 51 := h_pow_ge_one (by linarith) 51
        have h_prod_ge_one : 1 ≤ r.d ^ 2 * r.Q ^ 51 := by nlinarith
        have h_101_800_le_one : (101 : ℝ) / 800 ≤ 1 := by norm_num
        nlinarith
      nlinarith
    linarith
  have h_Xb_le : r.Xb ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp := by
    have h_Xb_unfolded : r.Xb = Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) + r.tp / 16 * r.lam * (1 + r.hb) * Real.sqrt r.Lam * r.Xi1 := rfl
    rw [h_Xb_unfolded]
    -- From h_Du_bound1: sqrt(Lam)*(hb*Xi1+exi) ≤ d^4*Q^72*tp + d*Q^20*tp/2
    have h_Du_le' : Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) ≤ r.d ^ 4 * r.Q ^ 72 * r.tp + r.d * r.Q ^ 20 * r.tp / 2 := by
      have h_Du_unfolded : r.Du = Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) := rfl
      rw [h_Du_unfolded] at h_Du_bound1
      exact h_Du_bound1
    -- Du ≤ d^4*Q^72*tp + d*Q^20*tp/2 ≤ d^4*Q^72*tp + d^4*Q^72*tp/2 = (3/2)*d^4*Q^72*tp
    have h_Du_le_3half : Real.sqrt r.Lam * (r.hb * r.Xi1 + r.exi) ≤ (3/2) * r.d ^ 4 * r.Q ^ 72 * r.tp := by
      nlinarith
    nlinarith
  exact ⟨h_Xb_nonneg, h_Xb_le, h_Du_nonneg, h_Du_le⟩

theorem DP_le (h : r.OK) : 0 ≤ r.DP ∧ r.DP ≤ 3 * r.d ^ 3 * r.Q ^ 91 * r.tp := by
  rcases h.hb_bd with ⟨hhb_nonneg, hhb_le⟩
  rcases h.p1 with ⟨_, _, hhb_le'⟩
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have hNe_nonneg : 0 ≤ r.Ne := by
    have hpos : 0 < (2 : ℝ) ^ (700 : ℕ) := pow_pos (by norm_num : 0 < (2 : ℝ)) 700
    exact le_of_lt (lt_trans hpos h.hN700)
  have hQ_nonneg : 0 ≤ r.Q := by linarith [h.hQ0]
  have hLam_nonneg : 0 ≤ r.Lam := by
    rw [AdversarialBco.Bit.PieceA.Reg.Lam]
    nlinarith
  have hDP_nonneg : 0 ≤ r.DP := by
    rw [AdversarialBco.Bit.PieceA.Reg.DP]
    nlinarith
  have h_main : r.DP ≤ 3 * r.d ^ 3 * r.Q ^ 91 * r.tp := by
    rw [AdversarialBco.Bit.PieceA.Reg.DP, AdversarialBco.Bit.PieceA.Reg.Lam]
    have hQ40 : r.Ne = r.Q ^ 40 := by
      linarith [h.hQ]
    rw [hQ40]
    have h_sum : 2 * r.hb + r.hb ^ 2 ≤ 3 * r.hb := by
      nlinarith
    have h_factor_nonneg : 0 ≤ r.d * r.Q ^ 40 := by
      have hQpow_nonneg : 0 ≤ r.Q ^ 40 := pow_nonneg hQ_nonneg 40
      exact mul_nonneg hd_nonneg hQpow_nonneg
    calc
      (2 * r.hb + r.hb ^ 2) * (r.d * r.Q ^ 40) ≤ (3 * r.hb) * (r.d * r.Q ^ 40) :=
        mul_le_mul_of_nonneg_right h_sum h_factor_nonneg
      _ ≤ (3 * (r.d ^ 2 * r.Q ^ 51 * r.tp)) * (r.d * r.Q ^ 40) :=
        mul_le_mul_of_nonneg_right (by nlinarith) h_factor_nonneg
      _ = 3 * r.d ^ 3 * r.Q ^ 91 * r.tp := by ring
  exact And.intro hDP_nonneg h_main

set_option maxHeartbeats 800000 in
theorem eb_ek (h : r.OK) : 0 ≤ r.eb ∧ r.eb ≤ 2 ^ 11 * r.d ^ 8 * r.Q ^ 93 * r.tp ∧ 0 ≤ r.ek ∧
    r.ek ≤ 2 ^ 18 * r.d ^ 9 * r.Q ^ 93 * r.tp := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  obtain ⟨hDc0, hDc⟩ := h.Dc_le
  obtain ⟨hcb0, hcb⟩ := h.cb_le
  obtain ⟨hXi0, hXiXi1, hXi1⟩ := h.Xi1_le
  obtain ⟨hsL0, hsL⟩ := h.sqrtLam
  obtain ⟨-, -, hDu0, hDu⟩ := h.Xb_Du
  obtain ⟨hDP0, hDP⟩ := h.DP_le
  obtain ⟨hsd1, hsd⟩ := h.sqrt_d_le
  obtain ⟨hRd, -⟩ := h.R_bd
  have hR1 := h.hR1
  have hR2 := h.hR2
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hLe1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hL1
  have hLam : r.Lam = r.d * r.Q ^ 40 := by simp only [Reg.Lam]; rw [← h.hQ]
  have hXi10 : 0 ≤ r.Xi1 := le_trans hXi0 hXiXi1
  have hR0 : 0 ≤ r.R := by linarith
  have hcb1 : r.cb ≤ 1 := by
    have : (1 : ℝ) ≤ r.d ^ 2 * r.Le ^ 7 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) (one_le_pow₀ hLe1)
    have : 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) ≤ 54 / 10 ^ 10 := div_le_self (by norm_num) this
    linarith
  have hDct : r.Dc ≤ r.tp := by
    have : 35 / 100 * r.cb * r.tp ≤ 35 / 100 * 1 * r.tp := by gcongr
    linarith
  have hmono : ∀ a b A B : ℕ, a ≤ A → b ≤ B → r.d ^ a * r.Q ^ b * r.tp ≤ r.d ^ A * r.Q ^ B * r.tp := by
    intro a b A B ha hb
    have := mul_le_mul (pow_le_pow_right₀ hd ha) (pow_le_pow_right₀ hQ1 hb) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this htp0.le
  have hX2 : r.Xi1 ^ 2 + 1 ≤ 2 * (r.d ^ 2 * r.Q ^ 2) := by
    have h1 : r.Xi1 ^ 2 ≤ (r.d * r.Q) ^ 2 := pow_le_pow_left₀ hXi10 hXi1 2
    have h2 : (1 : ℝ) ≤ r.d ^ 2 * r.Q ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) (one_le_pow₀ hQ1)
    have e : (r.d * r.Q) ^ 2 = r.d ^ 2 * r.Q ^ 2 := by ring
    linarith
  have hS : 203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP ≤ 706 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp) := by
    have a1 : 203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du ≤
        203 / 100 * (r.d * r.Q ^ 20) * (r.d * r.Q) * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) := by gcongr
    have e1 : 203 / 100 * (r.d * r.Q ^ 20) * (r.d * r.Q) * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) =
        406 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp) := by ring
    have a2 := hmono 3 91 6 93 (by norm_num) (by norm_num)
    have e2 : 3 * r.d ^ 3 * r.Q ^ 91 * r.tp = 3 * (r.d ^ 3 * r.Q ^ 91 * r.tp) := by ring
    linarith
  have hS0 : 0 ≤ 203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP := by positivity
  have hLX : r.Lam * (r.Xi1 ^ 2 + 1) ≤ 2 * (r.d ^ 3 * r.Q ^ 42) := by
    rw [hLam]
    calc r.d * r.Q ^ 40 * (r.Xi1 ^ 2 + 1) ≤ r.d * r.Q ^ 40 * (2 * (r.d ^ 2 * r.Q ^ 2)) := by gcongr
      _ = 2 * (r.d ^ 3 * r.Q ^ 42) := by ring
  have hLX0 : 0 ≤ r.Lam * (r.Xi1 ^ 2 + 1) := by rw [hLam]; positivity
  have hsdt : Real.sqrt r.d * r.tp ≤ r.d * r.tp := mul_le_mul_of_nonneg_right hsd htp0.le
  have t2 : 0 ≤ r.Dc * r.R * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) := by
    have e : r.Dc * r.R * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) =
        r.Dc * r.R * (103 / 100) * (r.Lam * (r.Xi1 ^ 2 + 1)) := by ring
    rw [e]; exact mul_nonneg (mul_nonneg (mul_nonneg hDc0 hR0) (by norm_num)) hLX0
  have t3 : 0 ≤ r.cb * r.R * (203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP) :=
    mul_nonneg (mul_nonneg hcb0 hR0) hS0
  have t1 : 0 ≤ Real.sqrt r.d * r.tp / 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Reg.eb]; linarith
  · simp only [Reg.eb]
    have m1 := hmono 1 0 8 93 (by norm_num) (by norm_num)
    have e1 : r.d ^ 1 * r.Q ^ 0 * r.tp = r.d * r.tp := by ring
    have b2 : r.Dc * r.R * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) ≤
        r.tp * (190 * r.d ^ 2) * (103 / 100) * (2 * (r.d ^ 3 * r.Q ^ 42)) := by
      have e : r.Dc * r.R * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) =
          r.Dc * r.R * (103 / 100) * (r.Lam * (r.Xi1 ^ 2 + 1)) := by ring
      rw [e]; gcongr
    have e2 : r.tp * (190 * r.d ^ 2) * (103 / 100) * (2 * (r.d ^ 3 * r.Q ^ 42)) =
        3914 / 10 * (r.d ^ 5 * r.Q ^ 42 * r.tp) := by ring
    have m2 := hmono 5 42 8 93 (by norm_num) (by norm_num)
    have b3 : r.cb * r.R * (203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP) ≤
        1 * (190 * r.d ^ 2) * (706 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp)) := by gcongr
    have e3 : 1 * (190 * r.d ^ 2) * (706 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp)) =
        13414 / 10 * (r.d ^ 8 * r.Q ^ 93 * r.tp) := by ring
    have e4 : 2 ^ 11 * r.d ^ 8 * r.Q ^ 93 * r.tp = 2048 * (r.d ^ 8 * r.Q ^ 93 * r.tp) := by ring
    have m0 : 0 ≤ r.d ^ 8 * r.Q ^ 93 * r.tp := by positivity
    linarith
  · simp only [Reg.ek]
    have u2 : 0 ≤ r.Dc * r.R ^ 2 * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) / 2 := by
      have e : r.Dc * r.R ^ 2 * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) / 2 =
          r.Dc * r.R ^ 2 * (103 / 100) * (r.Lam * (r.Xi1 ^ 2 + 1)) / 2 := by ring
      rw [e]; exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hDc0 (by positivity)) (by norm_num)) hLX0) (by norm_num)
    have u3 : 0 ≤ r.cb / 2 * r.R ^ 2 * (203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) hS0
    linarith [htp0]
  · simp only [Reg.ek]
    have m1 := hmono 0 0 9 93 (by norm_num) (by norm_num)
    have e1 : r.d ^ 0 * r.Q ^ 0 * r.tp = r.tp := by ring
    have b2 : r.Dc * r.R ^ 2 * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) / 2 ≤
        r.tp * (190 ^ 2 * r.d ^ 3) * (103 / 100) * (2 * (r.d ^ 3 * r.Q ^ 42)) / 2 := by
      have e : r.Dc * r.R ^ 2 * (103 / 100) * r.Lam * (r.Xi1 ^ 2 + 1) / 2 =
          r.Dc * r.R ^ 2 * (103 / 100) * (r.Lam * (r.Xi1 ^ 2 + 1)) / 2 := by ring
      rw [e]; gcongr
    have e2 : r.tp * (190 ^ 2 * r.d ^ 3) * (103 / 100) * (2 * (r.d ^ 3 * r.Q ^ 42)) / 2 =
        37183 * (r.d ^ 6 * r.Q ^ 42 * r.tp) := by ring
    have m2 := hmono 6 42 9 93 (by norm_num) (by norm_num)
    have b3 : r.cb / 2 * r.R ^ 2 * (203 / 100 * Real.sqrt r.Lam * r.Xi1 * r.Du + r.DP) ≤
        1 / 2 * (190 ^ 2 * r.d ^ 3) * (706 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp)) := by gcongr
    have e3 : 1 / 2 * (190 ^ 2 * r.d ^ 3) * (706 / 100 * (r.d ^ 6 * r.Q ^ 93 * r.tp)) =
        127433 * (r.d ^ 9 * r.Q ^ 93 * r.tp) := by ring
    have e4 : 2 ^ 18 * r.d ^ 9 * r.Q ^ 93 * r.tp = 262144 * (r.d ^ 9 * r.Q ^ 93 * r.tp) := by ring
    have m0 : 0 ≤ r.d ^ 9 * r.Q ^ 93 * r.tp := by positivity
    linarith

set_option maxHeartbeats 800000 in
theorem eg_el_Gb (h : r.OK) : 0 ≤ r.eg ∧ r.eg ≤ 4 * r.d ^ 4 * r.Q ^ 77 * r.tp ∧ 0 ≤ r.el ∧
    r.el ≤ 2 ^ 10 * r.d ^ 6 * r.Q ^ 77 * r.tp ∧ 0 ≤ r.Gb ∧ r.Gb ≤ r.d ^ 2 * r.Q ^ 36 := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, hQL, hQn, -, -, -⟩ := h.Q_bd
  obtain ⟨heY0, heY⟩ := h.eY_le
  obtain ⟨hYb1, hYb⟩ := h.Yb_bd
  obtain ⟨hXi0, hXiXi1, hXi1⟩ := h.Xi1_le
  obtain ⟨hsL0, hsL⟩ := h.sqrtLam
  obtain ⟨-, -, hDu0, hDu⟩ := h.Xb_Du
  obtain ⟨hsd1, hsd⟩ := h.sqrt_d_le
  obtain ⟨hRd, -⟩ := h.R_bd
  have hR1 := h.hR1
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hLe1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hL1
  have hXi10 : 0 ≤ r.Xi1 := le_trans hXi0 hXiXi1
  have hR0 : 0 ≤ r.R := by linarith
  have hYb0 : 0 ≤ r.Yb := le_trans (by positivity) hYb1
  have hmono : ∀ a b A B : ℕ, a ≤ A → b ≤ B → r.d ^ a * r.Q ^ b * r.tp ≤ r.d ^ A * r.Q ^ B * r.tp := by
    intro a b A B ha hb
    have := mul_le_mul (pow_le_pow_right₀ hd ha) (pow_le_pow_right₀ hQ1 hb) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this htp0.le
  have hmono2 : ∀ a b A B : ℕ, a ≤ A → b + 1 ≤ B →
      2 ^ 17 * (r.d ^ a * r.Q ^ b * r.tp) ≤ r.d ^ A * r.Q ^ B * r.tp := by
    intro a b A B ha hb
    have h1 := hmono a (b + 1) A B ha hb
    have h2 : 2 ^ 17 * (r.d ^ a * r.Q ^ b * r.tp) ≤ r.d ^ a * r.Q ^ (b + 1) * r.tp := by
      have hx : 0 ≤ r.d ^ a * r.Q ^ b * r.tp := by positivity
      have := mul_le_mul_of_nonneg_left hQ17 hx
      calc 2 ^ 17 * (r.d ^ a * r.Q ^ b * r.tp) = (r.d ^ a * r.Q ^ b * r.tp) * 2 ^ 17 := by ring
        _ ≤ (r.d ^ a * r.Q ^ b * r.tp) * r.Q := this
        _ = r.d ^ a * r.Q ^ (b + 1) * r.tp := by ring
    linarith
  -- `√Le ≤ Le ≤ Q/10`, so `eY ≤ Q tp`
  have hsLe : Real.sqrt r.Le ≤ r.Le := by
    have : Real.sqrt r.Le ≤ Real.sqrt (r.Le ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have heYQ : r.eY ≤ r.Q * r.tp := by
    have : 118 / 100 * Real.sqrt r.Le * r.tp ≤ 118 / 100 * (r.Q / 10) * r.tp := by
      gcongr; linarith
    nlinarith
  have hQ5 : r.Q ≤ r.Q ^ 5 := le_self_pow₀ hQ1 (by norm_num)
  have hE : r.eY + r.Yb * r.tp / 16 ≤ 2 * (r.Q ^ 5 * r.tp) := by
    have a1 : r.Q * r.tp ≤ r.Q ^ 5 * r.tp := mul_le_mul_of_nonneg_right hQ5 htp0.le
    have a2 : r.Yb * r.tp / 16 ≤ r.Q ^ 5 * r.tp / 16 := by gcongr
    have : 0 ≤ r.Q ^ 5 * r.tp := by positivity
    linarith
  have hE0 : 0 ≤ r.eY + r.Yb * r.tp / 16 := by positivity
  have heg : r.eg ≤ 4 * r.d ^ 4 * r.Q ^ 77 * r.tp := by
    simp only [Reg.eg]
    have b1 : Real.sqrt r.d * r.tp / 2 ≤ r.d * r.tp / 2 := by
      have := mul_le_mul_of_nonneg_right hsd htp0.le; linarith
    have m1 := hmono2 1 0 4 77 (by norm_num) (by norm_num)
    have e1 : r.d ^ 1 * r.Q ^ 0 * r.tp = r.d * r.tp := by ring
    have b2 : 101 / 100 * (r.eY + r.Yb * r.tp / 16) * (101 / 100) * Real.sqrt r.Lam * r.Xi1 ≤
        101 / 100 * (2 * (r.Q ^ 5 * r.tp)) * (101 / 100) * (r.d * r.Q ^ 20) * (r.d * r.Q) := by gcongr
    have e2 : 101 / 100 * (2 * (r.Q ^ 5 * r.tp)) * (101 / 100) * (r.d * r.Q ^ 20) * (r.d * r.Q) =
        20402 / 10000 * (r.d ^ 2 * r.Q ^ 26 * r.tp) := by ring
    have m2 := hmono2 2 26 4 77 (by norm_num) (by norm_num)
    have b3 : 101 / 100 * r.Yb * r.Du ≤ 101 / 100 * r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) := by gcongr
    have e3 : 101 / 100 * r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) = 202 / 100 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by
      ring
    have e4 : 4 * r.d ^ 4 * r.Q ^ 77 * r.tp = 4 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by ring
    have m0 : 0 ≤ r.d ^ 4 * r.Q ^ 77 * r.tp := by positivity
    linarith
  have heg0 : 0 ≤ r.eg := by simp only [Reg.eg]; positivity
  refine ⟨heg0, heg, ?_, ?_, ?_, ?_⟩
  · simp only [Reg.el]; positivity
  · simp only [Reg.el]
    have b1 : r.R * r.eg ≤ (190 * r.d ^ 2) * (4 * r.d ^ 4 * r.Q ^ 77 * r.tp) := by gcongr
    have e1 : (190 * r.d ^ 2) * (4 * r.d ^ 4 * r.Q ^ 77 * r.tp) = 760 * (r.d ^ 6 * r.Q ^ 77 * r.tp) := by ring
    have m1 := hmono 0 0 6 77 (by norm_num) (by norm_num)
    have e2 : r.d ^ 0 * r.Q ^ 0 * r.tp = r.tp := by ring
    have e4 : 2 ^ 10 * r.d ^ 6 * r.Q ^ 77 * r.tp = 1024 * (r.d ^ 6 * r.Q ^ 77 * r.tp) := by ring
    linarith
  · simp only [Reg.Gb]; positivity
  · simp only [Reg.Gb]
    have hn : r.n ≤ r.Q ^ 10 / 32 := by linarith
    have b1 : r.n * (101 / 100) * r.Yb * Real.sqrt r.Lam * r.Xi ≤
        r.Q ^ 10 / 32 * (101 / 100) * r.Q ^ 5 * (r.d * r.Q ^ 20) * (r.d * r.Q) := by
      have := le_trans hXiXi1 hXi1
      gcongr
    have e1 : r.Q ^ 10 / 32 * (101 / 100) * r.Q ^ 5 * (r.d * r.Q ^ 20) * (r.d * r.Q) =
        101 / 3200 * (r.d ^ 2 * r.Q ^ 36) := by ring
    have m0 : 0 ≤ r.d ^ 2 * r.Q ^ 36 := by positivity
    linarith

theorem ePhi_bd (h : r.OK) : 0 ≤ r.ePhi ∧ r.ePhi ≤ 2 ^ 15 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
  -- Extract bounds from h
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have hn_nonneg : 0 ≤ r.n := by linarith [h.hn]
  have hR_nonneg : 0 ≤ r.R := by linarith [h.hR1]
  have htp_nonneg : 0 ≤ r.tp := by linarith [h.htp0]
  have hQ_nonneg : 0 ≤ r.Q := by linarith [h.hQ0]
  have hR2_sq : r.R ^ 2 ≤ 36100 * r.d ^ 3 := by
    calc
      r.R ^ 2 ≤ 190 ^ 2 * r.d ^ 3 := h.hR2
      _ = 36100 * r.d ^ 3 := by norm_num
  have hQ_low : 2 ^ 17 ≤ r.Q := (Q_bd h).1
  have hnQ : r.n ≤ r.Q ^ 10 / 32 := by
    have := (Q_bd h).2.2.1
    linarith
  have hR_bd : r.R ≤ 190 * r.d ^ 2 := (R_bd h).1
  have hDP_nonneg : 0 ≤ r.DP := (DP_le h).1
  have hDP_le : r.DP ≤ 3 * r.d ^ 3 * r.Q ^ 91 * r.tp := (DP_le h).2
  have heb_nonneg : 0 ≤ r.eb := (eb_ek h).1
  have heb_le : r.eb ≤ 2 ^ 11 * r.d ^ 8 * r.Q ^ 93 * r.tp := (eb_ek h).2.1
  have hek_nonneg : 0 ≤ r.ek := (eb_ek h).2.2.1
  have hek_le : r.ek ≤ 2 ^ 18 * r.d ^ 9 * r.Q ^ 93 * r.tp := (eb_ek h).2.2.2
  have h_nonneg : 0 ≤ r.ePhi := by
    unfold Reg.ePhi
    positivity
  have h_le : r.ePhi ≤ 2 ^ 15 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
    unfold Reg.ePhi
    -- Bound for the first term: R^2/2 * DP ≤ d^10 * Q^103 * tp
    have hT1 : r.R ^ 2 / 2 * r.DP ≤ r.d ^ 10 * r.Q ^ 103 * r.tp := by
      have h_ineq : (54150 : ℝ) ≤ r.d ^ 4 * r.Q ^ 12 := by
        have hQ12 : (2^17)^12 ≤ r.Q^12 := by gcongr
        have h_54150_le : (54150 : ℝ) ≤ (2^17)^12 := by norm_num
        have hd4 : (1 : ℝ) ≤ r.d^4 := by
          calc
            (1 : ℝ) = (1 : ℝ)^4 := by norm_num
            _ ≤ r.d^4 := by
              gcongr
              exact h.hd
        calc
          (54150 : ℝ) ≤ (2^17)^12 := by norm_num
          _ ≤ r.Q^12 := hQ12
          _ = 1 * r.Q^12 := by ring
          _ ≤ r.d^4 * r.Q^12 := by gcongr
      calc
        r.R ^ 2 / 2 * r.DP ≤ (36100 * r.d ^ 3) / 2 * (3 * r.d ^ 3 * r.Q ^ 91 * r.tp) := by
          have hdiv : r.R ^ 2 / 2 ≤ (36100 * r.d ^ 3) / 2 := by gcongr
          exact mul_le_mul hdiv hDP_le hDP_nonneg (by positivity)
        _ = 54150 * r.d ^ 6 * r.Q ^ 91 * r.tp := by ring
        _ = (54150 : ℝ) * (r.d ^ 6 * r.Q ^ 91 * r.tp) := by ring
        _ ≤ (r.d ^ 4 * r.Q ^ 12) * (r.d ^ 6 * r.Q ^ 91 * r.tp) := by gcongr
        _ = r.d ^ 10 * r.Q ^ 103 * r.tp := by ring
    -- Bound for the second term: R * n * eb ≤ 12160 * d^10 * Q^103 * tp
    have hT2 : r.R * r.n * r.eb ≤ 12160 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
      calc
        r.R * r.n * r.eb ≤ (190 * r.d ^ 2) * (r.Q ^ 10 / 32) * (2^11 * r.d ^ 8 * r.Q ^ 93 * r.tp) := by
          gcongr
        _ = 12160 * r.d ^ 10 * r.Q ^ 103 * r.tp := by ring
    -- Bound for the third term: n * ek ≤ 8192 * d^10 * Q^103 * tp
    have hT3 : r.n * r.ek ≤ 8192 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
      have hd9_le_d10 : r.d ^ 9 ≤ r.d ^ 10 := by
        calc
          r.d ^ 9 = r.d ^ 9 * 1 := by ring
          _ ≤ r.d ^ 9 * r.d := by gcongr; exact h.hd
          _ = r.d ^ 10 := by ring
      calc
        r.n * r.ek ≤ (r.Q ^ 10 / 32) * (2^18 * r.d ^ 9 * r.Q ^ 93 * r.tp) := by
          gcongr
        _ = 8192 * r.d ^ 9 * r.Q ^ 103 * r.tp := by ring
        _ ≤ 8192 * r.d ^ 10 * r.Q ^ 103 * r.tp := by gcongr
    -- Sum the three bounds
    calc
      r.R ^ 2 / 2 * r.DP + r.R * r.n * r.eb + r.n * r.ek ≤
          (r.d ^ 10 * r.Q ^ 103 * r.tp) + (12160 * r.d ^ 10 * r.Q ^ 103 * r.tp) + (8192 * r.d ^ 10 * r.Q ^ 103 * r.tp) := by
        gcongr
      _ = (1 + 12160 + 8192) * r.d ^ 10 * r.Q ^ 103 * r.tp := by ring
      _ = 20353 * r.d ^ 10 * r.Q ^ 103 * r.tp := by ring
      _ ≤ (2 ^ 15 : ℝ) * r.d ^ 10 * r.Q ^ 103 * r.tp := by
        gcongr
        norm_num
  exact And.intro h_nonneg h_le

theorem eX_bd (h : r.OK) : 0 ≤ r.eX ∧ r.eX ≤ 2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
  rcases eta_bd h with ⟨heta_pos, heta_le_one⟩
  rcases eg_el_Gb h with ⟨heg_nonneg, heg_le, hel_nonneg, hel_le, hGb_nonneg, hGb_le⟩
  rcases R_bd h with ⟨hR_le, hR_sq_le⟩
  rcases ePhi_bd h with ⟨hePhi_nonneg, hePhi_le⟩
  rcases Q_bd h with ⟨hQ_ge, _, hn_le_Q10_div_32, _, _, _⟩
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num : (0 : ℝ) ≤ 1) h.hd
  have hn_nonneg : 0 ≤ r.n := le_trans (by norm_num : (0 : ℝ) ≤ 1) h.hn
  have htp_nonneg : 0 ≤ r.tp := h.htp0.le
  have hQ_nonneg : 0 ≤ r.Q := h.hQ0.le
  have hR_nonneg : 0 ≤ r.R := le_trans (by norm_num : (0 : ℝ) ≤ 157) h.hR1
  have h_nonneg : 0 ≤ r.eX := by
    unfold Reg.eX
    positivity
  -- helper: for d ≥ 1, we have d^k ≥ 1 for any k
  have h_pow_d_ge_one {k : ℕ} (hk : k ≠ 0) : 1 ≤ r.d ^ k := by
    induction' k with k ih
    · exact (hk rfl).elim
    · rw [pow_succ]
      have h1 : 1 ≤ r.d := h.hd
      have h_ih : 1 ≤ r.d ^ k := by
        rcases Nat.eq_zero_or_pos k with hk' | hk'
        · subst hk'; norm_num
        · exact ih hk'.ne'
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ r.d * r.d ^ k := mul_le_mul h1 h_ih (by norm_num) (by linarith)
        _ = r.d ^ (k + 1) := by ring
  -- helper: for Q ≥ 1, we have Q^k ≥ 1 for any k
  have h_pow_Q_ge_one {k : ℕ} (hk : k ≠ 0) : 1 ≤ r.Q ^ k := by
    induction' k with k ih
    · exact (hk rfl).elim
    · rw [pow_succ]
      have h1 : 1 ≤ r.Q := by
        have : 0 < 2 ^ 17 := by norm_num
        linarith
      have h_ih : 1 ≤ r.Q ^ k := by
        rcases Nat.eq_zero_or_pos k with hk' | hk'
        · subst hk'; norm_num
        · exact ih hk'.ne'
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ r.Q * r.Q ^ k := mul_le_mul h1 h_ih (by norm_num) (by linarith)
        _ = r.Q ^ (k + 1) := by ring
  have h_upper : r.eX ≤ 2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
    unfold Reg.eX
    have hn_el : r.n * r.el ≤ 32 * r.d ^ 6 * r.Q ^ 87 * r.tp := by
      have hn_le : r.n ≤ r.Q ^ 10 / 32 := by linarith
      calc
        r.n * r.el ≤ (r.Q ^ 10 / 32) * ((2 ^ 10 : ℝ) * r.d ^ 6 * r.Q ^ 77 * r.tp) := by
          apply mul_le_mul hn_le hel_le (by positivity) (by positivity)
        _ = (32 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp := by ring
    have h_R_n_eg : r.R * r.n * r.eg ≤ (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp := by
      have hn_le : r.n ≤ r.Q ^ 10 / 32 := by linarith
      calc
        r.R * r.n * r.eg ≤ (190 * r.d ^ 2) * (r.Q ^ 10 / 32) * (4 * r.d ^ 4 * r.Q ^ 77 * r.tp) := by
          apply mul_le_mul (mul_le_mul hR_le hn_le (by positivity) (by positivity)) heg_le (by positivity) (by positivity)
        _ = (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp := by ring
    have h_term1 : r.eta * (101 / 100 : ℝ) * (r.n * r.el + r.R * r.n * r.eg) ≤
        (101 / 100 : ℝ) * (32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp) := by
      have h_sum_nonneg : 0 ≤ r.n * r.el + r.R * r.n * r.eg := by positivity
      have h_sum : r.n * r.el + r.R * r.n * r.eg ≤ 32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp := by
        linarith
      have h_eta_factor : r.eta * (101 / 100 : ℝ) ≤ 1 * (101 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right heta_le_one (by norm_num)
      calc
        r.eta * (101 / 100 : ℝ) * (r.n * r.el + r.R * r.n * r.eg) ≤
            (1 * (101 / 100 : ℝ)) * (r.n * r.el + r.R * r.n * r.eg) :=
          mul_le_mul_of_nonneg_right h_eta_factor h_sum_nonneg
        _ = (101 / 100 : ℝ) * (r.n * r.el + r.R * r.n * r.eg) := by ring
        _ ≤ (101 / 100 : ℝ) * (32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp) := by
          apply mul_le_mul_of_nonneg_left h_sum (by norm_num)
    have h_term2 : r.eta * r.tp / 16 * (21 / 10 : ℝ) * r.R * r.Gb ≤ 25 * r.d ^ 4 * r.Q ^ 36 * r.tp := by
      have h_mul : r.eta * r.tp / 16 * (21 / 10 : ℝ) * r.R ≤ 1 * r.tp / 16 * (21 / 10 : ℝ) * (190 * r.d ^ 2) := by
        have h_factor_nonneg : 0 ≤ r.tp / 16 * (21 / 10 : ℝ) := by positivity
        calc
          r.eta * r.tp / 16 * (21 / 10 : ℝ) * r.R = (r.eta * (r.tp / 16 * (21 / 10 : ℝ))) * r.R := by ring
          _ ≤ (1 * (r.tp / 16 * (21 / 10 : ℝ))) * r.R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heta_le_one h_factor_nonneg) hR_nonneg
          _ ≤ (1 * (r.tp / 16 * (21 / 10 : ℝ))) * (190 * r.d ^ 2) :=
            mul_le_mul_of_nonneg_left hR_le (by positivity)
          _ = 1 * r.tp / 16 * (21 / 10 : ℝ) * (190 * r.d ^ 2) := by ring
      calc
        r.eta * r.tp / 16 * (21 / 10 : ℝ) * r.R * r.Gb ≤
            (1 * r.tp / 16 * (21 / 10 : ℝ) * (190 * r.d ^ 2)) * r.Gb :=
          mul_le_mul_of_nonneg_right h_mul hGb_nonneg
        _ ≤ (1 * r.tp / 16 * (21 / 10 : ℝ) * (190 * r.d ^ 2)) * (r.d ^ 2 * r.Q ^ 36) :=
          mul_le_mul_of_nonneg_left hGb_le (by positivity)
        _ = (399 / 16 : ℝ) * r.d ^ 4 * r.Q ^ 36 * r.tp := by ring
        _ ≤ 25 * r.d ^ 4 * r.Q ^ 36 * r.tp := by
          have hcoeff : (399 / 16 : ℝ) ≤ 25 := by norm_num
          have hX_nonneg : 0 ≤ r.d ^ 4 * r.Q ^ 36 * r.tp := by positivity
          have htemp := mul_le_mul_of_nonneg_right hcoeff hX_nonneg
          -- htemp: (399/16) * X ≤ 25 * X  where X = r.d^4 * r.Q^36 * r.tp
          -- goal: (399/16) * r.d^4 * r.Q^36 * r.tp ≤ 25 * r.d^4 * r.Q^36 * r.tp
          simpa [mul_assoc] using htemp
    have h_term3 : 2 * r.ePhi ≤ 2 ^ 16 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
      calc
        2 * r.ePhi ≤ 2 * (2 ^ 15 * r.d ^ 10 * r.Q ^ 103 * r.tp) :=
          mul_le_mul_of_nonneg_left hePhi_le (by norm_num)
        _ = 2 ^ 16 * r.d ^ 10 * r.Q ^ 103 * r.tp := by ring
    -- Now combine using the fact that d ≥ 1, Q ≥ 1
    have h_pow1 : r.d ^ 6 * r.Q ^ 87 ≤ r.d ^ 10 * r.Q ^ 103 := by
      have hd_pow : r.d ^ 6 ≤ r.d ^ 10 := by
        have h : r.d ^ 10 = r.d ^ 6 * r.d ^ 4 := by ring
        rw [h]
        have hpos : 0 ≤ r.d ^ 6 := pow_nonneg hd_nonneg 6
        have h_ge_one : 1 ≤ r.d ^ 4 := h_pow_d_ge_one (by omega)
        calc
          r.d ^ 6 = r.d ^ 6 * 1 := by ring
          _ ≤ r.d ^ 6 * r.d ^ 4 := mul_le_mul_of_nonneg_left h_ge_one hpos
      have hQ_pow : r.Q ^ 87 ≤ r.Q ^ 103 := by
        have h : r.Q ^ 103 = r.Q ^ 87 * r.Q ^ 16 := by ring
        rw [h]
        have hpos : 0 ≤ r.Q ^ 87 := pow_nonneg hQ_nonneg 87
        have h_ge_one : 1 ≤ r.Q ^ 16 := h_pow_Q_ge_one (by omega)
        calc
          r.Q ^ 87 = r.Q ^ 87 * 1 := by ring
          _ ≤ r.Q ^ 87 * r.Q ^ 16 := mul_le_mul_of_nonneg_left h_ge_one hpos
      exact mul_le_mul hd_pow hQ_pow (by positivity) (by positivity)
    have h_pow2 : r.d ^ 4 * r.Q ^ 36 ≤ r.d ^ 10 * r.Q ^ 103 := by
      have hd_pow : r.d ^ 4 ≤ r.d ^ 10 := by
        have h : r.d ^ 10 = r.d ^ 4 * r.d ^ 6 := by ring
        rw [h]
        have hpos : 0 ≤ r.d ^ 4 := pow_nonneg hd_nonneg 4
        have h_ge_one : 1 ≤ r.d ^ 6 := h_pow_d_ge_one (by omega)
        calc
          r.d ^ 4 = r.d ^ 4 * 1 := by ring
          _ ≤ r.d ^ 4 * r.d ^ 6 := mul_le_mul_of_nonneg_left h_ge_one hpos
      have hQ_pow : r.Q ^ 36 ≤ r.Q ^ 103 := by
        have h : r.Q ^ 103 = r.Q ^ 36 * r.Q ^ 67 := by ring
        rw [h]
        have hpos : 0 ≤ r.Q ^ 36 := pow_nonneg hQ_nonneg 36
        have h_ge_one : 1 ≤ r.Q ^ 67 := h_pow_Q_ge_one (by omega)
        calc
          r.Q ^ 36 = r.Q ^ 36 * 1 := by ring
          _ ≤ r.Q ^ 36 * r.Q ^ 67 := mul_le_mul_of_nonneg_left h_ge_one hpos
      exact mul_le_mul hd_pow hQ_pow (by positivity) (by positivity)
    have h_coeff_sum : (101 / 100 : ℝ) * (32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp) +
        25 * r.d ^ 4 * r.Q ^ 36 * r.tp + 2 ^ 16 * r.d ^ 10 * r.Q ^ 103 * r.tp ≤
        2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
      have h_term1' : (101 / 100 : ℝ) * (32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp) ≤
          (101 / 100 : ℝ) * ((32 + 2375 / 100 : ℝ) * (r.d ^ 10 * r.Q ^ 103) * r.tp) := by
        have hsum : 32 * r.d ^ 6 * r.Q ^ 87 * r.tp + (2375 / 100 : ℝ) * r.d ^ 6 * r.Q ^ 87 * r.tp =
            (32 + 2375 / 100 : ℝ) * (r.d ^ 6 * r.Q ^ 87) * r.tp := by ring
        rw [hsum]
        have htemp : (32 + 2375 / 100 : ℝ) * (r.d ^ 6 * r.Q ^ 87) ≤ (32 + 2375 / 100 : ℝ) * (r.d ^ 10 * r.Q ^ 103) :=
          mul_le_mul_of_nonneg_left h_pow1 (by positivity)
        have htemp2 : (32 + 2375 / 100 : ℝ) * (r.d ^ 6 * r.Q ^ 87) * r.tp ≤
            (32 + 2375 / 100 : ℝ) * (r.d ^ 10 * r.Q ^ 103) * r.tp :=
          mul_le_mul_of_nonneg_right htemp htp_nonneg
        exact mul_le_mul_of_nonneg_left htemp2 (by norm_num)
      have h_total : (101 / 100 : ℝ) * ((32 + 2375 / 100 : ℝ) * (r.d ^ 10 * r.Q ^ 103) * r.tp) +
          25 * r.d ^ 4 * r.Q ^ 36 * r.tp + 2 ^ 16 * r.d ^ 10 * r.Q ^ 103 * r.tp ≤
          2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp := by
        have h_term1'' : (101 / 100 : ℝ) * ((32 + 2375 / 100 : ℝ) * (r.d ^ 10 * r.Q ^ 103) * r.tp) =
            ((101 / 100 : ℝ) * (32 + 2375 / 100 : ℝ)) * (r.d ^ 10 * r.Q ^ 103 * r.tp) := by ring
        rw [h_term1'']
        have h_term2' : 25 * r.d ^ 4 * r.Q ^ 36 * r.tp ≤ 25 * (r.d ^ 10 * r.Q ^ 103) * r.tp := by
          have : r.d ^ 4 * r.Q ^ 36 ≤ r.d ^ 10 * r.Q ^ 103 := h_pow2
          nlinarith
        have h_sum : (101 / 100 : ℝ) * (32 + 2375 / 100 : ℝ) + 25 + 2 ^ 16 ≤ 2 ^ 17 := by
          norm_num
        nlinarith
      linarith
    linarith
  exact And.intro h_nonneg h_upper

theorem wr_we (h : r.OK) : 0 ≤ r.wr ∧ r.wr ≤ r.d ^ 2 * r.Q ^ 3 * r.tp / 10 ∧ 0 ≤ r.we ∧ r.we ≤ r.tp / 64 := by
  have hQpos : 0 < r.Q := h.hQ0
  have hQ_nonneg : 0 ≤ r.Q := by linarith
  have htp_pos : 0 < r.tp := h.htp0
  have htp_nonneg : 0 ≤ r.tp := by linarith
  have hd_nonneg : 0 ≤ r.d := by linarith [h.hd]
  have hLe_pos : 0 < r.Le := by linarith [h.hL1]
  have hLe_nonneg : 0 ≤ r.Le := by linarith
  have h10Le_nonneg : 0 ≤ 10 * r.Le := by nlinarith
  -- From h.hL40 : (10 * r.Le) ^ 40 ≤ r.Ne and h.hQ : r.Q ^ 40 = r.Ne
  have hL40_le_Q40 : (10 * r.Le) ^ 40 ≤ r.Q ^ 40 := by
    calc
      (10 * r.Le) ^ 40 ≤ r.Ne := h.hL40
      _ = r.Q ^ 40 := by symm; exact h.hQ
  have h10Le_le_Q : 10 * r.Le ≤ r.Q :=
    ((pow_le_pow_iff_left₀ h10Le_nonneg hQ_nonneg (by norm_num)).mp hL40_le_Q40)
  have hLe3_le_Q3_div_1000 : r.Le ^ 3 ≤ r.Q ^ 3 / 1000 := by
    have hLe_le_Q_div_10 : r.Le ≤ r.Q / 10 := by linarith
    have hQ_div_10_nonneg : 0 ≤ r.Q / 10 := by nlinarith
    have hcube : r.Le ^ 3 ≤ (r.Q / 10) ^ 3 :=
      ((pow_le_pow_iff_left₀ hLe_nonneg hQ_div_10_nonneg (by norm_num)).mpr hLe_le_Q_div_10)
    have hcalc : (r.Q / 10) ^ 3 = r.Q ^ 3 / 1000 := by ring
    rw [hcalc] at hcube
    exact hcube
  have hrho_nonneg : 0 ≤ r.rho := by
    rw [h.hrho]
    positivity
  have heps_nonneg : 0 ≤ r.eps := by
    rw [h.heps]
    positivity
  have hwr_nonneg : 0 ≤ r.wr := by
    rw [Reg.wr]
    nlinarith
  have hwe_nonneg : 0 ≤ r.we := by
    rw [Reg.we]
    nlinarith
  have hwr_le : r.wr ≤ r.d ^ 2 * r.Q ^ 3 * r.tp / 10 := by
    rw [Reg.wr, h.hrho]
    -- Goal: r.tp / 16 * (1450 * r.d ^ 2 * r.Le ^ 3) ≤ r.d ^ 2 * r.Q ^ 3 * r.tp / 10
    -- Multiply both sides by 80 (LCM of 16 and 10):
    -- 5 * r.tp * 1450 * r.d ^ 2 * r.Le ^ 3 ≤ 8 * r.d ^ 2 * r.Q ^ 3 * r.tp
    -- Since r.tp > 0, cancel it:
    -- 7250 * r.d ^ 2 * r.Le ^ 3 ≤ 8 * r.d ^ 2 * r.Q ^ 3
    -- From hLe3_le_Q3_div_1000: 1000 * r.Le ^ 3 ≤ r.Q ^ 3
    -- So 7250 * r.Le ^ 3 = 7.25 * (1000 * r.Le ^ 3) ≤ 7.25 * r.Q ^ 3 ≤ 8 * r.Q ^ 3
    have hkey : (7250 : ℝ) * r.Le ^ 3 ≤ (8 : ℝ) * r.Q ^ 3 := by
      have htemp : r.Le ^ 3 ≤ r.Q ^ 3 / 1000 := hLe3_le_Q3_div_1000
      have htemp2 : (1000 : ℝ) * r.Le ^ 3 ≤ r.Q ^ 3 := by linarith
      have htemp3 : (7250 : ℝ) * r.Le ^ 3 = ((29 : ℝ) / 4) * ((1000 : ℝ) * r.Le ^ 3) := by ring
      rw [htemp3]
      have hpos : 0 ≤ (29 : ℝ) / 4 := by norm_num
      have hQ3_nonneg : 0 ≤ r.Q ^ 3 := by
        have : 0 ≤ r.Q := hQ_nonneg
        positivity
      have h1 : ((29 : ℝ) / 4) * ((1000 : ℝ) * r.Le ^ 3) ≤ ((29 : ℝ) / 4) * r.Q ^ 3 := by
        nlinarith
      have h2 : ((29 : ℝ) / 4) * r.Q ^ 3 ≤ (8 : ℝ) * r.Q ^ 3 := by
        nlinarith
      nlinarith
    -- Now multiply both sides by r.d ^ 2 * r.tp (which is ≥ 0)
    have hd2tp_nonneg : 0 ≤ r.d ^ 2 * r.tp := by positivity
    have hgoal : (r.tp / 16 * (1450 * r.d ^ 2 * r.Le ^ 3)) ≤ r.d ^ 2 * r.Q ^ 3 * r.tp / 10 := by
      nlinarith
    exact hgoal
  have hwe_le : r.we ≤ r.tp / 64 := by
    rw [Reg.we]
    have h : r.tp / 16 * r.eps ≤ r.tp / 16 * (1/4) := by
      have : r.eps ≤ 1/4 := h.heps4
      nlinarith
    have h2 : r.tp / 16 * (1/4 : ℝ) = r.tp / 64 := by ring
    rw [h2] at h
    exact h
  exact And.intro hwr_nonneg (And.intro hwr_le (And.intro hwe_nonneg hwe_le))

set_option maxHeartbeats 800000 in
theorem Dw_le (h : r.OK) : 0 ≤ r.Ds5 ∧ 0 ≤ r.Dw ∧ r.Dw ≤ 3 * r.d ^ 4 * r.Q ^ 77 * r.tp := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, hQL, -, -, -, -⟩ := h.Q_bd
  obtain ⟨heta0, heta1⟩ := h.eta_bd
  obtain ⟨heY0, heY⟩ := h.eY_le
  obtain ⟨hYb1, hYb⟩ := h.Yb_bd
  obtain ⟨hDc0, hDc⟩ := h.Dc_le
  obtain ⟨hcb0, hcb⟩ := h.cb_le
  obtain ⟨hXi0, hXiXi1, hXi1⟩ := h.Xi1_le
  obtain ⟨-, -, hexi0, hexi⟩ := h.ezt_exi
  obtain ⟨hsL0, hsL⟩ := h.sqrtLam
  obtain ⟨-, -, hDu0, hDu⟩ := h.Xb_Du
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hLe1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hL1
  have hYb0 : 0 ≤ r.Yb := le_trans (by positivity) hYb1
  -- `cb ≤ 1`, `Dc ≤ u`
  have hcb1 : r.cb ≤ 1 := by
    have : (1 : ℝ) ≤ r.d ^ 2 * r.Le ^ 7 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) (one_le_pow₀ hLe1)
    have : 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) ≤ 54 / 10 ^ 10 := div_le_self (by norm_num) this
    linarith
  have hDcu : r.Dc ≤ r.tp := by nlinarith
  -- `√Le ≤ Le ≤ Q`, so `eY ≤ 2 Q u`
  have hsLe : Real.sqrt r.Le ≤ r.Le := by
    have : Real.sqrt r.Le ≤ Real.sqrt (r.Le ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have heYQ : r.eY ≤ 2 * r.Q * r.tp := by nlinarith
  -- `Dq ≤ 4 d² Q² u`
  have hXi1sq : r.Xi1 ^ 2 ≤ r.d ^ 2 * r.Q ^ 2 := by
    have := pow_le_pow_left₀ (le_trans hXi0 hXiXi1) hXi1 2
    nlinarith
  have hdQ : (1 : ℝ) ≤ r.d * r.Q := one_le_mul_of_one_le_of_one_le hd hQ1
  have hdQ2 : r.d * r.Q ≤ r.d ^ 2 * r.Q ^ 2 := by nlinarith
  have hDq0 : 0 ≤ r.Dq := by simp only [Reg.Dq]; have := le_trans hXi0 hXiXi1; positivity
  have hDq : r.Dq ≤ 4 * r.d ^ 2 * r.Q ^ 2 * r.tp := by
    simp only [Reg.Dq]
    have a1 : r.Dc * (1 + r.Xi1 ^ 2) ≤ r.tp * (2 * r.d ^ 2 * r.Q ^ 2) := by
      apply mul_le_mul hDcu (by nlinarith) (by positivity) htp0.le
    have a2 : 202 / 100 * r.cb * r.Xi1 * r.exi ≤ 202 / 100 * 1 * (r.d * r.Q) * (r.tp / 2) := by
      have := le_trans hXi0 hXiXi1
      gcongr
    have a3 := mul_le_mul_of_nonneg_right hdQ2 htp0.le
    have a4 : 0 ≤ r.d ^ 2 * r.Q ^ 2 * r.tp := by positivity
    linarith
  -- `Ds5 ≤ 5 d² Q^7 u`
  have hQ5 : r.Q ≤ r.Q ^ 7 := le_self_pow₀ hQ1 (by norm_num)
  have hQ57 : r.Q ^ 5 ≤ r.Q ^ 7 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hd2 : (1 : ℝ) ≤ r.d ^ 2 := one_le_pow₀ hd
  have hQ7 : (1 : ℝ) ≤ r.Q ^ 7 := one_le_pow₀ hQ1
  have hDs50 : 0 ≤ r.Ds5 := by simp only [Reg.Ds5]; positivity
  have hDs5 : r.Ds5 ≤ 7 * (r.d ^ 2 * r.Q ^ 7 * r.tp) := by
    simp only [Reg.Ds5]
    have b1 : r.eY + 3 * r.tp / 16 * r.Yb + r.Yb * r.Dq ≤
        2 * r.Q * r.tp + 3 * r.tp / 16 * r.Q ^ 5 + r.Q ^ 5 * (4 * r.d ^ 2 * r.Q ^ 2 * r.tp) := by
      gcongr
    have b2 : 0 ≤ r.eY + 3 * r.tp / 16 * r.Yb + r.Yb * r.Dq := by positivity
    have b3 : 103 / 100 * r.eta * (r.eY + 3 * r.tp / 16 * r.Yb + r.Yb * r.Dq) ≤
        103 / 100 * 1 * (2 * r.Q * r.tp + 3 * r.tp / 16 * r.Q ^ 5 + r.Q ^ 5 * (4 * r.d ^ 2 * r.Q ^ 2 * r.tp)) := by
      gcongr
    have m : (0 : ℝ) ≤ r.d ^ 2 * r.Q ^ 7 * r.tp := by positivity
    have c1 : r.Q * r.tp ≤ r.d ^ 2 * r.Q ^ 7 * r.tp := by
      have : r.Q ≤ r.d ^ 2 * r.Q ^ 7 := le_trans hQ5 (le_mul_of_one_le_left (by positivity) hd2)
      exact mul_le_mul_of_nonneg_right this htp0.le
    have c2 : r.Q ^ 5 * r.tp ≤ r.d ^ 2 * r.Q ^ 7 * r.tp := by
      have : r.Q ^ 5 ≤ r.d ^ 2 * r.Q ^ 7 := le_trans hQ57 (le_mul_of_one_le_left (by positivity) hd2)
      exact mul_le_mul_of_nonneg_right this htp0.le
    have c3 : r.tp ≤ r.d ^ 2 * r.Q ^ 7 * r.tp := le_mul_of_one_le_left htp0.le (one_le_mul_of_one_le_of_one_le hd2 hQ7)
    have e : r.Q ^ 5 * (4 * r.d ^ 2 * r.Q ^ 2 * r.tp) = 4 * (r.d ^ 2 * r.Q ^ 7 * r.tp) := by ring
    linarith
  refine ⟨hDs50, ?_, ?_⟩
  · simp only [Reg.Dw]; positivity
  · simp only [Reg.Dw]
    have d1 : r.Ds5 * Real.sqrt r.Lam * r.Xi ≤ 7 * (r.d ^ 2 * r.Q ^ 7 * r.tp) * (r.d * r.Q ^ 20) * (r.d * r.Q) := by
      gcongr; exact le_trans hXiXi1 hXi1
    have d2 : 103 / 100 * r.eta * r.Yb * r.Du ≤ 103 / 100 * 1 * r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) := by
      gcongr
    have e1 : 7 * (r.d ^ 2 * r.Q ^ 7 * r.tp) * (r.d * r.Q ^ 20) * (r.d * r.Q) = 7 * (r.d ^ 4 * r.Q ^ 28 * r.tp) := by
      ring
    have e2 : 103 / 100 * 1 * r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) = 206 / 100 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by
      ring
    have f : 7 * (r.d ^ 4 * r.Q ^ 28 * r.tp) ≤ 94 / 100 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by
      have hQ49 : (2 : ℝ) ^ 17 ≤ r.Q ^ 49 := le_trans hQ17 (le_self_pow₀ hQ1 (by norm_num))
      have : r.Q ^ 77 = r.Q ^ 28 * r.Q ^ 49 := by ring
      have m : (0 : ℝ) ≤ r.d ^ 4 * r.Q ^ 28 * r.tp := by positivity
      rw [this]
      have : r.d ^ 4 * (r.Q ^ 28 * r.Q ^ 49) * r.tp = (r.d ^ 4 * r.Q ^ 28 * r.tp) * r.Q ^ 49 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hQ49 m
      linarith
    calc _ ≤ 7 * (r.d ^ 2 * r.Q ^ 7 * r.tp) * (r.d * r.Q ^ 20) * (r.d * r.Q) +
          103 / 100 * 1 * r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) := add_le_add d1 d2
      _ = 7 * (r.d ^ 4 * r.Q ^ 28 * r.tp) + 206 / 100 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by rw [e1, e2]
      _ ≤ 3 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by linarith
      _ = 3 * r.d ^ 4 * r.Q ^ 77 * r.tp := by ring

theorem W0_bd (h : r.OK) : r.R ≤ r.W0 ∧ r.W0 ≤ r.d ^ 2 * r.Q ^ 20 := by
  rcases h.R_bd with ⟨hR_le, _⟩
  rcases h.Q_bd with ⟨hQ_ge, _, _, _, _, hd_le_Q3⟩
  have hsqrtL_ge : 132 ≤ Real.sqrt r.Le := h.sqrtL_ge
  have hd_ge1 : 1 ≤ r.d := h.hd
  have hpos_d : 0 ≤ r.d := by linarith
  have hpos_Ne : 0 ≤ r.Ne := by
    have hpos_pow : (0 : ℝ) < 2 ^ 700 := by norm_num
    have hlt : (2 ^ 700 : ℝ) < r.Ne := h.hN700
    exact (hpos_pow.trans hlt).le
  have hpos_Q20 : 0 ≤ r.Q ^ 20 := by positivity
  have hW0_def : r.W0 = r.R + 4 * r.d * Real.sqrt (r.Ne / r.Le) := rfl
  have h_first : r.R ≤ r.W0 := by
    rw [hW0_def]
    have h_nonneg : 0 ≤ 4 * r.d * Real.sqrt (r.Ne / r.Le) := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (r.Ne / r.Le) := Real.sqrt_nonneg _
      positivity
    nlinarith
  have h_second : r.W0 ≤ r.d ^ 2 * r.Q ^ 20 := by
    rw [hW0_def]
    have h_sqrt_div : Real.sqrt (r.Ne / r.Le) = Real.sqrt r.Ne / Real.sqrt r.Le :=
      Real.sqrt_div hpos_Ne r.Le
    have h_sqrt_Ne : Real.sqrt r.Ne = r.Q ^ 20 := by
      calc
        Real.sqrt r.Ne = Real.sqrt (r.Q ^ 40) := by rw [h.hQ]
        _ = Real.sqrt ((r.Q ^ 20) ^ 2) := by ring_nf
        _ = r.Q ^ 20 := Real.sqrt_sq hpos_Q20
    have h_denom_pos : 0 < Real.sqrt r.Le :=
      Real.sqrt_pos.mpr (by linarith [h.hL1] : 0 < r.Le)
    have h_sqrt_term : 4 * r.d * Real.sqrt (r.Ne / r.Le) ≤ r.d * r.Q ^ 20 / 33 := by
      rw [h_sqrt_div, h_sqrt_Ne]
      have h_div_le : (1 : ℝ) / Real.sqrt r.Le ≤ (1 : ℝ) / 132 := by
        refine (one_div_le_one_div h_denom_pos (by norm_num : 0 < (132 : ℝ))).mpr hsqrtL_ge
      calc
        4 * r.d * (r.Q ^ 20 / Real.sqrt r.Le) = (4 * r.d * r.Q ^ 20) * ((1 : ℝ) / Real.sqrt r.Le) := by ring
        _ ≤ (4 * r.d * r.Q ^ 20) * ((1 : ℝ) / 132) :=
          mul_le_mul_of_nonneg_left h_div_le (by positivity)
        _ = r.d * r.Q ^ 20 / 33 := by ring
    have h_sum : r.R + 4 * r.d * Real.sqrt (r.Ne / r.Le) ≤ 190 * r.d ^ 2 + r.d * r.Q ^ 20 / 33 := by
      nlinarith
    have hQ20_ge_380 : (380 : ℝ) ≤ r.Q ^ 20 := by
      have hQ_pow : (2^17 : ℝ) ^ 20 ≤ r.Q ^ 20 := by
        gcongr
      have h_comp : (380 : ℝ) ≤ (2^17 : ℝ) ^ 20 := by norm_num
      nlinarith
    have h_final : 190 * r.d ^ 2 + r.d * r.Q ^ 20 / 33 ≤ r.d ^ 2 * r.Q ^ 20 := by
      have h1 : 190 * r.d ≤ r.d * r.Q ^ 20 / 2 := by
        have : 380 * r.d ≤ r.d * r.Q ^ 20 := by
          nlinarith
        nlinarith
      have h2 : r.Q ^ 20 / 33 ≤ r.d * r.Q ^ 20 / 2 := by
        nlinarith
      nlinarith
    nlinarith
  exact And.intro h_first h_second

/-! ## The conditions of the precision theorem -/

theorem ePhi_le_eh (h : r.OK) : r.ePhi ≤ r.eh := by
  obtain ⟨hQ17, -, -, -, -, hdQ⟩ := h.Q_bd
  obtain ⟨-, hP⟩ := h.ePhi_bd
  obtain ⟨heh1, -⟩ := h.eh_bd
  have hd0 : 0 ≤ r.d := by linarith [h.hd]
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have htp := h.htp0
  have hd4 : r.d ^ 4 ≤ r.Q ^ 12 := by
    calc r.d ^ 4 ≤ (r.Q ^ 3) ^ 4 := pow_le_pow_left₀ hd0 hdQ 4
      _ = r.Q ^ 12 := by ring
  have hQ : r.Q ^ 115 ≤ r.Q ^ 120 := pow_le_pow_right₀ hQ1 (by norm_num)
  calc r.ePhi ≤ 2 ^ 15 * r.d ^ 10 * r.Q ^ 103 * r.tp := hP
    _ = 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 103 * r.d ^ 4 := by ring
    _ ≤ 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 103 * r.Q ^ 12 := by gcongr
    _ = 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 115 := by ring
    _ ≤ 2 ^ 64 * (r.d ^ 6 * r.tp) * r.Q ^ 120 := by
        have m0 : 0 ≤ r.d ^ 6 * r.tp := by positivity
        have k : (2 : ℝ) ^ 15 ≤ 2 ^ 64 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        have k1 : (2 : ℝ) ^ 15 * (r.d ^ 6 * r.tp) ≤ 2 ^ 64 * (r.d ^ 6 * r.tp) := mul_le_mul_of_nonneg_right k m0
        have k2 : (0 : ℝ) ≤ 2 ^ 64 * (r.d ^ 6 * r.tp) := mul_nonneg (by norm_num) m0
        have k3 : (0 : ℝ) ≤ r.Q ^ 115 := by positivity
        exact mul_le_mul k1 hQ k3 k2
    _ = 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp := by ring
    _ ≤ r.eh := heh1

theorem eX_le_eh (h : r.OK) : r.eX ≤ r.eh := by
  have hQ_bd := Q_bd h
  have heh_bd := eh_bd h
  have heX_bd := eX_bd h
  rcases hQ_bd with ⟨_, _, _, _, _, hd_le_Q3⟩
  rcases heX_bd with ⟨_, heX_le⟩
  rcases heh_bd with ⟨eh_bd_le, _⟩
  have htp_pos : 0 < r.tp := h.htp0
  have hQ_pos : 0 < r.Q := h.hQ0
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num) h.hd
  have hQ_nonneg : 0 ≤ r.Q := by linarith
  have hQ_ge_one : 1 ≤ r.Q := by
    have hN_pos : 1 < r.Ne := by
      have hd1 : 1 ≤ r.d := h.hd
      have hn1 : 1 ≤ r.n := h.hn
      have hd3 : 1 ≤ r.d ^ 3 := by
        have : 1 ^ 3 ≤ r.d ^ 3 := pow_le_pow_left₀ (by norm_num) hd1 3
        simpa using this
      have hn4 : 1 ≤ r.n ^ 4 := by
        have : 1 ^ 4 ≤ r.n ^ 4 := pow_le_pow_left₀ (by norm_num) hn1 4
        simpa using this
      rw [h.hNe]
      have hpos : 0 < 15 * 2 ^ 17 := by norm_num
      nlinarith
    have hQ40_gt_one : 1 < r.Q ^ 40 := by
      rw [h.hQ]
      exact hN_pos
    by_contra! hQ_le
    have hQ40_le_one : r.Q ^ 40 ≤ 1 := by
      have hQ_le_one : r.Q ≤ 1 := by linarith
      have : r.Q ^ 40 ≤ 1 ^ 40 := pow_le_pow_left₀ hQ_nonneg hQ_le_one 40
      simpa using this
    linarith
  have hd_pow4 : r.d ^ 4 ≤ r.Q ^ 12 := by
    have hd4 : r.d ^ 4 ≤ (r.Q ^ 3) ^ 4 := pow_le_pow_left₀ hd_nonneg hd_le_Q3 4
    have hQ12 : (r.Q ^ 3) ^ 4 = r.Q ^ 12 := by ring
    rw [hQ12] at hd4
    exact hd4
  have h_main : 2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp ≤ 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp := by
    have hQ115_le_Q120 : r.Q ^ 115 ≤ r.Q ^ 120 := by
      have h115_le_120 : (115 : ℕ) ≤ 120 := by omega
      exact pow_le_pow_right₀ hQ_ge_one h115_le_120
    have h2_17_le_2_64 : (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ 64 := by norm_num
    have hd10_eq : r.d ^ 10 = r.d ^ 6 * r.d ^ 4 := by ring
    have hd6_nonneg : 0 ≤ r.d ^ 6 := pow_nonneg hd_nonneg 6
    have htp_nonneg : 0 ≤ r.tp := by linarith
    have h1 : 2 ^ 17 * r.d ^ 10 * r.Q ^ 103 * r.tp = 2 ^ 17 * (r.d ^ 6 * r.d ^ 4) * r.Q ^ 103 * r.tp := by rw [hd10_eq]
    have h2 : 2 ^ 17 * (r.d ^ 6 * r.d ^ 4) * r.Q ^ 103 * r.tp ≤ 2 ^ 17 * (r.d ^ 6 * r.Q ^ 12) * r.Q ^ 103 * r.tp := by
      have h_inner : r.d ^ 6 * r.d ^ 4 ≤ r.d ^ 6 * r.Q ^ 12 := mul_le_mul_of_nonneg_left hd_pow4 hd6_nonneg
      have h_nonneg_2_17 : 0 ≤ (2 : ℝ) ^ 17 := by norm_num
      have h_nonneg_Q103 : 0 ≤ r.Q ^ 103 := pow_nonneg hQ_nonneg 103
      have h_nonneg_tp : 0 ≤ r.tp := by linarith
      have : (2 : ℝ) ^ 17 * (r.d ^ 6 * r.d ^ 4) * r.Q ^ 103 * r.tp ≤ (2 : ℝ) ^ 17 * (r.d ^ 6 * r.Q ^ 12) * r.Q ^ 103 * r.tp := by
        apply mul_le_mul_of_nonneg_right ?_ h_nonneg_tp
        apply mul_le_mul_of_nonneg_right ?_ h_nonneg_Q103
        apply mul_le_mul_of_nonneg_left h_inner h_nonneg_2_17
      exact this
    have h3 : 2 ^ 17 * (r.d ^ 6 * r.Q ^ 12) * r.Q ^ 103 * r.tp = 2 ^ 17 * r.d ^ 6 * r.Q ^ 115 * r.tp := by ring
    have h4 : 2 ^ 17 * r.d ^ 6 * r.Q ^ 115 * r.tp ≤ 2 ^ 64 * r.d ^ 6 * r.Q ^ 115 * r.tp := by
      have h_nonneg_rest : 0 ≤ r.d ^ 6 * r.Q ^ 115 := by
        have h1 : 0 ≤ r.d ^ 6 := hd6_nonneg
        have h2 : 0 ≤ r.Q ^ 115 := pow_nonneg hQ_nonneg 115
        nlinarith
      have : (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ 64 := h2_17_le_2_64
      nlinarith
    have h5 : 2 ^ 64 * r.d ^ 6 * r.Q ^ 115 * r.tp ≤ 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp := by
      have h_inner2 : r.d ^ 6 * r.Q ^ 115 ≤ r.d ^ 6 * r.Q ^ 120 := by
        have : r.Q ^ 115 ≤ r.Q ^ 120 := hQ115_le_Q120
        have h_nonneg_d6 : 0 ≤ r.d ^ 6 := hd6_nonneg
        exact mul_le_mul_of_nonneg_left this h_nonneg_d6
      have h_nonneg_2_64 : 0 ≤ (2 : ℝ) ^ 64 := by norm_num
      have h_nonneg_tp : 0 ≤ r.tp := by linarith
      nlinarith
    linarith
  linarith

theorem h_bd (h : r.OK) : 0 ≤ r.h ∧ r.h ≤ 1002 / 1000 * r.R * r.eh := by
  obtain ⟨hQ17, -, -, -, -, hdQ⟩ := h.Q_bd
  obtain ⟨hP0, hP⟩ := h.ePhi_bd
  obtain ⟨heh1, -⟩ := h.eh_bd
  obtain ⟨hwr0, hwr, hwe0, hwe⟩ := h.wr_we
  have hR1 := h.hR1
  have hR2 := h.hR2
  have hd := h.hd
  have hd0 : 0 ≤ r.d := by linarith
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hQ0 : 0 < r.Q := by linarith
  have htp := h.htp0
  have hR0 : 0 ≤ r.R := by linarith
  have hde : r.de = 1 / r.Q ^ 40 := by rw [h.hde, ← h.hQ]
  have hh : r.h = r.R * (r.eh + (r.ePhi + 8 * r.wr + 2 * r.R ^ 2 * r.we * r.Q ^ 80 + 2 * r.we)) := by
    simp only [Reg.h]; rw [hde]; field_simp; ring
  set m := r.d ^ 6 * r.Q ^ 120 * r.tp with hm
  have hm0 : 0 ≤ m := by positivity
  have hd61 : (1 : ℝ) ≤ r.d ^ 6 := one_le_pow₀ hd
  -- the four small terms
  have hd4 : r.d ^ 4 ≤ r.Q ^ 12 := by
    calc r.d ^ 4 ≤ (r.Q ^ 3) ^ 4 := pow_le_pow_left₀ hd0 hdQ 4
      _ = r.Q ^ 12 := by ring
  have a1 : r.ePhi ≤ 2 ^ 15 * m := by
    have hQ : r.Q ^ 115 ≤ r.Q ^ 120 := pow_le_pow_right₀ hQ1 (by norm_num)
    calc r.ePhi ≤ 2 ^ 15 * r.d ^ 10 * r.Q ^ 103 * r.tp := hP
      _ = 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 103 * r.d ^ 4 := by ring
      _ ≤ 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 103 * r.Q ^ 12 := by gcongr
      _ = 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 115 := by ring
      _ ≤ 2 ^ 15 * (r.d ^ 6 * r.tp) * r.Q ^ 120 := by gcongr
      _ = 2 ^ 15 * m := by rw [hm]; ring
  have hmono : ∀ a b : ℕ, a ≤ 6 → b ≤ 120 → r.d ^ a * r.Q ^ b * r.tp ≤ m := by
    intro a b ha hb
    rw [hm]
    have := mul_le_mul (pow_le_pow_right₀ hd ha) (pow_le_pow_right₀ hQ1 hb) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this htp.le
  have a2 : 8 * r.wr ≤ m := by
    have := hmono 2 3 (by norm_num) (by norm_num)
    linarith
  have a3 : 2 * r.R ^ 2 * r.we * r.Q ^ 80 ≤ 1129 * m := by
    have := hmono 3 80 (by norm_num) (by norm_num)
    have b1 : 2 * r.R ^ 2 * r.we * r.Q ^ 80 ≤ 2 * (190 ^ 2 * r.d ^ 3) * (r.tp / 64) * r.Q ^ 80 := by gcongr
    have e : 2 * (190 ^ 2 * r.d ^ 3) * (r.tp / 64) * r.Q ^ 80 = 72200 / 64 * (r.d ^ 3 * r.Q ^ 80 * r.tp) := by ring
    linarith
  have a4 : 2 * r.we ≤ m := by
    have := hmono 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    linarith
  have hS0 : 0 ≤ r.ePhi + 8 * r.wr + 2 * r.R ^ 2 * r.we * r.Q ^ 80 + 2 * r.we := by positivity
  have hS : r.ePhi + 8 * r.wr + 2 * r.R ^ 2 * r.we * r.Q ^ 80 + 2 * r.we ≤ 2 / 1000 * r.eh := by
    have : (2 : ℝ) ^ 15 * m + m + 1129 * m + m ≤ 2 / 1000 * (2 ^ 64 * m) := by nlinarith
    have e : 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp = 2 ^ 64 * m := by rw [hm]; ring
    linarith
  have heh0 : 0 ≤ r.eh := le_trans (by positivity) heh1
  refine ⟨by rw [hh]; positivity, ?_⟩
  rw [hh]
  calc r.R * (r.eh + (r.ePhi + 8 * r.wr + 2 * r.R ^ 2 * r.we * r.Q ^ 80 + 2 * r.we))
      ≤ r.R * (r.eh + 2 / 1000 * r.eh) := by gcongr
    _ = 1002 / 1000 * r.R * r.eh := by ring

theorem sel_le (h : r.OK) : r.sel ≤ r.selR := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, -, -, -, -, -⟩ := h.Q_bd
  obtain ⟨hh0, hh⟩ := h.h_bd
  obtain ⟨-, hwr, -, -⟩ := h.wr_we
  obtain ⟨heh1, heh2⟩ := h.eh_bd
  obtain ⟨hRd, hR1d⟩ := h.R_bd
  have hR1 := h.hR1
  have hR2 := h.hR2
  have hd := h.hd
  have hQ0 : 0 < r.Q := h.hQ0
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hR0 : 0 < r.R := by linarith
  have hde : r.de = 1 / r.Q ^ 40 := by rw [h.hde, ← h.hQ]
  -- `wr ≤ eh`
  have hwe : r.wr ≤ r.eh := by
    have : r.d ^ 2 * r.Q ^ 3 * r.tp / 10 ≤ 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp := by
      have h1 : r.d ^ 2 ≤ r.d ^ 6 := pow_le_pow_right₀ hd (by norm_num)
      have h2 : r.Q ^ 3 ≤ r.Q ^ 120 := pow_le_pow_right₀ hQ1 (by norm_num)
      have : r.d ^ 2 * r.Q ^ 3 ≤ r.d ^ 6 * r.Q ^ 120 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have h3 := mul_le_mul_of_nonneg_right this htp0.le
      have h4 : (0 : ℝ) ≤ r.d ^ 6 * r.Q ^ 120 * r.tp := by positivity
      nlinarith
    linarith
  -- `sel ≤ 6 R² Q^80 eh`
  set X := r.R ^ 2 * r.Q ^ 80 * r.eh with hX
  have hX5 : 5 * r.eh ≤ X := by
    have : (5 : ℝ) ≤ r.R ^ 2 * r.Q ^ 80 := by
      have h1 : (157 : ℝ) ^ 2 ≤ r.R ^ 2 := by nlinarith
      have h2 : (1 : ℝ) ≤ r.Q ^ 80 := one_le_pow₀ hQ1
      nlinarith
    nlinarith
  have hsel : r.sel ≤ 6 * X := by
    have hL : r.LipF = 4 * r.R * r.Q ^ 80 := by
      simp only [Reg.LipF, hde]; field_simp
    have : r.LipF * r.h ≤ 4 * r.R * r.Q ^ 80 * (1002 / 1000 * r.R * r.eh) := by
      rw [hL]; exact mul_le_mul_of_nonneg_left hh (by positivity)
    simp only [Reg.sel]
    nlinarith
  -- `selR = 3/(16 d R² (R + 1)² Q^200)`
  have hselR : r.selR = 3 / (16 * r.d * r.R ^ 2 * (r.R + 1) ^ 2 * r.Q ^ 200) := by
    simp only [Reg.selR, Reg.rmin, hde]; field_simp; ring
  rw [hselR, le_div_iff₀ (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_right hsel (by positivity)) ?_
  -- `96 d R^4 (R + 1)^2 Q^280 eh ≤ 3`
  have hE : r.eh * (2 ^ 87 * r.Q ^ 280 * r.d ^ 10) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at heh2; linarith
  have hR4 : r.R ^ 4 ≤ 190 ^ 4 * r.d ^ 6 := by nlinarith
  have hRR : r.R ^ 4 * (r.R + 1) ^ 2 ≤ 190 ^ 4 * r.d ^ 6 * ((158 / 157) ^ 2 * 190 ^ 2 * r.d ^ 3) :=
    mul_le_mul hR4 hR1d (by positivity) (by positivity)
  have hd9 : 0 < r.d ^ 9 := by positivity
  calc 6 * X * (16 * r.d * r.R ^ 2 * (r.R + 1) ^ 2 * r.Q ^ 200)
      = 96 / 2 ^ 87 * (r.R ^ 4 * (r.R + 1) ^ 2) / r.d ^ 9 * (r.eh * (2 ^ 87 * r.Q ^ 280 * r.d ^ 10)) := by
        rw [hX]; field_simp; norm_num
    _ ≤ 96 / 2 ^ 87 * (190 ^ 4 * r.d ^ 6 * ((158 / 157) ^ 2 * 190 ^ 2 * r.d ^ 3)) / r.d ^ 9 * 1 := by
        gcongr
    _ = 96 / 2 ^ 87 * (190 ^ 6 * (158 / 157) ^ 2) := by field_simp
    _ ≤ 3 := by norm_num

theorem h_le_rmin (h : r.OK) : r.h ≤ r.rmin / 4 := by
  have hh := h_bd h
  rcases hh with ⟨_, hh_bound⟩
  have heh := eh_bd h
  rcases heh with ⟨_, heh_bound⟩
  have hR := R_bd h
  rcases hR with ⟨hR_bound, _⟩
  have hQ := Q_bd h
  rcases hQ with ⟨hQ_lb, _, _, _, _, hd_le_Q3⟩
  have hd_pos : 1 ≤ r.d := h.hd
  have hR_pos : 157 ≤ r.R := h.hR1
  have hQ_pos : 0 < r.Q := h.hQ0
  have hd_pos' : 0 < r.d := by linarith
  have hR_pos' : 0 < r.R := by linarith
  have hQ80_pos : 0 < r.Q ^ 80 := pow_pos hQ_pos 80
  -- Unfold rmin/4
  have hrmin_div4 : r.rmin / 4 = r.de ^ 2 / (8 * r.R * (r.R + 1)) := by
    dsimp [Reg.rmin]
    have hpos : 2 * r.R * (r.R + 1) * 4 ≠ 0 := by positivity
    field_simp [hpos]
    ring
  rw [hrmin_div4]
  -- Now: r.h ≤ de^2 / (8 * R * (R+1))
  apply le_trans hh_bound
  -- Substitute de = 1/Q^40
  have hde_val : r.de = 1 / (r.Q ^ 40) := by
    rw [h.hde, h.hQ]
  rw [hde_val]
  -- Goal: 1002/1000 * R * eh ≤ 1 / (8 * R * (R+1) * Q^80)
  -- Establish R^2*(R+1) ≤ 2*190^3*d^6
  have hR_sq_mul_Rp1_le_2R3 : r.R ^ 2 * (r.R + 1) ≤ 2 * r.R ^ 3 := by
    have hR_ge1 : 1 ≤ r.R := by linarith
    nlinarith
  have hR_sq_mul_Rp1_le : r.R ^ 2 * (r.R + 1) ≤ 2 * (190 : ℝ) ^ 3 * r.d ^ 6 := by
    calc
      r.R ^ 2 * (r.R + 1) ≤ 2 * r.R ^ 3 := hR_sq_mul_Rp1_le_2R3
      _ ≤ 2 * ((190 : ℝ) * r.d ^ 2) ^ 3 := by
        gcongr
      _ = 2 * (190 : ℝ) ^ 3 * r.d ^ 6 := by ring
  -- Establish eh*Q^80 ≤ 1/(2^87*Q^200*d^10)
  have heh_Q80_le : r.eh * r.Q ^ 80 ≤ 1 / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 10) := by
    calc
      r.eh * r.Q ^ 80 ≤ (1 / ((2 : ℝ) ^ 87 * r.Q ^ 280 * r.d ^ 10)) * r.Q ^ 80 := by
        gcongr
      _ = 1 / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 10) := by
        field_simp
  -- Key numeric inequality
  have h_num : (2004/125 : ℝ) * (190 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 87 := by norm_num
  have hd4_ge1 : 1 ≤ r.d ^ 4 := by
    have h1 : (1 : ℝ) ^ 4 ≤ r.d ^ 4 := pow_le_pow_left₀ (by norm_num) hd_pos 4
    simpa using h1
  have hQ_ge1 : 1 ≤ r.Q := by linarith
  have hQ200_ge1 : 1 ≤ r.Q ^ 200 := by
    have h1 : (1 : ℝ) ^ 200 ≤ r.Q ^ 200 := pow_le_pow_left₀ (by norm_num) hQ_ge1 200
    simpa using h1
  -- Main inequality chain
  have h_main : 1002/1000 * r.R * r.eh * (8 * r.R * (r.R + 1) * r.Q ^ 80) ≤ 1 := by
    calc
      1002/1000 * r.R * r.eh * (8 * r.R * (r.R + 1) * r.Q ^ 80) =
          (1002/1000 * 8) * (r.R ^ 2 * (r.R + 1)) * (r.eh * r.Q ^ 80) := by ring
      _ ≤ (1002/1000 * 8) * (2 * (190 : ℝ) ^ 3 * r.d ^ 6) * (1 / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 10)) := by
        have hC_nonneg : 0 ≤ r.eh * r.Q ^ 80 := by
          have heh_nonneg : 0 ≤ r.eh := by
            have h_eh_bound := (eh_bd h).1
            have h_nonneg : 0 ≤ 2 ^ 64 * r.d ^ 6 * r.Q ^ 120 * r.tp := by
              apply mul_nonneg
              · apply mul_nonneg
                · apply mul_nonneg
                  · positivity
                  · apply pow_nonneg (by linarith) 6
                · apply pow_nonneg (by linarith) 120
              · exact h.htp0.le
            linarith
          positivity
        have hAD_nonneg : 0 ≤ (1002/1000 * 8) * (2 * (190 : ℝ) ^ 3 * r.d ^ 6) := by positivity
        refine mul_le_mul ?_ heh_Q80_le hC_nonneg hAD_nonneg
        · gcongr
      _ = ((1002/1000 * 8) * 2 * (190 : ℝ) ^ 3) / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 4) := by
        have h_d_pow : r.d ^ 6 / r.d ^ 10 = 1 / r.d ^ 4 := by
          field_simp [hd_pos'.ne.symm]
        calc
          ((1002/1000 * 8) * (2 * (190 : ℝ) ^ 3 * r.d ^ 6)) * (1 / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 10)) =
              ((1002/1000 * 8) * 2 * (190 : ℝ) ^ 3) * (r.d ^ 6 / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 10)) := by ring
          _ = ((1002/1000 * 8) * 2 * (190 : ℝ) ^ 3) * ((r.d ^ 6 / r.d ^ 10) / ((2 : ℝ) ^ 87 * r.Q ^ 200)) := by ring
          _ = ((1002/1000 * 8) * 2 * (190 : ℝ) ^ 3) * ((1 / r.d ^ 4) / ((2 : ℝ) ^ 87 * r.Q ^ 200)) := by rw [h_d_pow]
          _ = ((1002/1000 * 8) * 2 * (190 : ℝ) ^ 3) / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 4) := by ring
      _ = (2004/125 * (190 : ℝ) ^ 3) / ((2 : ℝ) ^ 87 * r.Q ^ 200 * r.d ^ 4) := by ring
      _ ≤ (2004/125 * (190 : ℝ) ^ 3) / ((2 : ℝ) ^ 87) := by
        refine div_le_div_of_nonneg_left ?_ (by positivity) ?_
        · positivity
        · nlinarith
      _ ≤ 1 := (div_le_one (by positivity)).mpr h_num
  -- Multiply h_main by 1000 to clear the denominator
  have h_main' : 1002 * r.R * r.eh * (8 * r.R * (r.R + 1) * r.Q ^ 80) ≤ 1000 := by
    linarith
  -- Convert h_main' to the goal using field_simp
  field_simp [hR_pos'.ne.symm, hQ80_pos.ne.symm]
  linarith

theorem val_le (h : r.OK) : r.val ≤ r.valR := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, -, hQn, -, -, -⟩ := h.Q_bd
  obtain ⟨hW1, hW2⟩ := h.W0_bd
  obtain ⟨-, hDw0, hDw⟩ := h.Dw_le
  obtain ⟨hDP0, hDP⟩ := h.DP_le
  obtain ⟨hh0, hh⟩ := h.h_bd
  obtain ⟨-, heh2⟩ := h.eh_bd
  obtain ⟨hRd, -⟩ := h.R_bd
  have hR1 := h.hR1
  have hR2 := h.hR2
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hQ0 : 0 < r.Q := by linarith
  have hR0 : 0 < r.R := by linarith
  have hde : r.de = 1 / r.Q ^ 40 := by rw [h.hde, ← h.hQ]
  have hLam : r.Lam = r.d * r.Q ^ 40 := by simp only [Reg.Lam]; rw [← h.hQ]
  -- `Dw ≤ 1`, `R + W0 + Dw ≤ 2 d² Q^20`
  have t1 := h.tiny 4 77 (by norm_num) (by norm_num)
  have hDw1 : r.Dw ≤ 1 := by
    have : (3 : ℝ) / 2 ^ 160 ≤ 1 := by norm_num
    nlinarith
  have hQ20 : (2 : ℝ) ^ 340 ≤ r.Q ^ 20 := by
    calc (2 : ℝ) ^ 340 = (2 ^ 17) ^ 20 := by rw [← pow_mul]
      _ ≤ r.Q ^ 20 := pow_le_pow_left₀ (by norm_num) hQ17 20
  have hd2 : (1 : ℝ) ≤ r.d ^ 2 := one_le_pow₀ hd
  have hS : r.R + r.W0 + r.Dw ≤ 2 * r.d ^ 2 * r.Q ^ 20 := by
    have : 191 * r.d ^ 2 ≤ r.d ^ 2 * r.Q ^ 20 := by
      have : (191 : ℝ) ≤ r.Q ^ 20 :=
        le_trans (le_trans (by norm_num : (191 : ℝ) ≤ 2 ^ 8) (pow_le_pow_right₀ (by norm_num) (by norm_num))) hQ20
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ r.d ^ 2)
      linarith
    nlinarith
  have hS0 : 0 ≤ r.R + r.W0 + r.Dw := by linarith
  -- `DF ≤ 12 d^7 Q^137 u`
  have hDF : r.DF ≤ 12 * r.d ^ 7 * r.Q ^ 137 * r.tp := by
    have e1 : (r.R + r.W0 + r.Dw) ^ 2 / 2 * r.DP ≤ (2 * r.d ^ 2 * r.Q ^ 20) ^ 2 / 2 * (3 * r.d ^ 3 * r.Q ^ 91 * r.tp) := by
      gcongr
    have e2 : r.Lam * r.Dw * (2 * r.R + 2 * r.W0 + r.Dw) / 2 ≤
        r.d * r.Q ^ 40 * (3 * r.d ^ 4 * r.Q ^ 77 * r.tp) * (2 * (2 * r.d ^ 2 * r.Q ^ 20)) / 2 := by
      rw [hLam]
      have : 2 * r.R + 2 * r.W0 + r.Dw ≤ 2 * (2 * r.d ^ 2 * r.Q ^ 20) := by linarith
      have : 0 ≤ 2 * r.R + 2 * r.W0 + r.Dw := by linarith
      gcongr
    have e3 : r.Q ^ 131 ≤ r.Q ^ 137 := pow_le_pow_right₀ hQ1 (by norm_num)
    have e4 : (0 : ℝ) ≤ r.d ^ 7 * r.tp := by positivity
    simp only [Reg.DF]
    nlinarith [mul_le_mul_of_nonneg_left e3 e4]
  -- `LF h ≤ 381 d^5 Q^60 eh`
  have hLF : r.LF * r.h ≤ 381 * r.d ^ 5 * r.Q ^ 60 * r.eh := by
    have e1 : r.LF ≤ r.d * r.Q ^ 40 * (2 * r.d ^ 2 * r.Q ^ 20) := by
      simp only [Reg.LF]; rw [hLam]
      have : r.R + r.W0 ≤ 2 * r.d ^ 2 * r.Q ^ 20 := by linarith
      gcongr
    have e2 : r.h ≤ 1002 / 1000 * (190 * r.d ^ 2) * r.eh := by
      have : 1002 / 1000 * r.R * r.eh ≤ 1002 / 1000 * (190 * r.d ^ 2) * r.eh := by gcongr
      linarith
    calc r.LF * r.h ≤ r.d * r.Q ^ 40 * (2 * r.d ^ 2 * r.Q ^ 20) * (1002 / 1000 * (190 * r.d ^ 2) * r.eh) :=
          mul_le_mul e1 e2 hh0 (by positivity)
      _ = 380.76 * r.d ^ 5 * r.Q ^ 60 * r.eh := by ring
      _ ≤ 381 * r.d ^ 5 * r.Q ^ 60 * r.eh := by gcongr; norm_num
  -- the two small terms
  have t2 := h.tiny 11 197 (by norm_num) (by norm_num)
  have hE : r.d ^ 9 * r.Q ^ 120 * r.eh ≤ 1 / 2 ^ 87 := by
    have : r.eh * (2 ^ 87 * r.Q ^ 280 * r.d ^ 10) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at heh2; linarith
    have hQd : (1 : ℝ) ≤ r.Q ^ 160 * r.d := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ1) hd
    rw [le_div_iff₀ (by positivity)]
    have e : r.d ^ 9 * r.Q ^ 120 * r.eh * 2 ^ 87 * (r.Q ^ 160 * r.d) = r.eh * (2 ^ 87 * r.Q ^ 280 * r.d ^ 10) := by
      ring
    have h0 : 0 ≤ r.d ^ 9 * r.Q ^ 120 * r.eh * 2 ^ 87 := by positivity
    nlinarith
  -- `val ≤ 1/(4513 d^4 Q^60) ≤ valR`
  have hX : 0 < r.d ^ 4 * r.Q ^ 60 := by positivity
  have hval : r.val * (r.d ^ 4 * r.Q ^ 60) ≤ 1 / 4513 := by
    have e : r.val * (r.d ^ 4 * r.Q ^ 60) ≤
        (2 * (12 * r.d ^ 7 * r.Q ^ 137 * r.tp) + 381 * r.d ^ 5 * r.Q ^ 60 * r.eh) * (r.d ^ 4 * r.Q ^ 60) := by
      simp only [Reg.val]; apply mul_le_mul_of_nonneg_right _ hX.le; linarith
    have e' : (2 * (12 * r.d ^ 7 * r.Q ^ 137 * r.tp) + 381 * r.d ^ 5 * r.Q ^ 60 * r.eh) * (r.d ^ 4 * r.Q ^ 60) =
        24 * (r.d ^ 11 * r.Q ^ 197 * r.tp) + 381 * (r.d ^ 9 * r.Q ^ 120 * r.eh) := by ring
    have : 24 * (1 / (2 : ℝ) ^ 160) + 381 * (1 / 2 ^ 87) ≤ 1 / 4513 := by norm_num
    linarith
  have hn2 : r.n ^ 2 ≤ r.Q ^ 20 / 1024 := by
    have h1 : (32 * r.n) ^ 2 ≤ (r.Q ^ 10) ^ 2 := pow_le_pow_left₀ (by positivity) hQn 2
    have e1 : (32 * r.n) ^ 2 = 1024 * r.n ^ 2 := by ring
    have e2 : (r.Q ^ 10) ^ 2 = r.Q ^ 20 := by ring
    rw [e1, e2] at h1
    linarith
  have hvalR : 1 / (4513 * (r.d ^ 4 * r.Q ^ 60)) ≤ r.valR := by
    simp only [Reg.valR, hde]
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
    have : 128 * r.n ^ 2 * r.R ^ 2 * r.d ≤ 128 * (r.Q ^ 20 / 1024) * (190 ^ 2 * r.d ^ 3) * r.d := by gcongr
    have e : r.Q ^ 40 * (128 * (r.Q ^ 20 / 1024) * (190 ^ 2 * r.d ^ 3) * r.d) = 4512.5 * (r.d ^ 4 * r.Q ^ 60) := by ring
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ r.Q ^ 40)
    linarith
  refine le_trans ?_ hvalR
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem p4 (h : r.OK) : r.Xb ≤ 1 / 16 ∧ r.reg ≤ 1 := by
  have hpos := pos h
  have hQbd := Q_bd h
  have hRbd := R_bd h
  have hPb_pib := Pb_pib h
  have hwr_we := wr_we h
  have hXb_Du := Xb_Du h
  have hinv_eps := inv_eps h
  have hd : 1 ≤ r.d := h.hd
  have hdpos : 0 < r.d := hpos.1
  have hnpos : 0 < r.n := hpos.2.1
  have hLehpos : 0 < r.Le := hpos.2.2.2.1
  have hepspos : 0 < r.eps := hpos.2.2.2.2.1
  have htp_pos : 0 < r.tp := hpos.2.2.2.2.2.2.1
  have hQpos : 0 < r.Q := by linarith [hQbd.1]
  have hQnonneg : 0 ≤ r.Q := by linarith
  have htp_nonneg : 0 ≤ r.tp := by linarith
  have hd_nonneg : 0 ≤ r.d := by linarith
  have heps_nonneg : 0 ≤ r.eps := by linarith
  have hR_nonneg : 0 ≤ r.R := by linarith [h.hR1]
  have hXb_nonneg : 0 ≤ r.Xb := hXb_Du.1
  -- Part 1: r.Xb ≤ 1/16
  have hXb_bound : r.Xb ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp := hXb_Du.2.1
  have htiny_4_72 : r.d ^ 4 * r.Q ^ 72 * r.tp ≤ (1 : ℝ) / (2 : ℝ) ^ 160 :=
    OK.tiny (r := r) h 4 72 (by norm_num) (by norm_num)
  have hXb_le_1 : r.Xb ≤ (1 : ℝ) / 16 := by
    have h1 : r.Xb ≤ 2 * (r.d ^ 4 * r.Q ^ 72 * r.tp) := by linarith
    have h2 : r.d ^ 4 * r.Q ^ 72 * r.tp ≤ (1 : ℝ) / (2 : ℝ) ^ 160 := htiny_4_72
    have h3 : r.Xb ≤ 2 * ((1 : ℝ) / (2 : ℝ) ^ 160) := by linarith
    have h4 : 2 * ((1 : ℝ) / (2 : ℝ) ^ 160) = (1 : ℝ) / (2 : ℝ) ^ 159 := by ring
    have h5 : (1 : ℝ) / (2 : ℝ) ^ 159 ≤ (1 : ℝ) / 16 := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · norm_num
      · calc
          (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
          _ ≤ (2 : ℝ) ^ 159 := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega : (4 : ℕ) ≤ 159)
    linarith
  -- Part 2: r.reg ≤ 1
  have hreg_le_1 : r.reg ≤ 1 := by
    -- Step 1: r.n / r.eps ≤ r.Q ^ 15
    have hn_div_eps_le : r.n / r.eps ≤ r.Q ^ 15 := by
      have hn_le : r.n ≤ r.Q ^ 10 / 32 := by linarith [hQbd.2.2.1]
      have hinv_le : 1 / r.eps ≤ r.Q ^ 5 / 72500 := hinv_eps
      have hprod : r.n * (1 / r.eps) ≤ (r.Q ^ 10 / 32) * (r.Q ^ 5 / 72500) :=
        mul_le_mul hn_le hinv_le (by positivity) (by positivity)
      have hQ15_nonneg : 0 ≤ r.Q ^ 15 := pow_nonneg hQnonneg 15
      have hfinal : (r.Q ^ 10 / 32) * (r.Q ^ 5 / 72500) ≤ r.Q ^ 15 := by
        calc
          (r.Q ^ 10 / 32) * (r.Q ^ 5 / 72500) = r.Q ^ 15 / ((32 : ℝ) * 72500) := by ring
          _ ≤ r.Q ^ 15 := div_le_self hQ15_nonneg (by norm_num : 1 ≤ (32 : ℝ) * 72500)
      calc
        r.n / r.eps = r.n * (1 / r.eps) := by ring
        _ ≤ (r.Q ^ 10 / 32) * (r.Q ^ 5 / 72500) := hprod
        _ ≤ r.Q ^ 15 := hfinal
    -- Step 2: bounds for (1+2R)*Xb
    have h_term1 : (1 + 2 * r.R) * r.Xb ≤ 381 * r.d ^ 2 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) := by
      have hR_le : r.R ≤ 190 * r.d ^ 2 := hRbd.1
      have hXb_le : r.Xb ≤ 2 * r.d ^ 4 * r.Q ^ 72 * r.tp := hXb_Du.2.1
      have h_one_plus_2R : 1 + 2 * r.R ≤ 381 * r.d ^ 2 := by
        have hd_sq_ge_one : 1 ≤ r.d ^ 2 := by
          calc
            (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
            _ ≤ r.d ^ 2 := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hd 2
        linarith
      have h_nonneg_Xb : 0 ≤ r.Xb := hXb_Du.1
      exact mul_le_mul h_one_plus_2R hXb_le h_nonneg_Xb (by positivity)
    -- Step 3: bound for 4 * R * pib * we
    have hpib_le_Q : r.pib ≤ r.Q := by
      have hpib_le : r.pib ≤ 101 / 100 * Real.sqrt r.Le := hPb_pib.2.2.2
      have h_sqrtLe_mul : 101 / 100 * Real.sqrt r.Le ≤ r.Q := by
        have hLe_le_Q_div_10 : r.Le ≤ r.Q / 10 := by linarith [hQbd.2.1]
        have h_sqrtLe_le : Real.sqrt r.Le ≤ Real.sqrt (r.Q / 10) :=
          Real.sqrt_le_sqrt hLe_le_Q_div_10
        have hQ_div_10_nonneg : 0 ≤ r.Q / 10 := by linarith
        have hQ_div_10_pos : 0 < r.Q / 10 := by linarith
        have hs_pos : 0 < Real.sqrt (r.Q / 10) := Real.sqrt_pos.mpr hQ_div_10_pos
        have hs_ge : 101/1000 ≤ Real.sqrt (r.Q / 10) := by
          have h_sq_lt : ((101 : ℝ) / 1000) ^ 2 < r.Q / 10 := by
            have hQ_ge_174670 : (174670 : ℝ) ≤ r.Q := by
              have hLe_ge : 17467 ≤ r.Le := h.hL1
              linarith
            have h_bound : ((101 : ℝ) / 1000) ^ 2 < (174670 : ℝ) / 10 := by norm_num
            linarith
          have h_lt : (101/1000 : ℝ) < Real.sqrt (r.Q / 10) :=
            ((Real.lt_sqrt (by norm_num : 0 ≤ (101 : ℝ) / 1000)).mpr h_sq_lt)
          exact h_lt.le
        have hineq : 101/100 * Real.sqrt (r.Q / 10) ≤ r.Q := by
          have h : 101/100 ≤ 10 * Real.sqrt (r.Q / 10) := by linarith
          calc
            101/100 * Real.sqrt (r.Q / 10) ≤ (10 * Real.sqrt (r.Q / 10)) * Real.sqrt (r.Q / 10) :=
              mul_le_mul_of_nonneg_right h hs_pos.le
            _ = 10 * ((Real.sqrt (r.Q / 10)) ^ 2) := by ring
            _ = 10 * (r.Q / 10) := by rw [Real.sq_sqrt hQ_div_10_nonneg]
            _ = r.Q := by ring
        calc
          101 / 100 * Real.sqrt r.Le ≤ 101 / 100 * Real.sqrt (r.Q / 10) :=
            mul_le_mul_of_nonneg_left h_sqrtLe_le (by norm_num : 0 ≤ (101 : ℝ) / 100)
          _ ≤ r.Q := hineq
      linarith
    -- Step 4: bound for we
    have hwe_le : r.we ≤ r.tp / 64 := hwr_we.2.2.2
    -- Step 5: combine
    have h_term2 : 4 * r.R * r.pib * r.we ≤ 12 * r.d ^ 2 * r.Q * r.tp := by
      have hR_le : r.R ≤ 190 * r.d ^ 2 := hRbd.1
      have hpib_le : r.pib ≤ r.Q := hpib_le_Q
      have hpib_nonneg : 0 ≤ r.pib := hPb_pib.2.2.1
      have hwe_nonneg : 0 ≤ r.we := hwr_we.2.2.1
      have h1 : 4 * r.R * r.pib * r.we ≤ 4 * (190 * r.d ^ 2) * r.Q * (r.tp / 64) := by
        have hR_le : r.R ≤ 190 * r.d ^ 2 := hRbd.1
        have hpib_le : r.pib ≤ r.Q := hpib_le_Q
        have hwe_le : r.we ≤ r.tp / 64 := hwr_we.2.2.2
        gcongr
      have h2 : 4 * (190 * r.d ^ 2) * r.Q * (r.tp / 64) ≤ 12 * r.d ^ 2 * r.Q * r.tp := by
        calc
          4 * (190 * r.d ^ 2) * r.Q * (r.tp / 64) = ((4 * 190 : ℝ) / 64) * (r.d ^ 2 * r.Q * r.tp) := by ring
          _ ≤ 12 * (r.d ^ 2 * r.Q * r.tp) := by
            gcongr
            norm_num
          _ = 12 * r.d ^ 2 * r.Q * r.tp := by ring
      linarith
    have h_sum : (1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we ≤
        381 * r.d ^ 2 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) + 12 * r.d ^ 2 * r.Q * r.tp := by
      linarith
    have h_sum_simp : 381 * r.d ^ 2 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) + 12 * r.d ^ 2 * r.Q * r.tp =
        762 * r.d ^ 6 * r.Q ^ 72 * r.tp + 12 * r.d ^ 2 * r.Q * r.tp := by ring
    have hd_sq_le_d6 : r.d ^ 2 ≤ r.d ^ 6 := by
      have hd4_ge_1 : 1 ≤ r.d ^ 4 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
          _ ≤ r.d ^ 4 := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hd 4
      calc
        r.d ^ 2 = r.d ^ 2 * 1 := by ring
        _ ≤ r.d ^ 2 * r.d ^ 4 := by gcongr
        _ = r.d ^ 6 := by ring
    have hQ_le_Q72 : r.Q ≤ r.Q ^ 72 := by
      have hQ_ge_1 : 1 ≤ r.Q := by linarith [hQbd.1]
      have hQ71_ge_1 : 1 ≤ r.Q ^ 71 := one_le_pow₀ hQ_ge_1 (n := 71)
      calc
        r.Q = r.Q * 1 := by ring
        _ ≤ r.Q * r.Q ^ 71 := by gcongr
        _ = r.Q ^ 72 := by ring
    have h_prod_tp : r.d ^ 2 * r.Q * r.tp ≤ r.d ^ 6 * r.Q ^ 72 * r.tp := by
      have h_prod : r.d ^ 2 * r.Q ≤ r.d ^ 6 * r.Q ^ 72 :=
        mul_le_mul hd_sq_le_d6 hQ_le_Q72 (by positivity) (by positivity)
      exact mul_le_mul h_prod (le_refl r.tp) (by positivity) (by positivity)
    have h_sum_simp2 : 762 * r.d ^ 6 * r.Q ^ 72 * r.tp + 12 * r.d ^ 2 * r.Q * r.tp ≤
        762 * r.d ^ 6 * r.Q ^ 72 * r.tp + 12 * r.d ^ 6 * r.Q ^ 72 * r.tp := by
      nlinarith
    have h_sum_simp3 : 762 * r.d ^ 6 * r.Q ^ 72 * r.tp + 12 * r.d ^ 6 * r.Q ^ 72 * r.tp =
        774 * r.d ^ 6 * r.Q ^ 72 * r.tp := by ring
    have h_sum_simp4 : 774 * r.d ^ 6 * r.Q ^ 72 * r.tp ≤ 2000 * r.d ^ 6 * r.Q ^ 72 * r.tp := by
      gcongr
      norm_num
    have h_bound_sum : (1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we ≤
        2000 * r.d ^ 6 * r.Q ^ 72 * r.tp := by
      linarith
    -- Now combine everything
    have h_reg_bound : r.reg ≤ r.Q ^ 15 * (2000 * r.d ^ 6 * r.Q ^ 72 * r.tp) := by
      rw [AdversarialBco.Bit.PieceA.Reg.reg]
      have h_nonneg_eps : 0 ≤ r.eps := by linarith
      have h_nonneg_n_div_eps : 0 ≤ r.n / r.eps := div_nonneg (by linarith) h_nonneg_eps
      have h_nonneg_sum : 0 ≤ (1 + 2 * r.R) * r.Xb + 4 * r.R * r.pib * r.we := by
        have h1 : 0 ≤ 1 + 2 * r.R := by linarith [h.hR1]
        have h2 : 0 ≤ 4 * r.R * r.pib * r.we := by
          have hR_nonneg : 0 ≤ r.R := by linarith [h.hR1]
          have hpib_nonneg : 0 ≤ r.pib := hPb_pib.2.2.1
          have hwe_nonneg : 0 ≤ r.we := hwr_we.2.2.1
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR_nonneg) hpib_nonneg) hwe_nonneg
        have h3 : 0 ≤ (1 + 2 * r.R) * r.Xb := mul_nonneg h1 hXb_nonneg
        linarith
      have h_nonneg_Q15 : 0 ≤ r.Q ^ 15 := pow_nonneg hQnonneg 15
      exact mul_le_mul hn_div_eps_le h_bound_sum h_nonneg_sum h_nonneg_Q15
    have h_reg_bound2 : r.Q ^ 15 * (2000 * r.d ^ 6 * r.Q ^ 72 * r.tp) =
        2000 * r.d ^ 6 * r.Q ^ 87 * r.tp := by ring
    have h_reg_bound3 : 2000 * r.d ^ 6 * r.Q ^ 87 * r.tp ≤ 2000 * ((1 : ℝ) / (2 : ℝ) ^ 160) := by
      have htiny_6_87 : r.d ^ 6 * r.Q ^ 87 * r.tp ≤ (1 : ℝ) / (2 : ℝ) ^ 160 :=
        OK.tiny (r := r) h 6 87 (by norm_num) (by norm_num)
      have h := mul_le_mul_of_nonneg_left htiny_6_87 (by norm_num : 0 ≤ (2000 : ℝ))
      simpa [mul_assoc] using h
    have h_final : 2000 * ((1 : ℝ) / (2 : ℝ) ^ 160) ≤ 1 := by
      have h_pow : (2000 : ℝ) ≤ (2 : ℝ) ^ 160 := by
        have h : (2 : ℝ) ^ 11 ≤ (2 : ℝ) ^ 160 :=
          pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega : (11 : ℕ) ≤ 160)
        have h2048 : (2000 : ℝ) ≤ (2 : ℝ) ^ 11 := by norm_num
        linarith
      have h_div : 2000 * ((1 : ℝ) / (2 : ℝ) ^ 160) = (2000 : ℝ) / (2 : ℝ) ^ 160 := by ring
      rw [h_div]
      refine (div_le_one ?_).mpr h_pow
      positivity
    linarith
  exact And.intro hXb_le_1 hreg_le_1

theorem guard (h : r.OK) : r.d * r.DP ≤ r.Lam ∧ r.Dw ≤ r.W0 ∧ 11 / 10 ^ 35 + r.Dc * (1 + r.Xi1 ^ 2) ≤ 1 / 2 := by
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num : (0 : ℝ) ≤ 1) h.hd
  have htp_nonneg : 0 ≤ r.tp := h.htp0.le
  have hQ_pos : 0 < r.Q := h.hQ0
  have hQ_nonneg : 0 ≤ r.Q := hQ_pos.le
  have hLam_eq : r.Lam = r.d * r.Q ^ 40 := by
    rw [Reg.Lam, h.hQ]
  have hW0_ge_one : 1 ≤ r.W0 := by
    have hW0_bd := W0_bd h
    have hR_le_W0 : r.R ≤ r.W0 := hW0_bd.1
    have h157_le_R : (157 : ℝ) ≤ r.R := h.hR1
    linarith
  have h_tiny_3_51 := tiny h 3 51 (by norm_num) (by norm_num)
  have h_tiny_4_77 := tiny h 4 77 (by norm_num) (by norm_num)
  have h_tiny_2_2 := tiny h 2 2 (by norm_num) (by norm_num)
  have hDc := Dc_le h
  have hDc_nonneg : 0 ≤ r.Dc := hDc.1
  have hDc_le : r.Dc ≤ 35 / 100 * r.cb * r.tp := hDc.2
  have hcb := cb_le h
  have hcb_nonneg : 0 ≤ r.cb := hcb.1
  have hcb_le : r.cb ≤ 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := hcb.2
  have hcb_le_one : r.cb ≤ 1 := by
    have hpos : 0 < r.d ^ 2 * r.Le ^ 7 := by
      have hd_pos : 0 < r.d := by linarith [h.hd]
      have hLe_pos : 0 < r.Le := by linarith [h.hL1]
      have hd_sq_pos : 0 < r.d ^ 2 := pow_pos hd_pos 2
      have hLe_pow_pos : 0 < r.Le ^ 7 := pow_pos hLe_pos 7
      exact mul_pos hd_sq_pos hLe_pow_pos
    have h_denom : 54 / 10 ^ 10 ≤ r.d ^ 2 * r.Le ^ 7 := by
      have h1 : (54 : ℝ) / 10 ^ 10 ≤ 1 := by norm_num
      have h2 : 1 ≤ r.d ^ 2 := by
        have : 1 ≤ r.d := h.hd
        nlinarith
      have h3 : 1 ≤ r.Le ^ 7 := by
        have hLe : (1 : ℝ) ≤ r.Le := by linarith [h.hL1]
        calc
          (1 : ℝ) = (1 : ℝ) ^ 7 := by norm_num
          _ ≤ r.Le ^ 7 := by gcongr
      nlinarith
    have h_div : 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) ≤ 1 :=
      (div_le_one hpos).mpr h_denom
    linarith
  have hXi1 := Xi1_le h
  have hXi_nonneg : 0 ≤ r.Xi := hXi1.1
  have hXi1_nonneg : 0 ≤ r.Xi1 := by
    unfold Xi1
    nlinarith
  have hXi1_le : r.Xi1 ≤ r.d * r.Q := hXi1.2.2
  refine ⟨?_, ?_, ?_⟩
  · -- r.d * r.DP ≤ r.Lam
    have hDP := DP_le h
    have hDP_nonneg : 0 ≤ r.DP := hDP.1
    have hDP_le : r.DP ≤ 3 * r.d ^ 3 * r.Q ^ 91 * r.tp := hDP.2
    have h_ineq : 3 * r.d ^ 3 * r.Q ^ 51 * r.tp ≤ 1 := by
      have : r.d ^ 3 * r.Q ^ 51 * r.tp ≤ 1 / 2 ^ 160 := h_tiny_3_51
      have h3 : (3 : ℝ) / 2 ^ 160 ≤ 1 := by norm_num
      linarith
    calc
      r.d * r.DP ≤ r.d * (3 * r.d ^ 3 * r.Q ^ 91 * r.tp) := by gcongr
      _ = 3 * r.d ^ 4 * r.Q ^ 91 * r.tp := by ring
      _ = (r.d * r.Q ^ 40) * (3 * r.d ^ 3 * r.Q ^ 51 * r.tp) := by ring
      _ ≤ (r.d * r.Q ^ 40) * 1 := by gcongr
      _ = r.d * r.Q ^ 40 := by ring
      _ = r.Lam := by rw [hLam_eq]
  · -- r.Dw ≤ r.W0
    have hDw := Dw_le h
    have hDw_nonneg : 0 ≤ r.Dw := hDw.2.1
    have hDw_le : r.Dw ≤ 3 * r.d ^ 4 * r.Q ^ 77 * r.tp := hDw.2.2
    have h_ineq : 3 * r.d ^ 4 * r.Q ^ 77 * r.tp ≤ 1 := by
      have : r.d ^ 4 * r.Q ^ 77 * r.tp ≤ 1 / 2 ^ 160 := h_tiny_4_77
      have h3 : (3 : ℝ) / 2 ^ 160 ≤ 1 := by norm_num
      linarith
    have hDw_le_one : r.Dw ≤ 1 := by linarith
    calc
      r.Dw ≤ 1 := hDw_le_one
      _ ≤ r.W0 := hW0_ge_one
  · -- 11 / 10 ^ 35 + r.Dc * (1 + r.Xi1 ^ 2) ≤ 1 / 2
    have hDc_tp_le : r.Dc ≤ r.tp := by
      calc
        r.Dc ≤ 35 / 100 * r.cb * r.tp := hDc_le
        _ ≤ 35 / 100 * 1 * r.tp := by gcongr
        _ = 35 / 100 * r.tp := by ring
        _ ≤ r.tp := by
          have : (35 : ℝ) / 100 ≤ 1 := by norm_num
          nlinarith
    have h_Xi1_sq_le : r.Xi1 ^ 2 ≤ (r.d * r.Q) ^ 2 := by
      have h_nonneg : 0 ≤ r.Xi1 := hXi1_nonneg
      have h_le : r.Xi1 ≤ r.d * r.Q := hXi1_le
      nlinarith
    have h_one_plus : 1 + r.Xi1 ^ 2 ≤ 2 * (r.d * r.Q) ^ 2 := by
      have h_sq_nonneg : 0 ≤ (r.d * r.Q) ^ 2 := by positivity
      have hQ1 : 1 ≤ r.Q := by
        by_contra! hQ_lt_one
        have hQ_nonneg : 0 ≤ r.Q := by linarith
        have hQ40_lt_one : r.Q ^ 40 < 1 :=
          pow_lt_one₀ hQ_nonneg hQ_lt_one (by norm_num : 40 ≠ 0)
        have hN700 : 2 ^ 700 < r.Ne := h.hN700
        rw [← h.hQ] at hN700
        have h2pos : (1 : ℝ) < (2 : ℝ) ^ 700 := by
          have h_nat : (1 : ℕ) < (2 : ℕ) ^ 700 := by norm_num
          exact_mod_cast h_nat
        have : (1 : ℝ) < 1 := by
          calc
            (1 : ℝ) < (2 : ℝ) ^ 700 := h2pos
            _ < r.Q ^ 40 := hN700
            _ < 1 := hQ40_lt_one
        exact lt_irrefl _ this
      have h_sq_ge_one : 1 ≤ (r.d * r.Q) ^ 2 := by
        have hd1 : 1 ≤ r.d := h.hd
        have hprod : 1 ≤ r.d * r.Q := by
          nlinarith
        nlinarith
      nlinarith
    have h_Dc_bound : r.Dc * (1 + r.Xi1 ^ 2) ≤ 2 * r.d ^ 2 * r.Q ^ 2 * r.tp := by
      calc
        r.Dc * (1 + r.Xi1 ^ 2) ≤ r.tp * (2 * (r.d * r.Q) ^ 2) := by
          apply mul_le_mul hDc_tp_le h_one_plus (by nlinarith) htp_nonneg
        _ = 2 * r.d ^ 2 * r.Q ^ 2 * r.tp := by ring
    have h_tp_bound : 2 * r.d ^ 2 * r.Q ^ 2 * r.tp ≤ 2 / 2 ^ 160 := by
      have : r.d ^ 2 * r.Q ^ 2 * r.tp ≤ 1 / 2 ^ 160 := h_tiny_2_2
      nlinarith
    have h_sum : 11 / 10 ^ 35 + r.Dc * (1 + r.Xi1 ^ 2) ≤ 11 / 10 ^ 35 + 2 / 2 ^ 160 := by
      nlinarith
    have h_final : 11 / 10 ^ 35 + 2 / 2 ^ 160 ≤ 1 / 2 := by
      norm_num
    linarith

theorem cb_dom (h : r.OK) : r.cb * (1 + r.Xi1 ^ 2) ≤ 1 / 10 ^ 30 := by
  have hcb := cb_le h
  have hxi := Xi_bd h
  have hcb_nonneg : 0 ≤ r.cb := hcb.1
  have hcb_le : r.cb ≤ 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := hcb.2
  have hxi_bound : 1 + r.Xi1 ^ 2 ≤ r.d * r.Le / 9 := hxi.2.1
  have hxi_nonneg : 0 ≤ 1 + r.Xi1 ^ 2 := by nlinarith
  have h_target_nonneg : 0 ≤ 54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7) := by
    have hdpos : 0 < r.d := by linarith [h.hd]
    have hLe_ge : 0 < r.Le := by linarith [h.hL1]
    positivity
  have hprod : r.cb * (1 + r.Xi1 ^ 2) ≤ (54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7)) * (r.d * r.Le / 9) := by
    apply mul_le_mul hcb_le hxi_bound hxi_nonneg h_target_nonneg
  have hsimp : (54 / 10 ^ 10 / (r.d ^ 2 * r.Le ^ 7)) * (r.d * r.Le / 9) = 6 / 10 ^ 10 / (r.d * r.Le ^ 6) := by
    field_simp
    ring
  rw [hsimp] at hprod
  have h_denom_pos : 0 < r.d * r.Le ^ 6 := by
    have hdpos : 0 < r.d := by linarith [h.hd]
    have hLe_ge : 0 < r.Le := by linarith [h.hL1]
    positivity
  have h_denom_bound : (17467 : ℝ) ^ 6 ≤ r.d * r.Le ^ 6 := by
    have hL_pow : (17467 : ℝ) ^ 6 ≤ r.Le ^ 6 :=
      pow_le_pow_left₀ (by norm_num : 0 ≤ (17467 : ℝ)) h.hL1 6
    have hd_ge_one : 1 ≤ r.d := h.hd
    have h_mul : r.Le ^ 6 ≤ r.d * r.Le ^ 6 := by
      calc
        r.Le ^ 6 = 1 * r.Le ^ 6 := by norm_num
        _ ≤ r.d * r.Le ^ 6 := mul_le_mul_of_nonneg_right hd_ge_one (by positivity)
    linarith
  have h_div1 : 6 / 10 ^ 10 / (r.d * r.Le ^ 6) ≤ 6 / 10 ^ 10 / ((17467 : ℝ) ^ 6) := by
    have ha_nonneg : (0 : ℝ) ≤ 6 / 10 ^ 10 := by norm_num
    have hc_pos : 0 < (17467 : ℝ) ^ 6 := by norm_num
    exact div_le_div_of_nonneg_left ha_nonneg hc_pos h_denom_bound
  have h_final : 6 / 10 ^ 10 / ((17467 : ℝ) ^ 6) ≤ 1 / 10 ^ 30 := by
    field_simp
    norm_num
  linarith

theorem budget (h : r.OK) : r.n * (r.dbits + r.n * r.kap0) ≤ 1 / 4 ∧ 0 ≤ r.kap0 := by
  obtain ⟨hd0, hn0, hN0, hL0, he0, hde0, htp0, heh0⟩ := h.pos
  obtain ⟨hQ17, hQL, hQn, -, -, -⟩ := h.Q_bd
  obtain ⟨hXb0, hXb, -, -⟩ := h.Xb_Du
  obtain ⟨-, -, hpib0, hpib⟩ := h.Pb_pib
  obtain ⟨hRd, -⟩ := h.R_bd
  have hie := h.inv_eps
  have hR1 := h.hR1
  have hd := h.hd
  have hQ1 : (1 : ℝ) ≤ r.Q := le_trans (by norm_num) hQ17
  have hQ5 : (2 : ℝ) ^ 85 ≤ r.Q ^ 5 := by
    calc (2 : ℝ) ^ 85 = (2 ^ 17) ^ 5 := by rw [← pow_mul]
      _ ≤ r.Q ^ 5 := pow_le_pow_left₀ (by norm_num) hQ17 5
  -- the factors
  have hLe1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hL1
  have hsL : Real.sqrt r.Le ≤ r.Le := by
    have : Real.sqrt r.Le ≤ Real.sqrt (r.Le ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hpibQ : r.pib ≤ r.Q := by linarith
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
          gcongr
      _ ≤ 50 * r.d ^ 2 * r.Q ^ 6 * r.tp := by
          have : (0 : ℝ) ≤ r.d ^ 2 * r.Q ^ 6 * r.tp := by positivity
          nlinarith
  have hmpar0 : 0 ≤ r.mpar := by
    simp only [Reg.mpar]; have : 0 ≤ r.R + 10 := by linarith
    positivity
  have hX : (2 + 16 / r.eps) * r.Xb ≤ r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) :=
    mul_le_mul h16 hXb hXb0 (by positivity)
  have hk0 : 0 ≤ r.kap0 := by simp only [Reg.kap0]; positivity
  have hd24 : r.d ^ 2 * r.Q ^ 6 ≤ r.d ^ 4 * r.Q ^ 77 :=
    mul_le_mul (pow_le_pow_right₀ hd (by norm_num)) (pow_le_pow_right₀ hQ1 (by norm_num)) (by positivity)
      (by positivity)
  have hkap : r.kap0 ≤ 70 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by
    simp only [Reg.kap0]
    have e : r.Q ^ 5 * (2 * r.d ^ 4 * r.Q ^ 72 * r.tp) = 2 * (r.d ^ 4 * r.Q ^ 77 * r.tp) := by ring
    have e2 : 50 * r.d ^ 2 * r.Q ^ 6 * r.tp = 50 * (r.d ^ 2 * r.Q ^ 6 * r.tp) := by ring
    have : r.d ^ 2 * r.Q ^ 6 * r.tp ≤ r.d ^ 4 * r.Q ^ 77 * r.tp := mul_le_mul_of_nonneg_right hd24 htp0.le
    nlinarith
  refine ⟨?_, hk0⟩
  have hn : r.n ≤ r.Q ^ 10 := by
    have : (0 : ℝ) ≤ r.Q ^ 10 := by positivity
    linarith
  have hn2 : r.n * r.n ≤ r.Q ^ 20 := by
    calc r.n * r.n ≤ r.Q ^ 10 * r.Q ^ 10 := mul_le_mul hn hn hn0.le (by positivity)
      _ = r.Q ^ 20 := by ring
  have t := h.tiny 4 97 (by norm_num) (by norm_num)
  have hQ97 : r.Q ^ 10 * r.tp ≤ r.d ^ 4 * r.Q ^ 97 * r.tp := by
    have : r.Q ^ 10 ≤ r.d ^ 4 * r.Q ^ 97 :=
      le_trans (pow_le_pow_right₀ hQ1 (by norm_num)) (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hd))
    exact mul_le_mul_of_nonneg_right this htp0.le
  simp only [Reg.dbits]
  have e : r.n * (r.tp / 4 + r.n * r.kap0) = r.n * r.tp / 4 + (r.n * r.n) * r.kap0 := by ring
  rw [e]
  have a1 : r.n * r.tp / 4 ≤ r.Q ^ 10 * r.tp / 4 := by gcongr
  have a2 : (r.n * r.n) * r.kap0 ≤ r.Q ^ 20 * (70 * (r.d ^ 4 * r.Q ^ 77 * r.tp)) :=
    mul_le_mul hn2 hkap hk0 (by positivity)
  have e3 : r.Q ^ 20 * (70 * (r.d ^ 4 * r.Q ^ 77 * r.tp)) = 70 * (r.d ^ 4 * r.Q ^ 97 * r.tp) := by ring
  have : (71 : ℝ) / 2 ^ 160 ≤ 1 / 4 := by norm_num
  nlinarith

end AdversarialBco.Bit.PieceA.Reg.OK
