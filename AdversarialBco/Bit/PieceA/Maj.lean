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

end AdversarialBco.Bit.PieceA.Reg.OK
