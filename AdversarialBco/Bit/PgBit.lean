/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The parameter lemma of Procedure PG-N-bit, the projected-gradient rounds in the bit model

The integer parameters: (a) `pg_par_lam_a`; (b) `pg_par_b`, `pg_par_b2`; (c) `pg_par_c`; (d) `pg_par_d4`, `pg_par_d5`
(the cases `s = 4`, `s = 5`), `pg_par_d_big` (the case `s ≥ 6`, through `2^H ≤ (2d + 2)^6` in naturals) and `pg_par_d`
(the bound for the least `s`); `pg_par_exists` (a length `s ≥ 4` meeting the size condition exists for every `d`).

Each lemma sits in a namespace `AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at
`AdversarialBco.Bit.<name>`.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit.Aux_pg_par_lam_a


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_lam_a (s : ℕ) :
    2 * ((5 * s ^ 2 / 7 : ℕ) : ℝ) * Real.log 2 ≤ (s : ℝ) ^ 2 := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have hlog_lt : Real.log 2 < 7/10 := by
    have h := Real.log_two_lt_d9
    linarith
  have hdiv : ((5 * s ^ 2 / 7 : ℕ) : ℝ) ≤ (5 * (s : ℝ) ^ 2 / 7) := by
    calc
      ((5 * s ^ 2 / 7 : ℕ) : ℝ) ≤ ((5 * s ^ 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) :=
        Nat.cast_div_le (α := ℝ) (m := 5 * s ^ 2) (n := 7)
      _ = 5 * (s : ℝ) ^ 2 / 7 := by simp
  calc
    2 * ((5 * s ^ 2 / 7 : ℕ) : ℝ) * Real.log 2 ≤ 2 * ((5 * (s : ℝ) ^ 2 / 7)) * Real.log 2 := by
      nlinarith
    _ ≤ 2 * ((5 * (s : ℝ) ^ 2 / 7)) * (7/10) := by
      nlinarith
    _ = (s : ℝ) ^ 2 := by
      ring

end AdversarialBco.Bit.Aux_pg_par_lam_a

namespace AdversarialBco.Bit.Aux_pg_par_b


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_b (d Lh ρ : ℝ) (hd : 0 ≤ d) (hLh : 0 ≤ Lh) (hρ : 0 ≤ ρ)
    (hC : 2086812 * d ^ 2 * Lh ≤ 125 * ρ ^ 2) :
    3 * (364 / 10) * d * Real.sqrt (2 * Lh * Real.log 2) ≤ ρ := by
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog_lt : Real.log 2 < 7/10 := by
    have h := Real.log_two_lt_d9
    linarith
  have h_nonneg_arg : 0 ≤ 2 * Lh * Real.log 2 := by
    nlinarith
  have h_sq : (3 * (364 / 10) * d * Real.sqrt (2 * Lh * Real.log 2)) ^ 2 ≤ ρ ^ 2 := by
    calc
      (3 * (364 / 10) * d * Real.sqrt (2 * Lh * Real.log 2)) ^ 2
          = ((3 * (364 / 10)) ^ 2) * (d ^ 2) * ((Real.sqrt (2 * Lh * Real.log 2)) ^ 2) := by ring
      _ = ((3 * (364 / 10)) ^ 2) * (d ^ 2) * (2 * Lh * Real.log 2) := by
        rw [Real.sq_sqrt h_nonneg_arg]
      _ ≤ ((3 * (364 / 10)) ^ 2) * (d ^ 2) * (2 * Lh * (7/10)) := by
        have hA : 0 ≤ ((3 * (364 / 10)) ^ 2) * (d ^ 2) := by positivity
        have hXY : 2 * Lh * Real.log 2 ≤ 2 * Lh * (7/10) := by
          gcongr
        exact mul_le_mul_of_nonneg_left hXY hA
      _ = (2086812 / 125) * (d ^ 2) * Lh := by ring
      _ ≤ ρ ^ 2 := by
        nlinarith
  exact le_of_sq_le_sq h_sq hρ

end AdversarialBco.Bit.Aux_pg_par_b

namespace AdversarialBco.Bit.Aux_pg_par_b2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_b2 (d lam ρ : ℝ) (hd : 1 ≤ d) (hlam : 1 ≤ lam)
    (h : 3 * (364 / 10) * d * lam ≤ ρ) : 2 * Real.sqrt d ≤ ρ := by
  have hd_nonneg : 0 ≤ d := by linarith
  have h_sqrt_le : Real.sqrt d ≤ d := by
    have hd_sq_ge_d : d ≤ d ^ 2 := by
      nlinarith
    calc
      Real.sqrt d ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt hd_sq_ge_d
      _ = d := Real.sqrt_sq hd_nonneg
  nlinarith

end AdversarialBco.Bit.Aux_pg_par_b2

namespace AdversarialBco.Bit.Aux_pg_par_c


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_c (s : ℕ) (hs : 4 ≤ s) :
    1 ≤ 5 * s ^ 2 / 7 ∧ 5 * s ^ 2 / 7 < (50 * s ^ 2 + 68) / 69 := by
  have hs_sq : 16 ≤ s ^ 2 := by
    have hsq : (4:ℕ)^2 ≤ s^2 := Nat.pow_le_pow_left hs 2
    omega
  have h5s2 : 7 ≤ 5 * s ^ 2 := by
    nlinarith
  have h1 : 1 ≤ 5 * s ^ 2 / 7 := by
    have hpos := Nat.div_pos h5s2 (by norm_num : 0 < 7)
    omega
  have h2 : 5 * s ^ 2 / 7 < (50 * s ^ 2 + 68) / 69 := by
    set q1 := 5 * s ^ 2 / 7
    set q2 := (50 * s ^ 2 + 68) / 69
    have hq1 : 7 * q1 ≤ 5 * s ^ 2 := Nat.mul_div_le (5 * s ^ 2) 7
    have hq2 : 50 * s ^ 2 ≤ 69 * q2 := by
      have h_eq := Nat.div_add_mod (50 * s ^ 2 + 68) 69
      have h_mod_lt : (50 * s ^ 2 + 68) % 69 < 69 :=
        Nat.mod_lt (50 * s ^ 2 + 68) (by norm_num : 0 < 69)
      omega
    by_contra! hge
    have hq2_le_q1 : q2 ≤ q1 := by omega
    have h_mul : 69 * q2 ≤ 69 * q1 := Nat.mul_le_mul_left 69 hq2_le_q1
    have hchain1 : 350 * s ^ 2 ≤ 483 * q2 := by
      calc
        350 * s ^ 2 = 7 * (50 * s ^ 2) := by ring
        _ ≤ 7 * (69 * q2) := Nat.mul_le_mul_left 7 hq2
        _ = 483 * q2 := by ring
    have hchain2 : 483 * q2 ≤ 483 * q1 := by
      calc
        483 * q2 = 7 * (69 * q2) := by ring
        _ ≤ 7 * (69 * q1) := Nat.mul_le_mul_left 7 h_mul
        _ = 483 * q1 := by ring
    have hchain3 : 483 * q1 ≤ 345 * s ^ 2 := by
      calc
        483 * q1 = 69 * (7 * q1) := by ring
        _ ≤ 69 * (5 * s ^ 2) := Nat.mul_le_mul_left 69 hq1
        _ = 345 * s ^ 2 := by ring
    have hfinal : 350 * s ^ 2 ≤ 345 * s ^ 2 := by
      omega
    have h_contra : 5 * s ^ 2 ≤ 0 := by
      omega
    nlinarith
  exact And.intro h1 h2

end AdversarialBco.Bit.Aux_pg_par_c

namespace AdversarialBco.Bit.Aux_pg_par_d4


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_d4 (d : ℝ) (hd : 1 ≤ d) :
    (364 / 10 : ℝ) ^ 2 * (2 * 12 * Real.log 2) ≤ 134 ^ 2 * Real.log (2 * d + 2) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2nonneg : 0 ≤ Real.log 2 := le_of_lt hlog2pos
  have hd' : (4 : ℝ) ≤ 2 * d + 2 := by linarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow, Nat.cast_ofNat]
  have hlog_le : Real.log (4 : ℝ) ≤ Real.log (2 * d + 2) :=
    Real.log_le_log (by norm_num : 0 < (4 : ℝ)) hd'
  have h_main : (364 / 10 : ℝ) ^ 2 * (2 * 12 * Real.log 2) ≤ 134 ^ 2 * (2 * Real.log 2) := by
    have h_inner : (364 / 10 : ℝ) ^ 2 * (2 * 12) ≤ 134 ^ 2 * (2 : ℝ) := by norm_num
    calc
      (364 / 10 : ℝ) ^ 2 * (2 * 12 * Real.log 2) = ((364 / 10 : ℝ) ^ 2 * (2 * 12)) * Real.log 2 := by ring
      _ ≤ (134 ^ 2 * (2 : ℝ)) * Real.log 2 := by
        apply mul_le_mul_of_nonneg_right h_inner hlog2nonneg
      _ = 134 ^ 2 * (2 * Real.log 2) := by ring
  calc
    (364 / 10 : ℝ) ^ 2 * (2 * 12 * Real.log 2) ≤ 134 ^ 2 * (2 * Real.log 2) := h_main
    _ = 134 ^ 2 * Real.log (4 : ℝ) := by rw [hlog4]
    _ ≤ 134 ^ 2 * Real.log (2 * d + 2) := by
      apply mul_le_mul_of_nonneg_left hlog_le (by norm_num : 0 ≤ (134 : ℝ) ^ 2)

end AdversarialBco.Bit.Aux_pg_par_d4

namespace AdversarialBco.Bit.Aux_pg_par_d5


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_d5 (d : ℕ) (hd : 1 ≤ d)
    (hC4 : ¬ (2086812 * d ^ 2 * 12 ≤ 125 * (2 ^ 11 - 1) ^ 2)) :
    (364 / 10 : ℝ) ^ 2 * (2 * 19 * Real.log 2) ≤ 134 ^ 2 * Real.log (2 * (d : ℝ) + 2) := by
  -- From hC4, deduce d ≥ 5
  have hd5 : 5 ≤ d := by
    by_contra! h
    -- h : d < 5, so d ≤ 4
    have hd_le_4 : d ≤ 4 := by omega
    have hsq : d ^ 2 ≤ 16 := Nat.pow_le_pow_left hd_le_4 2
    have h1 : 2086812 * d ^ 2 ≤ 2086812 * 16 := Nat.mul_le_mul_left 2086812 hsq
    have h2 : 2086812 * 16 * 12 < 125 * ((2 : ℕ) ^ 11 - 1) ^ 2 := by norm_num
    have h3 : 2086812 * d ^ 2 * 12 ≤ 2086812 * 16 * 12 :=
      Nat.mul_le_mul h1 (by rfl)
    have hcalc : 2086812 * d ^ 2 * 12 ≤ 125 * ((2 : ℕ) ^ 11 - 1) ^ 2 :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt h3 h2)
    exact hC4 hcalc
  -- Cast to ℝ
  have hd_real : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd5
  have h_two_d_plus_two : (12 : ℝ) ≤ 2 * (d : ℝ) + 2 := by
    nlinarith
  have h_log_mono : Real.log (12 : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) :=
    Real.log_le_log (by norm_num) h_two_d_plus_two
  have h_log2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_log12_ge_3log2 : (3 : ℝ) * Real.log (2 : ℝ) ≤ Real.log (12 : ℝ) := by
    calc
      (3 : ℝ) * Real.log (2 : ℝ) = Real.log ((2 : ℝ) ^ (3 : ℕ)) := by
        rw [Real.log_pow, Nat.cast_ofNat]
      _ = Real.log (8 : ℝ) := by norm_num
      _ ≤ Real.log (12 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
  have h_num : ((364 : ℝ) / 10) ^ 2 * (2 * 19) ≤ (134 : ℝ) ^ 2 * (3 : ℝ) := by
    nlinarith
  calc
    ((364 : ℝ) / 10) ^ 2 * (2 * 19 * Real.log 2) = (((364 : ℝ) / 10) ^ 2 * (2 * 19)) * Real.log 2 := by ring
    _ ≤ (((364 : ℝ) / 10) ^ 2 * (2 * 19)) * Real.log 2 := by rfl
    _ ≤ ((134 : ℝ) ^ 2 * (3 : ℝ)) * Real.log 2 := by
      nlinarith
    _ = (134 : ℝ) ^ 2 * ((3 : ℝ) * Real.log 2) := by ring
    _ ≤ (134 : ℝ) ^ 2 * Real.log (12 : ℝ) := by
      nlinarith
    _ ≤ (134 : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2) := by
      nlinarith

end AdversarialBco.Bit.Aux_pg_par_d5

namespace AdversarialBco.Bit.Aux_pg_par_d_big


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pdb_sq_le_two_pow (s : ℕ) (hs : 4 ≤ s) : s ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [h2]
    nlinarith

theorem _root_.AdversarialBco.Bit.pdb_exp (s : ℕ) (hs : 6 ≤ s) :
    (50 * s ^ 2 + 68) / 69 + 43 + 3 * s ≤ 6 * (5 * (s - 1) ^ 2 / 7) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 6 := ⟨s - 6, by omega⟩
  have h1 : (t + 6 - 1) = t + 5 := by omega
  rw [h1]
  have hA := Nat.div_mul_le_self (50 * (t + 6) ^ 2 + 68) 69
  have hB := Nat.lt_div_mul_add (a := 5 * (t + 5) ^ 2) (b := 7) (by norm_num)
  nlinarith

theorem _root_.AdversarialBco.Bit.pdb_nat (s d : ℕ) (hs : 6 ≤ s)
    (hC : ¬ (2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * (s - 1) ^ 2 / 7) - 1) ^ 2)) :
    2 ^ ((50 * s ^ 2 + 68) / 69) ≤ (2 * d + 2) ^ 6 := by
  set H := (50 * s ^ 2 + 68) / 69 with hH
  set H' := (50 * (s - 1) ^ 2 + 68) / 69 with hH'
  set L' := 5 * (s - 1) ^ 2 / 7 with hL'
  have hC' : 125 * (2 ^ L' - 1) ^ 2 < 2086812 * d ^ 2 * H' := by omega
  have hL1 : 1 ≤ L' := by
    have : 25 ≤ (s - 1) ^ 2 := by
      have : 5 ≤ s - 1 := by omega
      nlinarith
    omega
  have hH's : H' ≤ s ^ 2 := by
    have := Nat.div_mul_le_self (50 * (s - 1) ^ 2 + 68) 69
    have : (s - 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (Nat.sub_le s 1) 2
    have h6 : 36 ≤ s ^ 2 := by nlinarith
    omega
  have hH'pos : 0 < H' := by
    have : 25 ≤ (s - 1) ^ 2 := by
      have : 5 ≤ s - 1 := by omega
      nlinarith
    omega
  have hexp := AdversarialBco.Bit.pdb_exp s hs
  have hs6 : s ^ 6 ≤ 2 ^ (3 * s) := by
    have := AdversarialBco.Bit.pdb_sq_le_two_pow s (by omega)
    calc s ^ 6 = (s ^ 2) ^ 3 := by ring
      _ ≤ (2 ^ s) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 2 ^ (3 * s) := by ring
  -- `2^{L'-1} ≤ 2^{L'} - 1`
  have hpow : 2 ^ (L' - 1) ≤ 2 ^ L' - 1 := by
    have : 2 ^ L' = 2 * 2 ^ (L' - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (L' - 1) := Nat.one_le_two_pow
    omega
  -- the main chain
  have key : 2 ^ H * (2086812 * H') ^ 3 ≤ 125 ^ 3 * 2 ^ (6 * L') := by
    calc 2 ^ H * (2086812 * H') ^ 3 ≤ 2 ^ H * (2086812 ^ 3 * s ^ 6) := by
          apply Nat.mul_le_mul_left
          rw [mul_pow]
          apply Nat.mul_le_mul_left
          calc H' ^ 3 ≤ (s ^ 2) ^ 3 := Nat.pow_le_pow_left hH's 3
            _ = s ^ 6 := by ring
      _ ≤ 2 ^ H * (2 ^ 63 * 2 ^ (3 * s)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (by norm_num) hs6
      _ = 2 ^ (H + 63 + 3 * s) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (20 + 6 * L') := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 20 * 2 ^ (6 * L') := by rw [pow_add]
      _ ≤ 125 ^ 3 * 2 ^ (6 * L') := Nat.mul_le_mul_right _ (by norm_num)
  have h6L : 2 ^ (6 * L') = 64 * (2 ^ (L' - 1)) ^ 6 := by
    rw [← pow_mul]
    have : 6 * L' = 6 + (L' - 1) * 6 := by omega
    rw [this, pow_add]; norm_num
  have hcube : (125 * (2 ^ L' - 1) ^ 2) ^ 3 < (2086812 * d ^ 2 * H') ^ 3 :=
    Nat.pow_lt_pow_left hC' (by norm_num)
  have hlow : 125 ^ 3 * 2 ^ (6 * L') ≤ 64 * (125 * (2 ^ L' - 1) ^ 2) ^ 3 := by
    rw [h6L]
    have : (2 ^ (L' - 1)) ^ 6 ≤ (2 ^ L' - 1) ^ 6 := Nat.pow_le_pow_left hpow 6
    calc 125 ^ 3 * (64 * (2 ^ (L' - 1)) ^ 6) = 64 * 125 ^ 3 * (2 ^ (L' - 1)) ^ 6 := by ring
      _ ≤ 64 * 125 ^ 3 * (2 ^ L' - 1) ^ 6 := Nat.mul_le_mul_left _ this
      _ = 64 * (125 * (2 ^ L' - 1) ^ 2) ^ 3 := by ring
  have hmain : 2 ^ H * (2086812 * H') ^ 3 < 64 * d ^ 6 * (2086812 * H') ^ 3 := by
    calc 2 ^ H * (2086812 * H') ^ 3 ≤ 64 * (125 * (2 ^ L' - 1) ^ 2) ^ 3 := key.trans hlow
      _ < 64 * (2086812 * d ^ 2 * H') ^ 3 := by omega
      _ = 64 * d ^ 6 * (2086812 * H') ^ 3 := by ring
  have hpos : 0 < (2086812 * H') ^ 3 := by positivity
  have h1 : 2 ^ H < 64 * d ^ 6 := Nat.lt_of_mul_lt_mul_right hmain
  calc 2 ^ H ≤ 64 * d ^ 6 := h1.le
    _ = (2 * d) ^ 6 := by ring
    _ ≤ (2 * d + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6

theorem _root_.AdversarialBco.Bit.pg_par_d_big (s d : ℕ) (hs : 6 ≤ s) (hd : 1 ≤ d)
    (hC : ¬ (2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * (s - 1) ^ 2 / 7) - 1) ^ 2)) :
    (364 / 10 : ℝ) ^ 2 * (2 * (((50 * s ^ 2 + 68) / 69 : ℕ) : ℝ) * Real.log 2) ≤
      134 ^ 2 * Real.log (2 * (d : ℝ) + 2) := by
  have hN := AdversarialBco.Bit.pdb_nat s d hs hC
  set H := (50 * s ^ 2 + 68) / 69
  have hR : ((2 : ℝ) ^ H) ≤ (2 * (d : ℝ) + 2) ^ 6 := by exact_mod_cast hN
  have hlog : (H : ℝ) * Real.log 2 ≤ 6 * Real.log (2 * (d : ℝ) + 2) := by
    have := Real.log_le_log (by positivity) hR
    rwa [Real.log_pow, Real.log_pow] at this
  have hl0 : 0 ≤ Real.log (2 * (d : ℝ) + 2) := Real.log_nonneg (by have : (0 : ℝ) ≤ d := d.cast_nonneg; linarith)
  nlinarith

end AdversarialBco.Bit.Aux_pg_par_d_big

namespace AdversarialBco.Bit.Aux_pg_par_d


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_d (s d : ℕ) (hs : 4 ≤ s) (hd : 1 ≤ d)
    (hmin : ∀ s', 4 ≤ s' → s' < s →
      ¬ (2086812 * d ^ 2 * ((50 * s' ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * s' ^ 2 / 7) - 1) ^ 2)) :
    (364 / 10 : ℝ) ^ 2 * (2 * (((50 * s ^ 2 + 68) / 69 : ℕ) : ℝ) * Real.log 2) ≤
      134 ^ 2 * Real.log (2 * (d : ℝ) + 2) := by
  by_cases hs4 : s = 4
  · -- s = 4
    subst hs4
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hH : (((50 * 4 ^ 2 + 68) / 69 : ℕ) : ℝ) = (12 : ℝ) := by norm_num
    simpa [hH] using pg_par_d4 (d : ℝ) hd'
  · -- s ≠ 4
    by_cases hs5 : s = 5
    · -- s = 5
      subst hs5
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hH : (((50 * 5 ^ 2 + 68) / 69 : ℕ) : ℝ) = (19 : ℝ) := by norm_num
      have hC4 : ¬ (2086812 * d ^ 2 * 12 ≤ 125 * (2 ^ 11 - 1) ^ 2) := by
        have h := hmin 4 (by omega) (by omega)
        -- h : ¬ (2086812 * d ^ 2 * ((50 * 4 ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * 4 ^ 2 / 7) - 1) ^ 2)
        -- norm_num simplifies the Nat expressions inside
        simpa [show ((50 * 4 ^ 2 + 68) / 69 : ℕ) = 12 by norm_num,
               show (5 * 4 ^ 2 / 7 : ℕ) = 11 by norm_num] using h
      simpa [hH] using pg_par_d5 d hd hC4
    · -- s ≥ 6
      have hs6 : 6 ≤ s := by omega
      have h_prev_ge4 : 4 ≤ s - 1 := by omega
      have h_prev_lt_s : s - 1 < s := by omega
      have hC : ¬ (2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * (s - 1) ^ 2 / 7) - 1) ^ 2) :=
        hmin (s - 1) h_prev_ge4 h_prev_lt_s
      exact pg_par_d_big s d hs6 hd hC

end AdversarialBco.Bit.Aux_pg_par_d

namespace AdversarialBco.Bit.Aux_pg_par_exists


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pg_par_exists (d : ℕ) :
    ∃ s : ℕ, 4 ≤ s ∧ 2086812 * d ^ 2 * ((50 * s ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * s ^ 2 / 7) - 1) ^ 2 := by
  refine ⟨7 * (d + 10), by omega, ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, x = d + 10 := ⟨_, rfl⟩
  rw [← hx]
  have hx1 : 10 ≤ x := by omega
  have h57 : 5 * (7 * x) ^ 2 / 7 = 35 * x ^ 2 := by
    rw [show 5 * (7 * x) ^ 2 = 7 * (35 * x ^ 2) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h57]
  have hdiv : (50 * (7 * x) ^ 2 + 68) / 69 ≤ 2518 * x ^ 2 := by
    calc (50 * (7 * x) ^ 2 + 68) / 69 ≤ 50 * (7 * x) ^ 2 + 68 := Nat.div_le_self _ _
      _ ≤ 2518 * x ^ 2 := by nlinarith
  have hdx : d ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hL : 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := by
    calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2086812 * x ^ 2 * (2518 * x ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hdx) hdiv
      _ = 5254592616 * x ^ 4 := by ring
      _ ≤ 2 ^ 33 * x ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have hx4 : x ^ 4 ≤ 2 ^ (4 * x) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
  have hk : 33 + 4 * x ≤ 35 * x ^ 2 := by nlinarith
  have hK : 4 ≤ 2 ^ (35 * x ^ 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hR : 2 ^ (35 * x ^ 2) ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := by
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ (35 * x ^ 2) = j + 1 := ⟨2 ^ (35 * x ^ 2) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    have hj3 : 3 ≤ j := by omega
    nlinarith
  calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := hL
    _ ≤ 2 ^ 33 * 2 ^ (4 * x) := Nat.mul_le_mul_left _ hx4
    _ = 2 ^ (33 + 4 * x) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) hk
    _ ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := hR

end AdversarialBco.Bit.Aux_pg_par_exists

namespace AdversarialBco.Bit.Aux_pg_gauss_mom6


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

set_option maxHeartbeats 400000

end AdversarialBco.Bit.Aux_pg_gauss_mom6

