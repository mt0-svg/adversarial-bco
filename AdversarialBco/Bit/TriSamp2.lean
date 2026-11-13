/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.TriSamp

@[expose] public section

/-!
# The position theorem, the laws of the draws, the coupling and the stage bodies

The leaves of the position theorem that rest on those of Bit/TriSamp.lean:

* the row (R): `tri_par_row` (the four terms of the row against `e_h(ρ_h)` at the parameters of dimension `d`, with
  the rational majorants of `G`, `β` and `log(1/δ')`), `tri_epsG_le` (the coupling error at `k_g` bits);
* the sampler: `gs_bad` (the bad event of one vector draw has probability at most `d 2^{-B/2}`), `gs_cpl` (the
  coupling of the objective between the sampler law and the standard Gaussian), `gsOmega_cells` (the law of the cells
  of a draw), `cells_V_law` (blocks of `B` fair coins are independent with the law of a cell), `tri_draws_law` (the
  draws read off the coin stream are independent with the sampler law), `tri_draw_facts` (bound, measurability and
  locality of a draw);
* measurability: `triU_meas2`, `tri_V_meas2`, `triIter_meas2` (jointly in a parameter);
* the stages: `tri_cube_rows` (the rows of `K ∩ triCube c s`), `tri_stage_body`, `tri_stage0_body` (the body of a
  stage in the position of the previous one, and of the first stage).

Each lemma sits in a namespace `AdversarialBco.Bit.Aux_<name>`
with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/

namespace AdversarialBco.Bit.Aux_tri_epsG_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

-- Helper lemma: k ≤ 2^k for all natural k
private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction' n with k ih
  · exact Nat.zero_le _
  · have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    have h_one_le : 1 ≤ 2 ^ k := by omega
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h_one_le _
      _ = 2 * 2 ^ k := by ring
      _ = 2 ^ (k + 1) := by ring

-- Helper lemma: sqrt(d*(d+1)/2) ≤ d+1 for d ≥ 1
private lemma sqrt_d_mul_d_add_one_div_two_le_d_add_one {d : ℕ} (hd : 1 ≤ d) :
    Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) ≤ (d : ℝ) + 1 := by
  have hd' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have h_sq : (d : ℝ) * ((d : ℝ) + 1) / 2 ≤ ((d : ℝ) + 1) ^ 2 := by
    nlinarith
  have h_nonneg : 0 ≤ (d : ℝ) * ((d : ℝ) + 1) / 2 := by nlinarith
  calc
    Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) ≤ Real.sqrt (((d : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = |(d : ℝ) + 1| := Real.sqrt_sq_eq_abs _
    _ = (d : ℝ) + 1 := abs_of_pos (by nlinarith)

-- Helper lemma: sqrt(d) ≤ d for d ≥ 1
private lemma sqrt_d_le_d {d : ℕ} (hd : 1 ≤ d) : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    nlinarith
  have h_nonneg : 0 ≤ (d : ℝ) := by nlinarith
  calc
    Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = |(d : ℝ)| := Real.sqrt_sq_eq_abs _
    _ = (d : ℝ) := abs_of_pos (by nlinarith)

-- Helper lemma: sqrt(2*d*4*k) ≤ 8*d*k for d ≥ 1, k ≥ 2
private lemma sqrt_two_d_mul_four_k_le_eight_d_mul_k {d k : ℕ} (hd : 1 ≤ d) (hk : 2 ≤ k) :
    Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) ≤ 8 * (d : ℝ) * (k : ℝ) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_sq : 2 * (d : ℝ) * (4 * (k : ℝ)) ≤ (8 * (d : ℝ) * (k : ℝ)) ^ 2 := by
    have hpos : 1 ≤ 8 * (d : ℝ) * (k : ℝ) := by nlinarith
    have h_sq_ineq : 8 * (d : ℝ) * (k : ℝ) ≤ (8 * (d : ℝ) * (k : ℝ)) ^ 2 := by
      nlinarith
    nlinarith
  calc
    Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) ≤ Real.sqrt ((8 * (d : ℝ) * (k : ℝ)) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = |8 * (d : ℝ) * (k : ℝ)| := Real.sqrt_sq_eq_abs _
    _ = 8 * (d : ℝ) * (k : ℝ) := abs_of_pos (by nlinarith)

-- Helper lemma: k * 2^(-2k) ≤ 2^(-k) for k ≥ 2
private lemma k_mul_two_pow_neg_two_k_le_two_pow_neg_k {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_two_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  -- Express 2^(-2k) as (2^(-k))^2
  have h_expr : (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) = ((2 : ℝ) ^ (-(k : ℝ))) ^ 2 := by
    have h_exp1 : -((4 * k : ℕ) : ℝ) / 2 = -(2 * (k : ℝ)) := by push_cast; ring
    have h_exp2 : -(2 * (k : ℝ)) = (-(k : ℝ)) * 2 := by ring
    calc
      (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) = (2 : ℝ) ^ (-(2 * (k : ℝ))) := by rw [h_exp1]
      _ = (2 : ℝ) ^ ((-(k : ℝ)) * 2) := by rw [h_exp2]
      _ = ((2 : ℝ) ^ (-(k : ℝ))) ^ 2 := by
        simpa using Real.rpow_mul h_two_nonneg (-(k : ℝ)) 2
  -- First show: k * 2^(-k) ≤ 1
  have h_kmul : (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 := by
    have hk_le_two_pow : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have h_nat : k ≤ 2 ^ k := nat_le_two_pow k
      exact_mod_cast h_nat
    calc
      (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
        gcongr
      _ = (2 : ℝ) ^ ((k : ℝ) + (-(k : ℝ))) := by rw [Real.rpow_add h_two_pos (k : ℝ) (-(k : ℝ))]
      _ = (2 : ℝ) ^ (0 : ℝ) := by simp
      _ = 1 := by rw [Real.rpow_zero (2 : ℝ)]
  have hq_pos : 0 < (2 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos h_two_pos _
  calc
    (k : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) = (k : ℝ) * (((2 : ℝ) ^ (-(k : ℝ))) ^ 2) := by rw [h_expr]
    _ = ((k : ℝ) * (2 : ℝ) ^ (-(k : ℝ))) * (2 : ℝ) ^ (-(k : ℝ)) := by ring
    _ ≤ 1 * (2 : ℝ) ^ (-(k : ℝ)) := by gcongr
    _ = (2 : ℝ) ^ (-(k : ℝ)) := by simp

-- Helper lemma: sqrt(2^(-2k)) = 2^(-k)
private lemma sqrt_two_pow_neg_two_k_eq_two_pow_neg_k {k : ℕ} :
    Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) = (2 : ℝ) ^ (-(k : ℝ)) := by
  have h_two_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  calc
    Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) = ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) ^ (1/2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    _ = (2 : ℝ) ^ ((-((4 * k : ℕ) : ℝ) / 2) * (1/2 : ℝ)) := by rw [Real.rpow_mul h_two_nonneg]
    _ = (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 4) := by ring
    _ = (2 : ℝ) ^ (-(k : ℝ)) := by push_cast; ring

-- Helper lemma: 8*k ≤ 4^k for k ≥ 2

-- Helper lemma: 4π*sqrt(k) ≤ 2*4^k for k ≥ 2
-- Helper lemma: 1 + 4π*sqrt(k) ≤ 2*4^k for k ≥ 2
private lemma one_add_four_pi_sqrt_k_le_two_mul_four_pow_k {k : ℕ} (hk : 2 ≤ k) :
    1 + 4 * Real.pi * Real.sqrt (k : ℝ) ≤ 2 * (4 : ℝ) ^ (k : ℝ) := by
  have h_sqrt_k_le_k : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    have h_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    calc
      Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = |(k : ℝ)| := Real.sqrt_sq_eq_abs _
      _ = (k : ℝ) := abs_of_pos (by nlinarith)
  have h_four_pi_k_add_one_le_two_mul_four_pow_k : ∀ (m : ℕ), 2 ≤ m → 1 + 4 * Real.pi * (m : ℝ) ≤ 2 * (4 : ℝ) ^ (m : ℝ) := by
    intro m hm
    refine Nat.le_induction ?_ (fun n hn h_ih => ?_) _ hm
    · -- base m=2: 1 + 8π ≤ 2*16 = 32
      have hπ : Real.pi < 4 := Real.pi_lt_four
      have hgoal : 1 + 4 * Real.pi * (2 : ℝ) ≤ 2 * (4 : ℝ) ^ (2 : ℝ) := by
        norm_num
        have hπ : Real.pi < 3.1416 := Real.pi_lt_d4
        nlinarith
      simpa using hgoal
    · -- inductive step: 1 + 4π*(n+1) ≤ 2*4^(n+1)
      have h_pow_ge_16 : (16 : ℝ) ≤ (4 : ℝ) ^ (n : ℝ) := by
        have h_pow_nat : (4 : ℕ) ^ 2 ≤ (4 : ℕ) ^ n := Nat.pow_le_pow_right (by norm_num) hn
        have h_cast : ((4 : ℕ) ^ 2 : ℝ) ≤ ((4 : ℕ) ^ n : ℝ) := by exact_mod_cast h_pow_nat
        calc
          (16 : ℝ) = ((4 : ℕ) ^ 2 : ℝ) := by norm_num
          _ ≤ ((4 : ℕ) ^ n : ℝ) := h_cast
          _ = (4 : ℝ) ^ (n : ℝ) := by simp [Real.rpow_natCast]
      calc
        1 + 4 * Real.pi * ((n + 1 : ℕ) : ℝ) = (1 + 4 * Real.pi * (n : ℝ)) + 4 * Real.pi := by push_cast; ring
        _ ≤ 2 * (4 : ℝ) ^ (n : ℝ) + 4 * Real.pi := by
          have h := add_le_add_right h_ih (4 * Real.pi)
          simpa [add_comm, add_left_comm, add_assoc] using h
        _ ≤ 2 * (4 : ℝ) ^ (n : ℝ) + 6 * (4 : ℝ) ^ (n : ℝ) := by
          have h : 4 * Real.pi ≤ 6 * (4 : ℝ) ^ (n : ℝ) := by
            have hπ : Real.pi < 4 := Real.pi_lt_four
            nlinarith
          nlinarith
        _ = 8 * (4 : ℝ) ^ (n : ℝ) := by ring
        _ = 2 * (4 * (4 : ℝ) ^ (n : ℝ)) := by ring
        _ = 2 * ((4 : ℝ) ^ (1 : ℝ) * (4 : ℝ) ^ (n : ℝ)) := by norm_num
        _ = 2 * (4 : ℝ) ^ ((1 : ℝ) + (n : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : 0 < (4 : ℝ)) (1 : ℝ) (n : ℝ)]
        _ = 2 * (4 : ℝ) ^ ((n : ℝ) + 1) := by ring
        _ = 2 * (4 : ℝ) ^ ((n + 1 : ℕ) : ℝ) := by simp
  have h := h_four_pi_k_add_one_le_two_mul_four_pow_k k hk
  calc
    1 + 4 * Real.pi * Real.sqrt (k : ℝ) ≤ 1 + 4 * Real.pi * (k : ℝ) := by gcongr
    _ ≤ 2 * (4 : ℝ) ^ (k : ℝ) := h

-- Helper lemma: gsEps(4k) ≤ 2^(-k) for k ≥ 2
private lemma gsEps_four_k_le_two_pow_neg_k {k : ℕ} (hk : 2 ≤ k) :
    gsEps (4 * k) ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_two_ge_one : (1 : ℝ) ≤ 2 := by norm_num
  -- Expand gsEps(4k) = 2^(-4k) + 2^(1-2k) + 2π*sqrt(4k)*2^(-4k)
  have h_eps_eq : gsEps (4 * k) =
      (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) + (2 : ℝ) ^ (1 - ((4 * k : ℕ) : ℝ) / 2) +
        2 * Real.pi * Real.sqrt ((4 * k : ℕ) : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) := by
    dsimp [gsEps]
    have h : (1 : ℝ) / ((2 : ℝ) ^ (4 * k : ℕ)) = (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) := by
      calc
        (1 : ℝ) / ((2 : ℝ) ^ (4 * k : ℕ)) = ((2 : ℝ) ^ (4 * k : ℕ))⁻¹ := by simp
        _ = ((2 : ℝ) ^ ((4 * k : ℕ) : ℝ))⁻¹ := by rw [← Real.rpow_natCast]
        _ = (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) := by
          rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) ((4 * k : ℕ) : ℝ)]
    rw [h]
    ring
  rw [h_eps_eq]
  -- Simplify sqrt(4k) = 2*sqrt(k)
  have h_sqrt_4k : Real.sqrt ((4 * k : ℕ) : ℝ) = 2 * Real.sqrt (k : ℝ) := by
    push_cast
    calc
      Real.sqrt (4 * (k : ℝ)) = Real.sqrt (4 : ℝ) * Real.sqrt (k : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (k : ℝ) := by norm_num
  -- Combined bound: 2^(-4k) + 2π*sqrt(4k)*2^(-4k) ≤ 2*2^(-2k)
  -- i.e., (1 + 4π*sqrt(k)) * 2^(-4k) ≤ 2*2^(-2k)
  have h_bound_combined : (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) +
      2 * Real.pi * Real.sqrt ((4 * k : ℕ) : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) ≤
      2 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by
    rw [h_sqrt_4k]
    -- LHS = 2^(-4k) + 4π*sqrt(k)*2^(-4k) = (1 + 4π*sqrt(k)) * 2^(-4k)
    -- RHS = 2 * 2^(-2k)
    -- Need: (1 + 4π*sqrt(k)) * 2^(-4k) ≤ 2 * 2^(-2k)
    -- Equivalent to: 1 + 4π*sqrt(k) ≤ 2 * 2^(2k) = 2 * 4^k
    have h_key : 1 + 4 * Real.pi * Real.sqrt (k : ℝ) ≤ 2 * (4 : ℝ) ^ (k : ℝ) :=
      one_add_four_pi_sqrt_k_le_two_mul_four_pow_k hk
    have h_two_pow_pos : 0 < (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos h_two_pos _
    calc
      (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) + 2 * Real.pi * (2 * Real.sqrt (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ))
          = ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ))) * (1 + 4 * Real.pi * Real.sqrt (k : ℝ)) := by ring
      _ ≤ ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ))) * (2 * (4 : ℝ) ^ (k : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) * (2 * (2 : ℝ) ^ (2 * (k : ℝ))) := by
        have h4_eq : (4 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ (2 * (k : ℝ)) := by
          calc
            (4 : ℝ) ^ (k : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (k : ℝ) := by norm_num
            _ = (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) := by rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (2 : ℝ) (k : ℝ)]
            _ = (2 : ℝ) ^ (2 * (k : ℝ)) := by ring
        rw [h4_eq]
      _ = 2 * ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) * (2 : ℝ) ^ (2 * (k : ℝ))) := by ring
      _ = 2 * ((2 : ℝ) ^ ((-((4 * k : ℕ) : ℝ)) + (2 * (k : ℝ)))) := by
        rw [Real.rpow_add h_two_pos (-((4 * k : ℕ) : ℝ)) (2 * (k : ℝ))]
      _ = 2 * ((2 : ℝ) ^ (-((2 * k : ℕ) : ℝ))) := by
        push_cast
        ring
  -- Bound 2: 2^(1-2k) = 2 * 2^(-2k)
  have h_bound2 : (2 : ℝ) ^ (1 - ((4 * k : ℕ) : ℝ) / 2) = 2 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by
    calc
      (2 : ℝ) ^ (1 - ((4 * k : ℕ) : ℝ) / 2) = (2 : ℝ) ^ (1 - (2 * (k : ℝ))) := by push_cast; ring
      _ = (2 : ℝ) ^ ((1 : ℝ) + (-(2 * (k : ℝ)))) := by ring
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(2 * (k : ℝ))) := by
        rw [Real.rpow_add h_two_pos (1 : ℝ) (-(2 * (k : ℝ)))]
      _ = 2 * (2 : ℝ) ^ (-(2 * (k : ℝ))) := by norm_num
      _ = 2 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by push_cast; ring
  -- Combine the bounds
  calc
    (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ)) + (2 : ℝ) ^ (1 - ((4 * k : ℕ) : ℝ) / 2) +
        2 * Real.pi * Real.sqrt ((4 * k : ℕ) : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ))
    ≤ 2 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) + 2 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by
      nlinarith
    _ = 4 * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by ring
    _ = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (-((2 * k : ℕ) : ℝ)) := by norm_num
    _ = (2 : ℝ) ^ ((2 : ℝ) + (-((2 * k : ℕ) : ℝ))) := by rw [Real.rpow_add h_two_pos (2 : ℝ) (-((2 * k : ℕ) : ℝ))]
    _ = (2 : ℝ) ^ (2 * (1 - (k : ℝ))) := by
      congr
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le h_two_ge_one ?_
      nlinarith

theorem _root_.AdversarialBco.Bit.tri_epsG_le (d k : ℕ) (hd : 1 ≤ d) (hk : 2 ≤ k) (b : ℝ) (hb : 0 ≤ b) :
    b * Real.sqrt (d * (d + 1) / 2) *
        (Real.sqrt d * gsEps (4 * k) + d * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * d * (4 * k : ℕ)) +
          d * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2))) ≤
      b * (d + 1) * d * (8 * d + 2) / 2 ^ k := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  -- Rewrite RHS as b * (d+1) * d * (8d+2) * 2^(-k)
  have h_rhs : b * (d + 1) * d * (8 * d + 2) / 2 ^ k = b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by
    push_cast
    have h_pow : (2 : ℝ) ^ (-(k : ℝ)) = ((2 ^ k : ℝ))⁻¹ := by
      simp [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) (k : ℝ), Real.rpow_natCast]
    calc
      b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) / (2 ^ k : ℝ)
          = b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) * ((2 ^ k : ℝ)⁻¹) := by ring
      _ = b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by rw [h_pow]
  -- Step 1: S ≤ d+1
  have hS : Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) ≤ (d : ℝ) + 1 :=
    sqrt_d_mul_d_add_one_div_two_le_d_add_one hd
  -- Step 2: T ≤ d*(8d+2)*2^(-k)
  have hT : Real.sqrt (d : ℝ) * gsEps (4 * k) +
      (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
      (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) ≤
      (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by
    -- Bounds for each term
    have h_sqrt_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := sqrt_d_le_d hd
    have h_eps : gsEps (4 * k) ≤ (2 : ℝ) ^ (-(k : ℝ)) := gsEps_four_k_le_two_pow_neg_k hk
    have h_sqrt_2dk : Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) ≤ 8 * (d : ℝ) * (k : ℝ) :=
      sqrt_two_d_mul_four_k_le_eight_d_mul_k hd hk
    have h_sqrt_rpow : Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) = (2 : ℝ) ^ (-(k : ℝ)) :=
      sqrt_two_pow_neg_two_k_eq_two_pow_neg_k
    have h_k_rpow : (k : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) ≤ (2 : ℝ) ^ (-(k : ℝ)) :=
      k_mul_two_pow_neg_two_k_le_two_pow_neg_k hk
    -- First term: sqrt(d) * gsEps(4k) ≤ d * 2^(-k)
    have h_term1 : Real.sqrt (d : ℝ) * gsEps (4 * k) ≤ (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
      have h_nonneg_gsEps : 0 ≤ gsEps (4 * k) := by
        dsimp [gsEps]
        positivity
      apply mul_le_mul h_sqrt_d h_eps h_nonneg_gsEps hd0
    -- Second term: d * 2^(-2k) * sqrt(2*d*4k) ≤ d * 2^(-2k) * 8*d*k
    have h_term2 : (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) ≤
        (d : ℝ) * (8 * (d : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) := by
      have h_nonneg_dp : 0 ≤ (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) := by
        positivity
      calc
        (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ)))
            ≤ (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * (8 * (d : ℝ) * (k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_sqrt_2dk h_nonneg_dp
        _ = (d : ℝ) * (8 * (d : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) := by ring
    -- Now: d * (8*d*k) * 2^(-2k) = 8*d^2*k*2^(-2k) ≤ 8*d^2*2^(-k)
    have h_term2_bound : (d : ℝ) * (8 * (d : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) ≤
        (d : ℝ) * (8 * (d : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) := by
      have h_nonneg_d8d : 0 ≤ (d : ℝ) * 8 * (d : ℝ) := by positivity
      calc
        (d : ℝ) * (8 * (d : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)
            = ((d : ℝ) * 8 * (d : ℝ)) * ((k : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) := by ring
        _ ≤ ((d : ℝ) * 8 * (d : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_k_rpow h_nonneg_d8d
        _ = (d : ℝ) * (8 * (d : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) := by ring
    -- Third term: d * sqrt(2^(-2k)) = d * 2^(-k)
    have h_term3 : (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) = (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
      rw [h_sqrt_rpow]
    -- Combine: T ≤ d*2^(-k) + 8*d^2*2^(-k) + d*2^(-k) = d*(8d+2)*2^(-k)
    calc
      Real.sqrt (d : ℝ) * gsEps (4 * k) +
          (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
          (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2))
      ≤ (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) +
          (d : ℝ) * (8 * (d : ℝ) * (k : ℝ)) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) +
          (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
        nlinarith
      _ ≤ (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) +
          (d : ℝ) * (8 * (d : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) +
          (d : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
        nlinarith
      _ = (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by ring
  -- Now combine: LHS = b * S * T ≤ b * (d+1) * d*(8d+2)*2^(-k) = RHS
  have h_nonneg_T : 0 ≤ Real.sqrt (d : ℝ) * gsEps (4 * k) +
      (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
      (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) := by
    have h1 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have h2 : 0 ≤ gsEps (4 * k) := by
      dsimp [gsEps]
      positivity
    have h3 : 0 ≤ (d : ℝ) := hd0
    have h4 : 0 ≤ (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) :=
      (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _).le
    have h5 : 0 ≤ Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) := Real.sqrt_nonneg _
    have h6 : 0 ≤ Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)) := Real.sqrt_nonneg _
    positivity
  have h_nonneg_bT : 0 ≤ b * (Real.sqrt (d : ℝ) * gsEps (4 * k) +
      (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
      (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2))) := mul_nonneg hb h_nonneg_T
  have h_main : b * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) *
      (Real.sqrt (d : ℝ) * gsEps (4 * k) +
        (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
        (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2))) ≤
      b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by
    calc
      b * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) *
          (Real.sqrt (d : ℝ) * gsEps (4 * k) +
            (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
            (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)))
      = (b * (Real.sqrt (d : ℝ) * gsEps (4 * k) +
            (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
            (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)))) * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2) := by
        ring
      _ ≤ (b * (Real.sqrt (d : ℝ) * gsEps (4 * k) +
            (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
            (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2)))) * ((d : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left hS h_nonneg_bT
      _ = b * ((d : ℝ) + 1) *
          (Real.sqrt (d : ℝ) * gsEps (4 * k) +
            (d : ℝ) * (2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2) * Real.sqrt (2 * (d : ℝ) * (4 * (k : ℝ))) +
            (d : ℝ) * Real.sqrt ((2 : ℝ) ^ (-((4 * k : ℕ) : ℝ) / 2))) := by ring
      _ ≤ b * ((d : ℝ) + 1) * ((d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hT
        apply mul_nonneg (by nlinarith) (by nlinarith)
      _ = b * ((d : ℝ) + 1) * (d : ℝ) * (8 * (d : ℝ) + 2) * (2 : ℝ) ^ (-(k : ℝ)) := by ring
  simpa [h_rhs, Nat.cast_mul] using h_main

end AdversarialBco.Bit.Aux_tri_epsG_le

namespace AdversarialBco.Bit.Aux_tri_par_row


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem tpr_clog_le (b : ℕ) (hb : 1 < b) (X : ℝ) : X ≤ (b : ℝ) ^ Nat.clog b ⌈X⌉₊ := by
  calc X ≤ ⌈X⌉₊ := Nat.le_ceil X
    _ ≤ ((b ^ Nat.clog b ⌈X⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog hb _
    _ = (b : ℝ) ^ Nat.clog b ⌈X⌉₊ := by push_cast; ring

theorem tpr_clog_lt (b : ℕ) (hb : 1 < b) (X : ℝ) (hX : 1 < X) : (b : ℝ) ^ Nat.clog b ⌈X⌉₊ < b * X := by
  have h1 : 1 < ⌈X⌉₊ := by
    have : (1 : ℝ) < ⌈X⌉₊ := lt_of_lt_of_le hX (Nat.le_ceil X)
    exact_mod_cast this
  have hpos : 0 < Nat.clog b ⌈X⌉₊ := Nat.clog_pos hb h1
  have h2 := Nat.pow_pred_clog_lt_self hb h1
  have h3 : ((b ^ (Nat.clog b ⌈X⌉₊).pred : ℕ) : ℝ) < X := by
    have h4 : b ^ (Nat.clog b ⌈X⌉₊).pred + 1 ≤ ⌈X⌉₊ := h2
    have h5 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    have h6 : ((b ^ (Nat.clog b ⌈X⌉₊).pred : ℕ) : ℝ) + 1 ≤ ⌈X⌉₊ := by exact_mod_cast h4
    linarith
  have h7 : Nat.clog b ⌈X⌉₊ = (Nat.clog b ⌈X⌉₊).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [h7, pow_succ]
  push_cast at h3
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  nlinarith

theorem _root_.AdversarialBco.Bit.tri_par_row (d ℓ : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hℓ : Real.log (1 / δ) ≤ ℓ) :
    0 < triD2 d ∧
      Real.sqrt (triD2 d) ^ 2 / (2 * (1 / 2 ^ triJs d ℓ) * (2 ^ triNe d ℓ : ℕ)) +
          (1 / 2 ^ triJs d ℓ) / 2 * (triGu d + triBu d) ^ 2 + triBu d * Real.sqrt (triD2 d) +
          triGu d * Real.sqrt (triD2 d) * Real.sqrt (2 * Real.log (1 / δ) / (2 ^ triNe d ℓ : ℕ)) +
          2 * triEpsG d ≤ pgEh d (triRh d) := by
  obtain ⟨hRa1, -, hkR, -, -, -, hB1, -⟩ := tri_par_box d hd
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 0 < triR d := by
    have : (0 : ℝ) < pgKappa * triRa d := by unfold pgKappa; positivity
    linarith
  have hD2 : 0 < triD2 d := by
    unfold triD2
    have h1 : 0 < 4 * (d : ℝ) * triR d ^ 2 := by positivity
    have h2 : 0 ≤ (d : ℝ) * (triB d - triA d) ^ 2 := by positivity
    have h3 : 0 ≤ 2 * (d : ℝ) * (d - 1) * triB d ^ 2 := by
      have : (0 : ℝ) ≤ d - 1 := by linarith
      positivity
    linarith
  refine ⟨hD2, ?_⟩
  have hs4 : 4 ≤ triS d := (Nat.find_spec (pg_par_exists d)).1
  have hs16 : 16 ≤ triS d ^ 2 := by nlinarith
  have hLh1 : 1 ≤ triLh (triS d) := by unfold triLh; omega
  have hRh : triRh d = 2 ^ triLh (triS d) - 1 := rfl
  have hRh1 : (1 : ℝ) ≤ triRh d := by
    rw [hRh]
    have : (2 : ℝ) ≤ 2 ^ triLh (triS d) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hLh1
    linarith
  have hLhr : (1 : ℝ) ≤ triLh (triS d) := by exact_mod_cast hLh1
  have hden : 922 * (7 / 5) * (627 / 4000) ≤
      922 * (d : ℝ) ^ 2 * (7 / 5 * triLh (triS d)) * (627 / 4000 * triRh d) := by
    have h1 : (922 : ℝ) ≤ 922 * (d : ℝ) ^ 2 := by nlinarith
    have h2 : (7 / 5 : ℝ) ≤ 7 / 5 * triLh (triS d) := by linarith
    have h3 : (627 / 4000 : ℝ) ≤ 627 / 4000 * triRh d := by linarith
    exact mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by positivity)) h3 (by norm_num) (by positivity)
  have hden0 : (0 : ℝ) < 922 * (d : ℝ) ^ 2 * (7 / 5 * triLh (triS d)) * (627 / 4000 * triRh d) :=
    lt_of_lt_of_le (by norm_num) hden
  have helo0 : 0 < triElo d := by
    unfold triElo pgKappa
    exact div_pos (by norm_num) hden0
  have helo1 : triElo d ≤ 1 := by
    unfold triElo pgKappa
    rw [div_le_one hden0]
    linarith
  have heloEh : triElo d ≤ pgEh d (triRh d) := tri_elo_le d (triLh (triS d)) hd hLh1
  have hℓ0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hℓr : (0 : ℝ) ≤ ℓ := hℓ0.trans hℓ
  have hβ0 : 0 ≤ triBu d := by unfold triBu; positivity
  have hG2 : 2 ≤ triGu d := by
    unfold triGu
    have : (0 : ℝ) ≤ 2 ^ triJa d / 8 := by positivity
    have : (0 : ℝ) ≤ (Nat.sqrt (8 * d * triKg d) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsq : Real.sqrt (triD2 d) ^ 2 = triD2 d := Real.sq_sqrt hD2.le
  have hNc' : ((2 ^ triNe d ℓ : ℕ) : ℝ) = 2 ^ triNe d ℓ := by push_cast; ring
  -- the horizon
  have hNY : 16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) / (9 * triElo d ^ 2) ≤
      (2 : ℝ) ^ triNe d ℓ := by
    have := tpr_clog_le 2 (by norm_num)
      (16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) / (9 * triElo d ^ 2))
    simp only [Nat.cast_ofNat] at this
    exact this
  rw [div_le_iff₀ (by positivity)] at hNY
  -- the rounding grid
  have hBv : 64 * (d + 1) ^ 2 * triD2 d / triElo d ^ 2 ≤ (4 : ℝ) ^ triBv d := by
    have := tpr_clog_le 4 (by norm_num) (64 * (d + 1) ^ 2 * triD2 d / triElo d ^ 2)
    simp only [Nat.cast_ofNat] at this
    exact this
  rw [div_le_iff₀ (by positivity)] at hBv
  -- the sampler bits
  have hKg : 16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d ≤ (2 : ℝ) ^ triKg d := by
    have := tpr_clog_le 2 (by norm_num) (16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d)
    simp only [Nat.cast_ofNat] at this
    refine this.trans (pow_le_pow_right₀ (by norm_num) ?_)
    unfold triKg
    exact le_max_right _ _
  rw [div_le_iff₀ helo0] at hKg
  -- the step
  have hX1 : 1 < (triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ / triD2 d := by
    rw [one_lt_div hD2]
    have hG2' : (2 : ℝ) ≤ triGu d + triBu d := by linarith
    have hG' : 4 ≤ (triGu d + triBu d) ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hG2' 2
      norm_num at this
      exact this
    have e : 16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) =
        72 * triD2 d * (triGu d + triBu d) ^ 2 + 16 * triD2 d * (4 * triGu d ^ 2 * ℓ) := by ring
    have h0 : 0 ≤ 16 * triD2 d * (4 * triGu d ^ 2 * ℓ) := by positivity
    have hel2 : triElo d ^ 2 ≤ 1 := pow_le_one₀ helo0.le helo1
    have hp : (0 : ℝ) ≤ 2 ^ triNe d ℓ := by positivity
    have hel3 : triElo d ^ 2 * 2 ^ triNe d ℓ ≤ 1 * 2 ^ triNe d ℓ := mul_le_mul_of_nonneg_right hel2 hp
    have h8 : 8 * triD2 d * (triGu d + triBu d) ^ 2 ≤ 2 ^ triNe d ℓ := by linarith
    have hA : (triGu d + triBu d) ^ 2 * (8 * triD2 d * (triGu d + triBu d) ^ 2) ≤
        (triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ := mul_le_mul_of_nonneg_left h8 (by positivity)
    have hB : 8 * triD2 d * 4 ≤ 8 * triD2 d * (triGu d + triBu d) ^ 2 :=
      mul_le_mul_of_nonneg_left hG' (by positivity)
    have hC : 4 * (8 * triD2 d * 4) ≤ (triGu d + triBu d) ^ 2 * (8 * triD2 d * (triGu d + triBu d) ^ 2) :=
      mul_le_mul hG' hB (by positivity) (by positivity)
    linarith
  have hJs := tpr_clog_le 4 (by norm_num) ((triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ / triD2 d)
  have hJs' := tpr_clog_lt 4 (by norm_num) ((triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ / triD2 d) hX1
  simp only [Nat.cast_ofNat] at hJs hJs'
  change _ ≤ (4 : ℝ) ^ triJs d ℓ at hJs
  change (4 : ℝ) ^ triJs d ℓ < _ at hJs'
  have h4 : ((2 : ℝ) ^ triJs d ℓ) ^ 2 = 4 ^ triJs d ℓ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4p : (0 : ℝ) < 4 ^ triJs d ℓ := by positivity
  refine (tri_row_main (Real.sqrt (triD2 d)) (Real.sqrt (triD2 d)) (triGu d) (triGu d) (triBu d) (triBu d)
    (Real.log (1 / δ)) ℓ (1 / 2 ^ triJs d ℓ) ((2 ^ triNe d ℓ : ℕ) : ℝ) (triEpsG d) (triElo d)
    (Real.sqrt_pos.2 hD2) le_rfl (by linarith) le_rfl hβ0 le_rfl hℓ0 hℓ (by positivity) (by positivity)
    ?_ ?_ ?_ ?_ ?_ helo0.le).trans heloEh
  · -- hs1
    rw [hsq, div_pow, one_pow, h4, hNc']
    rw [mul_div_assoc', lt_div_iff₀ hD2] at hJs'
    rw [show 4 * (1 / 4 ^ triJs d ℓ) * (triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ =
      4 * ((triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ) / 4 ^ triJs d ℓ by ring, lt_div_iff₀ h4p]
    linarith
  · -- hs2
    rw [hsq, div_pow, one_pow, h4, hNc']
    rw [div_le_iff₀ hD2] at hJs
    rw [show 1 / 4 ^ triJs d ℓ * (triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ =
      (triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ / 4 ^ triJs d ℓ by ring, div_le_iff₀ h4p]
    linarith
  · -- hNc
    rw [hsq, hNc']
    linarith
  · -- hβc
    rw [hsq]
    unfold triBu
    rw [div_pow, show ((2 : ℝ) ^ triBv d) ^ 2 = 4 ^ triBv d by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    have h4b : (0 : ℝ) < 4 ^ triBv d := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h4b]
    linarith
  · -- hεc
    unfold triEpsG
    have h2k : (0 : ℝ) < 2 ^ triKg d := by positivity
    rw [mul_div_assoc', div_le_iff₀ h2k]
    linarith

end AdversarialBco.Bit.Aux_tri_par_row

namespace AdversarialBco.Bit.Aux_gs_bad


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_bad (d B : ℕ) (hB : 8 ≤ B) :
    (gsOmega d).real {ω | ∃ i, gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} ≤
      d * (2 : ℝ) ^ (-(B : ℝ) / 2) := by
  -- Step 1: rewrite the set as a union
  have h_union_set : {ω | ∃ i, gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} =
      ⋃ i : Fin d, {ω | gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} := by
    ext ω; simp
  rw [h_union_set]
  -- Step 2: union bound
  refine le_trans (measureReal_iUnion_fintype_le _) ?_
  -- Step 3: bound each term
  have h_each (i : Fin d) : (gsOmega d).real {ω | gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} ≤
      (2 : ℝ) ^ (-(B : ℝ) / 2) := by
    -- Define the sets
    let E_i : Set (ℝ × ℝ) := {p | gsEps B < |((gsSpec B (gsCell B p.1) (gsCell B p.2)).1 : ℝ) / 2 ^ (2 * gsm_prec B) - bmCos p|}
    let E_box : Set (ℝ × ℝ) := {p | (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) <
      |bmCos p - bmCos (((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B), ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|}
    -- Show that the set in question equals (eval i)⁻¹' E_i
    have h_preimage : {ω | gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} =
        (fun ω => ω i) ⁻¹' E_i := by
      ext ω; simp [E_i, gsVec, gsCells, bmCos]
    rw [h_preimage]
    -- Measurability of E_i
    have h_meas_E_i : MeasurableSet E_i := by
      have h_meas_fun : Measurable (fun (p : ℝ × ℝ) =>
          |((gsSpec B (gsCell B p.1) (gsCell B p.2)).1 : ℝ) / 2 ^ (2 * gsm_prec B) - bmCos p|) := by
        have hc : Measurable (gsCell B) := by
          unfold gsCell
          exact (show Measurable (Int.toNat : ℤ → ℕ) from Measurable.of_discrete).comp
            ((measurable_sub_const 1).comp (Int.measurable_ceil.comp (measurable_const.mul measurable_id)))
        have hb : Measurable bmCos := by unfold bmCos; fun_prop
        have hq : Measurable (fun q : ℕ × ℕ => ((gsSpec B q.1 q.2).1 : ℝ) / 2 ^ (2 * gsm_prec B)) :=
          measurable_of_countable _
        exact continuous_abs.measurable.comp
          ((hq.comp ((hc.comp measurable_fst).prodMk (hc.comp measurable_snd))).sub hb)
      have h_open : MeasurableSet (Set.Ioi (gsEps B)) := measurableSet_Ioi
      exact h_meas_fun h_open
    have h_meas_E_box : MeasurableSet E_box := by
      have h_meas_fun : Measurable (fun (p : ℝ × ℝ) =>
          |bmCos p - bmCos (((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B), ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|) := by
        have hb : Measurable bmCos := by unfold bmCos; fun_prop
        have hr : Measurable (fun x : ℝ => ((⌈(2 : ℝ) ^ B * x⌉ : ℤ) : ℝ) / 2 ^ B) :=
          ((show Measurable (fun z : ℤ => (z : ℝ)) from Measurable.of_discrete).comp
            (Int.measurable_ceil.comp (measurable_const.mul measurable_id))).div_const _
        exact continuous_abs.measurable.comp
          (hb.sub (hb.comp ((hr.comp measurable_fst).prodMk (hr.comp measurable_snd))))
      have h_open : MeasurableSet (Set.Ioi ((2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)))) :=
        measurableSet_Ioi
      exact h_meas_fun h_open
    -- Relate (gsOmega d).real ((eval i)⁻¹' E_i) to (unif01.prod unif01).real E_i
    have h_unif01_prob : IsProbabilityMeasure unif01 := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
    haveI : ∀ i : Fin d, IsProbabilityMeasure (unif01.prod unif01) := by
      intro i; infer_instance
    have h_mp : MeasurePreserving (fun ω => ω i) (gsOmega d) (unif01.prod unif01) :=
      measurePreserving_eval (fun _ : Fin d => unif01.prod unif01) i
    have h_map_eq : (gsOmega d).map (fun ω => ω i) = unif01.prod unif01 := h_mp.map_eq
    have h_measureReal_eq : ((gsOmega d).map (fun ω => ω i)).real E_i = (gsOmega d).real ((fun ω => ω i) ⁻¹' E_i) :=
      map_measureReal_apply (measurable_pi_apply i) h_meas_E_i
    rw [← h_measureReal_eq, h_map_eq]
    -- Now we need to show (unif01.prod unif01).real E_i ≤ 2^(-B/2)
    -- First, prove E_i ∩ S ⊆ E_box for S = Ioc 0 1 × Ioc 0 1
    let S : Set (ℝ × ℝ) := (Set.Ioc (0 : ℝ) 1) ×ˢ (Set.Ioc (0 : ℝ) 1)
    have h_subset : E_i ∩ S ⊆ E_box := by
      intro p hp
      rcases hp with ⟨hp_E_i, hp_S⟩
      rcases hp_S with ⟨hp1, hp2⟩
      have hp1_low : 0 < p.1 := hp1.1
      have hp1_high : p.1 ≤ 1 := hp1.2
      have hp2_low : 0 < p.2 := hp2.1
      have hp2_high : p.2 ≤ 1 := hp2.2
      have h_ceil1 := dyadic_ceil B p.1 hp1_low hp1_high
      have h_ceil2 := dyadic_ceil B p.2 hp2_low hp2_high
      rcases h_ceil1 with ⟨h_ceil1_low, h_ceil1_high, h_ceil1_le, h_ceil1_diff⟩
      rcases h_ceil2 with ⟨h_ceil2_low, h_ceil2_high, h_ceil2_le, h_ceil2_diff⟩
      let U := gsCell B p.1
      let W := gsCell B p.2
      have hU_lt : U < 2 ^ B := by
        unfold U gsCell
        have h_ceil_le_int : (⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) ≤ (2 ^ B : ℤ) := by exact_mod_cast h_ceil1_high
        have h_ceil_ge_one_int : (1 : ℤ) ≤ ⌈(2 : ℝ) ^ B * p.1⌉ := h_ceil1_low
        have h_sub_lt : (⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1 < (2 ^ B : ℤ) := by omega
        have h_nonneg : 0 ≤ (⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1 := by omega
        rw [Int.toNat_lt h_nonneg]
        exact h_sub_lt
      have hW_lt : W < 2 ^ B := by
        unfold W gsCell
        have h_ceil_le_int : (⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) ≤ (2 ^ B : ℤ) := by exact_mod_cast h_ceil2_high
        have h_ceil_ge_one_int : (1 : ℤ) ≤ ⌈(2 : ℝ) ^ B * p.2⌉ := h_ceil2_low
        have h_sub_lt : (⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1 < (2 ^ B : ℤ) := by omega
        have h_nonneg : 0 ≤ (⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1 := by omega
        rw [Int.toNat_lt h_nonneg]
        exact h_sub_lt
      have h_gsSpec := gsSpec_err B U W hB hU_lt hW_lt
      rcases h_gsSpec with ⟨h_gsSpec1, h_gsSpec2, h_gsSpec3, h_gsSpec4⟩
      have hU_cast : (U : ℝ) + 1 = (⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) := by
        unfold U gsCell
        have h_nonneg : 0 ≤ (⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1 := by
          have h_ceil_ge_one : (1 : ℤ) ≤ ⌈(2 : ℝ) ^ B * p.1⌉ := h_ceil1_low
          omega
        have h_toNat_eq : ((⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1).toNat = (⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1 :=
          Int.toNat_of_nonneg h_nonneg
        have h_eq : (((⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1).toNat : ℝ) = (((⌈(2 : ℝ) ^ B * p.1⌉ : ℤ) - 1 : ℤ) : ℝ) := by
          exact_mod_cast h_toNat_eq
        rw [h_eq]
        simp
      have hW_cast : (W : ℝ) + 1 = (⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) := by
        unfold W gsCell
        have h_nonneg : 0 ≤ (⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1 := by
          have h_ceil_ge_one : (1 : ℤ) ≤ ⌈(2 : ℝ) ^ B * p.2⌉ := h_ceil2_low
          omega
        have h_toNat_eq : ((⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1).toNat = (⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1 :=
          Int.toNat_of_nonneg h_nonneg
        have h_eq : (((⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1).toNat : ℝ) = (((⌈(2 : ℝ) ^ B * p.2⌉ : ℤ) - 1 : ℤ) : ℝ) := by
          exact_mod_cast h_toNat_eq
        rw [h_eq]
        simp
      have h_gsSpec1' : |((gsSpec B U W).1 : ℝ) / 2 ^ (2 * gsm_prec B) -
          bmCos (((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B), ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| ≤ 1 / 2 ^ B := by
        -- h_gsSpec1 has the expanded form of bmCos
        -- Rewrite using hU_cast and hW_cast
        rw [show ((U : ℝ) + 1) / 2 ^ B = ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B) from by rw [hU_cast]] at h_gsSpec1
        rw [show ((W : ℝ) + 1) / 2 ^ B = ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B) from by rw [hW_cast]] at h_gsSpec1
        simpa [bmCos] using h_gsSpec1
      replace hp_E_i : gsEps B < |((gsSpec B (gsCell B p.1) (gsCell B p.2)).1 : ℝ) / 2 ^ (2 * gsm_prec B) - bmCos p| := hp_E_i
      have h_gsEps_eq : gsEps B = 1 / (2 ^ B : ℝ) + ((2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ))) := by
        unfold gsEps; ring
      rw [h_gsEps_eq] at hp_E_i
      have h_ineq : (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) <
          |bmCos p - bmCos (((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B), ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| := by
        let G := ((gsSpec B U W).1 : ℝ) / 2 ^ (2 * gsm_prec B)
        let C := bmCos p
        let C' := bmCos (((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B), ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))
        have h_abs1 : |G - C| ≤ |G - C'| + |C' - C| := abs_sub_le G C' C
        have h_abs2 : |G - C'| ≤ 1 / (2 ^ B : ℝ) := h_gsSpec1'
        have h_sum : |G - C| > 1 / (2 ^ B : ℝ) + ((2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ))) := hp_E_i
        have h_lower : |G - C| - |G - C'| ≤ |C' - C| := by linarith
        have h_abs_sub_comm : |C - C'| = |C' - C| := by rw [abs_sub_comm]
        rw [h_abs_sub_comm]
        linarith
      unfold E_box
      simpa using h_ineq
    -- Now the key measure argument: E_i \ E_box ⊆ Sᶜ, and Sᶜ has measure 0
    have h_S_meas : MeasurableSet S := by
      unfold S; exact (measurableSet_Ioc.prod measurableSet_Ioc)
    have h_S_null : (unif01.prod unif01) (Sᶜ) = 0 := by
      have h_unif01_univ : unif01 Set.univ = 1 := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
      have h_S_univ : (unif01.prod unif01) S = 1 := by
        -- S = Ioc 0 1 ×ˢ Ioc 0 1, and unif01 = volume.restrict (Ioc 0 1)
        -- So (unif01.prod unif01) S = unif01 (Ioc 0 1) * unif01 (Ioc 0 1) = 1 * 1 = 1
        unfold S
        rw [Measure.prod_prod (Set.Ioc (0 : ℝ) 1) (Set.Ioc (0 : ℝ) 1)]
        have h1 : unif01 (Set.Ioc (0 : ℝ) 1) = 1 := by
          rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_self, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
        rw [h1, one_mul]
      have h_total : (unif01.prod unif01) Set.univ = 1 := by
        have h_prob : IsProbabilityMeasure (unif01.prod unif01) := by infer_instance
        exact h_prob.measure_univ
      have h_disjoint : Disjoint S (Sᶜ) := disjoint_compl_right
      have h_union : (unif01.prod unif01) (S ∪ Sᶜ) = (unif01.prod unif01) S + (unif01.prod unif01) (Sᶜ) :=
        measure_union h_disjoint h_S_meas.compl
      rw [Set.union_compl_self, h_total, h_S_univ] at h_union
      have h_one_ne_top : (1 : ENNReal) ≠ ∞ := by norm_num
      have h_eq : (1 : ENNReal) + (unif01.prod unif01) (Sᶜ) = (1 : ENNReal) + 0 := by
        simpa using h_union.symm
      exact ((ENNReal.add_right_inj h_one_ne_top).mp h_eq)
    have h_diff_subset : E_i \ E_box ⊆ Sᶜ := by
      intro x hx
      rcases hx with ⟨hx_E_i, hx_not_E_box⟩
      by_contra hx_not_S
      have hx_S : x ∈ S := by simpa using hx_not_S
      have hx_in_inter : x ∈ E_i ∩ S := ⟨hx_E_i, hx_S⟩
      have hx_in_box : x ∈ E_box := h_subset hx_in_inter
      exact hx_not_E_box hx_in_box
    have h_diff_measure_zero : (unif01.prod unif01) (E_i \ E_box) = 0 :=
      measure_mono_null h_diff_subset h_S_null
    have h_diff_real_zero : (unif01.prod unif01).real (E_i \ E_box) = 0 := by
      rw [measureReal_def, h_diff_measure_zero, ENNReal.toReal_zero]
    have h_disjoint : Disjoint (E_i ∩ E_box) (E_i \ E_box) :=
      Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2
    have h_meas_diff : MeasurableSet (E_i \ E_box) := h_meas_E_i.diff h_meas_E_box
    have h_fin1 : (unif01.prod unif01) (E_i ∩ E_box) ≠ ∞ := measure_ne_top _ _
    have h_fin2 : (unif01.prod unif01) (E_i \ E_box) ≠ ∞ := measure_ne_top _ _
    have h_union_eq : (E_i ∩ E_box) ∪ (E_i \ E_box) = E_i := by
      ext x; simp
    have h_split : (unif01.prod unif01).real E_i = (unif01.prod unif01).real (E_i ∩ E_box) := by
      calc
        (unif01.prod unif01).real E_i = (unif01.prod unif01).real ((E_i ∩ E_box) ∪ (E_i \ E_box)) := by rw [h_union_eq]
        _ = (unif01.prod unif01).real (E_i ∩ E_box) + (unif01.prod unif01).real (E_i \ E_box) :=
          measureReal_union h_disjoint h_meas_diff h_fin1 h_fin2
        _ = (unif01.prod unif01).real (E_i ∩ E_box) + 0 := by rw [h_diff_real_zero]
        _ = (unif01.prod unif01).real (E_i ∩ E_box) := by simp
    have h_fin_E_box : (unif01.prod unif01) E_box ≠ ∞ := by
      have h_bound : (unif01.prod unif01) E_box ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := boxMuller_coupling B
      exact ne_of_lt (lt_of_le_of_lt h_bound ENNReal.ofReal_lt_top)
    calc
      (unif01.prod unif01).real E_i = (unif01.prod unif01).real (E_i ∩ E_box) := h_split
      _ ≤ (unif01.prod unif01).real E_box := measureReal_mono Set.inter_subset_right h_fin_E_box
      _ ≤ ENNReal.toReal (ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2))) := by
        have h_box := boxMuller_coupling B
        rw [measureReal_def]
        refine ENNReal.toReal_mono (by
          -- ENNReal.ofReal x ≠ ∞ for any x
          exact ENNReal.ofReal_ne_top) h_box
      _ = (2 : ℝ) ^ (-(B : ℝ) / 2) := by
        rw [ENNReal.toReal_ofReal (by positivity)]
  -- Step 4: combine
  calc
    ∑ i : Fin d, (gsOmega d).real {ω | gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} ≤
        ∑ i : Fin d, (2 : ℝ) ^ (-(B : ℝ) / 2) := Finset.sum_le_sum (fun i _ => h_each i)
    _ = (Finset.card (Finset.univ : Finset (Fin d))) * (2 : ℝ) ^ (-(B : ℝ) / 2) := by simp
    _ = d * (2 : ℝ) ^ (-(B : ℝ) / 2) := by simp

end AdversarialBco.Bit.Aux_gs_bad

namespace AdversarialBco.Bit.Aux_gsOmega_cells


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gsOmega_cells (d B : ℕ) :
    (gsOmega d).map (gsCells d B) =
      Measure.pi fun _ : Fin d => (unif01.map (gsCell B)).prod (unif01.map (gsCell B)) := by
  unfold gsOmega gsCells unif01
  let f : Fin d → (ℝ × ℝ) → (ℕ × ℕ) := fun _ p => (gsCell B p.1, gsCell B p.2)
  have hf : ∀ (i : Fin d), AEMeasurable (f i)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    intro i
    refine (Measurable.aemeasurable ?_)
    unfold f
    have h_mul1 : Measurable (fun u : ℝ => (2 : ℝ) ^ B * u) :=
      (measurable_const_mul ((2 : ℝ) ^ B)).comp measurable_id
    have h_ceil1 : Measurable (fun u : ℝ => (⌈(2 : ℝ) ^ B * u⌉ : ℤ)) :=
      Int.measurable_ceil.comp h_mul1
    have h_sub1 : Measurable (fun z : ℤ => z - 1) :=
      measurable_sub_const 1
    have h_combined1 : Measurable (fun u : ℝ => (⌈(2 : ℝ) ^ B * u⌉ - 1 : ℤ)) :=
      h_sub1.comp h_ceil1
    have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := by
      apply measurable_of_countable
    have h_gsCell : Measurable (gsCell B) := h_toNat.comp h_combined1
    apply Measurable.prod
    · exact h_gsCell.comp measurable_fst
    · exact h_gsCell.comp measurable_snd
  rw [Measure.pi_map_pi hf]
  unfold f
  have h_gsCell_meas : Measurable (gsCell B) := by
    unfold gsCell
    have h_mul1 : Measurable (fun u : ℝ => (2 : ℝ) ^ B * u) :=
      (measurable_const_mul ((2 : ℝ) ^ B)).comp measurable_id
    have h_ceil1 : Measurable (fun u : ℝ => (⌈(2 : ℝ) ^ B * u⌉ : ℤ)) :=
      Int.measurable_ceil.comp h_mul1
    have h_sub1 : Measurable (fun z : ℤ => z - 1) :=
      measurable_sub_const 1
    have h_combined1 : Measurable (fun u : ℝ => (⌈(2 : ℝ) ^ B * u⌉ - 1 : ℤ)) :=
      h_sub1.comp h_ceil1
    have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := by
      apply measurable_of_countable
    exact h_toNat.comp h_combined1
  rw [Measure.map_prod_map (volume.restrict (Set.Ioc (0 : ℝ) 1))
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) h_gsCell_meas h_gsCell_meas]
  rfl

end AdversarialBco.Bit.Aux_gsOmega_cells

namespace AdversarialBco.Bit.Aux_cells_V_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.cells_V_law (B : ℕ) :
    AdversarialBco.BitRAM.coinStream.map
        (fun cs (q : ℕ) => (AdversarialBco.BitRAM.readCoins cs (q * B) B).toNat) =
      Measure.infinitePi fun _ : ℕ => unif01.map (gsCell B) := by
  classical
  let f : ℕ × Fin B → ℕ := fun p => p.1 * B + p.2
  have hf : Function.Injective f := by
    rintro ⟨q, k⟩ ⟨q', k'⟩ h
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) k.2
    have e1 : (q * B + k) / B = q ∧ (q * B + k) % B = k := (Nat.div_mod_unique hB).2 ⟨by ring, k.2⟩
    have e2 : (q' * B + k') / B = q' ∧ (q' * B + k') % B = k' := (Nat.div_mod_unique hB).2 ⟨by ring, k'.2⟩
    have h' : q * B + (k : ℕ) = q' * B + k' := h
    rw [h'] at e1
    have hq : q = q' := e1.1.symm.trans e2.1
    have hk : k = k' := Fin.ext (e1.2.symm.trans e2.2)
    rw [hq, hk]
  let ext : (Fin B → Bool) → ℕ → Bool := fun w i => if hi : i < B then w ⟨i, hi⟩ else false
  let hfun : (Fin B → Bool) → ℕ := fun w => (AdversarialBco.BitRAM.readCoins (ext w) 0 B).toNat
  have hblk : ∀ cs q, (AdversarialBco.BitRAM.readCoins cs (q * B) B).toNat =
      hfun (fun k : Fin B => cs (f (q, k))) := by
    intro cs q
    show _ = (AdversarialBco.BitRAM.readCoins (ext fun k : Fin B => cs (f (q, k))) 0 B).toNat
    congr 1
    rw [(readCoins_facts cs cs (q * B) B).2.2.1]
    refine (readCoins_facts (fun i => cs (q * B + i)) (ext fun k : Fin B => cs (f (q, k))) 0 B).2.2.2 ?_
    intro i _ hi
    have hiB : i < B := by omega
    simp only [ext, hiB, dif_pos, f]
  have hhm : Measurable hfun := measurable_of_finite _
  have hX : Measurable (fun x : ℕ → Bool => fun (j : ℕ) (k : Fin B) => x (f (j, k))) :=
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_pi_apply _
  have hW : Measurable (fun w : ℕ → Fin B → Bool => fun q => hfun (w q)) :=
    Measurable.of_eval fun q => hhm.comp (measurable_pi_apply q)
  have hcs : AdversarialBco.BitRAM.coinStream = Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinLaw := rfl
  have hcurry := coin_curry_inj AdversarialBco.BitRAM.coinLaw f hf
  have h1 : (Measure.infinitePi fun _ : Fin B => AdversarialBco.BitRAM.coinLaw).map hfun =
      unif01.map (gsCell B) := by
    have h0 := gs_coin_block B 0
    have e : (fun cs => (AdversarialBco.BitRAM.readCoins cs 0 B).toNat) =
        (hfun ∘ fun w : ℕ → Fin B → Bool => w 0) ∘ (fun x : ℕ → Bool => fun (j : ℕ) (k : Fin B) => x (f (j, k))) := by
      funext cs
      have := hblk cs 0
      rwa [zero_mul] at this
    rw [e, ← Measure.map_map (hhm.comp (measurable_pi_apply 0)) hX, hcs, hcurry,
      ← Measure.map_map hhm (measurable_pi_apply 0),
      Measure.infinitePi_map_eval (fun _ : ℕ => Measure.infinitePi fun _ : Fin B => AdversarialBco.BitRAM.coinLaw) 0] at h0
    exact h0
  have hmap : (fun cs (q : ℕ) => (AdversarialBco.BitRAM.readCoins cs (q * B) B).toNat) =
      (fun w : ℕ → Fin B → Bool => fun q => hfun (w q)) ∘
        (fun x : ℕ → Bool => fun (j : ℕ) (k : Fin B) => x (f (j, k))) := by
    funext cs q
    exact hblk cs q
  rw [hmap, ← Measure.map_map hW hX, hcs, hcurry,
    Measure.infinitePi_map_pi (fun _ : ℕ => Measure.infinitePi fun _ : Fin B => AdversarialBco.BitRAM.coinLaw)
      (f := fun _ => hfun) (fun _ => hhm), h1]

end AdversarialBco.Bit.Aux_cells_V_law

namespace AdversarialBco.Bit.Aux_tri_draws_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

set_option maxHeartbeats 400000

theorem _root_.AdversarialBco.Bit.tri_draws_law (d B : ℕ) :
    AdversarialBco.BitRAM.coinStream.map (fun x (t : ℕ) => triDraw d B x t) =
      Measure.infinitePi fun _ : ℕ => gsLaw d B := by
  -- helper: V cs q = (readCoins cs (q * B) B).toNat
  let V : (ℕ → Bool) → ℕ → ℕ := fun cs q => (AdversarialBco.BitRAM.readCoins cs (q * B) B).toNat
  -- U = unif01.map (gsCell B)
  let U : Measure ℕ := unif01.map (gsCell B)
  -- Φ : (ℕ → ℕ) → ℕ → EuclideanSpace ℝ (Fin d)
  let Φ : (ℕ → ℕ) → ℕ → EuclideanSpace ℝ (Fin d) :=
    fun v t => gsVec d B fun i => (v (2 * (t * d + i)), v (2 * (t * d + i) + 1))
  -- the injection f : ℕ × (Fin d × Fin 2) → ℕ
  let f : ℕ × (Fin d × Fin 2) → ℕ := fun (t, (i, s)) => 2 * (t * d + i) + s
  have hf_inj : Function.Injective f := by
    intro a b h
    rcases a with ⟨t, i, s⟩
    rcases b with ⟨t', i', s'⟩
    have h_eq : 2 * (t * d + i.val) + s.val = 2 * (t' * d + i'.val) + s'.val := h
    have hs : s.val = s'.val := by
      have hs_range : s.val < 2 := s.is_lt
      have hs'_range : s'.val < 2 := s'.is_lt
      have hmod := congrArg (fun x => x % 2) h_eq
      simp [Nat.mod_eq_of_lt hs_range, Nat.mod_eq_of_lt hs'_range] at hmod
      exact hmod
    have hbase : t * d + i.val = t' * d + i'.val := by
      omega
    have hi : i.val = i'.val := by
      have hi_lt : i.val < d := i.is_lt
      have hi'_lt : i'.val < d := i'.is_lt
      have hmod := congrArg (fun x => x % d) hbase
      simp [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hi'_lt] at hmod
      exact hmod
    have ht : t = t' := by
      have hd_pos : d > 0 := by
        by_contra hd
        have hd0 : d = 0 := by omega
        have : IsEmpty (Fin d) := by
          rw [hd0]
          exact inferInstance
        exact this.elim i
      rw [hi] at hbase
      have hbase' : t * d = t' * d := by omega
      -- Nat.eq_of_mul_eq_mul_left expects d * t = d * t', so use mul_comm
      rw [mul_comm t d, mul_comm t' d] at hbase'
      exact Nat.eq_of_mul_eq_mul_left hd_pos hbase'
    have hi_fin : i = i' := Fin.ext hi
    have hs_fin : s = s' := Fin.ext hs
    simp [ht, hi_fin, hs_fin]
  -- R : (ℕ → ℕ) → ℕ → (Fin d × Fin 2) → ℕ
  let R : (ℕ → ℕ) → ℕ → (Fin d × Fin 2) → ℕ := fun v t p => v (f (t, p))
  -- Ψ' : (ℕ → (Fin d × Fin 2) → ℕ) → ℕ → EuclideanSpace ℝ (Fin d)
  let Ψ' : (ℕ → (Fin d × Fin 2) → ℕ) → ℕ → EuclideanSpace ℝ (Fin d) :=
    fun w t => gsVec d B fun i => (w t (i, 0), w t (i, 1))
  -- measurability of V
  have hV_meas : Measurable V := by
    refine Measurable.of_eval fun q => ?_
    have h := AdversarialBco.Bit.readCoins_meas (q * B) B
    have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := by
      exact measurable_of_countable _
    exact h_toNat.comp h
  -- measurability of Φ
  have hΦ_meas : Measurable Φ := by
    refine Measurable.of_eval fun t => ?_
    have h_gsVec_meas : Measurable (gsVec d B) := by
      have : Countable (Fin d → ℕ × ℕ) := by infer_instance
      have : MeasurableSingletonClass (Fin d → ℕ × ℕ) := by infer_instance
      exact measurable_of_countable _
    refine h_gsVec_meas.comp ?_
    refine Measurable.of_eval fun i => ?_
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_apply (2 * (t * d + i))
    · exact measurable_pi_apply (2 * (t * d + i) + 1)
  -- measurability of R
  have hR_meas : Measurable R := by
    refine Measurable.of_eval fun t => ?_
    refine Measurable.of_eval fun p => ?_
    exact measurable_pi_apply (f (t, p))
  -- measurability of Ψ'
  have hΨ'_meas : Measurable Ψ' := by
    refine Measurable.of_eval fun t => ?_
    have h_gsVec_meas : Measurable (gsVec d B) := by
      have : Countable (Fin d → ℕ × ℕ) := by infer_instance
      have : MeasurableSingletonClass (Fin d → ℕ × ℕ) := by infer_instance
      exact measurable_of_countable _
    refine h_gsVec_meas.comp ?_
    refine Measurable.of_eval fun i => ?_
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_pi_apply (i, 0)).comp (measurable_pi_apply t)
    · exact (measurable_pi_apply (i, 1)).comp (measurable_pi_apply t)
  -- main proof
  have h_triDraw_eq : (fun (x : ℕ → Bool) (t : ℕ) => triDraw d B x t) = Φ ∘ V := by
    ext x t
    simp [triDraw, V, Φ, gsVec]
  rw [h_triDraw_eq]
  rw [← Measure.map_map hΦ_meas hV_meas]
  have h_map_V : Measure.map V BitRAM.coinStream = Measure.infinitePi fun _ : ℕ => U := by
    simp [BitRAM.coinStream, V, U]
    exact AdversarialBco.Bit.cells_V_law B
  rw [h_map_V]
  have h_Φ_eq_Ψ'_R : Φ = Ψ' ∘ R := by
    ext v t
    simp [Φ, Ψ', R, f]
  rw [h_Φ_eq_Ψ'_R]
  rw [← Measure.map_map hΨ'_meas hR_meas]
  -- Need IsProbabilityMeasure U for coin_curry_inj
  have h_unif01_prob : MeasureTheory.IsProbabilityMeasure unif01 := by
    constructor
    simp [unif01, Real.volume_Ioc]
  have hU_prob : MeasureTheory.IsProbabilityMeasure U := by
    unfold U
    infer_instance
  have h_coin_curry := AdversarialBco.Bit.coin_curry_inj U f hf_inj
  rw [h_coin_curry]
  -- Write Ψ' w t = F (w t) where F u = gsVec d B (fun i => (u (i,0), u (i,1)))
  let F : ((Fin d × Fin 2) → ℕ) → EuclideanSpace ℝ (Fin d) :=
    fun u => gsVec d B fun i => (u (i, 0), u (i, 1))
  have hΨ'_eq : Ψ' = fun w t => F (w t) := by
    ext w t
    simp [Ψ', F]
  rw [hΨ'_eq]
  -- Apply infinitePi_map_pi
  have hF_meas : Measurable F := by
    have : Countable ((Fin d × Fin 2) → ℕ) := by infer_instance
    have : MeasurableSingletonClass ((Fin d × Fin 2) → ℕ) := by infer_instance
    exact measurable_of_countable _
  have h_infinitePi_map := MeasureTheory.Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => Measure.infinitePi fun _ : Fin d × Fin 2 => U)
    (f := fun _ : ℕ => F)
    (hf := fun _ => hF_meas)
  rw [h_infinitePi_map]
  -- Now goal: infinitePi fun t => Measure.map F (infinitePi fun p : Fin d × Fin 2 => U)
  -- = infinitePi fun _ => gsLaw d B
  -- Prove the inner equality
  have h_gsVec_meas : Measurable (gsVec d B) := by
    have : Countable (Fin d → ℕ × ℕ) := by infer_instance
    have : MeasurableSingletonClass (Fin d → ℕ × ℕ) := by infer_instance
    exact measurable_of_countable _
  have h_gsCell_meas : Measurable (gsCell B) := by
    unfold gsCell
    have h_ceil : Measurable (Int.ceil : ℝ → ℤ) := Int.measurable_ceil
    have h_mul : Measurable (fun u : ℝ => ((2 : ℝ) ^ B) * u) :=
      (measurable_id.const_mul ((2 : ℝ) ^ B))
    have h_sub : Measurable (fun x : ℤ => x - 1) := measurable_of_countable _
    have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := measurable_of_countable _
    refine h_toNat.comp (h_sub.comp (h_ceil.comp h_mul))
  have h_pair_meas : Measurable (fun (w : (Fin d × Fin 2) → ℕ) (i : Fin d) => (w (i, 0), w (i, 1))) := by
    refine Measurable.of_eval fun i => ?_
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_apply (i, 0)
    · exact measurable_pi_apply (i, 1)
  have h_pair : Measure.map (fun (w : (Fin d × Fin 2) → ℕ) (i : Fin d) => (w (i, 0), w (i, 1)))
      (Measure.infinitePi fun _ : Fin d × Fin 2 => U) =
      Measure.pi fun _ : Fin d => U.prod U := by
    simpa using AdversarialBco.Bit.gs_pair_law U d
  have h_cells : (gsOmega d).map (gsCells d B) = Measure.pi fun _ : Fin d => U.prod U := by
    simpa [U, gsOmega, gsCells] using AdversarialBco.Bit.gsOmega_cells d B
  have h_cells_meas : Measurable (gsCells d B) := by
    refine Measurable.of_eval fun i => ?_
    refine Measurable.prodMk ?_ ?_
    · -- ω ↦ gsCell B (ω i).1
      exact h_gsCell_meas.comp (measurable_fst.comp (measurable_pi_apply i))
    · -- ω ↦ gsCell B (ω i).2
      exact h_gsCell_meas.comp (measurable_snd.comp (measurable_pi_apply i))
  have h_inner : Measure.map F (Measure.infinitePi fun _ : Fin d × Fin 2 => U) = gsLaw d B := by
    -- F = (gsVec d B) ∘ (fun w i => (w (i, 0), w (i, 1)))
    have hF_eq : F = (gsVec d B) ∘ (fun (w : (Fin d × Fin 2) → ℕ) (i : Fin d) => (w (i, 0), w (i, 1))) := by
      ext u
      simp [F]
    rw [hF_eq]
    -- Measure.map ((gsVec d B) ∘ ...) μ = Measure.map (gsVec d B) (Measure.map ... μ)
    rw [← Measure.map_map h_gsVec_meas h_pair_meas]
    -- Now: Measure.map (gsVec d B) (Measure.map ... μ) = gsLaw d B
    rw [h_pair]
    -- Now: Measure.map (gsVec d B) (Measure.pi fun _ : Fin d => U.prod U) = gsLaw d B
    rw [← h_cells]
    -- Now: Measure.map (gsVec d B) ((gsOmega d).map (gsCells d B)) = gsLaw d B
    rw [Measure.map_map h_gsVec_meas h_cells_meas]
    -- Now: ((gsOmega d).map (gsCells d B)).map (gsVec d B) = gsLaw d B
    -- But gsLaw d B = (gsOmega d).map (fun ω => gsVec d B (gsCells d B ω))
    -- = ((gsOmega d).map (gsCells d B)).map (gsVec d B) by Measure.map_map
    -- So this is true by definition
    rfl
  rw [h_inner]

end AdversarialBco.Bit.Aux_tri_draws_law

namespace AdversarialBco.Bit.Aux_tri_draw_facts


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_draw_facts (d B : ℕ) (hB : 8 ≤ B) :
    (∀ x t, ‖triDraw d B x t‖ ≤ Real.sqrt (2 * d * B)) ∧ Measurable (fun x (t : ℕ) => triDraw d B x t) ∧
      ∀ x x' t, (∀ i, i < 2 * (t + 1) * d * B → x i = x' i) → triDraw d B x t = triDraw d B x' t := by
  have hBpos : 0 < B := by omega
  have h_bound : ∀ x t, ‖triDraw d B x t‖ ≤ Real.sqrt (2 * d * B) := by
    intro x t
    dsimp [triDraw]
    apply gs_sure d B hB
    intro i
    have h1 := readCoins_facts x x (2 * (t * d + i) * B) B
    rcases h1 with ⟨h_nonneg1, h_lt1, _, _⟩
    have h_lt_nat1 : (AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat < 2 ^ B := by
      rw [Int.toNat_lt h_nonneg1]
      exact h_lt1
    have h2 := readCoins_facts x x ((2 * (t * d + i) + 1) * B) B
    rcases h2 with ⟨h_nonneg2, h_lt2, _, _⟩
    have h_lt_nat2 : (AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat < 2 ^ B := by
      rw [Int.toNat_lt h_nonneg2]
      exact h_lt2
    exact ⟨h_lt_nat1, h_lt_nat2⟩
  have h_meas : Measurable (fun x (t : ℕ) => triDraw d B x t) := by
    refine Measurable.of_eval fun t => ?_
    dsimp [triDraw]
    have h_gsvec : Measurable (gsVec d B) := measurable_of_countable _
    have h_arg : Measurable (fun x : ℕ → Bool => (fun i : Fin d =>
      ((AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat,
       (AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat))) := by
      refine Measurable.of_eval fun i => ?_
      have h_meas1 : Measurable (fun x : ℕ → Bool =>
        (AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat) := by
        have h_read : Measurable (fun x : ℕ → Bool =>
          AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B) := readCoins_meas _ _
        have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := Measurable.of_discrete
        exact h_toNat.comp h_read
      have h_meas2 : Measurable (fun x : ℕ → Bool =>
        (AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat) := by
        have h_read : Measurable (fun x : ℕ → Bool =>
          AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B) := readCoins_meas _ _
        have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := Measurable.of_discrete
        exact h_toNat.comp h_read
      exact Measurable.prodMk h_meas1 h_meas2
    exact h_gsvec.comp h_arg
  have h_loc : ∀ x x' t, (∀ i, i < 2 * (t + 1) * d * B → x i = x' i) → triDraw d B x t = triDraw d B x' t := by
    intro x x' t h_eq
    dsimp [triDraw]
    congr
    ext i
    · -- first component of the pair
      have hi_val : (i : ℕ) < d := i.2
      have h_idx2_le : (2 * (t * d + i) + 1) * B ≤ 2 * (t + 1) * d * B := by
        have h : (2 * (t * d + i) + 1 : ℤ) ≤ (2 * (t + 1) * d : ℤ) := by
          have hi' : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi_val
          nlinarith
        have h_mul : (2 * (t * d + i) + 1 : ℤ) * (B : ℤ) ≤ (2 * (t + 1) * d : ℤ) * (B : ℤ) :=
          mul_le_mul_of_nonneg_right h (by exact_mod_cast hBpos.le)
        exact_mod_cast h_mul
      have h_facts1 := readCoins_facts x x' (2 * (t * d + i) * B) B
      rcases h_facts1 with ⟨_, _, _, h_loc1⟩
      have h_eq1 : AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B =
        AdversarialBco.BitRAM.readCoins x' (2 * (t * d + i) * B) B :=
        h_loc1 (fun j hj1 hj2 => h_eq j (by
          have h_j_lt : j < (2 * (t * d + i) + 1) * B := by
            have : 2 * (t * d + i) * B + B = (2 * (t * d + i) + 1) * B := by ring
            rw [this] at hj2
            exact hj2
          exact lt_of_lt_of_le h_j_lt h_idx2_le
        ))
      simp [h_eq1]
    · -- second component of the pair
      have hi_val : (i : ℕ) < d := i.2
      have h_idx2_le : (2 * (t * d + i) + 1) * B ≤ 2 * (t + 1) * d * B := by
        have h : (2 * (t * d + i) + 1 : ℤ) ≤ (2 * (t + 1) * d : ℤ) := by
          have hi' : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi_val
          nlinarith
        have h_mul : (2 * (t * d + i) + 1 : ℤ) * (B : ℤ) ≤ (2 * (t + 1) * d : ℤ) * (B : ℤ) :=
          mul_le_mul_of_nonneg_right h (by exact_mod_cast hBpos.le)
        exact_mod_cast h_mul
      have h_idx3_le : (2 * (t * d + i) + 2) * B ≤ 2 * (t + 1) * d * B := by
        have h : (2 * (t * d + i) + 2 : ℤ) ≤ (2 * (t + 1) * d : ℤ) := by
          have hi' : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi_val
          nlinarith
        have h_mul : (2 * (t * d + i) + 2 : ℤ) * (B : ℤ) ≤ (2 * (t + 1) * d : ℤ) * (B : ℤ) :=
          mul_le_mul_of_nonneg_right h (by exact_mod_cast hBpos.le)
        exact_mod_cast h_mul
      have h_facts2 := readCoins_facts x x' ((2 * (t * d + i) + 1) * B) B
      rcases h_facts2 with ⟨_, _, _, h_loc2⟩
      have h_eq2 : AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B =
        AdversarialBco.BitRAM.readCoins x' ((2 * (t * d + i) + 1) * B) B :=
        h_loc2 (fun j hj1 hj2 => h_eq j (by
          have h_j_lt : j < (2 * (t * d + i) + 2) * B := by
            have : (2 * (t * d + i) + 1) * B + B = (2 * (t * d + i) + 2) * B := by ring
            rw [this] at hj2
            exact hj2
          exact lt_of_lt_of_le h_j_lt h_idx3_le
        ))
      simp [h_eq2]
  exact ⟨h_bound, h_meas, h_loc⟩

end AdversarialBco.Bit.Aux_tri_draw_facts

namespace AdversarialBco.Bit.Aux_gs_cpl


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

/-- `2 x ≤ t x² + 1/t` for `t > 0`. -/
theorem gsc_amgm (t x : ℝ) (ht : 0 < t) : x ≤ (t * x ^ 2 + 1 / t) / 2 := by
  have h : 0 ≤ (t * x - 1) ^ 2 := sq_nonneg _
  have e : (t * x ^ 2 + 1 / t) / 2 - x = (t * x - 1) ^ 2 / (2 * t) := by field_simp; ring
  have : 0 ≤ (t * x - 1) ^ 2 / (2 * t) := div_nonneg h (by linarith)
  linarith

/-- A vector whose coordinates are all at most `e` in absolute value has norm at most `√d e`. -/
theorem gsc_norm_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (e : ℝ) (he : 0 ≤ e) (hv : ∀ i, |v i| ≤ e) :
    ‖v‖ ≤ Real.sqrt d * e := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, e ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
  have h2 : ∑ _i : Fin d, e ^ 2 = (d : ℝ) * e ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * e ^ 2) := Real.sqrt_le_sqrt (h2 ▸ h1)
    _ = Real.sqrt d * e := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq he]

theorem _root_.AdversarialBco.Bit.gs_cpl (d B : ℕ) (hB : 8 ≤ B) (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : LipschitzWith 1 F)
    (hF0 : ∀ z, |F z| ≤ ‖z‖) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    |∫ y, F (μ + A y) ∂((gsOmega d).map fun ω => gsVec d B (gsCells d B ω)) -
        ∫ y, F (μ + A y) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      ‖A‖ * (Real.sqrt d * gsEps B + d * (2 : ℝ) ^ (-(B : ℝ) / 2) * Real.sqrt (2 * d * B) +
        d * Real.sqrt ((2 : ℝ) ^ (-(B : ℝ) / 2))) := by
  classical
  haveI hU : IsProbabilityMeasure unif01 :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero,
      ENNReal.ofReal_one]⟩
  haveI hP : IsProbabilityMeasure (gsOmega d) := by unfold gsOmega; infer_instance
  -- the maps
  have hcell : Measurable (gsCell B) := by
    unfold gsCell
    exact (show Measurable (Int.toNat : ℤ → ℕ) from Measurable.of_discrete).comp
      ((measurable_sub_const 1).comp (Int.measurable_ceil.comp (measurable_const.mul measurable_id)))
  have hcells : Measurable (gsCells d B) := by
    unfold gsCells
    refine Measurable.of_eval fun i => ?_
    exact (hcell.comp (measurable_fst.comp (measurable_pi_apply i))).prodMk
      (hcell.comp (measurable_snd.comp (measurable_pi_apply i)))
  have hY : Measurable fun ω => gsVec d B (gsCells d B ω) := (measurable_of_countable (gsVec d B)).comp hcells
  have hbm : Measurable bmCos := by unfold bmCos; fun_prop
  have hG : Measurable fun ω : Fin d → ℝ × ℝ => (WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d)) :=
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i => hbm.comp (measurable_pi_apply i))
  have hco : ∀ i : Fin d, Measurable (fun v : EuclideanSpace ℝ (Fin d) => v i) := fun i =>
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable
  -- the objective
  have hφL : ∀ y z, |F (μ + A y) - F (μ + A z)| ≤ ‖A‖ * ‖y - z‖ := by
    intro y z
    have := hF.dist_le_mul (μ + A y) (μ + A z)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at this
    calc |F (μ + A y) - F (μ + A z)| ≤ ‖μ + A y - (μ + A z)‖ := this
      _ = ‖A (y - z)‖ := by rw [map_sub, add_sub_add_left_eq_sub]
      _ ≤ ‖A‖ * ‖y - z‖ := A.le_opNorm _
  have hφc : Continuous fun y => F (μ + A y) := hF.continuous.comp (continuous_const.add A.continuous)
  have hφb : ∀ y, ‖F (μ + A y)‖ ≤ ‖μ‖ + ‖A‖ * ‖y‖ := by
    intro y
    rw [Real.norm_eq_abs]
    calc |F (μ + A y)| ≤ ‖μ + A y‖ := hF0 _
      _ ≤ ‖μ‖ + ‖A y‖ := norm_add_le _ _
      _ ≤ ‖μ‖ + ‖A‖ * ‖y‖ := by gcongr; exact A.le_opNorm y
  -- the Gaussian side
  have hgl := gs_g_law d
  have hG2 : Integrable (fun ω : Fin d → ℝ × ℝ => ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2)
      (gsOmega d) := by
    have h := AdversarialBco.Poly.SIF.integrable_norm_sq (d := d)
    rw [← hgl] at h
    exact (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable hG.aemeasurable).1 h
  have hG2i : ∫ ω, ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ∂(gsOmega d) = d := by
    have h := AdversarialBco.Poly.SIF.integral_norm_sq (d := d)
    rw [← hgl, integral_map hG.aemeasurable
      (show Continuous fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 by fun_prop).aestronglyMeasurable] at h
    exact h
  have hG1 : Integrable (fun ω : Fin d → ℝ × ℝ => ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖)
      (gsOmega d) := by
    refine Integrable.mono' ((integrable_const 1).add hG2) (continuous_norm.measurable.comp hG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have := gsc_amgm 1 ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ one_pos
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ - 1)]
  -- the sure bound
  have hYb : ∀ᵐ ω ∂(gsOmega d), ‖gsVec d B (gsCells d B ω)‖ ≤ Real.sqrt (2 * d * B) := by
    filter_upwards [gs_cells_ae d B] with ω hω
    exact gs_sure d B hB _ hω
  -- integrability of the two objectives
  have hIY : Integrable (fun ω => F (μ + A (gsVec d B (gsCells d B ω)))) (gsOmega d) := by
    refine Integrable.of_bound (hφc.measurable.comp hY).aestronglyMeasurable (‖μ‖ + ‖A‖ * Real.sqrt (2 * d * B)) ?_
    filter_upwards [hYb] with ω hω
    exact (hφb _).trans (by gcongr)
  have hIG : Integrable (fun ω : Fin d → ℝ × ℝ => F (μ + A (WithLp.toLp 2 fun i => bmCos (ω i)))) (gsOmega d) := by
    refine Integrable.mono' ((integrable_const ‖μ‖).add (hG1.const_mul ‖A‖)) (hφc.measurable.comp hG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    exact hφb _
  -- the two integrals on the coupling space
  rw [integral_map hY.aemeasurable hφc.aestronglyMeasurable, ← hgl,
    integral_map hG.aemeasurable hφc.aestronglyMeasurable, ← integral_sub hIY hIG]
  -- the bad event
  set S := {ω : Fin d → ℝ × ℝ | ∃ i, gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} with hSdef
  have hSm : MeasurableSet S := by
    have : S = ⋃ i, {ω : Fin d → ℝ × ℝ | gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)|} := by
      ext ω; simp [hSdef]
    rw [this]
    exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (((hco i).comp hY).sub (hbm.comp (measurable_pi_apply i))))
  have hPS := gs_bad d B hB
  rw [← hSdef] at hPS
  -- the constants
  set q : ℝ := (2 : ℝ) ^ (-(B : ℝ) / 2) with hq
  have hq0 : 0 < q := by positivity
  set t : ℝ := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hq0
  have htt : t * t = q := Real.mul_self_sqrt hq0.le
  set c1 : ℝ := Real.sqrt (2 * d * B) with hc1
  have hc10 : 0 ≤ c1 := Real.sqrt_nonneg _
  have hE0 : 0 ≤ gsEps B := by unfold gsEps; positivity
  set c0 : ℝ := Real.sqrt d * gsEps B with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set k : ℝ := c1 + 1 / (2 * t) with hk
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂(gsOmega d),
      |F (μ + A (gsVec d B (gsCells d B ω))) - F (μ + A (WithLp.toLp 2 fun i => bmCos (ω i)))| ≤
        ‖A‖ * (c0 + k * S.indicator 1 ω +
          t / 2 * ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
    filter_upwards [hYb] with ω hω
    refine (hφL _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    set g : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => bmCos (ω i) with hg
    have hg2 : 0 ≤ t / 2 * ‖g‖ ^ 2 := by positivity
    by_cases hωS : ω ∈ S
    · rw [Set.indicator_of_mem hωS, Pi.one_apply, mul_one]
      have ham := gsc_amgm t ‖g‖ ht0
      calc ‖gsVec d B (gsCells d B ω) - g‖ ≤ ‖gsVec d B (gsCells d B ω)‖ + ‖g‖ := norm_sub_le _ _
        _ ≤ c1 + (t * ‖g‖ ^ 2 + 1 / t) / 2 := add_le_add hω ham
        _ = c1 + 1 / (2 * t) + t / 2 * ‖g‖ ^ 2 := by ring
        _ ≤ c0 + k + t / 2 * ‖g‖ ^ 2 := by rw [hk]; linarith
    · rw [Set.indicator_of_notMem hωS, mul_zero, add_zero]
      have hcoord : ∀ i, |(gsVec d B (gsCells d B ω) - g) i| ≤ gsEps B := by
        intro i
        have : ¬ gsEps B < |gsVec d B (gsCells d B ω) i - bmCos (ω i)| := fun h => hωS ⟨i, h⟩
        rw [PiLp.sub_apply]
        exact not_lt.1 this
      have := gsc_norm_le _ _ hE0 hcoord
      linarith
  -- integrate
  have hRint : Integrable (fun ω => ‖A‖ * (c0 + k * S.indicator 1 ω +
      t / 2 * ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2)) (gsOmega d) :=
    (((integrable_const c0).add ((integrable_const (1 : ℝ)).indicator hSm |>.const_mul k)).add
      (hG2.const_mul (t / 2))).const_mul ‖A‖
  have hRval : ∫ ω, ‖A‖ * (c0 + k * S.indicator 1 ω +
      t / 2 * ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2) ∂(gsOmega d) =
      ‖A‖ * (c0 + k * (gsOmega d).real S + t / 2 * d) := by
    have hIk : Integrable (fun ω => k * S.indicator 1 ω) (gsOmega d) :=
      ((integrable_const (1 : ℝ)).indicator hSm).const_mul k
    have hIc : Integrable (fun ω => c0 + k * S.indicator 1 ω) (gsOmega d) := (integrable_const c0).add hIk
    have hIg : Integrable (fun ω => t / 2 *
        ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2) (gsOmega d) := hG2.const_mul (t / 2)
    rw [integral_const_mul, integral_add hIc hIg, integral_add (integrable_const c0) hIk, integral_const_mul k,
      integral_const_mul (t / 2), integral_indicator_one hSm, integral_const, hG2i]
    simp
  calc |∫ ω, F (μ + A (gsVec d B (gsCells d B ω))) - F (μ + A (WithLp.toLp 2 fun i => bmCos (ω i))) ∂(gsOmega d)|
      ≤ ∫ ω, |F (μ + A (gsVec d B (gsCells d B ω))) - F (μ + A (WithLp.toLp 2 fun i => bmCos (ω i)))| ∂(gsOmega d) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, ‖A‖ * (c0 + k * S.indicator 1 ω +
          t / 2 * ‖(WithLp.toLp 2 fun i => bmCos (ω i) : EuclideanSpace ℝ (Fin d))‖ ^ 2) ∂(gsOmega d) :=
        integral_mono_ae (hIY.sub hIG).abs hRint hpt
    _ = ‖A‖ * (c0 + k * (gsOmega d).real S + t / 2 * d) := hRval
    _ ≤ ‖A‖ * (c0 + k * (d * q) + t / 2 * d) := by
        gcongr
    _ = ‖A‖ * (Real.sqrt d * gsEps B + d * q * Real.sqrt (2 * d * B) + d * Real.sqrt q) := by
        congr 1
        rw [hk, hc0, hc1, ← ht]
        field_simp
        rw [← htt]
        ring

end AdversarialBco.Bit.Aux_gs_cpl

namespace AdversarialBco.Bit.Aux_triU_meas2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.triU_meas2 (d m : ℕ) :
    Measurable (fun q : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d) =>
      triU q.1 q.2.1 q.2.2) := by
  -- Unfold the definitions of triU and triQ
  unfold triU triQ
  -- Goal: Measurable (fun q => ∑ k, if 0 < inner ℝ (q.1 k) q.2.2 / q.2.1 k ∧ ... then (q.2.1 k)⁻¹ • q.1 k else 0)
  -- Use Finset.measurable_sum over Fin m
  refine Finset.measurable_sum Finset.univ ?_
  intro k hk
  -- For each k, we need to show the if-then-else is measurable
  -- Define the measurable functions we'll need
  let α := fun q : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d) => q.1
  let β := fun q : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d) => q.2.1
  let z := fun q : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d) => q.2.2
  have hα : Measurable α := measurable_fst
  have hβ : Measurable β := measurable_fst.comp measurable_snd
  have hz : Measurable z := measurable_snd.comp measurable_snd
  have hαk (k' : Fin m) : Measurable (fun q => α q k') :=
    (measurable_pi_apply k').comp hα
  have hβk (k' : Fin m) : Measurable (fun q => β q k') :=
    (measurable_pi_apply k').comp hβ
  -- f k' q = inner ℝ (α q k') (z q) / β q k'
  let f (k' : Fin m) (q : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d)) : ℝ :=
    inner ℝ (α q k') (z q) / β q k'
  have hf (k' : Fin m) : Measurable (f k') := by
    dsimp [f]
    refine Measurable.div ?_ ?_
    · exact Measurable.inner (hαk k') hz
    · exact hβk k'
  -- The condition C k q = 0 < f k q ∧ (∀ k', f k' q ≤ f k q) ∧ (∀ k', k' < k → f k' q < f k q)
  -- Each part is a measurable set
  have h_cond : MeasurableSet {q | 0 < f k q ∧ (∀ k', f k' q ≤ f k q) ∧ (∀ k', k' < k → f k' q < f k q)} := by
    -- First conjunct: 0 < f k q
    have h1 : MeasurableSet {q | 0 < f k q} :=
      measurableSet_lt measurable_const (hf k)
    -- Second conjunct: ∀ k', f k' q ≤ f k q  (finite conjunction over Fin m)
    have h2 : MeasurableSet {q | ∀ k', f k' q ≤ f k q} := by
      -- Convert ∀ k' to intersection over Finset.univ
      have : {q | ∀ k', f k' q ≤ f k q} = ⋂ k' ∈ Finset.univ, {q | f k' q ≤ f k q} := by
        ext q; simp
      rw [this]
      refine Finset.measurableSet_biInter Finset.univ ?_
      intro k' hk'
      exact measurableSet_le (hf k') (hf k)
    -- Third conjunct: ∀ k', k' < k → f k' q < f k q  (finite conjunction over k' < k)
    have h3 : MeasurableSet {q | ∀ k', k' < k → f k' q < f k q} := by
      have : {q | ∀ k', k' < k → f k' q < f k q} =
          ⋂ k' ∈ (Finset.univ.filter fun k' => k' < k), {q | f k' q < f k q} := by
        ext q; simp [Finset.mem_filter]
      rw [this]
      refine Finset.measurableSet_biInter (Finset.univ.filter fun k' => k' < k) ?_
      intro k' hk'
      exact measurableSet_lt (hf k') (hf k)
    -- Intersection of three measurable sets
    have h_eq : {q | 0 < f k q ∧ (∀ k', f k' q ≤ f k q) ∧ (∀ k', k' < k → f k' q < f k q)} =
        ({q | 0 < f k q} ∩ {q | ∀ k', f k' q ≤ f k q}) ∩ {q | ∀ k', k' < k → f k' q < f k q} := by
      ext q; simp [and_assoc]
    rw [h_eq]
    exact MeasurableSet.inter (MeasurableSet.inter h1 h2) h3
  -- The "then" branch: (β q k)⁻¹ • α q k
  have h_then : Measurable (fun q => (β q k)⁻¹ • α q k) := by
    have h_inv : Measurable (fun q => (β q k)⁻¹) := Measurable.inv (hβk k)
    refine Measurable.smul (f := fun q => (β q k)⁻¹) (g := fun q => α q k) h_inv (hαk k)
  -- The "else" branch: 0
  have h_else : Measurable (fun _ : (Fin m → EuclideanSpace ℝ (Fin d)) × (Fin m → ℝ) × EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d))) :=
    measurable_const
  -- Apply Measurable.ite
  exact Measurable.ite h_cond h_then h_else

end AdversarialBco.Bit.Aux_triU_meas2

namespace AdversarialBco.Bit.Aux_tri_V_meas2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_V_meas2 {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (u : Θ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : Measurable (fun q : Θ × EuclideanSpace ℝ (Fin d) => u q.1 q.2)) :
    Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) => triV (u q.1) q.2.1 q.2.2) := by
  have hz : Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) => pgMu q.2.1 + pgOp q.2.1 q.2.2) :=
    (pg_continuous d).2.2.measurable.comp measurable_snd
  have huz : Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) =>
      u q.1 (pgMu q.2.1 + pgOp q.2.1 q.2.2)) :=
    hu.comp (measurable_fst.prodMk hz)
  have hco : ∀ i : Fin d, Measurable (fun v : EuclideanSpace ℝ (Fin d) => v i) := fun i =>
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable
  have hmat : ∀ i j, Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) => pgMat q.2.1 i j) :=
    fun i j => (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d ⊕ Fin d × Fin d => ℝ)
      (Sum.inr (i, j))).measurable.comp (measurable_fst.comp measurable_snd)
  have hF : Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) =>
      (Sum.elim (fun i => u q.1 (pgMu q.2.1 + pgOp q.2.1 q.2.2) i)
        (fun p => (if p.2 ≤ p.1 then u q.1 (pgMu q.2.1 + pgOp q.2.1 q.2.2) p.1 * q.2.2 p.2 else 0) -
          (if p.1 = p.2 then pgKappa / d / pgMat q.2.1 p.1 p.1 else 0)) : Fin d ⊕ Fin d × Fin d → ℝ)) := by
    refine measurable_pi_iff.2 fun k => ?_
    rcases k with i | ⟨i, j⟩
    · exact (hco i).comp huz
    · simp only [Sum.elim_inr]
      refine Measurable.sub ?_ ?_
      · by_cases hji : j ≤ i
        · simp only [hji, if_true]
          exact ((hco i).comp huz).mul ((hco j).comp (measurable_snd.comp measurable_snd))
        · simp only [hji, if_false]
          exact measurable_const
      · by_cases hij : i = j
        · simp only [hij, if_true]
          exact measurable_const.div (hmat j j)
        · simp only [hij, if_false]
          exact measurable_const
  exact (WithLp.measurable_toLp 2 _).comp hF

end AdversarialBco.Bit.Aux_tri_V_meas2

namespace AdversarialBco.Bit.Aux_triIter_meas2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

lemma triClip_continuous {d : ℕ} (r a b : ℝ) : Continuous (triClip (d := d) r a b) := by
  have h_eq : triClip (d := d) r a b = (WithLp.toLp 2 : ((Fin d ⊕ Fin d × Fin d) → ℝ) → PgSp d) ∘
    (fun (x : PgSp d) (k : Fin d ⊕ Fin d × Fin d) => max (triLo r a b k) (min (triHi r b k) (x k))) := by
    ext x k
    simp [triClip]
  rw [h_eq]
  apply Continuous.comp
  · exact PiLp.continuous_toLp 2 (fun _ : Fin d ⊕ Fin d × Fin d => ℝ)
  · refine continuous_pi ?_
    intro k
    have hx : Continuous (fun (x : PgSp d) => x k) := by
      simpa using PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d × Fin d => ℝ) k
    refine Continuous.max continuous_const ?_
    refine Continuous.min continuous_const hx

lemma triClip_measurable {d : ℕ} (r a b : ℝ) : Measurable (triClip (d := d) r a b) :=
  (triClip_continuous r a b).measurable

theorem _root_.AdversarialBco.Bit.triIter_meas2 {d : ℕ} {Θ : Type*} [MeasurableSpace Θ] (r a b s : ℝ)
    (Vt : Θ → PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (hVt : Measurable (fun q : Θ × PgSp d × EuclideanSpace ℝ (Fin d) => Vt q.1 q.2.1 q.2.2)) :
    (∀ t, Measurable (fun q : Θ × (ℕ → EuclideanSpace ℝ (Fin d)) => triIter r a b s (Vt q.1) q.2 t)) ∧
      ∀ N, Measurable (fun q : Θ × (ℕ → EuclideanSpace ℝ (Fin d)) => triAvg r a b s (Vt q.1) q.2 N) := by
  have h_iter : ∀ t, Measurable (fun q : Θ × (ℕ → EuclideanSpace ℝ (Fin d)) => triIter r a b s (Vt q.1) q.2 t) := by
    intro t
    induction' t with t ih
    · -- t = 0: constant pgPack 0 1
      have h_eq : (fun q : Θ × (ℕ → EuclideanSpace ℝ (Fin d)) => triIter r a b s (Vt q.1) q.2 0) =
          fun _ => pgPack 0 1 := by
        ext q; simp [triIter]
      rw [h_eq]
      exact measurable_const
    · -- t+1
      simp [triIter]
      apply (triClip_measurable r a b).comp
      apply Measurable.sub
      · exact ih
      · -- Measurable (fun q => s • Vt q.1 (triIter r a b s (Vt q.1) q.2 t) (q.2 t))
        have h_triple : Measurable (fun (q : Θ × (ℕ → EuclideanSpace ℝ (Fin d))) =>
          (q.1, triIter r a b s (Vt q.1) q.2 t, q.2 t)) := by
          refine Measurable.prod measurable_fst ?_
          refine Measurable.prod ?_ ?_
          · exact ih
          · exact (measurable_pi_apply t).comp measurable_snd
        have hV_meas : Measurable (fun (q : Θ × (ℕ → EuclideanSpace ℝ (Fin d))) =>
            Vt q.1 (triIter r a b s (Vt q.1) q.2 t) (q.2 t)) := by
          have := hVt.comp h_triple
          convert this using 1
          ext q
          simp
        let g := fun (q : Θ × (ℕ → EuclideanSpace ℝ (Fin d))) =>
          Vt q.1 (triIter r a b s (Vt q.1) q.2 t) (q.2 t)
        have hg : Measurable g := hV_meas
        have : (fun q => s • g q) = s • g := by rfl
        rw [this]
        exact Measurable.const_smul hg s
  have h_avg : ∀ N, Measurable (fun q : Θ × (ℕ → EuclideanSpace ℝ (Fin d)) => triAvg r a b s (Vt q.1) q.2 N) := by
    intro N
    simp [triAvg]
    let g := fun (q : Θ × (ℕ → EuclideanSpace ℝ (Fin d))) =>
      ∑ t ∈ Finset.range N, triIter r a b s (Vt q.1) q.2 t
    have hg : Measurable g := by
      apply Finset.measurable_sum
      intro i hi
      exact h_iter i
    have : (fun q => (N : ℝ)⁻¹ • g q) = (N : ℝ)⁻¹ • g := by rfl
    rw [this]
    exact Measurable.const_smul hg (N : ℝ)⁻¹
  exact ⟨h_iter, h_avg⟩

end AdversarialBco.Bit.Aux_triIter_meas2

namespace AdversarialBco.Bit.Aux_tri_cube_rows


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_cube_rows {d m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    {y | ∀ k, inner ℝ (triRowsA A k) y ≤ triRowsB b c s k} = {y | ∀ k, inner ℝ (A k) y ≤ b k} ∩ triCube c s := by
  ext y
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k
      have := h (Fin.castAdd (d + d) k)
      simpa [triRowsA, triRowsB, Fin.append_left, -Fin.natAdd_eq_addNat] using this
    · intro i
      have hpos : inner ℝ (EuclideanSpace.single i 1) y ≤ c i + s := by
        have := h (Fin.natAdd m (Fin.castAdd d i))
        simpa [triRowsA, triRowsB, Fin.append_right, Fin.append_left, -Fin.natAdd_eq_addNat] using this
      have hneg : inner ℝ (-EuclideanSpace.single i 1) y ≤ s - c i := by
        have := h (Fin.natAdd m (Fin.natAdd d i))
        simpa [triRowsA, triRowsB, Fin.append_right, -Fin.natAdd_eq_addNat] using this
      have hypos : y i ≤ c i + s := by
        simpa [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using hpos
      have hyneg : -y i ≤ s - c i := by
        simpa [EuclideanSpace.inner_single_left, inner_neg_left, conj_trivial, one_mul] using hneg
      rw [abs_le]
      constructor <;> linarith
  · intro h
    rcases h with ⟨hA, hc⟩
    rw [Set.mem_setOf_eq]
    rw [Fin.forall_fin_add]
    refine ⟨?_, ?_⟩
    · intro k
      simpa [triRowsA, triRowsB, Fin.append_left, -Fin.natAdd_eq_addNat] using hA k
    · rw [Fin.forall_fin_add]
      refine ⟨?_, ?_⟩
      · intro i
        have hy_le : y i ≤ c i + s := by
          have hci := hc i
          rw [abs_le] at hci
          rcases hci with ⟨hle, _⟩
          linarith
        simpa [triRowsA, triRowsB, Fin.append_right, Fin.append_left, EuclideanSpace.inner_single_left, conj_trivial, one_mul, -Fin.natAdd_eq_addNat] using hy_le
      · intro i
        have hneg_y : -y i ≤ s - c i := by
          have hci := hc i
          rw [abs_le] at hci
          rcases hci with ⟨_, hge⟩
          linarith
        simpa [triRowsA, triRowsB, Fin.append_right, EuclideanSpace.inner_single_left, inner_neg_left, conj_trivial, one_mul, -Fin.natAdd_eq_addNat] using hneg_y

end AdversarialBco.Bit.Aux_tri_cube_rows

namespace AdversarialBco.Bit.Aux_tri_stage_body


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_stage_body {d : ℕ} (Ki K' : Set (EuclideanSpace ℝ (Fin d))) (hc : Convex ℝ K')
    (hcl : IsClosed K') (hKK : Ki ⊆ K') (c : EuclideanSpace ℝ (Fin d)) (hcK : c ∈ Ki)
    (hmid : ∀ x ∈ K', midpoint ℝ c x ∈ Ki) (P : PgSp d) (hP : (pgMat P).det ≠ 0) (R : ℝ)
    (h1 : Metric.closedBall 0 1 ⊆ posBody Ki (pgMu P) (pgOp P))
    (hR : posBody Ki (pgMu P) (pgOp P) ⊆ Metric.closedBall 0 R) :
    PgBody (posBody K' (pgMu P) (pgOp P)) (3 * R) := by
  obtain ⟨hcv, hcl'⟩ := posBody_closed K' hc hcl (pgMu P) (pgOp P)
  have hdet : IsUnit (pgMat P).det := isUnit_iff_ne_zero.2 hP
  let Bi : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat P)⁻¹
  have hAB : ∀ v, pgOp P (Bi v) = v := by
    intro v
    rw [pgOp_apply]
    show WithLp.toLp 2 (pgMat P *ᵥ ((pgMat P)⁻¹ *ᵥ WithLp.ofLp v)) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, WithLp.toLp_ofLp]
  have hBA : ∀ v, Bi (pgOp P v) = v := by
    intro v
    rw [pgOp_apply]
    show WithLp.toLp 2 ((pgMat P)⁻¹ *ᵥ WithLp.ofLp (WithLp.toLp 2 (pgMat P *ᵥ WithLp.ofLp v))) = v
    rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec,
      WithLp.toLp_ofLp]
  have hin : ∀ w, pgMu P + w ∈ Ki → ‖Bi w‖ ≤ R := by
    intro w hw
    have hm : Bi w ∈ posBody Ki (pgMu P) (pgOp P) := by
      show pgMu P + pgOp P (Bi w) ∈ Ki
      rw [hAB]
      exact hw
    have := hR hm
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  refine ⟨hcv, hcl', h1.trans fun y hy => hKK hy, fun y hy => ?_⟩
  have hy' : pgMu P + pgOp P y ∈ K' := hy
  set x := pgMu P + pgOp P y with hx
  have hym := hin (midpoint ℝ c x - pgMu P) (by rw [add_sub_cancel]; exact hmid x hy')
  have hyc := hin (c - pgMu P) (by rw [add_sub_cancel]; exact hcK)
  have hyeq : y = (2 : ℝ) • Bi (midpoint ℝ c x - pgMu P) - Bi (c - pgMu P) := by
    rw [← map_smul, ← map_sub]
    have e : (2 : ℝ) • (midpoint ℝ c x - pgMu P) - (c - pgMu P) = pgOp P y := by
      rw [midpoint_eq_smul_add, hx, invOf_eq_inv]
      module
    rw [e, hBA]
  rw [Metric.mem_closedBall, dist_zero_right, hyeq]
  calc ‖(2 : ℝ) • Bi (midpoint ℝ c x - pgMu P) - Bi (c - pgMu P)‖
      ≤ ‖(2 : ℝ) • Bi (midpoint ℝ c x - pgMu P)‖ + ‖Bi (c - pgMu P)‖ := norm_sub_le _ _
    _ = 2 * ‖Bi (midpoint ℝ c x - pgMu P)‖ + ‖Bi (c - pgMu P)‖ := by rw [norm_smul]; norm_num
    _ ≤ 2 * R + R := by linarith
    _ = 3 * R := by ring

end AdversarialBco.Bit.Aux_tri_stage_body

namespace AdversarialBco.Bit.Aux_tri_stage0_body


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

section
variable {d : ℕ}

theorem t0b_pgMat_pgPack_r0_one (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) :
    pgMat (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) = r0 • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i j
  simp [pgMat, pgPack]

theorem t0b_pgMu_pgPack (c : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    pgMu (pgPack c M) = c := by
  ext i
  simp [pgMu, pgPack]

theorem t0b_pgOp_pgPack_r0_one (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    pgOp (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) v = r0 • v := by
  simp [pgOp, t0b_pgMat_pgPack_r0_one c r0]

theorem t0b_convex_triCube (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Convex ℝ (triCube c s) := by
  have h_eq : triCube c s = ⋂ i, {y | |y i - c i| ≤ s} := by
    ext y; simp [triCube]
  rw [h_eq]
  refine convex_iInter fun i => ?_
  have h_abs : {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} = {y | -(s : ℝ) ≤ y i - c i} ∩ {y | y i - c i ≤ s} := by
    ext y; simp [abs_le]
  rw [h_abs]
  refine Convex.inter ?_ ?_
  · have h_linear : IsLinearMap ℝ (fun (y : EuclideanSpace ℝ (Fin d)) => y i) := by
      refine ⟨fun x y => ?_, fun r x => ?_⟩
      · simp
      · simp
    have : {y : EuclideanSpace ℝ (Fin d) | -(s : ℝ) ≤ y i - c i} = {y | c i - s ≤ y i} := by
      ext y; simp
    rw [this]
    exact convex_halfSpace_ge h_linear (c i - s)
  · have h_linear : IsLinearMap ℝ (fun (y : EuclideanSpace ℝ (Fin d)) => y i) := by
      refine ⟨fun x y => ?_, fun r x => ?_⟩
      · simp
      · simp
    have : {y : EuclideanSpace ℝ (Fin d) | y i - c i ≤ s} = {y | y i ≤ c i + s} := by
      ext y; simp [add_comm]
    rw [this]
    exact convex_halfSpace_le h_linear (c i + s)

theorem t0b_closed_triCube (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) : IsClosed (triCube c s) := by
  have h_eq : triCube c s = ⋂ i, {y | |y i - c i| ≤ s} := by
    ext y; simp [triCube]
  rw [h_eq]
  refine isClosed_iInter fun i => ?_
  have h_cont : Continuous (fun (y : EuclideanSpace ℝ (Fin d)) => |y i - c i|) := by
    refine Continuous.abs (Continuous.sub ?_ continuous_const)
    simpa using PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) (i := i)
  have : {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} = {y | |y i - c i| ≤ (fun _ => s) y} := by
    ext y; simp
  rw [this]
  exact isClosed_le h_cont (continuous_const)

end

theorem _root_.AdversarialBco.Bit.tri_stage0_body {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (hr0 : 0 < r0) (hK0 : Metric.closedBall c r0 ⊆ K) :
    (pgMat (pgPack c (r0 • 1) : PgSp d)).det ≠ 0 ∧
      PgBody (posBody (K ∩ triCube c (2 * r0)) (pgMu (pgPack c (r0 • 1) : PgSp d))
        (pgOp (pgPack c (r0 • 1) : PgSp d))) (2 * Real.sqrt d) := by
  let P := pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))
  have hmat : pgMat P = r0 • (1 : Matrix (Fin d) (Fin d) ℝ) := t0b_pgMat_pgPack_r0_one c r0
  have hmu_explicit : pgMu (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) = c := t0b_pgMu_pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))
  have h_op_explicit : ∀ v, pgOp (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) v = r0 • v := t0b_pgOp_pgPack_r0_one c r0
  have h_det : (pgMat P).det ≠ 0 := by
    rw [hmat]
    rw [Matrix.det_smul, Matrix.det_one]
    exact mul_ne_zero (pow_ne_zero (Fintype.card (Fin d)) hr0.ne.symm) (by norm_num)
  have h_pgbody : PgBody (posBody (K ∩ triCube c (2 * r0)) (pgMu (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ)))) (pgOp (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))))) (2 * Real.sqrt d) := by
    rw [hmu_explicit]
    let S := posBody (K ∩ triCube c (2 * r0)) c (pgOp (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))))
    have hS_eq : S = {z | c + r0 • z ∈ K ∧ ∀ i, |r0 * z i| ≤ 2 * r0} := by
      ext z
      simp [S, posBody, triCube, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left, h_op_explicit z]
    have h_cube_convex : Convex ℝ (triCube c (2 * r0)) := t0b_convex_triCube c (2 * r0)
    have h_cube_closed : IsClosed (triCube c (2 * r0)) := t0b_closed_triCube c (2 * r0)
    have h_inter_convex : Convex ℝ (K ∩ triCube c (2 * r0)) := Convex.inter hKc h_cube_convex
    have h_inter_closed : IsClosed (K ∩ triCube c (2 * r0)) := IsClosed.inter hKcl h_cube_closed
    have h_posbody_conv_closed := posBody_closed (K ∩ triCube c (2 * r0)) h_inter_convex h_inter_closed c (pgOp (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))))
    rcases h_posbody_conv_closed with ⟨h_conv, h_closed⟩
    have h_ball1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ S := by
      intro z hz
      have hznorm : ‖z‖ ≤ 1 := by
        rw [Metric.mem_closedBall] at hz
        -- hz : dist z 0 ≤ 1
        -- dist z 0 = ‖z - 0‖ = ‖z‖
        -- So we can use `dist_eq_norm` to convert
        -- Actually, `Metric.mem_closedBall` gives `dist z 0 ≤ 1`
        -- And `dist z 0 = ‖z‖` by `dist_eq_norm`
        -- Let's use `simpa [dist_eq_norm] using hz`
        simpa [dist_eq_norm] using hz
      rw [hS_eq]
      refine ⟨?_, ?_⟩
      · have hdist : dist (c + r0 • z) c ≤ r0 := by
          rw [dist_eq_norm]
          -- ‖(c + r0 • z) - c‖ = ‖r0 • z‖ = r0 * ‖z‖
          -- Since ‖z‖ ≤ 1 and r0 > 0, we have r0 * ‖z‖ ≤ r0
          calc
            ‖(c + r0 • z) - c‖ = ‖r0 • z‖ := by simp [add_sub_cancel_left]
            _ = r0 * ‖z‖ := by simp [norm_smul, hr0.le]
            _ ≤ r0 * 1 := mul_le_mul_of_nonneg_left hznorm hr0.le
            _ = r0 := mul_one _
        have hmem : c + r0 • z ∈ Metric.closedBall c r0 := by
          rw [Metric.mem_closedBall]
          exact hdist
        exact hK0 hmem
      · intro i
        have hzi : |z i| ≤ ‖z‖ := by
          simpa using PiLp.norm_apply_le z i
        have : |r0 * z i| = r0 * |z i| := by
          rw [abs_mul, abs_of_pos hr0]
        rw [this]
        -- Need: r0 * |z i| ≤ 2 * r0
        -- Since |z i| ≤ ‖z‖ ≤ 1 ≤ 2, we have r0 * |z i| ≤ r0 * 2 = 2 * r0
        have : |z i| ≤ 2 := by linarith
        nlinarith
    have h_ball2 : S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 * Real.sqrt d) := by
      intro z hz
      rw [hS_eq] at hz
      rcases hz with ⟨hKz, hcube⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hzi2 : ∀ i, (z i)^2 ≤ 4 := by
        intro i
        have hi := hcube i
        have h_abs : |r0 * z i| = r0 * |z i| := by
          rw [abs_mul, abs_of_pos hr0]
        rw [h_abs] at hi
        -- hi : r0 * |z i| ≤ 2 * r0
        -- Since r0 > 0, we can divide both sides by r0
        have h_zi_abs : |z i| ≤ 2 := by
          -- From hi: r0 * |z i| ≤ 2 * r0 = r0 * 2
          -- Since r0 > 0, we can cancel r0
          -- Using `le_of_mul_le_mul_left` or `nlinarith`
          -- Let's use `nlinarith` which handles this
          nlinarith
        -- Now from |z i| ≤ 2, we need (z i)^2 ≤ 4
        -- We have: (z i)^2 = |z i|^2 (by `sq_abs`)
        -- And |z i|^2 ≤ 2^2 = 4
        -- Use `sq_le_sq` which gives: a^2 ≤ b^2 ↔ |a| ≤ |b|
        -- So we need to show |z i| ≤ |2|
        -- Since |2| = 2, this is exactly h_zi_abs
        have h_sq : (z i)^2 ≤ (2 : ℝ)^2 := by
          -- Using `sq_le_sq`:
          -- `(sq_le_sq (a := z i) (b := 2)).mpr` needs `|z i| ≤ |2|`
          -- `|2| = 2` by `abs_of_pos` (since 2 > 0)
          have h_abs_two : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
          -- Actually, `sq_le_sq` is a lemma `a^2 ≤ b^2 ↔ |a| ≤ |b|`
          -- So `.mpr` takes `|a| ≤ |b|` and gives `a^2 ≤ b^2`
          -- We have `h_zi_abs : |z i| ≤ 2`
          -- And `|2| = 2`
          -- So `|z i| ≤ |2|` follows
          have h_abs_le : |z i| ≤ |(2 : ℝ)| := by
            rwa [abs_of_pos (by norm_num : 0 < (2 : ℝ))]
          exact ((sq_le_sq (a := z i) (b := 2)).mpr h_abs_le)
        -- Now (2 : ℝ)^2 = 4
        simpa [sq, show (2 : ℝ)^2 = 4 by norm_num] using h_sq
      have hnorm_sq : ‖z‖^2 ≤ (2 * Real.sqrt d)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          ∑ i : Fin d, (z i)^2 ≤ ∑ i : Fin d, (4 : ℝ) := Finset.sum_le_sum fun i _ => hzi2 i
          _ = (Fintype.card (Fin d) : ℝ) * 4 := by simp
          _ = (d : ℝ) * 4 := by simp
          _ = 4 * (d : ℝ) := mul_comm _ _
          _ = (2 * Real.sqrt d)^2 := by
            have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
            calc
              4 * (d : ℝ) = 4 * ((Real.sqrt (d : ℝ)) ^ 2) := by rw [Real.sq_sqrt hd]
              _ = (2 * Real.sqrt d)^2 := by ring
      have h_nonneg : 0 ≤ ‖z‖ := norm_nonneg _
      have h_nonneg_sqrt : 0 ≤ 2 * Real.sqrt d := by positivity
      rw [sub_zero]
      have h_sq : ‖z‖^2 ≤ (2 * Real.sqrt d)^2 := hnorm_sq
      have := (sq_le_sq (a := ‖z‖) (b := 2 * Real.sqrt d)).mp h_sq
      simpa [abs_of_nonneg h_nonneg, abs_of_nonneg h_nonneg_sqrt] using this
    exact ⟨h_conv, h_closed, h_ball1, h_ball2⟩
  exact And.intro h_det h_pgbody

end AdversarialBco.Bit.Aux_tri_stage0_body
