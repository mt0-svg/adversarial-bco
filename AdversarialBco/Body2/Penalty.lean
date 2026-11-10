/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Arith

@[expose] public section

/-!
# Lemma 4.1 and the choice of `t_0` in Proposition 2.2

The functions `T(z)`, `ι_0(z)`, `s_0(z)`, `Θ(z)` and `need(z)` of Lemma 4.1, the bounds on `(1 + T(z))^2`
and `Θ(z)` linear in `ln(z/2)`, the bound `need(z) ≤ 10^8 z^10` for `z ≥ 2`, the tail term at
`t_0 = σ (2 ln⁺(8 n^2 σ^2/ι))^{1/2}`, and the reduction of the penalty condition to `need(z)`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2

/-- `C_1 = 52 (π/2)^{1/2} (17/16) (1 + C')` with `C' = 10^8` (Lemma 4.1). -/
noncomputable def C1 : ℝ := 52 * Real.sqrt (Real.pi / 2) * (17 / 16) * (1 + 10 ^ 8)

/-- `T(z) = (2 ln(C_1 z^12))^{1/2}`. -/
noncomputable def Tz (z : ℝ) : ℝ := Real.sqrt (2 * Real.log (C1 * z ^ 12))

/-- `ι_0(z) = 1/(16 A_0 (1 + T(z))^2 z^2 ln(2z))` with `A_0 = 10^5`. -/
noncomputable def iota0 (z : ℝ) : ℝ := 1 / (16 * 10 ^ 5 * (1 + Tz z) ^ 2 * z ^ 2 * Real.log (2 * z))

/-- `s_0(z) = (π/2) c_1 z` with `c_1 = (π/2)^{1/2} (17/16)`. -/
noncomputable def s0 (z : ℝ) : ℝ := Real.pi / 2 * (Real.sqrt (Real.pi / 2) * (17 / 16)) * z

/-- `Θ(z) = ln(8 z^2 s_0(z)^2 / ι_0(z))`. -/
noncomputable def Theta (z : ℝ) : ℝ := Real.log (8 * z ^ 2 * s0 z ^ 2 / iota0 z)

/-- `need(z) = z^2/(4 ι_0) (3 + 2 s_0 (2 Θ)^{1/2})`. -/
noncomputable def need (z : ℝ) : ℝ := z ^ 2 / (4 * iota0 z) * (3 + 2 * s0 z * Real.sqrt (2 * Theta z))

end AdversarialBco.Body2

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.penalty_T_le (z : ℝ) (hz : 2 ≤ z) : (1 + AdversarialBco.Body2.Tz z) ^ 2 ≤ (1 + AdversarialBco.Body2.Tz 2) ^ 2 * (1 + 24 / (AdversarialBco.Body2.Tz 2 * (1 + AdversarialBco.Body2.Tz 2)) * Real.log (z / 2)) := by
  set T := AdversarialBco.Body2.Tz z with hT
  set T2 := AdversarialBco.Body2.Tz 2 with hT2
  set C1 := AdversarialBco.Body2.C1 with hC1
  have hC1pos : 0 < C1 := by
    unfold C1 AdversarialBco.Body2.C1
    positivity
  have hC1gt1 : 1 < C1 := by
    unfold C1 AdversarialBco.Body2.C1
    have hsqrt : 1 < Real.sqrt (Real.pi / 2) := by
      have hsq : (1 : ℝ) ^ 2 < Real.pi / 2 := by
        have hpi : 3 < Real.pi := Real.pi_gt_three
        nlinarith
      calc
        (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
        _ < Real.sqrt (Real.pi / 2) := Real.sqrt_lt_sqrt (by norm_num) hsq
    have h52 : 0 < (52 : ℝ) := by norm_num
    have h17 : 0 < (17 : ℝ) / 16 := by norm_num
    have h10 : 0 < (1 : ℝ) + (10 : ℝ) ^ 8 := by positivity
    have hpos_sqrt : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity : 0 < Real.pi / 2)
    nlinarith
  have hzpos : 0 < z := by linarith
  have hTpos : 0 ≤ T := Real.sqrt_nonneg _
  have hT2pos : 0 < T2 := by
    rw [hT2, AdversarialBco.Body2.Tz]
    refine Real.sqrt_pos.mpr ?_
    have : 1 < C1 * (2 : ℝ) ^ 12 := by
      have hpow : 1 < (2 : ℝ) ^ 12 := by norm_num
      nlinarith
    have hlogpos : 0 < Real.log (C1 * (2 : ℝ) ^ 12) := Real.log_pos this
    nlinarith
  have hT2sq_pos : 0 < T2 ^ 2 := pow_pos hT2pos 2
  set x := Real.log (z / 2) with hx
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    refine Real.log_nonneg ?_
    have hzdiv2 : 1 ≤ z / 2 := by linarith
    exact hzdiv2
  have hTz_eq : T ^ 2 = T2 ^ 2 + 24 * x := by
    rw [hT, hT2, hx, AdversarialBco.Body2.Tz, AdversarialBco.Body2.Tz]
    calc
      (Real.sqrt (2 * Real.log (C1 * z ^ 12))) ^ 2
          = 2 * Real.log (C1 * z ^ 12) := Real.sq_sqrt (by
            have : 1 ≤ C1 * z ^ 12 := by
              have hzpow : (2 : ℝ) ^ 12 ≤ z ^ 12 := by gcongr
              nlinarith
            have hlog_nonneg : 0 ≤ Real.log (C1 * z ^ 12) := Real.log_nonneg this
            nlinarith)
      _ = 2 * (Real.log (C1 * (2 : ℝ) ^ 12) + Real.log ((z / 2) ^ 12)) := by
        rw [show Real.log (C1 * z ^ 12) = Real.log (C1 * (2 : ℝ) ^ 12) + Real.log ((z / 2) ^ 12) from by
          calc
            Real.log (C1 * z ^ 12) = Real.log ((C1 * (2 : ℝ) ^ 12) * ((z / 2) ^ 12)) := by ring_nf
            _ = Real.log (C1 * (2 : ℝ) ^ 12) + Real.log ((z / 2) ^ 12) := Real.log_mul (by positivity) (by positivity)
        ]
      _ = 2 * Real.log (C1 * (2 : ℝ) ^ 12) + 2 * Real.log ((z / 2) ^ 12) := by ring
      _ = 2 * Real.log (C1 * (2 : ℝ) ^ 12) + 24 * Real.log (z / 2) := by
        rw [Real.log_pow, Nat.cast_ofNat]
        ring
      _ = (Real.sqrt (2 * Real.log (C1 * (2 : ℝ) ^ 12))) ^ 2 + 24 * Real.log (z / 2) := by
        rw [Real.sq_sqrt (by
          have : 1 ≤ C1 * (2 : ℝ) ^ 12 := by nlinarith
          have hlog_nonneg : 0 ≤ Real.log (C1 * (2 : ℝ) ^ 12) := Real.log_nonneg this
          nlinarith)]
  have h_sqrt_bound : T ≤ T2 + 12 * x / T2 := by
    have h_sq_bound : T ^ 2 ≤ (T2 + 12 * x / T2) ^ 2 := by
      rw [hTz_eq]
      have h : (T2 + 12 * x / T2) ^ 2 = T2 ^ 2 + 24 * x + (12 * x / T2) ^ 2 := by
        field_simp [hT2pos.ne.symm]
        ring_nf
      rw [h]
      nlinarith
    have h_rhs_nonneg : 0 ≤ T2 + 12 * x / T2 := by
      have hdiv_nonneg : 0 ≤ 12 * x / T2 := div_nonneg (by nlinarith) (by linarith)
      nlinarith
    nlinarith
  calc
    (1 + T) ^ 2 = 1 + 2 * T + T ^ 2 := by ring
    _ = 1 + 2 * T + (T2 ^ 2 + 24 * x) := by rw [hTz_eq]
    _ ≤ 1 + 2 * (T2 + 12 * x / T2) + (T2 ^ 2 + 24 * x) := by nlinarith
    _ = 1 + 2 * T2 + 24 * x / T2 + T2 ^ 2 + 24 * x := by ring
    _ = (1 + T2) ^ 2 + 24 * x * (1 + T2) / T2 := by
      field_simp [hT2pos.ne.symm]
      ring
    _ = (1 + T2) ^ 2 * (1 + 24 * x / (T2 * (1 + T2))) := by
      field_simp [hT2pos.ne.symm]
    _ = (1 + T2) ^ 2 * (1 + 24 / (T2 * (1 + T2)) * x) := by ring
    _ = (1 + T2) ^ 2 * (1 + 24 / (T2 * (1 + T2)) * Real.log (z / 2)) := by rw [hx]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.penalty_Theta_le (z : ℝ) (hz : 2 ≤ z) : AdversarialBco.Body2.Theta z ≤ AdversarialBco.Body2.Theta 2 + (6 + 24 / (AdversarialBco.Body2.Tz 2 * (1 + AdversarialBco.Body2.Tz 2)) + 1 / Real.log 4) * Real.log (z / 2) := by
  have hz_pos : 0 < z := by linarith
  have hz2_pos : 0 < z / 2 := by linarith
  have hz2_ge_one : 1 ≤ z / 2 := by linarith
  have hlog_z2_nonneg : 0 ≤ Real.log (z / 2) := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) hz2_ge_one
  set x := Real.log (z / 2) with hx_def
  have hx_nonneg : 0 ≤ x := hlog_z2_nonneg
  -- Tz(z) ≥ 0
  have hTz_nonneg : 0 ≤ AdversarialBco.Body2.Tz z := by
    unfold AdversarialBco.Body2.Tz
    refine Real.sqrt_nonneg _
  have hTz2_nonneg : 0 ≤ AdversarialBco.Body2.Tz 2 := by
    unfold AdversarialBco.Body2.Tz
    refine Real.sqrt_nonneg _
  have honepTz_pos : 0 < 1 + AdversarialBco.Body2.Tz z := by linarith
  have honepTz2_pos : 0 < 1 + AdversarialBco.Body2.Tz 2 := by linarith
  have hlog2z_pos : 0 < Real.log (2 * z) := by
    refine Real.log_pos (by linarith)
  have hlog4_pos : 0 < Real.log 4 := by
    refine Real.log_pos (by norm_num : 1 < (4 : ℝ))
  have hlog4_ne_zero : Real.log 4 ≠ 0 := by linarith
  -- The key algebraic identity: 8*z^2*s0(z)^2/iota0(z) = K*z^6*(1+Tz(z))^2*log(2z)
  -- where K = 8*(π/2*√(π/2)*17/16)^2*16*10^5
  have h_sqrt_sq : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi / 2)
  have hs0_sq : AdversarialBco.Body2.s0 z ^ 2 = ((Real.pi / 2) ^ 3 * ((17 : ℝ) / 16) ^ 2) * z ^ 2 := by
    unfold AdversarialBco.Body2.s0
    calc
      ((Real.pi / 2) * (Real.sqrt (Real.pi / 2) * (17 / 16)) * z) ^ 2
          = ((Real.pi / 2) * Real.sqrt (Real.pi / 2) * (17 / 16)) ^ 2 * z ^ 2 := by ring
      _ = ((Real.pi / 2) ^ 2 * (Real.sqrt (Real.pi / 2)) ^ 2 * ((17 : ℝ) / 16) ^ 2) * z ^ 2 := by ring
      _ = ((Real.pi / 2) ^ 2 * (Real.pi / 2) * ((17 : ℝ) / 16) ^ 2) * z ^ 2 := by rw [h_sqrt_sq]
      _ = ((Real.pi / 2) ^ 3 * ((17 : ℝ) / 16) ^ 2) * z ^ 2 := by ring
  have h_main_eq : 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 / AdversarialBco.Body2.iota0 z =
      (8 * ((Real.pi / 2) * Real.sqrt (Real.pi / 2) * (17 / 16)) ^ 2 * 16 * (10 : ℝ) ^ 5) *
      z ^ 6 * (1 + AdversarialBco.Body2.Tz z) ^ 2 * Real.log (2 * z) := by
    rw [hs0_sq]
    unfold AdversarialBco.Body2.iota0
    have h_denom_ne_zero : 16 * (10 : ℝ) ^ 5 * (1 + AdversarialBco.Body2.Tz z) ^ 2 * z ^ 2 * Real.log (2 * z) ≠ 0 := by
      positivity
    field_simp [h_denom_ne_zero]
    ring_nf
    have h_sqrt_sq' : (Real.sqrt (Real.pi * (1/2 : ℝ))) ^ 2 = Real.pi / 2 := by
      rw [show Real.pi * (1/2 : ℝ) = Real.pi / 2 by ring]
      exact h_sqrt_sq
    rw [h_sqrt_sq']
    ring
  set K := 8 * ((Real.pi / 2) * Real.sqrt (Real.pi / 2) * (17 / 16)) ^ 2 * 16 * (10 : ℝ) ^ 5 with hK_def
  have hK_pos : 0 < K := by
    unfold K
    positivity
  have hK_ne_zero : K ≠ 0 := by linarith
  -- Express Theta(z) in terms of K
  have hTheta_z_eq : AdversarialBco.Body2.Theta z = Real.log (K * z ^ 6 * (1 + AdversarialBco.Body2.Tz z) ^ 2 * Real.log (2 * z)) := by
    unfold AdversarialBco.Body2.Theta
    rw [h_main_eq, hK_def]
  have hTheta_2_eq : AdversarialBco.Body2.Theta 2 = Real.log (K * (2 : ℝ) ^ 6 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * Real.log 4) := by
    -- The same identity holds for z=2, so we can reuse the computation
    have h_main_eq_2 : 8 * (2 : ℝ) ^ 2 * AdversarialBco.Body2.s0 (2 : ℝ) ^ 2 / AdversarialBco.Body2.iota0 (2 : ℝ) =
        K * (2 : ℝ) ^ 6 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * Real.log 4 := by
      -- This follows from h_main_eq with z=2, but we need to recompute
      -- Actually, the same proof works for any z, so we can just apply the same reasoning
      have hs0_sq_2 : AdversarialBco.Body2.s0 (2 : ℝ) ^ 2 = ((Real.pi / 2) ^ 3 * ((17 : ℝ) / 16) ^ 2) * (2 : ℝ) ^ 2 := by
        unfold AdversarialBco.Body2.s0
        calc
          ((Real.pi / 2) * (Real.sqrt (Real.pi / 2) * (17 / 16)) * (2 : ℝ)) ^ 2
              = ((Real.pi / 2) * Real.sqrt (Real.pi / 2) * (17 / 16)) ^ 2 * (2 : ℝ) ^ 2 := by ring
          _ = ((Real.pi / 2) ^ 2 * (Real.sqrt (Real.pi / 2)) ^ 2 * ((17 : ℝ) / 16) ^ 2) * (2 : ℝ) ^ 2 := by ring
          _ = ((Real.pi / 2) ^ 2 * (Real.pi / 2) * ((17 : ℝ) / 16) ^ 2) * (2 : ℝ) ^ 2 := by rw [h_sqrt_sq]
          _ = ((Real.pi / 2) ^ 3 * ((17 : ℝ) / 16) ^ 2) * (2 : ℝ) ^ 2 := by ring
      rw [hs0_sq_2]
      unfold AdversarialBco.Body2.iota0
      have h_denom_ne_zero_2 : 16 * (10 : ℝ) ^ 5 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * (2 : ℝ) ^ 2 * Real.log 4 ≠ 0 := by
        positivity
      field_simp [h_denom_ne_zero_2]
      ring_nf
      field_simp [hlog4_ne_zero]
      rw [hK_def]
      ring_nf
      rw [show Real.pi * (1/2 : ℝ) = Real.pi / 2 by ring]
      rw [h_sqrt_sq]
      ring_nf
    unfold AdversarialBco.Body2.Theta
    rw [h_main_eq_2]
  -- Expand Theta(z) using log properties
  have hTheta_z_expand : AdversarialBco.Body2.Theta z =
      Real.log K + 6 * Real.log z + 2 * Real.log (1 + AdversarialBco.Body2.Tz z) + Real.log (Real.log (2 * z)) := by
    rw [hTheta_z_eq]
    have hz6_pos : z ^ 6 ≠ 0 := by positivity
    have honepTz_sq_pos : (1 + AdversarialBco.Body2.Tz z) ^ 2 ≠ 0 := by positivity
    have hlog2z_pos' : Real.log (2 * z) ≠ 0 := by linarith
    calc
      Real.log (K * z ^ 6 * (1 + AdversarialBco.Body2.Tz z) ^ 2 * Real.log (2 * z))
          = Real.log (K * z ^ 6 * (1 + AdversarialBco.Body2.Tz z) ^ 2) + Real.log (Real.log (2 * z)) := by
        refine Real.log_mul ?_ hlog2z_pos'
        positivity
      _ = Real.log (K * z ^ 6) + Real.log ((1 + AdversarialBco.Body2.Tz z) ^ 2) + Real.log (Real.log (2 * z)) := by
        refine congrArg (· + Real.log (Real.log (2 * z))) (Real.log_mul ?_ honepTz_sq_pos)
        positivity
      _ = Real.log K + Real.log (z ^ 6) + Real.log ((1 + AdversarialBco.Body2.Tz z) ^ 2) + Real.log (Real.log (2 * z)) := by
        rw [Real.log_mul (by exact hK_ne_zero) hz6_pos]
      _ = Real.log K + 6 * Real.log z + 2 * Real.log (1 + AdversarialBco.Body2.Tz z) + Real.log (Real.log (2 * z)) := by
        rw [Real.log_pow, Real.log_pow]
        ring
  -- Expand Theta(2) similarly
  have hTheta_2_expand : AdversarialBco.Body2.Theta 2 =
      Real.log K + 6 * Real.log 2 + 2 * Real.log (1 + AdversarialBco.Body2.Tz 2) + Real.log (Real.log 4) := by
    rw [hTheta_2_eq]
    have h26_pos : (2 : ℝ) ^ 6 ≠ 0 := by norm_num
    have honepTz2_sq_pos : (1 + AdversarialBco.Body2.Tz 2) ^ 2 ≠ 0 := by positivity
    have hlog4_pos' : Real.log 4 ≠ 0 := by linarith
    calc
      Real.log (K * (2 : ℝ) ^ 6 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * Real.log 4)
          = Real.log (K * (2 : ℝ) ^ 6 * (1 + AdversarialBco.Body2.Tz 2) ^ 2) + Real.log (Real.log 4) := by
        refine Real.log_mul ?_ hlog4_pos'
        positivity
      _ = Real.log (K * (2 : ℝ) ^ 6) + Real.log ((1 + AdversarialBco.Body2.Tz 2) ^ 2) + Real.log (Real.log 4) := by
        refine congrArg (· + Real.log (Real.log 4)) (Real.log_mul ?_ honepTz2_sq_pos)
        positivity
      _ = Real.log K + Real.log ((2 : ℝ) ^ 6) + Real.log ((1 + AdversarialBco.Body2.Tz 2) ^ 2) + Real.log (Real.log 4) := by
        rw [Real.log_mul (by exact hK_ne_zero) h26_pos]
      _ = Real.log K + 6 * Real.log 2 + 2 * Real.log (1 + AdversarialBco.Body2.Tz 2) + Real.log (Real.log 4) := by
        rw [Real.log_pow, Real.log_pow]
        ring
  -- Now compute the difference Theta(z) - Theta(2)
  have h_diff : AdversarialBco.Body2.Theta z - AdversarialBco.Body2.Theta 2 =
      6 * Real.log (z / 2) + 2 * Real.log ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) + Real.log (Real.log (2 * z) / Real.log 4) := by
    rw [hTheta_z_expand, hTheta_2_expand]
    calc
      (Real.log K + 6 * Real.log z + 2 * Real.log (1 + AdversarialBco.Body2.Tz z) + Real.log (Real.log (2 * z))) -
        (Real.log K + 6 * Real.log 2 + 2 * Real.log (1 + AdversarialBco.Body2.Tz 2) + Real.log (Real.log 4))
      = 6 * Real.log z - 6 * Real.log 2 + 2 * Real.log (1 + AdversarialBco.Body2.Tz z) - 2 * Real.log (1 + AdversarialBco.Body2.Tz 2) + Real.log (Real.log (2 * z)) - Real.log (Real.log 4) := by ring
      _ = 6 * (Real.log z - Real.log 2) + 2 * (Real.log (1 + AdversarialBco.Body2.Tz z) - Real.log (1 + AdversarialBco.Body2.Tz 2)) + (Real.log (Real.log (2 * z)) - Real.log (Real.log 4)) := by ring
      _ = 6 * Real.log (z / 2) + 2 * Real.log ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) + Real.log (Real.log (2 * z) / Real.log 4) := by
        rw [Real.log_div hz_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
        rw [Real.log_div honepTz_pos.ne' honepTz2_pos.ne']
        rw [Real.log_div hlog2z_pos.ne' hlog4_pos.ne']
  -- Now bound each term
  set q := 24 / (AdversarialBco.Body2.Tz 2 * (1 + AdversarialBco.Body2.Tz 2)) with hq_def
  have hq_nonneg : 0 ≤ q := by
    unfold q
    positivity
  have h_bound_Tz : 2 * Real.log ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) ≤ q * x := by
    have h_penalty := AdversarialBco.Body2.penalty_T_le z hz
    -- h_penalty: (1 + Tz z)^2 ≤ (1 + Tz 2)^2 * (1 + (24 / (Tz 2 * (1 + Tz 2))) * Real.log (z / 2))
    have h_penalty' : (1 + AdversarialBco.Body2.Tz z)^2 ≤ (1 + AdversarialBco.Body2.Tz 2)^2 * (1 + q * x) := by
      rw [hq_def, hx_def]
      exact h_penalty
    have h_div_sq : ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) ^ 2 ≤ 1 + q * x := by
      have hpos_sq : 0 < (1 + AdversarialBco.Body2.Tz 2) ^ 2 := by positivity
      rw [div_pow]
      -- Goal: (1+Tz z)^2 / (1+Tz 2)^2 ≤ 1 + q*x
      -- From h_penalty': (1+Tz z)^2 ≤ (1+Tz 2)^2 * (1 + q*x)
      -- So (1+Tz z)^2 / (1+Tz 2)^2 ≤ (1+Tz 2)^2 * (1+q*x) / (1+Tz 2)^2 = 1+q*x
      calc
        (1 + AdversarialBco.Body2.Tz z) ^ 2 / (1 + AdversarialBco.Body2.Tz 2) ^ 2
            ≤ ((1 + AdversarialBco.Body2.Tz 2) ^ 2 * (1 + q * x)) / (1 + AdversarialBco.Body2.Tz 2) ^ 2 := by
          refine (div_le_div_of_nonneg_right h_penalty' (by positivity))
        _ = 1 + q * x := by field_simp [hpos_sq.ne']
    have h_one_plus_qx_pos : 0 < 1 + q * x := by
      have : 0 ≤ q * x := mul_nonneg hq_nonneg hx_nonneg
      linarith
    have h_log_div_sq : Real.log (((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) ^ 2) ≤
        Real.log (1 + q * x) :=
      Real.log_le_log (by positivity) h_div_sq
    rw [Real.log_pow, Nat.cast_ofNat] at h_log_div_sq
    have h_log_bound : Real.log (1 + q * x) ≤ q * x := by
      have h := Real.log_le_sub_one_of_pos h_one_plus_qx_pos
      linarith
    linarith
  have h_bound_log : Real.log (Real.log (2 * z) / Real.log 4) ≤ x / Real.log 4 := by
    have h_log2z_eq : Real.log (2 * z) = Real.log 4 + x := by
      rw [hx_def]
      calc
        Real.log (2 * z) = Real.log (4 * (z / 2)) := by rw [show (2:ℝ)*z = 4*(z/2) by ring]
        _ = Real.log 4 + Real.log (z / 2) := Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hz2_pos.ne'
        _ = Real.log 4 + x := rfl
    rw [h_log2z_eq]
    -- Goal: Real.log ((Real.log 4 + x) / Real.log 4) ≤ x / Real.log 4
    rw [add_div, div_self hlog4_ne_zero]
    -- Goal: Real.log (1 + x / Real.log 4) ≤ x / Real.log 4
    have hpos_ratio : 0 < 1 + x / Real.log 4 := by
      refine add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg hx_nonneg (by linarith))
    simpa [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hpos_ratio
  -- Combine the bounds
  have h_total_bound : AdversarialBco.Body2.Theta z - AdversarialBco.Body2.Theta 2 ≤
      (6 + q + 1 / Real.log 4) * x := by
    rw [h_diff]
    -- Goal: 6*log(z/2) + 2*log(...) + log(...) ≤ (6 + q + 1/log 4) * log(z/2)
    -- Rewrite log(z/2) to x
    rw [← hx_def]
    -- Goal: 6*x + 2*log(...) + log(...) ≤ (6 + q + 1/log 4) * x
    have hsum : 6 * x + 2 * Real.log ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) +
        Real.log (Real.log (2 * z) / Real.log 4) ≤
        (6 + q + 1 / Real.log 4) * x := by
      have htemp : 6 * x + (2 * Real.log ((1 + AdversarialBco.Body2.Tz z) / (1 + AdversarialBco.Body2.Tz 2)) +
          Real.log (Real.log (2 * z) / Real.log 4)) ≤ 6 * x + (q * x + x / Real.log 4) := by
        nlinarith
      have hgoal : 6 * x + (q * x + x / Real.log 4) = (6 + q + 1 / Real.log 4) * x := by ring
      rw [hgoal] at htemp
      -- htemp: 6*x + (2*log + log) ≤ (6+q+1/log 4)*x
      -- But we need: 6*x + 2*log + log ≤ (6+q+1/log 4)*x
      -- These are equal by associativity
      simpa [add_assoc] using htemp
    exact hsum
  -- Convert the difference inequality to the target inequality
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.t0_arith (n σ ι : ℝ) (hσ : 0 < σ) (hι : 0 < ι) : 2 * n ^ 2 * σ ^ 2 * Real.exp (-(σ * Real.sqrt (2 * AdversarialBco.BodySpec.lnp (8 * n ^ 2 * σ ^ 2 / ι))) ^ 2 / (2 * σ ^ 2)) ≤ ι / 4 := by
  set y := 8 * n ^ 2 * σ ^ 2 / ι with hy_def
  set L := AdversarialBco.BodySpec.lnp y with hL_def
  have hy_nonneg : 0 ≤ y := by
    rw [hy_def]
    have hn_sq_nonneg : 0 ≤ n ^ 2 := pow_two_nonneg n
    have hσ_sq_nonneg : 0 ≤ σ ^ 2 := pow_two_nonneg σ
    have hnum_nonneg : 0 ≤ 8 * n ^ 2 * σ ^ 2 := by nlinarith
    exact div_nonneg hnum_nonneg hι.le
  have hσ_ne : σ ≠ 0 := by linarith
  have h2L_nonneg : 0 ≤ 2 * L := by
    have hL_nonneg : 0 ≤ L := by
      rw [hL_def]
      exact le_max_right _ _
    nlinarith
  -- simplify the exponent: -(σ * √(2L))² / (2σ²) = -L
  have hexp_simp : -(σ * Real.sqrt (2 * L)) ^ 2 / (2 * σ ^ 2) = -L := by
    calc
      -(σ * Real.sqrt (2 * L)) ^ 2 / (2 * σ ^ 2) = -(σ ^ 2 * (Real.sqrt (2 * L)) ^ 2) / (2 * σ ^ 2) := by ring
      _ = -(σ ^ 2 * (2 * L)) / (2 * σ ^ 2) := by rw [Real.sq_sqrt h2L_nonneg]
      _ = -(2 * σ ^ 2 * L) / (2 * σ ^ 2) := by ring
      _ = -L := by field_simp [hσ_ne]
  rw [hexp_simp]
  -- goal: 2 * n ^ 2 * σ ^ 2 * Real.exp (-L) ≤ ι / 4
  by_cases hy1 : 1 ≤ y
  · -- case y ≥ 1: L = log y, exp(-log y) = 1/y, and 2n²σ² / y = ι/4
    have hy_pos : 0 < y := by linarith
    have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hL_eq : L = Real.log y := by
      rw [hL_def]
      exact max_eq_left hlog_nonneg
    rw [hL_eq]
    rw [Real.exp_neg, Real.exp_log hy_pos]
    -- goal: 2 * n ^ 2 * σ ^ 2 * (y⁻¹) ≤ ι / 4
    have hnum_pos : 8 * n ^ 2 * σ ^ 2 > 0 := by
      rw [hy_def] at hy_pos
      rcases div_pos_iff.mp hy_pos with (⟨h, _⟩ | ⟨h, hneg⟩)
      · exact h
      · linarith [hneg, hι]
    have hn_ne_zero : n ≠ 0 := by
      intro hzero
      have : 8 * n ^ 2 * σ ^ 2 = 0 := by simp [hzero]
      linarith [hnum_pos, this]
    have hy_eq : 2 * n ^ 2 * σ ^ 2 * (y⁻¹) = ι / 4 := by
      rw [hy_def]
      field_simp [hι.ne.symm, hσ_ne, hn_ne_zero]
      ring
    rw [hy_eq]
  · -- case y < 1: L = 0, exp(0) = 1, and 8n²σ² < ι gives 2n²σ² ≤ ι/4
    have hy_lt_one : y < 1 := by linarith
    have hlog_nonpos : Real.log y ≤ 0 := Real.log_nonpos hy_nonneg (by linarith)
    have hL_eq : L = 0 := by
      rw [hL_def]
      exact max_eq_right hlog_nonpos
    rw [hL_eq, neg_zero, Real.exp_zero, mul_one]
    -- goal: 2 * n ^ 2 * σ ^ 2 ≤ ι / 4
    rw [hy_def] at hy_lt_one
    have h_ineq : 8 * n ^ 2 * σ ^ 2 < ι := (div_lt_one hι).mp hy_lt_one
    nlinarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.t0_mono (n z σ σ0 ι ι0 : ℝ) (hn : 0 ≤ n) (hnz : n ≤ z) (hσ : 0 ≤ σ) (hσ0 : σ ≤ σ0) (hι0 : 0 < ι0) (hι : ι0 ≤ ι) (h1 : 1 ≤ 8 * z ^ 2 * σ0 ^ 2 / ι0) : σ * Real.sqrt (2 * AdversarialBco.BodySpec.lnp (8 * n ^ 2 * σ ^ 2 / ι)) ≤ σ0 * Real.sqrt (2 * Real.log (8 * z ^ 2 * σ0 ^ 2 / ι0)) := by
  have hz : 0 ≤ z := le_trans hn hnz
  have hσ0' : 0 ≤ σ0 := le_trans hσ hσ0
  have hι_pos : 0 < ι := lt_of_lt_of_le hι0 hι
  have h_log_nonneg : 0 ≤ Real.log (8 * z ^ 2 * σ0 ^ 2 / ι0) := Real.log_nonneg h1
  have h_div : 8 * n ^ 2 * σ ^ 2 / ι ≤ 8 * z ^ 2 * σ0 ^ 2 / ι0 := by
    have h_nonneg_num : 0 ≤ 8 * n ^ 2 * σ ^ 2 := by nlinarith
    have h_num : 8 * n ^ 2 * σ ^ 2 ≤ 8 * z ^ 2 * σ0 ^ 2 := by
      have hz_sq : n ^ 2 ≤ z ^ 2 := by nlinarith
      have hσ_sq : σ ^ 2 ≤ σ0 ^ 2 := by nlinarith
      nlinarith
    apply le_trans (div_le_div_of_nonneg_left h_nonneg_num hι0 hι) ?_
    apply div_le_div_of_nonneg_right h_num hι0.le
  have h_lnp_le_log : AdversarialBco.BodySpec.lnp (8 * n ^ 2 * σ ^ 2 / ι) ≤ Real.log (8 * z ^ 2 * σ0 ^ 2 / ι0) := by
    unfold AdversarialBco.BodySpec.lnp
    by_cases hx : 8 * n ^ 2 * σ ^ 2 / ι = 0
    · simp [hx, h_log_nonneg]
    · have h_nonneg : 0 ≤ 8 * n ^ 2 * σ ^ 2 / ι := by
        apply div_nonneg
        · nlinarith
        · linarith
      have hx_pos : 0 < 8 * n ^ 2 * σ ^ 2 / ι := by
        contrapose! hx
        linarith
      have hlog := Real.log_le_log hx_pos h_div
      exact max_le hlog h_log_nonneg
  have h_sqrt : Real.sqrt (2 * AdversarialBco.BodySpec.lnp (8 * n ^ 2 * σ ^ 2 / ι)) ≤ Real.sqrt (2 * Real.log (8 * z ^ 2 * σ0 ^ 2 / ι0)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  exact mul_le_mul hσ0 h_sqrt (Real.sqrt_nonneg _) hσ0'
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.need_mono (n z t0 ι : ℝ) (hn0 : 0 ≤ n) (hnz : n ≤ z) (hz : 2 ≤ z) (ht0 : 0 ≤ t0) (ht : t0 ≤ AdversarialBco.Body2.s0 z * Real.sqrt (2 * AdversarialBco.Body2.Theta z)) (hι0 : 0 < AdversarialBco.Body2.iota0 z) (hι : AdversarialBco.Body2.iota0 z ≤ ι) : n ^ 2 * (3 + 2 * t0) / (4 * ι) ≤ AdversarialBco.Body2.need z := by
  have hX : 0 ≤ 3 + 2 * t0 := by linarith
  have h_n_sq_le_z_sq : n ^ 2 ≤ z ^ 2 := by
    nlinarith
  have h_denom1_pos : 0 < 4 * AdversarialBco.Body2.iota0 z := by
    nlinarith
  have h_denom2_pos : 0 < 4 * ι := by
    nlinarith
  have h_one_div_le : 1 / (4 * ι) ≤ 1 / (4 * AdversarialBco.Body2.iota0 z) := by
    rw [one_div_le_one_div h_denom2_pos h_denom1_pos]
    nlinarith
  have h_part1 : n ^ 2 * (3 + 2 * t0) / (4 * ι) ≤ z ^ 2 * (3 + 2 * t0) / (4 * AdversarialBco.Body2.iota0 z) := by
    calc
      n ^ 2 * (3 + 2 * t0) / (4 * ι) = (n ^ 2 * (3 + 2 * t0)) * (1 / (4 * ι)) := by ring
      _ = n ^ 2 * ((3 + 2 * t0) * (1 / (4 * ι))) := by ring
      _ ≤ z ^ 2 * ((3 + 2 * t0) * (1 / (4 * ι))) := by
        have h_nonneg_c : 0 ≤ (3 + 2 * t0) * (1 / (4 * ι)) :=
          mul_nonneg hX (div_nonneg (by norm_num) (by nlinarith))
        exact mul_le_mul_of_nonneg_right h_n_sq_le_z_sq h_nonneg_c
      _ = (z ^ 2 * (3 + 2 * t0)) * (1 / (4 * ι)) := by ring
      _ ≤ (z ^ 2 * (3 + 2 * t0)) * (1 / (4 * AdversarialBco.Body2.iota0 z)) := by
        have h_nonneg_z2X : 0 ≤ z ^ 2 * (3 + 2 * t0) := by nlinarith
        exact mul_le_mul_of_nonneg_left h_one_div_le h_nonneg_z2X
      _ = z ^ 2 * (3 + 2 * t0) / (4 * AdversarialBco.Body2.iota0 z) := by ring
  have h_part2 : z ^ 2 * (3 + 2 * t0) / (4 * AdversarialBco.Body2.iota0 z) ≤ AdversarialBco.Body2.need z := by
    rw [AdversarialBco.Body2.need, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hz_sq_nonneg : 0 ≤ z ^ 2 := pow_two_nonneg z
    nlinarith
  exact le_trans h_part1 h_part2
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.theta_arg (z : ℝ) (hz : 2 ≤ z) : 0 < AdversarialBco.Body2.iota0 z ∧ 1 ≤ 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 / AdversarialBco.Body2.iota0 z := by
  have hz_pos : 0 < z := by linarith
  have h2z_gt_one : 1 < 2 * z := by nlinarith
  have hlog2z_pos : 0 < Real.log (2 * z) := Real.log_pos h2z_gt_one
  have hTz_nonneg : 0 ≤ AdversarialBco.Body2.Tz z := by
    dsimp [AdversarialBco.Body2.Tz]
    apply Real.sqrt_nonneg
  have h_denom_pos : 0 < 16 * 10 ^ 5 * (1 + AdversarialBco.Body2.Tz z) ^ 2 * z ^ 2 * Real.log (2 * z) := by
    positivity
  have h_iota0_pos : 0 < AdversarialBco.Body2.iota0 z := by
    dsimp [AdversarialBco.Body2.iota0]
    refine div_pos (by norm_num) h_denom_pos
  have hlog4_gt_one : 1 < Real.log 4 := by
    have h_exp_one_lt_four : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_three]
    have h := Real.log_lt_log (Real.exp_pos 1) h_exp_one_lt_four
    rw [Real.log_exp (1 : ℝ)] at h
    exact h
  have hlog2z_ge_one : 1 ≤ Real.log (2 * z) := by
    have hlog_le : Real.log 4 ≤ Real.log (2 * z) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    linarith
  have h_iota0_le_one : AdversarialBco.Body2.iota0 z ≤ 1 := by
    dsimp [AdversarialBco.Body2.iota0]
    refine (div_le_one ?_).mpr ?_
    · exact h_denom_pos
    · have hTz_sq_ge_one : 1 ≤ (1 + AdversarialBco.Body2.Tz z) ^ 2 := by
        have h : 0 ≤ 1 + AdversarialBco.Body2.Tz z := by nlinarith
        nlinarith
      have hz_sq_ge_one : 1 ≤ z ^ 2 := by nlinarith
      have h_16_10_5_ge_one : (1 : ℝ) ≤ 16 * 10 ^ 5 := by norm_num
      have h_nonneg_log : 0 ≤ Real.log (2 * z) := by linarith
      calc
        (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ (16 * 10 ^ 5) * 1 * 1 * 1 := by gcongr
        _ ≤ (16 * 10 ^ 5) * ((1 + AdversarialBco.Body2.Tz z) ^ 2) * 1 * 1 := by gcongr
        _ ≤ (16 * 10 ^ 5) * ((1 + AdversarialBco.Body2.Tz z) ^ 2) * (z ^ 2) * 1 := by gcongr
        _ ≤ (16 * 10 ^ 5) * ((1 + AdversarialBco.Body2.Tz z) ^ 2) * (z ^ 2) * Real.log (2 * z) := by gcongr
  have h_s0_ge_one : 1 ≤ AdversarialBco.Body2.s0 z := by
    dsimp [AdversarialBco.Body2.s0]
    have hpi_gt_three : 3 < Real.pi := Real.pi_gt_three
    have h_pi_div_two_gt_one : 1 < Real.pi / 2 := by linarith
    have h_sqrt_gt_one : 1 < Real.sqrt (Real.pi / 2) := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ < Real.sqrt (Real.pi / 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have h17_16_gt_one : 1 < (17 : ℝ) / 16 := by norm_num
    have hz_gt_one : 1 < z := by linarith
    have h_nonneg_pi : 0 ≤ Real.pi / 2 := by linarith
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (Real.pi / 2) := by positivity
    have h_nonneg_17_16 : 0 ≤ (17 : ℝ) / 16 := by norm_num
    have h_nonneg_z : 0 ≤ z := by linarith
    have h1 : (1 : ℝ) ≤ Real.pi / 2 := h_pi_div_two_gt_one.le
    have h2 : (1 : ℝ) ≤ Real.sqrt (Real.pi / 2) := h_sqrt_gt_one.le
    have h3 : (1 : ℝ) ≤ (17 : ℝ) / 16 := h17_16_gt_one.le
    have h4 : (1 : ℝ) ≤ z := hz_gt_one.le
    have h_mul12 : (1 : ℝ) * 1 ≤ (Real.pi / 2) * Real.sqrt (Real.pi / 2) :=
      mul_le_mul h1 h2 (by norm_num : 0 ≤ (1 : ℝ)) h_nonneg_pi
    have h_mul123 : (1 : ℝ) * 1 * 1 ≤ (Real.pi / 2) * Real.sqrt (Real.pi / 2) * ((17 : ℝ) / 16) := by
      apply mul_le_mul h_mul12 h3 (by norm_num : 0 ≤ (1 : ℝ)) (mul_nonneg h_nonneg_pi h_nonneg_sqrt)
    have h_mul1234 : (1 : ℝ) * 1 * 1 * 1 ≤ (Real.pi / 2) * Real.sqrt (Real.pi / 2) * ((17 : ℝ) / 16) * z := by
      apply mul_le_mul h_mul123 h4 (by norm_num : 0 ≤ (1 : ℝ)) (by positivity)
    simpa [mul_assoc] using h_mul1234
  have h_second : 1 ≤ 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 / AdversarialBco.Body2.iota0 z := by
    have h_inv_iota0_ge_one : 1 ≤ (AdversarialBco.Body2.iota0 z)⁻¹ := by
      rw [← one_div]
      refine (one_le_div ?_).mpr h_iota0_le_one
      exact h_iota0_pos
    have h_num_ge_32 : 32 ≤ 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 := by
      have hz_sq_ge_four : 4 ≤ z ^ 2 := by nlinarith
      have hs0_sq_ge_one : 1 ≤ AdversarialBco.Body2.s0 z ^ 2 := by nlinarith
      nlinarith
    calc
      1 ≤ 32 := by norm_num
      _ ≤ 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 := h_num_ge_32
      _ = 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 * 1 := by ring
      _ ≤ 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 * (AdversarialBco.Body2.iota0 z)⁻¹ := by
        nlinarith
      _ = 8 * z ^ 2 * AdversarialBco.Body2.s0 z ^ 2 / AdversarialBco.Body2.iota0 z := by ring
  exact And.intro h_iota0_pos h_second
end

/-- The bound `T_h ≤ T(z)` and `(1 + T_h)^2 ≤ C_T ln z`, `C_T = (2 + 4 ln C_1)/ln 2 + 48`, of the proof of Proposition
2.2, from `s_h ≤ (π/2)^{1/2} (17/16) z` and `h > 1/(2n)`. -/
theorem AdversarialBco.Body2.T_arith (n d D s h : ℝ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hD : 1 ≤ D) (hs0 : 0 ≤ s) (hs : s ≤ Real.sqrt (Real.pi / 2) * (17 / 16) * (n * d * D)) (hh : 1 / (2 * n) < h) : Real.sqrt (2 * AdversarialBco.BodySpec.lnp (26 * d * (n + 10 ^ 8 * (n * d * D) ^ 10) * s / h)) ≤ AdversarialBco.Body2.Tz (n * d * D) ∧ (1 + Real.sqrt (2 * AdversarialBco.BodySpec.lnp (26 * d * (n + 10 ^ 8 * (n * d * D) ^ 10) * s / h))) ^ 2 ≤ ((2 + 4 * Real.log AdversarialBco.Body2.C1) / Real.log 2 + 48) * Real.log (n * d * D) := by
  set z := n * d * D with hz
  have hn0 : 0 < n := by linarith
  have hnd : n ≤ n * d := le_mul_of_one_le_right hn0.le hd
  have hndz : n * d ≤ z := le_mul_of_one_le_right (by linarith) hD
  have hz2 : 2 ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have h2n : 0 < 2 * n := by linarith
  have hh0 : 0 < h := lt_trans (by positivity) hh
  have hinv : 1 / h ≤ 2 * n := by
    have h1 : 1 < h * (2 * n) := (div_lt_iff₀ h2n).1 hh
    rw [div_le_iff₀ hh0]; linarith
  set c := Real.sqrt (Real.pi / 2) * (17 / 16) with hc
  have hsq1 : 1 ≤ Real.sqrt (Real.pi / 2) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_gt_three])
    rwa [Real.sqrt_one] at this
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hC1 : AdversarialBco.Body2.C1 = 52 * c * (1 + 10 ^ 8) := by
    unfold AdversarialBco.Body2.C1; rw [hc]; ring
  have hC1ge : 1 ≤ AdversarialBco.Body2.C1 := by rw [hC1]; nlinarith
  set A := n + 10 ^ 8 * z ^ 10 with hA
  have hz10 : z ≤ z ^ 10 := le_self_pow₀ hz1 (by norm_num)
  have hAle : A ≤ (1 + 10 ^ 8) * z ^ 10 := by rw [hA]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set Y := 26 * d * A * s / h with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ d := by linarith
    rw [hY]; positivity
  have hYle : Y ≤ AdversarialBco.Body2.C1 * z ^ 12 := by
    have hnd0 : 0 ≤ n * d := by positivity
    calc Y = 26 * d * A * s * (1 / h) := by rw [hY]; ring
      _ ≤ 26 * d * A * s * (2 * n) := mul_le_mul_of_nonneg_left hinv (by
          have : 0 ≤ d := by linarith
          positivity)
      _ = 52 * (n * d) * A * s := by ring
      _ ≤ 52 * z * ((1 + 10 ^ 8) * z ^ 10) * (c * z) := by
          have h1 : 52 * (n * d) ≤ 52 * z := by linarith
          have h2 : 52 * (n * d) * A ≤ 52 * z * ((1 + 10 ^ 8) * z ^ 10) :=
            mul_le_mul h1 hAle hA0 (by positivity)
          exact mul_le_mul h2 hs hs0 (by positivity)
      _ = AdversarialBco.Body2.C1 * z ^ 12 := by rw [hC1]; ring
  have hz12 : 1 ≤ z ^ 12 := one_le_pow₀ hz1
  have hCz : 1 ≤ AdversarialBco.Body2.C1 * z ^ 12 := by nlinarith
  have hlog0 : 0 ≤ Real.log (AdversarialBco.Body2.C1 * z ^ 12) := Real.log_nonneg hCz
  have hlnp : AdversarialBco.BodySpec.lnp Y ≤ Real.log (AdversarialBco.Body2.C1 * z ^ 12) := by
    unfold AdversarialBco.BodySpec.lnp
    refine max_le ?_ hlog0
    rcases hY0.eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]; exact hlog0
    · exact Real.log_le_log hpos hYle
  have hlnp0 : 0 ≤ AdversarialBco.BodySpec.lnp Y := le_max_right _ _
  constructor
  · unfold AdversarialBco.Body2.Tz; exact Real.sqrt_le_sqrt (by linarith)
  · set T := Real.sqrt (2 * AdversarialBco.BodySpec.lnp Y) with hT
    have hT2 : T ^ 2 = 2 * AdversarialBco.BodySpec.lnp Y := Real.sq_sqrt (by linarith)
    have h1 : (1 + T) ^ 2 ≤ 2 + 2 * T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    have hlogC : Real.log (AdversarialBco.Body2.C1 * z ^ 12) = Real.log AdversarialBco.Body2.C1 + 12 * Real.log z := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlz : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
    have hlC : 0 ≤ Real.log AdversarialBco.Body2.C1 := Real.log_nonneg hC1ge
    have hk : 2 + 4 * Real.log AdversarialBco.Body2.C1 ≤
        (2 + 4 * Real.log AdversarialBco.Body2.C1) / Real.log 2 * Real.log z := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; exact mul_le_mul_of_nonneg_left hlz (by linarith)
    calc (1 + T) ^ 2 ≤ 2 + 2 * T ^ 2 := h1
      _ = 2 + 4 * AdversarialBco.BodySpec.lnp Y := by rw [hT2]; ring
      _ ≤ 2 + 4 * (Real.log AdversarialBco.Body2.C1 + 12 * Real.log z) := by rw [← hlogC]; linarith
      _ = (2 + 4 * Real.log AdversarialBco.Body2.C1) + 48 * Real.log z := by ring
      _ ≤ ((2 + 4 * Real.log AdversarialBco.Body2.C1) / Real.log 2 + 48) * Real.log z := by
          rw [add_mul]; linarith [hk]

/-- The values at `z = 2` in Lemma 4.1: `need(2) ≤ 1024·10^8`, `T(2) ≥ 7`, `Θ(2) ≥ 20`. -/
theorem AdversarialBco.Body2.penalty_numeric : AdversarialBco.Body2.need 2 ≤ 1024 * 10 ^ 8 ∧ 7 ≤ AdversarialBco.Body2.Tz 2 ∧ 20 ≤ AdversarialBco.Body2.Theta 2 := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d4
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  -- `√(π/2) ∈ [1.25, 1.26]`
  have hs1 : (1.25 : ℝ) ≤ Real.sqrt (Real.pi / 2) := (Real.le_sqrt' (by norm_num)).2 (by norm_num; linarith)
  have hs2 : Real.sqrt (Real.pi / 2) ≤ 1.26 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num; linarith)
  -- `2^32 ≤ C_1 ≤ 2^33`
  have hC1 : (2 : ℝ) ^ 32 ≤ AdversarialBco.Body2.C1 ∧ AdversarialBco.Body2.C1 ≤ 2 ^ 33 := by
    unfold AdversarialBco.Body2.C1
    constructor <;> linarith
  have hC1pos : 0 < AdversarialBco.Body2.C1 := lt_of_lt_of_le (by norm_num) hC1.1
  -- `44 ln 2 ≤ ln (C_1 2^12) ≤ 45 ln 2`
  have hL1 : 44 * Real.log 2 ≤ Real.log (AdversarialBco.Body2.C1 * 2 ^ 12) := by
    have e : Real.log ((2 : ℝ) ^ 44) = 44 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by norm_num) (by linarith [hC1.1])
  have hL2 : Real.log (AdversarialBco.Body2.C1 * 2 ^ 12) ≤ 45 * Real.log 2 := by
    have e : Real.log ((2 : ℝ) ^ 45) = 45 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (mul_pos hC1pos (by norm_num)) (by linarith [hC1.2])
  -- `L` is a variable for linarith, whose `cancelDenoms` would rewrite `2 ^ 12` inside the atom in some facts only
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (AdversarialBco.Body2.C1 * 2 ^ 12) := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hL2
  -- `7.8 ≤ T(2) ≤ 7.9`
  have hT1 : (7.8 : ℝ) ≤ AdversarialBco.Body2.Tz 2 := by
    show (7.8 : ℝ) ≤ Real.sqrt (2 * Real.log (AdversarialBco.Body2.C1 * 2 ^ 12))
    rw [← hLdef]
    exact (Real.le_sqrt' (by norm_num)).2 (by linarith [show (7.8 : ℝ) ^ 2 = 60.84 by norm_num])
  have hT2 : AdversarialBco.Body2.Tz 2 ≤ 7.9 := by
    show Real.sqrt (2 * Real.log (AdversarialBco.Body2.C1 * 2 ^ 12)) ≤ 7.9
    rw [← hLdef]
    exact (Real.sqrt_le_left (by norm_num)).2 (by linarith [show (7.9 : ℝ) ^ 2 = 62.41 by norm_num])
  -- `4.17 ≤ s_0(2) ≤ 4.21`
  have hs0 : AdversarialBco.Body2.s0 2 = Real.pi * Real.sqrt (Real.pi / 2) * (17 / 16) := by
    unfold AdversarialBco.Body2.s0; ring
  have hs0lo : (4.17 : ℝ) ≤ AdversarialBco.Body2.s0 2 := by
    rw [hs0]; linarith [mul_le_mul hpi1.le hs1 (by norm_num) (by linarith)]
  have hs0hi : AdversarialBco.Body2.s0 2 ≤ 4.21 := by
    rw [hs0]; linarith [mul_le_mul hpi2.le hs2 (Real.sqrt_nonneg _) (by linarith)]
  -- `ι_0(2) = 1/K` with `K = 16·10^5 (1 + T(2))^2 2^2 ln 4`, `8.8·10^6 ≤ K ≤ 7.1·10^8`
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 16 * 10 ^ 5 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * 2 ^ 2 * Real.log (2 * 2) :=
    ⟨_, rfl⟩
  have hι : AdversarialBco.Body2.iota0 2 = 1 / K := by
    rw [hKdef]; unfold AdversarialBco.Body2.iota0; rfl
  have hlog4 : Real.log (2 * 2) = 2 * Real.log 2 := by rw [Real.log_mul two_ne_zero two_ne_zero]; ring
  have hTT : (1 + AdversarialBco.Body2.Tz 2) ^ 2 ≤ 8.9 ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hTT' : (1 : ℝ) ≤ (1 + AdversarialBco.Body2.Tz 2) ^ 2 := one_le_pow₀ (by linarith)
  have hKhi : K ≤ 7.1e8 := by
    rw [hKdef, hlog4]; linarith [mul_le_mul hTT hl2.le (by linarith) (by norm_num)]
  have hKlo : 8.8e6 ≤ K := by
    rw [hKdef, hlog4]; linarith [mul_le_mul hTT' hl1.le (by norm_num) (by positivity)]
  -- `Θ(2) = ln Y`, `Y = 32 s_0(2)^2 K ∈ [2^29, 2^39]`
  have hTheta : AdversarialBco.Body2.Theta 2 = Real.log (32 * AdversarialBco.Body2.s0 2 ^ 2 * K) := by
    unfold AdversarialBco.Body2.Theta
    rw [hι, div_div_eq_mul_div, div_one]
    ring_nf
  have hss : AdversarialBco.Body2.s0 2 ^ 2 ≤ 4.21 ^ 2 := pow_le_pow_left₀ (by linarith) hs0hi 2
  have hss' : (4.17 : ℝ) ^ 2 ≤ AdversarialBco.Body2.s0 2 ^ 2 := pow_le_pow_left₀ (by norm_num) hs0lo 2
  have hY1 : (2 : ℝ) ^ 29 ≤ 32 * AdversarialBco.Body2.s0 2 ^ 2 * K := by
    linarith [mul_le_mul hss' hKlo (by norm_num) (by positivity)]
  have hY2 : 32 * AdversarialBco.Body2.s0 2 ^ 2 * K ≤ 2 ^ 39 := by
    linarith [mul_le_mul hss hKhi (by linarith) (by positivity)]
  have hΘ1 : 29 * Real.log 2 ≤ AdversarialBco.Body2.Theta 2 := by
    have e : Real.log ((2 : ℝ) ^ 29) = 29 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hTheta, ← e]
    exact Real.log_le_log (by norm_num) hY1
  have hΘ2 : AdversarialBco.Body2.Theta 2 ≤ 39 * Real.log 2 := by
    have e : Real.log ((2 : ℝ) ^ 39) = 39 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hTheta, ← e]
    exact Real.log_le_log (by positivity) hY2
  have hsq : Real.sqrt (2 * AdversarialBco.Body2.Theta 2) ≤ 7.36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num; linarith)
  -- `need(2) = K (3 + 2 s_0(2) (2 Θ(2))^{1/2})`
  have hneed : AdversarialBco.Body2.need 2 =
      K * (3 + 2 * AdversarialBco.Body2.s0 2 * Real.sqrt (2 * AdversarialBco.Body2.Theta 2)) := by
    unfold AdversarialBco.Body2.need
    rw [hι, mul_one_div, div_div_eq_mul_div]
    ring
  have hX : 3 + 2 * AdversarialBco.Body2.s0 2 * Real.sqrt (2 * AdversarialBco.Body2.Theta 2) ≤ 3 + 2 * 4.21 * 7.36 := by
    linarith [mul_le_mul hs0hi hsq (Real.sqrt_nonneg _) (by norm_num)]
  have hX0 : 0 ≤ 3 + 2 * AdversarialBco.Body2.s0 2 * Real.sqrt (2 * AdversarialBco.Body2.Theta 2) :=
    add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg _))
  refine ⟨?_, by linarith, by linarith⟩
  rw [hneed]
  linarith [mul_le_mul hKhi hX hX0 (by norm_num)]

/-- Lemma 4.1: `need(z) ≤ 10^8 z^10` for `z ≥ 2`. -/
theorem AdversarialBco.Body2.penalty_need (z : ℝ) (hz : 2 ≤ z) : AdversarialBco.Body2.need z ≤ 10 ^ 8 * z ^ 10 := by
  obtain ⟨hN2, hT7, hΘ20⟩ := AdversarialBco.Body2.penalty_numeric
  have hz0 : 0 < z := by linarith
  have hz2 : 1 ≤ z / 2 := by linarith
  have hl4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
    linarith [Real.log_two_gt_d9]
  -- `need y = 4·10^5 (1 + T(y))^2 y^4 ln(2y) (3 + 2 s_0(y) (2 Θ(y))^{1/2})`
  have hform : ∀ y : ℝ, AdversarialBco.Body2.need y = 4 * 10 ^ 5 * (1 + AdversarialBco.Body2.Tz y) ^ 2 * y ^ 4 *
      Real.log (2 * y) * (3 + 2 * AdversarialBco.Body2.s0 y * Real.sqrt (2 * AdversarialBco.Body2.Theta y)) := by
    intro y
    unfold AdversarialBco.Body2.need AdversarialBco.Body2.iota0
    rw [mul_one_div, div_div_eq_mul_div]
    ring
  have hN2' : AdversarialBco.Body2.need 2 = 4 * 10 ^ 5 * (1 + AdversarialBco.Body2.Tz 2) ^ 2 * 16 * Real.log 4 *
      (3 + 2 * AdversarialBco.Body2.s0 2 * Real.sqrt (2 * AdversarialBco.Body2.Theta 2)) := by
    rw [hform 2, show (2 : ℝ) * 2 = 4 by norm_num]; ring
  have hT := AdversarialBco.Body2.penalty_T_le z hz
  have hΘ := AdversarialBco.Body2.penalty_Theta_le z hz
  have hs0z : AdversarialBco.Body2.s0 z = z / 2 * AdversarialBco.Body2.s0 2 := by
    unfold AdversarialBco.Body2.s0; ring
  have hs02 : 0 ≤ AdversarialBco.Body2.s0 2 := by unfold AdversarialBco.Body2.s0; positivity
  have hlogz : Real.log (2 * z) = Real.log 4 + Real.log (z / 2) := by
    rw [show 2 * z = 4 * (z / 2) by ring, Real.log_mul (by norm_num) (by positivity)]
  have hx0 : 0 ≤ Real.log (z / 2) := Real.log_nonneg hz2
  have hxe : Real.exp (Real.log (z / 2)) = z / 2 := Real.exp_log (by positivity)
  rw [hform z, hlogz, hs0z]
  rw [hN2'] at hN2
  -- variables in place of the transcendental atoms
  generalize Real.log (z / 2) = x at hT hΘ hx0 hxe ⊢
  generalize Real.log 4 = l at hN2 hΘ hl4 ⊢
  generalize AdversarialBco.Body2.Tz z = T at hT ⊢
  generalize AdversarialBco.Body2.Tz 2 = T2 at hN2 hT hΘ hT7 ⊢
  generalize AdversarialBco.Body2.Theta z = Θ at hΘ ⊢
  generalize AdversarialBco.Body2.Theta 2 = Θ2 at hN2 hΘ hΘ20 ⊢
  generalize AdversarialBco.Body2.s0 2 = s at hN2 hs02 ⊢
  have hl0 : 0 < l := by linarith
  have hT20 : 0 < T2 := by linarith
  set q := 24 / (T2 * (1 + T2)) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by positivity)]; nlinarith
  have hb0 : 0 ≤ 1 / l := by positivity
  have hb1 : 1 / l ≤ 1 := by rw [div_le_one hl0]; exact hl4
  set r := (6 + q + 1 / l) / (2 * Θ2) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by linarith)]; linarith
  have hrx : 1 ≤ 1 + r * x := by have := mul_nonneg hr0 hx0; linarith
  -- `(2Θ)^{1/2} ≤ (2Θ_2)^{1/2} (1 + r x)`
  have hsqrt : Real.sqrt (2 * Θ) ≤ Real.sqrt (2 * Θ2) * (1 + r * x) := by
    have e : 2 * Θ2 * (2 * r) = 2 * (6 + q + 1 / l) := by rw [hr]; field_simp
    have h1 : 2 * Θ ≤ 2 * Θ2 * (1 + r * x) ^ 2 := by
      have h2 : 0 ≤ 2 * Θ2 * (r * x) ^ 2 := by positivity
      have h3 : 2 * Θ2 * (1 + r * x) ^ 2 = 2 * Θ2 + (2 * Θ2 * (2 * r)) * x + 2 * Θ2 * (r * x) ^ 2 := by ring
      rw [h3, e]
      linarith
    calc Real.sqrt (2 * Θ) ≤ Real.sqrt (2 * Θ2 * (1 + r * x) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * Θ2) * (1 + r * x) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq (by linarith)]
  -- `3 + 2 s_0(z) (2Θ)^{1/2} ≤ (z/2)(1 + r x) X_2`
  set X2 := 3 + 2 * s * Real.sqrt (2 * Θ2) with hX2
  have hsq0 := Real.sqrt_nonneg (2 * Θ2)
  have hX20 : 0 ≤ X2 := by positivity
  have hXz : 3 + 2 * (z / 2 * s) * Real.sqrt (2 * Θ) ≤ z / 2 * (1 + r * x) * X2 := by
    have hA : 0 ≤ 2 * (z / 2 * s) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsqrt hA
    have h2 : (3 : ℝ) ≤ 3 * (z / 2 * (1 + r * x)) := by
      have := one_le_mul_of_one_le_of_one_le hz2 hrx; linarith
    have e : z / 2 * (1 + r * x) * X2 = 3 * (z / 2 * (1 + r * x)) + 2 * (z / 2 * s) * (Real.sqrt (2 * Θ2) * (1 + r * x)) := by
      rw [hX2]; ring
    rw [e]; linarith
  have hXz0 : 0 ≤ 3 + 2 * (z / 2 * s) * Real.sqrt (2 * Θ) := by
    have := Real.sqrt_nonneg (2 * Θ); positivity
  -- `need z ≤ need 2 (z/2)^5 (1 + q x)(1 + x/l)(1 + r x)`
  have hlx : l + x = l * (1 + 1 / l * x) := by field_simp
  have hlx0 : 0 ≤ l + x := by linarith
  have hTq : 0 ≤ (1 + T2) ^ 2 * (1 + q * x) := by have := mul_nonneg hq0 hx0; positivity
  have hP : 4 * 10 ^ 5 * (1 + T) ^ 2 * z ^ 4 * (l + x) * (3 + 2 * (z / 2 * s) * Real.sqrt (2 * Θ)) ≤
      4 * 10 ^ 5 * (1 + T2) ^ 2 * 16 * l * X2 * (z / 2) ^ 5 * ((1 + q * x) * (1 + 1 / l * x) * (1 + r * x)) := by
    calc 4 * 10 ^ 5 * (1 + T) ^ 2 * z ^ 4 * (l + x) * (3 + 2 * (z / 2 * s) * Real.sqrt (2 * Θ)) ≤
        4 * 10 ^ 5 * ((1 + T2) ^ 2 * (1 + q * x)) * z ^ 4 * (l + x) * (z / 2 * (1 + r * x) * X2) := by
          refine mul_le_mul ?_ hXz hXz0 (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ hlx0
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hT (by norm_num)
      _ = 4 * 10 ^ 5 * (1 + T2) ^ 2 * 16 * l * X2 * (z / 2) ^ 5 *
          ((1 + q * x) * (1 + 1 / l * x) * (1 + r * x)) := by rw [hlx]; ring
  -- the product is at most `exp (5x) = (z/2)^5`
  have hE := AdversarialBco.Body2.exp_prod_le q (1 / l) r x hq0 hb0 hr0 hx0
  have hE5 : Real.exp ((q + 1 / l + r) * x) ≤ (z / 2) ^ 5 := by
    rw [← hxe, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by push_cast; linarith) hx0)
  have hN0 : 0 ≤ 4 * 10 ^ 5 * (1 + T2) ^ 2 * 16 * l * X2 * (z / 2) ^ 5 := by positivity
  calc _ ≤ _ := hP
    _ ≤ 4 * 10 ^ 5 * (1 + T2) ^ 2 * 16 * l * X2 * (z / 2) ^ 5 * (z / 2) ^ 5 :=
        mul_le_mul_of_nonneg_left (hE.trans hE5) hN0
    _ ≤ 1024 * 10 ^ 8 * (z / 2) ^ 5 * (z / 2) ^ 5 := by
        have h5 : 0 ≤ (z / 2) ^ 5 := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN2 h5) h5
    _ = 10 ^ 8 * z ^ 10 := by ring
