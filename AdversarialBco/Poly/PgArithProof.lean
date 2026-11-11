/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgArith
public import AdversarialBco.Body2.Gauss1

@[expose] public section

/-!
# The arithmetic of Theorem 8.3: proofs

Proofs of the interface statements of `AdversarialBco/Poly/PgArith.lean`: the leaves, among them `pg_N_size`,
`pg_step`, `pg_conclusion`, `pg_moments`, and `qtail_a_ge` from `Body2.Qtail_one_bounds`, then one assembly per `Prop`.
-/

namespace AdversarialBco.Poly

/-! ## Leaves -/

theorem pg_propAi (x : ℝ) (hx : 0 < x) (h : x - 1 - Real.log x < 0.0012) : x ≤ 1.05 := by
  by_cases hxle : x ≤ 1.05
  · exact hxle
  · push_neg at hxle
    have hpos105 : 0 < (1.05 : ℝ) := by norm_num
    have hlogdiv : Real.log x - Real.log 1.05 = Real.log (x / 1.05) := by
      rw [Real.log_div (ne_of_gt hx) (ne_of_gt hpos105)]
    have hxdivpos : 0 < x / 1.05 := div_pos hx hpos105
    have hlogbound : Real.log (x / 1.05) ≤ x / 1.05 - 1 :=
      Real.log_le_sub_one_of_pos hxdivpos
    have hxbound : x / 1.05 - 1 ≤ x - 1.05 := by
      have h_eq : x / 1.05 - 1 = (x - 1.05) / 1.05 := by ring
      rw [h_eq]
      have hnonneg : 0 ≤ x - 1.05 := by linarith
      have hone : (1 : ℝ) ≤ 1.05 := by norm_num
      exact div_le_self hnonneg hone
    have hchain : Real.log x - Real.log 1.05 ≤ x - 1.05 := by
      linarith
    have hineq : x - 1 - Real.log x ≥ 1.05 - 1 - Real.log 1.05 := by
      linarith
    have hlog105_lt : Real.log (1.05 : ℝ) < 0.0488 := by
      rw [Real.log_lt_iff_lt_exp hpos105]
      have hexpsum : (1 : ℝ) + 0.0488 + (0.0488 ^ 2) / 2 + (0.0488 ^ 3) / 6 ≤ Real.exp 0.0488 := by
        have hsum := Real.sum_le_exp_of_nonneg (show 0 ≤ (0.0488 : ℝ) from by norm_num) 4
        simpa [Finset.sum_range_succ, Nat.factorial] using hsum
      have hsum_gt : (1.05 : ℝ) < (1 : ℝ) + 0.0488 + (0.0488 ^ 2) / 2 + (0.0488 ^ 3) / 6 := by
        norm_num
      linarith
    have h_contr : 1.05 - 1 - Real.log (1.05 : ℝ) > 0.0012 := by
      linarith
    linarith

theorem pg_c2_bound : 0 < pgC2 ∧ pgC2 ≤ 1.1742 := by
  have hpos : 0 < pgC2 := by
    unfold pgC2
    positivity
  have hub : pgC2 ≤ 1.1742 := by
    unfold pgC2
    have hexp : Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
    have hpi : 3.141592 < Real.pi := Real.pi_gt_d6
    have hsqrt : (2.5066 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      have hsq : (2.5066 : ℝ) ^ 2 = 6.28304356 := by norm_num
      have h2pi : (6.28304356 : ℝ) < 2 * Real.pi := by
        nlinarith
      calc
        (2.5066 : ℝ) = Real.sqrt ((2.5066 : ℝ) ^ 2) := by
          rw [Real.sqrt_sq (show 0 ≤ (2.5066 : ℝ) from by norm_num)]
        _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by
          rw [hsq]
          exact h2pi.le)
    have hdenpos : 0 < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
    have hpos25 : 0 < (2.5066 : ℝ) := by norm_num
    have hnum : 8 * Real.exp (-1) ≤ 8 * 0.3678794412 := by nlinarith
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := by positivity
    have hdiv1 : 8 * Real.exp (-1) / Real.sqrt (2 * Real.pi) ≤
                8 * 0.3678794412 / Real.sqrt (2 * Real.pi) :=
      div_le_div_of_nonneg_right hnum h_sqrt_nonneg
    have hdiv2 : 8 * 0.3678794412 / Real.sqrt (2 * Real.pi) ≤
                8 * 0.3678794412 / (2.5066 : ℝ) :=
      div_le_div_of_nonneg_left (by
        have : (0 : ℝ) ≤ 8 * (0.3678794412 : ℝ) := by norm_num
        exact this) hpos25 hsqrt
    have hfinal : 8 * 0.3678794412 / (2.5066 : ℝ) ≤ 1.1742 := by
      norm_num
    exact le_trans (le_trans hdiv1 hdiv2) hfinal
  exact And.intro hpos hub

theorem pg_corAi (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : pgEh d ρ < 0.0012 * pgKappa := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have h1pρpos : 0 < 1 + ρ := by linarith
  have hlog_lower : Real.log 2 ≤ Real.log (1 + ρ) :=
    Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by linarith)
  have h_log_lower : (0.6931471803 : ℝ) < Real.log (1 + ρ) := by
    linarith [Real.log_two_gt_d9, hlog_lower]
  have h_d_sq : (1 : ℝ) ≤ d ^ 2 := by
    nlinarith
  unfold pgEh pgLD pgLam pgKappa pgPB
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (1 + ρ))]
  -- Goal: (1/8)^2 / (922 * d^2 * (2 * Real.log (1+ρ)) * ((1/8)*(1254/1000)*ρ)) < 0.0012 * (1/8)
  have h_denom_pos : 0 < 922 * d ^ 2 * (2 * Real.log (1 + ρ)) * ((1/8 : ℝ) * (1254/1000 : ℝ) * ρ) := by
    positivity
  rw [div_lt_iff₀ h_denom_pos]
  -- Goal: (1/8)^2 < (0.0012 * (1/8)) * (922 * d^2 * (2 * Real.log (1+ρ)) * ((1/8)*(1254/1000)*ρ))
  -- Rearrange: the RHS constant is C = 0.0012*(1/8)*922*2*(1/8)*1.254
  -- We need: 1/64 < C * d^2 * Real.log(1+ρ) * ρ
  -- Using d^2 ≥ 1, ρ ≥ 1, Real.log(1+ρ) > 0.6931471803:
  -- RHS > C * 1 * 0.6931471803 * 1 = C * 0.6931471803
  -- So it suffices: 1/64 < C * 0.6931471803
  -- Compute C * 0.6931471803 with norm_num
  have h_sufficient : (1/64 : ℝ) < ((0.0012 : ℝ) * (1/8 : ℝ) * (922 : ℝ) * (2 : ℝ) * ((1/8 : ℝ) * (1254/1000 : ℝ))) * (0.6931471803 : ℝ) := by
    norm_num
  -- Now combine: RHS = C * d^2 * Real.log(1+ρ) * ρ ≥ C * 1 * 0.6931471803 * 1 > 1/64
  have h_goal : (1/8 : ℝ)^2 < ((0.0012 : ℝ) * (1/8 : ℝ)) * (922 * d ^ 2 * (2 * Real.log (1 + ρ)) * ((1/8 : ℝ) * (1254/1000 : ℝ) * ρ)) := by
    -- Factor out the constant
    calc
      (1/8 : ℝ)^2 = (1/64 : ℝ) := by norm_num
      _ < ((0.0012 : ℝ) * (1/8 : ℝ) * (922 : ℝ) * (2 : ℝ) * ((1/8 : ℝ) * (1254/1000 : ℝ))) * (0.6931471803 : ℝ) := h_sufficient
      _ ≤ ((0.0012 : ℝ) * (1/8 : ℝ) * (922 : ℝ) * (2 : ℝ) * ((1/8 : ℝ) * (1254/1000 : ℝ))) * (d ^ 2 * Real.log (1 + ρ) * ρ) := by
        -- Need to show 0.6931471803 ≤ d^2 * Real.log(1+ρ) * ρ
        -- Since d^2 ≥ 1, ρ ≥ 1, Real.log(1+ρ) > 0.6931471803
        have h_prod : (0.6931471803 : ℝ) ≤ d ^ 2 * Real.log (1 + ρ) * ρ := by
          have h_log_nonneg : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by linarith : 1 ≤ 1 + ρ)
          have h_d2_nonneg : 0 ≤ d ^ 2 := pow_two_nonneg d
          have h_ρ_nonneg : 0 ≤ ρ := by linarith
          have h1 : (0.6931471803 : ℝ) ≤ Real.log (1 + ρ) := by linarith
          have h_first : (1 : ℝ) * (0.6931471803 : ℝ) ≤ d ^ 2 * Real.log (1 + ρ) :=
            mul_le_mul h_d_sq h1 (by norm_num : 0 ≤ (0.6931471803 : ℝ)) h_d2_nonneg
          have h_second : ((1 : ℝ) * (0.6931471803 : ℝ)) * (1 : ℝ) ≤ (d ^ 2 * Real.log (1 + ρ)) * ρ :=
            mul_le_mul h_first hρ (by norm_num : 0 ≤ (1 : ℝ)) (mul_nonneg h_d2_nonneg h_log_nonneg)
          calc
            (0.6931471803 : ℝ) = ((1 : ℝ) * (0.6931471803 : ℝ)) * (1 : ℝ) := by norm_num
            _ ≤ (d ^ 2 * Real.log (1 + ρ)) * ρ := h_second
            _ = d ^ 2 * Real.log (1 + ρ) * ρ := by ring
        nlinarith
      _ = ((0.0012 : ℝ) * (1/8 : ℝ)) * (922 * d ^ 2 * (2 * Real.log (1 + ρ)) * ((1/8 : ℝ) * (1254/1000 : ℝ) * ρ)) := by ring
  exact h_goal

theorem pg_corAii (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgEh d ρ < pgKappa ^ 2 / (32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d)) := by
  have hκpos : 0 < pgKappa := by
    unfold pgKappa; norm_num
  have hdpos : 0 < d := by linarith
  have hdsqpos : 0 < d ^ 2 := pow_pos hdpos 2
  have hLam_pos : 0 < pgLam ρ := by
    unfold pgLam
    refine Real.sqrt_pos.mpr ?_
    have hlog := Real.log_pos (by linarith : 1 < 1 + ρ)
    nlinarith
  have hLam_sq_pos : 0 < pgLam ρ ^ 2 := pow_pos hLam_pos 2
  have hLDpos : 0 < pgLD ρ := by
    unfold pgLD pgKappa pgPB
    positivity
  have hκsq_pos : 0 < pgKappa ^ 2 := pow_pos hκpos 2
  have hdenom1_pos : 0 < 922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by positivity
  have hdenom2_pos : 0 < 32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d) := by
    have hinner : 0 < pgC2 * pgLD ρ + pgKappa / d := by
      have hc2pos : 0 < pgC2 := by
        unfold pgC2
        positivity
      positivity
    positivity
  unfold pgEh
  -- Goal: pgKappa ^ 2 / (922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ) <
  --       pgKappa ^ 2 / (32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d))
  refine ((div_lt_div_iff_of_pos_left hκsq_pos hdenom1_pos hdenom2_pos).mpr ?_)
  -- Goal: 32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d) < 922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ
  have hmain : 32 * (pgC2 * pgLD ρ + pgKappa / d) < 922 * pgLam ρ ^ 2 * pgLD ρ := by
    set L := pgLD ρ with hL
    set c2 := pgC2 with hc2
    set κ := pgKappa with hκ
    set lamSq := pgLam ρ ^ 2 with hlamSq
    have hc2_le_8 : c2 ≤ 8 := by
      unfold c2 pgC2
      have hexp_le_one : Real.exp (-1) ≤ 1 :=
        calc
          Real.exp (-1) ≤ Real.exp (0 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
          _ = 1 := Real.exp_zero
      have hsqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [Real.one_le_sqrt]
        nlinarith [Real.pi_gt_three]
      have hpos : 0 < Real.sqrt (2 * Real.pi) :=
        Real.sqrt_pos.mpr (by nlinarith [Real.pi_pos])
      have hnum : Real.exp (-1) ≤ Real.sqrt (2 * Real.pi) := by linarith
      have hdiv : Real.exp (-1) / Real.sqrt (2 * Real.pi) ≤ 1 :=
        (div_le_one hpos).mpr hnum
      calc
        8 * Real.exp (-1) / Real.sqrt (2 * Real.pi) = 8 * (Real.exp (-1) / Real.sqrt (2 * Real.pi)) := by ring
        _ ≤ 8 * 1 := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 8 := by ring
    have h_one_div_d_le_one : 1 / d ≤ 1 :=
      (div_le_one hdpos).mpr hd
    have hκ_div_d_le_κ : κ / d ≤ κ := by
      calc
        κ / d = κ * (1 / d) := by ring
        _ ≤ κ * 1 := mul_le_mul_of_nonneg_left h_one_div_d_le_one hκpos.le
        _ = κ := by ring
    have hκ_le_L : κ ≤ L := by
      unfold L pgLD κ pgKappa
      have hρpos : 0 < ρ := by linarith
      have h : (1 : ℝ) ≤ (1254/1000 : ℝ) * ρ := by
        nlinarith
      have h' : (1/8 : ℝ) * 1 ≤ (1/8 : ℝ) * ((1254/1000 : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (1/8 : ℝ))
      calc
        (1/8 : ℝ) = (1/8 : ℝ) * 1 := by ring
        _ ≤ (1/8 : ℝ) * ((1254/1000 : ℝ) * ρ) := h'
        _ = (1/8 : ℝ) * (1254/1000 : ℝ) * ρ := by ring
    have hlamSq_gt : 288/922 < lamSq := by
      unfold lamSq pgLam
      have hnonneg : 0 ≤ 2 * Real.log (1 + ρ) := by
        have hlog := Real.log_pos (by linarith : 1 < 1 + ρ)
        nlinarith
      rw [Real.sq_sqrt hnonneg]
      have hlog_ge_log2 : Real.log 2 ≤ Real.log (1 + ρ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 1 + ρ)
      have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      have h : 288/922 < 2 * Real.log 2 := by nlinarith
      nlinarith
    have hLHS_le : 32 * (c2 * L + κ / d) ≤ 288 * L := by
      have h1 : 32 * (c2 * L + κ / d) = 32 * c2 * L + 32 * (κ / d) := by ring
      have h2 : 32 * c2 * L ≤ 32 * 8 * L := by
        nlinarith
      have h3 : 32 * (κ / d) ≤ 32 * κ := by
        nlinarith
      have h4 : 32 * κ ≤ 32 * L := by
        nlinarith
      have h5 : 32 * 8 * L + 32 * L = 288 * L := by ring
      nlinarith
    have hRHS_gt : 288 * L < 922 * lamSq * L := by
      have hpos922 : 0 < (922 : ℝ) := by norm_num
      calc
        288 * L = 922 * ((288/922) * L) := by ring
        _ < 922 * (lamSq * L) := by
          refine mul_lt_mul_of_pos_left ?_ hpos922
          exact mul_lt_mul_of_pos_right hlamSq_gt hLDpos
        _ = 922 * lamSq * L := by ring
    nlinarith
  -- Multiply both sides by d^2 > 0
  calc
    32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d) = d ^ 2 * (32 * (pgC2 * pgLD ρ + pgKappa / d)) := by ring
    _ < d ^ 2 * (922 * pgLam ρ ^ 2 * pgLD ρ) := mul_lt_mul_of_pos_left hmain hdsqpos
    _ = 922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by ring

theorem pg_corAiii (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 1.6 * pgLD ρ * pgEh d ρ ≤ (pgTaub d ρ / 2) ^ 2 := by
  have hdpos : 0 < d := by linarith
  have hlogpos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
  have hlampos : 0 < pgLam ρ := by
    dsimp [pgLam]
    have h : 0 < 2 * Real.log (1 + ρ) := by nlinarith
    exact Real.sqrt_pos.mpr h
  have hkappapos : 0 < pgKappa := by
    dsimp [pgKappa]
    norm_num
  have hPBpos : 0 < pgPB := by
    dsimp [pgPB]
    norm_num
  have hM : 0 < pgKappa ^ 2 / (d ^ 2 * pgLam ρ ^ 2) := by positivity
  have hdiv : (1.6 : ℝ) / 922 ≤ (1 : ℝ) / 576 := by
    have hpos922 : 0 < (922 : ℝ) := by norm_num
    have hpos576 : 0 < (576 : ℝ) := by norm_num
    rw [div_le_div_iff₀ hpos922 hpos576]
    norm_num
  calc
    1.6 * pgLD ρ * pgEh d ρ
        = 1.6 * (pgKappa * pgPB * ρ) * (pgKappa ^ 2 / (922 * d ^ 2 * pgLam ρ ^ 2 * (pgKappa * pgPB * ρ))) := rfl
    _ = 1.6 * pgKappa ^ 2 / (922 * d ^ 2 * pgLam ρ ^ 2) := by
      field_simp [hlampos.ne.symm, hdpos.ne.symm, hkappapos.ne.symm, hPBpos.ne.symm]
    _ = ((1.6 : ℝ) / 922) * (pgKappa ^ 2 / (d ^ 2 * pgLam ρ ^ 2)) := by ring
    _ ≤ ((1 : ℝ) / 576) * (pgKappa ^ 2 / (d ^ 2 * pgLam ρ ^ 2)) := by
      apply mul_le_mul_of_nonneg_right hdiv
      positivity
    _ = pgKappa ^ 2 / (576 * d ^ 2 * pgLam ρ ^ 2) := by ring
    _ = (pgKappa / (12 * d * pgLam ρ) / 2) ^ 2 := by ring
    _ = (pgTaub d ρ / 2) ^ 2 := rfl

theorem pg_bias_u (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ 1 / (145600 * d ^ 3 * pgLam ρ ^ 3 * ρ ^ 2) := by
  have hpos_d : 0 < d := by linarith
  have hpos_ρ : 0 < ρ := by linarith
  have hpos_lam : 0 < pgLam ρ := by
    refine Real.sqrt_pos.mpr ?_
    have : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    positivity
  have hpos_ld : 0 < pgLD ρ := by
    unfold pgLD pgKappa pgPB
    positivity
  have hpos_delta : 0 < pgDelta d ρ := by
    unfold pgDelta pgKappa pgPB
    have hpos_inner : 0 < 4 + pgPB ^ 2 * d := by
      have : 0 ≤ pgPB ^ 2 * d := by
        unfold pgPB
        positivity
      linarith
    have : 0 < Real.sqrt (4 + pgPB ^ 2 * d) := Real.sqrt_pos.mpr hpos_inner
    positivity
  have h_sqrt_ge_two : 2 ≤ Real.sqrt (4 + pgPB ^ 2 * d) := by
    have h4 : (4 : ℝ) ≤ 4 + pgPB ^ 2 * d := by
      have : 0 ≤ pgPB ^ 2 * d := by positivity
      linarith
    calc
      2 = Real.sqrt (4 : ℝ) := by norm_num
      _ ≤ Real.sqrt (4 + pgPB ^ 2 * d) := Real.sqrt_le_sqrt h4
  have h_nonneg_coeff : 0 ≤ 922 * 9 * 7 * pgPB := by
    unfold pgPB
    positivity
  have h_key : (145600 : ℝ) ≤ 922 * 9 * 7 * pgPB * Real.sqrt (4 + pgPB ^ 2 * d) := by
    have h_bound : 922 * 9 * 7 * pgPB * 2 ≤ 922 * 9 * 7 * pgPB * Real.sqrt (4 + pgPB ^ 2 * d) :=
      mul_le_mul_of_nonneg_left h_sqrt_ge_two h_nonneg_coeff
    have h_calc : (145600 : ℝ) ≤ 922 * 9 * 7 * pgPB * 2 := by
      unfold pgPB
      norm_num
    linarith
  -- Compute the algebraic simplification:
  -- pgEta d ρ * pgLD ρ * (1 + √d) = 1 / (922 * 9 * 7 * pgPB * d^3 * (pgLam ρ)^3 * ρ^2 * √(4 + pgPB^2 * d))
  have h_simplify : pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) =
      1 / (922 * 9 * 7 * pgPB * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 * Real.sqrt (4 + pgPB ^ 2 * d)) := by
    unfold pgEta pgEh pgTmin pgDelta pgLD pgKappa pgPB
    field_simp
  rw [h_simplify]
  -- Goal: 1 / (922 * 9 * 7 * pgPB * d^3 * (pgLam ρ)^3 * ρ^2 * √(4 + pgPB^2 * d)) ≤
  --       1 / (145600 * d^3 * (pgLam ρ)^3 * ρ^2)
  -- Since all denominators are positive, we can cross-multiply
  have hpos_sqrt_delta' : 0 < Real.sqrt (4 + pgPB ^ 2 * d) := by
    refine Real.sqrt_pos.mpr ?_
    have : 0 ≤ pgPB ^ 2 * d := by
      unfold pgPB
      positivity
    linarith
  have hpos_denom1 : 0 < 922 * 9 * 7 * pgPB * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 * Real.sqrt (4 + pgPB ^ 2 * d) := by
    have hpos_rest : 0 < 922 * 9 * 7 * pgPB := by
      unfold pgPB
      positivity
    have hpos_powers : 0 < d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by
      positivity
    positivity
  have hpos_denom2 : 0 < 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by
    positivity
  -- Using: 1/a ≤ 1/b ↔ b ≤ a for positive a, b
  rw [one_div_le_one_div hpos_denom1 hpos_denom2]
  -- Goal: 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 ≤
  --       922 * 9 * 7 * pgPB * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 * Real.sqrt (4 + pgPB ^ 2 * d)
  -- Cancel the common factor d^3 * (pgLam ρ)^3 * ρ^2 (all positive)
  have hpos_common : 0 < d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by
    positivity
  -- Use mul_le_mul_of_nonneg_right after factoring
  -- Actually, let's rewrite the goal as:
  -- (d^3 * (pgLam ρ)^3 * ρ^2) * 145600 ≤ (d^3 * (pgLam ρ)^3 * ρ^2) * (922 * 9 * 7 * pgPB * Real.sqrt (4 + pgPB ^ 2 * d))
  -- Then cancel
  have h_goal : d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 * (145600 : ℝ) ≤
      d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 * (922 * 9 * 7 * pgPB * Real.sqrt (4 + pgPB ^ 2 * d)) := by
    apply mul_le_mul_of_nonneg_left h_key
    positivity
  -- The goal and h_goal differ only by associativity/commutativity
  -- Use simpa with ring to match
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_goal

theorem pg_bias_test (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    Real.sqrt 2 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) ≤ pgTaub d ρ / 8 ∧
      pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ pgKappa / 80 ∧ pgTaub d ρ / 8 ≤ pgKappa / (16 * d) := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have hdne : d ≠ 0 := by linarith
  have hρne : ρ ≠ 0 := by linarith
  have hLpos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
  have hL_ge_log2 : Real.log 2 ≤ Real.log (1 + ρ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 1 + ρ)
  have hs_gt_one : 1 < Real.sqrt (2 * Real.log (1 + ρ)) := by
    have h_inner : (1 : ℝ) < 2 * Real.log (1 + ρ) := by
      have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      have hlog2_le : Real.log 2 ≤ Real.log (1 + ρ) := hL_ge_log2
      nlinarith
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ < Real.sqrt (2 * Real.log (1 + ρ)) :=
        Real.sqrt_lt_sqrt (by norm_num) h_inner
  have h_pgLam_pos : 0 < pgLam ρ := by
    unfold pgLam
    refine Real.sqrt_pos.mpr ?_
    nlinarith
  have h_pgLam_ne : pgLam ρ ≠ 0 := by linarith
  have h_pgKappa_pos : 0 < pgKappa := by unfold pgKappa; norm_num
  have h_pgLD_pos : 0 < pgLD ρ := by
    unfold pgLD pgKappa pgPB
    positivity
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have h_sqrt2_lt_three_halves : Real.sqrt 2 < 3/2 := by
    refine (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3/2)).mpr ?_
    norm_num
  have h_log2_gt_69_100 : 69/100 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h_pgLam_sq : (pgLam ρ) ^ 2 = 2 * Real.log (1 + ρ) := by
    unfold pgLam
    rw [Real.sq_sqrt (by nlinarith : 0 ≤ 2 * Real.log (1 + ρ))]
  -- Goal 2: pgEta * pgLD * (1 + sqrt(d)) ≤ pgKappa / 80
  have h2 : pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ pgKappa / 80 := by
    have h_bias := pg_bias_u d ρ hd hρ
    refine le_trans h_bias ?_
    have h_pgKappa_80 : pgKappa / 80 = (1 : ℝ)/640 := by unfold pgKappa; norm_num
    rw [h_pgKappa_80]
    have h_denom_pos : 0 < 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by positivity
    refine (one_div_le_one_div h_denom_pos (by norm_num : 0 < (640 : ℝ))).mpr ?_
    have h_prod : (640 : ℝ) ≤ 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by
      have h_d3 : (1 : ℝ) ≤ d ^ 3 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
          _ ≤ d ^ 3 := by gcongr
      have h_rho2 : (1 : ℝ) ≤ ρ ^ 2 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
          _ ≤ ρ ^ 2 := by gcongr
      have h_lam3 : (1 : ℝ) ≤ (pgLam ρ) ^ 3 := by nlinarith
      have h145600 : (640 : ℝ) ≤ 145600 := by norm_num
      calc
        (640 : ℝ) = 640 * 1 * 1 * 1 := by norm_num
        _ ≤ 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by gcongr
    exact h_prod
  -- Goal 3: pgTaub / 8 ≤ pgKappa / (16 * d)
  have h3 : pgTaub d ρ / 8 ≤ pgKappa / (16 * d) := by
    unfold pgTaub pgKappa
    have h_expr : ((1 : ℝ)/8) / (12 * d * pgLam ρ) / 8 = 1 / (768 * d * pgLam ρ) := by ring
    rw [h_expr]
    have h_expr2 : (1/8 : ℝ) / (16 * d) = 1 / (128 * d) := by ring
    rw [h_expr2]
    have h_denom1_pos : 0 < 768 * d * pgLam ρ := by positivity
    have h_denom2_pos : 0 < 128 * d := by positivity
    refine (one_div_le_one_div h_denom1_pos h_denom2_pos).mpr ?_
    have h_lam_gt_one : 1 < pgLam ρ := by
      unfold pgLam; exact hs_gt_one
    nlinarith
  -- Goal 1: sqrt(2) * (pgEta * pgLD * (1 + sqrt(d))) ≤ pgTaub / 8
  have h1 : Real.sqrt 2 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) ≤ pgTaub d ρ / 8 := by
    have h_bias := pg_bias_u d ρ hd hρ
    have h_nonneg_inner : 0 ≤ pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) := by
      have h_eta_nonneg : 0 ≤ pgEta d ρ := by
        unfold pgEta pgEh pgTmin pgLD pgDelta pgKappa pgPB
        positivity
      have h_ld_nonneg : 0 ≤ pgLD ρ := by linarith
      have h_sqrt_nonneg : 0 ≤ 1 + Real.sqrt d := by nlinarith [Real.sqrt_nonneg d]
      positivity
    have h_mul : Real.sqrt 2 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) ≤
        Real.sqrt 2 * (1 / (145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2)) := by
      nlinarith
    refine le_trans h_mul ?_
    unfold pgTaub pgKappa
    have h_expr : ((1 : ℝ)/8) / (12 * d * pgLam ρ) / 8 = 1 / (768 * d * pgLam ρ) := by ring
    rw [h_expr]
    have h_denom1_pos : 0 < 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2 := by positivity
    have h_denom2_pos : 0 < 768 * d * pgLam ρ := by positivity
    field_simp [hdne, hρne, h_pgLam_ne]
    -- Goal: Real.sqrt 2 * 768 * d * pgLam ρ ≤ 145600 * d ^ 3 * (pgLam ρ) ^ 3 * ρ ^ 2
    rw [h_pgLam_sq]
    ring_nf
    -- Goal: Real.sqrt 2 * 768 ≤ 291200 * d ^ 2 * Real.log (1 + ρ) * ρ ^ 2
    have h_bound : Real.sqrt 2 * 768 ≤ 291200 * d ^ 2 * Real.log (1 + ρ) * ρ ^ 2 := by
      have h_left : Real.sqrt 2 * 768 < 1152 := by nlinarith
      have h_right : 200928 ≤ 291200 * d ^ 2 * Real.log (1 + ρ) * ρ ^ 2 := by
        have h_d2 : (1 : ℝ) ≤ d ^ 2 := by
          calc
            (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
            _ ≤ d ^ 2 := by gcongr
        have h_rho2 : (1 : ℝ) ≤ ρ ^ 2 := by
          calc
            (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
            _ ≤ ρ ^ 2 := by gcongr
        have h_log_ge : 69/100 ≤ Real.log (1 + ρ) := by linarith
        calc
          200928 = 291200 * (69/100) * 1 * 1 := by norm_num
          _ ≤ 291200 * Real.log (1 + ρ) * d ^ 2 * ρ ^ 2 := by gcongr
          _ = 291200 * d ^ 2 * Real.log (1 + ρ) * ρ ^ 2 := by ring
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_bound
  exact And.intro h1 (And.intro h2 h3)

theorem pg_eta_sq (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 0 ≤ pgEta d ρ ∧ (1 + pgEta d ρ) ^ 2 ≤ 5 / 4 := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have hsqrt_d_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have h_one_plus_sqrt_d_pos : 0 < 1 + Real.sqrt d := by linarith
  have h_one_plus_sqrt_d_ge_two : 2 ≤ 1 + Real.sqrt d := by
    have hsqrt_d_ge_one : 1 ≤ Real.sqrt d := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
    linarith
  have hLam_pos : 0 < pgLam ρ := by
    dsimp [pgLam]
    have hlog_pos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    positivity
  have hLam_ge_one : 1 ≤ pgLam ρ := by
    dsimp [pgLam]
    have hlog_ge : Real.log 2 ≤ Real.log (1 + ρ) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2_gt_half : 1/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h_inner : 1 ≤ 2 * Real.log (1 + ρ) := by
      nlinarith
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_le_sqrt h_inner
  have hLD_pos : 0 < pgLD ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    positivity
  have hDelta_pos : 0 < pgDelta d ρ := by
    dsimp [pgDelta, pgKappa, pgPB]
    positivity
  have hEh_pos : 0 < pgEh d ρ := by
    dsimp [pgEh, pgKappa, pgLD]
    positivity
  have hTmin_pos : 0 < pgTmin d ρ := by
    dsimp [pgTmin, pgLam]
    positivity
  have h_nonneg : 0 ≤ pgEta d ρ := by
    dsimp [pgEta]
    positivity
  have h_bound : (1 + pgEta d ρ) ^ 2 ≤ 5 / 4 := by
    have h_bias := pg_bias_u d ρ hd hρ
    have hRHS_le : 1 / (145600 * d ^ 3 * pgLam ρ ^ 3 * ρ ^ 2) ≤ 1 / 145600 := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · positivity
      · have hd3 : 1 ≤ d ^ 3 := by
          calc
            1 = 1 ^ 3 := by norm_num
            _ ≤ d ^ 3 := pow_le_pow_left₀ (by linarith) hd 3
        have hLam3 : 1 ≤ pgLam ρ ^ 3 := by
          calc
            1 = 1 ^ 3 := by norm_num
            _ ≤ pgLam ρ ^ 3 := pow_le_pow_left₀ (by linarith) hLam_ge_one 3
        have hρ2 : 1 ≤ ρ ^ 2 := by
          calc
            1 = 1 ^ 2 := by norm_num
            _ ≤ ρ ^ 2 := pow_le_pow_left₀ (by linarith) hρ 2
        calc
          145600 = 145600 * 1 := by ring
          _ ≤ 145600 * (d ^ 3) := mul_le_mul_of_nonneg_left hd3 (by norm_num : 0 ≤ (145600 : ℝ))
          _ = 145600 * d ^ 3 * 1 := by ring
          _ ≤ 145600 * d ^ 3 * (pgLam ρ ^ 3) :=
            mul_le_mul_of_nonneg_left hLam3 (by nlinarith)
          _ = 145600 * d ^ 3 * pgLam ρ ^ 3 * 1 := by ring
          _ ≤ 145600 * d ^ 3 * pgLam ρ ^ 3 * (ρ ^ 2) :=
            mul_le_mul_of_nonneg_left hρ2 (by nlinarith)
    have h_mid : pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ 1 / 145600 := by
      linarith
    have hLD_ge : 627/2000 ≤ pgLD ρ * (1 + Real.sqrt d) := by
      dsimp [pgLD, pgKappa, pgPB]
      nlinarith
    have hEta_le : pgEta d ρ ≤ 2000 / (145600 * 627) := by
      have hEta_le' : pgEta d ρ * (627/2000) ≤ 1/145600 := by
        calc
          pgEta d ρ * (627/2000) ≤ pgEta d ρ * (pgLD ρ * (1 + Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hLD_ge h_nonneg
          _ = (pgEta d ρ * pgLD ρ) * (1 + Real.sqrt d) := by ring
          _ = pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) := by ring
          _ ≤ 1 / 145600 := h_mid
      have hpos627 : (0 : ℝ) < 627 := by norm_num
      have htemp : pgEta d ρ * 627 ≤ 2000 / 145600 := by
        nlinarith
      calc
        pgEta d ρ = (pgEta d ρ * 627) / 627 := by field_simp [ne_of_gt hpos627]
        _ ≤ (2000 / 145600) / 627 := by
          refine (div_le_div_of_nonneg_right htemp (by norm_num : 0 ≤ (627 : ℝ)))
        _ = 2000 / (145600 * 627) := by ring
    have hEta_lt : pgEta d ρ < 1/10000 := by
      apply lt_of_le_of_lt hEta_le
      norm_num
    have h_sq_bound : (1 + pgEta d ρ) ^ 2 ≤ 5 / 4 := by
      have h_sq_lt : (1 + pgEta d ρ) ^ 2 < (1 + 1/10000) ^ 2 := by
        nlinarith
      have h_target : (1 + 1/10000) ^ 2 ≤ 5 / 4 := by
        norm_num
      linarith
    exact h_sq_bound
  exact And.intro h_nonneg h_bound

theorem pg_bias_descent (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    Real.sqrt 3 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) / pgTmin d ρ * pgDelta d ρ ≤ pgEh d ρ / 4 := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlogpos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
  have hLampos : 0 < pgLam ρ := by
    dsimp [pgLam]
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hLamSq_pos : 0 < pgLam ρ ^ 2 := pow_pos hLampos 2
  have hLDpos : 0 < pgLD ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    nlinarith
  have hTmin_pos : 0 < pgTmin d ρ := by
    dsimp [pgTmin]
    refine div_pos (by norm_num) (by
      refine mul_pos (mul_pos (by norm_num) hdpos) hLampos)
  have hDelta_pos : 0 < pgDelta d ρ := by
    dsimp [pgDelta, pgKappa, pgPB]
    refine mul_pos (mul_pos (by norm_num) hρpos) ?_
    refine Real.sqrt_pos.mpr (by nlinarith)
  have hEhpos : 0 < pgEh d ρ := by
    dsimp [pgEh, pgKappa]
    refine div_pos (by norm_num) (by
      refine mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hdpos 2)) hLamSq_pos) ?_
      dsimp [pgLD, pgKappa, pgPB]
      have hpos : 0 < (1/8 : ℝ) * (1254/1000 : ℝ) * ρ := by nlinarith
      exact hpos)
  have h_sqrt3_le : Real.sqrt 3 ≤ 7/4 := by
    calc
      Real.sqrt 3 ≤ Real.sqrt (49/16) := Real.sqrt_le_sqrt (by norm_num)
      _ = 7/4 := by norm_num
  have h_eq : pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) = pgEh d ρ * pgTmin d ρ / (7 * pgDelta d ρ) := by
    dsimp [pgEta]
    field_simp [hTmin_pos.ne.symm, hDelta_pos.ne.symm, hLDpos.ne.symm]
  calc
    Real.sqrt 3 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) / pgTmin d ρ * pgDelta d ρ
        = Real.sqrt 3 * (pgEh d ρ * pgTmin d ρ / (7 * pgDelta d ρ)) / pgTmin d ρ * pgDelta d ρ := by rw [h_eq]
    _ = (Real.sqrt 3 / 7) * pgEh d ρ := by
      field_simp [hTmin_pos.ne.symm, hDelta_pos.ne.symm]
    _ ≤ (1/4 : ℝ) * pgEh d ρ := by
      nlinarith
    _ = pgEh d ρ / 4 := by ring

theorem pg_counts (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    12 * (5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2) / (pgKappa / 80) ^ 2 ≤ pgNTreal d ρ ∧
      12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3))) / (pgTaub d ρ / 8) ^ 2 ≤ pgNTreal d ρ ∧
      12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5))) / (pgKappa / (16 * d)) ^ 2 ≤ pgNTreal d ρ := by
  have hdpos : 0 < d := by linarith
  have hd_ne_zero : d ≠ 0 := by linarith
  have hρpos : 0 < ρ := by linarith
  have h_one_plus_ρ_gt_one : 1 < 1 + ρ := by linarith
  have h_log_pos : 0 < Real.log (1 + ρ) := Real.log_pos h_one_plus_ρ_gt_one
  have h_two_log_pos : 0 < 2 * Real.log (1 + ρ) := by linarith
  have h_sqrt_log_pos : 0 < Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_pos.mpr h_two_log_pos
  have h_sqrt_d_ge_one : 1 ≤ Real.sqrt d := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
  have h_sq_bound : (1 + Real.sqrt d) ^ 2 ≤ 4 * d := by
    have h_sqrt_d_le_d : Real.sqrt d ≤ d := by
      have hdpos' : 0 ≤ d := by linarith
      calc
        Real.sqrt d = Real.sqrt d * 1 := by ring
        _ ≤ Real.sqrt d * Real.sqrt d := by gcongr
        _ = (Real.sqrt d) ^ 2 := by ring
        _ = d := Real.sq_sqrt hdpos'
    calc
      (1 + Real.sqrt d) ^ 2 = 1 + 2 * Real.sqrt d + (Real.sqrt d) ^ 2 := by ring
      _ = 1 + 2 * Real.sqrt d + d := by rw [Real.sq_sqrt (by linarith)]
      _ ≤ 1 + 2 * d + d := by gcongr
      _ = 1 + 3 * d := by ring
      _ ≤ d + 3 * d := by linarith
      _ = 4 * d := by ring
  have h_pgKappa_pos : 0 < pgKappa := by
    unfold pgKappa
    norm_num
  have h_pgKappa_sq_pos : 0 < pgKappa ^ 2 := by positivity
  have h_pgLD_sq_pos : 0 < pgLD ρ ^ 2 := by
    have hpos : 0 < pgLD ρ := by
      unfold pgLD pgKappa pgPB
      positivity
    positivity
  have h_pgLam_sq_pos : 0 < pgLam ρ ^ 2 := by
    have hpos : 0 < pgLam ρ := h_sqrt_log_pos
    positivity
  set A := 5/4 * pgLD ρ ^ 2 * d ^ 3 / pgKappa ^ 2 with hA
  have hA_pos : 0 < A := by
    rw [hA]
    positivity
  have hNT_eq : pgNTreal d ρ = A * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) := by
    rw [hA]
    unfold pgNTreal pgLD pgKappa
    field_simp
  have h2 : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3))) / (pgTaub d ρ / 8) ^ 2 = A * (221184 * (d + 3) * pgLam ρ ^ 2) := by
    rw [hA]
    unfold pgTaub pgKappa
    field_simp [hd_ne_zero]
    ring
  have h3 : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5))) / (pgKappa / (16 * d)) ^ 2 = A * (6144 * (d + 1) * (d + 5)) := by
    rw [hA]
    unfold pgKappa
    field_simp [hd_ne_zero]
    ring
  have h1 : 12 * (5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2) / (pgKappa / 80) ^ 2 ≤ A * (221184 * (d + 3) * pgLam ρ ^ 2) := by
    have hLHS_eq : 12 * (5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2) / (pgKappa / 80) ^ 2 = 96000 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2 / pgKappa ^ 2 := by
      unfold pgKappa
      field_simp
      ring
    rw [hLHS_eq]
    calc
      96000 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2 / pgKappa ^ 2 ≤ 96000 * pgLD ρ ^ 2 * (4 * d) / pgKappa ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith
      _ = 384000 * pgLD ρ ^ 2 * d / pgKappa ^ 2 := by ring
      _ ≤ (5/4 * pgLD ρ ^ 2 * d ^ 3 / pgKappa ^ 2) * (221184 * (d + 3) * pgLam ρ ^ 2) := by
        have h_ineq : 384000 * d ≤ (5/4 * d ^ 3) * (221184 * (d + 3) * pgLam ρ ^ 2) := by
          have h_lam_sq_gt : pgLam ρ ^ 2 > 1.386 := by
            have h_log_gt : Real.log (1 + ρ) > 0.6931471803 := by
              have h_log2_gt : Real.log 2 > 0.6931471803 := Real.log_two_gt_d9
              have h2_le_1prho : (2 : ℝ) ≤ 1 + ρ := by linarith
              have h_log_le : Real.log 2 ≤ Real.log (1 + ρ) := Real.log_le_log (by norm_num) h2_le_1prho
              linarith
            have h_sq_eq : pgLam ρ ^ 2 = 2 * Real.log (1 + ρ) := Real.sq_sqrt (by linarith)
            rw [h_sq_eq]
            nlinarith
          have h_d3_ge_d : d ^ 3 ≥ d := by
            have h_sq_ge_one : d ^ 2 ≥ 1 := by nlinarith
            calc
              d ^ 3 = d * (d ^ 2) := by ring
              _ ≥ d * 1 := by gcongr
              _ = d := by ring
          have h_d3_plus_3_ge_4 : d + 3 ≥ 4 := by linarith
          have h_prod_ge : d ^ 3 * (d + 3) * pgLam ρ ^ 2 ≥ d * 4 * 1.386 := by
            have h_mul1 : d ^ 3 * (d + 3) ≥ d * 4 := by
              exact mul_le_mul h_d3_ge_d h_d3_plus_3_ge_4 (by linarith) (by positivity)
            exact mul_le_mul h_mul1 h_lam_sq_gt.le (by positivity) (by positivity)
          calc
            384000 * d ≤ 1532805.12 * d := by
              gcongr
              norm_num
            _ = 276480 * (d * 4 * 1.386) := by ring
            _ ≤ 276480 * (d ^ 3 * (d + 3) * pgLam ρ ^ 2) := by gcongr
            _ = (5/4 * d ^ 3) * (221184 * (d + 3) * pgLam ρ ^ 2) := by ring
        calc
          384000 * pgLD ρ ^ 2 * d / pgKappa ^ 2 = (pgLD ρ ^ 2 / pgKappa ^ 2) * (384000 * d) := by ring
          _ ≤ (pgLD ρ ^ 2 / pgKappa ^ 2) * ((5/4 * d ^ 3) * (221184 * (d + 3) * pgLam ρ ^ 2)) := by gcongr
          _ = (5/4 * pgLD ρ ^ 2 * d ^ 3 / pgKappa ^ 2) * (221184 * (d + 3) * pgLam ρ ^ 2) := by ring
      _ = A * (221184 * (d + 3) * pgLam ρ ^ 2) := by rw [hA]
  refine ⟨?_, ?_, ?_⟩
  · rw [hNT_eq]
    apply le_trans h1
    gcongr
    exact le_max_right _ _
  · rw [hNT_eq, h2]
    gcongr
    exact le_max_right _ _
  · rw [hNT_eq, h3]
    gcongr
    exact le_max_left _ _

set_option maxHeartbeats 1000000 in
theorem pg_N_size (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgNreal d ρ + 1 ≤ 1.8e11 * d ^ 10 * ρ ^ 6 * Real.log (1 + ρ) ^ 3 := by
  set L := Real.log (1 + ρ) with hL
  have hL2 : (0.6931471803 : ℝ) < L :=
    lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) (by linarith))
  have hLpos : 0 < L := by linarith
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlam2 : pgLam ρ ^ 2 = 2 * L := by
    unfold pgLam; rw [Real.sq_sqrt (by linarith)]
  have hPB : pgPB = 1254 / 1000 := rfl
  have hK : pgKappa = 1 / 8 := rfl
  have hsq : Real.sqrt (4 + pgPB ^ 2 * d) ^ 2 = 4 + pgPB ^ 2 * d :=
    Real.sq_sqrt (by rw [hPB]; positivity)
  have hD : pgDelta d ρ ^ 2 = pgKappa ^ 2 * ρ ^ 2 * (4 + pgPB ^ 2 * d) := by
    unfold pgDelta; rw [mul_pow, mul_pow, hsq]
  have hT : pgTmin d ρ ^ 2 = 1 / (162 * d ^ 2 * L) := by
    unfold pgTmin; rw [div_pow, mul_pow, mul_pow, hlam2]; ring
  have hE : pgEh d ρ = pgKappa ^ 2 / (1844 * d ^ 2 * L * pgLD ρ) := by
    unfold pgEh; rw [hlam2]; ring
  have hG : pgG2 d ρ = (5 * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) * (162 * d ^ 2 * L) := by
    unfold pgG2; rw [hT]; field_simp
  have hN : pgNreal d ρ = (16 * 162 * 1844 ^ 2 * pgPB ^ 2 * pgKappa ^ 2) * (ρ ^ 4 * d ^ 6 * L ^ 3) *
      ((4 + pgPB ^ 2 * d) * (5 * pgPB ^ 2 * ρ ^ 2 * d * (d + 2) * (d + 5) + 2 / d)) := by
    unfold pgNreal; rw [hD, hG, hE]; unfold pgLD; rw [hK]; field_simp
  have hA : 0 ≤ ρ ^ 4 * d ^ 6 * L ^ 3 := by positivity
  have hf1 : 4 + pgPB ^ 2 * d ≤ 5.573 * d := by rw [hPB]; nlinarith
  have hdd : (d + 2) * (d + 5) ≤ 18 * d ^ 2 := by nlinarith
  have h2d : 2 / d ≤ 2 * ρ ^ 2 * d ^ 3 := by
    rw [div_le_iff₀ hdpos]
    have : 1 ≤ ρ ^ 2 * d ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hρ) (one_le_pow₀ hd)
    nlinarith
  have hf2 : 5 * pgPB ^ 2 * ρ ^ 2 * d * (d + 2) * (d + 5) + 2 / d ≤ 143.53 * ρ ^ 2 * d ^ 3 := by
    have hρd : 0 ≤ ρ ^ 2 * d := by positivity
    have : 5 * pgPB ^ 2 * ρ ^ 2 * d * (d + 2) * (d + 5) ≤ 5 * pgPB ^ 2 * (ρ ^ 2 * d) * (18 * d ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hdd (by rw [hPB]; positivity : (0 : ℝ) ≤ 5 * pgPB ^ 2 * (ρ ^ 2 * d))
      nlinarith [h]
    rw [hPB] at this ⊢
    nlinarith
  have hprod : (4 + pgPB ^ 2 * d) * (5 * pgPB ^ 2 * ρ ^ 2 * d * (d + 2) * (d + 5) + 2 / d) ≤
      5.573 * d * (143.53 * ρ ^ 2 * d ^ 3) :=
    mul_le_mul hf1 hf2 (by positivity) (by positivity)
  have hC : (16 * 162 * 1844 ^ 2 * pgPB ^ 2 * pgKappa ^ 2 : ℝ) ≤ 216557000 := by
    rw [hPB, hK]; norm_num
  have hkey : pgNreal d ρ ≤ 216557000 * (ρ ^ 4 * d ^ 6 * L ^ 3) * (5.573 * d * (143.53 * ρ ^ 2 * d ^ 3)) := by
    rw [hN]
    have hC0 : (0 : ℝ) ≤ 16 * 162 * 1844 ^ 2 * pgPB ^ 2 * pgKappa ^ 2 := by rw [hPB, hK]; norm_num
    calc _ ≤ (16 * 162 * 1844 ^ 2 * pgPB ^ 2 * pgKappa ^ 2) * (ρ ^ 4 * d ^ 6 * L ^ 3) *
          (5.573 * d * (143.53 * ρ ^ 2 * d ^ 3)) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hC0 hA)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA) (by positivity)
  have hone : 1 ≤ d ^ 10 * ρ ^ 6 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) (one_le_pow₀ hρ)
  have hL3 : (0.333 : ℝ) ≤ L ^ 3 := by
    have h : (0.6931471803 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL2.le 3
    have h' : (0.333 : ℝ) ≤ 0.6931471803 ^ 3 := by norm_num
    exact h'.trans h
  have hfin : 216557000 * (ρ ^ 4 * d ^ 6 * L ^ 3) * (5.573 * d * (143.53 * ρ ^ 2 * d ^ 3)) =
      (216557000 * 5.573 * 143.53) * (d ^ 10 * ρ ^ 6 * L ^ 3) := by ring
  rw [hfin] at hkey
  have hnum : (216557000 * 5.573 * 143.53 : ℝ) ≤ 1.7323e11 := by norm_num
  have hPL : 0.333 ≤ d ^ 10 * ρ ^ 6 * L ^ 3 := by
    have h := mul_le_mul hone hL3 (by norm_num) (by positivity)
    rw [one_mul] at h
    exact h
  have hP : 0 ≤ d ^ 10 * ρ ^ 6 * L ^ 3 := by positivity
  have h1 : (216557000 * 5.573 * 143.53) * (d ^ 10 * ρ ^ 6 * L ^ 3) ≤ 1.7323e11 * (d ^ 10 * ρ ^ 6 * L ^ 3) :=
    mul_le_mul_of_nonneg_right hnum hP
  have h2 : 1.8e11 * d ^ 10 * ρ ^ 6 * L ^ 3 = 1.8e11 * (d ^ 10 * ρ ^ 6 * L ^ 3) := by ring
  rw [h2]
  linarith only [hkey, h1, hPL]

set_option maxHeartbeats 400000 in
theorem pg_NT_size (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgNTreal d ρ + 1 ≤ 3.7e6 * d ^ 5 * ρ ^ 2 * Real.log (1 + ρ) := by
  set L := Real.log (1 + ρ) with hL
  have hLpos : 0 < L := by
    rw [hL]
    refine Real.log_pos (by linarith : 1 < 1 + ρ)
  have hL_gt : (0.6931471803 : ℝ) < L := by
    rw [hL]
    have h2le : (2 : ℝ) ≤ 1 + ρ := by linarith
    exact lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) h2le)
  have hdpos : 0 ≤ d := by linarith
  have hρpos : 0 ≤ ρ := by linarith
  have hcoeff : pgLD ρ ^ 2 / pgKappa ^ 2 = pgPB ^ 2 * ρ ^ 2 := by
    unfold pgLD pgKappa pgPB
    ring
  have hpgNTreal_eq : pgNTreal d ρ = 5/4 * pgPB ^ 2 * ρ ^ 2 * d ^ 3 *
      max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) := by
    unfold pgNTreal
    calc
      5/4 * pgLD ρ ^ 2 * d ^ 3 * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) / pgKappa ^ 2
          = 5/4 * (pgLD ρ ^ 2 / pgKappa ^ 2) * d ^ 3 * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) := by ring
      _ = 5/4 * (pgPB ^ 2 * ρ ^ 2) * d ^ 3 * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) := by rw [hcoeff]
      _ = 5/4 * pgPB ^ 2 * ρ ^ 2 * d ^ 3 * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) := by ring
  have hLam_sq : pgLam ρ ^ 2 = 2 * L := by
    unfold pgLam
    rw [hL]
    exact Real.sq_sqrt (by nlinarith)
  have hA_nonneg : 0 ≤ 6144 * (d + 1) * (d + 5) := by positivity
  have hB_nonneg : 0 ≤ 221184 * (d + 3) * pgLam ρ ^ 2 := by positivity
  have hmax_le_add : max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) ≤
      6144 * (d + 1) * (d + 5) + 221184 * (d + 3) * pgLam ρ ^ 2 :=
    max_le_add_of_nonneg hA_nonneg hB_nonneg
  have hA_bound : 6144 * (d + 1) * (d + 5) ≤ 6144 * 12 * d ^ 2 := by
    have h : (d + 1) * (d + 5) ≤ 12 * d ^ 2 := by
      nlinarith
    nlinarith
  have hB_bound : 221184 * (d + 3) * pgLam ρ ^ 2 ≤ 221184 * 8 * d * L := by
    have hd3 : d + 3 ≤ 4 * d := by nlinarith
    rw [hLam_sq]
    nlinarith
  have hsum_bound : 6144 * (d + 1) * (d + 5) + 221184 * (d + 3) * pgLam ρ ^ 2 ≤
      6144 * 12 * d ^ 2 + 221184 * 8 * d * L := by
    nlinarith
  have hmax_bound : max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) ≤
      6144 * 12 * d ^ 2 + 221184 * 8 * d * L := by
    linarith
  have hcoeff_pos : 0 ≤ 5/4 * pgPB ^ 2 * ρ ^ 2 * d ^ 3 := by positivity
  have hpgNTreal_bound : pgNTreal d ρ ≤ 5/4 * pgPB ^ 2 * ρ ^ 2 * (6144 * 12 * d ^ 5 + 221184 * 8 * d ^ 4 * L) := by
    rw [hpgNTreal_eq]
    have h := mul_le_mul_of_nonneg_left hmax_bound hcoeff_pos
    nlinarith
  have h_d4_le_d5 : d ^ 4 * L ≤ d ^ 5 * L := by
    have hd4 : d ^ 4 ≤ d ^ 5 := by
      calc
        d ^ 4 = 1 * d ^ 4 := by ring
        _ ≤ d * d ^ 4 := mul_le_mul_of_nonneg_right hd (by positivity)
        _ = d ^ 5 := by ring
    exact mul_le_mul_of_nonneg_right hd4 (by linarith)
  have hpgNTreal_bound2 : pgNTreal d ρ ≤ (5/4 * pgPB ^ 2 * (6144 * 12 + 221184 * 8 * L)) * d ^ 5 * ρ ^ 2 := by
    apply le_trans hpgNTreal_bound
    have hcalc : 5/4 * pgPB ^ 2 * ρ ^ 2 * (6144 * 12 * d ^ 5 + 221184 * 8 * d ^ 4 * L) ≤
        (5/4 * pgPB ^ 2 * (6144 * 12 + 221184 * 8 * L)) * d ^ 5 * ρ ^ 2 := by
      have hpos : 0 ≤ 5/4 * pgPB ^ 2 * ρ ^ 2 := by positivity
      have hineq : 221184 * 8 * d ^ 4 * L ≤ 221184 * 8 * L * d ^ 5 := by
        have hpos' : 0 ≤ 221184 * 8 * L := by positivity
        nlinarith
      nlinarith
    exact hcalc
  have h_d5ρ2_pos : 0 ≤ d ^ 5 * ρ ^ 2 := by positivity
  have h_d5ρ2_ge_one : 1 ≤ d ^ 5 * ρ ^ 2 := by
    have hd5 : 1 ≤ d ^ 5 := by
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hd 5
      simpa [one_pow] using h
    have hρ2 : 1 ≤ ρ ^ 2 := by
      nlinarith
    nlinarith
  have h_sufficient : (5/4 * pgPB ^ 2 * (6144 * 12) + 1 : ℝ) ≤
      ((3.7e6 : ℝ) - 5/4 * pgPB ^ 2 * (221184 * 8)) * (0.6931471803 : ℝ) := by
    unfold pgPB
    ring_nf
    norm_num
  have h_pos : 0 ≤ (3.7e6 : ℝ) - 5/4 * pgPB ^ 2 * (221184 * 8) := by
    unfold pgPB
    ring_nf
    norm_num
  have h_key : (5/4 * pgPB ^ 2 * (6144 * 12) + (5/4 * pgPB ^ 2 * (221184 * 8)) * L + 1) ≤ (3.7e6 : ℝ) * L := by
    have h_mul : ((3.7e6 : ℝ) - 5/4 * pgPB ^ 2 * (221184 * 8)) * (0.6931471803 : ℝ) ≤
        ((3.7e6 : ℝ) - 5/4 * pgPB ^ 2 * (221184 * 8)) * L := by
      nlinarith
    nlinarith
  have h_final : (5/4 * pgPB ^ 2 * (6144 * 12 + 221184 * 8 * L)) * d ^ 5 * ρ ^ 2 + 1 ≤ (3.7e6 : ℝ) * d ^ 5 * ρ ^ 2 * L := by
    nlinarith
  nlinarith

theorem pg_rho_eta (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ρ / pgEta d ρ ≤ 152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ) := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have h1ρpos : 1 < 1 + ρ := by linarith
  have hLpos : 0 < Real.log (1 + ρ) := Real.log_pos h1ρpos
  have hLpos' : 0 ≤ Real.log (1 + ρ) := by linarith
  have hLbdd : Real.log 2 ≤ Real.log (1 + ρ) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hLbdd' : Real.log (1 + ρ) ≤ ρ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ρ)
    linarith
  set L := Real.log (1 + ρ) with hLdef
  set s := Real.sqrt (2 * L) with hsdef
  set r := Real.sqrt d with hrdef
  have hs_sq : s ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
  have hr_sq : r ^ 2 = d := Real.sq_sqrt (by linarith)
  have hs_pos : 1 < s := by
    have hL2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    have hLge : 0.6931471803 < L := by linarith
    have hsq : 1 < s ^ 2 := by
      calc
        1 < 2 * 0.6931471803 := by norm_num
        _ < 2 * L := by linarith
        _ = s ^ 2 := by symm; exact hs_sq
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    nlinarith
  have hr_pos : 1 ≤ r := by
    have h1d : 1 ≤ d := hd
    have hsq : 1 ≤ r ^ 2 := by
      rw [hr_sq]
      exact h1d
    have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
    nlinarith
  have hρ_nonneg : 0 ≤ ρ := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  -- Unfold everything and simplify
  unfold pgEta pgEh pgTmin pgLD pgDelta pgLam
  -- Rewrite using L, s, r (note: ← direction)
  rw [← hLdef, ← hsdef, ← hrdef]
  -- Goal: ρ / ((pgKappa ^ 2 / (922 * d ^ 2 * s ^ 2 * (pgKappa * pgPB * ρ))) * (1 / (9 * d * s)) /
  --   (7 * (pgKappa * pgPB * ρ) * (1 + r) * (pgKappa * ρ * Real.sqrt (4 + pgPB ^ 2 * d)))) ≤
  --   152468 * d ^ 4 * ρ ^ (11 / 2)
  have h_kappa_pos : 0 < pgKappa := by unfold pgKappa; norm_num
  have h_pb_pos : 0 < pgPB := by unfold pgPB; norm_num
  have h_s_pos' : 0 < s := by linarith
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (4 + pgPB ^ 2 * d) := Real.sqrt_nonneg _
  -- Provide all nonzero conditions for field_simp
  have h_denom_pos : 0 < 922 * d ^ 2 * s ^ 2 * (pgKappa * pgPB * ρ) := by positivity
  have h_denom2_pos : 0 < 9 * d * s := by positivity
  have h_denom3_pos : 0 < 7 * (pgKappa * pgPB * ρ) * (1 + r) * (pgKappa * ρ * Real.sqrt (4 + pgPB ^ 2 * d)) := by positivity
  field_simp
  -- Goal: ρ ^ 4 * pgKappa * 922 * s ^ 3 * pgPB ^ 2 * 9 * 7 * (1 + r) * √(4 + d * pgPB ^ 2) ≤ d * 152468 * ρ ^ (11 / 2)
  -- Rewrite ρ^(11/2) = ρ^5 * sqrt(ρ)
  have h_rpow : ρ ^ (11 / 2 : ℝ) = ρ ^ 5 * Real.sqrt ρ := by
    calc
      ρ ^ (11 / 2 : ℝ) = ρ ^ ((5 : ℝ) + (1/2 : ℝ)) := by ring
      _ = ρ ^ (5 : ℝ) * ρ ^ (1/2 : ℝ) := by rw [Real.rpow_add hρpos (5 : ℝ) (1/2 : ℝ)]
      _ = ρ ^ 5 * Real.sqrt ρ := by simp [Real.sqrt_eq_rpow]
  rw [h_rpow]
  -- Goal: ρ ^ 4 * pgKappa * 922 * s ^ 3 * pgPB ^ 2 * 9 * 7 * (1 + r) * √(4 + d * pgPB ^ 2) ≤ d * (ρ ^ 5 * Real.sqrt ρ) * 152468
  -- Bound s^3 ≤ 2*sqrt(2) * ρ * sqrt(ρ)
  have h_s_bound : s ^ 3 ≤ 2 * Real.sqrt 2 * ρ * Real.sqrt ρ := by
    have h_s_sq_le : s ^ 2 ≤ 2 * ρ := by
      linarith
    have h_s_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    have h_s_le : s ≤ Real.sqrt 2 * Real.sqrt ρ := by
      calc
        s = Real.sqrt (s ^ 2) := by rw [Real.sqrt_sq h_s_nonneg]
        _ ≤ Real.sqrt (2 * ρ) := Real.sqrt_le_sqrt h_s_sq_le
        _ = Real.sqrt 2 * Real.sqrt ρ := Real.sqrt_mul (by norm_num) _
    calc
      s ^ 3 = s * (s ^ 2) := by ring
      _ ≤ s * (2 * ρ) := by nlinarith
      _ ≤ (Real.sqrt 2 * Real.sqrt ρ) * (2 * ρ) := by nlinarith
      _ = 2 * Real.sqrt 2 * ρ * Real.sqrt ρ := by ring
  -- Bound (1 + r) ≤ 2 * r (since r ≥ 1)
  have h_one_plus_r_bound : 1 + r ≤ 2 * r := by
    nlinarith
  -- Bound sqrt(4 + d * pgPB^2) ≤ sqrt(4 + pgPB^2) * r
  have h_sqrt_bound : Real.sqrt (4 + d * pgPB ^ 2) ≤ Real.sqrt (4 + pgPB ^ 2) * r := by
    have h_ineq : 4 + d * pgPB ^ 2 ≤ (4 + pgPB ^ 2) * d := by
      nlinarith
    calc
      Real.sqrt (4 + d * pgPB ^ 2) ≤ Real.sqrt ((4 + pgPB ^ 2) * d) := Real.sqrt_le_sqrt h_ineq
      _ = Real.sqrt (4 + pgPB ^ 2) * Real.sqrt d := Real.sqrt_mul (by nlinarith) _
      _ = Real.sqrt (4 + pgPB ^ 2) * r := by rw [hrdef]
  -- Tight numerical bounds
  have h_sqrt2_bound : Real.sqrt 2 ≤ 1.41421357 := by
    have h_sq : (1.41421357 : ℝ) ^ 2 ≥ 2 := by norm_num
    exact calc
      Real.sqrt 2 ≤ Real.sqrt ((1.41421357 : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = 1.41421357 := Real.sqrt_sq (by norm_num)
  have h_sqrt4_bound : Real.sqrt (4 + pgPB ^ 2) ≤ 2.3606178 := by
    have h_sq : (2.3606178 : ℝ) ^ 2 ≥ 4 + pgPB ^ 2 := by
      unfold pgPB; norm_num
    exact calc
      Real.sqrt (4 + pgPB ^ 2) ≤ Real.sqrt ((2.3606178 : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = 2.3606178 := Real.sqrt_sq (by norm_num)
  -- Now apply all bounds
  have h_nonneg_s3 : 0 ≤ s ^ 3 := by positivity
  have h_nonneg_1pr : 0 ≤ 1 + r := by linarith
  have h_nonneg_sqrt : 0 ≤ Real.sqrt (4 + d * pgPB ^ 2) := Real.sqrt_nonneg _
  have h_nonneg_sqrtρ : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
  have h_nonneg_ρ4 : 0 ≤ ρ ^ 4 := by positivity
  have h_nonneg_d : 0 ≤ d := by linarith
  have h_nonneg_ρ5 : 0 ≤ ρ ^ 5 := by positivity
  have h_nonneg_sqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_nonneg_sqrt4 : 0 ≤ Real.sqrt (4 + pgPB ^ 2) := Real.sqrt_nonneg _
  have h_nonneg_C : 0 ≤ 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 := by positivity
  -- Constant bound: 4 * κ * 922 * PB^2 * 9 * 7 * √2 * √(4+PB^2) ≤ 152468
  have h_total : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * (1.41421357 : ℝ) * (2.3606178 : ℝ) ≤ 152468 := by
    unfold pgKappa pgPB; norm_num
  have h_constant_bound : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * Real.sqrt 2 * Real.sqrt (4 + pgPB ^ 2) ≤ 152468 := by
    have h1 : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * Real.sqrt 2 ≤ 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * (1.41421357 : ℝ) :=
      mul_le_mul_of_nonneg_left h_sqrt2_bound h_nonneg_C
    have h2 : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * Real.sqrt 2 * Real.sqrt (4 + pgPB ^ 2) ≤
        4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * (1.41421357 : ℝ) * Real.sqrt (4 + pgPB ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h_nonneg_sqrt4
    have h3 : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * (1.41421357 : ℝ) * Real.sqrt (4 + pgPB ^ 2) ≤
        4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * (1.41421357 : ℝ) * (2.3606178 : ℝ) :=
      mul_le_mul_of_nonneg_left h_sqrt4_bound (by positivity)
    linarith
  -- Main inequality chain
  have h_main : ρ ^ 4 * pgKappa * 922 * s ^ 3 * pgPB ^ 2 * 9 * 7 * (1 + r) * Real.sqrt (4 + d * pgPB ^ 2) ≤
      d * (ρ ^ 5 * Real.sqrt ρ) * 152468 := by
    -- First, bound s^3, 1+r, sqrt(4+d*PB^2) using the individual bounds
    have h_s3_bound' : ρ ^ 4 * pgKappa * 922 * s ^ 3 * pgPB ^ 2 * 9 * 7 * (1 + r) * Real.sqrt (4 + d * pgPB ^ 2) ≤
        ρ ^ 4 * pgKappa * 922 * (2 * Real.sqrt 2 * ρ * Real.sqrt ρ) * pgPB ^ 2 * 9 * 7 * (2 * r) * (Real.sqrt (4 + pgPB ^ 2) * r) := by
      -- Apply s^3 ≤ 2*√2*ρ*√ρ
      have h1 : s ^ 3 ≤ 2 * Real.sqrt 2 * ρ * Real.sqrt ρ := h_s_bound
      -- Apply 1+r ≤ 2*r
      have h2 : 1 + r ≤ 2 * r := h_one_plus_r_bound
      -- Apply sqrt(4+d*PB^2) ≤ √(4+PB^2)*r
      have h3 : Real.sqrt (4 + d * pgPB ^ 2) ≤ Real.sqrt (4 + pgPB ^ 2) * r := h_sqrt_bound
      -- All factors are nonnegative, so we can multiply the inequalities
      have h_nonneg_2sqrt2ρsqrtρ : 0 ≤ 2 * Real.sqrt 2 * ρ * Real.sqrt ρ := by positivity
      have h_nonneg_2r : 0 ≤ 2 * r := by linarith
      have h_nonneg_sqrt4r : 0 ≤ Real.sqrt (4 + pgPB ^ 2) * r := by positivity
      gcongr
    -- Now simplify the RHS of h_s3_bound'
    -- RHS = ρ^4 * κ * 922 * (2*√2*ρ*√ρ) * PB^2 * 9 * 7 * (2*r) * (√(4+PB^2)*r)
    -- = 4 * κ * 922 * PB^2 * 9 * 7 * √2 * √(4+PB^2) * ρ^5 * r^2 * √ρ
    -- = 4 * κ * 922 * PB^2 * 9 * 7 * √2 * √(4+PB^2) * ρ^5 * d * √ρ
    have h_simplify : ρ ^ 4 * pgKappa * 922 * (2 * Real.sqrt 2 * ρ * Real.sqrt ρ) * pgPB ^ 2 * 9 * 7 * (2 * r) * (Real.sqrt (4 + pgPB ^ 2) * r) =
        4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * Real.sqrt 2 * Real.sqrt (4 + pgPB ^ 2) * ρ ^ 5 * d * Real.sqrt ρ := by
      ring
      rw [hr_sq]
      ring
    rw [h_simplify] at h_s3_bound'
    -- Now combine with h_constant_bound
    have h_final : 4 * pgKappa * 922 * pgPB ^ 2 * 9 * 7 * Real.sqrt 2 * Real.sqrt (4 + pgPB ^ 2) * ρ ^ 5 * d * Real.sqrt ρ ≤
        d * (ρ ^ 5 * Real.sqrt ρ) * 152468 := by
      -- Factor out ρ^5 * d * √ρ (all nonnegative)
      have h_nonneg_factor : 0 ≤ ρ ^ 5 * d * Real.sqrt ρ := by positivity
      -- We have: (4*κ*922*PB^2*9*7*√2*√(4+PB^2)) * (ρ^5 * d * √ρ) ≤ 152468 * (ρ^5 * d * √ρ)
      -- Since ρ^5 * d * √ρ ≥ 0, we can multiply h_constant_bound by it
      nlinarith
    linarith
  -- Match the goal's RHS associativity
  ring_nf at h_main ⊢
  exact h_main

theorem pg_bisect_steps (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    Real.logb 2 (ρ / pgEta d ρ) + 1 ≤ 19 + 4 * Real.logb 2 d + 5.5 * Real.logb 2 ρ := by
  have hdpos : 0 < d := by linarith
  have hρpos : 0 < ρ := by linarith
  have hpos2 : 1 < (2 : ℝ) := by norm_num
  have hpos_eta : 0 < ρ / pgEta d ρ := by
    have hEtaPos : 0 < pgEta d ρ := by
      unfold pgEta pgEh pgTmin pgLD pgLam pgDelta pgKappa pgPB
      have hKappa : 0 < (1/8 : ℝ) := by norm_num
      have hPB : 0 < (1254/1000 : ℝ) := by norm_num
      have hLog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
      have hLam : 0 < Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_pos.mpr (by nlinarith)
      have hLD : 0 < (1/8 : ℝ) * (1254/1000 : ℝ) * ρ := by positivity
      have hDelta : 0 < (1/8 : ℝ) * ρ * Real.sqrt (4 + (1254/1000 : ℝ) ^ 2 * d) := by
        positivity
      positivity
    exact div_pos hρpos hEtaPos
  have hpos_rhs : 0 < 152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ) := by positivity
  have hineq := pg_rho_eta d ρ hd hρ
  have hlog := Real.logb_le_logb_of_le hpos2 hpos_eta (by simpa using hineq)
  have hlog_mul : Real.logb 2 (152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ)) =
      Real.logb 2 (152468 : ℝ) + Real.logb 2 (d ^ 4) + Real.logb 2 (ρ ^ (11 / 2 : ℝ)) := by
    have h152468_ne : (152468 : ℝ) ≠ 0 := by norm_num
    have hd4_ne : d ^ 4 ≠ 0 := pow_ne_zero 4 hdpos.ne.symm
    have hrpow_ne : ρ ^ (11 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hρpos _).ne.symm
    have hprod_ne : d ^ 4 * ρ ^ (11 / 2 : ℝ) ≠ 0 := mul_ne_zero hd4_ne hrpow_ne
    calc
      Real.logb 2 (152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ))
          = Real.logb 2 ((152468 : ℝ) * (d ^ 4 * ρ ^ (11 / 2 : ℝ))) := by ring_nf
      _ = Real.logb 2 (152468 : ℝ) + Real.logb 2 (d ^ 4 * ρ ^ (11 / 2 : ℝ)) :=
        Real.logb_mul h152468_ne hprod_ne
      _ = Real.logb 2 (152468 : ℝ) + (Real.logb 2 (d ^ 4) + Real.logb 2 (ρ ^ (11 / 2 : ℝ))) := by
        rw [Real.logb_mul hd4_ne hrpow_ne]
      _ = Real.logb 2 (152468 : ℝ) + Real.logb 2 (d ^ 4) + Real.logb 2 (ρ ^ (11 / 2 : ℝ)) := by ring
  have hlog_d4 : Real.logb 2 (d ^ 4) = (4 : ℝ) * Real.logb 2 d := by
    simpa using Real.logb_pow 2 d 4
  have hlog_rho : Real.logb 2 (ρ ^ (11 / 2 : ℝ)) = (11 / 2 : ℝ) * Real.logb 2 ρ := by
    simpa using Real.logb_rpow_eq_mul_logb_of_pos (b := 2) (y := (11/2 : ℝ)) hρpos
  have hlog_rhs : Real.logb 2 (152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ)) =
      Real.logb 2 (152468 : ℝ) + (4 : ℝ) * Real.logb 2 d + (11 / 2 : ℝ) * Real.logb 2 ρ := by
    rw [hlog_mul, hlog_d4, hlog_rho]
  have h152468 : Real.logb 2 (152468 : ℝ) ≤ (18 : ℝ) := by
    have hpos152468 : 0 < (152468 : ℝ) := by norm_num
    rw [Real.logb_le_iff_le_rpow hpos2 hpos152468]
    have h : (2 : ℝ) ^ (18 : ℝ) = (262144 : ℝ) := by norm_num
    rw [h]
    norm_num
  have h_total : Real.logb 2 (ρ / pgEta d ρ) ≤ Real.logb 2 (152468 : ℝ) + (4 : ℝ) * Real.logb 2 d + (11 / 2 : ℝ) * Real.logb 2 ρ := by
    linarith
  linarith

theorem pg_failure (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (J : ℕ) (hJ : 1 ≤ J) (hJδ : 4 / δ ≤ 2 ^ J) :
    J * (δ / (2 * J)) + ((1 + δ / (2 * J)) / 2) ^ J ≤ 0.92 * δ := by
  have hJpos : (0 : ℝ) < J := by
    have : (0 : ℕ) < J := Nat.one_pos.trans_le hJ
    exact_mod_cast this
  have hJpos' : (0 : ℝ) ≤ J := by linarith
  have hJne0 : (J : ℝ) ≠ 0 := by linarith
  have h_first : (J : ℝ) * (δ / (2 * (J : ℝ))) = δ / 2 := by
    field_simp [hJne0]
  rw [h_first]
  set x := δ / (2 * (J : ℝ)) with hx
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    refine div_nonneg (by linarith) ?_
    nlinarith
  have h_one_plus_x_le_exp_x : 1 + x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have h_pow_le : (1 + x) ^ J ≤ (Real.exp x) ^ J :=
    pow_le_pow_left₀ (by linarith) h_one_plus_x_le_exp_x J
  have h_exp_pow_eq : (Real.exp x) ^ J = Real.exp ((J : ℝ) * x) := by
    rw [← Real.exp_nat_mul x J]
  have h_Jx_eq : (J : ℝ) * x = δ / 2 := by
    rw [hx]
    field_simp [hJne0]
  have h_exp_bound : Real.exp (δ / 2) ≤ 1.65 := by
    have h_exp_le : Real.exp (δ / 2) ≤ Real.exp (1/2) :=
      Real.exp_le_exp_of_le (by linarith)
    have h_sq : (Real.exp (1/2)) ^ 2 = Real.exp 1 := by
      calc
        (Real.exp (1/2)) ^ 2 = Real.exp ((2 : ℕ) * (1/2 : ℝ)) := by
          rw [Real.exp_nat_mul (1/2 : ℝ) 2]
        _ = Real.exp 1 := by norm_num
    have h_exp_one_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h_165_sq : (1.65 : ℝ) ^ 2 = 2.7225 := by norm_num
    have h_exp_one_lt_165sq : Real.exp 1 < (1.65 : ℝ) ^ 2 := by
      linarith
    have h_pos : 0 < Real.exp (1/2) := Real.exp_pos (1/2)
    have h_exp_half_lt_165 : Real.exp (1/2) < 1.65 := by
      nlinarith
    linarith
  have h_one_div_pow_bound : 1 / ((2 : ℝ) ^ J) ≤ δ / 4 := by
    have hpos_2pow : 0 < (2 : ℝ) ^ J := by positivity
    have hpos_4divδ : 0 < 4 / δ := by positivity
    have h := (one_div_le_one_div hpos_2pow hpos_4divδ).mpr hJδ
    have h_one_div : 1 / (4 / δ) = δ / 4 := by field_simp
    rw [h_one_div] at h
    exact h
  have h_pow_div_bound : (1 + x) ^ J / ((2 : ℝ) ^ J) ≤ Real.exp (δ / 2) / ((2 : ℝ) ^ J) := by
    refine ((div_le_div_iff_of_pos_right (by positivity)).mpr ?_)
    calc
      (1 + x) ^ J ≤ (Real.exp x) ^ J := h_pow_le
      _ = Real.exp ((J : ℝ) * x) := h_exp_pow_eq
      _ = Real.exp (δ / 2) := by rw [h_Jx_eq]
  have h_second_term : ((1 + x) / 2) ^ J ≤ 1.65 * (δ / 4) := by
    calc
      ((1 + x) / 2) ^ J = (1 + x) ^ J / ((2 : ℝ) ^ J) := by rw [div_pow]
      _ ≤ Real.exp (δ / 2) / ((2 : ℝ) ^ J) := h_pow_div_bound
      _ = Real.exp (δ / 2) * (1 / ((2 : ℝ) ^ J)) := by ring
      _ ≤ Real.exp (δ / 2) * (δ / 4) := by
        refine mul_le_mul_of_nonneg_left h_one_div_pow_bound (by positivity)
      _ ≤ 1.65 * (δ / 4) := by
        refine mul_le_mul_of_nonneg_right h_exp_bound (by positivity)
  calc
    δ / 2 + ((1 + x) / 2) ^ J ≤ δ / 2 + 1.65 * (δ / 4) := by nlinarith
    _ = 0.9125 * δ := by ring
    _ ≤ 0.92 * δ := by
      nlinarith

theorem pg_hoeffding (δ' : ℝ) (hδ : 0 < δ') (m : ℕ) (hm : 8 * Real.log (1 / δ') ≤ m) : Real.exp (-(m : ℝ) / 8) ≤ δ' := by
  have hineq : -(m : ℝ) / 8 ≤ Real.log δ' := by
    have h : Real.log (1 / δ') ≤ (m : ℝ) / 8 := by linarith
    have hlog : -Real.log (1 / δ') = Real.log δ' := by
      calc
        -Real.log (1 / δ') = -Real.log (δ'⁻¹) := by simp
        _ = -(-Real.log δ') := by rw [Real.log_inv]
        _ = Real.log δ' := by simp
    linarith
  calc
    Real.exp (-(m : ℝ) / 8) ≤ Real.exp (Real.log δ') := Real.exp_le_exp.mpr hineq
    _ = δ' := Real.exp_log hδ

theorem pg_rb_log (d : ℝ) (hd : 1 ≤ d) : Real.log (1 + pgRb d) ≤ 5.5 * Real.log (2 * d + 2) := by
  set x := 2 * d + 2 with hx_def
  have hxpos : 0 < x := by linarith
  have hx4 : 4 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogx_le_x : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hsqrt_log_le_sqrt_x : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt hlogx_le_x
  have h2d_le_x : 2 * d ≤ x := by linarith
  have hsqrtx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hd_nonneg : 0 ≤ d := by linarith
  have hpgRb_le : pgRb d ≤ 200 * x * Real.sqrt x := by
    dsimp [pgRb]
    calc
      400 * d * Real.sqrt (Real.log (2 * d + 2)) = 400 * d * Real.sqrt (Real.log x) := by simp [hx_def]
      _ ≤ 400 * d * Real.sqrt x := by
        have : 0 ≤ 400 * d := by positivity
        nlinarith
      _ = 200 * (2 * d) * Real.sqrt x := by ring
      _ ≤ 200 * x * Real.sqrt x := by
        have : 0 ≤ 200 * Real.sqrt x := by positivity
        nlinarith
  have hsqrtx_ge_2 : 2 ≤ Real.sqrt x := by
    calc
      2 = Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx4
  have hone_le : 1 ≤ x * Real.sqrt x / 8 := by
    have : 8 ≤ x * Real.sqrt x := by
      nlinarith
    linarith
  have hsum_le : 1 + pgRb d ≤ 256 * x * Real.sqrt x := by
    have h1 : 1 + pgRb d ≤ 1 + 200 * x * Real.sqrt x := by nlinarith
    have h2 : 1 + 200 * x * Real.sqrt x ≤ x * Real.sqrt x / 8 + 200 * x * Real.sqrt x := by nlinarith
    have h3 : x * Real.sqrt x / 8 + 200 * x * Real.sqrt x = (1601/8 : ℝ) * x * Real.sqrt x := by ring
    have h4 : (1601/8 : ℝ) ≤ (256 : ℝ) := by norm_num
    have h5 : (1601/8 : ℝ) * x * Real.sqrt x ≤ 256 * x * Real.sqrt x := by
      have : 0 ≤ x * Real.sqrt x := by positivity
      nlinarith
    nlinarith
  have hpos_sum : 0 < 1 + pgRb d := by
    have : 0 ≤ pgRb d := by
      dsimp [pgRb]
      positivity
    linarith
  have hlog_le : Real.log (1 + pgRb d) ≤ Real.log (256 * x * Real.sqrt x) :=
    Real.log_le_log hpos_sum hsum_le
  have hlog_rhs : Real.log (256 * x * Real.sqrt x) = Real.log (256 : ℝ) + Real.log x + Real.log (Real.sqrt x) := by
    calc
      Real.log (256 * x * Real.sqrt x) = Real.log ((256 * x) * Real.sqrt x) := by ring
      _ = Real.log (256 * x) + Real.log (Real.sqrt x) :=
        Real.log_mul (by positivity) (by positivity)
      _ = (Real.log (256 : ℝ) + Real.log x) + Real.log (Real.sqrt x) := by
        rw [Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (by positivity : x ≠ 0)]
      _ = Real.log (256 : ℝ) + Real.log x + Real.log (Real.sqrt x) := by ring
  have hlog_sqrt : Real.log (Real.sqrt x) = (1/2 : ℝ) * Real.log x := by
    rw [Real.log_sqrt hxpos.le]
    ring
  have hlog_256 : Real.log (256 : ℝ) = 4 * Real.log 4 := by
    have h : (256 : ℝ) = (4 : ℝ) ^ 4 := by norm_num
    rw [h, Real.log_pow, Nat.cast_ofNat]
  have hlog4_le_logx : Real.log 4 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx4
  calc
    Real.log (1 + pgRb d) ≤ Real.log (256 * x * Real.sqrt x) := hlog_le
    _ = Real.log (256 : ℝ) + Real.log x + Real.log (Real.sqrt x) := hlog_rhs
    _ = (4 * Real.log 4) + Real.log x + ((1/2 : ℝ) * Real.log x) := by rw [hlog_256, hlog_sqrt]
    _ = 4 * Real.log 4 + (3/2 : ℝ) * Real.log x := by ring
    _ ≤ 4 * Real.log x + (3/2 : ℝ) * Real.log x := by nlinarith
    _ = (11/2 : ℝ) * Real.log x := by ring
    _ ≤ 5.5 * Real.log x := by
      have h : (11/2 : ℝ) ≤ 5.5 := by norm_num
      nlinarith
    _ = 5.5 * Real.log (2 * d + 2) := by rfl

theorem pg_growing (d : ℝ) (hd : 1 ≤ d) :
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ pgRb d → 3 * 54 * d * Real.sqrt (Real.log (1 + ρ)) ≤ pgRb d) ∧
      54 * d * Real.sqrt (Real.log (1 + pgRb d)) ≤ 134 * d * Real.sqrt (Real.log (2 * d + 2)) := by
  have hd_nonneg : 0 ≤ d := by linarith
  have h_log2pos : 0 < Real.log (2 * d + 2) := by
    have hpos : 1 < 2 * d + 2 := by nlinarith
    exact Real.log_pos hpos
  have h_log2_nonneg : 0 ≤ Real.log (2 * d + 2) := le_of_lt h_log2pos
  have h_log_bound : Real.log (1 + pgRb d) ≤ 5.5 * Real.log (2 * d + 2) := pg_rb_log d hd
  have h_sqrt797_nonneg : 0 ≤ Real.sqrt (5.5 : ℝ) := Real.sqrt_nonneg _
  -- numeric inequalities
  have h_sq1 : (5.5 : ℝ) ≤ (400 / 162)^2 := by norm_num
  have h_sqrt1 : Real.sqrt (5.5 : ℝ) ≤ 400 / 162 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have h_sq2 : (5.5 : ℝ) ≤ (134 / 54)^2 := by norm_num
  have h_sqrt2 : Real.sqrt (5.5 : ℝ) ≤ 134 / 54 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have h_sqrtL_nonneg : 0 ≤ Real.sqrt (Real.log (2 * d + 2)) := Real.sqrt_nonneg _
  constructor
  · intro ρ hρ_nonneg hρ_le
    have h_log_rho : Real.log (1 + ρ) ≤ Real.log (1 + pgRb d) :=
      Real.log_le_log (by linarith) (by linarith)
    have h_log_rho' : Real.log (1 + ρ) ≤ 5.5 * Real.log (2 * d + 2) := by linarith
    have h_sqrt_rho : Real.sqrt (Real.log (1 + ρ)) ≤ Real.sqrt (5.5 * Real.log (2 * d + 2)) :=
      Real.sqrt_le_sqrt h_log_rho'
    have h_sqrt_mul : Real.sqrt (5.5 * Real.log (2 * d + 2)) = Real.sqrt (5.5 : ℝ) * Real.sqrt (Real.log (2 * d + 2)) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (5.5 : ℝ))]
    have h_ineq : Real.sqrt (Real.log (1 + ρ)) ≤ (400 / 162) * Real.sqrt (Real.log (2 * d + 2)) := by
      calc
        Real.sqrt (Real.log (1 + ρ)) ≤ Real.sqrt (5.5 * Real.log (2 * d + 2)) := h_sqrt_rho
        _ = Real.sqrt (5.5 : ℝ) * Real.sqrt (Real.log (2 * d + 2)) := h_sqrt_mul
        _ ≤ (400 / 162) * Real.sqrt (Real.log (2 * d + 2)) := by
          nlinarith
    calc
      3 * 54 * d * Real.sqrt (Real.log (1 + ρ)) = (3 * 54) * d * Real.sqrt (Real.log (1 + ρ)) := by ring
      _ ≤ (3 * 54) * d * ((400 / 162) * Real.sqrt (Real.log (2 * d + 2))) := by
        nlinarith
      _ = (3 * 54 * (400 / 162)) * d * Real.sqrt (Real.log (2 * d + 2)) := by ring
      _ = 400 * d * Real.sqrt (Real.log (2 * d + 2)) := by norm_num
      _ = pgRb d := rfl
  · have h_sqrt_log : Real.sqrt (Real.log (1 + pgRb d)) ≤ Real.sqrt (5.5 * Real.log (2 * d + 2)) :=
      Real.sqrt_le_sqrt h_log_bound
    have h_sqrt_mul : Real.sqrt (5.5 * Real.log (2 * d + 2)) = Real.sqrt (5.5 : ℝ) * Real.sqrt (Real.log (2 * d + 2)) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (5.5 : ℝ))]
    have h_ineq : Real.sqrt (Real.log (1 + pgRb d)) ≤ (134 / 54) * Real.sqrt (Real.log (2 * d + 2)) := by
      calc
        Real.sqrt (Real.log (1 + pgRb d)) ≤ Real.sqrt (5.5 * Real.log (2 * d + 2)) := h_sqrt_log
        _ = Real.sqrt (5.5 : ℝ) * Real.sqrt (Real.log (2 * d + 2)) := h_sqrt_mul
        _ ≤ (134 / 54) * Real.sqrt (Real.log (2 * d + 2)) := by
          nlinarith
    calc
      54 * d * Real.sqrt (Real.log (1 + pgRb d)) = (54 * d) * Real.sqrt (Real.log (1 + pgRb d)) := by ring
      _ ≤ (54 * d) * ((134 / 54) * Real.sqrt (Real.log (2 * d + 2))) := by
        nlinarith
      _ = (54 * (134 / 54)) * d * Real.sqrt (Real.log (2 * d + 2)) := by ring
      _ = 134 * d * Real.sqrt (Real.log (2 * d + 2)) := by norm_num

/-! ## Further leaves -/

theorem pg_step (a e N : ℝ) (ha : 0 < a) (he : 0 < e) (hN : 16 * a ^ 2 / e ^ 2 ≤ N) :
    a / Real.sqrt N ≤ e / 4 := by
  have hpos : 0 < 16 * a ^ 2 / e ^ 2 := by positivity
  have hN0 : 0 < N := lt_of_lt_of_le hpos hN
  have h1 : 16 * a ^ 2 ≤ N * e ^ 2 := by rwa [div_le_iff₀ (by positivity)] at hN
  have hs : 4 * a ≤ e * Real.sqrt N := by
    have h2 : (4 * a) ^ 2 ≤ e ^ 2 * Real.sqrt N ^ 2 := by
      rw [Real.sq_sqrt hN0.le]; nlinarith
    nlinarith [Real.sqrt_nonneg N, mul_nonneg he.le (Real.sqrt_nonneg N)]
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hN0) (by norm_num)]
  linarith

theorem pg_conclusion :
    36.4 / pgA ≤ (36.4 : ℝ) ∧ pgA * (1 / (1 - 0.1375)) ≤ (1.27 : ℝ) ∧ 36.4 * Real.sqrt 2 ≤ 54 ∧
      54 * Real.sqrt 5.5 ≤ 134 ∧ 134 * 1.27 ≤ (180 : ℝ) := by
  refine ⟨by norm_num [pgA], by norm_num [pgA], ?_, ?_, by norm_num⟩
  · have : Real.sqrt 2 ≤ 1.4144 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    linarith
  · have : Real.sqrt 5.5 ≤ 2.35 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    linarith

/-- `Q(a) ≥ 0.1375` at `a = 1`, from `Q(1) ≥ 0.156` (`Body2.Qtail_one_bounds`). -/
theorem qtail_a_ge : (0.1375 : ℝ) ≤ BodySpec.Qtail pgA := by
  unfold pgA
  exact le_trans (by norm_num) AdversarialBco.Body2.Qtail_one_bounds.1

theorem pg_moments (d : ℝ) (hd : 0 ≤ d) :
    d + d * (d + 2) = d * (d + 3) ∧
      d * (d + 2) * (d + 4) - d * (d + 2) + (d - 2) * d + d = d * (d + 1) * (d + 5) ∧
      2 * d * (d + 3) + 4 * d * (d + 1) * (d + 5) ≤ 4 * d * (d + 2) * (d + 5) := by
  refine ⟨by ring, by ring, ?_⟩
  nlinarith [sq_nonneg d, mul_nonneg hd (sq_nonneg d)]

/-! ## Assemblies -/

theorem pgPropAi : PgPropAi := pg_propAi
theorem pgC2Bound : PgC2Bound := pg_c2_bound
theorem pgCorAi : PgCorAi := pg_corAi
theorem pgCorAii : PgCorAii := pg_corAii
theorem pgCorAiii : PgCorAiii := pg_corAiii
theorem pgBiasU : PgBiasU := pg_bias_u
theorem pgBiasTest : PgBiasTest := pg_bias_test
theorem pgEtaSq : PgEtaSq := pg_eta_sq
theorem pgBiasDescent : PgBiasDescent := pg_bias_descent
theorem pgCounts : PgCounts := pg_counts
theorem pgNSize : PgNSize := pg_N_size
theorem pgNTSize : PgNTSize := pg_NT_size
theorem pgRhoEta : PgRhoEta := pg_rho_eta
theorem pgBisectSteps : PgBisectSteps := pg_bisect_steps
theorem pgFailure : PgFailure := pg_failure
theorem pgHoeffding : PgHoeffding := pg_hoeffding
theorem pgStep : PgStep := pg_step
theorem pgConclusion : PgConclusion := pg_conclusion
theorem pgQtail : PgQtail := qtail_a_ge
theorem pgRbLog : PgRbLog := pg_rb_log
theorem pgGrowing : PgGrowing := pg_growing
theorem pgMoments : PgMoments := pg_moments

end AdversarialBco.Poly
