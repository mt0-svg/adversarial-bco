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
# The arithmetic of the theorem of Procedure PG: proofs

Proofs of the interface statements of `AdversarialBco/Poly/PgArith.lean`: the leaves `pg_propAi`, `pg_corAi`,
`pg_corAii`, `pg_corAiii`, `pg_conclusion`, and `qtail_a_ge` from `Body2.Qtail_one_bounds`, then one assembly per
`Prop`.
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

/-! ## Further leaves -/

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

/-! ## Assemblies -/

theorem pgPropAi : PgPropAi := pg_propAi
theorem pgCorAi : PgCorAi := pg_corAi
theorem pgCorAii : PgCorAii := pg_corAii
theorem pgCorAiii : PgCorAiii := pg_corAiii
theorem pgConclusion : PgConclusion := pg_conclusion
theorem pgQtail : PgQtail := qtail_a_ge

end AdversarialBco.Poly
