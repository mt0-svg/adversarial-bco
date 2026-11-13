/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProcProof

@[expose] public section

/-!
# The near-minimiser theorem: the chain from a near-minimiser to a good position, with no domain

* `pgComplete_sound`: the complete condition implies the sound condition.
* `posF_lipschitz_of_opNorm`, `pgCorA_gen`, `pgSound_good_gen`, `pgGood_of_nearMin_gen` (the near-minimiser theorem):
  the chain for any invertible position, symmetric or not, in no domain. It reads the position only through
  `det ≠ 0` and the Lipschitz constant `pgLD ρ` of `posF`, and that constant follows from near-minimality by
  `d1Bounds` when the body lies in the ball of radius `ρ0` with `1.05 ρ0 ≤ ρ`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

open AdversarialBco.Poly

theorem AdversarialBco.Bit.pgComplete_sound {d : ℕ} (hd : 1 ≤ d) (ρ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (x : PgSp d) (h : PgComplete K ρ x) : PgSound K ρ x := by
  obtain ⟨hk, hb, hq⟩ := h
  have hκ : 0 < pgKappa := by unfold pgKappa; norm_num
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hτ : 0 ≤ pgTaub d ρ := by
    unfold pgTaub pgLam
    have h1 : 0 ≤ Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ 12 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) := by positivity
    exact div_nonneg hκ.le h2
  refine ⟨by linarith, by linarith, fun v => ?_⟩
  have h1 := hq v
  have h2 : pgKappa / (2 * d) ≤ 3 / 4 * (pgKappa / d) := by
    have e1 : pgKappa / (2 * (d : ℝ)) = 1 / 2 * (pgKappa / d) := by field_simp
    have e2 : 0 ≤ pgKappa / (d : ℝ) := div_nonneg hκ.le hd'.le
    rw [e1]; nlinarith
  have h3 : pgKappa / (2 * d) * ‖v‖ ^ 2 ≤ 3 / 4 * (pgKappa / d) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

theorem AdversarialBco.Bit.posF_lipschitz_of_opNorm {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (h1 : Metric.closedBall 0 1 ⊆ K) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (L : ℝ) (hT : ‖T‖ ≤ L) :
    LipschitzWith (Real.toNNReal L) (posF K μ T) := by
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ≥0) ⊆ K := by
    simpa using Metric.ball_subset_closedBall.trans h1
  have hgL : LipschitzWith 1 (gauge K) := by
    simpa using hK.lipschitzWith_gauge (r := 1) one_pos hball
  have hL0 : 0 ≤ L := (norm_nonneg T).trans hT
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  show dist (gauge K (μ + T y)) (gauge K (μ + T y')) ≤ _
  have h := hgL.dist_le_mul (μ + T y) (μ + T y')
  rw [NNReal.coe_one, one_mul, dist_eq_norm (μ + T y), add_sub_add_left_eq_sub, ← map_sub] at h
  rw [dist_eq_norm y y', Real.coe_toNNReal _ hL0]
  calc dist (gauge K (μ + T y)) (gauge K (μ + T y')) ≤ ‖T (y - y')‖ := h
    _ ≤ ‖T‖ * ‖y - y'‖ := T.le_opNorm _
    _ ≤ L * ‖y - y'‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)

/-- Corollary A for any invertible position: the body in the ball of radius `ρ0`, the analysis at a radius
`ρ ≥ 1.05 ρ0`. No domain: the Lipschitz constant `pgLD ρ` of `posF` comes from `k ≤ 1.05 κ` and `d1Bounds`. -/
theorem AdversarialBco.Bit.pgCorA_gen (d : ℕ) (ρ0 ρ : ℝ) (hd : 1 ≤ d) (hρ0 : 1 ≤ ρ0) (hρρ : 1.05 * ρ0 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ0) (x : PgSp d) (hdet : (pgMat x).det ≠ 0)
    (hstar : ℝ)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K pgKappa μ' A')
    (hx' : pgH K x ≤ hstar + pgEh d ρ) : PgComplete K ρ x := by
  have hρ : 1 ≤ ρ := by linarith
  have hKρ : PgBody K ρ := pgBody_mono K ρ0 ρ (by linarith) hK
  let μ := pgMu x
  let T := pgOp x
  let κ := pgKappa
  let e := pgEh d ρ
  let L := pgLD ρ
  have hκ_pos : 0 < κ := by
    unfold κ pgKappa
    norm_num
  have hpos_body : IsPosBody K 1 ρ := pgBody_isPosBody K ρ hρ hKρ
  have hdet_lin : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    show LinearMap.det (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0
    rw [pgOp_det]; exact hdet
  have hL_nonneg : 0 ≤ L := by
    unfold L pgLD pgKappa pgPB
    positivity
  have hx'_obj : posObj K κ μ T ≤ hstar + e := by
    unfold pgH at hx'
    simpa [κ, μ, T, e] using hx'
  -- Part (i): pgKs K x ≤ 1.05 * pgKappa
  have h_part1 : pgKs K x ≤ 1.05 * κ := by
    unfold pgKs
    by_cases hk_nonpos : posK K μ T ≤ 0
    · linarith [hκ_pos]
    · have hk_pos : 0 < posK K μ T := by linarith
      have hAi_app := propAi d K 1 ρ κ hstar e μ T hd hpos_body hκ_pos hdet_lin hmin hx'_obj hk_pos
      have hCAi_app := pgCorAi (d : ℝ) ρ (by exact_mod_cast hd) hρ
      have he_lt : e < 0.0012 * κ := by
        simpa [κ, pgKappa, e] using hCAi_app
      set r := posK K μ T / κ with hr_def
      have hr_pos : 0 < r := by
        rw [hr_def]
        exact div_pos hk_pos hκ_pos
      have h_ineq : κ * (r - 1 - Real.log r) ≤ e := by
        simpa [hr_def] using hAi_app
      have h_lt_0012 : r - 1 - Real.log r < 0.0012 := by
        have h_mul_lt : κ * (r - 1 - Real.log r) < 0.0012 * κ := by linarith
        have h_mul_lt' : κ * (r - 1 - Real.log r) < κ * 0.0012 := by
          simpa [mul_comm] using h_mul_lt
        exact lt_of_mul_lt_mul_left h_mul_lt' hκ_pos.le
      have hr_le_105 : r ≤ 1.05 := pgPropAi r hr_pos h_lt_0012
      rw [hr_def] at hr_le_105
      calc
        posK K μ T = (posK K μ T / κ) * κ := by field_simp [hκ_pos.ne.symm]
        _ ≤ 1.05 * κ := mul_le_mul_of_nonneg_right hr_le_105 hκ_pos.le
  -- The Lipschitz constant: `‖T‖ ≤ pgLD ρ` from `k ≤ 1.05 κ` and (D1) at the radius `ρ0` of the body.
  have hTnorm : ‖T‖ ≤ L := by
    have hD1 := (d1Bounds d K ρ0 μ T (by linarith) hK.1 hK.2.2.1 hK.2.2.2).2
    have hs_pos : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hPB := one_le_pgPB_mul_sqrt
    have hk105 : posK K μ T ≤ 1.05 * κ := h_part1
    have hadj : ‖ContinuousLinearMap.adjoint T‖ ≤ L := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm hL_nonneg fun u hu => ?_
      have h1 := hD1 u hu
      have ha : 0 ≤ ‖(ContinuousLinearMap.adjoint T) u‖ := norm_nonneg _
      have hPB0 : 0 ≤ pgPB := by unfold pgPB; norm_num
      have h2 : ‖(ContinuousLinearMap.adjoint T) u‖ ≤
          pgPB * (‖(ContinuousLinearMap.adjoint T) u‖ * Real.sqrt (2 / Real.pi)) := by
        have : ‖(ContinuousLinearMap.adjoint T) u‖ * 1 ≤
            ‖(ContinuousLinearMap.adjoint T) u‖ * (pgPB * Real.sqrt (2 / Real.pi)) :=
          mul_le_mul_of_nonneg_left hPB ha
        nlinarith
      have h3 : pgPB * (‖(ContinuousLinearMap.adjoint T) u‖ * Real.sqrt (2 / Real.pi)) ≤
          pgPB * (ρ0 * (1.05 * κ)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hPB0
        exact mul_le_mul_of_nonneg_left hk105 (by linarith)
      have h4 : pgPB * (ρ0 * (1.05 * κ)) ≤ L := by
        have : pgPB * (ρ0 * (1.05 * κ)) = κ * pgPB * (1.05 * ρ0) := by ring
        rw [this]
        show κ * pgPB * (1.05 * ρ0) ≤ pgKappa * pgPB * ρ
        exact mul_le_mul_of_nonneg_left hρρ (mul_nonneg hκ_pos.le hPB0)
      linarith
    calc ‖T‖ = ‖ContinuousLinearMap.adjoint T‖ := (LinearIsometryEquiv.norm_map _ T).symm
      _ ≤ L := hadj
  have hLip : LipschitzWith (Real.toNNReal L) (posF K μ T) :=
    posF_lipschitz_of_opNorm K hK.1 hK.2.2.1 μ T L hTnorm
  -- Part (ii): ‖pgBs K x‖ ≤ pgTaub d ρ / 2
  have h_part2 : ‖pgBs K x‖ ≤ pgTaub d ρ / 2 := by
    unfold pgBs
    have hAiii_app := propAiii d K 1 ρ κ hstar e μ T hpos_body hdet_lin hmin hx'_obj
      (Real.toNNReal L) hLip
    have hAiii_app' : ‖posB K μ T‖ ^ 2 ≤ 2 * Real.sqrt (2 / Real.pi) * L * e := by
      simpa [hL_nonneg] using hAiii_app
    have h_sqrt_bound : 2 * Real.sqrt (2 / Real.pi) ≤ (1.6 : ℝ) := by
      have hπ_gt : (3.125 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
      have h_sq : (2 / Real.pi) ≤ (0.64 : ℝ) := by
        have hpos : 0 < Real.pi := Real.pi_pos
        rw [div_le_iff₀ hpos]; nlinarith
      have h_sqrt : Real.sqrt (2 / Real.pi) ≤ Real.sqrt (0.64 : ℝ) :=
        Real.sqrt_le_sqrt h_sq
      have h_sqrt_064 : Real.sqrt (0.64 : ℝ) = 0.8 := by
        rw [show (0.64 : ℝ) = 0.8 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [h_sqrt_064] at h_sqrt
      linarith
    have h_mid : 2 * Real.sqrt (2 / Real.pi) * L * e ≤ 1.6 * L * e := by
      have he_nonneg : 0 ≤ e := by
        unfold e pgEh pgKappa
        positivity
      have h_nonneg_prod : 0 ≤ L * e := mul_nonneg hL_nonneg he_nonneg
      have h := mul_le_mul_of_nonneg_right h_sqrt_bound h_nonneg_prod
      simpa [mul_assoc] using h
    have hCAiii_app := pgCorAiii (d : ℝ) ρ (by exact_mod_cast hd) hρ
    have h_final : ‖posB K μ T‖ ^ 2 ≤ (pgTaub d ρ / 2) ^ 2 := by
      linarith
    have h_nonneg_b : 0 ≤ ‖posB K μ T‖ := norm_nonneg _
    have h_nonneg_taub : 0 ≤ pgTaub d ρ / 2 := by
      have : 0 ≤ pgTaub d ρ := by
        unfold pgTaub pgKappa
        have hLam_nonneg : 0 ≤ pgLam ρ := by
          unfold pgLam
          exact Real.sqrt_nonneg _
        have hd_pos : 0 < (d : ℝ) := by
          have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        positivity
      positivity
    nlinarith
  -- Part (iii): ∀ v, 3 / 4 * (pgKappa / d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v
  have h_part3 : ∀ v, 3 / 4 * (κ / d) * ‖v‖ ^ 2 ≤ posQ K μ T v v := by
    intro v
    by_cases hv_zero : v = 0
    · subst hv_zero
      simp [posQ]
    · have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
      let u := (‖v‖⁻¹ : ℝ) • v
      have hu_norm : ‖u‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp [hv_norm_pos.ne.symm]
      have h_t_pos : (0 : ℝ) < 1/4 := by norm_num
      have h_t_lt_one : (1/4 : ℝ) < 1 := by norm_num
      have h_e_cond : e < ((1/4 : ℝ) ^ 2) * (κ / (d : ℝ)) ^ 2 / (2 * (pgC2 * (Real.toNNReal L) + κ / (d : ℝ))) := by
        have hCAii_app := pgCorAii (d : ℝ) ρ (by exact_mod_cast hd) hρ
        have h_eq : ((1/4 : ℝ) ^ 2) * (κ / (d : ℝ)) ^ 2 / (2 * (pgC2 * (Real.toNNReal L) + κ / (d : ℝ))) =
            κ ^ 2 / (32 * (d : ℝ) ^ 2 * (pgC2 * L + κ / (d : ℝ))) := by
          have hL_eq : (Real.toNNReal L : ℝ) = L := by
            rw [Real.coe_toNNReal _ hL_nonneg]
          have hd_ne_zero : (d : ℝ) ≠ 0 := by
            have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
            linarith
          rw [hL_eq]
          field_simp [hd_ne_zero]
          ring
        rw [h_eq]
        exact hCAii_app
      have hAii_app := propAii d K 1 ρ κ hstar e (1/4) μ T hd hpos_body hκ_pos hdet_lin hmin hx'_obj
        (Real.toNNReal L) hLip h_t_pos h_t_lt_one h_e_cond
      have h_bound_u : (1 - (1/4 : ℝ)) * (κ / d) ≤ posQ K μ T u u :=
        hAii_app u hu_norm
      have h_34 : (1 - (1/4 : ℝ)) = (3/4 : ℝ) := by norm_num
      rw [h_34] at h_bound_u
      have h_posQ_homog : posQ K μ T v v = ‖v‖ ^ 2 * posQ K μ T u u := by
        have hv_eq : v = ‖v‖ • u := by
          dsimp [u]
          calc
            v = 1 • v := by rw [one_smul]
            _ = (‖v‖ * (‖v‖⁻¹ : ℝ)) • v := by
              simp [hv_norm_pos.ne.symm]
            _ = ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) := by rw [smul_smul]
        have h_homog1 : ∀ (c : ℝ) (a b : EuclideanSpace ℝ (Fin d)),
            posQ K μ T (c • a) b = c * posQ K μ T a b := by
          intro c a b
          unfold posQ
          have h1 : (fun (g : EuclideanSpace ℝ (Fin d)) =>
            (⟪c • a, g⟫ * ⟪b, g⟫ - ⟪c • a, b⟫) * posF K μ T g) =
            (fun g => c * ((⟪a, g⟫ * ⟪b, g⟫ - ⟪a, b⟫) * posF K μ T g)) := by
            ext g
            have h_inner1 : ⟪c • a, g⟫ = c * ⟪a, g⟫ := by
              rw [inner_smul_left]
              simp
            have h_inner2 : ⟪c • a, b⟫ = c * ⟪a, b⟫ := by
              rw [inner_smul_left]
              simp
            calc
              (⟪c • a, g⟫ * ⟪b, g⟫ - ⟪c • a, b⟫) * posF K μ T g
                  = ((c * ⟪a, g⟫) * ⟪b, g⟫ - (c * ⟪a, b⟫)) * posF K μ T g := by simp [h_inner1, h_inner2]
              _ = c * ((⟪a, g⟫ * ⟪b, g⟫ - ⟪a, b⟫) * posF K μ T g) := by ring
          rw [h1]
          rw [integral_const_mul]
        have h_symm : ∀ a b, posQ K μ T a b = posQ K μ T b a := by
          intro a b
          unfold posQ
          refine integral_congr_ae ?_
          filter_upwards with g
          simp [mul_comm, sub_eq_add_neg, real_inner_comm]
        calc
          posQ K μ T v v = posQ K μ T (‖v‖ • u) v := by
            exact congrArg (fun w => posQ K μ T w v) hv_eq
          _ = ‖v‖ * posQ K μ T u v := h_homog1 ‖v‖ u v
          _ = ‖v‖ * posQ K μ T v u := by rw [h_symm u v]
          _ = ‖v‖ * posQ K μ T (‖v‖ • u) u :=
            congrArg (fun w => ‖v‖ * posQ K μ T w u) hv_eq
          _ = ‖v‖ * (‖v‖ * posQ K μ T u u) := by rw [h_homog1 ‖v‖ u u]
          _ = ‖v‖ ^ 2 * posQ K μ T u u := by ring
      rw [h_posQ_homog]
      have h_sq_pos : 0 ≤ ‖v‖ ^ 2 := by positivity
      have h_temp := mul_le_mul_of_nonneg_right h_bound_u h_sq_pos
      simpa [mul_comm] using h_temp
  exact ⟨h_part1, h_part2, h_part3⟩

/-- The sound condition gives a good position, for any invertible position (the proof reads the position only
through `det ≠ 0`); the position returned is `x` itself (`pgOut x` has the same vector and matrix). -/
theorem AdversarialBco.Bit.pgSound_good_gen (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hdet : (pgMat x).det ≠ 0)
    (hs : PgSound K ρ x) :
    PgGood d K (36.4 * d * pgLam ρ) (some x) := by
  obtain ⟨hk, hb, hq⟩ := hs
  have hPB : IsPosBody K 1 ρ := pgBody_isPosBody K ρ hρ hK
  have hdetT : LinearMap.det (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rw [pgOp_det]; exact hdet
  have hk' : posK K (pgMu x) (pgOp x) ≤ 0.1375 := by
    have h := hk; unfold pgKs pgKappa at h; linarith
  have hk0 : 0 ≤ posK K (pgMu x) (pgOp x) := by
    unfold posK posF; exact integral_nonneg fun g => gauge_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨x, rfl, hdet, ?_, ?_, ?_⟩
  · have hQt : (0.1375 : ℝ) ≤ BodySpec.Qtail 1 := by
      have h : (0.1375 : ℝ) ≤ BodySpec.Qtail pgA := pgQtail
      unfold pgA at h; exact h
    exact propCb d K 1 ρ (pgMu x) (pgOp x) hPB 1 (by linarith)
  · obtain ⟨t, ht0, htl, hC⟩ := gaussConst ρ hρ
    have hlam : 0 < pgLam ρ := by
      unfold pgLam
      have := Real.log_pos (by linarith : (1 : ℝ) < 1 + ρ)
      exact Real.sqrt_pos.2 (by linarith)
    have htl' : t ≤ pgLam ρ := htl
    have hC' : bathC ρ t ≤ pgLam ρ := hC
    have hq0 : 0 < pgKappa / (2 * d) := by unfold pgKappa; positivity
    have hb' : ‖posB K (pgMu x) (pgOp x)‖ ≤ pgTaub d ρ := hb
    have h6 : 6 * |t| * ‖posB K (pgMu x) (pgOp x)‖ ≤ pgKappa / (2 * d) := by
      rw [abs_of_nonneg ht0]
      calc 6 * t * ‖posB K (pgMu x) (pgOp x)‖ ≤ 6 * pgLam ρ * pgTaub d ρ := by gcongr
        _ = pgKappa / (2 * d) := by unfold pgTaub; field_simp; ring
    intro y hy
    have hy' := propCaBound d K 1 ρ (pgMu x) (pgOp x) hPB hdetT (pgKappa / (2 * d)) t hq0 hq h6 y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine hy'.trans ?_
    rw [div_le_iff₀ hq0]
    have hR : 36.4 * (d : ℝ) * pgLam ρ * (pgKappa / (2 * d)) = 2.275 * pgLam ρ := by
      unfold pgKappa; field_simp; ring
    rw [hR]
    have hkey : (1 + posK K (pgMu x) (pgOp x)) * bathC ρ t ≤ 1.1375 * pgLam ρ := by
      rcases le_total 0 (bathC ρ t) with h | h
      · nlinarith
      · nlinarith
    linarith
  · unfold pgMw
    have hc := propCc d K 1 ρ (pgMu x) (pgOp x) hPB (by linarith)
    have hnm := normMeanLower d
    have hsq : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.2 (by linarith)
    have hN : 0 < ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      lt_of_lt_of_le (by positivity) hnm
    have hI : ∫ g, gauge (posBody K (pgMu x) (pgOp x)) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 1.27 := by
      refine hc.trans ?_
      have h1 : 1 / (1 - posK K (pgMu x) (pgOp x)) ≤ 1 / (1 - 0.1375) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h2 := pgConclusion.2.1
      unfold pgA at h2
      linarith
    rw [div_le_iff₀ hN]
    have hkey : (1.27 : ℝ) ≤ 1.27 * Real.sqrt (d + 1) / d * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      calc (1.27 : ℝ) = 1.27 * Real.sqrt (d + 1) / d * (d / Real.sqrt (d + 1)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hnm (by positivity)
    linarith

/-- The chain with no domain: for a closed convex body between the balls of radii `1` and `ρ0`, and `ρ ≥ 1.05 ρ0`, every
invertible position whose objective is within `pgEh d ρ` of a lower bound of the objective over all invertible
positions is a good position at the radius `36.4 d λ(ρ)`. The matrix of the position need not be symmetric. -/
theorem AdversarialBco.Bit.pgGood_of_nearMin_gen (d : ℕ) (ρ0 ρ : ℝ) (hd : 1 ≤ d) (hρ0 : 1 ≤ ρ0) (hρρ : 1.05 * ρ0 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ0) (x : PgSp d) (hdet : (pgMat x).det ≠ 0)
    (hstar : ℝ)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K pgKappa μ' A')
    (hx' : pgH K x ≤ hstar + pgEh d ρ) : PgGood d K (36.4 * d * pgLam ρ) (some x) :=
  pgSound_good_gen d ρ hd (by linarith) K (pgBody_mono K ρ0 ρ (by linarith) hK) x hdet
    (pgComplete_sound hd ρ K x (pgCorA_gen d ρ0 ρ hd hρ0 hρρ K hK x hdet hstar hmin hx'))
