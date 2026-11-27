/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.Clamp

@[expose] public section

/-!
# The widened row of the round (leaves B3, C1, C3, C4)

* C3: `(1 + η)² ≤ 21/20` (`PgEtaSqN`, from the proof of `pg_eta_sq`, PgArithProof.lean, which reaches `η < 10⁻⁴`).
* B3: the second moment of Lemma E (b') with `21/20` in place of `5/4`: `F~(g)² ≤ (21/20) 2 L_D² (1 + |g|²)`
  (`pgFt_sq_leN`, from `pgFt_sq_le`, PgProcProof.lean) and `E |V|² ≤ G₁²` (`pgV_second_momentN`, from `pgFt_sq_leN`,
  `pgV_norm_sq_le` and the Gaussian moments), `G₁² = (4 (21/20) L_D² d (d + 2)(d + 5) + 2 κ²/d)/t_min²` (`pgG2q`).
* C4: `G₁² ≤ (7/8) G²`.
* C1: the row of the round, Lemma SGD-e with the moment bound `G₁`, the step `s = Δ/(G N^{1/2})`, `θ = 10⁻⁶` and
  `e = e_P`: `Δ²/(2 s N) + (1 + θ) s G₁²/2 + β Δ + e_P Δ/s + e_P² (1 + 1/θ)/(2 s) ≤ e_h/2`.

C3, C4, B3 and C1 are proved, C3 and B3a by the cited proofs with the constants changed, C1 over the leaves C1a
(`row_abstract`) and C1b (`pgEh_le_delta_sqrtG2`). Everything here is proved.
Junk values: `pgG2q` divides by `d` and `t_min²`, positive for
`d, ρ ≥ 1`; the row divides by `s` and `θ`, positive.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly

/-- `G₁² = (4 (21/20) L_D² d (d + 2)(d + 5) + 2 κ²/d)/t_min²`, the second moment bound of Lemma E (b'). -/
noncomputable def pgG2q (d ρ : ℝ) : ℝ :=
  (21 / 5 * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) / pgTmin d ρ ^ 2

/-- `θ = 10⁻⁶`. -/
noncomputable def pgTheta : ℝ := 1 / 10 ^ 6

/-- Lemma E (b'): `0 ≤ η` and `(1 + η)² ≤ 21/20`. -/
def PgEtaSqN : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → 0 ≤ pgEta d ρ ∧ (1 + pgEta d ρ) ^ 2 ≤ 21 / 20

/-- C3, the proof of `pg_eta_sq` (PgArithProof.lean) copied, which reaches `η < 10⁻⁴`. -/
theorem pgEtaSqN : PgEtaSqN := by
  intro d ρ hd hρ
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
  have h_bound : (1 + pgEta d ρ) ^ 2 ≤ 21 / 20 := by
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
    have h_sq_bound : (1 + pgEta d ρ) ^ 2 ≤ 21 / 20 := by
      have h_sq_lt : (1 + pgEta d ρ) ^ 2 < (1 + 1/10000) ^ 2 := by
        nlinarith
      have h_target : (1 + 1/10000) ^ 2 ≤ 21 / 20 := by
        norm_num
      linarith
    exact h_sq_bound
  exact And.intro h_nonneg h_bound

/-- C4. -/
theorem pgG2q_le (d ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 0 ≤ pgG2q d ρ ∧ pgG2q d ρ ≤ 7 / 8 * pgG2 d ρ := by
  have hdpos : 0 < d := by linarith
  have hpgLam_pos : 0 < pgLam ρ := by
    dsimp [pgLam]
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    have hpos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
    exact Real.sqrt_pos.mpr hpos
  have hpgTmin_pos : 0 < pgTmin d ρ := by
    dsimp [pgTmin]
    have hnum : 0 < (1 : ℝ) := by norm_num
    have hden : 0 < 9 * d * pgLam ρ := by positivity
    exact div_pos hnum hden
  have htsq_pos : 0 < pgTmin d ρ ^ 2 := pow_pos hpgTmin_pos 2
  have hG2q_nonneg : 0 ≤ pgG2q d ρ := by
    dsimp [pgG2q]
    refine div_nonneg ?_ (by positivity)
    positivity
  have hG2_nonneg : 0 ≤ pgG2 d ρ := by
    dsimp [pgG2]
    refine div_nonneg ?_ (by positivity)
    positivity
  have h_ineq : pgG2q d ρ ≤ 7 / 8 * pgG2 d ρ := by
    dsimp [pgG2q, pgG2]
    have hnum : (21 / 5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d ≤
        (7 / 8 : ℝ) * ((5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) := by
      have hkey : 10 * (pgKappa ^ 2 / d) ≤ 7 * (pgLD ρ ^ 2 * d * (d + 2) * (d + 5)) := by
        dsimp [pgLD, pgKappa, pgPB]
        have h_cleared : (10 : ℝ) ≤ 7 * ((1254 / 1000 : ℝ) ^ 2) * (ρ ^ 2) * (d ^ 2) * ((d + 2) * (d + 5)) := by
          have h_base : (10 : ℝ) ≤ 7 * ((1254 / 1000 : ℝ) ^ 2) * (18 : ℝ) := by norm_num
          have h_factors : (18 : ℝ) ≤ (ρ ^ 2) * (d ^ 2) * ((d + 2) * (d + 5)) := by
            have hρ2 : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith
            have hd2 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
            have hd_add2 : (3 : ℝ) ≤ d + 2 := by linarith
            have hd_add5 : (6 : ℝ) ≤ d + 5 := by linarith
            calc
              (18 : ℝ) = (1 : ℝ) * (1 : ℝ) * ((3 : ℝ) * (6 : ℝ)) := by norm_num
              _ ≤ (ρ ^ 2) * (d ^ 2) * ((d + 2) * (d + 5)) := by
                gcongr
          have h_nonneg : 0 ≤ 7 * ((1254 / 1000 : ℝ) ^ 2) := by positivity
          nlinarith
        have h_mul : (10 * (((1 : ℝ) / 8) ^ 2 / d)) * d ≤
            (7 * (((1 : ℝ) / 8 * (1254 / 1000) * ρ) ^ 2 * d * (d + 2) * (d + 5))) * d := by
          field_simp [hdpos.ne.symm]
          field_simp at h_cleared
          simpa [mul_comm, mul_left_comm, mul_assoc] using h_cleared
        exact le_of_mul_le_mul_right h_mul hdpos
      have hgoal : (21 / 5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d ≤
          (7 / 8 : ℝ) * ((5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) := by
        have h_eq : (7 / 8 : ℝ) * ((5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) -
            ((21 / 5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) =
            ((7 : ℝ) * (pgLD ρ ^ 2 * d * (d + 2) * (d + 5)) - 10 * (pgKappa ^ 2 / d)) / 40 := by
          ring
        have h_nonneg : 0 ≤ (7 : ℝ) * (pgLD ρ ^ 2 * d * (d + 2) * (d + 5)) - 10 * (pgKappa ^ 2 / d) := by linarith
        have h_diff : 0 ≤ (7 / 8 : ℝ) * ((5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) -
            ((21 / 5 : ℝ) * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) := by
          rw [h_eq]
          have h40 : 0 ≤ (40 : ℝ) := by norm_num
          exact div_nonneg h_nonneg h40
        linarith
      exact hgoal
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right hnum (by positivity)
  exact And.intro hG2q_nonneg h_ineq

/-- B3a, `pgFt_sq_le` with `21/20`. -/
theorem pgFt_sq_leN (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSqN) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (g : EuclideanSpace ℝ (Fin d)) :
    0 ≤ pgFt K ρ x g ∧ pgFt K ρ x g ^ 2 ≤ 21 / 20 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hEta' := hEta (d : ℝ) ρ hd_real hρ
  rcases hEta' with ⟨hη_nonneg, hη_sq⟩
  have hFt_bounds := pgFt_bounds hLB hD4 d ρ hd hρ K hK x hx g
  rcases hFt_bounds with ⟨hle, hle2, hF_nonneg, hF_le⟩
  have h0 : 0 ≤ pgFt K ρ x g := by
    linarith
  have hρ_nonneg : 0 ≤ ρ := by linarith
  have h_norm_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
  have hL_nonneg : 0 ≤ pgLD ρ := by
    unfold pgLD pgKappa pgPB
    positivity
  have hL_sq_nonneg : 0 ≤ pgLD ρ ^ 2 := by positivity
  have h_norm_sq_nonneg : 0 ≤ (1 + ‖g‖) ^ 2 := by positivity
  have h_factor_nonneg : 0 ≤ (21 / 20 : ℝ) * pgLD ρ ^ 2 := by positivity
  have h_sq_bound : pgFt K ρ x g ^ 2 ≤ 21 / 20 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
    have h_mul : pgFt K ρ x g ≤ (1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖) := by
      have h_eta1_nonneg : 0 ≤ 1 + pgEta (d : ℝ) ρ := by linarith
      have h_norm1_nonneg : 0 ≤ 1 + ‖g‖ := by linarith
      nlinarith
    have h_sq_mul : pgFt K ρ x g ^ 2 ≤ ((1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 := by
      nlinarith
    have h_norm_sq : (1 + ‖g‖) ^ 2 ≤ 2 * (1 + ‖g‖ ^ 2) := by
      have h := sq_nonneg (1 - ‖g‖)
      nlinarith
    calc
      pgFt K ρ x g ^ 2 ≤ ((1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 := h_sq_mul
      _ = (1 + pgEta (d : ℝ) ρ) ^ 2 * pgLD ρ ^ 2 * (1 + ‖g‖) ^ 2 := by ring
      _ ≤ (21 / 20) * pgLD ρ ^ 2 * (1 + ‖g‖) ^ 2 := by
        have h1 : (1 + pgEta (d : ℝ) ρ) ^ 2 * pgLD ρ ^ 2 ≤ (21 / 20) * pgLD ρ ^ 2 :=
          mul_le_mul_of_nonneg_right hη_sq hL_sq_nonneg
        exact mul_le_mul_of_nonneg_right h1 h_norm_sq_nonneg
      _ ≤ (21 / 20) * pgLD ρ ^ 2 * (2 * (1 + ‖g‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h_norm_sq h_factor_nonneg
      _ = 21 / 20 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by ring
  exact And.intro h0 h_sq_bound

/-- B3b, the second moment `E |V|² ≤ G₁²` with `21/20`. -/
theorem pgV_second_momentN (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSqN)
    (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    ∫ g, ‖pgV K ρ x g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ pgG2q d ρ := by
  set L := pgLD ρ with hL
  set t := pgTmin d ρ with ht
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : ∀ n : ℕ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ n) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun n => (IsGaussian.memLp_id _ (n : ENNReal) (by simp)).integrable_norm_pow'
  have hI1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have he : (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) = fun g => ‖g‖ ^ 2 + ‖g‖ ^ 4 := by
      funext g; ring
    rw [he]; exact (hp 2).add (hp 4)
  have hI2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have he : (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)) =
        fun g => ‖g‖ ^ 6 - ‖g‖ ^ 4 + ((d : ℝ) - 2) * ‖g‖ ^ 2 + (d : ℝ) := by
      funext g; ring
    rw [he]; exact (((hp 6).sub (hp 4)).add ((hp 2).const_mul _)).add (integrable_const _)
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun g =>
    21 / 10 * L ^ 2 / t ^ 2 * (‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) +
      21 / 5 * L ^ 2 / t ^ 2 * ((‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)) + 2 * (pgKappa / d) ^ 2 * d / t ^ 2
    with hh
  have hhi : Integrable h (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ((hI1.const_mul _).add (hI2.const_mul _)).add (integrable_const _)
  have hbd : ∀ g, ‖pgV K ρ x g‖ ^ 2 ≤ h g := by
    intro g
    obtain ⟨-, hF⟩ := pgFt_sq_leN hLB hD4 hEta d ρ hd hρ K hK x hx g
    have hV := pgV_norm_sq_le d ρ hd hρ K x hx g
    have hS := hFrob d g
    have hS0 : 0 ≤ ∑ i, ∑ j, gstat g i j ^ 2 := by positivity
    rw [hS] at hV hS0
    set s := ‖g‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hg4 : ‖g‖ ^ 4 = s ^ 2 := by rw [hs]; ring
    rw [hg4] at hV hS0
    have hh' : h g = 21 / 10 * L ^ 2 / t ^ 2 * (s * (1 + s)) +
        21 / 5 * L ^ 2 / t ^ 2 * ((s ^ 2 - 2 * s + (d : ℝ)) * (1 + s)) + 2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
      rw [hh]; simp only; rw [hg4]
    rw [hh']
    set F2 := pgFt K ρ x g ^ 2
    set u := (t ^ 2)⁻¹ with hu
    have hu0 : 0 ≤ u := by positivity
    have hF' : F2 ≤ 21 / 10 * L ^ 2 * (1 + s) := by linarith
    have e1 : F2 * (s * u) ≤ 21 / 10 * L ^ 2 * (1 + s) * (s * u) :=
      mul_le_mul_of_nonneg_right hF' (mul_nonneg hs0 hu0)
    have e2 : F2 * ((s ^ 2 - 2 * s + d) * u) ≤ 21 / 10 * L ^ 2 * (1 + s) * ((s ^ 2 - 2 * s + d) * u) :=
      mul_le_mul_of_nonneg_right hF' (mul_nonneg hS0 hu0)
    have hV' : ‖pgV K ρ x g‖ ^ 2 ≤ F2 * (s * u) + 2 * (F2 * ((s ^ 2 - 2 * s + d) * u)) +
        2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
      refine hV.trans (le_of_eq ?_); rw [hu]; ring
    have hR : 21 / 10 * L ^ 2 / t ^ 2 * (s * (1 + s)) + 21 / 5 * L ^ 2 / t ^ 2 * ((s ^ 2 - 2 * s + (d : ℝ)) * (1 + s)) =
        21 / 10 * L ^ 2 * (1 + s) * (s * u) + 2 * (21 / 10 * L ^ 2 * (1 + s) * ((s ^ 2 - 2 * s + d) * u)) := by
      rw [hu]; ring
    linarith
  have hmom := (hMom d)
  calc ∫ g, ‖pgV K ρ x g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ ∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (pgV_integrable hPT hLB hD4 pgEtaSq d ρ hd hρ K hK x hx).2 hhi hbd
    _ = 21 / 10 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 3)) + 21 / 5 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 1) * (d + 5)) +
          2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
        have hA : Integrable (fun g : EuclideanSpace ℝ (Fin d) => 21 / 10 * L ^ 2 / t ^ 2 * (‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) +
            21 / 5 * L ^ 2 / t ^ 2 * ((‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)))
            (stdGaussian (EuclideanSpace ℝ (Fin d))) := (hI1.const_mul _).add (hI2.const_mul _)
        simp only [hh]
        rw [integral_add hA (integrable_const _), integral_add (hI1.const_mul (21 / 10 * L ^ 2 / t ^ 2))
          (hI2.const_mul (21 / 5 * L ^ 2 / t ^ 2)), integral_const_mul, integral_const_mul, hmom.1, hmom.2]
        simp
    _ ≤ pgG2q d ρ := by
        unfold pgG2q
        rw [← hL, ← ht]
        have hdd : 2 * (pgKappa / d) ^ 2 * d = 2 * pgKappa ^ 2 / d := by field_simp
        have hpoly : 21 / 10 * ((d : ℝ) * (d + 3)) + 21 / 5 * ((d : ℝ) * (d + 1) * (d + 5)) ≤ 21 / 5 * d * (d + 2) * (d + 5) := by
          nlinarith
        have hL2 : 0 ≤ L ^ 2 / t ^ 2 := by positivity
        have e : 21 / 10 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 3)) + 21 / 5 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 1) * (d + 5)) +
            2 * (pgKappa / d) ^ 2 * d / t ^ 2 =
            L ^ 2 / t ^ 2 * (21 / 10 * ((d : ℝ) * (d + 3)) + 21 / 5 * ((d : ℝ) * (d + 1) * (d + 5))) +
              2 * pgKappa ^ 2 / d / t ^ 2 := by rw [← hdd]; ring
        have e' : (21 / 5 * L ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) / t ^ 2 =
            L ^ 2 / t ^ 2 * (21 / 5 * d * (d + 2) * (d + 5)) + 2 * pgKappa ^ 2 / d / t ^ 2 := by ring
        rw [e, e']
        have := mul_le_mul_of_nonneg_left hpoly hL2
        linarith


/-- C1a, the arithmetic of the row on real numbers (`θ = 10⁻⁶`): the halves `Δ²/(2 s N) = s G²/2 ≤ e_h/8`,
`G₁² ≤ (7/8) G²`, `β Δ ≤ e_h/4`, `e_P Δ/s = 10⁻⁶ e_h` and the last term below `10⁻⁶ e_h` from `e_h ≤ Δ G`. -/
theorem row_abstract (Δ G2 G1 N e β s eP : ℝ) (hΔ : 0 < Δ) (hG2 : 0 < G2)
    (hN : 1 ≤ N) (he : 0 < e) (hG1 : 0 ≤ G1) (hG1G2 : G1 ≤ 7 / 8 * G2)
    (hs : s = Δ / (Real.sqrt G2 * Real.sqrt N))
    (hstep : Δ ^ 2 / (2 * s * N) + s * G2 / 2 ≤ e / 4) (hβ : β * Δ ≤ e / 4)
    (heP : eP = e / (10 ^ 6 * Real.sqrt G2 * Real.sqrt N)) (heΔ : e ≤ Δ * Real.sqrt G2) :
    Δ ^ 2 / (2 * s * N) + (1 + 1 / 10 ^ 6) * s * G1 / 2 + β * Δ + eP * Δ / s +
        eP ^ 2 * (1 + 1 / (1 / 10 ^ 6)) / (2 * s) ≤ e / 2 := by
  set g := Real.sqrt G2 with hg_def
  set n := Real.sqrt N with hn_def
  have hg_pos : 0 < g := Real.sqrt_pos.mpr hG2
  have hn_pos : 0 < n := Real.sqrt_pos.mpr (by linarith : 0 < N)
  have hn_one_le : 1 ≤ n := by
    rw [hn_def]
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt (by simpa using hN)
  have hg_sq : g ^ 2 = G2 := Real.sq_sqrt (by linarith : 0 ≤ G2)
  have hn_sq : n ^ 2 = N := Real.sq_sqrt (by linarith : 0 ≤ N)
  rw [hs, heP]
  have hg_ne : g ≠ 0 := by linarith
  have hn_ne : n ≠ 0 := by linarith
  have hΔ_ne : Δ ≠ 0 := by linarith
  have h10p6_pos : 0 < (10 : ℝ) ^ 6 := by norm_num
  have h10p6_ne : (10 : ℝ) ^ 6 ≠ 0 := by norm_num
  -- Key identity: Δ²/(2*(Δ/(g*n))*N) = (Δ/(g*n))*G2/2
  have h_id : Δ ^ 2 / (2 * (Δ / (g * n)) * N) = (Δ / (g * n)) * G2 / 2 := by
    field_simp [hg_ne, hn_ne, hΔ_ne]
    ring_nf
    rw [hg_sq, hn_sq]
    ring_nf
  -- From hstep (after rewriting s), we have: Δ²/(2sN) + sG2/2 ≤ e/4
  -- Using h_id, this means each term ≤ e/8
  have hT1 : Δ ^ 2 / (2 * (Δ / (g * n)) * N) ≤ e / 8 := by
    rw [h_id]
    have hsum := hstep
    rw [hs] at hsum
    rw [h_id] at hsum
    linarith
  -- Term 2: (1+1/10⁶)*(Δ/(g*n))*G1/2 ≤ (1+1/10⁶)*(7/64)*e
  have hT2 : (1 + 1 / (10 : ℝ) ^ 6) * ((Δ / (g * n)) * G1) / 2 ≤ (1 + 1 / (10 : ℝ) ^ 6) * (7 / 64) * e := by
    have hpos_s : 0 ≤ Δ / (g * n) := div_nonneg (by linarith) (by positivity)
    have h_coeff_pos : 0 ≤ 1 + 1 / (10 : ℝ) ^ 6 := by positivity
    have h_seven_eighths_pos : (0 : ℝ) ≤ 7 / 8 := by norm_num
    have h_inner : (Δ / (g * n)) * G1 / 2 ≤ (Δ / (g * n)) * (G2 / 2) * (7 / 8) := by
      have h_mul : (Δ / (g * n)) * G1 ≤ (Δ / (g * n)) * (7 / 8 * G2) := by
        apply mul_le_mul_of_nonneg_left hG1G2 hpos_s
      calc
        (Δ / (g * n)) * G1 / 2 ≤ ((Δ / (g * n)) * (7 / 8 * G2)) / 2 :=
          (div_le_div_of_nonneg_right h_mul (by norm_num : (0 : ℝ) ≤ 2))
        _ = (Δ / (g * n)) * (G2 / 2) * (7 / 8) := by ring
    calc
      (1 + 1 / (10 : ℝ) ^ 6) * ((Δ / (g * n)) * G1) / 2 =
          (1 + 1 / (10 : ℝ) ^ 6) * ((Δ / (g * n)) * G1 / 2) := by ring
      _ ≤ (1 + 1 / (10 : ℝ) ^ 6) * ((Δ / (g * n)) * (G2 / 2) * (7 / 8)) := by
        apply mul_le_mul_of_nonneg_left h_inner h_coeff_pos
      _ = (1 + 1 / (10 : ℝ) ^ 6) * (7 / 8) * ((Δ / (g * n)) * G2 / 2) := by ring
      _ ≤ (1 + 1 / (10 : ℝ) ^ 6) * (7 / 8) * (e / 8) := by
        apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg h_coeff_pos h_seven_eighths_pos)
        -- need: (Δ/(g*n))*G2/2 ≤ e/8
        -- which is exactly hT1 after rewriting
        rw [← h_id]
        exact hT1
      _ = (1 + 1 / (10 : ℝ) ^ 6) * (7 / 64) * e := by ring
  -- Term 3: β*Δ ≤ e/4
  have hT3 : β * Δ ≤ e / 4 := hβ
  -- Term 4: (e/(10⁶*g*n))*Δ/(Δ/(g*n)) = e/10⁶
  have hT4_eq : (e / ((10 : ℝ) ^ 6 * g * n)) * Δ / (Δ / (g * n)) = e / (10 : ℝ) ^ 6 := by
    field_simp [hg_ne, hn_ne, hΔ_ne]
  have hT4 : (e / ((10 : ℝ) ^ 6 * g * n)) * Δ / (Δ / (g * n)) ≤ e / (10 : ℝ) ^ 6 := by
    rw [hT4_eq]
  -- Term 5: (e/(10⁶*g*n))²*(1+1/(1/10⁶))/(2*(Δ/(g*n))) ≤ e*(1+10⁶)/(2*10¹²)
  have hT5 : (e / ((10 : ℝ) ^ 6 * g * n)) ^ 2 * (1 + 1 / ((1 : ℝ) / (10 : ℝ) ^ 6)) / (2 * (Δ / (g * n))) ≤
      e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) := by
    -- First simplify the algebraic expression
    have h_expr : (e / ((10 : ℝ) ^ 6 * g * n)) ^ 2 * (1 + 1 / ((1 : ℝ) / (10 : ℝ) ^ 6)) / (2 * (Δ / (g * n))) =
        e ^ 2 * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12 * g * n * Δ) := by
      field_simp [hg_ne, hn_ne, hΔ_ne]
    rw [h_expr]
    -- Now we need to show: e²*(1+10⁶)/(2*10¹²*g*n*Δ) ≤ e*(1+10⁶)/(2*10¹²)
    -- This is equivalent to e/(g*n*Δ) ≤ 1, which follows from e ≤ Δ*g and n ≥ 1
    have h_ratio : e / (g * n * Δ) ≤ 1 := by
      have h_num : e ≤ g * n * Δ := by
        calc
          e ≤ Δ * g := heΔ
          _ = g * Δ := by ring
          _ ≤ g * Δ * n := by
            have : 1 * (g * Δ) ≤ n * (g * Δ) :=
              mul_le_mul_of_nonneg_right hn_one_le (by positivity)
            simpa [one_mul, mul_comm] using this
          _ = g * n * Δ := by ring
      exact (div_le_one (by positivity)).mpr h_num
    have h_coeff_pos : 0 ≤ e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) := by
      positivity
    calc
      e ^ 2 * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12 * g * n * Δ) =
          (e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12)) * (e / (g * n * Δ)) := by
        field_simp [hg_ne, hn_ne, hΔ_ne]
      _ ≤ (e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12)) * 1 := by
        apply mul_le_mul_of_nonneg_left h_ratio h_coeff_pos
      _ = e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) := by ring
  -- Now sum all five terms
  have h_sum : e / 8 + ((1 + 1 / (10 : ℝ) ^ 6) * (7 / 64) * e) + e / 4 + e / (10 : ℝ) ^ 6 +
      e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) ≤ e / 2 := by
    field_simp [he.ne.symm]
    nlinarith
  -- Combine all bounds
  have h_total : Δ ^ 2 / (2 * (Δ / (g * n)) * N) + (1 + 1 / (10 : ℝ) ^ 6) * (Δ / (g * n)) * G1 / 2 + β * Δ +
        (e / ((10 : ℝ) ^ 6 * g * n)) * Δ / (Δ / (g * n)) +
        (e / ((10 : ℝ) ^ 6 * g * n)) ^ 2 * (1 + 1 / ((1 : ℝ) / (10 : ℝ) ^ 6)) / (2 * (Δ / (g * n))) ≤
      e / 8 + ((1 + 1 / (10 : ℝ) ^ 6) * (7 / 64) * e) + e / 4 + e / (10 : ℝ) ^ 6 +
        e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) := by
    have h1 := add_le_add hT1 hT2
    have h2 := add_le_add h1 hT3
    have h3 := add_le_add h2 hT4
    have h4 := add_le_add h3 hT5
    simpa [mul_assoc, add_assoc] using h4
  calc
    Δ ^ 2 / (2 * (Δ / (g * n)) * N) + (1 + 1 / (10 : ℝ) ^ 6) * (Δ / (g * n)) * G1 / 2 + β * Δ +
        (e / ((10 : ℝ) ^ 6 * g * n)) * Δ / (Δ / (g * n)) +
        (e / ((10 : ℝ) ^ 6 * g * n)) ^ 2 * (1 + 1 / ((1 : ℝ) / (10 : ℝ) ^ 6)) / (2 * (Δ / (g * n)))
    ≤ e / 8 + ((1 + 1 / (10 : ℝ) ^ 6) * (7 / 64) * e) + e / 4 + e / (10 : ℝ) ^ 6 +
        e * (1 + (10 : ℝ) ^ 6) / (2 * (10 : ℝ) ^ 12) := h_total
    _ ≤ e / 2 := h_sum

/-- C1b: `e_h ≤ Δ G` (crudely, `e_h ≤ 1/4 ≤ Δ` and `G ≥ 1`). -/
theorem pgEh_le_delta_sqrtG2 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgEh d ρ ≤ pgDelta d ρ * Real.sqrt (pgG2 d ρ) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by linarith : 1 ≤ 1 + ρ)
  have hlog_ge_log2 : Real.log 2 ≤ Real.log (1 + ρ) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- λ² ≥ 1
  have hlam_sq_ge_one : 1 ≤ pgLam ρ ^ 2 := by
    unfold pgLam
    have hineq : 1 ≤ 2 * Real.log (1 + ρ) := by nlinarith
    have hsq : (Real.sqrt (2 * Real.log (1 + ρ))) ^ 2 = 2 * Real.log (1 + ρ) :=
      Real.sq_sqrt (by nlinarith)
    nlinarith
  -- L_D ≥ 0.15
  have hLD_ge_015 : 0.15 ≤ pgLD ρ := by
    unfold pgLD pgKappa pgPB
    have hcoeff : 0.15 ≤ (1 : ℝ)/8 * (1254/1000 : ℝ) := by norm_num
    nlinarith
  -- denominator of pgEh ≥ 1
  have hden_ge_one : 1 ≤ 922 * ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) * (pgLD ρ) := by
    have hd_sq_ge_one : 1 ≤ (d : ℝ) ^ 2 := by nlinarith
    have h_lam_sq_ge_one : 1 ≤ pgLam ρ ^ 2 := hlam_sq_ge_one
    have h_LD_ge_015 : 0.15 ≤ pgLD ρ := hLD_ge_015
    have h_nonneg_d_sq : 0 ≤ (d : ℝ) ^ 2 := by nlinarith
    have h_nonneg_lam_sq : 0 ≤ pgLam ρ ^ 2 := by
      have h_nonneg_lam : 0 ≤ pgLam ρ := Real.sqrt_nonneg _
      nlinarith
    have h_nonneg_LD : 0 ≤ pgLD ρ := by linarith
    have h922pos : 0 ≤ (922 : ℝ) := by norm_num
    have h_base : (1 : ℝ) * (1 : ℝ) * (0.15 : ℝ) ≤ ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) * (pgLD ρ) := by
      have h12 : (1 : ℝ) * (1 : ℝ) ≤ ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) := by
        nlinarith
      have h_nonneg_12 : 0 ≤ (1 : ℝ) * (1 : ℝ) := by norm_num
      have h_nonneg_d2_lam2 : 0 ≤ ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) := by nlinarith
      exact mul_le_mul h12 h_LD_ge_015 (by linarith) h_nonneg_d2_lam2
    calc
      1 ≤ 922 * (0.15 : ℝ) := by norm_num
      _ = 922 * ((1 : ℝ) * (1 : ℝ) * (0.15 : ℝ)) := by ring
      _ ≤ 922 * (((d : ℝ) ^ 2) * (pgLam ρ ^ 2) * (pgLD ρ)) := by
        exact mul_le_mul_of_nonneg_left h_base h922pos
      _ = 922 * ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) * (pgLD ρ) := by ring
  -- pgEh ≤ 1/4
  have hEh_le_quarter : pgEh d ρ ≤ 1/4 := by
    unfold pgEh pgKappa
    have hsq : ((1 : ℝ)/8) ^ 2 = (1 : ℝ)/64 := by norm_num
    rw [hsq]
    calc
      (1 : ℝ)/64 / (922 * ((d : ℝ) ^ 2) * (pgLam ρ ^ 2) * (pgLD ρ)) ≤ (1 : ℝ)/64 :=
        div_le_self (by norm_num) hden_ge_one
      _ ≤ 1/4 := by norm_num
  -- pgDelta ≥ 1/4
  have hDelta_ge_quarter : 1/4 ≤ pgDelta d ρ := by
    unfold pgDelta pgKappa pgPB
    have hsqrt : 2 ≤ Real.sqrt (4 + ((1254 : ℝ)/1000) ^ 2 * (d : ℝ)) := by
      have hinner : (4 : ℝ) ≤ 4 + ((1254 : ℝ)/1000) ^ 2 * (d : ℝ) := by nlinarith
      calc
        2 = Real.sqrt (4 : ℝ) := by norm_num
        _ ≤ Real.sqrt (4 + ((1254 : ℝ)/1000) ^ 2 * (d : ℝ)) := Real.sqrt_le_sqrt hinner
    nlinarith
  -- pgG2 ≥ 1
  have hG2_ge_one : 1 ≤ pgG2 d ρ := by
    unfold pgG2 pgTmin pgLD pgKappa pgLam
    set s := Real.sqrt (2 * Real.log (1 + ρ)) with hs_def
    have hs_pos : 0 < s := by
      rw [hs_def]
      have hlogpos' : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
      have hpos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
      exact Real.sqrt_pos.mpr hpos
    have hs_sq : s ^ 2 = 2 * Real.log (1 + ρ) := Real.sq_sqrt (by nlinarith)
    have hs_sq_ge_one : 1 ≤ s ^ 2 := by nlinarith
    have hpos_denom : 0 < (1 / (9 * (d : ℝ) * s)) ^ 2 := by
      have hpos_inner : 0 < 1 / (9 * (d : ℝ) * s) := by positivity
      positivity
    have h_first_nonneg : 0 ≤ 5 * (((1 : ℝ)/8) * (1254/1000 : ℝ) * ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := by
      positivity
    have hB_div_C_ge_one : 1 ≤ (2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) / ((1 / (9 * (d : ℝ) * s)) ^ 2) := by
      have h_eq : (2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) / ((1 / (9 * (d : ℝ) * s)) ^ 2) =
          (2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) * (9 * (d : ℝ) * s) ^ 2 := by
        field_simp [hs_pos.ne.symm, hdpos.ne.symm]
      rw [h_eq]
      have hcalc : (2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) * (9 * (d : ℝ) * s) ^ 2 = (81/32 : ℝ) * (d : ℝ) * (s ^ 2) := by
        field_simp [hdpos.ne.symm]
        ring
      rw [hcalc]
      have hcoeff_ge_one : (1 : ℝ) ≤ (81/32 : ℝ) := by norm_num
      nlinarith
    have h_div_le : (2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) / ((1 / (9 * (d : ℝ) * s)) ^ 2) ≤
        (5 * (((1 : ℝ)/8) * (1254/1000 : ℝ) * ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) +
         2 * ((1 : ℝ)/8) ^ 2 / (d : ℝ)) / ((1 / (9 * (d : ℝ) * s)) ^ 2) := by
      apply div_le_div_of_nonneg_right ?_ (by
        have hnonneg_sq : 0 ≤ (1 / (9 * (d : ℝ) * s)) ^ 2 := by positivity
        exact hnonneg_sq)
      have hnonneg : 0 ≤ 5 * (((1 : ℝ)/8) * (1254/1000 : ℝ) * ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := h_first_nonneg
      linarith
    exact hB_div_C_ge_one.trans h_div_le
  have hsqrtG2_ge_one : 1 ≤ Real.sqrt (pgG2 d ρ) := by
    rw [Real.one_le_sqrt]
    exact hG2_ge_one
  have hDelta_nonneg : 0 ≤ pgDelta d ρ := by
    unfold pgDelta pgKappa
    positivity
  have hDelta_le_mul : pgDelta d ρ ≤ pgDelta d ρ * Real.sqrt (pgG2 d ρ) := by
    nlinarith
  calc
    pgEh d ρ ≤ 1/4 := hEh_le_quarter
    _ ≤ pgDelta d ρ := hDelta_ge_quarter
    _ ≤ pgDelta d ρ * Real.sqrt (pgG2 d ρ) := hDelta_le_mul

/-- C1, the row of the round. -/
theorem pgRowN (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgDelta d ρ ^ 2 / (2 * pgStepSize d ρ * pgNs d ρ) + (1 + pgTheta) * pgStepSize d ρ * pgG2q d ρ / 2 +
        pgBeta d ρ * pgDelta d ρ + pgEP d ρ * pgDelta d ρ / pgStepSize d ρ +
        pgEP d ρ ^ 2 * (1 + 1 / pgTheta) / (2 * pgStepSize d ρ) ≤
      pgEh d ρ / 2 := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hρpos : 0 < ρ := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hlam : 0 < pgLam ρ := by
    unfold pgLam
    exact Real.sqrt_pos.mpr (by have := Real.log_pos (by linarith : 1 < 1 + ρ); linarith)
  have hΔ : 0 < pgDelta d ρ := by unfold pgDelta pgKappa; positivity
  have hG2 : 0 < pgG2 d ρ := by unfold pgG2 pgLD pgTmin pgKappa pgPB; positivity
  have hN : (1 : ℝ) ≤ pgNs d ρ := by exact_mod_cast pgNs_pos d ρ hd hρ
  obtain ⟨hG1, hG1G2⟩ := pgG2q_le d ρ hdr hρ
  have hβ : pgBeta d ρ * pgDelta d ρ ≤ pgEh d ρ / 4 := pgBiasDescent d ρ hdr hρ
  unfold pgTheta
  exact row_abstract (pgDelta d ρ) (pgG2 d ρ) (pgG2q d ρ) (pgNs d ρ) (pgEh d ρ) (pgBeta d ρ) (pgStepSize d ρ)
    (pgEP d ρ) hΔ hG2 hN (pgEh_pos d ρ hd hρ) hG1 hG1G2 rfl (pgStep_arith pgStep d ρ hd hρ) hβ rfl
    (pgEh_le_delta_sqrtG2 d ρ hd hρ)

end AdversarialBco.Conj1Arith
