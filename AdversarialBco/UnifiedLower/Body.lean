/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.StopTop
public import AdversarialBco.Poly.PgProcProof
public import AdversarialBco.StatementUnifiedLower

@[expose] public section

/-!
# The pieces of clauses (a) and (b) of `TheoremLowerU` on every body of the class

The strategy of Theorem lowerbody (the tip `x°` and the clamped noise `z` fixed, `stratOf`, Conj1Lower/Top.lean) is
more than `StratsLip`: on a body inside `B(0, R0)` its losses take values in `[1/8, 7/8]` (the offset `b = 1/4`, the
dent between `0` and `L (R0 + 1/2) + g ≤ 1/2`, the clamped noise in `[-1/8, 1/8]`) and are `L`-Lipschitz on all of
`ℝ^d` with `L = σ/R0` (Lemma LEGAL, `dentS_lipschitz`, is global). The class `StratsMid K n L` records this, and:

* `stratOf_mid`: the strategy of a tip and a clamped noise sequence is in `StratsMid K n L`;
* `pullStrat_mem_mid`: the pull-back by an affine map `T` keeps the class, the Lipschitz constant multiplied by that of
  `T` (Lemma AFF, the paper's affine invariance, with the global constant);
* `exists_position` (Lemma POS, the paper's position lemma): every body of `BodyU` has an affine image between
  `B(0, 1/2)` and `B(0, 67 d (ln(2d + 2))^{1/2})`, from Theorem PG (`Poly.pgThm`) at `δ = 1/2`; the Lipschitz constant
  of such a position is at most `R''/r0` (`dist_le_of_ball_image`), so the pulled-back losses are
  `1/(8 r0)`-Lipschitz.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

namespace AdversarialBco.UnifiedLower.Body

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Top AdversarialBco.Lower.Stop

variable {d : ℕ}

/-! ## The class of the strategy of the tip -/

/-- The strategies of `Strats K n` whose loss, for `t < n` and every history, reads the past points only, takes values
in `[1/8, 7/8]` on `K` and is `L`-Lipschitz on all of `E d`. -/
def StratsMid (K : Set (E d)) (n : ℕ) (L : ℝ) : Set (Strategy d) :=
  {σ | σ ∈ Strats K n ∧ ∀ t < n, ∀ (x : Fin t → E d) (o o' : Fin t → ℝ), σ t x o = σ t x o' ∧
    (∀ y ∈ K, 1 / 8 ≤ σ t x o y ∧ σ t x o y ≤ 7 / 8) ∧ ∀ y z : E d, |σ t x o y - σ t x o z| ≤ L * dist y z}

/-- The class `StratsMid` at a constant at most `1/(4 r0)` is inside `StratsLowU K n r0`. -/
theorem stratsMid_lowU {K : Set (E d)} {n : ℕ} {L r0 : ℝ} (hr0 : 0 < r0) (hL : L ≤ 1 / (4 * r0))
    {σ : Strategy d} (hσ : σ ∈ StratsMid K n L) : σ ∈ StratsLowU K n r0 := by
  refine ⟨hσ.1, fun t ht x o o' => ⟨(hσ.2 t ht x o o').1, (hσ.2 t ht x o o').2.1, fun y z => ?_⟩⟩
  have h := (hσ.2 t ht x o o').2.2 y z
  have h4 : 0 < 4 * r0 := by positivity
  calc |σ t x o y - σ t x o z| ≤ L * dist y z := h
    _ ≤ 1 / (4 * r0) * dist y z := mul_le_mul_of_nonneg_right hL dist_nonneg
    _ = dist y z / (4 * r0) := by ring

section Tip

variable {R0 : ℝ}

/-- Lemma LEGAL-K with the range and the global constant: on a convex body `K` inside `B(0, R0)`, the strategy of a
tip and a noise sequence with `|σ z_i| ≤ 1/8` is in `StratsMid K n L`. -/
theorem stratOf_mid (I : Inputs) {P : SParams} (hP : Good P d R0) {K : Set (E d)} (hK : Convex ℝ K)
    (hKR : K ⊆ Metric.closedBall (0 : E d) R0) (n : ℕ) (xo : E d) (z : ℕ → ℝ) (hz : ∀ i, |P.sc * z i| ≤ 1 / 8) :
    stratOf (prior d (1 / 2)) (ruleS d P) P.sc xo z ∈ StratsMid K n P.L := by
  refine ⟨(stratOf_mem I hP hK hKR n xo z hz).1, fun t _ x o o' => ⟨rfl, fun y hy => ?_, fun y y' => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := sig_post_bounds I hP t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x) (hKR hy) xo
    obtain ⟨h3, h4⟩ := abs_le.1 (hz t)
    have := hP.rng
    have := hP.b_eq
    simp only [stratOf]
    constructor <;> linarith
  · have hS := (post_cov I hP P.sc t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x)).1
    simp only [stratOf, ruleS_sig, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub]
    rw [dist_eq_norm]
    split_ifs
    · exact dentS_lipschitz hP hS y y' xo
    · simp only [sub_self, abs_zero]
      exact mul_nonneg hP.L_pos.le (norm_nonneg _)

end Tip

/-! ## The affine pull-back with the global constant -/

/-- Lemma AFF with the class `StratsMid`: the pull-back by `T` of a strategy of `StratsMid (T '' K) n L` is in
`StratsMid K n (L M)` when `T` is `M`-Lipschitz. -/
theorem pullStrat_mem_mid (T : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {n : ℕ} {σ : Strategy d} {L M : ℝ}
    (hL : 0 ≤ L) (hT : ∀ y z, dist (T y) (T z) ≤ M * dist y z) (hσ : σ ∈ StratsMid (T '' K) n L) :
    pullStrat T σ ∈ StratsMid K n (L * M) := by
  refine ⟨pullStrat_mem_strats T hσ.1, fun t ht x o o' => ⟨?_, fun y hy => ?_, fun y z => ?_⟩⟩
  · have h := (hσ.2 t ht (fun i => T (x i)) o o').1
    show (fun z => σ t (fun i => T (x i)) o (T z)) = fun z => σ t (fun i => T (x i)) o' (T z)
    rw [h]
  · exact (hσ.2 t ht (fun i => T (x i)) o o).2.1 (T y) ⟨y, hy, rfl⟩
  · have h := (hσ.2 t ht (fun i => T (x i)) o o).2.2 (T y) (T z)
    calc |pullStrat T σ t x o y - pullStrat T σ t x o z| ≤ L * dist (T y) (T z) := h
      _ ≤ L * (M * dist y z) := mul_le_mul_of_nonneg_left (hT y z) hL
      _ = L * M * dist y z := by ring

/-- An affine map that sends `B̄(a, r0)` into `B̄(0, R)` is `R/r0`-Lipschitz. -/
theorem dist_le_of_ball_image (T : E d ≃ᵃ[ℝ] E d) {a : E d} {r0 R : ℝ} (hr0 : 0 < r0)
    (hT : T '' closedBall a r0 ⊆ closedBall 0 R) (y z : E d) : dist (T y) (T z) ≤ R / r0 * dist y z := by
  set L := T.toAffineMap.linear with hL
  have hlin : ∀ u v : E d, T u - T v = L (u - v) := fun u v => by
    simpa [hL, vsub_eq_sub] using (T.toAffineMap.linearMap_vsub u v).symm
  have hnorm : ∀ v : E d, ‖v‖ = r0 → ‖L v‖ ≤ R := by
    intro v hv
    have h1 : T (a + v) ∈ closedBall (0 : E d) R := hT ⟨a + v, by simp [dist_eq_norm, hv], rfl⟩
    have h2 : T (a - v) ∈ closedBall (0 : E d) R := hT ⟨a - v, by simp [hv], rfl⟩
    rw [mem_closedBall_zero_iff] at h1 h2
    have h3 : T (a + v) - T (a - v) = (2 : ℝ) • L v := by
      rw [hlin, show a + v - (a - v) = (2 : ℝ) • v by module, map_smul]
    have h4 : ‖(2 : ℝ) • L v‖ ≤ 2 * R := by
      rw [← h3]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_smul, Real.norm_two] at h4
    linarith
  rw [dist_eq_norm, dist_eq_norm, hlin]
  by_cases hu : y - z = 0
  · simp [hu]
  · have hpos : 0 < ‖y - z‖ := norm_pos_iff.2 hu
    set v := (r0 / ‖y - z‖) • (y - z) with hv
    have hvn : ‖v‖ = r0 := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr0 hpos), div_mul_cancel₀ _ hpos.ne']
    have hyz : y - z = (‖y - z‖ / r0) • v := by
      rw [hv, smul_smul, div_mul_div_cancel₀ hr0.ne', div_self hpos.ne', one_smul]
    rw [hyz, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hr0)]
    calc ‖y - z‖ / r0 * ‖L v‖ ≤ ‖y - z‖ / r0 * R := mul_le_mul_of_nonneg_left (hnorm v hvn) (by positivity)
      _ = R / r0 * ((‖y - z‖ / r0) * r0) := by field_simp
      _ = R / r0 * ‖(‖y - z‖ / r0) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hr0), hvn]

/-! ## Lemma POS from Theorem PG -/

theorem det_pgOp (M : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (𝕜 := ℝ) M : E d →ₗ[ℝ] E d) = M.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The radius of the position of Theorem PG, halved: `67 d (ln(2d + 2))^{1/2}`. -/
noncomputable def posR (d : ℕ) : ℝ := 67 * d * Real.sqrt (Real.log (2 * d + 2))

/-- **Lemma POS** (the paper's position lemma): every body of `BodyU` has an affine image between `B̄(0, 1/2)` and
`B̄(0, 67 d (ln(2d + 2))^{1/2})`; from Theorem PG (`Poly.pgThm`) at `δ = 1/2`, whose failure event has probability at
most `1/2 < 1`. -/
theorem exists_position (hd : 1 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) :
    ∃ T : E d ≃ᵃ[ℝ] E d, closedBall (0 : E d) (1 / 2) ⊆ T '' K ∧ T '' K ⊆ closedBall 0 (posR d) := by
  obtain ⟨hr0, hr0R, hKc, hKv, hK1, hK2⟩ := hb
  set K' : Set (E d) := (fun x => a + x) ⁻¹' K with hK'
  have hK'v : Convex ℝ K' := hKv.translate_preimage_right a
  have hK'c : IsClosed K' := hKc.isClosed.preimage (continuous_const.add continuous_id)
  have hK'1 : closedBall (0 : E d) r0 ⊆ K' := fun x hx => hK1 (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rwa [mem_closedBall, dist_zero_right] at hx)
  have hK'2 : K' ⊆ closedBall (0 : E d) R0 := fun x hx => by
    have := hK2 hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at this
    rwa [mem_closedBall, dist_zero_right]
  have hpg := Poly.pgThm d K' r0 R0 (1 / 2) hd hK'v hK'c hr0 hr0R hK'1 hK'2 (by norm_num) (by norm_num)
  obtain ⟨ω, hω⟩ : ∃ ω, Poly.PgGood d K' (134 * d * Real.sqrt (Real.log (2 * d + 2)))
      (Poly.pg d K' r0 R0 (1 / 2) ω) := by
    by_contra hne
    push Not at hne
    have huniv : {ω | ¬ Poly.PgGood d K' (134 * d * Real.sqrt (Real.log (2 * d + 2)))
        (Poly.pg d K' r0 R0 (1 / 2) ω)} = Set.univ := Set.eq_univ_of_forall hne
    rw [huniv, measure_univ] at hpg
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) := hpg
    rw [ENNReal.one_le_ofReal] at this
    norm_num at this
  obtain ⟨Q, -, hdet, hin, hout, -⟩ := hω
  set A : E d →L[ℝ] E d := Poly.pgOp Q with hA
  have hdetA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0 := by
    rw [hA, Poly.pgOp, det_pgOp]
    exact hdet
  set Ae : E d ≃ₗ[ℝ] E d := LinearMap.equivOfDetNeZero (A : E d →ₗ[ℝ] E d) hdetA with hAe
  have hAe_apply : ∀ y, Ae y = A y := fun y => rfl
  set L2 : E d ≃ₗ[ℝ] E d := (LinearEquiv.smulOfNeZero ℝ (E d) 2 two_ne_zero).trans Ae with hL2
  have hL2_apply : ∀ y, L2 y = A ((2 : ℝ) • y) := fun y => rfl
  set S : E d ≃ᵃ[ℝ] E d := L2.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (E d) (a + Poly.pgMu Q)) with hS
  have hS_apply : ∀ y, S y = a + (Poly.pgMu Q + A ((2 : ℝ) • y)) := fun y => by
    rw [hS, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, LinearEquiv.coe_toAffineEquiv, hL2_apply,
      vadd_eq_add, add_assoc]
  have himg : S.symm '' K = S ⁻¹' K := AffineEquiv.image_symm S K
  refine ⟨S.symm, ?_, ?_⟩
  · intro y hy
    rw [himg, Set.mem_preimage, hS_apply]
    have h2y : (2 : ℝ) • y ∈ closedBall (0 : E d) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_two]
      rw [mem_closedBall, dist_zero_right] at hy
      linarith
    exact hin h2y
  · intro y hy
    rw [himg, Set.mem_preimage, hS_apply] at hy
    have h2y := hout hy
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_two] at h2y
    rw [mem_closedBall, dist_zero_right, posR]
    have : (134 : ℝ) * d * Real.sqrt (Real.log (2 * d + 2)) = 2 * (67 * d * Real.sqrt (Real.log (2 * d + 2))) := by
      ring
    linarith

/-- The radius of the position is at least `1` and at most `d (120 ln d + 68)` for `d ≥ 4·10^6`. -/
theorem posR_bounds (hd : 4000000 ≤ d) : 1 ≤ posR d ∧ posR d ≤ d * kRipe d := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : 1 ≤ Real.log (2 * d + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hsq1 : 1 ≤ Real.sqrt (Real.log (2 * d + 2)) := Real.one_le_sqrt.2 hlog2
  have hsq : Real.sqrt (Real.log (2 * d + 2)) ≤ (1 + Real.log (2 * d + 2)) / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Real.log (2 * d + 2) by linarith),
      Real.sqrt_nonneg (Real.log (2 * d + 2)), sq_nonneg (Real.sqrt (Real.log (2 * d + 2)) - 1)]
  have hl3 : Real.log (2 * d + 2) ≤ Real.log 3 + Real.log d := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hl3' : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
    linarith
  have hld : 1 ≤ Real.log d := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  constructor
  · unfold posR
    have : (1 : ℝ) ≤ 67 * d := by linarith
    nlinarith
  · unfold posR kRipe
    have hdp : (0 : ℝ) ≤ d := by linarith
    have : 67 * Real.sqrt (Real.log (2 * d + 2)) ≤ 120 * Real.log d + 68 := by nlinarith
    nlinarith

/-! ## Clauses (a) and (b) -/

/-- `sigB n ≤ 1/8` for `n ≥ 2`. -/
theorem sigB_le (n : ℕ) (hn : 1 < n) : sigB n ≤ 1 / 8 := by
  have h := sigB_mul_ellB hn
  have hl : 1 ≤ ellB n := by
    unfold ellB
    rw [Real.one_le_sqrt]
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have := Real.log_two_gt_d9
    linarith
  have hs : 0 ≤ sigB n := by unfold sigB; positivity
  nlinarith

/-- The position of a body and its constants: an affine `T` with `B̄(0, 1/2) ⊆ T K ⊆ B̄(0, R'')`,
`1 ≤ R'' ≤ d kRipe d`, `T` being `R''/r0`-Lipschitz. -/
theorem position_facts {d : ℕ} (hd : 4000000 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) :
    ∃ T : E d ≃ᵃ[ℝ] E d, Convex ℝ (T '' K) ∧ closedBall (0 : E d) (1 / 2) ⊆ T '' K ∧
      T '' K ⊆ closedBall 0 (posR d) ∧ ∀ y z, dist (T y) (T z) ≤ posR d / r0 * dist y z := by
  obtain ⟨T, h1, h2⟩ := exists_position (by omega) hb
  refine ⟨T, hb.2.2.2.1.affine_image T.toAffineMap, h1, h2, dist_le_of_ball_image T (a := a) hb.1 ?_⟩
  exact (Set.image_mono hb.2.2.2.2.1).trans h2

end AdversarialBco.UnifiedLower.Body
