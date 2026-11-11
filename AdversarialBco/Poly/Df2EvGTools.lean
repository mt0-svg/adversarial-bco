/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvTools
public import AdversarialBco.Poly.Df2Layer2
public import AdversarialBco.Poly.GaussConcProof
public import AdversarialBco.Poly.PgLemmasProof
public import AdversarialBco.Poly.SrcToolsProof

@[expose] public section

/-!
# The leaves of the budget of Noise, Pi and Gauss

Self-contained facts for `Df2EvGProp`: the extension is `extOf` at `c = 2/ε`, nonnegative, of linear
growth and continuous; the surrogate of a convex function of linear growth is convex; the tail of the gauge of a
Gaussian point of small spread (lem:ons:mink, then the Lipschitz concentration at the constant `1/2`); the tails of
the noise and of the draw in one round; the facts of the parameters `df2oPar` the budget reads.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal NNReal Topology

namespace AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## The extension -/

theorem df2Pip_eq (p : Df2OPar) (Kt : Set (EuclideanSpace ℝ (Fin d))) : df2Pip p Kt = pipOf Kt p.eps := rfl

theorem df2Ext_eq (p : Df2OPar) (Kt : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    df2Ext p Kt g = extOf Kt p.eps (2 / p.eps) g := by
  funext x
  simp only [df2Ext, extOf, df2Pip_eq]
  ring

/-- `0 ≤ e(x) ≤ (1 + c) (1 + |x|/(1 - ε))`. -/
theorem extOf_abs_le (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf01 : ∀ x ∈ K, f x ∈ Set.Icc 0 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 ≤ c) (x : EuclideanSpace ℝ (Fin d)) :
    |extOf K ε c f x| ≤ (1 + c) + (1 + c) / (1 - ε) * ‖x‖ := by
  set p := pipOf K ε x with hp
  have hp_ge_one : 1 ≤ p := by
    dsimp [p, pipOf]
    exact le_max_left _ _
  have hp_pos : 0 < p := by linarith
  set y := p⁻¹ • x with hy
  have hy_mem_K : y ∈ K := by
    have h1 : (1 - ε)⁻¹ • y ∈ K := by
      dsimp [y]
      exact pip_play_mem K hK hKc hball ε hε0 hε1 x
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
      have mem_closedBall : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall, dist_self]
        exact zero_le_one
      exact hball mem_closedBall
    have h_smul_mem : (1 - ε) • ((1 - ε)⁻¹ • y) ∈ K := by
      apply hK.smul_mem_of_zero_mem h0 h1
      constructor
      · linarith
      · linarith
    have hy_eq : y = (1 - ε) • ((1 - ε)⁻¹ • y) := by
      dsimp [y]
      calc
        p⁻¹ • x = (1 : ℝ) • (p⁻¹ • x) := by simp
        _ = ((1 - ε) * (1 - ε)⁻¹) • (p⁻¹ • x) := by
          field_simp [show 1 - ε ≠ 0 from by linarith]
        _ = (1 - ε) • ((1 - ε)⁻¹ • (p⁻¹ • x)) := by simp [smul_smul, mul_assoc]
        _ = (1 - ε) • ((1 - ε)⁻¹ • y) := rfl
    rw [hy_eq]
    exact h_smul_mem
  have fy_range : f y ∈ Set.Icc (0 : ℝ) 1 := hf01 y hy_mem_K
  rcases fy_range with ⟨fy_nonneg, fy_le_one⟩
  have h_val_nonneg : 0 ≤ p * f y + c * (p - 1) := by
    nlinarith
  have h_val_eq_abs : |p * f y + c * (p - 1)| = p * f y + c * (p - 1) := by
    rw [abs_of_nonneg h_val_nonneg]
  have h_val_le : p * f y + c * (p - 1) ≤ (1 + c) * p := by
    nlinarith
  have h_gauge_le_norm : gauge K x ≤ ‖x‖ := by
    have hball_sub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K := by
      intro z hz
      apply hball
      rw [Metric.mem_closedBall]
      have hdist := Metric.mem_ball.mp hz
      linarith
    have := mul_gauge_le_norm (x := x) hball_sub
    simpa [one_mul] using this
  have hp_le : p ≤ 1 + ‖x‖ / (1 - ε) := by
    dsimp [p, pipOf]
    have h_gauge_div : gauge K x / (1 - ε) ≤ ‖x‖ / (1 - ε) := by
      apply div_le_div_of_nonneg_right h_gauge_le_norm
      linarith
    have h_one_le : (1 : ℝ) ≤ 1 + ‖x‖ / (1 - ε) := by
      have h_nonneg : 0 ≤ ‖x‖ / (1 - ε) := by
        apply div_nonneg (norm_nonneg _) (by linarith)
      linarith
    have h_gauge_div_le : gauge K x / (1 - ε) ≤ 1 + ‖x‖ / (1 - ε) := by
      linarith
    exact max_le h_one_le h_gauge_div_le
  have h_bound : (1 + c) * p ≤ (1 + c) + (1 + c) / (1 - ε) * ‖x‖ := by
    have h_mul : (1 + c) * p ≤ (1 + c) * (1 + ‖x‖ / (1 - ε)) := by
      nlinarith
    have h_eq : (1 + c) * (1 + ‖x‖ / (1 - ε)) = (1 + c) + (1 + c) / (1 - ε) * ‖x‖ := by
      field_simp [show 1 - ε ≠ 0 from by linarith]
    linarith
  dsimp [extOf, p]
  calc
    |p * f ((p⁻¹) • x) + c * (p - 1)| = p * f ((p⁻¹) • x) + c * (p - 1) := h_val_eq_abs
    _ ≤ (1 + c) * p := h_val_le
    _ ≤ (1 + c) + (1 + c) / (1 - ε) * ‖x‖ := h_bound

/-- A convex function on a finite-dimensional space is continuous. -/
theorem continuous_of_convexOn_univ (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F) :
    Continuous F := by
  have h := ConvexOn.continuousOn isOpen_univ hF
  rwa [continuousOn_univ] at h

/-! ## The surrogate -/

/-- The surrogate of a convex continuous function of linear growth is convex for `λ > 0`. -/
theorem df2Surr_convex (e : EuclideanSpace ℝ (Fin d) → ℝ) (he : ConvexOn ℝ Set.univ e) (hec : Continuous e)
    (a b : ℝ) (hg : ∀ x, |e x| ≤ a + b * ‖x‖) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ Set.univ (df2Surr e μ A lam) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_one_div_lam_pos : 0 < 1 / lam := div_pos (by norm_num) hlam
  have h_one_div_lam_nonneg : 0 ≤ 1 / lam := le_of_lt h_one_div_lam_pos
  -- Replace b with |b| to avoid sign issues; note that |e x| ≤ a + b * ‖x‖ ≤ a + |b| * ‖x‖
  have h_bound' : ∀ x, |e x| ≤ a + |b| * ‖x‖ := by
    intro x
    apply le_trans (hg x)
    have h_le : b * ‖x‖ ≤ |b| * ‖x‖ := by
      gcongr
      exact le_abs_self b
    nlinarith
  have h_int_norm : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖) γ := by
    have h_memLp : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 2 γ :=
      IsGaussian.memLp_two_id
    have h_int_norm_sq : Integrable (fun g => ‖g‖ ^ 2) γ := by
      have := h_memLp.integrable_norm_rpow' (p := 2)
      simpa using this
    have h_bound : ∀ g : EuclideanSpace ℝ (Fin d), ‖g‖ ≤ 1 + ‖g‖ ^ 2 := by
      intro g
      have h_sq : (‖g‖ - 1/2) ^ 2 ≥ 0 := pow_two_nonneg _
      nlinarith
    refine Integrable.mono' (integrable_const (1 : ℝ) |>.add h_int_norm_sq) ?_ ?_
    · have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) := by continuity
      exact h_cont.aestronglyMeasurable
    · filter_upwards with g
      simpa using h_bound g
  have h_int_e_comp (w : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun g => e ((1 - lam) • (μ + A g) + lam • w)) γ := by
    have h_bound : ∀ g, |e ((1 - lam) • (μ + A g) + lam • w)| ≤
        a + |b| * (|1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖) := by
      intro g
      apply le_trans (h_bound' _)
      have h_norm : ‖(1 - lam) • (μ + A g) + lam • w‖ ≤
          |1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖ := by
        calc
          ‖(1 - lam) • (μ + A g) + lam • w‖
              ≤ ‖(1 - lam) • (μ + A g)‖ + ‖lam • w‖ := norm_add_le _ _
          _ = |1 - lam| * ‖μ + A g‖ + |lam| * ‖w‖ := by
            simp [← smul_add, norm_smul, Real.norm_eq_abs]
          _ ≤ |1 - lam| * (‖μ‖ + ‖A g‖) + |lam| * ‖w‖ := by
            gcongr
            exact norm_add_le _ _
          _ ≤ |1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖ := by
            gcongr
            exact A.le_opNorm g
      have h_nonneg_abs_b : 0 ≤ |b| := abs_nonneg _
      have h_mul : |b| * ‖(1 - lam) • (μ + A g) + lam • w‖ ≤
          |b| * (|1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖) := by
        gcongr
      nlinarith
    have h_int_rhs : Integrable (fun g => a + |b| * (|1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖)) γ := by
      have h1 : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => a) γ := integrable_const _
      have h2 : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => |b| * |1 - lam| * ‖μ‖) γ := integrable_const _
      have h3 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (|b| * |1 - lam| * ‖A‖) * ‖g‖) γ := by
        -- Use Integrable.const_mul or similar
        convert h_int_norm.smul (|b| * |1 - lam| * ‖A‖) using 1
      have h4 : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => |b| * |lam| * ‖w‖) γ := integrable_const _
      have h_rhs_eq : (fun g : EuclideanSpace ℝ (Fin d) => a + |b| * (|1 - lam| * (‖μ‖ + ‖A‖ * ‖g‖) + |lam| * ‖w‖)) =
          fun g => a + |b| * |1 - lam| * ‖μ‖ + (|b| * |1 - lam| * ‖A‖) * ‖g‖ + |b| * |lam| * ‖w‖ := by
        ext g; ring
      rw [h_rhs_eq]
      exact ((h1.add h2).add h3).add h4
    refine Integrable.mono' h_int_rhs ?_ ?_
    · have h_cont : Continuous (fun g => (1 - lam) • (μ + A g) + lam • w) := by
        refine Continuous.add ?_ ?_
        · -- (1 - lam) • (μ + A g)
          have h_add : Continuous (fun g : EuclideanSpace ℝ (Fin d) => μ + A g) := by
            refine Continuous.add continuous_const A.continuous
          have h_smul : Continuous (fun g : EuclideanSpace ℝ (Fin d) => (1 - lam) • (μ + A g)) :=
            (continuous_const (y := (1 - lam))).smul h_add
          simpa [smul_add] using h_smul
        · -- lam • w
          exact continuous_const
      exact (hec.comp h_cont).aestronglyMeasurable
    · filter_upwards with g
      simpa [Real.norm_eq_abs] using h_bound g
  let C := ∫ g, e (μ + A g) ∂γ
  let I : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    ∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂γ
  have h_df2Surr_eq : df2Surr e μ A lam = fun z => (1 - 1 / lam) * C + (1 / lam) * I z := by
    ext z
    dsimp [df2Surr, C, I]
  rw [h_df2Surr_eq]
  have h_const_convex : ConvexOn ℝ Set.univ (fun _ : EuclideanSpace ℝ (Fin d) => (1 - 1 / lam) * C) :=
    convexOn_const _ convex_univ
  have h_I_convex : ConvexOn ℝ Set.univ I := by
    refine integral_convexOn_of_integrand_ae convex_univ (Filter.Eventually.of_forall fun g => ?_)
      fun w _ => h_int_e_comp w
    refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
    have hc : (1 - lam) • (μ + A g) = (p + q) • ((1 - lam) • (μ + A g)) := by rw [hpq, one_smul]
    have key : (1 - lam) • (μ + A g) + lam • (p • x + q • y) =
        p • ((1 - lam) • (μ + A g) + lam • x) + q • ((1 - lam) • (μ + A g) + lam • y) := by
      conv_lhs => rw [hc]
      module
    calc e ((1 - lam) • (μ + A g) + lam • (p • x + q • y))
        = e (p • ((1 - lam) • (μ + A g) + lam • x) + q • ((1 - lam) • (μ + A g) + lam • y)) := by rw [key]
      _ ≤ p • e ((1 - lam) • (μ + A g) + lam • x) + q • e ((1 - lam) • (μ + A g) + lam • y) :=
        he.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have h_smul_convex : ConvexOn ℝ Set.univ (fun z => (1 / lam) * I z) :=
    h_I_convex.smul h_one_div_lam_nonneg
  exact h_const_convex.add h_smul_convex

/-! ## Pi -/

/-- `E π(T g) ≤ s Mw(K) √d` for `‖T‖ ≤ s` (lem:ons:mink). -/
theorem gauge_mean_le (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (hs : 0 ≤ s) (hT : ‖T‖ ≤ s) :
    ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ s * pgMw K * Real.sqrt d := by
  -- K is a neighborhood of 0 (contains the closed unit ball), hence absorbent
  have hK_nhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) := by
    have hball_nhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
      Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
    exact Filter.mem_of_superset hball_nhds hball
  have hK_absorbent : Absorbent ℝ K := absorbent_nhds_zero hK_nhds
  -- gauge K is continuous (1-Lipschitz since ball 0 1 ⊆ K)
  have hK_cont : Continuous (gauge K) := by
    have h_lip : LipschitzWith (1 : ℝ≥0)⁻¹ (gauge K) :=
      hK.lipschitzWith_gauge (by norm_num : (0 : ℝ) < 1) (by
        -- Metric.ball 0 1 ⊆ K follows from hball since ball ⊆ closedBall
        exact fun x hx => hball (Metric.mem_closedBall.mpr (by
          have := Metric.mem_ball.mp hx
          exact this.le)))
    exact h_lip.continuous
  -- gauge K is convex on the whole space
  have hK_conv_on : ConvexOn ℝ Set.univ (gauge K) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    calc
      gauge K (a • x + b • y) ≤ gauge K (a • x) + gauge K (b • y) :=
        gauge_add_le hK hK_absorbent _ _
      _ = a * gauge K x + b * gauge K y := by
        simp [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul]
  -- bound: |gauge K x| ≤ ‖x‖ (since 0 ∈ K)
  have h_bound : ∀ x, |gauge K x| ≤ (0 : ℝ) + 1 * ‖x‖ := by
    intro x
    have h_nonneg := gauge_nonneg (s := K) x
    have h_le : gauge K x ≤ ‖x‖ := by
      have := mul_gauge_le_norm (r := 1) (by
        intro y hy
        exact hball (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le))
        (x := x)
      simpa [one_mul] using this
    rw [abs_of_nonneg h_nonneg, zero_add, one_mul]
    exact h_le
  -- apply the mean monotonicity lemma
  have h_mono := gauss_mean_mono (gauge K) hK_conv_on hK_cont 0 1 h_bound T s hs hT
  -- h_mono : ∫ gauge K (T g) ≤ ∫ gauge K (s • g)
  -- pull out s from gauge using gauge_smul_of_nonneg
  have h_smul : ∀ g, gauge K (s • g) = s * gauge K g := by
    intro g
    simpa [smul_eq_mul] using gauge_smul_of_nonneg hs g
  have h1 : ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
            s * ∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    calc
      ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, gauge K (s • g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := h_mono
      _ = ∫ g, (s * gauge K g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_congr_ae ?_
        filter_upwards with g using h_smul g
      _ = s * ∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_const_mul s (fun g => gauge K g)
  -- relate ∫ gauge K g to pgMw K * ∫ ‖g‖
  have h_int_norm_pos : 0 < ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_lower := normMeanLower d
    have hd_pos : 0 < (d : ℝ) / Real.sqrt ((d : ℝ) + 1) := by
      refine div_pos (by exact_mod_cast hd) ?_
      exact Real.sqrt_pos.mpr (by linarith [show (0 : ℝ) ≤ d from by exact_mod_cast Nat.zero_le d])
    linarith
  have h_pgMw_eq : ∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      pgMw K * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [pgMw]
    field_simp [ne_of_gt h_int_norm_pos]
  have h_pgMw_nonneg : 0 ≤ pgMw K := by
    have h_num : 0 ≤ ∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      integral_nonneg (fun g => gauge_nonneg _)
    have h_denom : 0 ≤ ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      integral_nonneg (fun g => norm_nonneg _)
    exact div_nonneg h_num h_denom
  have h_int_norm_le_sqrt_d : ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ Real.sqrt (d : ℝ) :=
    AdversarialBco.integral_norm_stdGaussian_le d
  calc
    ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        s * ∫ g, gauge K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := h1
    _ = s * (pgMw K * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by rw [h_pgMw_eq]
    _ = s * pgMw K * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by ring
    _ ≤ s * pgMw K * Real.sqrt (d : ℝ) := by
      have h_nonneg_prod : 0 ≤ s * pgMw K := mul_nonneg hs h_pgMw_nonneg
      exact mul_le_mul_of_nonneg_left h_int_norm_le_sqrt_d h_nonneg_prod

/-- The upper tail of `π(T g)` about its mean, at the constant `1/2` (a junk bound `1` when `T = 0`). -/
theorem gauge_conc (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ)
    (ht : 0 ≤ t) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
        {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) := by
  have hball_mem_nhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
    Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hK_mem_nhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset hball_mem_nhds hball
  have h_gauge_cont : Continuous (gauge K) :=
    continuous_gauge hK hK_mem_nhds
  have h_gauge_meas : Measurable (gauge K) :=
    h_gauge_cont.measurable
  have hT_meas : Measurable T :=
    T.continuous.measurable
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K :=
    Metric.ball_subset_closedBall.trans hball
  have h_lip : LipschitzWith (1 : ℝ≥0) (gauge K) := by
    have := hK.lipschitzWith_gauge (by norm_num : 0 < (1 : ℝ≥0)) hball'
    simpa [show ((1 : ℝ≥0)⁻¹ : ℝ≥0) = (1 : ℝ≥0) by norm_num] using this
  have h_gc := GConc.gaussConcSharp.1
  rcases h_gc d d (0 : EuclideanSpace ℝ (Fin d)) T (gauge K) (1 : ℝ≥0) h_lip with ⟨h_int, h_bound⟩
  have h_bound_t := (h_bound t ht).left
  set ν := (stdGaussian (EuclideanSpace ℝ (Fin d))).map fun g => (0 : EuclideanSpace ℝ (Fin d)) + T g with hν_def
  set c := ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) with hc_def
  have h_int_c : ∫ y, gauge K y ∂ν = c := by
    rw [hν_def, hc_def]
    have hφ_meas : AEMeasurable (fun g : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d)) + T g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ((measurable_const (a := (0 : EuclideanSpace ℝ (Fin d)))).add hT_meas).aemeasurable
    have h_gauge_aestrongly : AEStronglyMeasurable (gauge K) ν := by
      rw [hν_def]
      exact h_gauge_meas.aestronglyMeasurable
    calc
      ∫ y, gauge K y ∂ν = ∫ y, gauge K y ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map fun g => (0 : EuclideanSpace ℝ (Fin d)) + T g) := rfl
      _ = ∫ g, gauge K ((fun g' => (0 : EuclideanSpace ℝ (Fin d)) + T g') g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_map hφ_meas h_gauge_aestrongly]
      _ = ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by simp
      _ = c := rfl
  have h_bound_simp : ν.real {x | c + t ≤ gauge K x} ≤ Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2))) := by
    have h_set_eq : {x | t ≤ gauge K x - ∫ y, gauge K y ∂ν} = {x | c + t ≤ gauge K x} := by
      ext x
      simp [h_int_c]
      exact ⟨by intro h; linarith, by intro h; linarith⟩
    rw [h_set_eq] at h_bound_t
    have h_exp_eq : (-(1 / 2 * t ^ 2) / (((1 : ℝ≥0) : ℝ) * ‖T‖) ^ 2) = (-(t ^ 2 / (2 * ‖T‖ ^ 2))) := by
      simp
      ring
    rw [h_exp_eq] at h_bound_t
    exact h_bound_t
  have h_set_meas : MeasurableSet {x | c + t ≤ gauge K x} := by
    have h_closed : IsClosed {x | c + t ≤ gauge K x} := by
      have h_closed_set : IsClosed {y : ℝ | c + t ≤ y} := isClosed_Ici
      exact h_closed_set.preimage h_gauge_cont
    exact h_closed.measurableSet
  have h_ν_eq : ν {x | c + t ≤ gauge K x} = (stdGaussian (EuclideanSpace ℝ (Fin d))) (T ⁻¹' {x | c + t ≤ gauge K x}) := by
    rw [hν_def]
    have h_preimage : (fun g : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d)) + T g) ⁻¹' {x | c + t ≤ gauge K x} =
      T ⁻¹' {x | c + t ≤ gauge K x} := by
      ext g; simp
    have hf_meas : Measurable (fun g : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d)) + T g) :=
      (measurable_const (a := (0 : EuclideanSpace ℝ (Fin d)))).add hT_meas
    rw [Measure.map_apply hf_meas h_set_meas, h_preimage]
  have h_target_set_eq : T ⁻¹' {x | c + t ≤ gauge K x} = {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)} := by
    ext g
    simp [hc_def]
  rw [h_target_set_eq] at h_ν_eq
  have h_measure_ne_top : (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)} ≠ ∞ := by
    have : IsProbabilityMeasure (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      infer_instance
    exact measure_ne_top _ _
  calc
    (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)}
        = ENNReal.ofReal ((stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)}) := by
      rw [MeasureTheory.ofReal_measureReal h_measure_ne_top]
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have h_real_eq : ν.real {x | c + t ≤ gauge K x} = (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | (∫ h, gauge K (T h) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) + t ≤ gauge K (T g)} := by
        rw [Measure.real, Measure.real, h_ν_eq]
      rw [← h_real_eq]
      exact h_bound_simp

/-- `|1.27 √(d + 1)/d · √d| ≤ 2 √L` for `d ≥ 1`, `L ≥ 1`: the mean of the gauge at the spread `1/(2 √L)` is at most
`1`. -/
theorem mw_small (hd : 1 ≤ d) (Le : ℝ) (hLe : 1 ≤ Le) : df2Mw d * Real.sqrt d ≤ 2 * Real.sqrt Le := by
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hd_pos : 0 < (d : ℝ) := by
    have : 0 < (d : ℕ) := Nat.one_pos.trans_le hd
    exact_mod_cast this
  have h_sqrt_Le_ge_one : 1 ≤ Real.sqrt Le := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt Le := Real.sqrt_le_sqrt hLe
  have h_two_le : (2 : ℝ) ≤ 2 * Real.sqrt Le := by
    nlinarith
  have h_sq_bound : (d : ℝ) + 1 ≤ 2 * (d : ℝ) := by
    nlinarith
  have h_sqrt_bound : Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt (d : ℝ) := by
    calc
      Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt (2 * (d : ℝ)) := Real.sqrt_le_sqrt h_sq_bound
      _ = Real.sqrt 2 * Real.sqrt (d : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h_main : df2Mw d * Real.sqrt (d : ℝ) ≤ 1.27 * Real.sqrt 2 := by
    dsimp [df2Mw]
    have h_num_ineq : 1.27 * Real.sqrt ((d : ℝ) + 1) * Real.sqrt (d : ℝ) ≤
        1.27 * (Real.sqrt 2 * Real.sqrt (d : ℝ)) * Real.sqrt (d : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul_of_nonneg_left h_sqrt_bound (by norm_num : 0 ≤ (1.27 : ℝ))
    calc
      (1.27 * Real.sqrt ((d : ℝ) + 1) / (d : ℝ)) * Real.sqrt (d : ℝ) =
          1.27 * Real.sqrt ((d : ℝ) + 1) * Real.sqrt (d : ℝ) / (d : ℝ) := by
        rw [div_mul_eq_mul_div]
      _ ≤ 1.27 * (Real.sqrt 2 * Real.sqrt (d : ℝ)) * Real.sqrt (d : ℝ) / (d : ℝ) :=
        div_le_div_of_nonneg_right h_num_ineq hd_nonneg
      _ = 1.27 * Real.sqrt 2 * ((Real.sqrt (d : ℝ)) ^ 2) / (d : ℝ) := by ring
      _ = 1.27 * Real.sqrt 2 * (d : ℝ) / (d : ℝ) := by
        rw [Real.sq_sqrt hd_nonneg]
      _ = 1.27 * Real.sqrt 2 := by
        field_simp [hd_pos.ne.symm]
  have h_num : 1.27 * Real.sqrt 2 ≤ (2 : ℝ) := by
    have h_sq : (1.27 * Real.sqrt 2)^2 ≤ (2 : ℝ)^2 := by
      have h_sq_sqrt2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
      nlinarith
    have h_nonneg_val : 0 ≤ 1.27 * Real.sqrt 2 := by positivity
    have h_two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    nlinarith
  calc
    df2Mw d * Real.sqrt (d : ℝ) ≤ 1.27 * Real.sqrt 2 := h_main
    _ ≤ (2 : ℝ) := h_num
    _ ≤ 2 * Real.sqrt Le := h_two_le

open Topology Filter in
/-- Pi in one round, on `E d`: `P(π(μ + T g) > √L) ≤ exp(-2 L (√L - 2)²)` for `π(μ) ≤ 1`, `‖T‖ ≤ 1/(2 √L)`. -/
theorem pi_tail (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : EuclideanSpace ℝ (Fin d))
    (hmu : gauge K mu ≤ 1) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Le : ℝ) (hLe : 504 ≤ Le)
    (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt Le)) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) {g | Real.sqrt Le < gauge K (mu + T g)} ≤
      ENNReal.ofReal (Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set s := 1 / (2 * Real.sqrt Le) with hs_def
  set c := ∫ g, gauge K (T g) ∂γ with hc_def
  set t := Real.sqrt Le - 2 with ht_def
  have hLe_pos : 0 < Le := by linarith
  have hsqrt_pos : 0 < Real.sqrt Le := Real.sqrt_pos.mpr hLe_pos
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    refine div_nonneg (by norm_num) (mul_nonneg (by norm_num) (by positivity))
  have ht_nonneg : 0 ≤ t := by
    rw [ht_def]
    have hsqrt_ge_two : 2 ≤ Real.sqrt Le := by
      have hLe_four : 4 ≤ Le := by linarith
      calc
        2 = Real.sqrt (4 : ℝ) := by norm_num
        _ ≤ Real.sqrt Le := Real.sqrt_le_sqrt hLe_four
    linarith
  have h_absorbent : Absorbent ℝ K := by
    have hball_mem : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
      Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
    have hK_mem : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
      mem_of_superset hball_mem hball
    exact absorbent_nhds_zero hK_mem
  by_cases hT_zero : ‖T‖ = 0
  · -- case ‖T‖ = 0, then T = 0, set is empty
    have hT_eq_zero : T = 0 := (norm_eq_zero.mp hT_zero)
    have hsqrt_gt_one : 1 < Real.sqrt Le := by
      have hLe_one : 1 < Le := by linarith
      calc
        1 = Real.sqrt (1 : ℝ) := by norm_num
        _ < Real.sqrt Le := Real.sqrt_lt_sqrt (by norm_num) hLe_one
    have h_empty : {g | Real.sqrt Le < gauge K (mu + T g)} = (∅ : Set (EuclideanSpace ℝ (Fin d))) := by
      ext g
      constructor
      · intro hlt
        have hlt' : Real.sqrt Le < gauge K (mu + T g) := by simpa using hlt
        have hgauge_eq : gauge K (mu + T g) = gauge K mu := by
          simp [hT_eq_zero]
        linarith [hmu, hsqrt_gt_one, hlt', hgauge_eq]
      · intro h
        simp at h
    rw [h_empty]
    simp
  · -- case ‖T‖ > 0
    have hT_pos : 0 < ‖T‖ := by
      by_contra! h
      have heq : ‖T‖ = 0 := le_antisymm h (norm_nonneg _)
      exact hT_zero heq
    have hc_le_one : c ≤ 1 := by
      -- from gauge_mean_le: c ≤ s * pgMw K * √d
      have h_mean : c ≤ s * pgMw K * Real.sqrt (d : ℝ) :=
        gauge_mean_le hd K hK hKc hball T s hs_nonneg hT
      -- from hMw: pgMw K ≤ df2Mw d
      have h_pg_le : pgMw K ≤ df2Mw d := hMw
      -- from mw_small: df2Mw d * √d ≤ 2 * √Le
      have h_mw_small : df2Mw d * Real.sqrt (d : ℝ) ≤ 2 * Real.sqrt Le :=
        mw_small hd Le (by linarith)
      -- combine
      have h_sqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have h_sqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have h_factor_nonneg : 0 ≤ s * Real.sqrt (d : ℝ) := mul_nonneg hs_nonneg h_sqrt_d_nonneg
      calc
        c ≤ s * pgMw K * Real.sqrt (d : ℝ) := h_mean
        _ = (s * Real.sqrt (d : ℝ)) * pgMw K := by ring
        _ ≤ (s * Real.sqrt (d : ℝ)) * (df2Mw d) := by
          gcongr
        _ = s * (df2Mw d * Real.sqrt (d : ℝ)) := by ring
        _ ≤ s * (2 * Real.sqrt Le) := by
          gcongr
        _ = (1 / (2 * Real.sqrt Le)) * (2 * Real.sqrt Le) := by rw [hs_def]
        _ = 1 := by
          field_simp [ne_of_gt hsqrt_pos]
    have h_subset : {g | Real.sqrt Le < gauge K (mu + T g)} ⊆ {g | c + t ≤ gauge K (T g)} := by
      intro g hg
      simp only [Set.mem_ofPred_eq] at hg ⊢
      -- hg: Real.sqrt Le < gauge K (mu + T g)
      -- goal: c + t ≤ gauge K (T g)
      have h_add : gauge K (mu + T g) ≤ gauge K mu + gauge K (T g) :=
        gauge_add_le hK h_absorbent mu (T g)
      have h_sum : gauge K mu + gauge K (T g) ≤ 1 + gauge K (T g) := by gcongr
      have h_ineq : Real.sqrt Le < 1 + gauge K (T g) := by linarith
      have h_lt : Real.sqrt Le - 1 < gauge K (T g) := by linarith
      have h_lt' : c + t < gauge K (T g) := calc
        c + t = c + (Real.sqrt Le - 2) := by rw [ht_def]
        _ ≤ 1 + (Real.sqrt Le - 2) := by gcongr
        _ = Real.sqrt Le - 1 := by ring
        _ < gauge K (T g) := h_lt
      exact h_lt'.le
    have h_gc : γ {g | c + t ≤ gauge K (T g)} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) :=
      gauge_conc K hK hKc hball T t ht_nonneg
    have h_exp_ineq : Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2))) ≤ Real.exp (-(2 * Le * t ^ 2)) := by
      refine Real.exp_le_exp.mpr ?_
      -- need: -(t^2/(2‖T‖^2)) ≤ -(2*Le*t^2)
      -- i.e., t^2/(2‖T‖^2) ≥ 2*Le*t^2
      -- Since t^2 ≥ 0, it suffices to show 1/(2‖T‖^2) ≥ 2*Le
      -- i.e., ‖T‖^2 ≤ 1/(4*Le)
      have hT_sq_le : ‖T‖ ^ 2 ≤ 1 / (4 * Le) := by
        have hT_nonneg : 0 ≤ ‖T‖ := norm_nonneg _
        have h_sq : ‖T‖ ^ 2 ≤ s ^ 2 := by gcongr
        have h_s_sq : s ^ 2 = 1 / (4 * Le) := by
          rw [hs_def]
          calc
            (1 / (2 * Real.sqrt Le)) ^ 2 = 1 ^ 2 / ((2 * Real.sqrt Le) ^ 2) := by ring
            _ = 1 / ((2 * Real.sqrt Le) ^ 2) := by norm_num
            _ = 1 / (4 * ((Real.sqrt Le) ^ 2)) := by ring
            _ = 1 / (4 * Le) := by rw [Real.sq_sqrt (by positivity : 0 ≤ Le)]
        rw [h_s_sq] at h_sq
        exact h_sq
      have ht_sq_nonneg : 0 ≤ t ^ 2 := pow_two_nonneg _
      have h_div_ineq : 1 / (2 * ‖T‖ ^ 2) ≥ 2 * Le := by
        have hpos : 0 < ‖T‖ ^ 2 := pow_pos hT_pos 2
        have hpos' : 0 < 4 * Le := by positivity
        have h_mul : 4 * Le * ‖T‖ ^ 2 ≤ 1 := by
          calc
            4 * Le * ‖T‖ ^ 2 ≤ 4 * Le * (1 / (4 * Le)) := by gcongr
            _ = 1 := by field_simp [hpos'.ne']
        field_simp [hpos.ne']
        nlinarith
      calc
        -(t ^ 2 / (2 * ‖T‖ ^ 2)) = -(t ^ 2 * (1 / (2 * ‖T‖ ^ 2))) := by ring
        _ ≤ -(t ^ 2 * (2 * Le)) := by
          gcongr
        _ = -(2 * Le * t ^ 2) := by ring
    have h_ofReal_ineq : ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) ≤
        ENNReal.ofReal (Real.exp (-(2 * Le * t ^ 2))) :=
      ENNReal.ofReal_le_ofReal h_exp_ineq
    have h_target_exp : -(2 * Le * t ^ 2) = -(2 * Le * (Real.sqrt Le - 2) ^ 2) := by
      rw [ht_def]
    rw [h_target_exp] at h_ofReal_ineq
    calc
      γ {g | Real.sqrt Le < gauge K (mu + T g)} ≤ γ {g | c + t ≤ gauge K (T g)} :=
        measure_mono h_subset
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) := h_gc
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2))) := h_ofReal_ineq

/-- The operator norm from a quadratic bound: `|A w|² ≤ k |w|²` gives `‖A‖ ≤ √k`. -/
theorem toEuclideanCLM_norm_le (A : Matrix (Fin d) (Fin d) ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hA : ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ Real.sqrt k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg k) ?_
  intro x
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have h_sqrt_nonneg : 0 ≤ Real.sqrt k := Real.sqrt_nonneg k
  have h_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ ^ 2 ≤ (Real.sqrt k * ‖x‖) ^ 2 := by
    calc
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ ^ 2 = inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) := by
        rw [real_inner_self_eq_norm_sq]
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp ⬝ᵥ star ((Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp ⬝ᵥ (Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp := by
        simp
      _ = (A.mulVec (x.ofLp)) ⬝ᵥ (A.mulVec (x.ofLp)) := by
        rw [Matrix.toEuclideanCLM_toLp]
      _ ≤ k * ((x.ofLp) ⬝ᵥ (x.ofLp)) := hA (x.ofLp)
      _ = k * (x.ofLp ⬝ᵥ star (x.ofLp)) := by
        simp
      _ = k * (inner ℝ x x) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
      _ = k * ‖x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = (Real.sqrt k * ‖x‖) ^ 2 := by
        calc
          k * ‖x‖ ^ 2 = (Real.sqrt k) ^ 2 * ‖x‖ ^ 2 := by rw [Real.sq_sqrt hk]
          _ = (Real.sqrt k * ‖x‖) ^ 2 := by ring
  have h_nonneg_left : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ := norm_nonneg _
  have h_nonneg_right : 0 ≤ Real.sqrt k * ‖x‖ := mul_nonneg h_sqrt_nonneg hx_nonneg
  nlinarith

/-- Pi in one round, in the coordinates `Fin d → ℝ`, at a state with `π(μ) ≤ 1` and `|A w|² ≤ 2 σ² |w|²`,
`σ² = 1/(8 L)`. -/
theorem pi_round_law (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : Fin d → ℝ)
    (hmu : gauge K (WithLp.toLp 2 mu) ≤ 1) (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (Le : ℝ) (hLe : 504 ≤ Le) (hA : ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ 2 * (1 / (8 * Le)) * (w ⬝ᵥ w)) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        {x | Real.sqrt Le < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} ≤
      ENNReal.ofReal (Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2))) := by
  set T := (1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A with hTdef
  have hLe_pos : 0 < Le := by linarith
  have hk_pos : 0 ≤ 2 * (1 / (8 * Le)) := by
    have : 0 ≤ 1 / (8 * Le) := div_nonneg (by norm_num) (by linarith)
    nlinarith
  have hA_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ Real.sqrt (2 * (1 / (8 * Le))) :=
    toEuclideanCLM_norm_le A (2 * (1 / (8 * Le))) hk_pos hA
  have h_sqrt : Real.sqrt (2 * (1 / (8 * Le))) = 1 / (2 * Real.sqrt Le) := by
    calc
      Real.sqrt (2 * (1 / (8 * Le))) = Real.sqrt ((1 : ℝ) / (4 * Le)) := by
        field_simp [hLe_pos.ne.symm]
        ring
      _ = Real.sqrt 1 / Real.sqrt (4 * Le) := by rw [Real.sqrt_div (by norm_num) _]
      _ = 1 / Real.sqrt (4 * Le) := by norm_num
      _ = 1 / (Real.sqrt 4 * Real.sqrt Le) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
      _ = 1 / (2 * Real.sqrt Le) := by norm_num
  have hA_norm' : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ 1 / (2 * Real.sqrt Le) := by
    linarith
  have hT_norm : ‖T‖ ≤ 1 / (2 * Real.sqrt Le) := by
    rw [hTdef]
    have h_nonneg : 0 ≤ 1 - lam := by linarith
    have h_le_one : 1 - lam ≤ 1 := by linarith
    calc
      ‖(1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ = ‖(1 - lam)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
        rw [norm_smul]
      _ = |1 - lam| * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by rw [Real.norm_eq_abs]
      _ = (1 - lam) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by rw [abs_of_nonneg h_nonneg]
      _ ≤ 1 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
        have h_norm_nonneg : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := norm_nonneg _
        nlinarith
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by simp
      _ ≤ 1 / (2 * Real.sqrt Le) := hA_norm'
  have h_meas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) := by
    exact WithLp.measurable_toLp 2 _
  have h_set_eq : {x : Fin d → ℝ | Real.sqrt Le < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} =
      (WithLp.toLp 2) ⁻¹' {g : EuclideanSpace ℝ (Fin d) | Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T g)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have h1 : WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)) = WithLp.toLp 2 mu + WithLp.toLp 2 ((1 - lam) • (A *ᵥ x)) := by
      rw [WithLp.toLp_add]
    have h2 : WithLp.toLp 2 ((1 - lam) • (A *ᵥ x)) = (1 - lam) • WithLp.toLp 2 (A *ᵥ x) := by
      rw [WithLp.toLp_smul]
    have h3 : WithLp.toLp 2 (A *ᵥ x) = Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x) := by
      rw [toEuclideanCLM_toLp]
    calc
      Real.sqrt Le < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x))) ↔
          Real.sqrt Le < gauge K (WithLp.toLp 2 mu + WithLp.toLp 2 ((1 - lam) • (A *ᵥ x))) := by
        rw [h1]
      _ ↔ Real.sqrt Le < gauge K (WithLp.toLp 2 mu + (1 - lam) • WithLp.toLp 2 (A *ᵥ x)) := by
        rw [h2]
      _ ↔ Real.sqrt Le < gauge K (WithLp.toLp 2 mu + (1 - lam) • (Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x))) := by
        rw [h3]
      _ ↔ Real.sqrt Le < gauge K (WithLp.toLp 2 mu + ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 x)) := by
        simp [_root_.smul_apply]
      _ ↔ Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T (WithLp.toLp 2 x)) := by
        rw [hTdef]
  have h_gauge_measurable : MeasurableSet {g : EuclideanSpace ℝ (Fin d) | Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T g)} := by
    have h_cont : Continuous (gauge K : EuclideanSpace ℝ (Fin d) → ℝ) :=
      continuous_gauge hK (by
        have h_ball_mem : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) := by
          exact Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
        exact Filter.mem_of_superset h_ball_mem hball)
    have h_add_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => WithLp.toLp 2 mu + T g) := by
      have : Continuous (fun g : EuclideanSpace ℝ (Fin d) => T g) := by
        exact ContinuousLinearMap.continuous T
      have : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => WithLp.toLp 2 mu) := continuous_const
      continuity
    have h_open : MeasurableSet {r : ℝ | Real.sqrt Le < r} :=
      measurableSet_Ioi
    have h_comp_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => gauge K (WithLp.toLp 2 mu + T g)) :=
      h_cont.comp h_add_cont
    have h_comp_meas : Measurable (fun g : EuclideanSpace ℝ (Fin d) => gauge K (WithLp.toLp 2 mu + T g)) :=
      h_comp_cont.measurable
    exact h_open.preimage h_comp_meas
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        {x | Real.sqrt Le < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} =
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        ((WithLp.toLp 2) ⁻¹' {g : EuclideanSpace ℝ (Fin d) | Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T g)}) := by
      rw [h_set_eq]
    _ = ((Measure.pi fun _ : Fin d => gaussianReal 0 1).map (WithLp.toLp 2))
        {g : EuclideanSpace ℝ (Fin d) | Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T g)} := by
      rw [Measure.map_apply h_meas h_gauge_measurable]
    _ = stdGaussian (EuclideanSpace ℝ (Fin d))
        {g : EuclideanSpace ℝ (Fin d) | Real.sqrt Le < gauge K (WithLp.toLp 2 mu + T g)} := by
      rw [map_pi_eq_stdGaussian]
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2))) := by
      refine pi_tail hd K hK hKc hball hMw (WithLp.toLp 2 mu) hmu T Le hLe hT_norm

/-- The states of spread at most `k`: a closed set of matrices. -/
theorem isClosed_spread (k : ℝ) :
    IsClosed {A : Matrix (Fin d) (Fin d) ℝ | ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)} := by
  rw [Set.ofPred_forall]
  refine isClosed_iInter (fun w => ?_)
  refine isClosed_le ?_ ?_
  · fun_prop
  · exact continuous_const

/-! ## Noise and Gauss -/

/-- Noise in one round: `P(|e| > √L) ≤ 2 exp(-L)` when `E[exp(e²) | m] ≤ 2`. -/
theorem noise_round {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0) (e : Ω → ℝ) (he : Measurable[m0] e)
    (hint : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hexp : μ[fun ω => Real.exp (e ω ^ 2) | m] ≤ᵐ[μ] fun _ => 2) (L : ℝ) (hL : 0 ≤ L) :
    μ {ω | Real.sqrt L < |e ω|} ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  have h2 : ∫ ω, Real.exp (e ω ^ 2) ∂μ ≤ 2 := by
    rw [← integral_condExp hm]
    calc ∫ ω, (μ[fun ω => Real.exp (e ω ^ 2) | m]) ω ∂μ ≤ ∫ _, (2 : ℝ) ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) hexp
      _ = 2 := by simp
  have h := @noiseTail Ω m0 μ _ e he.aemeasurable hint h2 (Real.sqrt L) (Real.sqrt_nonneg L)
  rw [Real.sq_sqrt hL] at h
  exact (measure_mono fun ω (hω : Real.sqrt L < |e ω|) => le_of_lt hω).trans h

/-- Gauss in one round: `P(|ξ|² > (8d/3) L) ≤ 2 exp(-L)` for `ξ` standard Gaussian. -/
theorem gauss_round (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (ξ : Ω → Fin d → ℝ)
    (hξ : Measurable ξ) (hlaw : μ.map ξ = Measure.pi fun _ : Fin d => gaussianReal 0 1) (L : ℝ) :
    μ {ω | 8 * d / 3 * L < ξ ω ⬝ᵥ ξ ω} ≤ ENNReal.ofReal (2 * Real.exp (-L)) := by
  set t := 8 * (d : ℝ) / 3 * L with ht
  have hdpos : (0 : ℝ) < d := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  -- The set {ω | t < ξ ω ⬝ᵥ ξ ω} is the preimage under ξ
  have h_meas_set : MeasurableSet {x : Fin d → ℝ | t < x ⬝ᵥ x} := by
    have h_meas_dot : Measurable (fun x : Fin d → ℝ => x ⬝ᵥ x) := by
      unfold dotProduct
      refine Finset.measurable_sum _ ?_
      intro i hi
      have h_proj : Measurable (fun x : Fin d → ℝ => x i) := measurable_pi_apply i
      exact (h_proj.mul h_proj)
    have h_set : MeasurableSet (Set.Ioi t) := measurableSet_Ioi
    have : {x : Fin d → ℝ | t < x ⬝ᵥ x} = (fun x : Fin d → ℝ => x ⬝ᵥ x) ⁻¹' (Set.Ioi t) := by
      ext x; simp
    rw [this]
    exact MeasurableSet.preimage h_set h_meas_dot
  -- Step 1: μ {ω | t < ξ ω ⬝ᵥ ξ ω} = (μ.map ξ) {x | t < x ⬝ᵥ x}
  have h_preimage : {ω | t < ξ ω ⬝ᵥ ξ ω} = ξ ⁻¹' {x : Fin d → ℝ | t < x ⬝ᵥ x} := by
    ext ω; simp
  have h_step1 : μ {ω | t < ξ ω ⬝ᵥ ξ ω} = (μ.map ξ) {x : Fin d → ℝ | t < x ⬝ᵥ x} := by
    rw [h_preimage, Measure.map_apply hξ h_meas_set]
  -- Step 2: = (Measure.pi ...) {x | t < x ⬝ᵥ x}
  have h_step2 : (μ.map ξ) {x : Fin d → ℝ | t < x ⬝ᵥ x} =
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x : Fin d → ℝ | t < x ⬝ᵥ x} := by
    rw [hlaw]
  -- Step 3: Relate {x | t < x ⬝ᵥ x} to {W | t ≤ ‖W‖ ^ 2}
  -- Key identity: x ⬝ᵥ x = ‖WithLp.toLp 2 x‖ ^ 2
  have h_dot_norm (x : Fin d → ℝ) : x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    calc
      x ⬝ᵥ x = ((WithLp.toLp 2 x).ofLp : Fin d → ℝ) ⬝ᵥ (WithLp.toLp 2 x).ofLp := by
        simp
      _ = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp
      _ = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have h_subset : {x : Fin d → ℝ | t < x ⬝ᵥ x} ⊆
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' {W | t ≤ ‖W‖ ^ 2} := by
    intro x hx
    simp at hx ⊢
    have : t < x ⬝ᵥ x := hx
    rw [h_dot_norm x] at this
    linarith
  -- Step 4: By measure monotonicity
  have h_step4 : (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x : Fin d → ℝ | t < x ⬝ᵥ x} ≤
      (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        ((WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' {W | t ≤ ‖W‖ ^ 2}) := by
    apply measure_mono h_subset
  -- Step 5: Use map_pi_eq_stdGaussian
  have h_meas_S : MeasurableSet {W : EuclideanSpace ℝ (Fin d) | t ≤ ‖W‖ ^ 2} := by
    have h_cont : Continuous (fun W : EuclideanSpace ℝ (Fin d) => ‖W‖ ^ 2) := by
      continuity
    have h_set : MeasurableSet (Set.Ici t) := measurableSet_Ici
    have : {W : EuclideanSpace ℝ (Fin d) | t ≤ ‖W‖ ^ 2} =
        (fun W : EuclideanSpace ℝ (Fin d) => ‖W‖ ^ 2) ⁻¹' (Set.Ici t) := by
      ext W; simp
    rw [this]
    exact MeasurableSet.preimage h_set h_cont.measurable
  have h_map : (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      ((WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' {W | t ≤ ‖W‖ ^ 2}) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} := by
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d)]
    rw [Measure.map_apply (WithLp.measurable_toLp 2 (Fin d → ℝ)) h_meas_S]
  -- Step 6: Use gaussTailT2
  have h_step6 : stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} ≤
      ENNReal.ofReal (2 * Real.exp (-(3 * t / (8 * (d : ℝ))))) :=
    gaussTailT2 d t hd
  -- Step 7: Compute -(3 * t / (8 * d)) = -L
  have h_final : -(3 * t / (8 * (d : ℝ))) = -L := by
    dsimp [t]
    field_simp [hd_ne_zero]
  -- Combine everything
  calc
    μ {ω | 8 * d / 3 * L < ξ ω ⬝ᵥ ξ ω} = μ {ω | t < ξ ω ⬝ᵥ ξ ω} := by
      simp [t]
    _ = (μ.map ξ) {x : Fin d → ℝ | t < x ⬝ᵥ x} := h_step1
    _ = (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x : Fin d → ℝ | t < x ⬝ᵥ x} := h_step2
    _ ≤ (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        ((WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' {W | t ≤ ‖W‖ ^ 2}) := h_step4
    _ = stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} := h_map
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(3 * t / (8 * (d : ℝ))))) := h_step6
    _ = ENNReal.ofReal (2 * Real.exp (-L)) := by rw [h_final]

/-! ## The parameters -/

/-- `0 < δ_e < 1` and `log(1/δ_e) ≥ log n + 14`. -/
theorem par_de (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) :
    0 < (df2oPar d n δ).δe ∧ (df2oPar d n δ).δe < 1 ∧
      Real.log n + 14 ≤ Real.log (1 / (df2oPar d n δ).δe) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdpos : (0 : ℝ) < d := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hprod_pos : 0 < (d : ℝ) * (n : ℝ) := mul_pos hdpos hnpos
  have hprod_ge_one : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by nlinarith
  have hcube_ge_one : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
    have hsq : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hexp_pos : 0 < Real.exp (-14) := Real.exp_pos _
  have hexp14_pos : 0 < Real.exp 14 := Real.exp_pos _
  have h_exp_inv : (1 : ℝ) / Real.exp (-14) = Real.exp 14 := by
    rw [Real.exp_neg]
    field_simp [hexp14_pos.ne']
  have hδe_pos : 0 < (df2oPar d n δ).δe := by
    unfold df2oPar
    have hmin_pos : 0 < min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) := by
      refine lt_min_iff.mpr ⟨div_pos hδ0 (by norm_num), div_pos hexp_pos ?_⟩
      positivity
    have hnum : 0 < 4 * min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) := by nlinarith
    have hdenom : 0 < 5 * (n : ℝ) := by nlinarith
    exact div_pos hnum hdenom
  have hδe_lt_one : (df2oPar d n δ).δe < 1 := by
    unfold df2oPar
    have hmin_le : min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) ≤ Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3) :=
      min_le_right _ _
    have hdiv_le : Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3) ≤ Real.exp (-14) :=
      div_le_self (by positivity) hcube_ge_one
    have hexp_nonneg : 0 ≤ 4 * Real.exp (-14) := by positivity
    have hnum : 4 * min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) ≤ 4 * Real.exp (-14) := by
      nlinarith
    have hdenom_pos : (0 : ℝ) < 5 * (n : ℝ) := by nlinarith
    have h1 : 4 * min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) / (5 * (n : ℝ)) ≤
             4 * Real.exp (-14) / (5 * (n : ℝ)) :=
      (div_le_div_of_nonneg_right hnum (by nlinarith))
    have h5pos : (0 : ℝ) < 5 := by norm_num
    have h5n_ge_5 : (5 : ℝ) ≤ 5 * (n : ℝ) := by nlinarith
    have h2 : 4 * Real.exp (-14) / (5 * (n : ℝ)) ≤ 4 * Real.exp (-14) / 5 :=
      div_le_div_of_nonneg_left hexp_nonneg h5pos h5n_ge_5
    have hexp_lt_one : Real.exp (-14) < 1 := by
      have hneg : (-14 : ℝ) < 0 := by norm_num
      exact (Real.exp_lt_exp.mpr hneg).trans_eq (by norm_num : Real.exp (0 : ℝ) = 1)
    have h3 : 4 * Real.exp (-14) / 5 < 1 := by nlinarith
    nlinarith
  have h_log : Real.log n + 14 ≤ Real.log (1 / (df2oPar d n δ).δe) := by
    unfold df2oPar
    set δ1 := min (δ / 3) (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) with hδ1_def
    have hδ1pos : 0 < δ1 := by
      rw [hδ1_def]
      refine lt_min_iff.mpr ⟨div_pos hδ0 (by norm_num), div_pos hexp_pos ?_⟩
      positivity
    have hδ1_le : δ1 ≤ Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3) := min_le_right _ _
    have hpos_right : 0 < Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3) :=
      div_pos hexp_pos (by positivity)
    have h_inv_δ1_ge : ((d : ℝ) * (n : ℝ)) ^ 3 * Real.exp 14 ≤ 1 / δ1 := by
      have h_one_div : 1 / (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) ≤ 1 / δ1 :=
        (one_div_le_one_div hpos_right hδ1pos).mpr hδ1_le
      have h_eq : 1 / (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) = ((d : ℝ) * (n : ℝ)) ^ 3 * Real.exp 14 := by
        field_simp [hexp_pos.ne', show ((d : ℝ) * (n : ℝ)) ^ 3 ≠ 0 from by positivity]
        calc
          1 = Real.exp 0 := by norm_num
          _ = Real.exp ((-14 : ℝ) + 14) := by norm_num
          _ = Real.exp (-14) * Real.exp 14 := by rw [Real.exp_add]
      rw [h_eq] at h_one_div
      exact h_one_div
    have h_inv_δe_ge : (n : ℝ) * Real.exp 14 ≤ 1 / (4 * δ1 / (5 * (n : ℝ))) := by
      have h_eq : 1 / (4 * δ1 / (5 * (n : ℝ))) = (5 * (n : ℝ) / 4) * (1 / δ1) := by
        field_simp [hδ1pos.ne', show (n : ℝ) ≠ 0 from by linarith]
      rw [h_eq]
      have h_mul_ge : (n : ℝ) * Real.exp 14 ≤ (5 * (n : ℝ) / 4) * (((d : ℝ) * (n : ℝ)) ^ 3 * Real.exp 14) := by
        have h_ineq : (n : ℝ) ≤ (5 * (n : ℝ) / 4) * (((d : ℝ) * (n : ℝ)) ^ 3) := by
          have h_dn_cube_ge_one : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := hcube_ge_one
          nlinarith
        nlinarith
      have h_mul_ge2 : (5 * (n : ℝ) / 4) * (((d : ℝ) * (n : ℝ)) ^ 3 * Real.exp 14) ≤
                      (5 * (n : ℝ) / 4) * (1 / δ1) := by
        nlinarith
      nlinarith
    have h_n_exp14_pos : 0 < (n : ℝ) * Real.exp 14 := mul_pos hnpos hexp14_pos
    have h_log_ineq : Real.log ((n : ℝ) * Real.exp 14) ≤ Real.log (1 / (4 * δ1 / (5 * (n : ℝ)))) :=
      Real.log_le_log h_n_exp14_pos h_inv_δe_ge
    have h_log_eq : Real.log ((n : ℝ) * Real.exp 14) = Real.log (n : ℝ) + 14 := by
      rw [Real.log_mul (by linarith : (n : ℝ) ≠ 0) hexp14_pos.ne', Real.log_exp 14]
    rw [h_log_eq] at h_log_ineq
    simpa [Nat.cast_ofNat] using h_log_ineq
  exact And.intro hδe_pos (And.intro hδe_lt_one h_log)

/-- `L ≥ 504`, `0 ≤ L_g ≤ L`. -/
theorem par_Le (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) :
    504 ≤ (df2oPar d n δ).Le ∧ 0 ≤ df2Lg (df2oPar d n δ) n ∧ df2Lg (df2oPar d n δ) n ≤ (df2oPar d n δ).Le := by
  have hpar := par_de d n δ hd hn hδ0
  rcases hpar with ⟨hδe_pos, hδe_lt_one, hlog⟩
  have h_one_div_δe_pos : 1 ≤ 1 / (df2oPar d n δ).δe :=
    one_le_one_div hδe_pos hδe_lt_one.le
  have h_log_inv_δe_nonneg : 0 ≤ Real.log (1 / (df2oPar d n δ).δe) :=
    Real.log_nonneg h_one_div_δe_pos
  have h_log_n_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have h_log_14_le_14 : Real.log (14 : ℝ) ≤ 14 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (14 : ℝ))
    linarith
  have h_log_14_plus_log_n_le : Real.log (14 : ℝ) + Real.log (n : ℝ) ≤ Real.log (1 / (df2oPar d n δ).δe) := by
    linarith
  have h_504_le_Le : 504 ≤ (df2oPar d n δ).Le := by
    have hdef : (df2oPar d n δ).Le = df2C0 * Real.log (1 / (df2oPar d n δ).δe) := rfl
    rw [hdef]
    have h_df2C0 : df2C0 = (36 : ℝ) := rfl
    rw [h_df2C0]
    have h_log_inv_δe_ge_14 : (14 : ℝ) ≤ Real.log (1 / (df2oPar d n δ).δe) := by
      linarith
    have h504 : (504 : ℝ) = (36 : ℝ) * (14 : ℝ) := by norm_num
    rw [h504]
    exact mul_le_mul_of_nonneg_left h_log_inv_δe_ge_14 (by norm_num)
  have h_0_le_df2Lg : 0 ≤ df2Lg (df2oPar d n δ) n := by
    dsimp [df2Lg]
    have hone : (1 : ℝ) ≤ 14 * (n : ℝ) / (df2oPar d n δ).δe := by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.one_pos.trans_le hn)
      have hnum' : (1 : ℝ) ≤ 14 * (n : ℝ) := by
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      -- Since δe < 1, dividing by δe increases the value: 14*n/δe ≥ 14*n ≥ 1
      calc
        (1 : ℝ) ≤ 14 * (n : ℝ) := hnum'
        _ = (14 * (n : ℝ) / (df2oPar d n δ).δe) * (df2oPar d n δ).δe := by
          field_simp
        _ ≤ (14 * (n : ℝ) / (df2oPar d n δ).δe) * 1 := by
          gcongr
        _ = 14 * (n : ℝ) / (df2oPar d n δ).δe := by ring
    exact Real.log_nonneg hone
  have h_df2Lg_le_Le : df2Lg (df2oPar d n δ) n ≤ (df2oPar d n δ).Le := by
    dsimp [df2Lg]
    have hδe_ne_zero : (df2oPar d n δ).δe ≠ 0 := by linarith
    have h14n_ne_zero : 14 * (n : ℝ) ≠ 0 := by
      have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_pos.trans_le hn).ne'
      positivity
    have h_neg_log : -Real.log ((df2oPar d n δ).δe) = Real.log (1 / (df2oPar d n δ).δe) := by
      calc
        -Real.log ((df2oPar d n δ).δe) = Real.log (((df2oPar d n δ).δe)⁻¹) := by rw [← Real.log_inv]
        _ = Real.log (1 / (df2oPar d n δ).δe) := by rw [inv_eq_one_div]
    have h_eq : Real.log (14 * (n : ℝ) / (df2oPar d n δ).δe) =
        Real.log (14 : ℝ) + Real.log (n : ℝ) + Real.log (1 / (df2oPar d n δ).δe) := by
      rw [Real.log_div h14n_ne_zero hδe_ne_zero]
      rw [Real.log_mul (by norm_num : (14 : ℝ) ≠ 0) (by
        have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_pos.trans_le hn).ne'
        exact hnpos)]
      -- Goal: Real.log 14 + Real.log n - Real.log (δe) = Real.log 14 + Real.log n + Real.log (1/δe)
      rw [sub_eq_add_neg, h_neg_log]
    rw [h_eq]
    have h_le : Real.log (14 : ℝ) + Real.log (n : ℝ) + Real.log (1 / (df2oPar d n δ).δe) ≤
        Real.log (1 / (df2oPar d n δ).δe) + Real.log (1 / (df2oPar d n δ).δe) := by
      linarith
    have h_le3 : Real.log (1 / (df2oPar d n δ).δe) + Real.log (1 / (df2oPar d n δ).δe) ≤
        (df2oPar d n δ).Le := by
      have hdef : (df2oPar d n δ).Le = df2C0 * Real.log (1 / (df2oPar d n δ).δe) := rfl
      rw [hdef]
      have h_df2C0 : df2C0 = (36 : ℝ) := rfl
      rw [h_df2C0]
      calc
        Real.log (1 / (df2oPar d n δ).δe) + Real.log (1 / (df2oPar d n δ).δe)
            = 2 * Real.log (1 / (df2oPar d n δ).δe) := by ring
        _ ≤ 36 * Real.log (1 / (df2oPar d n δ).δe) :=
          mul_le_mul_of_nonneg_right (by norm_num) h_log_inv_δe_nonneg
    linarith
  exact And.intro h_504_le_Le (And.intro h_0_le_df2Lg h_df2Lg_le_Le)

/-- `0 < λ < 1`, `0 < ε`, `σ² = 1/(8 L)`, `η κ ≥ 0`. -/
theorem par_misc (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) :
    0 < (df2oPar d n δ).lam ∧ (df2oPar d n δ).lam < 1 ∧ 0 < (df2oPar d n δ).eps ∧
      (df2oPar d n δ).sig2 = 1 / (8 * (df2oPar d n δ).Le) ∧ 0 ≤ (df2oPar d n δ).eta * (df2oPar d n δ).kap := by
  set p := df2oPar d n δ with hp
  have hdpos_nat : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_one) hd
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_one) hn
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos_nat
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos_nat
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_exp_pos : 0 < Real.exp (-14) := Real.exp_pos _
  have h_denom_pos : 0 < ((d : ℝ) * (n : ℝ)) ^ 3 := by positivity
  have h_min_pos : 0 < min (δ / 3) (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) := by
    refine lt_min_iff.mpr ⟨?_, ?_⟩
    · linarith
    · exact div_pos h_exp_pos h_denom_pos
  have h_δ1_pos : 0 < p.δ1 := by
    rw [hp]
    unfold df2oPar
    exact h_min_pos
  have h_δ1_le : p.δ1 ≤ Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3 := by
    rw [hp]
    unfold df2oPar
    exact min_le_right _ _
  have h_δe_pos : 0 < p.δe := by
    rw [hp]
    unfold df2oPar
    positivity
  have h_δe_lt_one : p.δe < 1 := by
    rw [hp]
    unfold df2oPar
    have h_δ1_le_one : min (δ / 3) (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) ≤ 1 := by
      refine le_trans h_δ1_le ?_
      have h_exp_le_one : Real.exp (-14) ≤ 1 := by
        rw [Real.exp_neg]
        exact ((inv_lt_one₀ (Real.exp_pos 14)).mpr
          (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 14))).le
      have h_pow_ge_one : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
        have hprod : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by nlinarith
        have h_sq : (1 : ℝ)^2 ≤ ((d : ℝ) * (n : ℝ))^2 := by nlinarith
        calc
          (1 : ℝ) = (1 : ℝ) * (1 : ℝ)^2 := by norm_num
          _ ≤ ((d : ℝ) * (n : ℝ)) * ((d : ℝ) * (n : ℝ))^2 :=
            mul_le_mul hprod h_sq (by positivity) (by nlinarith)
          _ = ((d : ℝ) * (n : ℝ)) ^ 3 := by ring
      exact (div_le_one (by positivity)).mpr (by nlinarith)
    calc
      4 * min (δ / 3) (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) / (5 * (n : ℝ))
          ≤ 4 * 1 / (5 * (n : ℝ)) :=
        div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ 4 * 1 / (5 * 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
      _ = 4/5 := by norm_num
      _ < 1 := by norm_num
  have h_log_pos : 0 < Real.log (1 / p.δe) :=
    Real.log_pos (one_lt_one_div h_δe_pos h_δe_lt_one)
  have h_log_ge_14 : (14 : ℝ) ≤ Real.log (1 / p.δe) := by
    have h_ineq : Real.exp 14 ≤ 1 / p.δe := by
      have h_δe_bound : p.δe ≤ 4 * Real.exp (-14) / (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3) := by
        rw [hp]
        unfold df2oPar
        have h_min_le : min (δ / 3) (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) ≤
            Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3 := min_le_right _ _
        calc
          4 * min (δ / 3) (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) / (5 * (n : ℝ))
              ≤ 4 * (Real.exp (-14) / ((d : ℝ) * (n : ℝ)) ^ 3) / (5 * (n : ℝ)) :=
            div_le_div_of_nonneg_right (by nlinarith) (by positivity)
          _ = 4 * Real.exp (-14) / (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3) := by ring
      have h_denom_bound : (4 : ℝ) ≤ 5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3 := by
        have hprod : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by nlinarith
        have hcube : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
          have h_sq : (1 : ℝ)^2 ≤ ((d : ℝ) * (n : ℝ))^2 := by nlinarith
          calc
            (1 : ℝ) = (1 : ℝ) * (1 : ℝ)^2 := by norm_num
            _ ≤ ((d : ℝ) * (n : ℝ)) * ((d : ℝ) * (n : ℝ))^2 :=
              mul_le_mul hprod h_sq (by positivity) (by nlinarith)
            _ = ((d : ℝ) * (n : ℝ)) ^ 3 := by ring
        nlinarith
      have h_inv : 1 / (4 * Real.exp (-14) / (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3)) ≤ 1 / p.δe := by
        refine (one_div_le_one_div ?_ ?_).mpr h_δe_bound
        · positivity
        · positivity
      have h_compute : 1 / (4 * Real.exp (-14) / (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3)) =
          (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3) / (4 * Real.exp (-14)) := by
        field_simp
      rw [h_compute] at h_inv
      have h_exp_14_le : Real.exp 14 ≤ (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3) / (4 * Real.exp (-14)) := by
        calc
          Real.exp 14 = (Real.exp (-14))⁻¹ := by
            rw [Real.exp_neg, inv_inv]
          _ = 1 / Real.exp (-14) := by simp
          _ = (4 : ℝ) / (4 * Real.exp (-14)) := by field_simp
          _ ≤ (5 * (n : ℝ) * ((d : ℝ) * (n : ℝ)) ^ 3) / (4 * Real.exp (-14)) :=
            div_le_div_of_nonneg_right h_denom_bound (by positivity)
      exact le_trans h_exp_14_le h_inv
    have h_log_exp : Real.log (Real.exp 14) = (14 : ℝ) := Real.log_exp 14
    have h_log_le : Real.log (Real.exp 14) ≤ Real.log (1 / p.δe) :=
      Real.log_le_log (Real.exp_pos _) h_ineq
    linarith
  have h_Le_pos : 0 < p.Le := by
    have h_eq : p.Le = 36 * Real.log (1 / p.δe) := by
      rw [hp]
      unfold df2oPar
      rfl
    rw [h_eq]
    have hlog : 0 < Real.log (1 / p.δe) := h_log_pos
    positivity
  have h_Le_ge_504 : (504 : ℝ) ≤ p.Le := by
    have h_eq : p.Le = 36 * Real.log (1 / p.δe) := by
      rw [hp]
      unfold df2oPar
      rfl
    rw [h_eq]
    have h : (36 : ℝ) * (14 : ℝ) ≤ (36 : ℝ) * Real.log (1 / p.δe) := by
      gcongr
    have h_504 : (504 : ℝ) = (36 : ℝ) * (14 : ℝ) := by norm_num
    rw [h_504]
    exact h
  have h_lam_pos : 0 < p.lam := by
    have h_eq : p.lam = 1 / (df2oClam * (d : ℝ) * p.Le ^ 2) := by
      rw [hp]
      unfold df2oPar
      rfl
    rw [h_eq]
    have hpos : 0 < df2oClam * (d : ℝ) * p.Le ^ 2 := by
      have : 0 < df2oClam := by unfold df2oClam; norm_num
      positivity
    exact div_pos (by norm_num) hpos
  have h_lam_lt_one : p.lam < 1 := by
    have h_eq : p.lam = 1 / (df2oClam * (d : ℝ) * p.Le ^ 2) := by
      rw [hp]
      unfold df2oPar
      rfl
    rw [h_eq]
    have h_denom_gt_one : (1 : ℝ) < df2oClam * (d : ℝ) * p.Le ^ 2 := by
      have h_sq : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := by
        have h0 : (0 : ℝ) ≤ (504 : ℝ) := by norm_num
        have h0' : (0 : ℝ) ≤ p.Le := by positivity
        nlinarith
      have h_clam_pos : 0 < df2oClam := by unfold df2oClam; norm_num
      have h_prod : (725 : ℝ) * (1 : ℝ) * ((504 : ℝ) ^ 2) ≤ df2oClam * (d : ℝ) * p.Le ^ 2 := by
        have : df2oClam = (725 : ℝ) := by unfold df2oClam; rfl
        rw [this]
        have h_mul1 : (725 : ℝ) * (1 : ℝ) ≤ (725 : ℝ) * (d : ℝ) := by
          gcongr
        have h_mul2 : (725 : ℝ) * (d : ℝ) * ((504 : ℝ) ^ 2) ≤ (725 : ℝ) * (d : ℝ) * p.Le ^ 2 := by
          gcongr
        nlinarith
      have h_gt : (1 : ℝ) < (725 : ℝ) * (1 : ℝ) * ((504 : ℝ) ^ 2) := by norm_num
      linarith
    have h := (one_div_lt_one_div (by
      have hpos : 0 < df2oClam := by unfold df2oClam; norm_num
      positivity
    ) (by norm_num : (0 : ℝ) < 1)).mpr h_denom_gt_one
    simpa using h
  have h_eps_pos : 0 < p.eps := by
    have h_eq : p.eps = 20 * df2oClam * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 / Real.sqrt (n : ℝ) := by
      rw [hp]
      unfold df2oPar
      rfl
    rw [h_eq]
    have h_clam_pos : 0 < df2oClam := by unfold df2oClam; norm_num
    have h_sqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
    have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have h_pow5_pos : 0 < p.Le ^ 5 := pow_pos h_Le_pos 5
    positivity
  have h_sig2_eq : p.sig2 = 1 / (8 * p.Le) := by
    rw [hp]
    unfold df2oPar
    rfl
  have h_eta_kap_nonneg : 0 ≤ p.eta * p.kap := by
    have h_eta_nonneg : 0 ≤ p.eta := by
      rw [hp]
      unfold df2oPar
      refine div_nonneg ?_ ?_
      · exact Real.sqrt_nonneg _
      · refine mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have h_kap_nonneg : 0 ≤ p.kap := by
      rw [hp]
      unfold df2oPar
      norm_num
    exact mul_nonneg h_eta_nonneg h_kap_nonneg
  exact ⟨h_lam_pos, h_lam_lt_one, h_eps_pos, h_sig2_eq, h_eta_kap_nonneg⟩

/-- The budget of one round: `2 exp(-L_g) = δ_e/(7n)`. -/
theorem two_exp_Lg (p : Df2OPar) (n : ℕ) (hn : 1 ≤ n) (hde : 0 < p.δe) :
    2 * Real.exp (-df2Lg p n) = p.δe / (7 * n) := by
  have hnpos : 0 < (n : ℝ) := by
    have : 0 < (n : ℕ) := Nat.one_pos.trans_le hn
    exact_mod_cast this
  have hpos : 0 < 14 * (n : ℝ) / p.δe := by
    positivity
  rw [df2Lg]
  rw [Real.exp_neg, Real.exp_log hpos]
  field_simp [hnpos.ne.symm, hde.ne.symm]
  ring

/-- Pi costs no more than the budget of a round: `exp(-2 L (√L - 2)²) ≤ 2 exp(-L_g)` for `L_g ≤ L`, `L ≥ 504`. -/
theorem pi_le_budget (Le Lg : ℝ) (hLe : 504 ≤ Le) (hLg : Lg ≤ Le) :
    Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2)) ≤ 2 * Real.exp (-Lg) := by
  have hLe_pos : 0 ≤ Le := by linarith
  have h_sqrt_Le_ge_22 : 22 ≤ Real.sqrt Le := by
    calc
      22 = Real.sqrt ((22 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt 504 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ Real.sqrt Le := Real.sqrt_le_sqrt hLe
  have h_diff_ge_20 : 20 ≤ Real.sqrt Le - 2 := by linarith
  have h_sq_ge_400 : (400 : ℝ) ≤ (Real.sqrt Le - 2) ^ 2 := by
    have h_nonneg : 0 ≤ Real.sqrt Le - 2 := by linarith
    nlinarith
  have h_key : Lg ≤ 2 * Le * (Real.sqrt Le - 2) ^ 2 := by
    nlinarith
  have h_exp_le : Real.exp (-(2 * Le * (Real.sqrt Le - 2) ^ 2)) ≤ Real.exp (-Lg) := by
    apply (Real.exp_le_exp.mpr ?_)
    linarith
  have h_exp_pos : 0 < Real.exp (-Lg) := Real.exp_pos _
  nlinarith

end AdversarialBco.Poly.EvGY
