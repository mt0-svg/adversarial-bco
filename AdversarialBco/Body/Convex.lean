/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Convexity, projection, extension and the first-order condition of the entropic cloud

`grad_chord`, `hess_nonneg_of_convex`, `exists_proj`, `ec_S4`, `hasDerivAt_log_abs_det_comp`, `lipExt_lipschitz`,
`continuous_det_clm` and `ec_first_order`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal


theorem AdversarialBco.Body.grad_chord {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (F' : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hFc : ConvexOn ℝ Set.univ F) (g : EuclideanSpace ℝ (Fin d))
    (hF : HasFDerivAt F F' g) (u : EuclideanSpace ℝ (Fin d)) (R Γ s : ℝ) (hR : 0 < R)
    (hΓ : F (R • u) ≤ F 0 - Γ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (F g - F 0) / R + Γ / R * s ≤ F' ((1 / R) • g - s • u) := by
  set p := (s * R) • u with hp
  have hp_mem : p ∈ Set.univ := Set.mem_univ _
  have h0_mem : (0 : EuclideanSpace ℝ (Fin d)) ∈ Set.univ := Set.mem_univ _
  have hRu_mem : (R • u) ∈ Set.univ := Set.mem_univ _
  have ha : 0 ≤ 1 - s := by linarith
  have hb : 0 ≤ s := hs0
  have hab : (1 - s) + s = 1 := by ring
  have hconv := hFc.2 h0_mem hRu_mem ha hb hab
  -- hconv : F ((1 - s) • 0 + s • (R • u)) ≤ (1 - s) • F 0 + s • F (R • u)
  have h_simp : (1 - s) • (0 : EuclideanSpace ℝ (Fin d)) + s • (R • u) = p := by
    simp [hp, smul_zero, smul_smul, add_comm]
  rw [h_simp] at hconv
  -- hconv : F p ≤ (1 - s) • F 0 + s • F (R • u)
  have h_bound : (1 - s) • F 0 + s • F (R • u) ≤ F 0 - s * Γ := by
    have : (1 - s) • F 0 + s • F (R • u) = F 0 + s * (F (R • u) - F 0) := by ring
    rw [this]
    have h_diff : F (R • u) - F 0 ≤ -Γ := by linarith
    nlinarith
  have hp_le : F p ≤ F 0 - s * Γ := le_trans hconv h_bound
  -- gradient inequality at g toward p
  have h_grad : F g + F' (p - g) ≤ F p :=
    AdversarialBco.convexOn_ge_of_hasFDerivAt F F' hFc g hF p
  have h_grad' : F g - F p ≤ F' (g - p) := by
    have := h_grad
    -- F g + F' (p - g) ≤ F p
    -- F' (p - g) = -F' (g - p) by linearity
    have h_linear : F' (p - g) = -F' (g - p) := by
      rw [← neg_sub, map_neg]
    linarith
  have h_main : F g - F 0 + s * Γ ≤ F' (g - p) := by
    linarith
  -- Now compute F' ((1/R) • g - s • u) = (1/R) * F' (g - p)
  have h_scale : F' ((1 / R) • g - s • u) = (1 / R) * F' (g - p) := by
    calc
      F' ((1 / R) • g - s • u) = F' ((1 / R) • g) - F' (s • u) := by rw [map_sub]
      _ = ((1 / R) • F' g) - ((s : ℝ) • F' u) := by simp [map_smul]
      _ = (1 / R) * F' g - s * F' u := by simp [smul_eq_mul]
      _ = (1 / R) * (F' g - F' ((s * R) • u)) := by
        field_simp [hR.ne.symm]
        simp [map_smul, mul_assoc]
      _ = (1 / R) * (F' g - F' (p)) := by
        simp [hp]
      _ = (1 / R) * F' (g - p) := by rw [map_sub]
  rw [h_scale]
  -- Now we need: (F g - F 0) / R + Γ / R * s ≤ (1/R) * F' (g - p)
  -- From h_main: F g - F 0 + s * Γ ≤ F' (g - p)
  -- Divide both sides by R > 0
  have h_div : (F g - F 0 + s * Γ) / R ≤ F' (g - p) / R := by
    exact (div_le_div_of_nonneg_right h_main (by linarith))
  -- But we need: (F g - F 0) / R + Γ / R * s ≤ (1/R) * F' (g - p)
  -- Note that (1/R) * F' (g - p) = F' (g - p) / R
  -- And (F g - F 0 + s * Γ) / R = (F g - F 0) / R + (s * Γ) / R = (F g - F 0) / R + Γ / R * s
  calc
    (F g - F 0) / R + Γ / R * s = (F g - F 0 + s * Γ) / R := by ring
    _ ≤ F' (g - p) / R := h_div
    _ = (1 / R) * F' (g - p) := by ring


theorem AdversarialBco.Body.hess_nonneg_of_convex {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (G'' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hG : ∀ g, HasFDerivAt G (G' g) g) (hG' : ∀ g, HasFDerivAt G' (G'' g) g) (hGc : ConvexOn ℝ Set.univ G)
    (g v : EuclideanSpace ℝ (Fin d)) : 0 ≤ G'' g v v := by
  -- define the affine map t ↦ g + t·v
  let φ_map : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
    AffineMap.mk' (fun (t : ℝ) => g + t • v) (LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) v) (0 : ℝ) (by
      intro p'
      simp [vsub_eq_sub, add_comm])
  -- φ(t) = G(g + t·v) is convex on ℝ
  have h_φ_conv : ConvexOn ℝ Set.univ (G ∘ φ_map) := by
    have h := ConvexOn.comp_affineMap φ_map hGc
    simpa using h
  -- φ is differentiable everywhere
  have h_φ_diff : ∀ x ∈ Set.univ, DifferentiableAt ℝ (G ∘ φ_map) x := by
    intro x hx
    have h_line_deriv : HasDerivAt φ_map v x := by
      have := (AffineMap.hasDerivAt φ_map (x := x))
      simpa [φ_map] using this
    exact (hG (φ_map x)).differentiableAt.comp x h_line_deriv.differentiableAt
  -- the derivative of φ is monotone on ℝ
  have h_deriv_mono_on : MonotoneOn (deriv (G ∘ φ_map)) Set.univ :=
    ConvexOn.monotoneOn_deriv h_φ_conv h_φ_diff
  -- deriv φ = ψ where ψ(t) = G'(g + t·v) v
  have h_deriv_eq : deriv (G ∘ φ_map) = fun (t : ℝ) => G' (φ_map t) v := by
    ext t
    have h_diff_G : DifferentiableAt ℝ G (φ_map t) := (hG (φ_map t)).differentiableAt
    have h_diff_line : DifferentiableAt ℝ φ_map t :=
      (AffineMap.hasDerivAt φ_map (x := t)).differentiableAt
    rw [fderiv_comp_deriv t h_diff_G h_diff_line]
    have h_deriv_line : deriv φ_map t = v := by
      rw [AffineMap.deriv φ_map]
      simp [φ_map]
    have h_fderiv_G : fderiv ℝ G (φ_map t) = G' (φ_map t) :=
      (hG (φ_map t)).fderiv
    rw [h_fderiv_G, h_deriv_line]
  -- ψ is monotone on ℝ (since deriv φ = ψ and deriv φ is monotone on Set.univ)
  have h_ψ_mono_on : MonotoneOn (fun (t : ℝ) => G' (φ_map t) v) Set.univ := by
    rw [← h_deriv_eq]
    exact h_deriv_mono_on
  have h_ψ_mono : Monotone (fun (t : ℝ) => G' (φ_map t) v) :=
    (monotoneOn_univ (f := fun (t : ℝ) => G' (φ_map t) v)).mp h_ψ_mono_on
  -- ψ has derivative G'' g v v at 0
  have h_ψ_deriv : HasDerivAt (fun (t : ℝ) => G' (φ_map t) v) (G'' g v v) 0 := by
    have h_line_deriv : HasDerivAt φ_map v 0 := by
      have := (AffineMap.hasDerivAt φ_map (x := 0))
      simpa [φ_map] using this
    have h_G'_deriv : HasDerivAt (G' ∘ φ_map) ((G'' g) v) 0 := by
      have h := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hG' (φ_map 0)) h_line_deriv
      simpa [φ_map] using h
    have h_const : HasDerivAt (fun (_ : ℝ) => v) (0 : EuclideanSpace ℝ (Fin d)) 0 :=
      hasDerivAt_const (0 : ℝ) (c := v)
    have h_clm_apply := h_G'_deriv.clm_apply h_const
    simpa [φ_map, add_comm] using h_clm_apply
  -- apply the lemma: monotone function with derivative at a point has nonnegative derivative
  exact h_ψ_deriv.nonneg_of_monotone h_ψ_mono


theorem AdversarialBco.Body.exists_proj {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJc : IsCompact J)
    (hJv : Convex ℝ J) (hJn : J.Nonempty) :
    ∃ pr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), Continuous pr ∧ (∀ x, pr x ∈ J) ∧
      (∀ x, dist x (pr x) = Metric.infDist x J) ∧ ∀ x ∈ J, pr x = x := by
  have hJcomplete : IsComplete J := hJc.isComplete
  have h_exists : ∀ x : EuclideanSpace ℝ (Fin d), ∃ v ∈ J, ‖x - v‖ = ⨅ w : J, ‖x - (w : EuclideanSpace ℝ (Fin d))‖ := by
    intro x
    exact exists_norm_eq_iInf_of_complete_convex hJn hJcomplete hJv x
  -- choose a projection function pr
  let pr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => Classical.choose (h_exists x)
  have hpr_mem : ∀ x, pr x ∈ J := by
    intro x
    exact (Classical.choose_spec (h_exists x)).1
  have hpr_norm : ∀ x, ‖x - pr x‖ = ⨅ w : J, ‖x - (w : EuclideanSpace ℝ (Fin d))‖ := by
    intro x
    exact (Classical.choose_spec (h_exists x)).2
  have hpr_dist : ∀ x, dist x (pr x) = Metric.infDist x J := by
    intro x
    rw [Metric.infDist_eq_iInf]
    -- need: dist x (pr x) = ⨅ y : J, dist x y
    -- dist x (pr x) = ‖x - pr x‖ = ⨅ w : J, ‖x - w‖ = ⨅ y : J, dist x y
    calc
      dist x (pr x) = ‖x - pr x‖ := by rw [dist_eq_norm]
      _ = ⨅ w : J, ‖x - (w : EuclideanSpace ℝ (Fin d))‖ := hpr_norm x
      _ = ⨅ w : J, dist x (w : EuclideanSpace ℝ (Fin d)) := by
        simp_rw [dist_eq_norm]
  have hpr_fix : ∀ x ∈ J, pr x = x := by
    intro x hx
    have hdist : dist x (pr x) = Metric.infDist x J := hpr_dist x
    have hinf0 : Metric.infDist x J = 0 := Metric.infDist_zero_of_mem hx
    have hdist0 : dist x (pr x) = 0 := by rw [hpr_dist x, hinf0]
    rw [dist_eq_norm] at hdist0
    have hnorm0 : ‖x - pr x‖ = 0 := hdist0
    have hzero : x - pr x = 0 := by
      rwa [norm_eq_zero] at hnorm0
    exact (sub_eq_zero.mp hzero).symm
  have h_lipschitz : LipschitzWith 1 pr := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    -- need: dist (pr x) (pr y) ≤ (1 : NNReal) * dist x y
    -- equivalently: ‖pr x - pr y‖ ≤ ‖x - y‖
    have hx_char : ∀ w ∈ J, inner ℝ ((x : EuclideanSpace ℝ (Fin d)) - pr x) (w - pr x) ≤ 0 := by
      intro w hw
      have := (norm_eq_iInf_iff_real_inner_le_zero hJv (hpr_mem x)).mp (hpr_norm x) w hw
      exact this
    have hy_char : ∀ w ∈ J, inner ℝ ((y : EuclideanSpace ℝ (Fin d)) - pr y) (w - pr y) ≤ 0 := by
      intro w hw
      have := (norm_eq_iInf_iff_real_inner_le_zero hJv (hpr_mem y)).mp (hpr_norm y) w hw
      exact this
    have h1 : inner ℝ (x - pr x) (pr y - pr x) ≤ 0 := hx_char (pr y) (hpr_mem y)
    have h2 : inner ℝ (y - pr y) (pr x - pr y) ≤ 0 := hy_char (pr x) (hpr_mem x)
    have hsum : inner ℝ (x - pr x) (pr y - pr x) + inner ℝ (y - pr y) (pr x - pr y) ≤ 0 := by linarith
    -- rewrite h2: inner ℝ (y - pr y) (pr x - pr y) = -inner ℝ (y - pr y) (pr y - pr x)
    have h2' : inner ℝ (y - pr y) (pr x - pr y) = -inner ℝ (y - pr y) (pr y - pr x) := by
      have : pr x - pr y = -(pr y - pr x) := by abel
      rw [this, inner_neg_right]
    rw [h2'] at hsum
    -- hsum: inner ℝ (x - pr x) (pr y - pr x) - inner ℝ (y - pr y) (pr y - pr x) ≤ 0
    -- i.e., inner ℝ ((x - pr x) - (y - pr y)) (pr y - pr x) ≤ 0
    have hinner_sub : inner ℝ ((x - pr x) - (y - pr y)) (pr y - pr x) ≤ 0 := by
      rw [inner_sub_left]
      linarith
    -- (x - pr x) - (y - pr y) = (x - y) - (pr x - pr y)
    have hsub_eq : (x - pr x) - (y - pr y) = (x - y) - (pr x - pr y) := by
      abel
    rw [hsub_eq] at hinner_sub
    -- Let p := pr x - pr y, q := x - y. Then inner ℝ (q - p) (-p) ≤ 0
    -- i.e., -inner ℝ (q - p) p ≤ 0, so inner ℝ (q - p) p ≥ 0
    -- inner ℝ q p - inner ℝ p p ≥ 0, so inner ℝ q p ≥ ‖p‖²
    have hinner_rearr : inner ℝ ((x - y) - (pr x - pr y)) (-(pr x - pr y)) ≤ 0 := by
      simpa [sub_eq_add_neg] using hinner_sub
    rw [inner_neg_right] at hinner_rearr
    have h_nonneg : 0 ≤ inner ℝ ((x - y) - (pr x - pr y)) (pr x - pr y) := by linarith
    have h_expand : inner ℝ ((x - y) - (pr x - pr y)) (pr x - pr y) =
        inner ℝ (x - y) (pr x - pr y) - inner ℝ (pr x - pr y) (pr x - pr y) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    rw [h_expand] at h_nonneg
    have h_norm_sq_le : ‖pr x - pr y‖ ^ 2 ≤ inner ℝ (x - y) (pr x - pr y) := by
      have : inner ℝ (pr x - pr y) (pr x - pr y) = ‖pr x - pr y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      linarith
    -- By Cauchy-Schwarz: inner ℝ (x - y) (pr x - pr y) ≤ ‖x - y‖ * ‖pr x - pr y‖
    have h_cauchy : inner ℝ (x - y) (pr x - pr y) ≤ ‖x - y‖ * ‖pr x - pr y‖ := by
      calc
        inner ℝ (x - y) (pr x - pr y) ≤ |inner ℝ (x - y) (pr x - pr y)| := le_abs_self _
        _ ≤ ‖x - y‖ * ‖pr x - pr y‖ := abs_real_inner_le_norm _ _
    have h_norm_sq_le' : ‖pr x - pr y‖ ^ 2 ≤ ‖x - y‖ * ‖pr x - pr y‖ := by
      linarith
    -- If ‖pr x - pr y‖ = 0, then trivially ≤. Otherwise divide.
    by_cases hzero : ‖pr x - pr y‖ = 0
    · rw [dist_eq_norm, hzero, dist_eq_norm, NNReal.coe_one, one_mul]
      exact norm_nonneg _
    · have hpos : 0 < ‖pr x - pr y‖ := by
        apply lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      have hineq : ‖pr x - pr y‖ ≤ ‖x - y‖ := by
        nlinarith
      rw [dist_eq_norm]
      -- hineq gives ‖pr x - pr y‖ ≤ ‖x - y‖
      -- need: dist (pr x) (pr y) ≤ (1 : NNReal) * dist x y
      -- i.e., ‖pr x - pr y‖ ≤ 1 * ‖x - y‖
      simpa [dist_eq_norm, NNReal.coe_one] using hineq
  have h_cont : Continuous pr := h_lipschitz.continuous
  refine ⟨pr, h_cont, hpr_mem, hpr_dist, hpr_fix⟩



theorem AdversarialBco.Body.ec_S4 {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hGc : ConvexOn ℝ Set.univ G)
    (L : ℝ≥0) (hGL : LipschitzWith L G) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    G b ≤ ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hS_meas : Measurable S := S.continuous.measurable
  have hS_aemeas : AEMeasurable S (stdGaussian E) := hS_meas.aemeasurable
  let μ := (stdGaussian E).map S
  have h_prob : IsProbabilityMeasure μ :=
    ((MeasureTheory.Measure.isProbabilityMeasure_map_iff hS_aemeas).mpr inferInstance)
  have h_neg_map : (stdGaussian E).map (fun w => -w) = stdGaussian E := by
    simpa using (stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := E)))
  have h_symm : μ.map (fun w => -w) = μ := by
    dsimp [μ]
    rw [Measure.map_map measurable_neg hS_meas]
    have h_comp : (fun w => -w) ∘ S = S ∘ (fun w => -w) := by
      ext x; simp [S.map_neg]
    rw [h_comp, ← Measure.map_map hS_meas measurable_neg, h_neg_map]
  have h_int_bound : ∀ g, |G (b + S g)| ≤ (|G b| + (L : ℝ) * ‖S‖) * Real.exp (1 * ‖g‖) := by
    intro g
    have h_lip : |G (b + S g) - G b| ≤ (L : ℝ) * ‖S g‖ := by
      have := hGL.norm_sub_le (b + S g) b
      simpa [add_sub_cancel_left] using this
    have h_norm_Sg : ‖S g‖ ≤ ‖S‖ * ‖g‖ := S.le_opNorm g
    have h_exp : ‖g‖ ≤ Real.exp ‖g‖ := by
      have := Real.add_one_le_exp ‖g‖
      linarith
    have h_one_le_exp : (1 : ℝ) ≤ Real.exp ‖g‖ := by
      have h := Real.add_one_le_exp ‖g‖
      have h_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
      linarith
    have h_tri : |G (b + S g)| ≤ |G b| + |G (b + S g) - G b| := by
      calc
        |G (b + S g)| = |(G (b + S g) - G b) + G b| := by rw [sub_add_cancel]
        _ ≤ |G (b + S g) - G b| + |G b| := abs_add_le _ _
        _ = |G b| + |G (b + S g) - G b| := add_comm _ _
    have hL_nonneg : 0 ≤ (L : ℝ) := by exact L.2
    have hS_norm_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
    calc
      |G (b + S g)| ≤ |G b| + |G (b + S g) - G b| := h_tri
      _ ≤ |G b| + (L : ℝ) * ‖S g‖ := by nlinarith
      _ ≤ |G b| + (L : ℝ) * (‖S‖ * ‖g‖) := by
        have htemp : (L : ℝ) * ‖S g‖ ≤ (L : ℝ) * (‖S‖ * ‖g‖) :=
          mul_le_mul_of_nonneg_left h_norm_Sg hL_nonneg
        nlinarith
      _ = |G b| + (L : ℝ) * ‖S‖ * ‖g‖ := by ring
      _ = |G b| * 1 + (L : ℝ) * ‖S‖ * ‖g‖ := by ring
      _ ≤ |G b| * Real.exp ‖g‖ + (L : ℝ) * ‖S‖ * ‖g‖ := by
        have htemp : |G b| * 1 ≤ |G b| * Real.exp ‖g‖ :=
          mul_le_mul_of_nonneg_left h_one_le_exp (abs_nonneg _)
        nlinarith
      _ ≤ |G b| * Real.exp ‖g‖ + (L : ℝ) * ‖S‖ * Real.exp ‖g‖ := by
        have htemp : (L : ℝ) * ‖S‖ * ‖g‖ ≤ (L : ℝ) * ‖S‖ * Real.exp ‖g‖ :=
          mul_le_mul_of_nonneg_left h_exp (mul_nonneg hL_nonneg hS_norm_nonneg)
        nlinarith
      _ = (|G b| + (L : ℝ) * ‖S‖) * Real.exp ‖g‖ := by ring
      _ = (|G b| + (L : ℝ) * ‖S‖) * Real.exp (1 * ‖g‖) := by ring
  have h_cont_f : Continuous (fun g => G (b + S g)) :=
    hGL.continuous.comp ((continuous_const.add continuous_id).comp S.continuous)
  have h_cont_g : Continuous (fun w => G (b + w)) :=
    hGL.continuous.comp (continuous_const.add continuous_id)
  have h_int_std : Integrable (fun g => G (b + S g)) (stdGaussian E) := by
    refine AdversarialBco.Body.integrable_of_abs_le_exp (fun g => G (b + S g))
      h_cont_f.aestronglyMeasurable (|G b| + (L : ℝ) * ‖S‖) 1 h_int_bound
  have h_int_μ : Integrable (fun w => G (b + w)) μ := by
    have h_aestrong : AEStronglyMeasurable (fun w => G (b + w)) ((stdGaussian E).map S) :=
      h_cont_g.aestronglyMeasurable
    exact ((integrable_map_measure h_aestrong hS_aemeas).mpr h_int_std)
  have h_jensen := AdversarialBco.jensen_symm μ h_symm G hGc b h_int_μ
  have h_integral : ∫ w, G (b + w) ∂μ = ∫ g, G (b + S g) ∂(stdGaussian E) := by
    calc
      ∫ w, G (b + w) ∂μ = ∫ w, G (b + w) ∂((stdGaussian E).map S) := rfl
      _ = ∫ g, G (b + S g) ∂(stdGaussian E) := by
        rw [MeasureTheory.integral_map hS_aemeas h_cont_g.aestronglyMeasurable]
  calc
    G b ≤ ∫ w, G (b + w) ∂μ := h_jensen
    _ = ∫ g, G (b + S g) ∂(stdGaussian E) := h_integral


theorem AdversarialBco.Body.hasDerivAt_log_abs_det_comp {d : ℕ}
    (S E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) :
    (∀ᶠ t in nhds (0 : ℝ), LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) ∧
    HasDerivAt (fun t : ℝ => Real.log |LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
      (LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let S_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := S
  let E'_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := E'
  let M : Matrix (Fin d) (Fin d) ℝ := LinearMap.toMatrix b b E'_lin
  have h_detS : LinearMap.det S_lin ≠ 0 := hS
  -- Relate the goal expression to S_lin and E'_lin
  have h_coe_comp (t : ℝ) : ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      S_lin ∘ₗ ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    ext x; rfl
  have h_coe_id_smul (t : ℝ) : ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) + t • ((E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    ext x; rfl
  -- For any t, det(S ∘ (id + tE')) = det S * det(id + tE')
  have h_det_factor (t : ℝ) : LinearMap.det (S_lin ∘ₗ ((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
      LinearMap.det S_lin * LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) := by
    rw [LinearMap.det_comp]
  -- The matrix of id + tE' is 1 + tM
  have h_matrix (t : ℝ) : LinearMap.toMatrix b b (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
      (1 : Matrix (Fin d) (Fin d) ℝ) + t • M := by
    rw [h_coe_id_smul t]
    have h_id : LinearMap.toMatrix b b (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 := by
      simp [LinearMap.toMatrix_id b]
    have h_add : LinearMap.toMatrix b b ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) + t • (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
        LinearMap.toMatrix b b (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) +
        t • LinearMap.toMatrix b b (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
      simp [map_add, map_smul]
    simp [M, E'_lin, map_add, map_smul, LinearMap.toMatrix_id b]
  -- det(1 + tM) is continuous in t and equals 1 at t=0
  have h_det_pos_near_zero : ∀ᶠ t in nhds (0 : ℝ), (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det > 0) := by
    have h_cont : Continuous fun t : ℝ => ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det := by
      apply Continuous.matrix_det
      continuity
    have h_zero : ((1 : Matrix (Fin d) (Fin d) ℝ) + (0 : ℝ) • M).det = 1 := by
      simp
    have h_pos : (0 : ℝ) < ((1 : Matrix (Fin d) (Fin d) ℝ) + (0 : ℝ) • M).det := by
      rw [h_zero]
      norm_num
    -- Since det(1 + tM) is continuous and positive at 0, it's positive near 0
    have h_cont_at : ContinuousAt (fun t : ℝ => ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det) 0 :=
      h_cont.continuousAt
    have h_event := h_cont_at.eventually (eventually_gt_nhds h_pos)
    exact h_event
  -- First conjunct: the determinant is eventually nonzero
  have h_first : ∀ᶠ t in nhds (0 : ℝ), LinearMap.det
      ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    filter_upwards [h_det_pos_near_zero] with t ht
    rw [h_coe_comp t, h_det_factor t]
    have h_detM_ne_zero : LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b, h_matrix t]
      linarith
    exact mul_ne_zero h_detS h_detM_ne_zero
  -- Second conjunct: the derivative
  have h_second : HasDerivAt (fun t : ℝ => Real.log |LinearMap.det
      ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
      (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
    -- Near 0, we can simplify the expression
    have h_eventually_eq : ∀ᶠ t in nhds (0 : ℝ), Real.log |LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
        Real.log |LinearMap.det S_lin| +
        Real.log (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det) := by
      filter_upwards [h_det_pos_near_zero] with t ht
      rw [h_coe_comp t, h_det_factor t]
      have h_detM_eq : LinearMap.det (((ContinuousLinearMap.id ℝ _ + t • E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) = ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det := by
        rw [← LinearMap.det_toMatrix b, h_matrix t]
      rw [h_detM_eq]
      have hpos : ((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det > 0 := ht
      rw [abs_mul, abs_of_pos hpos]
      rw [Real.log_mul (abs_pos.mpr h_detS).ne.symm (by linarith)]
    -- Now compute the derivative using the simplified expression
    refine (HasDerivAt.congr_of_eventuallyEq (𝕜 := ℝ) (F := ℝ) ?_ h_eventually_eq)
    -- The derivative of log |det S| + log(det(1 + tM)) at 0
    have h_const : HasDerivAt (fun _ : ℝ => Real.log |LinearMap.det S_lin|) (0 : ℝ) (0 : ℝ) := by
      apply hasDerivAt_const (0 : ℝ) (Real.log |LinearMap.det S_lin|)
    -- For log(det(1 + tM)), use hasDerivAt_log_det on matrix 1
    have h_log_det : HasDerivAt (fun t : ℝ => Real.log (((1 : Matrix (Fin d) (Fin d) ℝ) + t • M).det))
        (((1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * M).trace) 0 := by
      apply AdversarialBco.hasDerivAt_log_det (1 : Matrix (Fin d) (Fin d) ℝ) M
      simp
    -- ((1 : Matrix _ _ ℝ)⁻¹ * M).trace = M.trace
    have h_trace : ((1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ * M).trace = M.trace := by
      simp
    -- M.trace = trace(E')
    have h_trace_M : M.trace = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) E'_lin := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b E'_lin]
    rw [h_trace, h_trace_M] at h_log_det
    -- Now combine: derivative of sum = sum of derivatives
    have h_sum := h_const.add h_log_det
    -- h_sum : HasDerivAt ((fun x => Real.log |det S_lin|) + (fun t => Real.log (1 + t • M).det)) (0 + trace E'_lin) 0
    -- Goal: HasDerivAt (fun x => Real.log |det S_lin| + Real.log (1 + x • M).det) (trace ↑E') 0
    -- The function parts are definitionally equal, so we can coerce
    have h_sum' : HasDerivAt (fun (x : ℝ) => Real.log |LinearMap.det S_lin| + Real.log (1 + x • M).det)
        ((0 : ℝ) + (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d))) E'_lin) (0 : ℝ) := h_sum
    simpa [E'_lin, add_zero] using h_sum'
  exact And.intro h_first h_second

namespace AdversarialBco.Body

/-- The Lipschitz extension is `L`-Lipschitz. -/
theorem lipExt_lipschitz {F : Type*} [NormedAddCommGroup F] (J : Set F) (hJ : J.Nonempty) (f : F → ℝ)
    (hfb : BddBelow (f '' J)) (L : ℝ≥0) : LipschitzWith L (AdversarialBco.lipExt J f L) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := AdversarialBco.lipExt_le J hJ f hfb (L : ℝ) L.2 x y
  have h2 := AdversarialBco.lipExt_le J hJ f hfb (L : ℝ) L.2 y x
  rw [dist_comm y x] at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- The determinant is continuous on the operators of `EuclideanSpace ℝ (Fin d)`. -/
theorem continuous_det_clm {d : ℕ} :
    Continuous fun S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  ContinuousLinearMap.continuous_det

/-- The first-order condition along `t ↦ (b + t db, S (1 + t E))`. -/
theorem ec_first_order {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hG'c : Continuous G') (L : ℝ≥0) (hGL : LipschitzWith L G) (lam : ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hdet : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (hmin : ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
          ∫ g, G (b' + S' g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
    (db : EuclideanSpace ℝ (Fin d)) (E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ g, G' (b + S g) (db + S (E' g)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      lam * LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  obtain ⟨hev, hlog⟩ := hasDerivAt_log_abs_det_comp S E' hdet
  have hGL' : ∀ x, ‖G' x‖ ≤ L := fun x => by
    rw [← (hG x).fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hGL
  have hGi : ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      Integrable (fun g => G (b' + S' g)) γ := fun b' S' => by
    have h1 : LipschitzWith (L * ‖S'‖₊) (fun g => G (b' + S' g)) := AdversarialBco.lipschitzWith_comp_affine G L hGL b' S'
    exact AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm h1.continuous.aestronglyMeasurable
      (AdversarialBco.Gauss.abs_le_of_lipschitz h1)
  have hint : HasDerivAt (fun t : ℝ => ∫ g, G ((b + S g) + t • (db + S (E' g))) ∂γ)
      (∫ g, G' (b + S g) (db + S (E' g)) ∂γ) 0 := by
    refine AdversarialBco.hasDerivAt_integral_affine γ G G' L hG hGL' hG'c (fun g => b + S g)
      (fun g => db + S (E' g)) (by fun_prop) (by fun_prop) ?_ (hGi b S)
    refine AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm (by fun_prop) (A := ‖db‖) (B := ‖S‖ * ‖E'‖)
      fun g => ?_
    rw [abs_norm]
    calc ‖db + S (E' g)‖ ≤ ‖db‖ + ‖S (E' g)‖ := norm_add_le _ _
      _ ≤ ‖db‖ + ‖S‖ * (‖E'‖ * ‖g‖) := by gcongr; exact (S.le_opNorm _).trans (by gcongr; exact E'.le_opNorm g)
      _ = ‖db‖ + ‖S‖ * ‖E'‖ * ‖g‖ := by ring
  have heq : ∀ t : ℝ, (fun g => G ((b + S g) + t • (db + S (E' g)))) =
      fun g => G ((b + t • db) + (S.comp (ContinuousLinearMap.id ℝ _ + t • E')) g) := fun t => by
    funext g
    congr 1
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, ContinuousLinearMap.id_apply, _root_.smul_apply,
      map_add, map_smul, smul_add]
    abel
  set f : ℝ → ℝ := fun t => ∫ g, G ((b + t • db) + (S.comp (ContinuousLinearMap.id ℝ _ + t • E')) g) ∂γ -
    lam * Real.log |LinearMap.det
        ((S.comp (ContinuousLinearMap.id ℝ _ + t • E') : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| with hf
  have hderiv : HasDerivAt f (∫ g, G' (b + S g) (db + S (E' g)) ∂γ -
      lam * LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
    have h1 := hint
    simp_rw [heq] at h1
    exact h1.sub (hlog.const_mul lam)
  have hf0 : f 0 = ∫ g, G (b + S g) ∂γ -
      lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
    simp [hf]
  have hlocmin : IsLocalMin f 0 := by
    filter_upwards [hev] with t ht
    rw [hf0]
    exact hmin _ _ ht
  have := hlocmin.hasDerivAt_eq_zero hderiv
  linarith

end AdversarialBco.Body
