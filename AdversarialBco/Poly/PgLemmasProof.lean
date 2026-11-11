/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgLemmas
public import AdversarialBco.Poly.PosGaussProof
public import AdversarialBco.Body.Dil
public import AdversarialBco.Body.Smooth
public import AdversarialBco.Body2.Gauss2

@[expose] public section

/-!
# The lemmas of Theorem 8.3: proofs

Proofs of the 22 interface statements of `AdversarialBco/Poly/PgLemmas.lean` (Proposition A, Lemma B with a general
relative error `η`, the domain facts (D1), (D4), (D5), the log-determinant concavity, the curvature bound, the moments
of Lemma E, the pathwise bound of Lemma SGD), from the results of `AdversarialBco/Poly/PosGaussProof.lean`.

The leaves, then the assemblies, one theorem per `Prop` named after it in lower camel case,
close the file.
-/

open AdversarialBco.Poly MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Topology
open Filter

/-! ## From AdversarialBco/Poly/PosGaussProof.lean -/

theorem AdversarialBco.Poly.posF_convex {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ) (hK : AdversarialBco.Poly.IsPosBody K r0 α)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (∃ L : ℝ≥0, LipschitzWith L (AdversarialBco.Poly.posF K μ A)) ∧ ConvexOn ℝ Set.univ (AdversarialBco.Poly.posF K μ A) :=
  posF_facts hK μ A

/-! ## Leaves -/

theorem AdversarialBco.Poly.bisect_spec (P : ℝ → Prop) (p lo hi : ℝ) (hP : ∀ s, P s ↔ p ≤ s)
    (hlo : lo ≤ p) (hhi : p ≤ hi) (j : ℕ) :
    (AdversarialBco.Poly.bisect P lo hi j).1 ≤ p ∧ p ≤ (AdversarialBco.Poly.bisect P lo hi j).2 ∧
      (AdversarialBco.Poly.bisect P lo hi j).2 - (AdversarialBco.Poly.bisect P lo hi j).1 = (hi - lo) / 2 ^ j := by
  induction' j with j ih
  · refine ⟨hlo, hhi, ?_⟩
    simp [AdversarialBco.Poly.bisect]
  · rcases ih with ⟨hI1, hI2, hlen⟩
    simp only [AdversarialBco.Poly.bisect]
    split_ifs with hPm
    · have hp_le_m : p ≤ ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2 :=
        (hP _).mp hPm
      have hlen' : ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2 -
          (AdversarialBco.Poly.bisect P lo hi j).1 = (hi - lo) / 2 ^ (j + 1) := by
        calc
          ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2 -
              (AdversarialBco.Poly.bisect P lo hi j).1
              = ((AdversarialBco.Poly.bisect P lo hi j).2 - (AdversarialBco.Poly.bisect P lo hi j).1) / 2 := by ring
          _ = ((hi - lo) / 2 ^ j) / 2 := by rw [hlen]
          _ = (hi - lo) / 2 ^ (j + 1) := by ring
      exact ⟨hI1, hp_le_m, hlen'⟩
    · have hm_le_p : ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2 ≤ p := by
        have h_not : ¬ (p ≤ ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2) := by
          rwa [← hP _]
        exact le_of_lt (lt_of_not_ge h_not)
      have hlen' : (AdversarialBco.Poly.bisect P lo hi j).2 -
          ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2 = (hi - lo) / 2 ^ (j + 1) := by
        calc
          (AdversarialBco.Poly.bisect P lo hi j).2 -
              ((AdversarialBco.Poly.bisect P lo hi j).1 + (AdversarialBco.Poly.bisect P lo hi j).2) / 2
              = ((AdversarialBco.Poly.bisect P lo hi j).2 - (AdversarialBco.Poly.bisect P lo hi j).1) / 2 := by ring
          _ = ((hi - lo) / 2 ^ j) / 2 := by rw [hlen]
          _ = (hi - lo) / 2 ^ (j + 1) := by ring
      exact ⟨hm_le_p, hI2, hlen'⟩

theorem AdversarialBco.Poly.gauge_bounds (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : Convex ℝ K) (h1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K)
    (hρK : K ⊆ Metric.closedBall 0 ρ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ / ρ ≤ gauge K x ∧ gauge K x ≤ ‖x‖ := by
  have hρ_nonneg : 0 ≤ ρ := hρ.le
  have h_ball_mem_nhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds 0 :=
    Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hK_mem_nhds : K ∈ nhds 0 :=
    Filter.mem_of_superset h_ball_mem_nhds h1
  have hK_absorbent : Absorbent ℝ K := absorbent_nhds_zero hK_mem_nhds
  have h_ball_absorbent : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    absorbent_nhds_zero h_ball_mem_nhds
  have h_right : gauge K x ≤ ‖x‖ := by
    have h_mono := gauge_mono h_ball_absorbent h1 x
    have h_gauge_ball : gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x = ‖x‖ := by
      calc
        gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x = ‖x‖ / 1 := gauge_closedBall (by norm_num : (0 : ℝ) ≤ 1) x
        _ = ‖x‖ := by simp
    calc
      gauge K x ≤ gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x := h_mono
      _ = ‖x‖ := h_gauge_ball
  have h_left : ‖x‖ / ρ ≤ gauge K x := by
    have h_mono := gauge_mono hK_absorbent hρK x
    have h_gauge_ball : gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ) x = ‖x‖ / ρ :=
      gauge_closedBall hρ_nonneg x
    calc
      ‖x‖ / ρ = gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ) x := by rw [h_gauge_ball]
      _ ≤ gauge K x := h_mono
  exact And.intro h_left h_right

theorem AdversarialBco.Poly.sgd_pathwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (proj : E → E) (hproj : ∀ y, ∀ z ∈ D, ‖proj y - z‖ ≤ ‖y - z‖)
    (xs : E) (hxs : xs ∈ D) (s Δ : ℝ) (hs : 0 < s) (x v : ℕ → E) (hx : ∀ t, x (t + 1) = proj (x t - s • v t))
    (hx0 : ‖x 0 - xs‖ ≤ Δ) (N : ℕ) :
    ∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫ ≤ Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v t‖ ^ 2 := by
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have h2s_pos : 0 < 2 * s := by linarith
  have hx0_sq : ‖x 0 - xs‖ ^ 2 ≤ Δ ^ 2 := by
    have h := norm_nonneg (x 0 - xs)
    nlinarith
  -- Per-step inequality from projection
  have h_step (t : ℕ) : 2 * s * ⟪v t, x t - xs⟫ ≤ ‖x t - xs‖ ^ 2 - ‖x (t + 1) - xs‖ ^ 2 + s ^ 2 * ‖v t‖ ^ 2 := by
    have hproj_ineq : ‖x (t + 1) - xs‖ ≤ ‖(x t - s • v t) - xs‖ := by
      rw [hx t]
      exact hproj (x t - s • v t) xs hxs
    have h_sq : ‖x (t + 1) - xs‖ ^ 2 ≤ ‖(x t - s • v t) - xs‖ ^ 2 := by
      have h := mul_self_le_mul_self (norm_nonneg _) hproj_ineq
      simpa [sq] using h
    have h_expand : ‖(x t - s • v t) - xs‖ ^ 2 = ‖x t - xs‖ ^ 2 - 2 * s * ⟪v t, x t - xs⟫ + s ^ 2 * ‖v t‖ ^ 2 := by
      calc
        ‖(x t - s • v t) - xs‖ ^ 2 = ‖(x t - xs) - s • v t‖ ^ 2 := by abel
        _ = ‖x t - xs‖ ^ 2 - 2 * inner ℝ (x t - xs) (s • v t) + ‖s • v t‖ ^ 2 := by rw [norm_sub_sq_real]
        _ = ‖x t - xs‖ ^ 2 - 2 * (s * inner ℝ (x t - xs) (v t)) + ‖s • v t‖ ^ 2 := by rw [inner_smul_right]
        _ = ‖x t - xs‖ ^ 2 - 2 * s * inner ℝ (x t - xs) (v t) + ‖s • v t‖ ^ 2 := by ring
        _ = ‖x t - xs‖ ^ 2 - 2 * s * ⟪v t, x t - xs⟫ + ‖s • v t‖ ^ 2 := by rw [real_inner_comm]
        _ = ‖x t - xs‖ ^ 2 - 2 * s * ⟪v t, x t - xs⟫ + (s * ‖v t‖) ^ 2 := by
          simp [norm_smul, abs_of_nonneg hs_nonneg]
        _ = ‖x t - xs‖ ^ 2 - 2 * s * ⟪v t, x t - xs⟫ + s ^ 2 * ‖v t‖ ^ 2 := by ring
    nlinarith
  -- Sum the per-step inequality over t < N
  have h_sum : 2 * s * (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) ≤
      ‖x 0 - xs‖ ^ 2 - ‖x N - xs‖ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) := by
    induction' N with N ih
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith [h_step N, ih]
  -- Bound the RHS
  have h_bound : ‖x 0 - xs‖ ^ 2 - ‖x N - xs‖ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) ≤
      Δ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) := by
    have h_nonneg_sq : 0 ≤ ‖x N - xs‖ ^ 2 := pow_two_nonneg _
    nlinarith
  -- Combine
  have h_combined : 2 * s * (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) ≤ Δ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) := by
    nlinarith
  -- Divide by 2*s > 0
  have h_mul : (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) * (2 * s) ≤ Δ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) := by
    nlinarith
  calc
    (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) = ((∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) * (2 * s)) / (2 * s) := by
      field_simp [h2s_pos.ne.symm]
    _ ≤ (Δ ^ 2 + s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2)) / (2 * s) :=
      div_le_div_of_nonneg_right h_mul (by linarith)
    _ = Δ ^ 2 / (2 * s) + s / 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) := by
      field_simp [hs.ne.symm]

theorem AdversarialBco.Poly.gauge_le_iff_pos_mem {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hK : Convex ℝ K)
    (hKc : IsClosed K) (h1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K) (hρK : K ⊆ Metric.closedBall 0 ρ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) (s : ℝ) : (0 < s ∧ s⁻¹ • x ∈ K) ↔ gauge K x ≤ s := by
  have hK_nhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) := by
    apply Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
    exact h1
  have hK_absorbent : Absorbent ℝ K := absorbent_nhds_zero hK_nhds
  have hK0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K :=
    h1 (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  have hρ_nonneg : 0 ≤ ρ := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ := hρK hK0
    rw [Metric.mem_closedBall, dist_eq_norm] at h0
    simpa using h0
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρ_pos : 0 < ρ := by
    have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have hnorm_unit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hnorm_nonneg]
      field_simp [hx_norm_pos.ne.symm]
    have hu_mem : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa [sub_zero] using hnorm_unit.le
    have hu_mem_K : ‖x‖⁻¹ • x ∈ K := h1 hu_mem
    have hu_mem_closedBall : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ := hρK hu_mem_K
    rw [Metric.mem_closedBall, dist_eq_norm] at hu_mem_closedBall
    have hle : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ ρ := by simpa [sub_zero] using hu_mem_closedBall
    rw [hnorm_unit] at hle
    linarith
  constructor
  · rintro ⟨hs, hxK⟩
    have hx_smul : x ∈ s • K := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne.symm K x]
      exact hxK
    exact gauge_le_of_mem hs.le hx_smul
  · intro hg
    have hs_pos : 0 < s := by
      have hnorm : ‖x‖ / ρ ≤ gauge K x := le_gauge_of_subset_closedBall hK_absorbent hρ_nonneg hρK
      have hdiv_pos : 0 < ‖x‖ / ρ := div_pos hx_norm_pos hρ_pos
      linarith
    have hs_nonneg : 0 ≤ s := hs_pos.le
    have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_nonneg
    have hg_smul : gauge K (s⁻¹ • x) ≤ 1 := by
      calc
        gauge K (s⁻¹ • x) = s⁻¹ * gauge K x := by
          simpa [smul_eq_mul] using gauge_smul_of_nonneg hs_inv_nonneg x
        _ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hg hs_inv_nonneg
        _ = 1 := by field_simp [hs_pos.ne.symm]
    have h_mem_closure : s⁻¹ • x ∈ closure K :=
      ((gauge_le_one_iff_mem_closure hK hK_nhds).mp hg_smul)
    rw [hKc.closure_eq] at h_mem_closure
    exact ⟨hs_pos, h_mem_closure⟩

theorem AdversarialBco.Poly.opnorm_le_of_form {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (τ : ℝ) (hT : IsSelfAdjoint T)
    (h0 : ∀ v, 0 ≤ ⟪T v, v⟫) (h1 : ∀ v, ⟪T v, v⟫ ≤ τ * ‖v‖ ^ 2) (v : EuclideanSpace ℝ (Fin d)) : ‖T v‖ ≤ τ * ‖v‖ := by
  -- handle v = 0 case separately
  by_cases hv : v = 0
  · subst hv
    simp
  · -- v ≠ 0, so we can prove τ ≥ 0
    have hτ_nonneg : 0 ≤ τ := by
      have hpos : 0 < ‖v‖ ^ 2 := pow_pos ((norm_pos_iff.mpr hv)) 2
      have h0v := h0 v
      have h1v := h1 v
      nlinarith
    -- get symmetry from self-adjoint
    have hT_symm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫ := by
      have h := hT.isSymmetric
      intro x y
      exact h x y
    -- define B as a bilinear form using LinearMap.mk₂
    let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d)) :=
      LinearMap.mk₂ ℝ (fun x y => ⟪T x, y⟫)
        (by
          intro x₁ x₂ y
          simp [ContinuousLinearMap.map_add, inner_add_left]
        )
        (by
          intro c x y
          simp [inner_smul_left]
        )
        (by
          intro x y₁ y₂
          simp [inner_add_right]
        )
        (by
          intro c x y
          simp [inner_smul_right]
        )
    -- B is positive semidefinite
    have hB_nonneg : ∀ x, 0 ≤ (B x) x := by
      intro x
      simp [B, h0 x]
    -- B is symmetric
    have hB_symm : LinearMap.IsSymm B :=
      LinearMap.IsSymm.mk (by
        intro x y
        calc
          ⟪T x, y⟫ = ⟪x, T y⟫ := hT_symm x y
          _ = ⟪T y, x⟫ := by rw [real_inner_comm]
      )
    -- apply Cauchy-Schwarz for B
    have h_cauchy := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm v (T v)
    -- h_cauchy : (B v) (T v) ^ 2 ≤ (B v) v * (B (T v)) (T v)
    -- which expands to ⟪T v, T v⟫ ^ 2 ≤ ⟪T v, v⟫ * ⟪T (T v), T v⟫
    have h_cauchy' : ⟪T v, T v⟫ ^ 2 ≤ ⟪T v, v⟫ * ⟪T (T v), T v⟫ := by
      simpa [B] using h_cauchy
    -- from h1: ⟪T v, v⟫ ≤ τ * ‖v‖^2 and ⟪T (T v), T v⟫ ≤ τ * ‖T v‖^2
    have h_bound1 : ⟪T v, v⟫ ≤ τ * ‖v‖ ^ 2 := h1 v
    have h_bound2 : ⟪T (T v), T v⟫ ≤ τ * ‖T v‖ ^ 2 := h1 (T v)
    -- nonnegativity from h0
    have h_nonneg1 : 0 ≤ ⟪T v, v⟫ := h0 v
    have h_nonneg2 : 0 ≤ ⟪T (T v), T v⟫ := h0 (T v)
    -- nonnegativity of bounds
    have h_nonneg_A : 0 ≤ τ * ‖v‖ ^ 2 := by
      have h_nonneg_norm_sq : 0 ≤ ‖v‖ ^ 2 := pow_two_nonneg _
      nlinarith
    have h_nonneg_B : 0 ≤ τ * ‖T v‖ ^ 2 := by
      have h_nonneg_norm_sq : 0 ≤ ‖T v‖ ^ 2 := pow_two_nonneg _
      nlinarith
    -- combine inequalities
    have h_ineq : ‖T v‖ ^ 4 ≤ τ ^ 2 * (‖v‖ ^ 2 * ‖T v‖ ^ 2) := by
      have h_norm_sq : ⟪T v, T v⟫ = ‖T v‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [h_norm_sq] at h_cauchy'
      -- h_cauchy' : (‖T v‖ ^ 2) ^ 2 ≤ ⟪T v, v⟫ * ⟪T (T v), T v⟫
      have h_sq_sq : (‖T v‖ ^ 2) ^ 2 = ‖T v‖ ^ 4 := by ring
      rw [h_sq_sq] at h_cauchy'
      -- h_cauchy' : ‖T v‖ ^ 4 ≤ ⟪T v, v⟫ * ⟪T (T v), T v⟫
      have h_mul : ⟪T v, v⟫ * ⟪T (T v), T v⟫ ≤ (τ * ‖v‖ ^ 2) * (τ * ‖T v‖ ^ 2) :=
        mul_le_mul h_bound1 h_bound2 h_nonneg2 h_nonneg_A
      nlinarith
    -- Now we have ‖T v‖ ^ 4 ≤ τ ^ 2 * (‖v‖ ^ 2 * ‖T v‖ ^ 2)
    -- If T v = 0, the conclusion is trivial
    by_cases hTv : T v = 0
    · rw [hTv]
      have h_nonneg_norm_v : 0 ≤ ‖v‖ := norm_nonneg _
      simp [mul_nonneg hτ_nonneg h_nonneg_norm_v]
    · -- T v ≠ 0, so ‖T v‖ > 0
      have hposTv : 0 < ‖T v‖ ^ 2 := pow_pos ((norm_pos_iff.mpr hTv)) 2
      -- divide both sides of h_ineq by ‖T v‖ ^ 2
      have h_ineq2 : ‖T v‖ ^ 2 ≤ τ ^ 2 * ‖v‖ ^ 2 := by
        nlinarith
      -- since τ ≥ 0 and ‖v‖ ≥ 0 and ‖T v‖ ≥ 0, we can take square roots
      have h_nonneg_norm_v : 0 ≤ ‖v‖ := norm_nonneg _
      have h_nonneg_norm_Tv : 0 ≤ ‖T v‖ := norm_nonneg _
      have h_nonneg_τ : 0 ≤ τ := hτ_nonneg
      -- use sq_le_sq₀ or mul_self_le_mul_self_iff
      have h_sq : ‖T v‖ ^ 2 ≤ (τ * ‖v‖) ^ 2 := by
        nlinarith
      -- now use sq_le_sq₀ to get ‖T v‖ ≤ τ * ‖v‖
      have h_result := (sq_le_sq₀ h_nonneg_norm_Tv (mul_nonneg h_nonneg_τ h_nonneg_norm_v)).mp h_sq
      exact h_result

open Classical in
/-- The bisection map `f_j(x)` is measurable into `ℝ × ℝ`. -/
theorem AdversarialBco.Poly.piTilde_f_measurable {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hK : IsClosed K) (j : ℕ) :
    Measurable (fun (x : EuclideanSpace ℝ (Fin d)) =>
      AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j) := by
  induction' j with j ih
  · -- base case j = 0
    simp only [AdversarialBco.Poly.bisect]
    refine Measurable.prodMk ?_ ?_
    · -- ‖x‖ / ρ
      refine (measurable_norm.div ?_)
      exact measurable_const
    · -- ‖x‖
      exact measurable_norm
  · -- inductive step
    simp only [AdversarialBco.Poly.bisect]
    -- I x = bisect ... j x : ℝ × ℝ
    let I := fun (x : EuclideanSpace ℝ (Fin d)) =>
      AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j
    have hI : Measurable I := ih
    let m : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ((I x).1 + (I x).2) / 2
    have hm : Measurable m := by
      dsimp [m]
      refine (measurable_fst.comp hI).add (measurable_snd.comp hI) |>.div ?_
      exact measurable_const
    have hS : MeasurableSet {x | 0 < m x ∧ (m x)⁻¹ • x ∈ K} := by
      refine MeasurableSet.inter ?_ ?_
      · -- {x | 0 < m x}
        refine measurableSet_lt measurable_const hm
      · -- {x | (m x)⁻¹ • x ∈ K}
        have hpre : Measurable (fun (x : EuclideanSpace ℝ (Fin d)) => (m x)⁻¹ • x) :=
          Measurable.smul (M := ℝ) (Measurable.inv hm) measurable_id
        exact hK.measurableSet.preimage hpre
    refine Measurable.ite hS ?_ ?_
    · -- then branch: (I x).1, m x)
      refine Measurable.prodMk ?_ ?_
      · exact measurable_fst.comp hI
      · exact hm
    · -- else branch: (m x, (I x).2)
      refine Measurable.prodMk ?_ ?_
      · exact hm
      · exact measurable_snd.comp hI

open Classical in
theorem AdversarialBco.Poly.piTilde_measurable (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hK : IsClosed K) (j : ℕ) :
    Measurable (AdversarialBco.Poly.piTilde K ρ j) := by
  unfold AdversarialBco.Poly.piTilde
  refine Measurable.ite ?_ ?_ ?_
  · -- {x | x = 0}
    exact (MeasurableSingletonClass.measurableSet_singleton (0 : EuclideanSpace ℝ (Fin d)))
  · -- then branch: 0
    exact measurable_const
  · -- else branch: (f_j x).2
    have hf := AdversarialBco.Poly.piTilde_f_measurable K ρ hK j
    exact measurable_snd.comp hf

theorem AdversarialBco.Poly.convex_fderiv_subgrad {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F) (x y : EuclideanSpace ℝ (Fin d))
    (hx : DifferentiableAt ℝ F x) : F x + fderiv ℝ F x (y - x) ≤ F y := by
  set g : ℝ → EuclideanSpace ℝ (Fin d) := fun t => x + t • (y - x) with hg_def
  have h_conv : ConvexOn ℝ Set.univ (F ∘ g) := by
    let φ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      { toFun := fun t => x + t • (y - x)
        linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
        map_vadd' := by
          intro t s
          simp [add_smul, vadd_eq_add, add_assoc, add_comm] }
    have := hF.comp_affineMap φ
    have h_preimage : φ ⁻¹' (Set.univ : Set (EuclideanSpace ℝ (Fin d))) = Set.univ := by
      simp
    have h_eq : φ = g := by
      ext t
      simp [φ, g]
    simpa [h_preimage, h_eq] using this
  have hg0 : g 0 = x := by
    simp [g]
  have h_deriv : HasDerivAt (F ∘ g) (fderiv ℝ F x (y - x)) 0 := by
    have hFderiv : HasFDerivAt F (fderiv ℝ F x) (g 0) := by
      rw [hg0]
      exact hx.hasFDerivAt
    have hg_deriv : HasDerivAt g (y - x) 0 := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id' 0
      have h_smul : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
        simpa [one_smul] using HasDerivAt.smul_const h_id (y - x)
      simpa [g, add_comm] using HasDerivAt.add_const x h_smul
    exact hFderiv.comp_hasDerivAt 0 hg_deriv
  have h_diff : DifferentiableAt ℝ (F ∘ g) 0 :=
    h_deriv.differentiableAt
  have h0 : (0 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 0
  have h1 : (1 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 1
  have h01 : (0 : ℝ) < 1 := by norm_num
  have h_slope : deriv (F ∘ g) 0 ≤ slope (F ∘ g) (0 : ℝ) 1 :=
    h_conv.deriv_le_slope h0 h1 h01 h_diff
  have h_deriv_eq : deriv (F ∘ g) 0 = fderiv ℝ F x (y - x) :=
    h_deriv.deriv
  have h_slope_eq : slope (F ∘ g) (0 : ℝ) 1 = (F ∘ g) 1 - (F ∘ g) 0 := by
    simp [slope]
  rw [h_deriv_eq, h_slope_eq] at h_slope
  have hg0_val : (F ∘ g) 0 = F x := by simp [g]
  have hg1_val : (F ∘ g) 1 = F y := by simp [g]
  rw [hg0_val, hg1_val] at h_slope
  linarith

theorem AdversarialBco.Poly.det_id_add_rank_one {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    LinearMap.det ((ContinuousLinearMap.id ℝ _ + s • (innerSL ℝ u).smulRight u : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 + s * ‖u‖ ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) + s • (innerSL ℝ u).smulRight u : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).toLinearMap
  have hdet := LinearMap.det_toMatrix b f
  rw [← hdet]
  have hM : LinearMap.toMatrix b b f = 1 + Matrix.replicateCol (Fin 1) (s • (u : Fin d → ℝ)) * Matrix.replicateRow (Fin 1) (u : Fin d → ℝ) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Matrix.mul_apply]
    have h2 : b.repr u i = u i := by
      simp [b]
    have h3 : ⟪u, b j⟫ = u j := by
      have : b j = EuclideanSpace.basisFun (Fin d) ℝ j := rfl
      rw [this, EuclideanSpace.inner_basisFun_real]
    simp [f, h2, h3, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_assoc,
      Finsupp.single_apply, eq_comm]
  rw [hM]
  have hdetM := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (s • u.ofLp) u.ofLp
  -- hdetM : det (1 + replicateCol (Fin 1) (s • u.ofLp) * replicateRow (Fin 1) u.ofLp) = 1 + u.ofLp ⬝ᵥ (s • u.ofLp)
  -- hdetM gives us the determinant, we need to connect the RHS to 1 + s * ‖u‖ ^ 2
  apply hdetM.trans
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.mul_sum, sq, mul_left_comm]

theorem AdversarialBco.Poly.frobStat_main {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) :
    ∑ i, ∑ j, AdversarialBco.Poly.gstat g i j ^ 2 = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + d := by
  let s := ‖g‖ ^ 2
  have hs : s = ∑ i : Fin d, g i ^ 2 := by
    calc
      s = ‖g‖ ^ 2 := rfl
      _ = ∑ i : Fin d, g i ^ 2 := by
        simpa using EuclideanSpace.real_norm_sq_eq g
  have h_sum_sq : ∑ i : Fin d, ∑ j : Fin d, (g i * g j) ^ 2 = (∑ i : Fin d, g i ^ 2) * (∑ j : Fin d, g j ^ 2) := by
    calc
      ∑ i : Fin d, ∑ j : Fin d, (g i * g j) ^ 2
          = ∑ i : Fin d, ∑ j : Fin d, (g i ^ 2 * g j ^ 2) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        ring
      _ = (∑ i : Fin d, g i ^ 2) * (∑ j : Fin d, g j ^ 2) := by
        simp [Finset.sum_mul_sum]
  have h_sum_cross : ∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0) * (g i * g j) = ∑ i : Fin d, g i ^ 2 := by
    simp [Finset.sum_ite_eq, Finset.mem_univ, sq]
  have h_sum_delta : ∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0) = (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    ∑ i : Fin d, ∑ j : Fin d, (AdversarialBco.Poly.gstat g i j) ^ 2
        = ∑ i : Fin d, ∑ j : Fin d, (g i * g j - (if i = j then (1 : ℝ) else 0)) ^ 2 := by
      simp [AdversarialBco.Poly.gstat]
    _ = ∑ i : Fin d, ∑ j : Fin d, ((g i * g j) ^ 2 - 2 * (if i = j then (1 : ℝ) else 0) * (g i * g j) + (if i = j then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    _ = (∑ i : Fin d, ∑ j : Fin d, (g i * g j) ^ 2) - (∑ i : Fin d, ∑ j : Fin d, 2 * (if i = j then (1 : ℝ) else 0) * (g i * g j)) + (∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0)) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i : Fin d, ∑ j : Fin d, (g i * g j) ^ 2) - 2 * (∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0) * (g i * g j)) + (∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0)) := by
      simp [Finset.mul_sum]
    _ = ((∑ i : Fin d, g i ^ 2) * (∑ j : Fin d, g j ^ 2)) - 2 * (∑ i : Fin d, g i ^ 2) + (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) := by
      rw [h_sum_sq, h_sum_cross, h_sum_delta]
    _ = s * s - 2 * s + (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) := by
      rw [hs]
    _ = s ^ 2 - 2 * s + (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) := by ring
    _ = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) := by
      rw [show s ^ 2 = (‖g‖ ^ 2) ^ 2 by rfl, show (‖g‖ ^ 2) ^ 2 = ‖g‖ ^ 4 by ring]
    _ = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ) := by simp
    _ = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + d := by simp

theorem AdversarialBco.Poly.vecCS_main {d : ℕ} (ε : EuclideanSpace ℝ (Fin d) → ℝ) (hε : MemLp ε 2 (stdGaussian (EuclideanSpace ℝ (Fin d)))) :
    ‖∫ g, ε g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖ ^ 2 ≤ ∫ g, ε g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  set b := ∫ g, ε g • g ∂μ with hb
  have h_int_smul : Integrable (fun g => ε g • g) μ := by
    have h_id : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 2 μ :=
      IsGaussian.memLp_two_id
    have h_mem : MemLp (fun g => ε g • g) 1 μ :=
      MemLp.smul hε h_id
    exact h_mem.integrable (by norm_num : (1 : ENNReal) ≤ 1)
  have h_mem_inner : MemLp (fun g => ⟪b, g⟫) 2 μ :=
    (IsGaussian.memLp_two_id (μ := μ)).continuousLinearMap_comp (innerSL ℝ b)
  have h_int_inner : Integrable (fun g => ⟪b, g⟫) μ :=
    h_mem_inner.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h_int_prod : Integrable (fun g => ε g * ⟪b, g⟫) μ :=
    hε.integrable_mul h_mem_inner
  have h_int_sq_ε : Integrable (fun g => ε g ^ 2) μ :=
    hε.integrable_sq
  have h_int_sq_inner : Integrable (fun g => ⟪b, g⟫ ^ 2) μ :=
    h_mem_inner.integrable_sq
  have h_inner_eq : ∫ g, ε g * ⟪b, g⟫ ∂μ = ‖b‖ ^ 2 := by
    calc
      ∫ g, ε g * ⟪b, g⟫ ∂μ = ∫ g, ⟪b, ε g • g⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [inner_smul_right]
      _ = ⟪b, ∫ g, ε g • g ∂μ⟫ := integral_inner h_int_smul b
      _ = ⟪b, b⟫ := by rw [hb]
      _ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
  have h_inner_sq_eq : ∫ g, ⟪b, g⟫ ^ 2 ∂μ = ‖b‖ ^ 2 :=
    AdversarialBco.Body.integral_inner_sq b
  have h_nonneg_sq : 0 ≤ fun g => (ε g - ⟪b, g⟫) ^ 2 := by
    intro g
    apply pow_two_nonneg
  have h_nonneg : 0 ≤ ∫ g, (ε g - ⟪b, g⟫) ^ 2 ∂μ := integral_nonneg h_nonneg_sq
  have h_diff_mem : MemLp (fun g => ε g - ⟪b, g⟫) 2 μ :=
    hε.sub h_mem_inner
  have h_int_diff_sq : Integrable (fun g => (ε g - ⟪b, g⟫) ^ 2) μ :=
    h_diff_mem.integrable_sq
  have h_int_two_prod : Integrable (fun g => 2 * ε g * ⟪b, g⟫) μ := by
    simpa [mul_assoc] using h_int_prod.const_mul 2
  have h_int_diff : Integrable (fun g => ε g ^ 2 - 2 * ε g * ⟪b, g⟫) μ :=
    h_int_sq_ε.sub h_int_two_prod
  have h_expand : ∫ g, (ε g - ⟪b, g⟫) ^ 2 ∂μ = (∫ g, ε g ^ 2 ∂μ) - ‖b‖ ^ 2 := by
    calc
      ∫ g, (ε g - ⟪b, g⟫) ^ 2 ∂μ = ∫ g, (ε g ^ 2 - 2 * ε g * ⟪b, g⟫ + ⟪b, g⟫ ^ 2) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        ring
      _ = ∫ g, (ε g ^ 2 - 2 * ε g * ⟪b, g⟫) + ⟪b, g⟫ ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        ring
      _ = (∫ g, (ε g ^ 2 - 2 * ε g * ⟪b, g⟫) ∂μ) + (∫ g, ⟪b, g⟫ ^ 2 ∂μ) := integral_add h_int_diff h_int_sq_inner
      _ = ((∫ g, ε g ^ 2 ∂μ) - (∫ g, 2 * ε g * ⟪b, g⟫ ∂μ)) + (∫ g, ⟪b, g⟫ ^ 2 ∂μ) := by rw [integral_sub h_int_sq_ε h_int_two_prod]
      _ = ((∫ g, ε g ^ 2 ∂μ) - (∫ g, 2 * (ε g * ⟪b, g⟫) ∂μ)) + (∫ g, ⟪b, g⟫ ^ 2 ∂μ) := by ring
      _ = ((∫ g, ε g ^ 2 ∂μ) - 2 * (∫ g, ε g * ⟪b, g⟫ ∂μ)) + (∫ g, ⟪b, g⟫ ^ 2 ∂μ) := by rw [integral_const_mul 2 (fun g => ε g * ⟪b, g⟫)]
      _ = ((∫ g, ε g ^ 2 ∂μ) - 2 * (‖b‖ ^ 2)) + (‖b‖ ^ 2) := by rw [h_inner_eq, h_inner_sq_eq]
      _ = (∫ g, ε g ^ 2 ∂μ) - ‖b‖ ^ 2 := by ring
  have h_nonneg' : 0 ≤ (∫ g, ε g ^ 2 ∂μ) - ‖b‖ ^ 2 := by
    rw [← h_expand]
    exact h_nonneg
  linarith

theorem AdversarialBco.Poly.gauss_coord2 {d : ℕ} (i j : Fin d) :
    ∫ g, g i * g j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = if i = j then 1 else 0 := by
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d)]
  rw [integral_map (by fun_prop) (by fun_prop)]
  -- Goal: ∫ x, (WithLp.toLp 2 x) i * (WithLp.toLp 2 x) j ∂(Measure.pi fun _ => gaussianReal 0 1) = ...
  have h_simp : (fun (x : Fin d → ℝ) => ((WithLp.toLp 2 x) i) * ((WithLp.toLp 2 x) j)) =
      (fun x => x i * x j) := by
    ext x
    simp
  rw [h_simp]
  by_cases h : i = j
  · subst h
    -- Need: ∫ x, x i * x i ∂(Measure.pi fun _ => gaussianReal 0 1) = 1
    have h_int_sq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal (0 : ℝ) 1) = 1 := by
      have h_var : Var[id; gaussianReal (0 : ℝ) 1] = 1 := by
        simpa using ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1)
      have h_mean : ∫ x : ℝ, x ∂(gaussianReal (0 : ℝ) 1) = (0 : ℝ) := by
        simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
      have h_var_eq : Var[id; gaussianReal (0 : ℝ) 1] =
          ∫ x : ℝ, (x - ∫ y : ℝ, y ∂(gaussianReal (0 : ℝ) 1)) ^ 2 ∂(gaussianReal (0 : ℝ) 1) := by
        have h_ae : AEMeasurable id (gaussianReal (0 : ℝ) 1) := by fun_prop
        simpa using ProbabilityTheory.variance_eq_integral h_ae
      rw [h_mean] at h_var_eq
      have : (fun (x : ℝ) => (x - (0 : ℝ)) ^ 2) = (fun x => x ^ 2) := by
        ext x; simp
      rw [this] at h_var_eq
      rw [← h_var_eq, h_var]
    -- Use integral_fintype_prod_eq_prod: write x i * x i as product over all coordinates
    let f : Fin d → ℝ → ℝ := fun k => if k = i then (fun x => x * x) else (fun _ => 1)
    have h_int_prod : ∫ x : Fin d → ℝ, ∏ k : Fin d, f k (x k) ∂
        (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) =
        ∏ k : Fin d, ∫ x : ℝ, f k x ∂(gaussianReal (0 : ℝ) 1) :=
      integral_fintype_prod_eq_prod f
    have h_prod_simp : (∏ k : Fin d, ∫ x : ℝ, f k x ∂(gaussianReal (0 : ℝ) 1)) = 1 := by
      have h_fi : ∫ x : ℝ, f i x ∂(gaussianReal (0 : ℝ) 1) = 1 := by
        simpa [f, sq] using h_int_sq
      have h_fk : ∀ k, k ≠ i → ∫ x : ℝ, f k x ∂(gaussianReal (0 : ℝ) 1) = 1 := by
        intro k hk
        simp [f, hk, MeasureTheory.integral_const]
      have h_prod_univ : (∏ k : Fin d, ∫ x : ℝ, f k x ∂(gaussianReal (0 : ℝ) 1)) =
          (∏ k ∈ Finset.univ, ∫ x : ℝ, f k x ∂(gaussianReal (0 : ℝ) 1)) := by simp
      rw [h_prod_univ]
      refine (Finset.prod_eq_single i (fun k hk_mem hk_ne => h_fk k hk_ne) (fun h => ?_)).trans h_fi
      exfalso; exact h (Finset.mem_univ i)
    have h_eq : (fun (x : Fin d → ℝ) => x i * x i) =
        (fun x => ∏ k : Fin d, f k (x k)) := by
      ext x
      have h_prod_erase : (∏ k : Fin d, f k (x k)) =
          f i (x i) * (∏ k ∈ (Finset.univ.erase i), f k (x k)) := by
        calc
          (∏ k : Fin d, f k (x k)) = (∏ k ∈ Finset.univ, f k (x k)) := by simp
          _ = f i (x i) * (∏ k ∈ Finset.univ.erase i, f k (x k)) := by
            rw [← Finset.mul_prod_erase Finset.univ (fun k => f k (x k)) (Finset.mem_univ i)]
      rw [h_prod_erase]
      have h_fi : f i (x i) = x i * x i := by simp [f]
      have h_fk : ∀ k, k ∈ Finset.univ.erase i → f k (x k) = 1 := by
        intro k hk
        have hk_ne : k ≠ i := Finset.ne_of_mem_erase hk
        simp [f, hk_ne]
      rw [h_fi]
      -- Goal: x i * x i = (x i * x i) * ∏ k ∈ Finset.univ.erase i, f k (x k)
      -- Since f k (x k) = 1 for k ≠ i, the product is 1
      have h_prod_one : (∏ k ∈ Finset.univ.erase i, f k (x k)) = 1 := by
        refine Finset.prod_eq_one (fun k hk => h_fk k hk)
      rw [h_prod_one]
      simp
    rw [h_eq, h_int_prod, h_prod_simp]
    simp
  · -- i ≠ j case
    have h_indep : (fun (x : Fin d → ℝ) => x i) ⟂ᵢ[Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1]
        (fun (x : Fin d → ℝ) => x j) := by
      have h_iIndep : iIndepFun (fun (k : Fin d) (x : Fin d → ℝ) => x k)
          (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) := by
        have := iIndepFun_pi (μ := fun _ : Fin d => gaussianReal (0 : ℝ) 1)
          (X := fun _ => id) (fun k => (measurable_id.aemeasurable (μ := gaussianReal (0 : ℝ) 1)))
        simpa using this
      exact h_iIndep.indepFun h
    have h_ae_i : AEStronglyMeasurable (fun (x : Fin d → ℝ) => x i)
        (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) := by
      -- x i is the projection, which is measurable
      exact (measurable_pi_apply i).aestronglyMeasurable
    have h_ae_j : AEStronglyMeasurable (fun (x : Fin d → ℝ) => x j)
        (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) := by
      exact (measurable_pi_apply j).aestronglyMeasurable
    have h_integral := IndepFun.integral_mul_eq_mul_integral h_indep h_ae_i h_ae_j
    -- h_integral : ∫ x, (x i) * (x j) ∂... = (∫ x, x i ∂...) * (∫ x, x j ∂...)
    have h_int_i : ∫ x : Fin d → ℝ, x i ∂(Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) = 0 := by
      -- Use integral_map with the fact that (Measure.pi μ).map (eval i) = μ i
      have h_map := MeasureTheory.Measure.pi_map_eval (μ := fun _ : Fin d => gaussianReal (0 : ℝ) 1) i
      -- h_map : Measure.map (eval i) (Measure.pi μ) = (∏ j ∈ erase i, (μ j) univ) • μ i
      -- For probability measures, this simplifies to μ i
      have h_map_simp : (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1).map (fun x => x i) =
          gaussianReal (0 : ℝ) 1 := by
        -- Since gaussianReal 0 1 is a probability measure, (μ j) univ = 1
        simpa [show (gaussianReal (0 : ℝ) 1) Set.univ = 1 from by simp] using h_map
      calc
        ∫ x : Fin d → ℝ, x i ∂(Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1)
            = ∫ x : ℝ, x ∂((Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1).map (fun x => x i)) := by
          rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
        _ = ∫ x : ℝ, x ∂(gaussianReal (0 : ℝ) 1) := by rw [h_map_simp]
        _ = 0 := by simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    have h_int_j : ∫ x : Fin d → ℝ, x j ∂(Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1) = 0 := by
      have h_map := MeasureTheory.Measure.pi_map_eval (μ := fun _ : Fin d => gaussianReal (0 : ℝ) 1) j
      have h_map_simp : (Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1).map (fun x => x j) =
          gaussianReal (0 : ℝ) 1 := by
        simpa [show (gaussianReal (0 : ℝ) 1) Set.univ = 1 from by simp] using h_map
      calc
        ∫ x : Fin d → ℝ, x j ∂(Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1)
            = ∫ x : ℝ, x ∂((Measure.pi fun _ : Fin d => gaussianReal (0 : ℝ) 1).map (fun x => x j)) := by
          rw [integral_map (measurable_pi_apply j).aemeasurable (by fun_prop)]
        _ = ∫ x : ℝ, x ∂(gaussianReal (0 : ℝ) 1) := by rw [h_map_simp]
        _ = 0 := by simpa using ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    simpa [h_int_i, h_int_j, h] using h_integral

theorem AdversarialBco.Poly.gauss_isserlis {d : ℕ} (i j k l : Fin d) :
    ∫ g, g i * g j * g k * g l ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) + (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  have hP : ∀ a (g : EuclideanSpace ℝ (Fin d)), (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) g = g a :=
    fun a g => rfl
  have hPn : ∀ a, ‖(EuclideanSpace.proj a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ 1 := fun a =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      rw [hP, one_mul]
      exact PiLp.norm_apply_le g a
  have hga : ∀ a (g : EuclideanSpace ℝ (Fin d)), |g a| ≤ ‖g‖ := fun a g => by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le g a
  have hPs : ∀ a, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (EuclideanSpace.single i 1) =
      if i = a then 1 else 0 := fun a => by
    rw [hP]
    by_cases h : i = a
    · subst h
      simp
    · simp [h, Ne.symm h]
  set Φ' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun g =>
    (g j * g k) • EuclideanSpace.proj l + g l • (g j • EuclideanSpace.proj k + g k • EuclideanSpace.proj j) with hΦ'
  have hΦ : ∀ g, HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => y j * y k * y l) (Φ' g) g := fun g =>
    (((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt).mul
      ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt)).mul
      ((EuclideanSpace.proj l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt)
  have hx3 : ∀ x : ℝ, 0 ≤ x → x ^ 3 ≤ 6 * Real.exp (1 * x) := fun x hx => by
    have := Real.pow_div_factorial_le_exp x hx 3
    rw [one_mul]
    norm_num [Nat.factorial] at this
    linarith
  have hx2 : ∀ x : ℝ, 0 ≤ x → 3 * x ^ 2 ≤ 6 * Real.exp (1 * x) := fun x hx => by
    have := Real.pow_div_factorial_le_exp x hx 2
    rw [one_mul]
    norm_num [Nat.factorial] at this
    linarith
  have hb : ∀ g : EuclideanSpace ℝ (Fin d), |g j * g k * g l| ≤ 6 * Real.exp (1 * ‖g‖) := fun g => by
    rw [abs_mul, abs_mul]
    have hjk : |g j| * |g k| ≤ ‖g‖ * ‖g‖ := mul_le_mul (hga j g) (hga k g) (abs_nonneg _) (norm_nonneg _)
    have h3 : |g j| * |g k| * |g l| ≤ ‖g‖ * ‖g‖ * ‖g‖ :=
      mul_le_mul hjk (hga l g) (abs_nonneg _) (by positivity)
    have := hx3 ‖g‖ (norm_nonneg _)
    nlinarith
  have hb' : ∀ g, ‖Φ' g‖ ≤ 6 * Real.exp (1 * ‖g‖) := fun g => by
    have hjk : |g j| * |g k| ≤ ‖g‖ * ‖g‖ := mul_le_mul (hga j g) (hga k g) (abs_nonneg _) (norm_nonneg _)
    have e1 : |g j| * |g k| * ‖(EuclideanSpace.proj l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ ‖g‖ * ‖g‖ := by
      nlinarith [hPn l, norm_nonneg (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
        mul_nonneg (abs_nonneg (g j)) (abs_nonneg (g k))]
    have e2 : |g j| * ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ ‖g‖ := by
      nlinarith [hPn k, norm_nonneg (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), abs_nonneg (g j),
        hga j g]
    have e3 : |g k| * ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ ‖g‖ := by
      nlinarith [hPn j, norm_nonneg (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), abs_nonneg (g k),
        hga k g]
    have e4 := mul_le_mul (hga l g) (add_le_add e2 e3) (by positivity) (norm_nonneg _)
    have hn : ‖Φ' g‖ ≤ |g j| * |g k| * ‖(EuclideanSpace.proj l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ +
        |g l| * (|g j| * ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ +
          |g k| * ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖) := by
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_mul]
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := hx2 ‖g‖ (norm_nonneg _)
    nlinarith
  have hS := AdversarialBco.Body.stein_dir (fun y : EuclideanSpace ℝ (Fin d) => y j * y k * y l) Φ' hΦ 6 1 hb hb'
    (EuclideanSpace.single i 1)
  have hm : ∀ a, MemLp (fun g : EuclideanSpace ℝ (Fin d) => g a) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun a => (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp_memLp'
      (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))))
  have hpair : ∀ a b, Integrable (fun g : EuclideanSpace ℝ (Fin d) => g a * g b) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun a b => (hm a).integrable_mul (hm b)
  have eL : ∫ g, g i * g j * g k * g l ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ⟪EuclideanSpace.single i 1, g⟫ * (g j * g k * g l) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    congr 1
    funext g
    rw [EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    ring
  have eR : (fun g => Φ' g (EuclideanSpace.single i 1)) = fun g : EuclideanSpace ℝ (Fin d) =>
      (if i = l then (1 : ℝ) else 0) * (g j * g k) + (if i = k then (1 : ℝ) else 0) * (g j * g l) +
        (if i = j then (1 : ℝ) else 0) * (g k * g l) := by
    funext g
    simp only [hΦ', add_apply, smul_apply, smul_eq_mul, hPs]
    ring
  have i12 : Integrable (fun g : EuclideanSpace ℝ (Fin d) =>
      (if i = l then (1 : ℝ) else 0) * (g j * g k) + (if i = k then (1 : ℝ) else 0) * (g j * g l))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := ((hpair j k).const_mul _).add ((hpair j l).const_mul _)
  rw [eL, hS, eR, integral_add i12 ((hpair k l).const_mul _),
    integral_add ((hpair j k).const_mul _) ((hpair j l).const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, AdversarialBco.Poly.gauss_coord2, AdversarialBco.Poly.gauss_coord2,
    AdversarialBco.Poly.gauss_coord2]
  ring

open ENNReal in
theorem AdversarialBco.Poly.gstat_memLp {d : ℕ} (i j : Fin d) :
    MemLp (fun g => AdversarialBco.Poly.gstat g i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h_id4 : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 4
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 4 (by norm_num)
  let proj_i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj i
  let proj_j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj j
  have h_proj_i : MemLp (proj_i ∘ id) 4 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    proj_i.comp_memLp' h_id4
  have h_proj_j : MemLp (proj_j ∘ id) 4 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    proj_j.comp_memLp' h_id4
  have h_holder : HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := by
    have h := HolderTriple.of (4 : ℝ≥0∞) (4 : ℝ≥0∞)
    -- h : HolderTriple 4 4 ((4⁻¹ + 4⁻¹)⁻¹)
    -- We need to show ((4⁻¹ + 4⁻¹)⁻¹) = 2
    have h_eq : ((4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹)⁻¹ = (2 : ℝ≥0∞) := by
      have h_nnreal : (((4 : NNReal)⁻¹ + (4 : NNReal)⁻¹)⁻¹ : NNReal) = (2 : NNReal) := by norm_num
      have h4 : (4 : NNReal) ≠ 0 := by norm_num
      simpa [ENNReal.coe_inv h4, ENNReal.coe_add] using congrArg (fun x : NNReal => (x : ℝ≥0∞)) h_nnreal
    simpa [h_eq] using h
  have h_prod : MemLp ((proj_i ∘ id) * (proj_j ∘ id)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    h_proj_i.mul h_proj_j
  have h_const : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (if i = j then (1 : ℝ) else 0)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    memLp_const _
  have h_sub : MemLp ((proj_i ∘ id) * (proj_j ∘ id) - fun _ => (if i = j then (1 : ℝ) else 0)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    h_prod.sub h_const
  have h_eq : (fun g => AdversarialBco.Poly.gstat g i j) =
      (proj_i ∘ id) * (proj_j ∘ id) - fun _ => (if i = j then (1 : ℝ) else 0) := by
    ext g
    simp [AdversarialBco.Poly.gstat, proj_i, proj_j, EuclideanSpace.coe_proj]
  simpa [h_eq] using h_sub

theorem AdversarialBco.Poly.gstat_cov {d : ℕ} (i j k l : Fin d) :
    ∫ g, AdversarialBco.Poly.gstat g i j * AdversarialBco.Poly.gstat g k l ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  have hP : ∀ a b : Fin d, MemLp (fun g : EuclideanSpace ℝ (Fin d) => g a * g b) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun a b => by
    convert (AdversarialBco.Poly.gstat_memLp a b).add (memLp_const (if a = b then (1 : ℝ) else 0)) using 1
    funext g
    simp [AdversarialBco.Poly.gstat]
  have i4 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => g i * g j * (g k * g l))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := (hP i j).integrable_mul (hP k l)
  have iij : Integrable (fun g : EuclideanSpace ℝ (Fin d) => g i * g j) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (hP i j).integrable one_le_two
  have ikl : Integrable (fun g : EuclideanSpace ℝ (Fin d) => g k * g l) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (hP k l).integrable one_le_two
  have hA : ∫ g, g i * g j * (g k * g l) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) + (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
    rw [← AdversarialBco.Poly.gauss_isserlis i j k l]
    congr 1
    funext g
    ring
  have e : (fun g : EuclideanSpace ℝ (Fin d) => AdversarialBco.Poly.gstat g i j * AdversarialBco.Poly.gstat g k l) =
      fun g => (g i * g j * (g k * g l) - (if i = j then (1 : ℝ) else 0) * (g k * g l)) -
        ((if k = l then (1 : ℝ) else 0) * (g i * g j) - (if i = j then (1 : ℝ) else 0) * (if k = l then 1 else 0)) := by
    funext g
    simp only [AdversarialBco.Poly.gstat]
    ring
  rw [e, integral_sub (f := fun g : EuclideanSpace ℝ (Fin d) =>
      g i * g j * (g k * g l) - (if i = j then (1 : ℝ) else 0) * (g k * g l))
      (g := fun g => (if k = l then (1 : ℝ) else 0) * (g i * g j) - (if i = j then (1 : ℝ) else 0) * (if k = l then 1 else 0))
      (i4.sub (ikl.const_mul _)) ((iij.const_mul _).sub (integrable_const _)),
    integral_sub (f := fun g : EuclideanSpace ℝ (Fin d) => g i * g j * (g k * g l))
      (g := fun g => (if i = j then (1 : ℝ) else 0) * (g k * g l)) i4 (ikl.const_mul _),
    integral_sub (f := fun g : EuclideanSpace ℝ (Fin d) => (if k = l then (1 : ℝ) else 0) * (g i * g j))
      (g := fun _ => (if i = j then (1 : ℝ) else 0) * (if k = l then 1 else 0)) (iij.const_mul _) (integrable_const _),
    integral_const_mul, integral_const_mul, integral_const, hA, AdversarialBco.Poly.gauss_coord2,
    AdversarialBco.Poly.gauss_coord2]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

theorem AdversarialBco.Poly.matCS_main {d : ℕ} (ε : EuclideanSpace ℝ (Fin d) → ℝ) (hε : MemLp ε 2 (stdGaussian (EuclideanSpace ℝ (Fin d)))) :
    ∑ i, ∑ j, (∫ g, AdversarialBco.Poly.gstat g i j * ε g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ^ 2 ≤ 2 * ∫ g, ε g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set c := fun (i j : Fin d) => ∫ g, AdversarialBco.Poly.gstat g i j * ε g ∂μ with hc_def
  set S := ∑ i, ∑ j, (c i j) ^ 2 with hS_def
  set ψ := fun (g : EuclideanSpace ℝ (Fin d)) => ∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j with hψ_def
  have h_symm : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    congr 1 with g
    dsimp [AdversarialBco.Poly.gstat]
    by_cases h : i = j
    · simp [h, mul_comm]
    · simp [h, mul_comm, Ne.symm h]
  -- integrability of each term gstat i j * ε
  have h_int_gstat_ε : ∀ i j, Integrable (fun g => AdversarialBco.Poly.gstat g i j * ε g) μ := by
    intro i j
    have h_gstat_mem : MemLp (AdversarialBco.Poly.gstat · i j) 2 μ := AdversarialBco.Poly.gstat_memLp i j
    exact h_gstat_mem.integrable_mul hε
  -- integrability of c i j * gstat i j * ε g
  have h_int_c_gstat_ε : ∀ i j, Integrable (fun g => c i j * AdversarialBco.Poly.gstat g i j * ε g) μ := by
    intro i j
    have := (h_int_gstat_ε i j).const_mul (c i j)
    simpa [mul_assoc] using this
  -- integrability of ψ * ε
  have h_int_ψ_ε : Integrable (fun g => ψ g * ε g) μ := by
    dsimp [ψ]
    have h_sum : Integrable (fun g => ∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j * ε g) μ := by
      simpa using integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i hi =>
        integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj => h_int_c_gstat_ε i j))
    have h_eq : (fun g => (∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j) * ε g) =
               (fun g => ∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j * ε g) := by
      ext g; simp [Finset.sum_mul, Finset.mul_sum]
    simpa [h_eq] using h_sum
  -- compute ∫ ψ * ε = S
  have h_int_ψ_ε_eq : ∫ g, ψ g * ε g ∂μ = S := by
    have h_exchange : ∫ g, ∑ i, ∑ j, (c i j * AdversarialBco.Poly.gstat g i j * ε g) ∂μ = ∑ i, ∑ j, ∫ g, c i j * AdversarialBco.Poly.gstat g i j * ε g ∂μ := by
      calc
        ∫ g, ∑ i, ∑ j, (c i j * AdversarialBco.Poly.gstat g i j * ε g) ∂μ
            = ∑ i, ∫ g, ∑ j, (c i j * AdversarialBco.Poly.gstat g i j * ε g) ∂μ := by
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun i hi =>
            integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj => h_int_c_gstat_ε i j))]
        _ = ∑ i, ∑ j, ∫ g, c i j * AdversarialBco.Poly.gstat g i j * ε g ∂μ := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj => h_int_c_gstat_ε i j)]
    calc
      ∫ g, ψ g * ε g ∂μ = ∫ g, (∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j) * ε g ∂μ := rfl
      _ = ∫ g, ∑ i, ∑ j, (c i j * AdversarialBco.Poly.gstat g i j * ε g) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with g
        simp [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i, ∑ j, ∫ g, c i j * AdversarialBco.Poly.gstat g i j * ε g ∂μ := by rw [h_exchange]
      _ = ∑ i, ∑ j, (c i j * ∫ g, (AdversarialBco.Poly.gstat g i j * ε g) ∂μ) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simpa [mul_assoc] using integral_const_mul (c i j) (fun g => AdversarialBco.Poly.gstat g i j * ε g)
      _ = ∑ i, ∑ j, (c i j * c i j) := by simp [hc_def]
      _ = ∑ i, ∑ j, (c i j) ^ 2 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        refine Finset.sum_congr rfl (fun j hj => ?_)
        ring
      _ = S := rfl
  -- integrability of ε * ψ
  have h_int_ε_ψ : Integrable (fun g => ε g * ψ g) μ := by
    simpa [mul_comm] using h_int_ψ_ε
  -- integrability of ψ^2
  have h_int_ψ_sq : Integrable (fun g => ψ g ^ 2) μ := by
    dsimp [ψ]
    have h_term : ∀ i j k l, Integrable (fun g => (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) μ := by
      intro i j k l
      have h1 : MemLp (fun g => c i j * AdversarialBco.Poly.gstat g i j) 2 μ :=
        (AdversarialBco.Poly.gstat_memLp i j).const_mul (c i j)
      have h2 : MemLp (fun g => c k l * AdversarialBco.Poly.gstat g k l) 2 μ :=
        (AdversarialBco.Poly.gstat_memLp k l).const_mul (c k l)
      exact h1.integrable_mul h2
    have h_sum : Integrable (fun g => ∑ i, ∑ j, ∑ k, ∑ l, (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) μ := by
      simpa using integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i hi =>
        integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj =>
          integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun k hk =>
            integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun l hl => h_term i j k l))))
    have h_eq : (fun g => (∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j) ^ 2) =
               (fun g => ∑ i, ∑ j, ∑ k, ∑ l, (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) := by
      ext g
      set a := fun (i j : Fin d) => c i j * AdversarialBco.Poly.gstat g i j with ha
      calc
        (∑ i, ∑ j, a i j) ^ 2 = (∑ i, ∑ j, a i j) * (∑ i, ∑ j, a i j) := by ring
        _ = (∑ i, ∑ j, a i j) * (∑ k, ∑ l, a k l) := rfl
        _ = ∑ i, ∑ j, (a i j * (∑ k, ∑ l, a k l)) := by simp [Finset.sum_mul]
        _ = ∑ i, ∑ j, ∑ k, ∑ l, (a i j * a k l) := by simp [Finset.mul_sum]
        _ = ∑ i, ∑ j, ∑ k, ∑ l, (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l) := by simp [ha]
    simpa [h_eq] using h_sum
  -- Now compute ∫ ψ^2 = 2S
  have h_int_ψ_sq_eq : ∫ g, ψ g ^ 2 ∂μ = 2 * S := by
    have h_term_int : ∀ i j k l, Integrable (fun g => (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) μ := by
      intro i j k l
      have h1 : MemLp (fun g => c i j * AdversarialBco.Poly.gstat g i j) 2 μ :=
        (AdversarialBco.Poly.gstat_memLp i j).const_mul (c i j)
      have h2 : MemLp (fun g => c k l * AdversarialBco.Poly.gstat g k l) 2 μ :=
        (AdversarialBco.Poly.gstat_memLp k l).const_mul (c k l)
      exact h1.integrable_mul h2
    have h_exchange : ∫ g, ∑ i, ∑ j, ∑ k, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ =
        ∑ i, ∑ j, ∑ k, ∑ l, ∫ g, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
      calc
        ∫ g, ∑ i, ∑ j, ∑ k, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ
            = ∑ i, ∫ g, ∑ j, ∑ k, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun i hi =>
            integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj =>
              integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun k hk =>
                integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun l hl => h_term_int i j k l))))]
        _ = ∑ i, ∑ j, ∫ g, ∑ k, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun j hj =>
            integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun k hk =>
              integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun l hl => h_term_int i j k l)))]
        _ = ∑ i, ∑ j, ∑ k, ∫ g, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun k hk =>
            integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun l hl => h_term_int i j k l))]
        _ = ∑ i, ∑ j, ∑ k, ∑ l, ∫ g, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [integral_finsetSum (Finset.univ : Finset (Fin d)) (fun l hl => h_term_int i j k l)]
    have h_sum_simplify : ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0) + (if i = l then 1 else 0) * (if j = k then 1 else 0))) = S + S := by
      have h_first : ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0))) = S := by
        calc
          ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0)))
              = ∑ i, ∑ j, (c i j * c i j) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            refine Finset.sum_congr rfl (fun j hj => ?_)
            calc
              ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0)))
                  = c i j * (∑ k, ∑ l, c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0))) := by
                simp [Finset.mul_sum]
              _ = c i j * c i j := by
                simp [Finset.sum_ite_eq, Finset.mem_univ]
          _ = S := by
            rw [hS_def]
            simp [sq]
      have h_second : ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = l then 1 else 0) * (if j = k then 1 else 0))) = S := by
        calc
          ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = l then 1 else 0) * (if j = k then 1 else 0)))
              = ∑ i, ∑ j, (c i j * c j i) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            refine Finset.sum_congr rfl (fun j hj => ?_)
            calc
              ∑ k, ∑ l, (c i j * c k l * ((if i = l then 1 else 0) * (if j = k then 1 else 0)))
                  = c i j * (∑ k, ∑ l, c k l * ((if i = l then 1 else 0) * (if j = k then 1 else 0))) := by
                simp [Finset.mul_sum]
              _ = c i j * c j i := by
                simp [Finset.sum_ite_eq, Finset.mem_univ]
          _ = S := by
            simp_rw [h_symm]
            rw [hS_def]
            simp [sq]
      calc
        ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0) + (if i = l then 1 else 0) * (if j = k then 1 else 0)))
            = (∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0)))) +
              (∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = l then 1 else 0) * (if j = k then 1 else 0)))) := by
          simp [Finset.sum_add_distrib, mul_add]
        _ = S + S := by rw [h_first, h_second]
    calc
      ∫ g, ψ g ^ 2 ∂μ = ∫ g, (∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j) * (∑ k, ∑ l, c k l * AdversarialBco.Poly.gstat g k l) ∂μ := by
        dsimp [ψ]; ring
      _ = ∫ g, ∑ i, ∑ j, ∑ k, ∑ l, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with g
        set a := fun (i j : Fin d) => c i j * AdversarialBco.Poly.gstat g i j with ha
        calc
          (∑ i, ∑ j, c i j * AdversarialBco.Poly.gstat g i j) * (∑ k, ∑ l, c k l * AdversarialBco.Poly.gstat g k l)
              = (∑ i, ∑ j, a i j) * (∑ k, ∑ l, a k l) := by simp [ha]
          _ = ∑ i, ∑ j, (a i j * (∑ k, ∑ l, a k l)) := by simp [Finset.sum_mul]
          _ = ∑ i, ∑ j, ∑ k, ∑ l, (a i j * a k l) := by simp [Finset.mul_sum]
          _ = ∑ i, ∑ j, ∑ k, ∑ l, (c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l) := by simp [ha]
      _ = ∑ i, ∑ j, ∑ k, ∑ l, ∫ g, ((c i j * AdversarialBco.Poly.gstat g i j) * (c k l * AdversarialBco.Poly.gstat g k l)) ∂μ := by rw [h_exchange]
      _ = ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ∫ g, AdversarialBco.Poly.gstat g i j * AdversarialBco.Poly.gstat g k l ∂μ) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        refine Finset.sum_congr rfl (fun j hj => ?_)
        refine Finset.sum_congr rfl (fun k hk => ?_)
        refine Finset.sum_congr rfl (fun l hl => ?_)
        simpa [mul_assoc, mul_comm, mul_left_comm] using integral_const_mul (c i j * c k l) (fun g => AdversarialBco.Poly.gstat g i j * AdversarialBco.Poly.gstat g k l)
      _ = ∑ i, ∑ j, ∑ k, ∑ l, (c i j * c k l * ((if i = k then 1 else 0) * (if j = l then 1 else 0) + (if i = l then 1 else 0) * (if j = k then 1 else 0))) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        refine Finset.sum_congr rfl (fun j hj => ?_)
        refine Finset.sum_congr rfl (fun k hk => ?_)
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [AdversarialBco.Poly.gstat_cov i j k l]
      _ = S + S := by rw [h_sum_simplify]
      _ = 2 * S := by ring
  -- Now use the inequality 0 ≤ ∫ (ε - ψ/2)^2
  have h_nonneg : 0 ≤ ∫ g, (ε g - ψ g / 2) ^ 2 ∂μ := integral_nonneg (fun g => by positivity)
  have h_expand : ∫ g, (ε g - ψ g / 2) ^ 2 ∂μ = (∫ g, ε g ^ 2 ∂μ) - S + S / 2 := by
    calc
      ∫ g, (ε g - ψ g / 2) ^ 2 ∂μ = ∫ g, (ε g ^ 2 - ε g * ψ g + (ψ g ^ 2) / 4) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with g
        ring
      _ = (∫ g, ε g ^ 2 ∂μ) - (∫ g, ε g * ψ g ∂μ) + (∫ g, (ψ g ^ 2) / 4 ∂μ) := by
        have h_int_diff : Integrable (fun g => ε g ^ 2 - ε g * ψ g) μ :=
          hε.integrable_sq.sub h_int_ε_ψ
        have h_int_half : Integrable (fun g => (ψ g ^ 2) / 4) μ := by
          simpa [div_eq_mul_inv, mul_comm] using h_int_ψ_sq.const_mul (1/4 : ℝ)
        rw [integral_add h_int_diff h_int_half]
        rw [integral_sub hε.integrable_sq h_int_ε_ψ]
      _ = (∫ g, ε g ^ 2 ∂μ) - (∫ g, ψ g * ε g ∂μ) + (∫ g, (ψ g ^ 2) / 4 ∂μ) := by
        congr 1
        rw [show (fun g => ε g * ψ g) = (fun g => ψ g * ε g) by ext g; exact mul_comm _ _]
      _ = (∫ g, ε g ^ 2 ∂μ) - S + (∫ g, ψ g ^ 2 ∂μ) / 4 := by
        rw [h_int_ψ_ε_eq]
        have : (fun g => (ψ g ^ 2) / 4) = (fun g => (1/4 : ℝ) * ψ g ^ 2) := by ext g; ring
        rw [this, integral_const_mul (1/4 : ℝ) (fun g => ψ g ^ 2)]
        ring
      _ = (∫ g, ε g ^ 2 ∂μ) - S + (2 * S) / 4 := by rw [h_int_ψ_sq_eq]
      _ = (∫ g, ε g ^ 2 ∂μ) - S + S / 2 := by ring
  have h_ineq : S ≤ 2 * (∫ g, ε g ^ 2 ∂μ) := by
    linarith [h_nonneg, h_expand]
  simpa [hS_def] using h_ineq

theorem AdversarialBco.Poly.gaussMoments_main (d : ℕ) :
    ∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) ∧ ∫ g, ‖g‖ ^ 6 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 2) * (d + 4) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_mom2 : ∫ g, ‖g‖ ^ 2 ∂μ = (d : ℝ) :=
    (AdversarialBco.Body.gauss_moments d).1
  have h_int2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) μ := by
    have h_mem : MemLp id (2 : ENNReal) μ := IsGaussian.memLp_id μ (2 : ENNReal) (by norm_num)
    have h_mem' : MemLp id (2 : ℕ) μ := by
      simpa using h_mem
    exact h_mem'.integrable_norm_pow (by norm_num)
  have h_int4 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 4) μ := by
    have h_mem : MemLp id (4 : ENNReal) μ := IsGaussian.memLp_id μ (4 : ENNReal) (by norm_num)
    have h_mem' : MemLp id (4 : ℕ) μ := by
      simpa using h_mem
    exact h_mem'.integrable_norm_pow (by norm_num)
  have h_int6 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 6) μ := by
    have h_mem : MemLp id (6 : ENNReal) μ := IsGaussian.memLp_id μ (6 : ENNReal) (by norm_num)
    have h_mem' : MemLp id (6 : ℕ) μ := by
      simpa using h_mem
    exact h_mem'.integrable_norm_pow (by norm_num)
  have h_bound_sq (g : EuclideanSpace ℝ (Fin d)) : |‖g‖ ^ 2| ≤ (2 : ℝ) * Real.exp (‖g‖) := by
    have h_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
    have h_sq_nonneg : 0 ≤ ‖g‖ ^ 2 := pow_nonneg h_nonneg 2
    rw [abs_of_nonneg h_sq_nonneg]
    have h := Real.pow_div_factorial_le_exp ‖g‖ h_nonneg 2
    have h_fact : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [h_fact] at h
    linarith
  have h_bound_deriv_sq (g : EuclideanSpace ℝ (Fin d)) : ‖(2 : ℝ) • innerSL ℝ g‖ ≤ (2 : ℝ) * Real.exp (‖g‖) := by
    calc
      ‖(2 : ℝ) • innerSL ℝ g‖ = (2 : ℝ) * ‖innerSL ℝ g‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      _ = (2 : ℝ) * ‖g‖ := by rw [innerSL_apply_norm]
      _ ≤ (2 : ℝ) * Real.exp (‖g‖) := by
        have h := Real.add_one_le_exp (‖g‖)
        linarith
  have h_deriv_sq (g : EuclideanSpace ℝ (Fin d)) : HasFDerivAt (fun g => ‖g‖ ^ 2) ((2 : ℝ) • innerSL ℝ g) g := by
    convert (hasStrictFDerivAt_norm_sq g).hasFDerivAt using 1
    ext x; simp
  have h_stein_sq := AdversarialBco.Body.stein_radial (fun g => ‖g‖ ^ 2) (fun g => (2 : ℝ) • innerSL ℝ g)
    h_deriv_sq (2 : ℝ) (1 : ℝ) (by simpa [one_mul] using h_bound_sq) (by simpa [one_mul] using h_bound_deriv_sq)
  have h_sq_deriv_val (g : EuclideanSpace ℝ (Fin d)) : ((2 : ℝ) • innerSL ℝ g) g = (2 : ℝ) * ‖g‖ ^ 2 := by
    simp [innerSL_apply_apply]
  have h_mom4 : ∫ g, ‖g‖ ^ 4 ∂μ = (d : ℝ) * ((d : ℝ) + 2) := by
    have h_left : ∫ g, ((2 : ℝ) • innerSL ℝ g) g ∂μ = (2 : ℝ) * ∫ g, ‖g‖ ^ 2 ∂μ := by
      simp_rw [h_sq_deriv_val]
      simpa using integral_smul (2 : ℝ) (fun g => ‖g‖ ^ 2)
    have h_right : ∫ g, (‖g‖ ^ 2) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ =
        ∫ g, ‖g‖ ^ 4 ∂μ - (d : ℝ) * ∫ g, ‖g‖ ^ 2 ∂μ := by
      calc
        ∫ g, (‖g‖ ^ 2) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ =
            ∫ g, (‖g‖ ^ 4 - (d : ℝ) * ‖g‖ ^ 2) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with g
          ring
        _ = (∫ g, ‖g‖ ^ 4 ∂μ) - ∫ g, (d : ℝ) * ‖g‖ ^ 2 ∂μ := by
          rw [integral_sub h_int4 (h_int2.const_mul (d : ℝ))]
        _ = (∫ g, ‖g‖ ^ 4 ∂μ) - (d : ℝ) * ∫ g, ‖g‖ ^ 2 ∂μ := by
          apply congrArg (fun t => (∫ g, ‖g‖ ^ 4 ∂μ) - t)
          simpa using integral_smul (d : ℝ) (fun g => ‖g‖ ^ 2)
    rw [h_left, h_right] at h_stein_sq
    rw [h_mom2] at h_stein_sq
    have h_eq : (2 : ℝ) * (d : ℝ) = ∫ g, ‖g‖ ^ 4 ∂μ - (d : ℝ) * (d : ℝ) := by
      linarith
    linarith
  have h_bound_4 (g : EuclideanSpace ℝ (Fin d)) : |‖g‖ ^ 4| ≤ (24 : ℝ) * Real.exp (‖g‖) := by
    have h_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
    have h_sq_nonneg : 0 ≤ ‖g‖ ^ 4 := pow_nonneg h_nonneg 4
    rw [abs_of_nonneg h_sq_nonneg]
    have h := Real.pow_div_factorial_le_exp ‖g‖ h_nonneg 4
    have h_fact : (Nat.factorial 4 : ℝ) = 24 := by norm_num
    rw [h_fact] at h
    linarith
  have h_bound_deriv_4 (g : EuclideanSpace ℝ (Fin d)) : ‖(4 * ‖g‖ ^ 2) • innerSL ℝ g‖ ≤ (24 : ℝ) * Real.exp (‖g‖) := by
    calc
      ‖(4 * ‖g‖ ^ 2) • innerSL ℝ g‖ = (4 * ‖g‖ ^ 2) * ‖innerSL ℝ g‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 4 * ‖g‖ ^ 2)]
      _ = (4 * ‖g‖ ^ 2) * ‖g‖ := by rw [innerSL_apply_norm]
      _ = 4 * ‖g‖ ^ 3 := by ring
      _ ≤ 4 * ((Nat.factorial 3 : ℝ) * Real.exp (‖g‖)) := by
        have h_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
        have h := Real.pow_div_factorial_le_exp ‖g‖ h_nonneg 3
        have h_fact : (Nat.factorial 3 : ℝ) = 6 := by norm_num
        rw [h_fact] at h ⊢
        -- h : ‖g‖ ^ 3 / 6 ≤ Real.exp (‖g‖)
        -- goal: 4 * ‖g‖ ^ 3 ≤ 4 * (6 * Real.exp (‖g‖))
        have h' : ‖g‖ ^ 3 ≤ 6 * Real.exp (‖g‖) := by linarith
        nlinarith
      _ = 24 * Real.exp (‖g‖) := by ring
  have h_deriv_4 (g : EuclideanSpace ℝ (Fin d)) : HasFDerivAt (fun g => ‖g‖ ^ 4) ((4 * ‖g‖ ^ 2) • innerSL ℝ g) g := by
    have h_sq : HasFDerivAt (fun g => ‖g‖ ^ 2) (2 • innerSL ℝ g) g := by
      simpa using (hasStrictFDerivAt_norm_sq g).hasFDerivAt
    have h_pow := h_sq.pow 2
    convert h_pow using 1
    · ext x; ring
    · ext h; simp [innerSL_apply_apply]; ring
  have h_stein_4 := AdversarialBco.Body.stein_radial (fun g => ‖g‖ ^ 4) (fun g => (4 * ‖g‖ ^ 2) • innerSL ℝ g)
    h_deriv_4 (24 : ℝ) (1 : ℝ) (by simpa [one_mul] using h_bound_4) (by simpa [one_mul] using h_bound_deriv_4)
  have h_4_deriv_val (g : EuclideanSpace ℝ (Fin d)) : ((4 * ‖g‖ ^ 2) • innerSL ℝ g) g = (4 : ℝ) * ‖g‖ ^ 4 := by
    simp [innerSL_apply_apply]
    ring
  have h_mom6 : ∫ g, ‖g‖ ^ 6 ∂μ = (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 4) := by
    have h_left : ∫ g, ((4 * ‖g‖ ^ 2) • innerSL ℝ g) g ∂μ = (4 : ℝ) * ∫ g, ‖g‖ ^ 4 ∂μ := by
      simp_rw [h_4_deriv_val]
      simpa using integral_smul (4 : ℝ) (fun g => ‖g‖ ^ 4)
    have h_right : ∫ g, (‖g‖ ^ 4) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ =
        ∫ g, ‖g‖ ^ 6 ∂μ - (d : ℝ) * ∫ g, ‖g‖ ^ 4 ∂μ := by
      calc
        ∫ g, (‖g‖ ^ 4) * (‖g‖ ^ 2 - (d : ℝ)) ∂μ =
            ∫ g, (‖g‖ ^ 6 - (d : ℝ) * ‖g‖ ^ 4) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with g
          ring
        _ = (∫ g, ‖g‖ ^ 6 ∂μ) - ∫ g, (d : ℝ) * ‖g‖ ^ 4 ∂μ := by
          rw [integral_sub h_int6 (h_int4.const_mul (d : ℝ))]
        _ = (∫ g, ‖g‖ ^ 6 ∂μ) - (d : ℝ) * ∫ g, ‖g‖ ^ 4 ∂μ := by
          apply congrArg (fun t => (∫ g, ‖g‖ ^ 6 ∂μ) - t)
          simpa using integral_smul (d : ℝ) (fun g => ‖g‖ ^ 4)
    rw [h_left, h_right] at h_stein_4
    rw [h_mom4] at h_stein_4
    have h_eq : (4 : ℝ) * ((d : ℝ) * ((d : ℝ) + 2)) = ∫ g, ‖g‖ ^ 6 ∂μ - (d : ℝ) * ((d : ℝ) * ((d : ℝ) + 2)) := by
      linarith
    linarith
  exact And.intro h_mom4 h_mom6

theorem AdversarialBco.Poly.momentsE_main (d : ℕ) :
    ∫ g, ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 3) ∧
      ∫ g, (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 1) * (d + 5) := by
  have h_int2 : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (2 : ENNReal)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 2 (by simp)
    have hp : (2 : ℕ) ≠ 0 := by norm_num
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 2) h_mem hp
  have h_int4 : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 4) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (4 : ENNReal)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 4 (by simp)
    have hp : (4 : ℕ) ≠ 0 := by norm_num
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 4) h_mem hp
  have h_int6 : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 6) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (6 : ENNReal)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 6 (by simp)
    have hp : (6 : ℕ) ≠ 0 := by norm_num
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 6) h_mem hp
  have h_int_const : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    apply integrable_const
  have h_moments2 : ∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) :=
    (AdversarialBco.Body.gauss_moments d).1
  have h_moments4 : ∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * ((d : ℝ) + 2) :=
    (AdversarialBco.Poly.gaussMoments_main d).1
  have h_moments6 : ∫ g, ‖g‖ ^ 6 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 4) :=
    (AdversarialBco.Poly.gaussMoments_main d).2
  have h_first : ∫ g, ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * ((d : ℝ) + 3) := by
    calc
      ∫ g, ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
          = ∫ g, (‖g‖ ^ 2 + ‖g‖ ^ 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
            refine integral_congr_ae ?_
            filter_upwards with g
            ring
      _ = (∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) +
          (∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
            rw [integral_add h_int2 h_int4]
      _ = (d : ℝ) + (d : ℝ) * ((d : ℝ) + 2) := by rw [h_moments2, h_moments4]
      _ = (d : ℝ) * ((d : ℝ) + 3) := by ring
  have h_int_sq_mul : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ((d : ℝ) - 2) * ‖g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    h_int2.const_mul ((d : ℝ) - 2)
  have h_int_d : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (d : ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_const (d : ℝ)
  have h_second : ∫ g, (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5) := by
    let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
    have h_prob : IsProbabilityMeasure μ := by infer_instance
    calc
      ∫ g, (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2) ∂μ
          = ∫ g, (‖g‖ ^ 6 - ‖g‖ ^ 4 + ((d : ℝ) - 2) * ‖g‖ ^ 2 + (d : ℝ)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with g
            ring
      _ = (∫ g, ‖g‖ ^ 6 ∂μ) - (∫ g, ‖g‖ ^ 4 ∂μ) + (∫ g, ((d : ℝ) - 2) * ‖g‖ ^ 2 ∂μ) + (∫ g, (d : ℝ) ∂μ) := by
            have h_int_AB : Integrable (fun g => ‖g‖ ^ 6 - ‖g‖ ^ 4) μ := h_int6.sub h_int4
            have h_int_ABC : Integrable (fun g => ‖g‖ ^ 6 - ‖g‖ ^ 4 + ((d : ℝ) - 2) * ‖g‖ ^ 2) μ := h_int_AB.add h_int_sq_mul
            rw [integral_add h_int_ABC h_int_d,
              integral_add h_int_AB h_int_sq_mul,
              integral_sub h_int6 h_int4]
      _ = (∫ g, ‖g‖ ^ 6 ∂μ) - (∫ g, ‖g‖ ^ 4 ∂μ) + ((d : ℝ) - 2) * (∫ g, ‖g‖ ^ 2 ∂μ) + (μ.real Set.univ • (d : ℝ)) := by
            rw [integral_const_mul ((d : ℝ) - 2) (fun g => ‖g‖ ^ 2), integral_const (d : ℝ)]
      _ = (∫ g, ‖g‖ ^ 6 ∂μ) - (∫ g, ‖g‖ ^ 4 ∂μ) + ((d : ℝ) - 2) * (∫ g, ‖g‖ ^ 2 ∂μ) + (d : ℝ) := by
            have h_real_univ : μ.real Set.univ = (1 : ℝ) := by
              have h := h_prob.measure_univ
              simpa [Measure.real] using congrArg ENNReal.toReal h
            simp [h_real_univ]
      _ = ((d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 4)) - ((d : ℝ) * ((d : ℝ) + 2)) +
          ((d : ℝ) - 2) * (d : ℝ) + (d : ℝ) := by
            rw [h_moments6, h_moments4, h_moments2]
      _ = (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5) := by
            ring
  exact And.intro h_first h_second

theorem AdversarialBco.Poly.nml_fderiv_norm {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    fderiv ℝ (fun x => ‖x‖) x = (‖x‖⁻¹) • innerSL ℝ x := by
  have hsq : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hpos : (‖x‖ ^ 2 : ℝ) ≠ 0 := by
    simpa [sq_eq_zero_iff] using hx
  have hsqrt := hsq.sqrt hpos
  have hsqrt_simp : (fun y : EuclideanSpace ℝ (Fin d) => √(‖y‖ ^ 2)) = (fun y => ‖y‖) := by
    ext y; simp [Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt_simp] at hsqrt
  have hderiv_simp : (1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x) = (‖x‖⁻¹) • innerSL ℝ x := by
    have hsqrtx : √(‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
    rw [hsqrtx]
    ext y
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hderiv_simp] at hsqrt
  exact hsqrt.fderiv

theorem AdversarialBco.Poly.nml_sum_fderiv_norm {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) :
    ∑ i : Fin d, g i * fderiv ℝ (fun x => ‖x‖) g (EuclideanSpace.single i (1 : ℝ)) = ‖g‖ := by
  by_cases hg : g = 0
  · subst g; simp
  · have h_fderiv := AdversarialBco.Poly.nml_fderiv_norm hg
    calc
      ∑ i : Fin d, g i * fderiv ℝ (fun x => ‖x‖) g (EuclideanSpace.single i (1 : ℝ))
          = ∑ i : Fin d, g i * (((‖g‖⁻¹) • innerSL ℝ g) (EuclideanSpace.single i (1 : ℝ))) := by rw [h_fderiv]
      _ = ∑ i : Fin d, g i * ((‖g‖⁻¹) * inner ℝ g (EuclideanSpace.single i (1 : ℝ))) := by simp
      _ = ∑ i : Fin d, g i * ((‖g‖⁻¹) * ⟪EuclideanSpace.single i (1 : ℝ), g⟫) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_comm]
      _ = ∑ i : Fin d, g i * ((‖g‖⁻¹) * (g i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h_inner : ⟪EuclideanSpace.single i (1 : ℝ), g⟫ = g i := by
          calc
            ⟪EuclideanSpace.single i (1 : ℝ), g⟫ = ⟪g, EuclideanSpace.single i (1 : ℝ)⟫ := real_inner_comm _ _
            _ = (1 : ℝ) * (star (g i)) := EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := g)
            _ = g i := by simp
        simp [h_inner]
      _ = (∑ i : Fin d, g i ^ 2) * (‖g‖⁻¹) := by
        simp [Finset.sum_mul, mul_comm, mul_assoc, sq]
      _ = ‖g‖ ^ 2 * (‖g‖⁻¹) := by rw [EuclideanSpace.real_norm_sq_eq]
      _ = ‖g‖ := by
        have hgnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.2 hg
        field_simp [hgnorm]

theorem AdversarialBco.Poly.normMeanLower_main (d : ℕ) :
    (d : ℝ) / Real.sqrt (d + 1) ≤ ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hm_gauss := AdversarialBco.Body.gauss_moments d
  rcases hm_gauss with ⟨hm2_eq, _⟩
  -- hm2_eq : ∫ g, ‖g‖ ^ 2 ∂μ = (d : ℝ)
  set m1 := ∫ g, ‖g‖ ∂μ with hm1_def
  set m2 := ∫ g, ‖g‖ ^ 2 ∂μ with hm2_def
  set m3 := ∫ g, ‖g‖ ^ 3 ∂μ with hm3_def
  have hm2_eq' : m2 = (d : ℝ) := hm2_eq
  -- integrability
  haveI : ProbabilityTheory.IsGaussian μ := inferInstance
  have h_int_norm : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) μ := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 1 μ :=
      ProbabilityTheory.IsGaussian.memLp_id μ 1 (by norm_num)
    have h_mem_norm : MemLp (fun g => ‖g‖) 1 μ := h_mem.norm
    exact h_mem_norm.integrable (by norm_num : (1 : ENNReal) ≤ 1)
  have h_int_norm_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) μ := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 2 μ :=
      ProbabilityTheory.IsGaussian.memLp_id μ 2 (by norm_num)
    exact h_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have h_int_norm_cube : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 3) μ := by
    have h_mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 3 μ :=
      ProbabilityTheory.IsGaussian.memLp_id μ 3 (by norm_num)
    exact h_mem.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  -- Lipschitz and convexity for norm
  have h_lip_norm : LipschitzWith 1 (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) :=
    lipschitzWith_one_norm
  have h_conv_norm : ConvexOn ℝ Set.univ (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) :=
    convexOn_univ_norm
  -- Step 2: m3 = (d+1) * m1 using ibp_lip2
  have h_m3_eq : m3 = ((d : ℝ) + 1) * m1 := by
    let e : Fin d → EuclideanSpace ℝ (Fin d) := fun i => EuclideanSpace.single i (1 : ℝ)
    have he_inner (i : Fin d) (g : EuclideanSpace ℝ (Fin d)) : ⟪e i, g⟫ = g i := by
      rw [real_inner_comm]
      simp [e, EuclideanSpace.inner_single_right]
    have he_norm_sq (i : Fin d) : ‖e i‖ ^ 2 = 1 := by
      simp [e]
    -- For each i, apply ibp_lip2
    have h_ibp (i : Fin d) : ∫ g, (g i ^ 2 - 1) * ‖g‖ ∂μ = ∫ g, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ := by
      have h := AdversarialBco.Poly.ibp_lip2 (fun g => ‖g‖) 1 h_lip_norm h_conv_norm (e i) (e i)
      simpa [he_inner, he_norm_sq, sq] using h
    -- Sum of LHS
    have h_sum_lhs : ∑ i : Fin d, ∫ g, (g i ^ 2 - 1) * ‖g‖ ∂μ = m3 - (d : ℝ) * m1 := by
      calc
        ∑ i : Fin d, ∫ g, (g i ^ 2 - 1) * ‖g‖ ∂μ = ∫ g, ∑ i : Fin d, (g i ^ 2 - 1) * ‖g‖ ∂μ := by
          rw [integral_finsetSum]
          intro i _
          have h_int := (AdversarialBco.Poly.integrable_moments (fun g => ‖g‖) 1 h_lip_norm (e i) (e i)).2.1
          simpa [he_inner, he_norm_sq, sq] using h_int
        _ = ∫ g, (∑ i : Fin d, (g i ^ 2 - 1)) * ‖g‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with g
          rw [Finset.sum_mul]
        _ = ∫ g, ((∑ i : Fin d, g i ^ 2) - (d : ℝ)) * ‖g‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with g
          simp [Finset.sum_sub_distrib]
        _ = ∫ g, (‖g‖ ^ 2 - (d : ℝ)) * ‖g‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with g
          simp [EuclideanSpace.real_norm_sq_eq]
        _ = ∫ g, (‖g‖ ^ 3 - (d : ℝ) * ‖g‖) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with g
          ring
        _ = (∫ g, ‖g‖ ^ 3 ∂μ) - (∫ g, (d : ℝ) * ‖g‖ ∂μ) := by
          rw [integral_sub h_int_norm_cube (h_int_norm.const_mul (d : ℝ))]
        _ = m3 - (d : ℝ) * (∫ g, ‖g‖ ∂μ) := by
          rw [hm3_def, integral_const_mul]
        _ = m3 - (d : ℝ) * m1 := rfl
    -- Sum of RHS using the lemma
    have h_sum_rhs : ∑ i : Fin d, ∫ g, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ = m1 := by
      calc
        ∑ i : Fin d, ∫ g, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ
            = ∫ g, ∑ i : Fin d, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ := by
          rw [integral_finsetSum]
          intro i _
          have h_bound : ∀ g, |g i * fderiv ℝ (fun x => ‖x‖) g (e i)| ≤ ‖g‖ := by
            intro g
            by_cases hg : g = 0
            · subst g; simp
            · have h_fderiv := AdversarialBco.Poly.nml_fderiv_norm hg
              have h_val : fderiv ℝ (fun x => ‖x‖) g (e i) = (‖g‖⁻¹) * g i := by
                calc
                  fderiv ℝ (fun x => ‖x‖) g (e i) = ((‖g‖⁻¹) • innerSL ℝ g) (e i) := by rw [h_fderiv]
                  _ = (‖g‖⁻¹) * inner ℝ g (e i) := by simp
                  _ = (‖g‖⁻¹) * ⟪e i, g⟫ := by rw [real_inner_comm]
                  _ = (‖g‖⁻¹) * g i := by rw [he_inner i g]
              rw [h_val]
              have h_sq : (g i)^2 ≤ ‖g‖^2 := by
                calc
                  (g i)^2 ≤ ∑ j : Fin d, (g j)^2 :=
                    Finset.single_le_sum (fun j _ => pow_two_nonneg (g j)) (Finset.mem_univ i)
                  _ = ‖g‖^2 := by rw [EuclideanSpace.real_norm_sq_eq]
              calc
                |g i * ((‖g‖⁻¹) * g i)| = |(g i)^2 * (‖g‖⁻¹)| := by
                  simp [mul_comm, mul_assoc, sq]
                _ = (g i)^2 * |‖g‖⁻¹| := by rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
                _ = (g i)^2 * (‖g‖⁻¹) := by
                  rw [abs_inv, abs_of_nonneg (norm_nonneg _)]
                _ ≤ ‖g‖^2 * (‖g‖⁻¹) := by
                  gcongr
                _ = ‖g‖ := by
                  have hgnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.2 hg
                  field_simp [hgnorm]
          have h_meas : AEStronglyMeasurable (fun g => g i * fderiv ℝ (fun x => ‖x‖) g (e i)) μ := by
            have h_meas_g_i : Measurable fun g : EuclideanSpace ℝ (Fin d) => g i := by
              let φ := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
              have h_meas_φ : Measurable (φ : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) := φ.continuous.measurable
              have h_eq : (fun g : EuclideanSpace ℝ (Fin d) => g i) = (fun g => (φ g) i) := by
                ext g; rfl
              rw [h_eq]
              exact (measurable_pi_apply (a := i) (X := fun _ : Fin d => ℝ)).comp h_meas_φ
            have h_meas_fderiv : Measurable fun g : EuclideanSpace ℝ (Fin d) =>
                fderiv ℝ (fun x => ‖x‖) g (e i) :=
              measurable_fderiv_apply_const (𝕜 := ℝ) (f := fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) (e i)
            exact ((h_meas_g_i.aestronglyMeasurable).mul h_meas_fderiv.aestronglyMeasurable)
          exact h_int_norm.mono' h_meas (ae_of_all _ h_bound)
        _ = ∫ g, ‖g‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with g
          simp [e, AdversarialBco.Poly.nml_sum_fderiv_norm g]
        _ = m1 := by rfl
    -- Combine: m3 - d*m1 = m1, so m3 = (d+1)*m1
    have h_eq : (∑ i : Fin d, ∫ g, (g i ^ 2 - 1) * ‖g‖ ∂μ) = (∑ i : Fin d, ∫ g, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ) := by
      simp [h_ibp]
    calc
      m3 = (∑ i : Fin d, ∫ g, (g i ^ 2 - 1) * ‖g‖ ∂μ) + (d : ℝ) * m1 := by
        linarith [h_sum_lhs]
      _ = (∑ i : Fin d, ∫ g, g i * fderiv ℝ (fun x => ‖x‖) g (e i) ∂μ) + (d : ℝ) * m1 := by rw [h_eq]
      _ = m1 + (d : ℝ) * m1 := by rw [h_sum_rhs]
      _ = ((d : ℝ) + 1) * m1 := by ring
  -- Step 3: m2^2 ≤ m1 * m3
  have h_ineq : m2^2 ≤ m1 * m3 := by
    by_cases hm1_zero : m1 = 0
    · -- If m1 = 0, then ∫ ‖g‖ = 0, so ‖g‖ = 0 a.e., so m2 = 0
      rw [hm1_zero, zero_mul]
      have hm2_zero : m2 = 0 := by
        rw [hm2_def]
        have h_int_zero : ∫ g, ‖g‖ ∂μ = 0 := by rw [← hm1_def, hm1_zero]
        have h_nonneg : 0 ≤ᵐ[μ] fun g => ‖g‖ := by
          filter_upwards [] with g; apply norm_nonneg
        have h_ae_zero := ((integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int_norm).mp h_int_zero)
        -- h_ae_zero : (fun g => ‖g‖) =ᵐ[μ] 0
        -- So ‖g‖^2 = 0 a.e.
        have h_sq_ae_zero : (fun g => ‖g‖ ^ 2) =ᵐ[μ] 0 := by
          filter_upwards [h_ae_zero] with g hg
          simp [hg]
        -- Therefore ∫ ‖g‖^2 = 0
        have h_int_sq_zero : ∫ g, ‖g‖ ^ 2 ∂μ = 0 := by
          calc
            ∫ g, ‖g‖ ^ 2 ∂μ = ∫ g, (0 : ℝ) ∂μ := integral_congr_ae h_sq_ae_zero
            _ = 0 := by simp
        exact h_int_sq_zero
      rw [hm2_zero]
      nlinarith
    · -- m1 ≠ 0, use the quadratic form with t = m2/m1
      have h_quad : 0 ≤ ∫ g, ‖g‖ * ((‖g‖ - (m2 / m1)) ^ 2) ∂μ := by
        refine integral_nonneg ?_
        intro g; apply mul_nonneg (norm_nonneg _) (pow_two_nonneg _)
      -- Expand the integrand
      -- ‖g‖ * ((‖g‖ - m2/m1)^2) = ‖g‖^3 - 2*(m2/m1)*‖g‖^2 + (m2/m1)^2*‖g‖
      -- So the integral is m3 - 2*(m2/m1)*m2 + (m2/m1)^2*m1 = m3 - m2^2/m1
      -- Since this is ≥ 0, we have m3 ≥ m2^2/m1, so m2^2 ≤ m1*m3
      have h_expand : (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ * ((‖g‖ - (m2 / m1)) ^ 2)) =
          (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 3 - 2 * (m2 / m1) * ‖g‖ ^ 2 + ((m2 / m1) ^ 2) * ‖g‖) := by
        ext g
        ring_nf
      rw [h_expand] at h_quad
      -- Now split the integral
      have h_int1 : Integrable (fun g => ‖g‖ ^ 3) μ := h_int_norm_cube
      have h_int2 : Integrable (fun g => ‖g‖ ^ 2) μ := h_int_norm_sq
      have h_int3 : Integrable (fun g => ‖g‖) μ := h_int_norm
      have h_sum : ∫ g, (‖g‖ ^ 3 - 2 * (m2 / m1) * ‖g‖ ^ 2 + ((m2 / m1) ^ 2) * ‖g‖) ∂μ =
          (∫ g, ‖g‖ ^ 3 ∂μ) - 2 * (m2 / m1) * (∫ g, ‖g‖ ^ 2 ∂μ) + ((m2 / m1) ^ 2) * (∫ g, ‖g‖ ∂μ) := by
        have h_int_AB : Integrable (fun g => ‖g‖ ^ 3 - 2 * (m2 / m1) * ‖g‖ ^ 2) μ :=
          h_int_norm_cube.sub (h_int_norm_sq.const_mul (2 * (m2 / m1)))
        rw [integral_add h_int_AB (h_int_norm.const_mul ((m2 / m1) ^ 2))]
        rw [integral_sub h_int_norm_cube (h_int_norm_sq.const_mul (2 * (m2 / m1)))]
        simp [integral_const_mul, hm1_def, hm2_def]
      rw [h_sum] at h_quad
      -- h_quad : 0 ≤ m3 - 2*(m2/m1)*m2 + (m2/m1)^2*m1
      -- Simplify: 0 ≤ m3 - m2^2/m1
      -- So m2^2/m1 ≤ m3, i.e., m2^2 ≤ m1*m3
      have h_simp : (∫ g, ‖g‖ ^ 3 ∂μ) - 2 * (m2 / m1) * (∫ g, ‖g‖ ^ 2 ∂μ) + ((m2 / m1) ^ 2) * (∫ g, ‖g‖ ∂μ) =
          m3 - m2^2 / m1 := by
        rw [hm1_def, hm2_def, hm3_def]
        field_simp [hm1_zero]
        ring
      rw [h_simp] at h_quad
      -- h_quad : 0 ≤ m3 - m2^2 / m1
      -- So m2^2 / m1 ≤ m3, i.e., m2^2 ≤ m1*m3
      have h_div : m2^2 / m1 ≤ m3 := by linarith
      -- Multiply both sides by m1 (positive? no, m1 ≥ 0, but could be 0)
      -- Since m1 ≠ 0, we can multiply
      have hm1_nonneg : 0 ≤ m1 := by
        rw [hm1_def]
        refine integral_nonneg ?_
        intro g; apply norm_nonneg
      have hm1_pos' : 0 < m1 := by
        by_contra! H
        have hm1_eq_zero : m1 = 0 := by linarith
        exact hm1_zero hm1_eq_zero
      rw [div_le_iff₀ hm1_pos'] at h_div
      -- h_div : m2^2 ≤ m3 * m1
      -- But we need m2^2 ≤ m1 * m3
      rw [mul_comm] at h_div
      exact h_div
  -- Step 4: Combine to get the final inequality
  rw [hm2_eq'] at h_ineq
  rw [h_m3_eq] at h_ineq
  -- h_ineq : (d : ℝ)^2 ≤ m1 * ((d : ℝ) + 1) * m1 = m1^2 * ((d : ℝ) + 1)
  -- So d^2 ≤ m1^2 * (d+1)
  -- Taking sqrt: d / sqrt(d+1) ≤ m1
  have h_nonneg_d : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have h_m1_nonneg : 0 ≤ m1 := by
    rw [hm1_def]
    refine integral_nonneg ?_
    intro g; apply norm_nonneg
  -- From h_ineq: d^2 ≤ m1^2 * (d+1)
  have h_sq_ineq : (d : ℝ)^2 ≤ m1^2 * ((d : ℝ) + 1) := by
    nlinarith
  -- Divide both sides by (d+1) > 0
  have h_pos : 0 < (d : ℝ) + 1 := by linarith
  have h_div : (d : ℝ)^2 / ((d : ℝ) + 1) ≤ m1^2 := by
    -- From h_sq_ineq: d^2 ≤ m1^2 * (d+1)
    -- Divide both sides by (d+1)
    rw [div_le_iff₀ h_pos]
    -- d^2 ≤ m1^2 * (d+1)
    -- But h_sq_ineq is exactly this
    -- Wait, h_sq_ineq is d^2 ≤ m1^2 * (d+1)
    -- And we need d^2 ≤ m1^2 * (d+1) which is the same
    -- Actually, div_le_iff₀ h_pos : a / c ≤ b ↔ a ≤ b * c
    -- So we need d^2 ≤ m1^2 * (d+1)
    -- But h_sq_ineq gives d^2 ≤ m1^2 * (d+1)
    -- So this is immediate
    simpa [mul_comm] using h_sq_ineq
  -- Now take sqrt
  have h_final : (d : ℝ) / Real.sqrt ((d : ℝ) + 1) ≤ m1 := by
    -- From h_div: d^2/(d+1) ≤ m1^2
    -- Taking sqrt: d/sqrt(d+1) ≤ m1
    -- Using Real.le_sqrt_sq and Real.sqrt_div
    have h_sqrt_div : Real.sqrt ((d : ℝ)^2 / ((d : ℝ) + 1)) = (d : ℝ) / Real.sqrt ((d : ℝ) + 1) := by
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq h_nonneg_d]
    -- We have: sqrt(d^2/(d+1)) ≤ sqrt(m1^2)
    -- Since sqrt is monotone
    have h_sqrt_ineq : Real.sqrt ((d : ℝ)^2 / ((d : ℝ) + 1)) ≤ Real.sqrt (m1^2) :=
      Real.sqrt_le_sqrt h_div
    rw [h_sqrt_div] at h_sqrt_ineq
    -- Real.sqrt (m1^2) = |m1| = m1 (since m1 ≥ 0)
    rw [Real.sqrt_sq h_m1_nonneg] at h_sqrt_ineq
    exact h_sqrt_ineq
  -- Unfold m1
  rw [hm1_def] at h_final
  exact h_final

theorem AdversarialBco.Poly.d1_inv {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (R' : ℝ)
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) (h1 : Metric.closedBall 0 1 ⊆ K)
    (hR : ∀ y ∈ AdversarialBco.Poly.posBody K μ A, ‖y‖ ≤ R') (u y : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ ≤ 1) (hy : A y = u) :
    ‖y‖ ≤ R' := by
  -- A is surjective because its determinant is nonzero
  have h_det_isUnit : IsUnit (LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) :=
    Ne.isUnit hA
  have h_linear_isUnit : IsUnit (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact h_det_isUnit
  rw [LinearMap.isUnit_iff_range_eq_top] at h_linear_isUnit
  -- Pick z such that A z = -μ
  have h_neg_mem : (-μ) ∈ LinearMap.range (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [h_linear_isUnit]
    exact Submodule.mem_top
  rcases h_neg_mem with ⟨z, hz⟩
  -- hz : (A : ...) z = -μ
  -- Define yp = z + y and ym = z - y
  set yp := z + y with hyp
  set ym := z - y with hym
  -- Show yp ∈ posBody K μ A
  have hyp_mem : yp ∈ AdversarialBco.Poly.posBody K μ A := by
    rw [AdversarialBco.Poly.posBody]
    -- Need μ + A yp ∈ K
    -- μ + A yp = μ + A(z + y) = μ + A z + A y = μ + (-μ) + u = u
    -- And u ∈ closedBall 0 1 ⊆ K
    have hmem : μ + A yp = u := by
      calc
        μ + A yp = μ + A (z + y) := rfl
        _ = μ + (A z + A y) := by rw [map_add]
        _ = μ + ((-μ) + u) := by
          rw [show A z = -μ from hz, hy]
        _ = (μ + (-μ)) + u := by abel
        _ = 0 + u := by simp
        _ = u := by simp
    have hmem' : μ + A yp ∈ K := by
      rw [hmem]
      have hu_mem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa using hu
      exact h1 hu_mem
    exact hmem'
  -- Show ym ∈ posBody K μ A
  have hym_mem : ym ∈ AdversarialBco.Poly.posBody K μ A := by
    rw [AdversarialBco.Poly.posBody]
    have hmem : μ + A ym = -u := by
      calc
        μ + A ym = μ + A (z - y) := rfl
        _ = μ + (A z - A y) := by rw [map_sub]
        _ = μ + ((-μ) - u) := by
          rw [show A z = -μ from hz, hy]
        _ = (μ + (-μ)) - u := by abel
        _ = 0 - u := by simp
        _ = -u := by simp
    have hmem' : μ + A ym ∈ K := by
      rw [hmem]
      have h_neg_u_mem : -u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [norm_neg] using hu
      exact h1 h_neg_u_mem
    exact hmem'
  -- Apply hR to get bounds on ‖yp‖ and ‖ym‖
  have hyp_bound : ‖yp‖ ≤ R' := hR yp hyp_mem
  have hym_bound : ‖ym‖ ≤ R' := hR ym hym_mem
  -- Now y = (1/2) • (yp - ym)
  have hy_eq : y = (1/2 : ℝ) • (yp - ym) := by
    dsimp [yp, ym]
    calc
      y = (1/2 : ℝ) • ((2 : ℝ) • y) := by
        have h : ((1/2 : ℝ) * (2 : ℝ)) • y = (1/2 : ℝ) • ((2 : ℝ) • y) :=
          (smul_smul (1/2 : ℝ) (2 : ℝ) y).symm
        calc
          y = 1 • y := by simp
          _ = ((1/2 : ℝ) * (2 : ℝ)) • y := by norm_num
          _ = (1/2 : ℝ) • ((2 : ℝ) • y) := by rw [h]
      _ = (1/2 : ℝ) • ((z + y) - (z - y)) := by
        have h : (2 : ℝ) • y = (z + y) - (z - y) := by
          calc
            (2 : ℝ) • y = y + y := by simp [two_smul]
            _ = (z + y - z) + y := by abel
            _ = (z + y) + (-z + y) := by abel
            _ = (z + y) - (z - y) := by abel
        rw [h]
      _ = (1/2 : ℝ) • (yp - ym) := rfl
  rw [hy_eq]
  calc
    ‖(1/2 : ℝ) • (yp - ym)‖ = ‖(1/2 : ℝ)‖ * ‖yp - ym‖ := by rw [norm_smul]
    _ = |(1/2 : ℝ)| * ‖yp - ym‖ := by simp
    _ = (1/2 : ℝ) * ‖yp - ym‖ := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    _ ≤ (1/2 : ℝ) * (‖yp‖ + ‖ym‖) := by
      nlinarith [norm_sub_le yp ym]
    _ ≤ (1/2 : ℝ) * (R' + R') := by nlinarith
    _ = R' := by ring

theorem AdversarialBco.Poly.stdGaussian_map_eq {d : ℕ} (A B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : A.comp (ContinuousLinearMap.adjoint A) = B.comp (ContinuousLinearMap.adjoint B)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map A = (stdGaussian (EuclideanSpace ℝ (Fin d))).map B := by
  refine Measure.ext_of_charFun ?_
  ext t
  have h_map_eq (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      charFun ((stdGaussian (EuclideanSpace ℝ (Fin d))).map L) t =
      charFun (stdGaussian (EuclideanSpace ℝ (Fin d))) (ContinuousLinearMap.adjoint L t) := by
    rw [charFun_eq_charFunDual_toDualMap, charFun_eq_charFunDual_toDualMap]
    rw [charFunDual_map]
    have h_eq : (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d)) t : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) ∘SL L =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d)) (ContinuousLinearMap.adjoint L t) := by
      ext x
      simp [InnerProductSpace.toDualMap, ContinuousLinearMap.innerSL_apply_comp]
    rw [h_eq]
  rw [h_map_eq A, h_map_eq B, charFun_stdGaussian, charFun_stdGaussian]
  have h_norm_sq : ‖ContinuousLinearMap.adjoint A t‖ ^ 2 = ‖ContinuousLinearMap.adjoint B t‖ ^ 2 := by
    calc
      ‖ContinuousLinearMap.adjoint A t‖ ^ 2 = inner (𝕜 := ℝ) (ContinuousLinearMap.adjoint A t) (ContinuousLinearMap.adjoint A t) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner (𝕜 := ℝ) (A (ContinuousLinearMap.adjoint A t)) t := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = inner (𝕜 := ℝ) (B (ContinuousLinearMap.adjoint B t)) t := by
        have h_app := congrArg (fun (f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) => f t) h
        simpa using congrArg (fun x => inner (𝕜 := ℝ) x t) h_app
      _ = inner (𝕜 := ℝ) (ContinuousLinearMap.adjoint B t) (ContinuousLinearMap.adjoint B t) := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = ‖ContinuousLinearMap.adjoint B t‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have h_norm_sq_ℂ : ((‖ContinuousLinearMap.adjoint A t‖ : ℂ) ^ 2) = ((‖ContinuousLinearMap.adjoint B t‖ : ℂ) ^ 2) := by
    exact_mod_cast h_norm_sq
  simp [h_norm_sq_ℂ]

theorem AdversarialBco.Poly.exists_sqrt_posdef {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : IsSelfAdjoint T)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) :
    ∃ S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSelfAdjoint S ∧ (∀ v, v ≠ 0 → 0 < ⟪S v, v⟫) ∧ S.comp S = T := by
  let n := Module.finrank ℝ (EuclideanSpace ℝ (Fin d))
  have hn : n = Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := rfl
  let b := hT.isSymmetric.eigenvectorBasis hn
  let eigenvals := hT.isSymmetric.eigenvalues hn
  have h_eigen : ∀ (i : Fin n), (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (b i) = (eigenvals i : ℝ) • (b i) := by
    intro i
    have h := hT.isSymmetric.hasEigenvector_eigenvectorBasis hn i
    apply h.apply_eq_smul
  have hb_ne_zero : ∀ i, b i ≠ 0 := by
    intro i
    exact b.orthonormal.ne_zero i
  have h_inner_self : ∀ i, ⟪b i, b i⟫ = 1 := by
    intro i
    have h := b.orthonormal.1 i
    -- h : ‖b i‖ = 1
    -- In a real inner product space, ⟪x, x⟫ = ‖x‖^2
    -- But we can also use the fact that b is orthonormal
    simpa [inner_self_eq_norm_sq] using congrArg (fun x => x ^ 2) h
  have heigen_pos : ∀ i, 0 < eigenvals i := by
    intro i
    have hpos_inner : 0 < ⟪T (b i), (b i)⟫ := hpos (b i) (hb_ne_zero i)
    have h_eigen_i : T (b i) = (eigenvals i : ℝ) • (b i) := h_eigen i
    rw [h_eigen_i] at hpos_inner
    -- hpos_inner : 0 < ⟪(eigenvals i : ℝ) • (b i), (b i)⟫
    rw [inner_smul_left] at hpos_inner
    -- hpos_inner : 0 < (eigenvals i : ℝ) * ⟪b i, b i⟫
    rw [h_inner_self i] at hpos_inner
    -- hpos_inner : 0 < (eigenvals i : ℝ) * 1
    simpa using hpos_inner
  -- Define the square root function on the basis
  let f : Fin n → EuclideanSpace ℝ (Fin d) := fun i => Real.sqrt (eigenvals i) • (b i)
  -- Define the linear map S
  let S_lin : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (b.toBasis).constr ℝ f
  let S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    S_lin.toContinuousLinearMap
  have hS_basis : ∀ i, S (b i) = Real.sqrt (eigenvals i) • (b i) := by
    intro i
    simp [S, S_lin, f, Module.Basis.constr_basis]
  -- Helper lemma: formula for ⟪S x, y⟫
  have hS_inner : ∀ x y, ⟪S x, y⟫ = ∑ i, inner ℝ (b i) x * Real.sqrt (eigenvals i) * inner ℝ (b i) y := by
    intro x y
    have hx := OrthonormalBasis.sum_repr' b x
    have hy := OrthonormalBasis.sum_repr' b y
    -- Expand S x using linearity
    have hSx : S x = ∑ i, (inner ℝ (b i) x * Real.sqrt (eigenvals i)) • (b i) := by
      calc
        S x = S (∑ i, inner ℝ (b i) x • b i) := by rw [hx]
        _ = ∑ i, inner ℝ (b i) x • S (b i) := by
          simpa using map_sum (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
            (fun i => inner ℝ (b i) x • b i) Finset.univ
        _ = ∑ i, inner ℝ (b i) x • (Real.sqrt (eigenvals i) • (b i)) := by simp_rw [hS_basis]
        _ = ∑ i, (inner ℝ (b i) x * Real.sqrt (eigenvals i)) • (b i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [smul_smul]
    rw [hSx]
    -- Now compute ⟪∑ i, ... , y⟫
    rw [sum_inner]
    have htemp : (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))),
      (inner ℝ (b i) x * Real.sqrt (eigenvals i)) * inner ℝ (b i) y) =
      ∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))), inner ℝ (b i) x * Real.sqrt (eigenvals i) * inner ℝ (b i) y := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans htemp
    rw [inner_smul_left]
    simp
  refine ⟨S, ?_, ?_, ?_⟩
  · -- IsSelfAdjoint S
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    -- Goal: ⟪↑S x, y⟫ = ⟪x, ↑S y⟫
    -- Note: ⟪↑S x, y⟫ = ⟪S x, y⟫ definitionally
    -- Similarly, ⟪x, ↑S y⟫ = ⟪x, S y⟫
    -- So we need ⟪S x, y⟫ = ⟪x, S y⟫
    -- Using hS_inner and symmetry of inner product:
    have hgoal : ⟪S x, y⟫ = ⟪x, S y⟫ := by
      rw [hS_inner x y, real_inner_comm (S y) x, hS_inner y x]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_comm x (b i), real_inner_comm y (b i)]
      ring
    simpa using hgoal
  · -- ∀ v ≠ 0, 0 < ⟪S v, v⟫
    intro v hv
    have hpos_inner : 0 < ⟪S v, v⟫ := by
      rw [hS_inner v v]
      -- Goal: 0 < ∑ i, inner ℝ (b i) v * Real.sqrt (eigenvals i) * inner ℝ (b i) v
      have h_sqrt_pos' : ∀ i, 0 < Real.sqrt (eigenvals i) := by
        intro i
        exact Real.sqrt_pos.mpr (heigen_pos i)
      -- v ≠ 0 implies that not all inner products are zero
      have h_exists_nonzero : ∃ i, inner ℝ (b i) v ≠ 0 := by
        by_contra! h_all_zero
        have h_all_zero' : ∀ i, inner ℝ (b i) v = 0 := h_all_zero
        have hv_zero : v = 0 := by
          calc
            v = ∑ i, inner ℝ (b i) v • b i := by rw [OrthonormalBasis.sum_repr' b v]
            _ = ∑ i, (0 : ℝ) • b i := by simp_rw [h_all_zero']
            _ = 0 := by simp
        exact hv hv_zero
      rcases h_exists_nonzero with ⟨i, hi⟩
      -- Apply Finset.sum_pos'
      refine Finset.sum_pos' (fun i _ => ?_) ?_
      · -- Show each term is nonnegative
        have h_nonneg : 0 ≤ inner ℝ (b i) v * Real.sqrt (eigenvals i) * inner ℝ (b i) v := by
          -- This equals (inner ℝ (b i) v)^2 * Real.sqrt (eigenvals i) which is nonnegative
          nlinarith [sq_nonneg (inner ℝ (b i) v), Real.sqrt_nonneg (eigenvals i)]
        exact h_nonneg
      · -- There exists a positive term
        refine ⟨i, Finset.mem_univ i, ?_⟩
        have h_sq_pos : 0 < (inner ℝ (b i) v)^2 := sq_pos_iff.mpr hi
        have h_term : inner ℝ (b i) v * Real.sqrt (eigenvals i) * inner ℝ (b i) v = (inner ℝ (b i) v)^2 * Real.sqrt (eigenvals i) := by ring
        rw [h_term]
        exact mul_pos h_sq_pos (h_sqrt_pos' i)
    exact hpos_inner
  · -- S.comp S = T
    have hS_basis : ∀ i, S (b i) = Real.sqrt (eigenvals i) • (b i) := by
      intro i
      simp [S, S_lin, f]
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis]
    show S (S (b i)) = T (b i)
    rw [hS_basis i, map_smul, hS_basis i, smul_smul, Real.mul_self_sqrt (heigen_pos i).le]
    exact (h_eigen i).symm

theorem AdversarialBco.Poly.logdet_le_trace_sub {d : ℕ} (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hM : IsSelfAdjoint M)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪M v, v⟫) :
    Real.log (LinearMap.det (M : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≤ LinearMap.trace ℝ _ (M : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) - d := by
  set E := EuclideanSpace ℝ (Fin d) with hE
  have hn : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have hM_sym : (M : E →ₗ[ℝ] E).IsSymmetric := hM.isSymmetric
  have h_det : LinearMap.det (M : E →ₗ[ℝ] E) = ∏ i : Fin d, (hM_sym.eigenvalues hn i : ℝ) := by
    simpa using hM_sym.det_eq_prod_eigenvalues hn
  have h_trace : LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) = ∑ i : Fin d, (hM_sym.eigenvalues hn i : ℝ) := by
    simpa using hM_sym.trace_eq_sum_eigenvalues hn
  have h_eigen_pos : ∀ i : Fin d, 0 < hM_sym.eigenvalues hn i := by
    intro i
    set v := (hM_sym.eigenvectorBasis hn) i with hv_def
    have h_has_eigen : Module.End.HasEigenvector (M : E →ₗ[ℝ] E) (hM_sym.eigenvalues hn i) v :=
      hM_sym.hasEigenvector_eigenvectorBasis hn i
    rcases (Module.End.hasEigenvector_iff).mp h_has_eigen with ⟨h_mem, hv_ne_zero⟩
    have h_apply : (M : E →ₗ[ℝ] E) v = (hM_sym.eigenvalues hn i : ℝ) • v :=
      (Module.End.mem_eigenspace_iff).mp h_mem
    have h_inner_pos : 0 < ⟪(M : E →ₗ[ℝ] E) v, v⟫ := hpos v hv_ne_zero
    rw [h_apply] at h_inner_pos
    have h_inner_smul : ⟪(hM_sym.eigenvalues hn i : ℝ) • v, v⟫ = (hM_sym.eigenvalues hn i : ℝ) * ⟪v, v⟫ := by
      rw [real_inner_smul_left]
    rw [h_inner_smul] at h_inner_pos
    have h_inner_self_pos : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv_ne_zero
    -- Now h_inner_pos : 0 < λ * ⟪v, v⟫ and h_inner_self_pos : 0 < ⟪v, v⟫
    -- So λ > 0
    exact pos_of_mul_pos_left h_inner_pos (by positivity)
  have h_log_prod : Real.log (∏ i : Fin d, (hM_sym.eigenvalues hn i : ℝ)) = ∑ i : Fin d, Real.log (hM_sym.eigenvalues hn i) := by
    refine Real.log_prod ?_
    intro i hi
    have hpos_i := h_eigen_pos i
    linarith
  have h_log_le : ∀ i : Fin d, Real.log (hM_sym.eigenvalues hn i) ≤ (hM_sym.eigenvalues hn i : ℝ) - 1 := by
    intro i
    refine Real.log_le_sub_one_of_pos (h_eigen_pos i)
  have h_sum_log_le : (∑ i : Fin d, Real.log (hM_sym.eigenvalues hn i)) ≤ (∑ i : Fin d, ((hM_sym.eigenvalues hn i : ℝ) - 1)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact h_log_le i
  have h_sum_sub : (∑ i : Fin d, ((hM_sym.eigenvalues hn i : ℝ) - 1)) = (∑ i : Fin d, (hM_sym.eigenvalues hn i : ℝ)) - d := by
    simp [Finset.sum_sub_distrib]
  calc
    Real.log (LinearMap.det (M : E →ₗ[ℝ] E)) = Real.log (∏ i : Fin d, (hM_sym.eigenvalues hn i : ℝ)) := by rw [h_det]
    _ = ∑ i : Fin d, Real.log (hM_sym.eigenvalues hn i) := by rw [h_log_prod]
    _ ≤ ∑ i : Fin d, ((hM_sym.eigenvalues hn i : ℝ) - 1) := h_sum_log_le
    _ = (∑ i : Fin d, (hM_sym.eigenvalues hn i : ℝ)) - d := by rw [h_sum_sub]
    _ = LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) - d := by rw [h_trace]
    _ = LinearMap.trace ℝ _ (M : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) - d := by rfl

theorem AdversarialBco.Poly.logdet_concave_main {d : ℕ} (T T' Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : IsSelfAdjoint T)
    (hT' : IsSelfAdjoint T') (hpos : ∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) (hpos' : ∀ v, v ≠ 0 → 0 < ⟪T' v, v⟫)
    (hinv : T.comp Ti = ContinuousLinearMap.id ℝ _ ∧ Ti.comp T = ContinuousLinearMap.id ℝ _) :
    Real.log (LinearMap.det (T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≤ Real.log (LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) +
      LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
  let E := EuclideanSpace ℝ (Fin d)
  rcases hinv with ⟨hTcompTi, hTicompT⟩
  -- ring identities: f * g = f.comp g, 1 = id
  have hT_mul_Ti : T * Ti = 1 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]; exact hTcompTi
  have hTi_mul_T : Ti * T = 1 := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]; exact hTicompT
  -- get square root S of T
  obtain ⟨S, hS_sa, hSpos, hS_mul_S⟩ := AdversarialBco.Poly.exists_sqrt_posdef T hT hpos
  -- hS_mul_S : S.comp S = T, convert to S * S = T
  have hS_mul_S' : S * S = T := by
    rw [ContinuousLinearMap.mul_def]; exact hS_mul_S
  -- T * S = S * T
  have hT_mul_S : T * S = S * T := by
    calc
      T * S = (S * S) * S := by rw [hS_mul_S']
      _ = S * (S * S) := by rw [mul_assoc]
      _ = S * T := by rw [hS_mul_S']
  -- Ti * S = S * Ti
  have hTi_mul_S : Ti * S = S * Ti := by
    calc
      Ti * S = (Ti * S) * 1 := by simp
      _ = (Ti * S) * (T * Ti) := by rw [hT_mul_Ti]
      _ = Ti * S * T * Ti := by simp [mul_assoc]
      _ = Ti * (S * T) * Ti := by simp [mul_assoc]
      _ = Ti * (T * S) * Ti := by rw [hT_mul_S]
      _ = (Ti * T) * S * Ti := by simp [mul_assoc]
      _ = 1 * S * Ti := by rw [hTi_mul_T]
      _ = S * Ti := by simp
  -- Si := S * Ti
  let Si := S * Ti
  have hS_mul_Si : S * Si = 1 := by
    calc
      S * Si = S * (S * Ti) := rfl
      _ = (S * S) * Ti := by rw [mul_assoc]
      _ = T * Ti := by rw [hS_mul_S']
      _ = 1 := by rw [hT_mul_Ti]
  have hSi_mul_S : Si * S = 1 := by
    calc
      Si * S = (S * Ti) * S := rfl
      _ = S * (Ti * S) := by rw [mul_assoc]
      _ = S * (S * Ti) := by rw [hTi_mul_S]
      _ = (S * S) * Ti := by rw [mul_assoc]
      _ = T * Ti := by rw [hS_mul_S']
      _ = 1 := by rw [hT_mul_Ti]
  have hSi_mul_Si : Si * Si = Ti := by
    calc
      Si * Si = (S * Ti) * (S * Ti) := rfl
      _ = S * (Ti * S) * Ti := by simp [mul_assoc]
      _ = S * (S * Ti) * Ti := by rw [hTi_mul_S]
      _ = (S * S) * Ti * Ti := by simp [mul_assoc]
      _ = T * Ti * Ti := by rw [hS_mul_S']
      _ = (T * Ti) * Ti := by rw [mul_assoc]
      _ = 1 * Ti := by rw [hT_mul_Ti]
      _ = Ti := by simp
  -- star Ti = Ti
  have hTi_sa : IsSelfAdjoint Ti := by
    have hstarTi : star Ti = Ti := by
      calc
        star Ti = star Ti * 1 := by simp
        _ = star Ti * (T * Ti) := by rw [hT_mul_Ti]
        _ = (star Ti * T) * Ti := by rw [mul_assoc]
        _ = (star Ti * star T) * Ti := by rw [hT.star_eq]
        _ = star (T * Ti) * Ti := by rw [star_mul]
        _ = star 1 * Ti := by rw [hT_mul_Ti]
        _ = 1 * Ti := by simp
        _ = Ti := by simp
    exact hstarTi
  -- star Si = Si
  have hSi_sa : IsSelfAdjoint Si := by
    have hstarSi : star Si = Si := by
      calc
        star Si = star (S * Ti) := rfl
        _ = star Ti * star S := by rw [star_mul]
        _ = Ti * S := by rw [hTi_sa.star_eq, hS_sa.star_eq]
        _ = S * Ti := by rw [hTi_mul_S]
        _ = Si := rfl
    exact hstarSi
  -- M := Si * T' * Si is self-adjoint
  let M := Si * T' * Si
  have hM_sa : IsSelfAdjoint M := by
    have := hT'.conjugate Si
    rw [hSi_sa.star_eq] at this
    exact this
  -- M is positive definite
  have hMpos : ∀ v, v ≠ 0 → 0 < ⟪M v, v⟫ := by
    intro v hv
    have hSv_ne_zero : Si v ≠ 0 := by
      intro hzero
      apply hv
      have : S (Si v) = v := by
        calc
          S (Si v) = (S * Si) v := rfl
          _ = (1 : E →L[ℝ] E) v := by rw [hS_mul_Si]
          _ = v := by simp
      rw [hzero] at this
      simpa using this.symm
    have hadj_Si : ContinuousLinearMap.adjoint Si = Si := by
      rw [← ContinuousLinearMap.star_eq_adjoint Si, hSi_sa.star_eq]
    have h_inner_M : ⟪M v, v⟫ = ⟪T' (Si v), Si v⟫ := by
      calc
        ⟪M v, v⟫ = ⟪Si ((T' * Si) v), v⟫ := rfl
        _ = ⟪(T' * Si) v, Si v⟫ := by
          rw [← ContinuousLinearMap.adjoint_inner_left Si v ((T' * Si) v), hadj_Si]
        _ = ⟪T' (Si v), Si v⟫ := rfl
    rw [h_inner_M]
    exact hpos' (Si v) hSv_ne_zero
  -- determinant identities
  have h_det_T_Ti : LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (Ti : E →ₗ[ℝ] E) = 1 := by
    calc
      LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (Ti : E →ₗ[ℝ] E) =
          LinearMap.det ((T * Ti : E →L[ℝ] E) : E →ₗ[ℝ] E) := by simp
      _ = LinearMap.det ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [hT_mul_Ti]
      _ = 1 := by simp
  have h_det_S_Si : LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) = 1 := by
    calc
      LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) =
          LinearMap.det ((S * Si : E →L[ℝ] E) : E →ₗ[ℝ] E) := by simp
      _ = LinearMap.det ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [hS_mul_Si]
      _ = 1 := by simp
  have h_det_T_S : LinearMap.det (T : E →ₗ[ℝ] E) = LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (S : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (T : E →ₗ[ℝ] E) = LinearMap.det ((S * S : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [hS_mul_S']
      _ = LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (S : E →ₗ[ℝ] E) := by simp
  have h_det_M : LinearMap.det (M : E →ₗ[ℝ] E) = LinearMap.det (Si : E →ₗ[ℝ] E) * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (M : E →ₗ[ℝ] E) = LinearMap.det ((Si * T' * Si : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
      _ = LinearMap.det (((Si * T') * Si : E →L[ℝ] E) : E →ₗ[ℝ] E) := by ring
      _ = LinearMap.det ((Si * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by simp
      _ = (LinearMap.det (Si : E →ₗ[ℝ] E) * LinearMap.det (T' : E →ₗ[ℝ] E)) * LinearMap.det (Si : E →ₗ[ℝ] E) := by simp
      _ = LinearMap.det (Si : E →ₗ[ℝ] E) * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by ring
  -- det T ≠ 0
  have h_det_T_ne_zero : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := by
    intro hzero
    have : LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (Ti : E →ₗ[ℝ] E) = 0 := by rw [hzero, zero_mul]
    rw [h_det_T_Ti] at this
    exact one_ne_zero this
  -- T' is injective, hence a unit, so det T' ≠ 0
  have h_det_T'_ne_zero : LinearMap.det (T' : E →ₗ[ℝ] E) ≠ 0 := by
    have h_inj : Function.Injective (T' : E →ₗ[ℝ] E) := by
      intro x y h
      have hzero : (T' : E →ₗ[ℝ] E) (x - y) = 0 := by
        rw [map_sub, h, sub_self]
      by_contra hne
      have hpos := hpos' (x - y) (sub_ne_zero.mpr hne)
      -- hpos : 0 < ⟪T' (x - y), x - y⟫  (T' is ContinuousLinearMap)
      -- hzero : (T' : E →ₗ[ℝ] E) (x - y) = 0
      have hzero' : T' (x - y) = 0 := by simpa using hzero
      rw [hzero'] at hpos
      simp at hpos
    have h_ker : LinearMap.ker (T' : E →ₗ[ℝ] E) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact h_inj
    have h_unit : IsUnit (T' : E →ₗ[ℝ] E) :=
      (LinearMap.isUnit_iff_ker_eq_bot (T' : E →ₗ[ℝ] E)).mpr h_ker
    have h_det_unit : IsUnit (LinearMap.det (T' : E →ₗ[ℝ] E)) :=
      (LinearMap.isUnit_iff_isUnit_det (T' : E →ₗ[ℝ] E)).mp h_unit
    exact h_det_unit.ne_zero
  -- det T' = det T * det M (key algebraic identity)
  have h_det_prod_eq : LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (M : E →ₗ[ℝ] E) = LinearMap.det (T' : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (M : E →ₗ[ℝ] E) =
          (LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (S : E →ₗ[ℝ] E)) * (LinearMap.det (Si : E →ₗ[ℝ] E) * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E)) := by rw [h_det_T_S, h_det_M]
      _ = LinearMap.det (S : E →ₗ[ℝ] E) * (LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E)) * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by ring
      _ = LinearMap.det (S : E →ₗ[ℝ] E) * 1 * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by rw [h_det_S_Si]
      _ = LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by simp
      _ = LinearMap.det (T' : E →ₗ[ℝ] E) * LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E) := by ring
      _ = LinearMap.det (T' : E →ₗ[ℝ] E) * (LinearMap.det (S : E →ₗ[ℝ] E) * LinearMap.det (Si : E →ₗ[ℝ] E)) := by ring
      _ = LinearMap.det (T' : E →ₗ[ℝ] E) * 1 := by rw [h_det_S_Si]
      _ = LinearMap.det (T' : E →ₗ[ℝ] E) := by simp
  have h_det_T'_eq : LinearMap.det (T' : E →ₗ[ℝ] E) = LinearMap.det (T : E →ₗ[ℝ] E) * LinearMap.det (M : E →ₗ[ℝ] E) := by
    rw [← h_det_prod_eq]
  -- det M ≠ 0
  have h_det_M_ne_zero : LinearMap.det (M : E →ₗ[ℝ] E) ≠ 0 := by
    intro hzero
    apply h_det_T'_ne_zero
    rw [h_det_T'_eq, hzero, mul_zero]
  -- log(det T') = log(det T) + log(det M)
  have h_log_det : Real.log (LinearMap.det (T' : E →ₗ[ℝ] E)) = Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + Real.log (LinearMap.det (M : E →ₗ[ℝ] E)) := by
    rw [h_det_T'_eq, Real.log_mul h_det_T_ne_zero h_det_M_ne_zero]
  -- apply logdet_le_trace_sub to M
  have h_log_M_le : Real.log (LinearMap.det (M : E →ₗ[ℝ] E)) ≤ LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) - (d : ℝ) :=
    AdversarialBco.Poly.logdet_le_trace_sub M hM_sa hMpos
  -- trace identities
  have h_trace_M : LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) = LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    have h_trace_mul_comm (A B : E →L[ℝ] E) : LinearMap.trace ℝ E ((A * B : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.trace ℝ E ((B * A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      simpa using (LinearMap.trace_mul_comm ℝ (A : E →ₗ[ℝ] E) (B : E →ₗ[ℝ] E))
    calc
      LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) = LinearMap.trace ℝ E ((Si * T' * Si : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
      _ = LinearMap.trace ℝ E ((Si * (T' * Si) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by simp [mul_assoc]
      _ = LinearMap.trace ℝ E (((T' * Si) * Si : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [h_trace_mul_comm Si (T' * Si)]
      _ = LinearMap.trace ℝ E ((T' * (Si * Si) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by simp [mul_assoc]
      _ = LinearMap.trace ℝ E ((T' * Ti : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [hSi_mul_Si]
      _ = LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [h_trace_mul_comm T' Ti]
  have h_finrank : Module.finrank ℝ E = d := by
    simp [E, finrank_euclideanSpace_fin (𝕜 := ℝ) (n := d)]
  have h_trace_Ti_T'_sub_d : LinearMap.trace ℝ E ((Ti * (T' - T) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) - (d : ℝ) := by
    calc
      LinearMap.trace ℝ E ((Ti * (T' - T) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
          LinearMap.trace ℝ E (((Ti * T' : E →L[ℝ] E) - (Ti * T : E →L[ℝ] E)) : E →ₗ[ℝ] E) := by simp [mul_sub]
      _ = LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.trace ℝ E ((Ti * T : E →L[ℝ] E) : E →ₗ[ℝ] E) := by simp
      _ = LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.trace ℝ E ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [hTi_mul_T]
      _ = LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) - (d : ℝ) := by simp [LinearMap.trace_one, h_finrank]
  -- combine everything
  calc
    Real.log (LinearMap.det (T' : E →ₗ[ℝ] E)) = Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + Real.log (LinearMap.det (M : E →ₗ[ℝ] E)) := by rw [h_log_det]
    _ ≤ Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + (LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) - (d : ℝ)) := by
      nlinarith
    _ = Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + (LinearMap.trace ℝ E ((Ti * T' : E →L[ℝ] E) : E →ₗ[ℝ] E) - (d : ℝ)) := by rw [h_trace_M]
    _ = Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + LinearMap.trace ℝ E ((Ti * (T' - T) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by rw [h_trace_Ti_T'_sub_d]
    _ = Real.log (LinearMap.det (T : E →ₗ[ℝ] E)) + LinearMap.trace ℝ E ((Ti.comp (T' - T) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      simp [ContinuousLinearMap.mul_def]


theorem AdversarialBco.Poly.polarSym_main (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) :
    ∃ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSelfAdjoint T ∧ (∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) ∧ (stdGaussian (EuclideanSpace ℝ (Fin d))).map T = (stdGaussian (EuclideanSpace ℝ (Fin d))).map A ∧
      |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| = |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  set P := A.comp (ContinuousLinearMap.adjoint A) with hP_def
  have hA_ker_eq_bot : LinearMap.ker (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = ⊥ := by
    have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))).not.mp hA
    simpa using h
  have hA_range_eq_top : LinearMap.range (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top (f := (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))).mp hA_ker_eq_bot
  have hA_adjoint_ker_eq_bot : LinearMap.ker (LinearMap.adjoint (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) = ⊥ := by
    rw [← LinearMap.orthogonal_range, hA_range_eq_top]
    exact (Submodule.orthogonal_eq_bot_iff (K := ⊤)).mpr rfl
  have hP_selfadjoint : IsSelfAdjoint P := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    rw [hP_def]
    calc
      ContinuousLinearMap.adjoint (A.comp (ContinuousLinearMap.adjoint A)) =
          ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) ∘L ContinuousLinearMap.adjoint A := by
        rw [ContinuousLinearMap.adjoint_comp]
      _ = A ∘L ContinuousLinearMap.adjoint A := by rw [ContinuousLinearMap.adjoint_adjoint]
  have hP_pos : ∀ v, v ≠ 0 → 0 < ⟪P v, v⟫ := by
    intro v hv
    rw [hP_def]
    have h_inner : ⟪(A.comp (ContinuousLinearMap.adjoint A)) v, v⟫ = ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
      calc
        ⟪(A.comp (ContinuousLinearMap.adjoint A)) v, v⟫ = ⟪ContinuousLinearMap.adjoint A v, ContinuousLinearMap.adjoint A v⟫ := by
          rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
        _ = ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
          simpa using inner_self_eq_norm_sq (𝕜 := ℝ) (ContinuousLinearMap.adjoint A v)
    rw [h_inner]
    have h_adjoint_ne_zero : ContinuousLinearMap.adjoint A v ≠ 0 := by
      intro hzero
      have h_mem_ker : v ∈ LinearMap.ker (LinearMap.adjoint (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) := by
        rw [LinearMap.mem_ker]
        exact hzero
      rw [hA_adjoint_ker_eq_bot] at h_mem_ker
      rw [Submodule.mem_bot] at h_mem_ker
      exact hv h_mem_ker
    have h_norm_pos : 0 < ‖ContinuousLinearMap.adjoint A v‖ := norm_pos_iff.mpr h_adjoint_ne_zero
    exact pow_pos h_norm_pos 2
  obtain ⟨T, hT_selfadjoint, hT_pos, hT_sqrt⟩ := AdversarialBco.Poly.exists_sqrt_posdef P hP_selfadjoint hP_pos
  have hT_adjoint_eq_T : ContinuousLinearMap.adjoint T = T :=
    (ContinuousLinearMap.star_eq_adjoint (𝕜 := ℝ) T).symm.trans hT_selfadjoint
  have hT_comp_T_eq_P : T.comp T = P := hT_sqrt
  have h_map_eq : (stdGaussian (EuclideanSpace ℝ (Fin d))).map T = (stdGaussian (EuclideanSpace ℝ (Fin d))).map A := by
    apply AdversarialBco.Poly.stdGaussian_map_eq T A
    calc
      T.comp (ContinuousLinearMap.adjoint T) = T.comp T := by rw [hT_adjoint_eq_T]
      _ = P := hT_comp_T_eq_P
      _ = A.comp (ContinuousLinearMap.adjoint A) := by rw [hP_def]
  have hT_adjoint_linear : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).adjoint =
      (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [ContinuousLinearMap.adjoint_toLinearMap T, hT_adjoint_eq_T]
  have h_det_eq : |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
      |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
    have hT_normDet_sq : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 =
        (P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).det := by
      have h := ContinuousLinearMap.normDet_sq (f := T)
      -- h: ↑(T.normDet ^ 2) = (T.adjoint ∘SL T).det
      have h' : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 =
          (T ∘SL T).det := by
        simpa [hT_adjoint_eq_T] using h
      rw [hT_comp_T_eq_P] at h'
      exact h'
    have hA_normDet_sq : (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 =
        (P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).det := by
      have h := ContinuousLinearMap.normDet_sq (f := A)
      -- h: ↑(A.normDet ^ 2) = (A.adjoint ∘SL A).det
      have h' : (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 =
          (ContinuousLinearMap.adjoint A ∘SL A).det := by
        simpa using h
      -- Relate (A.adjoint ∘SL A).det to P.det
      have h_adjoint_comp_det : (ContinuousLinearMap.adjoint A ∘SL A).det =
          (P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).det := by
        rw [hP_def]
        calc
          (ContinuousLinearMap.adjoint A ∘SL A).det =
              ((ContinuousLinearMap.adjoint A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ∘ₗ
                (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))).det := rfl
          _ = LinearMap.det (ContinuousLinearMap.adjoint A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
              LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
            rw [LinearMap.det_comp]
          _ = LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
              LinearMap.det (ContinuousLinearMap.adjoint A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
            rw [mul_comm]
          _ = ((A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ∘ₗ
              (ContinuousLinearMap.adjoint A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))).det := by
            rw [LinearMap.det_comp]
          _ = (A ∘SL ContinuousLinearMap.adjoint A).det := rfl
      rw [h_adjoint_comp_det] at h'
      exact h'
    have h_normDet_sq_eq : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 =
        (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet ^ 2 := by
      rw [hT_normDet_sq, hA_normDet_sq]
    have h_normDet_eq_abs_det_T : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet =
        |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      LinearMap.normDet_eq_abs_det _
    have h_normDet_eq_abs_det_A : (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).normDet =
        |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      LinearMap.normDet_eq_abs_det _
    rw [h_normDet_eq_abs_det_T, h_normDet_eq_abs_det_A] at h_normDet_sq_eq
    have h_nonneg_T : 0 ≤ |LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_nonneg _
    have h_nonneg_A : 0 ≤ |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_nonneg _
    nlinarith
  exact ⟨T, hT_selfadjoint, hT_pos, h_map_eq, h_det_eq⟩

theorem AdversarialBco.Poly.d1_bounds (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hρ : 0 < ρ)
    (hK : Convex ℝ K) (h1 : Metric.closedBall 0 1 ⊆ K) (hKρ : K ⊆ Metric.closedBall 0 ρ) :
    ‖μ‖ ≤ ρ * AdversarialBco.Poly.posK K μ A ∧
      ∀ u, ‖u‖ = 1 → ‖(ContinuousLinearMap.adjoint A) u‖ * Real.sqrt (2 / Real.pi) ≤ ρ * AdversarialBco.Poly.posK K μ A := by
  let E := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ
  -- K is absorbent because it contains a ball around 0
  have hK_absorbent : Absorbent ℝ K := by
    have hball_absorbent : Absorbent ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      absorbent_ball (by simpa [norm_zero] using hρ)
    have hclosedball_absorbent : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      hball_absorbent.mono Metric.ball_subset_closedBall
    exact hclosedball_absorbent.mono h1
  -- Integrability of g ↦ μ + A g
  have hμA_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => μ + A g) E := by
    have hid : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) E :=
      IsGaussian.integrable_id
    have hA_int : Integrable (fun g => A g) E :=
      ContinuousLinearMap.integrable_comp A hid
    have hconst : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => μ) E :=
      integrable_const _
    exact hconst.add hA_int
  have hnorm_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖μ + A g‖) E :=
    hμA_int.norm
  -- The function F(g) = gauge K (μ + A g) is Lipschitz with constant ‖A‖₊
  have hF_lipschitz : LipschitzWith ‖A‖₊ (fun g : EuclideanSpace ℝ (Fin d) => gauge K (μ + A g)) := by
    refine LipschitzWith.of_dist_le_mul (fun g h => ?_)
    have h_sub : gauge K (μ + A g) - gauge K (μ + A h) ≤ gauge K (A (g - h)) := by
      have h_add := gauge_add_le hK hK_absorbent (μ + A h) (A g - A h)
      have h_eq : (μ + A h) + (A g - A h) = μ + A g := by
        simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      rw [h_eq] at h_add
      have h_map_sub : A g - A h = A (g - h) := by simp
      rw [h_map_sub] at h_add
      linarith
    have h_sub' : gauge K (μ + A h) - gauge K (μ + A g) ≤ gauge K (A (h - g)) := by
      have h_add := gauge_add_le hK hK_absorbent (μ + A g) (A h - A g)
      have h_eq : (μ + A g) + (A h - A g) = μ + A h := by
        simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      rw [h_eq] at h_add
      have h_map_sub : A h - A g = A (h - g) := by simp
      rw [h_map_sub] at h_add
      linarith
    have h_bound : ∀ (x : EuclideanSpace ℝ (Fin d)), gauge K x ≤ ‖x‖ := by
      intro x
      exact (AdversarialBco.Poly.gauge_bounds d K ρ hρ hK h1 hKρ x).2
    have h_bound_A : gauge K (A (g - h)) ≤ ‖A (g - h)‖ := h_bound (A (g - h))
    have h_bound_A' : gauge K (A (h - g)) ≤ ‖A (h - g)‖ := h_bound (A (h - g))
    have h_norm_A : ‖A (g - h)‖ ≤ ‖A‖ * ‖g - h‖ := by
      simpa using ContinuousLinearMap.le_opNorm_of_le A (le_refl ‖g - h‖)
    have h_norm_A' : ‖A (h - g)‖ ≤ ‖A‖ * ‖h - g‖ := by
      have h_eq : A (h - g) = -(A (g - h)) := by
        simp [map_sub, sub_eq_add_neg]
      calc
        ‖A (h - g)‖ = ‖-(A (g - h))‖ := by rw [h_eq]
        _ = ‖A (g - h)‖ := by rw [norm_neg]
        _ ≤ ‖A‖ * ‖g - h‖ := h_norm_A
        _ = ‖A‖ * ‖h - g‖ := by rw [norm_sub_rev]
    have hA_coe : (‖A‖₊ : ℝ) = ‖A‖ := rfl
    have h_total : |gauge K (μ + A g) - gauge K (μ + A h)| ≤ (‖A‖₊ : ℝ) * ‖g - h‖ := by
      have h1' : gauge K (μ + A g) - gauge K (μ + A h) ≤ (‖A‖₊ : ℝ) * ‖g - h‖ := by
        calc
          gauge K (μ + A g) - gauge K (μ + A h) ≤ gauge K (A (g - h)) := h_sub
          _ ≤ ‖A (g - h)‖ := h_bound_A
          _ ≤ ‖A‖ * ‖g - h‖ := h_norm_A
          _ = (‖A‖₊ : ℝ) * ‖g - h‖ := by rw [hA_coe]
      have h2' : -(gauge K (μ + A g) - gauge K (μ + A h)) ≤ (‖A‖₊ : ℝ) * ‖g - h‖ := by
        calc
          -(gauge K (μ + A g) - gauge K (μ + A h)) = gauge K (μ + A h) - gauge K (μ + A g) := by ring
          _ ≤ gauge K (A (h - g)) := h_sub'
          _ ≤ ‖A (h - g)‖ := h_bound_A'
          _ ≤ ‖A‖ * ‖h - g‖ := h_norm_A'
          _ = (‖A‖₊ : ℝ) * ‖g - h‖ := by rw [norm_sub_rev, hA_coe]
      rw [abs_le]
      constructor
      · linarith
      · linarith
    simpa [dist_eq_norm] using h_total
  have hF_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => gauge K (μ + A g)) E :=
    AdversarialBco.Poly.integrable_of_lipschitz (fun g => gauge K (μ + A g)) ‖A‖₊ hF_lipschitz
  -- First inequality: ‖μ‖ ≤ ρ * posK K μ A
  have h_first : ‖μ‖ ≤ ρ * AdversarialBco.Poly.posK K μ A := by
    -- From gauge_bounds: ‖x‖ / ρ ≤ gauge K x, so ‖μ + A g‖ ≤ ρ * gauge K (μ + A g)
    have h_pointwise : ∀ g, ‖μ + A g‖ ≤ ρ * gauge K (μ + A g) := by
      intro g
      have hbound := (AdversarialBco.Poly.gauge_bounds d K ρ hρ hK h1 hKρ (μ + A g)).1
      -- hbound : ‖μ + A g‖ / ρ ≤ gauge K (μ + A g)
      -- Using div_le_iff₀ hρ : b / ρ ≤ a ↔ b ≤ a * ρ
      have h := (div_le_iff₀ hρ).mp hbound
      -- h : ‖μ + A g‖ ≤ gauge K (μ + A g) * ρ
      -- Commute the multiplication
      simpa [mul_comm] using h
    have h_int_ineq : ∫ g, ‖μ + A g‖ ∂E ≤ ∫ g, ρ * gauge K (μ + A g) ∂E :=
      MeasureTheory.integral_mono hnorm_int (hF_int.const_mul ρ)
        (fun g => h_pointwise g)
    have h_int_norm_le : ∫ g, ‖μ + A g‖ ∂E ≤ ρ * AdversarialBco.Poly.posK K μ A := by
      calc
        ∫ g, ‖μ + A g‖ ∂E ≤ ∫ g, ρ * gauge K (μ + A g) ∂E := h_int_ineq
        _ = ρ * ∫ g, gauge K (μ + A g) ∂E := by rw [MeasureTheory.integral_const_mul]
        _ = ρ * AdversarialBco.Poly.posK K μ A := rfl
    -- Now ‖μ‖ = ‖∫ (μ + A g) dE‖ ≤ ∫ ‖μ + A g‖ dE
    have h_int_mu : ∫ g, (μ + A g) ∂E = μ := by
      have hA_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => A g) E :=
        ContinuousLinearMap.integrable_comp A IsGaussian.integrable_id
      have h_int_A : ∫ g, A g ∂E = A (∫ g, g ∂E) :=
        ContinuousLinearMap.integral_comp_comm A IsGaussian.integrable_id
      calc
        ∫ g, (μ + A g) ∂E = (∫ g, μ ∂E) + (∫ g, A g ∂E) := by
          rw [MeasureTheory.integral_add (integrable_const _) hA_int]
        _ = μ + (∫ g, A g ∂E) := by simp
        _ = μ + A (∫ g, g ∂E) := by rw [h_int_A]
        _ = μ + A 0 := by rw [ProbabilityTheory.integral_id_stdGaussian]
        _ = μ := by simp
    have h_norm_int : ‖μ‖ ≤ ∫ g, ‖μ + A g‖ ∂E := by
      calc
        ‖μ‖ = ‖∫ g, (μ + A g) ∂E‖ := by rw [h_int_mu]
        _ ≤ ∫ g, ‖μ + A g‖ ∂E := MeasureTheory.norm_integral_le_integral_norm _
    calc
      ‖μ‖ ≤ ∫ g, ‖μ + A g‖ ∂E := h_norm_int
      _ ≤ ρ * AdversarialBco.Poly.posK K μ A := h_int_norm_le
  -- Second inequality: for unit u, ‖A† u‖ * sqrt(2/π) ≤ ρ * posK K μ A
  have h_second : ∀ u, ‖u‖ = 1 → ‖(ContinuousLinearMap.adjoint A) u‖ * Real.sqrt (2 / Real.pi) ≤ ρ * AdversarialBco.Poly.posK K μ A := by
    intro u hu
    -- Key inequality: |⟪u, A g⟫| ≤ (‖μ + A g‖ + ‖-μ + A g‖) / 2
    have h_inner_bound : ∀ g, |⟪u, A g⟫| ≤ (‖μ + A g‖ + ‖-μ + A g‖) / 2 := by
      intro g
      have h_triangle : ‖A g‖ ≤ (‖μ + A g‖ + ‖-μ + A g‖) / 2 := by
        have h_two_smul : (μ + A g) + (-μ + A g) = (2 : ℝ) • A g := by
          simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, two_smul]
        have h_norm_sum : ‖(μ + A g) + (-μ + A g)‖ ≤ ‖μ + A g‖ + ‖-μ + A g‖ := norm_add_le _ _
        have h_ineq : 2 * ‖A g‖ ≤ ‖μ + A g‖ + ‖-μ + A g‖ := by
          calc
            2 * ‖A g‖ = ‖(2 : ℝ) • A g‖ := by
              simp [norm_smul]
            _ = ‖(μ + A g) + (-μ + A g)‖ := by rw [h_two_smul]
            _ ≤ ‖μ + A g‖ + ‖-μ + A g‖ := h_norm_sum
        linarith
      calc
        |⟪u, A g⟫| = ‖⟪u, A g⟫‖ := by simp
        _ ≤ ‖u‖ * ‖A g‖ := norm_inner_le_norm _ _
        _ = 1 * ‖A g‖ := by rw [hu]
        _ = ‖A g‖ := by simp
        _ ≤ (‖μ + A g‖ + ‖-μ + A g‖) / 2 := h_triangle
    -- Integrability of |⟪u, A g⟫|
    have h_inner_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => |⟪u, A g⟫|) E := by
      have h_bound : ∀ g, |⟪u, A g⟫| ≤ ‖u‖ * ‖A g‖ := by
        intro g
        calc
          |⟪u, A g⟫| = ‖⟪u, A g⟫‖ := by simp
          _ ≤ ‖u‖ * ‖A g‖ := norm_inner_le_norm _ _
      have h_int_norm_A : Integrable (fun g => ‖u‖ * ‖A g‖) E := by
        have hA_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => A g) E :=
          ContinuousLinearMap.integrable_comp A IsGaussian.integrable_id
        have h_norm_A_int : Integrable (fun g => ‖A g‖) E := hA_int.norm
        exact h_norm_A_int.const_mul ‖u‖
      have h_ae : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => |⟪u, A g⟫|) E := by
        refine (Continuous.aestronglyMeasurable ?_)
        refine Continuous.abs ?_
        refine Continuous.inner ?_ A.continuous
        exact continuous_const
      refine h_int_norm_A.mono h_ae ?_
      filter_upwards [] with g
      simpa [hu] using h_bound g
    -- Integrability of ‖-μ + A g‖
    have hnorm_int_neg : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖-μ + A g‖) E := by
      have hμA_int_neg : Integrable (fun g : EuclideanSpace ℝ (Fin d) => -μ + A g) E := by
        have hA_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => A g) E :=
          ContinuousLinearMap.integrable_comp A IsGaussian.integrable_id
        have hconst : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => -μ) E := integrable_const _
        exact hconst.add hA_int
      exact hμA_int_neg.norm
    -- Symmetry: E[‖-μ + A g‖] = E[‖μ + A g‖]
    have h_symm : ∫ g, ‖-μ + A g‖ ∂E = ∫ g, ‖μ + A g‖ ∂E := by
      have h_pointwise : ∀ g, ‖-μ + A g‖ = ‖μ + A (-g)‖ := by
        intro g
        calc
          ‖-μ + A g‖ = ‖-(μ + (-A g))‖ := by simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
          _ = ‖μ + (-A g)‖ := by rw [norm_neg]
          _ = ‖μ + A (-g)‖ := by simp
      -- Using change of variables g ↦ -g
      let φ : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
        LinearIsometryEquiv.neg (R := ℝ) (E := EuclideanSpace ℝ (Fin d))
      have h_map : Measure.map (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) E = E := by
        simpa [E] using ProbabilityTheory.stdGaussian_map φ
      have h_meas : AEMeasurable (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) E :=
        φ.continuous.aemeasurable
      have h_ae_strongly : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => ‖-μ + A g‖)
          (Measure.map (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) E) := by
        rw [h_map]
        refine (Continuous.aestronglyMeasurable ?_)
        refine Continuous.norm ?_
        refine (Continuous.add ?_ A.continuous)
        exact continuous_const
      calc
        ∫ g, ‖-μ + A g‖ ∂E = ∫ g, ‖-μ + A g‖ ∂(Measure.map (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) E) := by rw [h_map]
        _ = ∫ g, ‖-μ + A (φ g)‖ ∂E := by rw [MeasureTheory.integral_map h_meas h_ae_strongly]
        _ = ∫ g, ‖-μ + A (-g)‖ ∂E := rfl
        _ = ∫ g, ‖μ + A g‖ ∂E := by
          -- ‖-μ + A (-g)‖ = ‖μ + A g‖ because -μ + A(-g) = -(μ + A g)
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [] with g
          calc
            ‖-μ + A (-g)‖ = ‖-(μ + A g)‖ := by simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
            _ = ‖μ + A g‖ := by rw [norm_neg]
    -- Take expectation of h_inner_bound
    have h_sum_int : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖μ + A g‖ + ‖-μ + A g‖) / 2) E := by
      have h_sum : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖μ + A g‖ + ‖-μ + A g‖) E :=
        hnorm_int.add hnorm_int_neg
      exact h_sum.div_const 2
    have h_exp_bound : ∫ g, |⟪u, A g⟫| ∂E ≤ (∫ g, ‖μ + A g‖ ∂E + ∫ g, ‖-μ + A g‖ ∂E) / 2 := by
      have h_int_mid : ∫ g, (‖μ + A g‖ + ‖-μ + A g‖) / 2 ∂E = (∫ g, ‖μ + A g‖ ∂E + ∫ g, ‖-μ + A g‖ ∂E) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add hnorm_int hnorm_int_neg]
      calc
        ∫ g, |⟪u, A g⟫| ∂E ≤ ∫ g, (‖μ + A g‖ + ‖-μ + A g‖) / 2 ∂E :=
          MeasureTheory.integral_mono h_inner_int h_sum_int (fun g => h_inner_bound g)
        _ = (∫ g, ‖μ + A g‖ ∂E + ∫ g, ‖-μ + A g‖ ∂E) / 2 := by rw [h_int_mid]
    -- Now use symmetry to simplify
    have h_exp_bound2 : ∫ g, |⟪u, A g⟫| ∂E ≤ ∫ g, ‖μ + A g‖ ∂E := by
      rw [h_symm] at h_exp_bound
      -- h_exp_bound : ... ≤ (I + I) / 2 = I
      have : (∫ g, ‖μ + A g‖ ∂E + ∫ g, ‖μ + A g‖ ∂E) / 2 = ∫ g, ‖μ + A g‖ ∂E := by ring
      rw [this] at h_exp_bound
      exact h_exp_bound
    -- Now relate |⟪u, A g⟫| to |⟪A† u, g⟫|
    have h_adjoint : ∀ g, |⟪u, A g⟫| = |⟪(ContinuousLinearMap.adjoint A) u, g⟫| := by
      intro g
      simp [ContinuousLinearMap.adjoint_inner_left A u (A g), ContinuousLinearMap.adjoint_inner_left]
    -- Actually, adjoint_inner_left gives: inner (adjoint A y) x = inner y (A x)
    -- So ⟪A† u, g⟫ = ⟪u, A g⟫
    -- Therefore |⟪u, A g⟫| = |⟪A† u, g⟫|
    have h_adjoint_eq : (fun g : EuclideanSpace ℝ (Fin d) => |⟪u, A g⟫|) =
                        (fun g : EuclideanSpace ℝ (Fin d) => |⟪(ContinuousLinearMap.adjoint A) u, g⟫|) := by
      ext g
      simp [ContinuousLinearMap.adjoint_inner_left]
    rw [h_adjoint_eq] at h_exp_bound2
    -- Now use integral_abs_inner
    have h_int_abs_inner : ∫ g, |⟪(ContinuousLinearMap.adjoint A) u, g⟫| ∂E =
                          ‖(ContinuousLinearMap.adjoint A) u‖ * Real.sqrt (2 / Real.pi) := by
      rw [AdversarialBco.Body.integral_abs_inner (ContinuousLinearMap.adjoint A u)]
    -- Now we have: ‖A† u‖ * sqrt(2/π) ≤ ∫ ‖μ + A g‖ ≤ ρ * posK K μ A
    calc
      ‖(ContinuousLinearMap.adjoint A) u‖ * Real.sqrt (2 / Real.pi) = ∫ g, |⟪(ContinuousLinearMap.adjoint A) u, g⟫| ∂E := by rw [h_int_abs_inner]
      _ ≤ ∫ g, ‖μ + A g‖ ∂E := h_exp_bound2
      _ ≤ ρ * AdversarialBco.Poly.posK K μ A := by
        -- We already proved this in h_first
        -- h_first gives: ‖μ‖ ≤ ρ * posK K μ A
        -- But we need ∫ ‖μ + A g‖ ≤ ρ * posK K μ A
        -- This was h_int_norm_le in the first part
        -- Let me extract it
        have h_int_norm_le : ∫ g, ‖μ + A g‖ ∂E ≤ ρ * AdversarialBco.Poly.posK K μ A := by
          -- Reuse the proof from h_first
          have h_pointwise : ∀ g, ‖μ + A g‖ ≤ ρ * gauge K (μ + A g) := by
            intro g'
            have hbound := (AdversarialBco.Poly.gauge_bounds d K ρ hρ hK h1 hKρ (μ + A g')).1
            have h := (div_le_iff₀ hρ).mp hbound
            simpa [mul_comm] using h
          have h_int_ineq : ∫ g, ‖μ + A g‖ ∂E ≤ ∫ g, ρ * gauge K (μ + A g) ∂E :=
            MeasureTheory.integral_mono hnorm_int (hF_int.const_mul ρ) (fun g => h_pointwise g)
          calc
            ∫ g, ‖μ + A g‖ ∂E ≤ ∫ g, ρ * gauge K (μ + A g) ∂E := h_int_ineq
            _ = ρ * ∫ g, gauge K (μ + A g) ∂E := by rw [MeasureTheory.integral_const_mul]
            _ = ρ * AdversarialBco.Poly.posK K μ A := rfl
        exact h_int_norm_le
  exact And.intro h_first h_second

theorem AdversarialBco.Poly.d4_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (τ0 τ1 R : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hK : Convex ℝ K)
    (h1 : Metric.closedBall 0 1 ⊆ K) (hτ0 : 0 ≤ τ0) (hD : AdversarialBco.Poly.IsPgDom τ0 τ1 R μ T) :
    LipschitzWith (Real.toNNReal τ1) (AdversarialBco.Poly.posF K μ T) ∧
      (∀ y, 0 ≤ AdversarialBco.Poly.posF K μ T y ∧ AdversarialBco.Poly.posF K μ T y ≤ ‖μ‖ + τ1 * ‖y‖) ∧
      ∫ g, AdversarialBco.Poly.posF K μ T g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ (R + τ1 * Real.sqrt d) ^ 2 := by
  obtain ⟨hTs, hμR, hform⟩ := hD
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ≥0) ⊆ K := by
    simpa using Metric.ball_subset_closedBall.trans h1
  have hgL : LipschitzWith 1 (gauge K) := by
    simpa using hK.lipschitzWith_gauge (r := 1) one_pos hball
  have hgle : ∀ x, gauge K x ≤ ‖x‖ := fun x => by
    simpa using mul_gauge_le_norm (r := 1) (x := x) (by simpa using hball)
  have hTv : ∀ v, ‖T v‖ ≤ τ1 * ‖v‖ := AdversarialBco.Poly.opnorm_le_of_form T τ1 hTs
    (fun v => (mul_nonneg hτ0 (sq_nonneg _)).trans (hform v).1) (fun v => (hform v).2)
  have hτg : ∀ v : EuclideanSpace ℝ (Fin d), 0 ≤ τ1 * ‖v‖ := fun v => by
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h, mul_zero]
    · have h2 : 0 ≤ τ1 * ‖v‖ ^ 2 :=
        (mul_nonneg hτ0 (sq_nonneg _)).trans ((hform v).1.trans (hform v).2)
      have : 0 ≤ τ1 := by
        by_contra hneg
        rw [not_le] at hneg
        have : τ1 * ‖v‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
        linarith
      positivity
  have hF : ∀ y, 0 ≤ AdversarialBco.Poly.posF K μ T y ∧ AdversarialBco.Poly.posF K μ T y ≤ ‖μ‖ + τ1 * ‖y‖ :=
    fun y => ⟨gauge_nonneg _, (hgle _).trans ((norm_add_le _ _).trans (by linarith [hTv y]))⟩
  refine ⟨LipschitzWith.of_dist_le_mul fun y y' => ?_, hF, ?_⟩
  · show dist (gauge K (μ + T y)) (gauge K (μ + T y')) ≤ _
    have h := hgL.dist_le_mul (μ + T y) (μ + T y')
    rw [NNReal.coe_one, one_mul, dist_eq_norm (μ + T y), add_sub_add_left_eq_sub, ← map_sub] at h
    rw [dist_eq_norm y y']
    exact h.trans ((hTv _).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal τ1) (norm_nonneg _)))
  · have hn1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.integrable_id.norm
    have hn2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (memLp_two_iff_integrable_sq_norm IsGaussian.integrable_id.aestronglyMeasurable).1 IsGaussian.memLp_two_id
    have hm2 : ∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = d := (AdversarialBco.Body.gauss_moments d).1
    have hm0 : 0 ≤ ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := integral_nonneg fun _ => norm_nonneg _
    have hm : ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ Real.sqrt d := by
      have h0 : 0 ≤ ∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ^ 2 := by
        have hv := variance_eq_sub (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
          (IsGaussian.memLp_two_id.norm)
        have := variance_nonneg (fun x : EuclideanSpace ℝ (Fin d) => ‖id x‖) (stdGaussian (EuclideanSpace ℝ (Fin d)))
        rw [hv] at this
        simpa [Pi.pow_apply] using this
      rw [Real.le_sqrt hm0 (Nat.cast_nonneg _)]
      linarith
    have hFint : Integrable (fun g => AdversarialBco.Poly.posF K μ T g ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine Integrable.mono' ((((integrable_const (‖μ‖ ^ 2)).add (hn1.const_mul (2 * ‖μ‖ * τ1))).add
        (hn2.const_mul (τ1 ^ 2)))) ?_ (Filter.Eventually.of_forall fun g => ?_)
      · exact ((continuous_gauge hK (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos)
          (by simpa using hball))).comp (continuous_const.add T.continuous)).pow 2 |>.aestronglyMeasurable
      · have hsq := pow_le_pow_left₀ (hF g).1 (hF g).2 2
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hF g).1]
        nlinarith [hsq]
    have hmu0 : 0 ≤ ‖μ‖ := norm_nonneg _
    have hR2 : ‖μ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hmu0 hμR 2
    calc ∫ g, AdversarialBco.Poly.posF K μ T g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        ≤ ∫ g, (‖μ‖ ^ 2 + 2 * ‖μ‖ * τ1 * ‖g‖ + τ1 ^ 2 * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          refine integral_mono hFint (((integrable_const _).add (hn1.const_mul _)).add (hn2.const_mul _))
            fun g => ?_
          have hsq := pow_le_pow_left₀ (hF g).1 (hF g).2 2
          nlinarith [hsq]
      _ = ‖μ‖ ^ 2 + 2 * ‖μ‖ * τ1 * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + τ1 ^ 2 * d := by
          rw [integral_add (f := fun g : EuclideanSpace ℝ (Fin d) => ‖μ‖ ^ 2 + 2 * ‖μ‖ * τ1 * ‖g‖)
              (g := fun g => τ1 ^ 2 * ‖g‖ ^ 2) ((integrable_const _).add (hn1.const_mul _)) (hn2.const_mul _),
            integral_add (f := fun _ : EuclideanSpace ℝ (Fin d) => ‖μ‖ ^ 2)
              (g := fun g => 2 * ‖μ‖ * τ1 * ‖g‖) (integrable_const _) (hn1.const_mul _),
            integral_const_mul, integral_const_mul, hm2, integral_const]
          simp
      _ ≤ (R + τ1 * Real.sqrt d) ^ 2 := by
          have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
          have hexp : (R + τ1 * Real.sqrt d) ^ 2 = R ^ 2 + 2 * (R * (τ1 * Real.sqrt d)) + τ1 ^ 2 * Real.sqrt d ^ 2 := by
            ring
          rw [hexp, hsq]
          rcases Nat.eq_zero_or_pos d with hd | hd
          · have hm' : ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0 := by
              have := hm; simp only [hd, Nat.cast_zero, Real.sqrt_zero] at this; linarith
            rw [hm']
            simp only [hd, Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero]
            linarith
          · have hτ1 : 0 ≤ τ1 := by
              have h := hτg (EuclideanSpace.single ⟨0, hd⟩ 1)
              simpa using h
            have h2 : ‖μ‖ * (τ1 * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ R * (τ1 * Real.sqrt d) :=
              mul_le_mul hμR (mul_le_mul_of_nonneg_left hm hτ1) (mul_nonneg hτ1 hm0) (hmu0.trans hμR)
            nlinarith [h2]

theorem AdversarialBco.Poly.propAi_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hd : 1 ≤ d) (hK : AdversarialBco.Poly.IsPosBody K r0 α) (hκ : 0 < κ) (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 → hstar ≤ AdversarialBco.Poly.posObj K κ μ' A')
    (he : AdversarialBco.Poly.posObj K κ μ A ≤ hstar + e) (hk : 0 < AdversarialBco.Poly.posK K μ A) :
    κ * (AdversarialBco.Poly.posK K μ A / κ - 1 - Real.log (AdversarialBco.Poly.posK K μ A / κ)) ≤ e := by
  set k := AdversarialBco.Poly.posK K μ A with hk_def
  have hk_pos : 0 < k := hk
  set s := κ / k with hs_def
  have hs_pos : 0 < s := div_pos hκ hk_pos
  have hd_pos : 0 < (d : ℝ) := by
    have : 0 < (d : ℕ) := by omega
    exact_mod_cast this
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hdet_smul_ne_zero : LinearMap.det ((s • A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    have hlog := AdversarialBco.Poly.log_det_smul A hA s hs_pos
    exact hlog.1
  have hposK_smul : AdversarialBco.Poly.posK K (s • μ) (s • A) = κ := by
    rw [AdversarialBco.Poly.posK_smul K μ A s hs_pos, ← hk_def]
    rw [hs_def]
    field_simp [hk_pos.ne.symm]
  have hposObj_smul : AdversarialBco.Poly.posObj K κ (s • μ) (s • A) = κ - κ * Real.log s - κ / (d : ℝ) * Real.log |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
    rw [AdversarialBco.Poly.posObj, hposK_smul]
    have hlog := AdversarialBco.Poly.log_det_smul A hA s hs_pos
    rcases hlog with ⟨_, hlog_eq⟩
    rw [hlog_eq]
    field_simp [hd_ne_zero]
    ring
  have hineq1 : hstar ≤ AdversarialBco.Poly.posObj K κ (s • μ) (s • A) :=
    hmin (s • μ) (s • A) hdet_smul_ne_zero
  have hineq2 : AdversarialBco.Poly.posObj K κ μ A ≤ hstar + e := he
  have hineq_combined : AdversarialBco.Poly.posObj K κ μ A ≤ AdversarialBco.Poly.posObj K κ (s • μ) (s • A) + e := by
    linarith
  unfold AdversarialBco.Poly.posObj at hineq_combined
  rw [← hk_def] at hineq_combined
  rw [hposK_smul] at hineq_combined
  have hlog := AdversarialBco.Poly.log_det_smul A hA s hs_pos
  rcases hlog with ⟨_, hlog_eq⟩
  rw [hlog_eq] at hineq_combined
  -- hineq_combined: k - κ/d * |det A| ≤ κ - κ/d * (d * log s + log|det A|) + e
  -- Clear denominator d and cancel the log|det A| terms
  have h_simp : k ≤ κ - κ * Real.log s + e := by
    field_simp [hd_ne_zero] at hineq_combined
    nlinarith
  have h_log_s : Real.log s = -Real.log (k / κ) := by
    rw [hs_def]
    calc
      Real.log (κ / k) = Real.log κ - Real.log k := Real.log_div hκ.ne.symm hk_pos.ne.symm
      _ = -(Real.log k - Real.log κ) := by ring
      _ = -Real.log (k / κ) := by rw [← Real.log_div hk_pos.ne.symm hκ.ne.symm]
  rw [h_log_s] at h_simp
  -- h_simp: k ≤ κ + κ * Real.log (k / κ) + e
  have h_target : k - κ - κ * Real.log (k / κ) ≤ e := by
    linarith
  have h_final : κ * (k / κ - 1 - Real.log (k / κ)) = k - κ - κ * Real.log (k / κ) := by
    have h : κ * (k / κ) = k := by field_simp [hκ.ne.symm]
    calc
      κ * (k / κ - 1 - Real.log (k / κ))
          = κ * (k / κ) - κ * 1 - κ * Real.log (k / κ) := by ring
      _ = κ * (k / κ) - κ - κ * Real.log (k / κ) := by ring
      _ = k - κ - κ * Real.log (k / κ) := by rw [h]
  rw [h_final]
  exact h_target

theorem AdversarialBco.Poly.lemmaB_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hρ : 1 ≤ ρ) (hK : Convex ℝ K)
    (hKc : IsClosed K) (h1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K) (hρK : K ⊆ Metric.closedBall 0 ρ) (j : ℕ) (η : ℝ)
    (hη : ρ / 2 ^ j ≤ η) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x ≤ AdversarialBco.Poly.piTilde K ρ j x ∧
      AdversarialBco.Poly.piTilde K ρ j x ≤ gauge K x + ‖x‖ / 2 ^ j ∧
        AdversarialBco.Poly.piTilde K ρ j x ≤ (1 + η) * gauge K x := by
  have hρpos : 0 < ρ := by linarith
  by_cases hx : x = 0
  · subst hx
    simp [AdversarialBco.Poly.piTilde, gauge_zero]
  · have hp_nonneg : 0 ≤ gauge K x := gauge_nonneg x
    have hmem : ∀ s, (0 < s ∧ s⁻¹ • x ∈ K) ↔ gauge K x ≤ s :=
      AdversarialBco.Poly.gauge_le_iff_pos_mem K ρ hK hKc h1 hρK x hx
    have hbounds : ‖x‖ / ρ ≤ gauge K x ∧ gauge K x ≤ ‖x‖ :=
      AdversarialBco.Poly.gauge_bounds d K ρ hρpos hK h1 hρK x
    rcases hbounds with ⟨hlo, hhi⟩
    have hspec := AdversarialBco.Poly.bisect_spec (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (gauge K x) (‖x‖ / ρ) ‖x‖ hmem hlo hhi j
    rcases hspec with ⟨hlo', hp_le_hi', hdiff⟩
    have h_first : gauge K x ≤ AdversarialBco.Poly.piTilde K ρ j x := by
      unfold AdversarialBco.Poly.piTilde
      simp [hx]
      exact hp_le_hi'
    have h_two_pow_nonneg : 0 ≤ (2 : ℝ) ^ j := pow_nonneg (by norm_num) j
    have h_second : AdversarialBco.Poly.piTilde K ρ j x ≤ gauge K x + ‖x‖ / 2 ^ j := by
      unfold AdversarialBco.Poly.piTilde
      simp [hx]
      have hi'_le_p_plus_diff : (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 ≤
          gauge K x + ((‖x‖ - ‖x‖ / ρ) / (2 : ℝ) ^ j) := by
        have : (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 -
            gauge K x ≤
            (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 -
            (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).1 := by
          nlinarith
        nlinarith
      have h_diff_le_norm_div : ((‖x‖ - ‖x‖ / ρ) / (2 : ℝ) ^ j) ≤ ‖x‖ / (2 : ℝ) ^ j := by
        have h_nonneg : 0 ≤ ‖x‖ / ρ := div_nonneg (norm_nonneg _) (by linarith)
        exact (div_le_div_of_nonneg_right (by nlinarith) h_two_pow_nonneg)
      nlinarith
    have h_third : AdversarialBco.Poly.piTilde K ρ j x ≤ (1 + η) * gauge K x := by
      unfold AdversarialBco.Poly.piTilde
      simp [hx]
      have hx_norm_le : ‖x‖ ≤ ρ * gauge K x := by
        have := (div_le_iff₀ hρpos).mp hlo
        nlinarith
      have h_norm_div : ‖x‖ / (2 : ℝ) ^ j ≤ η * gauge K x := by
        calc
          ‖x‖ / (2 : ℝ) ^ j ≤ (ρ * gauge K x) / (2 : ℝ) ^ j :=
            div_le_div_of_nonneg_right hx_norm_le h_two_pow_nonneg
          _ = (ρ / (2 : ℝ) ^ j) * gauge K x := by ring
          _ ≤ η * gauge K x := by
            nlinarith
      have hi'_le_p_plus_diff : (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 ≤
          gauge K x + ((‖x‖ - ‖x‖ / ρ) / (2 : ℝ) ^ j) := by
        have : (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 -
            gauge K x ≤
            (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).2 -
            (AdversarialBco.Poly.bisect (fun s => 0 < s ∧ s⁻¹ • x ∈ K) (‖x‖ / ρ) ‖x‖ j).1 := by
          nlinarith
        nlinarith
      have h_diff_le_norm_div : ((‖x‖ - ‖x‖ / ρ) / (2 : ℝ) ^ j) ≤ ‖x‖ / (2 : ℝ) ^ j := by
        have h_nonneg : 0 ≤ ‖x‖ / ρ := div_nonneg (norm_nonneg _) (by linarith)
        exact (div_le_div_of_nonneg_right (by nlinarith) h_two_pow_nonneg)
      nlinarith
    exact ⟨h_first, h_second, h_third⟩

theorem AdversarialBco.Poly.telescope_bound (Ψ D : ℝ → ℝ) (s C : ℝ) (hs : 0 ≤ s)
    (hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → Ψ b - Ψ a ≤ (b - a) * D b)
    (hD : ∀ t, 0 ≤ t → t ≤ s → D t ≤ D 0 + C * t) :
    Ψ s - Ψ 0 ≤ s * D 0 + C * s ^ 2 / 2 := by
  by_cases hs0 : s = 0
  · subst hs0; simp
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsum_succ (N : ℕ) : (∑ k ∈ Finset.range N, ((k : ℝ) + 1)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
      induction N with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    have h_bound (N : ℕ) (hN : N ≥ 1) : Ψ s - Ψ 0 ≤ s * D 0 + C * s ^ 2 / 2 + C * s ^ 2 / (2 * (N : ℝ)) := by
      have hNpos : (N : ℝ) > 0 := by
        have : (0 : ℕ) < N := Nat.one_pos.trans_le hN
        exact_mod_cast this
      have hNpos' : (N : ℝ) ≠ 0 := by linarith
      set t := fun (k : ℕ) => (k : ℝ) * s / (N : ℝ) with ht
      have ht0 : t 0 = 0 := by
        dsimp [t]; simp
      have htN : t N = s := by
        dsimp [t]
        field_simp [hNpos']
      have ht_nonneg : ∀ k, k ≤ N → 0 ≤ t k := by
        intro k hk
        dsimp [t]
        have hk' : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        positivity
      have ht_le_s : ∀ k, k ≤ N → t k ≤ s := by
        intro k hk
        dsimp [t]
        have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
        calc
          (k : ℝ) * s / (N : ℝ) ≤ (s * (N : ℝ)) / (N : ℝ) :=
            (div_le_div_of_nonneg_right (by nlinarith) (by positivity))
          _ = s := by field_simp [hNpos']
      have ht_mono : ∀ k, k < N → t k ≤ t (k+1) := by
        intro k hk
        dsimp [t]
        have hk' : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        calc
          (k : ℝ) * s / (N : ℝ) ≤ (((k+1 : ℕ) : ℝ) * s) / (N : ℝ) :=
            (div_le_div_of_nonneg_right (by nlinarith) (by positivity))
          _ = ((k+1 : ℕ) : ℝ) * s / (N : ℝ) := rfl
      -- telescoping sum identity
      have h_telescope : Ψ s - Ψ 0 = (∑ k ∈ Finset.range N, (Ψ (t (k+1)) - Ψ (t k))) := by
        calc
          Ψ s - Ψ 0 = (Ψ ∘ t) N - (Ψ ∘ t) 0 := by simp [ht0, htN]
          _ = (∑ k ∈ Finset.range N, ((Ψ ∘ t) (k+1) - (Ψ ∘ t) k)) := by rw [Finset.sum_range_sub]
          _ = (∑ k ∈ Finset.range N, (Ψ (t (k+1)) - Ψ (t k))) := rfl
      -- bound each term
      have h_each (k : ℕ) (hk : k < N) : Ψ (t (k+1)) - Ψ (t k) ≤ (s / (N : ℝ)) * (D 0 + C * t (k+1)) := by
        have h_nonneg_tk : 0 ≤ t k := ht_nonneg k (Nat.le_of_lt hk)
        have h_le_tk_tk1 : t k ≤ t (k+1) := ht_mono k hk
        have h_le_tk1_s : t (k+1) ≤ s := ht_le_s (k+1) (by omega)
        have hsub' := hsub (t k) (t (k+1)) h_nonneg_tk h_le_tk_tk1 h_le_tk1_s
        have h_diff : t (k+1) - t k = s / (N : ℝ) := by
          dsimp [t]
          field_simp [hNpos']
          push_cast
          ring
        rw [h_diff] at hsub'
        have hD' := hD (t (k+1)) (ht_nonneg (k+1) (by omega)) h_le_tk1_s
        nlinarith
      -- sum the bounds
      have h_sum : (∑ k ∈ Finset.range N, (Ψ (t (k+1)) - Ψ (t k))) ≤
          (∑ k ∈ Finset.range N, (s / (N : ℝ)) * (D 0 + C * t (k+1))) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        rw [Finset.mem_range] at hk
        exact h_each k hk
      -- compute the RHS sum
      have h_rhs : (∑ k ∈ Finset.range N, (s / (N : ℝ)) * (D 0 + C * t (k+1))) =
          s * D 0 + C * s ^ 2 / 2 + C * s ^ 2 / (2 * (N : ℝ)) := by
        calc
          (∑ k ∈ Finset.range N, (s / (N : ℝ)) * (D 0 + C * t (k+1)))
              = (s / (N : ℝ)) * (∑ k ∈ Finset.range N, (D 0 + C * t (k+1))) := by
            simp [Finset.mul_sum]
          _ = (s / (N : ℝ)) * ((∑ k ∈ Finset.range N, D 0) + C * (∑ k ∈ Finset.range N, t (k+1))) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          _ = (s / (N : ℝ)) * ((N : ℝ) * D 0 + C * (∑ k ∈ Finset.range N, t (k+1))) := by simp
          _ = (s / (N : ℝ)) * ((N : ℝ) * D 0 + C * (∑ k ∈ Finset.range N, ((k+1 : ℕ) : ℝ) * s / (N : ℝ))) := by
            have htemp : (∑ k ∈ Finset.range N, t (k+1)) = (∑ k ∈ Finset.range N, ((k+1 : ℕ) : ℝ) * s / (N : ℝ)) := by
              refine Finset.sum_congr rfl (fun k hk => ?_)
              simp [t]
            rw [htemp]
          _ = (s / (N : ℝ)) * ((N : ℝ) * D 0 + C * ((s / (N : ℝ)) * (∑ k ∈ Finset.range N, ((k : ℝ) + 1)))) := by
            have htemp2 : (∑ k ∈ Finset.range N, ((k+1 : ℕ) : ℝ) * s / (N : ℝ)) = (s / (N : ℝ)) * (∑ k ∈ Finset.range N, ((k : ℝ) + 1)) := by
              calc
                (∑ k ∈ Finset.range N, ((k+1 : ℕ) : ℝ) * s / (N : ℝ))
                    = (∑ k ∈ Finset.range N, (s / (N : ℝ)) * ((k : ℝ) + 1)) := by
                  refine Finset.sum_congr rfl (fun x hx => ?_)
                  push_cast
                  ring
                _ = (s / (N : ℝ)) * (∑ k ∈ Finset.range N, ((k : ℝ) + 1)) := by
                  simp [Finset.mul_sum]
            rw [htemp2]
          _ = (s / (N : ℝ)) * ((N : ℝ) * D 0 + C * (s / (N : ℝ)) * ((N : ℝ) * ((N : ℝ) + 1) / 2)) := by
            rw [hsum_succ N]
            ring
          _ = s * D 0 + C * s ^ 2 / 2 + C * s ^ 2 / (2 * (N : ℝ)) := by
            field_simp [hNpos']
            ring
      -- combine everything
      rw [h_telescope]
      calc
        (∑ k ∈ Finset.range N, (Ψ (t (k+1)) - Ψ (t k))) ≤
            (∑ k ∈ Finset.range N, (s / (N : ℝ)) * (D 0 + C * t (k+1))) := h_sum
        _ = s * D 0 + C * s ^ 2 / 2 + C * s ^ 2 / (2 * (N : ℝ)) := h_rhs
    by_cases hC : C ≤ 0
    · -- C ≤ 0: take N = 1
      have h1 : (1 : ℕ) ≥ 1 := by omega
      have hb := h_bound 1 h1
      have h_nonpos : C * s ^ 2 / (2 * (1 : ℝ)) ≤ 0 := by
        have : C * s ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
        nlinarith
      linarith
    · -- C > 0: use le_of_forall_pos_lt_add
      have hCpos : 0 < C := by linarith
      apply le_of_forall_pos_lt_add
      intro ε hε
      -- Choose N large enough so that C*s^2/(2N) < ε
      have h_exists_N : ∃ N : ℕ, N ≥ 1 ∧ C * s ^ 2 / (2 * (N : ℝ)) < ε := by
        have hN : ∃ N : ℕ, (C * s ^ 2) / (2 * ε) < (N : ℝ) := by
          exact exists_nat_gt ((C * s ^ 2) / (2 * ε))
        rcases hN with ⟨N, hN⟩
        refine ⟨max N 1, by omega, ?_⟩
        have hNpos' : 0 < (N : ℝ) := by
          by_contra! hNle
          have : (C * s ^ 2) / (2 * ε) < 0 := by linarith
          have hpos'' : 0 ≤ (C * s ^ 2) / (2 * ε) := by positivity
          linarith
        have hdiv : C * s ^ 2 / (2 * (N : ℝ)) < ε := by
          have hpos_ε : 0 < 2 * ε := by positivity
          have h_mul : C * s ^ 2 < 2 * ε * (N : ℝ) := by
            calc
              C * s ^ 2 = ((C * s ^ 2) / (2 * ε)) * (2 * ε) := by field_simp [ne_of_gt hpos_ε]
              _ < (N : ℝ) * (2 * ε) := mul_lt_mul_of_pos_right hN hpos_ε
              _ = 2 * ε * (N : ℝ) := by ring
          have hpos_N : 0 < 2 * (N : ℝ) := by positivity
          calc
            C * s ^ 2 / (2 * (N : ℝ)) < (2 * ε * (N : ℝ)) / (2 * (N : ℝ)) := by
              exact (div_lt_div_of_pos_right h_mul hpos_N)
            _ = ε := by field_simp [ne_of_gt hpos_N]
        have hmax : C * s ^ 2 / (2 * ((max N 1 : ℕ) : ℝ)) ≤ C * s ^ 2 / (2 * (N : ℝ)) := by
          have hmax' : (2 * (N : ℝ)) ≤ (2 * ((max N 1 : ℕ) : ℝ)) := by
            have h : (N : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact mod_cast Nat.le_max_left _ _
            exact mul_le_mul_of_nonneg_left h (by norm_num)
          have hnum : 0 ≤ C * s ^ 2 := by positivity
          -- div_le_div_of_nonneg_left ha hc h : a / b ≤ a / c when c ≤ b
          -- We have 2*N ≤ 2*max(N,1), so a/(2*max(N,1)) ≤ a/(2*N)
          exact div_le_div_of_nonneg_left hnum (by positivity) hmax'
        linarith
      rcases h_exists_N with ⟨N, hN, hNε⟩
      have hb := h_bound N hN
      linarith

theorem AdversarialBco.Poly.log_one_add_ge (s : ℝ) (hs : 0 ≤ s) : s - s ^ 2 / 2 ≤ Real.log (1 + s) := by
  have h_bound : s - s ^ 2 / 2 ≤ 2 * s / (s + 2) := by
    have h_denom_pos : 0 < s + 2 := by linarith
    field_simp [h_denom_pos.ne.symm]
    have h_nonneg_sq : 0 ≤ s ^ 3 := pow_nonneg hs 3
    nlinarith
  have h_log : 2 * s / (s + 2) ≤ Real.log (1 + s) := Real.le_log_one_add_of_nonneg hs
  exact le_trans h_bound h_log

theorem AdversarialBco.Poly.weighted_stein {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ) (K' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hK : ∀ g, HasFDerivAt K (K' g) g) (B : ℝ) (hb : ∀ g, |K g| ≤ B) (hb' : ∀ g, ‖K' g‖ ≤ B) (u : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪u, g⟫ ^ 2 * K' g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ∫ g, (⟪u, g⟫ ^ 3 - 2 * ‖u‖ ^ 2 * ⟪u, g⟫) * K g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain rfl : K' = fderiv ℝ K := funext fun g => (hK g).fderiv.symm
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun g => (hK g).continuousAt
  set a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ u with ha
  have haa : ∀ g, a g = ⟪u, g⟫ := fun g => innerSL_apply_apply (𝕜 := ℝ) u g
  have han : ‖a‖ = ‖u‖ := innerSL_apply_norm (𝕜 := ℝ) u
  have hag : ∀ g, |a g| ≤ ‖u‖ * ‖g‖ := fun g => by rw [haa]; exact abs_real_inner_le_norm u g
  set Φ' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := fun g =>
    (a g * a g) • fderiv ℝ K g + K g • (a g • a + a g • a) with hΦ'
  have hΦ : ∀ g, HasFDerivAt (fun y => a y * a y * K y) (Φ' g) g := fun g =>
    (a.hasFDerivAt.mul a.hasFDerivAt).mul (hK g)
  have hx2 : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 2 * Real.exp (1 * x) := fun x hx => by
    have := Real.pow_div_factorial_le_exp x hx 2
    rw [one_mul]
    norm_num [Nat.factorial] at this
    linarith
  have hx1 : ∀ x : ℝ, 0 ≤ x → x ≤ Real.exp (1 * x) := fun x _ => by
    rw [one_mul]
    linarith [Real.add_one_le_exp x]
  have hbΦ : ∀ g, |a g * a g * K g| ≤ 4 * B * ‖u‖ ^ 2 * Real.exp (1 * ‖g‖) := fun g => by
    have h1 : |a g| * |a g| ≤ (‖u‖ * ‖g‖) * (‖u‖ * ‖g‖) :=
      mul_le_mul (hag g) (hag g) (abs_nonneg _) (by positivity)
    have h2 : |a g| * |a g| * |K g| ≤ (‖u‖ * ‖g‖) * (‖u‖ * ‖g‖) * B :=
      mul_le_mul h1 (hb g) (abs_nonneg _) (by positivity)
    have h3 := hx2 ‖g‖ (norm_nonneg _)
    have h4 : (‖u‖ * ‖g‖) * (‖u‖ * ‖g‖) * B = B * ‖u‖ ^ 2 * ‖g‖ ^ 2 := by ring
    have h5 : B * ‖u‖ ^ 2 * ‖g‖ ^ 2 ≤ B * ‖u‖ ^ 2 * (2 * Real.exp (1 * ‖g‖)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h6 : 0 ≤ B * ‖u‖ ^ 2 * Real.exp (1 * ‖g‖) := by positivity
    rw [abs_mul, abs_mul]
    nlinarith
  have hbΦ' : ∀ g, ‖Φ' g‖ ≤ 4 * B * ‖u‖ ^ 2 * Real.exp (1 * ‖g‖) := fun g => by
    have hn : ‖Φ' g‖ ≤ |a g| * |a g| * ‖fderiv ℝ K g‖ + |K g| * (|a g| * ‖a‖ + |a g| * ‖a‖) := by
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_mul]
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
        rw [norm_smul, Real.norm_eq_abs]
    rw [han] at hn
    have h1 : |a g| * |a g| ≤ (‖u‖ * ‖g‖) * (‖u‖ * ‖g‖) :=
      mul_le_mul (hag g) (hag g) (abs_nonneg _) (by positivity)
    have h2 : |a g| * |a g| * ‖fderiv ℝ K g‖ ≤ (‖u‖ * ‖g‖) * (‖u‖ * ‖g‖) * B :=
      mul_le_mul h1 (hb' g) (norm_nonneg _) (by positivity)
    have h3 : |a g| * ‖u‖ + |a g| * ‖u‖ ≤ 2 * (‖u‖ ^ 2 * ‖g‖) := by
      have := mul_le_mul_of_nonneg_right (hag g) (norm_nonneg u)
      nlinarith
    have h4 : |K g| * (|a g| * ‖u‖ + |a g| * ‖u‖) ≤ B * (2 * (‖u‖ ^ 2 * ‖g‖)) :=
      mul_le_mul (hb g) h3 (by positivity) hB0
    have e2 := hx2 ‖g‖ (norm_nonneg _)
    have e1 := hx1 ‖g‖ (norm_nonneg _)
    have h5 : B * ‖u‖ ^ 2 * ‖g‖ ^ 2 ≤ B * ‖u‖ ^ 2 * (2 * Real.exp (1 * ‖g‖)) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    have h6 : B * ‖u‖ ^ 2 * ‖g‖ ≤ B * ‖u‖ ^ 2 * Real.exp (1 * ‖g‖) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    nlinarith
  have hS := AdversarialBco.Body.stein_dir (fun y => a y * a y * K y) Φ' hΦ (4 * B * ‖u‖ ^ 2) 1 hbΦ hbΦ' u
  have hΦu : ∀ g, Φ' g u = ⟪u, g⟫ ^ 2 * fderiv ℝ K g u + 2 * ‖u‖ ^ 2 * (⟪u, g⟫ * K g) := fun g => by
    simp only [hΦ', add_apply, smul_apply, smul_eq_mul, haa,
      real_inner_self_eq_norm_sq]
    ring
  have hm2 : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) 2 γ :=
    (innerSL ℝ u).comp_memLp' (IsGaussian.memLp_two_id (μ := γ))
  have hm3 : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) ((3 : ℕ) : ENNReal) γ :=
    (innerSL ℝ u).comp_memLp' (IsGaussian.memLp_id γ ((3 : ℕ) : ENNReal) (by simp))
  have hsq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 2) γ := hm2.integrable_sq
  have hab1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) γ := hm2.integrable one_le_two
  have hcube : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖⟪u, g⟫‖ ^ 3) γ :=
    hm3.integrable_norm_pow (by norm_num)
  have hmeasI : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) :=
    (continuous_const.inner continuous_id).measurable
  have I1 : Integrable (fun g => ⟪u, g⟫ ^ 2 * fderiv ℝ K g u) γ := by
    refine Integrable.mono' (hsq.const_mul (B * ‖u‖))
      ((hmeasI.pow_const 2).mul (measurable_fderiv_apply_const ℝ K u)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |fderiv ℝ K g u| ≤ B * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ K g).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hb' g) (norm_nonneg _))
    have := mul_le_mul_of_nonneg_left this (sq_nonneg ⟪u, g⟫)
    linarith
  have I2 : Integrable (fun g => ⟪u, g⟫ * K g) γ := by
    refine Integrable.mono' (hab1.norm.const_mul B) (hmeasI.mul hKc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul, Real.norm_eq_abs (K g)]
    have := mul_le_mul_of_nonneg_left (hb g) (norm_nonneg ⟪u, g⟫)
    linarith
  have I3 : Integrable (fun g => ⟪u, g⟫ ^ 3 * K g) γ := by
    refine Integrable.mono' (hcube.const_mul B) ((hmeasI.pow_const 3).mul hKc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul, norm_pow, Real.norm_eq_abs (K g)]
    have := mul_le_mul_of_nonneg_left (hb g) (pow_nonneg (norm_nonneg ⟪u, g⟫) 3)
    linarith
  have I2' : Integrable (fun g => 2 * ‖u‖ ^ 2 * (⟪u, g⟫ * K g)) γ := I2.const_mul _
  have eL : ∫ g, ⟪u, g⟫ * (a g * a g * K g) ∂γ = ∫ g, ⟪u, g⟫ ^ 3 * K g ∂γ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [haa]
    ring
  have eR : ∫ g, Φ' g u ∂γ = ∫ g, ⟪u, g⟫ ^ 2 * fderiv ℝ K g u ∂γ + 2 * ‖u‖ ^ 2 * ∫ g, ⟪u, g⟫ * K g ∂γ := by
    simp only [hΦu]
    rw [integral_add I1 I2', integral_const_mul]
  have eG : ∫ g, (⟪u, g⟫ ^ 3 - 2 * ‖u‖ ^ 2 * ⟪u, g⟫) * K g ∂γ =
      ∫ g, ⟪u, g⟫ ^ 3 * K g ∂γ - 2 * ‖u‖ ^ 2 * ∫ g, ⟪u, g⟫ * K g ∂γ := by
    rw [← integral_const_mul, ← integral_sub I3 I2']
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    ring
  rw [eL, eR] at hS
  rw [eG]
  linarith

theorem AdversarialBco.Poly.abs_cubic2_gauss :
    ∫ x, |x ^ 3 - 2 * x| ∂(ProbabilityTheory.gaussianReal 0 1) ≤ AdversarialBco.Poly.pgC2 := by
  rw [AdversarialBco.Body2.integral_gaussianReal_phi]
  have hφpos : ∀ t, 0 < AdversarialBco.BodySpec.phi t := fun t => by
    unfold AdversarialBco.BodySpec.phi
    positivity
  have hφe : ∀ t, AdversarialBco.BodySpec.phi (-t) = AdversarialBco.BodySpec.phi t := fun t => by
    unfold AdversarialBco.BodySpec.phi
    rw [neg_sq]
  have hφeq : ∀ t, AdversarialBco.BodySpec.phi t =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * t ^ 2) := fun t => by
    unfold AdversarialBco.BodySpec.phi
    rw [div_eq_mul_inv, one_div, mul_comm]
    congr 2
    ring
  have hhd : ∀ x, HasDerivAt (fun x : ℝ => x ^ 2 * AdversarialBco.BodySpec.phi x)
      ((2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x) x := fun x => by
    have h := (hasDerivAt_pow 2 x).mul (AdversarialBco.Body2.mills_antitone_hasDerivAt_phi x)
    exact h.congr_deriv (by push_cast; ring)
  have hcont : Continuous fun x : ℝ => x ^ 2 * AdversarialBco.BodySpec.phi x :=
    continuous_iff_continuousAt.2 fun x => (hhd x).continuousAt
  have hT : Tendsto (fun x : ℝ => x ^ 2 * AdversarialBco.BodySpec.phi x) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num : (0 : ℝ) < 2)
    have h2 : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h3 := (h2.comp h1).const_mul (2 / Real.sqrt (2 * Real.pi))
    rw [mul_zero] at h3
    refine h3.congr fun x => ?_
    simp only [Function.comp_apply]
    unfold AdversarialBco.BodySpec.phi
    rw [neg_div]
    field_simp
  have hB : Tendsto (fun x : ℝ => x ^ 2 * AdversarialBco.BodySpec.phi x) atBot (nhds 0) := by
    refine (hT.comp tendsto_neg_atBot_atTop).congr fun x => ?_
    simp only [Function.comp_apply, neg_sq, hφe]
  have i1 : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 1) (by norm_num)
    simpa only [Real.rpow_one] using h
  have i3 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(1 / 2) * x ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 3) (by norm_num)
    have e : (fun x : ℝ => x ^ (3 : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) =
        fun x : ℝ => x ^ 3 * Real.exp (-(1 / 2) * x ^ 2) := by
      funext x
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h
    exact h
  have hint : Integrable (fun x : ℝ => (2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x) := by
    have h := (i1.const_mul (2 / Real.sqrt (2 * Real.pi))).sub (i3.const_mul (1 / Real.sqrt (2 * Real.pi)))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hφeq]
    ring
  have hnint : Integrable (fun x : ℝ => -((2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x)) := hint.neg
  have habs : (fun x : ℝ => |x ^ 3 - 2 * x| * AdversarialBco.BodySpec.phi x) =
      fun x => |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x| := by
    funext x
    rw [abs_mul, abs_of_pos (hφpos x), abs_sub_comm]
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 2 := by positivity
  rw [habs]
  have hI : Integrable (fun x : ℝ => |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x|) := hint.abs
  -- the four pieces
  have P1 : ∫ x in Set.Iic (-Real.sqrt 2), |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x| =
      Real.sqrt 2 ^ 2 * AdversarialBco.BodySpec.phi (Real.sqrt 2) := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun x => (2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x)
      fun x hx => by
        have hx' : x ≤ -Real.sqrt 2 := hx
        have hx0 : x ≤ 0 := by linarith
        have hxx : 2 ≤ x ^ 2 := by nlinarith
        rw [abs_of_nonneg (mul_nonneg (by nlinarith) (hφpos x).le)]]
    rw [integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt (fun x _ => hhd x) hint.integrableOn hB,
      neg_sq, hφe, sub_zero]
  have P4 : ∫ x in Set.Ioi (Real.sqrt 2), |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x| =
      Real.sqrt 2 ^ 2 * AdversarialBco.BodySpec.phi (Real.sqrt 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => -((2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x))
      fun x hx => by
        have hx' : Real.sqrt 2 < x := hx
        have hxx : 2 ≤ x ^ 2 := by nlinarith
        rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (hφpos x).le)]]
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x => -(x ^ 2 * AdversarialBco.BodySpec.phi x))
      hcont.neg.continuousWithinAt (fun x _ => (hhd x).neg) hnint.integrableOn (by simpa using hT.neg)]
    ring
  have P2 : ∫ x in (-Real.sqrt 2)..0, |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x| =
      Real.sqrt 2 ^ 2 * AdversarialBco.BodySpec.phi (Real.sqrt 2) := by
    rw [intervalIntegral.integral_congr (g := fun x => -((2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x))
      fun x hx => by
        rw [Set.uIcc_of_le (by linarith)] at hx
        have hxx : x ^ 2 ≤ 2 := by nlinarith [hx.1, hx.2]
        rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hx.1, hx.2]) (hφpos x).le)]]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -(x ^ 2 * AdversarialBco.BodySpec.phi x))
      (fun x _ => (hhd x).neg) hnint.intervalIntegrable]
    simp only [neg_sq, hφe]
    ring
  have P3 : ∫ x in (0 : ℝ)..Real.sqrt 2, |(2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x| =
      Real.sqrt 2 ^ 2 * AdversarialBco.BodySpec.phi (Real.sqrt 2) := by
    rw [intervalIntegral.integral_congr (g := fun x => (2 * x - x ^ 3) * AdversarialBco.BodySpec.phi x)
      fun x hx => by
        rw [Set.uIcc_of_le hr0.le] at hx
        have hxx : x ^ 2 ≤ 2 := by nlinarith [hx.1, hx.2]
        rw [abs_of_nonneg (mul_nonneg (by nlinarith [hx.1, hx.2]) (hφpos x).le)]]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hhd x) hint.intervalIntegrable]
    ring
  have hsplit1 := intervalIntegral.integral_Iic_add_Ioi (b := Real.sqrt 2) hI.integrableOn hI.integrableOn
  have hsplit2 := intervalIntegral.integral_Iic_sub_Iic (a := -Real.sqrt 2) (b := Real.sqrt 2)
    hI.integrableOn hI.integrableOn
  have hsplit3 := intervalIntegral.integral_add_adjacent_intervals (a := -Real.sqrt 2) (b := 0) (c := Real.sqrt 2)
    hI.intervalIntegrable hI.intervalIntegrable
  have hval : 4 * (Real.sqrt 2 ^ 2 * AdversarialBco.BodySpec.phi (Real.sqrt 2)) = AdversarialBco.Poly.pgC2 := by
    unfold AdversarialBco.Poly.pgC2 AdversarialBco.BodySpec.phi
    rw [hr2]
    ring_nf
  linarith

theorem AdversarialBco.Poly.inner_abs_cubic2 {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∫ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ AdversarialBco.Poly.pgC2 := by
  have h_map := AdversarialBco.Body.map_inner_stdGaussian u hu
  have h_meas : AEStronglyMeasurable (fun (x : ℝ) => |x ^ 3 - 2 * x|)
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) := by
    refine (Continuous.aestronglyMeasurable ?_)
    fun_prop
  have h_ae_meas : AEMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine (Continuous.aemeasurable ?_)
    fun_prop
  calc
    ∫ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ x, |x ^ 3 - 2 * x| ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) := by
      rw [integral_map h_ae_meas h_meas]
    _ = ∫ x, |x ^ 3 - 2 * x| ∂(gaussianReal 0 1) := by rw [h_map]
    _ ≤ AdversarialBco.Poly.pgC2 := AdversarialBco.Poly.abs_cubic2_gauss

theorem AdversarialBco.Poly.curv_D_hasDeriv {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ≥0) (hF2 : ContDiff ℝ 2 F)
    (hM : LipschitzWith M (fderiv ℝ F)) (u : EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
      (∫ g, ⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((σ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) σ := by
  have hφ : ContDiff ℝ 1 (fun y => fderiv ℝ F y u) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφd : ∀ y, HasFDerivAt (fun y => fderiv ℝ F y u) (fderiv ℝ (fun y => fderiv ℝ F y u) y) y :=
    fun y => ((hφ.differentiable one_ne_zero) y).hasFDerivAt
  have hφL : LipschitzWith (M * ‖u‖₊) (fun y => fderiv ℝ F y u) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, ← sub_apply]
    calc ‖(fderiv ℝ F y - fderiv ℝ F y') u‖ ≤ ‖fderiv ℝ F y - fderiv ℝ F y'‖ * ‖u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * dist y y') * ‖u‖ := by
          gcongr
          rw [← dist_eq_norm]
          exact hM.dist_le_mul y y'
      _ = _ := by push_cast; ring
  have hφn : ∀ y, ‖fderiv ℝ (fun y => fderiv ℝ F y u) y‖ ≤ M * ‖u‖ := fun y => by
    simpa using norm_fderiv_le_of_lipschitz ℝ hφL
  have hpath : ∀ (g : EuclideanSpace ℝ (Fin d)) (τ : ℝ),
      HasDerivAt (fun τ : ℝ => g + ((τ - 1) * ⟪u, g⟫) • u) (⟪u, g⟫ • u) τ := fun g τ => by
    have h1 : HasDerivAt (fun τ : ℝ => (τ - 1) * ⟪u, g⟫) ⟪u, g⟫ τ := by
      simpa using ((hasDerivAt_id τ).sub_const 1).mul_const ⟪u, g⟫
    simpa using (h1.smul_const u).const_add g
  have hdiff : ∀ (g : EuclideanSpace ℝ (Fin d)) (τ : ℝ),
      HasDerivAt (fun τ => ⟪u, g⟫ * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u)
        (⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((τ - 1) * ⟪u, g⟫) • u) u) τ := fun g τ => by
    have h := ((hφd (g + ((τ - 1) * ⟪u, g⟫) • u)).comp_hasDerivAt τ (hpath g τ)).const_mul ⟪u, g⟫
    rw [map_smul, smul_eq_mul] at h
    exact h.congr_deriv (by ring)
  have hA : ∀ τ : ℝ, Continuous fun g : EuclideanSpace ℝ (Fin d) => g + ((τ - 1) * ⟪u, g⟫) • u := fun τ => by
    fun_prop
  have hmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun g => ⟪u, g⟫ * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun τ =>
    ((continuous_const.inner continuous_id).mul
      (((hF2.continuous_fderiv (by norm_num)).comp (hA τ)).clm_apply continuous_const)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun g => ⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((σ - 1) * ⟪u, g⟫) • u) u)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (((continuous_const.inner continuous_id).pow 2).mul
      (((hφ.continuous_fderiv one_ne_zero).comp (hA σ)).clm_apply continuous_const)).aestronglyMeasurable
  have hm : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa using (innerSL ℝ u).comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))))
  have hξ2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hm.integrable_sq
  have hn1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.integrable_id.norm
  have hn2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (memLp_two_iff_integrable_sq_norm IsGaussian.integrable_id.aestronglyMeasurable).1 IsGaussian.memLp_two_id
  have hbd : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖u‖ * |fderiv ℝ F 0 u|) * ‖g‖ +
      (‖u‖ * (M * ‖u‖) * (1 + |σ - 1| * ‖u‖ ^ 2)) * ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (hn1.const_mul _).add (hn2.const_mul _)
  have hint : Integrable (fun g => ⟪u, g⟫ * fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' hbd (hmeas σ) (Eventually.of_forall fun g => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hξg : |⟪u, g⟫| ≤ ‖u‖ * ‖g‖ := abs_real_inner_le_norm u g
    have hpg : ‖g + ((σ - 1) * ⟪u, g⟫) • u‖ ≤ (1 + |σ - 1| * ‖u‖ ^ 2) * ‖g‖ := by
      calc ‖g + ((σ - 1) * ⟪u, g⟫) • u‖ ≤ ‖g‖ + ‖((σ - 1) * ⟪u, g⟫) • u‖ := norm_add_le _ _
        _ = ‖g‖ + |σ - 1| * |⟪u, g⟫| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ ‖g‖ + |σ - 1| * (‖u‖ * ‖g‖) * ‖u‖ := by gcongr
        _ = (1 + |σ - 1| * ‖u‖ ^ 2) * ‖g‖ := by ring
    have hφb : |fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u| ≤
        |fderiv ℝ F 0 u| + M * ‖u‖ * ((1 + |σ - 1| * ‖u‖ ^ 2) * ‖g‖) := by
      have h := hφL.dist_le_mul (g + ((σ - 1) * ⟪u, g⟫) • u) 0
      rw [Real.dist_eq, dist_zero_right] at h
      push_cast at h
      have h2 := abs_sub_abs_le_abs_sub (fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u) (fderiv ℝ F 0 u)
      have h3 := mul_le_mul_of_nonneg_left hpg (by positivity : (0 : ℝ) ≤ M * ‖u‖)
      linarith
    calc |⟪u, g⟫| * |fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u|
        ≤ (‖u‖ * ‖g‖) * (|fderiv ℝ F 0 u| + M * ‖u‖ * ((1 + |σ - 1| * ‖u‖ ^ 2) * ‖g‖)) :=
          mul_le_mul hξg hφb (abs_nonneg _) (by positivity)
      _ = (‖u‖ * |fderiv ℝ F 0 u|) * ‖g‖ + (‖u‖ * (M * ‖u‖) * (1 + |σ - 1| * ‖u‖ ^ 2)) * ‖g‖ ^ 2 := by ring
  have hbound : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), ∀ τ ∈ (Set.univ : Set ℝ),
      ‖⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((τ - 1) * ⟪u, g⟫) • u) u‖ ≤
        (M * ‖u‖ * ‖u‖) * ⟪u, g⟫ ^ 2 := Eventually.of_forall fun g τ _ => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
    have h : ‖fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((τ - 1) * ⟪u, g⟫) • u) u‖ ≤ M * ‖u‖ * ‖u‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hφn _) (norm_nonneg _))
    nlinarith [sq_nonneg ⟪u, g⟫]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := σ) Filter.univ_mem
    (Eventually.of_forall fun τ => hmeas τ) hint hmeas' hbound (hξ2.const_mul _)
    (Eventually.of_forall fun g τ _ => hdiff g τ)).2

theorem AdversarialBco.Poly.curv_second_identity {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L M : ℝ≥0) (hF2 : ContDiff ℝ 2 F)
    (hFL : LipschitzWith L F) (hM : LipschitzWith M (fderiv ℝ F)) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (σ : ℝ) :
    σ * ∫ g, ⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((σ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, (⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫) * fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hφ : ContDiff ℝ 1 (fun y => fderiv ℝ F y u) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφd : ∀ y, HasFDerivAt (fun y => fderiv ℝ F y u) (fderiv ℝ (fun y => fderiv ℝ F y u) y) y :=
    fun y => ((hφ.differentiable one_ne_zero) y).hasFDerivAt
  have hφL : LipschitzWith (M * ‖u‖₊) (fun y => fderiv ℝ F y u) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, ← sub_apply]
    calc ‖(fderiv ℝ F y - fderiv ℝ F y') u‖ ≤ ‖fderiv ℝ F y - fderiv ℝ F y'‖ * ‖u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * dist y y') * ‖u‖ := by
          gcongr
          rw [← dist_eq_norm]
          exact hM.dist_le_mul y y'
      _ = _ := by push_cast; ring
  have hφn : ∀ y, ‖fderiv ℝ (fun y => fderiv ℝ F y u) y‖ ≤ M := fun y => by
    simpa [hu] using norm_fderiv_le_of_lipschitz ℝ hφL
  set Ac : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) + ((σ - 1) • innerSL ℝ u).smulRight u with hAc
  have hAcg : ∀ g, Ac g = g + ((σ - 1) * ⟪u, g⟫) • u := fun g => by simp [Ac]
  have hAcu : Ac u = σ • u := by
    rw [hAcg, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    module
  have hK : ∀ g, HasFDerivAt (fun g => fderiv ℝ F (Ac g) u)
      ((fderiv ℝ (fun y => fderiv ℝ F y u) (Ac g)).comp Ac) g :=
    fun g => (hφd (Ac g)).comp g Ac.hasFDerivAt
  have hb : ∀ g, |fderiv ℝ F (Ac g) u| ≤ max (L : ℝ) (M * ‖Ac‖) := fun g => by
    have h : |fderiv ℝ F (Ac g) u| ≤ L := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ F _).le_opNorm u).trans (by rw [hu, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hFL)
    exact h.trans (le_max_left _ _)
  have hb' : ∀ g, ‖(fderiv ℝ (fun y => fderiv ℝ F y u) (Ac g)).comp Ac‖ ≤ max (L : ℝ) (M * ‖Ac‖) := fun g =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hφn _) (norm_nonneg _)).trans (le_max_right _ _))
  have hW := AdversarialBco.Poly.weighted_stein (fun g => fderiv ℝ F (Ac g) u) _ hK _ hb hb' u
  simp only [ContinuousLinearMap.comp_apply, hAcu, map_smul, smul_eq_mul, hu, one_pow, mul_one] at hW
  simp only [hAcg] at hW
  rw [← integral_const_mul, ← hW]
  congr 1
  funext g
  ring

theorem AdversarialBco.Poly.curv_D_bound {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L M : ℝ≥0) (hF2 : ContDiff ℝ 2 F)
    (hFL : LipschitzWith L F) (hM : LipschitzWith M (fderiv ℝ F)) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (σ : ℝ) (hσ : 1 ≤ σ) :
    ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + ((σ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, ⟪u, g⟫ * fderiv ℝ F g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + AdversarialBco.Poly.pgC2 * L * (σ - 1) := by
  set D : ℝ → ℝ := fun τ : ℝ => ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
  set D2 : ℝ → ℝ := fun τ : ℝ => ∫ g, ⟪u, g⟫ ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y u) (g + ((τ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
  have hD1_eq : D 1 = ∫ g, ⟪u, g⟫ * fderiv ℝ F g u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [D]
    congr with g
    simp
  have h_deriv (τ : ℝ) : HasDerivAt D (D2 τ) τ := by
    dsimp [D, D2]
    exact AdversarialBco.Poly.curv_D_hasDeriv F M hF2 hM u τ
  have h_second (τ : ℝ) : τ * D2 τ = ∫ g, (⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫) * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [D2]
    exact AdversarialBco.Poly.curv_second_identity F L M hF2 hFL hM u hu τ
  have h_norm_fderiv (y : EuclideanSpace ℝ (Fin d)) : |fderiv ℝ F y u| ≤ (L : ℝ) := by
    have h_op_norm : ‖fderiv ℝ F y‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hFL
    have h_apply : ‖(fderiv ℝ F y) u‖ ≤ (L : ℝ) * ‖u‖ :=
      ContinuousLinearMap.le_of_opNorm_le_of_le (f := fderiv ℝ F y) (x := u) (a := (L : ℝ)) (b := ‖u‖) h_op_norm (le_refl ‖u‖)
    have h_val : |fderiv ℝ F y u| = ‖(fderiv ℝ F y) u‖ := by simp
    rw [h_val]
    calc
      ‖(fderiv ℝ F y) u‖ ≤ (L : ℝ) * ‖u‖ := h_apply
      _ = (L : ℝ) := by simp [hu]
  have h_memLp_inner (p : ENNReal) (hp : p ≠ ⊤) : MemLp (fun g => ⟪u, g⟫) p (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_id : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) p (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) p hp
    have h_inner : (fun g => ⟪u, g⟫) = (fun x => (innerSL ℝ u) (id x)) := by simp
    rw [h_inner]
    exact h_id.continuousLinearMap_comp (innerSL ℝ u)
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_integrable_abs_cubic : Integrable (fun g => |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫|) μ := by
    have h_memLp_3 : MemLp (fun g => ⟪u, g⟫) 3 μ := h_memLp_inner 3 (by norm_num)
    have h_memLp_1 : MemLp (fun g => ⟪u, g⟫) 1 μ := h_memLp_inner 1 (by norm_num)
    have h_int_norm_cube : Integrable (fun g => |⟪u, g⟫| ^ 3) μ := by
      have := h_memLp_3.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
      simpa [Real.norm_eq_abs] using this
    have h_int_norm_linear : Integrable (fun g => |⟪u, g⟫|) μ := by
      have h_int : Integrable (fun g => ⟪u, g⟫) μ := h_memLp_1.integrable (by norm_num : 1 ≤ (1 : ENNReal))
      exact h_int.abs
    have h_bound : ∀ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| ≤ |⟪u, g⟫| ^ 3 + 2 * |⟪u, g⟫| := by
      intro g
      calc
        |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| ≤ |⟪u, g⟫ ^ 3| + |2 * ⟪u, g⟫| := abs_sub _ _
        _ = |⟪u, g⟫| ^ 3 + 2 * |⟪u, g⟫| := by simp [abs_mul, abs_pow]
    have h_int_sum : Integrable (fun g => |⟪u, g⟫| ^ 3 + 2 * |⟪u, g⟫|) μ :=
      Integrable.add h_int_norm_cube (h_int_norm_linear.const_mul 2)
    have h_ae_meas : AEStronglyMeasurable (fun g => |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫|) μ := by
      have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫) := by
        refine Continuous.sub ?_ ?_
        · exact ((continuous_const.inner continuous_id).pow 3)
        · exact ((continuous_const.inner continuous_id).const_mul 2)
      exact (h_cont.abs).aestronglyMeasurable
    have h_upper_ae : (fun g => |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫|) ≤ᵐ[μ] (fun g => |⟪u, g⟫| ^ 3 + 2 * |⟪u, g⟫|) := by
      filter_upwards with g
      exact h_bound g
    have h_lower_ae : (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ᵐ[μ] (fun g => |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫|) := by
      filter_upwards with g
      exact abs_nonneg _
    have h_int_zero : Integrable (0 : EuclideanSpace ℝ (Fin d) → ℝ) μ := by
      apply integrable_zero
    exact integrable_of_le_of_le h_ae_meas h_lower_ae h_upper_ae h_int_zero h_int_sum
  have h_bound_D2 (τ : ℝ) (hτ : 1 ≤ τ) : D2 τ ≤ (L : ℝ) * AdversarialBco.Poly.pgC2 := by
    have hτ_pos : 0 < τ := by linarith
    have hτ_nonneg : 0 ≤ τ := by linarith
    have h_abs_bound : |τ * D2 τ| ≤ (L : ℝ) * AdversarialBco.Poly.pgC2 := by
      rw [h_second τ]
      calc
        |∫ g, (⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫) * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u ∂μ| ≤
            ∫ g, |(⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫) * fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
        _ = ∫ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| * |fderiv ℝ F (g + ((τ - 1) * ⟪u, g⟫) • u) u| ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with g
          simp [abs_mul]
        _ ≤ ∫ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| * (L : ℝ) ∂μ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards with g
            positivity
          · -- integrability of |...| * L
            have := h_integrable_abs_cubic.mul_const (L : ℝ)
            simpa [mul_comm] using this
          · filter_upwards with g
            have h := h_norm_fderiv (g + ((τ - 1) * ⟪u, g⟫) • u)
            have h_nonneg_abs : 0 ≤ |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| := abs_nonneg _
            nlinarith
        _ = (∫ g, |⟪u, g⟫ ^ 3 - 2 * ⟪u, g⟫| ∂μ) * (L : ℝ) := by rw [MeasureTheory.integral_mul_const]
        _ ≤ AdversarialBco.Poly.pgC2 * (L : ℝ) := by
          nlinarith [AdversarialBco.Poly.inner_abs_cubic2 u hu]
        _ = (L : ℝ) * AdversarialBco.Poly.pgC2 := by ring
    have h_D2_le_abs : D2 τ ≤ |D2 τ| := le_abs_self (D2 τ)
    have h_abs_D2_eq : |D2 τ| = |τ * D2 τ| / τ := by
      rw [abs_mul, abs_of_nonneg hτ_nonneg]
      field_simp [ne_of_gt hτ_pos]
    calc
      D2 τ ≤ |D2 τ| := h_D2_le_abs
      _ = |τ * D2 τ| / τ := h_abs_D2_eq
      _ ≤ ((L : ℝ) * AdversarialBco.Poly.pgC2) / τ := by
        exact div_le_div_of_nonneg_right h_abs_bound hτ_nonneg
      _ ≤ (L : ℝ) * AdversarialBco.Poly.pgC2 := by
        have h_prod_nonneg : 0 ≤ (L : ℝ) * AdversarialBco.Poly.pgC2 := by
          have hL : 0 ≤ (L : ℝ) := NNReal.coe_nonneg _
          have hpgC2 : 0 ≤ AdversarialBco.Poly.pgC2 := by
            unfold AdversarialBco.Poly.pgC2
            positivity
          exact mul_nonneg hL hpgC2
        exact div_le_self h_prod_nonneg hτ
  have h_convex : Convex ℝ (Set.Icc (1 : ℝ) σ) :=
    convex_Icc _ _
  have h_cont_D : ContinuousOn D (Set.Icc (1 : ℝ) σ) := by
    intro x hx
    have h_diff : DifferentiableAt ℝ D x := h_deriv x |>.differentiableAt
    exact h_diff.continuousAt.continuousWithinAt
  have h_diffOn : DifferentiableOn ℝ D (interior (Set.Icc (1 : ℝ) σ)) := by
    intro x hx
    have h_diff : DifferentiableAt ℝ D x := h_deriv x |>.differentiableAt
    exact h_diff.differentiableWithinAt
  have h_deriv_bound : ∀ x ∈ interior (Set.Icc (1 : ℝ) σ), deriv D x ≤ (L : ℝ) * AdversarialBco.Poly.pgC2 := by
    intro x hx
    have h_deriv_x : HasDerivAt D (D2 x) x := h_deriv x
    have h_deriv_eq : deriv D x = D2 x := h_deriv_x.deriv
    rw [h_deriv_eq]
    -- x ∈ interior (Icc 1 σ) implies 1 < x < σ, so in particular 1 ≤ x
    have hx_mem_Ioo : x ∈ Set.Ioo (1 : ℝ) σ := by
      rw [interior_Icc] at hx
      exact hx
    rcases hx_mem_Ioo with ⟨hx_low, hx_high⟩
    exact h_bound_D2 x hx_low.le
  have h_mem_1 : (1 : ℝ) ∈ Set.Icc (1 : ℝ) σ := Set.left_mem_Icc.mpr hσ
  have h_mem_σ : σ ∈ Set.Icc (1 : ℝ) σ := Set.right_mem_Icc.mpr hσ
  have h_ineq : D σ - D 1 ≤ ((L : ℝ) * AdversarialBco.Poly.pgC2) * (σ - 1) := by
    refine Convex.image_sub_le_mul_sub_of_deriv_le h_convex h_cont_D h_diffOn h_deriv_bound 1 h_mem_1 σ h_mem_σ hσ
  calc
    D σ = (D σ - D 1) + D 1 := by ring
    _ ≤ ((L : ℝ) * AdversarialBco.Poly.pgC2) * (σ - 1) + D 1 := by nlinarith
    _ = ((L : ℝ) * AdversarialBco.Poly.pgC2) * (σ - 1) + (∫ g, ⟪u, g⟫ * fderiv ℝ F g u ∂μ) := by rw [hD1_eq]
    _ = (∫ g, ⟪u, g⟫ * fderiv ℝ F g u ∂μ) + AdversarialBco.Poly.pgC2 * L * (σ - 1) := by ring

theorem AdversarialBco.Poly.curv_smooth {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L M : ℝ≥0) (hF2 : ContDiff ℝ 2 F)
    (hFc : ConvexOn ℝ Set.univ F) (hFL : LipschitzWith L F) (hM : LipschitzWith M (fderiv ℝ F)) (u : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (s : ℝ) (hs : 0 ≤ s) :
    ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + s * ∫ g, (⟪u, g⟫ ^ 2 - 1) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + AdversarialBco.Poly.pgC2 * L * s ^ 2 / 2 := by
  have hdiff : ∀ x, DifferentiableAt ℝ F x := fun x => (hF2.differentiable (by norm_num)) x
  have hT : ∀ (t : ℝ) (g : EuclideanSpace ℝ (Fin d)), (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) +
      (t • innerSL ℝ u).smulRight u) g = g + (t * ⟪u, g⟫) • u := fun t g => by simp
  have hcomp : ∀ t : ℝ, Integrable (fun g => F (g + (t * ⟪u, g⟫) • u)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro t
    have h := AdversarialBco.Poly.integrable_of_lipschitz _ _ (hFL.comp (ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin d)) + (t • innerSL ℝ u).smulRight u).lipschitzWith)
    simpa only [Function.comp_def, hT] using h
  have hξ : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa using (innerSL ℝ u).integrable_comp (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))))
  have hA : ∀ t : ℝ, Continuous fun g : EuclideanSpace ℝ (Fin d) => g + (t * ⟪u, g⟫) • u := fun t =>
    by fun_prop
  have hDint : ∀ t : ℝ, Integrable (fun g => ⟪u, g⟫ * fderiv ℝ F (g + (t * ⟪u, g⟫) • u) u)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro t
    refine Integrable.mono' (hξ.norm.const_mul (L : ℝ)) ?_ (Eventually.of_forall fun g => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (((hF2.continuous_fderiv (by norm_num)).comp (hA t)).clm_apply continuous_const)).aestronglyMeasurable
    · rw [norm_mul]
      have hN : ‖fderiv ℝ F (g + (t * ⟪u, g⟫) • u) u‖ ≤ L :=
        ((fderiv ℝ F _).le_opNorm u).trans (by rw [hu, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hFL)
      have := mul_le_mul_of_nonneg_left hN (norm_nonneg ⟪u, g⟫)
      linarith
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ s →
      ∫ g, F (g + (b * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
        ∫ g, F (g + (a * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      (b - a) * ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + (b * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro a b _ _ _
    rw [← integral_sub (hcomp b) (hcomp a), ← integral_const_mul]
    refine integral_mono ((hcomp b).sub (hcomp a)) ((hDint b).const_mul _) fun g => ?_
    dsimp only
    have h := AdversarialBco.Poly.convex_fderiv_subgrad F hFc (g + (b * ⟪u, g⟫) • u) (g + (a * ⟪u, g⟫) • u)
      (hdiff _)
    have e : (g + (a * ⟪u, g⟫) • u) - (g + (b * ⟪u, g⟫) • u) = (-((b - a) * ⟪u, g⟫)) • u := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      ring
    rw [e, map_smul, smul_eq_mul] at h
    nlinarith [h]
  have hD : ∀ t : ℝ, 0 ≤ t → t ≤ s →
      ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + (t * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + ((0 : ℝ) * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
          AdversarialBco.Poly.pgC2 * L * t := by
    intro t ht _
    have h := AdversarialBco.Poly.curv_D_bound F L M hF2 hFL hM u hu (1 + t) (by linarith)
    simp only [add_sub_cancel_left] at h
    simpa only [zero_mul, zero_smul, add_zero] using h
  have hTel := AdversarialBco.Poly.telescope_bound
    (fun t => ∫ g, F (g + (t * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
    (fun t => ∫ g, ⟪u, g⟫ * fderiv ℝ F (g + (t * ⟪u, g⟫) • u) u ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
    s (AdversarialBco.Poly.pgC2 * L) hs hsub hD
  have hI := AdversarialBco.Poly.ibp_lip2 F L hFL hFc u u
  have e : (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫ ^ 2 - 1) * F g) =
      fun g => (⟪u, g⟫ * ⟪u, g⟫ - ⟪u, u⟫) * F g := by
    funext g
    rw [real_inner_self_eq_norm_sq, hu]
    ring
  simp only [zero_mul, zero_smul, add_zero] at hTel
  rw [e, hI]
  linarith

theorem AdversarialBco.Poly.curvBound_main (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hFL : LipschitzWith L F)
    (hFc : ConvexOn ℝ Set.univ F) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (s : ℝ) (hs : 0 ≤ s) :
    ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + s * ∫ g, (⟪u, g⟫ ^ 2 - 1) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + AdversarialBco.Poly.pgC2 * L * s ^ 2 / 2 := by
  have hT : ∀ g : EuclideanSpace ℝ (Fin d), (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) +
      (s • innerSL ℝ u).smulRight u) g = g + (s * ⟪u, g⟫) • u := fun g => by simp
  have hcomp : ∀ (G : EuclideanSpace ℝ (Fin d) → ℝ) (L' : ℝ≥0), LipschitzWith L' G →
      Integrable (fun g => G (g + (s * ⟪u, g⟫) • u)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro G L' hG
    have h := AdversarialBco.Poly.integrable_of_lipschitz _ _ (hG.comp (ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin d)) + (s • innerSL ℝ u).smulRight u).lipschitzWith)
    simpa only [Function.comp_def, hT] using h
  have hmom : ∀ (G : EuclideanSpace ℝ (Fin d) → ℝ) (L' : ℝ≥0), LipschitzWith L' G →
      Integrable (fun g => (⟪u, g⟫ ^ 2 - 1) * G g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro G L' hG
    have h := (AdversarialBco.Poly.integrable_moments G L' hG u u).2.1
    have e : (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫ ^ 2 - 1) * G g) =
        fun g => (⟪u, g⟫ * ⟪u, g⟫ - ⟪u, u⟫) * G g := by
      funext g
      rw [real_inner_self_eq_norm_sq, hu]
      ring
    rw [e]
    exact h
  have hξ : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa using (innerSL ℝ u).comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))))
  have hξ2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hξ.integrable_sq
  have hξ21 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫ ^ 2 + 1)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hξ2.add (integrable_const 1)
  have hI2 : ∫ g, ⟪u, g⟫ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 1 := by
    rw [AdversarialBco.Body.integral_inner_sq, hu, one_pow]
  have key : ∀ ε > 0, ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        s * ∫ g, (⟪u, g⟫ ^ 2 - 1) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
          AdversarialBco.Poly.pgC2 * L * s ^ 2 / 2 + (2 + 2 * s) * ε := by
    intro ε hε
    obtain ⟨Fn, hFn2, hFnc, hFnL, ⟨M, hM⟩, hclose⟩ := AdversarialBco.Body.smooth_convex F L hFL hFc ε hε
    have hS := AdversarialBco.Poly.curv_smooth Fn L M hFn2 hFnc hFnL hM u hu s hs
    have h1 : ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, Fn (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + ε := by
      have hm : ∫ g, F (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, (Fn (g + (s * ⟪u, g⟫) • u) + ε) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (hcomp F L hFL) ((hcomp Fn L hFnL).add (integrable_const ε))
        (fun g => by
          have := (abs_le.mp (hclose (g + (s * ⟪u, g⟫) • u))).1
          show F _ ≤ Fn _ + ε
          linarith)
      rw [integral_add (hcomp Fn L hFnL) (integrable_const ε), integral_const] at hm
      simpa using hm
    have h2 : ∫ g, Fn g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + ε := by
      have hm : ∫ g, Fn g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, (F g + ε) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (AdversarialBco.Poly.integrable_of_lipschitz Fn L hFnL)
        ((AdversarialBco.Poly.integrable_of_lipschitz F L hFL).add (integrable_const ε))
        (fun g => by
          have := (abs_le.mp (hclose g)).2
          show Fn g ≤ F g + ε
          linarith)
      rw [integral_add (AdversarialBco.Poly.integrable_of_lipschitz F L hFL) (integrable_const ε),
        integral_const] at hm
      simpa using hm
    have h3 : ∫ g, (⟪u, g⟫ ^ 2 - 1) * Fn g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, (⟪u, g⟫ ^ 2 - 1) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + 2 * ε := by
      have hm : ∫ g, (⟪u, g⟫ ^ 2 - 1) * Fn g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, ((⟪u, g⟫ ^ 2 - 1) * F g + ε * (⟪u, g⟫ ^ 2 + 1)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (hmom Fn L hFnL) ((hmom F L hFL).add (hξ21.const_mul ε))
        (fun g => by
          have hc := abs_le.mp (hclose g)
          have hq : 0 ≤ ⟪u, g⟫ ^ 2 := sq_nonneg _
          show (⟪u, g⟫ ^ 2 - 1) * Fn g ≤ (⟪u, g⟫ ^ 2 - 1) * F g + ε * (⟪u, g⟫ ^ 2 + 1)
          have hd : (⟪u, g⟫ ^ 2 - 1) * Fn g - (⟪u, g⟫ ^ 2 - 1) * F g = (⟪u, g⟫ ^ 2 - 1) * (Fn g - F g) := by ring
          have hab : |(⟪u, g⟫ ^ 2 - 1) * (Fn g - F g)| ≤ ε * (⟪u, g⟫ ^ 2 + 1) := by
            rw [abs_mul, mul_comm ε]
            refine mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) (hclose g) (abs_nonneg _) (by linarith)
          linarith [le_abs_self ((⟪u, g⟫ ^ 2 - 1) * (Fn g - F g))])
      rw [integral_add (hmom F L hFL) (hξ21.const_mul ε), integral_const_mul,
        integral_add hξ2 (integrable_const 1), hI2, integral_const] at hm
      simp only [probReal_univ, smul_eq_mul, one_mul] at hm
      linarith
    have h3' := mul_le_mul_of_nonneg_left h3 hs
    nlinarith [h1, h2, h3', hS]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h2s : 0 < 2 + 2 * s := by linarith
  have h := key (ε / (2 + 2 * s)) (div_pos hε h2s)
  rwa [mul_div_cancel₀ _ h2s.ne'] at h

theorem AdversarialBco.Poly.grad_lip_bound {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hFL : LipschitzWith L F) (ν w : EuclideanSpace ℝ (Fin d)) :
    ∫ g, (F (g + ν) - F g) * ⟪w, g⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ L * ‖ν‖ * (‖w‖ * Real.sqrt (2 / Real.pi)) := by
  -- Let μ be the standard Gaussian measure
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hμ : IsGaussian μ := inferInstance
  -- The inner product with w is a continuous linear functional, hence integrable
  let Lw : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ w
  have h_int_inner : Integrable (fun g => ⟪w, g⟫) μ :=
    IsGaussian.integrable_dual μ Lw
  have h_int_abs_inner : Integrable (fun g => |⟪w, g⟫|) μ :=
    h_int_inner.abs
  -- The RHS constant
  set C := L * ‖ν‖ with hC_def
  -- The RHS is integrable
  have h_int_rhs : Integrable (fun g => C * |⟪w, g⟫|) μ :=
    h_int_abs_inner.const_mul C
  -- The LHS integrand is integrable
  have h_bound : ∀ᵐ g ∂μ, ‖F (g + ν) - F g‖ ≤ (C : ℝ) := by
    filter_upwards with g
    have h_dist : dist (F (g + ν)) (F g) ≤ (L : ℝ) * dist (g + ν) g :=
      hFL.dist_le_mul (g + ν) g
    have h_dist_eq_norm : dist (g + ν) g = ‖ν‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    have h_dist_F : dist (F (g + ν)) (F g) = |F (g + ν) - F g| := by
      rw [Real.dist_eq]
    rw [h_dist_F, h_dist_eq_norm] at h_dist
    have h : |F (g + ν) - F g| ≤ C := by
      simpa [hC_def] using h_dist
    -- Now we need ‖F(g+ν) - F g‖ ≤ C
    -- In ℝ, ‖x‖ = |x|
    simpa [Real.norm_eq_abs] using h
  have h_ae_meas : AEStronglyMeasurable (fun g => F (g + ν) - F g) μ := by
    -- F is Lipschitz, hence continuous, and translation is continuous
    have h_cont : Continuous F := hFL.continuous
    have h_cont_trans : Continuous (fun g => F (g + ν)) := h_cont.comp (continuous_add_const ν)
    have h_cont_sub : Continuous (fun g => F (g + ν) - F g) := h_cont_trans.sub h_cont
    exact h_cont_sub.aestronglyMeasurable
  have h_int_lhs : Integrable (fun g => (F (g + ν) - F g) * ⟪w, g⟫) μ :=
    h_int_inner.bdd_mul h_ae_meas h_bound
  -- Pointwise inequality: (F(g+ν) - F g) * ⟪w, g⟫ ≤ C * |⟪w, g⟫|
  have h_pointwise : ∀ g, (F (g + ν) - F g) * ⟪w, g⟫ ≤ C * |⟪w, g⟫| := by
    intro g
    have h_abs_bound : |F (g + ν) - F g| ≤ C := by
      have h_dist : dist (F (g + ν)) (F g) ≤ (L : ℝ) * dist (g + ν) g :=
        hFL.dist_le_mul (g + ν) g
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h_dist
      simpa [hC_def] using h_dist
    have h_mul_le : (F (g + ν) - F g) * ⟪w, g⟫ ≤ |F (g + ν) - F g| * |⟪w, g⟫| := by
      calc
        (F (g + ν) - F g) * ⟪w, g⟫ ≤ |(F (g + ν) - F g) * ⟪w, g⟫| := le_abs_self _
        _ = |F (g + ν) - F g| * |⟪w, g⟫| := abs_mul _ _
    have h_mul_le2 : |F (g + ν) - F g| * |⟪w, g⟫| ≤ C * |⟪w, g⟫| := by
      gcongr
    exact h_mul_le.trans h_mul_le2
  -- Now integrate
  have h_integral_ineq : ∫ g, (F (g + ν) - F g) * ⟪w, g⟫ ∂μ ≤ ∫ g, C * |⟪w, g⟫| ∂μ :=
    integral_mono h_int_lhs h_int_rhs h_pointwise
  -- Compute the RHS integral
  have h_integral_rhs : ∫ g, C * |⟪w, g⟫| ∂μ = C * (‖w‖ * Real.sqrt (2 / Real.pi)) := by
    rw [integral_const_mul C, AdversarialBco.Body.integral_abs_inner w]
  -- Combine
  rw [h_integral_rhs] at h_integral_ineq
  -- h_integral_ineq gives the goal
  simpa [hC_def, μ] using h_integral_ineq

theorem AdversarialBco.Poly.descent_bound {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hFL : LipschitzWith L F)
    (hFc : ConvexOn ℝ Set.univ F) (ν : EuclideanSpace ℝ (Fin d)) :
    ∫ g, F (g + ν) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + ⟪∫ g, F g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), ν⟫ + L * Real.sqrt (2 / Real.pi) * ‖ν‖ ^ 2 / 2 := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set Ψ : ℝ → ℝ := fun t => ∫ g, F (g + t • ν) ∂γ with hΨ
  set D : ℝ → ℝ := fun t => ∫ g, ⟪ν, g⟫ * F (g + t • ν) ∂γ with hDdef
  have hGL : ∀ t : ℝ, LipschitzWith L (fun y : EuclideanSpace ℝ (Fin d) => F (y + t • ν)) := fun t =>
    LipschitzWith.of_dist_le_mul fun x y => by
      have := hFL.dist_le_mul (x + t • ν) (y + t • ν)
      rwa [dist_add_right] at this
  have hGc : ∀ t : ℝ, ConvexOn ℝ Set.univ (fun y : EuclideanSpace ℝ (Fin d) => F (y + t • ν)) := fun t =>
    ⟨convex_univ, fun x _ y _ p q hp hq hpq => by
      have e : p • x + q • y + t • ν = p • (x + t • ν) + q • (y + t • ν) := by
        rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hpq, one_smul]
      simp only [smul_eq_mul]
      rw [e]
      exact hFc.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq⟩
  have hGi : ∀ t : ℝ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => F (g + t • ν)) γ := fun t =>
    AdversarialBco.Poly.integrable_of_lipschitz _ L (hGL t)
  have hGm : ∀ t : ℝ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪ν, g⟫ * F (g + t • ν)) γ := fun t =>
    (AdversarialBco.Poly.integrable_moments _ L (hGL t) ν ν).1
  have hFd : ∀ t : ℝ, ∀ g, |fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => F (y + t • ν)) g ν| ≤ L * ‖ν‖ :=
    fun t g => by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ _ g).le_opNorm ν).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hGL t)) (norm_nonneg _))
  have hIc : ∀ t : ℝ, Integrable (fun g => fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => F (y + t • ν)) g ν) γ :=
    fun t => Integrable.mono' (integrable_const (L * ‖ν‖))
      (measurable_fderiv_apply_const ℝ _ ν).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hFd t g)
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → Ψ b - Ψ a ≤ (b - a) * D b := by
    intro a b _ hab _
    have hae := AdversarialBco.Poly.gauss_ae_diff d _ L (hGL b)
    have hpt : ∀ᵐ g ∂γ, F (g + b • ν) - F (g + a • ν) ≤
        (b - a) * fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => F (y + b • ν)) g ν := by
      filter_upwards [hae] with g hg
      have hdF : DifferentiableAt ℝ F (g + b • ν) := (differentiableAt_comp_add_right _).1 hg
      rw [fderiv_comp_add_right]
      have h1 := AdversarialBco.Poly.convex_fderiv_subgrad F hFc (g + b • ν) (g + a • ν) hdF
      have e : g + a • ν - (g + b • ν) = (a - b) • ν := by
        rw [sub_smul]; abel
      rw [e, map_smul, smul_eq_mul] at h1
      linarith
    have hsI : Integrable (fun g : EuclideanSpace ℝ (Fin d) => F (g + b • ν) - F (g + a • ν)) γ := (hGi b).sub (hGi a)
    have hrI : Integrable (fun g => (b - a) * fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) => F (y + b • ν)) g ν) γ :=
      (hIc b).const_mul (b - a)
    have h2 := integral_mono_ae hsI hrI hpt
    rw [integral_sub (hGi b) (hGi a), integral_const_mul,
      ← AdversarialBco.Poly.ibp_lip1 _ L (hGL b) (hGc b) ν] at h2
    exact h2
  have hD : ∀ t, 0 ≤ t → t ≤ 1 → D t ≤ D 0 + L * Real.sqrt (2 / Real.pi) * ‖ν‖ ^ 2 * t := by
    intro t ht _
    have h1 := AdversarialBco.Poly.grad_lip_bound F L hFL (t • ν) ν
    have hD0 : D 0 = ∫ g, ⟪ν, g⟫ * F g ∂γ := by
      simp only [hDdef, zero_smul, add_zero]
    have hF0 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪ν, g⟫ * F g) γ :=
      (AdversarialBco.Poly.integrable_moments F L hFL ν ν).1
    have hdiff : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (F (g + t • ν) - F g) * ⟪ν, g⟫) γ := by
      refine ((hGm t).sub hF0).congr (Filter.Eventually.of_forall fun g => ?_)
      simp only [Pi.sub_apply]
      ring
    have e : D t = ∫ g, ⟪ν, g⟫ * F g ∂γ + ∫ g, (F (g + t • ν) - F g) * ⟪ν, g⟫ ∂γ := by
      rw [← integral_add hF0 hdiff]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      ring
    rw [e, hD0]
    rw [norm_smul, Real.norm_of_nonneg ht] at h1
    have : (L : ℝ) * (t * ‖ν‖) * (‖ν‖ * Real.sqrt (2 / Real.pi)) =
        L * Real.sqrt (2 / Real.pi) * ‖ν‖ ^ 2 * t := by ring
    linarith
  have hT := AdversarialBco.Poly.telescope_bound Ψ D 1 (L * Real.sqrt (2 / Real.pi) * ‖ν‖ ^ 2) zero_le_one hsub hD
  have hΨ1 : Ψ 1 = ∫ g, F (g + ν) ∂γ := by simp only [hΨ, one_smul]
  have hΨ0 : Ψ 0 = ∫ g, F g ∂γ := by simp only [hΨ, zero_smul, add_zero]
  have hD0 : D 0 = ⟪∫ g, F g • g ∂γ, ν⟫ := by
    rw [real_inner_comm, ← integral_inner (AdversarialBco.Poly.integrable_moments F L hFL ν ν).2.2]
    simp only [hDdef, zero_smul, add_zero, inner_smul_right]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    ring
  rw [hΨ1, hΨ0, hD0] at hT
  linarith

theorem AdversarialBco.Poly.propAii_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e t : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hd : 1 ≤ d) (hK : AdversarialBco.Poly.IsPosBody K r0 α) (hκ : 0 < κ) (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 → hstar ≤ AdversarialBco.Poly.posObj K κ μ' A')
    (he : AdversarialBco.Poly.posObj K κ μ A ≤ hstar + e) (L : ℝ≥0) (hL : LipschitzWith L (AdversarialBco.Poly.posF K μ A))
    (ht0 : 0 < t) (ht1 : t < 1) (het : e < t ^ 2 * (κ / d) ^ 2 / (2 * (AdversarialBco.Poly.pgC2 * L + κ / d)))
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) : (1 - t) * (κ / d) ≤ AdversarialBco.Poly.posQ K μ A u u := by
  rcases hK with ⟨hKconv, hKcomp, hr0pos, hball, hα_nonneg, hnegK⟩
  have hK_absorbent : Absorbent ℝ K := by
    have hball_absorbent : Absorbent ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r0) :=
      absorbent_ball_zero hr0pos
    exact hball_absorbent.mono hball
  have hposF_convex : ConvexOn ℝ Set.univ (AdversarialBco.Poly.posF K μ A) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    dsimp [AdversarialBco.Poly.posF]
    have hz : μ + A (a • x + b • y) = a • (μ + A x) + b • (μ + A y) := by
      calc
        μ + A (a • x + b • y) = μ + (a • A x + b • A y) := by simp [map_add, map_smul]
        _ = (a • μ + b • μ) + (a • A x + b • A y) := by rw [← add_smul a b μ, hab, one_smul]
        _ = (a • μ + a • A x) + (b • μ + b • A y) := by abel
        _ = a • (μ + A x) + b • (μ + A y) := by simp [smul_add]
    rw [hz]
    calc
      gauge K (a • (μ + A x) + b • (μ + A y)) ≤ gauge K (a • (μ + A x)) + gauge K (b • (μ + A y)) :=
        gauge_add_le hKconv hK_absorbent _ _
      _ = a • gauge K (μ + A x) + b • gauge K (μ + A y) := by
        rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb]
      _ = a * gauge K (μ + A x) + b * gauge K (μ + A y) := by simp
  set Q := AdversarialBco.Poly.posQ K μ A u u with hQdef
  by_contra! hQlt
  have hdpos : 0 < (d : ℝ) := by
    have hdpos' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hκdpos : 0 < κ / d := div_pos hκ hdpos
  have hpgC2pos : 0 < AdversarialBco.Poly.pgC2 := by
    refine div_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.sqrt_pos.mpr ?_)
    positivity
  have hdenpos : 0 < AdversarialBco.Poly.pgC2 * (L : ℝ) + κ / d := by
    positivity
  set s := t * (κ / d) / (AdversarialBco.Poly.pgC2 * (L : ℝ) + κ / d) with hs_def
  have hs_pos : 0 < s := by
    refine div_pos (mul_pos ht0 hκdpos) hdenpos
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  set Ps := (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) + s • ((innerSL ℝ u).smulRight u)) with hPs_def
  have hPs_action (g : EuclideanSpace ℝ (Fin d)) : Ps g = g + (s * ⟪u, g⟫) • u := by
    simp [Ps, hPs_def, ContinuousLinearMap.smulRight, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  set As := A.comp Ps with hAs_def
  have hdet_As : LinearMap.det (As : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rw [hAs_def]
    have hdet_comp : LinearMap.det ((A.comp Ps : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
      LinearMap.det (Ps : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      LinearMap.det_comp _ _
    rw [hdet_comp]
    have hdet_Ps : LinearMap.det (Ps : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 + s * ‖u‖ ^ 2 :=
      AdversarialBco.Poly.det_id_add_rank_one u s
    rw [hdet_Ps, hu]
    have h_target : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) * (1 + s) ≠ 0 := by
      have hpos : 0 < 1 + s := by linarith
      exact mul_ne_zero hA (by linarith)
    simpa [sq] using h_target
  have hposF_As (g : EuclideanSpace ℝ (Fin d)) :
    AdversarialBco.Poly.posF K μ As g = AdversarialBco.Poly.posF K μ A (Ps g) := by
    simp [AdversarialBco.Poly.posF, As, Ps, hAs_def, hPs_def]
  have hposK_As : AdversarialBco.Poly.posK K μ As =
    ∫ g, AdversarialBco.Poly.posF K μ A (Ps g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simp [AdversarialBco.Poly.posK, hposF_As]
  have hcurv := AdversarialBco.Poly.curvBound_main d (AdversarialBco.Poly.posF K μ A) L hL
    hposF_convex u hu s hs_nonneg
  have hposQ_eq : AdversarialBco.Poly.posQ K μ A u u =
    ∫ g, (⟪u, g⟫ ^ 2 - 1) * AdversarialBco.Poly.posF K μ A g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [AdversarialBco.Poly.posQ]
    refine integral_congr_ae ?_
    filter_upwards with g
    simp [hu, inner_self_eq_norm_sq, sq]
  have hposK_As_bound : AdversarialBco.Poly.posK K μ As ≤
    AdversarialBco.Poly.posK K μ A + s * Q + AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 := by
    calc
      AdversarialBco.Poly.posK K μ As = ∫ g, AdversarialBco.Poly.posF K μ As g ∂(stdGaussian _) := rfl
      _ = ∫ g, AdversarialBco.Poly.posF K μ A (Ps g) ∂(stdGaussian _) := by simp [hposF_As]
      _ = ∫ g, AdversarialBco.Poly.posF K μ A (g + (s * ⟪u, g⟫) • u) ∂(stdGaussian _) := by simp [hPs_action]
      _ ≤ ∫ g, AdversarialBco.Poly.posF K μ A g ∂(stdGaussian _) +
          s * ∫ g, (⟪u, g⟫ ^ 2 - 1) * AdversarialBco.Poly.posF K μ A g ∂(stdGaussian _) +
          AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 := hcurv
      _ = (∫ g, AdversarialBco.Poly.posF K μ A g ∂(stdGaussian _)) + s * Q +
          AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 := by rw [← hposQ_eq]
      _ = AdversarialBco.Poly.posK K μ A + s * Q + AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 := rfl
  have hlog_det_As : Real.log |LinearMap.det (As : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
    Real.log |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| + Real.log (1 + s) := by
    rw [hAs_def]
    have hdet_comp : LinearMap.det ((A.comp Ps : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
      LinearMap.det (Ps : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      LinearMap.det_comp _ _
    rw [hdet_comp]
    have hdet_Ps : LinearMap.det (Ps : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 + s * ‖u‖ ^ 2 :=
      AdversarialBco.Poly.det_id_add_rank_one u s
    rw [hdet_Ps, hu]
    -- target: Real.log |det A * (1 + s * 1^2)| = Real.log |det A| + Real.log (1 + s)
    -- simplify 1^2 = 1
    have h_sq_one : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h_sq_one, mul_one]
    have hpos : 0 < 1 + s := by linarith
    have habs_pos : 0 < |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
      abs_pos.mpr hA
    rw [abs_mul, abs_of_pos hpos, Real.log_mul habs_pos.ne' (by linarith), add_comm]
  have hposObj_As_bound : AdversarialBco.Poly.posObj K κ μ As ≤
    AdversarialBco.Poly.posObj K κ μ A + s * Q + AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 - (κ / d) * Real.log (1 + s) := by
    rw [AdversarialBco.Poly.posObj, AdversarialBco.Poly.posObj, hlog_det_As]
    nlinarith
  have hmin_As := hmin μ As hdet_As
  have hineq : (κ / d) * Real.log (1 + s) - s * Q - AdversarialBco.Poly.pgC2 * (L : ℝ) * s ^ 2 / 2 ≤ e := by
    linarith
  have hlog_ineq : s - s ^ 2 / 2 ≤ Real.log (1 + s) :=
    AdversarialBco.Poly.log_one_add_ge s hs_nonneg
  have hineq2 : s * (κ / d - Q) - s ^ 2 * (AdversarialBco.Poly.pgC2 * (L : ℝ) + κ / d) / 2 ≤ e := by
    nlinarith
  set D := AdversarialBco.Poly.pgC2 * (L : ℝ) + κ / d with hD_def
  have hDpos : 0 < D := hdenpos
  have hs_eq : s = t * (κ / d) / D := hs_def
  have h_kappa_diff_gt : t * (κ / d) < κ / d - Q := by
    linarith
  have h_main_ineq : t ^ 2 * (κ / d) ^ 2 / (2 * D) < s * (κ / d - Q) - s ^ 2 * D / 2 := by
    have h_sq_eq : s ^ 2 * D / 2 = t ^ 2 * (κ / d) ^ 2 / (2 * D) := by
      rw [hs_eq]
      have hDpos_ne : D ≠ 0 := by linarith
      field_simp [hDpos_ne]
    have h_diff_pos : 0 < κ / d - Q - t * (κ / d) := by linarith
    have h_gt : s * (t * (κ / d)) < s * (κ / d - Q) := mul_lt_mul_of_pos_left h_kappa_diff_gt hs_pos
    have h_s_t : s * (t * (κ / d)) = t ^ 2 * (κ / d) ^ 2 / D := by
      rw [hs_eq]
      have hDpos_ne : D ≠ 0 := by linarith
      field_simp [hDpos_ne]
    rw [h_s_t] at h_gt
    have h_target : t ^ 2 * (κ / d) ^ 2 / (2 * D) < s * (κ / d - Q) - s ^ 2 * D / 2 := by
      have h_sub : t ^ 2 * (κ / d) ^ 2 / D - s ^ 2 * D / 2 = t ^ 2 * (κ / d) ^ 2 / (2 * D) := by
        rw [h_sq_eq]
        field_simp [hDpos.ne']
        ring
      have h_ineq' : t ^ 2 * (κ / d) ^ 2 / D - s ^ 2 * D / 2 < s * (κ / d - Q) - s ^ 2 * D / 2 := by linarith
      linarith
    exact h_target
  have h_contra : e < s * (κ / d - Q) - s ^ 2 * D / 2 := by
    linarith
  rw [hD_def] at h_contra
  linarith

theorem AdversarialBco.Poly.propAiii_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ hstar e : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : AdversarialBco.Poly.IsPosBody K r0 α) (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)), LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 → hstar ≤ AdversarialBco.Poly.posObj K κ μ' A')
    (he : AdversarialBco.Poly.posObj K κ μ A ≤ hstar + e) (L : ℝ≥0) (hL : LipschitzWith L (AdversarialBco.Poly.posF K μ A)) :
    ‖AdversarialBco.Poly.posB K μ A‖ ^ 2 ≤ 2 * Real.sqrt (2 / Real.pi) * L * e := by
  set F := AdversarialBco.Poly.posF K μ A with hF_def
  set b := AdversarialBco.Poly.posB K μ A with hb_def
  set c := (L : ℝ) * Real.sqrt (2 / Real.pi) with hc_def
  have hF_convex : ConvexOn ℝ Set.univ F := (AdversarialBco.Poly.posF_convex K r0 α hK μ A).2
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    have hL_nonneg : 0 ≤ (L : ℝ) := L.2
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
    exact mul_nonneg hL_nonneg h_sqrt_nonneg
  have h_posF_shift (ν g : EuclideanSpace ℝ (Fin d)) : AdversarialBco.Poly.posF K (μ + A ν) A g = F (g + ν) := by
    dsimp [F, AdversarialBco.Poly.posF]
    calc
      gauge K ((μ + A ν) + A g) = gauge K (μ + A ν + A g) := rfl
      _ = gauge K (μ + (A ν + A g)) := by rw [add_assoc]
      _ = gauge K (μ + A (ν + g)) := by rw [← A.map_add]
      _ = gauge K (μ + A (g + ν)) := by rw [add_comm ν g]
  have h_posK_shift (ν : EuclideanSpace ℝ (Fin d)) :
      AdversarialBco.Poly.posK K (μ + A ν) A = ∫ g, F (g + ν) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [AdversarialBco.Poly.posK]
    rw [integral_congr_ae]
    filter_upwards with g
    rw [h_posF_shift ν g]
  have h_posK_eq : AdversarialBco.Poly.posK K μ A = ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [AdversarialBco.Poly.posK, F]
  have h_posB_eq : b = ∫ g, F g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [b, AdversarialBco.Poly.posB, F]
  have h_obj_shift_le (ν : EuclideanSpace ℝ (Fin d)) :
      AdversarialBco.Poly.posObj K κ (μ + A ν) A ≤ AdversarialBco.Poly.posObj K κ μ A + inner ℝ b ν + c * ‖ν‖ ^ 2 / 2 := by
    have h_db := AdversarialBco.Poly.descent_bound F L hL hF_convex ν
    rw [← h_posK_shift ν, ← h_posK_eq, ← h_posB_eq] at h_db
    rw [← hc_def] at h_db
    dsimp [AdversarialBco.Poly.posObj]
    linarith
  have h_ineq (ν : EuclideanSpace ℝ (Fin d)) : -inner ℝ b ν - c * ‖ν‖ ^ 2 / 2 ≤ e := by
    have h_obj := h_obj_shift_le ν
    have h_min := hmin (μ + A ν) A hA
    have h_min_self := hmin μ A hA
    linarith
  have h_ineq' (t : ℝ) (ht : 0 ≤ t) : t * ‖b‖ ^ 2 - c * (t ^ 2 * ‖b‖ ^ 2) / 2 ≤ e := by
    have hν := h_ineq (-t • b)
    have h_inner : inner ℝ b (-t • b) = -(t * ‖b‖ ^ 2) := by
      calc
        inner ℝ b (-t • b) = (-t) * inner ℝ b b := by rw [inner_smul_right]
        _ = (-t) * ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
        _ = -(t * ‖b‖ ^ 2) := by ring
    have h_norm : ‖-t • b‖ ^ 2 = t ^ 2 * ‖b‖ ^ 2 := by
      calc
        ‖-t • b‖ ^ 2 = (‖-t‖ * ‖b‖) ^ 2 := by rw [norm_smul]
        _ = (|-t| * ‖b‖) ^ 2 := by rw [Real.norm_eq_abs]
        _ = (t * ‖b‖) ^ 2 := by rw [abs_neg, abs_of_nonneg ht]
        _ = t ^ 2 * ‖b‖ ^ 2 := by ring
    rw [h_inner, h_norm] at hν
    nlinarith
  by_cases hc_zero : c = 0
  · have hsq_zero : ‖b‖ ^ 2 = 0 := by
      by_contra h_ne
      have h_pos : 0 < ‖b‖ ^ 2 := by
        have h_nonneg_sq : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
        exact lt_of_le_of_ne h_nonneg_sq (Ne.symm h_ne)
      set t := |e| / ‖b‖ ^ 2 + 1 with ht_def
      have ht_nonneg : 0 ≤ t := by
        dsimp [t]
        have h_div_nonneg : 0 ≤ |e| / ‖b‖ ^ 2 := div_nonneg (abs_nonneg _) (by positivity)
        nlinarith
      have h_ineq_t := h_ineq' t ht_nonneg
      rw [hc_zero] at h_ineq_t
      simp at h_ineq_t
      dsimp [t] at h_ineq_t
      have h_abs_le : e ≤ |e| := le_abs_self e
      have h_contra : |e| + ‖b‖ ^ 2 ≤ e := by
        have h_left : (|e| / ‖b‖ ^ 2) * ‖b‖ ^ 2 = |e| :=
          div_mul_cancel₀ (|e|) (h_pos.ne.symm)
        calc
          |e| + ‖b‖ ^ 2 = ((|e| / ‖b‖ ^ 2) * ‖b‖ ^ 2) + ‖b‖ ^ 2 := by rw [h_left]
          _ = (|e| / ‖b‖ ^ 2 + 1) * ‖b‖ ^ 2 := by ring
          _ ≤ e := h_ineq_t
      nlinarith
    rw [hsq_zero]
    have hRHS_nonneg : 0 ≤ 2 * Real.sqrt (2 / Real.pi) * (L : ℝ) * e := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
      have hL_nonneg : 0 ≤ (L : ℝ) := L.2
      have he_nonneg : 0 ≤ e := by
        have h_min_self := hmin μ A hA
        linarith
      nlinarith
    nlinarith
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_zero)
    set t := 1 / c with ht_def
    have ht_nonneg : 0 ≤ t := div_nonneg (by norm_num) (by linarith)
    have h_ineq_t := h_ineq' t ht_nonneg
    dsimp [t] at h_ineq_t
    field_simp [hc_pos.ne.symm] at h_ineq_t
    ring_nf at h_ineq_t
    dsimp [c] at h_ineq_t
    ring_nf at h_ineq_t ⊢
    nlinarith

theorem AdversarialBco.Poly.d5_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α κ : ℝ) (μ μ' : EuclideanSpace ℝ (Fin d)) (T T' Ti : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : AdversarialBco.Poly.IsPosBody K r0 α) (hT : IsSelfAdjoint T) (hT' : IsSelfAdjoint T')
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) (hpos' : ∀ v, v ≠ 0 → 0 < ⟪T' v, v⟫)
    (hinv : T.comp Ti = ContinuousLinearMap.id ℝ _ ∧ Ti.comp T = ContinuousLinearMap.id ℝ _) (hκ : 0 ≤ κ) :
    AdversarialBco.Poly.posObj K κ μ T + ⟪AdversarialBco.Poly.posB K μ T, Ti (μ' - μ)⟫ +
        ∑ i, AdversarialBco.Poly.posQ K μ T (EuclideanSpace.single i 1) (Ti ((T' - T) (EuclideanSpace.single i 1))) -
        κ / d * LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≤
      AdversarialBco.Poly.posObj K κ μ' T' := by
  rcases hinv with ⟨hT_Ti, hTi_T⟩
  rcases posF_convex K r0 α hK μ T with ⟨⟨L, hL⟩, hF_conv⟩
  rcases posF_convex K r0 α hK μ' T' with ⟨⟨L', hL'⟩, hF'_conv⟩
  -- T is injective from hpos
  have hT_inj : Function.Injective (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    intro x y h
    by_contra hne
    have hne' : x - y ≠ 0 := mt sub_eq_zero.mp hne
    have hpos_xy := hpos (x - y) hne'
    have hzero : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    -- Now hpos_xy : 0 < ⟪T (x - y), x - y⟫ where T is the continuous linear map
    -- But hzero is about the linear map. We need to relate them.
    have hzero' : (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (x - y) = 0 := by
      simpa [map_sub] using hzero
    rw [hzero'] at hpos_xy
    simp at hpos_xy
  have hT_det_ne_zero : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    intro hdet
    have hker := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))).mp hdet
    have hker_bot : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).ker = ⊥ := by
      rwa [LinearMap.ker_eq_bot]
    exact hker hker_bot
  -- F = posF K μ T is convex and L-Lipschitz
  set F := AdversarialBco.Poly.posF K μ T with hF_def
  set F' := AdversarialBco.Poly.posF K μ' T' with hF'_def
  have hF_ae_diff : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ F g :=
    AdversarialBco.Poly.gauss_ae_diff d F L hL
  -- Define M = Ti ∘ (T' - T)
  set M := Ti.comp (T' - T) with hM_def
  -- Relate F(g + v) to F'
  have h_F_shift (g : EuclideanSpace ℝ (Fin d)) : F (g + Ti (μ' - μ) + M g) = F' g := by
    dsimp [F, F', M, AdversarialBco.Poly.posF]
    have hT_Ti_μ'μ : (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ti (μ' - μ)) = μ' - μ := by
      have := congrArg (fun f => f (μ' - μ)) hT_Ti
      simpa [ContinuousLinearMap.comp_apply] using this
    have hT_Ti_T'T (v : EuclideanSpace ℝ (Fin d)) : (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ti ((T' - T) v)) = (T' - T) v := by
      have := congrArg (fun f => f ((T' - T) v)) hT_Ti
      simpa [ContinuousLinearMap.comp_apply] using this
    have hcalc : (μ + (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (g + Ti (μ' - μ) + Ti ((T' - T) g))) =
        (μ' + (T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g) := by
      calc
        μ + (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (g + Ti (μ' - μ) + Ti ((T' - T) g)) =
            μ + ((T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ti (μ' - μ)) + (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (Ti ((T' - T) g))) := by
          simp [ContinuousLinearMap.map_add, add_assoc]
        _ = μ + ((T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (μ' - μ) + (T' - T) g) := by
          rw [hT_Ti_μ'μ, hT_Ti_T'T]
        _ = (μ' + (T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g) := by
          have h : (T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g - (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g = (T' - T) g := by
            rfl
          -- Actually, this is just the definition of subtraction for linear maps
          -- The key identity: T g + ((T' - T) g) = T' g
          have hkey : (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (T' - T) g = (T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g := by
            simp [sub_apply, add_comm, add_left_comm, add_assoc]
          calc
            μ + ((T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (μ' - μ) + (T' - T) g) =
                μ + (((T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (T' - T) g) + (μ' - μ)) := by abel
            _ = μ + ((T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g + (μ' - μ)) := by rw [hkey]
            _ = μ' + (T' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) g := by
              abel
    rw [hcalc]
  -- Key inequality: F g + fderiv ℝ F g (Ti (μ' - μ) + M g) ≤ F' g  for a.e. g
  have h_key_ae : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))),
      F g + fderiv ℝ F g (Ti (μ' - μ) + M g) ≤ F' g := by
    filter_upwards [hF_ae_diff] with g hg_diff
    have h_subgrad := AdversarialBco.Poly.convex_fderiv_subgrad F hF_conv g (g + Ti (μ' - μ) + M g) hg_diff
    have h_simp : (g + Ti (μ' - μ) + M g) - g = Ti (μ' - μ) + M g := by
      abel
    rw [h_simp, h_F_shift g] at h_subgrad
    exact h_subgrad
  -- Integrability from Lipschitz and moments
  have h_int_F : Integrable F (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Poly.integrable_of_lipschitz F L hL
  have hn1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.integrable_id.norm
  have hFd : ∀ g w, |fderiv ℝ F g w| ≤ L * ‖w‖ := fun g w => by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ F g).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
  have hIc : ∀ w, Integrable (fun g => fderiv ℝ F g w) (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun w =>
    Integrable.mono' (integrable_const (L * ‖w‖)) (measurable_fderiv_apply_const ℝ F w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hFd g w)
  have hIv : ∀ v w, Integrable (fun g => ⟪v, g⟫ * fderiv ℝ F g w) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun v w => by
      refine Integrable.mono' (hn1.const_mul (‖v‖ * (L * ‖w‖)))
        (((continuous_const.inner continuous_id).measurable.mul
          (measurable_fderiv_apply_const ℝ F w)).aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := mul_le_mul (abs_real_inner_le_norm v g) (hFd g w) (abs_nonneg _) (by positivity)
      linarith
  have h_int_F' : Integrable F' (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    AdversarialBco.Poly.integrable_of_lipschitz F' L' hL'
  -- Use ibp_lip1 to relate ∫ fderiv F g (Ti (μ' - μ)) to ⟪posB, Ti (μ' - μ)⟫
  have h_int_fderiv_Ti : (∫ g, fderiv ℝ F g (Ti (μ' - μ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ⟪AdversarialBco.Poly.posB K μ T, Ti (μ' - μ)⟫ := by
    have h_ibp := AdversarialBco.Poly.ibp_lip1 F L hL hF_conv (Ti (μ' - μ))
    -- h_ibp : ∫ g, inner ℝ (Ti (μ' - μ)) g * F g = ∫ g, (fderiv ℝ F g) (Ti (μ' - μ))
    rw [← h_ibp]
    -- Now ∫ g, inner ℝ (Ti (μ' - μ)) g * F g = ⟪Ti (μ' - μ), ∫ g, F g • g⟫
    calc
      (∫ g, inner ℝ (Ti (μ' - μ)) g * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
          (∫ g, inner ℝ (Ti (μ' - μ)) (F g • g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [inner_smul_right, mul_comm]
      _ = inner ℝ (Ti (μ' - μ)) (∫ g, F g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
        rw [integral_inner (AdversarialBco.Poly.integrable_moments F L hL (Ti (μ' - μ)) (Ti (μ' - μ))).2.2 (Ti (μ' - μ))]
      _ = ⟪AdversarialBco.Poly.posB K μ T, Ti (μ' - μ)⟫ := by
        rw [AdversarialBco.Poly.posB, hF_def]
        rw [real_inner_comm]
  -- Use ibp_lip2 and basis expansion for the sum term
  have h_int_fderiv_M : (∫ g, fderiv ℝ F g (M g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∑ i, AdversarialBco.Poly.posQ K μ T (EuclideanSpace.single i 1) (Ti ((T' - T) (EuclideanSpace.single i 1))) := by
    have h_expand (g : EuclideanSpace ℝ (Fin d)) : M g = ∑ i : Fin d, (g i) • M (EuclideanSpace.single i 1) := by
      dsimp [M]
      have h_basis : g = ∑ i : Fin d, (g i) • EuclideanSpace.single i 1 := by
        simpa [EuclideanSpace.basisFun_apply] using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr g).symm
      calc
        (Ti.comp (T' - T)) g = Ti ((T' - T) g) := rfl
        _ = Ti ((T' - T) (∑ i : Fin d, (g i) • EuclideanSpace.single i 1)) := by
          conv =>
            lhs
            arg 2
            rw [h_basis]
        _ = Ti (∑ i : Fin d, (g i) • (T' - T) (EuclideanSpace.single i 1)) := by simp [map_sum, ContinuousLinearMap.map_smul]
        _ = ∑ i : Fin d, (g i) • Ti ((T' - T) (EuclideanSpace.single i 1)) := by simp [ContinuousLinearMap.map_smul]
        _ = ∑ i : Fin d, (g i) • ((Ti.comp (T' - T)) (EuclideanSpace.single i 1)) := rfl
    have h_fderiv_expand (g : EuclideanSpace ℝ (Fin d)) : fderiv ℝ F g (M g) =
        ∑ i : Fin d, (g i) • fderiv ℝ F g (M (EuclideanSpace.single i 1)) := by
      rw [h_expand g]
      -- Use map_sum for the linear map fderiv ℝ F g
      rw [map_sum (fderiv ℝ F g) (fun i => (g i) • M (EuclideanSpace.single i 1)) Finset.univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ContinuousLinearMap.map_smul]
    have h_eq : (fun g => fderiv ℝ F g (M g)) = (fun g => ∑ i : Fin d, (g i) • fderiv ℝ F g (M (EuclideanSpace.single i 1))) := by
      ext g; rw [h_fderiv_expand g]
    rw [h_eq, MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have h_inner : (fun g : EuclideanSpace ℝ (Fin d) => (g i) • fderiv ℝ F g (M (EuclideanSpace.single i 1))) =
          (fun g => ⟪EuclideanSpace.single i 1, g⟫ * fderiv ℝ F g (M (EuclideanSpace.single i 1))) := by
        ext g; simp [EuclideanSpace.inner_single_left]
      rw [h_inner]
      have h_ibp := AdversarialBco.Poly.ibp_lip2 F L hL hF_conv (EuclideanSpace.single i 1) (M (EuclideanSpace.single i 1))
      rw [← h_ibp]
      rfl
    · intro i _
      refine (hIv (EuclideanSpace.single i 1) (M (EuclideanSpace.single i 1))).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp [EuclideanSpace.inner_single_left]
  have hIM : Integrable (fun g => fderiv ℝ F g (M g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hIv (EuclideanSpace.single i 1)
      (M (EuclideanSpace.single i 1))
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    have hg : M g = ∑ i, g i • M (EuclideanSpace.single i 1) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr g]
      simp [map_sum, map_smul]
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, EuclideanSpace.inner_single_left]
    simp
  -- Now combine the inequalities
  have h_main : (∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) +
      (∫ g, fderiv ℝ F g (Ti (μ' - μ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) +
      (∫ g, fderiv ℝ F g (M g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
      (∫ g, F' g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    -- From h_int_ineq and integral_add
    have hsum : Integrable (fun g => F g + fderiv ℝ F g (Ti (μ' - μ)) + fderiv ℝ F g (M g))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := (h_int_F.add (hIc _)).add hIM
    have hF2 : Integrable (fun g => F g + fderiv ℝ F g (Ti (μ' - μ))) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      h_int_F.add (hIc _)
    have h1 : ∫ g, (F g + fderiv ℝ F g (Ti (μ' - μ)) + fderiv ℝ F g (M g)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, F' g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      integral_mono_ae hsum h_int_F' (by
        filter_upwards [h_key_ae] with g hg
        rw [map_add] at hg
        linarith)
    rw [integral_add hF2 hIM, integral_add h_int_F (hIc _)] at h1
    exact h1
  -- Now relate the integrals to posK
  have h_posK : (∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = AdversarialBco.Poly.posK K μ T := by
    rw [hF_def, AdversarialBco.Poly.posK]
  have h_posK' : (∫ g, F' g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) = AdversarialBco.Poly.posK K μ' T' := by
    rw [hF'_def, AdversarialBco.Poly.posK]
  -- Log-determinant inequality from logdet_concave_main
  have h_logdet : Real.log (LinearMap.det (T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≤
      Real.log (LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) +
      LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    AdversarialBco.Poly.logdet_concave_main T T' Ti hT hT' hpos hpos' ⟨hT_Ti, hTi_T⟩
  have h_logdet_mul : κ / d * Real.log (LinearMap.det (T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≤
      κ / d * Real.log (LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) +
      κ / d * LinearMap.trace ℝ _ ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left h_logdet (div_nonneg hκ (Nat.cast_nonneg d))
  unfold AdversarialBco.Poly.posObj
  rw [Real.log_abs, Real.log_abs]
  linarith [h_main, h_posK, h_posK', h_int_fderiv_Ti, h_int_fderiv_M, h_logdet_mul]

/-! ## Assemblies -/

namespace AdversarialBco.Poly

/-- `E F(μ + T g)` depends on `T` only through the law of `T g`. -/
theorem posK_congr_map {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hK : K ∈ 𝓝 0) (hKc : Convex ℝ K)
    (h : (stdGaussian (EuclideanSpace ℝ (Fin d))).map T = (stdGaussian (EuclideanSpace ℝ (Fin d))).map A) :
    posK K μ T = posK K μ A := by
  have hc : Continuous fun y : EuclideanSpace ℝ (Fin d) => gauge K (μ + y) :=
    (continuous_gauge hKc hK).comp (continuous_const.add continuous_id)
  have key : ∀ B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      posK K μ B = ∫ y, gauge K (μ + y) ∂((stdGaussian (EuclideanSpace ℝ (Fin d))).map B) := fun B => by
    rw [integral_map B.continuous.aemeasurable hc.aestronglyMeasurable]
    rfl
  rw [key T, key A, h]

/-- Lemma F.1 with a symmetric positive definite minimiser, from Lemma F.1, the polar square root and the value forms at
any minimiser. -/
theorem lemmaLSym_of (hL : LemmaL) (hP : PolarSym) (hM : LemmaLOfMin) : LemmaLSym := by
  intro d hd K r0 α κ hK hκ
  obtain ⟨μ, A, hA, hmin, -⟩ := hL d hd K r0 α κ hK hκ
  obtain ⟨T, hTs, hTpos, hmap, hdet⟩ := hP d A hA
  have hK0 : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hK.2.2.1) hK.2.2.2.1
  have hobj : posObj K κ μ T = posObj K κ μ A := by
    unfold posObj
    rw [posK_congr_map K μ A T hK0 hK.1 hmap, hdet]
  have hTdet : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rw [← abs_ne_zero, hdet, abs_ne_zero]; exact hA
  have hTmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      posObj K κ μ T ≤ posObj K κ μ' A' := fun μ' A' hA' => hobj ▸ hmin μ' A' hA'
  obtain ⟨hk, hb, hQ⟩ := hM d hd K r0 α κ μ T hK hκ hTdet hTmin
  exact ⟨μ, T, hTs, hTpos, hTmin, hk, hb, hQ⟩

theorem bisectSpec : BisectSpec := fun P p lo hi hP hlo hhi j => bisect_spec P p lo hi hP hlo hhi j

theorem gaugeBounds : GaugeBounds := fun d K ρ hρ hK h1 hρK x => gauge_bounds d K ρ hρ hK h1 hρK x

theorem lemmaB : LemmaB := fun d K ρ hρ hK hKc h1 hρK j η hη x => lemmaB_main d K ρ hρ hK hKc h1 hρK j η hη x

theorem piTildeMeasurable : PiTildeMeasurable := fun d K ρ hK j => piTilde_measurable d K ρ hK j

theorem d4Bounds : D4Bounds := fun d K τ0 τ1 R μ T hK h1 hτ0 hD => d4_main d K τ0 τ1 R μ T hK h1 hτ0 hD

theorem polarSym : PolarSym := fun d A hA => polarSym_main d A hA

theorem lemmaLSym : LemmaLSym := lemmaLSym_of lemmaL polarSym lemmaLOfMin

theorem d1Bounds : D1Bounds := fun d K ρ μ A hρ hK h1 hKρ => d1_bounds d K ρ μ A hρ hK h1 hKρ

theorem d1Inv : D1Inv := fun _ K μ A R' hA h1 hR u y hu hy => d1_inv K μ A R' hA h1 hR u y hu hy

theorem logDetConcave : LogDetConcave := fun _ T T' Ti hT hT' hp hp' hinv => logdet_concave_main T T' Ti hT hT' hp hp' hinv

theorem d5Subgrad : D5Subgrad := fun d K r0 α κ μ μ' T T' Ti hK hT hT' hp hp' hinv hκ =>
  d5_main d K r0 α κ μ μ' T T' Ti hK hT hT' hp hp' hinv hκ

theorem propAi : PropAi := fun d K r0 α κ hstar e μ A hd hK hκ hA hmin he hk =>
  propAi_main d K r0 α κ hstar e μ A hd hK hκ hA hmin he hk

theorem curvBound : CurvBound := fun d F L hFL hFc u hu s hs => curvBound_main d F L hFL hFc u hu s hs

theorem propAii : PropAii := fun d K r0 α κ hstar e t μ A hd hK hκ hA hmin he L hL ht0 ht1 het u hu =>
  propAii_main d K r0 α κ hstar e t μ A hd hK hκ hA hmin he L hL ht0 ht1 het u hu

theorem propAiii : PropAiii := fun d K r0 α κ hstar e μ A hK hA hmin he L hL =>
  propAiii_main d K r0 α κ hstar e μ A hK hA hmin he L hL

theorem vecCS : VecCS := fun _ ε hε => vecCS_main ε hε

theorem matCS : MatCS := fun _ ε hε => matCS_main ε hε

theorem frobStat : FrobStat := fun _ g => frobStat_main g

theorem gaussMoments : GaussMoments := gaussMoments_main

theorem momentsE : MomentsE := momentsE_main

theorem normMeanLower : NormMeanLower := normMeanLower_main

theorem sgdPathwise : SgdPathwise := fun _ _ _ D proj hproj xs hxs s Δ hs x v hx hx0 N =>
  sgd_pathwise D proj hproj xs hxs s Δ hs x v hx hx0 N

end AdversarialBco.Poly
