/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PosGauss
public import AdversarialBco.Body.Dil
public import AdversarialBco.Body.Smooth
public import AdversarialBco.Body2.Gauss2

@[expose] public section

/-!
# Lemma F.1 and Proposition F.2: proofs

Proofs of the interface statements of `AdversarialBco/Poly/PosGauss.lean`. The leaves, then
Proposition F.2 (a) (`propCa_main`, from
the bathtub bound, integration by parts and the a.e. gauge derivative bounds), Lemma F.1 (`lemmaLOfMin_main`,
`lemmaL_main`: a minimiser from `ec_min_exists`, `k = κ` by scaling, `b = 0` and `Q = (κ/d) I` from the first order
conditions), the radii bound `lemmaLRadii_main`, and one assembly per interface `Prop`.
-/

open AdversarialBco.Poly MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Topology
open Filter

/-! ## Leaves -/

theorem AdversarialBco.Poly.gauss_abs_cont (d : ℕ) : stdGaussian (EuclideanSpace ℝ (Fin d)) ≪ volume := by
  have hvol : (gaussianReal 0 1 : Measure ℝ) ≪ volume :=
    gaussianReal_absolutelyContinuous 0 (by norm_num)
  have hpi : (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) ≪
      (Measure.pi (fun _ : Fin d ↦ volume)) := by
    induction' d with d ih
    · -- d = 0: Fin 0 is empty
      have h_empty_gauss : (Measure.pi (fun _ : Fin 0 ↦ gaussianReal 0 1)) = Measure.dirac 0 :=
        MeasureTheory.Measure.pi_of_empty _ _
      have h_empty_vol : (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ))) = Measure.dirac 0 :=
        MeasureTheory.Measure.pi_of_empty _ _
      rw [h_empty_gauss, h_empty_vol]
    · -- d = d+1: use finSuccEquiv' to relate Fin (d+1) to Option (Fin d)
      let e : Fin (d+1) ≃ Option (Fin d) := finSuccEquiv' 0
      -- First prove the result for Option (Fin d) using pi_map_piOptionEquivProd
      have hpi_option : (Measure.pi (fun i : Option (Fin d) ↦ gaussianReal 0 1)) ≪
          (Measure.pi (fun i : Option (Fin d) ↦ (volume : Measure ℝ))) := by
        have h_prod : ((Measure.pi (fun i : Fin d ↦ gaussianReal 0 1)).prod (gaussianReal 0 1)) ≪
            ((Measure.pi (fun i : Fin d ↦ (volume : Measure ℝ))).prod (volume : Measure ℝ)) :=
          MeasureTheory.Measure.AbsolutelyContinuous.prod ih hvol
        have hmeas_symm : Measurable ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin d) ↦ ℝ)).symm :
          ((i : Fin d) → ℝ) × ℝ → (i : Option (Fin d)) → ℝ) :=
          (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin d) ↦ ℝ)).symm.measurable
        have h_mapped := MeasureTheory.Measure.AbsolutelyContinuous.map h_prod hmeas_symm
        -- h_mapped : map ... (prod ...) ≪ map ... (prod ...)
        -- pi_map_piOptionEquivProd says: map ... (prod ...) = Measure.pi ...
        -- So we rewrite h_mapped using these equalities
        simpa [MeasureTheory.Measure.pi_map_piOptionEquivProd (fun i : Option (Fin d) ↦ gaussianReal 0 1),
          MeasureTheory.Measure.pi_map_piOptionEquivProd (fun i : Option (Fin d) ↦ (volume : Measure ℝ))]
          using h_mapped
      -- Now transport from Option (Fin d) to Fin (d+1) using measurePreserving_piCongrLeft
      -- e.symm : Option (Fin d) ≃ Fin (d+1)
      have hmp_gauss := MeasureTheory.measurePreserving_piCongrLeft
        (μ := fun (_ : Fin (d+1)) ↦ gaussianReal 0 1) e.symm
      have hmp_vol := MeasureTheory.measurePreserving_piCongrLeft
        (μ := fun (_ : Fin (d+1)) ↦ (volume : Measure ℝ)) e.symm
      have hmeas : Measurable (MeasurableEquiv.piCongrLeft (fun _ : Fin (d+1) ↦ ℝ) e.symm) :=
        (MeasurableEquiv.piCongrLeft (fun _ : Fin (d+1) ↦ ℝ) e.symm).measurable
      -- Apply AbsolutelyContinuous.map
      have h_mapped := MeasureTheory.Measure.AbsolutelyContinuous.map hpi_option hmeas
      -- Rewrite using hmp_gauss.map_eq and hmp_vol.map_eq
      rw [hmp_gauss.map_eq, hmp_vol.map_eq] at h_mapped
      exact h_mapped
  calc
    stdGaussian (EuclideanSpace ℝ (Fin d)) = (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).map (WithLp.toLp 2) := by
      rw [ProbabilityTheory.map_pi_eq_stdGaussian]
    _ ≪ (Measure.pi (fun _ : Fin d ↦ volume)).map (WithLp.toLp 2) :=
      MeasureTheory.Measure.AbsolutelyContinuous.map hpi (WithLp.measurable_toLp 2 (Fin d → ℝ))
    _ = (volume : Measure (Fin d → ℝ)).map (WithLp.toLp 2) := by rw [MeasureTheory.volume_pi]
    _ = volume := (PiLp.volume_preserving_toLp (Fin d)).map_eq

theorem AdversarialBco.Poly.gauss_ae_diff (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith L F) : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ F g := by
  have h_vol : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ F x :=
    hF.ae_differentiableAt (μ := volume)
  exact (AdversarialBco.Poly.gauss_abs_cont d).ae_le h_vol

theorem AdversarialBco.Poly.diff_of_comp_affine {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (g : EuclideanSpace ℝ (Fin d)) (h : DifferentiableAt ℝ (fun y => G (b + S y)) g) :
    DifferentiableAt ℝ G (b + S g) ∧
      ∀ w, fderiv ℝ (fun y => G (b + S y)) g w = fderiv ℝ G (b + S g) (S w) := by
  -- Get a continuous linear equivalence from the nonzero determinant
  let S_equiv : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.equivOfDetNeZero (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) hS).toContinuousLinearEquiv
  let S_inv := S_equiv.symm
  have hS_apply (x : EuclideanSpace ℝ (Fin d)) : S_equiv x = S x := rfl
  have hS_inv_apply (x : EuclideanSpace ℝ (Fin d)) : S (S_inv x) = x := by
    calc
      S (S_inv x) = S_equiv (S_equiv.symm x) := by simp [S_inv, hS_apply]
      _ = x := by simp
  -- The affine map φ(x) = S⁻¹(x - b)
  let φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => S_inv (x - b)
  have hφ_at_target : φ (b + S g) = g := by
    dsimp [φ]
    have h_sub : b + S g - b = S g := by simp
    rw [h_sub]
    calc
      S_inv (S g) = S_equiv.symm (S g) := rfl
      _ = S_equiv.symm (S_equiv g) := by rw [hS_apply g]
      _ = g := by simp
  have hφ_diff : DifferentiableAt ℝ φ (b + S g) := by
    have : φ = (fun x => S_inv x - S_inv b) := by
      ext x; dsimp [φ]; simp
    rw [this]
    exact (S_inv.differentiableAt).sub (differentiableAt_const _)
  -- Show G = (fun y => G (b + S y)) ∘ φ
  have hG_eq : G = (fun y => G (b + S y)) ∘ φ := by
    ext x
    dsimp [φ]
    calc
      G x = G (b + (x - b)) := by simp
      _ = G (b + S (S_inv (x - b))) := by rw [hS_inv_apply (x - b)]
      _ = ((fun y => G (b + S y)) ∘ φ) x := rfl
  have hG_diff : DifferentiableAt ℝ G (b + S g) := by
    rw [hG_eq]
    have h' : DifferentiableAt ℝ (fun y => G (b + S y)) (φ (b + S g)) := by
      rw [hφ_at_target]
      exact h
    exact h'.comp (b + S g) hφ_diff
  -- Now prove the fderiv equality using the chain rule
  have hf_diff : DifferentiableAt ℝ (fun y => b + S y) g := by
    simpa using ((differentiableAt_const b).add (S.differentiableAt (x := g)))
  have h_fderiv_f : fderiv ℝ (fun y => b + S y) g = S := by
    simp [S.fderiv]
  have h_comp_fderiv : fderiv ℝ (G ∘ (fun y => b + S y)) g = (fderiv ℝ G ((fun y => b + S y) g)).comp (fderiv ℝ (fun y => b + S y) g) :=
    fderiv_comp (x := g) hG_diff hf_diff
  have h_fderiv_eq : ∀ w, fderiv ℝ (fun y => G (b + S y)) g w = fderiv ℝ G (b + S g) (S w) := by
    intro w
    calc
      fderiv ℝ (fun y => G (b + S y)) g w = (fderiv ℝ (G ∘ (fun y => b + S y)) g) w := rfl
      _ = ((fderiv ℝ G ((fun y => b + S y) g)).comp (fderiv ℝ (fun y => b + S y) g)) w := by rw [h_comp_fderiv]
      _ = (fderiv ℝ G (b + S g)) (fderiv ℝ (fun y => b + S y) g w) := rfl
      _ = (fderiv ℝ G (b + S g)) (S w) := by rw [h_fderiv_f]
  exact And.intro hG_diff h_fderiv_eq

theorem AdversarialBco.Poly.convex_squeeze {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (Fn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℕ → ℝ) (hFn : ∀ n, ConvexOn ℝ Set.univ (Fn n))
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (hclose : ∀ n y, |Fn n y - F y| ≤ ε n)
    (x : EuclideanSpace ℝ (Fin d)) (hFx : DifferentiableAt ℝ F x) (hFnx : ∀ n, DifferentiableAt ℝ (Fn n) x)
    (v : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n => fderiv ℝ (Fn n) x v) Filter.atTop (nhds (fderiv ℝ F x v)) := by
  set D := fderiv ℝ F x v with hD
  have hFx_has : HasFDerivAt F (fderiv ℝ F x) x := hFx.hasFDerivAt
  -- define the 1D restriction g(s) = F(x + s•v)
  set g : ℝ → ℝ := fun s => F (x + s • v) with hg
  have hg_diff : HasDerivAt g D 0 := by
    have hφ_deriv : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      have h_id : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id 0
      have h_smul : HasDerivAt (fun s : ℝ => s • v) v 0 := by
        simpa [one_smul] using HasDerivAt.smul_const h_id v
      simpa [add_comm] using (hasDerivAt_const_add_iff x).mpr h_smul
    have h_comp : HasFDerivAt (g : ℝ → ℝ)
        ((fderiv ℝ F x).comp ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v))) 0 := by
      have : g = F ∘ (fun s : ℝ => x + s • v) := by
        ext s; rfl
      rw [this]
      have hφ_fderiv : HasFDerivAt (fun s : ℝ => x + s • v)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0 := by
        have h := hφ_deriv.hasFDerivAt
        simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h
      have hFx_has' : HasFDerivAt F (fderiv ℝ F x) ((fun s : ℝ => x + s • v) 0) := by
        simpa using hFx_has
      exact HasFDerivAt.comp 0 hFx_has' hφ_fderiv
    rw [hasFDerivAt_iff_hasDerivAt] at h_comp
    simpa [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply] using h_comp
  -- For each n, define gn(s) = Fn n (x + s • v) and show it's convex and differentiable at 0
  have hgn_diff (n : ℕ) : HasDerivAt (fun s : ℝ => Fn n (x + s • v)) (fderiv ℝ (Fn n) x v) 0 := by
    have hFnx_has : HasFDerivAt (Fn n) (fderiv ℝ (Fn n) x) x := (hFnx n).hasFDerivAt
    have hφ_fderiv : HasFDerivAt (fun s : ℝ => x + s • v)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0 := by
      have hφ_deriv : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
        have h_id : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id 0
        have h_smul : HasDerivAt (fun s : ℝ => s • v) v 0 := by
          simpa [one_smul] using HasDerivAt.smul_const h_id v
        simpa [add_comm] using (hasDerivAt_const_add_iff x).mpr h_smul
      have h := hφ_deriv.hasFDerivAt
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h
    have hFnx_has' : HasFDerivAt (Fn n) (fderiv ℝ (Fn n) x) ((fun s : ℝ => x + s • v) 0) := by
      simpa using hFnx_has
    have h_comp := HasFDerivAt.comp 0 hFnx_has' hφ_fderiv
    rw [hasFDerivAt_iff_hasDerivAt] at h_comp
    convert h_comp using 1
    · ext s; rfl
    · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply]
  have hgn_convex (n : ℕ) : ConvexOn ℝ Set.univ (fun s : ℝ => Fn n (x + s • v)) := by
    let φ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).toAffineMap + AffineMap.const ℝ _ x
    have hφ_def : (φ : ℝ → EuclideanSpace ℝ (Fin d)) = fun s => x + s • v := by
      ext s
      simp [φ, ContinuousAffineMap.add_apply, AffineMap.const_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, add_comm]
    have h_convex_comp : ConvexOn ℝ (φ ⁻¹' Set.univ) (Fn n ∘ φ) :=
      (hFn n).comp_affineMap φ
    have h_preimage : φ ⁻¹' Set.univ = Set.univ := by simp
    rw [h_preimage] at h_convex_comp
    have : (Fn n ∘ φ) = (fun s : ℝ => Fn n (x + s • v)) := by
      rw [hφ_def]
      rfl
    simpa [this] using h_convex_comp
  -- Now prove the main limit
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hδ4 : 0 < δ / 4 := by linarith
  -- From HasDerivAt g D 0, the slope (g(s)-g(0))/s → D as s → 0
  have h_slope_tendsto : Filter.Tendsto (fun s : ℝ => slope g 0 s) (nhdsWithin 0 {0}ᶜ) (𝓝 D) :=
    hg_diff.tendsto_slope
  -- For the left difference quotient, define g_neg(s) = F(x - s•v) = g(-s)
  -- Then g_neg'(0) = -D, so slope g_neg 0 s → -D as s → 0
  set g_neg : ℝ → ℝ := fun s => F (x - s • v) with hg_neg
  have hg_neg_diff : HasDerivAt g_neg (-D) 0 := by
    -- g_neg = g ∘ (fun s => -s)
    have h_neg_deriv : HasDerivAt (fun s : ℝ => -s) (-1) 0 := by
      simpa using hasDerivAt_neg 0
    have hg_neg_eq : g_neg = g ∘ (fun s : ℝ => -s) := by
      ext s
      simp [hg_neg, hg, sub_eq_add_neg]
    rw [hg_neg_eq]
    -- g_neg'(0) = g'(g(0)) * (-1) = D * (-1) = -D
    -- Use HasDerivAt.comp
    have h_comp : HasDerivAt (g ∘ (fun s : ℝ => -s)) ((D : ℝ) * (-1)) 0 :=
      HasDerivAt.comp 0 (by simpa using hg_diff) h_neg_deriv
    simpa [mul_comm, hD] using h_comp
  have h_slope_tendsto_neg : Filter.Tendsto (fun s : ℝ => slope g_neg 0 s) (𝓝[≠] 0) (𝓝 (-D)) :=
    hg_neg_diff.tendsto_slope
  -- Now we have:
  -- slope g 0 s = (F(x+s•v) - F x) / s → D as s → 0
  -- slope g_neg 0 s = (F(x-s•v) - F x) / s → -D as s → 0
  -- So (F x - F(x-s•v))/s = -slope g_neg 0 s → D as s → 0

  -- Use the metric epsilon-delta characterization of the limit
  have h_slope_metric := (Metric.tendsto_nhdsWithin_nhds.mp h_slope_tendsto) (δ/4) (by linarith)
  have h_slope_neg_metric := (Metric.tendsto_nhdsWithin_nhds.mp h_slope_tendsto_neg) (δ/4) (by linarith)

  -- h_slope_metric : ∃ δ₁ > 0, ∀ x ∈ {0}ᶜ, dist x 0 < δ₁ → dist (slope g 0 x) D < δ/4
  -- h_slope_neg_metric : ∃ δ₂ > 0, ∀ x ∈ {0}ᶜ, dist x 0 < δ₂ → dist (slope g_neg 0 x) (-D) < δ/4

  rcases h_slope_metric with ⟨δ₁, hδ₁_pos, hδ₁⟩
  rcases h_slope_neg_metric with ⟨δ₂, hδ₂_pos, hδ₂⟩

  -- Choose s > 0 smaller than both δ₁ and δ₂
  set s := min (δ₁ / 2) (δ₂ / 2) with hs_def
  have hs_pos : s > 0 := by
    rw [hs_def]
    have hmin : 0 < min (δ₁ / 2) (δ₂ / 2) := by
      exact lt_min (half_pos hδ₁_pos) (half_pos hδ₂_pos)
    exact hmin
  have hs_lt_δ₁ : s < δ₁ := by
    rw [hs_def]
    calc
      min (δ₁ / 2) (δ₂ / 2) ≤ δ₁ / 2 := min_le_left _ _
      _ < δ₁ := by linarith
  have hs_lt_δ₂ : s < δ₂ := by
    rw [hs_def]
    calc
      min (δ₁ / 2) (δ₂ / 2) ≤ δ₂ / 2 := min_le_right _ _
      _ < δ₂ := by linarith

  -- Now s > 0 and s < δ₁, s < δ₂, so we can apply the metric bounds
  have h_slope_bound : dist (slope g 0 s) D < δ/4 := by
    apply hδ₁ (by
      -- s ∈ {0}ᶜ because s > 0
      simp [hs_pos.ne.symm])
    -- dist s 0 < δ₁
    rw [Real.dist_eq, sub_zero, abs_of_pos hs_pos]
    exact hs_lt_δ₁

  have h_slope_neg_bound : dist (slope g_neg 0 s) (-D) < δ/4 := by
    apply hδ₂ (by
      simp [hs_pos.ne.symm])
    rw [Real.dist_eq, sub_zero, abs_of_pos hs_pos]
    exact hs_lt_δ₂

  -- Now we have:
  -- |slope g 0 s - D| < δ/4
  -- |slope g_neg 0 s + D| < δ/4 (since dist (slope g_neg 0 s) (-D) = |slope g_neg 0 s + D|)

  -- From h_slope_bound, we get slope g 0 s ∈ (D - δ/4, D + δ/4)
  have h_slope_range : slope g 0 s ∈ Set.Ioo (D - δ/4) (D + δ/4) := by
    rw [Real.dist_eq] at h_slope_bound
    have h_abs : |slope g 0 s - D| < δ/4 := h_slope_bound
    rcases abs_lt.mp h_abs with ⟨h1, h2⟩
    constructor <;> linarith

  -- Similarly for slope g_neg 0 s
  have h_slope_neg_range : slope g_neg 0 s ∈ Set.Ioo (-D - δ/4) (-D + δ/4) := by
    rw [Real.dist_eq] at h_slope_neg_bound
    have h_abs : |slope g_neg 0 s - (-D)| < δ/4 := h_slope_neg_bound
    rcases abs_lt.mp h_abs with ⟨h1, h2⟩
    constructor <;> linarith

  -- Now we have s > 0 such that both slope bounds hold.
  -- From the slope bounds, we can derive bounds on Dn.

  -- For each n, we have from convexity:
  -- Dn ≤ (Fn n (x + s • v) - Fn n x) / s
  -- Dn ≥ (Fn n x - Fn n (x - s • v)) / s

  -- And from hclose:
  -- |Fn n (x + s • v) - F (x + s • v)| ≤ ε n
  -- |Fn n x - F x| ≤ ε n
  -- |Fn n (x - s • v) - F (x - s • v)| ≤ ε n

  -- So:
  -- (Fn n (x + s • v) - Fn n x) / s ≤ (F (x + s • v) - F x) / s + 2 ε n / s
  -- (Fn n x - Fn n (x - s • v)) / s ≥ (F x - F (x - s • v)) / s - 2 ε n / s

  -- And:
  -- slope g 0 s = (F (x + s • v) - F x) / s
  -- slope g_neg 0 s = (F (x - s • v) - F x) / s
  -- So (F x - F (x - s • v)) / s = -slope g_neg 0 s

  -- Therefore:
  -- Dn ≤ slope g 0 s + 2 ε n / s < D + δ/4 + 2 ε n / s
  -- Dn ≥ -slope g_neg 0 s - 2 ε n / s > D - δ/4 - 2 ε n / s

  -- Now choose N large enough so that 2 ε n / s < δ/4 for n ≥ N
  have hε_bound : Filter.Tendsto (fun n : ℕ => ε n / s) Filter.atTop (𝓝 0) := by
    -- Since ε n → 0 and s > 0, ε n / s → 0
    have := hε
    -- hε : Tendsto ε atTop (𝓝 0)
    -- Divide by s
    simpa [div_eq_mul_inv] using hε.div_const s

  -- Now we have s > 0 with the slope bounds.
  -- For each n, we prove |Dn - D| < δ using the convexity bounds.

  -- First, establish the convexity bounds for any n
  have h_upper (n : ℕ) : fderiv ℝ (Fn n) x v ≤ slope g 0 s + 2 * ε n / s := by
    -- From convexity: Dn ≤ (Fn n (x + s • v) - Fn n x) / s
    have h_conv := (hgn_convex n).le_slope_of_hasDerivAt (by simp) (by simp) hs_pos (hgn_diff n)
    rw [slope_def_field] at h_conv
    simp at h_conv
    -- h_conv : fderiv ℝ (Fn n) x v ≤ (Fn n (x + s • v) - Fn n x) / s
    -- From hclose: Fn n (x + s • v) ≤ F (x + s • v) + ε n
    -- From hclose: Fn n x ≥ F x - ε n
    have hclose1 : Fn n (x + s • v) ≤ F (x + s • v) + ε n := by
      have h := hclose n (x + s • v)
      rcases abs_le.mp h with ⟨h1, h2⟩
      linarith
    have hclose2 : F x - ε n ≤ Fn n x := by
      have h := hclose n x
      rcases abs_le.mp h with ⟨h1, h2⟩
      linarith
    -- So (Fn n (x + s • v) - Fn n x) / s ≤ ((F (x + s • v) + ε n) - (F x - ε n)) / s
    -- = (F (x + s • v) - F x) / s + 2 * ε n / s = slope g 0 s + 2 * ε n / s
    have h_div : (Fn n (x + s • v) - Fn n x) / s ≤ ((F (x + s • v) + ε n) - (F x - ε n)) / s := by
      -- Since s > 0, division preserves the inequality
      exact div_le_div_of_nonneg_right (sub_le_sub hclose1 hclose2) (by linarith)
    -- Now compute the RHS
    have h_rhs : ((F (x + s • v) + ε n) - (F x - ε n)) / s = slope g 0 s + 2 * ε n / s := by
      rw [slope_def_field]
      simp [hg]
      ring
    rw [h_rhs] at h_div
    linarith

  have h_lower (n : ℕ) : -slope g_neg 0 s - 2 * ε n / s ≤ fderiv ℝ (Fn n) x v := by
    -- From convexity: (Fn n x - Fn n (x - s • v)) / s ≤ Dn
    have h_neg_s : -s < 0 := by linarith
    have h_conv := (hgn_convex n).slope_le_of_hasDerivAt (by simp) (by simp) h_neg_s (hgn_diff n)
    rw [slope_def_field] at h_conv
    simp [neg_smul] at h_conv
    -- h_conv : (Fn n x + -Fn n (x + -(s • v))) / s ≤ fderiv ℝ (Fn n) x v
    -- Convert to subtraction form
    have h_conv' : (Fn n x - Fn n (x - s • v)) / s ≤ fderiv ℝ (Fn n) x v := by
      -- The two sides are equal by sub_eq_add_neg
      simpa [sub_eq_add_neg] using h_conv
    -- Now use h_conv'
    -- From hclose: Fn n x ≥ F x - ε n
    -- From hclose: Fn n (x - s • v) ≤ F (x - s • v) + ε n
    have hclose1 : F x - ε n ≤ Fn n x := by
      have h := hclose n x
      rcases abs_le.mp h with ⟨h1, h2⟩
      linarith
    have hclose2 : Fn n (x - s • v) ≤ F (x - s • v) + ε n := by
      have h := hclose n (x - s • v)
      rcases abs_le.mp h with ⟨h1, h2⟩
      linarith
    -- So (Fn n x - Fn n (x - s • v)) / s ≥ ((F x - ε n) - (F (x - s • v) + ε n)) / s
    -- = (F x - F (x - s • v)) / s - 2 * ε n / s = -slope g_neg 0 s - 2 * ε n / s
    have h_div : ((F x - ε n) - (F (x - s • v) + ε n)) / s ≤ (Fn n x - Fn n (x - s • v)) / s := by
      -- Since s > 0, division preserves the inequality
      exact div_le_div_of_nonneg_right (sub_le_sub hclose1 hclose2) (by linarith)
    -- Now compute the LHS
    have h_lhs : ((F x - ε n) - (F (x - s • v) + ε n)) / s = -slope g_neg 0 s - 2 * ε n / s := by
      rw [slope_def_field]
      simp [hg_neg, hg, sub_eq_add_neg]
      ring
    rw [h_lhs] at h_div
    linarith

  -- Now we have:
  -- slope g_neg 0 s - 2 * ε n / s ≤ Dn ≤ slope g 0 s + 2 * ε n / s

  -- From the slope bounds:
  -- slope g 0 s < D + δ/4
  -- slope g_neg 0 s > -D - δ/4 (since it's in Ioo (-D-δ/4) (-D+δ/4))

  have h_slope_lt : slope g 0 s < D + δ/4 := by
    rcases h_slope_range with ⟨hlo, hhi⟩
    exact hhi

  have h_slope_gt : -D - δ/4 < slope g_neg 0 s := by
    rcases h_slope_neg_range with ⟨hlo, hhi⟩
    exact hlo

  -- Now for any n, we have:
  -- Dn ≤ slope g 0 s + 2 * ε n / s < D + δ/4 + 2 * ε n / s
  -- Dn ≥ slope g_neg 0 s - 2 * ε n / s > -D - δ/4 - 2 * ε n / s

  -- Choose N large enough so that 2 * ε n / s < δ/4 for n ≥ N
  have hε_tendsto : Filter.Tendsto (fun n : ℕ => 2 * ε n / s) Filter.atTop (𝓝 0) := by
    -- Since ε n → 0, 2 * ε n / s → 0
    -- hε : Tendsto ε atTop (𝓝 0)
    -- Multiply by 2/s (which is a constant)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hε.const_mul (2 / s)

  -- Now use the metric epsilon-delta for hε_tendsto
  have hε_metric := (Metric.tendsto_atTop.mp hε_tendsto) (δ/4) (by linarith)
  -- hε_metric : ∃ N, ∀ n ≥ N, dist (2 * ε n / s) 0 < δ/4
  -- i.e., |2 * ε n / s| < δ/4, i.e., 2 * ε n / s < δ/4 (since ε n ≥ 0? not necessarily, but we can use absolute value)

  rcases hε_metric with ⟨N, hN⟩

  -- Now we need to show: for all n ≥ N, |fderiv ℝ (Fn n) x v - D| < δ
  -- Actually, the goal is already rewritten using Metric.tendsto_atTop, so we need:
  -- ∃ N, ∀ n ≥ N, dist (fderiv ℝ (Fn n) x v) D < δ

  refine ⟨N, ?_⟩
  intro n hn

  -- For n ≥ N, we have |2 * ε n / s| < δ/4
  have hε_bound : |2 * ε n / s| < δ/4 := by
    -- From hN: dist (2 * ε n / s) 0 < δ/4
    have h := hN n hn
    -- h : dist (2 * ε n / s) 0 < δ/4
    rw [Real.dist_eq, sub_zero] at h
    -- h : |2 * ε n / s| < δ/4
    exact h

  -- Since 2 * ε n / s may be negative, we use absolute value
  have hε_bound' : 2 * ε n / s < δ/4 := by
    have : |2 * ε n / s| < δ/4 := hε_bound
    linarith [abs_lt.mp this]

  -- Now combine the bounds
  have h_upper_bound : fderiv ℝ (Fn n) x v < D + δ/2 := by
    -- Dn ≤ slope g 0 s + 2 * ε n / s < D + δ/4 + δ/4 = D + δ/2
    have h := h_upper n
    have h_slope_bound' : slope g 0 s < D + δ/4 := h_slope_lt
    have : fderiv ℝ (Fn n) x v < D + δ/4 + 2 * ε n / s := by linarith
    have : D + δ/4 + 2 * ε n / s < D + δ/4 + δ/4 := by linarith
    linarith

  have h_lower_bound : D - δ/2 < fderiv ℝ (Fn n) x v := by
    -- h_lower n : -slope g_neg 0 s - 2 * ε n / s ≤ Dn
    -- h_slope_neg_range gives: slope g_neg 0 s < -D + δ/4
    -- So -slope g_neg 0 s > D - δ/4
    -- Thus Dn ≥ -slope g_neg 0 s - 2 * ε n / s > D - δ/4 - 2 * ε n / s > D - δ/4 - δ/4 = D - δ/2
    have h_low := h_lower n
    have h_slope_hi : slope g_neg 0 s < -D + δ/4 := by
      rcases h_slope_neg_range with ⟨hlo, hhi⟩
      exact hhi
    have h_neg_slope : D - δ/4 < -slope g_neg 0 s := by linarith
    have h_ε_bound : 2 * ε n / s < δ/4 := by
      -- From hε_bound: |2 * ε n / s| < δ/4
      -- So 2 * ε n / s < δ/4
      have : |2 * ε n / s| < δ/4 := hε_bound
      rcases abs_lt.mp this with ⟨hlo', hhi'⟩
      exact hhi'
    linarith

  -- Then |Dn - D| < δ/2 < δ
  rw [Real.dist_eq]
  have h_abs : |fderiv ℝ (Fn n) x v - D| < δ := by
    -- We have D - δ/2 < Dn < D + δ/2
    -- So |Dn - D| < δ/2 < δ
    have h_lt : -(δ/2) < fderiv ℝ (Fn n) x v - D ∧ fderiv ℝ (Fn n) x v - D < δ/2 := by
      constructor
      · linarith
      · linarith
    rcases h_lt with ⟨hlo, hhi⟩
    rw [abs_lt]
    constructor <;> linarith
  exact h_abs

theorem AdversarialBco.Poly.gauge_convexOn {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d))) : ConvexOn ℝ Set.univ (gauge K) := by
  have habs : Absorbent ℝ K := absorbent_nhds_zero hK0
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  calc
    gauge K (a • x + b • y) ≤ gauge K (a • x) + gauge K (b • y) :=
      gauge_add_le hK habs (a • x) (b • y)
    _ = (a • gauge K x) + (b • gauge K y) := by
      rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb]
    _ = a * gauge K x + b * gauge K y := by simp

theorem AdversarialBco.Poly.fderiv_gauge_le {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d))) (x z : EuclideanSpace ℝ (Fin d))
    (hx : DifferentiableAt ℝ (gauge K) x) : fderiv ℝ (gauge K) x z ≤ gauge K z := by
  have h_abs : Absorbent ℝ K := absorbent_nhds_zero hK0
  have h_add := gauge_add_le hK h_abs
  set g := fun (s : ℝ) => gauge K (x + s • z) with hg
  have hg_deriv : HasDerivAt g (fderiv ℝ (gauge K) x z) 0 := by
    have h_fderiv : HasFDerivAt (gauge K) (fderiv ℝ (gauge K) x) x := hx.hasFDerivAt
    have h_line : HasLineDerivAt ℝ (gauge K) ((fderiv ℝ (gauge K) x) z) x z :=
      h_fderiv.hasLineDerivAt z
    simpa [g, hg, HasLineDerivAt] using h_line
  have h_slope_bound : ∀ᶠ (s : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi 0), slope g 0 s ≤ gauge K z := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs_nonneg : 0 ≤ s := le_of_lt hs
    have hs_pos : 0 < s := hs
    have h_gauge_smul : gauge K (s • z) = s • gauge K z :=
      gauge_smul_of_nonneg (s := K) (a := s) (ha := hs_nonneg) (x := z)
    have h_add_bound : gauge K (x + s • z) ≤ gauge K x + gauge K (s • z) := h_add x (s • z)
    have h_ineq : gauge K (x + s • z) - gauge K x ≤ s * gauge K z := by
      have h_gauge_smul' : gauge K (s • z) = s * gauge K z := by
        simpa [smul_eq_mul] using h_gauge_smul
      linarith
    rw [slope_def_field]
    have h_div : (g s - g 0) / s ≤ (s * gauge K z) / s := by
      have h_ineq' : g s - g 0 ≤ s * gauge K z := by
        simpa [g, hg] using h_ineq
      exact div_le_div_of_nonneg_right h_ineq' (le_of_lt hs_pos)
    have h_simp : (s * gauge K z) / s = gauge K z := by
      field_simp [ne_of_gt hs_pos]
    rw [h_simp] at h_div
    simpa [g, hg] using h_div
  have h_tendsto : Tendsto (slope g 0) (nhdsWithin (0 : ℝ) {0}ᶜ) (𝓝 (fderiv ℝ (gauge K) x z)) :=
    (hasDerivAt_iff_tendsto_slope.mp hg_deriv)
  have h_tendsto' : Tendsto (slope g 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (fderiv ℝ (gauge K) x z)) :=
    h_tendsto.mono_left (nhdsWithin_mono 0 (by
      intro s hs
      simp at hs
      exact Set.mem_compl_singleton_iff.mpr (ne_of_gt hs)))
  exact le_of_tendsto h_tendsto' h_slope_bound

theorem AdversarialBco.Poly.gauge_neg_le {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d))) (α : ℝ) (hα : 0 ≤ α) (hneg : -K ⊆ α • K)
    (x : EuclideanSpace ℝ (Fin d)) : gauge K (-x) ≤ α * gauge K x := by
  have h_abs : Absorbent ℝ K := absorbent_nhds_zero hK0
  have h0_mem_K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := mem_of_mem_nhds hK0
  have hK_nonempty : K.Nonempty := ⟨0, h0_mem_K⟩
  by_cases hα0 : α = 0
  · -- case α = 0
    have hK_sub_singleton : K ⊆ {(0 : EuclideanSpace ℝ (Fin d))} := by
      intro y hy
      have h_neg_y : -y ∈ -K := by simpa using hy
      have hmem : -y ∈ α • K := hneg h_neg_y
      rw [hα0] at hmem
      -- 0 • K = {0} since K is nonempty
      have hzero_smul := Set.zero_smul_set (α := ℝ) (β := EuclideanSpace ℝ (Fin d)) hK_nonempty
      rw [hzero_smul] at hmem
      -- hmem : -y ∈ (0 : Set (EuclideanSpace ℝ (Fin d)))
      -- (0 : Set _) is {0}, so -y = 0, hence y = 0
      simpa using hmem
    have hK_eq : K = {(0 : EuclideanSpace ℝ (Fin d))} := by
      apply Set.Subset.antisymm hK_sub_singleton
      simpa using h0_mem_K
    have h_gauge_zero : gauge K = 0 := by
      rw [hK_eq]
      exact gauge_of_subset_zero (by simp)
    simp [congrFun h_gauge_zero (-x), hα0]
  · -- case α > 0
    have hα_pos : 0 < α := by
      by_contra! hle
      apply hα0
      linarith
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set t := gauge K x + ε / α with ht_def
    have ht_gt : gauge K x < t := by
      dsimp [t]
      have hdiv_pos : 0 < ε / α := div_pos hε hα_pos
      nlinarith
    obtain ⟨r, hr_pos, hr_lt_t, hx_mem⟩ := exists_lt_of_gauge_lt h_abs ht_gt
    have h_neg_mem : -x ∈ r • (-K) := by
      rw [Set.smul_set_neg]
      simpa [Set.mem_neg] using hx_mem
    have h_sub : r • (-K) ⊆ (r * α) • K := by
      have h1 : r • (-K) ⊆ r • (α • K) := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        have hz' : z ∈ α • K := hneg hz
        exact Set.smul_mem_smul_set hz'
      have h2 : r • (α • K) = (r * α) • K := by
        simp [smul_smul]
      exact h1.trans (by simpa [h2])
    have h_neg_mem' : -x ∈ (r * α) • K := h_sub h_neg_mem
    have h_nonneg_ra : 0 ≤ r * α := mul_nonneg hr_pos.le hα
    have h_gauge_le : gauge K (-x) ≤ r * α := gauge_le_of_mem h_nonneg_ra h_neg_mem'
    have h_mul_le : r * α ≤ t * α := mul_le_mul_of_nonneg_right hr_lt_t.le hα
    have h_total : gauge K (-x) ≤ t * α := h_gauge_le.trans h_mul_le
    have h_t_mul : t * α = α * gauge K x + ε := by
      rw [ht_def]
      field_simp [hα_pos.ne.symm]
    rw [h_t_mul] at h_total
    exact h_total

theorem AdversarialBco.Poly.gauge_le_one_iff {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hKc : IsClosed K) (hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x ≤ 1 ↔ x ∈ K := by
  rw [gauge_le_one_iff_mem_closure hK hK0, hKc.closure_eq]

theorem AdversarialBco.Poly.gauge_body_le {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (hKc : IsClosed K) (hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hμ : gauge K μ < 1)
    (y : EuclideanSpace ℝ (Fin d)) :
    gauge (AdversarialBco.Poly.posBody K μ A) y ≤ 1 + AdversarialBco.Poly.posF K μ A y / (1 - gauge K μ) := by
  set p := gauge K μ with hp_def
  set Fy := AdversarialBco.Poly.posF K μ A y with hFy_def
  set t := 1 + Fy / (1 - p) with ht_def
  have hp_lt_one : p < 1 := hμ
  have h_one_minus_p_pos : 0 < 1 - p := by linarith
  have hFy_nonneg : 0 ≤ Fy := by
    rw [hFy_def, AdversarialBco.Poly.posF]
    exact gauge_nonneg (μ + A y)
  have ht_pos : 0 < t := by
    rw [ht_def]
    have hdiv_nonneg : 0 ≤ Fy / (1 - p) := div_nonneg hFy_nonneg (by linarith)
    linarith
  have hmem : y ∈ t • AdversarialBco.Poly.posBody K μ A := by
    have heq : y = t • (t⁻¹ • y) := by
      calc
        y = (1 : ℝ) • y := by simp
        _ = (t * t⁻¹) • y := by field_simp [ne_of_gt ht_pos]
        _ = t • (t⁻¹ • y) := by simp [mul_smul]
    rw [heq]
    refine Set.mem_smul_set.mpr ?_
    refine ⟨t⁻¹ • y, ?_, rfl⟩
    rw [AdversarialBco.Poly.posBody, Set.mem_setOf_eq]
    apply (AdversarialBco.Poly.gauge_le_one_iff K hK hKc hK0 (μ + A (t⁻¹ • y))).mp
    have h_mu_decomp : μ = (1 - t⁻¹) • μ + t⁻¹ • μ := by
      calc
        μ = (1 : ℝ) • μ := by simp
        _ = ((1 - t⁻¹) + t⁻¹) • μ := by ring
        _ = (1 - t⁻¹) • μ + t⁻¹ • μ := by rw [add_smul]
    have h_comb : μ + A (t⁻¹ • y) = (1 - t⁻¹) • μ + t⁻¹ • (μ + A y) := by
      calc
        μ + A (t⁻¹ • y) = μ + t⁻¹ • A y := by simp
        _ = ((1 - t⁻¹) • μ + t⁻¹ • μ) + t⁻¹ • A y := by
          -- h_mu_decomp : μ = (1 - t⁻¹) • μ + t⁻¹ • μ
          -- add t⁻¹ • A y to both sides
          have := congrArg (· + t⁻¹ • A y) h_mu_decomp
          simpa using this
        _ = (1 - t⁻¹) • μ + (t⁻¹ • μ + t⁻¹ • A y) := by abel
        _ = (1 - t⁻¹) • μ + t⁻¹ • (μ + A y) := by simp [smul_add]
    rw [h_comb]
    set a := 1 - t⁻¹ with ha_def
    set b := t⁻¹ with hb_def
    have hab_sum : a + b = 1 := by
      rw [ha_def, hb_def]
      field_simp [ne_of_gt ht_pos]
      ring
    have ha_nonneg : 0 ≤ a := by
      rw [ha_def]
      have ht_ge_one : 1 ≤ t := by
        rw [ht_def]
        have hdiv_nonneg : 0 ≤ Fy / (1 - p) := div_nonneg hFy_nonneg (by linarith)
        linarith
      have ht_inv_le_one : t⁻¹ ≤ 1 := by
        rw [← one_div]
        exact (div_le_one ht_pos).mpr ht_ge_one
      exact sub_nonneg.mpr ht_inv_le_one
    have hb_nonneg : 0 ≤ b := by
      rw [hb_def]
      exact inv_nonneg.mpr (by linarith)
    have hab_pos : 0 < a + b := by
      rw [hab_sum]
      norm_num
    have h_ineq := (convexOn_iff_div.mp (AdversarialBco.Poly.gauge_convexOn K hK hK0)).2
      (Set.mem_univ μ) (Set.mem_univ (μ + A y)) ha_nonneg hb_nonneg hab_pos
    rw [hab_sum] at h_ineq
    simp [ha_def, hb_def] at h_ineq
    have hcalc : a * p + b * Fy ≤ 1 := by
      rw [ha_def, hb_def]
      have hkey : t * (1 - p) = (1 - p) + Fy := by
        rw [ht_def]
        field_simp [ne_of_gt h_one_minus_p_pos]
      have hineq' : Fy - p ≤ t * (1 - p) := by
        rw [hkey]
        linarith
      have htemp : t⁻¹ * (Fy - p) ≤ 1 - p := by
        have hpos_tinv : 0 ≤ t⁻¹ := inv_nonneg.mpr (by linarith)
        calc
          t⁻¹ * (Fy - p) ≤ t⁻¹ * (t * (1 - p)) :=
            mul_le_mul_of_nonneg_left hineq' hpos_tinv
          _ = (t⁻¹ * t) * (1 - p) := by ring
          _ = 1 * (1 - p) := by field_simp [ne_of_gt ht_pos]
          _ = 1 - p := by simp
      calc
        (1 - t⁻¹) * p + t⁻¹ * Fy = p + t⁻¹ * (Fy - p) := by ring
        _ ≤ p + (1 - p) := by linarith
        _ = 1 := by ring
    have h_ineq' : gauge K (a • μ + b • (μ + A y)) ≤ a * p + b * Fy := by
      simpa [ha_def, hb_def, hp_def, hFy_def, AdversarialBco.Poly.posF] using h_ineq
    linarith
  exact gauge_le_of_mem (by linarith) hmem

theorem AdversarialBco.Poly.hinge_mean (t : ℝ) :
    ∫ x, max (-x - t) 0 ∂(gaussianReal 0 1) =
      AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t := by
  have h_symm : ∫ x, (max (-x - t) 0) * AdversarialBco.BodySpec.phi x =
               ∫ x, (max (x - t) 0) * AdversarialBco.BodySpec.phi x := by
    calc
      ∫ x, (max (-x - t) 0) * AdversarialBco.BodySpec.phi x
          = ∫ x, (max (-(-x) - t) 0) * AdversarialBco.BodySpec.phi (-x) := by
            rw [integral_neg_eq_self (fun x => (max (-x - t) 0) * AdversarialBco.BodySpec.phi x) volume]
      _ = ∫ x, (max (x - t) 0) * AdversarialBco.BodySpec.phi x := by
        simp [AdversarialBco.BodySpec.phi]
  have h_zero : ∀ x, x ∉ Set.Ioi t → (max (x - t) 0) * AdversarialBco.BodySpec.phi x = 0 := by
    intro x hx
    have hx' : x ≤ t := by
      simpa [Set.mem_Ioi] using hx
    have h_max : max (x - t) 0 = 0 := by
      rw [max_eq_right (sub_nonpos.mpr hx')]
    simp [h_max]
  have h_set : ∫ x, (max (x - t) 0) * AdversarialBco.BodySpec.phi x =
               ∫ x in Set.Ioi t, (x - t) * AdversarialBco.BodySpec.phi x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_zero]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have : max (x - t) 0 = x - t := by
      rw [max_eq_left (by linarith [Set.mem_Ioi.mp hx])]
    simp [this]
  have h_int_phi : IntegrableOn AdversarialBco.BodySpec.phi (Set.Ioi t) := by
    have h_int : Integrable AdversarialBco.BodySpec.phi := by
      have hb : 0 < (1/2 : ℝ) := by norm_num
      have h_int_exp : Integrable (fun x : ℝ => Real.exp (-((1/2 : ℝ)) * x ^ 2)) :=
        integrable_exp_neg_mul_sq hb
      have h_sqrt_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
        Real.sqrt_pos.mpr (by positivity) |>.ne'
      have h_isUnit : IsUnit (Real.sqrt (2 * Real.pi) : ℝ) := Ne.isUnit h_sqrt_ne_zero
      have h_eq : (fun x : ℝ => Real.exp (-((1/2 : ℝ)) * x ^ 2)) =
          fun x => (Real.sqrt (2 * Real.pi)) * AdversarialBco.BodySpec.phi x := by
        ext x
        dsimp [AdversarialBco.BodySpec.phi]
        field_simp
      have h_int_sqrt_mul_phi : Integrable (fun x => (Real.sqrt (2 * Real.pi)) * AdversarialBco.BodySpec.phi x) := by
        rw [← h_eq]
        exact h_int_exp
      rw [← integrable_const_mul_iff h_isUnit]
      exact h_int_sqrt_mul_phi
    exact h_int.integrableOn
  have h_int_x_phi : IntegrableOn (fun x => x * AdversarialBco.BodySpec.phi x) (Set.Ioi t) := by
    have h_int : Integrable (fun x => x * AdversarialBco.BodySpec.phi x) := by
      have hb : 0 < (1/2 : ℝ) := by norm_num
      have h_int_exp : Integrable (fun x : ℝ => x * Real.exp (-((1/2 : ℝ)) * x ^ 2)) :=
        integrable_mul_exp_neg_mul_sq hb
      have h_sqrt_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
        Real.sqrt_pos.mpr (by positivity) |>.ne'
      have h_isUnit : IsUnit (Real.sqrt (2 * Real.pi) : ℝ) := Ne.isUnit h_sqrt_ne_zero
      have h_eq : (fun x : ℝ => x * Real.exp (-((1/2 : ℝ)) * x ^ 2)) =
          fun x => (Real.sqrt (2 * Real.pi)) * (x * AdversarialBco.BodySpec.phi x) := by
        ext x
        dsimp [AdversarialBco.BodySpec.phi]
        field_simp
      have h_int_sqrt_mul : Integrable (fun x => (Real.sqrt (2 * Real.pi)) * (x * AdversarialBco.BodySpec.phi x)) := by
        rw [← h_eq]
        exact h_int_exp
      rw [← integrable_const_mul_iff h_isUnit]
      exact h_int_sqrt_mul
    exact h_int.integrableOn
  have h_sub : ∫ x in Set.Ioi t, (x - t) * AdversarialBco.BodySpec.phi x =
               (∫ x in Set.Ioi t, x * AdversarialBco.BodySpec.phi x) -
               (∫ x in Set.Ioi t, t * AdversarialBco.BodySpec.phi x) := by
    calc
      ∫ x in Set.Ioi t, (x - t) * AdversarialBco.BodySpec.phi x
          = ∫ x in Set.Ioi t, (x * AdversarialBco.BodySpec.phi x - t * AdversarialBco.BodySpec.phi x) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro x hx
            ring
      _ = (∫ x in Set.Ioi t, x * AdversarialBco.BodySpec.phi x) -
          (∫ x in Set.Ioi t, t * AdversarialBco.BodySpec.phi x) := by
            have h_int_t_phi : IntegrableOn (fun x => t * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
              h_int_phi.const_mul t
            rw [integral_sub h_int_x_phi h_int_t_phi]
  calc
    ∫ x, max (-x - t) 0 ∂(gaussianReal 0 1)
        = ∫ x, (max (-x - t) 0) * AdversarialBco.BodySpec.phi x := by
      rw [AdversarialBco.Body2.integral_gaussianReal_phi]
    _ = ∫ x, (max (x - t) 0) * AdversarialBco.BodySpec.phi x := by rw [h_symm]
    _ = ∫ x in Set.Ioi t, (x - t) * AdversarialBco.BodySpec.phi x := by rw [h_set]
    _ = (∫ x in Set.Ioi t, x * AdversarialBco.BodySpec.phi x) -
        (∫ x in Set.Ioi t, t * AdversarialBco.BodySpec.phi x) := by rw [h_sub]
    _ = AdversarialBco.BodySpec.phi t - t * (∫ x in Set.Ioi t, AdversarialBco.BodySpec.phi x) := by
      rw [AdversarialBco.Body2.integral_Ioi_mul_phi, integral_const_mul]
    _ = AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t := by rfl

theorem AdversarialBco.Poly.bathtub_upper (d : ℕ) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (α t : ℝ) (hα : 0 ≤ α)
    (hh : AEStronglyMeasurable h (stdGaussian (EuclideanSpace ℝ (Fin d))))
    (hb : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -α ≤ h g ∧ h g ≤ 1) :
    ∫ g, ⟪u, g⟫ * h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      AdversarialBco.Poly.bathC α t - t * ∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  have hαpos : 0 < 1 + α := by linarith
  have hmeas_inner : AEMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫) μ :=
    (innerSL ℝ u).measurable.aemeasurable
  have hmap : μ.map (fun g => ⟪u, g⟫) = gaussianReal (0 : ℝ) 1 :=
    AdversarialBco.Body.map_inner_stdGaussian u hu
  have hint_xi : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫) μ := by
    have h_int_id_map : Integrable (fun (x : ℝ) => x) (μ.map (fun g => ⟪u, g⟫)) := by
      rw [hmap]
      exact IsGaussian.integrable_id
    exact h_int_id_map.comp_measurable (innerSL ℝ u).measurable
  have hint_h : Integrable h μ := by
    have h_bound : ∀ᵐ g ∂μ, ‖h g‖ ≤ max α 1 := by
      filter_upwards [hb] with g hg
      rcases hg with ⟨hgl, hgr⟩
      rw [Real.norm_eq_abs]
      by_cases hpos : 0 ≤ h g
      · rw [abs_of_nonneg hpos]
        have h1 : 1 ≤ max α 1 := le_max_right _ _
        linarith
      · rw [abs_of_neg (not_le.mp hpos)]
        have hα' : α ≤ max α 1 := le_max_left _ _
        linarith
    refine Integrable.mono' (integrable_const (max α 1)) hh h_bound
  have hint_w : Integrable (fun g => (1 - h g) / (1 + α)) μ := by
    have : (fun g => (1 - h g) / (1 + α)) = (fun g => (1 + α)⁻¹ * (1 - h g)) := by
      ext g; simp [div_eq_mul_inv, mul_comm]
    rw [this]
    refine Integrable.const_mul ?_ (1 + α)⁻¹
    have h1 : Integrable (fun _ => (1 : ℝ)) μ := integrable_const _
    exact Integrable.sub h1 hint_h
  set ξ := fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫ with hξ
  set w := fun (g : EuclideanSpace ℝ (Fin d)) => (1 - h g) / (1 + α) with hw
  have hw_nonneg_ae : ∀ᵐ g ∂μ, 0 ≤ w g := by
    filter_upwards [hb] with g hg
    rcases hg with ⟨hgl, hgr⟩
    rw [hw]
    have : 0 ≤ 1 - h g := by linarith
    refine div_nonneg this (by linarith)
  have hw_le_one_ae : ∀ᵐ g ∂μ, w g ≤ 1 := by
    filter_upwards [hb] with g hg
    rcases hg with ⟨hgl, hgr⟩
    rw [hw]
    refine (div_le_one ?_).mpr ?_
    · linarith
    · linarith
  have hw_bound : ∀ᵐ g ∂μ, ‖w g‖ ≤ 1 := by
    filter_upwards [hw_nonneg_ae, hw_le_one_ae] with g hwn hwl
    rw [Real.norm_eq_abs, abs_of_nonneg hwn]
    exact hwl
  have h_eq : h = fun g => 1 - (1 + α) * w g := by
    ext g
    dsimp [w]
    field_simp [show 1 + α ≠ 0 from by linarith]
    ring
  have h_int_xi : ∫ g, ξ g ∂μ = 0 := by
    calc
      ∫ g, ξ g ∂μ = ∫ g, ⟪u, g⟫ ∂μ := rfl
      _ = ⟪u, ∫ g, g ∂μ⟫ := by simpa using integral_inner (f := id) IsGaussian.integrable_id u
      _ = ⟪u, 0⟫ := by rw [integral_id_stdGaussian]
      _ = 0 := by simp
  have hint_xi_mul_w : Integrable (fun g => ξ g * w g) μ := by
    have := Integrable.bdd_mul (g := ξ) (f := w) hint_xi hint_w.aestronglyMeasurable hw_bound
    simpa [mul_comm] using this
  have h_int_xi_mul_h : ∫ g, ξ g * h g ∂μ = (1 + α) * ∫ g, (-ξ g) * w g ∂μ := by
    calc
      ∫ g, ξ g * h g ∂μ = ∫ g, ξ g * (1 - (1 + α) * w g) ∂μ := by rw [h_eq]
      _ = ∫ g, (ξ g - (1 + α) * (ξ g * w g)) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with g
        ring
      _ = (∫ g, ξ g ∂μ) - (1 + α) * (∫ g, ξ g * w g ∂μ) := by
        rw [integral_sub hint_xi (Integrable.const_mul hint_xi_mul_w (1 + α))]
        simp [integral_const_mul]
      _ = 0 - (1 + α) * (∫ g, ξ g * w g ∂μ) := by rw [h_int_xi]
      _ = -(1 + α) * (∫ g, ξ g * w g ∂μ) := by ring
      _ = (1 + α) * (-(∫ g, ξ g * w g ∂μ)) := by ring
      _ = (1 + α) * (∫ g, -(ξ g * w g) ∂μ) := by rw [integral_neg]
      _ = (1 + α) * (∫ g, (-ξ g) * w g ∂μ) := by
        congr
        ext g
        ring
  have hint_neg_xi : Integrable (fun g => -ξ g) μ :=
    Integrable.neg hint_xi
  have hint_neg_xi_mul_w : Integrable (fun g => (-ξ g) * w g) μ := by
    have := Integrable.bdd_mul (g := fun g => -ξ g) (f := w) hint_neg_xi hint_w.aestronglyMeasurable hw_bound
    simpa [mul_comm] using this
  have hint_max : Integrable (fun g => max (-ξ g - t) 0) μ :=
    Integrable.pos_part (Integrable.sub hint_neg_xi (integrable_const t))
  have h_pointwise_ae : ∀ᵐ g ∂μ, (-ξ g) * w g ≤ max (-ξ g - t) 0 + t * w g := by
    filter_upwards [hw_nonneg_ae, hw_le_one_ae] with g hw_nonneg hw_le_one
    by_cases hcase : -ξ g - t ≥ 0
    · have hmax : max (-ξ g - t) 0 = -ξ g - t := max_eq_left hcase
      rw [hmax]
      have : (-ξ g) * w g = (-ξ g - t) * w g + t * w g := by ring
      rw [this]
      have h_mul : (-ξ g - t) * w g ≤ -ξ g - t := by
        nlinarith
      nlinarith
    · have hmax : max (-ξ g - t) 0 = 0 := max_eq_right (by linarith)
      rw [hmax]
      have : (-ξ g) * w g = (-ξ g - t) * w g + t * w g := by ring
      rw [this]
      have h_mul : (-ξ g - t) * w g ≤ 0 := by
        nlinarith
      nlinarith
  have h_int_ineq : ∫ g, (-ξ g) * w g ∂μ ≤ ∫ g, max (-ξ g - t) 0 ∂μ + t * ∫ g, w g ∂μ := by
    calc
      ∫ g, (-ξ g) * w g ∂μ ≤ ∫ g, (max (-ξ g - t) 0 + t * w g) ∂μ :=
        integral_mono_ae hint_neg_xi_mul_w (Integrable.add hint_max (Integrable.const_mul hint_w t))
          h_pointwise_ae
      _ = (∫ g, max (-ξ g - t) 0 ∂μ) + (∫ g, t * w g ∂μ) := integral_add hint_max (Integrable.const_mul hint_w t)
      _ = (∫ g, max (-ξ g - t) 0 ∂μ) + t * (∫ g, w g ∂μ) := by rw [integral_const_mul]
  have h_int_max : ∫ g, max (-ξ g - t) 0 ∂μ = AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t := by
    have h_ae : AEStronglyMeasurable (fun (x : ℝ) => max (-x - t) 0) (μ.map ξ) := by
      rw [hmap]
      have h_cont : Continuous (fun (x : ℝ) => max (-x - t) 0) :=
        (Continuous.sub (Continuous.neg continuous_id) continuous_const).max continuous_const
      exact h_cont.stronglyMeasurable.aestronglyMeasurable
    rw [← integral_map hmeas_inner h_ae, hmap]
    exact AdversarialBco.Poly.hinge_mean t
  have h_int_w : ∫ g, w g ∂μ = (1 - ∫ g, h g ∂μ) / (1 + α) := by
    dsimp [w]
    rw [integral_div (1 + α)]
    rw [integral_sub (integrable_const _) hint_h]
    have huniv : ∫ g, (1 : ℝ) ∂μ = (1 : ℝ) := by
      have hprob : IsProbabilityMeasure μ := by
        dsimp [μ]; infer_instance
      have h_univ : μ Set.univ = 1 := measure_univ
      rw [integral_const]
      -- goal: μ.real Set.univ • (1 : ℝ) = (1 : ℝ)
      -- i.e., (μ Set.univ).toReal • 1 = 1
      have : μ.real Set.univ = (μ Set.univ).toReal := rfl
      rw [this, h_univ]
      norm_num
    rw [huniv]
  have h_final : (1 + α) * ∫ g, (-ξ g) * w g ∂μ ≤
      (1 + α) * (AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t) + t * (1 - ∫ g, h g ∂μ) := by
    have h1 : (1 + α) * ∫ g, (-ξ g) * w g ∂μ ≤ (1 + α) * (∫ g, max (-ξ g - t) 0 ∂μ + t * ∫ g, w g ∂μ) := by
      nlinarith
    have h2 : (1 + α) * (∫ g, max (-ξ g - t) 0 ∂μ + t * ∫ g, w g ∂μ) =
        (1 + α) * (AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t) + t * (1 - ∫ g, h g ∂μ) := by
      rw [h_int_max, h_int_w]
      field_simp [show 1 + α ≠ 0 from by linarith]
    nlinarith
  have h_goal : ∫ g, ξ g * h g ∂μ ≤ AdversarialBco.Poly.bathC α t - t * ∫ g, h g ∂μ := by
    rw [h_int_xi_mul_h]
    calc
      (1 + α) * ∫ g, (-ξ g) * w g ∂μ ≤ (1 + α) * (AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t) + t * (1 - ∫ g, h g ∂μ) :=
        h_final
      _ = (1 + α) * AdversarialBco.BodySpec.phi t + t * (1 - (1 + α) * AdversarialBco.BodySpec.Qtail t) - t * ∫ g, h g ∂μ := by
        ring_nf
      _ = AdversarialBco.Poly.bathC α t - t * ∫ g, h g ∂μ := by rfl
  exact h_goal

theorem AdversarialBco.Poly.bathtub (d : ℕ) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (α k t : ℝ) (hα : 0 ≤ α) (hk : 0 ≤ k)
    (hh : AEStronglyMeasurable h (stdGaussian (EuclideanSpace ℝ (Fin d))))
    (hb : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -(α * k) ≤ h g ∧ h g ≤ k) :
    |∫ g, ⟪u, g⟫ * h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤
      k * AdversarialBco.Poly.bathC α t + |t| * |∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  by_cases hk0 : k = 0
  · -- case k = 0
    subst hk0
    have hzero : ∀ᵐ g ∂μ, h g = 0 := by
      filter_upwards [hb] with g hg
      rcases hg with ⟨hgl, hgr⟩
      linarith
    have hint_phi : ∫ g, ⟪u, g⟫ * h g ∂μ = 0 := by
      calc
        ∫ g, ⟪u, g⟫ * h g ∂μ = ∫ g, ⟪u, g⟫ * (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hzero] with g hg
          simp [hg]
        _ = 0 := by simp
    have hint_h : ∫ g, h g ∂μ = 0 := by
      calc
        ∫ g, h g ∂μ = ∫ g, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hzero] with g hg
          simp [hg]
        _ = 0 := by simp
    rw [hint_phi, hint_h]
    simp
  · -- case k > 0
    have hk_pos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    let h' : EuclideanSpace ℝ (Fin d) → ℝ := λ g => h g / k
    have hh' : AEStronglyMeasurable h' μ := by
      -- h' = h * (1/k), and multiplication by a constant preserves AEStronglyMeasurable
      have : h' = (λ g => h g * (k⁻¹ : ℝ)) := by
        ext g; simp [h', div_eq_mul_inv]
      rw [this]
      exact hh.mul_const (k⁻¹ : ℝ)
    have hb' : ∀ᵐ g ∂μ, -α ≤ h' g ∧ h' g ≤ 1 := by
      filter_upwards [hb] with g hg
      rcases hg with ⟨hgl, hgr⟩
      have hgl' : -α * k ≤ h g := by
        calc
          -α * k = -(α * k) := by ring
          _ ≤ h g := hgl
      constructor
      · -- -α ≤ h g / k
        exact (le_div_iff₀ hk_pos).mpr hgl'
      · -- h g / k ≤ 1
        exact (div_le_one hk_pos).mpr hgr
    have hu_neg : ‖-u‖ = 1 := by
      simp [hu]
    have h_upper_u := AdversarialBco.Poly.bathtub_upper d u hu h' α t hα hh' hb'
    have h_upper_neg_u := AdversarialBco.Poly.bathtub_upper d (-u) hu_neg h' α t hα hh' hb'
    -- h_upper_u : ∫ ⟪u, g⟫ * h' g ≤ bathC α t - t * ∫ h' g
    -- h_upper_neg_u : ∫ ⟪-u, g⟫ * h' g ≤ bathC α t - t * ∫ h' g
    -- Rewrite ⟪-u, g⟫ = -⟪u, g⟫
    have h_upper_neg_u' : -∫ g, ⟪u, g⟫ * h' g ∂μ ≤ AdversarialBco.Poly.bathC α t - t * ∫ g, h' g ∂μ := by
      simpa [inner_neg_left, integral_neg, neg_mul] using h_upper_neg_u
    have h_abs : |∫ g, ⟪u, g⟫ * h' g ∂μ| ≤ AdversarialBco.Poly.bathC α t - t * ∫ g, h' g ∂μ := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have h_int_phi_div : ∫ g, ⟪u, g⟫ * h' g ∂μ = (∫ g, ⟪u, g⟫ * h g ∂μ) / k := by
      calc
        ∫ g, ⟪u, g⟫ * h' g ∂μ = ∫ g, ⟪u, g⟫ * (h g / k) ∂μ := rfl
        _ = ∫ g, (⟪u, g⟫ * h g) / k ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with g
          ring
        _ = (∫ g, ⟪u, g⟫ * h g ∂μ) / k := by rw [integral_div]
    have h_int_h_div : ∫ g, h' g ∂μ = (∫ g, h g ∂μ) / k := by
      calc
        ∫ g, h' g ∂μ = ∫ g, (h g / k) ∂μ := rfl
        _ = (∫ g, h g ∂μ) / k := by rw [integral_div]
    rw [h_int_phi_div, h_int_h_div] at h_abs
    have h_abs_div : |(∫ g, ⟪u, g⟫ * h g ∂μ) / k| = |∫ g, ⟪u, g⟫ * h g ∂μ| / k := by
      rw [abs_div, abs_of_pos hk_pos]
    rw [h_abs_div] at h_abs
    have h_mul : |∫ g, ⟪u, g⟫ * h g ∂μ| ≤ k * (AdversarialBco.Poly.bathC α t - t * ((∫ g, h g ∂μ) / k)) := by
      have := (div_le_iff₀ hk_pos).mp h_abs
      simpa [mul_comm] using this
    have h_simp : k * (AdversarialBco.Poly.bathC α t - t * ((∫ g, h g ∂μ) / k)) = k * AdversarialBco.Poly.bathC α t - t * ∫ g, h g ∂μ := by
      field_simp [hk_pos.ne.symm]
    rw [h_simp] at h_mul
    have h_aux : -t * (∫ g, h g ∂μ) ≤ |t| * |∫ g, h g ∂μ| := by
      calc
        -t * (∫ g, h g ∂μ) = -(t * (∫ g, h g ∂μ)) := by ring
        _ ≤ |t * (∫ g, h g ∂μ)| := neg_le_abs _
        _ = |t| * |∫ g, h g ∂μ| := abs_mul _ _
    linarith

theorem AdversarialBco.Poly.bathC_nonneg (α t : ℝ) (hα : 0 ≤ α) : 0 ≤ AdversarialBco.Poly.bathC α t := by
  have h_bathC_eq : AdversarialBco.Poly.bathC α t = (1 + α) * (AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t) + t := by
    dsimp [AdversarialBco.Poly.bathC]
    ring
  rw [h_bathC_eq]
  have h_hinge := AdversarialBco.Poly.hinge_mean t
  have h_int_id : MeasureTheory.Integrable (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.IsGaussian.integrable_fun_id
  have h_int_neg_id : MeasureTheory.Integrable (fun x : ℝ => -x) (ProbabilityTheory.gaussianReal 0 1) :=
    h_int_id.neg
  have h_int_const_t : MeasureTheory.Integrable (fun _ : ℝ => t) (ProbabilityTheory.gaussianReal 0 1) :=
    MeasureTheory.integrable_const _
  have h_int_sub : MeasureTheory.Integrable (fun x : ℝ => -x - t) (ProbabilityTheory.gaussianReal 0 1) := by
    have : (fun x : ℝ => -x - t) = (fun x : ℝ => (-x) + (-t)) := by
      ext x; ring
    rw [this]
    exact h_int_neg_id.add (h_int_const_t.neg)
  have h_int_const_zero : MeasureTheory.Integrable (fun _ : ℝ => (0 : ℝ)) (ProbabilityTheory.gaussianReal 0 1) :=
    MeasureTheory.integrable_const _
  have h_int_max : MeasureTheory.Integrable (fun x : ℝ => max (-x - t) 0) (ProbabilityTheory.gaussianReal 0 1) := by
    have : (fun x : ℝ => max (-x - t) 0) = (fun x : ℝ => (-x - t) ⊔ (0 : ℝ)) := by
      ext x; simp
    rw [this]
    exact MeasureTheory.Integrable.sup h_int_sub h_int_const_zero
  have h_nonneg_int : 0 ≤ ∫ x, max (-x - t) 0 ∂(ProbabilityTheory.gaussianReal 0 1) := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact le_max_right _ _
  have h_pointwise : (fun x : ℝ => -x - t) ≤ (fun x : ℝ => max (-x - t) 0) := by
    intro x
    exact le_max_left _ _
  have h_int_sub_val : ∫ x, (-x - t) ∂(ProbabilityTheory.gaussianReal 0 1) = -t := by
    calc
      ∫ x, (-x - t) ∂(ProbabilityTheory.gaussianReal 0 1) = (∫ x, -x ∂(ProbabilityTheory.gaussianReal 0 1)) - (∫ x, t ∂(ProbabilityTheory.gaussianReal 0 1)) := by
        rw [MeasureTheory.integral_sub h_int_neg_id h_int_const_t]
      _ = (-∫ x, x ∂(ProbabilityTheory.gaussianReal 0 1)) - (∫ x, t ∂(ProbabilityTheory.gaussianReal 0 1)) := by
        rw [MeasureTheory.integral_neg]
      _ = (-0) - (∫ x, t ∂(ProbabilityTheory.gaussianReal 0 1)) := by
        rw [ProbabilityTheory.integral_id_gaussianReal]
      _ = (-0) - t := by
        rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
        simp
      _ = -t := by ring
  have h_ge_neg_t : -t ≤ ∫ x, max (-x - t) 0 ∂(ProbabilityTheory.gaussianReal 0 1) := by
    have h_mono := MeasureTheory.integral_mono h_int_sub h_int_max h_pointwise
    rw [h_int_sub_val] at h_mono
    exact h_mono
  have hI_nonneg : 0 ≤ AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t := by
    rw [← h_hinge]
    exact h_nonneg_int
  have hI_ge_neg_t : -t ≤ AdversarialBco.BodySpec.phi t - t * AdversarialBco.BodySpec.Qtail t := by
    rw [← h_hinge]
    exact h_ge_neg_t
  by_cases ht : 0 ≤ t
  · -- t ≥ 0
    nlinarith
  · -- t < 0
    nlinarith

theorem AdversarialBco.Poly.qtail_strictAnti : StrictAnti AdversarialBco.BodySpec.Qtail := by
  refine strictAnti_of_deriv_neg ?_
  intro x
  have hderiv := (AdversarialBco.Body2.hasDerivAt_Qtail x).deriv
  have hpos : 0 < AdversarialBco.BodySpec.phi x := by
    dsimp [AdversarialBco.BodySpec.phi]
    have hnum : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
    have hden : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)
    exact div_pos hnum hden
  have hneg : deriv AdversarialBco.BodySpec.Qtail x < 0 := by
    rw [hderiv]
    linarith
  exact hneg

theorem AdversarialBco.Poly.halfspace_measure {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (s : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | ⟪u, g⟫ < s} = 1 - AdversarialBco.BodySpec.Qtail s := by
  have h_map : (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫) = gaussianReal 0 1 :=
    AdversarialBco.Body.map_inner_stdGaussian u hu
  have h_meas_inner : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => ⟪u, g⟫) :=
    (continuous_const.inner continuous_id).measurable
  have h_meas_Iio : MeasurableSet (Set.Iio s) := measurableSet_Iio
  have h_meas_Ici : MeasurableSet (Set.Ici s) := measurableSet_Ici
  have h_eq_inner : (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | ⟪u, g⟫ < s} =
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) (Set.Iio s) := by
    calc
      (stdGaussian (EuclideanSpace ℝ (Fin d))) {g | ⟪u, g⟫ < s}
          = (stdGaussian (EuclideanSpace ℝ (Fin d))) ((fun g => ⟪u, g⟫) ⁻¹' (Set.Iio s)) := by
        congr
      _ = ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) (Set.Iio s) := by
        rw [Measure.map_apply h_meas_inner h_meas_Iio]
  have h_int_Ici_eq_Ioi : (∫ x in Set.Ici s, AdversarialBco.BodySpec.phi x) =
      (∫ x in Set.Ioi s, AdversarialBco.BodySpec.phi x) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  calc
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | ⟪u, g⟫ < s}
        = ((stdGaussian (EuclideanSpace ℝ (Fin d))) {g | ⟪u, g⟫ < s}).toReal := by
      rw [Measure.real_def]
    _ = (((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)) (Set.Iio s)).toReal := by
      rw [h_eq_inner]
    _ = ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun g => ⟪u, g⟫)).real (Set.Iio s) := by
      rw [Measure.real_def]
    _ = (gaussianReal (0 : ℝ) 1).real (Set.Iio s) := by rw [h_map]
    _ = (gaussianReal (0 : ℝ) 1).real ((Set.Ici s)ᶜ) := by rw [Set.compl_Ici]
    _ = (gaussianReal (0 : ℝ) 1).real Set.univ - (gaussianReal (0 : ℝ) 1).real (Set.Ici s) := by
      rw [measureReal_compl h_meas_Ici]
    _ = 1 - (gaussianReal (0 : ℝ) 1).real (Set.Ici s) := by
      rw [probReal_univ]
    _ = 1 - (∫ x, (Set.Ici s).indicator 1 x ∂(gaussianReal (0 : ℝ) 1)) := by
      rw [MeasureTheory.integral_indicator_one h_meas_Ici]
    _ = 1 - (∫ x, (Set.Ici s).indicator 1 x * AdversarialBco.BodySpec.phi x) := by
      rw [AdversarialBco.Body2.integral_gaussianReal_phi]
    _ = 1 - (∫ x, (Set.Ici s).indicator (AdversarialBco.BodySpec.phi ·) x) := by
      refine congrArg (fun t => 1 - t) ?_
      refine integral_congr_ae ?_
      filter_upwards [] with x
      simp [Set.indicator]
    _ = 1 - (∫ x in Set.Ici s, AdversarialBco.BodySpec.phi x) := by
      rw [MeasureTheory.integral_indicator h_meas_Ici]
    _ = 1 - (∫ x in Set.Ioi s, AdversarialBco.BodySpec.phi x) := by rw [h_int_Ici_eq_Ioi]
    _ = 1 - AdversarialBco.BodySpec.Qtail s := rfl

theorem AdversarialBco.Poly.gc_quantile (α : ℝ) (hα : 1 ≤ α) :
    ∃ t : ℝ, 0 ≤ t ∧ AdversarialBco.BodySpec.Qtail t = 1 / (1 + α) := by
  set T := 1 + α with hTdef
  have hTpos : 0 < T := by
    linarith
  have h_cont : Continuous AdversarialBco.BodySpec.Qtail := by
    have h_diff : ∀ x, HasDerivAt AdversarialBco.BodySpec.Qtail (-AdversarialBco.BodySpec.phi x) x :=
      AdversarialBco.Body2.hasDerivAt_Qtail
    have h_cont_at : ∀ x, ContinuousAt AdversarialBco.BodySpec.Qtail x := by
      intro x
      exact (h_diff x).continuousAt
    exact continuous_iff_continuousAt.mpr h_cont_at
  have h_cont_on : ContinuousOn AdversarialBco.BodySpec.Qtail (Set.Icc (0 : ℝ) T) :=
    h_cont.continuousOn
  have hQ0 : AdversarialBco.BodySpec.Qtail 0 = 1/2 := by
    -- Qtail 0 = ∫_{Ioi 0} phi = 1/2
    rw [AdversarialBco.BodySpec.Qtail]
    exact AdversarialBco.Body2.integral_phi_Ioi_zero
  have hQT_le : AdversarialBco.BodySpec.Qtail T ≤ 1 / (1 + α) := by
    have hTpos' : 0 < T := hTpos
    have h_le : AdversarialBco.BodySpec.Qtail T ≤ AdversarialBco.BodySpec.phi T / T :=
      AdversarialBco.Body2.Qtail_le_phi_div T hTpos'
    -- need phi T ≤ 1
    have h_phi_le_one : AdversarialBco.BodySpec.phi T ≤ 1 := by
      rw [AdversarialBco.BodySpec.phi]
      have h_exp_le_one : Real.exp (-(T ^ 2) / 2) ≤ 1 := by
        have h_nonpos : -(T ^ 2) / 2 ≤ 0 := by nlinarith
        exact (Real.exp_le_one_iff.mpr h_nonpos)
      have h_denom_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by
        have hpi : 0 < Real.pi := Real.pi_pos
        nlinarith)
      have h_denom_ge_one : 1 ≤ Real.sqrt (2 * Real.pi) := by
        -- sqrt(2π) > sqrt(1) = 1 since 2π > 1
        have h_2pi_gt_one : 1 < 2 * Real.pi := by
          have hpi : 3 < Real.pi := Real.pi_gt_three
          nlinarith
        exact calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by linarith)
      -- phi T = exp(-T^2/2) / sqrt(2π) ≤ 1 / sqrt(2π) ≤ 1/1 = 1
      have h_div_sqrt : Real.exp (-(T ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤ 1 / Real.sqrt (2 * Real.pi) :=
        div_le_div_of_nonneg_right h_exp_le_one (by linarith [h_denom_pos])
      have h_one_div_sqrt : 1 / Real.sqrt (2 * Real.pi) ≤ 1 / 1 := by
        refine (one_div_le_one_div h_denom_pos (by norm_num : (0 : ℝ) < 1)).mpr h_denom_ge_one
      calc
        Real.exp (-(T ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤ 1 / Real.sqrt (2 * Real.pi) := h_div_sqrt
        _ ≤ 1 / 1 := h_one_div_sqrt
        _ = 1 := by norm_num
    have h_div : AdversarialBco.BodySpec.phi T / T ≤ 1 / T := by
      refine (div_le_div_iff_of_pos_right hTpos').mpr h_phi_le_one
    calc
      AdversarialBco.BodySpec.Qtail T ≤ AdversarialBco.BodySpec.phi T / T := h_le
      _ ≤ 1 / T := h_div
      _ = 1 / (1 + α) := by rfl
  have h_target_in_range : 1 / (1 + α) ∈ Set.Icc (AdversarialBco.BodySpec.Qtail T) (AdversarialBco.BodySpec.Qtail 0) := by
    rw [hQ0]
    have h_nonneg : 0 ≤ 1 / (1 + α) := by
      have h_denom : 0 < 1 + α := by linarith
      exact div_nonneg (by norm_num) (by linarith)
    have h_le_half : 1 / (1 + α) ≤ 1/2 := by
      -- Since α ≥ 1, 1+α ≥ 2, so 1/(1+α) ≤ 1/2
      have h_denom : 2 ≤ 1 + α := by linarith
      exact (one_div_le_one_div (by linarith) (by linarith)).mpr h_denom
    exact Set.mem_Icc.mpr ⟨hQT_le, h_le_half⟩
  have h_ivt : Set.Icc (AdversarialBco.BodySpec.Qtail T) (AdversarialBco.BodySpec.Qtail 0) ⊆
      AdversarialBco.BodySpec.Qtail '' Set.Icc (0 : ℝ) T :=
    intermediate_value_Icc' (by linarith [hTpos]) h_cont_on
  rcases h_ivt h_target_in_range with ⟨t, ht_mem, ht_eq⟩
  refine ⟨t, ht_mem.1, ht_eq⟩

namespace AdversarialBco.Poly

/- Helper lemma: `gaussianPDFReal 0 1` equals `BodySpec.phi`. -/
theorem gaussianPDFReal_eq_phi : gaussianPDFReal (0 : ℝ) (1 : NNReal) = AdversarialBco.BodySpec.phi := by
  ext x
  rw [gaussianPDFReal_def (0 : ℝ) (1 : NNReal)]
  dsimp [AdversarialBco.BodySpec.phi]
  ring_nf

/- Helper lemma: integrability of `exp(s*x) * phi x` on ℝ w.r.t. volume,
   derived from `integrable_exp_mul_gaussianReal` and the fact that
   `gaussianReal 0 1` has density `phi`. -/
theorem integrable_exp_mul_phi (s : ℝ) : Integrable (fun x => Real.exp (s * x) * AdversarialBco.BodySpec.phi x) := by
  have hv : (1 : NNReal) ≠ 0 := by norm_num
  have h_eq : gaussianReal (0 : ℝ) (1 : NNReal) = volume.withDensity (gaussianPDF (0 : ℝ) (1 : NNReal)) :=
    gaussianReal_of_var_ne_zero (0 : ℝ) hv
  have h_int : Integrable (fun x => Real.exp (s * x)) (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    integrable_exp_mul_gaussianReal s
  rw [h_eq] at h_int
  have h_meas : Measurable (gaussianPDF (0 : ℝ) (1 : NNReal)) := measurable_gaussianPDF (0 : ℝ) (1 : NNReal)
  have h_fin : ∀ᵐ x ∂volume, gaussianPDF (0 : ℝ) (1 : NNReal) x < ⊤ := by
    filter_upwards [] with x
    have : gaussianPDF (0 : ℝ) (1 : NNReal) x = ENNReal.ofReal (gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := rfl
    rw [this]
    exact ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff h_meas h_fin] at h_int
  have h_toReal (x : ℝ) : (gaussianPDF (0 : ℝ) (1 : NNReal) x).toReal = gaussianPDFReal (0 : ℝ) (1 : NNReal) x := by
    rw [show gaussianPDF (0 : ℝ) (1 : NNReal) x = ENNReal.ofReal (gaussianPDFReal (0 : ℝ) (1 : NNReal) x) from rfl]
    have h_nonneg : 0 ≤ gaussianPDFReal (0 : ℝ) (1 : NNReal) x := by
      rw [gaussianPDFReal_def (0 : ℝ) (1 : NNReal)]
      positivity
    simp [h_nonneg]
  have h_int' : Integrable (fun x => Real.exp (s * x) * gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := by
    simpa [h_toReal] using h_int
  rw [gaussianPDFReal_eq_phi] at h_int'
  simpa [mul_comm] using h_int'

/- Integrability of `phi` and `x * phi` on ℝ (for splitting integrals). -/
theorem integrable_phi : Integrable (AdversarialBco.BodySpec.phi) := by
  have h_int_exp : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
    have h := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num : 0 < (1/2 : ℝ))
    simpa [div_eq_inv_mul] using h
  have h_phi_eq : AdversarialBco.BodySpec.phi = fun x => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by
    ext x; simp [AdversarialBco.BodySpec.phi]
  rw [h_phi_eq]
  exact h_int_exp.div_const _

theorem integrable_x_mul_phi : Integrable (fun x => x * AdversarialBco.BodySpec.phi x) := by
  have h_int_x_exp : Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num : 0 < (1/2 : ℝ)) (s := 1) (by norm_num : (-1 : ℝ) < 1)
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h_phi_eq : AdversarialBco.BodySpec.phi = fun x => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by
    ext x; simp [AdversarialBco.BodySpec.phi]
  rw [h_phi_eq]
  have : (fun x : ℝ => x * (Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))) =
      (fun x => (x * Real.exp (-(x ^ 2) / 2)) / Real.sqrt (2 * Real.pi)) := by
    ext x; ring
  rw [this]
  exact h_int_x_exp.div_const _

end AdversarialBco.Poly

theorem AdversarialBco.Poly.gc_upper (α t : ℝ) (hα : 1 ≤ α) (ht : AdversarialBco.BodySpec.Qtail t = 1 / (1 + α)) :
    (1 + α) * AdversarialBco.BodySpec.phi t ≤ Real.sqrt (2 * Real.log (1 + α)) := by
  -- Notation: let c = (1+α)*phi t, P = Qtail t = 1/(1+α), s = sqrt(2*log(1+α))
  set c := (1 + α) * AdversarialBco.BodySpec.phi t with hc
  set P := AdversarialBco.BodySpec.Qtail t with hP
  have hP_eq : P = 1 / (1 + α) := ht
  have h_one_plus_α_pos : 0 < 1 + α := by linarith
  have hc_mul_P : c * P = AdversarialBco.BodySpec.phi t := by
    rw [hc, hP_eq]
    field_simp [h_one_plus_α_pos.ne']
  set s := Real.sqrt (2 * Real.log (1 + α)) with hs
  have h_log_pos : 0 < Real.log (1 + α) := Real.log_pos (by linarith : 1 < 1 + α)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hs_sq : s ^ 2 = 2 * Real.log (1 + α) := Real.sq_sqrt (by nlinarith)
  -- Key inequality from convexity of exp: exp(s*x) ≥ exp(s*c) * (1 + s*(x-c))
  have h_exp_ineq (x : ℝ) : Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x ≤ Real.exp (s * x) * AdversarialBco.BodySpec.phi x := by
    have h := Real.add_one_le_exp (s * (x - c))
    have h' : 1 + s * (x - c) ≤ Real.exp (s * (x - c)) := by linarith
    have hpos : 0 < Real.exp (s * c) := Real.exp_pos _
    have hpos_phi : 0 ≤ AdversarialBco.BodySpec.phi x := by
      rw [AdversarialBco.BodySpec.phi]
      positivity
    have h_mul : Real.exp (s * c) * (1 + s * (x - c)) ≤ Real.exp (s * c) * Real.exp (s * (x - c)) :=
      mul_le_mul_of_nonneg_left h' (by positivity)
    have h_expand' : Real.exp (s * c) * Real.exp (s * (x - c)) = Real.exp (s * x) := by
      rw [← Real.exp_add]
      ring_nf
    calc
      Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x ≤
          (Real.exp (s * c) * Real.exp (s * (x - c))) * AdversarialBco.BodySpec.phi x := by gcongr
      _ = Real.exp (s * x) * AdversarialBco.BodySpec.phi x := by rw [h_expand']
  -- Integrability on Ioi t for the integrands
  have h_int_phi_on : IntegrableOn (AdversarialBco.BodySpec.phi) (Set.Ioi t) :=
    AdversarialBco.Poly.integrable_phi.integrableOn
  have h_int_x_phi_on : IntegrableOn (fun x => x * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
    AdversarialBco.Poly.integrable_x_mul_phi.integrableOn
  -- Integral inequality via setIntegral_mono
  have h_int_ineq : (∫ x in Set.Ioi t, Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) ≤
      (∫ x in Set.Ioi t, Real.exp (s * x) * AdversarialBco.BodySpec.phi x) := by
    have h_int_L : IntegrableOn (fun x => Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) (Set.Ioi t) := by
      -- Expand: exp(s*c)*(1+s*(x-c))*phi = exp(s*c)*phi + exp(s*c)*s*x*phi - exp(s*c)*s*c*phi
      -- Each term is integrable
      have h1 : IntegrableOn (fun x => Real.exp (s * c) * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
        h_int_phi_on.const_mul (Real.exp (s * c))
      have h2 : IntegrableOn (fun x => Real.exp (s * c) * s * (x * AdversarialBco.BodySpec.phi x)) (Set.Ioi t) :=
        h_int_x_phi_on.const_mul (Real.exp (s * c) * s)
      have h3 : IntegrableOn (fun x => Real.exp (s * c) * s * c * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
        h_int_phi_on.const_mul (Real.exp (s * c) * s * c)
      have h_eq : (fun x => Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) =
          (fun x => Real.exp (s * c) * AdversarialBco.BodySpec.phi x + Real.exp (s * c) * s * (x * AdversarialBco.BodySpec.phi x) - Real.exp (s * c) * s * c * AdversarialBco.BodySpec.phi x) := by
        ext x; ring
      rw [h_eq]
      exact (h1.add h2).sub h3
    have h_int_R : IntegrableOn (fun x => Real.exp (s * x) * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
      AdversarialBco.Poly.integrable_exp_mul_phi s |>.integrableOn
    refine setIntegral_mono h_int_L h_int_R h_exp_ineq
  -- Simplify the LHS integral to exp(s*c) * P
  have h_LHS_simp : (∫ x in Set.Ioi t, Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) =
      Real.exp (s * c) * P := by
    -- Use the identity: (1 + s*(x-c)) * phi = phi + s*(x*phi - c*phi)
    have h_expand (x : ℝ) : (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x =
        AdversarialBco.BodySpec.phi x + s * (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x) := by
      ring
    -- Rewrite the integrand
    have h_integrand_eq : (fun x => Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) =
        (fun x => Real.exp (s * c) * (AdversarialBco.BodySpec.phi x + s * (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x))) := by
      ext x
      calc
        Real.exp (s * c) * (1 + s * (x - c)) * AdversarialBco.BodySpec.phi x =
            Real.exp (s * c) * ((1 + s * (x - c)) * AdversarialBco.BodySpec.phi x) := by ring
        _ = Real.exp (s * c) * (AdversarialBco.BodySpec.phi x + s * (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x)) := by rw [h_expand]
    rw [h_integrand_eq]
    rw [integral_const_mul (Real.exp (s * c)) (f := fun x => (AdversarialBco.BodySpec.phi x + s * (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x)))]
    have h_int_s_diff : IntegrableOn (fun x => s * (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x)) (Set.Ioi t) := by
      have h_int_diff : IntegrableOn (fun x => x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x) (Set.Ioi t) :=
        h_int_x_phi_on.sub (h_int_phi_on.const_mul c)
      exact Integrable.const_mul h_int_diff s
    rw [integral_add h_int_phi_on h_int_s_diff]
    rw [integral_const_mul s (f := fun x => (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x))]
    have h_sub : (∫ x in Set.Ioi t, (x * AdversarialBco.BodySpec.phi x - c * AdversarialBco.BodySpec.phi x)) =
        (∫ x in Set.Ioi t, x * AdversarialBco.BodySpec.phi x) - c * (∫ x in Set.Ioi t, AdversarialBco.BodySpec.phi x) := by
      rw [integral_sub h_int_x_phi_on (h_int_phi_on.const_mul c)]
      rw [integral_const_mul c (f := AdversarialBco.BodySpec.phi)]
    rw [h_sub]
    rw [AdversarialBco.Body2.integral_Ioi_mul_phi t]
    -- Now goal: exp(s*c) * ((∫ phi) + s*(phi t - c*(∫ phi))) = exp(s*c) * P
    -- We have: hc_mul_P : c * P = phi t
    -- And P is defined as BodySpec.Qtail t = ∫ phi
    -- So phi t = c * P = c * (∫ phi)
    -- Thus the goal becomes: exp(s*c) * ((∫ phi) + s*(c*(∫ phi) - c*(∫ phi))) = exp(s*c) * P
    -- which simplifies by ring
    rw [← hc_mul_P]
    -- Now goal: exp(s*c) * ((∫ phi) + s*(c*P - c*(∫ phi))) = exp(s*c) * P
    -- Since P is defined as BodySpec.Qtail t = ∫ phi, we can unfold P
    dsimp [P, AdversarialBco.BodySpec.Qtail]
    -- Now goal: exp(s*c) * ((∫ phi) + s*(c*(∫ phi) - c*(∫ phi))) = exp(s*c) * (∫ phi)
    -- Simplify: c*(∫ phi) - c*(∫ phi) = 0
    have hzero : c * (∫ x in Set.Ioi t, AdversarialBco.BodySpec.phi x) - c * (∫ x in Set.Ioi t, AdversarialBco.BodySpec.phi x) = 0 := by ring
    rw [hzero]
    simp
  -- Now combine: exp(s*c)*P ≤ ∫_{Ioi t} exp(s*x)*phi x ≤ ∫_ℝ exp(s*x)*phi x = exp(s^2/2)
  have h_bound : Real.exp (s * c) * P ≤ Real.exp (s ^ 2 / 2) := by
    have h1 : Real.exp (s * c) * P ≤ (∫ x in Set.Ioi t, Real.exp (s * x) * AdversarialBco.BodySpec.phi x) := by
      linarith
    have h2 : (∫ x in Set.Ioi t, Real.exp (s * x) * AdversarialBco.BodySpec.phi x) ≤
        (∫ x, Real.exp (s * x) * AdversarialBco.BodySpec.phi x) := by
      refine setIntegral_le_integral (AdversarialBco.Poly.integrable_exp_mul_phi s) ?_
      have h_nonneg : 0 ≤ᵐ[volume] (fun x => Real.exp (s * x) * AdversarialBco.BodySpec.phi x) := by
        refine ae_of_all volume (fun x => ?_)
        have h_exp_nonneg : 0 ≤ Real.exp (s * x) := Real.exp_pos _ |>.le
        have h_phi_nonneg : 0 ≤ AdversarialBco.BodySpec.phi x := by
          rw [AdversarialBco.BodySpec.phi]
          positivity
        apply mul_nonneg h_exp_nonneg h_phi_nonneg
      exact h_nonneg
    have h3 : (∫ x, Real.exp (s * x) * AdversarialBco.BodySpec.phi x) = Real.exp (s ^ 2 / 2) := by
      -- integral_gaussianReal_phi: ∫ f ∂(gaussianReal 0 1) = ∫ f * phi
      -- So ∫ exp(s*x) * phi = ∫ exp(s*x) ∂(gaussianReal 0 1)
      rw [← AdversarialBco.Body2.integral_gaussianReal_phi (fun x => Real.exp (s * x))]
      -- Now: ∫ exp(s*x) ∂(gaussianReal 0 1) = mgf id (gaussianReal 0 1) s = exp(s^2/2)
      have h_mgf_val : mgf (fun x => x) (gaussianReal (0 : ℝ) (1 : NNReal)) s = Real.exp (s ^ 2 / 2) := by
        rw [mgf_fun_id_gaussianReal]
        simp
      simpa [mgf] using h_mgf_val
    linarith
  -- Now from h_bound: exp(s*c) * P ≤ exp(s^2/2)
  -- Since P = 1/(1+α), we have exp(s*c) / (1+α) ≤ exp(s^2/2)
  have h_exp_ineq2 : Real.exp (s * c) ≤ Real.exp (s ^ 2 / 2) * (1 + α) := by
    rw [hP_eq] at h_bound
    have h := mul_le_mul_of_nonneg_right h_bound (by positivity : 0 ≤ 1 + α)
    field_simp [h_one_plus_α_pos.ne'] at h
    simpa [mul_comm] using h
  -- Take logs: s*c ≤ s^2/2 + log(1+α)
  have h_log_ineq : s * c ≤ s ^ 2 / 2 + Real.log (1 + α) := by
    have h_exp_pos : 0 < Real.exp (s * c) := Real.exp_pos _
    have h_rhs_pos : 0 < Real.exp (s ^ 2 / 2) * (1 + α) := by positivity
    have h_log := Real.log_le_log h_exp_pos h_exp_ineq2
    rw [Real.log_exp (s * c), Real.log_mul (by positivity : Real.exp (s ^ 2 / 2) ≠ 0) (by positivity : (1 + α) ≠ 0),
      Real.log_exp (s ^ 2 / 2)] at h_log
    exact h_log
  -- Since s^2 = 2*log(1+α), we have s^2/2 + log(1+α) = s^2
  have h_final : s * c ≤ s ^ 2 := by
    rw [hs_sq] at h_log_ineq
    nlinarith
  -- Therefore c ≤ s, which is the goal
  rw [hc, hs]
  nlinarith

theorem AdversarialBco.Poly.gc_lower (α t : ℝ) (hα : 1 ≤ α) (ht0 : 0 ≤ t)
    (ht : AdversarialBco.BodySpec.Qtail t = 1 / (1 + α)) : t ≤ (1 + α) * AdversarialBco.BodySpec.phi t := by
  by_cases h : t = 0
  · rw [h]
    have hpos : 0 < (1 + α) * AdversarialBco.BodySpec.phi 0 := by
      have h1α : 0 < 1 + α := by linarith
      have hphi0 : 0 < AdversarialBco.BodySpec.phi 0 := by
        unfold AdversarialBco.BodySpec.phi
        have hnum : Real.exp (-(0 : ℝ) ^ 2 / 2) = 1 := by norm_num
        have hden : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
        positivity
      positivity
    exact hpos.le
  · have hpos_t : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    have hpos_1πα : 0 < 1 + α := by linarith
    have hineq := AdversarialBco.Body2.Qtail_le_phi_div t hpos_t
    rw [ht] at hineq
    calc
      t = (1 / (1 + α)) * ((1 + α) * t) := by
        field_simp [hpos_1πα.ne.symm]
      _ ≤ (AdversarialBco.BodySpec.phi t / t) * ((1 + α) * t) :=
        mul_le_mul_of_nonneg_right hineq (by positivity)
      _ = (1 + α) * AdversarialBco.BodySpec.phi t := by
        field_simp [hpos_t.ne.symm]

theorem AdversarialBco.Poly.gauss_const (α : ℝ) (hα : 1 ≤ α) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.sqrt (2 * Real.log (1 + α)) ∧
      AdversarialBco.Poly.bathC α t ≤ Real.sqrt (2 * Real.log (1 + α)) := by
  obtain ⟨t, ht0, htQ⟩ := AdversarialBco.Poly.gc_quantile α hα
  have hbath_eq : AdversarialBco.Poly.bathC α t = (1 + α) * AdversarialBco.BodySpec.phi t := by
    dsimp [AdversarialBco.Poly.bathC]
    rw [htQ]
    have h_ne : 1 + α ≠ 0 := by linarith
    field_simp [h_ne]
    ring
  have h_lower : t ≤ (1 + α) * AdversarialBco.BodySpec.phi t :=
    AdversarialBco.Poly.gc_lower α t hα ht0 htQ
  have h_upper : (1 + α) * AdversarialBco.BodySpec.phi t ≤ Real.sqrt (2 * Real.log (1 + α)) :=
    AdversarialBco.Poly.gc_upper α t hα htQ
  have h_t_le_sqrt : t ≤ Real.sqrt (2 * Real.log (1 + α)) := by
    linarith
  have h_bath_le_sqrt : AdversarialBco.Poly.bathC α t ≤ Real.sqrt (2 * Real.log (1 + α)) := by
    rw [hbath_eq]
    exact h_upper
  exact ⟨t, ht0, h_t_le_sqrt, h_bath_le_sqrt⟩

theorem AdversarialBco.Poly.scale_stationary (k c : ℝ) (h : ∀ s : ℝ, 0 < s → k ≤ s * k - c * Real.log s) :
    k = c := by
  set f : ℝ → ℝ := λ s => s * k - c * Real.log s with hf
  have hf1 : f 1 = k := by
    dsimp [f]
    simp
  have hmin : IsLocalMin f 1 := by
    have hpos : (0 : ℝ) < 1 := by norm_num
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds hpos
    have h_all : ∀ s ∈ Set.Ioi (0 : ℝ), f 1 ≤ f s := by
      intro s hs
      rw [hf1]
      have hs_pos : 0 < s := hs
      exact h s hs_pos
    have h_eventually : ∀ᶠ s in 𝓝 (1 : ℝ), f 1 ≤ f s :=
      Filter.eventually_of_mem hmem h_all
    exact h_eventually
  have hderiv : HasDerivAt f (k - c) 1 := by
    dsimp [f]
    have h_id : HasDerivAt (λ s : ℝ => s) (1 : ℝ) (1 : ℝ) := hasDerivAt_id _
    have h_log : HasDerivAt Real.log (1 : ℝ) (1 : ℝ) := by
      have hx : (1 : ℝ) ≠ 0 := by norm_num
      have := Real.hasDerivAt_log hx
      simpa using this
    have h_mul : HasDerivAt (λ s : ℝ => s * k) k (1 : ℝ) := by
      have := HasDerivAt.mul h_id (hasDerivAt_const (1 : ℝ) k)
      -- this : HasDerivAt ((fun s => s) * fun x => k) (1 * k + 1 * 0) 1
      have h1 : ((fun s : ℝ => s) * fun _ : ℝ => k) = (fun s : ℝ => s * k) := by
        ext s; simp
      have h2 : (1 : ℝ) * k + (1 : ℝ) * (0 : ℝ) = k := by ring
      simpa [h1, h2] using this
    have h_log_mul : HasDerivAt (λ s : ℝ => c * Real.log s) c (1 : ℝ) := by
      have := HasDerivAt.const_mul c h_log
      simpa [mul_comm] using this
    have h_sub : HasDerivAt (λ s : ℝ => s * k - c * Real.log s) (k - c) (1 : ℝ) :=
      HasDerivAt.sub h_mul h_log_mul
    simpa using h_sub
  have h_eq_zero : k - c = 0 := IsLocalMin.hasDerivAt_eq_zero hmin hderiv
  linarith

theorem AdversarialBco.Poly.radius_of_bound {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsCompact S)
    (y0 : EuclideanSpace ℝ (Fin d)) (hy0 : y0 ∈ S) (q c β : ℝ) (hq : 0 < q) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (h6 : 6 * β ≤ q) (hb : ∀ y ∈ S, q * ‖y‖ ≤ c + β * (‖y - y0‖ + ‖y0‖)) : ∀ y ∈ S, ‖y‖ ≤ 2 * c / q := by
  have hS_nonempty : S.Nonempty := ⟨y0, hy0⟩
  have h_cont : ContinuousOn (fun (y : EuclideanSpace ℝ (Fin d)) => ‖y‖) S :=
    continuous_norm.continuousOn
  obtain ⟨y_star, hy_star, h_max⟩ := hS.exists_isMaxOn hS_nonempty h_cont
  have hy0_norm_le : ‖y0‖ ≤ ‖y_star‖ := h_max hy0
  have h_bound : q * ‖y_star‖ ≤ c + β * (‖y_star - y0‖ + ‖y0‖) := hb y_star hy_star
  have h_sub : ‖y_star - y0‖ ≤ ‖y_star‖ + ‖y0‖ := norm_sub_le _ _
  have h_ineq1 : q * ‖y_star‖ ≤ c + β * ((‖y_star‖ + ‖y0‖) + ‖y0‖) := by
    nlinarith
  have h_ineq2 : q * ‖y_star‖ ≤ c + 3 * β * ‖y_star‖ := by
    nlinarith
  have h_ineq3 : (q - 3 * β) * ‖y_star‖ ≤ c := by
    nlinarith
  have h_q_R_le_2c : q * ‖y_star‖ ≤ 2 * c := by
    have h_factor : q ≤ 2 * (q - 3 * β) := by
      nlinarith
    nlinarith
  have h_final : ‖y_star‖ ≤ 2 * c / q := by
    apply (le_div_iff₀ hq).mpr
    -- need: ‖y_star‖ * q ≤ 2 * c
    -- have: q * ‖y_star‖ ≤ 2 * c
    nlinarith
  intro y hy
  have hy_norm_le : ‖y‖ ≤ ‖y_star‖ := h_max hy
  nlinarith

theorem AdversarialBco.Poly.trace_rank_one {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    LinearMap.trace ℝ _ (((innerSL ℝ v).smulRight w : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = ⟪v, w⟫ := by
  have h := LinearMap.trace_smulRight (innerSL ℝ v : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) w
  simpa [ContinuousLinearMap.coe_smulRight] using h

theorem AdversarialBco.Poly.integrable_of_lipschitz {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith L F) : Integrable F (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h_meas : AEStronglyMeasurable F (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hF.continuous.aestronglyMeasurable
  have h_bound : ∀ x, |F x| ≤ |F 0| + (L : ℝ) * ‖x‖ := by
    intro x
    have h := hF.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at h
    calc
      |F x| = |(F x - F 0) + F 0| := by rw [sub_add_cancel]
      _ ≤ |F x - F 0| + |F 0| := abs_add_le _ _
      _ ≤ ((L : ℝ) * ‖x‖) + |F 0| := by nlinarith
      _ = |F 0| + (L : ℝ) * ‖x‖ := add_comm _ _
  have h_int_norm : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.integrable_id.norm
  have h_int_bound : Integrable (fun x : EuclideanSpace ℝ (Fin d) => |F 0| + (L : ℝ) * ‖x‖)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine (integrable_const (|F 0|)).add ?_
    exact h_int_norm.const_mul (L : ℝ)
  refine Integrable.mono' h_int_bound h_meas ?_
  filter_upwards [] with x
  simpa [Real.dist_eq] using h_bound x

theorem AdversarialBco.Poly.integrable_moments {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith L F) (v w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => ⟪v, g⟫ * F g) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => F g • g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hF_cont : Continuous F := hF.continuous
  have hF_ae : AEStronglyMeasurable F μ := hF_cont.aestronglyMeasurable

  -- Bound on |F g| from Lipschitz
  have hF_bound (g : EuclideanSpace ℝ (Fin d)) : |F g| ≤ |F 0| + (L : ℝ) * ‖g‖ := by
    have h := hF.dist_le_mul 0 g
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [norm_sub_rev] at h
    have h_zero_sub : ‖0 - g‖ = ‖g‖ := by simp
    rw [h_zero_sub] at h
    -- h : ‖F g - F 0‖ ≤ (L : ℝ) * ‖g‖
    have h_abs : |F g| ≤ |F 0| + |F g - F 0| := by
      calc
        |F g| = |(F g - F 0) + F 0| := by ring_nf
        _ ≤ |F g - F 0| + |F 0| := abs_add_le _ _
        _ = |F 0| + |F g - F 0| := add_comm _ _
    have h_abs_sub : |F g - F 0| = ‖F g - F 0‖ := by simp
    rw [h_abs_sub] at h_abs
    linarith

  -- Cauchy-Schwarz: |⟪v, g⟫| ≤ ‖v‖ * ‖g‖
  have h_cauchy_schwarz (g : EuclideanSpace ℝ (Fin d)) : |⟪v, g⟫| ≤ ‖v‖ * ‖g‖ := by
    calc
      |⟪v, g⟫| = |inner ℝ v g| := rfl
      _ ≤ ‖v‖ * ‖g‖ := abs_real_inner_le_norm _ _

  have h_cauchy_schwarz_w (g : EuclideanSpace ℝ (Fin d)) : |⟪w, g⟫| ≤ ‖w‖ * ‖g‖ := by
    calc
      |⟪w, g⟫| = |inner ℝ w g| := rfl
      _ ≤ ‖w‖ * ‖g‖ := abs_real_inner_le_norm _ _

  -- Helper: integrability of ‖g‖^k for any positive integer k
  have h_int_norm_pow (k : ℕ) (hk : k ≠ 0) : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ k) μ := by
    have hk_top : (k : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top k
    have h_mem : MemLp id ((k : ℕ) : ENNReal) μ := by
      have := IsGaussian.memLp_id μ (k : ENNReal) hk_top
      simpa using this
    exact MemLp.integrable_norm_pow h_mem hk

  -- Get integrability for k = 1, 2, 3
  have h_int_norm : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) μ := by
    simpa using h_int_norm_pow 1 (by norm_num)

  have h_int_norm_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) μ := by
    simpa using h_int_norm_pow 2 (by norm_num)

  have h_int_norm_cube : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 3) μ := by
    simpa using h_int_norm_pow 3 (by norm_num)

  -- Now prove the three integrabilities

  -- First: Integrable (fun g => ⟪v, g⟫ * F g) μ
  have h1 : Integrable (fun g => ⟪v, g⟫ * F g) μ := by
    -- Bound: |⟪v, g⟫ * F g| ≤ ‖v‖ * |F 0| * ‖g‖ + ‖v‖ * L * ‖g‖^2
    let bound (g : EuclideanSpace ℝ (Fin d)) : ℝ := ‖v‖ * |F 0| * ‖g‖ + ‖v‖ * (L : ℝ) * ‖g‖ ^ 2
    have h_bound_int : Integrable bound μ := by
      dsimp [bound]
      refine Integrable.add ?_ ?_
      · -- ‖v‖ * |F 0| * ‖g‖
        have : (fun g : EuclideanSpace ℝ (Fin d) => ‖v‖ * |F 0| * ‖g‖) =
               (fun g => (|F 0| * ‖v‖) * ‖g‖) := by
          ext g; ring
        rw [this]
        exact h_int_norm.const_mul (|F 0| * ‖v‖)
      · -- ‖v‖ * L * ‖g‖^2
        have : (fun g : EuclideanSpace ℝ (Fin d) => ‖v‖ * (L : ℝ) * ‖g‖ ^ 2) =
               (fun g => ((L : ℝ) * ‖v‖) * (‖g‖ ^ 2)) := by
          ext g; ring
        rw [this]
        exact h_int_norm_sq.const_mul ((L : ℝ) * ‖v‖)
    have h_meas : AEStronglyMeasurable (fun g => ⟪v, g⟫ * F g) μ := by
      have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => ⟪v, g⟫ * F g) := by
        exact (continuous_const.inner continuous_id).mul hF_cont
      exact h_cont.aestronglyMeasurable
    have h_bound : ∀ᵐ g ∂μ, ‖(fun g => ⟪v, g⟫ * F g) g‖ ≤ bound g := by
      filter_upwards [] with g
      rw [Real.norm_eq_abs, abs_mul]
      have h_nonneg_inner : 0 ≤ |⟪v, g⟫| := abs_nonneg _
      have h_nonneg_Fg : 0 ≤ |F g| := abs_nonneg _
      have h_nonneg_v : 0 ≤ ‖v‖ := norm_nonneg _
      have h_nonneg_g : 0 ≤ ‖g‖ := norm_nonneg _
      have h_nonneg_F0 : 0 ≤ |F 0| := abs_nonneg _
      have h_nonneg_L : 0 ≤ (L : ℝ) := NNReal.coe_nonneg _
      calc
        |⟪v, g⟫| * |F g| ≤ (‖v‖ * ‖g‖) * |F g| := by
          apply mul_le_mul_of_nonneg_right (h_cauchy_schwarz g) h_nonneg_Fg
        _ ≤ (‖v‖ * ‖g‖) * (|F 0| + (L : ℝ) * ‖g‖) := by
          apply mul_le_mul_of_nonneg_left (hF_bound g) ?_
          nlinarith
        _ = ‖v‖ * |F 0| * ‖g‖ + ‖v‖ * (L : ℝ) * ‖g‖ ^ 2 := by ring
    exact Integrable.mono' h_bound_int h_meas h_bound

  -- Second: Integrable (fun g => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) μ
  have h2 : Integrable (fun g => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) μ := by
    -- Bound: |(⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g|
    -- ≤ (‖v‖*‖w‖*‖g‖^2 + ‖v‖*‖w‖) * (|F 0| + L*‖g‖)
    let bound (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
      ‖v‖ * ‖w‖ * |F 0| * ‖g‖ ^ 2 + ‖v‖ * ‖w‖ * (L : ℝ) * ‖g‖ ^ 3 + ‖v‖ * ‖w‖ * |F 0| + ‖v‖ * ‖w‖ * (L : ℝ) * ‖g‖
    have h_bound_int : Integrable bound μ := by
      dsimp [bound]
      refine Integrable.add (Integrable.add (Integrable.add ?_ ?_) ?_) ?_
      · exact h_int_norm_sq.const_mul (‖v‖ * ‖w‖ * |F 0|)
      · exact h_int_norm_cube.const_mul (‖v‖ * ‖w‖ * (L : ℝ))
      · exact integrable_const _
      · exact h_int_norm.const_mul (‖v‖ * ‖w‖ * (L : ℝ))
    have h_meas : AEStronglyMeasurable (fun g => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) μ := by
      have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) := by
        refine ((continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)
          |>.sub continuous_const) |>.mul hF_cont
      exact h_cont.aestronglyMeasurable
    have h_bound : ∀ᵐ g ∂μ, ‖(fun g => (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g) g‖ ≤ bound g := by
      filter_upwards [] with g
      rw [Real.norm_eq_abs, abs_mul]
      -- |(⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g| = |⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫| * |F g|
      have h_inner_prod : |⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫| ≤ ‖v‖ * ‖w‖ * ‖g‖ ^ 2 + ‖v‖ * ‖w‖ := by
        have h_nonneg_vw : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have h_nonneg_g2 : 0 ≤ ‖g‖ ^ 2 := by positivity
        have h_nonneg_inner_vw : 0 ≤ |⟪v, w⟫| := abs_nonneg _
        have h_nonneg_inner_vg : 0 ≤ |⟪v, g⟫| := abs_nonneg _
        have h_nonneg_inner_wg : 0 ≤ |⟪w, g⟫| := abs_nonneg _
        have h_nonneg_vg : 0 ≤ ‖v‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have h_nonneg_wg : 0 ≤ ‖w‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc
          |⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫| ≤ |⟪v, g⟫ * ⟪w, g⟫| + |⟪v, w⟫| := abs_sub _ _
          _ = |⟪v, g⟫| * |⟪w, g⟫| + |⟪v, w⟫| := by rw [abs_mul]
          _ ≤ (‖v‖ * ‖g‖) * (‖w‖ * ‖g‖) + |⟪v, w⟫| := by
            have hprod : |⟪v, g⟫| * |⟪w, g⟫| ≤ (‖v‖ * ‖g‖) * (‖w‖ * ‖g‖) :=
              mul_le_mul (h_cauchy_schwarz g) (h_cauchy_schwarz_w g) h_nonneg_inner_wg h_nonneg_vg
            nlinarith
          _ = (‖v‖ * ‖w‖) * (‖g‖ * ‖g‖) + |⟪v, w⟫| := by ring
          _ = (‖v‖ * ‖w‖) * (‖g‖ ^ 2) + |⟪v, w⟫| := by ring
          _ ≤ ‖v‖ * ‖w‖ * ‖g‖ ^ 2 + ‖v‖ * ‖w‖ := by
            have h_inner_vw : |⟪v, w⟫| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm _ _
            nlinarith
      have h_nonneg_inner_prod : 0 ≤ |⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫| := abs_nonneg _
      have h_nonneg_Fg : 0 ≤ |F g| := abs_nonneg _
      have h_nonneg_F0 : 0 ≤ |F 0| := abs_nonneg _
      have h_nonneg_L : 0 ≤ (L : ℝ) := NNReal.coe_nonneg _
      have h_nonneg_g : 0 ≤ ‖g‖ := norm_nonneg _
      calc
        |⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫| * |F g| ≤ (‖v‖ * ‖w‖ * ‖g‖ ^ 2 + ‖v‖ * ‖w‖) * (|F 0| + (L : ℝ) * ‖g‖) := by
          apply mul_le_mul h_inner_prod (hF_bound g) h_nonneg_Fg ?_
          nlinarith
        _ = ‖v‖ * ‖w‖ * |F 0| * ‖g‖ ^ 2 + ‖v‖ * ‖w‖ * (L : ℝ) * ‖g‖ ^ 3 + ‖v‖ * ‖w‖ * |F 0| + ‖v‖ * ‖w‖ * (L : ℝ) * ‖g‖ := by ring
    exact Integrable.mono' h_bound_int h_meas h_bound

  -- Third: Integrable (fun g => F g • g) μ
  have h3 : Integrable (fun g => F g • g) μ := by
    -- Bound: ‖F g • g‖ = |F g| * ‖g‖ ≤ (|F 0| + L*‖g‖) * ‖g‖ = |F 0|*‖g‖ + L*‖g‖^2
    let bound (g : EuclideanSpace ℝ (Fin d)) : ℝ := |F 0| * ‖g‖ + (L : ℝ) * ‖g‖ ^ 2
    have h_bound_int : Integrable bound μ := by
      dsimp [bound]
      refine Integrable.add ?_ ?_
      · exact h_int_norm.const_mul (|F 0|)
      · exact h_int_norm_sq.const_mul (L : ℝ)
    have h_meas : AEStronglyMeasurable (fun g => F g • g) μ := by
      have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => F g • g) := by
        exact hF_cont.smul continuous_id
      exact h_cont.aestronglyMeasurable
    have h_bound : ∀ᵐ g ∂μ, ‖(fun g => F g • g) g‖ ≤ bound g := by
      filter_upwards [] with g
      show ‖F g • g‖ ≤ bound g
      rw [norm_smul, Real.norm_eq_abs]
      -- Now goal: |F g| * ‖g‖ ≤ bound g
      have h_nonneg_Fg : 0 ≤ |F g| := abs_nonneg _
      have h_nonneg_g : 0 ≤ ‖g‖ := norm_nonneg _
      have h_nonneg_F0 : 0 ≤ |F 0| := abs_nonneg _
      have h_nonneg_L : 0 ≤ (L : ℝ) := NNReal.coe_nonneg _
      calc
        |F g| * ‖g‖ ≤ (|F 0| + (L : ℝ) * ‖g‖) * ‖g‖ := by
          apply mul_le_mul_of_nonneg_right (hF_bound g) h_nonneg_g
        _ = |F 0| * ‖g‖ + (L : ℝ) * ‖g‖ ^ 2 := by ring
    exact Integrable.mono' h_bound_int h_meas h_bound

  exact ⟨h1, h2, h3⟩

theorem AdversarialBco.Poly.first_order_ae {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hGL : LipschitzWith L G) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hdet : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (hdiff : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ G (b + S g))
    (hmin : ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
          ∫ g, G (b' + S' g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)
    (db : EuclideanSpace ℝ (Fin d)) (E' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ g, fderiv ℝ G (b + S g) (db + S (E' g)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      lam * LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let a (g : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := b + S g
  let c (g : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := db + S (E' g)
  let F (t : ℝ) (g : EuclideanSpace ℝ (Fin d)) : ℝ := G (a g + t • c g)
  let S' (t : ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    S.comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) + t • E')
  let Ldet (t : ℝ) : ℝ := Real.log |LinearMap.det (S' t : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|
  let f (t : ℝ) : ℝ := (∫ g, F t g ∂γ) - lam * Ldet t
  have h_cont_a : Continuous a := by
    dsimp [a]; exact (continuous_const.add S.continuous)
  have h_cont_c : Continuous c := by
    dsimp [c]; exact (continuous_const.add (S.comp E').continuous)
  -- f has a local minimum at 0
  have h_local_min : IsLocalMin f 0 := by
    have h_det_nonzero : ∀ᶠ t in nhds (0 : ℝ),
        LinearMap.det (S' t : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 :=
      (AdversarialBco.Body.hasDerivAt_log_abs_det_comp S E' hdet).1
    have h_min : ∀ᶠ t in nhds (0 : ℝ), f 0 ≤ f t := by
      filter_upwards [h_det_nonzero] with t ht
      have h_f0 : f 0 = (∫ g, G (b + S g) ∂γ) - lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
        dsimp [f, F, Ldet, S', a, c]; simp
      have h_ft : f t = (∫ g, G (b + t • db + (S' t) g) ∂γ) -
          lam * Real.log |LinearMap.det (S' t : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
        dsimp [f, F, Ldet, S', a, c]
        have h_eq : (fun g => G ((b + S g) + t • (db + S (E' g)))) =
            (fun g => G (b + t • db + (S.comp (ContinuousLinearMap.id ℝ _ + t • E')) g)) := by
          ext g
          congr 1
          calc
            (b + S g) + t • (db + S (E' g)) = (b + S g) + (t • db + t • S (E' g)) := by simp [smul_add]
            _ = b + t • db + (S g + t • S (E' g)) := by abel
            _ = b + t • db + S (g + t • E' g) := by simp
            _ = b + t • db + (S.comp (ContinuousLinearMap.id ℝ _ + t • E')) g := rfl
        rw [h_eq]
        simp [ContinuousLinearMap.comp_apply]
      rw [h_f0, h_ft]
      exact hmin (b + t • db) (S' t) ht
    exact h_min
  -- Derivative of the integral term via dominated convergence
  have h_int_deriv : HasDerivAt (fun t => ∫ g, F t g ∂γ) (∫ g, fderiv ℝ G (a g) (c g) ∂γ) 0 := by
    set s := Set.univ with hs
    have hs_nhds : s ∈ nhds (0 : ℝ) := by
      rw [hs]; exact Filter.univ_mem
    have hF_meas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) γ := by
      refine Filter.Eventually.of_forall ?_
      intro t
      have h_cont_Ft : Continuous (F t) := by
        dsimp [F]; exact hGL.continuous.comp ((h_cont_a.add (h_cont_c.const_smul t)))
      exact h_cont_Ft.aestronglyMeasurable
    have hF_int : Integrable (F 0) γ := by
      have h_lip : LipschitzWith (L * ‖S‖₊) (fun g => G (a g)) := by
        have h_affine_lip : LipschitzWith ‖S‖₊ a := by
          refine LipschitzWith.of_dist_le_mul ?_
          intro g₁ g₂
          dsimp [a]
          calc
            dist (b + S g₁) (b + S g₂) = ‖(b + S g₁) - (b + S g₂)‖ := rfl
            _ = ‖S g₁ - S g₂‖ := by simp
            _ = dist (S g₁) (S g₂) := rfl
            _ ≤ ‖S‖₊ * dist g₁ g₂ := S.lipschitz.dist_le_mul g₁ g₂
        exact hGL.comp h_affine_lip
      have : F 0 = fun g => G (a g) := by ext g; dsimp [F]; simp
      rw [this]
      exact AdversarialBco.Poly.integrable_of_lipschitz _ _ h_lip
    have hF'_meas : AEStronglyMeasurable (fun g => fderiv ℝ G (a g) (c g)) γ := by
      have h_meas : Measurable (fun g => fderiv ℝ G (a g) (c g)) := by
        have h_meas_fderiv : Measurable (fderiv ℝ G) := measurable_fderiv ℝ G
        have h_meas_a : Measurable a := h_cont_a.measurable
        have h_meas_c : Measurable c := h_cont_c.measurable
        have h_eval_meas : Measurable (fun (p : ((EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) × (EuclideanSpace ℝ (Fin d))) => p.1 p.2) :=
          ContinuousLinearMap.measurable_apply₂ (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (F := ℝ)
        have h_pair_meas : Measurable (fun g => (fderiv ℝ G (a g), c g)) :=
          Measurable.prodMk (h_meas_fderiv.comp h_meas_a) h_meas_c
        exact h_eval_meas.comp h_pair_meas
      exact h_meas.aestronglyMeasurable
    have h_lipsch : ∀ᵐ g ∂γ, LipschitzOnWith (Real.nnabs ((L : ℝ) * ‖c g‖)) (fun t => F t g) s := by
      filter_upwards [hdiff] with g hg_diff
      have h_line_lip : LipschitzWith ‖c g‖₊ (fun (t : ℝ) => a g + t • c g) := by
        refine LipschitzWith.of_dist_le_mul ?_
        intro t₁ t₂
        calc
          dist (a g + t₁ • c g) (a g + t₂ • c g) = ‖(a g + t₁ • c g) - (a g + t₂ • c g)‖ := rfl
          _ = ‖(t₁ - t₂) • c g‖ := by simp [sub_smul]
          _ = |t₁ - t₂| * ‖c g‖ := by simp [norm_smul]
          _ = ‖c g‖ * |t₁ - t₂| := mul_comm _ _
          _ ≤ (‖c g‖₊ : ℝ) * dist t₁ t₂ := by simp [dist_eq_norm]
      have h_lip : LipschitzWith (L * ‖c g‖₊) (fun t => G (a g + t • c g)) :=
        hGL.comp h_line_lip
      have h_goal : LipschitzOnWith (Real.nnabs ((L : ℝ) * ‖c g‖)) (fun t => F t g) Set.univ := by
        have h_eq_fun : (fun t => F t g) = (fun t => G (a g + t • c g)) := by
          ext t; rfl
        rw [h_eq_fun]
        apply (lipschitzOnWith_univ (K := Real.nnabs ((L : ℝ) * ‖c g‖)) (f := fun t => G (a g + t • c g))).mpr
        have h_nonneg : 0 ≤ (L : ℝ) * ‖c g‖ := mul_nonneg (NNReal.coe_nonneg L) (norm_nonneg _)
        have h_const_eq : Real.nnabs ((L : ℝ) * ‖c g‖) = L * ‖c g‖₊ := by
          rw [Real.nnabs_of_nonneg h_nonneg]
          ext
          simp [Real.coe_toNNReal _ h_nonneg]
        rw [h_const_eq]
        exact h_lip
      exact h_goal
    have bound_integrable : Integrable (fun g => (L : ℝ) * ‖c g‖) γ := by
      have hc_lip : LipschitzWith ‖S.comp E'‖₊ c := by
        refine LipschitzWith.of_dist_le_mul fun g₁ g₂ => ?_
        simp only [c, dist_eq_norm]
        rw [add_sub_add_left_eq_sub, ← map_sub, ← map_sub]
        simpa using (S.comp E').le_opNorm (g₁ - g₂)
      have h_norm_c_lip : LipschitzWith ‖S.comp E'‖₊ (fun g => ‖c g‖) := by
        have h_temp : LipschitzWith (1 * ‖S.comp E'‖₊) (norm ∘ c) := lipschitzWith_one_norm.comp hc_lip
        rw [one_mul] at h_temp
        exact h_temp
      have h_int_norm_c : Integrable (fun g => ‖c g‖) γ :=
        AdversarialBco.Poly.integrable_of_lipschitz _ _ h_norm_c_lip
      exact h_int_norm_c.const_mul (L : ℝ)
    have h_diff : ∀ᵐ g ∂γ, HasDerivAt (fun t => F t g) (fderiv ℝ G (a g) (c g)) 0 := by
      filter_upwards [hdiff] with g hg_diff
      have hG_fderiv : HasFDerivAt G (fderiv ℝ G (a g)) (a g) := by
        simpa [a] using hg_diff.hasFDerivAt
      have h_line_deriv : HasDerivAt (fun (t : ℝ) => a g + t • c g) (c g) 0 := by
        have h_const : HasDerivAt (fun (_ : ℝ) => a g) 0 0 := hasDerivAt_const _ _
        have h_smul : HasDerivAt (fun (t : ℝ) => t • c g) (c g) 0 := by
          simpa [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const (c g)
        have h_add := h_const.add h_smul
        rw [zero_add] at h_add
        exact h_add
      have hG_fderiv' : HasFDerivAt G (fderiv ℝ G (a g)) ((fun (t : ℝ) => a g + t • c g) 0) := by
        simpa using hG_fderiv
      have h_comp := hG_fderiv'.comp_hasDerivAt 0 h_line_deriv
      simpa [F, Function.comp_def] using h_comp
    rcases hasDerivAt_integral_of_dominated_loc_of_lip hs_nhds hF_meas hF_int hF'_meas h_lipsch
      bound_integrable h_diff with ⟨_, h_int_deriv'⟩
    exact h_int_deriv'
  -- Derivative of the log-det term
  have h_log_deriv : HasDerivAt Ldet (LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
    dsimp [Ldet, S']
    exact (AdversarialBco.Body.hasDerivAt_log_abs_det_comp S E' hdet).2
  -- Combine derivatives
  have h_f_deriv : HasDerivAt f ((∫ g, fderiv ℝ G (a g) (c g) ∂γ) -
      lam * LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 := by
    dsimp [f]
    have h_log_lam : HasDerivAt (fun t => lam * Ldet t) (lam * LinearMap.trace ℝ _ (E' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) 0 :=
      h_log_deriv.const_mul lam
    exact h_int_deriv.sub h_log_lam
  -- Apply IsLocalMin.hasDerivAt_eq_zero
  have h_eq_zero := h_local_min.hasDerivAt_eq_zero h_f_deriv
  simpa [a, c] using sub_eq_zero.mp h_eq_zero

theorem AdversarialBco.Poly.posBody_compact {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : AdversarialBco.Poly.IsPosBody K r0 α)
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) :
    IsCompact (AdversarialBco.Poly.posBody K μ A) ∧ Convex ℝ (AdversarialBco.Poly.posBody K μ A) := by
  have hK_conv : Convex ℝ K := hK.1
  have hK_compact : IsCompact K := hK.2.1
  have hA_det : A.det ≠ 0 := by
    simpa using hA
  let φ := A.toContinuousLinearEquivOfDetNeZero hA_det
  have hφ_apply (x : EuclideanSpace ℝ (Fin d)) : φ x = A x := by
    rfl
  have h_compact : IsCompact (AdversarialBco.Poly.posBody K μ A) := by
    have h_eq : AdversarialBco.Poly.posBody K μ A = (fun y => φ.symm (y - μ)) '' K := by
      ext y
      constructor
      · intro hy
        dsimp [AdversarialBco.Poly.posBody] at hy
        refine ⟨μ + A y, hy, ?_⟩
        dsimp
        have : (μ + A y) - μ = A y := by simp
        rw [this, ← hφ_apply y]
        simp
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        dsimp [AdversarialBco.Poly.posBody]
        rw [← hφ_apply (φ.symm (x - μ)), φ.apply_symm_apply (x - μ)]
        have hx' : μ + (x - μ) = x := by abel
        rw [hx']
        exact hx
    rw [h_eq]
    have h_cont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => φ.symm (y - μ)) :=
      φ.symm.continuous.comp (continuous_id.sub continuous_const)
    exact hK_compact.image h_cont
  have h_convex : Convex ℝ (AdversarialBco.Poly.posBody K μ A) := by
    intro x hx y hy a b ha hb hab
    dsimp [AdversarialBco.Poly.posBody] at hx hy ⊢
    have h : μ + A (a • x + b • y) = a • (μ + A x) + b • (μ + A y) := by
      calc
        μ + A (a • x + b • y) = μ + (A (a • x) + A (b • y)) := by rw [A.map_add]
        _ = μ + (a • A x + b • A y) := by rw [A.map_smul, A.map_smul]
        _ = (a • μ + b • μ) + (a • A x + b • A y) := by
          have hμ : μ = a • μ + b • μ := by
            calc
              μ = (a + b) • μ := by rw [hab, one_smul]
              _ = a • μ + b • μ := by rw [add_smul]
          rw [← hμ]
        _ = a • μ + a • A x + (b • μ + b • A y) := by abel
        _ = a • (μ + A x) + b • (μ + A y) := by rw [smul_add, smul_add]
    rw [h]
    exact hK_conv hx hy ha hb hab
  exact And.intro h_compact h_convex

theorem AdversarialBco.Poly.propCb_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : AdversarialBco.Poly.IsPosBody K r0 α) (a : ℝ)
    (ha : AdversarialBco.Poly.posK K μ A ≤ AdversarialBco.BodySpec.Qtail a) :
    Metric.closedBall 0 a ⊆ AdversarialBco.Poly.posBody K μ A := by
  rcases hK with ⟨hK_conv, hK_compact, hr0_pos, hK_ball, hα_nonneg, hK_sym⟩
  have hK_closed : IsClosed K := hK_compact.isClosed
  set F := AdversarialBco.Poly.posF K μ A with hF_def
  set K' := AdversarialBco.Poly.posBody K μ A with hK'_def
  -- K' is closed (preimage of closed K under continuous map)
  have hK'_closed : IsClosed K' := by
    rw [hK'_def, AdversarialBco.Poly.posBody]
    have h_cont : Continuous (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) := by continuity
    exact hK_closed.preimage h_cont
  -- K' is convex (preimage of convex K under affine map)
  have hK'_convex : Convex ℝ K' := by
    rw [hK'_def, AdversarialBco.Poly.posBody]
    let φ : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      AffineMap.mk' (fun y => μ + A y) (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) 0
        (by
          intro p'
          simp [add_comm])
    exact hK_conv.affine_preimage φ
  have hF_nonneg : ∀ y, 0 ≤ F y := by
    intro y
    dsimp [F, AdversarialBco.Poly.posF]
    exact gauge_nonneg _
  -- F is integrable w.r.t. stdGaussian
  have hF_integrable : Integrable F (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    dsimp [F, AdversarialBco.Poly.posF]
    let r0' : NNReal := ⟨r0, hr0_pos.le⟩
    have hr0'_pos : 0 < r0' := hr0_pos
    have h_ball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r0' : ℝ) ⊆ K :=
      hK_ball
    have h_gauge_lipschitz : LipschitzWith r0'⁻¹ (gauge K) :=
      Convex.lipschitzWith_gauge hK_conv hr0'_pos h_ball'
    have h_affine_lipschitz : LipschitzWith ‖A‖₊ (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) := by
      have h_trans_lipschitz : LipschitzWith (1 : NNReal) (fun (z : EuclideanSpace ℝ (Fin d)) => μ + z) :=
        LipschitzWith.of_dist_le_mul (by
          intro x y
          simp [dist_eq_norm, add_sub_add_left_eq_sub])
      have hA_lipschitz : LipschitzWith ‖A‖₊ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
        ContinuousLinearMap.lipschitzWith A
      have h_comp : LipschitzWith ((1 : NNReal) * ‖A‖₊) ((fun (z : EuclideanSpace ℝ (Fin d)) => μ + z) ∘ A) :=
        LipschitzWith.comp h_trans_lipschitz hA_lipschitz
      simpa [Function.comp_def, mul_comm] using h_comp
    have hF_lipschitz : LipschitzWith (r0'⁻¹ * ‖A‖₊)
        (gauge K ∘ (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y)) :=
      LipschitzWith.comp h_gauge_lipschitz h_affine_lipschitz
    exact AdversarialBco.Poly.integrable_of_lipschitz
      (gauge K ∘ (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y)) (r0'⁻¹ * ‖A‖₊) hF_lipschitz
  -- Apply Markov inequality: μ.real {y | 1 < F y} ≤ posK K μ A
  have h_markov : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | 1 < F y} ≤
      AdversarialBco.Poly.posK K μ A := by
    have h_int : ∫ y, F y ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = AdversarialBco.Poly.posK K μ A := by
      dsimp [F, AdversarialBco.Poly.posK]
    have h_nonneg_ae : 0 ≤ᵐ[stdGaussian (EuclideanSpace ℝ (Fin d))] F :=
      Filter.Eventually.of_forall hF_nonneg
    have h_markov' := mul_meas_ge_le_integral_of_nonneg h_nonneg_ae hF_integrable (1 : ℝ)
    -- h_markov' : 1 * μ.real {y | 1 ≤ F y} ≤ ∫ F
    have h_subset : {y | 1 < F y} ⊆ {y | (1 : ℝ) ≤ F y} := by
      intro y hy
      have hy' : 1 < F y := hy
      exact hy'.le
    have h_meas : (stdGaussian (EuclideanSpace ℝ (Fin d))) ({y | (1 : ℝ) ≤ F y}) ≠ ⊤ := by
      -- Gaussian measure is finite
      have : IsFiniteMeasure (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        infer_instance
      exact measure_ne_top _ _
    have h_le : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | 1 < F y} ≤
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | (1 : ℝ) ≤ F y} :=
      measureReal_mono h_subset h_meas
    have h_markov'' : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | (1 : ℝ) ≤ F y} ≤
        ∫ y, F y ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      linarith [h_markov']
    calc
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | 1 < F y} ≤
          (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | (1 : ℝ) ≤ F y} := h_le
      _ ≤ ∫ y, F y ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := h_markov''
      _ = AdversarialBco.Poly.posK K μ A := by rw [h_int]
  -- Therefore μ.real K' = 1 - μ.real {y | 1 < F y} ≥ 1 - posK ≥ 1 - Qtail a
  have hK'_measure_ge : 1 - AdversarialBco.BodySpec.Qtail a ≤
      (stdGaussian (EuclideanSpace ℝ (Fin d))).real K' := by
    have h_total : (stdGaussian (EuclideanSpace ℝ (Fin d))).real Set.univ = 1 :=
      probReal_univ
    have hK'_eq : K' = {y | F y ≤ 1} := by
      ext y
      dsimp [K', AdversarialBco.Poly.posBody, F, AdversarialBco.Poly.posF]
      -- Need: μ + A y ∈ K ↔ gauge K (μ + A y) ≤ 1
      -- This is exactly gauge_le_one_iff
      have hK_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) := by
        rw [Metric.mem_nhds_iff]
        exact ⟨r0, hr0_pos, hK_ball⟩
      rw [AdversarialBco.Poly.gauge_le_one_iff K hK_conv hK_closed hK_nhds (μ + A y)]
    have h_compl : (stdGaussian (EuclideanSpace ℝ (Fin d))).real K'ᶜ =
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real {y | 1 < F y} := by
      rw [hK'_eq]
      -- {y | F y ≤ 1}ᶜ = {y | 1 < F y}
      have h_compl_eq : {y | F y ≤ 1}ᶜ = {y | (1 : ℝ) < F y} := by
        ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      rw [h_compl_eq]
    have h_finite : (stdGaussian (EuclideanSpace ℝ (Fin d))) K' ≠ ⊤ := by
      have : IsFiniteMeasure (stdGaussian (EuclideanSpace ℝ (Fin d))) := by infer_instance
      exact measure_ne_top _ _
    have h_meas_K' : MeasurableSet K' := hK'_closed.measurableSet
    have h_measure_compl : (stdGaussian (EuclideanSpace ℝ (Fin d))).real K'ᶜ =
        1 - (stdGaussian (EuclideanSpace ℝ (Fin d))).real K' := by
      rw [probReal_compl_eq_one_sub h_meas_K']
    rw [← h_compl, h_measure_compl] at h_markov
    linarith
  -- Now the main proof: take y with ‖y‖ ≤ a, show y ∈ K'
  intro y hy
  have hy_norm : ‖y‖ ≤ a := by
    have hy' := hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy'
    exact hy'
  by_contra! hy_notin
  -- y ∉ K', so F y > 1
  have hFy_gt_one : 1 < F y := by
    have hK'_eq : K' = {y | F y ≤ 1} := by
      ext y
      dsimp [K', AdversarialBco.Poly.posBody, F, AdversarialBco.Poly.posF]
      have hK_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) := by
        rw [Metric.mem_nhds_iff]
        exact ⟨r0, hr0_pos, hK_ball⟩
      rw [AdversarialBco.Poly.gauge_le_one_iff K hK_conv hK_closed hK_nhds (μ + A y)]
    have hy_notin' : y ∉ {y | F y ≤ 1} := by
      rw [← hK'_eq]
      exact hy_notin
    simp_rw [Set.mem_setOf_eq] at hy_notin'
    exact lt_of_not_ge hy_notin'
  -- Apply geometric Hahn-Banach separation
  have h_sep := geometric_hahn_banach_closed_point hK'_convex hK'_closed hy_notin
  rcases h_sep with ⟨f, s, hf_lt, hs_lt⟩
  -- Riesz representation: f = inner w · for some w
  let w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm f
  have hf_eq : ∀ z, f z = ⟪w, z⟫ := by
    intro z
    have h_eq : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) w = f :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).apply_symm_apply f
    calc
      f z = ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) w) z := by rw [← h_eq]
      _ = ⟪w, z⟫ := by rw [InnerProductSpace.toDual_apply_apply]
  -- If w = 0, then f = 0, so s < 0. Also K' must be empty (otherwise 0 < s and s < 0).
  -- Then μ.real K' = 0, so 1 - Qtail a ≤ 0, i.e., Qtail a ≥ 1.
  -- But Qtail a < 1 (from Qtail_neg and positivity of Qtail), contradiction.
  by_cases hw_zero : w = 0
  · have hf_zero : ∀ z, f z = 0 := by
      intro z
      rw [hf_eq z, hw_zero]
      simp
    have hs_neg : s < 0 := by
      rw [hf_zero y] at hs_lt
      exact hs_lt
    by_cases hK'_empty : K' = ∅
    · -- K' is empty, so μ.real K' = 0
      have hK'_real_zero : (stdGaussian (EuclideanSpace ℝ (Fin d))).real K' = 0 := by
        rw [hK'_empty]
        simp
      rw [hK'_real_zero] at hK'_measure_ge
      have hQtail_ge_one : 1 ≤ AdversarialBco.BodySpec.Qtail a := by linarith
      -- From Qtail_neg, Qtail (-a) = 1 - Qtail a ≥ 0, so Qtail a ≤ 1
      -- But Qtail a ≥ 1, so Qtail a = 1, so Qtail (-a) = 0
      -- But Qtail (-a) > 0 since phi > 0 on Ioi (-a), contradiction
      have hQtail_neg_nonneg : 0 ≤ AdversarialBco.BodySpec.Qtail (-a) := by
        dsimp [AdversarialBco.BodySpec.Qtail]
        refine integral_nonneg (fun s => ?_)
        dsimp [AdversarialBco.BodySpec.phi]
        positivity
      have hQtail_neg_eq : AdversarialBco.BodySpec.Qtail (-a) = 1 - AdversarialBco.BodySpec.Qtail a :=
        AdversarialBco.Body2.Qtail_neg a
      have hQtail_eq_one : AdversarialBco.BodySpec.Qtail a = 1 := by linarith
      rw [hQtail_neg_eq, hQtail_eq_one] at hQtail_neg_nonneg
      have hQtail_neg_zero : AdversarialBco.BodySpec.Qtail (-a) = 0 := by linarith
      -- Now show Qtail (-a) > 0 using integrable_gaussianPDFReal
      have hQtail_neg_pos : 0 < AdversarialBco.BodySpec.Qtail (-a) := by
        have h_int_phi : MeasureTheory.Integrable BodySpec.phi MeasureTheory.volume := by
          -- phi = gaussianPDFReal 0 1
          have h_phi_eq : BodySpec.phi = ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) := by
            ext t
            simp [BodySpec.phi, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, mul_comm, mul_left_comm]
          rw [h_phi_eq]
          exact ProbabilityTheory.integrable_gaussianPDFReal (0 : ℝ) (1 : NNReal)
        have h_int_on : MeasureTheory.IntegrableOn BodySpec.phi (Set.Ioi (-a)) MeasureTheory.volume :=
          h_int_phi.integrableOn
        have h_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (-a))] BodySpec.phi := by
          refine Filter.Eventually.of_forall (fun s => ?_)
          have hpos : 0 < BodySpec.phi s := by
            dsimp [BodySpec.phi]
            positivity
          exact hpos.le
        have h_support : 0 < MeasureTheory.volume (Function.support BodySpec.phi ∩ Set.Ioi (-a)) := by
          have h_support_phi : Function.support BodySpec.phi = Set.univ := by
            ext s
            dsimp [Function.support, BodySpec.phi]
            have h_sqrt_pos : Real.sqrt (2 * Real.pi) ≠ 0 :=
              Real.sqrt_ne_zero'.mpr (by positivity)
            have h_exp_pos : Real.exp (-(s ^ 2) / 2) ≠ 0 := Real.exp_ne_zero _
            constructor
            · intro h; exact Set.mem_univ _
            · intro h; exact div_ne_zero h_exp_pos h_sqrt_pos
          rw [h_support_phi, Set.univ_inter]
          have h_nonempty : (Set.Ioi (-a) : Set ℝ).Nonempty := by
            refine ⟨-a + 1, Set.mem_Ioi.mpr ?_⟩
            nlinarith
          have h_pos : 0 < MeasureTheory.volume (Set.Ioi (-a) : Set ℝ) := by
            have h_interval : Set.Ioo (-a) (-a + 1) ⊆ Set.Ioi (-a) := by
              intro x hx; exact Set.mem_Ioi.mpr (by linarith [hx.1])
            have h_vol_interval : 0 < MeasureTheory.volume (Set.Ioo (-a) (-a + 1) : Set ℝ) := by
              simp
            exact lt_of_lt_of_le h_vol_interval (MeasureTheory.measure_mono h_interval)
          exact h_pos
        have h_pos_iff := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae h_nonneg h_int_on).mpr h_support
        dsimp [AdversarialBco.BodySpec.Qtail]
        exact h_pos_iff
      have : (0 : ℝ) < 0 := by
        simpa [hQtail_neg_zero] using hQtail_neg_pos
      exact lt_irrefl _ this
    · -- K' is nonempty, so ∃ z ∈ K', and then 0 < s from hf_lt, contradicting s < 0
      have hK'_nonempty : Set.Nonempty K' := Set.nonempty_iff_ne_empty.mpr hK'_empty
      rcases hK'_nonempty with ⟨z, hz⟩
      have hs_pos : 0 < s := by
        rw [← hf_zero z]
        exact hf_lt z hz
      linarith
  · -- w ≠ 0, so we can form unit vector u = w / ‖w‖
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_zero
    set u := (‖w‖⁻¹ : ℝ) • w with hu_def
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm]
      field_simp [ne_of_gt hw_norm_pos]
    -- For any z ∈ K', f z < s, so ⟪w, z⟫ < s, so ⟪u, z⟫ < s / ‖w‖
    have hK'_subset : K' ⊆ {z | ⟪u, z⟫ < s / ‖w‖} := by
      intro z hz
      have h_fz_lt_s : f z < s := hf_lt z hz
      rw [hf_eq z] at h_fz_lt_s
      -- ⟪w, z⟫ < s
      rw [hu_def, Set.mem_setOf_eq]
      -- inner (‖w‖⁻¹ • w) z = (‖w‖⁻¹) * inner w z
      rw [inner_smul_left]
      have hpos : 0 < ‖w‖ := hw_norm_pos
      calc
        (‖w‖⁻¹ : ℝ) * ⟪w, z⟫ < (‖w‖⁻¹ : ℝ) * s := by
          exact mul_lt_mul_of_pos_left h_fz_lt_s (by positivity)
        _ = s / ‖w‖ := by ring
    -- By halfspace_measure, μ.real {z | ⟪u, z⟫ < s / ‖w‖} = 1 - Qtail (s / ‖w‖)
    have h_halfspace_meas : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {z | ⟪u, z⟫ < s / ‖w‖} =
        1 - AdversarialBco.BodySpec.Qtail (s / ‖w‖) :=
      AdversarialBco.Poly.halfspace_measure u hu_norm (s / ‖w‖)
    -- Since K' ⊆ that set, μ.real K' ≤ 1 - Qtail (s / ‖w‖)
    have hK'_measure_le : (stdGaussian (EuclideanSpace ℝ (Fin d))).real K' ≤
        1 - AdversarialBco.BodySpec.Qtail (s / ‖w‖) := by
      -- Need measurability of the halfspace
      have h_meas_halfspace : MeasurableSet {z | ⟪u, z⟫ < s / ‖w‖} := by
        have h_cont : Continuous (fun z => ⟪u, z⟫) :=
          continuous_inner.comp (Continuous.prodMk continuous_const continuous_id)
        have h_meas : Measurable (fun z => ⟪u, z⟫) := h_cont.measurable
        exact measurableSet_lt h_meas measurable_const
      have h_finite : (stdGaussian (EuclideanSpace ℝ (Fin d))) {z | ⟪u, z⟫ < s / ‖w‖} ≠ ⊤ := by
        have : IsFiniteMeasure (stdGaussian (EuclideanSpace ℝ (Fin d))) := by infer_instance
        exact measure_ne_top _ _
      -- measureReal_mono for the subset relation
      have h_subset_meas : K' ⊆ {z | ⟪u, z⟫ < s / ‖w‖} := hK'_subset
      have h_le_measure : (stdGaussian (EuclideanSpace ℝ (Fin d))).real K' ≤
          (stdGaussian (EuclideanSpace ℝ (Fin d))).real {z | ⟪u, z⟫ < s / ‖w‖} :=
        measureReal_mono h_subset_meas h_finite
      rw [h_halfspace_meas] at h_le_measure
      exact h_le_measure
    -- Combine with hK'_measure_ge: 1 - Qtail a ≤ μ.real K' ≤ 1 - Qtail (s / ‖w‖)
    -- So Qtail (s / ‖w‖) ≤ Qtail a
    have hQtail_le : AdversarialBco.BodySpec.Qtail (s / ‖w‖) ≤
        AdversarialBco.BodySpec.Qtail a := by
      linarith
    -- Since qtail_strictAnti, we get a ≤ s / ‖w‖
    have ha_le : a ≤ s / ‖w‖ := by
      have h_strictAnti := AdversarialBco.Poly.qtail_strictAnti
      -- h_strictAnti : StrictAnti Qtail
      -- Use the lemma StrictAnti.le_iff_ge
      have h_equiv := (StrictAnti.le_iff_ge h_strictAnti).mp hQtail_le
      -- h_equiv : a ≤ s / ‖w‖
      exact h_equiv
    -- But s < f y = ⟪w, y⟫ = ‖w‖ * ⟪u, y⟫
    have hs_lt_inner : s < ⟪w, y⟫ := by
      rw [hf_eq y] at hs_lt
      exact hs_lt
    -- So s / ‖w‖ < ⟪u, y⟫
    have hs_div_lt_inner : s / ‖w‖ < ⟪u, y⟫ := by
      have hpos : 0 < ‖w‖ := hw_norm_pos
      calc
        s / ‖w‖ < ⟪w, y⟫ / ‖w‖ := div_lt_div_of_pos_right hs_lt_inner hpos
        _ = ⟪u, y⟫ := by
          rw [hu_def]
          simp [inner_smul_left, div_eq_mul_inv, mul_comm]
    -- And ⟪u, y⟫ ≤ ‖u‖ * ‖y‖ = ‖y‖ ≤ a
    have h_inner_le_norm : ⟪u, y⟫ ≤ ‖y‖ := by
      calc
        ⟪u, y⟫ ≤ ‖u‖ * ‖y‖ := real_inner_le_norm u y
        _ = 1 * ‖y‖ := by rw [hu_norm]
        _ = ‖y‖ := by simp
    have h_norm_y_le_a : ‖y‖ ≤ a := hy_norm
    -- So s / ‖w‖ < a, contradicting a ≤ s / ‖w‖
    linarith



theorem AdversarialBco.Poly.propCc_main (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 α : ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hK : AdversarialBco.Poly.IsPosBody K r0 α) (hk : AdversarialBco.Poly.posK K μ A < 1) :
    ∫ g, gauge (AdversarialBco.Poly.posBody K μ A) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      1 / (1 - AdversarialBco.Poly.posK K μ A) := by
  rcases hK with ⟨hK_conv, hK_compact, hr0_pos, hball, hα_nonneg, hnegK⟩
  have hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) := by
    have hball_mem : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r0 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
      Metric.ball_mem_nhds 0 hr0_pos
    exact Filter.mem_of_superset hball_mem hball
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- Convexity of gauge K on the whole space
  have h_gauge_conv : ConvexOn ℝ Set.univ (gauge K) :=
    AdversarialBco.Poly.gauge_convexOn K hK_conv hK0
  -- Lipschitz constant for gauge K
  let r0nn : ℝ≥0 := ⟨r0, hr0_pos.le⟩
  have h_gauge_lip : LipschitzWith r0nn⁻¹ (gauge K) :=
    Convex.lipschitzWith_gauge hK_conv hr0_pos hball
  -- Jensen: gauge K μ ≤ posK K μ A
  have h_gauge_le_k : gauge K μ ≤ AdversarialBco.Poly.posK K μ A := by
    have h := AdversarialBco.Body.ec_S4 (gauge K) h_gauge_conv r0nn⁻¹ h_gauge_lip μ A
    simpa [AdversarialBco.Poly.posK, AdversarialBco.Poly.posF] using h
  have h_gauge_lt_one : gauge K μ < 1 := by
    linarith
  have h_gauge_nonneg : 0 ≤ gauge K μ := gauge_nonneg μ
  -- posF is Lipschitz (composition of Lipschitz gauge with affine map)
  have h_posF_lip : LipschitzWith (r0nn⁻¹ * ‖A‖₊) (AdversarialBco.Poly.posF K μ A) := by
    have hA : LipschitzWith ‖A‖₊ (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
      ContinuousLinearMap.lipschitzWith A
    have h_affine : LipschitzWith ‖A‖₊ (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) := by
      refine LipschitzWith.of_dist_le_mul (fun y y' => ?_)
      calc
        dist (μ + A y) (μ + A y') = ‖(μ + A y) - (μ + A y')‖ := by rw [dist_eq_norm]
        _ = ‖A (y - y')‖ := by simp
        _ ≤ ‖A‖ * ‖y - y'‖ := A.le_opNorm (y - y')
        _ = (↑‖A‖₊ : ℝ) * dist y y' := by simp [dist_eq_norm]
    exact h_gauge_lip.comp h_affine
  -- Integrability of posF
  have h_posF_int : Integrable (AdversarialBco.Poly.posF K μ A) (stdGaussian _) :=
    AdversarialBco.Poly.integrable_of_lipschitz (AdversarialBco.Poly.posF K μ A) (r0nn⁻¹ * ‖A‖₊) h_posF_lip
  -- posBody K μ A is convex and in 𝓝 0, hence gauge is continuous
  have h_mem_interior : μ ∈ interior K := by
    rw [← gauge_lt_one_iff_mem_interior hK_conv hK0]
    exact h_gauge_lt_one
  have h_posBody_conv : Convex ℝ (AdversarialBco.Poly.posBody K μ A) := by
    let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
      { toFun := fun y => μ + A y
        linear := A
        map_vadd' := by
          intro x v
          simp [vadd_eq_add, add_comm, add_left_comm, map_add] }
    have : AdversarialBco.Poly.posBody K μ A = f ⁻¹' K := by
      ext y; simp [AdversarialBco.Poly.posBody, f]
    rw [this]
    exact hK_conv.affine_preimage f
  have h_posBody_nhds : AdversarialBco.Poly.posBody K μ A ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) := by
    have h_interior_nhds : interior K ∈ nhds μ :=
      isOpen_interior.mem_nhds h_mem_interior
    rcases Metric.mem_nhds_iff.mp h_interior_nhds with ⟨ε, hε_pos, h_ball_sub⟩
    have h_preimage_open : IsOpen ((fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) ⁻¹' (Metric.ball μ ε)) :=
      (continuous_const.add A.continuous).isOpen_preimage _ Metric.isOpen_ball
    have h_zero_mem : (0 : EuclideanSpace ℝ (Fin d)) ∈ (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) ⁻¹' (Metric.ball μ ε) := by
      simp [hε_pos]
    have h_preimage_nhds : (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) ⁻¹' (Metric.ball μ ε) ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
      h_preimage_open.mem_nhds h_zero_mem
    have h_sub : (fun (y : EuclideanSpace ℝ (Fin d)) => μ + A y) ⁻¹' (Metric.ball μ ε) ⊆ AdversarialBco.Poly.posBody K μ A := by
      intro y hy
      have hball : μ + A y ∈ Metric.ball μ ε := hy
      have h_int : μ + A y ∈ interior K := h_ball_sub hball
      have hK : μ + A y ∈ K := interior_subset h_int
      simp [AdversarialBco.Poly.posBody, hK]
    exact Filter.mem_of_superset h_preimage_nhds h_sub
  have h_gauge_posBody_cont : Continuous (gauge (AdversarialBco.Poly.posBody K μ A)) :=
    continuous_gauge h_posBody_conv h_posBody_nhds
  have h_meas : AEStronglyMeasurable (fun y => gauge (AdversarialBco.Poly.posBody K μ A) y) (stdGaussian _) :=
    h_gauge_posBody_cont.aestronglyMeasurable
  -- Pointwise bound from gauge_body_le
  have h_pointwise : ∀ y, gauge (AdversarialBco.Poly.posBody K μ A) y ≤ 1 + AdversarialBco.Poly.posF K μ A y / (1 - gauge K μ) := by
    intro y
    exact AdversarialBco.Poly.gauge_body_le K hK_conv hK_closed hK0 μ A h_gauge_lt_one y
  -- Integrability of the bounding function
  have h_denom_pos : 0 < 1 - gauge K μ := by linarith
  have h_int_bound : Integrable (fun y => 1 + AdversarialBco.Poly.posF K μ A y / (1 - gauge K μ)) (stdGaussian _) := by
    have h_one_int : Integrable (fun (_ : EuclideanSpace ℝ (Fin d)) => (1 : ℝ)) (stdGaussian _) :=
      MeasureTheory.integrable_const _
    have h_posF_div_int : Integrable (fun y => AdversarialBco.Poly.posF K μ A y / (1 - gauge K μ)) (stdGaussian _) :=
      h_posF_int.div_const (1 - gauge K μ)
    exact h_one_int.add h_posF_div_int
  -- Integrability of gauge (posBody K μ A) via monotonicity
  have h_gauge_int : Integrable (fun y => gauge (AdversarialBco.Poly.posBody K μ A) y) (stdGaussian _) := by
    have h_bound : ∀ᵐ y ∂(stdGaussian _), ‖gauge (AdversarialBco.Poly.posBody K μ A) y‖ ≤
        1 + AdversarialBco.Poly.posF K μ A y / (1 - gauge K μ) := by
      filter_upwards with y
      have h_nonneg_gauge : 0 ≤ gauge (AdversarialBco.Poly.posBody K μ A) y := gauge_nonneg _
      rw [Real.norm_of_nonneg h_nonneg_gauge]
      exact h_pointwise y
    exact h_int_bound.mono' h_meas h_bound
  -- Apply integral_mono
  have h_integral_bound : ∫ g, gauge (AdversarialBco.Poly.posBody K μ A) g ∂(stdGaussian _) ≤
      ∫ g, (1 + AdversarialBco.Poly.posF K μ A g / (1 - gauge K μ)) ∂(stdGaussian _) :=
    integral_mono h_gauge_int h_int_bound h_pointwise
  -- Compute the RHS integral
  have h_int_rhs : ∫ g, (1 + AdversarialBco.Poly.posF K μ A g / (1 - gauge K μ)) ∂(stdGaussian _) =
      1 + AdversarialBco.Poly.posK K μ A / (1 - gauge K μ) := by
    calc
      ∫ g, (1 + AdversarialBco.Poly.posF K μ A g / (1 - gauge K μ)) ∂(stdGaussian _) =
          (∫ g, (1 : ℝ) ∂(stdGaussian _)) + (∫ g, AdversarialBco.Poly.posF K μ A g / (1 - gauge K μ) ∂(stdGaussian _)) := by
        rw [integral_add (MeasureTheory.integrable_const (1 : ℝ)) (h_posF_int.div_const (1 - gauge K μ))]
      _ = (1 : ℝ) + (∫ g, AdversarialBco.Poly.posF K μ A g / (1 - gauge K μ) ∂(stdGaussian _)) := by
        rw [integral_const (c := (1 : ℝ)) (μ := stdGaussian _)]
        simp
      _ = 1 + (∫ g, AdversarialBco.Poly.posF K μ A g ∂(stdGaussian _)) / (1 - gauge K μ) := by
        rw [MeasureTheory.integral_div (1 - gauge K μ) (AdversarialBco.Poly.posF K μ A)]
      _ = 1 + AdversarialBco.Poly.posK K μ A / (1 - gauge K μ) := rfl
  -- Nonnegativity of posK
  have h_posK_nonneg : 0 ≤ AdversarialBco.Poly.posK K μ A := by
    have h_nonneg : 0 ≤ fun g => gauge K (μ + A g) := fun g => gauge_nonneg _
    have h_int_nonneg : 0 ≤ ∫ g, gauge K (μ + A g) ∂(stdGaussian _) :=
      MeasureTheory.integral_nonneg h_nonneg
    simpa [AdversarialBco.Poly.posK, AdversarialBco.Poly.posF] using h_int_nonneg
  -- Final algebraic inequality: 1 + k/(1-g) ≤ 1/(1-k)
  have h_final : 1 + AdversarialBco.Poly.posK K μ A / (1 - gauge K μ) ≤ 1 / (1 - AdversarialBco.Poly.posK K μ A) := by
    have h1 : 0 < 1 - gauge K μ := by linarith
    have h2 : 0 < 1 - AdversarialBco.Poly.posK K μ A := by linarith
    field_simp [h1.ne.symm, h2.ne.symm]
    nlinarith
  linarith

theorem AdversarialBco.Poly.ibp_lip1 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hFL : LipschitzWith L F) (hFc : ConvexOn ℝ Set.univ F) (v : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪v, g⟫ * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, fderiv ℝ F g v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hIntNorm : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖) μ :=
    (IsGaussian.integrable_id (μ := μ)).norm
  have hIntNormSq : Integrable (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 2) μ := by
    have hMem : MemLp (fun (g : EuclideanSpace ℝ (Fin d)) => g) 2 μ :=
      IsGaussian.memLp_two_id (μ := μ)
    have hAE : AEStronglyMeasurable (fun (g : EuclideanSpace ℝ (Fin d)) => g) μ :=
      (IsGaussian.integrable_id (μ := μ)).aestronglyMeasurable
    have := (MeasureTheory.memLp_two_iff_integrable_sq_norm hAE).mp hMem
    simpa using this
  have hεpos : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 < (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    exact div_pos (by norm_num) hpos
  have hSmooth : ∀ n : ℕ, ∃ (Fn : EuclideanSpace ℝ (Fin d) → ℝ),
    ContDiff ℝ 2 Fn ∧ ConvexOn ℝ Set.univ Fn ∧ LipschitzWith L Fn ∧
    (∃ M : ℝ≥0, LipschitzWith M (fderiv ℝ Fn)) ∧ ∀ x, |Fn x - F x| ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    exact AdversarialBco.Body.smooth_convex F L hFL hFc ((1 : ℝ) / ((n : ℝ) + 1)) (hεpos n)
  choose Fn hFn using hSmooth
  have hLipFn : ∀ n, LipschitzWith L (Fn n) := fun n => (hFn n).2.2.1
  set A := (|F 0| + 1 + (L : ℝ)) with hAdef
  have hStein : ∀ n, ∫ g, ⟪v, g⟫ * Fn n g ∂μ = ∫ g, (fderiv ℝ (Fn n) g) v ∂μ := by
    intro n
    rcases hFn n with ⟨hContDiff, hConv, hLip, ⟨M, hM⟩, hClose⟩
    have hDiff : ∀ g, HasFDerivAt (Fn n) (fderiv ℝ (Fn n) g) g := by
      intro g
      have hContDiffAt : ContDiffAt ℝ 2 (Fn n) g := hContDiff.contDiffAt
      have hDiffAt : DifferentiableAt ℝ (Fn n) g :=
        hContDiffAt.differentiableAt (by norm_num)
      exact hDiffAt.hasFDerivAt
    have hBound : ∀ g, |Fn n g| ≤ A * Real.exp (1 * ‖g‖) := by
      intro g
      have hFbound : |F g| ≤ |F 0| + (L : ℝ) * ‖g‖ := by
        have h := hFL.dist_le_mul 0 g
        have h' : |F 0 - F g| ≤ (L : ℝ) * ‖0 - g‖ := by
          simpa [dist_eq_norm] using h
        calc
          |F g| = |(F g - F 0) + F 0| := by ring
          _ ≤ |F g - F 0| + |F 0| := abs_add_le _ _
          _ = |F 0 - F g| + |F 0| := by rw [abs_sub_comm]
          _ ≤ (L : ℝ) * ‖0 - g‖ + |F 0| := by nlinarith
          _ = (L : ℝ) * ‖g‖ + |F 0| := by simp
          _ = |F 0| + (L : ℝ) * ‖g‖ := add_comm _ _
      have hCloseG := hClose g
      have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        have hpos : 1 ≤ (n : ℝ) + 1 := by
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          linarith
        exact (div_le_one (by linarith)).mpr hpos
      calc
        |Fn n g| ≤ |F g| + |Fn n g - F g| := by
          have h := abs_sub_abs_le_abs_sub (Fn n g) (F g)
          linarith
        _ ≤ (|F 0| + (L : ℝ) * ‖g‖) + ((1 : ℝ) / ((n : ℝ) + 1)) := by nlinarith
        _ ≤ |F 0| + (L : ℝ) * ‖g‖ + 1 := by nlinarith
        _ = |F 0| + 1 + (L : ℝ) * ‖g‖ := by ring
        _ ≤ (|F 0| + 1) * Real.exp ‖g‖ + (L : ℝ) * Real.exp ‖g‖ := by
          have hexp : 1 ≤ Real.exp ‖g‖ := Real.one_le_exp (norm_nonneg _)
          have h1 : |F 0| + 1 ≤ (|F 0| + 1) * Real.exp ‖g‖ := by
            have hpos : 0 ≤ |F 0| + 1 := by positivity
            nlinarith
          have h2 : (L : ℝ) * ‖g‖ ≤ (L : ℝ) * Real.exp ‖g‖ :=
            mul_le_mul_of_nonneg_left (by
              have h := Real.add_one_le_exp ‖g‖
              linarith) (NNReal.coe_nonneg _)
          nlinarith
        _ = (|F 0| + 1 + (L : ℝ)) * Real.exp ‖g‖ := by ring
        _ = A * Real.exp ‖g‖ := rfl
        _ = A * Real.exp (1 * ‖g‖) := by ring
    have hBound' : ∀ g, ‖fderiv ℝ (Fn n) g‖ ≤ A * Real.exp (1 * ‖g‖) := by
      intro g
      have hNorm : ‖fderiv ℝ (Fn n) g‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hLip
      have hA : (L : ℝ) ≤ A := by
        have hF0 : 0 ≤ |F 0| := abs_nonneg _
        nlinarith
      have hExpOne : 1 ≤ Real.exp (1 * ‖g‖) :=
        Real.one_le_exp (by nlinarith [norm_nonneg g])
      nlinarith
    exact AdversarialBco.Body.stein_dir (Fn n) (fderiv ℝ (Fn n)) hDiff A 1 hBound hBound' v
  -- left side via dominated convergence
  have hLeftConv : Tendsto (fun n : ℕ => ∫ g, ⟪v, g⟫ * Fn n g ∂μ) atTop (nhds (∫ g, ⟪v, g⟫ * F g ∂μ)) := by
    set F_n := fun (n : ℕ) (g : EuclideanSpace ℝ (Fin d)) => ⟪v, g⟫ * Fn n g with hF_n
    set f := fun (g : EuclideanSpace ℝ (Fin d)) => ⟪v, g⟫ * F g with hf
    set bound := fun (g : EuclideanSpace ℝ (Fin d)) => ‖v‖ * ‖g‖ * (|F 0| + 1 + (L : ℝ) * ‖g‖) with hbound
    have hF_meas : ∀ n, AEStronglyMeasurable (F_n n) μ := by
      intro n
      have hCont : Continuous (Fn n) := (hFn n).1.continuous
      have hInner : Continuous (fun g : EuclideanSpace ℝ (Fin d) => ⟪v, g⟫) :=
        continuous_inner.comp (Continuous.prodMk continuous_const continuous_id)
      exact (hInner.mul hCont).aestronglyMeasurable
    have hBound_int : Integrable bound μ := by
      dsimp [bound]
      have h1 : Integrable (fun g => (‖v‖ * (|F 0| + 1)) * ‖g‖) μ :=
        hIntNorm.const_mul (‖v‖ * (|F 0| + 1))
      have h2 : Integrable (fun g => (‖v‖ * (L : ℝ)) * (‖g‖ ^ 2)) μ :=
        hIntNormSq.const_mul (‖v‖ * (L : ℝ))
      have h_eq : (fun g : EuclideanSpace ℝ (Fin d) => ‖v‖ * ‖g‖ * (|F 0| + 1 + (L : ℝ) * ‖g‖)) =
                 (fun g => (‖v‖ * (|F 0| + 1)) * ‖g‖ + (‖v‖ * (L : ℝ)) * (‖g‖ ^ 2)) := by
        ext g; ring
      rw [h_eq]
      exact h1.add h2
    have hBound_le : ∀ n, ∀ᵐ g ∂μ, ‖F_n n g‖ ≤ bound g := by
      intro n
      filter_upwards with g
      dsimp [F_n, bound]
      have hInner : |⟪v, g⟫| ≤ ‖v‖ * ‖g‖ := abs_real_inner_le_norm _ _
      have hCloseG : |Fn n g - F g| ≤ (1 : ℝ) / ((n : ℝ) + 1) := (hFn n).2.2.2.2 g
      have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        have hpos : 1 ≤ (n : ℝ) + 1 := by
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          linarith
        exact (div_le_one (by linarith)).mpr hpos
      calc
        ‖⟪v, g⟫ * Fn n g‖ = |⟪v, g⟫| * |Fn n g| := by simp [norm_mul]
        _ ≤ (‖v‖ * ‖g‖) * |Fn n g| := mul_le_mul_of_nonneg_right hInner (abs_nonneg _)
        _ ≤ (‖v‖ * ‖g‖) * (|F g| + |Fn n g - F g|) := by
          have hpos : 0 ≤ ‖v‖ * ‖g‖ := by positivity
          have h_tri : |Fn n g| ≤ |F g| + |Fn n g - F g| := by
            have h := abs_sub_abs_le_abs_sub (Fn n g) (F g)
            linarith
          nlinarith
        _ = (‖v‖ * ‖g‖) * |F g| + (‖v‖ * ‖g‖) * |Fn n g - F g| := by ring
        _ ≤ (‖v‖ * ‖g‖) * (|F 0| + (L : ℝ) * ‖g‖) + (‖v‖ * ‖g‖) * ((1 : ℝ) / ((n : ℝ) + 1)) := by
          have hFbound : |F g| ≤ |F 0| + (L : ℝ) * ‖g‖ := by
            have h := hFL.dist_le_mul 0 g
            have h' : |F 0 - F g| ≤ (L : ℝ) * ‖0 - g‖ := by
              simpa [dist_eq_norm] using h
            calc
              |F g| = |(F g - F 0) + F 0| := by ring
              _ ≤ |F g - F 0| + |F 0| := abs_add_le _ _
              _ = |F 0 - F g| + |F 0| := by rw [abs_sub_comm]
              _ ≤ (L : ℝ) * ‖0 - g‖ + |F 0| := by nlinarith
              _ = (L : ℝ) * ‖g‖ + |F 0| := by simp
              _ = |F 0| + (L : ℝ) * ‖g‖ := add_comm _ _
          have hpos : 0 ≤ ‖v‖ * ‖g‖ := by positivity
          nlinarith
        _ ≤ (‖v‖ * ‖g‖) * (|F 0| + (L : ℝ) * ‖g‖) + (‖v‖ * ‖g‖) * 1 := by
          have hpos : 0 ≤ ‖v‖ * ‖g‖ := by positivity
          nlinarith
        _ = ‖v‖ * ‖g‖ * (|F 0| + 1 + (L : ℝ) * ‖g‖) := by ring
    have hPointwise : ∀ᵐ g ∂μ, Tendsto (fun n : ℕ => F_n n g) atTop (nhds (f g)) := by
      filter_upwards with g
      dsimp [F_n, f]
      have hFnTendsto : Tendsto (fun n : ℕ => Fn n g) atTop (nhds (F g)) := by
        have hClose : Tendsto (fun n : ℕ => |Fn n g - F g|) atTop (nhds 0) := by
          have hεTendsto : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
            have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
            -- h : Tendsto (fun n => 1 / (↑(n+1) : ℝ)) atTop (nhds 0)
            exact h
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) hεTendsto
            (fun n => by positivity) (fun n => (hFn n).2.2.2.2 g)
        rw [Metric.tendsto_nhds] at hClose ⊢
        intro ε hε
        have hClose' := hClose ε hε
        filter_upwards [hClose'] with n hn
        simpa [Real.dist_eq] using hn
      have hInner : Tendsto (fun n : ℕ => ⟪v, g⟫ * Fn n g) atTop (nhds (⟪v, g⟫ * F g)) :=
        Tendsto.const_mul (⟪v, g⟫) hFnTendsto
      simpa [mul_comm] using hInner
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hF_meas hBound_int hBound_le hPointwise
  -- right side via dominated convergence
  have hRightConv : Tendsto (fun n : ℕ => ∫ g, (fderiv ℝ (Fn n) g) v ∂μ) atTop (nhds (∫ g, (fderiv ℝ F g) v ∂μ)) := by
    set F_n := fun (n : ℕ) (g : EuclideanSpace ℝ (Fin d)) => (fderiv ℝ (Fn n) g) v with hF_n
    have hF_meas : ∀ n, AEStronglyMeasurable (F_n n) μ := by
      intro n
      have hContFderiv : Continuous (fderiv ℝ (Fn n)) :=
        (hFn n).1.continuous_fderiv (by norm_num)
      have hEvalCont : Continuous (fun (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) => L v) :=
        ContinuousEvalConst.continuous_eval_const v
      exact (hEvalCont.comp hContFderiv).aestronglyMeasurable
    have hBound_int : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (L : ℝ) * ‖v‖) μ :=
      MeasureTheory.integrable_const _
    have hBound_le : ∀ n, ∀ᵐ g ∂μ, ‖F_n n g‖ ≤ (L : ℝ) * ‖v‖ := by
      intro n
      filter_upwards with g
      dsimp [F_n]
      calc
        ‖(fderiv ℝ (Fn n) g) v‖ ≤ ‖fderiv ℝ (Fn n) g‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm (fderiv ℝ (Fn n) g) v
        _ ≤ (L : ℝ) * ‖v‖ := by
          have hNorm : ‖fderiv ℝ (Fn n) g‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hLipFn n)
          have hpos : 0 ≤ ‖v‖ := norm_nonneg _
          nlinarith
    have hPointwise : ∀ᵐ g ∂μ, Tendsto (fun n : ℕ => F_n n g) atTop (nhds ((fderiv ℝ F g) v)) := by
      have hDiffF : ∀ᵐ g ∂μ, DifferentiableAt ℝ F g :=
        AdversarialBco.Poly.gauss_ae_diff d F L hFL
      have hDiffFn : ∀ n g, DifferentiableAt ℝ (Fn n) g := by
        intro n g
        have hContDiff : ContDiff ℝ 2 (Fn n) := (hFn n).1
        have hContDiffAt : ContDiffAt ℝ 2 (Fn n) g := hContDiff.contDiffAt
        exact hContDiffAt.differentiableAt (by norm_num)
      have hClose : ∀ n y, |Fn n y - F y| ≤ (1 : ℝ) / ((n : ℝ) + 1) := fun n => (hFn n).2.2.2.2
      have hεTendsto : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
        have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        exact h
      filter_upwards [hDiffF] with g hg
      dsimp [F_n]
      exact AdversarialBco.Poly.convex_squeeze F Fn (fun n => (1 : ℝ) / ((n : ℝ) + 1))
        (fun n => (hFn n).2.1) hεTendsto hClose g hg (hDiffFn · g) v
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => (L : ℝ) * ‖v‖) hF_meas hBound_int hBound_le hPointwise
  -- conclude
  have hSeqEq : (fun n : ℕ => ∫ g, ⟪v, g⟫ * Fn n g ∂μ) = (fun n : ℕ => ∫ g, (fderiv ℝ (Fn n) g) v ∂μ) := by
    ext n; exact hStein n
  have hRightConv' : Tendsto (fun n : ℕ => ∫ g, ⟪v, g⟫ * Fn n g ∂μ) atTop (nhds (∫ g, (fderiv ℝ F g) v ∂μ)) := by
    simpa [hSeqEq] using hRightConv
  exact tendsto_nhds_unique hLeftConv hRightConv'

theorem AdversarialBco.Poly.ibp_lip2 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hFL : LipschitzWith L F) (hFc : ConvexOn ℝ Set.univ F) (v w : EuclideanSpace ℝ (Fin d)) :
    ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, ⟪v, g⟫ * fderiv ℝ F g w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  have hIntNorm : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) μ :=
    (IsGaussian.integrable_id (μ := μ)).norm
  have hεpos : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := fun n => by positivity
  have hε1 : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεT : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose Fn hFn using fun n : ℕ => AdversarialBco.Body.smooth_convex F L hFL hFc _ (hεpos n)
  have hLipFn : ∀ n, LipschitzWith L (Fn n) := fun n => (hFn n).2.2.1
  have hClose : ∀ n y, |Fn n y - F y| ≤ (1 : ℝ) / ((n : ℝ) + 1) := fun n => (hFn n).2.2.2.2
  have hDiffFn : ∀ n g, HasFDerivAt (Fn n) (fderiv ℝ (Fn n) g) g := fun n g =>
    ((hFn n).1.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have hFbd : ∀ g, |F g| ≤ |F 0| + (L : ℝ) * ‖g‖ := fun g => by
    have h := hFL.dist_le_mul g 0
    rw [Real.dist_eq, dist_zero_right] at h
    have := abs_sub_abs_le_abs_sub (F g) (F 0)
    linarith
  set A := |F 0| + 1 + (L : ℝ) with hA
  have hA0 : 0 ≤ |F 0| := abs_nonneg _
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hApos : 0 ≤ A := by positivity
  have hgexp : ∀ g : EuclideanSpace ℝ (Fin d), ‖g‖ ≤ Real.exp ‖g‖ := fun g => by
    linarith [Real.add_one_le_exp ‖g‖]
  have hexp1 : ∀ g : EuclideanSpace ℝ (Fin d), 1 ≤ Real.exp ‖g‖ := fun g => Real.one_le_exp (norm_nonneg _)
  have hFnbd : ∀ n g, |Fn n g| ≤ A * Real.exp ‖g‖ := fun n g => by
    have h1 := abs_sub_abs_le_abs_sub (Fn n g) (F g)
    have h2 := hClose n g
    have h3 := hε1 n
    have h4 := hFbd g
    nlinarith [mul_le_mul_of_nonneg_left (hgexp g) hL0,
      mul_le_mul_of_nonneg_left (hexp1 g) (by positivity : (0 : ℝ) ≤ |F 0| + 1)]
  have hStein : ∀ n, ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * Fn n g ∂μ = ∫ g, ⟪v, g⟫ * fderiv ℝ (Fn n) g w ∂μ := by
    intro n
    have hΦ : ∀ g, HasFDerivAt (fun g => ⟪v, g⟫ * Fn n g)
        (⟪v, g⟫ • fderiv ℝ (Fn n) g + Fn n g • innerSL ℝ v) g := fun g =>
      ((innerSL ℝ v).hasFDerivAt).mul (hDiffFn n g)
    have hee : ∀ g : EuclideanSpace ℝ (Fin d), Real.exp ‖g‖ * Real.exp ‖g‖ = Real.exp (2 * ‖g‖) := fun g => by
      rw [← Real.exp_add]
      ring_nf
    have hb : ∀ g, |⟪v, g⟫ * Fn n g| ≤ (2 * ‖v‖ * A) * Real.exp (2 * ‖g‖) := fun g => by
      rw [abs_mul, ← hee]
      have h1 : |⟪v, g⟫| ≤ ‖v‖ * Real.exp ‖g‖ :=
        (abs_real_inner_le_norm v g).trans (mul_le_mul_of_nonneg_left (hgexp g) (norm_nonneg _))
      have h2 := mul_le_mul h1 (hFnbd n g) (abs_nonneg _) (by positivity)
      have h0 : 0 ≤ ‖v‖ * A * (Real.exp ‖g‖ * Real.exp ‖g‖) := by positivity
      nlinarith [h2, h0]
    have hb' : ∀ g, ‖⟪v, g⟫ • fderiv ℝ (Fn n) g + Fn n g • innerSL ℝ v‖ ≤
        (2 * ‖v‖ * A) * Real.exp (2 * ‖g‖) := fun g => by
      have hN : ‖fderiv ℝ (Fn n) g‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ (hLipFn n)
      have h1 : |⟪v, g⟫| ≤ ‖v‖ * Real.exp ‖g‖ :=
        (abs_real_inner_le_norm v g).trans (mul_le_mul_of_nonneg_left (hgexp g) (norm_nonneg _))
      have hLA : (L : ℝ) ≤ A := by linarith
      have hnorm : ‖⟪v, g⟫ • fderiv ℝ (Fn n) g + Fn n g • innerSL ℝ v‖ ≤
          |⟪v, g⟫| * ‖fderiv ℝ (Fn n) g‖ + |Fn n g| * ‖v‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, innerSL_apply_norm]
      rw [← hee]
      have e1 := mul_le_mul h1 hN (norm_nonneg _) (by positivity)
      have e2 := mul_le_mul_of_nonneg_right (hFnbd n g) (norm_nonneg v)
      have e3 : ‖v‖ * Real.exp ‖g‖ * L ≤ ‖v‖ * A * (Real.exp ‖g‖ * Real.exp ‖g‖) := by
        have := mul_le_mul hLA (hexp1 g) zero_le_one hApos
        have h0 : 0 ≤ ‖v‖ * Real.exp ‖g‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
      have e4 : A * Real.exp ‖g‖ * ‖v‖ ≤ ‖v‖ * A * (Real.exp ‖g‖ * Real.exp ‖g‖) := by
        have h0 : 0 ≤ ‖v‖ * A * Real.exp ‖g‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (hexp1 g) h0]
      linarith
    have hS := AdversarialBco.Body.stein_dir (fun g => ⟪v, g⟫ * Fn n g) _ hΦ (2 * ‖v‖ * A) 2 hb hb' w
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul] at hS
    have iFn : Integrable (Fn n) μ := AdversarialBco.Poly.integrable_of_lipschitz _ L (hLipFn n)
    have iM := (AdversarialBco.Poly.integrable_moments (Fn n) L (hLipFn n) v w).2.1
    have iD : Integrable (fun g => ⟪v, g⟫ * fderiv ℝ (Fn n) g w) μ := by
      refine Integrable.mono' (hIntNorm.const_mul (‖v‖ * (L * ‖w‖))) ?_ (Eventually.of_forall fun g => ?_)
      · exact ((continuous_const.inner continuous_id).mul
          (((hFn n).1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable
      · rw [norm_mul, Real.norm_eq_abs]
        have hN : ‖fderiv ℝ (Fn n) g w‖ ≤ L * ‖w‖ :=
          ((fderiv ℝ (Fn n) g).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hLipFn n)) (norm_nonneg _))
        have := mul_le_mul (abs_real_inner_le_norm v g) hN (norm_nonneg _) (by positivity)
        linarith
    have e1 : ∫ g, ⟪w, g⟫ * (⟪v, g⟫ * Fn n g) ∂μ =
        ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * Fn n g ∂μ + ⟪v, w⟫ * ∫ g, Fn n g ∂μ := by
      rw [← integral_const_mul, ← integral_add iM (iFn.const_mul _)]
      congr 1
      funext g
      ring
    have e2 : ∫ g, (⟪v, g⟫ * fderiv ℝ (Fn n) g w + Fn n g * ⟪v, w⟫) ∂μ =
        ∫ g, ⟪v, g⟫ * fderiv ℝ (Fn n) g w ∂μ + ⟪v, w⟫ * ∫ g, Fn n g ∂μ := by
      rw [integral_add iD (iFn.mul_const _), integral_mul_const]
      ring
    linarith [hS, e1, e2]
  have iMF := (AdversarialBco.Poly.integrable_moments F L hFL v w).2.1
  have iH : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) μ := by
    have := (AdversarialBco.Poly.integrable_moments (fun _ => (1 : ℝ)) 0 (LipschitzWith.const 1) v w).2.1
    simpa using this
  have hLeft : Tendsto (fun n : ℕ => ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * Fn n g ∂μ) atTop
      (nhds (∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g ∂μ)) := by
    have hbd : ∀ n : ℕ, ‖∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * Fn n g ∂μ - ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * F g ∂μ‖ ≤
        (1 : ℝ) / ((n : ℝ) + 1) * ∫ g, ‖⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫‖ ∂μ := by
      intro n
      have iMn := (AdversarialBco.Poly.integrable_moments (Fn n) L (hLipFn n) v w).2.1
      rw [← integral_sub iMn iMF, ← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans (integral_mono (iMn.sub iMF).norm (iH.norm.const_mul _) fun g => ?_)
      dsimp only
      rw [← mul_sub, norm_mul, mul_comm (1 / _), Real.norm_eq_abs (Fn n g - F g)]
      exact mul_le_mul_of_nonneg_left (hClose n g) (norm_nonneg _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
    simpa using hεT.mul_const (∫ g, ‖⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫‖ ∂μ)
  have hRight : Tendsto (fun n : ℕ => ∫ g, ⟪v, g⟫ * fderiv ℝ (Fn n) g w ∂μ) atTop
      (nhds (∫ g, ⟪v, g⟫ * fderiv ℝ F g w ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun g => (‖v‖ * (L * ‖w‖)) * ‖g‖) (fun n => ?_)
      (hIntNorm.const_mul _) (fun n => Eventually.of_forall fun g => ?_) ?_
    · exact ((continuous_const.inner continuous_id).mul
        (((hFn n).1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      have hN : ‖fderiv ℝ (Fn n) g w‖ ≤ L * ‖w‖ :=
        ((fderiv ℝ (Fn n) g).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hLipFn n)) (norm_nonneg _))
      have := mul_le_mul (abs_real_inner_le_norm v g) hN (norm_nonneg _) (by positivity)
      linarith
    · filter_upwards [AdversarialBco.Poly.gauss_ae_diff d F L hFL] with g hg
      exact (AdversarialBco.Poly.convex_squeeze F Fn _ (fun n => (hFn n).2.1) hεT hClose g hg
        (fun n => (hDiffFn n g).differentiableAt) w).const_mul _
  have hRight' : Tendsto (fun n : ℕ => ∫ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * Fn n g ∂μ) atTop
      (nhds (∫ g, ⟪v, g⟫ * fderiv ℝ F g w ∂μ)) := by
    simpa only [hStein] using hRight
  exact tendsto_nhds_unique hLeft hRight'


/-! ## Proposition F.2 (a), Lemma F.1 and the assemblies -/

namespace AdversarialBco.Poly

/-- The facts of a body used below: `K ∈ 𝓝 0`, `K` closed, `gauge K` Lipschitz and convex. -/
theorem posBody_facts {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} {r0 α : ℝ} (hK : IsPosBody K r0 α) :
    K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) ∧ IsClosed K ∧
      (∃ L : ℝ≥0, LipschitzWith L (gauge K)) ∧ ConvexOn ℝ Set.univ (gauge K) := by
  obtain ⟨hconv, hcomp, hr0, hball, -, -⟩ := hK
  have hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr0) hball
  exact ⟨hK0, hcomp.isClosed, hconv.lipschitz_gauge hK0, gauge_convexOn K hconv hK0⟩

/-- `F = posF K μ A` is Lipschitz and convex. -/
theorem posF_facts {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} {r0 α : ℝ} (hK : IsPosBody K r0 α)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (∃ L : ℝ≥0, LipschitzWith L (posF K μ A)) ∧ ConvexOn ℝ Set.univ (posF K μ A) := by
  obtain ⟨-, -, ⟨L, hL⟩, hc⟩ := posBody_facts hK
  exact ⟨⟨_, AdversarialBco.lipschitzWith_comp_affine (gauge K) _ hL μ A⟩,
    AdversarialBco.Body.convexOn_comp_cloud (gauge K) hc μ A⟩

/-- `Q` is linear in its first argument under scalars. -/
theorem posQ_smul_left {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (c : ℝ) (v w : EuclideanSpace ℝ (Fin d)) :
    posQ K μ A (c • v) w = c * posQ K μ A v w := by
  unfold posQ
  rw [← integral_const_mul]
  congr 1
  funext g
  rw [real_inner_smul_left, real_inner_smul_left]
  ring

/-- `⟪w, b⟫ = E[⟪w, g⟫ F(g)]`. -/
theorem inner_posB {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} {r0 α : ℝ} (hK : IsPosBody K r0 α)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) :
    ⟪w, posB K μ A⟫ = ∫ g, ⟪w, g⟫ * posF K μ A g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨⟨L, hL⟩, -⟩ := posF_facts hK μ A
  obtain ⟨-, -, hi⟩ := integrable_moments (posF K μ A) L hL w w
  unfold posB
  rw [← integral_inner hi]
  congr 1
  funext g
  rw [real_inner_smul_right, mul_comm]

/-- At a point of differentiability of the gauge, `-(α π(z)) ≤ Dπ(x) z ≤ π(z)`. -/
theorem fderiv_gauge_bounds {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} {r0 α : ℝ} (hK : IsPosBody K r0 α)
    (x z : EuclideanSpace ℝ (Fin d)) (hx : DifferentiableAt ℝ (gauge K) x) :
    -(α * gauge K z) ≤ fderiv ℝ (gauge K) x z ∧ fderiv ℝ (gauge K) x z ≤ gauge K z := by
  obtain ⟨hK0, -, -, -⟩ := posBody_facts hK
  have hconv := hK.1
  refine ⟨?_, fderiv_gauge_le K hconv hK0 x z hx⟩
  have h1 := fderiv_gauge_le K hconv hK0 x (-z) hx
  have h2 := gauge_neg_le K hconv hK0 α hK.2.2.2.2.1 hK.2.2.2.2.2 z
  rw [map_neg] at h1
  linarith

/-- `⟪v, ·⟫` is integrable under the Gaussian. -/
theorem integrable_inner_gauss {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => ⟪v, g⟫) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h := (integrable_moments (fun _ => (1 : ℝ)) 0 (LipschitzWith.const 1) v v).1
  simpa using h

/-- Proposition F.2 (a), before the choice of the radius. -/
theorem propCa_main : PropCa := by
  intro d K r0 α μ A hK hA q t y0 hy0 hQ y hy
  obtain ⟨hK0, hKc, ⟨Lπ, hπL⟩, hπc⟩ := posBody_facts hK
  obtain ⟨⟨LF, hFL⟩, hFc⟩ := posF_facts hK μ A
  have hα : 0 ≤ α := hK.2.2.2.2.1
  have hC0 : 0 ≤ bathC α t := bathC_nonneg α t hα
  have hJ : gauge K μ ≤ posK K μ A := AdversarialBco.Body.ec_S4 (gauge K) hπc Lπ hπL μ A
  have hp0 : 0 ≤ gauge K μ := gauge_nonneg μ
  have hk0 : 0 ≤ posK K μ A := hp0.trans hJ
  have hd : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ (gauge K) (μ + A g) ∧
      ∀ w, fderiv ℝ (posF K μ A) g w = fderiv ℝ (gauge K) (μ + A g) (A w) := by
    filter_upwards [gauss_ae_diff d (posF K μ A) LF hFL] with g hg
    exact diff_of_comp_affine (gauge K) μ A hA g hg
  have hz1 : gauge K (μ + A y) ≤ 1 := gauge_le_one_of_mem hy
  obtain ⟨h1, hh1⟩ : ∃ h1 : EuclideanSpace ℝ (Fin d) → ℝ,
      h1 = fun g => fderiv ℝ (gauge K) (μ + A g) (μ + A y) := ⟨_, rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ h2 : EuclideanSpace ℝ (Fin d) → ℝ,
      h2 = fun g => fderiv ℝ (gauge K) (μ + A g) μ := ⟨_, rfl⟩
  have haff : Measurable fun g : EuclideanSpace ℝ (Fin d) => μ + A g :=
    (continuous_const.add A.continuous).measurable
  have hm1 : AEStronglyMeasurable h1 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hh1]; exact ((measurable_fderiv_apply_const ℝ (gauge K) (μ + A y)).comp haff).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable h2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [hh2]; exact ((measurable_fderiv_apply_const ℝ (gauge K) μ).comp haff).aestronglyMeasurable
  have hb1 : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -(α * 1) ≤ h1 g ∧ h1 g ≤ 1 := by
    filter_upwards [hd] with g hg
    obtain ⟨l, u⟩ := fderiv_gauge_bounds hK (μ + A g) (μ + A y) hg.1
    have hαz : α * gauge K (μ + A y) ≤ α * 1 := mul_le_mul_of_nonneg_left hz1 hα
    rw [hh1]
    exact ⟨by linarith, u.trans hz1⟩
  have hb2 : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -(α * gauge K μ) ≤ h2 g ∧ h2 g ≤ gauge K μ := by
    filter_upwards [hd] with g hg
    rw [hh2]
    exact fderiv_gauge_bounds hK (μ + A g) μ hg.1
  have hmean1 : ∫ g, h1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ⟪y - y0, posB K μ A⟫ := by
    rw [inner_posB hK μ A (y - y0), ibp_lip1 (posF K μ A) LF hFL hFc (y - y0)]
    refine integral_congr_ae ?_
    filter_upwards [hd] with g hg
    rw [hh1, hg.2, map_sub, hy0, sub_neg_eq_add, add_comm]
  have hmean2 : ∫ g, h2 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = ⟪-y0, posB K μ A⟫ := by
    rw [inner_posB hK μ A (-y0), ibp_lip1 (posF K μ A) LF hFL hFc (-y0)]
    refine integral_congr_ae ?_
    filter_upwards [hd] with g hg
    rw [hh2, hg.2, map_neg, hy0, neg_neg]
  have hi : ∀ (v : EuclideanSpace ℝ (Fin d)) (h : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ),
      AEStronglyMeasurable h (stdGaussian (EuclideanSpace ℝ (Fin d))) →
      (∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), -(α * c) ≤ h g ∧ h g ≤ c) → 0 ≤ c →
      Integrable (fun g => ⟪v, g⟫ * h g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro v h c hm hb hc
    refine (integrable_inner_gauss v).mul_bdd (c := α * c + c) hm ?_
    filter_upwards [hb] with g hg
    rw [Real.norm_eq_abs, abs_le]
    have : 0 ≤ α * c := mul_nonneg hα hc
    constructor <;> linarith [hg.1, hg.2]
  have hQy : ∀ v, posQ K μ A v y = ∫ g, ⟪v, g⟫ * h1 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
      ∫ g, ⟪v, g⟫ * h2 g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro v
    unfold posQ
    rw [ibp_lip2 (posF K μ A) LF hFL hFc v y,
      ← integral_sub (hi v h1 1 hm1 hb1 zero_le_one) (hi v h2 (gauge K μ) hm2 hb2 hp0)]
    refine integral_congr_ae ?_
    filter_upwards [hd] with g hg
    rw [hh1, hh2, hg.2, ← mul_sub, ← map_sub, add_sub_cancel_left]
  have key : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 →
      posQ K μ A v y ≤ (1 + posK K μ A) * bathC α t + |t| * ‖posB K μ A‖ * (‖y - y0‖ + ‖y0‖) := by
    intro v hv
    have B1 := bathtub d v hv h1 α 1 t hα zero_le_one hm1 hb1
    have B2 := bathtub d v hv h2 α (gauge K μ) t hα hp0 hm2 hb2
    rw [hmean1] at B1
    rw [hmean2] at B2
    have e1 : |⟪y - y0, posB K μ A⟫| ≤ ‖y - y0‖ * ‖posB K μ A‖ := abs_real_inner_le_norm _ _
    have e2 : |⟪-y0, posB K μ A⟫| ≤ ‖y0‖ * ‖posB K μ A‖ := by
      simpa [norm_neg] using abs_real_inner_le_norm (-y0) (posB K μ A)
    have ht : 0 ≤ |t| := abs_nonneg t
    have f1 := mul_le_mul_of_nonneg_left e1 ht
    have f2 := mul_le_mul_of_nonneg_left e2 ht
    have hpC : gauge K μ * bathC α t ≤ posK K μ A * bathC α t := mul_le_mul_of_nonneg_right hJ hC0
    rw [hQy v]
    have a1 := abs_le.1 B1
    have a2 := abs_le.1 B2
    nlinarith [a1.1, a1.2, a2.1, a2.2]
  by_cases hy' : y = 0
  · subst hy'
    rw [norm_zero, mul_zero]
    have : 0 ≤ |t| * ‖posB K μ A‖ * (‖0 - y0‖ + ‖y0‖) := by positivity
    have : 0 ≤ (1 + posK K μ A) * bathC α t := mul_nonneg (by linarith) hC0
    linarith
  · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy'
    have hv : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hsv : ‖y‖ • (‖y‖⁻¹ • y) = y := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hQyy : posQ K μ A y y = ‖y‖ * posQ K μ A (‖y‖⁻¹ • y) y := by
      rw [← posQ_smul_left, hsv]
    have h1' := hQ y
    have h2' := key _ hv
    rw [hQyy] at h1'
    refine le_of_mul_le_mul_left ?_ hn
    nlinarith [mul_le_mul_of_nonneg_left h2' hn.le]

/-- An invertible `A` is onto. -/
theorem exists_preimage_of_det {d : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : ∃ y, A y = x := by
  have hu : IsUnit (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA)
  obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 x
  exact ⟨y, hy⟩

/-- `k ≥ 0`. -/
theorem posK_nonneg {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : 0 ≤ posK K μ A :=
  integral_nonneg fun _ => gauge_nonneg _

/-- Proposition F.2 (a). -/
theorem propCaBound_main : PropCaBound := by
  intro d K r0 α μ A hK hA q t hq hQ h6 y hy
  obtain ⟨y0, hy0⟩ := exists_preimage_of_det A hA (-μ)
  have hy0K : y0 ∈ posBody K μ A := by
    show μ + A y0 ∈ K
    rw [hy0, add_neg_cancel]
    exact hK.2.2.2.1 (Metric.mem_ball_self hK.2.2.1)
  have hk0 := posK_nonneg K μ A
  have hC0 := bathC_nonneg α t hK.2.2.2.2.1
  have h := radius_of_bound (posBody K μ A) (posBody_compact K r0 α μ A hK hA).1 y0 hy0K q
    ((1 + posK K μ A) * bathC α t) (|t| * ‖posB K μ A‖) hq (mul_nonneg (by linarith) hC0) (by positivity)
    (by linarith [h6]) (fun y hy => propCa_main d K r0 α μ A hK hA q t y0 hy0 hQ y hy) y hy
  calc ‖y‖ ≤ 2 * ((1 + posK K μ A) * bathC α t) / q := h
    _ = 2 * (1 + posK K μ A) * bathC α t / q := by ring

/-- Homogeneity: `k(s μ, s A) = s k(μ, A)` for `s > 0`. -/
theorem posK_smul {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (s : ℝ) (hs : 0 < s) :
    posK K (s • μ) (s • A) = s * posK K μ A := by
  unfold posK posF
  rw [← integral_const_mul]
  congr 1
  funext g
  rw [ContinuousLinearMap.smul_apply, ← smul_add, gauge_smul_of_nonneg hs.le, smul_eq_mul]

/-- `log |det (s A)| = d log s + log |det A|` for `s > 0`. -/
theorem log_det_smul {d : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) (s : ℝ) (hs : 0 < s) :
    LinearMap.det ((s • A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
      Real.log |LinearMap.det ((s • A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| =
        d * Real.log s + Real.log |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  have hdet : LinearMap.det ((s • A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      s ^ d * LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, finrank_euclideanSpace_fin]
  refine ⟨by rw [hdet]; exact mul_ne_zero (pow_ne_zero _ hs.ne') hA, ?_⟩
  rw [hdet, abs_mul, abs_pow, abs_of_pos hs, Real.log_mul (pow_ne_zero _ hs.ne') (abs_ne_zero.2 hA),
    Real.log_pow]

/-- The value forms at any minimiser: `k = κ`, `b = 0`, `Q = (κ/d) I`. -/
theorem lemmaLOfMin_main : LemmaLOfMin := by
  intro d hd K r0 α κ μ A hK hκ hA hmin
  obtain ⟨hK0, -, ⟨Lπ, hπL⟩, -⟩ := posBody_facts hK
  obtain ⟨⟨LF, hFL⟩, hFc⟩ := posF_facts hK μ A
  have hdiff : ∀ᵐ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ (gauge K) (μ + A g) ∧
      ∀ w, fderiv ℝ (posF K μ A) g w = fderiv ℝ (gauge K) (μ + A g) (A w) := by
    filter_upwards [gauss_ae_diff d (posF K μ A) LF hFL] with g hg
    exact diff_of_comp_affine (gauge K) μ A hA g hg
  have hfo := first_order_ae (gauge K) Lπ hπL (κ / d) μ A hA (hdiff.mono fun g hg => hg.1) hmin
  refine ⟨?_, ?_, ?_⟩
  · refine scale_stationary (posK K μ A) κ fun s hs => ?_
    obtain ⟨hdet, hlog⟩ := log_det_smul A hA s hs
    have h : posK K μ A - κ / d * Real.log |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)| ≤
        posK K (s • μ) (s • A) - κ / d * Real.log |LinearMap.det
          ((s • A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)| :=
      hmin (s • μ) (s • A) hdet
    rw [posK_smul K μ A s hs, hlog] at h
    have e : κ / d * (d * Real.log s) = κ * Real.log s := by
      have : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hd)
      field_simp
    nlinarith [e]
  · have hw : ∀ w, ⟪w, posB K μ A⟫ = 0 := fun w => by
      have h := hfo (A w) 0
      simp only [ContinuousLinearMap.zero_apply, map_zero, add_zero, ContinuousLinearMap.coe_zero,
        mul_zero] at h
      rw [inner_posB hK μ A w, ibp_lip1 (posF K μ A) LF hFL hFc w, ← h]
      refine integral_congr_ae ?_
      filter_upwards [hdiff] with g hg
      exact hg.2 w
    exact inner_self_eq_zero.1 (hw _)
  · intro v w
    have h := hfo 0 ((innerSL ℝ v).smulRight w)
    rw [trace_rank_one] at h
    unfold posQ
    rw [ibp_lip2 (posF K μ A) LF hFL hFc v w, ← h]
    refine integral_congr_ae ?_
    filter_upwards [hdiff] with g hg
    simp only [zero_add, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, smul_eq_mul]
    rw [hg.2 w]

/-- Lemma F.1: existence of the minimiser and its value forms. -/
theorem lemmaL_main : LemmaL := by
  intro d hd K r0 α κ hK hκ
  obtain ⟨hK0, -, ⟨Lπ, hπL⟩, -⟩ := posBody_facts hK
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨R, hR⟩ := hK.2.1.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hR'pos : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ Metric.closedBall 0 (max R 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have habs : Absorbent ℝ K := absorbent_nhds_zero hK0
  have hcoer : ∀ x, (max R 1)⁻¹ * ‖x‖ - 0 ≤ gauge K x := fun x => by
    rw [sub_zero, inv_mul_eq_div]
    exact le_gauge_of_subset_closedBall habs hR'pos.le hKR
  obtain ⟨μ, A, hA, hmin⟩ := AdversarialBco.Body.ec_min_exists (gauge K) Lπ hπL (max R 1)⁻¹ 0
    (inv_pos.2 hR'pos) hcoer (κ / d) (div_pos hκ hdpos)
  exact ⟨μ, A, hA, fun μ' A' hA' => hmin μ' A' hA', lemmaLOfMin_main d hd K r0 α κ μ A hK hκ hA hmin⟩

/-- Lemma F.1 (a) to (c) from Proposition F.2 at the value forms of the minimiser. -/
theorem lemmaLRadii_main : LemmaLRadii := by
  intro d hd K r0 α κ μ A hK hA hκ hκ1 hk hb hQ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨y0, hy0⟩ := exists_preimage_of_det A hA (-μ)
  refine ⟨fun t y hy => ?_, fun a ha => propCb_main d K r0 α μ A hK a (hk ▸ ha), ?_⟩
  · have h := propCa_main d K r0 α μ A hK hA (κ / d) t y0 hy0
      (fun v => le_of_eq (by rw [hQ v v, real_inner_self_eq_norm_sq])) y hy
    rw [hk, hb, norm_zero, mul_zero, zero_mul, add_zero] at h
    rw [le_div_iff₀ hκ]
    have h' := mul_le_mul_of_nonneg_left h hdpos.le
    have e : (d : ℝ) * (κ / d * ‖y‖) = ‖y‖ * κ := by field_simp
    rw [e] at h'
    linarith
  · have h := propCc_main d K r0 α μ A hK (by rw [hk]; exact hκ1)
    rwa [hk] at h

/-! ## The statements of `AdversarialBco/Poly/PosGauss.lean` -/

theorem gaussAbsCont : GaussAbsCont := gauss_abs_cont

theorem gaussAeDiff : GaussAeDiff := gauss_ae_diff

theorem ibpLip : IbpLip := fun _ F L hL hc v w => ⟨ibp_lip1 F L hL hc v, ibp_lip2 F L hL hc v w⟩

theorem bathtubBound : BathtubBound := bathtub

theorem bathCNonneg : BathCNonneg := bathC_nonneg

theorem gaussConst : GaussConst := gauss_const

theorem propCa : PropCa := propCa_main

theorem propCaBound : PropCaBound := propCaBound_main

theorem propCb : PropCb := propCb_main

theorem propCc : PropCc := propCc_main

theorem lemmaLOfMin : LemmaLOfMin := lemmaLOfMin_main

theorem lemmaL : LemmaL := lemmaL_main

theorem lemmaLRadii : LemmaLRadii := lemmaLRadii_main

end AdversarialBco.Poly
