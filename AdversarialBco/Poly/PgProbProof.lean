/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProb
public import AdversarialBco.Poly.PgLemmasProof

@[expose] public section

/-!
# The generic probability of Procedure PG: proofs

One theorem per `Prop` of `AdversarialBco/Poly/PgProb.lean`, named after it in lower camel case, and the leaves they
are assembled from.
`sgd_expect_main` (Lemma SGD): one step in expectation through the product law of `sgd_law_step` and Fubini on the law of the
iterate, the pathwise bound `sgd_pathwise`, Jensen through the subgradients. `cheb_avg_main` and its helpers
`tails_*`: Markov's inequality on the squared norm, `E‖∑ Ψ(ω i)‖² = n E‖Ψ‖²` for centred
independent copies (`IndepFun.integral_bilin` with `innerSL`), and `E‖Φ - EΦ‖² = E‖Φ‖² - ‖EΦ‖²`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-! ## Leaves -/

theorem AdversarialBco.Poly.sgd_iter_mem {E G : Type*} [AddCommGroup E] [Module ℝ E] (D : Set E) (proj : E → E)
    (V : E → G → E) (s : ℝ) (x1 : E) (hproj : ∀ y, proj y ∈ D) (hx1 : x1 ∈ D) (ω : ℕ → G) (t : ℕ) :
    AdversarialBco.Poly.sgdIter proj V s x1 ω t ∈ D := by
  induction t with
  | zero =>
    simp [AdversarialBco.Poly.sgdIter, hx1]
  | succ t ih =>
    simp [AdversarialBco.Poly.sgdIter]
    exact hproj _

theorem AdversarialBco.Poly.sgd_avg_mem {E G : Type*} [AddCommGroup E] [Module ℝ E] (D : Set E) (proj : E → E)
    (V : E → G → E) (s : ℝ) (x1 : E) (hD : Convex ℝ D) (hproj : ∀ y, proj y ∈ D) (hx1 : x1 ∈ D) (N : ℕ)
    (hN : 1 ≤ N) (ω : ℕ → G) :
    AdversarialBco.Poly.sgdAvg proj V s x1 N ω ∈ D := by
  have hNpos_nat : N ≠ 0 := (Nat.one_le_iff_ne_zero.mp hN)
  have hNpos' : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos_nat
  have hweight_nonneg : ∀ i ∈ Finset.range N, 0 ≤ (N : ℝ)⁻¹ := by
    intro i hi
    have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    exact inv_nonneg.mpr hN_nonneg
  have hweight_sum : ∑ i ∈ Finset.range N, (N : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_inv_cancel₀ hNpos'
  have hz : ∀ i ∈ Finset.range N, AdversarialBco.Poly.sgdIter proj V s x1 ω i ∈ D := by
    intro i hi
    exact AdversarialBco.Poly.sgd_iter_mem D proj V s x1 hproj hx1 ω i
  have hsum_mem : ∑ i ∈ Finset.range N, ((N : ℝ)⁻¹ • AdversarialBco.Poly.sgdIter proj V s x1 ω i) ∈ D :=
    hD.sum_mem hweight_nonneg hweight_sum hz
  rw [AdversarialBco.Poly.sgdAvg]
  rw [Finset.smul_sum]
  exact hsum_mem

theorem AdversarialBco.Poly.sgd_iter_measurable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace G] (proj : E → E)
    (V : E → G → E) (s : ℝ) (x1 : E) (hproj : Measurable proj) (hV : Measurable (Function.uncurry V)) (t : ℕ) :
    Measurable (fun ω : ℕ → G => AdversarialBco.Poly.sgdIter proj V s x1 ω t) := by
  induction' t with t ih
  · exact measurable_const
  · have h_eq : (fun ω : ℕ → G => AdversarialBco.Poly.sgdIter proj V s x1 ω (t + 1)) =
      (fun ω => proj ((AdversarialBco.Poly.sgdIter proj V s x1 ω t) -
        s • V (AdversarialBco.Poly.sgdIter proj V s x1 ω t) (ω t))) := by
      ext ω; simp [AdversarialBco.Poly.sgdIter]
    rw [h_eq]
    have h_pair : Measurable (fun ω : ℕ → G =>
      (AdversarialBco.Poly.sgdIter proj V s x1 ω t, ω t)) :=
      Measurable.prodMk ih (measurable_pi_apply t)
    have h_V : Measurable (fun ω : ℕ → G => V (AdversarialBco.Poly.sgdIter proj V s x1 ω t) (ω t)) :=
      hV.comp h_pair
    have h_smul : Measurable (fun ω : ℕ → G => s • V (AdversarialBco.Poly.sgdIter proj V s x1 ω t) (ω t)) :=
      Measurable.const_smul h_V s
    have h_sub : Measurable (fun ω : ℕ → G =>
      (AdversarialBco.Poly.sgdIter proj V s x1 ω t) -
        s • V (AdversarialBco.Poly.sgdIter proj V s x1 ω t) (ω t)) :=
      Measurable.sub ih h_smul
    exact hproj.comp h_sub

/-- sgdIter depends only on coordinates < t. -/
theorem AdversarialBco.Poly.sgdIter_depends_on_range {E G : Type*} [AddCommGroup E] [Module ℝ E]
    (proj : E → E) (V : E → G → E) (s : ℝ) (x1 : E) (t : ℕ) (ω ω' : ℕ → G)
    (h : ∀ i < t, ω i = ω' i) :
    AdversarialBco.Poly.sgdIter proj V s x1 ω t = AdversarialBco.Poly.sgdIter proj V s x1 ω' t := by
  induction' t with t ih
  · rfl
  · dsimp [AdversarialBco.Poly.sgdIter]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_le (Nat.le_of_lt hi))), h t (Nat.lt_succ_self t)]

theorem AdversarialBco.Poly.sgd_law_step {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (proj : E → E) (V : E → G → E) (s : ℝ) (x1 : E) (hproj : Measurable proj)
    (hV : Measurable (Function.uncurry V)) (t : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun ω => (AdversarialBco.Poly.sgdIter proj V s x1 ω t, ω t)) =
      ((Measure.infinitePi fun _ : ℕ => ν).map (fun ω => AdversarialBco.Poly.sgdIter proj V s x1 ω t)).prod ν := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  set X := fun ω : ℕ → G => AdversarialBco.Poly.sgdIter proj V s x1 ω t
  set Y := fun ω : ℕ → G => ω t
  have hX_meas : Measurable X := AdversarialBco.Poly.sgd_iter_measurable proj V s x1 hproj hV t
  have hY_meas : Measurable Y := by
    -- Y ω = ω t is the evaluation at t, which is measurable
    simpa [Y] using measurable_pi_apply t
  have h_indep : IndepFun X Y μ := by
    -- The coordinate projections are independent under μ
    have h_indep_coord : iIndepFun (fun (i : ℕ) (ω : ℕ → G) => ω i) μ :=
      iIndepFun_infinitePi (X := fun i ω => ω) (by fun_prop)
    -- Split coordinates into {0,...,t-1} and {t}
    let S : Finset ℕ := Finset.range t
    let T : Finset ℕ := {t}
    have h_disjoint : Disjoint S T := by
      refine Finset.disjoint_singleton_right.mpr ?_
      rw [Finset.mem_range]
      exact fun h => Nat.not_lt.mpr (le_refl t) h
    have h_indep_tuple : IndepFun (S.restrict : (ℕ → G) → (S → G))
        (T.restrict : (ℕ → G) → (T → G)) μ :=
      h_indep_coord.indepFun_finset S T h_disjoint (by fun_prop)
    -- Get a default value for G (needed for extension)
    let default : G := Classical.choice (by
      -- G is nonempty because it has a MeasurableSpace (but we can't guarantee nonempty...)
      -- Actually, we can use the fact that ν is a probability measure on G, so G is nonempty
      have h_ne : Nonempty G := by
        by_contra h_empty
        have : IsEmpty G := not_nonempty_iff.mp h_empty
        have : ν = 0 := by
          apply Measure.eq_zero_of_isEmpty
        -- But ν is a probability measure, so ν univ = 1, contradiction
        have h_univ : ν Set.univ = 1 := by simp
        rw [this] at h_univ
        simp at h_univ
      exact h_ne)
    -- Define F : (S → G) → E that computes sgdIter from the restricted coordinates
    set F : (S → G) → E := fun ω_S =>
      AdversarialBco.Poly.sgdIter proj V s x1
        (fun i => if h : i ∈ S then ω_S ⟨i, h⟩ else default) t
    with hF_def
    have hF_meas : Measurable F := by
      -- F is measurable as a composition of measurable functions
      -- First, the function that extends ω_S to ℕ is measurable
      have h_ext_meas : Measurable (fun (ω_S : S → G) (i : ℕ) => if h : i ∈ S then ω_S ⟨i, h⟩ else default) := by
        refine Measurable.of_eval (fun i => ?_)
        by_cases hi : i ∈ S
        · -- When i ∈ S, this is the projection
          have : (fun (ω_S : S → G) => if h : i ∈ S then ω_S ⟨i, h⟩ else default) =
                 (fun ω_S => ω_S ⟨i, hi⟩) := by
            ext ω_S; simp [hi]
          rw [this]
          exact measurable_pi_apply _
        · -- When i ∉ S, this is constant default
          have : (fun (ω_S : S → G) => if h : i ∈ S then ω_S ⟨i, h⟩ else default) = fun _ => default := by
            ext ω_S; simp [hi]
          rw [this]
          exact measurable_const
      -- F = X ∘ (extension function)
      have hF_eq : F = X ∘ (fun (ω_S : S → G) => fun i => if h : i ∈ S then ω_S ⟨i, h⟩ else default) := by
        ext ω_S
        simp [F, X]
      rw [hF_eq]
      exact hX_meas.comp h_ext_meas
    -- X factors through S.restrict via F
    have hX_factor : X = F ∘ (S.restrict : (ℕ → G) → (S → G)) := by
      ext ω
      dsimp [X, F, S]
      apply AdversarialBco.Poly.sgdIter_depends_on_range proj V s x1 t ω (fun i => if h : i ∈ Finset.range t then ω i else default)
      intro i hi
      have hi_mem : i ∈ Finset.range t := Finset.mem_range.mpr hi
      simp [hi_mem]
    -- Y factors through T.restrict
    have hY_factor : Y = (fun (ω_T : T → G) => ω_T ⟨t, by simp [T]⟩) ∘ (T.restrict : (ℕ → G) → (T → G)) := by
      ext ω
      simp [Y, T]
    have hY_proj_meas : Measurable (fun (ω_T : T → G) => ω_T ⟨t, by simp [T]⟩) :=
      measurable_pi_apply _
    rw [hX_factor, hY_factor]
    exact IndepFun.comp h_indep_tuple hF_meas hY_proj_meas
  have h_map_Y : μ.map Y = ν := by
    simp [Y, μ, MeasureTheory.Measure.infinitePi_map_eval]
  have hX_aemeasurable : AEMeasurable X μ :=
    hX_meas.aemeasurable
  have hY_aemeasurable : AEMeasurable Y μ :=
    hY_meas.aemeasurable
  -- Use the independence to get the product equality
  have h_eq : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
    IndepFun.map_prod_eq_prod_map_map hX_aemeasurable hY_aemeasurable h_indep
  -- Now substitute μ.map Y = ν
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) := h_eq
    _ = (μ.map X).prod ν := by rw [h_map_Y]

theorem AdversarialBco.Poly.subgrad_jensen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (D : Set E)
    (hD : Convex ℝ D) (h : E → ℝ) (γ : E → E) (hγ : ∀ x ∈ D, ∀ y ∈ D, h x + ⟪γ x, y - x⟫ ≤ h y) (N : ℕ)
    (hN : 1 ≤ N) (x : ℕ → E) (hx : ∀ t, x t ∈ D) :
    h ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) ≤ (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, h (x t) := by
  let z := (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t
  have hNpos : 0 < (N : ℝ) := by
    have hN' : 0 < (N : ℕ) := by omega
    exact_mod_cast hN'
  have hzD : z ∈ D := by
    have hsum : (∑ t ∈ Finset.range N, ((N : ℝ)⁻¹ : ℝ)) = 1 := by
      simp [Finset.card_range, hNpos.ne']
    have h_nonneg : ∀ i ∈ Finset.range N, 0 ≤ (N : ℝ)⁻¹ := by
      intro i hi; positivity
    have h_mem : ∀ i ∈ Finset.range N, x i ∈ D := by
      intro i hi; exact hx i
    have h := hD.sum_mem h_nonneg hsum h_mem
    simpa [z, Finset.smul_sum] using h
  have hineq : ∀ t, h z + ⟪γ z, x t - z⟫ ≤ h (x t) := by
    intro t
    exact hγ z hzD (x t) (hx t)
  have hsum_ineq : (∑ t ∈ Finset.range N, (h z + ⟪γ z, x t - z⟫)) ≤ (∑ t ∈ Finset.range N, h (x t)) :=
    Finset.sum_le_sum (fun t ht => hineq t)
  have hsum_eq : (N : ℝ) • z = (∑ t ∈ Finset.range N, x t) := by
    dsimp [z]
    have h_mul : (N : ℝ) * (N : ℝ)⁻¹ = 1 := by field_simp [hNpos.ne']
    rw [smul_smul, h_mul, one_smul]
  have hsum_inner : ⟪γ z, ∑ t ∈ Finset.range N, (x t - z)⟫ = 0 := by
    have hsumzero : (∑ t ∈ Finset.range N, (x t - z)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hsumz : (∑ t ∈ Finset.range N, z) = (N : ℝ) • z := by
        rw [Finset.sum_const]
        simp [Finset.card_range]
        norm_cast
      rw [hsumz, ← hsum_eq, sub_self]
    rw [hsumzero, inner_zero_right]
  have hcalc : (∑ t ∈ Finset.range N, (h z + ⟪γ z, x t - z⟫)) = (N : ℝ) * h z := by
    calc
      (∑ t ∈ Finset.range N, (h z + ⟪γ z, x t - z⟫)) =
          (∑ t ∈ Finset.range N, h z) + (∑ t ∈ Finset.range N, ⟪γ z, x t - z⟫) := by
        rw [Finset.sum_add_distrib]
      _ = ((Finset.range N).card : ℝ) * h z + (∑ t ∈ Finset.range N, ⟪γ z, x t - z⟫) := by simp
      _ = (N : ℝ) * h z + (∑ t ∈ Finset.range N, ⟪γ z, x t - z⟫) := by simp [Finset.card_range]
      _ = (N : ℝ) * h z + ⟪γ z, ∑ t ∈ Finset.range N, (x t - z)⟫ := by rw [inner_sum]
      _ = (N : ℝ) * h z + 0 := by rw [hsum_inner]
      _ = (N : ℝ) * h z := by simp
  rw [hcalc] at hsum_ineq
  have hpos : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hfinal : h z ≤ (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N, h (x t)) := by
    have h_mul : (N : ℝ)⁻¹ * ((N : ℝ) * h z) ≤ (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N, h (x t)) :=
      mul_le_mul_of_nonneg_left hsum_ineq hpos
    have h_simp : (N : ℝ)⁻¹ * ((N : ℝ) * h z) = h z := by
      field_simp [hNpos.ne']
    rw [h_simp] at h_mul
    exact h_mul
  dsimp [z] at hfinal
  exact hfinal

theorem AdversarialBco.Poly.sgd_expect_main (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (G : Type*) [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (D : Set E) (proj : E → E) (h : E → ℝ) (γ : E → E) (V : E → G → E) (xs x1 : E)
    (Δ s G2 β : ℝ) (N : ℕ) (hDc : IsCompact D) (hDv : Convex ℝ D) (hh : ContinuousOn h D) (hpc : Continuous proj)
    (hpD : ∀ y, proj y ∈ D) (hpn : ∀ y, ∀ z ∈ D, ‖proj y - z‖ ≤ ‖y - z‖) (hV : Measurable (Function.uncurry V))
    (hx1 : x1 ∈ D) (hxs : xs ∈ D) (hmin : ∀ y ∈ D, h xs ≤ h y) (hΔ : ∀ y ∈ D, ∀ z ∈ D, ‖y - z‖ ≤ Δ)
    (hγ : ∀ x ∈ D, ∀ y ∈ D, h x + ⟪γ x, y - x⟫ ≤ h y)
    (hVm : ∀ x ∈ D, Integrable (V x) ν ∧ Integrable (fun g => ‖V x g‖ ^ 2) ν ∧ ‖∫ g, V x g ∂ν - γ x‖ ≤ β ∧
      ∫ g, ‖V x g‖ ^ 2 ∂ν ≤ G2)
    (hs : 0 < s) (hN : 1 ≤ N) :
    ∫ ω, h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      h xs + Δ ^ 2 / (2 * s * N) + s * G2 / 2 + β * Δ := by
  set P := Measure.infinitePi (fun _ : ℕ => ν) with hP
  have hx0 : ‖x1 - xs‖ ≤ Δ := hΔ x1 hx1 xs hxs
  set x := fun (ω : ℕ → G) (t : ℕ) => AdversarialBco.Poly.sgdIter proj V s x1 ω t with hx_def
  set v := fun (ω : ℕ → G) (t : ℕ) => V (x ω t) (ω t) with hv_def
  have hx_succ : ∀ ω t, x ω (t + 1) = proj (x ω t - s • v ω t) := by
    intro ω t; dsimp [x, v, AdversarialBco.Poly.sgdIter]
  have hx_mem : ∀ ω t, x ω t ∈ D := by
    intro ω t; exact AdversarialBco.Poly.sgd_iter_mem D proj V s x1 hpD hx1 ω t
  have hproj_meas : Measurable proj := hpc.measurable
  have hx_meas : ∀ t, Measurable (fun ω => x ω t) := by
    intro t; exact AdversarialBco.Poly.sgd_iter_measurable proj V s x1 hproj_meas hV t
  have hv_meas : ∀ t, Measurable (fun ω => v ω t) := by
    intro t
    dsimp [v]
    have h_pair : Measurable (fun ω : ℕ → G => (x ω t, ω t)) :=
      Measurable.prodMk (hx_meas t) (measurable_pi_apply t)
    exact hV.comp h_pair
  have hD_meas : MeasurableSet D := hDc.measurableSet
  have hh_restrict : Continuous (D.domRestrict h) := hh.restrict
  have hh_meas : Measurable (D.domRestrict h) := hh_restrict.measurable
  have hx_meas_subtype : ∀ t, Measurable (fun ω : ℕ → G => (⟨x ω t, hx_mem ω t⟩ : D)) := by
    intro t; apply Measurable.subtype_mk (hx_meas t)
  have hh_comp_meas : ∀ t, Measurable (fun ω : ℕ → G => h (x ω t)) := by
    intro t
    have eq : (fun ω : ℕ → G => h (x ω t)) = (D.domRestrict h) ∘ (fun ω : ℕ → G => (⟨x ω t, hx_mem ω t⟩ : D)) := by
      ext ω; rfl
    rw [eq]
    exact Measurable.comp hh_meas (hx_meas_subtype t)
  -- h is bounded on D
  obtain ⟨M, hM⟩ := hDc.exists_bound_of_continuousOn hh
  have hh_bound : ∀ y, y ∈ D → |h y| ≤ M := by
    intro y hy
    exact hM y hy
  -- integrability of h ∘ x_t
  have hhx_int : ∀ t, Integrable (fun ω : ℕ → G => h (x ω t)) P := by
    intro t
    have h_bound : ∀ ω, |h (x ω t)| ≤ M := fun ω => hh_bound (x ω t) (hx_mem ω t)
    have h_meas : AEStronglyMeasurable (fun ω : ℕ → G => h (x ω t)) P :=
      (hh_comp_meas t).aestronglyMeasurable
    have h_int_const : Integrable (fun _ : ℕ → G => (M : ℝ)) P := by
      have : IsFiniteMeasure P := by
        rw [hP]
        infer_instance
      exact integrable_const M
    refine Integrable.mono' h_int_const h_meas ?_
    -- need: ∀ᵐ ω ∂P, ‖h (x ω t)‖ ≤ (fun _ => M) ω
    have h_all : ∀ ω, ‖h (x ω t)‖ ≤ (fun _ : ℕ → G => (M : ℝ)) ω := by
      intro ω
      simpa [Real.norm_eq_abs] using h_bound ω
    exact ae_of_all P h_all
  -- integrability of ‖v_t‖² using lintegral approach
  have h_norm_sq_int : ∀ t, Integrable (fun ω : ℕ → G => ‖v ω t‖ ^ 2) P := by
    intro t
    dsimp [v]
    set g := fun ω : ℕ → G => ‖V (x ω t) (ω t)‖ ^ 2 with hg_def
    have hg_nonneg : 0 ≤ g := by
      intro ω; dsimp [g]; positivity
    have hg_meas : AEStronglyMeasurable g P := by
      dsimp [g]
      have hV_meas : Measurable (fun (z : E × G) => V z.1 z.2) := by
        have : (Function.uncurry V) = (fun (z : E × G) => V z.1 z.2) := by
          ext ⟨x, g⟩; rfl
        simpa [this] using hV
      have h_norm_sq_cont : Continuous (fun (x : E) => ‖x‖ ^ 2) := by
        continuity
      have h_comp2 : Measurable (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) := by
        have eq : (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) = (fun (x : E) => ‖x‖ ^ 2) ∘ (fun (z : E × G) => V z.1 z.2) := by
          ext z; rfl
        rw [eq]
        exact h_norm_sq_cont.measurable.comp hV_meas
      have h_pair_meas : Measurable (fun ω : ℕ → G => (x ω t, ω t)) :=
        Measurable.prodMk (hx_meas t) (measurable_pi_apply t)
      have h_comp3 : Measurable (fun ω : ℕ → G => ‖V (x ω t) (ω t)‖ ^ 2) :=
        h_comp2.comp h_pair_meas
      exact h_comp3.aestronglyMeasurable
    -- Compute the lintegral of g
    have h_lintegral_lt_top : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P < ⊤ := by
      have h_ennreal_meas : Measurable (fun (z : E × G) => ENNReal.ofReal (‖V z.1 z.2‖ ^ 2)) := by
        have hV_meas : Measurable (fun (z : E × G) => V z.1 z.2) := by
          have : (Function.uncurry V) = (fun (z : E × G) => V z.1 z.2) := by
            ext ⟨x, g⟩; rfl
          simpa [this] using hV
        have h_cont : Continuous (fun (x : E) => ‖x‖ ^ 2) := by continuity
        have h_comp' : Measurable (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) := by
          have eq : (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) = (fun (x : E) => ‖x‖ ^ 2) ∘ (fun (z : E × G) => V z.1 z.2) := by
            ext z; rfl
          rw [eq]
          exact h_cont.measurable.comp hV_meas
        exact ENNReal.continuous_ofReal.measurable.comp h_comp'
      have h_pair_meas : Measurable (fun ω : ℕ → G => (x ω t, ω t)) :=
        Measurable.prodMk (hx_meas t) (measurable_pi_apply t)
      have h_law := AdversarialBco.Poly.sgd_law_step ν proj V s x1 hproj_meas hV t
      calc
        ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ∫⁻ ω, ENNReal.ofReal (‖V (x ω t) (ω t)‖ ^ 2) ∂P := rfl
        _ = ∫⁻ (z : E × G), ENNReal.ofReal (‖V z.1 z.2‖ ^ 2) ∂(Measure.map (fun ω : ℕ → G => (x ω t, ω t)) P) := by
          rw [lintegral_map h_ennreal_meas h_pair_meas]
        _ = ∫⁻ (z : E × G), ENNReal.ofReal (‖V z.1 z.2‖ ^ 2) ∂((Measure.map (fun ω : ℕ → G => x ω t) P).prod ν) := by
          rw [h_law]
        _ = ∫⁻ x, ∫⁻ g', ENNReal.ofReal (‖V x g'‖ ^ 2) ∂ν ∂(Measure.map (fun ω : ℕ → G => x ω t) P) := by
          rw [← lintegral_prod _ h_ennreal_meas.aemeasurable]
        _ ≤ ∫⁻ x, ENNReal.ofReal G2 ∂(Measure.map (fun ω : ℕ → G => x ω t) P) := by
          have h_support : ∀ᵐ x ∂(Measure.map (fun ω : ℕ → G => x ω t) P), x ∈ D := by
            have h_empty : (fun ω : ℕ → G => x ω t) ⁻¹' Dᶜ = ∅ := by
              ext ω; simp [hx_mem ω t]
            have h_measure_zero : (Measure.map (fun ω : ℕ → G => x ω t) P) Dᶜ = 0 := by
              rw [Measure.map_apply (hx_meas t) hD_meas.compl, h_empty]
              simp
            rw [ae_iff]
            have : {a | a ∉ D} = Dᶜ := by ext; simp
            rw [this, h_measure_zero]
          refine lintegral_mono_ae ?_
          filter_upwards [h_support] with x hx
          rcases hVm x hx with ⟨_, _, _, h_int_norm_sq⟩
          have h_nonneg_ae : 0 ≤ᵐ[ν] fun g' => ‖V x g'‖ ^ 2 := by
            refine ae_of_all _ (fun g' => ?_)
            positivity
          have h_eq : ∫⁻ g', ENNReal.ofReal (‖V x g'‖ ^ 2) ∂ν = ENNReal.ofReal (∫ g', ‖V x g'‖ ^ 2 ∂ν) := by
            rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hVm x hx).2.1 h_nonneg_ae]
          rw [h_eq]
          exact ENNReal.ofReal_le_ofReal h_int_norm_sq
        _ = ENNReal.ofReal G2 := by simp
        _ < ⊤ := by simp
    -- Now use the equivalence between finite lintegral and integrability
    have h_int : Integrable g P :=
      ((lintegral_ofReal_ne_top_iff_integrable hg_meas (ae_of_all P hg_nonneg)).mp h_lintegral_lt_top.ne)
    simpa [g] using h_int
  -- Now the main proof
  -- Pathwise inequality for each ω
  have h_pathwise : ∀ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ≤
      Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 := by
    intro ω
    apply AdversarialBco.Poly.sgd_pathwise D proj hpn xs hxs s Δ hs (x ω) (v ω) (hx_succ ω) hx0 N
  -- Integrability of ⟪v_t, x_t - xs⟫
  have h_inner_int : ∀ t, Integrable (fun ω : ℕ → G => ⟪v ω t, x ω t - xs⟫) P := by
    intro t
    have h_bound : ∀ ω, |⟪v ω t, x ω t - xs⟫| ≤ (1 + ‖v ω t‖ ^ 2) * Δ := by
      intro ω
      have h_norm_bound : ‖x ω t - xs‖ ≤ Δ := by
        exact hΔ (x ω t) (hx_mem ω t) xs hxs
      have h_cauchy : |⟪v ω t, x ω t - xs⟫| ≤ ‖v ω t‖ * ‖x ω t - xs‖ :=
        abs_real_inner_le_norm (v ω t) (x ω t - xs)
      have h_ineq : ‖v ω t‖ ≤ 1 + ‖v ω t‖ ^ 2 := by
        have : (‖v ω t‖ - 1/2) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith
      have hΔ_nonneg : 0 ≤ Δ := by
        have h_nonneg_norm : 0 ≤ ‖x1 - xs‖ := norm_nonneg _
        have h_bound := hΔ x1 hx1 xs hxs
        linarith
      have h_mul1 : ‖v ω t‖ * ‖x ω t - xs‖ ≤ ‖v ω t‖ * Δ :=
        mul_le_mul_of_nonneg_left h_norm_bound (norm_nonneg _)
      calc
        |⟪v ω t, x ω t - xs⟫| ≤ ‖v ω t‖ * ‖x ω t - xs‖ := h_cauchy
        _ ≤ ‖v ω t‖ * Δ := h_mul1
        _ ≤ (1 + ‖v ω t‖ ^ 2) * Δ := mul_le_mul_of_nonneg_right h_ineq hΔ_nonneg
    -- Now use Integrable.mono' with the bound
    have h_meas : AEStronglyMeasurable (fun ω : ℕ → G => ⟪v ω t, x ω t - xs⟫) P := by
      -- inner product of measurable functions is measurable
      have h_v_meas : AEStronglyMeasurable (fun ω => v ω t) P := (hv_meas t).aestronglyMeasurable
      have h_x_meas : AEStronglyMeasurable (fun ω => x ω t - xs) P :=
        ((hx_meas t).aestronglyMeasurable.sub aestronglyMeasurable_const)
      -- AEStronglyMeasurable.inner
      exact AEStronglyMeasurable.inner h_v_meas h_x_meas
    have h_bound_ae : ∀ᵐ ω ∂P, ‖⟪v ω t, x ω t - xs⟫‖ ≤ (fun _ => (1 + ‖v ω t‖ ^ 2) * Δ) ω := by
      refine ae_of_all _ (fun ω => ?_)
      simpa [Real.norm_eq_abs] using h_bound ω
    have h_int_bound : Integrable (fun ω : ℕ → G => (1 + ‖v ω t‖ ^ 2) * Δ) P := by
      have h_int_one : Integrable (fun _ : ℕ → G => (1 : ℝ)) P := by
        have : IsFiniteMeasure P := by rw [hP]; infer_instance
        exact integrable_const 1
      have h_int_norm_sq : Integrable (fun ω : ℕ → G => ‖v ω t‖ ^ 2) P := h_norm_sq_int t
      have h_int_sum : Integrable (fun ω : ℕ → G => (1 : ℝ) + ‖v ω t‖ ^ 2) P :=
        Integrable.add h_int_one h_int_norm_sq
      simpa [mul_comm] using Integrable.const_mul h_int_sum Δ
    refine Integrable.mono' h_int_bound h_meas h_bound_ae
  -- Now integrate the pathwise inequality
  have h_pathwise_int : (∫ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ∂P) ≤
      Δ ^ 2 / (2 * s) + s / 2 * (∫ ω, ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) := by
    have h_left_int : Integrable (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫) P :=
      integrable_finsetSum _ (fun t ht => h_inner_int t)
    have h_sum_int : Integrable (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
      integrable_finsetSum _ (fun t ht => h_norm_sq_int t)
    have h_right_int : Integrable (fun ω : ℕ → G => Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P := by
      have h_const : Integrable (fun _ : ℕ → G => Δ ^ 2 / (2 * s)) P := by
        have : IsFiniteMeasure P := by rw [hP]; infer_instance
        exact integrable_const _
      have h_scaled : Integrable (fun ω : ℕ → G => s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
        Integrable.const_mul h_sum_int (s / 2)
      exact Integrable.add h_const h_scaled
    have h_int_mono : (∫ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ∂P) ≤
        (∫ ω, Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) :=
      integral_mono h_left_int h_right_int (h_pathwise ·)
    -- Now pull out the constant from the right integral
    have h_right_eq : (∫ ω, Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) =
        Δ ^ 2 / (2 * s) + s / 2 * (∫ ω, ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) := by
      have h_int1 : Integrable (fun _ : ℕ → G => Δ ^ 2 / (2 * s)) P := by
        have : IsFiniteMeasure P := by rw [hP]; infer_instance
        exact integrable_const _
      have h_int2 : Integrable (fun ω : ℕ → G => s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
        Integrable.const_mul h_sum_int (s / 2)
      rw [integral_add h_int1 h_int2, integral_const]
      rw [integral_const_mul (s / 2) (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2)]
      have h_mass : P.real Set.univ = 1 := by
        have : IsProbabilityMeasure P := by rw [hP]; infer_instance
        simp
      rw [h_mass]
      ring
    linarith
  -- Left side: integral of sum = sum of integrals
  have h_left_sum : (∫ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ∂P) =
      ∑ t ∈ Finset.range N, (∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P) := by
    rw [integral_finsetSum]
    intro t ht
    exact h_inner_int t
  -- Right side: integral of sum = sum of integrals
  have h_right_sum : (∫ ω, ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) =
      ∑ t ∈ Finset.range N, (∫ ω, ‖v ω t‖ ^ 2 ∂P) := by
    rw [integral_finsetSum]
    intro t ht
    exact h_norm_sq_int t
  rw [h_left_sum, h_right_sum] at h_pathwise_int
  -- Now combine h_pathwise_int with bounds from hVm
  -- First, get the bound ∫ ‖v_t‖² ≤ G2 from the lintegral bound we already proved
  have h_norm_sq_bound : ∀ t, (∫ ω, ‖v ω t‖ ^ 2 ∂P) ≤ G2 := by
    intro t
    have h_lintegral_bound : ∫⁻ ω, ENNReal.ofReal (‖v ω t‖ ^ 2) ∂P ≤ ENNReal.ofReal G2 := by
      -- Reuse the calculation from h_norm_sq_int (the lintegral part)
      -- We already have all the ingredients
      set g := fun ω : ℕ → G => ‖v ω t‖ ^ 2 with hg_def
      have hg_nonneg : 0 ≤ g := by intro ω; dsimp [g]; positivity
      have h_ennreal_meas : Measurable (fun (z : E × G) => ENNReal.ofReal (‖V z.1 z.2‖ ^ 2)) := by
        have hV_meas : Measurable (fun (z : E × G) => V z.1 z.2) := by
          have : (Function.uncurry V) = (fun (z : E × G) => V z.1 z.2) := by ext ⟨x, g⟩; rfl
          simpa [this] using hV
        have h_cont : Continuous (fun (x : E) => ‖x‖ ^ 2) := by continuity
        have h_comp' : Measurable (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) := by
          have eq : (fun (z : E × G) => ‖V z.1 z.2‖ ^ 2) = (fun (x : E) => ‖x‖ ^ 2) ∘ (fun (z : E × G) => V z.1 z.2) := by
            ext z; rfl
          rw [eq]
          exact h_cont.measurable.comp hV_meas
        exact ENNReal.continuous_ofReal.measurable.comp h_comp'
      have h_pair_meas : Measurable (fun ω : ℕ → G => (x ω t, ω t)) :=
        Measurable.prodMk (hx_meas t) (measurable_pi_apply t)
      have h_law := AdversarialBco.Poly.sgd_law_step ν proj V s x1 hproj_meas hV t
      calc
        ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ∫⁻ ω, ENNReal.ofReal (‖V (x ω t) (ω t)‖ ^ 2) ∂P := rfl
        _ = ∫⁻ (z : E × G), ENNReal.ofReal (‖V z.1 z.2‖ ^ 2) ∂(Measure.map (fun ω : ℕ → G => (x ω t, ω t)) P) := by
          rw [lintegral_map h_ennreal_meas h_pair_meas]
        _ = ∫⁻ (z : E × G), ENNReal.ofReal (‖V z.1 z.2‖ ^ 2) ∂((Measure.map (fun ω : ℕ → G => x ω t) P).prod ν) := by rw [h_law]
        _ = ∫⁻ x', ∫⁻ g', ENNReal.ofReal (‖V x' g'‖ ^ 2) ∂ν ∂(Measure.map (fun ω : ℕ → G => x ω t) P) := by
          rw [lintegral_prod _ h_ennreal_meas.aemeasurable]
        _ ≤ ∫⁻ x', ENNReal.ofReal G2 ∂(Measure.map (fun ω : ℕ → G => x ω t) P) := by
          have h_support : ∀ᵐ x' ∂(Measure.map (fun ω : ℕ → G => x ω t) P), x' ∈ D := by
            have h_empty : (fun ω : ℕ → G => x ω t) ⁻¹' Dᶜ = ∅ := by ext ω; simp [hx_mem ω t]
            have h_measure_zero : (Measure.map (fun ω : ℕ → G => x ω t) P) Dᶜ = 0 := by
              rw [Measure.map_apply (hx_meas t) hD_meas.compl, h_empty]; simp
            rw [ae_iff]
            have : {a | a ∉ D} = Dᶜ := by ext; simp
            rw [this, h_measure_zero]
          refine lintegral_mono_ae ?_
          filter_upwards [h_support] with x' hx'
          rcases hVm x' hx' with ⟨_, _, _, h_int_norm_sq⟩
          have h_nonneg_ae : 0 ≤ᵐ[ν] fun g' => ‖V x' g'‖ ^ 2 := by
            refine ae_of_all _ (fun g' => ?_); positivity
          have h_eq' : ∫⁻ g', ENNReal.ofReal (‖V x' g'‖ ^ 2) ∂ν = ENNReal.ofReal (∫ g', ‖V x' g'‖ ^ 2 ∂ν) := by
            rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hVm x' hx').2.1 h_nonneg_ae]
          rw [h_eq']
          exact ENNReal.ofReal_le_ofReal h_int_norm_sq
        _ = ENNReal.ofReal G2 := by simp
    have h_int : Integrable (fun ω : ℕ → G => ‖v ω t‖ ^ 2) P := h_norm_sq_int t
    have h_nonneg : 0 ≤ fun ω : ℕ → G => ‖v ω t‖ ^ 2 := by intro ω; positivity
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h_nonneg) h_int.aestronglyMeasurable]
    have h_lt_top : ∫⁻ ω, ENNReal.ofReal (‖v ω t‖ ^ 2) ∂P < ⊤ := by
      apply lt_of_le_of_lt h_lintegral_bound
      simp
    exact ENNReal.toReal_le_of_le_ofReal ((integral_nonneg fun g => by positivity).trans (hVm x1 hx1).2.2.2)
      h_lintegral_bound
  haveI hP1 : IsProbabilityMeasure P := by rw [hP]; infer_instance
  -- One step in expectation: the law of `(x_t, ω t)` is the product of the law of `x_t` with `ν`.
  have h_inner_bound : ∀ t, (∫ ω, h (x ω t) ∂P) - h xs - β * Δ ≤ ∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P := by
    intro t
    have h_law := AdversarialBco.Poly.sgd_law_step ν proj V s x1 hproj_meas hV t
    have h_pair_meas : Measurable (fun ω : ℕ → G => (x ω t, ω t)) :=
      (hx_meas t).prodMk (measurable_pi_apply t)
    set μx := P.map (fun ω => x ω t) with hμx
    set F : E × G → ℝ := fun z => ⟪V z.1 z.2, z.1 - xs⟫ with hF
    have hF_meas : Measurable F := hV.inner (measurable_fst.sub_const xs)
    have hF_int : Integrable F (μx.prod ν) := by
      have h1 := (integrable_map_measure hF_meas.aestronglyMeasurable h_pair_meas.aemeasurable).mpr
        (h_inner_int t)
      rwa [h_law] at h1
    set Gf : E → ℝ := fun y => ∫ g, F (y, g) ∂ν with hGf
    have hG_int : Integrable Gf μx := hF_int.integral_prod_left
    have hG_meas : AEStronglyMeasurable Gf μx := hG_int.aestronglyMeasurable
    have hA : ∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P = ∫ ω, Gf (x ω t) ∂P := by
      calc ∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P = ∫ z, F z ∂(P.map (fun ω => (x ω t, ω t))) :=
            (integral_map h_pair_meas.aemeasurable hF_meas.aestronglyMeasurable).symm
        _ = ∫ z, F z ∂(μx.prod ν) := by rw [h_law]
        _ = ∫ y, Gf y ∂μx := integral_prod F hF_int
        _ = ∫ ω, Gf (x ω t) ∂P := integral_map (hx_meas t).aemeasurable hG_meas
    have hGx_int : Integrable (fun ω => Gf (x ω t)) P :=
      (integrable_map_measure hG_meas (hx_meas t).aemeasurable).mp hG_int
    have hB : ∀ ω, h (x ω t) - h xs - β * Δ ≤ Gf (x ω t) := by
      intro ω
      have hxD := hx_mem ω t
      obtain ⟨hVi, -, hβ, -⟩ := hVm _ hxD
      have hG_eq : Gf (x ω t) = ⟪∫ g, V (x ω t) g ∂ν, x ω t - xs⟫ := by
        calc Gf (x ω t) = ∫ g, ⟪x ω t - xs, V (x ω t) g⟫ ∂ν :=
              integral_congr_ae (ae_of_all _ fun g => real_inner_comm _ _)
          _ = ⟪x ω t - xs, ∫ g, V (x ω t) g ∂ν⟫ := integral_inner hVi _
          _ = _ := real_inner_comm _ _
      have hsub := hγ _ hxD xs hxs
      have hneg : ⟪γ (x ω t), xs - x ω t⟫ = -⟪γ (x ω t), x ω t - xs⟫ := by
        rw [← inner_neg_right, neg_sub]
      have hab := abs_real_inner_le_norm (∫ g, V (x ω t) g ∂ν - γ (x ω t)) (x ω t - xs)
      have hmul : ‖∫ g, V (x ω t) g ∂ν - γ (x ω t)‖ * ‖x ω t - xs‖ ≤ β * Δ :=
        mul_le_mul hβ (hΔ _ hxD xs hxs) (norm_nonneg _) ((norm_nonneg _).trans hβ)
      have hsplit : ⟪∫ g, V (x ω t) g ∂ν, x ω t - xs⟫ =
          ⟪γ (x ω t), x ω t - xs⟫ + ⟪∫ g, V (x ω t) g ∂ν - γ (x ω t), x ω t - xs⟫ := by
        rw [inner_sub_left]; ring
      have habs := neg_abs_le ⟪∫ g, V (x ω t) g ∂ν - γ (x ω t), x ω t - xs⟫
      rw [hG_eq, hsplit]
      linarith
    have hc_int : Integrable (fun ω => h (x ω t) - h xs - β * Δ) P :=
      ((hhx_int t).sub (integrable_const _)).sub (integrable_const _)
    calc (∫ ω, h (x ω t) ∂P) - h xs - β * Δ = ∫ ω, (h (x ω t) - h xs - β * Δ) ∂P := by
          rw [integral_sub (f := fun ω => h (x ω t) - h xs) (g := fun _ => β * Δ)
              ((hhx_int t).sub (integrable_const _)) (integrable_const _),
            integral_sub (f := fun ω => h (x ω t)) (g := fun _ => h xs) (hhx_int t) (integrable_const _)]
          simp
      _ ≤ ∫ ω, Gf (x ω t) ∂P := integral_mono hc_int hGx_int hB
      _ = _ := hA.symm
  -- Sum over the rounds, with the pathwise bound and the second moments.
  have h_sum_bound : ∑ t ∈ Finset.range N, ((∫ ω, h (x ω t) ∂P) - h xs - β * Δ) ≤
      Δ ^ 2 / (2 * s) + s / 2 * (N * G2) := by
    calc ∑ t ∈ Finset.range N, ((∫ ω, h (x ω t) ∂P) - h xs - β * Δ)
        ≤ ∑ t ∈ Finset.range N, ∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P :=
          Finset.sum_le_sum fun t _ => h_inner_bound t
      _ ≤ Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, ∫ ω, ‖v ω t‖ ^ 2 ∂P := h_pathwise_int
      _ ≤ Δ ^ 2 / (2 * s) + s / 2 * ∑ t ∈ Finset.range N, G2 := by
          have hs2 : 0 ≤ s / 2 := by positivity
          gcongr with t ht
          exact h_norm_sq_bound t
      _ = Δ ^ 2 / (2 * s) + s / 2 * (N * G2) := by simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h_sum_expand : ∑ t ∈ Finset.range N, ((∫ ω, h (x ω t) ∂P) - h xs - β * Δ) =
      (∑ t ∈ Finset.range N, ∫ ω, h (x ω t) ∂P) - N * (h xs + β * Δ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h_avg_bound : (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ ω, h (x ω t) ∂P ≤
      h xs + Δ ^ 2 / (2 * s * N) + s * G2 / 2 + β * Δ := by
    rw [h_sum_expand] at h_sum_bound
    rw [inv_mul_le_iff₀ hNpos]
    have hexp : (N : ℝ) * (h xs + Δ ^ 2 / (2 * s * N) + s * G2 / 2 + β * Δ) =
        N * (h xs + β * Δ) + Δ ^ 2 / (2 * s) + s / 2 * (N * G2) := by
      field_simp
      ring
    rw [hexp]
    linarith
  -- Jensen through the subgradients, then integrate.
  have h_avg_meas : Measurable (fun ω => AdversarialBco.Poly.sgdAvg proj V s x1 N ω) := by
    unfold AdversarialBco.Poly.sgdAvg
    exact (Finset.measurable_sum _ fun t _ => hx_meas t).const_smul _
  have h_avg_mem := fun ω => AdversarialBco.Poly.sgd_avg_mem D proj V s x1 hDv hpD hx1 N hN ω
  have h_avg_int : Integrable (fun ω => h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω)) P := by
    have hm : Measurable (fun ω => h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω)) := by
      have eq : (fun ω => h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω)) =
          (D.domRestrict h) ∘ (fun ω => (⟨_, h_avg_mem ω⟩ : D)) := rfl
      rw [eq]
      exact hh_meas.comp h_avg_meas.subtype_mk
    refine Integrable.mono' (integrable_const M) hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs] using hh_bound _ (h_avg_mem ω)
  have h_jensen : ∀ ω, h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω) ≤
      (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, h (x ω t) := fun ω =>
    AdversarialBco.Poly.subgrad_jensen D hDv h γ hγ N hN (x ω) (hx_mem ω)
  have h_rhs_int : Integrable (fun ω => (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, h (x ω t)) P :=
    (integrable_finsetSum _ fun t _ => hhx_int t).const_mul _
  calc ∫ ω, h (AdversarialBco.Poly.sgdAvg proj V s x1 N ω) ∂P
      ≤ ∫ ω, (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, h (x ω t) ∂P := integral_mono h_avg_int h_rhs_int h_jensen
    _ = (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ ω, h (x ω t) ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun t _ => hhx_int t]
    _ ≤ _ := h_avg_bound

theorem AdversarialBco.Poly.tails_integral_comp_eval {G F : Type*} [MeasurableSpace G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ν : Measure G) [IsProbabilityMeasure ν] (f : G → F) (hf : AEStronglyMeasurable f ν) (i : ℕ) :
    ∫ ω, f (ω i) ∂(Measure.infinitePi fun _ : ℕ => ν) = ∫ g, f g ∂ν := by
  have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => ν) i
  rw [← hmap] at hf
  calc ∫ ω, f (ω i) ∂(Measure.infinitePi fun _ : ℕ => ν)
      = ∫ g, f g ∂((Measure.infinitePi fun _ : ℕ => ν).map (fun ω => ω i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ g, f g ∂ν := by rw [hmap]

theorem AdversarialBco.Poly.tails_memLp_comp_eval {G F : Type*} [MeasurableSpace G] [NormedAddCommGroup F]
    (ν : Measure G) [IsProbabilityMeasure ν] (f : G → F) (p : ENNReal) (hf : MemLp f p ν) (i : ℕ) :
    MemLp (fun ω : ℕ → G => f (ω i)) p (Measure.infinitePi fun _ : ℕ => ν) :=
  hf.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i)

theorem AdversarialBco.Poly.tails_cross_inner_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {G : Type*} [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (Ψ : G → E) (hΨ : Measurable Ψ) (hΨ1 : Integrable Ψ ν) (hΨ0 : ∫ g, Ψ g ∂ν = 0)
    (i j : ℕ) (hij : i ≠ j) :
    ∫ ω, ⟪Ψ (ω i), Ψ (ω j)⟫ ∂(Measure.infinitePi fun _ : ℕ => ν) = 0 := by
  have hind : IndepFun (fun ω : ℕ → G => Ψ (ω i)) (fun ω => Ψ (ω j)) (Measure.infinitePi fun _ : ℕ => ν) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => Ψ) (fun _ => hΨ)).indepFun hij
  have hi : Integrable (fun ω : ℕ → G => Ψ (ω i)) (Measure.infinitePi fun _ : ℕ => ν) := by
    have := AdversarialBco.Poly.tails_memLp_comp_eval ν Ψ 1 (memLp_one_iff_integrable.mpr hΨ1) i
    exact memLp_one_iff_integrable.mp this
  have hj : Integrable (fun ω : ℕ → G => Ψ (ω j)) (Measure.infinitePi fun _ : ℕ => ν) := by
    have := AdversarialBco.Poly.tails_memLp_comp_eval ν Ψ 1 (memLp_one_iff_integrable.mpr hΨ1) j
    exact memLp_one_iff_integrable.mp this
  have h := hind.integral_bilin hi hj (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  change ∫ ω, ⟪Ψ (ω i), Ψ (ω j)⟫ ∂(Measure.infinitePi fun _ : ℕ => ν) = ⟪_, _⟫ at h
  rw [h, AdversarialBco.Poly.tails_integral_comp_eval ν Ψ hΨ1.aestronglyMeasurable i,
    AdversarialBco.Poly.tails_integral_comp_eval ν Ψ hΨ1.aestronglyMeasurable j, hΨ0, inner_zero_left]

theorem AdversarialBco.Poly.tails_vec_sq_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {G : Type*} [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (Ψ : G → E) (hΨ : Measurable Ψ) (hΨ2 : MemLp Ψ 2 ν) (hΨ0 : ∫ g, Ψ g ∂ν = 0)
    (n : ℕ) :
    ∫ ω, ‖∑ i ∈ Finset.range n, Ψ (ω i)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => ν) = n * ∫ g, ‖Ψ g‖ ^ 2 ∂ν := by
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  have hL2 : ∀ i, MemLp (fun ω : ℕ → G => Ψ (ω i)) 2 P := fun i =>
    AdversarialBco.Poly.tails_memLp_comp_eval ν Ψ 2 hΨ2 i
  have hint : ∀ i j, Integrable (fun ω : ℕ → G => ⟪Ψ (ω i), Ψ (ω j)⟫) P := by
    intro i j
    have hb : Integrable (fun ω => ‖Ψ (ω i)‖ * ‖Ψ (ω j)‖) P := (hL2 i).norm.integrable_mul (hL2 j).norm
    refine hb.mono' ((hL2 i).aestronglyMeasurable.inner (hL2 j).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hexp : ∀ ω : ℕ → G, ‖∑ i ∈ Finset.range n, Ψ (ω i)‖ ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ⟪Ψ (ω i), Ψ (ω j)⟫ := by
    intro ω
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have hdiag : ∀ i ∈ Finset.range n,
      ∫ ω, ∑ j ∈ Finset.range n, ⟪Ψ (ω i), Ψ (ω j)⟫ ∂P = ∫ g, ‖Ψ g‖ ^ 2 ∂ν := by
    intro i hi
    rw [integral_finsetSum _ fun j _ => hint i j,
      Finset.sum_eq_single_of_mem i hi (fun j _ hji => AdversarialBco.Poly.tails_cross_inner_zero ν Ψ hΨ
        (hΨ2.integrable one_le_two) hΨ0 i j (Ne.symm hji))]
    simp_rw [real_inner_self_eq_norm_sq]
    exact AdversarialBco.Poly.tails_integral_comp_eval ν (fun g => ‖Ψ g‖ ^ 2)
      (hΨ2.aestronglyMeasurable.norm.pow 2) i
  rw [Finset.sum_congr rfl hdiag]
  simp

theorem AdversarialBco.Poly.tails_norm_sq_sub_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (Φ : G → E)
    (hΦ2 : MemLp Φ 2 ν) :
    ∫ g, ‖Φ g - ∫ g', Φ g' ∂ν‖ ^ 2 ∂ν = ∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖∫ g, Φ g ∂ν‖ ^ 2 := by
  set m := ∫ g, Φ g ∂ν with hm
  have h1 : Integrable (fun g => ‖Φ g‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hΦ2.aestronglyMeasurable).mp hΦ2
  have hΦ1 : Integrable Φ ν := hΦ2.integrable one_le_two
  have hI : Integrable (fun g => ⟪m, Φ g⟫) ν := (innerSL ℝ m).integrable_comp hΦ1
  have hpt : ∀ g, ‖Φ g - m‖ ^ 2 = ‖Φ g‖ ^ 2 - 2 * ⟪m, Φ g⟫ + ‖m‖ ^ 2 := by
    intro g; rw [norm_sub_sq_real, real_inner_comm]
  simp_rw [hpt]
  rw [integral_add (f := fun g => ‖Φ g‖ ^ 2 - 2 * ⟪m, Φ g⟫) (g := fun _ => ‖m‖ ^ 2)
      (h1.sub (hI.const_mul 2)) (integrable_const _),
    integral_sub (f := fun g => ‖Φ g‖ ^ 2) (g := fun g => 2 * ⟪m, Φ g⟫) h1 (hI.const_mul 2),
    integral_const_mul, integral_inner hΦ1 m, real_inner_self_eq_norm_sq, integral_const]
  simp
  ring

theorem AdversarialBco.Poly.tails_markov_norm {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) [IsFiniteMeasure P] (S : Ω → E) (hS : MemLp S 2 P) (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ‖S ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖S ω‖ ^ 2 ∂P) / t ^ 2) := by
  have hint : Integrable (fun ω => ‖S ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg ‖S ω‖) hint (t ^ 2)
  have hset : {ω | t ^ 2 ≤ ‖S ω‖ ^ 2} = {ω | t ≤ ‖S ω‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact pow_le_pow_iff_left₀ ht.le (norm_nonneg _) two_ne_zero
  rw [hset] at hmk
  have ht2 : 0 < t ^ 2 := by positivity
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ ht2]
  linarith

theorem AdversarialBco.Poly.cheb_avg_main (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (G : Type*) [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (Φ : G → E) (hΦ : Measurable Φ) (hΦ2 : MemLp Φ 2 ν) (n : ℕ) (t : ℝ) (hn : 1 ≤ n)
    (ht : 0 < t) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) - ∫ g, Φ g ∂ν‖} ≤
      ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂ν) / (n * t ^ 2)) := by
  have hnorm2 := AdversarialBco.Poly.tails_norm_sq_sub_integral ν Φ hΦ2
  obtain ⟨m, hm⟩ : ∃ m : E, m = ∫ g, Φ g ∂ν := ⟨_, rfl⟩
  rw [← hm] at hnorm2 ⊢
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : G → E, Ψ = fun g => Φ g - m := ⟨_, rfl⟩
  have hΨ : Measurable Ψ := hΨdef ▸ hΦ.sub_const m
  have hΨ2 : MemLp Ψ 2 ν := hΨdef ▸ hΦ2.sub (memLp_const m)
  have hΨ0 : ∫ g, Ψ g ∂ν = 0 := by
    rw [hΨdef, integral_sub (hΦ2.integrable one_le_two) (integrable_const m), integral_const, ← hm]
    simp
  have hΨn : ∫ g, ‖Ψ g‖ ^ 2 ∂ν = ∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2 := by rw [hΨdef, hnorm2]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨S, hSdef⟩ : ∃ S : (ℕ → G) → E, S = fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Ψ (ω i) := ⟨_, rfl⟩
  have hrw : ∀ ω : ℕ → G, (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) - m = S ω := by
    intro ω
    rw [hSdef, hΨdef]
    simp only
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub,
      smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul]
  have hset : {ω : ℕ → G | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) - m‖} = {ω | t ≤ ‖S ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hrw ω]
  rw [hset]
  have hSL2 : MemLp S 2 (Measure.infinitePi fun _ : ℕ => ν) := by
    rw [hSdef]
    exact (memLp_finsetSum _ fun i _ => AdversarialBco.Poly.tails_memLp_comp_eval ν Ψ 2 hΨ2 i).const_smul
      ((n : ℝ)⁻¹)
  have hES : ∫ ω, ‖S ω‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => ν) =
      (n : ℝ)⁻¹ * (∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) := by
    have hpt : ∀ ω, ‖S ω‖ ^ 2 = ((n : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ Finset.range n, Ψ (ω i)‖ ^ 2 := by
      intro ω
      rw [hSdef, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp_rw [hpt]
    rw [integral_const_mul, AdversarialBco.Poly.tails_vec_sq_sum ν Ψ hΨ hΨ2 hΨ0 n, hΨn]
    field_simp
  have hm2 : 0 ≤ ‖m‖ ^ 2 := sq_nonneg _
  have ht2 : 0 < t ^ 2 := by positivity
  have hfin : (n : ℝ)⁻¹ * (∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) / t ^ 2 ≤ (∫ g, ‖Φ g‖ ^ 2 ∂ν) / (n * t ^ 2) := by
    rw [div_le_div_iff₀ ht2 (mul_pos hnpos ht2)]
    have hinv : (n : ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hnpos.ne'
    have hA : (n : ℝ)⁻¹ * (∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) * (n * t ^ 2) =
        (∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) * t ^ 2 := by
      rw [show (n : ℝ)⁻¹ * (∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) * (n * t ^ 2) =
        ((n : ℝ)⁻¹ * n) * ((∫ g, ‖Φ g‖ ^ 2 ∂ν - ‖m‖ ^ 2) * t ^ 2) by ring, hinv, one_mul]
    rw [hA]
    nlinarith
  calc (Measure.infinitePi fun _ : ℕ => ν) {ω | t ≤ ‖S ω‖}
      ≤ ENNReal.ofReal ((∫ ω, ‖S ω‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => ν)) / t ^ 2) :=
        AdversarialBco.Poly.tails_markov_norm _ S hSL2 t ht
    _ ≤ ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂ν) / (n * t ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hES]
      exact hfin


open Classical in
theorem AdversarialBco.Poly.majority_main (G : Type*) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    (B : Set G) (hB : MeasurableSet B) (hνB : ν B ≤ 1 / 4) (m : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => ω i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := by
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  set p := (ν B).toReal with hp
  have hp_fin : ν B < ⊤ := by
    have : IsZeroOrProbabilityMeasure ν := by infer_instance
    have h_fin : IsFiniteMeasure ν := IsZeroOrProbabilityMeasure.toIsFiniteMeasure ν
    exact measure_lt_top ν B
  have hp_one_fin : (1 : ENNReal) / 4 < ⊤ := by
    norm_num
  have hp_le : p ≤ 1/4 := by
    rw [hp]
    have h := (ENNReal.toReal_le_toReal (ne_of_lt hp_fin) (ne_of_lt hp_one_fin)).mpr hνB
    simpa using h
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact mod_cast Nat.zero_le m
  -- define X_i(x) = 1_B(x) - p
  let X : ℕ → G → ℝ := fun i x => (if x ∈ B then (1 : ℝ) else 0) - p
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    unfold X
    refine Measurable.sub (measurable_const.indicator hB) measurable_const
  have hX_range : ∀ i, ∀ x, X i x ∈ Set.Icc (-p) (1 - p) := by
    intro i x
    unfold X
    have hx_low : 0 ≤ (if x ∈ B then (1 : ℝ) else 0) := by
      split <;> norm_num
    have hx_high : (if x ∈ B then (1 : ℝ) else 0) ≤ 1 := by
      split <;> norm_num
    have hlow : -p ≤ (if x ∈ B then (1 : ℝ) else 0) - p := by linarith
    have hhigh : (if x ∈ B then (1 : ℝ) else 0) - p ≤ 1 - p := by linarith
    exact ⟨hlow, hhigh⟩
  have hX_int : ∀ i, ∫ ω, X i (ω i) ∂P = 0 := by
    intro i
    unfold X
    have h_int_indicator : ∫ ω, (if ω i ∈ B then (1 : ℝ) else 0) ∂P = p := by
      calc
        ∫ ω, (if ω i ∈ B then (1 : ℝ) else 0) ∂P
            = ∫ ω, (B.indicator (fun _ => (1 : ℝ))) (ω i) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with ω
          simp [Set.indicator]
        _ = ∫ x, (B.indicator (fun _ => (1 : ℝ))) x ∂(P.map (fun ω => ω i)) := by
          rw [integral_map (measurable_pi_apply i).aemeasurable
            ((measurable_const.indicator hB).aestronglyMeasurable)]
        _ = ∫ x, (B.indicator (fun _ => (1 : ℝ))) x ∂ν := by rw [hP, Measure.infinitePi_map_eval]
        _ = ν.real B := integral_indicator_one hB
        _ = p := by rw [hp, Measure.real_def]
    have h_int_const : ∫ ω, p ∂P = p := by
      rw [integral_const, smul_eq_mul]
      have : P.real Set.univ = 1 := by simp [Measure.real_def]
      rw [this, one_mul]
    have hint_integrable : Integrable (fun ω => (if ω i ∈ B then (1 : ℝ) else 0)) P := by
      have h_eq : (fun (ω : ℕ → G) => (if ω i ∈ B then (1 : ℝ) else 0)) =
          (B.indicator (fun _ => (1 : ℝ))) ∘ (fun (ω : ℕ → G) => ω i) := by
        funext ω; simp [Set.indicator]
      rw [h_eq]
      rw [← integrable_map_measure ((measurable_const.indicator hB).aestronglyMeasurable)
        (measurable_pi_apply i).aemeasurable]
      rw [hP, Measure.infinitePi_map_eval]
      rw [integrable_indicator_iff hB]
      exact integrableOn_const (ne_of_lt hp_fin)
    calc
      ∫ ω, ((if ω i ∈ B then (1 : ℝ) else 0) - p) ∂P
          = (∫ ω, (if ω i ∈ B then (1 : ℝ) else 0) ∂P) - (∫ ω, p ∂P) := by
        rw [integral_sub hint_integrable (integrable_const _)]
      _ = p - p := by rw [h_int_indicator, h_int_const]
      _ = 0 := by ring
  have h_indep : iIndepFun (fun i ω => X i (ω i)) P := by
    rw [hP]
    exact iIndepFun_infinitePi hX_meas
  have h_subG : ∀ i < m, HasSubgaussianMGF (fun ω => X i (ω i)) ((1 : NNReal) / 4) P := by
    intro i hi
    have h_subg : HasSubgaussianMGF (fun ω => X i (ω i)) ((‖(1 - p) - (-p)‖₊ / 2) ^ 2) P :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        ((hX_meas i).comp (measurable_pi_apply i)).aemeasurable
        (ae_of_all _ (fun ω => hX_range i (ω i)))
        (hX_int i)
    -- simplify the parameter: (1/2)^2 = 1/4
    have h_param : ((‖(1 - p) - (-p)‖₊ / 2) ^ 2 : NNReal) = (1 : NNReal) / 4 := by
      have h_diff : (1 : ℝ) - p - (-p) = (1 : ℝ) := by ring
      rw [h_diff]
      norm_num
    -- convert the parameter using h_param
    convert h_subg using 1
    exact h_param.symm
  -- Now apply Hoeffding inequality
  have h_hoeffding : P.real {ω | (m : ℝ) / 4 ≤ ∑ i ∈ Finset.range m, X i (ω i)} ≤
      Real.exp (-(m : ℝ) / 8) := by
    have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep (fun i hi => h_subG i hi)
      (ε := (m : ℝ) / 4) (div_nonneg hm_nonneg (by norm_num))
    -- The lemma gives: P.real {ω | (m:ℝ)/4 ≤ ∑ X_i} ≤ exp (-(m/4)^2 / (2 * m * (1/4)))
    -- We need: P.real {ω | (m:ℝ)/4 ≤ ∑ X_i} ≤ exp (-m/8)
    -- h gives the inequality with the LHS exponent; we need to rewrite the exponent
    -- The exponents are equal: -(m/4)^2 / (2 * m * (1/4)) = -m/8
    -- We can use `field_simp` and `ring` to prove this
    refine h.trans ?_
    -- Goal: Real.exp (-(↑m / 4) ^ 2 / (2 * ↑m * ↑(1 / 4))) ≤ Real.exp (-↑m / 8)
    -- Since Real.exp is monotone, it suffices to show the exponent equality
    have h_exp_eq : (-(↑m / 4) ^ 2 / (2 * ↑m * ↑(1 / 4)) : ℝ) = (-↑m / 8) := by
      field_simp
      ring
    -- Now rewrite the LHS using h_exp_eq
    -- We need to rewrite inside Real.exp
    have := congrArg Real.exp h_exp_eq
    -- this: Real.exp (LHS) = Real.exp (RHS)
    -- So LHS ≤ RHS follows by le_of_eq
    rw [← this]
    -- Now goal is Real.exp (LHS) ≤ Real.exp (LHS), which is le_rfl
    exact le_rfl
  -- Connect the event: if m/2 ≤ card then m/4 ≤ ∑ X_i
  have h_event : {ω : ℕ → G | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => ω i ∈ B).card} ⊆
      {ω : ℕ → G | (m : ℝ) / 4 ≤ ∑ i ∈ Finset.range m, X i (ω i)} := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω ⊢
    have h_card : ((Finset.range m).filter fun i => ω i ∈ B).card = ∑ i ∈ Finset.range m, (if ω i ∈ B then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]
      simp
    rw [h_card] at hω
    have h_sum : ∑ i ∈ Finset.range m, X i (ω i) = (∑ i ∈ Finset.range m, (if ω i ∈ B then (1 : ℝ) else 0)) - (m : ℝ) * p := by
      calc
        ∑ i ∈ Finset.range m, X i (ω i) = ∑ i ∈ Finset.range m, ((if ω i ∈ B then (1 : ℝ) else 0) - p) := rfl
        _ = (∑ i ∈ Finset.range m, (if ω i ∈ B then (1 : ℝ) else 0)) - (∑ i ∈ Finset.range m, p) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ i ∈ Finset.range m, (if ω i ∈ B then (1 : ℝ) else 0)) - (m : ℝ) * p := by
          simp [Finset.sum_const]
    rw [h_sum]
    nlinarith [hp_le]
  -- Now combine everything
  calc
    P {ω | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => ω i ∈ B).card}
        ≤ P {ω | (m : ℝ) / 4 ≤ ∑ i ∈ Finset.range m, X i (ω i)} :=
      measure_mono h_event
    _ = ENNReal.ofReal (P.real {ω | (m : ℝ) / 4 ≤ ∑ i ∈ Finset.range m, X i (ω i)}) := by
      rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) :=
      ENNReal.ofReal_le_ofReal h_hoeffding

theorem AdversarialBco.Poly.rounds_all_miss (G : Type*) [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (A : Set G) (hA : MeasurableSet A) (J : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω | ∀ r < J, ω r ∈ A} = ν A ^ J := by
  have h_set_eq : {ω | ∀ r < J, ω r ∈ A} = ((Finset.range J : Set ℕ).pi fun _ : ℕ => A) := by
    ext ω
    simp [Set.mem_pi]
  rw [h_set_eq]
  have h_meas : ∀ i ∈ Finset.range J, MeasurableSet (A : Set G) := by
    intro i hi
    exact hA
  rw [MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => ν) h_meas]
  simp [Finset.prod_const, Finset.card_range]

theorem AdversarialBco.Poly.rounds_some_hit (G : Type*) [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] (B : Set G) (hB : MeasurableSet B) (J : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω | ∃ r < J, ω r ∈ B} ≤ J * ν B := by
  have h_eq : {ω' : ℕ → G | ∃ r < J, ω' r ∈ B} = ⋃ r ∈ Finset.range J, (fun ω' => ω' r) ⁻¹' B := by
    ext ω'; simp [Finset.mem_range]
  rw [h_eq]
  calc
    (Measure.infinitePi fun _ : ℕ => ν) (⋃ r ∈ Finset.range J, (fun ω' => ω' r) ⁻¹' B) ≤
        ∑ r ∈ Finset.range J, (Measure.infinitePi fun _ : ℕ => ν) ((fun ω' => ω' r) ⁻¹' B) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ = ∑ r ∈ Finset.range J, ν B := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hmeas : Measurable (fun (ω : ℕ → G) => ω r) := measurable_pi_apply r
      rw [← MeasureTheory.Measure.map_apply hmeas hB, MeasureTheory.Measure.infinitePi_map_eval]
    _ = ((Finset.range J).card : ENNReal) • ν B := by simp [Finset.sum_const]
    _ = (J : ENNReal) • ν B := by simp
    _ = J * ν B := by simp [smul_eq_mul]

namespace AdversarialBco.Poly

/-! ## Assemblies -/

theorem sgdExpect : SgdExpect := fun E _ _ _ _ _ G _ ν _ D proj h γ V xs x1 Δ s G2 β N hDc hDv hh hpc hpD hpn hV
    hx1 hxs hmin hΔ hγ hVm hs hN =>
  sgd_expect_main E G ν D proj h γ V xs x1 Δ s G2 β N hDc hDv hh hpc hpD hpn hV hx1 hxs hmin hΔ hγ hVm hs hN

theorem chebAvg : ChebAvg := fun E _ _ _ _ _ G _ ν _ Φ hΦ hΦ2 n t hn ht =>
  cheb_avg_main E G ν Φ hΦ hΦ2 n t hn ht

theorem majorityHoeffding : MajorityHoeffding := fun G _ ν _ B hB hνB m => by
  convert majority_main G ν B hB hνB m

theorem roundsAllMiss : RoundsAllMiss := fun G _ ν _ A hA J => rounds_all_miss G ν A hA J

theorem roundsSomeHit : RoundsSomeHit := fun G _ ν _ B hB J => rounds_some_hit G ν B hB J

end AdversarialBco.Poly
