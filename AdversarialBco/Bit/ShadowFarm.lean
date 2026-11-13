/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowAdv
public import AdversarialBco.Poly.Df2OracleProof

@[expose] public section

/-!
# Self-contained lemmas of the coupling layer

* `oball_interior`, `rat_dense_lower`, `apAdv_spec` ((O7)): the checked advice routine meets `ApSpec` for every advice
  (`d ≥ 1`): a candidate that passes the test at every rational point of a convex region with nonempty interior is
  within `e` of the infimum on the whole region; otherwise the routine is `apCall`, which meets `ApSpec` (`propAP`);
* `fshift`, `setE_shift`: setting (E) passes to the filtration started at `a`;
* `lintegral_affine_abs`, `step2_core`: `E (κ0 + κ1 |ε|) ≤ κ0 + κ1` when `E |ε| ≤ 1`, and the section bound (Step 2 of
  SHADOW);
* `union5`: the union bound over the five events of a virtual epoch.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.Poly

variable {d : ℕ}

/-! ## (O7): `ApSpec` of the checked advice routine -/

theorem oball_interior (Q : Set (Fin d → ℝ)) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) (h : oBall a r ⊆ Q) :
    a ∈ interior Q := by
  set g := fun (x : Fin d → ℝ) => Real.sqrt ((x - a) ⬝ᵥ (x - a)) with hg
  have hg_cont : Continuous g := by
    have h_sub_cont : Continuous (fun (x : Fin d → ℝ) => x - a) := by fun_prop
    exact Real.continuous_sqrt.comp (Continuous.dotProduct h_sub_cont h_sub_cont)
  have hU_open : IsOpen {x | g x < r} := isOpen_lt hg_cont continuous_const
  have ha_mem_U : a ∈ {x | g x < r} := by
    show Real.sqrt ((a - a) ⬝ᵥ (a - a)) < r
    simpa using hr
  have hU_sub_Q : {x | g x < r} ⊆ Q := fun x hx => h (by show oNorm (x - a) ≤ r; unfold oNorm; exact le_of_lt hx)
  rw [mem_interior]
  exact ⟨{x | g x < r}, hU_sub_Q, hU_open, ha_mem_U⟩

theorem rat_dense_lower (Q : Set (Fin d → ℝ)) (hQ : Convex ℝ Q) (hint : (interior Q).Nonempty)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (c : ℝ)
    (h : ∀ q : Fin d → ℚ, (fun i => (q i : ℝ)) ∈ Q → c ≤ f (fun i => (q i : ℝ))) : ∀ y ∈ Q, c ≤ f y := by
  let D : Set (Fin d → ℝ) := Set.range (fun (q : Fin d → ℚ) => fun i => (q i : ℝ))
  have hD_dense : Dense D := by
    have h_pi : DenseRange (Pi.map (fun (_ : Fin d) => (Rat.cast : ℚ → ℝ))) :=
      DenseRange.piMap (fun (_ : Fin d) => Rat.denseRange_cast (𝕜 := ℝ))
    have h_eq : Pi.map (fun (_ : Fin d) => (Rat.cast : ℚ → ℝ)) = (fun (q : Fin d → ℚ) => fun i => (q i : ℝ)) := by
      ext q i; rfl
    rw [h_eq] at h_pi
    exact h_pi
  let C : Set (Fin d → ℝ) := {y | c ≤ f y}
  have hC_closed : IsClosed C := isClosed_le continuous_const hf
  have h_sub_closure : interior Q ⊆ closure (interior Q ∩ D) :=
    Dense.open_subset_closure_inter hD_dense isOpen_interior
  have h_inter_sub_C : interior Q ∩ D ⊆ C := by
    rintro x ⟨hx_int, q, rfl⟩
    exact h q (interior_subset hx_int)
  have h_intQ_sub_C : interior Q ⊆ C := h_sub_closure.trans (closure_minimal h_inter_sub_C hC_closed)
  have h_Q_sub_closure_intQ : Q ⊆ closure (interior Q) := by
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior hQ hint]
    exact subset_closure
  intro y hy
  exact closure_minimal h_intQ_sub_C hC_closed (h_Q_sub_closure_intQ hy)

/-- `ApSpec` of the proved routine, from `PropAP` (`d ≥ 1`). -/
theorem apSpec_apCall (hd : 1 ≤ d) : ApSpec (d := d) apCall := fun Q a0 r R P w e =>
  ⟨fun h1 h2 h3 h4 h5 h6 h7 => (propAP d Q a0 r R P w e).1 hd h1 h2 h3 h4 h5 h6 h7, (propAP d Q a0 r R P w e).2⟩

/-- (O7): the checked advice routine meets `ApSpec` for every advice. -/
theorem apAdv_spec (hd : 1 ≤ d) (v : Adv d) : ApSpec (apAdv v) := by
  classical
  intro Q a0 r R P w e
  obtain ⟨h_clause_a, h_clause_b⟩ := apSpec_apCall hd Q a0 r R P w e
  constructor
  · intro hconv hclosed hr hball hQball hposdef he_pos
    by_cases hadv_ok : advOK Q R P w e (advPick v e)
    · have hok := hadv_ok
      obtain ⟨hxQ, -, hrat⟩ := hadv_ok
      have hint : a0 ∈ interior Q := oball_interior Q a0 r hr hball
      have hcont : Continuous (ellF P w) :=
        continuous_ellF.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      have h_dense := rat_dense_lower Q hconv ⟨a0, hint⟩ (ellF P w) hcont (ellF P w (advPick v e) - e)
        fun q hqQ => by linarith [hrat q hqQ]
      refine ⟨advPick v e, ?_, hxQ, fun y hy => by linarith [h_dense y hy]⟩
      simp only [apAdv, hok, ↓reduceIte]
    · obtain ⟨μ, hμ, hμQ, hμell⟩ := h_clause_a hconv hclosed hr hball hQball hposdef he_pos
      refine ⟨μ, ?_, hμQ, hμell⟩
      simp only [apAdv, hadv_ok, ↓reduceIte]
      exact hμ
  · by_cases hadv_ok : advOK Q R P w e (advPick v e)
    · right
      refine ⟨advPick v e, ?_, hadv_ok.1, hadv_ok.2.1⟩
      simp only [apAdv, hadv_ok, ↓reduceIte]
    · rcases h_clause_b with hnone | ⟨μ, hμ, hμQ, hμR⟩
      · left
        simp only [apAdv, hadv_ok, ↓reduceIte]
        exact hnone
      · right
        refine ⟨μ, ?_, hμQ, hμR⟩
        simp only [apAdv, hadv_ok, ↓reduceIte]
        exact hμ

/-! ## Setting (E) from a start round -/

/-- The filtration started at `a`. -/
def fshift {Ω : Type} [m0 : MeasurableSpace Ω] (𝒢 : Filtration ℕ m0) (a : ℕ) : Filtration ℕ m0 where
  seq s := 𝒢 (a + s)
  mono' _ _ h := 𝒢.mono (Nat.add_le_add_left h a)
  le' s := 𝒢.le (a + s)

/-- Setting (E) passes to the filtration started at `a`, with the draws and noises read from `a`. -/
theorem setE_shift {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (H : Df2SetE d μ 𝒢 ξ e) (a : ℕ) :
    Df2SetE d μ (fshift 𝒢 a) (fun s => ξ (a + s)) (fun s => e (a + s)) :=
  ⟨fun s => H.xi_meas (a + s), fun s => H.xi_law (a + s), fun s => H.xi_indep (a + s),
    fun s => H.e_meas (a + s), fun s => H.e_int (a + s), fun s => H.e_mean (a + s), fun s => H.e_exp (a + s)⟩

/-! ## Step 2 -/

theorem lintegral_affine_abs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Ω → ℝ)
    (hε : Measurable ε) (h1 : ∫⁻ ω, ENNReal.ofReal |ε ω| ∂μ ≤ 1) (κ0 κ1 : ℝ) (h0 : 0 ≤ κ0) (h1' : 0 ≤ κ1) :
    ∫⁻ ω, ENNReal.ofReal (κ0 + κ1 * |ε ω|) ∂μ ≤ ENNReal.ofReal (κ0 + κ1) := by
  have h_meas_abs : Measurable fun ω => ENNReal.ofReal (|ε ω|) := (Measurable.abs hε).ennreal_ofReal
  calc
    ∫⁻ ω, ENNReal.ofReal (κ0 + κ1 * |ε ω|) ∂μ
        = ∫⁻ ω, (ENNReal.ofReal κ0 + ENNReal.ofReal κ1 * ENNReal.ofReal (|ε ω|)) ∂μ := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_add h0 (mul_nonneg h1' (abs_nonneg _)), ENNReal.ofReal_mul h1']
    _ = ENNReal.ofReal κ0 + ENNReal.ofReal κ1 * ∫⁻ ω, ENNReal.ofReal (|ε ω|) ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ h_meas_abs, measure_univ,
        mul_one]
    _ ≤ ENNReal.ofReal κ0 + ENNReal.ofReal κ1 * 1 := by gcongr
    _ = ENNReal.ofReal (κ0 + κ1) := by rw [mul_one, ENNReal.ofReal_add h0 h1']


/-- Step 2's core: the measure of `{(X, Z) ∈ D, X ∈ B}` when `Z` is independent of `X`'s σ-algebra, by the
  section bound on `B`. -/
theorem step2_core {Ω α β : Type*} (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ m0)
    (X : Ω → α) (hX : Measurable[m] X) (Z : Ω → β) (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m μ) (D : Set (α × β)) (hD : MeasurableSet D)
    (B : Set α) (hB : MeasurableSet B) (g : α → ℝ) (hg : Measurable g)
    (hDB : ∀ x ∈ B, (μ.map Z) (Prod.mk x ⁻¹' D) ≤ ENNReal.ofReal (g x)) :
    μ {ω | (X ω, Z ω) ∈ D ∧ X ω ∈ B} ≤ ∫⁻ ω, ENNReal.ofReal (g (X ω)) ∂μ := by
  -- Convert hX to Measurable w.r.t. m0
  have hX' : Measurable X := hX.mono hm le_rfl
  have hX_aemeas : AEMeasurable X μ := hX'.aemeasurable
  have hZ_aemeas : AEMeasurable Z μ := hZ.aemeasurable
  -- Step 1: Get IndepFun X Z μ
  have hX_comap_le : MeasurableSpace.comap X inferInstance ≤ m := hX.comap_le
  have hind' : Indep (MeasurableSpace.comap Z inferInstance) (MeasurableSpace.comap X inferInstance) μ :=
    indep_of_indep_of_le_right hind hX_comap_le
  have hind'' : Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Z inferInstance) μ :=
    hind'.symm
  have h_indep_fun : IndepFun X Z μ := hind''
  -- Step 2: Get the map equality
  have h_map_eq : Measure.map (fun ω => (X ω, Z ω)) μ = (Measure.map X μ).prod (Measure.map Z μ) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hX_aemeas hZ_aemeas).mp h_indep_fun)
  -- Step 3: Define S = D ∩ (B ×ˢ Set.univ)
  let S : Set (α × β) := D ∩ (B ×ˢ Set.univ)
  have hS_meas : MeasurableSet S :=
    MeasurableSet.inter hD (MeasurableSet.prod hB MeasurableSet.univ)
  -- Step 4: The target set is the preimage of S under the pair map
  have h_target : {ω | (X ω, Z ω) ∈ D ∧ X ω ∈ B} = (fun ω => (X ω, Z ω)) ⁻¹' S := by
    ext ω; simp [S]
  -- Step 5: Measure of target = ((μ.map X).prod (μ.map Z)) S
  have h_target_measure : μ {ω | (X ω, Z ω) ∈ D ∧ X ω ∈ B} = ((Measure.map X μ).prod (Measure.map Z μ)) S := by
    calc
      μ {ω | (X ω, Z ω) ∈ D ∧ X ω ∈ B} = μ ((fun ω => (X ω, Z ω)) ⁻¹' S) := by rw [h_target]
      _ = (Measure.map (fun ω => (X ω, Z ω)) μ) S := by
        rw [Measure.map_apply (Measurable.prodMk hX' hZ) hS_meas]
      _ = ((Measure.map X μ).prod (Measure.map Z μ)) S := by rw [h_map_eq]
  -- Step 6: Express as integral
  have h_prod_apply : ((Measure.map X μ).prod (Measure.map Z μ)) S = ∫⁻ x, (Measure.map Z μ) (Prod.mk x ⁻¹' S) ∂(Measure.map X μ) :=
    Measure.prod_apply hS_meas
  -- Step 7: Bound the integrand
  have h_bound : ∀ x, (Measure.map Z μ) (Prod.mk x ⁻¹' S) ≤ ENNReal.ofReal (g x) := by
    intro x
    by_cases hxB : x ∈ B
    · have h_preimage_eq : Prod.mk x ⁻¹' S = Prod.mk x ⁻¹' D := by
        ext y; simp [S, hxB]
      rw [h_preimage_eq]
      exact hDB x hxB
    · have h_preimage_eq : Prod.mk x ⁻¹' S = ∅ := by
        ext y; simp [S, hxB]
      rw [h_preimage_eq]
      simp
  -- Step 8: Integrate the bound
  have h_integral_bound : ∫⁻ x, (Measure.map Z μ) (Prod.mk x ⁻¹' S) ∂(Measure.map X μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂(Measure.map X μ) :=
    lintegral_mono h_bound
  -- Step 9: Change of variables back to ω
  have h_lintegral_map : ∫⁻ x, ENNReal.ofReal (g x) ∂(Measure.map X μ) = ∫⁻ ω, ENNReal.ofReal (g (X ω)) ∂μ := by
    rw [MeasureTheory.lintegral_map (hg.ennreal_ofReal) hX']
  -- Combine everything
  calc
    μ {ω | (X ω, Z ω) ∈ D ∧ X ω ∈ B} = ((Measure.map X μ).prod (Measure.map Z μ)) S := h_target_measure
    _ = ∫⁻ x, (Measure.map Z μ) (Prod.mk x ⁻¹' S) ∂(Measure.map X μ) := h_prod_apply
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂(Measure.map X μ) := h_integral_bound
    _ = ∫⁻ ω, ENNReal.ofReal (g (X ω)) ∂μ := h_lintegral_map

/-- The union bound over the five events of a virtual epoch, with the budgets `3/7, 1/7, 1/21, 1/7, 1/8` of `δe`. -/
theorem union5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G Y LQ SDF DQ : Ω → Prop) (δe : ℝ) (hδe : 0 ≤ δe)
    (hG : μ {ω | ¬ G ω} ≤ ENNReal.ofReal (3 / 7 * δe))
    (hY : μ {ω | G ω ∧ ¬ Y ω} ≤ ENNReal.ofReal (1 / 7 * δe))
    (hLQ : μ {ω | G ω ∧ ¬ LQ ω} ≤ ENNReal.ofReal (1 / 21 * δe))
    (hSDF : μ {ω | G ω ∧ ¬ SDF ω} ≤ ENNReal.ofReal (1 / 7 * δe))
    (hDQ : μ {ω | G ω ∧ ¬ DQ ω} ≤ ENNReal.ofReal (1 / 8 * δe)) :
    μ {ω | ¬ (G ω ∧ Y ω ∧ LQ ω ∧ SDF ω ∧ DQ ω)} ≤ ENNReal.ofReal (149 / 168 * δe) := by
  set A := {ω | ¬ G ω} with hA
  set B := {ω | G ω ∧ ¬ Y ω} with hB
  set C := {ω | G ω ∧ ¬ LQ ω} with hC
  set D := {ω | G ω ∧ ¬ SDF ω} with hD
  set E := {ω | G ω ∧ ¬ DQ ω} with hE
  have h_sub : {ω | ¬ (G ω ∧ Y ω ∧ LQ ω ∧ SDF ω ∧ DQ ω)} ⊆ A ∪ B ∪ C ∪ D ∪ E := by
    intro ω hω
    have hnot : ¬ (G ω ∧ Y ω ∧ LQ ω ∧ SDF ω ∧ DQ ω) := hω
    by_cases hGω : G ω
    · have hrest : ¬ (Y ω ∧ LQ ω ∧ SDF ω ∧ DQ ω) := by
        intro hrest
        apply hnot
        exact ⟨hGω, hrest⟩
      simp only [not_and_or] at hrest
      rcases hrest with (hY' | hLQ' | hSDF' | hDQ')
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hGω, hY'⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hGω, hLQ'⟩))
      · exact Or.inl (Or.inr ⟨hGω, hSDF'⟩)
      · exact Or.inr ⟨hGω, hDQ'⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl hGω)))
  have h_meas : μ {ω | ¬ (G ω ∧ Y ω ∧ LQ ω ∧ SDF ω ∧ DQ ω)} ≤ μ (A ∪ B ∪ C ∪ D ∪ E) :=
    measure_mono h_sub
  have h_union : μ (A ∪ B ∪ C ∪ D ∪ E) ≤ μ A + μ B + μ C + μ D + μ E := by
    have hAB := measure_union_le (μ := μ) A B
    have hABC := measure_union_le (μ := μ) (A ∪ B) C
    have hABCD := measure_union_le (μ := μ) (A ∪ B ∪ C) D
    have hABCDE := measure_union_le (μ := μ) (A ∪ B ∪ C ∪ D) E
    calc
      μ (A ∪ B ∪ C ∪ D ∪ E) ≤ μ (A ∪ B ∪ C ∪ D) + μ E := hABCDE
      _ ≤ (μ (A ∪ B ∪ C) + μ D) + μ E :=
        add_le_add_left hABCD (μ E)
      _ ≤ ((μ (A ∪ B) + μ C) + μ D) + μ E :=
        add_le_add_left (add_le_add_left hABC (μ D)) (μ E)
      _ ≤ (((μ A + μ B) + μ C) + μ D) + μ E :=
        add_le_add_left (add_le_add_left (add_le_add_left hAB (μ C)) (μ D)) (μ E)
  have hpos1 : 0 ≤ (3/7 : ℝ) * δe := mul_nonneg (by norm_num) hδe
  have hpos2 : 0 ≤ (1/7 : ℝ) * δe := mul_nonneg (by norm_num) hδe
  have hpos3 : 0 ≤ (1/21 : ℝ) * δe := mul_nonneg (by norm_num) hδe
  have hpos4 : 0 ≤ (1/7 : ℝ) * δe := mul_nonneg (by norm_num) hδe
  have hpos5 : 0 ≤ (1/8 : ℝ) * δe := mul_nonneg (by norm_num) hδe
  have h_sum : ENNReal.ofReal (3 / 7 * δe) + ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 21 * δe) +
      ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) = ENNReal.ofReal (149 / 168 * δe) := by
    calc
      ENNReal.ofReal (3 / 7 * δe) + ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 21 * δe) +
          ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) =
          ENNReal.ofReal ((3/7 * δe) + (1/7 * δe)) + ENNReal.ofReal (1 / 21 * δe) +
          ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) := by
        rw [← ENNReal.ofReal_add hpos1 hpos2]
      _ = ENNReal.ofReal ((3/7 + 1/7) * δe) + ENNReal.ofReal (1 / 21 * δe) +
          ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) := by ring
      _ = ENNReal.ofReal (4/7 * δe) + ENNReal.ofReal (1 / 21 * δe) +
          ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) := by norm_num
      _ = ENNReal.ofReal ((4/7 * δe) + (1/21 * δe)) + ENNReal.ofReal (1 / 7 * δe) +
          ENNReal.ofReal (1 / 8 * δe) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hδe) hpos3]
      _ = ENNReal.ofReal ((4/7 + 1/21) * δe) + ENNReal.ofReal (1 / 7 * δe) +
          ENNReal.ofReal (1 / 8 * δe) := by ring
      _ = ENNReal.ofReal (13/21 * δe) + ENNReal.ofReal (1 / 7 * δe) +
          ENNReal.ofReal (1 / 8 * δe) := by norm_num
      _ = ENNReal.ofReal ((13/21 * δe) + (1/7 * δe)) + ENNReal.ofReal (1 / 8 * δe) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hδe) hpos4]
      _ = ENNReal.ofReal ((13/21 + 1/7) * δe) + ENNReal.ofReal (1 / 8 * δe) := by ring
      _ = ENNReal.ofReal (16/21 * δe) + ENNReal.ofReal (1 / 8 * δe) := by norm_num
      _ = ENNReal.ofReal ((16/21 * δe) + (1/8 * δe)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hδe) hpos5]
      _ = ENNReal.ofReal ((16/21 + 1/8) * δe) := by ring
      _ = ENNReal.ofReal (149/168 * δe) := by norm_num
  have h_add := add_le_add hG (add_le_add hY (add_le_add hLQ (add_le_add hSDF hDQ)))
  have h_add' : μ A + μ B + μ C + μ D + μ E ≤
      ENNReal.ofReal (3 / 7 * δe) + ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 21 * δe) +
      ENNReal.ofReal (1 / 7 * δe) + ENNReal.ofReal (1 / 8 * δe) := by
    simpa [add_assoc] using h_add
  simpa [hA, hB, hC, hD, hE] using
    h_meas.trans (h_union.trans (h_add'.trans (le_of_eq h_sum)))

end AdversarialBco.Bit.Cpl
