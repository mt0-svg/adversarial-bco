/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProbProof

@[expose] public section

/-!
# Lemma SGD-e: projected stochastic descent with a projection exact up to `e` (leaves B1 and B2)

Let `D` be compact convex of diameter at most `Δ`, `h` convex on `D` with a minimiser `xs ∈ D`, `e ≥ 0`, `θ > 0` and
`proj` a map into `D` with `|proj y - z| ≤ |y - z| + e` for every `y` and every `z ∈ D`. For the iterates
`x_{t+1} = proj (x_t - s v_t)` of `sgdIter`, with `E v_t = γ_t + β_t`, `γ_t` a subgradient of `h` at `x_t`,
`|β_t| ≤ β` and `E |v_t|² ≤ G²`:

  `E h(x̄) - h(xs) ≤ Δ²/(2 s N) + (1 + θ) s G²/2 + β Δ + e Δ/s + e² (1 + 1/θ)/(2 s)`.

`sgd_step_e` is the pathwise step (B1); `SgdExpectE` is the statement in expectation, in the form of `SgdExpect`
(PgProb.lean) with the projection exact up to `e` and measurable instead of continuous (B2, from the proof of
`sgd_expect_main`, PgProbProof.lean l.243 to 637, which reads the continuity of the projection only through its
measurability). With `e = 0` and `θ → 0` it is `SgdExpect`.

B1 and B2 are proved (B2 by the proof of `sgd_expect_main`, copied, with the pathwise bound B2a `sgd_pathwise_e`
in place of `sgd_pathwise`). Everything here is proved.

Junk values. The bound divides by `s`, `N`, `θ`, read at `s > 0`, `N ≥ 1`, `θ > 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly

/-- B1: one step of the descent with a projection exact up to `e`. -/
theorem sgd_step_e {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (proj : E → E) (x xs v : E)
    (s e θ Δ : ℝ) (hΔ : ‖x - xs‖ ≤ Δ) (hs : 0 ≤ s) (he : 0 ≤ e) (hθ : 0 < θ)
    (hp : ‖proj (x - s • v) - xs‖ ≤ ‖x - s • v - xs‖ + e) :
    2 * s * ⟪v, x - xs⟫ ≤ ‖x - xs‖ ^ 2 - ‖proj (x - s • v) - xs‖ ^ 2 + (1 + θ) * s ^ 2 * ‖v‖ ^ 2 +
      2 * e * Δ + e ^ 2 * (1 + 1 / θ) := by
  set y := x - s • v with hy
  set p := proj y with hpj
  set A := ‖x - xs‖ with hA
  set B := ‖y - xs‖ with hB
  set n := ‖v‖ with hn
  have hy_sub_eq : y - xs = (x - xs) - s • v := by
    dsimp [y]
    abel
  have h_norm_s : ‖s‖ = s := by
    simpa using abs_of_nonneg hs
  have hB_sq : B ^ 2 = A ^ 2 - 2 * s * ⟪v, x - xs⟫ + s ^ 2 * n ^ 2 := by
    dsimp [B, A, n]
    rw [hy_sub_eq]
    rw [norm_sub_sq_real]
    rw [inner_smul_right]
    rw [norm_smul]
    rw [h_norm_s]
    rw [real_inner_comm]
    ring
  have hB_le_A_sn : B ≤ A + s * n := by
    dsimp [B, A, n, y]
    calc
      ‖(x - s • v) - xs‖ = ‖(x - xs) - s • v‖ := by abel
      _ ≤ ‖x - xs‖ + ‖s • v‖ := norm_sub_le _ _
      _ = ‖x - xs‖ + ‖s‖ * ‖v‖ := by rw [norm_smul]
      _ = ‖x - xs‖ + s * ‖v‖ := by rw [h_norm_s]
  have hB_le_Δ_sn : B ≤ Δ + s * n := by
    linarith
  have hp_sq_le : ‖p - xs‖ ^ 2 ≤ (B + e) ^ 2 := by
    have h_nonneg : 0 ≤ ‖p - xs‖ := norm_nonneg _
    have h_le : ‖p - xs‖ ≤ B + e := by
      dsimp [p, y]
      simpa [B] using hp
    nlinarith
  have h_amgm_poly : 2 * θ * e * s * n ≤ θ ^ 2 * s ^ 2 * n ^ 2 + e ^ 2 := by
    have h_nonneg_sq : 0 ≤ (θ * s * n - e) ^ 2 := pow_two_nonneg _
    nlinarith
  have h_main : 2 * s * ⟪v, x - xs⟫ ≤ A ^ 2 - ‖p - xs‖ ^ 2 + (1 + θ) * s ^ 2 * n ^ 2 + 2 * e * Δ + e ^ 2 * (1 + 1 / θ) := by
    have hθ_ne : θ ≠ 0 := by linarith
    field_simp [hθ_ne]
    have h_eq : 2 * s * ⟪v, x - xs⟫ = A ^ 2 - B ^ 2 + s ^ 2 * n ^ 2 := by linarith
    rw [h_eq]
    have h_sq_expand : ‖p - xs‖ ^ 2 ≤ B ^ 2 + 2 * e * B + e ^ 2 := by
      nlinarith
    have h_B_bound : 2 * θ * e * B ≤ 2 * θ * e * (Δ + s * n) := by
      apply mul_le_mul_of_nonneg_left hB_le_Δ_sn
      positivity
    have h_amgm_goal : 2 * θ * e * s * n ≤ θ ^ 2 * s ^ 2 * n ^ 2 + e ^ 2 := h_amgm_poly
    nlinarith
  simpa [A, n, p, y] using h_main

/-- B2a: the pathwise bound, summed over the first `N` steps. -/
theorem sgd_pathwise_e {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (xs : E) (s e θ Δ : ℝ) (hs : 0 < s) (he : 0 ≤ e) (hθ : 0 < θ) (x v : ℕ → E)
    (hx : ∀ t, x (t + 1) = proj (x t - s • v t)) (hΔ : ∀ t, ‖x t - xs‖ ≤ Δ)
    (hp : ∀ t, ‖proj (x t - s • v t) - xs‖ ≤ ‖x t - s • v t - xs‖ + e) (N : ℕ) :
    ∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫ ≤
      (Δ ^ 2 / (2 * s) + N * (e * Δ / s + e ^ 2 * (1 + 1 / θ) / (2 * s))) +
        (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v t‖ ^ 2 := by
  have hpos2s : 0 < 2 * s := by nlinarith
  have h_nonneg_Δ : 0 ≤ Δ := by
    have h0 := hΔ 0
    have hnorm : 0 ≤ ‖x 0 - xs‖ := norm_nonneg _
    nlinarith
  set c := 2 * e * Δ + e ^ 2 * (1 + 1 / θ) with hc_def
  have h_step : ∀ t, 2 * s * ⟪v t, x t - xs⟫ ≤ ‖x t - xs‖ ^ 2 - ‖x (t + 1) - xs‖ ^ 2 + (1 + θ) * s ^ 2 * ‖v t‖ ^ 2 + c := by
    intro t
    have h := AdversarialBco.Conj1Arith.sgd_step_e proj (x t) xs (v t) s e θ Δ (hΔ t) hs.le he hθ (hp t)
    simpa [hx t, hc_def, add_assoc] using h
  have h_summed : 2 * s * (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) ≤
      ‖x 0 - xs‖ ^ 2 - ‖x N - xs‖ ^ 2 + (1 + θ) * s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + (N : ℝ) * c := by
    induction' N with N ih
    · simp [hc_def]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep := h_step N
      have h_add := add_le_add ih hstep
      -- h_add: 2*s*(∑ range N) + 2*s*⟪v N, x N - xs⟫ ≤ ‖x 0 - xs‖² - ‖x N - xs‖² + (1+θ)*s²*(∑ range N) + N*c + (‖x N - xs‖² - ‖x (N+1) - xs‖² + (1+θ)*s²*‖v N‖² + c)
      -- goal:  2*s*((∑ range N) + ⟪v N, x N - xs⟫) ≤ ‖x 0 - xs‖² - ‖x (N+1) - xs‖² + (1+θ)*s²*((∑ range N) + ‖v N‖²) + ((N:ℝ)+1)*c
      simpa [Nat.cast_succ] using
        calc
          2 * s * ((∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) + ⟪v N, x N - xs⟫)
              = 2 * s * (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) + 2 * s * ⟪v N, x N - xs⟫ := by ring
          _ ≤ ‖x 0 - xs‖ ^ 2 - ‖x N - xs‖ ^ 2 + (1 + θ) * s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + (N : ℝ) * c +
              (‖x N - xs‖ ^ 2 - ‖x (N + 1) - xs‖ ^ 2 + (1 + θ) * s ^ 2 * ‖v N‖ ^ 2 + c) := h_add
          _ = ‖x 0 - xs‖ ^ 2 - ‖x (N + 1) - xs‖ ^ 2 + (1 + θ) * s ^ 2 * ((∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + ‖v N‖ ^ 2) + ((N : ℝ) + 1) * c := by ring
  have h_bound : 2 * s * (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) ≤
      Δ ^ 2 + (1 + θ) * s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + (N : ℝ) * c := by
    have h_sq : ‖x 0 - xs‖ ^ 2 ≤ Δ ^ 2 := by
      have h0 := hΔ 0
      have h_nonneg_x0 : 0 ≤ ‖x 0 - xs‖ := norm_nonneg _
      nlinarith
    have h_nonneg_xN : 0 ≤ ‖x N - xs‖ ^ 2 := pow_two_nonneg _
    nlinarith
  have h_div : (∑ t ∈ Finset.range N, ⟪v t, x t - xs⟫) ≤
      (Δ ^ 2 + (1 + θ) * s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + (N : ℝ) * c) / (2 * s) := by
    apply (le_div_iff₀ hpos2s).mpr
    simpa [mul_comm] using h_bound
  have h_eq : (Δ ^ 2 + (1 + θ) * s ^ 2 * (∑ t ∈ Finset.range N, ‖v t‖ ^ 2) + (N : ℝ) * c) / (2 * s) =
      (Δ ^ 2 / (2 * s) + N * (e * Δ / s + e ^ 2 * (1 + 1 / θ) / (2 * s))) +
        (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v t‖ ^ 2 := by
    rw [hc_def]
    field_simp [hs.ne.symm, hθ.ne.symm]
    ring
  exact h_div.trans h_eq.le

/-- Lemma SGD-e, in expectation over independent samples. -/
def SgdExpectE : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    (D : Set E) (proj : E → E) (h : E → ℝ) (γ : E → E) (V : E → G → E) (xs x1 : E) (Δ s G2 β e θ : ℝ) (N : ℕ),
    IsCompact D → Convex ℝ D → ContinuousOn h D → Measurable proj → (∀ y, proj y ∈ D) →
    (∀ y, ∀ z ∈ D, ‖proj y - z‖ ≤ ‖y - z‖ + e) → Measurable (Function.uncurry V) → x1 ∈ D → xs ∈ D →
    (∀ y ∈ D, h xs ≤ h y) → (∀ y ∈ D, ∀ z ∈ D, ‖y - z‖ ≤ Δ) →
    (∀ x ∈ D, ∀ y ∈ D, h x + ⟪γ x, y - x⟫ ≤ h y) →
    (∀ x ∈ D, Integrable (V x) ν ∧ Integrable (fun g => ‖V x g‖ ^ 2) ν ∧ ‖∫ g, V x g ∂ν - γ x‖ ≤ β ∧
      ∫ g, ‖V x g‖ ^ 2 ∂ν ≤ G2) →
    0 < s → 1 ≤ N → 0 ≤ e → 0 < θ →
    ∫ ω, h (sgdAvg proj V s x1 N ω) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      h xs + Δ ^ 2 / (2 * s * N) + (1 + θ) * s * G2 / 2 + β * Δ + e * Δ / s + e ^ 2 * (1 + 1 / θ) / (2 * s)

/-- B2. -/
theorem sgdExpectE : SgdExpectE := by
  intro E _ _ _ _ _ G _ ν _ D proj h γ V xs x1 Δ s G2 β e θ N hDc hDv hh hpm hpD hpn hV hx1 hxs hmin hΔ hγ hVm hs hN he hθ
  set P := Measure.infinitePi (fun _ : ℕ => ν) with hP
  have hx0 : ‖x1 - xs‖ ≤ Δ := hΔ x1 hx1 xs hxs
  set x := fun (ω : ℕ → G) (t : ℕ) => AdversarialBco.Poly.sgdIter proj V s x1 ω t with hx_def
  set v := fun (ω : ℕ → G) (t : ℕ) => V (x ω t) (ω t) with hv_def
  have hx_succ : ∀ ω t, x ω (t + 1) = proj (x ω t - s • v ω t) := by
    intro ω t; dsimp [x, v, AdversarialBco.Poly.sgdIter]
  have hx_mem : ∀ ω t, x ω t ∈ D := by
    intro ω t; exact AdversarialBco.Poly.sgd_iter_mem D proj V s x1 hpD hx1 ω t
  have hproj_meas : Measurable proj := hpm
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
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Δ ^ 2 / (2 * s) + N * (e * Δ / s + e ^ 2 * (1 + 1 / θ) / (2 * s)) := ⟨_, rfl⟩
  have h_pathwise : ∀ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ≤
      A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 := by
    intro ω
    rw [hA]
    exact sgd_pathwise_e proj xs s e θ Δ hs he hθ (x ω) (v ω) (hx_succ ω)
      (fun t => hΔ _ (hx_mem ω t) xs hxs) (fun t => hpn _ xs hxs) N
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
      A + (1 + θ) * s / 2 * (∫ ω, ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) := by
    have h_left_int : Integrable (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫) P :=
      integrable_finsetSum _ (fun t ht => h_inner_int t)
    have h_sum_int : Integrable (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
      integrable_finsetSum _ (fun t ht => h_norm_sq_int t)
    have h_right_int : Integrable (fun ω : ℕ → G => A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P := by
      have h_const : Integrable (fun _ : ℕ → G => A) P := by
        have : IsFiniteMeasure P := by rw [hP]; infer_instance
        exact integrable_const _
      have h_scaled : Integrable (fun ω : ℕ → G => (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
        Integrable.const_mul h_sum_int ((1 + θ) * s / 2)
      exact Integrable.add h_const h_scaled
    have h_int_mono : (∫ ω, ∑ t ∈ Finset.range N, ⟪v ω t, x ω t - xs⟫ ∂P) ≤
        (∫ ω, A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) :=
      integral_mono h_left_int h_right_int (h_pathwise ·)
    -- Now pull out the constant from the right integral
    have h_right_eq : (∫ ω, A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) =
        A + (1 + θ) * s / 2 * (∫ ω, ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2 ∂P) := by
      have h_int1 : Integrable (fun _ : ℕ → G => A) P := by
        have : IsFiniteMeasure P := by rw [hP]; infer_instance
        exact integrable_const _
      have h_int2 : Integrable (fun ω : ℕ → G => (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2) P :=
        Integrable.const_mul h_sum_int ((1 + θ) * s / 2)
      rw [integral_add h_int1 h_int2, integral_const]
      rw [integral_const_mul ((1 + θ) * s / 2) (fun ω : ℕ → G => ∑ t ∈ Finset.range N, ‖v ω t‖ ^ 2)]
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
      A + (1 + θ) * s / 2 * (N * G2) := by
    calc ∑ t ∈ Finset.range N, ((∫ ω, h (x ω t) ∂P) - h xs - β * Δ)
        ≤ ∑ t ∈ Finset.range N, ∫ ω, ⟪v ω t, x ω t - xs⟫ ∂P :=
          Finset.sum_le_sum fun t _ => h_inner_bound t
      _ ≤ A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, ∫ ω, ‖v ω t‖ ^ 2 ∂P := h_pathwise_int
      _ ≤ A + (1 + θ) * s / 2 * ∑ t ∈ Finset.range N, G2 := by
          have hs2 : 0 ≤ (1 + θ) * s / 2 := div_nonneg (mul_nonneg (by linarith) hs.le) (by norm_num)
          gcongr with t ht
          exact h_norm_sq_bound t
      _ = A + (1 + θ) * s / 2 * (N * G2) := by simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h_sum_expand : ∑ t ∈ Finset.range N, ((∫ ω, h (x ω t) ∂P) - h xs - β * Δ) =
      (∑ t ∈ Finset.range N, ∫ ω, h (x ω t) ∂P) - N * (h xs + β * Δ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have h_avg_bound : (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ ω, h (x ω t) ∂P ≤
      h xs + Δ ^ 2 / (2 * s * N) + (1 + θ) * s * G2 / 2 + β * Δ + e * Δ / s + e ^ 2 * (1 + 1 / θ) / (2 * s) := by
    rw [h_sum_expand] at h_sum_bound
    rw [inv_mul_le_iff₀ hNpos]
    have hexp : (N : ℝ) * (h xs + Δ ^ 2 / (2 * s * N) + (1 + θ) * s * G2 / 2 + β * Δ + e * Δ / s +
        e ^ 2 * (1 + 1 / θ) / (2 * s)) = N * (h xs + β * Δ) + A + (1 + θ) * s / 2 * (N * G2) := by
      rw [hA]
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

end AdversarialBco.Conj1Arith
