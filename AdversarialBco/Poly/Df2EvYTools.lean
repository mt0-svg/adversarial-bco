/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvGTools
public import AdversarialBco.Poly.FreedmanProof

@[expose] public section

/-!
# The leaves of the budget of Y

Self-contained facts for the budget of the event Y: the conditional second moment of the observation given the
past and the draw; the conditional variance of a bounded nonnegative variable; Freedman's inequality for bounded
nonnegative increments, uniform over the horizons (a hitting time makes the union over the horizons free); the
second moment of `v = pip - 1` by truncation at `2 L`; the first moment of `v` by Jensen on the extension at the
coefficient `1/ε`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Topology Matrix

namespace AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## Conditional moments -/

/-- `E[P² (a + e)² | H] ≤ 2 P²` for `a ∈ [0, 1]` and `P` bounded and `H`-measurable, `E[e | H] = 0` and
`E[exp(e²) | H] ≤ 2`. -/
theorem condExp_obs_sq_le {Ω : Type} (H : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] (μ : Measure[m0] Ω)
    [IsProbabilityMeasure μ] (hH : H ≤ m0) (a P : Ω → ℝ) (ha : StronglyMeasurable[H] a)
    (ha01 : ∀ ω, a ω ∈ Set.Icc (0 : ℝ) 1) (hP : StronglyMeasurable[H] P) (k : ℝ) (hPk : ∀ ω, |P ω| ≤ k)
    (e : Ω → ℝ) (he : Measurable[m0] e) (hint : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hmean : μ[e | H] =ᵐ[μ] 0) (hexp : μ[fun ω => Real.exp (e ω ^ 2) | H] ≤ᵐ[μ] fun _ => 2) :
    μ[fun ω => P ω ^ 2 * (a ω + e ω) ^ 2 | H] ≤ᵐ[μ] fun ω => 2 * P ω ^ 2 := by
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => (ha01 ω).1
  have ha1 : ∀ ω, a ω ≤ 1 := fun ω => (ha01 ω).2
  have ha_sq_bound : ∀ ω, a ω ^ 2 ≤ 1 := by
    intro ω; nlinarith [ha0 ω, ha1 ω]
  have hP_sq_bound_abs : ∀ ω, P ω ^ 2 ≤ k ^ 2 := by
    intro ω
    have h_abs : |P ω| ≤ k := hPk ω
    rcases abs_le.mp h_abs with ⟨h_low, h_high⟩
    nlinarith
  -- e is integrable: |e| ≤ 1 + e² ≤ exp(e²)
  have he_int : Integrable e μ := by
    have h_ae : AEStronglyMeasurable e μ := he.aestronglyMeasurable
    have h_bound : ∀ᵐ ω ∂μ, ‖e ω‖ ≤ ‖Real.exp (e ω ^ 2)‖ := by
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have h_exp_nonneg : 0 ≤ Real.exp (e ω ^ 2) := le_of_lt (Real.exp_pos _)
      rw [abs_of_nonneg h_exp_nonneg]
      have h_abs_le_one_plus_sq : |e ω| ≤ 1 + e ω ^ 2 := by
        by_cases hle : |e ω| ≤ 1
        · nlinarith
        · have hge : 1 ≤ |e ω| := by nlinarith
          have h_sq_ge_abs : |e ω| ≤ (e ω) ^ 2 := by
            have h_abs_sq_eq : (e ω) ^ 2 = |e ω| ^ 2 := by
              simpa [sq] using abs_mul_abs_self (e ω)
            rw [h_abs_sq_eq]
            nlinarith
          nlinarith
      have h_one_plus_sq_le_exp : 1 + e ω ^ 2 ≤ Real.exp (e ω ^ 2) := by
        have h := Real.add_one_le_exp (e ω ^ 2)
        nlinarith
      nlinarith
    exact hint.mono h_ae h_bound
  have he_sq_int : Integrable (fun ω => e ω ^ 2) μ := by
    have h_ae : AEStronglyMeasurable (fun ω => e ω ^ 2) μ := by
      have h := he.aestronglyMeasurable (μ := μ)
      have h_mul : AEStronglyMeasurable (e * e) μ := h.mul h
      convert h_mul using 1
      ext ω; simp [sq]
    have h_bound : ∀ᵐ ω ∂μ, ‖e ω ^ 2‖ ≤ ‖Real.exp (e ω ^ 2)‖ := by
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have h_sq_nonneg : 0 ≤ e ω ^ 2 := pow_two_nonneg _
      have h_exp_nonneg : 0 ≤ Real.exp (e ω ^ 2) := le_of_lt (Real.exp_pos _)
      rw [abs_of_nonneg h_sq_nonneg, abs_of_nonneg h_exp_nonneg]
      have h := Real.add_one_le_exp (e ω ^ 2)
      nlinarith
    exact hint.mono h_ae h_bound
  -- P² is H-strongly measurable
  have hP_sq : StronglyMeasurable[H] (fun ω => P ω ^ 2) := hP.pow 2
  have hP_sq_ae : AEStronglyMeasurable (fun ω => P ω ^ 2) μ :=
    (hP_sq.mono hH).aestronglyMeasurable
  have hP_sq_bound : ∀ᵐ ω ∂μ, ‖P ω ^ 2‖ ≤ k ^ 2 := by
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_two_nonneg _)]
    exact hP_sq_bound_abs ω
  -- P² a² is integrable (bounded)
  have hP_sq_a_sq_int : Integrable (fun ω => P ω ^ 2 * a ω ^ 2) μ := by
    have h_bound : ∀ᵐ ω ∂μ, ‖P ω ^ 2 * a ω ^ 2‖ ≤ k ^ 2 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have h_nonneg : 0 ≤ P ω ^ 2 * a ω ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      nlinarith [ha_sq_bound ω, hP_sq_bound_abs ω]
    have h_const : Integrable (fun _ => (k ^ 2 : ℝ)) μ := integrable_const _
    have h_bound' : ∀ᵐ ω ∂μ, ‖P ω ^ 2 * a ω ^ 2‖ ≤ ‖(fun _ => (k ^ 2 : ℝ)) ω‖ := by
      filter_upwards [h_bound] with ω hω
      simpa using hω
    have h_ae_prod : AEStronglyMeasurable (fun ω => P ω ^ 2 * a ω ^ 2) μ := by
      have h_ae_a_sq : AEStronglyMeasurable (fun ω => a ω ^ 2) μ := by
        have h := (ha.mono hH).aestronglyMeasurable (μ := μ)
        have h_mul : AEStronglyMeasurable (a * a) μ := h.mul h
        convert h_mul using 1
        ext ω; simp [sq]
      have h_mul' : AEStronglyMeasurable ((fun ω => P ω ^ 2) * (fun ω => a ω ^ 2)) μ :=
        hP_sq_ae.mul h_ae_a_sq
      -- h_mul' : AEStronglyMeasurable (P^2 * a^2) μ, but the goal is AEStronglyMeasurable (fun ω => P ω ^ 2 * a ω ^ 2) μ
      -- These are definitionally equal via η-expansion
      exact h_mul'
    exact h_const.mono h_ae_prod h_bound'
  -- 2 * P² * a is H-strongly measurable and bounded
  have h2P_sq_a : StronglyMeasurable[H] (fun ω => 2 * P ω ^ 2 * a ω) := by
    have : StronglyMeasurable[H] (fun ω => (2 : ℝ) • (P ω ^ 2 * a ω)) :=
      (hP_sq.mul ha).const_smul (2 : ℝ)
    simpa [smul_eq_mul, mul_assoc] using this
  have h2P_sq_a_ae : AEStronglyMeasurable (fun ω => 2 * P ω ^ 2 * a ω) μ :=
    (h2P_sq_a.mono hH).aestronglyMeasurable
  have h2P_sq_a_bound : ∀ᵐ ω ∂μ, ‖(fun ω => 2 * P ω ^ 2 * a ω) ω‖ ≤ 2 * k ^ 2 := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h_nonneg : 0 ≤ 2 * P ω ^ 2 * a ω := by
      have hP_sq_nonneg : 0 ≤ P ω ^ 2 := pow_two_nonneg _
      have ha_nonneg : 0 ≤ a ω := ha0 ω
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    nlinarith [ha1 ω, hP_sq_bound_abs ω]
  have h2P_sq_a_int : Integrable (fun ω => 2 * P ω ^ 2 * a ω) μ := by
    have h_const : Integrable (fun _ => (2 * k ^ 2 : ℝ)) μ := integrable_const _
    have h_bound' : ∀ᵐ ω ∂μ, ‖(fun ω => 2 * P ω ^ 2 * a ω) ω‖ ≤ ‖(fun _ => (2 * k ^ 2 : ℝ)) ω‖ := by
      filter_upwards [h2P_sq_a_bound] with ω hω
      simpa using hω
    exact h_const.mono h2P_sq_a_ae h_bound'
  -- 2 * P² * a * e is integrable (bounded * integrable)
  have h2P_sq_a_e_int : Integrable (fun ω => 2 * P ω ^ 2 * a ω * e ω) μ :=
    he_int.bdd_mul h2P_sq_a_ae h2P_sq_a_bound
  -- P² * e² is integrable (bounded * integrable)
  have hP_sq_e_sq_int : Integrable (fun ω => P ω ^ 2 * e ω ^ 2) μ :=
    he_sq_int.bdd_mul hP_sq_ae hP_sq_bound
  -- Expand the integrand: P² (a + e)² = P² a² + 2 P² a e + P² e²
  have h_expand : (fun ω => P ω ^ 2 * (a ω + e ω) ^ 2) = (fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω + P ω ^ 2 * e ω ^ 2) := by
    ext ω; ring
  rw [h_expand]
  -- Compute conditional expectation of the sum using linearity
  have h_sum_int : Integrable (fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω) μ :=
    hP_sq_a_sq_int.add h2P_sq_a_e_int
  have h_cond_exp_split1 : μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω + P ω ^ 2 * e ω ^ 2 | H]
      =ᵐ[μ] μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω | H] + μ[fun ω => P ω ^ 2 * e ω ^ 2 | H] :=
    condExp_add h_sum_int hP_sq_e_sq_int H
  have h_cond_exp_split2 : μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω | H]
      =ᵐ[μ] μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] + μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H] :=
    condExp_add hP_sq_a_sq_int h2P_sq_a_e_int H
  -- Combine the two splits using a direct pointwise argument
  have h_cond_exp_total : μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω + P ω ^ 2 * e ω ^ 2 | H]
      =ᵐ[μ] μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] + μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H] + μ[fun ω => P ω ^ 2 * e ω ^ 2 | H] := by
    calc
      μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω + P ω ^ 2 * e ω ^ 2 | H]
          =ᵐ[μ] (μ[fun ω => P ω ^ 2 * a ω ^ 2 + 2 * P ω ^ 2 * a ω * e ω | H] + μ[fun ω => P ω ^ 2 * e ω ^ 2 | H]) := h_cond_exp_split1
      _ =ᵐ[μ] ((μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] + μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H]) + μ[fun ω => P ω ^ 2 * e ω ^ 2 | H]) :=
        h_cond_exp_split2.add (by rfl)
      _ =ᵐ[μ] μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] + μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H] + μ[fun ω => P ω ^ 2 * e ω ^ 2 | H] := by rw [add_assoc]
  -- μ[P² a² | H] = P² a² (since P² a² is H-measurable)
  have h_cond_P_sq_a_sq_eq : μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] = fun ω => P ω ^ 2 * a ω ^ 2 :=
    condExp_of_stronglyMeasurable hH (hP_sq.mul (ha.pow 2)) hP_sq_a_sq_int
  have h_cond_P_sq_a_sq : μ[fun ω => P ω ^ 2 * a ω ^ 2 | H] =ᵐ[μ] fun ω => P ω ^ 2 * a ω ^ 2 := by
    rw [h_cond_P_sq_a_sq_eq]
  -- μ[2 P² a e | H] = (2 P² a) * μ[e | H] (pull-out), then = 0 by hmean
  have h_cond_2P_sq_a_e : μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H]
      =ᵐ[μ] fun ω => (2 * P ω ^ 2 * a ω) * μ[e | H] ω :=
    condExp_mul_of_stronglyMeasurable_left h2P_sq_a h2P_sq_a_e_int he_int
  have h_cond_2P_sq_a_e_zero : μ[fun ω => 2 * P ω ^ 2 * a ω * e ω | H] =ᵐ[μ] 0 := by
    filter_upwards [h_cond_2P_sq_a_e, hmean] with ω hω1 hω2
    rw [hω1, hω2]
    simp
  -- μ[P² e² | H] = P² * μ[e² | H] (pull-out)
  have h_cond_P_sq_e_sq : μ[fun ω => P ω ^ 2 * e ω ^ 2 | H]
      =ᵐ[μ] fun ω => (P ω ^ 2) * μ[fun ω => e ω ^ 2 | H] ω :=
    condExp_mul_of_stronglyMeasurable_left hP_sq hP_sq_e_sq_int he_sq_int
  -- Bound μ[e² | H] ≤ 1 using hexp
  have h_e_sq_bound : μ[fun ω => e ω ^ 2 | H] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h_e_sq_le_exp_sub_one : (fun ω => e ω ^ 2) ≤ᵐ[μ] fun ω => Real.exp (e ω ^ 2) - 1 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      have h := Real.add_one_le_exp (e ω ^ 2)
      nlinarith
    have h_exp_sub_one_int : Integrable (fun ω => Real.exp (e ω ^ 2) - 1) μ :=
      hint.sub (integrable_const 1)
    have h_bound_cond : μ[fun ω => e ω ^ 2 | H] ≤ᵐ[μ] μ[fun ω => Real.exp (e ω ^ 2) - 1 | H] :=
      condExp_mono he_sq_int h_exp_sub_one_int h_e_sq_le_exp_sub_one
    have h_cond_sub_eq : μ[fun ω => Real.exp (e ω ^ 2) - 1 | H] =ᵐ[μ] μ[fun ω => Real.exp (e ω ^ 2) | H] - μ[fun _ => (1 : ℝ) | H] :=
      condExp_sub hint (integrable_const 1) H
    have h_cond_const_eq : μ[fun _ => (1 : ℝ) | H] = fun _ => (1 : ℝ) :=
      condExp_const hH (1 : ℝ)
    have h_cond_const : μ[fun _ => (1 : ℝ) | H] =ᵐ[μ] fun _ => (1 : ℝ) := by
      rw [h_cond_const_eq]
    have h_cond_sub_bound : μ[fun ω => Real.exp (e ω ^ 2) - 1 | H] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [h_cond_sub_eq, h_cond_const, hexp] with ω hω1 hω2 hω3
      have h_eq : (μ[fun ω => Real.exp (e ω ^ 2) | H] - μ[fun _ => (1 : ℝ) | H]) ω =
          μ[fun ω => Real.exp (e ω ^ 2) | H] ω - μ[fun _ => (1 : ℝ) | H] ω := rfl
      rw [hω1, h_eq, hω2]
      linarith
    filter_upwards [h_bound_cond, h_cond_sub_bound] with ω hω1 hω2
    linarith
  -- Combine everything
  filter_upwards [h_cond_exp_total, h_cond_P_sq_a_sq, h_cond_2P_sq_a_e_zero, h_cond_P_sq_e_sq, h_e_sq_bound] with ω hω1 hω2 hω3 hω4 hω5
  rw [hω1]
  -- Expand the sum: (A + B + C) ω = A ω + B ω + C ω
  simp [Pi.add_apply, hω2, hω3, hω4]
  have hP_sq_nonneg : 0 ≤ P ω ^ 2 := pow_two_nonneg _
  nlinarith [ha_sq_bound ω, hω5]

/-- The conditional variance of `0 ≤ Z ≤ B` is at most `B E[Z | H]`. -/
theorem condExp_centered_sq_le {Ω : Type} (H : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] (μ : Measure[m0] Ω)
    [IsProbabilityMeasure μ] (hH : H ≤ m0) (Z : Ω → ℝ) (hZ : Measurable[m0] Z) (B : ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZB : ∀ ω, Z ω ≤ B) :
    μ[fun ω => (Z ω - μ[Z | H] ω) ^ 2 | H] ≤ᵐ[μ] fun ω => B * μ[Z | H] ω := by
  have hZ_memLp : MemLp Z 2 μ := by
    have hZ_ae : AEStronglyMeasurable Z μ := hZ.aestronglyMeasurable
    have hB_nonneg : 0 ≤ B := by
      have h_nonempty : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure μ
      obtain ⟨ω⟩ := h_nonempty
      have h0 := hZ0 ω
      have hB := hZB ω
      linarith
    have hZ_bound : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ |B| := by
      filter_upwards with ω
      have h0 := hZ0 ω
      have hB := hZB ω
      rw [Real.norm_of_nonneg h0, abs_of_nonneg hB_nonneg]
      exact hB
    exact MemLp.of_bound hZ_ae |B| hZ_bound
  have h_key := condVar_ae_eq_condExp_sq_sub_sq_condExp (μ := μ) (m := H) hH hZ_memLp
  have h_var_eq : μ[fun ω => (Z ω - μ[Z | H] ω) ^ 2 | H] =ᵐ[μ] μ[Z ^ 2 | H] - μ[Z | H] ^ 2 := by
    have : (fun ω => (Z ω - μ[Z | H] ω) ^ 2) = (Z - μ[Z | H]) ^ 2 := by
      ext ω; rfl
    simpa [ProbabilityTheory.condVar, this] using h_key
  have h_sq_le_BZ : Z ^ 2 ≤ᵐ[μ] fun ω => B * Z ω := by
    refine ae_of_all _ (fun ω => ?_)
    have h0 := hZ0 ω
    have hB := hZB ω
    -- (Z ^ 2) ω = Z ω ^ 2, and we need Z ω ^ 2 ≤ B * Z ω
    simpa using (by
      have : Z ω ^ 2 ≤ B * Z ω := by
        nlinarith
      exact this)
  have hZ_sq_integrable : Integrable (Z ^ 2) μ :=
    hZ_memLp.integrable_sq
  have hBZ_integrable : Integrable (fun ω => B * Z ω) μ := by
    have hZ_integrable : Integrable Z μ := hZ_memLp.integrable (show (1 : ℝ≥0∞) ≤ 2 from by norm_num)
    exact hZ_integrable.const_mul' B
  have h_nonneg_condExp_sq : 0 ≤ᵐ[μ] μ[Z | H] ^ 2 := by
    have h_nonneg : 0 ≤ᵐ[μ] μ[Z | H] := condExp_nonneg (ae_of_all _ hZ0) (μ := μ) (m := H)
    filter_upwards [h_nonneg] with ω h
    have : 0 ≤ (μ[Z | H] ω) ^ 2 := by
      have h0 : 0 ≤ μ[Z | H] ω := h
      nlinarith
    simpa using this
  calc
    μ[fun ω => (Z ω - μ[Z | H] ω) ^ 2 | H] =ᵐ[μ] μ[Z ^ 2 | H] - μ[Z | H] ^ 2 := h_var_eq
    _ ≤ᵐ[μ] μ[Z ^ 2 | H] := by
      filter_upwards [h_nonneg_condExp_sq] with ω h
      dsimp at h
      dsimp
      linarith
    _ ≤ᵐ[μ] μ[fun ω => B * Z ω | H] :=
      condExp_mono (m := H) hZ_sq_integrable hBZ_integrable h_sq_le_BZ
    _ =ᵐ[μ] fun ω => B * μ[Z | H] ω :=
      condExp_smul (μ := μ) (m := H) B Z

/-- Freedman's inequality at every horizon `t ≤ N` at once (the one-sided unnormalised form): the event that the
bound fails at some horizon has probability at most `δ`. -/
theorem freedman_unnorm_max {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (α : ℝ) (hα : 0 < α) (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hX : ∀ t, Integrable (X t) μ) (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ)
    (hle : ∀ t, ∀ᵐ ω ∂μ, α * X t ω ≤ 1) (hdrift : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] 0) (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | ∃ t ≤ N, α * predVar μ ℱ X t ω + Real.log (1 / δ) / α ≤ ∑ u ∈ Finset.range t, X u ω} ≤
      ENNReal.ofReal δ := by
  by_cases hδ_one : δ < 1
  · -- Case δ < 1: c = log(1/δ)/α > 0
    have h_one_div_δ_gt_one : 1 < 1 / δ := one_lt_one_div hδ hδ_one
    have h_log_pos : 0 < Real.log (1 / δ) := Real.log_pos h_one_div_δ_gt_one
    have hc_pos : 0 < Real.log (1 / δ) / α := div_pos h_log_pos hα
    set c := Real.log (1 / δ) / α with hc_def
    -- Define S t ω = sum_{u<t} X u ω - α * predVar μ ℱ X t ω
    set S := fun t ω => (∑ u ∈ Finset.range t, X u ω) - α * predVar μ ℱ X t ω with hS_def
    -- Define the stopped process Y u ω = X u ω if no crossing before u, else 0
    -- "no crossing before u" means ∀ t ≤ u, S t ω < c
    set I := fun u ω => ({ω' | ∀ t ≤ u, S t ω' < c}).indicator (fun _ => (1 : ℝ)) ω with hI_def
    set Y := fun u ω => I u ω * X u ω with hY_def
    -- Helper to convert StronglyMeasurable to a given filtration level
    have hX_meas_t : ∀ t u, u < t → StronglyMeasurable[ℱ t] (X u) := by
      intro t u hu_lt_t
      have h_le : ℱ (u + 1) ≤ ℱ t := ℱ.mono (by omega)
      exact (hXm u).mono h_le
    -- Measurability of S t with respect to ℱ t
    have hS_meas : ∀ t, StronglyMeasurable[ℱ t] (S t) := by
      intro t
      dsimp [S]
      have h_sum_meas : StronglyMeasurable[ℱ t] (fun ω => ∑ u ∈ Finset.range t, X u ω) := by
        have h_each : ∀ u ∈ Finset.range t, StronglyMeasurable[ℱ t] (X u) := by
          intro u hu
          have hu_lt_t : u < t := Finset.mem_range.1 hu
          exact hX_meas_t t u hu_lt_t
        -- Use `haveI` to temporarily change the MeasurableSpace instance
        haveI : MeasurableSpace Ω := ℱ t
        simpa using Finset.stronglyMeasurable_fun_sum (Finset.range t) h_each
      have h_predVar_meas : StronglyMeasurable[ℱ t] (predVar μ ℱ X t) := by
        unfold predVar
        have h_each : ∀ u ∈ Finset.range t, StronglyMeasurable[ℱ t] (μ[fun ω => X u ω ^ 2 | ℱ u]) := by
          intro u hu
          have hu_lt_t : u < t := Finset.mem_range.1 hu
          have h_le : ℱ u ≤ ℱ t := ℱ.mono (Nat.le_of_lt hu_lt_t)
          have h_condExp : StronglyMeasurable[ℱ u] (μ[fun ω => X u ω ^ 2 | ℱ u]) :=
            stronglyMeasurable_condExp
          exact h_condExp.mono h_le
        haveI : MeasurableSpace Ω := ℱ t
        simpa using Finset.stronglyMeasurable_fun_sum (Finset.range t) h_each
      exact h_sum_meas.sub (h_predVar_meas.const_mul α)
    -- Measurability of I u
    have hI_meas : ∀ u, StronglyMeasurable[ℱ u] (I u) := by
      intro u
      dsimp [I]
      have h_set : MeasurableSet[ℱ u] {ω | ∀ t ≤ u, S t ω < c} := by
        have h_eq : {ω | ∀ t ≤ u, S t ω < c} = ⋂ t ∈ Finset.range (u + 1), {ω | S t ω < c} := by
          ext ω; simp [Finset.mem_range]
        rw [h_eq]
        haveI : MeasurableSpace Ω := ℱ u
        -- Use MeasurableSet.iInter for the countable intersection
        refine MeasurableSet.iInter (fun t => ?_)
        refine MeasurableSet.iInter (fun ht => ?_)
        have h_le : ℱ t ≤ ℱ u := ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.1 ht))
        have hS_meas_u : StronglyMeasurable[ℱ u] (S t) := (hS_meas t).mono h_le
        exact hS_meas_u.measurableSet_lt stronglyMeasurable_const
      exact stronglyMeasurable_const.indicator h_set
    -- Measurability of Y u
    have hY_meas : ∀ u, StronglyMeasurable[ℱ (u + 1)] (Y u) := by
      intro u
      dsimp [Y]
      have h_le : ℱ u ≤ ℱ (u + 1) := ℱ.mono (by omega)
      have hI_meas' : StronglyMeasurable[ℱ (u + 1)] (I u) := (hI_meas u).mono h_le
      exact hI_meas'.mul (hXm u)
    -- Boundedness of I
    have hI_bound : ∀ u ω, |I u ω| ≤ 1 := by
      intro u ω
      dsimp [I, Set.indicator]
      split
      · simp
      · simp
    have hI_nonneg : ∀ u ω, 0 ≤ I u ω := by
      intro u ω
      dsimp [I, Set.indicator]
      split
      · norm_num
      · norm_num
    -- Integrability of Y u
    have hY_int : ∀ u, Integrable (Y u) μ := by
      intro u
      dsimp [Y]
      have h_bound : ∀ᵐ ω ∂μ, ‖I u ω‖ ≤ (1 : ℝ) := by
        filter_upwards with ω
        simpa [Real.norm_eq_abs] using hI_bound u ω
      have h_ae : AEStronglyMeasurable (I u) μ := by
        obtain ⟨g, hg, hg_eq⟩ := (hI_meas u).aestronglyMeasurable
        exact ⟨g, hg.mono (ℱ.le u), hg_eq⟩
      exact (hX u).bdd_mul h_ae h_bound
    -- Integrability of Y u ^ 2
    have hY2_int : ∀ u, Integrable (fun ω => Y u ω ^ 2) μ := by
      intro u
      dsimp [Y]
      have h_bound : ∀ᵐ ω ∂μ, ‖I u ω‖ ≤ (1 : ℝ) := by
        filter_upwards with ω
        simpa [Real.norm_eq_abs] using hI_bound u ω
      have h_ae : AEStronglyMeasurable (I u) μ := by
        obtain ⟨g, hg, hg_eq⟩ := (hI_meas u).aestronglyMeasurable
        exact ⟨g, hg.mono (ℱ.le u), hg_eq⟩
      have h_int_X2 : Integrable (fun ω => X u ω ^ 2) μ := hX2 u
      -- Y u ^ 2 = I u * X u ^ 2 (since I u ∈ {0,1})
      have h_eq : (fun ω => Y u ω ^ 2) = (fun ω => I u ω * X u ω ^ 2) := by
        ext ω
        dsimp [Y]
        dsimp [I, Set.indicator] at *
        split <;> simp
      rw [h_eq]
      exact h_int_X2.bdd_mul h_ae h_bound
    -- α * Y u ≤ 1 a.e.
    have hY_bound : ∀ u, ∀ᵐ ω ∂μ, α * Y u ω ≤ 1 := by
      intro u
      filter_upwards [hle u] with ω hle_u
      dsimp [Y]
      dsimp [I, Set.indicator] at *
      split
      · -- I u ω = 1
        rename_i h
        simpa [mul_comm, mul_left_comm, mul_assoc] using hle_u
      · -- I u ω = 0
        rename_i h
        simp
    -- Drift condition: μ[Y u | ℱ u] ≤ 0 a.e.
    have hY_drift : ∀ u, μ[Y u | ℱ u] ≤ᵐ[μ] 0 := by
      intro u
      have h_condExp_eq : μ[Y u | ℱ u] =ᵐ[μ] I u * μ[X u | ℱ u] := by
        refine condExp_mul_of_stronglyMeasurable_left (hI_meas u) ?_ (hX u)
        exact hY_int u
      refine h_condExp_eq.le.trans ?_
      have h_nonneg : 0 ≤ᵐ[μ] I u := by
        filter_upwards with ω
        exact hI_nonneg u ω
      have h_drift_u : μ[X u | ℱ u] ≤ᵐ[μ] 0 := hdrift u
      filter_upwards [h_nonneg, h_drift_u] with ω h_nonneg_u h_drift_u
      exact mul_nonpos_of_nonneg_of_nonpos h_nonneg_u h_drift_u
    -- Pull-out equality for conditional expectations (a.e.)
    have h_pullout : ∀ u, μ[Y u ^ 2 | ℱ u] =ᵐ[μ] I u * μ[X u ^ 2 | ℱ u] := by
      intro u
      have hY_sq_eq : Y u ^ 2 = I u * X u ^ 2 := by
        ext ω
        dsimp [Y]
        dsimp [I, Set.indicator] at *
        split <;> simp
      rw [hY_sq_eq]
      refine condExp_mul_of_stronglyMeasurable_left (hI_meas u) ?_ (hX2 u)
      have h_bound : ∀ᵐ ω ∂μ, ‖I u ω‖ ≤ (1 : ℝ) := by
        filter_upwards with ω
        simpa [Real.norm_eq_abs] using hI_bound u ω
      have h_ae : AEStronglyMeasurable (I u) μ := by
        obtain ⟨g, hg, hg_eq⟩ := (hI_meas u).aestronglyMeasurable
        exact ⟨g, hg.mono (ℱ.le u), hg_eq⟩
      exact (hX2 u).bdd_mul h_ae h_bound
    -- Combine pull-out equalities for all u < N using ae_all_iff
    have h_all_pullout : ∀ᵐ ω ∂μ, ∀ u ∈ Finset.range N,
        (μ[Y u ^ 2 | ℱ u]) ω = I u ω * (μ[X u ^ 2 | ℱ u]) ω := by
      have h_all : ∀ᵐ ω ∂μ, ∀ u, (μ[Y u ^ 2 | ℱ u]) ω = I u ω * (μ[X u ^ 2 | ℱ u]) ω := by
        rw [ae_all_iff]
        intro u
        filter_upwards [h_pullout u] with ω h_eq
        exact h_eq
      filter_upwards [h_all] with ω h
      intro u hu
      exact h u
    -- Define the target event A and the freedmanUnnorm event B
    set A := {ω | ∃ t ≤ N, α * predVar μ ℱ X t ω + Real.log (1 / δ) / α ≤ ∑ u ∈ Finset.range t, X u ω} with hA_def
    have hA_eq : A = {ω | ∃ t ≤ N, c ≤ S t ω} := by
      ext ω
      simp [hA_def, hS_def, hc_def]
      constructor
      · rintro ⟨t, ht, h⟩; refine ⟨t, ht, ?_⟩; linarith
      · rintro ⟨t, ht, h⟩; refine ⟨t, ht, ?_⟩; linarith
    rw [hA_eq]
    set B := {ω | α * predVar μ ℱ Y N ω + c ≤ ∑ u ∈ Finset.range N, Y u ω} with hB_def
    -- Define B' which replaces predVar Y with the a.e.-equivalent expression
    set B' := {ω | α * (∑ u ∈ Finset.range N, I u ω * (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω) + c ≤
      ∑ u ∈ Finset.range N, Y u ω} with hB'_def
    -- B' and B are equal a.e.
    have hB'_eq_B_ae : B' =ᵐ[μ] B := by
      filter_upwards [h_all_pullout] with ω h_pullout_all
      dsimp [B, B']
      have h_sum_eq : (∑ u ∈ Finset.range N, (μ[Y u ^ 2 | ℱ u]) ω) =
          (∑ u ∈ Finset.range N, I u ω * (μ[X u ^ 2 | ℱ u]) ω) := by
        simpa using @Finset.sum_congr ℕ ℝ (Finset.range N) (Finset.range N) _
          (fun u => (μ[Y u ^ 2 | ℱ u]) ω) (fun u => I u ω * (μ[X u ^ 2 | ℱ u]) ω)
          rfl (fun u hu => h_pullout_all u hu)
      have h_eq : α * predVar μ ℱ Y N ω + c = α * (∑ u ∈ Finset.range N, I u ω * (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω) + c := by
        unfold predVar
        apply congrArg (fun s => α * s + c)
        exact h_sum_eq
      simp [h_eq]
    -- A ⊆ B' pointwise
    have hA_sub_B' : A ⊆ B' := by
      intro ω hω
      rw [hA_def, Set.mem_setOf_eq] at hω
      obtain ⟨t, ht_le_N, hc_le⟩ := hω
      -- hc_le : c ≤ S t ω
      -- Let t* be the minimal crossing time
      have hc_le' : c ≤ S t ω := by
        dsimp [S, c]
        linarith
      have h_exists : ∃ t', t' ≤ N ∧ c ≤ S t' ω := ⟨t, ht_le_N, hc_le'⟩
      set tstar := Nat.find h_exists with htstar_def
      have htstar_le_N : tstar ≤ N := (Nat.find_spec h_exists).1
      have hc_le_S_tstar : c ≤ S tstar ω := (Nat.find_spec h_exists).2
      have hS_tstar_min : ∀ u < tstar, S u ω < c := by
        intro u hu
        by_contra! hge
        have hu_le_N : u ≤ N := by omega
        have hu_prop : u ≤ N ∧ c ≤ S u ω := ⟨hu_le_N, hge⟩
        have hle' : tstar ≤ u := Nat.find_min' h_exists hu_prop
        omega
      -- Key property: for all u, if u < tstar then S u ω < c, else I u ω = 0
      have hI_lt_tstar : ∀ u, u < tstar → I u ω = 1 := by
        intro u hu
        have h_all_lt : ∀ t' ≤ u, S t' ω < c := by
          intro t' ht'_le_u
          by_cases h_eq : t' = u
          · rw [h_eq]; exact hS_tstar_min u hu
          · have ht'_lt_u : t' < u := by omega
            by_contra! hge
            have ht'_le_N : t' ≤ N := by omega
            have ht'_prop : t' ≤ N ∧ c ≤ S t' ω := ⟨ht'_le_N, hge⟩
            have hle' : tstar ≤ t' := Nat.find_min' h_exists ht'_prop
            omega
        exact Set.indicator_of_mem (s := {ω' | ∀ t ≤ u, S t ω' < c}) h_all_lt _
      have hI_ge_tstar : ∀ u, tstar ≤ u → I u ω = 0 := by
        intro u hu
        have h_not_all_lt : ¬ ∀ t' ≤ u, S t' ω < c := by
          intro h_all
          have h_lt : S tstar ω < c := h_all tstar hu
          linarith [hc_le_S_tstar, h_lt]
        exact Set.indicator_of_notMem (s := {ω' | ∀ t ≤ u, S t ω' < c}) h_not_all_lt _
      -- Compute sums in B'
      have h_sum_Y : ∑ u ∈ Finset.range N, Y u ω = ∑ u ∈ Finset.range tstar, X u ω := by
        dsimp [Y]
        calc
          ∑ u ∈ Finset.range N, (I u ω * X u ω)
              = ∑ u ∈ Finset.range N, (if u < tstar then X u ω else 0) := by
            refine Finset.sum_congr rfl (fun u hu => ?_)
            by_cases hu_lt : u < tstar
            · simp [hI_lt_tstar u hu_lt, hu_lt]
            · have h_le : tstar ≤ u := by omega
              simp [hI_ge_tstar u h_le, not_lt.2 h_le]
          _ = ∑ u ∈ (Finset.range N).filter (· < tstar), X u ω := by rw [Finset.sum_filter]
          _ = ∑ u ∈ Finset.range tstar, X u ω := by
            have h_filter_eq : (Finset.range N).filter (· < tstar) = Finset.range tstar := by
              ext u; simp; omega
            rw [h_filter_eq]
      have h_predVar_sum : (∑ u ∈ Finset.range N, I u ω * (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω) =
          predVar μ ℱ X tstar ω := by
        calc
          (∑ u ∈ Finset.range N, I u ω * (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω)
              = ∑ u ∈ Finset.range N, (if u < tstar then (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω else 0) := by
            refine Finset.sum_congr rfl (fun u hu => ?_)
            by_cases hu_lt : u < tstar
            · simp [hI_lt_tstar u hu_lt, hu_lt]
            · have h_le : tstar ≤ u := by omega
              simp [hI_ge_tstar u h_le, not_lt.2 h_le]
          _ = ∑ u ∈ (Finset.range N).filter (· < tstar), (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω := by
            rw [Finset.sum_filter]
          _ = ∑ u ∈ Finset.range tstar, (μ[fun ω' => X u ω' ^ 2 | ℱ u]) ω := by
            have h_filter_eq : (Finset.range N).filter (· < tstar) = Finset.range tstar := by
              ext u; simp; omega
            rw [h_filter_eq]
          _ = predVar μ ℱ X tstar ω := rfl
      rw [hB'_def, Set.mem_setOf_eq]
      rw [h_predVar_sum, h_sum_Y]
      have hS' : S tstar ω = ∑ u ∈ Finset.range tstar, X u ω - α * predVar μ ℱ X tstar ω := rfl
      linarith
    -- Now conclude using the a.e. equality
    have hμA_le_hμB' : μ A ≤ μ B' := measure_mono hA_sub_B'
    have hμB'_eq_hμB : μ B' = μ B := measure_congr hB'_eq_B_ae
    have h_freedman := freedmanUnnorm μ ℱ Y α hα (hY_meas) (hY_int) (hY2_int) (hY_bound) (hY_drift) N δ hδ
    have h_freedman' : μ B ≤ ENNReal.ofReal δ := by
      simpa [hB_def, hc_def] using h_freedman
    rw [← hA_eq]
    calc
      μ A ≤ μ B' := hμA_le_hμB'
      _ = μ B := hμB'_eq_hμB
      _ ≤ ENNReal.ofReal δ := h_freedman'
  · -- Case δ ≥ 1: trivial
    have hδ_ge_one : 1 ≤ δ := by linarith
    calc
      μ {ω | ∃ t ≤ N, α * predVar μ ℱ X t ω + Real.log (1 / δ) / α ≤ ∑ u ∈ Finset.range t, X u ω}
          ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
      _ ≤ ENNReal.ofReal δ := by
        exact ENNReal.one_le_ofReal.mpr hδ_ge_one

set_option maxHeartbeats 400000 in
/-- Freedman's inequality for increments in `[0, B]`, uniform over the horizons `t ≤ N`: with probability at least
`1 - δ`, `∑_{u < t} Z_u < 2 ∑_{u < t} E[Z_u | 𝒢_u] + B log(1/δ)` for every `t ≤ N`. -/
theorem freedman_uniform {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒢 : Filtration ℕ m0) (Z : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 < B) (hZm : ∀ t, StronglyMeasurable[𝒢 (t + 1)] (Z t))
    (hZ0 : ∀ t ω, 0 ≤ Z t ω) (hZB : ∀ t ω, Z t ω ≤ B) (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | ∃ t ≤ N, 2 * ∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω + B * Real.log (1 / δ) ≤
      ∑ u ∈ Finset.range t, Z u ω} ≤ ENNReal.ofReal δ := by
  set α := 1 / B with hα_def
  have hα_pos : 0 < α := by
    rw [hα_def]
    exact div_pos (by linarith) hB
  set X := fun t ω => Z t ω - (μ[Z t | 𝒢 t]) ω with hX_def
  have hZ_meas : ∀ t, Measurable (Z t) := by
    intro t
    have h_strong : StronglyMeasurable[𝒢 (t + 1)] (Z t) := hZm t
    have h_meas' : Measurable[𝒢 (t + 1)] (Z t) := h_strong.measurable
    have h_le : 𝒢 (t + 1) ≤ m0 := 𝒢.le (t + 1)
    exact h_meas'.mono h_le (by rfl)
  have hXm : ∀ t, StronglyMeasurable[𝒢 (t + 1)] (X t) := by
    intro t
    have hZ : StronglyMeasurable[𝒢 (t + 1)] (Z t) := hZm t
    have h_cond : StronglyMeasurable[𝒢 (t + 1)] (μ[Z t | 𝒢 t]) := by
      have h_cond' : StronglyMeasurable[𝒢 t] (μ[Z t | 𝒢 t]) := stronglyMeasurable_condExp
      have h_le : 𝒢 t ≤ 𝒢 (t + 1) := 𝒢.mono (by omega)
      exact h_cond'.mono h_le
    exact hZ.sub h_cond
  have h_cond_nonneg_ae : ∀ t, 0 ≤ᵐ[μ] (μ[Z t | 𝒢 t]) := by
    intro t
    have h_nonneg_ae : 0 ≤ᵐ[μ] Z t := by
      have h_all : ∀ ω, 0 ≤ Z t ω := hZ0 t
      exact MeasureTheory.ae_of_all μ h_all
    exact condExp_nonneg (m := 𝒢 t) (m₀ := m0) h_nonneg_ae
  have h_cond_le_ae : ∀ t, μ[Z t | 𝒢 t] ≤ᵐ[μ] (fun _ => B) := by
    intro t
    have h_int_Z : Integrable (Z t) μ := by
      have h_meas_ae : AEStronglyMeasurable (Z t) μ := (hZ_meas t).aestronglyMeasurable
      have h_bound : ∀ᵐ ω ∂μ, ‖Z t ω‖ ≤ B := by
        have h_all : ∀ ω, ‖Z t ω‖ ≤ B := by
          intro ω
          rw [Real.norm_of_nonneg (hZ0 t ω)]
          exact hZB t ω
        exact MeasureTheory.ae_of_all μ h_all
      have h_int_const : Integrable (fun _ : Ω => B) μ := integrable_const (c := B)
      exact h_int_const.mono' h_meas_ae h_bound
    have h_int_B : Integrable (fun _ : Ω => B) μ := integrable_const (c := B)
    have h_le : Z t ≤ᵐ[μ] (fun _ => B) := by
      have h_all : ∀ ω, Z t ω ≤ B := hZB t
      exact MeasureTheory.ae_of_all μ h_all
    have h := condExp_mono (m := 𝒢 t) h_int_Z h_int_B h_le
    have h_cond_B : μ[(fun _ : Ω => B) | 𝒢 t] ≤ᵐ[μ] (fun _ => B) := by
      have h_le' : 𝒢 t ≤ m0 := 𝒢.le t
      have h_eq : μ[(fun _ : Ω => B) | 𝒢 t] = (fun _ => B) := condExp_const h_le' B
      have h_ae_eq : μ[(fun _ : Ω => B) | 𝒢 t] =ᵐ[μ] (fun _ => B) := by rw [h_eq]
      exact h_ae_eq.le
    exact h.trans h_cond_B
  have hX_bound_ae : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ B := by
    intro t
    rw [hX_def]
    filter_upwards [h_cond_nonneg_ae t, h_cond_le_ae t] with ω hn hl
    have hn' : 0 ≤ (μ[Z t | 𝒢 t]) ω := by simpa using hn
    have hZω := hZ0 t ω
    have hZω' := hZB t ω
    have h_low : -B ≤ Z t ω - (μ[Z t | 𝒢 t]) ω := by
      linarith
    have h_high : Z t ω - (μ[Z t | 𝒢 t]) ω ≤ B := by
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hX_int : ∀ t, Integrable (X t) μ := by
    intro t
    have hZ_int : Integrable (Z t) μ := by
      have h_meas_ae : AEStronglyMeasurable (Z t) μ := (hZ_meas t).aestronglyMeasurable
      have h_bound : ∀ᵐ ω ∂μ, ‖Z t ω‖ ≤ B := by
        have h_all : ∀ ω, ‖Z t ω‖ ≤ B := by
          intro ω
          rw [Real.norm_of_nonneg (hZ0 t ω)]
          exact hZB t ω
        exact MeasureTheory.ae_of_all μ h_all
      have h_int_const : Integrable (fun _ : Ω => B) μ := integrable_const (c := B)
      exact h_int_const.mono' h_meas_ae h_bound
    have h_cond_int : Integrable (μ[Z t | 𝒢 t]) μ := integrable_condExp
    rw [hX_def]
    exact hZ_int.sub h_cond_int
  have hX2_int : ∀ t, Integrable (fun ω => X t ω ^ 2) μ := by
    intro t
    rw [hX_def]
    have h_ae : AEStronglyMeasurable (fun ω => (Z t ω - (μ[Z t | 𝒢 t]) ω) ^ 2) μ := by
      have hZ_ae : AEStronglyMeasurable (Z t) μ := (hZ_meas t).aestronglyMeasurable
      have h_cond_ae : AEStronglyMeasurable (μ[Z t | 𝒢 t]) μ := by
        have h_meas : Measurable (μ[Z t | 𝒢 t]) := by
          have h_strong : StronglyMeasurable[𝒢 t] (μ[Z t | 𝒢 t]) := stronglyMeasurable_condExp
          have h_meas' : Measurable[𝒢 t] (μ[Z t | 𝒢 t]) := h_strong.measurable
          have h_le : 𝒢 t ≤ m0 := 𝒢.le t
          exact h_meas'.mono h_le (by rfl)
        exact h_meas.aestronglyMeasurable
      have hX_ae : AEStronglyMeasurable (fun ω => Z t ω - (μ[Z t | 𝒢 t]) ω) μ :=
        hZ_ae.sub h_cond_ae
      exact hX_ae.pow 2
    have h_bound : ∀ᵐ ω ∂μ, ‖(Z t ω - (μ[Z t | 𝒢 t]) ω) ^ 2‖ ≤ B ^ 2 := by
      filter_upwards [hX_bound_ae t] with ω h
      have h_abs : |Z t ω - (μ[Z t | 𝒢 t]) ω| ≤ B := h
      have h_sq_nonneg : 0 ≤ (Z t ω - (μ[Z t | 𝒢 t]) ω) ^ 2 := sq_nonneg _
      rw [Real.norm_of_nonneg h_sq_nonneg]
      have h_abs_sq : (Z t ω - (μ[Z t | 𝒢 t]) ω) ^ 2 ≤ B ^ 2 := by
        have h_abs' := abs_le.mp h_abs
        have h_low := h_abs'.1
        have h_high := h_abs'.2
        nlinarith
      exact h_abs_sq
    have h_int_const : Integrable (fun _ : Ω => B ^ 2) μ := integrable_const (c := B ^ 2)
    exact h_int_const.mono' h_ae h_bound
  have hle : ∀ t, ∀ᵐ ω ∂μ, α * X t ω ≤ 1 := by
    intro t
    rw [hα_def, hX_def]
    filter_upwards [hX_bound_ae t] with ω h
    have h_abs : |Z t ω - (μ[Z t | 𝒢 t]) ω| ≤ B := h
    have h_diff_le : Z t ω - (μ[Z t | 𝒢 t]) ω ≤ B := by
      have := abs_le.mp h_abs
      linarith
    calc
      (1 / B) * (Z t ω - (μ[Z t | 𝒢 t]) ω) ≤ (1 / B) * B :=
        mul_le_mul_of_nonneg_left h_diff_le (by positivity)
      _ = 1 := by field_simp [ne_of_gt hB]
  have hdrift : ∀ t, μ[X t | 𝒢 t] ≤ᵐ[μ] 0 := by
    intro t
    rw [hX_def]
    have h_int_Z : Integrable (Z t) μ := by
      have h_meas_ae : AEStronglyMeasurable (Z t) μ := (hZ_meas t).aestronglyMeasurable
      have h_bound : ∀ᵐ ω ∂μ, ‖Z t ω‖ ≤ B := by
        have h_all : ∀ ω, ‖Z t ω‖ ≤ B := by
          intro ω
          rw [Real.norm_of_nonneg (hZ0 t ω)]
          exact hZB t ω
        exact MeasureTheory.ae_of_all μ h_all
      have h_int_const : Integrable (fun _ : Ω => B) μ := integrable_const (c := B)
      exact h_int_const.mono' h_meas_ae h_bound
    have h_cond_int : Integrable (μ[Z t | 𝒢 t]) μ := integrable_condExp
    have h_sub : μ[Z t - (μ[Z t | 𝒢 t]) | 𝒢 t] =ᵐ[μ] μ[Z t | 𝒢 t] - μ[(μ[Z t | 𝒢 t]) | 𝒢 t] :=
      condExp_sub h_int_Z h_cond_int (𝒢 t)
    have h_cond_cond : μ[(μ[Z t | 𝒢 t]) | 𝒢 t] =ᵐ[μ] μ[Z t | 𝒢 t] := by
      have h_le : 𝒢 t ≤ 𝒢 t := le_rfl
      have h_le_m0 : 𝒢 t ≤ m0 := 𝒢.le t
      exact condExp_condExp_of_le h_le h_le_m0
    have h_diff : (μ[Z t | 𝒢 t] - μ[(μ[Z t | 𝒢 t]) | 𝒢 t]) =ᵐ[μ] (μ[Z t | 𝒢 t] - μ[Z t | 𝒢 t]) :=
      Filter.EventuallyEq.sub (Filter.EventuallyEq.refl (ae μ) _) h_cond_cond
    have h_zero : (μ[Z t | 𝒢 t] - μ[Z t | 𝒢 t]) = (0 : Ω → ℝ) := by
      ext ω; simp
    have h_eq : μ[Z t - (μ[Z t | 𝒢 t]) | 𝒢 t] =ᵐ[μ] 0 := by
      calc
        μ[Z t - (μ[Z t | 𝒢 t]) | 𝒢 t] =ᵐ[μ] μ[Z t | 𝒢 t] - μ[(μ[Z t | 𝒢 t]) | 𝒢 t] := h_sub
        _ =ᵐ[μ] μ[Z t | 𝒢 t] - μ[Z t | 𝒢 t] := h_diff
        _ = 0 := by rw [h_zero]
        _ =ᵐ[μ] 0 := by rfl
    exact h_eq.le
  have h_freedman := freedman_unnorm_max μ 𝒢 X α hα_pos hXm hX_int hX2_int hle hdrift N δ hδ
  refine le_trans ?_ h_freedman
  have h_cond_sq_ae : ∀ᵐ ω ∂μ, ∀ u, u < N → μ[(Z u - μ[Z u | 𝒢 u]) ^ 2 | 𝒢 u] ω ≤ B * μ[Z u | 𝒢 u] ω := by
    rw [ae_all_iff]
    intro u
    by_cases hu : u < N
    · have h_sq := condExp_centered_sq_le (𝒢 u) μ (𝒢.le u) (Z u)
        (hZ_meas u) B (hZ0 u) (hZB u)
      filter_upwards [h_sq] with ω hω
      intro h_lt
      exact hω
    · refine MeasureTheory.ae_of_all μ ?_
      intro ω h_lt
      exfalso; exact hu h_lt
  have h_subset : {ω | ∃ t ≤ N, 2 * ∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω + B * Real.log (1 / δ) ≤
      ∑ u ∈ Finset.range t, Z u ω} ≤ᵐ[μ]
      {ω | ∃ t ≤ N, α * predVar μ 𝒢 X t ω + Real.log (1 / δ) / α ≤ ∑ u ∈ Finset.range t, X u ω} := by
    filter_upwards [h_cond_sq_ae] with ω h_cond_sq
    intro hω
    rcases hω with ⟨t, htN, hineq⟩
    refine ⟨t, htN, ?_⟩
    rw [hα_def]
    have h_log_div : Real.log (1 / δ) / (1 / B) = B * Real.log (1 / δ) := by
      field_simp [ne_of_gt hB]
    rw [h_log_div]
    rw [hX_def]
    -- Left side: (1/B) * predVar μ 𝒢 X t ω + B * Real.log (1 / δ)
    -- Right side: ∑ u, (Z u ω - μ[Z u | 𝒢 u] ω) = (∑ u, Z u ω) - (∑ u, μ[Z u | 𝒢 u] ω)
    -- Let S := ∑ u, Z u ω and T := ∑ u, μ[Z u | 𝒢 u] ω
    -- hineq: 2 * T + B * log(1/δ) ≤ S
    -- So S - T ≥ T + B * log(1/δ)
    -- We need: (1/B) * predVar + B * log(1/δ) ≤ S - T
    -- From h_cond_sq: for all u < N, μ[(Z u - μ[Z u | 𝒢 u]) ^ 2 | 𝒢 u] ω ≤ B * μ[Z u | 𝒢 u] ω
    -- So predVar = ∑ u < t, μ[X u ^ 2 | 𝒢 u] ω ≤ ∑ u < t, B * μ[Z u | 𝒢 u] ω = B * T
    -- Hence (1/B) * predVar ≤ T
    -- So (1/B) * predVar + B * log(1/δ) ≤ T + B * log(1/δ) ≤ S - T
    have h_pred_var_le : predVar μ 𝒢 X t ω ≤ B * (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) := by
      calc
        predVar μ 𝒢 X t ω = ∑ u ∈ Finset.range t, (μ[(fun ω => X u ω ^ 2) | 𝒢 u]) ω := rfl
        _ ≤ ∑ u ∈ Finset.range t, B * (μ[Z u | 𝒢 u] ω) := by
          refine Finset.sum_le_sum ?_
          intro u hu
          have hu_lt_N : u < N := by
            have : u < t := Finset.mem_range.1 hu
            exact lt_of_lt_of_le this htN
          have h_sq := h_cond_sq u hu_lt_N
          -- h_sq : μ[(Z u - μ[Z u | 𝒢 u]) ^ 2 | 𝒢 u] ω ≤ B * μ[Z u | 𝒢 u] ω
          -- But we need it for X u = Z u - μ[Z u | 𝒢 u]
          have : (fun ω => X u ω ^ 2) = (Z u - μ[Z u | 𝒢 u]) ^ 2 := by
            ext ω; simp [hX_def]
          rw [this]
          exact h_sq
        _ = B * (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) := by
          simp [Finset.mul_sum]
    have h_sum_X : (∑ u ∈ Finset.range t, (Z u ω - (μ[Z u | 𝒢 u]) ω)) =
        (∑ u ∈ Finset.range t, Z u ω) - (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) := by
      simp [Finset.sum_sub_distrib]
    rw [h_sum_X]
    -- Now we need: (1/B) * predVar + B * log(1/δ) ≤ S - T
    -- where S = ∑ Z, T = ∑ μ[Z|𝒢]
    -- From hineq: 2*T + B*log(1/δ) ≤ S
    -- So S - T ≥ T + B*log(1/δ)
    -- And from h_pred_var_le: (1/B) * predVar ≤ T
    -- So (1/B) * predVar + B*log(1/δ) ≤ T + B*log(1/δ) ≤ S - T
    have h_ineq' : (∑ u ∈ Finset.range t, Z u ω) - (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) ≥
        (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) + B * Real.log (1 / δ) := by
      linarith
    have h_pred_div : (1 / B) * predVar μ 𝒢 X t ω ≤ ∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω := by
      have hBpos' : 0 ≤ 1 / B := by positivity
      -- from h_pred_var_le: predVar ≤ B * T
      -- multiply both sides by (1/B)
      calc
        (1 / B) * predVar μ 𝒢 X t ω ≤ (1 / B) * (B * (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω)) :=
          mul_le_mul_of_nonneg_left h_pred_var_le hBpos'
        _ = (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) := by
          field_simp [ne_of_gt hB]
    have h_sum : (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) + B * Real.log (1 / δ) ≤
        ((∑ u ∈ Finset.range t, Z u ω) - (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω)) := by
      linarith
    calc
      (1 / B) * predVar μ 𝒢 X t ω + B * Real.log (1 / δ) ≤
          (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω) + B * Real.log (1 / δ) := by
        nlinarith
      _ ≤ ((∑ u ∈ Finset.range t, Z u ω) - (∑ u ∈ Finset.range t, μ[Z u | 𝒢 u] ω)) := h_sum
  exact measure_mono_ae h_subset

/-! ## The moments of `v = pip - 1` at a good state -/

/-- A continuous function of linear growth, composed with an affine map, is integrable under the standard
Gaussian, and so is its square. -/
theorem integrable_of_growth (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : Continuous F) (a b : ℝ)
    (hg : ∀ x, |F x| ≤ a + b * ‖x‖) (mu : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => F (mu + T g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => F (mu + T g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => F (mu + T g)) :=
    hF.comp ((continuous_const.add T.continuous))
  have h_meas : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => F (mu + T g)) μ :=
    h_cont.aestronglyMeasurable
  have h_bound : ∀ g, |F (mu + T g)| ≤ a + |b| * ‖mu‖ + |b| * ‖T‖ * ‖g‖ := by
    intro g
    have h := hg (mu + T g)
    have h_norm : ‖mu + T g‖ ≤ ‖mu‖ + ‖T g‖ := norm_add_le _ _
    have h_Tg : ‖T g‖ ≤ ‖T‖ * ‖g‖ := T.le_opNorm g
    calc
      |F (mu + T g)| ≤ a + b * ‖mu + T g‖ := h
      _ ≤ a + |b| * ‖mu + T g‖ := by
        gcongr
        exact le_abs_self b
      _ ≤ a + |b| * (‖mu‖ + ‖T g‖) := by gcongr
      _ = a + |b| * ‖mu‖ + |b| * ‖T g‖ := by ring
      _ ≤ a + |b| * ‖mu‖ + |b| * (‖T‖ * ‖g‖) := by gcongr
      _ = a + |b| * ‖mu‖ + |b| * ‖T‖ * ‖g‖ := by ring
  have h_sq_bound (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have h_bound_sq : ∀ g, |F (mu + T g)| ^ 2 ≤ 2 * (a + |b| * ‖mu‖) ^ 2 + 2 * (|b| * ‖T‖) ^ 2 * ‖g‖ ^ 2 := by
    intro g
    have h := h_bound g
    have h_nonneg_abs : 0 ≤ |b| := abs_nonneg _
    have h_nonneg_bound : 0 ≤ a + |b| * ‖mu‖ + |b| * ‖T‖ * ‖g‖ := by
      -- since |F(...)| ≥ 0, the bound must be nonnegative
      linarith [abs_nonneg (F (mu + T g)), h]
    have h_sq : (a + |b| * ‖mu‖ + |b| * ‖T‖ * ‖g‖) ^ 2 ≤
        2 * (a + |b| * ‖mu‖) ^ 2 + 2 * (|b| * ‖T‖ * ‖g‖) ^ 2 :=
      h_sq_bound (a + |b| * ‖mu‖) (|b| * ‖T‖ * ‖g‖)
    have h_abs_sq : |F (mu + T g)| ^ 2 ≤ (a + |b| * ‖mu‖ + |b| * ‖T‖ * ‖g‖) ^ 2 := by
      have h_nonneg_left : 0 ≤ |F (mu + T g)| := abs_nonneg _
      nlinarith
    nlinarith
  have h_int_norm : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) μ := by
    have h_mem1 : MemLp id (1 : ℝ≥0∞) μ := IsGaussian.memLp_id μ 1 (by norm_num)
    have h := h_mem1.integrable_norm_rpow (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    simpa using h
  have h_int_norm_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) μ := by
    have h_mem2 : MemLp id (2 : ℝ≥0∞) μ := IsGaussian.memLp_two_id
    have h := h_mem2.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using h
  let C1 : ℝ := a + |b| * ‖mu‖
  let C2 : ℝ := |b| * ‖T‖
  have h_int_dom1 : Integrable (fun g => C1 + C2 * ‖g‖) μ :=
    (integrable_const _).add (h_int_norm.const_mul C2)
  have h_int_dom2 : Integrable (fun g => 2 * C1 ^ 2 + 2 * C2 ^ 2 * ‖g‖ ^ 2) μ :=
    (integrable_const _).add (h_int_norm_sq.const_mul (2 * C2 ^ 2))
  have h_int1 : Integrable (fun g => F (mu + T g)) μ := by
    refine h_int_dom1.mono' h_meas ?_
    filter_upwards with g
    simpa [Real.norm_eq_abs] using h_bound g
  have h_cont_sq : Continuous (fun g : EuclideanSpace ℝ (Fin d) => F (mu + T g) ^ 2) :=
    h_cont.pow 2
  have h_meas_sq : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => F (mu + T g) ^ 2) μ :=
    h_cont_sq.aestronglyMeasurable
  have h_int2 : Integrable (fun g => F (mu + T g) ^ 2) μ := by
    refine h_int_dom2.mono' h_meas_sq ?_
    filter_upwards with g
    have h_nonneg_sq : 0 ≤ F (mu + T g) ^ 2 := pow_two_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg_sq, sq_abs] using h_bound_sq g
  exact And.intro h_int1 h_int2

/-- The tail of the gauge of `T g` at the level `L`, for `‖T‖ ≤ 1/(2 √L)`. -/
theorem gauge_tail_L (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 504 ≤ L)
    (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt L)) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) {g | L < gauge K (T g)} ≤
      ENNReal.ofReal (Real.exp (-(2 * L * (L - 2) ^ 2))) := by
  have hLpos : 0 < L := by linarith
  have hL_one : 1 ≤ L := by linarith
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hs_nonneg : 0 ≤ 1 / (2 * Real.sqrt L) := by
    refine div_nonneg (by norm_num) ?_
    nlinarith
  set c := ∫ g, gauge K (T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) with hc_def
  have hc_le_one : c ≤ 1 := by
    have h1 : c ≤ (1 / (2 * Real.sqrt L)) * pgMw K * Real.sqrt d := by
      refine gauge_mean_le hd K hK hKc hball T (1 / (2 * Real.sqrt L)) hs_nonneg hT
    have h2 : (1 / (2 * Real.sqrt L)) * pgMw K * Real.sqrt d ≤ (1 / (2 * Real.sqrt L)) * (df2Mw d) * Real.sqrt d := by
      have hMw' : pgMw K ≤ df2Mw d := hMw
      have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      have h_nonneg : 0 ≤ 1 / (2 * Real.sqrt L) := hs_nonneg
      have h_mul : pgMw K * Real.sqrt d ≤ (df2Mw d) * Real.sqrt d :=
        mul_le_mul_of_nonneg_right hMw' hsqrt_nonneg
      have h_total : (1 / (2 * Real.sqrt L)) * pgMw K * Real.sqrt d =
          (1 / (2 * Real.sqrt L)) * (pgMw K * Real.sqrt d) := by ring
      have h_total2 : (1 / (2 * Real.sqrt L)) * (df2Mw d) * Real.sqrt d =
          (1 / (2 * Real.sqrt L)) * ((df2Mw d) * Real.sqrt d) := by ring
      rw [h_total, h_total2]
      exact mul_le_mul_of_nonneg_left h_mul h_nonneg
    have h3 : (1 / (2 * Real.sqrt L)) * (df2Mw d) * Real.sqrt d ≤ (1 / (2 * Real.sqrt L)) * (2 * Real.sqrt L) := by
      have hmw_small : df2Mw d * Real.sqrt d ≤ 2 * Real.sqrt L := mw_small hd L hL_one
      have h_nonneg : 0 ≤ 1 / (2 * Real.sqrt L) := hs_nonneg
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmw_small h_nonneg
    have h4 : (1 / (2 * Real.sqrt L)) * (2 * Real.sqrt L) = 1 := by
      field_simp [hsqrtL_pos.ne']
    calc
      c ≤ (1 / (2 * Real.sqrt L)) * pgMw K * Real.sqrt d := h1
      _ ≤ (1 / (2 * Real.sqrt L)) * (df2Mw d) * Real.sqrt d := h2
      _ ≤ (1 / (2 * Real.sqrt L)) * (2 * Real.sqrt L) := h3
      _ = 1 := h4
  have hL_sub_two_nonneg : 0 ≤ L - 2 := by linarith
  have h_subset : {g | L < gauge K (T g)} ⊆ {g | c + (L - 2) ≤ gauge K (T g)} := by
    intro g hg
    simp_rw [Set.mem_ofPred_eq] at hg ⊢
    have h1 : c + (L - 2) ≤ 1 + (L - 2) := by nlinarith
    have h2 : 1 + (L - 2) < L := by nlinarith
    nlinarith
  have h_measure : stdGaussian (EuclideanSpace ℝ (Fin d)) {g | c + (L - 2) ≤ gauge K (T g)} ≤
      ENNReal.ofReal (Real.exp (-((L - 2) ^ 2 / (2 * ‖T‖ ^ 2)))) := by
    simpa [hc_def] using gauge_conc K hK hKc hball T (L - 2) hL_sub_two_nonneg
  by_cases hTzero : ‖T‖ = 0
  · have hT_eq_zero : T = 0 := norm_eq_zero.mp hTzero
    have h_empty : {g | L < gauge K (T g)} = (∅ : Set (EuclideanSpace ℝ (Fin d))) := by
      ext g
      simp [hT_eq_zero, hLpos.le]
    simp [h_empty]
  · have hT_pos : 0 < ‖T‖ := by
      by_contra! hle
      have h_eq_zero : ‖T‖ = 0 := le_antisymm hle (norm_nonneg T)
      exact hTzero h_eq_zero
    have hT_sq_pos : 0 < ‖T‖ ^ 2 := pow_pos hT_pos 2
    have h_sqrt_sq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt (by linarith)
    have hT_sq_le : ‖T‖ ^ 2 ≤ 1 / (4 * L) := by
      have h_bound : ‖T‖ ^ 2 ≤ (1 / (2 * Real.sqrt L)) ^ 2 := by
        nlinarith
      have h_eq : (1 / (2 * Real.sqrt L)) ^ 2 = 1 / (4 * L) := by
        field_simp [hsqrtL_pos.ne']
        nlinarith
      nlinarith
    have h_final : ENNReal.ofReal (Real.exp (-((L - 2) ^ 2 / (2 * ‖T‖ ^ 2)))) ≤
        ENNReal.ofReal (Real.exp (-(2 * L * (L - 2) ^ 2))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      refine Real.exp_le_exp.mpr ?_
      have hLsq_pos : 0 < (L - 2) ^ 2 := by
        have hpos : 0 < L - 2 := by linarith
        exact pow_pos hpos 2
      have h_div_ineq : (L - 2) ^ 2 / (2 * ‖T‖ ^ 2) ≥ 2 * L * (L - 2) ^ 2 := by
        have hkey : 1 / (2 * ‖T‖ ^ 2) ≥ 2 * L := by
          have h_inv : 1 / (‖T‖ ^ 2) ≥ 4 * L := by
            have h_mul : ‖T‖ ^ 2 * (4 * L) ≤ 1 := by
              calc
                ‖T‖ ^ 2 * (4 * L) ≤ (1 / (4 * L)) * (4 * L) :=
                  mul_le_mul_of_nonneg_right hT_sq_le (by positivity)
                _ = 1 := by field_simp [show 4 * L ≠ 0 from by positivity]
            field_simp [hT_sq_pos.ne']
            nlinarith
          calc
            1 / (2 * ‖T‖ ^ 2) = (1 / 2) * (1 / (‖T‖ ^ 2)) := by ring
            _ ≥ (1 / 2) * (4 * L) := by nlinarith
            _ = 2 * L := by ring
        calc
          (L - 2) ^ 2 / (2 * ‖T‖ ^ 2) = ((L - 2) ^ 2) * (1 / (2 * ‖T‖ ^ 2)) := by ring
          _ ≥ ((L - 2) ^ 2) * (2 * L) := by nlinarith
          _ = 2 * L * (L - 2) ^ 2 := by ring
      linarith
    calc
      stdGaussian (EuclideanSpace ℝ (Fin d)) {g | L < gauge K (T g)} ≤
          stdGaussian (EuclideanSpace ℝ (Fin d)) {g | c + (L - 2) ≤ gauge K (T g)} :=
        measure_mono h_subset
      _ ≤ ENNReal.ofReal (Real.exp (-((L - 2) ^ 2 / (2 * ‖T‖ ^ 2)))) := h_measure
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * L * (L - 2) ^ 2))) := h_final

/-- The fourth moment of the gauge: `E π(T g)⁴ ≤ ‖T‖⁴ d (d + 2)`. -/
theorem gauge_fourth_le (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ g, gauge K (T g) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ‖T‖ ^ 4 * (d * (d + 2)) := by
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K :=
    Metric.ball_subset_closedBall.trans hball
  have h_nonneg_T_norm : 0 ≤ ‖T‖ := norm_nonneg _
  have h_gauge_bound : ∀ g, gauge K (T g) ≤ ‖T‖ * ‖g‖ := by
    intro g
    have h1 : gauge K (T g) ≤ ‖T g‖ := by
      have := mul_gauge_le_norm hball' (x := T g)
      simpa [one_mul] using this
    have h2 : ‖T g‖ ≤ ‖T‖ * ‖g‖ := ContinuousLinearMap.le_opNorm T g
    exact le_trans h1 h2
  have h_pow_bound : ∀ g, gauge K (T g) ^ 4 ≤ (‖T‖ * ‖g‖) ^ 4 := by
    intro g
    have h_nonneg_gauge : 0 ≤ gauge K (T g) := gauge_nonneg (T g)
    exact pow_le_pow_left₀ h_nonneg_gauge (h_gauge_bound g) 4
  have h_int_norm_pow_four : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 4)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    by_cases hd : (d : ℝ) * (d + 2) = 0
    · -- then d = 0 (since d ≥ 0)
      have hd0 : d = 0 := by
        by_contra! hpos
        have hpos_d : (d : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hpos
        have hpos_prod : (d : ℝ) * (d + 2) > 0 := mul_pos hpos_d (by linarith)
        linarith
      subst hd0
      have h_zero : (fun g : EuclideanSpace ℝ (Fin 0) => ‖g‖ ^ 4) = fun _ => (0 : ℝ) := by
        ext g
        have : g = 0 := Subsingleton.elim _ _
        simp [this]
      rw [h_zero]
      exact integrable_const _
    · -- integral is nonzero, so integrable
      refine MeasureTheory.Integrable.of_integral_ne_zero ?_
      rw [(gaussMoments d).1]
      exact hd
  have h_int_bound : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖T‖ * ‖g‖) ^ 4)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have : (fun g : EuclideanSpace ℝ (Fin d) => (‖T‖ * ‖g‖) ^ 4) =
        fun g => ‖T‖ ^ 4 * (‖g‖ ^ 4) := by
      ext g; ring
    rw [this]
    exact (h_int_norm_pow_four.const_mul (‖T‖ ^ 4))
  by_cases h_int_gauge : Integrable (fun g : EuclideanSpace ℝ (Fin d) => gauge K (T g) ^ 4)
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
  · -- integrable case: use integral_mono
    calc
      ∫ g, gauge K (T g) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, (‖T‖ * ‖g‖) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_mono_ae h_int_gauge h_int_bound (ae_of_all _ h_pow_bound)
      _ = ∫ g, (‖T‖ ^ 4 * ‖g‖ ^ 4) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine integral_congr_ae ?_
        filter_upwards with g
        ring
      _ = ‖T‖ ^ 4 * ∫ g, ‖g‖ ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_const_mul]
      _ = ‖T‖ ^ 4 * ((d : ℝ) * (d + 2)) := by rw [(gaussMoments d).1]
      _ = ‖T‖ ^ 4 * (d * (d + 2)) := by simp
  · -- not integrable: integral is 0, inequality holds since RHS is nonnegative
    have h_int_zero : ∫ g, gauge K (T g) ^ 4 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0 :=
      integral_undef h_int_gauge
    rw [h_int_zero]
    positivity


/-- The tail term of the truncation: `4 E[π(T g)² 1{π(T g) > L}] ≤ e^{-L}` for `‖T‖ ≤ 1/(2 √L)` and `d ≤ e^L`, by
`π² 1_A ≤ (s π⁴ + 1_A/s)/2` at `s = exp(-L(L - 2)²)`, the fourth moment and the tail at `L`. -/
theorem gauge_sq_tail_le (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 504 ≤ L)
    (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt L)) (hdL : (d : ℝ) ≤ Real.exp L) :
    4 * ∫ g, gauge K (T g) ^ 2 * Set.indicator {x | L < gauge K (T x)} (fun _ => (1 : ℝ)) g
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ Real.exp (-L) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set A : Set (EuclideanSpace ℝ (Fin d)) := {x | L < gauge K (T x)} with hA
  have hK0 : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball
  have hπc : Continuous fun g => gauge K (T g) := (continuous_gauge hK hK0).comp T.continuous
  have hAm : MeasurableSet A := (isOpen_lt continuous_const hπc).measurableSet
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K := Metric.ball_subset_closedBall.trans hball
  have hgle : ∀ g, gauge K (T g) ≤ ‖T‖ * ‖g‖ := fun g =>
    le_trans (by simpa [one_mul] using mul_gauge_le_norm hball' (x := T g)) (T.le_opNorm g)
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hT1 : ‖T‖ ≤ 1 := by
    refine hT.trans ?_
    rw [div_le_one (by positivity)]
    have : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; linarith
    linarith
  have hint4 : Integrable (fun g => gauge K (T g) ^ 4) γ := by
    have h4 := (IsGaussian.memLp_id γ (4 : ℕ) (by simp)).integrable_norm_pow (p := 4) (by norm_num)
    refine (h4.const_mul (‖T‖ ^ 4)).mono' (hπc.pow 4).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), id, ← mul_pow]
    exact pow_le_pow_left₀ (gauge_nonneg _) (hgle g) 4
  have hintA : Integrable (A.indicator fun _ => (1 : ℝ)) γ := (integrable_const (1 : ℝ)).indicator hAm
  set s := Real.exp (-(L * (L - 2) ^ 2)) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hpt : ∀ g, gauge K (T g) ^ 2 * A.indicator (fun _ => (1 : ℝ)) g ≤
      (s * gauge K (T g) ^ 4 + A.indicator (fun _ => (1 : ℝ)) g / s) / 2 := by
    intro g
    by_cases hg : g ∈ A
    · rw [Set.indicator_of_mem hg, mul_one, le_div_iff₀ two_pos]
      have key : 0 ≤ (s * gauge K (T g) ^ 2 - 1) ^ 2 / s := by positivity
      have e : (s * gauge K (T g) ^ 2 - 1) ^ 2 / s = s * gauge K (T g) ^ 4 + 1 / s - 2 * gauge K (T g) ^ 2 := by
        field_simp; ring
      linarith
    · rw [Set.indicator_of_notMem hg, mul_zero, zero_div, add_zero]
      have : 0 ≤ gauge K (T g) := gauge_nonneg _
      positivity
  have hI : ∫ g, gauge K (T g) ^ 2 * A.indicator (fun _ => (1 : ℝ)) g ∂γ ≤
      (s * ∫ g, gauge K (T g) ^ 4 ∂γ + (γ A).toReal / s) / 2 := by
    have hrhs : Integrable (fun g => (s * gauge K (T g) ^ 4 + A.indicator (fun _ => (1 : ℝ)) g / s) / 2) γ :=
      (((hint4.const_mul s).add (hintA.div_const s)).div_const 2)
    refine (integral_mono_of_nonneg (ae_of_all _ fun g => ?_) hrhs (ae_of_all _ hpt)).trans_eq ?_
    · have : 0 ≤ gauge K (T g) := gauge_nonneg _
      have : 0 ≤ A.indicator (fun _ => (1 : ℝ)) g := Set.indicator_nonneg (fun _ _ => zero_le_one) g
      positivity
    · rw [integral_div, integral_add (hint4.const_mul s) (hintA.div_const s), integral_const_mul, integral_div,
        integral_indicator_const (1 : ℝ) hAm, smul_eq_mul, mul_one, measureReal_def]
  have h4 : ∫ g, gauge K (T g) ^ 4 ∂γ ≤ 3 * Real.exp (2 * L) := by
    refine (gauge_fourth_le K hK hKc hball T).trans ?_
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hT4 : ‖T‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) hT1
    have hdd : (d : ℝ) * (d + 2) ≤ 3 * Real.exp (2 * L) := by
      have : Real.exp (2 * L) = Real.exp L ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
      rw [this]
      nlinarith
    calc ‖T‖ ^ 4 * (d * (d + 2)) ≤ 1 * (d * (d + 2)) := by gcongr
      _ ≤ 3 * Real.exp (2 * L) := by linarith
  have hAle : (γ A).toReal ≤ s ^ 2 := by
    have h := gauge_tail_L hd K hK hKc hball hMw T L hL hT
    have : s ^ 2 = Real.exp (-(2 * L * (L - 2) ^ 2)) := by rw [hs, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le h
  have h0 : 0 ≤ ∫ g, gauge K (T g) ^ 4 ∂γ := integral_nonneg fun g => by positivity
  have hfin : 8 * Real.exp (2 * L) * s ≤ Real.exp (-L) := by
    rw [hs, mul_assoc, ← Real.exp_add]
    have h8 : (8 : ℝ) ≤ Real.exp (L * (L - 2) ^ 2 - 3 * L) := by
      have := Real.add_one_le_exp (L * (L - 2) ^ 2 - 3 * L)
      nlinarith
    calc 8 * Real.exp (2 * L + -(L * (L - 2) ^ 2))
        ≤ Real.exp (L * (L - 2) ^ 2 - 3 * L) * Real.exp (2 * L + -(L * (L - 2) ^ 2)) := by gcongr
      _ = Real.exp (-L) := by rw [← Real.exp_add]; ring_nf
  have e1 : (γ A).toReal / s ≤ s := by rw [div_le_iff₀ hs0]; nlinarith
  have e2 : s * ∫ g, gauge K (T g) ^ 4 ∂γ ≤ s * (3 * Real.exp (2 * L)) := by gcongr
  have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  nlinarith
/-- By truncation: `E v² ≤ 2 L E v + e^{-L}` at a state with `π(μ) ≤ 1 - ε` and `‖T‖ ≤ 1/(2 √L)`. -/
theorem v_sq_le (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (mu : EuclideanSpace ℝ (Fin d)) (hmu : gauge K mu ≤ 1 - ε)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 504 ≤ L)
    (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt L)) (hdL : (d : ℝ) ≤ Real.exp L) :
    ∫ g, (pipOf K ε (mu + T g) - 1) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      2 * L * ∫ g, (pipOf K ε (mu + T g) - 1) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + Real.exp (-L) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let v (g : EuclideanSpace ℝ (Fin d)) : ℝ := pipOf K ε (mu + T g) - 1
  let π (g : EuclideanSpace ℝ (Fin d)) : ℝ := gauge K (T g)
  have hball_mem : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hK_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset hball_mem hball
  have hK_absorbent : Absorbent ℝ K :=
    absorbent_nhds_zero hK_nhds
  have h_gauge_cont : Continuous (gauge K) :=
    continuous_gauge hK hK_nhds
  have h_pip_comp : Continuous (fun g : EuclideanSpace ℝ (Fin d) => pipOf K ε (mu + T g)) := by
    unfold pipOf
    have h_gauge_comp : Continuous (fun g : EuclideanSpace ℝ (Fin d) => gauge K (mu + T g)) :=
      h_gauge_cont.comp (continuous_const.add T.continuous)
    have h_div : Continuous (fun g : EuclideanSpace ℝ (Fin d) => gauge K (mu + T g) / (1 - ε)) :=
      h_gauge_comp.div_const (1 - ε)
    exact Continuous.max (by exact continuous_const) (by exact h_div)
  have h_v_cont : Continuous v := by
    unfold v
    exact Continuous.sub h_pip_comp continuous_const
  have h_π_cont : Continuous π := by
    unfold π
    exact h_gauge_cont.comp T.continuous
  have h_v_nonneg : ∀ g, 0 ≤ v g := by
    intro g
    unfold v pipOf
    have h : 1 ≤ max 1 (gauge K (mu + T g) / (1 - ε)) := le_max_left _ _
    linarith
  have h_one_minus_eps_pos : 0 < 1 - ε := by linarith
  -- key inequality: v g ≤ 2 * π g
  have h_v_le_two_π : ∀ g, v g ≤ 2 * π g := by
    intro g
    unfold v π
    have h_gauge_add : gauge K (mu + T g) ≤ gauge K mu + gauge K (T g) :=
      gauge_add_le hK hK_absorbent mu (T g)
    have h_gauge_mu : gauge K mu ≤ 1 - ε := hmu
    unfold pipOf
    by_cases h : gauge K (mu + T g) / (1 - ε) ≤ 1
    · have hmax : max 1 (gauge K (mu + T g) / (1 - ε)) = 1 := max_eq_left h
      rw [hmax]
      have h_pi_nonneg : 0 ≤ gauge K (T g) := gauge_nonneg _
      nlinarith
    · have hmax : max 1 (gauge K (mu + T g) / (1 - ε)) = gauge K (mu + T g) / (1 - ε) :=
        max_eq_right (by linarith)
      rw [hmax]
      have h_eps_div : 1 / (1 - ε) ≤ 2 := by
        have h1 : 1 - ε ≥ 1/2 := by linarith
        calc
          1 / (1 - ε) ≤ 1 / (1/2) := by gcongr
          _ = 2 := by norm_num
      have h_pi_nonneg : 0 ≤ gauge K (T g) := gauge_nonneg _
      have h_gauge_sum : gauge K (mu + T g) ≤ (1 - ε) + gauge K (T g) := by
        linarith
      calc
        gauge K (mu + T g) / (1 - ε) - 1 ≤ ((1 - ε) + gauge K (T g)) / (1 - ε) - 1 := by
          gcongr
        _ = (1 + gauge K (T g) / (1 - ε)) - 1 := by
          field_simp [h_one_minus_eps_pos.ne.symm]
        _ = gauge K (T g) / (1 - ε) := by ring
        _ = gauge K (T g) * (1 / (1 - ε)) := by ring
        _ ≤ gauge K (T g) * 2 := by gcongr
        _ = 2 * gauge K (T g) := by ring
  -- pointwise inequality: v g ^ 2 ≤ 2 * L * v g + 4 * (π g) ^ 2 * indicator_{L < π}(g)
  have h_pointwise : ∀ g, v g ^ 2 ≤ 2 * L * v g + 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) := by
    intro g
    by_cases h_le : v g ≤ 2 * L
    · have h_sq : v g ^ 2 ≤ 2 * L * v g := by
        have hv_nonneg_g : 0 ≤ v g := h_v_nonneg g
        have hL_nonneg : 0 ≤ L := by linarith
        nlinarith
      have h_indicator_nonneg : 0 ≤ 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) := by
        have h_pi_sq_nonneg : 0 ≤ (π g) ^ 2 := pow_two_nonneg _
        have h_indicator_nonneg' : 0 ≤ Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g :=
          Set.indicator_nonneg (fun x hx => by norm_num) _
        have h_four_nonneg : 0 ≤ (4 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg h_four_nonneg h_pi_sq_nonneg) h_indicator_nonneg'
      nlinarith
    · have h_π_gt_L : L < π g := by
        have : v g ≤ 2 * π g := h_v_le_two_π g
        linarith
      have h_sq : v g ^ 2 ≤ 4 * (π g) ^ 2 := by
        have h_le' : v g ≤ 2 * π g := h_v_le_two_π g
        nlinarith
      have h_indicator : (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) = (1 : ℝ) := by
        apply Set.indicator_of_mem
        exact h_π_gt_L
      have hgoal : v g ^ 2 ≤ 2 * L * v g + 4 * (π g) ^ 2 := by
        have : 0 ≤ 2 * L * v g := by
          have hL_nonneg : 0 ≤ L := by linarith
          have hv_nonneg_g : 0 ≤ v g := h_v_nonneg g
          nlinarith
        nlinarith
      have h_eq : 2 * L * v g + 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) = 2 * L * v g + 4 * (π g) ^ 2 := by
        calc
          2 * L * v g + 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)
              = 2 * L * v g + 4 * (π g) ^ 2 * (1 : ℝ) := by
                apply congrArg (fun t => 2 * L * v g + 4 * (π g) ^ 2 * t)
                exact h_indicator
          _ = 2 * L * v g + 4 * (π g) ^ 2 := by ring
      apply hgoal.trans
      rw [h_eq]
  -- lemma: gauge K x ≤ ‖x‖
  have h_gauge_le_norm : ∀ x, gauge K x ≤ ‖x‖ := by
    intro x
    simpa [one_mul] using mul_gauge_le_norm (Metric.ball_subset_closedBall.trans hball) (x := x)
  -- integrability of v via integrable_of_growth
  have h_int_v_g : Integrable v γ := by
    have h_bound : ∀ x : EuclideanSpace ℝ (Fin d), |(fun x => pipOf K ε x - 1) x| ≤ (0 : ℝ) + (2 : ℝ) * ‖x‖ := by
      intro x
      have h_nonneg : 0 ≤ pipOf K ε x - 1 := by
        unfold pipOf
        have : 1 ≤ max 1 (gauge K x / (1 - ε)) := le_max_left _ _
        linarith
      have h_le : pipOf K ε x - 1 ≤ 2 * gauge K x := by
        unfold pipOf
        by_cases h : gauge K x / (1 - ε) ≤ 1
        · have hmax : max 1 (gauge K x / (1 - ε)) = 1 := max_eq_left h
          rw [hmax]
          have h_nonneg_gauge : 0 ≤ gauge K x := gauge_nonneg _
          nlinarith
        · have hmax : max 1 (gauge K x / (1 - ε)) = gauge K x / (1 - ε) := max_eq_right (by linarith)
          rw [hmax]
          have h_eps_div : 1 / (1 - ε) ≤ 2 := by
            have h1 : 1 - ε ≥ 1/2 := by linarith
            calc
              1 / (1 - ε) ≤ 1 / (1/2) := by gcongr
              _ = 2 := by norm_num
          calc
            gauge K x / (1 - ε) - 1 ≤ gauge K x / (1 - ε) := by
              have : 0 ≤ gauge K x / (1 - ε) := div_nonneg (gauge_nonneg _) (by linarith)
              nlinarith
            _ = gauge K x * (1 / (1 - ε)) := by ring
            _ ≤ gauge K x * 2 := mul_le_mul_of_nonneg_left h_eps_div (gauge_nonneg _)
            _ = 2 * gauge K x := by ring
      rw [abs_of_nonneg h_nonneg]
      calc
        pipOf K ε x - 1 ≤ 2 * gauge K x := h_le
        _ ≤ 2 * ‖x‖ := by gcongr; exact h_gauge_le_norm x
        _ = (0 : ℝ) + (2 : ℝ) * ‖x‖ := by ring
    have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => pipOf K ε x - 1) := by
      unfold pipOf
      have h_gauge_cont' : Continuous (gauge K) := h_gauge_cont
      have h_div : Continuous (fun x : EuclideanSpace ℝ (Fin d) => gauge K x / (1 - ε)) :=
        h_gauge_cont'.div_const (1 - ε)
      have h_max : Continuous (fun x : EuclideanSpace ℝ (Fin d) => max (1 : ℝ) (gauge K x / (1 - ε))) :=
        Continuous.max continuous_const h_div
      exact Continuous.sub h_max continuous_const
    have h_int := integrable_of_growth (fun x => pipOf K ε x - 1) h_cont 0 2 h_bound mu T
    -- h_int : Integrable (fun g => (pipOf K ε (mu + T g) - 1)) γ ∧ Integrable (fun g => (pipOf K ε (mu + T g) - 1)^2) γ
    exact h_int.1
  have h_int_v_sq : Integrable (fun g => v g ^ 2) γ := by
    have h_bound : ∀ x : EuclideanSpace ℝ (Fin d), |(fun x => pipOf K ε x - 1) x| ≤ (0 : ℝ) + (2 : ℝ) * ‖x‖ := by
      intro x
      have h_nonneg : 0 ≤ pipOf K ε x - 1 := by
        unfold pipOf
        have : 1 ≤ max 1 (gauge K x / (1 - ε)) := le_max_left _ _
        linarith
      have h_le : pipOf K ε x - 1 ≤ 2 * gauge K x := by
        unfold pipOf
        by_cases h : gauge K x / (1 - ε) ≤ 1
        · have hmax : max 1 (gauge K x / (1 - ε)) = 1 := max_eq_left h
          rw [hmax]
          have h_nonneg_gauge : 0 ≤ gauge K x := gauge_nonneg _
          nlinarith
        · have hmax : max 1 (gauge K x / (1 - ε)) = gauge K x / (1 - ε) := max_eq_right (by linarith)
          rw [hmax]
          have h_eps_div : 1 / (1 - ε) ≤ 2 := by
            have h1 : 1 - ε ≥ 1/2 := by linarith
            calc
              1 / (1 - ε) ≤ 1 / (1/2) := by gcongr
              _ = 2 := by norm_num
          calc
            gauge K x / (1 - ε) - 1 ≤ gauge K x / (1 - ε) := by
              have : 0 ≤ gauge K x / (1 - ε) := div_nonneg (gauge_nonneg _) (by linarith)
              nlinarith
            _ = gauge K x * (1 / (1 - ε)) := by ring
            _ ≤ gauge K x * 2 := mul_le_mul_of_nonneg_left h_eps_div (gauge_nonneg _)
            _ = 2 * gauge K x := by ring
      rw [abs_of_nonneg h_nonneg]
      calc
        pipOf K ε x - 1 ≤ 2 * gauge K x := h_le
        _ ≤ 2 * ‖x‖ := by gcongr; exact h_gauge_le_norm x
        _ = (0 : ℝ) + (2 : ℝ) * ‖x‖ := by ring
    have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => pipOf K ε x - 1) := by
      unfold pipOf
      have h_div : Continuous (fun x : EuclideanSpace ℝ (Fin d) => gauge K x / (1 - ε)) :=
        h_gauge_cont.div_const (1 - ε)
      have h_max : Continuous (fun x : EuclideanSpace ℝ (Fin d) => max (1 : ℝ) (gauge K x / (1 - ε))) :=
        Continuous.max continuous_const h_div
      exact Continuous.sub h_max continuous_const
    have h_int := integrable_of_growth (fun x => pipOf K ε x - 1) h_cont 0 2 h_bound mu T
    exact h_int.2
  -- integrability of π^2 * indicator
  have h_int_extra : Integrable (fun g => (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)) γ := by
    have h_bound : ∀ g, ‖(π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)‖ ≤ ‖(π g) ^ 2‖ := by
      intro g
      rw [norm_mul]
      have h1 : ‖Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g‖ ≤ 1 := by
        by_cases hx : g ∈ {x | L < π x}
        · rw [Set.indicator_of_mem hx]; simp
        · rw [Set.indicator_of_notMem hx]; simp
      exact mul_le_of_le_one_right (norm_nonneg _) h1
    have h_ae_strongly_measurable : AEStronglyMeasurable (fun g => (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)) γ := by
      have h_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => (π g) ^ 2) := h_π_cont.pow 2
      have h_meas_set : MeasurableSet {x | L < π x} :=
        (isOpen_lt continuous_const h_π_cont).measurableSet
      have h_indicator_ae : AEStronglyMeasurable (Set.indicator {x | L < π x} (fun _ => (1 : ℝ))) γ :=
        (measurable_const.indicator h_meas_set).aestronglyMeasurable
      exact (h_cont.aestronglyMeasurable.mul h_indicator_ae)
    -- now use Integrable.mono' since π^2 is integrable
    have h_int_π_sq : Integrable (fun g => (π g) ^ 2) γ := by
      have hgr : ∀ x : EuclideanSpace ℝ (Fin d), |gauge K x| ≤ 0 + 1 * ‖x‖ := by
        intro x
        rw [abs_of_nonneg (gauge_nonneg x), zero_add, one_mul]
        simpa [one_mul] using mul_gauge_le_norm (Metric.ball_subset_closedBall.trans hball) (x := x)
      simpa [π] using (integrable_of_growth (gauge K) h_gauge_cont 0 1 hgr 0 T).2
    exact h_int_π_sq.mono' h_ae_strongly_measurable (ae_of_all _ fun g => (h_bound g).trans_eq (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]))
  -- integrate the pointwise inequality
  have h_int_ineq : ∫ g, v g ^ 2 ∂γ ≤ 2 * L * ∫ g, v g ∂γ + 4 * ∫ g, (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) ∂γ := by
    calc
      ∫ g, v g ^ 2 ∂γ ≤ ∫ g, (2 * L * v g + 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)) ∂γ :=
        integral_mono h_int_v_sq (by
          have h_int_rhs : Integrable (fun g => 2 * L * v g + 4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)) γ := by
            apply Integrable.add
            · exact h_int_v_g.const_mul (2 * L)
            · simpa [mul_assoc] using h_int_extra.const_mul (4 : ℝ)
          exact h_int_rhs) h_pointwise
      _ = ∫ g, (2 * L * v g) ∂γ + ∫ g, (4 * (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g)) ∂γ := by
        rw [integral_add (h_int_v_g.const_mul (2 * L)) ?_]
        simpa [mul_assoc] using h_int_extra.const_mul (4 : ℝ)
      _ = 2 * L * ∫ g, v g ∂γ + 4 * ∫ g, (π g) ^ 2 * (Set.indicator {x | L < π x} (fun _ => (1 : ℝ)) g) ∂γ := by
        simp [integral_const_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Now bound the extra term: 4 * ∫ π^2 * indicator
  -- Use Cauchy-Schwarz: ∫ π^2 * 1_{π>L} ≤ (∫ π^4)^{1/2} * γ{π>L}^{1/2}
  -- Then use gauge_fourth_le and gauge_tail_L
  -- Finally use numeric bounds with L ≥ 504 and d ≤ exp(L)
  have htail := gauge_sq_tail_le hd K hK hKc hball hMw T L hL hT hdL
  linarith

/-- The first moment of `v` by Jensen: `E v(μ + T g) ≤ ε (E e(μ + T g) - e(μ))`, `e` the extension at `2/ε`. -/
theorem v_mean_le (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f)
    (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (mu : EuclideanSpace ℝ (Fin d)) (hmu : gauge K mu ≤ 1 - ε)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ g, (pipOf K ε (mu + T g) - 1) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ε * ((∫ g, extOf K ε (2 / ε) f (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        extOf K ε (2 / ε) f mu) := by
  set e := extOf K ε (2 / ε) f
  set h := extOf K ε (1 / ε) f
  set p := pipOf K ε
  have hpe : ∀ x, p x - 1 = ε * (e x - h x) := by
    intro x
    dsimp [e, h, extOf]
    field_simp [hε0.ne.symm]
    ring
  have hmu_p : p mu = 1 := by
    dsimp [p, pipOf]
    have hdiv : gauge K mu / (1 - ε) ≤ 1 := by
      refine (div_le_one ?_).mpr hmu
      linarith
    exact max_eq_left hdiv
  have hmu_pip : pipOf K ε mu = 1 := by
    dsimp [p] at hmu_p
    exact hmu_p
  have hemu_eq_fmu : e mu = f mu := by
    dsimp [e, extOf]
    rw [hmu_pip]
    simp
  have hmu_eq_fmu : h mu = f mu := by
    dsimp [h, extOf]
    rw [hmu_pip]
    simp
  have h_convex : ConvexOn ℝ Set.univ h := by
    refine extOf_convex K hK hKc hball f hf hf01 ε hε0 hε1 (1 / ε) ?_
    have hdiv : (1 - ε) / ε ≤ 1 / ε := by
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      linarith
    exact hdiv
  have h_cont : Continuous h := continuous_of_convexOn_univ h h_convex
  have h_growth : ∀ x, |h x| ≤ ((1 : ℝ) + (1 : ℝ) / ε) + ((1 : ℝ) + (1 : ℝ) / ε) / (1 - ε) * ‖x‖ := by
    intro x
    exact extOf_abs_le K hK hKc hball f hf01 ε hε0 hε1 (1 / ε) (by positivity) x
  have h_jensen : h mu ≤ ∫ g, h (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    le_integral_add_gauss h h_convex h_cont ((1 : ℝ) + (1 : ℝ) / ε) (((1 : ℝ) + (1 : ℝ) / ε) / (1 - ε)) h_growth T mu
  obtain ⟨h_int_h, _⟩ := integrable_of_growth h h_cont ((1 : ℝ) + (1 : ℝ) / ε) (((1 : ℝ) + (1 : ℝ) / ε) / (1 - ε)) h_growth mu T
  have h_int_e : Integrable (fun g => e (mu + T g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_cont_e : Continuous e := by
      have h_convex_e : ConvexOn ℝ Set.univ e := by
        refine extOf_convex K hK hKc hball f hf hf01 ε hε0 hε1 (2 / ε) ?_
        have hdiv' : (1 - ε) / ε ≤ 2 / ε := by
          refine div_le_div_of_nonneg_right ?_ (by linarith)
          linarith
        exact hdiv'
      exact continuous_of_convexOn_univ e h_convex_e
    exact (integrable_of_growth e h_cont_e ((1 : ℝ) + (2 : ℝ) / ε) (((1 : ℝ) + (2 : ℝ) / ε) / (1 - ε))
      (fun x => extOf_abs_le K hK hKc hball f hf01 ε hε0 hε1 (2 / ε) (by positivity) x) mu T).1
  calc
    ∫ g, (p (mu + T g) - 1) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = ∫ g, ε * (e (mu + T g) - h (mu + T g)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          refine integral_congr_ae ?_
          filter_upwards with g
          rw [hpe]
    _ = ε * ∫ g, (e (mu + T g) - h (mu + T g)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          rw [integral_const_mul]
    _ = ε * ((∫ g, e (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
              (∫ g, h (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) := by
          rw [integral_sub h_int_e h_int_h]
    _ ≤ ε * ((∫ g, e (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) - h mu) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine sub_le_sub_left h_jensen _
    _ = ε * ((∫ g, e (mu + T g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) - e mu) := by
          rw [hemu_eq_fmu, hmu_eq_fmu]


/-- `|Y| ≤ 2L/ε` on Noise and Pi: `|P (a + e) + 2 (P - 1)/ε| ≤ 2 L/ε` for `1 ≤ P ≤ 2 √L`, `a ∈ [0, 1]`,
`|e| ≤ √L_g`, `L_g ≤ L`, `L ≥ 25`, `0 < ε ≤ 1/2`. -/
theorem ymax_le (L Lg ε P a e : ℝ) (hL : 25 ≤ L) (hLg : Lg ≤ L) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hP1 : 1 ≤ P)
    (hP : P ≤ 2 * Real.sqrt L) (ha : a ∈ Set.Icc (0 : ℝ) 1) (he : |e| ≤ Real.sqrt Lg) :
    (P * (a + e) + 2 * (P - 1) / ε) ^ 2 ≤ (2 * L / ε) ^ 2 := by
  rcases ha with ⟨ha0, ha1⟩
  have hL0 : 0 ≤ L := by linarith
  have hLsq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL0
  set s := Real.sqrt L with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg L
  have hs5 : 5 ≤ s := by
    calc
      5 = Real.sqrt ((25 : ℕ).cast : ℝ) := by norm_num
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
      _ = s := rfl
  have hPbound : P ≤ 2 * s := by
    simpa [hs_def] using hP
  have he_abs : |e| ≤ s := by
    calc
      |e| ≤ Real.sqrt Lg := he
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hLg
      _ = s := rfl
  have he_upper : e ≤ s := by
    have := abs_le.mp he_abs
    linarith
  have he_lower : -s ≤ e := by
    have := abs_le.mp he_abs
    linarith
  have h_lower_mul : -2 * L ≤ ε * (P * (a + e)) + 2 * (P - 1) := by
    have hP_nonneg : 0 ≤ P := by linarith
    have h1 : a + e ≥ -s := by linarith
    have h2 : P * (a + e) ≥ P * (-s) := by nlinarith
    have h3 : P * (-s) ≥ (2 * s) * (-s) := by
      -- P ≤ 2s, and -s ≤ 0, so multiplying reverses
      nlinarith
    have h4 : (2 * s) * (-s) = -(2 * s ^ 2) := by ring
    have h5 : -(2 * s ^ 2) = -2 * ((Real.sqrt L) ^ 2) := by
      simp [hs_def]
    have h6 : -2 * ((Real.sqrt L) ^ 2) = -2 * L := by rw [hLsq]
    have h7 : ε * (P * (a + e)) ≥ ε * (P * (-s)) := by
      nlinarith
    have h8 : ε * (P * (-s)) ≥ ε * (-2 * L) := by nlinarith
    have h9 : ε * (-2 * L) ≥ -2 * L := by
      -- ε ≤ 1, and -2L ≤ 0, so ε*(-2L) ≥ -2L
      have : -2 * L ≤ 0 := by nlinarith
      nlinarith
    have h_nonneg : 0 ≤ 2 * (P - 1) := by
      have : 1 ≤ P := hP1
      nlinarith
    nlinarith
  have h_upper_mul : ε * (P * (a + e)) + 2 * (P - 1) ≤ 2 * L := by
    have h1 : a + e ≤ 1 + s := by linarith
    have h2 : P * (a + e) ≤ P * (1 + s) := by nlinarith
    have h3 : P * (1 + s) ≤ (2 * s) * (1 + s) := by nlinarith
    have h4 : (2 * s) * (1 + s) = 2 * s + 2 * (s ^ 2) := by ring
    have h5 : 2 * s + 2 * (s ^ 2) = 2 * s + 2 * L := by
      rw [hs_def, hLsq]
    have h6 : ε * (P * (a + e)) ≤ ε * (2 * s + 2 * L) := by nlinarith
    have h7 : 2 * (P - 1) ≤ 2 * (2 * s - 1) := by nlinarith
    have h8 : 2 * (2 * s - 1) ≤ 4 * s := by nlinarith
    have h9 : ε * (P * (a + e)) + 2 * (P - 1) ≤ ε * (2 * s + 2 * L) + 4 * s := by nlinarith
    have h10 : ε * (2 * s + 2 * L) + 4 * s ≤ 2 * L := by
      -- ε ≤ 1/2, so ε*(2s+2L) ≤ s+L
      -- s ≥ 5, so 5s ≤ s^2 = L
      -- Therefore ε*(2s+2L) + 4s ≤ (s+L) + 4s = L + 5s ≤ L + L = 2L
      have hε_half : ε ≤ 1/2 := hε
      have h_ineq : ε * (2 * s + 2 * L) ≤ s + L := by nlinarith
      have h_5s_le_L : 5 * s ≤ L := by
        -- s ≥ 5, so s^2 ≥ 5s, and s^2 = L
        nlinarith
      nlinarith
    nlinarith
  apply sq_le_sq'
  · -- lower bound: -(2*L/ε) ≤ P*(a+e) + 2*(P-1)/ε
    calc
      -(2 * L / ε) = (-2 * L) / ε := by ring
      _ ≤ (ε * (P * (a + e)) + 2 * (P - 1)) / ε :=
        div_le_div_of_nonneg_right h_lower_mul hε0.le
      _ = P * (a + e) + 2 * (P - 1) / ε := by field_simp [hε0.ne.symm]
  · -- upper bound: P*(a+e) + 2*(P-1)/ε ≤ 2*L/ε
    calc
      P * (a + e) + 2 * (P - 1) / ε = (ε * (P * (a + e)) + 2 * (P - 1)) / ε := by
        field_simp [hε0.ne.symm]
      _ ≤ (2 * L) / ε := div_le_div_of_nonneg_right h_upper_mul hε0.le
      _ = 2 * L / ε := by ring


/-! ## The sum of the second moments -/

/-- The product of standard Gaussians on `Fin d → ℝ` and the standard Gaussian on `E d` give the same integrals. -/
theorem integral_pi_eq (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ z, F (WithLp.toLp 2 z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) =
      ∫ g, F g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h : (Measure.pi fun _ : Fin d => gaussianReal 0 1).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := map_pi_eq_stdGaussian
  rw [← h]
  exact (integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ)) F).symm

/-- `E ‖g‖² = d` under the standard Gaussian, by the coordinates. -/
theorem integral_norm_sq_std : ∫ g, ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = d := by
  rw [← integral_pi_eq (fun g => ‖g‖ ^ 2)]
  have h1 : ∀ i : Fin d, ∫ z : Fin d → ℝ, z i ^ 2 ∂(Measure.pi fun _ => gaussianReal 0 1) = 1 := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
      (by fun_prop)]
    have h := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1) aemeasurable_id
      (by simp [integral_id_gaussianReal])
    rw [variance_id_gaussianReal] at h
    simpa using h.symm
  have h2 : ∀ i : Fin d, Integrable (fun z : Fin d → ℝ => z i ^ 2) (Measure.pi fun _ => gaussianReal 0 1) :=
    fun i => integrable_comp_eval (μ := fun _ : Fin d => gaussianReal 0 1) (f := fun x : ℝ => x ^ 2)
      (memLp_id_gaussianReal 2).integrable_sq
  calc ∫ z, ‖WithLp.toLp 2 z‖ ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
        = ∫ z, ∑ i, z i ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
          integral_congr_ae (ae_of_all _ fun z => by simp [EuclideanSpace.norm_sq_eq])
    _ = ∑ i, ∫ z, z i ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
          integral_finset_sum _ fun i _ => h2 i
    _ = d := by simp [h1]

/-- The crude bound `E v² ≤ 4 ‖T‖² d` at a state with `π(μ) ≤ 1 - ε`. -/
theorem v_sq_crude (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (mu : EuclideanSpace ℝ (Fin d))
    (hmu : gauge K mu ≤ 1 - ε) (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ g, (pipOf K ε (mu + T g) - 1) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 4 * ‖T‖ ^ 2 * d := by
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K := Metric.ball_subset_closedBall.trans hball
  have hK0 : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball
  have hKa : Absorbent ℝ K := absorbent_nhds_zero hK0
  have hε1 : 0 < 1 - ε := by linarith
  have hpt : ∀ g, (pipOf K ε (mu + T g) - 1) ^ 2 ≤ 4 * ‖T‖ ^ 2 * ‖g‖ ^ 2 := by
    intro g
    have hπ0 : 0 ≤ gauge K (T g) := gauge_nonneg _
    have hπ : gauge K (T g) ≤ ‖T‖ * ‖g‖ :=
      le_trans (by simpa using mul_gauge_le_norm hball' (x := T g)) (T.le_opNorm g)
    have hadd : gauge K (mu + T g) ≤ gauge K mu + gauge K (T g) := gauge_add_le hK hKa _ _
    have key : gauge K (mu + T g) / (1 - ε) ≤ 1 + 2 * gauge K (T g) := by
      rw [div_le_iff₀ hε1]
      nlinarith
    have h0 : 0 ≤ pipOf K ε (mu + T g) - 1 := by
      unfold pipOf; linarith [le_max_left 1 (gauge K (mu + T g) / (1 - ε))]
    have h1 : pipOf K ε (mu + T g) - 1 ≤ 2 * (‖T‖ * ‖g‖) := by
      unfold pipOf
      have : max 1 (gauge K (mu + T g) / (1 - ε)) ≤ 1 + 2 * gauge K (T g) := max_le (by linarith) key
      linarith
    calc (pipOf K ε (mu + T g) - 1) ^ 2 ≤ (2 * (‖T‖ * ‖g‖)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * ‖T‖ ^ 2 * ‖g‖ ^ 2 := by ring
  have hint : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm.integrable_sq
  calc ∫ g, (pipOf K ε (mu + T g) - 1) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        ≤ ∫ g, 4 * ‖T‖ ^ 2 * ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          integral_mono_of_nonneg (ae_of_all _ fun g => sq_nonneg _) (hint.const_mul _) (ae_of_all _ hpt)
    _ = 4 * ‖T‖ ^ 2 * d := by rw [integral_const_mul, integral_norm_sq_std]

/-- The arithmetic of the sum, from the rows R5p, R7, R8 and c2dl and `n e^{-L} ≤ 1`: the sum of the bounds of the
rounds is at most `n ε²/4`. -/
theorem vsum_arith (d n L ε lam η δe : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hL : 504 ≤ L) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) (hlam : 0 < lam) (hη : 0 < η) (hde : 0 < δe)
    (hr5p : 352 / 36 * d * L ^ 2 / (lam * η * ε) ≤ n) (hr7 : L ^ 3 / ε ^ 2 ≤ n)
    (hr8 : d ^ 2 * L / ε ≤ Real.sqrt (d * n)) (hc2dl : 2 * δe * d * n / lam ≤ 1) (hnL : n * Real.exp (-L) ≤ 1) :
    2 * L * ε * (d * L / (lam * η)) + n * (2 * L * ε * (2 * δe * d / lam) + Real.exp (-L)) + d / L ≤
      1 / 4 * n * ε ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < d := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hL3 : L ^ 3 ≤ n * ε ^ 2 := by
    have := (div_le_iff₀ hε2).1 hr7
    linarith
  have hL1000 : 1000 * L ≤ L ^ 3 := by nlinarith
  have h1000 : (1000 : ℝ) ≤ L ^ 3 := by nlinarith
  have hX : d * L ^ 2 / (lam * η) ≤ 36 / 352 * (n * ε) := by
    have e : 352 / 36 * d * L ^ 2 / (lam * η * ε) = 352 / 36 * (d * L ^ 2 / (lam * η)) / ε := by
      field_simp
    rw [e, div_le_iff₀ hε0] at hr5p
    linarith
  have hT1 : 2 * L * ε * (d * L / (lam * η)) ≤ 72 / 352 * (n * ε ^ 2) := by
    have e : 2 * L * ε * (d * L / (lam * η)) = 2 * ε * (d * L ^ 2 / (lam * η)) := by ring
    rw [e]
    calc 2 * ε * (d * L ^ 2 / (lam * η)) ≤ 2 * ε * (36 / 352 * (n * ε)) := by gcongr
      _ = 72 / 352 * (n * ε ^ 2) := by ring
  have hT2 : n * (2 * L * ε * (2 * δe * d / lam)) ≤ L := by
    have e : n * (2 * L * ε * (2 * δe * d / lam)) = (2 * L * ε) * (2 * δe * d * n / lam) := by ring
    rw [e]
    calc (2 * L * ε) * (2 * δe * d * n / lam) ≤ (2 * L * ε) * 1 := by gcongr
      _ ≤ L := by nlinarith
  have hd3 : d ^ 3 * L ^ 2 ≤ n * ε ^ 2 := by
    have h0 : 0 ≤ d ^ 2 * L / ε := by positivity
    have hsq := pow_le_pow_left₀ h0 hr8 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    have e : (d ^ 2 * L / ε) ^ 2 = d ^ 4 * L ^ 2 / ε ^ 2 := by ring
    rw [e, div_le_iff₀ hε2] at hsq
    have h2 : d * (d ^ 3 * L ^ 2) ≤ d * (n * ε ^ 2) := by
      have e2 : d * (d ^ 3 * L ^ 2) = d ^ 4 * L ^ 2 := by ring
      have e3 : d * (n * ε ^ 2) = d * n * ε ^ 2 := by ring
      rw [e2, e3]
      exact hsq
    exact le_of_mul_le_mul_left h2 hd0
  have hdL2 : d * L ^ 2 ≤ n * ε ^ 2 := by
    have hdd : d ≤ d ^ 3 := by nlinarith
    calc d * L ^ 2 ≤ d ^ 3 * L ^ 2 := by gcongr
      _ ≤ n * ε ^ 2 := hd3
  have hT4 : d / L ≤ n * ε ^ 2 / 1000 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have h3 : d * L ^ 2 * L ≤ n * ε ^ 2 * L := mul_le_mul_of_nonneg_right hdL2 hL0.le
    have h4 : d * 1000 ≤ d * L ^ 3 := mul_le_mul_of_nonneg_left h1000 hd0.le
    have e : d * L ^ 3 = d * L ^ 2 * L := by ring
    linarith
  rw [mul_add]
  linarith


/-! ## The conditional bound of one round of Y -/

/-- One round of Y given `H`: `E[J min(Y², B) | H] ≤ J (4 P² + 8 v²/ε²)` for `Y = P (a + e) + 2 v/ε`, `J ∈ {0, 1}`,
`P`, `a`, `v` and `J` measurable in `H`, `a ∈ [0, 1]`, `J P` and `J v` bounded, `E[e | H] = 0`, `E[exp(e²) | H] ≤ 2`. -/
theorem condExp_round_le {Ω : Type} (H : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] (μ : Measure[m0] Ω)
    [IsProbabilityMeasure μ] (hH : H ≤ m0) (J P a v : Ω → ℝ) (hJ : StronglyMeasurable[H] J)
    (hJ01 : ∀ ω, J ω = 0 ∨ J ω = 1) (hP : StronglyMeasurable[H] P) (ha : StronglyMeasurable[H] a)
    (ha01 : ∀ ω, a ω ∈ Set.Icc (0 : ℝ) 1) (hv : StronglyMeasurable[H] v) (k : ℝ) (hJP : ∀ ω, |J ω * P ω| ≤ k)
    (hJv : ∀ ω, |J ω * v ω| ≤ k) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (e : Ω → ℝ) (he : Measurable[m0] e)
    (hint : Integrable (fun ω => Real.exp (e ω ^ 2)) μ) (hmean : μ[e | H] =ᵐ[μ] 0)
    (hexp : μ[fun ω => Real.exp (e ω ^ 2) | H] ≤ᵐ[μ] fun _ => 2) :
    μ[fun ω => J ω * min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B | H] ≤ᵐ[μ]
      fun ω => J ω * (4 * P ω ^ 2 + 8 * v ω ^ 2 / ε ^ 2) := by
  have hJ0 : ∀ ω, 0 ≤ J ω := fun ω => by rcases hJ01 ω with h | h <;> simp [h]
  have hJ2 : ∀ ω, J ω ^ 2 = J ω := fun ω => by rcases hJ01 ω with h | h <;> simp [h]
  have hJm : Measurable[m0] J := (hJ.mono hH).measurable
  have hPm : Measurable[m0] P := (hP.mono hH).measurable
  have ham : Measurable[m0] a := (ha.mono hH).measurable
  have hvm : Measurable[m0] v := (hv.mono hH).measurable
  have he2 : ∀ ω, e ω ^ 2 ≤ Real.exp (e ω ^ 2) := fun ω => by linarith [Real.add_one_le_exp (e ω ^ 2)]
  have hk : ∀ ω, (J ω * P ω) ^ 2 ≤ k ^ 2 := fun ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hJP ω) 2
  have hkv : ∀ ω, (J ω * v ω) ^ 2 ≤ k ^ 2 := fun ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hJv ω) 2
  have hae : ∀ ω, (a ω + e ω) ^ 2 ≤ 2 + 2 * Real.exp (e ω ^ 2) := fun ω => by
    have h1 := (ha01 ω).1
    have h2 := (ha01 ω).2
    have ha2 : a ω ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (a ω - e ω), he2 ω]
  set f1 : Ω → ℝ := fun ω => (J ω * P ω) ^ 2 * (a ω + e ω) ^ 2 with hf1def
  set G : Ω → ℝ := fun ω => 8 * (J ω * v ω) ^ 2 / ε ^ 2 with hGdef
  have hf1 : Integrable f1 μ := by
    have hg : Integrable (fun ω => k ^ 2 * (2 + 2 * Real.exp (e ω ^ 2))) μ :=
      ((integrable_const (2 : ℝ)).add (hint.const_mul 2)).const_mul (k ^ 2)
    refine hg.mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact (((hJm.mul hPm).pow_const 2).mul ((ham.add he).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (hk ω) (hae ω) (sq_nonneg _) ((sq_nonneg _).trans (hk ω))
  have hGmH : Measurable[H] G :=
    (((hJ.measurable.mul hv.measurable).pow_const 2).const_mul 8).div_const _
  have hGm : StronglyMeasurable[H] G := hGmH.stronglyMeasurable
  have hGi : Integrable G μ := by
    refine Integrable.of_bound (hGm.mono hH).aestronglyMeasurable (8 * k ^ 2 / ε ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hkv ω
    simp only [G]
    gcongr
  have hLm : Measurable[m0] fun ω => J ω * min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B :=
    hJm.mul ((((hPm.mul (ham.add he)).add ((hvm.const_mul 2).div_const ε)).pow_const 2).min measurable_const)
  have hLi : Integrable (fun ω => J ω * min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B) μ := by
    refine Integrable.of_bound hLm.aestronglyMeasurable B (ae_of_all _ fun ω => ?_)
    have hmin0 : 0 ≤ min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B := le_min (sq_nonneg _) hB
    rcases hJ01 ω with h | h
    · simp only [h, zero_mul, norm_zero]; exact hB
    · simp only [h, one_mul, Real.norm_eq_abs]; rw [abs_of_nonneg hmin0]; exact min_le_right _ _
  have hpt : ∀ ω, J ω * min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B ≤ ((2 : ℝ) • f1 + G) ω := by
    intro ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, f1, G]
    rcases hJ01 ω with h | h
    · rw [h]; simp only [zero_mul]; positivity
    · rw [h]
      have h1 : min ((P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2) B ≤ (P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2 :=
        min_le_left _ _
      have h2 : (P ω * (a ω + e ω) + 2 * v ω / ε) ^ 2 ≤
          2 * (P ω * (a ω + e ω)) ^ 2 + 2 * (2 * v ω / ε) ^ 2 := by
        nlinarith [sq_nonneg (P ω * (a ω + e ω) - 2 * v ω / ε)]
      have h3 : 2 * (P ω * (a ω + e ω)) ^ 2 + 2 * (2 * v ω / ε) ^ 2 =
          2 * ((1 * P ω) ^ 2 * (a ω + e ω) ^ 2) + 8 * (1 * v ω) ^ 2 / ε ^ 2 := by ring
      linarith
  have hmono := condExp_mono (m := H) hLi ((hf1.smul (2 : ℝ)).add hGi) (ae_of_all _ hpt)
  have hlin : μ[(2 : ℝ) • f1 + G | H] =ᵐ[μ] (2 : ℝ) • μ[f1 | H] + G := by
    filter_upwards [condExp_add (hf1.smul (2 : ℝ)) hGi H, condExp_smul (μ := μ) (2 : ℝ) f1 H] with ω h1 h2
    rw [h1, Pi.add_apply, Pi.add_apply, h2, condExp_of_stronglyMeasurable hH hGm hGi]
  have hobs := condExp_obs_sq_le H μ hH a (fun ω => J ω * P ω) ha ha01 (hJ.mul hP) k hJP e he hint hmean hexp
  filter_upwards [hmono, hlin, hobs] with ω h1 h2 h3
  refine h1.trans ?_
  rw [h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (J ω * P ω) ^ 2 = J ω * P ω ^ 2 := by rw [mul_pow, hJ2]
  have e2 : G ω = J ω * (8 * v ω ^ 2 / ε ^ 2) := by
    simp only [G]; rw [mul_pow, hJ2]; ring
  have h3' : μ[f1 | H] ω ≤ 2 * (J ω * P ω) ^ 2 := h3
  rw [e2]
  nlinarith [hJ0 ω]

/-- The tower through a finer sigma-field and freezing: if `E[Y | H] ≤ F(x, ζ)` with `𝒢 ≤ H`, `x` measurable in `𝒢`,
`ζ` independent of `𝒢` and `F` measurable and bounded, then `E[Y | 𝒢] ≤ ∫ F(x, z) d(law ζ)(z)`. -/
theorem condExp_le_freeze (hFR : LemmaFR) {Ω X Z : Type} (𝒢 H : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] (μ : Measure[m0] Ω)
    [IsProbabilityMeasure μ] (h𝒢H : 𝒢 ≤ H) (hH : H ≤ m0) (x : Ω → X) (ζ : Ω → Z) (hx : Measurable[𝒢] x)
    (hζ : Measurable[m0] ζ) (hind : @Indep Ω (MeasurableSpace.comap ζ inferInstance) 𝒢 m0 μ) (Y : Ω → ℝ)
    (_hY : Integrable Y μ) (F : X × Z → ℝ) (hF : Measurable F) (C : ℝ) (hF0 : ∀ y, 0 ≤ F y) (hFC : ∀ y, F y ≤ C)
    (hYF : μ[Y | H] ≤ᵐ[μ] fun ω => F (x ω, ζ ω)) :
    μ[Y | 𝒢] ≤ᵐ[μ] fun ω => ∫ z, F (x ω, z) ∂(@Measure.map Ω Z m0 _ ζ μ) := by
  have hm := h𝒢H.trans hH
  have hFx : Measurable[m0] fun ω => F (x ω, ζ ω) := hF.comp ((hx.mono hm le_rfl).prodMk hζ)
  have hint : Integrable (fun ω => F (x ω, ζ ω)) μ :=
    Integrable.of_bound hFx.aestronglyMeasurable C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]; exact hFC _)
  have h1 : μ[μ[Y | H] | 𝒢] =ᵐ[μ] μ[Y | 𝒢] := condExp_condExp_of_le h𝒢H hH
  have h2 : μ[μ[Y | H] | 𝒢] ≤ᵐ[μ] μ[fun ω => F (x ω, ζ ω) | 𝒢] := condExp_mono integrable_condExp hint hYF
  have h3 := hFR Ω X Z 𝒢 μ x ζ F hm hx hζ hind hF hint
  exact h1.symm.trans_le (h2.trans h3.le)

/-- Freedman's inequality with a bound `W` of the conditional means: with probability at least `1 - δ`,
`∑_{u < t} Z_u < 2 ∑_{u < t} W_u + B log(1/δ)` for every `t ≤ N`. -/
theorem freedman_W {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒢 : Filtration ℕ m0) (Z W : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 < B) (hZm : ∀ t, StronglyMeasurable[𝒢 (t + 1)] (Z t))
    (hZ0 : ∀ t ω, 0 ≤ Z t ω) (hZB : ∀ t ω, Z t ω ≤ B) (hW : ∀ t, μ[Z t | 𝒢 t] ≤ᵐ[μ] W t) (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    μ {ω | ∃ t ≤ N, 2 * ∑ u ∈ Finset.range t, W u ω + B * Real.log (1 / δ) ≤ ∑ u ∈ Finset.range t, Z u ω} ≤
      ENNReal.ofReal δ := by
  have hae : ∀ᵐ ω ∂μ, ∀ t, μ[Z t | 𝒢 t] ω ≤ W t ω := ae_all_iff.2 hW
  refine le_trans (measure_mono_ae ?_) (freedman_uniform μ 𝒢 Z B hB hZm hZ0 hZB N δ hδ)
  filter_upwards [hae] with ω hω hmem
  obtain ⟨t, ht, h⟩ := hmem
  refine ⟨t, ht, le_trans ?_ h⟩
  have := Finset.sum_le_sum fun u (_ : u ∈ Finset.range t) => hω u
  linarith

/-- `v² = (pip - 1)²` at the play is integrable under the product of standard Gaussians. -/
theorem integrable_vsq_pi (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1) (mu : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) :
    MeasureTheory.Integrable (fun z : Fin d → ℝ => (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K := by
    intro x hx
    apply hball
    rw [Metric.mem_closedBall]
    have hx' := Metric.mem_ball.mp hx
    linarith
  have hgauge_le_norm (x : EuclideanSpace ℝ (Fin d)) : gauge K x ≤ ‖x‖ := by
    have h := mul_gauge_le_norm (x := x) hball'
    linarith
  have h_pip_sub_le (x : EuclideanSpace ℝ (Fin d)) : pipOf K ε x - 1 ≤ gauge K x / (1 - ε) := by
    dsimp [pipOf]
    by_cases hg : gauge K x / (1 - ε) ≤ 1
    · have hmax : max 1 (gauge K x / (1 - ε)) = 1 := max_eq_left hg
      rw [hmax]
      have h_nonneg : 0 ≤ gauge K x / (1 - ε) := div_nonneg (gauge_nonneg _) (by linarith)
      linarith
    · have hmax : max 1 (gauge K x / (1 - ε)) = gauge K x / (1 - ε) := max_eq_right (by linarith)
      rw [hmax]
      linarith
  have h_pip_bound (x : EuclideanSpace ℝ (Fin d)) : pipOf K ε x - 1 ≤ ‖x‖ / (1 - ε) := by
    have hε1 : 0 < 1 - ε := by linarith
    have hdiv : gauge K x / (1 - ε) ≤ ‖x‖ / (1 - ε) := by
      gcongr
      exact hgauge_le_norm x
    linarith [h_pip_sub_le x, hdiv]
  have h_pip_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ pipOf K ε x - 1 := by
    dsimp [pipOf]
    have h1 : 1 ≤ max 1 (gauge K x / (1 - ε)) := le_max_left _ _
    linarith
  have hε1 : 0 < 1 - ε := by linarith
  -- Define the linear map T = toEuclideanCLM A
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A
  have hT_mulVec (z : Fin d → ℝ) : T (WithLp.toLp 2 z) = WithLp.toLp 2 (A.mulVec z) := by
    simpa [T] using Matrix.toEuclideanCLM_toLp A z
  have h_bound (z : Fin d → ℝ) : pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1 ≤
      (‖WithLp.toLp 2 mu‖ + |1 - lam| * ‖T‖ * ‖WithLp.toLp 2 z‖) / (1 - ε) := by
    have hx : WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z)) =
        WithLp.toLp 2 mu + (1 - lam) • T (WithLp.toLp 2 z) := by
      calc
        WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))
            = WithLp.toLp 2 mu + WithLp.toLp 2 ((1 - lam) • (A.mulVec z)) := by
          simpa using map_add (WithLp.toLp 2 : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) mu ((1 - lam) • (A.mulVec z))
        _ = WithLp.toLp 2 mu + (1 - lam) • WithLp.toLp 2 (A.mulVec z) := by
          simp
        _ = WithLp.toLp 2 mu + (1 - lam) • T (WithLp.toLp 2 z) := by rw [hT_mulVec]
    rw [hx]
    calc
      pipOf K ε (WithLp.toLp 2 mu + (1 - lam) • T (WithLp.toLp 2 z)) - 1
          ≤ ‖WithLp.toLp 2 mu + (1 - lam) • T (WithLp.toLp 2 z)‖ / (1 - ε) := h_pip_bound _
      _ ≤ (‖WithLp.toLp 2 mu‖ + ‖(1 - lam) • T (WithLp.toLp 2 z)‖) / (1 - ε) := by
        gcongr
        exact norm_add_le _ _
      _ = (‖WithLp.toLp 2 mu‖ + |1 - lam| * ‖T (WithLp.toLp 2 z)‖) / (1 - ε) := by
        simp [norm_smul]
      _ ≤ (‖WithLp.toLp 2 mu‖ + |1 - lam| * (‖T‖ * ‖WithLp.toLp 2 z‖)) / (1 - ε) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm T (WithLp.toLp 2 z)
      _ = (‖WithLp.toLp 2 mu‖ + |1 - lam| * ‖T‖ * ‖WithLp.toLp 2 z‖) / (1 - ε) := by ring
  -- Now we have: 0 ≤ f(z) ≤ ((C1 + C2 * ‖z‖_euclidean) / (1-ε))^2 ≤ C * (1 + ‖z‖_euclidean^2)
  -- where ‖z‖_euclidean = ‖WithLp.toLp 2 z‖
  have h_cont_gauge : Continuous (gauge K) :=
    continuous_gauge hK (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)) hball)
  have h_cont_pipOf : Continuous (pipOf K ε) := by
    unfold pipOf
    refine Continuous.max continuous_const ?_
    exact (h_cont_gauge.div_const (1 - ε))
  have h_cont_inner : Continuous (fun z : Fin d → ℝ => WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) := by
    -- matrix multiplication, addition, scalar multiplication are continuous
    -- WithLp.toLp 2 is continuous
    fun_prop
  have h_cont_sq : Continuous (fun z : Fin d → ℝ => (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2) := by
    fun_prop
  have h_meas : AEStronglyMeasurable (fun z : Fin d → ℝ => (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    h_cont_sq.aestronglyMeasurable
  -- Bound the function by C * (1 + ‖WithLp.toLp 2 z‖^2)
  set C1 := ‖WithLp.toLp 2 mu‖ with hC1
  set C2 := |1 - lam| * ‖T‖ with hC2
  have hC2_nonneg : 0 ≤ C2 := by
    dsimp [C2]
    positivity
  have h_bound_sq (z : Fin d → ℝ) : (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2 ≤
      ((C1 + C2 * ‖WithLp.toLp 2 z‖) / (1 - ε)) ^ 2 := by
    have h_nonneg : 0 ≤ pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1 :=
      h_pip_nonneg _
    have h_le : pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1 ≤ (C1 + C2 * ‖WithLp.toLp 2 z‖) / (1 - ε) := by
      simpa [C1, C2] using h_bound z
    nlinarith
  -- Bound: (C1 + C2*t)^2 ≤ (C1^2 + C2^2)*(1 + t^2) because
  -- (C1^2 + C2^2)*(1 + t^2) - (C1 + C2*t)^2 = (C1*t - C2)^2 ≥ 0
  set M := (C1 ^ 2 + C2 ^ 2) / ((1 - ε) ^ 2) with hM
  have h_bound_quad (t : ℝ) (ht : 0 ≤ t) : ((C1 + C2 * t) / (1 - ε)) ^ 2 ≤ M + M * t ^ 2 := by
    have hε_pos : 0 < 1 - ε := by linarith
    have h_sq_diff : (C1 ^ 2 + C2 ^ 2) * (1 + t ^ 2) - (C1 + C2 * t) ^ 2 = (C1 * t - C2) ^ 2 := by
      ring
    have h_nonneg_diff : 0 ≤ (C1 ^ 2 + C2 ^ 2) * (1 + t ^ 2) - (C1 + C2 * t) ^ 2 := by
      rw [h_sq_diff]
      apply pow_two_nonneg
    have h_main : (C1 + C2 * t) ^ 2 ≤ (C1 ^ 2 + C2 ^ 2) * (1 + t ^ 2) := by linarith
    calc
      ((C1 + C2 * t) / (1 - ε)) ^ 2 = (C1 + C2 * t) ^ 2 / ((1 - ε) ^ 2) := by rw [div_pow]
      _ ≤ ((C1 ^ 2 + C2 ^ 2) * (1 + t ^ 2)) / ((1 - ε) ^ 2) := by gcongr
      _ = (C1 ^ 2 + C2 ^ 2) / ((1 - ε) ^ 2) * (1 + t ^ 2) := by rw [div_mul_eq_mul_div]
      _ = M * (1 + t ^ 2) := by rw [hM]
      _ = M + M * t ^ 2 := by ring
  have h_bound_final (z : Fin d → ℝ) : (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2 ≤
      M + M * ‖WithLp.toLp 2 z‖ ^ 2 := by
    have h_nonneg_norm : 0 ≤ ‖WithLp.toLp 2 z‖ := norm_nonneg _
    calc
      (pipOf K ε (WithLp.toLp 2 (mu + (1 - lam) • (A.mulVec z))) - 1) ^ 2
          ≤ ((C1 + C2 * ‖WithLp.toLp 2 z‖) / (1 - ε)) ^ 2 := h_bound_sq z
      _ ≤ M + M * ‖WithLp.toLp 2 z‖ ^ 2 := h_bound_quad (‖WithLp.toLp 2 z‖) h_nonneg_norm
  -- Now show that M + M * ‖WithLp.toLp 2 z‖^2 is integrable
  have h_int_norm_sq : Integrable (fun z : Fin d → ℝ => ‖WithLp.toLp 2 z‖ ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    have h_map := map_pi_eq_stdGaussian (ι := Fin d)
    have h_int_std : Integrable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_mem : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        IsGaussian.memLp_two_id
      have h_ae : AEStronglyMeasurable id (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        continuous_id.aestronglyMeasurable
      have h := ((memLp_two_iff_integrable_sq_norm h_ae).mp h_mem)
      simpa using h
    -- Rewrite using the map equality
    rw [← h_map] at h_int_std
    -- Now h_int_std : Integrable (fun y => ‖y‖^2) ((Measure.pi ...).map (toLp 2))
    -- Use Integrable.comp_measurable
    -- Note: (fun y => ‖y‖^2) ∘ (WithLp.toLp 2) = fun z => ‖WithLp.toLp 2 z‖^2 definitionally
    exact h_int_std.comp_measurable (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ))
  have h_int_bound : Integrable (fun z : Fin d → ℝ => M + M * ‖WithLp.toLp 2 z‖ ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    have h_int_const : Integrable (fun _ : Fin d → ℝ => M) (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
      apply integrable_const
    have h_int_mul : Integrable (fun z : Fin d → ℝ => M * ‖WithLp.toLp 2 z‖ ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
      h_int_norm_sq.const_mul M
    exact h_int_const.add h_int_mul
  -- Now apply Integrable.mono' to conclude
  -- Integrable.mono' hg hf h : Integrable g μ → AEStronglyMeasurable f μ → (∀ᵐ a, ‖f a‖ ≤ g a) → Integrable f μ
  refine Integrable.mono' h_int_bound h_meas ?_
  refine ae_of_all _ (fun z => ?_)
  -- Need: ‖(pipOf ... - 1)^2‖ ≤ M + M * ‖WithLp.toLp 2 z‖^2
  -- Since the LHS is nonnegative, ‖LHS‖ = LHS
  have h_bound_goal : (pipOf K ε (WithLp.toLp 2 mu + (1 - lam) • WithLp.toLp 2 (A *ᵥ z)) - 1) ^ 2 ≤
      M + M * ‖WithLp.toLp 2 z‖ ^ 2 := by
    -- h_bound_final uses T, but T (WithLp.toLp 2 z) = WithLp.toLp 2 (A.mulVec z)
    simpa [T, hT_mulVec] using h_bound_final z
  rw [Real.norm_of_nonneg (pow_two_nonneg _)]
  exact h_bound_goal

/-- The deviation term of Y: `(4 L²/ε²) log(7/δ_e) ≤ n` from the row R7 and `L = 36 log(1/δ_e)`,
`log(1/δ_e) ≥ 14`. -/
theorem yb_arith (n L ε δe : ℝ) (hde : 0 < δe) (hx : 14 ≤ Real.log (1 / δe)) (hL : L = 36 * Real.log (1 / δe))
    (hε0 : 0 < ε) (hr7 : L ^ 3 / ε ^ 2 ≤ n) : 4 * L ^ 2 / ε ^ 2 * Real.log (1 / (δe / 7)) ≤ n := by
  have hlog : Real.log (1 / (δe / 7)) = Real.log 7 + Real.log (1 / δe) := by
    rw [show 1 / (δe / 7) = 7 * (1 / δe) by field_simp]
    exact Real.log_mul (by norm_num) (by positivity)
  have h7 : Real.log 7 < 6 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 7) (by norm_num)
    linarith
  have hlogle : Real.log (1 / (δe / 7)) ≤ L / 4 := by rw [hlog, hL]; linarith
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hpos : 0 ≤ 4 * L ^ 2 / ε ^ 2 := by positivity
  calc 4 * L ^ 2 / ε ^ 2 * Real.log (1 / (δe / 7)) ≤ 4 * L ^ 2 / ε ^ 2 * (L / 4) :=
        mul_le_mul_of_nonneg_left hlogle hpos
    _ = L ^ 3 / ε ^ 2 := by ring
    _ ≤ n := hr7

end AdversarialBco.Poly.EvGY
