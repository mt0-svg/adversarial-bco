/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Game

@[expose] public section

/-!
# The regret under the null world: Facts 4 and 5 and Chebyshev in the tip

Facts 4 and 5 and Chebyshev at the Gaussian price. The fake run reads no tip, so given the noise
and the seed `y` the plays `x̃_t` and the rounds `I_y` before the budget is spent are fixed, and the stopped sum
`S = Σ_{t ∈ I_y} D(x̃_t; θ)` is a sum of functions of the tip `θ ~ U`:

* `cheb_points`: for fixed plays, `U(S < (1 - η) M) ≤ n a/(η² M)`, `M = Σ_{t ∈ I} E D(x_t; ·)`, when
  `E (q - D)² ≤ a E D` at every play (Lemma PRICE-U (ii));
* `stop_mass_ge` (Fact 5): `M_y ≥ min(n f₀, B/Π)` when `E D ≥ f₀` and `c(x) ≤ Π E D` at every play (Facts 4, 5);
* `prob_stopS_lt`: `P(S < (1 - η) M₀) ≤ n a/(η² M₀)` over the whole sample, for `0 < M₀ ≤ min(n f₀, B/Π)`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace AdversarialBco.Grow

open AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Stop

variable {d : ℕ}

/-! ## Chebyshev in the tip for fixed plays -/

/-- `E (X - E X)² ≤ E (X - c)²` under the tip law. -/
theorem integral_sq_sub_mean_le {X : E d → ℝ} (hX : Measurable X) (c : ℝ) :
    ∫ θ, (X θ - ∫ θ', X θ' ∂tipLaw d) ^ 2 ∂tipLaw d ≤ ∫ θ, (X θ - c) ^ 2 ∂tipLaw d := by
  rw [← variance_eq_integral hX.aemeasurable, ← variance_sub_const hX.aestronglyMeasurable c]
  exact variance_le_expectation_sq (hX.sub_const c).aestronglyMeasurable

/-- **Chebyshev for fixed plays.** -/
theorem cheb_points {g k a η : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (hη : 0 < η) {n : ℕ} (I : Finset ℕ)
    (hI : I.card ≤ n) (x : ℕ → E d)
    (hgap : ∀ t ∈ I, ∫ θ, (bowlG d g k (x t) - dentG d g k θ (x t)) ^ 2 ∂tipLaw d ≤
      a * ∫ θ, dentG d g k θ (x t) ∂tipLaw d)
    (hM : 0 < ∑ t ∈ I, ∫ θ, dentG d g k θ (x t) ∂tipLaw d) :
    (tipLaw d).real {θ | ∑ t ∈ I, dentG d g k θ (x t) < (1 - η) * ∑ t ∈ I, ∫ θ, dentG d g k θ (x t) ∂tipLaw d} ≤
      n * a / (η ^ 2 * ∑ t ∈ I, ∫ θ, dentG d g k θ (x t) ∂tipLaw d) := by
  set M := ∑ t ∈ I, ∫ θ, dentG d g k θ (x t) ∂tipLaw d with hM_def
  set m : ℕ → ℝ := fun t => ∫ θ, dentG d g k θ (x t) ∂tipLaw d with hm_def
  have hDm : ∀ t, Measurable fun θ => dentG d g k θ (x t) := fun t =>
    measurable_dent_tip _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) (x t)
  set Y : E d → ℝ := fun θ => ∑ t ∈ I, (dentG d g k θ (x t) - m t) with hY
  have hYm : Measurable Y := Finset.measurable_sum _ fun t _ => (hDm t).sub_const _
  have hsub : {θ | ∑ t ∈ I, dentG d g k θ (x t) < (1 - η) * M} ⊆ {θ | (η * M) ^ 2 ≤ Y θ ^ 2} := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ ⊢
    have hYθ : Y θ = ∑ t ∈ I, dentG d g k θ (x t) - M := by
      simp only [hY, Finset.sum_sub_distrib, hM_def, hm_def]
    have h1 : η * M < -Y θ := by rw [hYθ]; linarith
    have h2 : 0 ≤ η * M := by positivity
    nlinarith
  have hY2 : ∫ θ, Y θ ^ 2 ∂tipLaw d ≤ n * (a * M) := by
    have hpt : ∀ θ, Y θ ^ 2 ≤ I.card * ∑ t ∈ I, (dentG d g k θ (x t) - m t) ^ 2 := fun θ =>
      sq_sum_le_card_mul_sum_sq
    have hi : ∀ t, Integrable (fun θ => (dentG d g k θ (x t) - m t) ^ 2) (tipLaw d) := fun t =>
      integrable_tipLaw (((hDm t).sub_const _).pow_const 2)
    calc ∫ θ, Y θ ^ 2 ∂tipLaw d
        ≤ ∫ θ, (I.card : ℝ) * ∑ t ∈ I, (dentG d g k θ (x t) - m t) ^ 2 ∂tipLaw d :=
          integral_mono (integrable_tipLaw (hYm.pow_const 2))
            ((integrable_finsetSum _ fun t _ => hi t).const_mul _) hpt
      _ = I.card * ∑ t ∈ I, ∫ θ, (dentG d g k θ (x t) - m t) ^ 2 ∂tipLaw d := by
          rw [integral_const_mul, integral_finsetSum _ fun t _ => hi t]
      _ ≤ I.card * ∑ t ∈ I, a * m t := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t ht => ?_) (Nat.cast_nonneg _)
          refine (integral_sq_sub_mean_le (hDm t) (bowlG d g k (x t))).trans ?_
          refine le_trans (le_of_eq ?_) (hgap t ht)
          congr 1
          funext θ
          ring
      _ = I.card * (a * M) := by rw [← Finset.mul_sum]
      _ ≤ n * (a * M) := by
          have haM : 0 ≤ a * M := by
            rw [hM_def, Finset.mul_sum]
            exact Finset.sum_nonneg fun t ht => (integral_nonneg fun θ => sq_nonneg _).trans (hgap t ht)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) haM
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := tipLaw d) (f := fun θ => Y θ ^ 2)
    (ae_of_all _ fun θ => sq_nonneg _) (integrable_tipLaw (hYm.pow_const 2)) ((η * M) ^ 2)
  have hpos : 0 < (η * M) ^ 2 := by positivity
  calc (tipLaw d).real {θ | ∑ t ∈ I, dentG d g k θ (x t) < (1 - η) * M}
      ≤ (tipLaw d).real {θ | (η * M) ^ 2 ≤ Y θ ^ 2} := measureReal_mono hsub
    _ ≤ n * (a * M) / (η * M) ^ 2 := by
        rw [le_div_iff₀ hpos]
        linarith
    _ = n * a / (η ^ 2 * M) := by
        field_simp

/-! ## The rounds before the budget is spent, and Fact 5 -/

variable {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- The rounds `t < n` before the budget is spent: `C_u ≤ B` for every `u < t`. -/
noncomputable def roundsI (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (y : (ℕ → ℝ) × Ω) : Finset ℕ :=
  (range n).filter fun t => ∀ u ∈ range t, cumF P pol n u y ≤ B

/-- The mean of the stopped sum given the noise and the seed: `M_y = Σ_{t ∈ I_y} E D(x̃_t; ·)`. -/
noncomputable def massM (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (y : (ℕ → ℝ) × Ω) : ℝ :=
  ∑ t ∈ roundsI P pol n B y, ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d

omit [MeasurableSpace Ω] in
theorem stopS_eq (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (θ : E d) (y : (ℕ → ℝ) × Ω) :
    stopS P pol n B (θ, y) = ∑ t ∈ roundsI P pol n B y, dentG d P.g P.k θ (xF P pol t y) := by
  unfold stopS roundsI
  rw [Finset.sum_filter]

omit [MeasurableSpace Ω] in
/-- **Fact 5**: `M_y ≥ min(n f₀, B/Π)` when `E D ≥ f₀` and `c(x) ≤ Π E D` at every play. -/
theorem stop_mass_ge {P : GP} {pol : Learner Ω d} {n : ℕ} {B f0 cPi : ℝ} (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hfloor : ∀ x, f0 ≤ ∫ θ, dentG d P.g P.k θ x ∂tipLaw d)
    (hprice : ∀ x, cG P x ≤ cPi * ∫ θ, dentG d P.g P.k θ x ∂tipLaw d) (hPi : 0 < cPi) (y : (ℕ → ℝ) × Ω) :
    min (n * f0) (B / cPi) ≤ massM P pol n B y := by
  have hD0 : ∀ x, 0 ≤ ∫ θ, dentG d P.g P.k θ x ∂tipLaw d := fun x =>
    integral_nonneg fun θ => dentG_nonneg hg hk θ x
  by_cases h : ∃ t, t < n ∧ B < cumF P pol n t y
  · classical
    set t0 := Nat.find h with ht0
    obtain ⟨ht0n, ht0B⟩ := Nat.find_spec h
    have hmin : ∀ u < t0, cumF P pol n u y ≤ B := fun u hu => by
      have := Nat.find_min h hu
      push Not at this
      exact this (by omega)
    have hsub : range (t0 + 1) ⊆ roundsI P pol n B y := fun t ht => by
      have ht' : t ≤ t0 := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
      unfold roundsI
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.2 (by omega), fun u hu => hmin u (by have := Finset.mem_range.1 hu; omega)⟩
    have h1 : ∑ t ∈ range (t0 + 1), ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d ≤ massM P pol n B y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hD0 _
    have h2 : cumF P pol n t0 y ≤ cPi * ∑ t ∈ range (t0 + 1), ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d := by
      unfold cumF
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun t ht => ?_
      have ht' : t < n := by have := Finset.mem_range.1 ht; omega
      unfold priceF
      rw [ite_eq_left ht']
      exact hprice _
    have h3 : B / cPi < ∑ t ∈ range (t0 + 1), ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d := by
      rw [div_lt_iff₀ hPi]
      linarith
    exact (min_le_right _ _).trans (h3.le.trans h1)
  · push Not at h
    have hall : roundsI P pol n B y = range n := by
      unfold roundsI
      rw [Finset.filter_eq_self]
      intro t ht u hu
      exact h u (by have := Finset.mem_range.1 ht; have := Finset.mem_range.1 hu; omega)
    refine (min_le_left _ _).trans ?_
    unfold massM
    rw [hall]
    calc (n : ℝ) * f0 = ∑ _t ∈ range n, f0 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ => hfloor _

/-! ## Chebyshev over the whole sample -/

theorem measurable_stopS {P : GP} {pol : Learner Ω d} {n : ℕ} (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) (B : ℝ) :
    Measurable (stopS P pol n B) := by
  unfold stopS
  refine Finset.measurable_sum _ fun t ht => ?_
  refine Measurable.ite ?_ (measurable_dentG_play hg hk measurable_fst
    ((measurable_xF hpol (Finset.mem_range.1 ht)).comp measurable_snd)) measurable_const
  have : {s : Sample d Ω | ∀ u ∈ range t, cumF P pol n u s.2 ≤ B} =
      ⋂ u ∈ range t, {s : Sample d Ω | cumF P pol n u s.2 ≤ B} := by
    ext s
    simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun u _ =>
    measurableSet_le ((measurable_cumF hg hk hpol u).comp measurable_snd) measurable_const

/-- **Chebyshev in the tip**, integrated over the noise and the seed: `P(S < (1 - η) M₀) ≤ n a/(η² M₀)` when
`0 < M₀ ≤ M_y` for every `y` and `E (q - D)² ≤ a E D` at every play. -/
theorem prob_stopS_lt (μ : Measure Ω) [IsProbabilityMeasure μ] {P : GP} {pol : Learner Ω d} {n : ℕ} {B a η M0 : ℝ}
    (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    (ha : 0 ≤ a) (hη : 0 < η) (hη1 : η ≤ 1) (hM0 : 0 < M0) (hM : ∀ y, M0 ≤ massM P pol n B y)
    (hgap : ∀ x, ∫ θ, (bowlG d P.g P.k x - dentG d P.g P.k θ x) ^ 2 ∂tipLaw d ≤
      a * ∫ θ, dentG d P.g P.k θ x ∂tipLaw d) :
    (gameLaw (tipLaw d) μ).real {s | stopS P pol n B s < (1 - η) * M0} ≤ n * a / (η ^ 2 * M0) := by
  have hG := isProbabilityMeasure_gameLaw (tipLaw d) μ
  have hA : MeasurableSet {s : Sample d Ω | stopS P pol n B s < (1 - η) * M0} :=
    measurableSet_lt (measurable_stopS hg hk hpol B) measurable_const
  have hc : 0 ≤ n * a / (η ^ 2 * M0) := by positivity
  have hsec : ∀ y : (ℕ → ℝ) × Ω, tipLaw d ((fun θ => ((θ, y) : Sample d Ω)) ⁻¹'
      {s | stopS P pol n B s < (1 - η) * M0}) ≤ ENNReal.ofReal (n * a / (η ^ 2 * M0)) := fun y => by
    have hMy := hM y
    have hMy0 : 0 < massM P pol n B y := hM0.trans_le hMy
    have hsub : (fun θ => ((θ, y) : Sample d Ω)) ⁻¹' {s | stopS P pol n B s < (1 - η) * M0} ⊆
        {θ | ∑ t ∈ roundsI P pol n B y, dentG d P.g P.k θ (xF P pol t y) <
          (1 - η) * ∑ t ∈ roundsI P pol n B y, ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d} := by
      intro θ hθ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, stopS_eq] at hθ ⊢
      have : (1 - η) * M0 ≤ (1 - η) * massM P pol n B y := mul_le_mul_of_nonneg_left hMy (by linarith)
      unfold massM at this
      linarith
    have hcard : (roundsI P pol n B y).card ≤ n := by
      unfold roundsI
      exact (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have h := cheb_points (x := fun t => xF P pol t y) hg hk hη _ hcard (fun t _ => hgap _) hMy0
    have h' : (tipLaw d).real {θ | ∑ t ∈ roundsI P pol n B y, dentG d P.g P.k θ (xF P pol t y) <
          (1 - η) * ∑ t ∈ roundsI P pol n B y, ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d} ≤
        n * a / (η ^ 2 * M0) := by
      refine h.trans ?_
      unfold massM at hMy hMy0
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hMy (by positivity))
    calc tipLaw d ((fun θ => ((θ, y) : Sample d Ω)) ⁻¹' {s | stopS P pol n B s < (1 - η) * M0})
        ≤ tipLaw d {θ | ∑ t ∈ roundsI P pol n B y, dentG d P.g P.k θ (xF P pol t y) <
          (1 - η) * ∑ t ∈ roundsI P pol n B y, ∫ θ, dentG d P.g P.k θ (xF P pol t y) ∂tipLaw d} :=
          measure_mono hsub
      _ = ENNReal.ofReal ((tipLaw d).real _) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (n * a / (η ^ 2 * M0)) := ENNReal.ofReal_le_ofReal h'
  have hP : gameLaw (tipLaw d) μ {s | stopS P pol n B s < (1 - η) * M0} ≤ ENNReal.ofReal (n * a / (η ^ 2 * M0)) := by
    unfold gameLaw
    rw [Measure.prod_apply_symm hA]
    calc ∫⁻ y, tipLaw d ((fun θ => ((θ, y) : Sample d Ω)) ⁻¹' {s | stopS P pol n B s < (1 - η) * M0})
          ∂(RealRAM.gaussStream.prod μ)
        ≤ ∫⁻ _y, ENNReal.ofReal (n * a / (η ^ 2 * M0)) ∂(RealRAM.gaussStream.prod μ) := lintegral_mono hsec
      _ = ENNReal.ofReal (n * a / (η ^ 2 * M0)) := by
        rw [lintegral_const, measure_univ, mul_one]
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc hP

end AdversarialBco.Grow
