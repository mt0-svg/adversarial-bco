/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBody

@[expose] public section

/-!
# Set-up facts of Proposition 2.2

Monotonicity of hypothesis (H) in `β`, the inner body contains a ball of radius `1/2`, a body containing a ball of
radius `1/2` has diameter at least `1`, and the reindexing of a law to its positive weights.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.hypH_mono {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (L lo hi α β β' : ℝ) (h : AdversarialBco.BodySpec.HypH J L lo hi α β) (hβ : β ≤ β') : AdversarialBco.BodySpec.HypH J L lo hi α β' := by
  intro k w F hw hwsum hF
  rcases h k w F hw hwsum hF with ⟨ρ, hρ_prob, hρ_support, hρ_int, hρ_bound⟩
  refine ⟨ρ, hρ_prob, hρ_support, hρ_int, ?_⟩
  set I := ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ with hI
  have hI_nonneg : 0 ≤ I := by
    rw [hI]
    refine integral_nonneg ?_
    intro x
    refine Finset.sum_nonneg ?_
    intro i _
    have hw_i : 0 ≤ w i := hw i
    have hsq_nonneg : 0 ≤ ((∑ j, w j * F j x) - F i x) ^ 2 := pow_two_nonneg _
    exact mul_nonneg hw_i hsq_nonneg
  have h_mul : β * I ≤ β' * I := mul_le_mul_of_nonneg_right hβ hI_nonneg
  have h_sqrt : √(β * I) ≤ √(β' * I) := Real.sqrt_le_sqrt h_mul
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.inner_ball {d : ℕ} (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (hc : Metric.closedBall c 1 ⊆ K) : Metric.closedBall c (1 / 2) ⊆ {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} := by
  intro y hy
  rw [Metric.mem_closedBall] at hy
  intro x hx
  rw [Metric.mem_closedBall] at hx
  have hx_bound : dist x c ≤ 1 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have hpos : 0 < n := by omega
      exact_mod_cast hpos
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hdiv : (1 : ℝ) / (n : ℝ) ≤ 1/2 := by
      apply (one_div_le_one_div hn_pos h2_pos).mpr
      exact hn_real
    calc
      dist x c ≤ dist x y + dist y c := dist_triangle _ _ _
      _ ≤ (1 / (n : ℝ)) + (1 / 2) := by nlinarith
      _ ≤ 1 := by nlinarith
  have hx_mem : x ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall]
    exact hx_bound
  exact hc hx_mem
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.one_le_diam {d : ℕ} (hd : 1 ≤ d) (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : Bornology.IsBounded J) (c : EuclideanSpace ℝ (Fin d)) (hc : Metric.closedBall c (1 / 2) ⊆ J) : 1 ≤ Metric.diam J := by
  have hpos_nat : 0 < d := by omega
  let i : Fin d := ⟨0, hpos_nat⟩
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  have he_norm : ‖e‖ = 1 := by
    rw [EuclideanSpace.norm_single i 1]
    norm_num
  have hpos : c + (1/2 : ℝ) • e ∈ Metric.closedBall c (1/2) := by
    rw [mem_closedBall_iff_norm]
    have h : (c + (1/2 : ℝ) • e) - c = (1/2 : ℝ) • e := by simp
    rw [h, norm_smul]
    have hnorm : ‖(1/2 : ℝ)‖ = (1/2 : ℝ) := by norm_num
    rw [hnorm, he_norm]
    norm_num
  have hneg : c - (1/2 : ℝ) • e ∈ Metric.closedBall c (1/2) := by
    rw [mem_closedBall_iff_norm]
    have h : (c - (1/2 : ℝ) • e) - c = (-(1/2 : ℝ)) • e := by simp
    rw [h, norm_smul]
    have hnorm : ‖(-(1/2 : ℝ))‖ = (1/2 : ℝ) := by norm_num
    rw [hnorm, he_norm]
    norm_num
  have hJpos : c + (1/2 : ℝ) • e ∈ J := hc hpos
  have hJneg : c - (1/2 : ℝ) • e ∈ J := hc hneg
  have hdist : dist (c + (1/2 : ℝ) • e) (c - (1/2 : ℝ) • e) = 1 := by
    rw [dist_eq_norm_sub]
    have h : (c + (1/2 : ℝ) • e) - (c - (1/2 : ℝ) • e) = e := by
      calc
        (c + (1/2 : ℝ) • e) - (c - (1/2 : ℝ) • e) = ((1/2 : ℝ) • e) + ((1/2 : ℝ) • e) := by abel
        _ = ((1/2 : ℝ) + (1/2 : ℝ)) • e := by rw [add_smul]
        _ = (1 : ℝ) • e := by norm_num
        _ = e := by simp
    rw [h, he_norm]
  have hineq : dist (c + (1/2 : ℝ) • e) (c - (1/2 : ℝ) • e) ≤ Metric.diam J :=
    Metric.dist_le_diam_of_mem hJ hJpos hJneg
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.reindex_pos (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) : ∃ (k' : ℕ) (e : Fin k' → Fin k), Function.Injective e ∧ (∀ j, 0 < w (e j)) ∧ ∀ X : Fin k → ℝ, ∑ i, w i * X i = ∑ j, w (e j) * X (e j) := by
  let s := Finset.univ.filter (fun i => 0 < w i)
  let k' := s.card
  let e : Fin k' → Fin k := fun j => (s.equivFin.symm j).val
  refine ⟨k', e, ?_, ?_, ?_⟩
  · -- Function.Injective e
    intro x y h
    apply s.equivFin.symm.injective
    apply Subtype.ext
    exact h
  · -- ∀ j, 0 < w (e j)
    intro j
    have hmem : (s.equivFin.symm j).val ∈ s := (s.equivFin.symm j).property
    have hpos := (Finset.mem_filter.mp hmem).2
    simpa [e] using hpos
  · -- ∀ X : Fin k → ℝ, ∑ i, w i * X i = ∑ j, w (e j) * X (e j)
    intro X
    have hsum_all : ∑ i, w i * X i = ∑ i ∈ s, w i * X i := by
      calc
        ∑ i, w i * X i = ∑ i ∈ (Finset.univ : Finset (Fin k)), w i * X i := by simp
        _ = ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), w i * X i := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (λ i hi => ?_)
          by_cases hiw : 0 < w i
          · simp [hiw]
          · have hwi : w i = 0 := by
              have hle : w i ≤ 0 := le_of_not_gt hiw
              exact le_antisymm hle (hw i)
            simp [hwi]
        _ = ∑ i ∈ s, w i * X i := by simp [s]
    have hsum_coe : ∑ i ∈ s, w i * X i = ∑ i : s, w (i.val) * X (i.val) := by
      rw [← Finset.sum_coe_sort]
    have hsum_equiv : ∑ i : s, w (i.val) * X (i.val) = ∑ j : Fin k', w (((s.equivFin.symm j).val)) * X (((s.equivFin.symm j).val)) := by
      refine Fintype.sum_equiv s.equivFin (fun i => w (i.val) * X (i.val)) (fun j => w (((s.equivFin.symm j).val)) * X (((s.equivFin.symm j).val))) (fun i => ?_)
      simp
    have hsum_e : ∑ j : Fin k', w (((s.equivFin.symm j).val)) * X (((s.equivFin.symm j).val)) = ∑ j : Fin k', w (e j) * X (e j) := by
      simp [e]
    calc
      ∑ i, w i * X i = ∑ i ∈ s, w i * X i := hsum_all
      _ = ∑ i : s, w (i.val) * X (i.val) := hsum_coe
      _ = ∑ j : Fin k', w (((s.equivFin.symm j).val)) * X (((s.equivFin.symm j).val)) := hsum_equiv
      _ = ∑ j : Fin k', w (e j) * X (e j) := hsum_e
end
