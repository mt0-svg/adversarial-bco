/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2
public import AdversarialBco.StatementConj1

@[expose] public section

/-!
# The comparator as an infimum over the rational points of the interior

The infimum of a convex function over a convex body as an infimum over the rational points of its interior (the
measurable form of the comparator, `sInf_image_eq_iInf_rat`), with a sum of convex functions (`convexOn_sum_range`)
and the approximation from the interior (`convex_interior_approx`, `iInf_rat_le_of_continuousOn`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly.PropGAd

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly
open Classical

/-! ## The comparator as an infimum over the rational points of the interior -/

theorem convexOn_sum_range {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (n : ℕ)
    (g : ℕ → E d → ℝ) (hg : ∀ t < n, ConvexOn ℝ K (g t)) (hg01 : ∀ t < n, ∀ y ∈ K, g t y ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ K (fun y => ∑ t ∈ Finset.range n, g t y) ∧
      ∀ y ∈ K, (∑ t ∈ Finset.range n, g t y) ∈ Set.Icc (0 : ℝ) n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
      exact convexOn_const 0 hK
    · intro y hy
      simp
  | succ n ih =>
    have hg_n : ConvexOn ℝ K (g n) := hg n (Nat.lt_succ_self n)
    have hg01_n : ∀ y ∈ K, g n y ∈ Set.Icc (0 : ℝ) 1 := hg01 n (Nat.lt_succ_self n)
    have hg_restrict : ∀ t < n, ConvexOn ℝ K (g t) := fun t ht =>
      hg t (lt_of_lt_of_le ht (Nat.le_succ n))
    have hg01_restrict : ∀ t < n, ∀ y ∈ K, g t y ∈ Set.Icc (0 : ℝ) 1 := fun t ht y hy =>
      hg01 t (lt_of_lt_of_le ht (Nat.le_succ n)) y hy
    rcases ih hg_restrict hg01_restrict with ⟨ih_conv, ih_bound⟩
    have hsum_eq : (fun y => ∑ t ∈ Finset.range (n + 1), g t y) =
        (fun y => (∑ t ∈ Finset.range n, g t y) + g n y) := by
      ext y; simp [Finset.sum_range_succ]
    have h_conv : ConvexOn ℝ K (fun y => ∑ t ∈ Finset.range (n + 1), g t y) := by
      rw [hsum_eq]
      exact ih_conv.add hg_n
    have h_bound : ∀ y ∈ K, (∑ t ∈ Finset.range (n + 1), g t y) ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1) := by
      intro y hy
      have hlow : 0 ≤ ∑ t ∈ Finset.range (n + 1), g t y := by
        refine Finset.sum_nonneg (fun t _ => ?_)
        have ht : t < n + 1 := Finset.mem_range.1 ‹_›
        exact (hg01 t ht y hy).1
      have hhigh : (∑ t ∈ Finset.range (n + 1), g t y) ≤ (n : ℝ) + 1 := by
        rw [Finset.sum_range_succ]
        have hg01_n_y := (hg01_n y hy).2
        have h_ih_bound := (ih_bound y hy).2
        nlinarith
      exact ⟨hlow, hhigh⟩
    simpa [Nat.cast_succ] using ⟨h_conv, h_bound⟩

theorem convex_interior_approx {d : ℕ} (K : Set (E d)) (G : E d → ℝ)
    (hG : ConvexOn ℝ K G) (M : ℝ) (hG01 : ∀ y ∈ K, G y ∈ Set.Icc (0 : ℝ) M) (c b : E d) (hc : c ∈ interior K)
    (hb : b ∈ K) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (1 - s) • b + s • c ∈ interior K ∧ G ((1 - s) • b + s • c) ≤ G b + s * M := by
  rcases hG with ⟨hconvK, hconv⟩
  have hcK : c ∈ K := interior_subset hc
  have hmem : s • c + (1 - s) • b ∈ interior K :=
    Convex.combo_interior_self_mem_interior hconvK hc hb hs0 (by linarith) (by ring_nf)
  have h_ineq : G (s • c + (1 - s) • b) ≤ G b + s * M := by
    have hGc : G c ∈ Set.Icc (0 : ℝ) M := hG01 c hcK
    have hGb : G b ∈ Set.Icc (0 : ℝ) M := hG01 b hb
    have hGc_le_M : G c ≤ M := hGc.2
    have hGc_nonneg : 0 ≤ G c := hGc.1
    have hGb_nonneg : 0 ≤ G b := hGb.1
    have hconv_ineq := hconv hcK hb (a := s) (b := 1 - s) hs0.le (by linarith) (by ring_nf)
    have h1 : s * G c ≤ s * M := by
      nlinarith
    have h2 : (1 - s) * G b ≤ G b := by
      nlinarith
    have hsum : s • G c + (1 - s) • G b ≤ G b + s * M := by
      simpa [smul_eq_mul, add_comm] using by nlinarith
    nlinarith
  have hmem' : (1 - s) • b + s • c ∈ interior K := by
    simpa [add_comm] using hmem
  have h_ineq' : G ((1 - s) • b + s • c) ≤ G b + s * M := by
    simpa [add_comm] using h_ineq
  exact And.intro hmem' h_ineq'

theorem iInf_rat_le_of_continuousOn {d : ℕ} (U : Set (E d)) (hU : IsOpen U)
    (G : E d → ℝ) (hG : ContinuousOn G U) (M : ℝ) (hM : 0 ≤ M) (hG0 : ∀ y ∈ U, 0 ≤ G y) (y : E d) (hy : y ∈ U) :
    (⨅ q : Fin d → ℚ, if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ U then G (WithLp.toLp 2 (fun i => (q i : ℝ)))
      else M) ≤ G y := by
  -- Let I be the infimum
  set I := ⨅ q : Fin d → ℚ, if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ U then G (WithLp.toLp 2 (fun i => (q i : ℝ)))
    else M with hI
  -- It suffices to show I ≤ G y + ε for every ε > 0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- From continuity of G at y within U, get δ₂ > 0 such that |G z - G y| < ε on a δ₂-ball
  have h_cont : ContinuousWithinAt G U y := hG y hy
  rcases Metric.continuousWithinAt_iff.mp h_cont ε hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
  -- From U open, get δ₁ > 0 such that Metric.ball y δ₁ ⊆ U
  have h_open : U ∈ nhds y := hU.mem_nhds hy
  rcases Metric.mem_nhds_iff.mp h_open with ⟨δ₁, hδ₁_pos, hδ₁_ball⟩
  -- Take δ = min δ₁ δ₂
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  have hδ_le_δ₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ_le_δ₂ : δ ≤ δ₂ := min_le_right _ _
  -- Rational points are dense in EuclideanSpace ℝ (Fin d)
  let f : (Fin d → ℚ) → E d := fun q => WithLp.toLp 2 (fun i => (q i : ℝ))
  have h_dense_rat : DenseRange (fun (q : ℚ) => (q : ℝ)) := Rat.denseRange_cast
  have h_dense_pi : DenseRange (Pi.map (fun (_ : Fin d) => (fun (q : ℚ) => (q : ℝ)))) :=
    DenseRange.piMap (fun _ => h_dense_rat)
  have h_surj_toLp : Function.Surjective (WithLp.toLp 2 : (Fin d → ℝ) → E d) := by
    intro x
    refine ⟨fun i => x i, rfl⟩
  have h_dense_toLp : DenseRange (WithLp.toLp 2 : (Fin d → ℝ) → E d) :=
    h_surj_toLp.denseRange
  have h_cont_toLp : Continuous (WithLp.toLp 2 : (Fin d → ℝ) → E d) :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)
  have h_dense : DenseRange f :=
    h_dense_toLp.comp h_dense_pi h_cont_toLp
  -- Get q : Fin d → ℚ such that dist (f q) y < δ
  rcases h_dense.exists_dist_lt y hδ_pos with ⟨q, hq_dist⟩
  -- Therefore f q ∈ ball y δ₁ ⊆ U
  have h_mem_U : f q ∈ U := by
    have h_ball : f q ∈ Metric.ball y δ₁ := by
      rw [Metric.mem_ball, dist_comm]
      linarith
    exact hδ₁_ball h_ball
  -- So the infimum term at q is G (f q)
  have h_term : (if f q ∈ U then G (f q) else M) = G (f q) := by
    rw [ite_eq_left h_mem_U]
  -- Now I ≤ G (f q) by definition of infimum
  have h_I_le_term : I ≤ G (f q) := by
    rw [hI]
    -- ciInf_le : ⨅ i, f i ≤ f i  (requires ConditionallyCompleteLattice)
    have h_bdd : BddBelow (Set.range (fun (q' : Fin d → ℚ) =>
      if f q' ∈ U then G (f q') else M)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨q', rfl⟩
      by_cases hq'U : f q' ∈ U
      · simpa [hq'U] using hG0 (f q') hq'U
      · simpa [hq'U] using hM
    have h_le := ciInf_le h_bdd q
    -- h_le : (⨅ q', ...) ≤ (if f q ∈ U then G (f q) else M)
    -- we need (⨅ q', ...) ≤ G (f q)
    simpa [h_term] using h_le
  -- And |G (f q) - G y| < ε, so G (f q) < G y + ε
  have h_G_lt : G (f q) < G y + ε := by
    have h_dist_q_y : dist (f q) y < δ₂ := by
      rw [dist_comm]
      linarith
    have h_dist_G : dist (G (f q)) (G y) < ε :=
      hδ₂ h_mem_U h_dist_q_y
    rw [dist_eq_norm] at h_dist_G
    have h_abs : |G (f q) - G y| < ε := by
      rw [← Real.norm_eq_abs]
      exact h_dist_G
    linarith [abs_lt.mp h_abs]
  -- Combine: I ≤ G(f q) < G y + ε
  linarith

theorem sInf_image_eq_iInf_rat {d : ℕ} (K : Set (E d)) (hK : (interior K).Nonempty)
    (G : E d → ℝ) (hG : ConvexOn ℝ K G) (M : ℝ) (hG01 : ∀ y ∈ K, G y ∈ Set.Icc (0 : ℝ) M) :
    sInf (G '' K) = ⨅ q : Fin d → ℚ,
      if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ interior K then G (WithLp.toLp 2 (fun i => (q i : ℝ))) else M := by
  set S := G '' K
  set I := ⨅ q : Fin d → ℚ,
    if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ interior K then G (WithLp.toLp 2 (fun i => (q i : ℝ))) else M
  have hS_nonempty : S.Nonempty := by
    rcases hK with ⟨c, hc⟩
    have hcK : c ∈ K := interior_subset hc
    exact ⟨G c, c, hcK, rfl⟩
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, fun y hy => ?_⟩
    rcases hy with ⟨x, hx, rfl⟩
    rcases ((Set.mem_Icc (a := (0 : ℝ)) (b := M) (x := G x)).mp (hG01 x hx)) with ⟨hGx0, _⟩
    exact hGx0
  have hM_nonneg : 0 ≤ M := by
    rcases hK with ⟨c, hc⟩
    have hcK : c ∈ K := interior_subset hc
    rcases ((Set.mem_Icc (a := (0 : ℝ)) (b := M) (x := G c)).mp (hG01 c hcK)) with ⟨hGc0, hGcM⟩
    exact le_trans hGc0 hGcM
  apply le_antisymm
  · -- sInf S ≤ I
    refine le_ciInf ?_
    intro q
    set x := (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d)
    by_cases hx : x ∈ interior K
    · -- x ∈ interior K, so G x ∈ S
      have hxK : x ∈ K := interior_subset hx
      have hGxS : G x ∈ S := ⟨x, hxK, rfl⟩
      simpa [hx] using csInf_le hS_bddBelow hGxS
    · -- x ∉ interior K, term is M
      have hterm : (if x ∈ interior K then G x else M) = M := by
        simp [hx]
      rw [hterm]
      rcases hK with ⟨c, hc⟩
      have hcK : c ∈ K := interior_subset hc
      have hGcS : G c ∈ S := ⟨c, hcK, rfl⟩
      have hGc_le_M : G c ≤ M := by
        rcases ((Set.mem_Icc (a := (0 : ℝ)) (b := M) (x := G c)).mp (hG01 c hcK)) with ⟨_, hGcM⟩
        exact hGcM
      exact le_trans (csInf_le hS_bddBelow hGcS) hGc_le_M
  · -- I ≤ sInf S
    refine le_csInf hS_nonempty ?_
    intro y hy
    rcases hy with ⟨b, hbK, rfl⟩
    rcases hK with ⟨c, hc⟩
    have hcK : c ∈ K := interior_subset hc
    have hM_nonneg' : 0 ≤ M := by
      rcases ((Set.mem_Icc (a := (0 : ℝ)) (b := M) (x := G c)).mp (hG01 c hcK)) with ⟨hGc0, hGcM⟩
      exact le_trans hGc0 hGcM
    have hG_nonneg_on_interior : ∀ y ∈ interior K, 0 ≤ G y := by
      intro y hy
      have hyK : y ∈ K := interior_subset hy
      rcases ((Set.mem_Icc (a := (0 : ℝ)) (b := M) (x := G y)).mp (hG01 y hyK)) with ⟨hGy0, _⟩
      exact hGy0
    have h_cont : ContinuousOn G (interior K) :=
      hG.continuousOn_interior
    have h_open : IsOpen (interior K) := isOpen_interior
    -- For each s ∈ (0,1], define y_s = (1-s)•b + s•c
    -- Then I ≤ G y_s ≤ G b + s*M
    -- Take s → 0 to get I ≤ G b
    have h_le_forall_s : ∀ s : ℝ, 0 < s → s ≤ 1 → I ≤ G b + s * M := by
      intro s hs_pos hs_le_one
      set ys := (1 - s) • b + s • c
      have h_ys_interior : ys ∈ interior K := by
        have h_approx := convex_interior_approx K G hG M hG01 c b hc hbK s hs_pos hs_le_one
        exact h_approx.1
      have h_G_ys_le : G ys ≤ G b + s * M := by
        have h_approx := convex_interior_approx K G hG M hG01 c b hc hbK s hs_pos hs_le_one
        exact h_approx.2
      have h_I_le_G_ys : I ≤ G ys := by
        have := iInf_rat_le_of_continuousOn (interior K) h_open G h_cont M hM_nonneg'
          hG_nonneg_on_interior ys h_ys_interior
        exact this
      exact le_trans h_I_le_G_ys h_G_ys_le
    -- Now use the limit argument: if M = 0, trivial; if M > 0, use ε = s*M
    by_cases hM_zero : M = 0
    · -- M = 0, then G b + s * M = G b
      have h_le : I ≤ G b := by
        have := h_le_forall_s (1/2) (by norm_num) (by norm_num)
        simpa [hM_zero] using this
      exact h_le
    · -- M > 0 (since M ≥ 0)
      have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg' (Ne.symm hM_zero)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      set s := min (1 : ℝ) (ε / M) with hs_def
      have hs_pos : 0 < s := by
        refine lt_min_iff.mpr ⟨by norm_num, div_pos hε hM_pos⟩
      have hs_le_one : s ≤ 1 := min_le_left _ _
      have h_ineq : I ≤ G b + ε := by
        have htemp := h_le_forall_s s hs_pos hs_le_one
        have hsM_le_ε : s * M ≤ ε := by
          have : s ≤ ε / M := min_le_right _ _
          calc
            s * M ≤ (ε / M) * M := mul_le_mul_of_nonneg_right this hM_nonneg'
            _ = ε := by field_simp [ne_of_gt hM_pos]
        linarith
      exact h_ineq

end AdversarialBco.Poly.PropGAd
