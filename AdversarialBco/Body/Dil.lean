/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Convex
public import AdversarialBco.Body.Cloud

@[expose] public section

/-!
# The entropic Gaussian lemma: existence of a minimiser

`ec_min_exists`: for a coercive Lipschitz `G`, the entropic objective `E G(b + S g) - lam log |det S|` has a minimiser
`(b, S)`, `S` invertible.
`convexOn_comp_cloud`: a convex function stays convex after the affine change of variables `g ↦ b + S g`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body

/-! ## The entropic Gaussian lemma: existence of a minimiser -/

/-- Existence of a minimiser of the entropic objective `E G(b + S g) - lam log |det S|` over every invertible `S`. -/
theorem ec_min_exists {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hGL : LipschitzWith L G)
    (a a' : ℝ) (ha : 0 < a) (hcoer : ∀ x, a * ‖x‖ - a' ≤ G x) (lam : ℝ) (hlam : 0 < lam) :
    ∃ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 ∧
      ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        ∫ g, G (b + S g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
          ∫ g, G (b' + S' g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam * Real.log |LinearMap.det (S' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  let f : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) → ℝ := fun p =>
    ∫ g, G (p.1 + p.2 g) ∂γ -
      lam * Real.log |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|
  let U : Set (EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) :=
    {p | LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0}
  let x0 : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (0, ContinuousLinearMap.id ℝ _)
  have hx0 : x0 ∈ U := by simp [U, x0]
  obtain ⟨M, δ, hδ, hMδ⟩ := entropic_bounded G L hGL a a' ha hcoer lam hlam (f x0)
  have hIc : Continuous fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =>
      ∫ g, G (p.1 + p.2 g) ∂γ := by
    set c := ∫ g, ‖g‖ ∂γ
    have hc : 0 ≤ c := integral_nonneg fun _ => norm_nonneg _
    refine (LipschitzWith.of_dist_le_mul (K := (L * (1 + c)).toNNReal) fun p p' => ?_).continuous
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have h := integral_cloud_lipschitz G L hGL p.1 p'.1 p.2 p'.2
    have h1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
      rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
    have h2 : ‖p.2 - p'.2‖ ≤ dist p p' := by
      rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_right _ _
    calc _ ≤ (L : ℝ) * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖ * c) := h
      _ ≤ L * (dist p p' + dist p p' * c) := by gcongr
      _ = L * (1 + c) * dist p p' := by ring
  have hdc : Continuous fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =>
      LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    continuous_det_clm.comp continuous_snd
  have hfc : ContinuousOn f U := by
    refine hIc.continuousOn.sub (continuousOn_const.mul ?_)
    refine Real.continuousOn_log.comp (continuous_abs.comp hdc).continuousOn fun p hp => ?_
    simpa [U] using hp
  have hK : IsCompact {p | p ∈ U ∧ f p ≤ f x0} := by
    have heq : {p | p ∈ U ∧ f p ≤ f x0} =
        {p | δ ≤ |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|} ∩
          f ⁻¹' Set.Iic (f x0) := by
      ext p
      constructor
      · rintro ⟨hp, hle⟩
        exact ⟨(hMδ p.1 p.2 hp hle).2.2, hle⟩
      · rintro ⟨hp, hle⟩
        refine ⟨fun h0 => ?_, hle⟩
        simp only [Set.mem_ofPred_eq, h0, abs_zero] at hp
        linarith
    have hsub : {p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) |
        δ ≤ |LinearMap.det (p.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|} ⊆ U := by
      intro p hp h0
      simp only [Set.mem_ofPred_eq, h0, abs_zero] at hp
      linarith
    have hcl := ContinuousOn.preimage_isClosed_of_isClosed (hfc.mono hsub)
      (isClosed_le continuous_const (continuous_abs.comp hdc)) (isClosed_Iic (a := f x0))
    rw [heq]
    refine Metric.isCompact_of_isClosed_isBounded hcl ((Metric.isBounded_closedBall (x := 0) (r := M)).subset ?_)
    rintro p ⟨hp1, hp2⟩
    obtain ⟨hb, hS, -⟩ := hMδ p.1 p.2 (hsub hp1) hp2
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hb hS
  obtain ⟨p, hpU, hp⟩ := AdversarialBco.exists_min_of_compact_sublevel U f hfc x0 hx0 hK
  exact ⟨p.1, p.2, hpU, fun b' S' h => hp (b', S') h⟩

/-! ## Convexity under an affine change of variables -/

/-- A convex function stays convex after an affine change of variables `g ↦ b + S g`. -/
theorem convexOn_comp_cloud {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun g => F (b + S g)) := by
  refine ⟨convex_univ, fun g _ g' _ s t hs ht hst => ?_⟩
  have e : b + S (s • g + t • g') = s • (b + S g) + t • (b + S g') := by
    rw [map_add, map_smul, map_smul, smul_add, smul_add]
    have hb : b = s • b + t • b := by rw [← add_smul, hst, one_smul]
    nth_rewrite 1 [hb]
    abel
  simp only [e, smul_eq_mul]
  exact hF.2 (Set.mem_univ _) (Set.mem_univ _) hs ht hst

end AdversarialBco.Body
