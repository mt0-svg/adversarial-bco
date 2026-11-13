/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProcBase

@[expose] public section

/-!
# Procedure PG: measurability of the event `PgGood`

Proof of the named hypothesis `PgGoodMeas` of `AdversarialBco/Poly/PgProc.lean` (theorem `pgGoodMeas`), with the
measurability tools around it: the continuity of `pgPack` and of the composition `pgComp`, the measurability of the
graph of a body in a position (`posBody_family_measurableSet`) and of the inverse `M⁻¹ = (det M)⁻¹ • adj M`.

For a convex body containing `B̄(0, 1)`, the gauge is an infimum over rational scales (`gauge_eq_iInf_rat`), jointly
measurable in the position and the point, so the mean width is measurable in the position; the outer radius condition
is a countable intersection over a dense subset of the body (`posBody_subset_ball_measurableSet`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AdversarialBco.Poly

namespace PgMeas

/-! ## Continuity of the coordinates and of the composition -/

theorem pgPack_continuous (d : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ => pgPack p.1 p.2) := by
  unfold pgPack
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
  rintro (i | ⟨i, j⟩)
  · exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
  · exact (continuous_snd.matrix_elem i j)

theorem pgComp_continuous (d : ℕ) : Continuous (fun p : PgSp d × PgSp d => pgComp p.1 p.2) := by
  unfold pgComp
  refine (pgPack_continuous d).comp (Continuous.prodMk ?_ ?_)
  · exact (pg_continuous d).2.2.comp (continuous_fst.prodMk ((pg_continuous d).1.comp continuous_snd))
  · exact ((pg_continuous d).2.1.comp continuous_fst).matrix_mul ((pg_continuous d).2.1.comp continuous_snd)

/-! ## Bodies depending measurably on a parameter -/

theorem posBody_family_measurableSet {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × EuclideanSpace ℝ (Fin d) | p.2 ∈ posBody K (pgMu p.1) (pgOp p.1)} :=
  (hK.preimage (pg_continuous d).2.2).measurableSet

/-- `M ↦ M⁻¹ = (det M)⁻¹ • adj M` is measurable. -/
theorem matrix_inv_measurable (d : ℕ) : Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) := by
  have h : (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul ((continuous_id.matrix_adjugate.matrix_elem i j).measurable)

/-! ## Composition of measurable maps -/

theorem measurable_comp_lam {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {g : β → γ} (hg : Measurable g) (f : α → β) (hf : Measurable f) : Measurable (fun x => g (f x)) :=
  hg.comp hf

/-! ## The event `PgGood` -/

open Classical in
theorem gauge_eq_iInf_rat {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (hs : Convex ℝ s)
    (h1 : Metric.closedBall 0 1 ⊆ s) (x : EuclideanSpace ℝ (Fin d)) :
    gauge s x = ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖ := by
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ s := h1 (Metric.mem_closedBall_self zero_le_one)
  have habsB : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (absorbent_ball_zero zero_lt_one).mono Metric.ball_subset_closedBall
  have habs : Absorbent ℝ s := habsB.mono h1
  have hgx : gauge s x ≤ ‖x‖ := by
    calc gauge s x ≤ gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x := gauge_mono habsB h1 x
      _ = ‖x‖ := by rw [gauge_closedBall zero_le_one, div_one]
  have hfge : ∀ q : ℚ, gauge s x ≤ if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖ := by
    intro q
    split_ifs with h
    · have hq : (0 : ℝ) < q := by exact_mod_cast h.1
      apply gauge_le_of_mem hq.le
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hq.ne' s x]
      exact h.2
    · exact hgx
  have hbdd : BddBelow (Set.range fun q : ℚ => if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact (gauge_nonneg x).trans (hfge q)⟩
  apply le_antisymm (le_ciInf hfge)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (gauge s x) hε)
  have hqpos : (0 : ℝ) < q := (gauge_nonneg x).trans_lt hq1
  have hmem : (q : ℝ)⁻¹ • x ∈ s := by
    apply setOfPred_gauge_lt_one_subset_self hs h0 habs
    show gauge s ((q : ℝ)⁻¹ • x) < 1
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hqpos.le), smul_eq_mul, inv_mul_lt_iff₀ hqpos, mul_one]
    exact hq1
  calc (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖)
      ≤ (if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖) := ciInf_le hbdd q
    _ = q := by
      split_ifs with h
      · rfl
      · exact absurd ⟨by exact_mod_cast hqpos, hmem⟩ h
    _ < gauge s x + ε := hq2

open Classical in
theorem gaugeRat_family_measurable {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    Measurable (fun p : PgSp d × EuclideanSpace ℝ (Fin d) =>
      ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • p.2 ∈ posBody K (pgMu p.1) (pgOp p.1) then (q : ℝ) else ‖p.2‖) := by
  refine Measurable.iInf fun q => ?_
  have hS : MeasurableSet {p : PgSp d × EuclideanSpace ℝ (Fin d) |
      0 < q ∧ (q : ℝ)⁻¹ • p.2 ∈ posBody K (pgMu p.1) (pgOp p.1)} :=
    (MeasurableSet.const (0 < q)).inter ((posBody_family_measurableSet K hK).preimage
      (f := fun p : PgSp d × EuclideanSpace ℝ (Fin d) => (p.1, (q : ℝ)⁻¹ • p.2))
      (measurable_fst.prodMk (measurable_snd.const_smul ((q : ℝ)⁻¹))))
  exact Measurable.ite hS measurable_const (measurable_norm.comp measurable_snd)

theorem posBody_subset_ball_measurableSet {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) :
    MeasurableSet {Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} := by
  obtain ⟨D, hDK, hDc, hKD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hT : ∀ k : EuclideanSpace ℝ (Fin d), Measurable (fun Q : PgSp d =>
      ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖) := by
    intro k
    have h1 : Measurable (fun Q : PgSp d => (pgMat Q)⁻¹) :=
      (matrix_inv_measurable d).comp (pg_continuous d).2.1.measurable
    have h2 : Measurable (fun Q : PgSp d => WithLp.ofLp (k - pgMu Q)) :=
      ((PiLp.continuous_ofLp 2 _).comp (continuous_const.sub (pg_continuous d).1)).measurable
    have hc : Continuous (fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => ‖WithLp.toLp 2 (p.1 *ᵥ p.2)‖) :=
      ((PiLp.continuous_toLp 2 _).comp (continuous_fst.matrix_mulVec continuous_snd)).norm
    exact measurable_comp_lam hc.measurable (fun Q : PgSp d => ((pgMat Q)⁻¹, WithLp.ofLp (k - pgMu Q))) (h1.prodMk h2)
  have hop : ∀ (Q : PgSp d) (v : EuclideanSpace ℝ (Fin d)),
      pgOp Q v = WithLp.toLp 2 (pgMat Q *ᵥ WithLp.ofLp v) := fun Q v => by
    rw [pgOp, ← Matrix.toEuclideanCLM_toLp]
  have heq : {Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} =
      {Q : PgSp d | (pgMat Q).det ≠ 0} ∩
        ⋂ k ∈ D, {Q | ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖ ≤ R} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hdet, hsub⟩
      refine ⟨hdet, fun k hk => ?_⟩
      have hmem : WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q)) ∈ posBody K (pgMu Q) (pgOp Q) := by
        show pgMu Q + pgOp Q _ ∈ K
        rw [hop, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.one_mulVec, WithLp.toLp_ofLp, add_sub_cancel]
        exact hDK hk
      simpa using hsub hmem
    · rintro ⟨hdet, hD⟩
      refine ⟨hdet, fun y hy => ?_⟩
      have hk0 : pgMu Q + pgOp Q y ∈ closure D := hKD hy
      have hclosed : IsClosed {k : EuclideanSpace ℝ (Fin d) |
          ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖ ≤ R} :=
        isClosed_le (((PiLp.continuous_toLp 2 _).comp (continuous_const.matrix_mulVec
          ((PiLp.continuous_ofLp 2 _).comp (continuous_id.sub continuous_const)))).norm) continuous_const
      have h3 : ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp ((pgMu Q + pgOp Q y) - pgMu Q))‖ ≤ R :=
        closure_minimal (fun k hk => hD k hk) hclosed hk0
      rw [add_sub_cancel_left, hop, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec, WithLp.toLp_ofLp] at h3
      rw [mem_closedBall_zero_iff]
      exact h3
  rw [heq]
  exact (isOpen_ne_fun (pg_continuous d).2.1.matrix_det continuous_const).measurableSet.inter
    (MeasurableSet.biInter hDc fun k _ => measurableSet_le (hT k) measurable_const)

theorem ball_subset_posBody_isClosed {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    IsClosed {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} := by
  have h_cont : Continuous (fun (x : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMu x.1 + pgOp x.1 x.2) :=
    (pg_continuous d).2.2
  have h_cont_fixed (y : EuclideanSpace ℝ (Fin d)) : Continuous (fun (Q : PgSp d) => pgMu Q + pgOp Q y) := by
    refine h_cont.comp (Continuous.prodMk ?_ continuous_const)
    exact continuous_id
  have h_eq : {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} =
      ⋂ y ∈ Metric.closedBall 0 1, {Q : PgSp d | pgMu Q + pgOp Q y ∈ K} := by
    ext Q; simp [Set.subset_def, posBody]
  rw [h_eq]
  refine isClosed_biInter (fun y hy => ?_)
  rw [← Set.preimage_ofPred_eq]
  exact hK.preimage (h_cont_fixed y)

theorem posBody_convex {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Convex ℝ (posBody K μ A) := by
  intro x hx y hy a b ha hb hab
  show μ + A (a • x + b • y) ∈ K
  have h : μ + A (a • x + b • y) = a • (μ + A x) + b • (μ + A y) := by
    rw [map_add, map_smul, map_smul, smul_add, smul_add]
    have hμ : μ = a • μ + b • μ := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hμ]
    abel
  rw [h]
  exact hK hx hy ha hb hab

theorem pgGood_measurableSet (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (hcv : Convex ℝ K)
    (hK : IsClosed K) : MeasurableSet {Q : PgSp d | PgGood d K R (some Q)} := by
  classical
  have hGm := gaugeRat_family_measurable K hK
  have hI : Measurable (fun Q : PgSp d => ∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
      then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
    (hGm.stronglyMeasurable.integral_prod_right').measurable
  have hA : MeasurableSet {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} :=
    (ball_subset_posBody_isClosed K hK).measurableSet
  have hdet : MeasurableSet {Q : PgSp d | (pgMat Q).det ≠ 0} :=
    (isOpen_ne_fun ((pg_continuous d).2.1.matrix_det) continuous_const).measurableSet
  have hB := posBody_subset_ball_measurableSet K R
  have hW : MeasurableSet {Q : PgSp d | (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
      then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
        (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ 1.27 * Real.sqrt (d + 1) / d} :=
    measurableSet_le (hI.div_const _) measurable_const
  have hmw : ∀ Q : PgSp d, Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q) →
      pgMw (posBody K (pgMu Q) (pgOp Q)) = (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
        then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
          (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    intro Q hQ
    unfold pgMw
    congr 2
    funext g
    exact gauge_eq_iInf_rat _ (posBody_convex K hcv _ _) hQ g
  have heq : {Q : PgSp d | PgGood d K R (some Q)} =
      {Q : PgSp d | (pgMat Q).det ≠ 0} ∩ ({Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} ∩
        ({Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} ∩
          {Q : PgSp d | (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
            then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
              (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ 1.27 * Real.sqrt (d + 1) / d})) := by
    ext Q
    simp only [PgGood, Option.some.injEq, exists_eq_left', Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, ⟨h1, h3⟩, hmw Q h2 ▸ h4⟩
    · rintro ⟨h1, h2, ⟨-, h3⟩, h4⟩
      exact ⟨h1, h2, h3, (hmw Q h2).symm ▸ h4⟩
  rw [heq]
  exact hdet.inter (hA.inter (hB.inter hW))

theorem pgGoodMeas : PgGoodMeas := fun d K R hcv hK => pgGood_measurableSet d K R hcv hK

end PgMeas

end AdversarialBco.Poly
