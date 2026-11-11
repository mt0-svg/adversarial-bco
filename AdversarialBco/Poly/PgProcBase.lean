/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProc

@[expose] public section

/-!
# Procedures PG-core and PG: the base facts shared by the proofs

The facts about the space `PgSp d`, the domain `D` and the measurability of the steps of `pgCore` on a fixed closed
body, which both the proofs of `PgCoreThm` and `PgThm` (`PgProcProof.lean`) and those of the
measurability statements `PgCoreMeas`, `PgMeas`, `PgGoodMeas` read. Each theorem takes the interface statements it uses
(`PiTildeMeasurable`) as hypotheses. No `sorry`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

namespace AdversarialBco.Poly

/-! ## The space `PgSp d` -/

/-- The point of `PgSp d` packed from `μ` and `M` has mean `μ`. -/
theorem pgMu_pgPack {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    pgMu (pgPack μ M) = μ := by
  rfl

/-- The point of `PgSp d` packed from `μ` and `M` has matrix `M`. -/
theorem pgMat_pgPack {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    pgMat (pgPack μ M) = M := by
  rfl

/-- `T v = M v` in coordinates. -/
theorem pgOp_apply {d : ℕ} (x : PgSp d) (v : EuclideanSpace ℝ (Fin d)) :
    pgOp x v = WithLp.toLp 2 (pgMat x *ᵥ WithLp.ofLp v) := by
  rw [pgOp, ← Matrix.toEuclideanCLM_toLp]

/-- The inner product of `PgSp d` is the sum of the inner products of the means and of the matrices. -/
theorem pgSp_inner {d : ℕ} (x y : PgSp d) :
    ⟪x, y⟫ = ⟪pgMu x, pgMu y⟫ + ∑ i, ∑ j, pgMat x i j * pgMat y i j := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, pgMu, pgMat, RCLike.inner_apply,
    conj_trivial]
  simp [mul_comm]

/-- `|x|^2 = |μ|^2 + |M|_F^2`. -/
theorem pgSp_norm_sq {d : ℕ} (x : PgSp d) :
    ‖x‖ ^ 2 = ‖pgMu x‖ ^ 2 + ∑ i, ∑ j, pgMat x i j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, pgSp_inner]
  simp [sq]

/-- `μ`, the matrix and the affine map `(x, y) ↦ μ + T y` are continuous on `PgSp d`. -/
theorem pg_continuous (d : ℕ) :
    Continuous (fun x : PgSp d => pgMu x) ∧ Continuous (fun x : PgSp d => pgMat x) ∧
      Continuous (fun p : PgSp d × EuclideanSpace ℝ (Fin d) => pgMu p.1 + pgOp p.1 p.2) := by
  have hmu : Continuous (fun x : PgSp d => pgMu x) := by
    unfold pgMu
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (PiLp.continuous_apply 2 _ (Sum.inl i)))
  have hmat : Continuous (fun x : PgSp d => pgMat x) := by
    unfold pgMat
    exact continuous_pi fun i => continuous_pi fun j => PiLp.continuous_apply 2 _ (Sum.inr (i, j))
  refine ⟨hmu, hmat, ?_⟩
  have hop : ∀ (x : PgSp d) (v : EuclideanSpace ℝ (Fin d)),
      pgOp x v = WithLp.toLp 2 (pgMat x *ᵥ WithLp.ofLp v) := fun x v => by
    rw [pgOp, ← Matrix.toEuclideanCLM_toLp]
  simp_rw [hop]
  refine (hmu.comp continuous_fst).add ((PiLp.continuous_toLp 2 _).comp ?_)
  exact (hmat.comp continuous_fst).matrix_mulVec ((PiLp.continuous_ofLp 2 _).comp continuous_snd)

/-! ## The domain `D` -/

/-- `D` is convex. -/
theorem pgDom_convex (d : ℕ) (ρ : ℝ) : Convex ℝ (pgDom d ρ) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hsum
  have hx_dom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
  have hy_dom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu y) (pgOp y) := hy
  rcases hx_dom with ⟨hx_adj, hx_norm, hx_forall⟩
  rcases hy_dom with ⟨hy_adj, hy_norm, hy_forall⟩
  have h_mu_add : pgMu (a • x + b • y) = a • pgMu x + b • pgMu y := by
    ext i
    simp [pgMu]
  have h_op_add : pgOp (a • x + b • y) = a • pgOp x + b • pgOp y := by
    dsimp [pgOp]
    have h_mat : pgMat (a • x + b • y) = pgMat (a • x) + pgMat (b • y) := by
      ext i j; simp [pgMat]
    have h_smul_add : pgMat (a • x) + pgMat (b • y) = a • pgMat x + b • pgMat y := by
      ext i j; simp [pgMat]
    rw [h_mat, h_smul_add]
    simpa using LinearMap.map_add (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) :
      Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (a • pgMat x) (b • pgMat y)
  have h_adj : IsSelfAdjoint (pgOp (a • x + b • y)) := by
    rw [h_op_add]
    unfold IsSelfAdjoint
    have hx_adj' : star (pgOp x) = pgOp x := hx_adj
    have hy_adj' : star (pgOp y) = pgOp y := hy_adj
    rw [star_add (r := a • pgOp x) (s := b • pgOp y)]
    rw [star_smul (r := a) (a := pgOp x), star_smul (r := b) (a := pgOp y)]
    simp [hx_adj', hy_adj']
  have h_norm : ‖pgMu (a • x + b • y)‖ ≤ pgKappa * ρ := by
    rw [h_mu_add]
    calc
      ‖a • pgMu x + b • pgMu y‖ ≤ ‖a • pgMu x‖ + ‖b • pgMu y‖ := norm_add_le _ _
      _ = ‖a‖ * ‖pgMu x‖ + ‖b‖ * ‖pgMu y‖ := by rw [norm_smul, norm_smul]
      _ = |a| * ‖pgMu x‖ + |b| * ‖pgMu y‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ = a * ‖pgMu x‖ + b * ‖pgMu y‖ := by rw [abs_of_pos ha, abs_of_pos hb]
      _ ≤ a * (pgKappa * ρ) + b * (pgKappa * ρ) := by
        nlinarith
      _ = (a + b) * (pgKappa * ρ) := by ring
      _ = pgKappa * ρ := by rw [hsum, one_mul]
  have h_lower : ∀ v, pgTmin d ρ * ‖v‖ ^ 2 ≤ ⟪pgOp (a • x + b • y) v, v⟫ := by
    intro v
    rw [h_op_add]
    have h_inner_add : ⟪(a • pgOp x + b • pgOp y) v, v⟫ = a * ⟪pgOp x v, v⟫ + b * ⟪pgOp y v, v⟫ := by
      have h : (a • pgOp x + b • pgOp y) v = a • (pgOp x v) + b • (pgOp y v) := by simp
      rw [h]
      simp [inner_add_left, inner_smul_left]
    rw [h_inner_add]
    have hx_bounds := hx_forall v
    have hy_bounds := hy_forall v
    rcases hx_bounds with ⟨hx_low, hx_high⟩
    rcases hy_bounds with ⟨hy_low, hy_high⟩
    have h1 : a * ⟪pgOp x v, v⟫ ≥ a * (pgTmin d ρ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hx_low ha.le
    have h2 : b * ⟪pgOp y v, v⟫ ≥ b * (pgTmin d ρ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hy_low hb.le
    have hsum' : a * (pgTmin d ρ * ‖v‖ ^ 2) + b * (pgTmin d ρ * ‖v‖ ^ 2) = pgTmin d ρ * ‖v‖ ^ 2 := by
      rw [← add_mul, hsum, one_mul]
    linarith
  have h_upper : ∀ v, ⟪pgOp (a • x + b • y) v, v⟫ ≤ pgLD ρ * ‖v‖ ^ 2 := by
    intro v
    rw [h_op_add]
    have h_inner_add : ⟪(a • pgOp x + b • pgOp y) v, v⟫ = a * ⟪pgOp x v, v⟫ + b * ⟪pgOp y v, v⟫ := by
      have h : (a • pgOp x + b • pgOp y) v = a • (pgOp x v) + b • (pgOp y v) := by simp
      rw [h]
      simp [inner_add_left, inner_smul_left]
    rw [h_inner_add]
    have hx_bounds := hx_forall v
    have hy_bounds := hy_forall v
    rcases hx_bounds with ⟨hx_low, hx_high⟩
    rcases hy_bounds with ⟨hy_low, hy_high⟩
    have h1 : a * ⟪pgOp x v, v⟫ ≤ a * (pgLD ρ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hx_high ha.le
    have h2 : b * ⟪pgOp y v, v⟫ ≤ b * (pgLD ρ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hy_high hb.le
    have hsum' : a * (pgLD ρ * ‖v‖ ^ 2) + b * (pgLD ρ * ‖v‖ ^ 2) = pgLD ρ * ‖v‖ ^ 2 := by
      rw [← add_mul, hsum, one_mul]
    linarith
  refine ⟨h_adj, h_norm, ?_⟩
  intro v
  exact ⟨h_lower v, h_upper v⟩

/-- `D` is compact: closed as an intersection of closed conditions, bounded by `|μ| ≤ κ ρ` and the entry bound
`|M i j| ≤ 2 (|t_min| + |t_max|)` (polarization on `e_i ± e_j`). -/
theorem pgDom_isCompact (d : ℕ) (ρ : ℝ) : IsCompact (pgDom d ρ) := by
  have hcv : ∀ v : EuclideanSpace ℝ (Fin d), Continuous fun x : PgSp d => pgOp x v := by
    intro v
    simp_rw [pgOp_apply]
    exact (PiLp.continuous_toLp 2 _).comp (((pg_continuous d).2.1).matrix_mulVec continuous_const)
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hset : pgDom d ρ = (⋂ v : EuclideanSpace ℝ (Fin d), ⋂ w : EuclideanSpace ℝ (Fin d),
        {x : PgSp d | ⟪pgOp x v, w⟫ = ⟪v, pgOp x w⟫}) ∩ {x | ‖pgMu x‖ ≤ pgKappa * ρ} ∩
        ⋂ v : EuclideanSpace ℝ (Fin d), ({x : PgSp d | pgTmin d ρ * ‖v‖ ^ 2 ≤ ⟪pgOp x v, v⟫} ∩
          {x | ⟪pgOp x v, v⟫ ≤ pgLD ρ * ‖v‖ ^ 2}) := by
      ext x
      simp only [pgDom, IsPgDom, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe]
      tauto
    rw [hset]
    refine ((isClosed_iInter fun v => isClosed_iInter fun w => ?_).inter ?_).inter
      (isClosed_iInter fun v => (isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const))
    · exact isClosed_eq ((hcv v).inner continuous_const) (continuous_const.inner (hcv w))
    · exact isClosed_le (pg_continuous d).1.norm continuous_const
    · exact (hcv v).inner continuous_const
    · exact (hcv v).inner continuous_const
  · rw [isBounded_iff_forall_norm_le]
    obtain ⟨c, hcdef⟩ : ∃ c, c = |pgTmin d ρ| + |pgLD ρ| := ⟨_, rfl⟩
    have hc : 0 ≤ c := by rw [hcdef]; positivity
    refine ⟨Real.sqrt ((pgKappa * ρ) ^ 2 + d * d * (2 * c) ^ 2), fun x hx => ?_⟩
    have hx' : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
    obtain ⟨hsa, hmu, hform⟩ := hx'
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
    have hq : ∀ u, |⟪pgOp x u, u⟫| ≤ c * ‖u‖ ^ 2 := by
      intro u
      obtain ⟨h1, h2⟩ := hform u
      have hu := sq_nonneg ‖u‖
      have a1 := neg_abs_le (pgTmin d ρ)
      have a2 := le_abs_self (pgLD ρ)
      have a3 := abs_nonneg (pgTmin d ρ)
      have a4 := abs_nonneg (pgLD ρ)
      rw [abs_le]; constructor <;> nlinarith
    have hent : ∀ i j, |pgMat x i j| ≤ 2 * c := by
      intro i j
      obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin d), a = EuclideanSpace.single j (1 : ℝ) := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin d), b = EuclideanSpace.single i (1 : ℝ) := ⟨_, rfl⟩
      have hentry : pgMat x i j = ⟪pgOp x a, b⟫ := by
        rw [pgOp_apply, ha, hb, EuclideanSpace.inner_single_right]
        simp [Matrix.mulVec_single]
      have hs : ⟪pgOp x b, a⟫ = ⟪pgOp x a, b⟫ := by
        have := hsym b a
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [this, real_inner_comm]
      have hpol : 4 * ⟪pgOp x a, b⟫ = ⟪pgOp x (a + b), a + b⟫ - ⟪pgOp x (a - b), a - b⟫ := by
        simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
        linarith [hs]
      have hna : ‖a‖ = 1 := by rw [ha]; simp
      have hnb : ‖b‖ = 1 := by rw [hb]; simp
      have h1 : ‖a + b‖ ^ 2 ≤ 4 := by nlinarith [norm_add_le a b, norm_nonneg (a + b)]
      have h2 : ‖a - b‖ ^ 2 ≤ 4 := by nlinarith [norm_sub_le a b, norm_nonneg (a - b)]
      have e1 := hq (a + b)
      have e2 := hq (a - b)
      rw [hentry, abs_le]
      rw [abs_le] at e1 e2
      constructor <;> nlinarith
    rw [← Real.sqrt_sq (norm_nonneg x)]
    apply Real.sqrt_le_sqrt
    rw [pgSp_norm_sq]
    gcongr ?_ + ?_
    · exact pow_le_pow_left₀ (norm_nonneg _) hmu 2
    · calc ∑ i, ∑ j, pgMat x i j ^ 2 ≤ ∑ _i : Fin d, ∑ _j : Fin d, (2 * c) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            exact sq_le_sq' (abs_le.mp (hent i j)).1 (abs_le.mp (hent i j)).2
        _ = d * d * (2 * c) ^ 2 := by simp; ring


/-- The projection on a nonempty closed convex `D` lands in `D`, is a contraction towards each point of `D`, and is
1-Lipschitz. -/
theorem pgProj_spec (d : ℕ) (ρ : ℝ) (hne : (pgDom d ρ).Nonempty) (hcl : IsClosed (pgDom d ρ))
    (hcv : Convex ℝ (pgDom d ρ)) :
    (∀ y, pgProj d ρ y ∈ pgDom d ρ) ∧ (∀ y, ∀ z ∈ pgDom d ρ, ‖pgProj d ρ y - z‖ ≤ ‖y - z‖) ∧
      LipschitzWith 1 (pgProj d ρ) := by
  have hcomp : IsComplete (pgDom d ρ) := hcl.isComplete
  have h_exists : ∀ y : PgSp d, ∃ p ∈ pgDom d ρ, ‖y - p‖ = ⨅ w : (pgDom d ρ), ‖y - w‖ := by
    intro y
    exact exists_norm_eq_iInf_of_complete_convex hne hcomp hcv y
  have h_mem : ∀ y : PgSp d, pgProj d ρ y ∈ pgDom d ρ := by
    intro y
    dsimp [pgProj]
    by_cases h : ∃ z ∈ pgDom d ρ, ∀ w ∈ pgDom d ρ, ‖y - z‖ ≤ ‖y - w‖
    · rw [dite_eq_left h]
      exact h.choose_spec.1
    · rw [dite_eq_right h]
      exfalso
      rcases h_exists y with ⟨p, hp, h_eq⟩
      apply h
      refine ⟨p, hp, ?_⟩
      intro w hw
      have hle : ‖y - p‖ ≤ ‖y - w‖ := by
        have hbdd : BddBelow (Set.range fun (w' : pgDom d ρ) => ‖y - w'‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w', rfl⟩
          apply norm_nonneg
        have := ciInf_le hbdd ⟨w, hw⟩
        rw [h_eq]
        exact this
      exact hle
  have h_min : ∀ y w : PgSp d, w ∈ pgDom d ρ → ‖y - pgProj d ρ y‖ ≤ ‖y - w‖ := by
    intro y w hw
    dsimp [pgProj]
    by_cases h : ∃ z ∈ pgDom d ρ, ∀ w' ∈ pgDom d ρ, ‖y - z‖ ≤ ‖y - w'‖
    · rw [dite_eq_left h]
      exact h.choose_spec.2 w hw
    · rw [dite_eq_right h]
      exfalso
      rcases h_exists y with ⟨p, hp, h_eq⟩
      apply h
      refine ⟨p, hp, ?_⟩
      intro w' hw'
      have hle : ‖y - p‖ ≤ ‖y - w'‖ := by
        have hbdd : BddBelow (Set.range fun (w' : pgDom d ρ) => ‖y - w'‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w', rfl⟩
          apply norm_nonneg
        have := ciInf_le hbdd ⟨w', hw'⟩
        rw [h_eq]
        exact this
      exact hle
  have h_var : ∀ y w : PgSp d, w ∈ pgDom d ρ → inner ℝ (y - pgProj d ρ y) (w - pgProj d ρ y) ≤ 0 := by
    intro y w hw
    set p := pgProj d ρ y with hp_def
    have hp_mem : p ∈ pgDom d ρ := h_mem y
    have hp_eq : ‖y - p‖ = ⨅ w' : (pgDom d ρ), ‖y - w'‖ := by
      apply le_antisymm
      · have h_nonempty : Nonempty (pgDom d ρ) := hne.coe_sort
        refine le_ciInf ?_
        intro w'
        have hmin := h_min y w'.1 w'.2
        simpa [hp_def] using hmin
      · have hbdd : BddBelow (Set.range fun (w' : pgDom d ρ) => ‖y - w'‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨w', rfl⟩
          apply norm_nonneg
        have hciInf := ciInf_le hbdd ⟨p, hp_mem⟩
        simpa [hp_def] using hciInf
    exact ((norm_eq_iInf_iff_real_inner_le_zero hcv hp_mem).mp hp_eq w hw)
  have h_nonexp : ∀ y z : PgSp d, z ∈ pgDom d ρ → ‖pgProj d ρ y - z‖ ≤ ‖y - z‖ := by
    intro y z hz
    set p := pgProj d ρ y with hp_def
    have hp_mem : p ∈ pgDom d ρ := h_mem y
    have hvar := h_var y z hz
    have h_expand : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 + ‖p - z‖ ^ 2 + 2 * inner ℝ (y - p) (p - z) := by
      have h_sub_add : y - z = (y - p) + (p - z) := by abel
      rw [h_sub_add]
      rw [norm_add_sq_real]
      ring
    have h_inner_nonneg : 0 ≤ inner ℝ (y - p) (p - z) := by
      have : inner ℝ (y - p) (p - z) = -inner ℝ (y - p) (z - p) := by
        rw [show p - z = -(z - p) by abel, inner_neg_right]
      rw [this]
      linarith
    have h_sq_ineq : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
      nlinarith
    have h_nonneg_norm : 0 ≤ ‖p - z‖ := norm_nonneg _
    have h_nonneg_norm' : 0 ≤ ‖y - z‖ := norm_nonneg _
    nlinarith
  have h_lipschitz : LipschitzWith 1 (pgProj d ρ) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro y y'
    set p := pgProj d ρ y with hp_def
    set q := pgProj d ρ y' with hq_def
    have hp_mem : p ∈ pgDom d ρ := h_mem y
    have hq_mem : q ∈ pgDom d ρ := h_mem y'
    have hvar1 : inner ℝ (y - p) (q - p) ≤ 0 := h_var y q hq_mem
    have hvar2 : inner ℝ (y' - q) (p - q) ≤ 0 := h_var y' p hp_mem
    have h_add : inner ℝ (y - p) (q - p) + inner ℝ (y' - q) (p - q) ≤ 0 := by linarith
    have h_rearrange : inner ℝ (y - p) (q - p) + inner ℝ (y' - q) (p - q) =
        inner ℝ (y - y') (q - p) + ‖q - p‖ ^ 2 := by
      calc
        inner ℝ (y - p) (q - p) + inner ℝ (y' - q) (p - q)
            = inner ℝ (y - p) (q - p) + inner ℝ (y' - q) (-(q - p)) := by rw [neg_sub q p]
        _ = inner ℝ (y - p) (q - p) + (-inner ℝ (y' - q) (q - p)) := by rw [inner_neg_right]
        _ = inner ℝ (y - p) (q - p) - inner ℝ (y' - q) (q - p) := by ring
        _ = inner ℝ ((y - p) - (y' - q)) (q - p) := by rw [← inner_sub_left]
        _ = inner ℝ ((y - y') + (q - p)) (q - p) := by
          congr 1
          abel
        _ = inner ℝ (y - y') (q - p) + inner ℝ (q - p) (q - p) := by rw [inner_add_left]
        _ = inner ℝ (y - y') (q - p) + ‖q - p‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    rw [h_rearrange] at h_add
    have h_inner_eq : inner ℝ (y' - y) (q - p) = -inner ℝ (y - y') (q - p) := by
      rw [← inner_neg_left, neg_sub]
    have h_cauchy : inner ℝ (y' - y) (q - p) ≤ ‖y' - y‖ * ‖q - p‖ :=
      real_inner_le_norm _ _
    have h_norm_sub : ‖y' - y‖ = ‖y - y'‖ := norm_sub_rev _ _
    rw [h_norm_sub] at h_cauchy
    have h_ineq : ‖q - p‖ ^ 2 ≤ ‖y - y'‖ * ‖q - p‖ := by
      have h_nonneg_sq : 0 ≤ ‖q - p‖ ^ 2 := by positivity
      have h_lower : ‖q - p‖ ^ 2 ≤ inner ℝ (y' - y) (q - p) := by
        linarith
      linarith
    by_cases hzero : ‖q - p‖ = 0
    · rw [dist_eq_norm, norm_sub_rev, hzero]
      simp
    · have hpos : 0 < ‖q - p‖ := by
        have hnonneg := norm_nonneg (q - p)
        exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
      have h_div : ‖q - p‖ ≤ ‖y - y'‖ := by
        nlinarith
      rw [dist_eq_norm, norm_sub_rev]
      simpa [dist_eq_norm] using h_div
  exact ⟨h_mem, h_nonexp, h_lipschitz⟩

/-! ## Measurability at a fixed body -/

/-- `F~(x, g) = π~(μ + T g)` is measurable jointly in the point and the sample, for a closed body. -/
theorem pgFt_measurable (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) :
    Measurable (fun p : PgSp d × EuclideanSpace ℝ (Fin d) => pgFt K ρ p.1 p.2) := by
  exact (hPT d K ρ hK (pgJb d ρ)).comp (pg_continuous d).2.2.measurable

/-- `x ↦ (T_x)⁻¹` is measurable on `PgSp d` (`M⁻¹ = (det M)⁻¹ adj M`). -/
theorem pgMat_inv_measurable (d : ℕ) : Measurable fun x : PgSp d => (pgMat x)⁻¹ := by
  have : (fun x : PgSp d => (pgMat x)⁻¹) = fun x => (pgMat x).det⁻¹ • (pgMat x).adjugate := by
    funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (pg_continuous d).2.1.matrix_det.measurable.inv.smul (pg_continuous d).2.1.matrix_adjugate.measurable

/-- `pgPack` is continuous jointly in the mean and the matrix. -/
theorem pgPack_continuous (d : ℕ) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ => pgPack p.1 p.2 := by
  unfold pgPack
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  rcases k with i | ⟨i, j⟩
  · exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
  · exact (continuous_snd.matrix_elem i j)

/-- `g ↦ g gᵀ - I` is continuous. -/
theorem pgGG_continuous (d : ℕ) : Continuous fun g : EuclideanSpace ℝ (Fin d) => pgGG g := by
  unfold pgGG
  have hg : Continuous fun g : EuclideanSpace ℝ (Fin d) => (fun i => g i : Fin d → ℝ) :=
    continuous_pi fun i => PiLp.continuous_apply 2 _ i
  exact (hg.matrix_vecMulVec hg).sub continuous_const

/-- The estimate `V(x, g)` of Lemma E is measurable jointly in the point and the sample, for a closed body. -/
theorem pgV_measurable (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) : Measurable (Function.uncurry (pgV K ρ)) := by
  have hF := pgFt_measurable hPT d K ρ hK
  have hinv : Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) => (pgMat p.1)⁻¹ :=
    (pgMat_inv_measurable d).comp measurable_fst
  have hg : Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) => (fun i => p.2 i : Fin d → ℝ) :=
    (continuous_pi fun i => PiLp.continuous_apply 2 _ i).measurable.comp measurable_snd
  have hGG : Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) => pgGG p.2 :=
    (pgGG_continuous d).measurable.comp measurable_snd
  have hmv : Continuous fun q : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => q.1 *ᵥ q.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  have hA : Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) =>
      WithLp.toLp 2 (pgFt K ρ p.1 p.2 • ((pgMat p.1)⁻¹ *ᵥ fun i => p.2 i)) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (hF.smul (hmv.measurable.comp (hinv.prodMk hg)))
  have hB : Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) =>
      (pgFt K ρ p.1 p.2 / 2) • ((pgMat p.1)⁻¹ * pgGG p.2 + ((pgMat p.1)⁻¹ * pgGG p.2)ᵀ) -
        (pgKappa / d) • (pgMat p.1)⁻¹ := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply,
      smul_eq_mul]
    have he : ∀ a b : Fin d, Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) => (pgMat p.1)⁻¹ a b :=
      fun a b => hinv.eval_matrix
    have hge : ∀ a b : Fin d, Measurable fun p : PgSp d × EuclideanSpace ℝ (Fin d) => pgGG p.2 a b :=
      fun a b => hGG.eval_matrix
    refine ((hF.div_const 2).mul ((Finset.measurable_sum _ fun k _ => (he i k).mul (hge k j)).add
      (Finset.measurable_sum _ fun k _ => (he j k).mul (hge k i)))).sub (measurable_const.mul (he i j))
  have hP := (pgPack_continuous d).measurable.comp (hA.prodMk hB)
  have heq : Function.uncurry (pgV K ρ) = fun p : PgSp d × EuclideanSpace ℝ (Fin d) =>
      pgPack (WithLp.toLp 2 (pgFt K ρ p.1 p.2 • ((pgMat p.1)⁻¹ *ᵥ fun i => p.2 i)))
        ((pgFt K ρ p.1 p.2 / 2) • ((pgMat p.1)⁻¹ * pgGG p.2 + ((pgMat p.1)⁻¹ * pgGG p.2)ᵀ) -
          (pgKappa / d) • (pgMat p.1)⁻¹) := by
    funext p; rfl
  rw [heq]
  exact hP

/-- The basic verdict is a measurable event of the point and the samples, for a closed body: the matrix condition is
the preimage of a closed set of matrices. -/
theorem pgVerdict_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 p.2} := by
  have hw : ∀ i, Measurable fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) => p.2 i := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  have hF : ∀ i, Measurable fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) => pgFt K ρ p.1 (p.2 i) := fun i =>
    (pgFt_measurable hPT d K ρ hK).comp (measurable_fst.prodMk (hw i))
  have hkh : Measurable fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) =>
      ((pgNT d ρ : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hF i)
  have hbh : Measurable fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) =>
      ((pgNT d ρ : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) • p.2 i :=
    Measurable.fun_const_smul (Finset.measurable_sum _ fun i _ => (hF i).smul (hw i)) _
  have hQh : Measurable fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) =>
      ((pgNT d ρ : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) • pgGG (p.2 i) := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (hF i).mul
      ((pgGG_continuous d).measurable.comp (hw i)).eval_matrix)
  have hC : IsClosed {M : Matrix (Fin d) (Fin d) ℝ |
      ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))
  have hset : {p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 p.2} =
      {p | ((pgNT d ρ : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) ≤ 1.075 * pgKappa} ∩
      {p | ‖((pgNT d ρ : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) • p.2 i‖ ≤
        3 / 4 * pgTaub d ρ} ∩
      (fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) =>
        ((pgNT d ρ : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ p.1 (p.2 i) • pgGG (p.2 i)) ⁻¹'
        {M : Matrix (Fin d) (Fin d) ℝ | ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)} := by
    ext p
    simp only [pgVerdict, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, and_assoc]
  rw [hset]
  exact ((measurableSet_le hkh measurable_const).inter (measurableSet_le hbh.norm measurable_const)).inter
    (hC.measurableSet.preimage hQh)

/-- The amplified test is a measurable event of the point and the blocks, for a closed body. -/
theorem pgTest_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTest K ρ δ p.1 p.2} := by
  classical
  let m := pgMT δ
  have hVerdictSet : MeasurableSet {q : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ q.1 q.2} :=
    pgVerdict_measurableSet hPT d K ρ hK
  have h_eval (i : ℕ) : Measurable (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h_map (i : ℕ) : Measurable (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => (p.1, p.2 i)) :=
    Measurable.prodMk measurable_fst (h_eval i)
  have hAi (i : ℕ) : MeasurableSet {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} := by
    have h_eq : {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} =
        (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => (p.1, p.2 i)) ⁻¹'
        {q : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ q.1 q.2} := by
      ext p; simp
    rw [h_eq]
    exact hVerdictSet.preimage (h_map i)
  have h_sum_meas : Measurable (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) =>
      ∑ i ∈ Finset.range m, ((({p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} : Set _).indicator (fun _ => (1 : ℝ))) p)) := by
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.indicator measurable_const (hAi i)
  have h_card_eq (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) :
      (((Finset.range m).filter fun i => pgVerdict K ρ p.1 (p.2 i)).card : ℝ) =
      ∑ i ∈ Finset.range m, ((({p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} : Set _).indicator (fun _ => (1 : ℝ))) p) := by
    classical
    calc
      (((Finset.range m).filter fun i => pgVerdict K ρ p.1 (p.2 i)).card : ℝ)
          = (∑ i ∈ (Finset.range m).filter (fun i => pgVerdict K ρ p.1 (p.2 i)), (1 : ℝ)) := by
        simp
      _ = ∑ i ∈ Finset.range m, (if pgVerdict K ρ p.1 (p.2 i) then (1 : ℝ) else 0) := by
        simp
      _ = ∑ i ∈ Finset.range m, ((({p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} : Set _).indicator (fun _ => (1 : ℝ))) p) := by
        simp [Set.indicator]
  have h_target_eq : {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTest K ρ δ p.1 p.2} =
      {p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | (m : ℝ) / 2 < (((Finset.range m).filter fun i => pgVerdict K ρ p.1 (p.2 i)).card : ℝ)} := by
    ext p; simp [pgTest, m]
  rw [h_target_eq]
  have h_const_meas : Measurable (fun (_ : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => (m : ℝ) / 2) :=
    measurable_const
  have h_rhs_meas : Measurable (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) =>
      (((Finset.range m).filter fun i => pgVerdict K ρ p.1 (p.2 i)).card : ℝ)) := by
    have : (fun (p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) =>
        (((Finset.range m).filter fun i => pgVerdict K ρ p.1 (p.2 i)).card : ℝ)) =
        (fun p => ∑ i ∈ Finset.range m, ((({p : PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict K ρ p.1 (p.2 i)} : Set _).indicator (fun _ => (1 : ℝ))) p)) := by
      ext p; exact h_card_eq p
    rw [this]
    exact h_sum_meas
  exact measurableSet_lt h_const_meas h_rhs_meas

/-- The average of the descent is measurable in the samples, for a closed body and a continuous projection. -/
theorem pgDescent_measurable (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) (hproj : Continuous (pgProj d ρ)) : Measurable (pgDescent K ρ) := by
  unfold pgDescent sgdAvg
  have h_proj_meas : Measurable (pgProj d ρ) := hproj.measurable
  have h_pgV_meas : Measurable (Function.uncurry (pgV K ρ)) := pgV_measurable hPT d K ρ hK
  have h_iter_meas : ∀ (t : ℕ), Measurable (λ (a : ℕ → EuclideanSpace ℝ (Fin d)) =>
    sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t) := by
    intro t
    induction' t with t ih
    · simp [sgdIter]
    · simp [sgdIter]
      have h_pair : Measurable (λ (a : ℕ → EuclideanSpace ℝ (Fin d)) =>
        (sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t, a t)) :=
        Measurable.prodMk ih (measurable_pi_apply t)
      have h_V : Measurable (λ (a : ℕ → EuclideanSpace ℝ (Fin d)) =>
        (pgV K ρ) (sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t) (a t)) := by
        have := h_pgV_meas.comp h_pair
        convert this using 1
        ext a
        simp [Function.uncurry]
      have h_sub : Measurable (λ (a : ℕ → EuclideanSpace ℝ (Fin d)) =>
        sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t -
        (pgStepSize d ρ) • (pgV K ρ) (sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t) (a t)) :=
        Measurable.sub ih (h_V.const_smul (pgStepSize d ρ))
      exact h_proj_meas.comp h_sub
  have h_sum : Measurable (λ (a : ℕ → EuclideanSpace ℝ (Fin d)) =>
    ∑ t ∈ Finset.range (pgNs d ρ), sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t) :=
    Finset.measurable_sum (Finset.range (pgNs d ρ)) (λ t _ => h_iter_meas t)
  exact h_sum.const_smul ((pgNs d ρ : ℝ)⁻¹)

end AdversarialBco.Poly
