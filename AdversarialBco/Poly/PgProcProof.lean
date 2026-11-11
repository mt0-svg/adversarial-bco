/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProcBase
public import AdversarialBco.Poly.PgLemmasProof
public import AdversarialBco.Poly.PgArithProof
public import AdversarialBco.Poly.PosGaussProof
public import AdversarialBco.Poly.PgMeasProof
public import AdversarialBco.Poly.PgProbProof

@[expose] public section

/-!
Theorems PG-core and PG, `pgCoreThm : PgCoreThm` and `pgThm : PgThm` of
`PgProc.lean`: the auxiliary definitions, the leaves and the assemblies. The leaves take the interface statements they
read (`D5Subgrad`, `SgdExpect`, ...) as hypotheses; `pgCoreHyps_of` and `pgCoreThm_pgThm_of` feed them the delivered
theorems: `PgLemmasProof.lean`, `PgArithProof.lean`, `PosGaussProof.lean`, `PgProbProof.lean` and
`PgMeasProof.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

namespace AdversarialBco.Poly

/-! ## Auxiliary definitions -/

/-- The hypotheses of Theorem F.3 on the body: closed, convex, `B̄(0, 1) ⊆ K ⊆ B̄(0, ρ)`. -/
def PgBody {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) : Prop :=
  Convex ℝ K ∧ IsClosed K ∧ Metric.closedBall 0 1 ⊆ K ∧ K ⊆ Metric.closedBall 0 ρ

/-- The objective `h(μ, T) = E π(μ + T g) - (κ/d) log |det T|` on `PgSp d`. -/
noncomputable def pgH {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d) : ℝ :=
  posObj K pgKappa (pgMu x) (pgOp x)

/-- `k = E F(g)` at `x`. -/
noncomputable def pgKs {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d) : ℝ := posK K (pgMu x) (pgOp x)

/-- `b = E[F(g) g]` at `x`. -/
noncomputable def pgBs {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d) : EuclideanSpace ℝ (Fin d) :=
  posB K (pgMu x) (pgOp x)

/-- The matrix `Q = E[(g gᵀ - I) F(g)]` at `x`. -/
noncomputable def pgQs {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => posQ K (pgMu x) (pgOp x) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- The subgradient `γ = (T⁻¹ b, sym(T⁻¹ Q) - (κ/d) T⁻¹)` of (D5). -/
noncomputable def pgGam {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d) : PgSp d :=
  pgPack (WithLp.toLp 2 ((pgMat x)⁻¹ *ᵥ fun i => pgBs K x i))
    ((1 / 2 : ℝ) • ((pgMat x)⁻¹ * pgQs K x + ((pgMat x)⁻¹ * pgQs K x)ᵀ) - (pgKappa / d) • (pgMat x)⁻¹)

/-- The bias bound `u = η L_D (1 + d^{1/2})` of Lemma E and Lemma T. -/
noncomputable def pgU (d ρ : ℝ) : ℝ := pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)

/-- `β = 3^{1/2} u/t_min`, the bias of the estimates of the descent (Lemma E (a)). -/
noncomputable def pgBeta (d ρ : ℝ) : ℝ := Real.sqrt 3 * pgU d ρ / pgTmin d ρ

/-- The sound condition of the test: `k ≤ 1.1 κ`, `|b| ≤ τ_b`, `Q ≥ (κ/(2d)) I`. -/
def PgSound {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) : Prop :=
  pgKs K x ≤ 1.1 * pgKappa ∧ ‖pgBs K x‖ ≤ pgTaub d ρ ∧
    ∀ v, pgKappa / (2 * d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v

/-- The complete condition of the test: `k ≤ 1.05 κ`, `|b| ≤ τ_b/2`, `Q ≥ (3/4)(κ/d) I`. -/
def PgComplete {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) : Prop :=
  pgKs K x ≤ 1.05 * pgKappa ∧ ‖pgBs K x‖ ≤ pgTaub d ρ / 2 ∧
    ∀ v, 3 / 4 * (pgKappa / d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v

/-- The estimate `k^` of a basic verdict. -/
noncomputable def pgKh {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (pgNT d ρ : ℝ)⁻¹ * ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i)

/-- The estimate `b^` of a basic verdict. -/
noncomputable def pgBh {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (pgNT d ρ : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i

/-- The estimate `Q^` of a basic verdict. -/
noncomputable def pgQh {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  (pgNT d ρ : ℝ)⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • pgGG (w i)

/-- The estimates of a basic verdict are accurate: `|k^ - k| ≤ κ/40`, `|b^ - b| ≤ τ_b/4`,
`|Q^ - Q|_F ≤ κ/(8d)`. -/
def PgAccurate {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40 ∧ ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4 ∧
    ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2

/-- `δ' = δ/(2J)`. -/
noncomputable def pgDp (δ : ℝ) : ℝ := δ / (2 * pgJr δ)

/-- The error `ε(g) = F~(g) - F(g)` of the gauge by bisection. -/
noncomputable def pgEps {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  pgFt K ρ x g - posF K (pgMu x) (pgOp x) g

/-- The vector `E[ε(g) g]`. -/
noncomputable def pgEpsVec {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) : Fin d → ℝ :=
  fun i => ∫ g, pgEps K ρ x g * g i ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The matrix `E[(g gᵀ - I) ε(g)]`. -/
noncomputable def pgEpsMat {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ g, gstat g i j * pgEps K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The conclusion reached after the first `i` stages: nothing before the first stage; after stage `i + 1`, a good
position for the body `K ∩ B̄(0, 2^{i+1} r0)` with the radius `36.4 d λ(ρ_{i+1})` of Theorem F.3. -/
def PgStageGood (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 : ℝ) : ℕ → Option (PgSp d) → Prop
  | 0, _ => True
  | i + 1, o => PgGood d (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (36.4 * d * pgLam (pgRhoStage d i)) o

/-! ## Leaves: the domain -/

theorem pgX1_mem (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : pgX1 d ρ ∈ pgDom d ρ := by
  have hMu : pgMu (pgX1 d ρ) = 0 := by
    ext i; simp [pgX1, pgMu, pgPack]
  have hMat : pgMat (pgX1 d ρ) = pgTmin d ρ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j; simp [pgX1, pgMat, pgPack]
  have hOp : pgOp (pgX1 d ρ) = Matrix.toEuclideanCLM (𝕜 := ℝ) (pgTmin d ρ • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    simp [pgOp, hMat]
  unfold pgDom IsPgDom
  simp [hMu, hOp]
  have h_sa : IsSelfAdjoint ((pgTmin d ρ : ℝ) • (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) := by
    have h_eq : star ((pgTmin d ρ : ℝ) • (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) =
      (pgTmin d ρ : ℝ) • (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
      simpa [star_smul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_one]
    exact h_eq
  have h_norm : 0 ≤ pgKappa * ρ := by
    have hk : 0 ≤ pgKappa := by unfold pgKappa; norm_num
    have hρ' : 0 ≤ ρ := by linarith
    nlinarith
  have h_ineq : pgTmin d ρ ≤ pgLD ρ := by
    unfold pgTmin pgLD pgKappa pgPB pgLam
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hρ' : (1 : ℝ) ≤ ρ := hρ
    have h_sqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.log (1 + ρ)) := by
      have h_arg_ge_one : 1 ≤ 2 * Real.log (1 + ρ) := by
        have h_log_ge : Real.log 2 ≤ Real.log (1 + ρ) :=
          Real.log_le_log (by norm_num) (by linarith)
        have h_two_log2 : 1 ≤ 2 * Real.log 2 := by
          have hlog2pos : 0.5 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          linarith
        linarith
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_le_sqrt h_arg_ge_one
    have h_pos_denom : 0 < 9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) := by positivity
    have h_pos_rhs : 0 < ((1 : ℝ)/8 * (1254/1000 : ℝ)) * ρ := by positivity
    field_simp
    ring_nf
    have h_goal : (8000 : ℝ) ≤ (11286 : ℝ) * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) * ρ := by
      have h_rhs_ge : 11286 * 1 * 1 * 1 ≤ 11286 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) * ρ := by
        have h_d : (1 : ℝ) ≤ d := hd'
        have h_rho : (1 : ℝ) ≤ ρ := hρ'
        have h_sqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.log (1 + ρ)) := h_sqrt_ge_one
        nlinarith
      have h_8000_le_11286 : (8000 : ℝ) ≤ 11286 * 1 * 1 * 1 := by norm_num
      exact le_trans h_8000_le_11286 h_rhs_ge
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_goal
  refine ⟨h_sa, h_norm, ?_⟩
  intro v
  have h_inner : ⟪(pgTmin d ρ : ℝ) • v, v⟫ = pgTmin d ρ * ‖v‖ ^ 2 := by
    calc
      ⟪(pgTmin d ρ : ℝ) • v, v⟫ = (pgTmin d ρ : ℝ) * ⟪v, v⟫ := by rw [real_inner_smul_left]
      _ = pgTmin d ρ * ‖v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  constructor
  · rw [h_inner]
  · rw [h_inner]
    nlinarith

theorem pgDom_diam (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ∀ x ∈ pgDom d ρ, ∀ y ∈ pgDom d ρ, ‖x - y‖ ≤ pgDelta d ρ := by
  intro x hx y hy
  have hx' : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
  have hy' : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu y) (pgOp y) := hy
  obtain ⟨hsx, hmx, hfx⟩ := hx'
  obtain ⟨hsy, hmy, hfy⟩ := hy'
  have hlam : 0 < pgLam ρ := by
    unfold pgLam
    apply Real.sqrt_pos.2
    have : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have htmin : 0 ≤ pgTmin d ρ := by unfold pgTmin; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = pgLD ρ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; unfold pgLD pgKappa pgPB; positivity
  obtain ⟨A, hA⟩ : ∃ A, A = pgOp x - pgOp y := ⟨_, rfl⟩
  have hAsym : (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).IsSymmetric := by
    have h1 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsx
    have h2 := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsy
    intro u v
    have e1 := h1 u v
    have e2 := h2 u v
    simp only [ContinuousLinearMap.coe_coe] at e1 e2 ⊢
    rw [hA, sub_apply, sub_apply, inner_sub_left, inner_sub_right, e1, e2]
  have hq : ∀ v, |⟪A v, v⟫| ≤ c * ‖v‖ ^ 2 := by
    intro v
    obtain ⟨a1, a2⟩ := hfx v
    obtain ⟨b1, b2⟩ := hfy v
    rw [hA, sub_apply, inner_sub_left, abs_le, hc]
    have := sq_nonneg ‖v‖
    constructor <;> nlinarith
  have hAnorm : ‖A‖ ≤ c := by
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient A hAsym]
    refine ciSup_le fun v => ?_
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real]
    rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
    · rw [← hv]; simp [hc0]
    · rw [abs_div, abs_sq, div_le_iff₀ (by positivity)]
      exact hq v
  have hcol : ∀ j, ∑ i, (pgMat x - pgMat y) i j ^ 2 ≤ c ^ 2 := by
    intro j
    have hAe : A (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun i => (pgMat x - pgMat y) i j) := by
      rw [hA, sub_apply, pgOp_apply, pgOp_apply]
      ext i
      simp [Matrix.mulVec_single, Matrix.sub_apply]
    have h1 : ‖A (EuclideanSpace.single j 1)‖ ≤ c := by
      calc ‖A (EuclideanSpace.single j 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := A.le_opNorm _
        _ ≤ c := by simpa using hAnorm
    have h2 : ‖A (EuclideanSpace.single j 1)‖ ^ 2 = ∑ i, (pgMat x - pgMat y) i j ^ 2 := by
      rw [hAe, EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hmu : pgMu (x - y) = pgMu x - pgMu y := by
    ext i; simp [pgMu]
  have hmat : pgMat (x - y) = pgMat x - pgMat y := by
    ext i j; simp [pgMat]
  have hmu2 : ‖pgMu x - pgMu y‖ ^ 2 ≤ (2 * (pgKappa * ρ)) ^ 2 := by
    have := norm_sub_le (pgMu x) (pgMu y)
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hmat2 : ∑ i, ∑ j, (pgMat x - pgMat y) i j ^ 2 ≤ d * c ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, (pgMat x - pgMat y) i j ^ 2 ≤ ∑ _j : Fin d, c ^ 2 := Finset.sum_le_sum fun j _ => hcol j
      _ = d * c ^ 2 := by simp
  have hD0 : 0 ≤ pgDelta d ρ := by unfold pgDelta pgKappa pgPB; positivity
  have hD2 : pgDelta d ρ ^ 2 = (pgKappa * ρ) ^ 2 * (4 + pgPB ^ 2 * d) := by
    unfold pgDelta
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq : ‖x - y‖ ^ 2 ≤ pgDelta d ρ ^ 2 := by
    rw [pgSp_norm_sq, hmu, hmat, hD2]
    have hc2 : c ^ 2 = (pgKappa * ρ) ^ 2 * pgPB ^ 2 := by rw [hc]; unfold pgLD; ring
    rw [hc2] at hmat2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hD0 two_ne_zero).mp hsq

theorem pgDom_inv (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (pgMat x).det ≠ 0 ∧ IsInvPair (pgOp x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹) ∧
      ∀ v, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹ v‖ ≤ ‖v‖ / pgTmin d ρ := by
  have hdom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
  rcases hdom with ⟨h_sa, h_norm, h_bound⟩
  have hlam_pos : 0 < pgLam ρ := by
    rw [AdversarialBco.Poly.pgLam]
    refine Real.sqrt_pos.mpr ?_
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    nlinarith
  have hd_pos : 0 < (d : ℝ) := by
    have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpos : 0 < pgTmin d ρ := by
    rw [AdversarialBco.Poly.pgTmin]
    refine div_pos (by norm_num) ?_
    nlinarith
  set M := pgMat x
  set T := pgOp x
  have hT_eq : T = Matrix.toEuclideanCLM (𝕜 := ℝ) M := rfl
  have h_det_ne_zero : M.det ≠ 0 := by
    by_contra hzero
    have h_exists := (Matrix.exists_mulVec_eq_zero_iff (M := M)).mpr hzero
    rcases h_exists with ⟨v, hv_ne, hv_eq⟩
    apply hv_ne
    have hv_zero : T (WithLp.toLp 2 v) = 0 := by
      rw [hT_eq]
      apply (WithLp.ofLp_eq_zero 2).mp
      rw [Matrix.ofLp_toEuclideanCLM]
      simpa using hv_eq
    have h_inner : ⟪T (WithLp.toLp 2 v), WithLp.toLp 2 v⟫ = 0 := by
      rw [hv_zero, inner_zero_left]
    have h_bound_v := h_bound (WithLp.toLp 2 v)
    rcases h_bound_v with ⟨h_low, _⟩
    rw [h_inner] at h_low
    have h_norm_sq_nonneg : 0 ≤ ‖WithLp.toLp 2 v‖ ^ 2 := by positivity
    have h_norm_sq_zero : ‖WithLp.toLp 2 v‖ ^ 2 = 0 := by
      nlinarith
    have h_norm_zero : ‖WithLp.toLp 2 v‖ = 0 := by
      nlinarith
    have h_zero : WithLp.toLp 2 v = 0 := by
      rwa [norm_eq_zero] at h_norm_zero
    simpa using (WithLp.toLp_eq_zero 2).mp h_zero
  have h_unit : IsUnit (M.det) := isUnit_iff_ne_zero.mpr h_det_ne_zero
  have h_mul_inv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h_unit
  have h_inv_mul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h_unit
  have h_comp1 : (Matrix.toEuclideanCLM (𝕜 := ℝ) M) * (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) = 1 := by
    calc
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M) * (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹)
          = Matrix.toEuclideanCLM (𝕜 := ℝ) (M * M⁻¹) := by
        rw [← map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ))]
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) 1 := by rw [h_mul_inv]
      _ = 1 := map_one _
  have h_comp2 : (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) * (Matrix.toEuclideanCLM (𝕜 := ℝ) M) = 1 := by
    calc
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) * (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
          = Matrix.toEuclideanCLM (𝕜 := ℝ) (M⁻¹ * M) := by
        rw [← map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ))]
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) 1 := by rw [h_inv_mul]
      _ = 1 := map_one _
  have h_inv_pair : IsInvPair T (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) := by
    rw [hT_eq]
    exact ⟨h_comp1, h_comp2⟩
  have h_norm_bound : ∀ v, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ v‖ ≤ ‖v‖ / pgTmin d ρ := by
    intro v
    set w := (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) v
    have hTw : T w = v := by
      rw [hT_eq]
      rw [← mul_apply_eq_comp (Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) v]
      rw [h_comp1]
      rw [one_apply_eq_self]
    rcases h_bound w with ⟨h_low, _⟩
    have h_inner_eq : ⟪T w, w⟫ = ⟪v, w⟫ := by rw [hTw]
    rw [h_inner_eq] at h_low
    have h_cauchy : ⟪v, w⟫ ≤ ‖v‖ * ‖w‖ := real_inner_le_norm v w
    have h_ineq : pgTmin d ρ * ‖w‖ ^ 2 ≤ ‖v‖ * ‖w‖ := by
      linarith
    by_cases hw_zero : ‖w‖ = 0
    · rw [hw_zero]
      have : 0 ≤ ‖v‖ / pgTmin d ρ := div_nonneg (norm_nonneg _) (by linarith)
      simpa
    · have h_norm_pos : 0 < ‖w‖ := by
        apply lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw_zero)
      have h_div_ineq : ‖w‖ ≤ ‖v‖ / pgTmin d ρ := by
        -- from pgTmin d ρ * ‖w‖² ≤ ‖v‖ * ‖w‖
        -- divide both sides by ‖w‖ (positive):
        -- pgTmin d ρ * ‖w‖ ≤ ‖v‖
        -- so ‖w‖ ≤ ‖v‖ / pgTmin d ρ
        have h_mul_ineq : pgTmin d ρ * ‖w‖ ≤ ‖v‖ := by
          nlinarith
        rw [le_div_iff₀ hpos]
        nlinarith
      exact h_div_ineq
  exact ⟨h_det_ne_zero, h_inv_pair, h_norm_bound⟩

/-! ## Leaves: the objective and its minimiser -/

theorem pgBody_isPosBody {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (hρ : 1 ≤ ρ) (hK : PgBody K ρ) :
    IsPosBody K 1 ρ := by
  rcases hK with ⟨hconv, hclosed, hball_sub, hK_sub⟩
  have hρpos : 0 < ρ := by linarith
  have hρnonneg : 0 ≤ ρ := by linarith
  have hρinv_nonneg : 0 ≤ ρ⁻¹ := by positivity
  have hK_bounded : Bornology.IsBounded K :=
    Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0) (r := ρ)) hK_sub
  refine ⟨hconv, Metric.isCompact_of_isClosed_isBounded hclosed hK_bounded, by norm_num,
    Metric.ball_subset_closedBall.trans hball_sub, hρnonneg, ?_⟩
  intro y hy
  -- hy : y ∈ -K, so -y ∈ K
  have hy' : -y ∈ K := by simpa using hy
  have hy_norm : ‖-y‖ ≤ ρ := by
    have : -y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ := hK_sub hy'
    rw [mem_closedBall_iff_norm] at this
    simpa using this
  -- Take z = ρ⁻¹ • y. Then ρ • z = y and z ∈ K.
  have hz_mem_closedBall : ρ⁻¹ • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_closedBall_iff_norm]
    -- goal: ‖(ρ⁻¹ • y) - 0‖ ≤ 1, i.e., ‖ρ⁻¹ • y‖ ≤ 1
    simpa [sub_zero] using
      calc
        ‖ρ⁻¹ • y‖ = ρ⁻¹ * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρinv_nonneg]
        _ = ρ⁻¹ * ‖-y‖ := by rw [← norm_neg y]
        _ ≤ ρ⁻¹ * ρ := by nlinarith
        _ = 1 := by field_simp [hρpos.ne.symm]
  have hz_mem : ρ⁻¹ • y ∈ K := hball_sub hz_mem_closedBall
  refine ⟨ρ⁻¹ • y, hz_mem, ?_⟩
  calc
    ρ • (ρ⁻¹ • y) = (ρ * ρ⁻¹) • y := by simp [mul_smul]
    _ = 1 • y := by simp [hρpos.ne.symm]
    _ = y := by simp

theorem pgOp_det {d : ℕ} (x : PgSp d) :
    LinearMap.det (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (pgMat x).det := by
  have h1 : (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      Matrix.toEuclideanLin (pgMat x) := by
    simpa [pgOp] using (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (pgMat x))
  rw [h1]
  have h2 : Matrix.toEuclideanLin (pgMat x) =
      Matrix.toLin ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) (pgMat x) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [h2]
  rw [LinearMap.det_toLin]

theorem pgH_continuousOn (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : PgBody K ρ) : ContinuousOn (pgH K) (pgDom d ρ) := by
  obtain ⟨hKc, -, h1, -⟩ := hK
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ≥0) ⊆ K := by
    simpa using Metric.ball_subset_closedBall.trans h1
  have hgL : LipschitzWith 1 (gauge K) := by
    simpa using hKc.lipschitzWith_gauge (r := 1) one_pos hball
  have hτ0 : 0 ≤ pgTmin d ρ := by unfold pgTmin pgLam; positivity
  have hcont := pg_continuous d
  have hK1 : ContinuousOn (fun x : PgSp d => posK K (pgMu x) (pgOp x)) (pgDom d ρ) := by
    unfold posK
    refine continuousOn_of_dominated (bound := fun g => pgKappa * ρ + pgLD ρ * ‖g‖) ?_ ?_ ?_ ?_
    · intro x hx
      exact (d4_main d K _ _ _ (pgMu x) (pgOp x) hKc h1 hτ0 hx).1.continuous.aestronglyMeasurable
    · intro x hx
      refine Filter.Eventually.of_forall fun g => ?_
      obtain ⟨-, hb, -⟩ := d4_main d K _ _ _ (pgMu x) (pgOp x) hKc h1 hτ0 hx
      have hmu : ‖pgMu x‖ ≤ pgKappa * ρ := hx.2.1
      rw [Real.norm_of_nonneg (hb g).1]
      linarith [(hb g).2]
    · exact (integrable_const _).add (IsGaussian.integrable_id.norm.const_mul _)
    · refine Filter.Eventually.of_forall fun g => Continuous.continuousOn ?_
      unfold posF
      exact hgL.continuous.comp (hcont.2.2.comp (continuous_id.prodMk continuous_const))
  have hK2 : ContinuousOn (fun x : PgSp d =>
      Real.log |LinearMap.det (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|) (pgDom d ρ) := by
    simp_rw [pgOp_det]
    refine ContinuousOn.log (hcont.2.1.matrix_det.abs.continuousOn) fun x hx => ?_
    exact abs_ne_zero.2 (pgDom_inv d ρ hd hρ x hx).1
  unfold pgH posObj
  exact hK1.sub (continuousOn_const.mul hK2)

theorem posQ_eq_sum {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (h1 : Metric.closedBall 0 1 ⊆ K) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (v w : EuclideanSpace ℝ (Fin d)) :
    posQ K μ T v w =
      ∑ i, ∑ j, v i * w j * posQ K μ T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ≥0) ⊆ K := by
    simpa using Metric.ball_subset_closedBall.trans h1
  have hgL : LipschitzWith 1 (gauge K) := by
    simpa using hK.lipschitzWith_gauge (r := 1) one_pos hball
  have hAff : LipschitzWith ‖T‖₊ (fun y : EuclideanSpace ℝ (Fin d) => μ + T y) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub, coe_nnnorm]
      exact T.le_opNorm _
  have hFL : LipschitzWith (1 * ‖T‖₊) (posF K μ T) := hgL.comp hAff
  have e1 : ∀ (i : Fin d) (g : EuclideanSpace ℝ (Fin d)), ⟪EuclideanSpace.single i (1 : ℝ), g⟫ = g i := by
    intro i g; simp [EuclideanSpace.inner_single_left]
  have e2 : ∀ i j : Fin d, ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ =
      if i = j then 1 else 0 := by
    intro i j; rw [e1]; simp [EuclideanSpace.single_apply]
  have ev : ∀ a b : EuclideanSpace ℝ (Fin d), ⟪a, b⟫ = ∑ i, a i * b i := by
    intro a b; simp [PiLp.inner_apply, mul_comm]
  have hint : ∀ i j : Fin d, Integrable (fun g => (⟪EuclideanSpace.single i (1 : ℝ), g⟫ *
      ⟪EuclideanSpace.single j (1 : ℝ), g⟫ - ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫) *
      posF K μ T g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun i j => (integrable_moments _ _ hFL _ _).2.1
  have hpt : ∀ g, (⟪v, g⟫ * ⟪w, g⟫ - ⟪v, w⟫) * posF K μ T g =
      ∑ i, ∑ j, v i * w j * ((⟪EuclideanSpace.single i (1 : ℝ), g⟫ * ⟪EuclideanSpace.single j (1 : ℝ), g⟫ -
        ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫) * posF K μ T g) := by
    intro g
    simp only [e2]
    simp only [e1]
    simp only [ev]
    have h3 : ∀ i j : Fin d, v i * w j * ((g i * g j - if i = j then 1 else 0) * posF K μ T g) =
        (v i * g i) * (w j * g j) * posF K μ T g - (if i = j then v i * w j * posF K μ T g else 0) := by
      intro i j; split_ifs <;> ring
    simp only [h3, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [sub_mul, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
    simp only [Finset.sum_mul]
  unfold posQ
  simp_rw [hpt]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

theorem gam_alg {d : ℕ} (N Q S : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hN : Nᵀ = N) (hQ : Qᵀ = Q) (hS : Sᵀ = S) :
    ∑ i, ∑ j, ((1 / 2 : ℝ) • (N * Q + (N * Q)ᵀ) - c • N) i j * S i j =
      (Q * (N * S)).trace - c * (N * S).trace := by
  have hF : ∀ A B : Matrix (Fin d) (Fin d) ℝ, ∑ i, ∑ j, A i j * B i j = (A * Bᵀ).trace := by
    intro A B; simp [Matrix.trace, Matrix.mul_apply]
  have e1 : ∑ i, ∑ j, ((1 / 2 : ℝ) • (N * Q + (N * Q)ᵀ) - c • N) i j * S i j =
      (1 / 2) * ((N * Q * Sᵀ).trace + ((N * Q)ᵀ * Sᵀ).trace) - c * (N * Sᵀ).trace := by
    rw [← hF, ← hF, ← hF]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    simp only [sub_mul, add_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [e1, hS]
  have e2 : ((N * Q)ᵀ * S).trace = (N * Q * S).trace := by
    rw [Matrix.transpose_mul, hN, hQ, ← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hS, hN,
      hQ, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Q * (N * S)).trace = (N * Q * S).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hS, hN, hQ]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [e2, e3]; ring

theorem toEuclideanCLM_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.trace ℝ _ (Matrix.toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      A.trace := by
  have h1 : (Matrix.toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      Matrix.toEuclideanLin A := by
    simpa using (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A)
  rw [h1, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis, LinearMap.toMatrix_toLin]

theorem pgGam_subgrad (hD5 : D5Subgrad) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    ∀ x ∈ pgDom d ρ, ∀ y ∈ pgDom d ρ, pgH K x + ⟪pgGam K x, y - x⟫ ≤ pgH K y := by
  intro x hx y hy
  have hx' : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
  have hy' : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu y) (pgOp y) := hy
  have hlam : 0 < pgLam ρ := by
    unfold pgLam
    have := Real.log_pos (by linarith : (1 : ℝ) < 1 + ρ)
    exact Real.sqrt_pos.2 (by linarith)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have htmin : 0 < pgTmin d ρ := by unfold pgTmin; positivity
  have hpos : ∀ z : PgSp d, IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu z) (pgOp z) →
      ∀ v, v ≠ 0 → 0 < ⟪pgOp z v, v⟫ := by
    intro z hz v hv
    have h1 := (hz.2.2 v).1
    have h2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv; positivity
    nlinarith
  have hsym : ∀ z : PgSp d, IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu z) (pgOp z) →
      (pgMat z)ᵀ = pgMat z := by
    intro z hz
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) (star (pgMat z)) = Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat z) := by
      rw [map_star]; exact hz.1
    have h2 := Matrix.toEuclideanCLM.injective h1
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  obtain ⟨-, hinv, -⟩ := pgDom_inv d ρ hd hρ x hx
  have hD := hD5 d K 1 ρ pgKappa (pgMu x) (pgMu y) (pgOp x) (pgOp y)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹) (pgBody_isPosBody K ρ hρ hK) hx'.1 hy'.1 (hpos x hx')
    (hpos y hy') hinv (by unfold pgKappa; norm_num)
  set N := (pgMat x)⁻¹ with hNdef
  set S := pgMat y - pgMat x with hSdef
  have hN : Nᵀ = N := by rw [hNdef, Matrix.transpose_nonsing_inv, hsym x hx']
  have hS : Sᵀ = S := by rw [hSdef, Matrix.transpose_sub, hsym x hx', hsym y hy']
  have hQ : (pgQs K x)ᵀ = pgQs K x := by
    ext i j
    simp only [Matrix.transpose_apply, pgQs, posQ]
    congr 1; ext g
    rw [mul_comm ⟪EuclideanSpace.single j (1 : ℝ), g⟫, real_inner_comm (EuclideanSpace.single j (1 : ℝ))]
  have hcomp : (Matrix.toEuclideanCLM (𝕜 := ℝ) N).comp (pgOp y - pgOp x) = Matrix.toEuclideanCLM (𝕜 := ℝ) (N * S) := by
    unfold pgOp; rw [hSdef, map_mul, map_sub]; rfl
  have hT3 : LinearMap.trace ℝ _ (((Matrix.toEuclideanCLM (𝕜 := ℝ) N).comp (pgOp y - pgOp x) :
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      (N * S).trace := by
    rw [hcomp, toEuclideanCLM_trace]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) ℝ) (i b : Fin d),
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.single i 1)) b = A b i := by
    intro A i b
    simp [EuclideanSpace.single, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
  have hT2 : ∑ i, posQ K (pgMu x) (pgOp x) (EuclideanSpace.single i 1)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) N ((pgOp y - pgOp x) (EuclideanSpace.single i 1))) =
      (pgQs K x * (N * S)).trace := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw : Matrix.toEuclideanCLM (𝕜 := ℝ) N ((pgOp y - pgOp x) (EuclideanSpace.single i 1)) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (N * S) (EuclideanSpace.single i 1) := by
      rw [← hcomp]; rfl
    rw [hw, posQ_eq_sum K hK.1 hK.2.2.1]
    simp only [hcol, EuclideanSpace.single_apply]
    simp [Matrix.mul_apply, pgQs, ite_mul, Finset.sum_ite_eq', mul_comm]
  have hT1 : ⟪posB K (pgMu x) (pgOp x), Matrix.toEuclideanCLM (𝕜 := ℝ) N (pgMu y - pgMu x)⟫ =
      ⟪(WithLp.toLp 2 (N *ᵥ fun i => pgBs K x i) : EuclideanSpace ℝ (Fin d)), pgMu y - pgMu x⟫ := by
    have hsa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) N) := by
      rw [IsSelfAdjoint, ← map_star, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, hN]
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) (posB K (pgMu x) (pgOp x)) (pgMu y - pgMu x)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h]
    rfl
  have hmu : pgMu (y - x) = pgMu y - pgMu x := by ext i; simp [pgMu]
  have hmat : pgMat (y - x) = S := by ext i j; simp [pgMat, hSdef]
  have hG := gam_alg N (pgQs K x) S (pgKappa / d) hN hQ hS
  have key : pgH K x + ⟪pgGam K x, y - x⟫ =
      posObj K pgKappa (pgMu x) (pgOp x) + ⟪posB K (pgMu x) (pgOp x),
        Matrix.toEuclideanCLM (𝕜 := ℝ) N (pgMu y - pgMu x)⟫ +
        ∑ i, posQ K (pgMu x) (pgOp x) (EuclideanSpace.single i 1)
          (Matrix.toEuclideanCLM (𝕜 := ℝ) N ((pgOp y - pgOp x) (EuclideanSpace.single i 1))) -
        pgKappa / d * LinearMap.trace ℝ _ (((Matrix.toEuclideanCLM (𝕜 := ℝ) N).comp (pgOp y - pgOp x) :
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [hT1, hT2, hT3, pgSp_inner, hmu, hmat]
    unfold pgGam pgH
    rw [pgMu_pgPack, pgMat_pgPack, hG]
    ring
  rw [key]
  unfold pgH
  exact hD

theorem form_lower_of_inv {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : IsSelfAdjoint T) (hpos : ∀ v, v ≠ 0 → 0 < ⟪T v, v⟫) (R : ℝ) (hR : 0 < R)
    (hinv : ∀ u y : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → T y = u → ‖y‖ ≤ R) :
    ∀ v, ‖v‖ ^ 2 / R ≤ ⟪T v, v⟫ := by
  intro v
  by_cases hd : d = 0
  · subst hd
    have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := by
      infer_instance
    have hv : v = 0 := Subsingleton.elim v 0
    rw [hv]
    simp
  · have hT_symm : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).IsSymmetric :=
      hT.isSymmetric
    have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (n := d)
    let b := hT_symm.eigenvectorBasis h_finrank
    have h_apply : ∀ i, T (b i) = (hT_symm.eigenvalues h_finrank i) • (b i) :=
      hT_symm.apply_eigenvectorBasis h_finrank
    have h_eigen_pos : ∀ i, 0 < hT_symm.eigenvalues h_finrank i := by
      intro i
      have h_ne_zero : b i ≠ 0 := by
        have h_norm : ‖b i‖ = 1 := OrthonormalBasis.norm_eq_one b i
        intro h_eq
        rw [h_eq, norm_zero] at h_norm
        linarith
      have h_inner_pos : 0 < ⟪T (b i), b i⟫ := hpos (b i) h_ne_zero
      rw [h_apply i] at h_inner_pos
      have h_inner_self : ⟪b i, b i⟫ = 1 := OrthonormalBasis.inner_eq_one b i
      rw [real_inner_smul_left] at h_inner_pos
      -- h_inner_pos : 0 < (hT_symm.eigenvalues h_finrank i) * ⟪b i, b i⟫
      rw [h_inner_self] at h_inner_pos
      -- h_inner_pos : 0 < hT_symm.eigenvalues h_finrank i * 1
      simpa using h_inner_pos
    have h_eigen_ge_invR : ∀ i, (1 : ℝ) / R ≤ hT_symm.eigenvalues h_finrank i := by
      intro i
      let eig_i := hT_symm.eigenvalues h_finrank i
      have h_eig_pos : 0 < eig_i := h_eigen_pos i
      let u := b i
      have hu_norm : ‖u‖ = 1 := OrthonormalBasis.norm_eq_one b i
      have hu_norm_le : ‖u‖ ≤ 1 := by rw [hu_norm]
      let y := (eig_i⁻¹) • u
      have hTy : T y = u := by
        calc
          T y = T ((eig_i⁻¹) • u) := rfl
          _ = (eig_i⁻¹) • T u := by
            simpa using (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).map_smul u (eig_i⁻¹)
          _ = (eig_i⁻¹) • (eig_i • u) := by rw [h_apply i]
          _ = ((eig_i⁻¹) * eig_i) • u := by simp [mul_smul]
          _ = (1 : ℝ) • u := by simp [h_eig_pos.ne.symm]
          _ = u := by simp
      have h_inv_bound : ‖y‖ ≤ R := hinv u y hu_norm_le hTy
      have h_norm_y : ‖y‖ = |eig_i⁻¹| := by
        rw [norm_smul, hu_norm, mul_one]
        simp [Real.norm_eq_abs]
      have h_abs_inv_le : |eig_i⁻¹| ≤ R := by
        rwa [h_norm_y] at h_inv_bound
      have h_inv_nonneg : 0 ≤ eig_i⁻¹ :=
        inv_nonneg.mpr (by linarith)
      rw [abs_of_nonneg h_inv_nonneg] at h_abs_inv_le
      rw [div_le_iff₀' hR]
      calc
        1 = eig_i * eig_i⁻¹ := by field_simp [h_eig_pos.ne.symm]
        _ ≤ eig_i * R := mul_le_mul_of_nonneg_left h_abs_inv_le (by linarith)
        _ = R * eig_i := mul_comm _ _
    calc
      ‖v‖ ^ 2 / R = (∑ i : Fin d, ⟪b i, v⟫ ^ 2) / R := by
        rw [OrthonormalBasis.sum_sq_inner_right b v]
      _ = ∑ i : Fin d, (⟪b i, v⟫ ^ 2) / R := by
        rw [Finset.sum_div]
      _ ≤ ∑ i : Fin d, (⟪b i, v⟫ ^ 2) * (hT_symm.eigenvalues h_finrank i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h_eigen_ge : (1 : ℝ) / R ≤ hT_symm.eigenvalues h_finrank i := h_eigen_ge_invR i
        have h_sq_nonneg : 0 ≤ ⟪b i, v⟫ ^ 2 := by positivity
        have h_mul : (⟪b i, v⟫ ^ 2) * ((1 : ℝ) / R) ≤ (⟪b i, v⟫ ^ 2) * (hT_symm.eigenvalues h_finrank i) :=
          mul_le_mul_of_nonneg_left h_eigen_ge h_sq_nonneg
        -- (⟪b i, v⟫ ^ 2) * ((1 : ℝ) / R) = (⟪b i, v⟫ ^ 2) / R
        simpa [div_eq_mul_inv] using h_mul
      _ = ∑ i : Fin d, (hT_symm.eigenvalues h_finrank i) * (⟪b i, v⟫ ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      _ = ∑ i : Fin d, (hT_symm.eigenvalues h_finrank i) * ⟪b i, v⟫ * ⟪b i, v⟫ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      _ = ∑ i : Fin d, ⟪T v, b i⟫ * ⟪b i, v⟫ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        calc
          (hT_symm.eigenvalues h_finrank i) * ⟪b i, v⟫ * ⟪b i, v⟫
              = ⟪v, (hT_symm.eigenvalues h_finrank i) • (b i)⟫ * ⟪b i, v⟫ := by
            simp [real_inner_smul_right, real_inner_comm (b i) v]
          _ = ⟪v, T (b i)⟫ * ⟪b i, v⟫ := by rw [h_apply i]
          _ = ⟪T v, b i⟫ * ⟪b i, v⟫ := by
            simpa using congrArg (· * ⟪b i, v⟫) (hT_symm v (b i)).symm
      _ = ⟪T v, v⟫ := by
        rw [OrthonormalBasis.sum_inner_mul_inner b (T v) v]

theorem form_upper_of_norm {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hc : ∀ u, ‖u‖ = 1 → ‖T u‖ ≤ c) : ∀ v, ⟪T v, v⟫ ≤ c * ‖v‖ ^ 2 := by
  intro v
  by_cases hv : v = 0
  · subst hv; simp
  · have hpos : 0 < ‖v‖ := (norm_pos_iff.mpr hv)
    set u := (‖v‖⁻¹ : ℝ) • v with hu
    have hu_norm : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs]
      have h_inv_nonneg : 0 ≤ (‖v‖⁻¹ : ℝ) := by positivity
      rw [abs_of_nonneg h_inv_nonneg]
      field_simp [hpos.ne']
    have hv_eq : (‖v‖ : ℝ) • u = v := by
      rw [hu]
      simp [smul_smul, hpos.ne']
    calc
      ⟪T v, v⟫ = ⟪T ((‖v‖ : ℝ) • u), (‖v‖ : ℝ) • u⟫ := by rw [hv_eq]
      _ = ⟪(‖v‖ : ℝ) • T u, (‖v‖ : ℝ) • u⟫ := by rw [T.map_smul]
      _ = (‖v‖ : ℝ) * (‖v‖ : ℝ) * ⟪T u, u⟫ := by
        simp [inner_smul_left, inner_smul_right, mul_assoc]
      _ = ‖v‖ ^ 2 * ⟪T u, u⟫ := by ring
      _ ≤ ‖v‖ ^ 2 * (‖T u‖ * ‖u‖) := by
        nlinarith [real_inner_le_norm (T u) u]
      _ = ‖v‖ ^ 2 * ‖T u‖ := by rw [hu_norm, mul_one]
      _ ≤ ‖v‖ ^ 2 * c := by nlinarith [hc u hu_norm]
      _ = c * ‖v‖ ^ 2 := by ring

theorem one_le_pgPB_mul_sqrt : 1 ≤ pgPB * Real.sqrt (2 / Real.pi) := by
  have hpos_pi : 0 < Real.pi := Real.pi_pos
  have hpos_ratio : 0 ≤ (1000 : ℝ) / 1254 := by norm_num
  have hpos_two_div_pi : 0 ≤ 2 / Real.pi := by positivity
  have hsq : ((1000 : ℝ) / 1254) ^ 2 ≤ 2 / Real.pi := by
    have h_target : Real.pi ≤ 2 * ((1254 : ℝ) / 1000) ^ 2 := by
      have hcalc : (2 : ℝ) * ((1254 : ℝ) / 1000) ^ 2 = (3.145032 : ℝ) := by norm_num
      rw [hcalc]
      linarith [Real.pi_lt_d4]
    have h_sq_pos : 0 ≤ ((1000 : ℝ) / 1254) ^ 2 := by positivity
    have h_mul : ((1000 : ℝ) / 1254) ^ 2 * Real.pi ≤ 2 := by
      calc
        ((1000 : ℝ) / 1254) ^ 2 * Real.pi ≤ ((1000 : ℝ) / 1254) ^ 2 * (2 * ((1254 : ℝ) / 1000) ^ 2) :=
          mul_le_mul_of_nonneg_left h_target h_sq_pos
        _ = 2 := by norm_num
    exact (le_div_iff₀ hpos_pi).mpr h_mul
  have hle : (1000 : ℝ) / 1254 ≤ Real.sqrt (2 / Real.pi) :=
    ((Real.le_sqrt hpos_ratio hpos_two_div_pi).mpr hsq)
  calc
    1 = ((1000 : ℝ) / 1254) * ((1254 : ℝ) / 1000) := by norm_num
    _ ≤ Real.sqrt (2 / Real.pi) * ((1254 : ℝ) / 1000) := by
      nlinarith
    _ = pgPB * Real.sqrt (2 / Real.pi) := by unfold pgPB; ring

theorem pgMin_exists (hL : LemmaLSym) (hD1 : D1Bounds) (hD1i : D1Inv) (hR : LemmaLRadii) (hG : GaussConst)
    (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    ∃ xs ∈ pgDom d ρ, ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      pgH K xs ≤ posObj K pgKappa μ' A' := by
  have hposKappa : 0 < pgKappa := by
    unfold pgKappa
    norm_num
  have hposρ : 0 < ρ := by linarith
  have hKappa_lt_one : pgKappa < 1 := by
    unfold pgKappa
    norm_num
  have hIsPosBody : IsPosBody K 1 ρ :=
    pgBody_isPosBody K ρ hρ hK
  rcases hL d hd K 1 ρ pgKappa hIsPosBody hposKappa with
    ⟨μstar, Tstar, hTsa, hTpos, hTmin, hTposK, hTposB, hTposQ⟩
  have hTdet_ne_zero : LinearMap.det (Tstar : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    intro hzero
    have hker_ne_bot : LinearMap.ker (Tstar : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ ⊥ := by
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot] at hzero
    have h_exists : ∃ x ∈ LinearMap.ker (Tstar : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)), x ≠ 0 := by
      apply Submodule.exists_mem_ne_zero_of_ne_bot hker_ne_bot
    rcases h_exists with ⟨x, hx, hx_ne⟩
    have hTxzero : Tstar x = 0 := LinearMap.mem_ker.mp hx
    have hzero_inner : ⟪Tstar x, x⟫ = 0 := by rw [hTxzero, inner_zero_left]
    have hpos_inner := hTpos x hx_ne
    linarith
  have hTadjoint_eq : ContinuousLinearMap.adjoint Tstar = Tstar := by
    have := hTsa
    rw [IsSelfAdjoint] at this
    exact this
  have hK_closedBall : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K :=
    hK.2.2.1
  have hposLam : 0 < pgLam ρ := by
    unfold pgLam
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hRpos : 0 < 9 * (d : ℝ) * pgLam ρ := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
    positivity
  rcases hG ρ hρ with ⟨t, ht_nonneg, ht_le, ht_bath⟩
  have h_bound_posBody : ∀ y ∈ posBody K μstar Tstar, ‖y‖ ≤ 9 * (d : ℝ) * pgLam ρ := by
    intro y hy
    have hRfull := hR d hd K 1 ρ pgKappa μstar Tstar hIsPosBody hTdet_ne_zero hposKappa hKappa_lt_one
      hTposK hTposB hTposQ
    rcases hRfull with ⟨hforall, _, _⟩
    have hle := hforall t y hy
    calc
      ‖y‖ ≤ (d : ℝ) * (1 + pgKappa) * bathC ρ t / pgKappa := hle
      _ ≤ (d : ℝ) * (1 + pgKappa) * pgLam ρ / pgKappa :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht_bath (by positivity)) (by positivity)
      _ = 9 * (d : ℝ) * pgLam ρ := by
        unfold pgKappa
        ring
  have h_lower_inv : ∀ u y : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → Tstar y = u → ‖y‖ ≤ 9 * (d : ℝ) * pgLam ρ := by
    intro u y hu_norm hy_eq
    apply hD1i d K μstar Tstar (9 * (d : ℝ) * pgLam ρ) hTdet_ne_zero hK_closedBall h_bound_posBody u y hu_norm hy_eq
  have h_lower_form : ∀ v, ‖v‖ ^ 2 / (9 * (d : ℝ) * pgLam ρ) ≤ ⟪Tstar v, v⟫ := by
    intro v
    exact form_lower_of_inv Tstar hTsa hTpos (9 * (d : ℝ) * pgLam ρ) hRpos h_lower_inv v
  have h_upper_norm : ∀ u, ‖u‖ = 1 → ‖Tstar u‖ ≤ pgLD ρ := by
    intro u hu_norm
    have hbound := hD1 d K ρ μstar Tstar hposρ hK.1 hK_closedBall hK.2.2.2
    rcases hbound with ⟨hle, hbound_upper⟩
    have hbound' := hbound_upper u hu_norm
    rw [hTadjoint_eq, hTposK] at hbound'
    have h_sqrt_pos : 0 < Real.sqrt (2 / Real.pi) :=
      Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)
    have h_one_le_pgPB_sqrt : 1 ≤ pgPB * Real.sqrt (2 / Real.pi) := one_le_pgPB_mul_sqrt
    have h_norm_bound : ‖Tstar u‖ ≤ ρ * pgKappa / Real.sqrt (2 / Real.pi) := by
      calc
        ‖Tstar u‖ = (‖Tstar u‖ * Real.sqrt (2 / Real.pi)) / Real.sqrt (2 / Real.pi) := by
          field_simp [h_sqrt_pos.ne']
        _ ≤ (ρ * pgKappa) / Real.sqrt (2 / Real.pi) :=
          (div_le_div_of_nonneg_right hbound' (by positivity))
    have h_final : ρ * pgKappa / Real.sqrt (2 / Real.pi) ≤ pgLD ρ := by
      have h_div : 1 / Real.sqrt (2 / Real.pi) ≤ pgPB := by
        calc
          1 / Real.sqrt (2 / Real.pi) ≤ (pgPB * Real.sqrt (2 / Real.pi)) / Real.sqrt (2 / Real.pi) :=
            div_le_div_of_nonneg_right h_one_le_pgPB_sqrt (by positivity)
          _ = pgPB := by field_simp [h_sqrt_pos.ne']
      calc
        ρ * pgKappa / Real.sqrt (2 / Real.pi) = ρ * pgKappa * (1 / Real.sqrt (2 / Real.pi)) := by ring
        _ ≤ ρ * pgKappa * pgPB := mul_le_mul_of_nonneg_left h_div (by positivity)
        _ = pgLD ρ := by
          unfold pgLD
          ring
    linarith
  have h_upper_form : ∀ v, ⟪Tstar v, v⟫ ≤ pgLD ρ * ‖v‖ ^ 2 :=
    form_upper_of_norm Tstar (pgLD ρ) h_upper_norm
  have h_mu_bound : ‖μstar‖ ≤ pgKappa * ρ := by
    have hbound := hD1 d K ρ μstar Tstar hposρ hK.1 hK_closedBall hK.2.2.2
    rcases hbound with ⟨hle, _⟩
    rw [hTposK] at hle
    linarith
  set M := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm Tstar with hM_def
  set xs := pgPack μstar M with hxs_def
  have hxs_pgMu : pgMu xs = μstar := pgMu_pgPack μstar M
  have hxs_pgMat : pgMat xs = M := pgMat_pgPack μstar M
  have hxs_pgOp : pgOp xs = Tstar := by
    calc
      pgOp xs = Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat xs) := rfl
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) M := by rw [hxs_pgMat]
      _ = Matrix.toEuclideanCLM (𝕜 := ℝ) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm Tstar) := rfl
      _ = Tstar := StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (𝕜 := ℝ)) Tstar
  have hxs_dom : xs ∈ pgDom d ρ := by
    rw [pgDom, Set.mem_setOf_eq, hxs_pgMu, hxs_pgOp]
    refine ⟨?_, ?_, ?_⟩
    · exact hTsa
    · exact h_mu_bound
    · intro v
      have h_lower : pgTmin d ρ * ‖v‖ ^ 2 ≤ ⟪Tstar v, v⟫ := by
        have := h_lower_form v
        unfold pgTmin
        calc
          (1 / (9 * (d : ℝ) * pgLam ρ)) * ‖v‖ ^ 2 = ‖v‖ ^ 2 / (9 * (d : ℝ) * pgLam ρ) := by ring
          _ ≤ ⟪Tstar v, v⟫ := this
      have h_upper : ⟪Tstar v, v⟫ ≤ pgLD ρ * ‖v‖ ^ 2 := h_upper_form v
      exact ⟨h_lower, h_upper⟩
  refine ⟨xs, hxs_dom, ?_⟩
  intro μ' A' hA'det
  unfold pgH
  rw [hxs_pgMu, hxs_pgOp]
  exact hTmin μ' A' hA'det

/-! ## Leaves: Lemma E -/

theorem pgFt_bounds (hLB : LemmaB) (hD4 : D4Bounds) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (g : EuclideanSpace ℝ (Fin d)) :
    posF K (pgMu x) (pgOp x) g ≤ pgFt K ρ x g ∧ pgFt K ρ x g ≤ (1 + pgEta d ρ) * posF K (pgMu x) (pgOp x) g ∧
      0 ≤ posF K (pgMu x) (pgOp x) g ∧ posF K (pgMu x) (pgOp x) g ≤ pgLD ρ * (1 + ‖g‖) := by
  rcases hK with ⟨hK_conv, hK_closed, hK_ball1, hK_ballρ⟩
  have hx_dom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := by
    simpa [pgDom] using hx
  set η := pgEta d ρ with hη
  set j := pgJb d ρ with hj
  set z := pgMu x + pgOp x g with hz
  have hposF : posF K (pgMu x) (pgOp x) g = gauge K z := by
    dsimp [posF, z]
  have hpgFt : pgFt K ρ x g = piTilde K ρ j z := by
    dsimp [pgFt, j, z]
  have h_eta_pos : 0 < η := by
    dsimp [η, pgEta, pgEh, pgTmin, pgLD, pgDelta, pgLam, pgKappa, pgPB]
    have hρ' : 0 < ρ := by linarith
    have hdpos_nat : 0 < d := by omega
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    have hsqrt_log : 0 < Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_pos.mpr (by nlinarith)
    have h_num : 0 < ((1/8)^2 / (922 * (d:ℝ)^2 * (Real.sqrt (2 * Real.log (1 + ρ)))^2 * ((1/8) * (1254/1000) * ρ))) *
        (1 / (9 * (d:ℝ) * Real.sqrt (2 * Real.log (1 + ρ)))) := by
      refine mul_pos ?_ ?_
      · refine div_pos ?_ ?_
        · positivity
        · have h1 : 0 < (922 : ℝ) := by norm_num
          have h2 : 0 < (d : ℝ) ^ 2 := by positivity
          have h3 : 0 < (Real.sqrt (2 * Real.log (1 + ρ))) ^ 2 := by positivity
          have h4 : 0 < (1/8 : ℝ) * (1254/1000 : ℝ) * ρ := by positivity
          positivity
      · refine div_pos (by norm_num) ?_
        positivity
    have h_denom : 0 < 7 * ((1/8) * (1254/1000) * ρ) * (1 + Real.sqrt (d:ℝ)) *
        ((1/8) * ρ * Real.sqrt (4 + (1254/1000)^2 * (d:ℝ))) := by
      have h1 : 0 < (1/8 : ℝ) * (1254/1000 : ℝ) * ρ := by positivity
      have h2 : 0 < 1 + Real.sqrt (d : ℝ) := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
        nlinarith
      have h3 : 0 < (1/8 : ℝ) * ρ * Real.sqrt (4 + (1254/1000)^2 * (d : ℝ)) := by
        refine mul_pos (mul_pos (by norm_num) hρ') ?_
        refine Real.sqrt_pos.mpr ?_
        nlinarith
      positivity
    exact div_pos h_num h_denom
  have h_rho_div_eta_pos : 0 < ρ / η := div_pos (by linarith) h_eta_pos
  have h_logb_le_j : Real.logb 2 (ρ / η) ≤ (j : ℝ) := by
    dsimp [j, pgJb]
    simpa using Nat.le_ceil (Real.logb 2 (ρ / η))
  have h_two_gt_one : 1 < (2 : ℝ) := by norm_num
  have h_logb_ineq : ρ / η ≤ (2 : ℝ) ^ (j : ℝ) :=
    ((Real.logb_le_iff_le_rpow h_two_gt_one h_rho_div_eta_pos).mp h_logb_le_j)
  have h_eq : (2 : ℝ) ^ (j : ℝ) = ((2 : ℝ) ^ j : ℝ) := by
    simpa using Real.rpow_natCast (2 : ℝ) j
  rw [h_eq] at h_logb_ineq
  have h_two_pow_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
  have h_rho_div_two_pow_j_le_η : ρ / ((2 : ℝ) ^ j) ≤ η := by
    have h_mul : ρ ≤ η * ((2 : ℝ) ^ j) := by
      have := (div_le_iff₀ h_eta_pos).mp h_logb_ineq
      simpa [mul_comm] using this
    exact (div_le_iff₀ h_two_pow_pos).mpr h_mul
  have hLB_ineq := hLB d K ρ hρ hK_conv hK_closed hK_ball1 hK_ballρ j η h_rho_div_two_pow_j_le_η z
  rcases hLB_ineq with ⟨h_le_gauge, h_gauge_add, h_le_one_plus⟩
  have h_nonneg_gauge : 0 ≤ gauge K z := gauge_nonneg _
  have hD4_ineq := hD4 d K (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) hK_conv hK_ball1
    (by
      dsimp [pgTmin, pgLam]
      refine div_nonneg (by norm_num) ?_
      have hlog : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by linarith : 1 ≤ 1 + ρ)
      positivity)
    hx_dom
  rcases hD4_ineq with ⟨_, hD4_nonneg_bound, _⟩
  obtain ⟨h_sa, h_mu_bound, h_op_bound⟩ := hx_dom
  have h_nonneg_posF : 0 ≤ posF K (pgMu x) (pgOp x) g := by
    rw [hposF]
    exact h_nonneg_gauge
  have h_bound_posF : posF K (pgMu x) (pgOp x) g ≤ pgLD ρ * (1 + ‖g‖) := by
    rw [hposF]
    have h_bound := (hD4_nonneg_bound g).2
    have h_mu_norm : ‖pgMu x‖ ≤ pgKappa * ρ := h_mu_bound
    have h_kappa_rho_le_LD : pgKappa * ρ ≤ pgLD ρ := by
      dsimp [pgLD, pgKappa, pgPB]
      nlinarith
    have h_total : ‖pgMu x‖ + pgLD ρ * ‖g‖ ≤ pgLD ρ * (1 + ‖g‖) := by
      nlinarith
    linarith
  rw [hposF, hpgFt]
  exact ⟨h_le_gauge, h_le_one_plus, h_nonneg_posF, h_bound_posF⟩

theorem pgV_norm_sq_le (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (x : PgSp d) (hx : x ∈ pgDom d ρ) (g : EuclideanSpace ℝ (Fin d)) :
    ‖pgV K ρ x g‖ ^ 2 ≤ pgFt K ρ x g ^ 2 * ‖g‖ ^ 2 / pgTmin d ρ ^ 2 +
      2 * pgFt K ρ x g ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / pgTmin d ρ ^ 2 +
      2 * (pgKappa / d) ^ 2 * d / pgTmin d ρ ^ 2 := by
  set f := pgFt K ρ x g with hf
  set T := pgMat x with hT
  set G := pgGG g with hG
  set t := pgTmin d ρ with ht
  have ht_pos : 0 < t := by
    rw [ht, pgTmin]
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
    have hsqrt : 0 < Real.sqrt (2 * Real.log (1 + ρ)) :=
      Real.sqrt_pos.mpr (by nlinarith)
    have hd_pos : (0 : ℝ) < d := by
      have : 0 < (d : ℕ) := by omega
      exact mod_cast this
    positivity
  rcases pgDom_inv d ρ hd hρ x hx with ⟨hdet, hinv, hbound⟩
  have h_norm_sq := pgSp_norm_sq (pgV K ρ x g)
  have h_mu_val : pgMu (pgV K ρ x g) = WithLp.toLp 2 (f • (T⁻¹ *ᵥ g)) := by
    unfold pgV; rw [pgMu_pgPack]
  have h_mat_val : pgMat (pgV K ρ x g) = (f/2) • (T⁻¹ * G + (T⁻¹ * G)ᵀ) - (pgKappa / d) • T⁻¹ := by
    unfold pgV; rw [pgMat_pgPack]
  rw [h_norm_sq, h_mu_val, h_mat_val]
  -- Helper lemma: norm squared of WithLp.toLp 2 v equals sum of squares
  have norm_sq_toLp_two (v : Fin d → ℝ) : ‖WithLp.toLp (p := 2) v‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    simp
    have hsum : 0 ≤ ∑ i : Fin d, v i ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
    rw [Real.sq_sqrt hsum]
  -- Helper lemma: sum of squares of matrix-vector product equals norm squared
  have sum_sq_mulVec_eq_norm_sq (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
      ∑ i, ((M *ᵥ (fun j => v j)) i) ^ 2 = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M v‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    simp
    have hsum : 0 ≤ ∑ i, (M *ᵥ v.ofLp) i ^ 2 :=
      Finset.sum_nonneg (fun i _ => by positivity)
    rw [Real.sq_sqrt hsum]
  -- Inequality: (a - b)^2 ≤ 2*a^2 + 2*b^2
  have sub_sq_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2 := by
      have : (a + b) ^ 2 ≥ 0 := by positivity
      nlinarith
    nlinarith
  -- Inequality: (a + b)^2 ≤ 2*a^2 + 2*b^2
  have add_sq_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  -- Bound on the first term
  have h_first : ‖WithLp.toLp 2 (f • (T⁻¹ *ᵥ g))‖ ^ 2 ≤ f ^ 2 * ‖g‖ ^ 2 / t ^ 2 := by
    rw [norm_sq_toLp_two]
    simp_rw [Pi.smul_apply, smul_eq_mul]
    calc
      ∑ i, (f * (T⁻¹ *ᵥ g) i) ^ 2 = f ^ 2 * ∑ i, ((T⁻¹ *ᵥ g) i) ^ 2 := by
        simp [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc, mul_pow]
      _ = f ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ ^ 2 := by
        rw [sum_sq_mulVec_eq_norm_sq T⁻¹ g]
      _ ≤ f ^ 2 * (‖g‖ / t) ^ 2 := by
        have h_nonneg_f_sq : 0 ≤ f ^ 2 := by positivity
        have h_bound_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ ^ 2 ≤ (‖g‖ / t) ^ 2 := by
          have h_nonneg_norm : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ := by positivity
          have h_nonneg_g : 0 ≤ ‖g‖ := by positivity
          have h_nonneg_t : 0 ≤ t := by positivity
          -- From hbound g: ‖T⁻¹ g‖ ≤ ‖g‖ / t
          -- Multiply by t: ‖T⁻¹ g‖ * t ≤ ‖g‖
          have h_mul : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ * t ≤ ‖g‖ := by
            calc
              ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ * t ≤ (‖g‖ / t) * t :=
                mul_le_mul_of_nonneg_right (hbound g) h_nonneg_t
              _ = ‖g‖ := by field_simp [ht_pos.ne']
          -- Square both sides
          have h_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ ^ 2 * t ^ 2 ≤ ‖g‖ ^ 2 := by
            have h_nonneg_mul : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g‖ * t :=
              mul_nonneg h_nonneg_norm h_nonneg_t
            nlinarith
          -- Now use the equivalence: A ≤ B / t^2 ↔ A * t^2 ≤ B
          rw [div_pow]
          exact (le_div_iff₀ (by positivity : 0 < t ^ 2)).mpr h_sq
        apply mul_le_mul_of_nonneg_left h_bound_sq h_nonneg_f_sq
      _ = f ^ 2 * ‖g‖ ^ 2 / t ^ 2 := by ring
  -- Set A = (f/2) • (T⁻¹ * G + (T⁻¹ * G)ᵀ), B = (pgKappa / d) • T⁻¹
  set A := (f/2) • (T⁻¹ * G + (T⁻¹ * G)ᵀ) with hA
  set B := (pgKappa / d) • T⁻¹ with hB
  have h_second : ∑ i, ∑ j, (A i j - B i j) ^ 2 ≤
      2 * f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2 + 2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
    -- Helper: standard basis vector
    let e (j : Fin d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => if i = j then 1 else 0)
    have h_norm_e (j : Fin d) : ‖e j‖ = 1 := by
      rw [EuclideanSpace.norm_eq]; simp [e]
    -- Helper: sum of squares of column j equals norm squared of matrix-vector product
    have sum_sq_col_eq (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
        ∑ i, (M i j) ^ 2 = ‖WithLp.toLp (p := 2) (M *ᵥ (fun i => if i = j then 1 else 0))‖ ^ 2 := by
      rw [norm_sq_toLp_two]
      congr
      ext i
      simp [Matrix.mulVec, dotProduct]
    -- Helper: bound on ∑ i, ((T⁻¹ * M) i j)^2 using the operator bound
    have h_col_mulVec_bound (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
        ∑ i, ((T⁻¹ * M) i j) ^ 2 ≤ (∑ i, M i j ^ 2) / t ^ 2 := by
      -- Key: (T⁻¹ * M) i j = (T⁻¹ *ᵥ (fun k => M k j)) i
      have h_mulVec_eq : ∀ i, ((T⁻¹ * M) i j) = (T⁻¹ *ᵥ (fun k => M k j)) i := by
        intro i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      have h_sum_eq : ∑ i, ((T⁻¹ * M) i j) ^ 2 = ∑ i, ((T⁻¹ *ᵥ (fun k => M k j)) i) ^ 2 := by
        simp [h_mulVec_eq]
      rw [h_sum_eq]
      -- Now use the operator bound hbound
      -- We need to relate ‖Matrix.toEuclideanCLM T⁻¹ v‖ to ‖T⁻¹ *ᵥ v.ofLp‖
      -- From pgOp_apply, we have: Matrix.toEuclideanCLM T v = WithLp.toLp 2 (T *ᵥ v.ofLp)
      -- So ‖Matrix.toEuclideanCLM T⁻¹ v‖ = ‖WithLp.toLp 2 (T⁻¹ *ᵥ v.ofLp)‖
      -- And ‖WithLp.toLp 2 w‖² = ∑ i, w i ^ 2
      -- So ∑ i, ((T⁻¹ *ᵥ v.ofLp) i) ^ 2 = ‖Matrix.toEuclideanCLM T⁻¹ v‖² ≤ (‖v‖ / t)²
      let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun k => M k j)
      have h_toEuclideanCLM : Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v = WithLp.toLp 2 (T⁻¹ *ᵥ v.ofLp) := by
        -- This follows from pgOp_apply
        calc
          Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v = pgOp (pgPack 0 T⁻¹) v := rfl
          _ = WithLp.toLp 2 ((pgMat (pgPack 0 T⁻¹)) *ᵥ v.ofLp) := by rw [pgOp_apply]
          _ = WithLp.toLp 2 (T⁻¹ *ᵥ v.ofLp) := by rw [pgMat_pgPack]
      have h_norm_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v‖ ^ 2 = ∑ i, ((T⁻¹ *ᵥ v.ofLp) i) ^ 2 := by
        rw [h_toEuclideanCLM, norm_sq_toLp_two]
      rw [← h_norm_sq]
      have h_bound := hbound v
      -- h_bound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v‖ ≤ ‖v‖ / t
      have h_norm_v_sq : ‖v‖ ^ 2 = ∑ i, M i j ^ 2 := by
        rw [norm_sq_toLp_two]
      have h_nonneg : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v‖ := by positivity
      -- From h_bound: ‖...‖ ≤ ‖v‖ / t
      -- Square both sides (using nlinarith which can handle this since t > 0)
      -- (‖v‖ / t)^2 = ‖v‖^2 / t^2
      -- So after squaring: ‖...‖^2 ≤ ‖v‖^2 / t^2
      -- Then use h_norm_v_sq
      have h_goal : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v‖ ^ 2 ≤ (∑ i, M i j ^ 2) / t ^ 2 := by
        -- From h_bound: ‖...‖ ≤ ‖v‖ / t
        -- Since both sides are nonnegative, we can square
        have h_nonneg_v : 0 ≤ ‖v‖ := by positivity
        have h_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ v‖ ^ 2 ≤ (‖v‖ / t) ^ 2 := by
          nlinarith
        -- (‖v‖ / t)^2 = ‖v‖^2 / t^2
        rw [div_pow] at h_sq
        -- h_sq : ‖...‖ ^ 2 ≤ ‖v‖ ^ 2 / t ^ 2
        rw [h_norm_v_sq] at h_sq
        -- h_sq : ‖...‖ ^ 2 ≤ (∑ i, M i j ^ 2) / t ^ 2
        exact h_sq
      exact h_goal
    -- Step 1: (a-b)^2 ≤ 2*a^2 + 2*b^2 entrywise
    have h_entrywise : ∀ i j, (A i j - B i j) ^ 2 ≤ 2 * A i j ^ 2 + 2 * B i j ^ 2 :=
      fun i j => sub_sq_le (A i j) (B i j)
    have h_sum_entrywise : ∑ i, ∑ j, (A i j - B i j) ^ 2 ≤
        2 * (∑ i, ∑ j, A i j ^ 2) + 2 * (∑ i, ∑ j, B i j ^ 2) := by
      calc
        ∑ i, ∑ j, (A i j - B i j) ^ 2 ≤ ∑ i, ∑ j, (2 * A i j ^ 2 + 2 * B i j ^ 2) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_entrywise i j))
        _ = 2 * (∑ i, ∑ j, A i j ^ 2) + 2 * (∑ i, ∑ j, B i j ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    -- Step 2: Bound ∑ B i j ^ 2 = (pgKappa / d)^2 * ∑ (T⁻¹ i j)^2 ≤ (pgKappa / d)^2 * d / t^2
    have hB_sum : ∑ i, ∑ j, B i j ^ 2 ≤ (pgKappa / d) ^ 2 * d / t ^ 2 := by
      calc
        ∑ i, ∑ j, B i j ^ 2 = ∑ i, ∑ j, (((pgKappa / d) • T⁻¹) i j) ^ 2 := rfl
        _ = (pgKappa / d) ^ 2 * ∑ i, ∑ j, (T⁻¹ i j) ^ 2 := by
          simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
        _ ≤ (pgKappa / d) ^ 2 * (d / t ^ 2) := by
          have h_nonneg : 0 ≤ (pgKappa / d) ^ 2 := by positivity
          apply mul_le_mul_of_nonneg_left ?_ h_nonneg
          calc
            ∑ i, ∑ j, (T⁻¹ i j) ^ 2 = ∑ i, ∑ j, ((T⁻¹ * (1 : Matrix (Fin d) (Fin d) ℝ)) i j) ^ 2 := by simp
            _ ≤ ∑ j, ((∑ i, (1 : Matrix (Fin d) (Fin d) ℝ) i j ^ 2) / t ^ 2) := by
              -- Use h_col_mulVec_bound for each column
              -- Actually, we need to sum over j first
              -- ∑ i, ∑ j, ((T⁻¹ * 1) i j)^2 = ∑ j, ∑ i, ((T⁻¹ * 1) i j)^2
              -- ≤ ∑ j, (∑ i, (1 i j)^2) / t^2
              rw [Finset.sum_comm]
              refine Finset.sum_le_sum (fun j _ => h_col_mulVec_bound (1 : Matrix (Fin d) (Fin d) ℝ) j)
            _ = (∑ j, ∑ i, (1 : Matrix (Fin d) (Fin d) ℝ) i j ^ 2) / t ^ 2 := by
              simp [Finset.sum_div]
            _ = (∑ i, ∑ j, (1 : Matrix (Fin d) (Fin d) ℝ) i j ^ 2) / t ^ 2 := by rw [Finset.sum_comm]
            _ = (d : ℝ) / t ^ 2 := by simp [Matrix.one_apply]
            _ = d / t ^ 2 := rfl
        _ = (pgKappa / d) ^ 2 * d / t ^ 2 := by ring
    -- Step 3: Bound ∑ A i j ^ 2
    have hA_sum : ∑ i, ∑ j, A i j ^ 2 ≤ f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2 := by
      have h_add_sq_bound (M : Matrix (Fin d) (Fin d) ℝ) :
          ∑ i, ∑ j, ((M + Mᵀ) i j) ^ 2 ≤ 4 * ∑ i, ∑ j, (M i j) ^ 2 := by
        calc
          ∑ i, ∑ j, ((M + Mᵀ) i j) ^ 2 = ∑ i, ∑ j, (M i j + M j i) ^ 2 := rfl
          _ ≤ ∑ i, ∑ j, (2 * M i j ^ 2 + 2 * M j i ^ 2) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => add_sq_le (M i j) (M j i)))
          _ = 2 * (∑ i, ∑ j, M i j ^ 2) + 2 * (∑ i, ∑ j, M j i ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
          _ = 2 * (∑ i, ∑ j, M i j ^ 2) + 2 * (∑ i, ∑ j, M i j ^ 2) := by
            rw [Finset.sum_comm]
          _ = 4 * ∑ i, ∑ j, (M i j) ^ 2 := by ring
      calc
        ∑ i, ∑ j, A i j ^ 2 = ∑ i, ∑ j, (((f/2) • (T⁻¹ * G + (T⁻¹ * G)ᵀ)) i j) ^ 2 := rfl
        _ = (f/2) ^ 2 * ∑ i, ∑ j, ((T⁻¹ * G + (T⁻¹ * G)ᵀ) i j) ^ 2 := by
          simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
        _ ≤ (f/2) ^ 2 * (4 * ∑ i, ∑ j, ((T⁻¹ * G) i j) ^ 2) := by
          have h_nonneg : 0 ≤ (f/2) ^ 2 := by positivity
          apply mul_le_mul_of_nonneg_left (h_add_sq_bound (T⁻¹ * G)) h_nonneg
        _ = f ^ 2 * ∑ i, ∑ j, ((T⁻¹ * G) i j) ^ 2 := by ring
        _ ≤ f ^ 2 * ((∑ i, ∑ j, G i j ^ 2) / t ^ 2) := by
          have h_nonneg : 0 ≤ f ^ 2 := by positivity
          apply mul_le_mul_of_nonneg_left ?_ h_nonneg
          calc
            ∑ i, ∑ j, ((T⁻¹ * G) i j) ^ 2 = ∑ j, ∑ i, ((T⁻¹ * G) i j) ^ 2 := Finset.sum_comm
            _ ≤ ∑ j, ((∑ i, G i j ^ 2) / t ^ 2) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              exact h_col_mulVec_bound G j
            _ = (∑ j, ∑ i, G i j ^ 2) / t ^ 2 := by
              simp [Finset.sum_div]
            _ = (∑ i, ∑ j, G i j ^ 2) / t ^ 2 := by rw [Finset.sum_comm]
        _ = f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2 := by
          dsimp [G]
          have h_eq : (∑ i, ∑ j, (pgGG g) i j ^ 2) = (∑ i, ∑ j, gstat g i j ^ 2) := by
            unfold gstat pgGG
            congr
          rw [h_eq]
          ring
    -- Step 4: Combine
    apply le_trans h_sum_entrywise
    -- Goal: 2 * (∑ i, ∑ j, A i j ^ 2) + 2 * (∑ i, ∑ j, B i j ^ 2) ≤
    --   2 * f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2 + 2 * (pgKappa / d) ^ 2 * d / t ^ 2
    -- Rewrite RHS to match the form from hA_sum and hB_sum
    have hR : 2 * f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2 + 2 * (pgKappa / d) ^ 2 * d / t ^ 2 =
        2 * (f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2) + 2 * ((pgKappa / d) ^ 2 * d / t ^ 2) := by ring
    rw [hR]
    -- Goal: 2 * (∑ i, ∑ j, A i j ^ 2) + 2 * (∑ i, ∑ j, B i j ^ 2) ≤
    --   2 * (f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2) + 2 * ((pgKappa / d) ^ 2 * d / t ^ 2)
    -- This follows from hA_sum and hB_sum by add_le_add and mul_le_mul
    have h_left : 2 * (∑ i, ∑ j, A i j ^ 2) ≤ 2 * (f ^ 2 * (∑ i, ∑ j, gstat g i j ^ 2) / t ^ 2) := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      apply mul_le_mul_of_nonneg_left hA_sum this
    have h_right : 2 * (∑ i, ∑ j, B i j ^ 2) ≤ 2 * ((pgKappa / d) ^ 2 * d / t ^ 2) := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      apply mul_le_mul_of_nonneg_left hB_sum this
    exact add_le_add h_left h_right
  -- Combine the two bounds
  -- Goal: A + B ≤ C + D + E
  -- h_first: A ≤ C
  -- h_second: B ≤ D + E
  -- So A + B ≤ C + (D + E) = C + D + E
  simpa [add_assoc] using add_le_add h_first h_second

theorem pgFt_sq_le (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (g : EuclideanSpace ℝ (Fin d)) :
    0 ≤ pgFt K ρ x g ∧ pgFt K ρ x g ^ 2 ≤ 5 / 4 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hEta' := hEta (d : ℝ) ρ hd_real hρ
  rcases hEta' with ⟨hη_nonneg, hη_sq⟩
  have hFt_bounds := pgFt_bounds hLB hD4 d ρ hd hρ K hK x hx g
  rcases hFt_bounds with ⟨hle, hle2, hF_nonneg, hF_le⟩
  have h0 : 0 ≤ pgFt K ρ x g := by
    linarith
  have hρ_nonneg : 0 ≤ ρ := by linarith
  have h_norm_nonneg : 0 ≤ ‖g‖ := norm_nonneg _
  have hL_nonneg : 0 ≤ pgLD ρ := by
    unfold pgLD pgKappa pgPB
    positivity
  have hL_sq_nonneg : 0 ≤ pgLD ρ ^ 2 := by positivity
  have h_norm_sq_nonneg : 0 ≤ (1 + ‖g‖) ^ 2 := by positivity
  have h_factor_nonneg : 0 ≤ (5 / 4 : ℝ) * pgLD ρ ^ 2 := by positivity
  have h_sq_bound : pgFt K ρ x g ^ 2 ≤ 5 / 4 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
    have h_mul : pgFt K ρ x g ≤ (1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖) := by
      have h_eta1_nonneg : 0 ≤ 1 + pgEta (d : ℝ) ρ := by linarith
      have h_norm1_nonneg : 0 ≤ 1 + ‖g‖ := by linarith
      nlinarith
    have h_sq_mul : pgFt K ρ x g ^ 2 ≤ ((1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 := by
      nlinarith
    have h_norm_sq : (1 + ‖g‖) ^ 2 ≤ 2 * (1 + ‖g‖ ^ 2) := by
      have h := sq_nonneg (1 - ‖g‖)
      nlinarith
    calc
      pgFt K ρ x g ^ 2 ≤ ((1 + pgEta (d : ℝ) ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 := h_sq_mul
      _ = (1 + pgEta (d : ℝ) ρ) ^ 2 * pgLD ρ ^ 2 * (1 + ‖g‖) ^ 2 := by ring
      _ ≤ (5 / 4) * pgLD ρ ^ 2 * (1 + ‖g‖) ^ 2 := by
        have h1 : (1 + pgEta (d : ℝ) ρ) ^ 2 * pgLD ρ ^ 2 ≤ (5 / 4) * pgLD ρ ^ 2 :=
          mul_le_mul_of_nonneg_right hη_sq hL_sq_nonneg
        exact mul_le_mul_of_nonneg_right h1 h_norm_sq_nonneg
      _ ≤ (5 / 4) * pgLD ρ ^ 2 * (2 * (1 + ‖g‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h_norm_sq h_factor_nonneg
      _ = 5 / 4 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by ring
  exact And.intro h0 h_sq_bound

theorem gstat_sum_sq_le {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) :
    ∑ i, ∑ j, gstat g i j ^ 2 ≤ 2 * ‖g‖ ^ 4 + 2 * d := by
  have hn : ‖g‖ ^ 2 = ∑ i, g i ^ 2 := EuclideanSpace.real_norm_sq_eq g
  have h1 : ∀ i j, gstat g i j ^ 2 ≤ 2 * (g i ^ 2 * g j ^ 2) + 2 * (if i = j then 1 else 0) := by
    intro i j
    unfold gstat
    split_ifs <;> nlinarith [sq_nonneg (g i * g j + 1), sq_nonneg (g i * g j)]
  calc ∑ i, ∑ j, gstat g i j ^ 2 ≤ ∑ i, ∑ j, (2 * (g i ^ 2 * g j ^ 2) + 2 * (if i = j then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = 2 * ((∑ i, g i ^ 2) * (∑ j, g j ^ 2)) + 2 * d := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul_sum]
        simp
    _ = 2 * ‖g‖ ^ 4 + 2 * d := by rw [← hn]; ring

theorem integrable_one_add_norm_sq_pow3 {d : ℕ} :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => (1 + ‖g‖ ^ 2) ^ 3) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hp : ∀ n : ℕ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ n) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun n => (IsGaussian.memLp_id _ (n : ENNReal) (by simp)).integrable_norm_pow'
  have he : (fun g : EuclideanSpace ℝ (Fin d) => (1 + ‖g‖ ^ 2) ^ 3) =
      fun g => 1 + 3 * ‖g‖ ^ 2 + 3 * ‖g‖ ^ 4 + ‖g‖ ^ 6 := by funext g; ring
  rw [he]
  exact (((integrable_const 1).add ((hp 2).const_mul 3)).add ((hp 4).const_mul 3)).add (hp 6)

theorem pgV_integrable (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq) (d : ℕ)
    (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d)
    (hx : x ∈ pgDom d ρ) :
    Integrable (pgV K ρ x) (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      Integrable (fun g => ‖pgV K ρ x g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hmeas : Measurable (pgV K ρ x) :=
    (pgV_measurable hPT d K ρ hK.2.1).of_uncurry_left
  set c : ℝ := 5 / 4 * (2 * pgLD ρ ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set M : ℝ := (c + 4 * c * (1 + d) + 2 * (pgKappa / d) ^ 2 * d) / pgTmin d ρ ^ 2 with hM
  have hbd : ∀ g, ‖pgV K ρ x g‖ ^ 2 ≤ M * (1 + ‖g‖ ^ 2) ^ 3 := by
    intro g
    obtain ⟨-, hF⟩ := pgFt_sq_le hLB hD4 hEta d ρ hd hρ K hK x hx g
    have hV := pgV_norm_sq_le d ρ hd hρ K x hx g
    have hG := gstat_sum_sq_le g
    have hG0 : 0 ≤ ∑ i, ∑ j, gstat g i j ^ 2 := by positivity
    set S := ∑ i, ∑ j, gstat g i j ^ 2
    set s := ‖g‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hg4 : ‖g‖ ^ 4 = s ^ 2 := by rw [hs]; ring
    rw [hg4] at hG
    set F2 := pgFt K ρ x g ^ 2 with hF2
    have hF' : F2 ≤ c * (1 + s) := by rw [hc]; linarith
    have hF20 : 0 ≤ F2 := sq_nonneg _
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hp1 : 1 ≤ (1 + s) ^ 3 := one_le_pow₀ (by linarith)
    have k1 : F2 * s ≤ c * (1 + s) ^ 3 := by
      have : F2 * s ≤ c * (1 + s) * s := mul_le_mul_of_nonneg_right hF' hs0
      nlinarith [mul_nonneg hc0 hs0, mul_nonneg (mul_nonneg hc0 hs0) hs0, mul_nonneg hc0 (mul_nonneg hs0 (mul_nonneg hs0 hs0))]
    have hS' : S ≤ (2 + 2 * d) * (1 + s) ^ 2 := by nlinarith [mul_nonneg hd0 hs0, mul_nonneg hd0 (mul_nonneg hs0 hs0)]
    have k2 : 2 * F2 * S ≤ 4 * c * (1 + d) * (1 + s) ^ 3 := by
      have : F2 * S ≤ c * (1 + s) * ((2 + 2 * d) * (1 + s) ^ 2) :=
        mul_le_mul hF' hS' hG0 (by positivity)
      nlinarith
    have k3 : 2 * (pgKappa / d) ^ 2 * d ≤ 2 * (pgKappa / d) ^ 2 * d * (1 + s) ^ 3 :=
      le_mul_of_one_le_right (by positivity) hp1
    calc ‖pgV K ρ x g‖ ^ 2 ≤ _ := hV
      _ = (F2 * s + 2 * F2 * S + 2 * (pgKappa / d) ^ 2 * d) / pgTmin d ρ ^ 2 := by ring
      _ ≤ (c * (1 + s) ^ 3 + 4 * c * (1 + d) * (1 + s) ^ 3 + 2 * (pgKappa / d) ^ 2 * d * (1 + s) ^ 3) /
          pgTmin d ρ ^ 2 := by gcongr
      _ = M * (1 + s) ^ 3 := by rw [hM]; ring
  have h2 : Integrable (fun g => ‖pgV K ρ x g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine (integrable_one_add_norm_sq_pow3.const_mul M).mono' ((hmeas.norm.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [] with g
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbd g
  refine ⟨?_, h2⟩
  refine ((integrable_const (1 : ℝ)).add h2).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with g
  show ‖pgV K ρ x g‖ ≤ 1 + ‖pgV K ρ x g‖ ^ 2
  nlinarith [sq_nonneg (‖pgV K ρ x g‖ - 1), norm_nonneg (pgV K ρ x g)]

theorem pgV_second_moment (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    ∫ g, ‖pgV K ρ x g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ pgG2 d ρ := by
  set L := pgLD ρ with hL
  set t := pgTmin d ρ with ht
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : ∀ n : ℕ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ n) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun n => (IsGaussian.memLp_id _ (n : ENNReal) (by simp)).integrable_norm_pow'
  have hI1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have he : (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) = fun g => ‖g‖ ^ 2 + ‖g‖ ^ 4 := by
      funext g; ring
    rw [he]; exact (hp 2).add (hp 4)
  have hI2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have he : (fun g : EuclideanSpace ℝ (Fin d) => (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)) =
        fun g => ‖g‖ ^ 6 - ‖g‖ ^ 4 + ((d : ℝ) - 2) * ‖g‖ ^ 2 + (d : ℝ) := by
      funext g; ring
    rw [he]; exact (((hp 6).sub (hp 4)).add ((hp 2).const_mul _)).add (integrable_const _)
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun g =>
    5 / 2 * L ^ 2 / t ^ 2 * (‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) +
      5 * L ^ 2 / t ^ 2 * ((‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)) + 2 * (pgKappa / d) ^ 2 * d / t ^ 2
    with hh
  have hhi : Integrable h (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ((hI1.const_mul _).add (hI2.const_mul _)).add (integrable_const _)
  have hbd : ∀ g, ‖pgV K ρ x g‖ ^ 2 ≤ h g := by
    intro g
    obtain ⟨-, hF⟩ := pgFt_sq_le hLB hD4 hEta d ρ hd hρ K hK x hx g
    have hV := pgV_norm_sq_le d ρ hd hρ K x hx g
    have hS := hFrob d g
    have hS0 : 0 ≤ ∑ i, ∑ j, gstat g i j ^ 2 := by positivity
    rw [hS] at hV hS0
    set s := ‖g‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hg4 : ‖g‖ ^ 4 = s ^ 2 := by rw [hs]; ring
    rw [hg4] at hV hS0
    have hh' : h g = 5 / 2 * L ^ 2 / t ^ 2 * (s * (1 + s)) +
        5 * L ^ 2 / t ^ 2 * ((s ^ 2 - 2 * s + (d : ℝ)) * (1 + s)) + 2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
      rw [hh]; simp only; rw [hg4]
    rw [hh']
    set F2 := pgFt K ρ x g ^ 2
    set u := (t ^ 2)⁻¹ with hu
    have hu0 : 0 ≤ u := by positivity
    have hF' : F2 ≤ 5 / 2 * L ^ 2 * (1 + s) := by linarith
    have e1 : F2 * (s * u) ≤ 5 / 2 * L ^ 2 * (1 + s) * (s * u) :=
      mul_le_mul_of_nonneg_right hF' (mul_nonneg hs0 hu0)
    have e2 : F2 * ((s ^ 2 - 2 * s + d) * u) ≤ 5 / 2 * L ^ 2 * (1 + s) * ((s ^ 2 - 2 * s + d) * u) :=
      mul_le_mul_of_nonneg_right hF' (mul_nonneg hS0 hu0)
    have hV' : ‖pgV K ρ x g‖ ^ 2 ≤ F2 * (s * u) + 2 * (F2 * ((s ^ 2 - 2 * s + d) * u)) +
        2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
      refine hV.trans (le_of_eq ?_); rw [hu]; ring
    have hR : 5 / 2 * L ^ 2 / t ^ 2 * (s * (1 + s)) + 5 * L ^ 2 / t ^ 2 * ((s ^ 2 - 2 * s + (d : ℝ)) * (1 + s)) =
        5 / 2 * L ^ 2 * (1 + s) * (s * u) + 2 * (5 / 2 * L ^ 2 * (1 + s) * ((s ^ 2 - 2 * s + d) * u)) := by
      rw [hu]; ring
    linarith
  have hmom := (hMom d)
  calc ∫ g, ‖pgV K ρ x g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ ∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (pgV_integrable hPT hLB hD4 hEta d ρ hd hρ K hK x hx).2 hhi hbd
    _ = 5 / 2 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 3)) + 5 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 1) * (d + 5)) +
          2 * (pgKappa / d) ^ 2 * d / t ^ 2 := by
        have hA : Integrable (fun g : EuclideanSpace ℝ (Fin d) => 5 / 2 * L ^ 2 / t ^ 2 * (‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) +
            5 * L ^ 2 / t ^ 2 * ((‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)))
            (stdGaussian (EuclideanSpace ℝ (Fin d))) := (hI1.const_mul _).add (hI2.const_mul _)
        simp only [hh]
        rw [integral_add hA (integrable_const _), integral_add (hI1.const_mul (5 / 2 * L ^ 2 / t ^ 2))
          (hI2.const_mul (5 * L ^ 2 / t ^ 2)), integral_const_mul, integral_const_mul, hmom.1, hmom.2]
        simp
    _ ≤ pgG2 d ρ := by
        unfold pgG2
        rw [← hL, ← ht]
        have hdd : 2 * (pgKappa / d) ^ 2 * d = 2 * pgKappa ^ 2 / d := by field_simp
        have hpoly : 5 / 2 * ((d : ℝ) * (d + 3)) + 5 * ((d : ℝ) * (d + 1) * (d + 5)) ≤ 5 * d * (d + 2) * (d + 5) := by
          nlinarith
        have hL2 : 0 ≤ L ^ 2 / t ^ 2 := by positivity
        have e : 5 / 2 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 3)) + 5 * L ^ 2 / t ^ 2 * ((d : ℝ) * (d + 1) * (d + 5)) +
            2 * (pgKappa / d) ^ 2 * d / t ^ 2 =
            L ^ 2 / t ^ 2 * (5 / 2 * ((d : ℝ) * (d + 3)) + 5 * ((d : ℝ) * (d + 1) * (d + 5))) +
              2 * pgKappa ^ 2 / d / t ^ 2 := by rw [← hdd]; ring
        have e' : (5 * L ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) / t ^ 2 =
            L ^ 2 / t ^ 2 * (5 * d * (d + 2) * (d + 5)) + 2 * pgKappa ^ 2 / d / t ^ 2 := by ring
        rw [e, e']
        have := mul_le_mul_of_nonneg_left hpoly hL2
        linarith

theorem pgEps_sq (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d)
    (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    MemLp (pgEps K ρ x) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ g, pgEps K ρ x g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        pgU d ρ ^ 2 := by
  have hK_conv := hK.1
  have hK_closed := hK.2.1
  have hK_ball1 := hK.2.2.1
  have hK_ballρ := hK.2.2.2
  have hx_dom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := hx
  have hTmin_nonneg : 0 ≤ pgTmin d ρ := by
    have hd' : 0 ≤ (d : ℝ) := by exact mod_cast (Nat.zero_le d)
    have hlam_nonneg : 0 ≤ pgLam ρ := by
      dsimp [pgLam]
      have hlog_nonneg : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by linarith)
      nlinarith [Real.sqrt_nonneg (2 * Real.log (1 + ρ))]
    refine div_nonneg (by norm_num) ?_
    refine mul_nonneg (mul_nonneg (by norm_num) hd') hlam_nonneg
  have hD4_app := hD4 d K (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) hK_conv hK_ball1
    hTmin_nonneg hx_dom
  rcases hD4_app with ⟨hF_lip, hF_bounds, hF_int⟩
  have hF_nonneg (g : EuclideanSpace ℝ (Fin d)) : 0 ≤ posF K (pgMu x) (pgOp x) g := (hF_bounds g).1
  have hF_le (g : EuclideanSpace ℝ (Fin d)) : posF K (pgMu x) (pgOp x) g ≤ pgLD ρ * (1 + ‖g‖) :=
    (pgFt_bounds hLB hD4 d ρ hd hρ K hK x hx g).2.2.2
  have hFt_bounds_app := pgFt_bounds hLB hD4 d ρ hd hρ K hK x hx
  have h_ft_le (g : EuclideanSpace ℝ (Fin d)) : posF K (pgMu x) (pgOp x) g ≤ pgFt K ρ x g :=
    (hFt_bounds_app g).1
  have h_ft_le_eta (g : EuclideanSpace ℝ (Fin d)) : pgFt K ρ x g ≤ (1 + pgEta d ρ) * posF K (pgMu x) (pgOp x) g :=
    (hFt_bounds_app g).2.1
  have h_eps_nonneg (g : EuclideanSpace ℝ (Fin d)) : 0 ≤ pgEps K ρ x g := by
    unfold pgEps
    linarith [h_ft_le g]
  have h_eps_le (g : EuclideanSpace ℝ (Fin d)) : pgEps K ρ x g ≤ pgEta d ρ * posF K (pgMu x) (pgOp x) g := by
    unfold pgEps
    linarith [h_ft_le_eta g]
  have hLD_nonneg : 0 ≤ pgLD ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    positivity
  have h_eta_nonneg : 0 ≤ pgEta d ρ := by
    dsimp [pgEta]
    have hEh_nonneg : 0 ≤ pgEh d ρ := by
      dsimp [pgEh]
      have hKappa_sq_nonneg : 0 ≤ pgKappa ^ 2 := pow_two_nonneg _
      have h_denom_pos : 0 < 922 * (d : ℝ) ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by
        have h922 : 0 < (922 : ℝ) := by norm_num
        have hd_sq_pos : 0 < (d : ℝ) ^ 2 := by
          have hd_pos : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          have hd_pos' : 0 < (d : ℝ) := by linarith
          exact pow_pos hd_pos' 2
        have hLam_sq_pos : 0 < pgLam ρ ^ 2 := pow_pos (by
          dsimp [pgLam]
          have hlog_pos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
          have h_inner_pos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
          exact Real.sqrt_pos.mpr h_inner_pos) 2
        have hLD_pos : 0 < pgLD ρ := by
          dsimp [pgLD, pgKappa, pgPB]
          positivity
        positivity
      refine div_nonneg hKappa_sq_nonneg (by positivity)
    have hTmin_nonneg' : 0 ≤ pgTmin d ρ := hTmin_nonneg
    have hDelta_nonneg : 0 ≤ pgDelta d ρ := by
      dsimp [pgDelta]
      have hKappa_nonneg : 0 ≤ pgKappa := by
        dsimp [pgKappa]
        norm_num
      have h_rho_nonneg : 0 ≤ ρ := by linarith
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (4 + pgPB ^ 2 * (d : ℝ)) := Real.sqrt_nonneg _
      positivity
    positivity
  have h_eps_le_etaL (g : EuclideanSpace ℝ (Fin d)) : pgEps K ρ x g ≤ pgEta d ρ * pgLD ρ * (1 + ‖g‖) := by
    calc
      pgEps K ρ x g ≤ pgEta d ρ * posF K (pgMu x) (pgOp x) g := h_eps_le g
      _ ≤ pgEta d ρ * (pgLD ρ * (1 + ‖g‖)) := by
        nlinarith [hF_le g, h_eta_nonneg]
      _ = pgEta d ρ * pgLD ρ * (1 + ‖g‖) := by ring
  have h_eps_sq_le (g : EuclideanSpace ℝ (Fin d)) : (pgEps K ρ x g) ^ 2 ≤ (pgEta d ρ) ^ 2 * (posF K (pgMu x) (pgOp x) g) ^ 2 := by
    have h_eps := h_eps_le g
    have h_eps_nonneg_g := h_eps_nonneg g
    nlinarith
  -- Measurability of pgEps
  have h_meas_pgFt : Measurable (pgFt K ρ x) := by
    have h_pt_meas : Measurable (piTilde K ρ (pgJb d ρ)) :=
      hPT d K ρ hK_closed (pgJb d ρ)
    have h_add_meas : Measurable (fun g : EuclideanSpace ℝ (Fin d) => pgMu x + pgOp x g) := by
      refine (measurable_const.add ?_)
      exact (pgOp x).continuous.measurable
    exact h_pt_meas.comp h_add_meas
  have h_meas_posF : AEStronglyMeasurable (posF K (pgMu x) (pgOp x)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_cont : Continuous (posF K (pgMu x) (pgOp x)) := by
      have h_gauge_cont : Continuous (gauge K) := by
        refine continuous_gauge hK_conv ?_
        have h0_mem_closedBall : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
          rw [Metric.mem_closedBall]
          simp [show (0 : ℝ) ≤ 1 from by norm_num]
        have h_nhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
          Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) (by norm_num)) hK_ball1
        exact h_nhds
      have h_add_cont : Continuous (fun g : EuclideanSpace ℝ (Fin d) => pgMu x + pgOp x g) := by
        continuity
      exact h_gauge_cont.comp h_add_cont
    exact h_cont.aestronglyMeasurable
  have h_meas_eps : AEStronglyMeasurable (pgEps K ρ x) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    unfold pgEps
    exact AEStronglyMeasurable.sub h_meas_pgFt.aestronglyMeasurable h_meas_posF
  -- The bounding function g ↦ η * L * (1 + ‖g‖) is in L²
  have h_memLp_bound : MemLp (fun g : EuclideanSpace ℝ (Fin d) => pgEta d ρ * pgLD ρ * (1 + ‖g‖)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_id_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => g) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ProbabilityTheory.IsGaussian.memLp_two_fun_id (E := EuclideanSpace ℝ (Fin d))
        (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    have h_const_mem : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      memLp_const (1 : ℝ)
    have h_norm_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_id_ae : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => g)
          (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        continuous_id.aestronglyMeasurable
      exact (memLp_norm_iff h_id_ae).mpr h_id_mem
    have h_sum_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => (1 : ℝ) + ‖g‖) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      MemLp.add h_const_mem h_norm_mem
    have h_mul_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => pgEta d ρ * pgLD ρ * ((1 : ℝ) + ‖g‖)) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      h_sum_mem.const_mul (pgEta d ρ * pgLD ρ)
    simpa [mul_add] using h_mul_mem
  -- Apply MemLp.mono to get pgEps is in L²
  have h_memLp_eps : MemLp (pgEps K ρ x) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine MemLp.mono h_memLp_bound h_meas_eps ?_
    filter_upwards with g
    have h := h_eps_le_etaL g
    have h_nonneg_eps : 0 ≤ pgEps K ρ x g := h_eps_nonneg g
    have h_nonneg_bound : 0 ≤ pgEta d ρ * pgLD ρ * (1 + ‖g‖) := by
      positivity
    calc
      |pgEps K ρ x g| = pgEps K ρ x g := abs_of_nonneg h_nonneg_eps
      _ ≤ pgEta d ρ * pgLD ρ * (1 + ‖g‖) := h
      _ = |pgEta d ρ * pgLD ρ * (1 + ‖g‖)| := by rw [abs_of_nonneg h_nonneg_bound]
  -- F is in L² because it's bounded by a linear function which is in L²
  have hF_memLp : MemLp (posF K (pgMu x) (pgOp x)) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_bound_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ‖pgMu x‖ + pgLD ρ * ‖g‖) 2
        (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_const_mem : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => ‖pgMu x‖) 2
          (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        memLp_const _
      have h_norm_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖) 2
          (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        have h_id_ae : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => g)
            (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          continuous_id.aestronglyMeasurable
        exact (memLp_norm_iff h_id_ae).mpr
          (ProbabilityTheory.IsGaussian.memLp_two_fun_id (E := EuclideanSpace ℝ (Fin d))
            (μ := stdGaussian (EuclideanSpace ℝ (Fin d))))
      have h_mul_mem : MemLp (fun g : EuclideanSpace ℝ (Fin d) => pgLD ρ * ‖g‖) 2
          (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        h_norm_mem.const_mul (pgLD ρ)
      exact MemLp.add h_const_mem h_mul_mem
    refine MemLp.mono h_bound_mem h_meas_posF ?_
    filter_upwards with g
    have h := hF_bounds g
    have h_nonneg_F : 0 ≤ posF K (pgMu x) (pgOp x) g := h.1
    have h_nonneg_bound : 0 ≤ ‖pgMu x‖ + pgLD ρ * ‖g‖ := by
      positivity
    calc
      |posF K (pgMu x) (pgOp x) g| = posF K (pgMu x) (pgOp x) g := abs_of_nonneg h_nonneg_F
      _ ≤ ‖pgMu x‖ + pgLD ρ * ‖g‖ := h.2
      _ = |‖pgMu x‖ + pgLD ρ * ‖g‖| := by rw [abs_of_nonneg h_nonneg_bound]
  -- Integral inequality
  have h_int_bound : ∫ g, (pgEps K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      pgU d ρ ^ 2 := by
    have h_one_le_two : (1 : ENNReal) ≤ 2 := by norm_num
    have h_int_pgEps_sq : ∫ g, (pgEps K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        ∫ g, (pgEta d ρ) ^ 2 * ((posF K (pgMu x) (pgOp x) g) ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine integral_mono ?_ ?_ h_eps_sq_le
      · -- integrability of pgEps^2
        exact h_memLp_eps.integrable_sq
      · -- integrability of η² * F²
        have hF_sq_int : Integrable (fun g => (posF K (pgMu x) (pgOp x) g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          hF_memLp.integrable_sq
        exact hF_sq_int.const_mul ((pgEta d ρ) ^ 2)
    calc
      ∫ g, (pgEps K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, (pgEta d ρ) ^ 2 * ((posF K (pgMu x) (pgOp x) g) ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        h_int_pgEps_sq
      _ = (pgEta d ρ) ^ 2 * ∫ g, (posF K (pgMu x) (pgOp x) g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_const_mul]
      _ ≤ (pgEta d ρ) ^ 2 * ((pgKappa * ρ + pgLD ρ * Real.sqrt (d : ℝ)) ^ 2) := by
        nlinarith
      _ ≤ (pgEta d ρ) ^ 2 * ((pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2) := by
        have hKappa_sq_nonneg : 0 ≤ (pgEta d ρ) ^ 2 := pow_two_nonneg _
        have hKappa_le_LD : pgKappa * ρ ≤ pgLD ρ := by
          dsimp [pgLD, pgKappa, pgPB]
          nlinarith
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
        have h_nonneg_left : 0 ≤ pgKappa * ρ + pgLD ρ * Real.sqrt (d : ℝ) := by
          have hKappa_nonneg : 0 ≤ pgKappa := by
            dsimp [pgKappa]
            norm_num
          have h_rho_nonneg : 0 ≤ ρ := by linarith
          have hLD_nonneg : 0 ≤ pgLD ρ := hLD_nonneg
          have h_sqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
          positivity
        have h_nonneg_right : 0 ≤ pgLD ρ * (1 + Real.sqrt (d : ℝ)) := by
          positivity
        have h_bound : pgKappa * ρ + pgLD ρ * Real.sqrt (d : ℝ) ≤ pgLD ρ * (1 + Real.sqrt (d : ℝ)) := by
          nlinarith
        have h_sq_bound : (pgKappa * ρ + pgLD ρ * Real.sqrt (d : ℝ)) ^ 2 ≤ (pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2 := by
          nlinarith
        nlinarith
      _ = (pgEta d ρ * pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2 := by ring
      _ = (pgU d ρ) ^ 2 := rfl
  exact And.intro h_memLp_eps h_int_bound

theorem integral_euclid_apply {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {f : α → EuclideanSpace ℝ ι} (hf : Integrable f μ) (i : ι) : (∫ a, f a ∂μ) i = ∫ a, f a i ∂μ :=
  ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm hf).symm

theorem pgV_mean_aux (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (d : ℕ) (ρ : ℝ)
    (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d)
    (hx : x ∈ pgDom d ρ) :
    (∀ l, Integrable (fun g => pgFt K ρ x g * g l) (stdGaussian (EuclideanSpace ℝ (Fin d)))) ∧
      (∀ l j, Integrable (fun g => pgFt K ρ x g * gstat g l j) (stdGaussian (EuclideanSpace ℝ (Fin d)))) ∧
      (∀ l, ∫ g, pgFt K ρ x g * g l ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgBs K x l = pgEpsVec K ρ x l) ∧
      (∀ l j, ∫ g, pgFt K ρ x g * gstat g l j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgQs K x l j =
        pgEpsMat K ρ x l j) := by
  have hε2 := (pgEps_sq hPT hLB hD4 d ρ hd hρ K hK x hx).1
  have hτ0 : 0 ≤ pgTmin d ρ := by unfold pgTmin pgLam; positivity
  obtain ⟨hFL, -, -⟩ := d4_main d K _ _ _ (pgMu x) (pgOp x) hK.1 hK.2.2.1 hτ0 hx
  have hFt : ∀ g, pgFt K ρ x g = pgEps K ρ x g + posF K (pgMu x) (pgOp x) g := fun g => by
    unfold pgEps; ring
  have e1 : ∀ (i : Fin d) (g : EuclideanSpace ℝ (Fin d)), ⟪EuclideanSpace.single i (1 : ℝ), g⟫ = g i := by
    intro i g; simp [EuclideanSpace.inner_single_left]
  have hgl : ∀ l : Fin d, MemLp (fun g : EuclideanSpace ℝ (Fin d) => g l) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun l => by
    have := (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).continuousLinearMap_comp
      (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    simpa using this
  have hεl : ∀ l : Fin d, Integrable (fun g => pgEps K ρ x g * g l) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro l
    have := hε2.smul (p := 2) (q := 2) (r := 1) (hgl l)
    refine (memLp_one_iff_integrable.1 this).congr (Filter.Eventually.of_forall fun g => ?_)
    simp [Pi.smul_apply, smul_eq_mul]
  have hFl : ∀ l : Fin d, Integrable (fun g => posF K (pgMu x) (pgOp x) g * g l)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro l
    have := (integrable_moments _ _ hFL (EuclideanSpace.single l 1) 0).1
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [e1]; ring
  have hgs : ∀ (i j : Fin d) (g : EuclideanSpace ℝ (Fin d)),
      ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * ⟪EuclideanSpace.single j (1 : ℝ), g⟫ -
        ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ = gstat g i j := fun i j g => by
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, gstat]
    simp
  have hFq : ∀ i j : Fin d, Integrable (fun g => gstat g i j * posF K (pgMu x) (pgOp x) g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro i j
    have := (integrable_moments _ _ hFL (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).2.1
    simpa only [hgs] using this
  have hgsm : ∀ i j : Fin d, MemLp (fun g : EuclideanSpace ℝ (Fin d) => gstat g i j) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro i j
    have hm : Measurable (fun g : EuclideanSpace ℝ (Fin d) => gstat g i j) := by
      unfold gstat; fun_prop
    refine memLp_two_iff_integrable_sq hm.aestronglyMeasurable |>.2 ?_
    have hp : ∀ n : ℕ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ n)
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      fun n => (IsGaussian.memLp_id _ (n : ENNReal) (by simp)).integrable_norm_pow'
    refine (((hp 4).const_mul 2).add (integrable_const 2)).mono' (hm.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun g => ?_
    have hi : |g i| ≤ ‖g‖ := by simpa using PiLp.norm_apply_le g i
    have hj : |g j| ≤ ‖g‖ := by simpa using PiLp.norm_apply_le g j
    have hij : (g i * g j) ^ 2 ≤ ‖g‖ ^ 4 := by
      rw [mul_pow, show ‖g‖ ^ 4 = ‖g‖ ^ 2 * ‖g‖ ^ 2 by ring]
      exact mul_le_mul (sq_le_sq' (abs_le.1 hi).1 (abs_le.1 hi).2) (sq_le_sq' (abs_le.1 hj).1 (abs_le.1 hj).2)
        (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show (gstat g i j) ^ 2 ≤ 2 * ‖g‖ ^ 4 + 2
    unfold gstat
    split_ifs <;> nlinarith [sq_nonneg (g i * g j + 1)]
  have hεq : ∀ i j : Fin d, Integrable (fun g => gstat g i j * pgEps K ρ x g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro i j
    have := (hgsm i j).smul (p := 2) (q := 2) (r := 1) hε2
    refine (memLp_one_iff_integrable.1 this).congr (Filter.Eventually.of_forall fun g => ?_)
    simp [Pi.smul_apply, smul_eq_mul]
  refine ⟨fun l => ?_, fun l j => ?_, fun l => ?_, fun l j => ?_⟩
  · exact ((hεl l).add (hFl l)).congr (Filter.Eventually.of_forall fun g => by
      simp only [Pi.add_apply, hFt]; ring)
  · exact ((hεq l j).add (hFq l j)).congr (Filter.Eventually.of_forall fun g => by
      simp only [Pi.add_apply, hFt]; ring)
  · have hb : pgBs K x l = ∫ g, posF K (pgMu x) (pgOp x) g * g l ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      unfold pgBs posB
      rw [integral_euclid_apply (integrable_moments _ _ hFL 0 0).2.2]
      simp [smul_eq_mul]
    have hsplit : (fun g => pgFt K ρ x g * g l) =
        fun g => pgEps K ρ x g * g l + posF K (pgMu x) (pgOp x) g * g l := by
      funext g; rw [hFt]; ring
    rw [hb, hsplit, integral_add (hεl l) (hFl l)]
    unfold pgEpsVec; ring
  · have hq : pgQs K x l j =
        ∫ g, gstat g l j * posF K (pgMu x) (pgOp x) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      unfold pgQs posQ; simp only [hgs]
    have hsplit : (fun g => pgFt K ρ x g * gstat g l j) =
        fun g => gstat g l j * pgEps K ρ x g + gstat g l j * posF K (pgMu x) (pgOp x) g := by
      funext g; rw [hFt]; ring
    rw [hq, hsplit, integral_add (hεq l j) (hFq l j)]
    simp [pgEpsMat]

theorem pgV_mean_sub (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq) (d : ℕ) (ρ : ℝ)
    (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d)
    (hx : x ∈ pgDom d ρ) :
    ∫ g, pgV K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgGam K x =
      pgPack (WithLp.toLp 2 ((pgMat x)⁻¹ *ᵥ pgEpsVec K ρ x))
        ((1 / 2 : ℝ) • ((pgMat x)⁻¹ * pgEpsMat K ρ x + ((pgMat x)⁻¹ * pgEpsMat K ρ x)ᵀ)) := by
  obtain ⟨hI1, hI2, hE1, hE2⟩ := pgV_mean_aux hPT hLB hD4 d ρ hd hρ K hK x hx
  have hVi := (pgV_integrable hPT hLB hD4 hEta d ρ hd hρ K hK x hx).1
  set N := (pgMat x)⁻¹ with hNdef
  ext k
  rw [PiLp.sub_apply, integral_euclid_apply hVi]
  rcases k with i | ⟨i, j⟩
  · have hV : ∀ g, (pgV K ρ x g) (Sum.inl i) = ∑ l, N i l * (pgFt K ρ x g * g l) := by
      intro g
      simp [pgV, pgPack, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, hNdef]
    simp_rw [hV]
    rw [integral_finsetSum _ fun l _ => (hI1 l).const_mul _]
    simp_rw [integral_const_mul]
    simp only [pgGam, pgPack, PiLp.toLp_apply, Sum.elim_inl, Matrix.mulVec, dotProduct, ← hNdef]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_sub, hE1 l]
  · have hV : ∀ g, (pgV K ρ x g) (Sum.inr (i, j)) =
        1 / 2 * ∑ l, N i l * (pgFt K ρ x g * gstat g l j) + 1 / 2 * ∑ l, N j l * (pgFt K ρ x g * gstat g l i) -
          pgKappa / d * N i j := by
      intro g
      have hs : ∀ a b, ∑ l, N a l * pgGG g l b = ∑ l, N a l * gstat g l b := by
        intro a b
        refine Finset.sum_congr rfl fun l _ => ?_
        simp [pgGG, gstat, Matrix.vecMulVec_apply, Matrix.one_apply]
      have hs2 : ∀ a b, ∑ l, N a l * (pgFt K ρ x g * gstat g l b) = pgFt K ρ x g * ∑ l, N a l * gstat g l b := by
        intro a b
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      simp only [pgV, pgPack, PiLp.toLp_apply, Sum.elim_inr, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.transpose_apply, Matrix.mul_apply, smul_eq_mul, ← hNdef]
      rw [hs, hs, hs2, hs2]
      ring
    simp_rw [hV]
    have hA : Integrable (fun g => 1 / 2 * ∑ l, N i l * (pgFt K ρ x g * gstat g l j))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (integrable_finsetSum _ fun l _ => (hI2 l j).const_mul _).const_mul _
    have hB : Integrable (fun g => 1 / 2 * ∑ l, N j l * (pgFt K ρ x g * gstat g l i))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (integrable_finsetSum _ fun l _ => (hI2 l i).const_mul _).const_mul _
    have hAB : Integrable (fun g => 1 / 2 * ∑ l, N i l * (pgFt K ρ x g * gstat g l j) +
        1 / 2 * ∑ l, N j l * (pgFt K ρ x g * gstat g l i)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := hA.add hB
    rw [integral_sub hAB (integrable_const _), integral_add hA hB, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun l _ => (hI2 l j).const_mul _, integral_finsetSum _ fun l _ => (hI2 l i).const_mul _]
    simp_rw [integral_const_mul]
    simp only [pgGam, pgPack, PiLp.toLp_apply, Sum.elim_inr, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, Matrix.mul_apply, smul_eq_mul, integral_const, probReal_univ, one_smul, ← hNdef]
    have h1 : ∀ a b : Fin d, ∑ l, N a l * pgEpsMat K ρ x l b =
        ∑ l, N a l * ∫ g, pgFt K ρ x g * gstat g l b ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
          ∑ l, N a l * pgQs K x l b := by
      intro a b
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_sub, hE2 l b]
    rw [h1 i j, h1 j i]
    ring

theorem pgPack_sym_norm_le (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (a : Fin d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖pgPack (WithLp.toLp 2 ((pgMat x)⁻¹ *ᵥ a)) ((1 / 2 : ℝ) • ((pgMat x)⁻¹ * M + ((pgMat x)⁻¹ * M)ᵀ))‖ ^ 2 ≤
      (∑ i, a i ^ 2 + ∑ i, ∑ j, M i j ^ 2) / pgTmin d ρ ^ 2 := by
  set Ti := (pgMat x)⁻¹ with hTi
  set t := pgTmin d ρ with ht
  have htpos : 0 < t := by
    rw [ht, pgTmin]
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    have hsq : 0 < Real.sqrt (2 * Real.log (1 + ρ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have h_inv_raw := (pgDom_inv d ρ hd hρ x hx).2.2
  have h_inv (v : EuclideanSpace ℝ (Fin d)) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Ti v‖ ≤ ‖v‖ / t := by
    simpa [ht] using h_inv_raw v
  have h_norm_pgPack := pgSp_norm_sq (pgPack (WithLp.toLp 2 (Ti *ᵥ a)) ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ)))
  have h_mu := pgMu_pgPack (WithLp.toLp 2 (Ti *ᵥ a)) ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ))
  have h_mat := pgMat_pgPack (WithLp.toLp 2 (Ti *ᵥ a)) ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ))
  rw [h_norm_pgPack, h_mu, h_mat]
  -- Expand the vector norm squared
  have h_vec_norm : ‖WithLp.toLp 2 (Ti *ᵥ a)‖ ^ 2 = ∑ i, (Ti *ᵥ a) i ^ 2 := by
    calc
      ‖WithLp.toLp 2 (Ti *ᵥ a)‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (Ti *ᵥ a)).ofLp i‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      _ = ∑ i, ‖(Ti *ᵥ a) i‖ ^ 2 := by simp
      _ = ∑ i, (Ti *ᵥ a) i ^ 2 := by simp
  rw [h_vec_norm]
  -- Simplify the matrix sum
  have h_norm_sq_vec (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have h_mat_sum : ∑ i, ∑ j, ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ)) i j ^ 2 ≤ ∑ i, ∑ j, (Ti * M) i j ^ 2 := by
    have h_entry (i j : Fin d) : ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ)) i j ^ 2 ≤
        (1/2) * (((Ti * M) i j) ^ 2 + ((Ti * M) j i) ^ 2) := by
      calc
        ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ)) i j ^ 2
            = ((1/2) * ((Ti * M + (Ti * M)ᵀ) i j)) ^ 2 := by simp [Matrix.smul_apply]
        _ = ((1/2) * ((Ti * M) i j + ((Ti * M)ᵀ) i j)) ^ 2 := by rw [Matrix.add_apply]
        _ = ((1/2) * ((Ti * M) i j + (Ti * M) j i)) ^ 2 := by rw [Matrix.transpose_apply]
        _ = (1/4) * ((Ti * M) i j + (Ti * M) j i) ^ 2 := by ring
        _ ≤ (1/4) * (2 * (((Ti * M) i j) ^ 2 + ((Ti * M) j i) ^ 2)) := by
          gcongr
          exact add_sq_le
        _ = (1/2) * (((Ti * M) i j) ^ 2 + ((Ti * M) j i) ^ 2) := by ring
    calc
      ∑ i, ∑ j, ((1 / 2 : ℝ) • (Ti * M + (Ti * M)ᵀ)) i j ^ 2
          ≤ ∑ i, ∑ j, (1/2) * (((Ti * M) i j) ^ 2 + ((Ti * M) j i) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_entry i j
      _ = (1/2) * ∑ i, ∑ j, (((Ti * M) i j) ^ 2 + ((Ti * M) j i) ^ 2) := by
        simp [Finset.mul_sum]
      _ = (1/2) * (∑ i, ∑ j, ((Ti * M) i j) ^ 2 + ∑ i, ∑ j, ((Ti * M) j i) ^ 2) := by
        simp [Finset.sum_add_distrib]
      _ = (1/2) * (∑ i, ∑ j, ((Ti * M) i j) ^ 2 + ∑ i, ∑ j, ((Ti * M) i j) ^ 2) := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ((Ti * M) i j) ^ 2 := by ring
  -- Bound the vector part
  have h_vec_bound : ∑ i, (Ti *ᵥ a) i ^ 2 ≤ (∑ i, a i ^ 2) / t ^ 2 := by
    have h := h_inv (WithLp.toLp 2 a)
    rw [Matrix.toEuclideanCLM_toLp] at h
    -- h : ‖WithLp.toLp 2 (Ti.mulVec a)‖ ≤ ‖WithLp.toLp 2 a‖ / t
    have h_nonneg_left : 0 ≤ ‖WithLp.toLp 2 (Ti *ᵥ a)‖ := norm_nonneg _
    have h_nonneg_right : 0 ≤ ‖WithLp.toLp 2 a‖ / t := by
      have h_norm_nonneg : 0 ≤ ‖WithLp.toLp 2 a‖ := norm_nonneg _
      have ht_nonneg : 0 ≤ t := by linarith
      positivity
    have h_sq : ‖WithLp.toLp 2 (Ti *ᵥ a)‖ ^ 2 ≤ (‖WithLp.toLp 2 a‖ / t) ^ 2 := by
      nlinarith
    have h_left : ‖WithLp.toLp 2 (Ti *ᵥ a)‖ ^ 2 = ∑ i, (Ti *ᵥ a) i ^ 2 := h_vec_norm
    have h_right : (‖WithLp.toLp 2 a‖ / t) ^ 2 = (∑ i, a i ^ 2) / t ^ 2 := by
      have h_norm_a : ‖WithLp.toLp 2 a‖ ^ 2 = ∑ i, a i ^ 2 := h_norm_sq_vec _
      calc
        (‖WithLp.toLp 2 a‖ / t) ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 / t ^ 2 := by ring
        _ = (∑ i, a i ^ 2) / t ^ 2 := by rw [h_norm_a]
    rw [h_left, h_right] at h_sq
    exact h_sq
  -- Bound the matrix part column by column
  have h_mat_bound : ∑ i, ∑ j, (Ti * M) i j ^ 2 ≤ (∑ i, ∑ j, M i j ^ 2) / t ^ 2 := by
    have h_col_eq (j : Fin d) : (fun i => (Ti * M) i j) = Ti.mulVec (fun k => M k j) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    calc
      ∑ i, ∑ j, (Ti * M) i j ^ 2 = ∑ j, ∑ i, (Ti * M) i j ^ 2 := Finset.sum_comm
      _ = ∑ j, ∑ i, (Ti.mulVec (fun k => M k j)) i ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← congrFun (h_col_eq j) i]
      _ = ∑ j, ‖WithLp.toLp 2 (Ti.mulVec (fun k => M k j))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h_norm_sq_vec (WithLp.toLp 2 (Ti.mulVec (fun k => M k j)))]
      _ ≤ ∑ j, (‖WithLp.toLp 2 (fun k => M k j)‖ / t) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := h_inv (WithLp.toLp 2 (fun k => M k j))
        rw [Matrix.toEuclideanCLM_toLp] at h
        have h_nonneg_left : 0 ≤ ‖WithLp.toLp 2 (Ti.mulVec (fun k => M k j))‖ := norm_nonneg _
        have h_nonneg_right : 0 ≤ ‖WithLp.toLp 2 (fun k => M k j)‖ / t := by
          have h_norm_nonneg : 0 ≤ ‖WithLp.toLp 2 (fun k => M k j)‖ := norm_nonneg _
          have ht_nonneg : 0 ≤ t := by linarith
          positivity
        nlinarith
      _ = ∑ j, ((∑ k, M k j ^ 2) / t ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h_norm : ‖WithLp.toLp 2 (fun k => M k j)‖ ^ 2 = ∑ k, M k j ^ 2 := h_norm_sq_vec _
        calc
          (‖WithLp.toLp 2 (fun k => M k j)‖ / t) ^ 2 = ‖WithLp.toLp 2 (fun k => M k j)‖ ^ 2 / t ^ 2 := by ring
          _ = (∑ k, M k j ^ 2) / t ^ 2 := by rw [h_norm]
      _ = (∑ i, ∑ j, M i j ^ 2) / t ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_comm]
  -- Combine the bounds
  have h_total : ∑ i, (Ti *ᵥ a) i ^ 2 + ∑ i, ∑ j, (Ti * M) i j ^ 2 ≤
      (∑ i, a i ^ 2) / t ^ 2 + (∑ i, ∑ j, M i j ^ 2) / t ^ 2 := by
    nlinarith
  -- Final simplification
  have h_final : (∑ i, a i ^ 2) / t ^ 2 + (∑ i, ∑ j, M i j ^ 2) / t ^ 2 =
      (∑ i, a i ^ 2 + ∑ i, ∑ j, M i j ^ 2) / t ^ 2 := by
    ring
  rw [h_final] at h_total
  nlinarith

theorem pgV_bias (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq) (hVec : VecCS)
    (hMat : MatCS) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    ‖∫ g, pgV K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgGam K x‖ ≤ pgBeta d ρ := by
  have hsub := pgV_mean_sub hPT hLB hD4 hEta d ρ hd hρ K hK x hx
  have hpsn := pgPack_sym_norm_le d ρ hd hρ x hx
  have hEps := pgEps_sq hPT hLB hD4 d ρ hd hρ K hK x hx
  rcases hEps with ⟨hMemLp, hEpsSq⟩
  have hvec := hVec d (pgEps K ρ x) hMemLp
  have hmat := hMat d (pgEps K ρ x) hMemLp
  -- Each component of the identity is in L^2 (using the fact that stdGaussian is a Gaussian measure)
  have hMemLp_comp (i : Fin d) : MemLp (fun g : EuclideanSpace ℝ (Fin d) => g i) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have hMemLp_id : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 2 (by norm_num : (2 : ENNReal) ≠ ⊤)
    -- The projection fun v => v i is a continuous linear map, hence preserves L^p
    let proj : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin d => ℝ) i
    exact proj.comp_memLp' hMemLp_id
  -- The product pgEps * (fun g => g i) is integrable for each i
  have hInteg_comp (i : Fin d) : Integrable (fun g : EuclideanSpace ℝ (Fin d) => pgEps K ρ x g * g i) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have hProd := MeasureTheory.MemLp.integrable_mul hMemLp (hMemLp_comp i)
    simpa [Pi.mul_def] using hProd
  -- Now we can pull components out of the Bochner integral
  let I := ∫ g, pgEps K ρ x g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
  have hInteg_comp' (i : Fin d) : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (pgEps K ρ x g • g).ofLp i) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simpa [Pi.smul_apply', smul_eq_mul] using hInteg_comp i
  have hI_ofLp (i : Fin d) : (I : EuclideanSpace ℝ (Fin d)) i = ∫ g, pgEps K ρ x g * g i ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_int := MeasureTheory.eval_integral_piLp (fun i => hInteg_comp' i) i
    -- h_int : (∫ g, (pgEps K ρ x g • g) ∂μ).ofLp i = ∫ g, (pgEps K ρ x g • g).ofLp i ∂μ
    -- We need: I i = ∫ g, pgEps K ρ x g * g i
    -- Note: (pgEps K ρ x g • g).ofLp i = pgEps K ρ x g * g i
    simpa [I, Pi.smul_apply', smul_eq_mul] using h_int
  have hEpsVec_norm_sq_eq : (∑ i : Fin d, (pgEpsVec K ρ x) i ^ 2) = ‖I‖ ^ 2 := by
    calc
      (∑ i : Fin d, (pgEpsVec K ρ x) i ^ 2) = (∑ i : Fin d, (∫ g, pgEps K ρ x g * g i ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ^ 2) := by
        simp [pgEpsVec]
      _ = (∑ i : Fin d, (I i) ^ 2) := by
        simp [hI_ofLp]
      _ = ‖I‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp
  have hsum1 : (∑ i : Fin d, (pgEpsVec K ρ x) i ^ 2) ≤ pgU d ρ ^ 2 := by
    rw [hEpsVec_norm_sq_eq]
    calc
      ‖I‖ ^ 2 ≤ ∫ g, (pgEps K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        simpa [I] using hvec
      _ ≤ pgU d ρ ^ 2 := hEpsSq
  have hsum2 : (∑ i : Fin d, ∑ j : Fin d, (pgEpsMat K ρ x) i j ^ 2) ≤ 2 * pgU d ρ ^ 2 := by
    calc
      (∑ i : Fin d, ∑ j : Fin d, (pgEpsMat K ρ x) i j ^ 2) =
        (∑ i : Fin d, ∑ j : Fin d, (∫ g, gstat g i j * pgEps K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ^ 2) := by
        simp [pgEpsMat, gstat]
      _ ≤ 2 * ∫ g, (pgEps K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := hmat
      _ ≤ 2 * pgU d ρ ^ 2 := by nlinarith
  have hnum : (∑ i : Fin d, (pgEpsVec K ρ x) i ^ 2 + ∑ i : Fin d, ∑ j : Fin d, (pgEpsMat K ρ x) i j ^ 2) ≤ 3 * pgU d ρ ^ 2 := by
    nlinarith
  have hnorm_sq : ‖∫ g, pgV K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgGam K x‖ ^ 2 ≤ (pgBeta d ρ) ^ 2 := by
    rw [hsub]
    have h1 := hpsn (pgEpsVec K ρ x) (pgEpsMat K ρ x)
    calc
      ‖pgPack (WithLp.toLp 2 ((pgMat x)⁻¹ *ᵥ pgEpsVec K ρ x))
        ((1 / 2 : ℝ) • ((pgMat x)⁻¹ * pgEpsMat K ρ x + ((pgMat x)⁻¹ * pgEpsMat K ρ x)ᵀ))‖ ^ 2
          ≤ (∑ i : Fin d, (pgEpsVec K ρ x) i ^ 2 + ∑ i : Fin d, ∑ j : Fin d, (pgEpsMat K ρ x) i j ^ 2) / pgTmin d ρ ^ 2 := h1
      _ ≤ (3 * pgU d ρ ^ 2) / pgTmin d ρ ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = 3 * (pgU d ρ ^ 2 / pgTmin d ρ ^ 2) := by ring
      _ = (Real.sqrt 3 * pgU d ρ / pgTmin d ρ) ^ 2 := by
        have h3 : (0 : ℝ) ≤ 3 := by norm_num
        calc
          3 * (pgU d ρ ^ 2 / pgTmin d ρ ^ 2) = (Real.sqrt 3) ^ 2 * (pgU d ρ ^ 2 / pgTmin d ρ ^ 2) := by
            rw [Real.sq_sqrt h3]
          _ = ((Real.sqrt 3) * pgU d ρ / pgTmin d ρ) ^ 2 := by ring
      _ = (pgBeta d ρ) ^ 2 := rfl
  have hbeta_nonneg : 0 ≤ pgBeta d ρ := by
    have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hU : 0 ≤ pgU d ρ := by
      have hEtaSq := hEta (d : ℝ) ρ (by exact_mod_cast hd) hρ
      rcases hEtaSq with ⟨hEta_nonneg, hEta_sq⟩
      have hLD : 0 ≤ pgLD ρ := by
        unfold pgLD pgKappa pgPB
        have hρ' : 0 ≤ ρ := by linarith
        nlinarith
      have hsqrt : 0 ≤ 1 + Real.sqrt (d : ℝ) := by
        have hsq : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
        nlinarith
      have hEta_nonneg' : 0 ≤ pgEta d ρ := hEta_nonneg
      unfold pgU
      apply mul_nonneg
      · apply mul_nonneg hEta_nonneg' hLD
      · exact hsqrt
    have hTmin : 0 ≤ pgTmin d ρ := by
      unfold pgTmin
      have hdpos : 0 ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le _)
      have hLam_nonneg : 0 ≤ pgLam ρ := by
        unfold pgLam
        have hpos : 1 ≤ 1 + ρ := by linarith
        have hlog : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg hpos
        have h2 : 0 ≤ (2 : ℝ) := by norm_num
        have hprod : 0 ≤ 2 * Real.log (1 + ρ) := by nlinarith
        exact Real.sqrt_nonneg _
      have hnum : (0 : ℝ) ≤ 1 := by norm_num
      have hden : 0 ≤ 9 * (d : ℝ) * pgLam ρ := by
        apply mul_nonneg
        · apply mul_nonneg (by norm_num : 0 ≤ (9 : ℝ)) hdpos
        · exact hLam_nonneg
      exact div_nonneg hnum hden
    unfold pgBeta
    apply div_nonneg
    · apply mul_nonneg hsqrt3 hU
    · exact hTmin
  exact le_of_sq_le_sq hnorm_sq hbeta_nonneg

/-! ## Leaves: Corollary A and the test -/

theorem pgCorA (hAi : PropAi) (hAii : PropAii) (hAiii : PropAiii) (hD4 : D4Bounds) (hPAi : PgPropAi) (hCAi : PgCorAi)
    (hCAii : PgCorAii) (hCAiii : PgCorAiii) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d)
    (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (hstar : ℝ)
    (hmin : ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
      hstar ≤ posObj K pgKappa μ' A')
    (hx' : pgH K x ≤ hstar + pgEh d ρ) : PgComplete K ρ x := by
  let μ := pgMu x
  let T := pgOp x
  let κ := pgKappa
  let e := pgEh d ρ
  let L := pgLD ρ
  have hκ_pos : 0 < κ := by
    unfold κ pgKappa
    norm_num
  have hpos_body : IsPosBody K 1 ρ := pgBody_isPosBody K ρ hρ hK
  have hdet_info : (pgMat x).det ≠ 0 ∧ IsInvPair (pgOp x) (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹) ∧
    ∀ v, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹ v‖ ≤ ‖v‖ / pgTmin d ρ := pgDom_inv d ρ hd hρ x hx
  rcases hdet_info with ⟨hdet_mat, hinv, hnorm⟩
  have hdet_lin : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rcases hinv with ⟨h1, h2⟩
    have h_det_comp : LinearMap.det ((T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ∘ₗ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) =
      LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
      LinearMap.det (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      LinearMap.det_comp _ _
    have h1_lin : (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ∘ₗ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (pgMat x)⁻¹ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = LinearMap.id := by
      simpa using congrArg (fun (f : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =>
        (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) h1
    have h_det_id : LinearMap.det (LinearMap.id : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 := by simp
    rw [h1_lin, h_det_id] at h_det_comp
    intro hzero
    rw [hzero, zero_mul] at h_det_comp
    linarith
  have hL_nonneg : 0 ≤ L := by
    unfold L pgLD pgKappa pgPB
    positivity
  have hLip : LipschitzWith (Real.toNNReal L) (posF K μ T) := by
    rcases hK with ⟨hK_conv, hK_closed, hK_ball1, hK_ballρ⟩
    have h_dom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) μ T := hx
    have hD4_app := hD4 d K (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) μ T hK_conv hK_ball1
      (by
        dsimp [L, pgTmin]
        have hd_pos : 0 < (d : ℝ) := by
          have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        have hLam_pos : 0 < pgLam ρ := by
          unfold pgLam
          have hlog_pos : 0 < Real.log (1 + ρ) :=
            Real.log_pos (by linarith : 1 < 1 + ρ)
          positivity
        positivity) h_dom
    exact hD4_app.1
  have hx'_obj : posObj K κ μ T ≤ hstar + e := by
    unfold pgH at hx'
    simpa [κ, μ, T, e] using hx'
  -- Part (i): pgKs K x ≤ 1.05 * pgKappa
  have h_part1 : pgKs K x ≤ 1.05 * κ := by
    unfold pgKs
    by_cases hk_nonpos : posK K μ T ≤ 0
    · linarith [hκ_pos]
    · have hk_pos : 0 < posK K μ T := by linarith
      have hAi_app := hAi d K 1 ρ κ hstar e μ T hd hpos_body hκ_pos hdet_lin hmin hx'_obj hk_pos
      have hCAi_app := hCAi (d : ℝ) ρ (by exact_mod_cast hd) hρ
      have he_lt : e < 0.0012 * κ := by
        simpa [κ, pgKappa, e] using hCAi_app
      set x := posK K μ T / κ with hx_def
      have hx_pos : 0 < x := by
        rw [hx_def]
        exact div_pos hk_pos hκ_pos
      have h_ineq : κ * (x - 1 - Real.log x) ≤ e := by
        simpa [hx_def] using hAi_app
      have h_lt_0012 : x - 1 - Real.log x < 0.0012 := by
        have h_mul_lt : κ * (x - 1 - Real.log x) < 0.0012 * κ := by linarith
        have h_mul_lt' : κ * (x - 1 - Real.log x) < κ * 0.0012 := by
          simpa [mul_comm] using h_mul_lt
        exact lt_of_mul_lt_mul_left h_mul_lt' hκ_pos.le
      have hx_le_105 : x ≤ 1.05 := hPAi x hx_pos h_lt_0012
      rw [hx_def] at hx_le_105
      calc
        posK K μ T = (posK K μ T / κ) * κ := by field_simp [hκ_pos.ne.symm]
        _ ≤ 1.05 * κ := mul_le_mul_of_nonneg_right hx_le_105 hκ_pos.le
  -- Part (ii): ‖pgBs K x‖ ≤ pgTaub d ρ / 2
  have h_part2 : ‖pgBs K x‖ ≤ pgTaub d ρ / 2 := by
    unfold pgBs
    have hAiii_app := hAiii d K 1 ρ κ hstar e μ T hpos_body hdet_lin hmin hx'_obj
      (Real.toNNReal L) hLip
    have hAiii_app' : ‖posB K μ T‖ ^ 2 ≤ 2 * Real.sqrt (2 / Real.pi) * L * e := by
      simpa [hL_nonneg] using hAiii_app
    have h_sqrt_bound : 2 * Real.sqrt (2 / Real.pi) ≤ (1.6 : ℝ) := by
      have hπ_gt : (3.125 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
      have h_sq : (2 / Real.pi) ≤ (0.64 : ℝ) := by
        have hpos : 0 < Real.pi := Real.pi_pos
        have h_mul_lt : (0.64 : ℝ) * (3.125 : ℝ) < (0.64 : ℝ) * Real.pi :=
          mul_lt_mul_of_pos_left hπ_gt (by norm_num : (0 : ℝ) < 0.64)
        have h_lt : (2 : ℝ) < (0.64 : ℝ) * Real.pi := by
          have hcalc : (0.64 : ℝ) * (3.125 : ℝ) = 2 := by norm_num
          linarith
        have h_div_lt : 2 / Real.pi < 0.64 := by
          calc
            2 / Real.pi < ((0.64 : ℝ) * Real.pi) / Real.pi :=
              div_lt_div_of_pos_right h_lt hpos
            _ = 0.64 := by field_simp [hpos.ne.symm]
        exact h_div_lt.le
      have h_sqrt : Real.sqrt (2 / Real.pi) ≤ Real.sqrt (0.64 : ℝ) :=
        Real.sqrt_le_sqrt h_sq
      have h_sqrt_064 : Real.sqrt (0.64 : ℝ) = 0.8 := by norm_num
      calc
        2 * Real.sqrt (2 / Real.pi) ≤ 2 * Real.sqrt (0.64 : ℝ) := by nlinarith
        _ = 2 * (0.8 : ℝ) := by rw [h_sqrt_064]
        _ = (1.6 : ℝ) := by norm_num
    have h_mid : 2 * Real.sqrt (2 / Real.pi) * L * e ≤ 1.6 * L * e := by
      have he_nonneg : 0 ≤ e := by
        unfold e pgEh pgKappa
        positivity
      have h_nonneg_prod : 0 ≤ L * e := mul_nonneg hL_nonneg he_nonneg
      have h := mul_le_mul_of_nonneg_right h_sqrt_bound h_nonneg_prod
      simpa [mul_assoc] using h
    have hCAiii_app := hCAiii (d : ℝ) ρ (by exact_mod_cast hd) hρ
    have h_final : ‖posB K μ T‖ ^ 2 ≤ (pgTaub d ρ / 2) ^ 2 := by
      linarith
    have h_nonneg_b : 0 ≤ ‖posB K μ T‖ := norm_nonneg _
    have h_nonneg_taub : 0 ≤ pgTaub d ρ / 2 := by
      have : 0 ≤ pgTaub d ρ := by
        unfold pgTaub pgKappa
        have hLam_nonneg : 0 ≤ pgLam ρ := by
          unfold pgLam
          have hlog : 0 ≤ Real.log (1 + ρ) :=
            Real.log_nonneg (by linarith [hρ] : 1 ≤ 1 + ρ)
          positivity
        have hd_pos : 0 < (d : ℝ) := by
          have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        positivity
      positivity
    nlinarith
  -- Part (iii): ∀ v, 3 / 4 * (pgKappa / d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v
  have h_part3 : ∀ v, 3 / 4 * (κ / d) * ‖v‖ ^ 2 ≤ posQ K μ T v v := by
    intro v
    by_cases hv_zero : v = 0
    · subst hv_zero
      simp [posQ]
    · have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
      let u := (‖v‖⁻¹ : ℝ) • v
      have hu_norm : ‖u‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp [hv_norm_pos.ne.symm]
      have h_t_pos : (0 : ℝ) < 1/4 := by norm_num
      have h_t_lt_one : (1/4 : ℝ) < 1 := by norm_num
      have h_e_cond : e < ((1/4 : ℝ) ^ 2) * (κ / (d : ℝ)) ^ 2 / (2 * (pgC2 * (Real.toNNReal L) + κ / (d : ℝ))) := by
        have hCAii_app := hCAii (d : ℝ) ρ (by exact_mod_cast hd) hρ
        have h_eq : ((1/4 : ℝ) ^ 2) * (κ / (d : ℝ)) ^ 2 / (2 * (pgC2 * (Real.toNNReal L) + κ / (d : ℝ))) =
            κ ^ 2 / (32 * (d : ℝ) ^ 2 * (pgC2 * L + κ / (d : ℝ))) := by
          have hL_eq : (Real.toNNReal L : ℝ) = L := by
            rw [Real.coe_toNNReal _ hL_nonneg]
          have hd_ne_zero : (d : ℝ) ≠ 0 := by
            have : 1 ≤ (d : ℝ) := by exact_mod_cast hd
            linarith
          rw [hL_eq]
          field_simp [hd_ne_zero]
          ring
        -- hCAii_app: e < κ^2 / (32 * d^2 * (pgC2 * L + κ/d))
        -- h_eq: (1/4)^2 * (κ/d)^2 / (2 * (pgC2 * (Real.toNNReal L) + κ/d)) = κ^2 / (32 * d^2 * (pgC2 * L + κ/d))
        -- So the goal follows from hCAii_app by rewriting
        -- The goal is: e < LHS
        -- hCAii_app gives: e < RHS
        -- h_eq: LHS = RHS
        -- So we rewrite the goal using h_eq to get e < RHS, which is hCAii_app
        rw [h_eq]
        exact hCAii_app
      have hAii_app := hAii d K 1 ρ κ hstar e (1/4) μ T hd hpos_body hκ_pos hdet_lin hmin hx'_obj
        (Real.toNNReal L) hLip h_t_pos h_t_lt_one h_e_cond
      have h_bound_u : (1 - (1/4 : ℝ)) * (κ / d) ≤ posQ K μ T u u :=
        hAii_app u hu_norm
      have h_34 : (1 - (1/4 : ℝ)) = (3/4 : ℝ) := by norm_num
      rw [h_34] at h_bound_u
      have h_posQ_homog : posQ K μ T v v = ‖v‖ ^ 2 * posQ K μ T u u := by
        -- First, note that v = ‖v‖ • u since u = ‖v‖⁻¹ • v
        have hv_eq : v = ‖v‖ • u := by
          dsimp [u]
          calc
            v = 1 • v := by rw [one_smul]
            _ = (‖v‖ * (‖v‖⁻¹ : ℝ)) • v := by
              simp [hv_norm_pos.ne.symm]
            _ = ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) := by rw [smul_smul]
        -- Now use homogeneity of posQ in the first argument
        have h_homog1 : ∀ (c : ℝ) (a b : EuclideanSpace ℝ (Fin d)),
            posQ K μ T (c • a) b = c * posQ K μ T a b := by
          intro c a b
          unfold posQ
          have h1 : (fun (g : EuclideanSpace ℝ (Fin d)) =>
            (⟪c • a, g⟫ * ⟪b, g⟫ - ⟪c • a, b⟫) * posF K μ T g) =
            (fun g => c * ((⟪a, g⟫ * ⟪b, g⟫ - ⟪a, b⟫) * posF K μ T g)) := by
            ext g
            have h_inner1 : ⟪c • a, g⟫ = c * ⟪a, g⟫ := by
              rw [inner_smul_left]
              simp
            have h_inner2 : ⟪c • a, b⟫ = c * ⟪a, b⟫ := by
              rw [inner_smul_left]
              simp
            calc
              (⟪c • a, g⟫ * ⟪b, g⟫ - ⟪c • a, b⟫) * posF K μ T g
                  = ((c * ⟪a, g⟫) * ⟪b, g⟫ - (c * ⟪a, b⟫)) * posF K μ T g := by simp [h_inner1, h_inner2]
              _ = c * ((⟪a, g⟫ * ⟪b, g⟫ - ⟪a, b⟫) * posF K μ T g) := by ring
          rw [h1]
          rw [integral_const_mul]
        -- Use symmetry of posQ
        have h_symm : ∀ a b, posQ K μ T a b = posQ K μ T b a := by
          intro a b
          unfold posQ
          -- The integrand is symmetric: (⟪a,g⟫ * ⟪b,g⟫ - ⟪a,b⟫) = (⟪b,g⟫ * ⟪a,g⟫ - ⟪b,a⟫)
          -- because ⟪a,b⟫ = ⟪b,a⟫ and multiplication commutes
          refine integral_congr_ae ?_
          filter_upwards with g
          simp [mul_comm, sub_eq_add_neg, real_inner_comm]
        calc
          posQ K μ T v v = posQ K μ T (‖v‖ • u) v := by
            -- Only rewrite the first v, not the second
            exact congrArg (fun w => posQ K μ T w v) hv_eq
          _ = ‖v‖ * posQ K μ T u v := h_homog1 ‖v‖ u v
          _ = ‖v‖ * posQ K μ T v u := by rw [h_symm u v]
          _ = ‖v‖ * posQ K μ T (‖v‖ • u) u :=
            congrArg (fun w => ‖v‖ * posQ K μ T w u) hv_eq
          _ = ‖v‖ * (‖v‖ * posQ K μ T u u) := by rw [h_homog1 ‖v‖ u u]
          _ = ‖v‖ ^ 2 * posQ K μ T u u := by ring
      rw [h_posQ_homog]
      have h_sq_pos : 0 ≤ ‖v‖ ^ 2 := by positivity
      -- h_bound_u: 3/4 * (κ/d) ≤ posQ K μ T u u
      -- We need: 3/4 * (κ/d) * ‖v‖^2 ≤ ‖v‖^2 * posQ K μ T u u
      -- Using mul_le_mul_of_nonneg_right: a ≤ b → a*c ≤ b*c
      -- But this gives (3/4*(κ/d)) * ‖v‖^2 ≤ (posQ K μ T u u) * ‖v‖^2
      -- We need to commute the RHS
      have h_temp := mul_le_mul_of_nonneg_right h_bound_u h_sq_pos
      -- h_temp: (3/4*(κ/d)) * ‖v‖^2 ≤ (posQ K μ T u u) * ‖v‖^2
      -- We need: (3/4*(κ/d)) * ‖v‖^2 ≤ ‖v‖^2 * (posQ K μ T u u)
      -- These are equal by commutativity
      simpa [mul_comm] using h_temp
  exact ⟨h_part1, h_part2, h_part3⟩

theorem quad_le_frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∑ i, ∑ j, M i j ^ 2 ≤ c ^ 2) (v : EuclideanSpace ℝ (Fin d)) :
    |∑ i, ∑ j, v i * v j * M i j| ≤ c * ‖v‖ ^ 2 := by
  set S := ∑ i, ∑ j, v i * v j * M i j with hS
  set A := ‖v‖ ^ 2 with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    positivity
  have hcA_nonneg : 0 ≤ c * A := mul_nonneg hc hA_nonneg
  have hS_sq_le : S ^ 2 ≤ (c * A) ^ 2 := by
    rw [hS, hA]
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
      (λ p => v p.1 * v p.2) (λ p => M p.1 p.2)
    have h_sum_eq : (∑ i : Fin d, ∑ j : Fin d, v i * v j * M i j) =
                   (∑ p : Fin d × Fin d, (v p.1 * v p.2) * M p.1 p.2) := by
      calc
        (∑ i : Fin d, ∑ j : Fin d, v i * v j * M i j) =
            (∑ i ∈ (Finset.univ : Finset (Fin d)), ∑ j ∈ (Finset.univ : Finset (Fin d)), v i * v j * M i j) := by simp
        _ = (∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset (Fin d)), (v p.1 * v p.2) * M p.1 p.2) := by
          rw [Finset.sum_product]
        _ = (∑ p : Fin d × Fin d, (v p.1 * v p.2) * M p.1 p.2) := by simp
    have h_v_sq : (∑ p : Fin d × Fin d, (v p.1 * v p.2)^2) = (∑ i : Fin d, v i ^ 2)^2 := by
      calc
        (∑ p : Fin d × Fin d, (v p.1 * v p.2)^2) = (∑ p : Fin d × Fin d, v p.1 ^ 2 * v p.2 ^ 2) := by
          refine Finset.sum_congr rfl (λ p hp => ?_)
          ring
        _ = (∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset (Fin d)), v p.1 ^ 2 * v p.2 ^ 2) := by simp
        _ = (∑ i ∈ (Finset.univ : Finset (Fin d)), ∑ j ∈ (Finset.univ : Finset (Fin d)), v i ^ 2 * v j ^ 2) := by
          rw [Finset.sum_product]
        _ = (∑ i : Fin d, ∑ j : Fin d, v i ^ 2 * v j ^ 2) := by simp
        _ = (∑ i : Fin d, v i ^ 2) * (∑ j : Fin d, v j ^ 2) := by rw [Finset.sum_mul_sum]
        _ = (∑ i : Fin d, v i ^ 2)^2 := by ring
    have h_M_sq : (∑ p : Fin d × Fin d, M p.1 p.2 ^ 2) = (∑ i : Fin d, ∑ j : Fin d, M i j ^ 2) := by
      calc
        (∑ p : Fin d × Fin d, M p.1 p.2 ^ 2) = (∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset (Fin d)), M p.1 p.2 ^ 2) := by simp
        _ = (∑ i ∈ (Finset.univ : Finset (Fin d)), ∑ j ∈ (Finset.univ : Finset (Fin d)), M i j ^ 2) := by
          rw [Finset.sum_product]
        _ = (∑ i : Fin d, ∑ j : Fin d, M i j ^ 2) := by simp
    have h_norm_sq : ‖v‖ ^ 2 = (∑ i : Fin d, v i ^ 2) := by
      have h := EuclideanSpace.norm_sq_eq v
      simpa using h
    rw [h_sum_eq]
    calc
      (∑ p : Fin d × Fin d, (v p.1 * v p.2) * M p.1 p.2)^2
          ≤ (∑ p : Fin d × Fin d, (v p.1 * v p.2)^2) * (∑ p : Fin d × Fin d, M p.1 p.2 ^ 2) := h_cs
      _ = (∑ i : Fin d, v i ^ 2)^2 * (∑ i : Fin d, ∑ j : Fin d, M i j ^ 2) := by rw [h_v_sq, h_M_sq]
      _ ≤ (∑ i : Fin d, v i ^ 2)^2 * (c ^ 2) := by
        nlinarith
      _ = ((∑ i : Fin d, v i ^ 2) * c)^2 := by ring
      _ = (c * (∑ i : Fin d, v i ^ 2))^2 := by ring
      _ = (c * ‖v‖ ^ 2)^2 := by rw [h_norm_sq]
  exact abs_le_of_sq_le_sq hS_sq_le hcA_nonneg

theorem pgVerdict_iff {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    pgVerdict K ρ x w ↔ pgKh K ρ x w ≤ 1.075 * pgKappa ∧ ‖pgBh K ρ x w‖ ≤ 3 / 4 * pgTaub d ρ ∧
      ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (pgQh K ρ x w *ᵥ v) := by
  unfold pgVerdict pgKh pgBh pgQh; rfl

theorem pgVerdict_sound (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d)
    (hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hacc : PgAccurate K ρ x w) (hv : pgVerdict K ρ x w) : PgSound K ρ x := by
  rcases hacc with ⟨hacc1, hacc2, hacc3⟩
  rcases hv with ⟨hv1, hv2, hv3⟩
  have hd' : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hkappa_pos : 0 ≤ pgKappa := by
    -- pgKappa = 1/8 > 0
    unfold pgKappa
    positivity
  have hc_nonneg : 0 ≤ pgKappa / (8 * (d : ℝ)) := by
    positivity
  have h1 : pgKs K x ≤ 1.1 * pgKappa := by
    have hle : pgKs K x ≤ pgKh K ρ x w + pgKappa / 40 := by
      have := (abs_sub_le_iff.mp hacc1).2
      linarith
    have hbound : pgKh K ρ x w + pgKappa / 40 ≤ 1.075 * pgKappa + pgKappa / 40 := by
      have hv1' : pgKh K ρ x w ≤ 1.075 * pgKappa := by
        simpa [pgKh] using hv1
      linarith
    have hcalc : 1.075 * pgKappa + pgKappa / 40 = 1.1 * pgKappa := by
      unfold pgKappa
      ring
    linarith
  have h2 : ‖pgBs K x‖ ≤ pgTaub d ρ := by
    have htri : ‖pgBs K x‖ ≤ ‖pgBh K ρ x w‖ + ‖pgBh K ρ x w - pgBs K x‖ := by
      calc
        ‖pgBs K x‖ = ‖(pgBh K ρ x w) - (pgBh K ρ x w - pgBs K x)‖ := by simp
        _ ≤ ‖pgBh K ρ x w‖ + ‖pgBh K ρ x w - pgBs K x‖ := norm_sub_le _ _
    have hsum : ‖pgBh K ρ x w‖ + ‖pgBh K ρ x w - pgBs K x‖ ≤ 3/4 * pgTaub d ρ + pgTaub d ρ / 4 := by
      have hv2' : ‖pgBh K ρ x w‖ ≤ 3/4 * pgTaub d ρ := by
        simpa [pgBh] using hv2
      linarith
    have hcalc : 3/4 * pgTaub d ρ + pgTaub d ρ / 4 = pgTaub d ρ := by ring
    linarith
  have h3 : ∀ v, pgKappa / (2 * (d : ℝ)) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v := by
    intro v
    rw [hQ v]
    -- goal: pgKappa / (2 * (d : ℝ)) * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * v j * pgQs K x i j
    set Qh := pgQh K ρ x w
    set Qs := pgQs K x
    set M := Qh - Qs
    have hsum_eq : ∑ i, ∑ j, v i * v j * Qs i j = ∑ i, ∑ j, v i * v j * Qh i j - ∑ i, ∑ j, v i * v j * M i j := by
      calc
        ∑ i, ∑ j, v i * v j * Qs i j = ∑ i, ∑ j, v i * v j * (Qh i j - M i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp [M]
          ring
        _ = ∑ i, ∑ j, (v i * v j * Qh i j - v i * v j * M i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        _ = (∑ i, ∑ j, v i * v j * Qh i j) - (∑ i, ∑ j, v i * v j * M i j) := by
          simp [Finset.sum_sub_distrib]
    have hmain : 5/8 * (pgKappa / (d : ℝ)) * (v ⬝ᵥ v) ≤ ∑ i, ∑ j, v i * v j * Qh i j := by
      -- from hv3, and the identity ∑ v_i v_j Qh_ij = v ⬝ᵥ (Qh.mulVec v)
      have hid : ∑ i, ∑ j, v i * v j * Qh i j = v ⬝ᵥ (Qh.mulVec v) := by
        rw [Matrix.dotProduct_mulVec]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        calc
          ∑ i, v.ofLp i * v.ofLp j * Qh i j = ∑ i, (v.ofLp i * Qh i j) * v.ofLp j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          _ = (∑ i, v.ofLp i * Qh i j) * v.ofLp j := by rw [Finset.sum_mul]
          _ = (v.ofLp ᵥ* Qh) j * v.ofLp j := rfl
      rw [hid]
      -- now goal: 5/8 * (pgKappa / (d : ℝ)) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Qh.mulVec v)
      -- from hv3: 5/8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Qh *ᵥ v)
      -- but hv3 uses Fin d → ℝ, and v is EuclideanSpace; they are compatible
      simpa [Qh, pgQh] using hv3 v
    have herr : |∑ i, ∑ j, v i * v j * M i j| ≤ (pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2 := by
      have hMsq : ∑ i, ∑ j, M i j ^ 2 ≤ (pgKappa / (8 * (d : ℝ))) ^ 2 := by
        -- from hacc3: ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2
        -- and M = Qh - Qs
        dsimp [M]
        -- hacc3: ∑ i, ∑ j, (Qh i j - Qs i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2
        -- we need: ∑ i, ∑ j, (Qh i j - Qs i j) ^ 2 ≤ (pgKappa / (8 * (d : ℝ))) ^ 2
        -- the RHS uses (d : ℝ) vs d which is ℕ; need to cast
        simpa [div_eq_inv_mul] using hacc3
      have hpos : 0 ≤ pgKappa / (8 * (d : ℝ)) := hc_nonneg
      -- apply quad_le_frob
      have h := AdversarialBco.Poly.quad_le_frob M (pgKappa / (8 * (d : ℝ))) hpos hMsq v
      -- h: |∑ i, ∑ j, v.ofLp i * v.ofLp j * M i j| ≤ (pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2
      -- but we need |∑ i, ∑ j, v i * v j * M i j|, which is the same since v i = v.ofLp i
      simpa using h
    have hnorm_sq : v ⬝ᵥ v = ‖v‖ ^ 2 := by
      calc
        v.ofLp ⬝ᵥ v.ofLp = ∑ x, v.ofLp x * v.ofLp x := rfl
        _ = ∑ x, v.ofLp x ^ 2 := by simp [sq]
        _ = ‖v‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
    rw [hnorm_sq] at hmain
    -- Now we have:
    -- hmain: 5/8 * (pgKappa / (d : ℝ)) * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * v j * Qh i j
    -- herr: |∑ i, ∑ j, v i * v j * M i j| ≤ (pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2
    -- hsum_eq: ∑ i, ∑ j, v i * v j * Qs i j = (∑ i, ∑ j, v i * v j * Qh i j) - (∑ i, ∑ j, v i * v j * M i j)
    rw [hsum_eq]
    -- goal: pgKappa / (2 * (d : ℝ)) * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, v i * v j * Qh i j) - (∑ i, ∑ j, v i * v j * M i j)
    have hpos_sq : 0 ≤ ‖v‖ ^ 2 := by positivity
    have herr_abs := abs_le.mp herr
    rcases herr_abs with ⟨herr_low, herr_high⟩
    -- herr_low: -(pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * v j * M i j
    -- herr_high: ∑ i, ∑ j, v i * v j * M i j ≤ (pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2
    have hineq : pgKappa / (2 * (d : ℝ)) * ‖v‖ ^ 2 ≤ (5/8 * (pgKappa / (d : ℝ)) * ‖v‖ ^ 2) - (pgKappa / (8 * (d : ℝ))) * ‖v‖ ^ 2 := by
      ring_nf
      nlinarith [hkappa_pos, hd']
    -- From hmain: 5/8 * (pgKappa / d) * ‖v‖^2 ≤ sum Qh
    -- From herr_low: -sum M ≤ pgKappa/(8*d) * ‖v‖^2, so sum Qh - sum M ≥ sum Qh - pgKappa/(8*d) * ‖v‖^2
    -- And sum Qh - pgKappa/(8*d) * ‖v‖^2 ≥ 5/8 * (pgKappa/d) * ‖v‖^2 - pgKappa/(8*d) * ‖v‖^2
    -- And we just showed pgKappa/(2*d) * ‖v‖^2 ≤ that
    nlinarith
  exact And.intro h1 (And.intro h2 h3)

theorem pgVerdict_complete (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d)
    (hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hacc : PgAccurate K ρ x w) (hc : PgComplete K ρ x) :
    pgVerdict K ρ x w := by
  rcases hacc with ⟨hkh, hbh, hqh⟩
  rcases hc with ⟨hks, hbs, hqs⟩
  have hkh_le : pgKh K ρ x w ≤ 1.075 * pgKappa := by
    have h := abs_le.mp hkh
    have h' : pgKh K ρ x w - pgKs K x ≤ pgKappa / 40 := h.right
    linarith
  have hbh_le : ‖pgBh K ρ x w‖ ≤ 3 / 4 * pgTaub d ρ := by
    have h := calc
      ‖pgBh K ρ x w‖ = ‖(pgBh K ρ x w - pgBs K x) + pgBs K x‖ := by simp
      _ ≤ ‖pgBh K ρ x w - pgBs K x‖ + ‖pgBs K x‖ := norm_add_le _ _
      _ ≤ pgTaub d ρ / 4 + pgTaub d ρ / 2 := by nlinarith
      _ = 3 / 4 * pgTaub d ρ := by ring
    exact h
  have hqh_le : ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (pgQh K ρ x w *ᵥ v) := by
    intro v
    let v' : EuclideanSpace ℝ (Fin d) := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm v
    have hv_ofLp_eq_v : v'.ofLp = v := by ext i; rfl
    have hv_norm_sq : ‖v'‖ ^ 2 = v ⬝ᵥ v := by
      have h_inner : inner ℝ v' v' = ‖v'‖ ^ 2 := real_inner_self_eq_norm_sq v'
      have h_inner_v : inner ℝ v' v' = v ⬝ᵥ v := by
        simp [dotProduct, inner, v']
      linarith
    have hposQ : 3 / 4 * (pgKappa / d) * ‖v'‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v' v' := hqs v'
    have hQ_eq : posQ K (pgMu x) (pgOp x) v' v' = ∑ i, ∑ j, v' i * v' j * pgQs K x i j := hQ v'
    have hQs_ineq : 3 / 4 * (pgKappa / d) * (v ⬝ᵥ v) ≤ ∑ i, ∑ j, v i * v j * pgQs K x i j := by
      calc
        3 / 4 * (pgKappa / d) * (v ⬝ᵥ v) = 3 / 4 * (pgKappa / d) * ‖v'‖ ^ 2 := by rw [hv_norm_sq]
        _ ≤ posQ K (pgMu x) (pgOp x) v' v' := hposQ
        _ = ∑ i, ∑ j, v' i * v' j * pgQs K x i j := hQ_eq
        _ = ∑ i, ∑ j, v i * v j * pgQs K x i j := by simp [v']
    have h_sum_eq : v ⬝ᵥ (pgQh K ρ x w *ᵥ v) = ∑ i, ∑ j, v i * v j * pgQh K ρ x w i j := by
      simp [dotProduct, Matrix.mulVec_apply, Finset.mul_sum, mul_comm, mul_assoc]
    have h_diff_eq : ∑ i, ∑ j, v i * v j * (pgQh K ρ x w i j - pgQs K x i j) =
        (∑ i, ∑ j, v i * v j * pgQh K ρ x w i j) - (∑ i, ∑ j, v i * v j * pgQs K x i j) := by
      simp [Finset.sum_sub_distrib, mul_sub]
    have hQh_diff : |∑ i, ∑ j, v i * v j * (pgQh K ρ x w i j - pgQs K x i j)| ≤ (pgKappa / (8 * d)) * (v ⬝ᵥ v) := by
      have h_sq : ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2 := hqh
      have h_nonneg : 0 ≤ pgKappa / (8 * d) := by
        have hkappa : 0 ≤ pgKappa := by unfold pgKappa; norm_num
        have hdpos : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        positivity
      have h_quad := quad_le_frob (pgQh K ρ x w - pgQs K x) (pgKappa / (8 * d)) h_nonneg h_sq v'
      -- h_quad : |∑ i, ∑ j, v'.ofLp i * v'.ofLp j * ((pgQh K ρ x w - pgQs K x) i j)| ≤ (pgKappa / (8 * d)) * ‖v'‖ ^ 2
      convert h_quad using 1
      · -- LHS: replace v'.ofLp with v
        simp [hv_ofLp_eq_v]
      · -- RHS: replace ‖v'‖ ^ 2 with v ⬝ᵥ v
        rw [hv_norm_sq]
    have h_lower : ∑ i, ∑ j, v i * v j * pgQs K x i j -
        (pgKappa / (8 * d)) * (v ⬝ᵥ v) ≤ ∑ i, ∑ j, v i * v j * pgQh K ρ x w i j := by
      have h_abs := abs_le.mp hQh_diff
      -- h_abs.left : -(pgKappa / (8 * d) * (v ⬝ᵥ v)) ≤ sum_diff
      have h_diff_lower : -(pgKappa / (8 * d)) * (v ⬝ᵥ v) ≤
          ∑ i, ∑ j, v i * v j * (pgQh K ρ x w i j - pgQs K x i j) := by
        linarith
      rw [h_diff_eq] at h_diff_lower
      linarith
    calc
      5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) = (3 / 4 * (pgKappa / d) * (v ⬝ᵥ v)) - (pgKappa / (8 * d)) * (v ⬝ᵥ v) := by ring
      _ ≤ (∑ i, ∑ j, v i * v j * pgQs K x i j) - (pgKappa / (8 * d)) * (v ⬝ᵥ v) := by
        nlinarith
      _ ≤ ∑ i, ∑ j, v i * v j * pgQh K ρ x w i j := h_lower
      _ = v ⬝ᵥ (pgQh K ρ x w *ᵥ v) := by rw [h_sum_eq]
  unfold pgVerdict
  exact And.intro hkh_le (And.intro hbh_le hqh_le)

/-! ## Leaves: Lemma T -/

theorem pgFt_moments (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    MemLp (fun g => pgFt K ρ x g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ g, pgFt K ρ x g ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2 ∧
      MemLp (fun g => pgFt K ρ x g • g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ g, ‖pgFt K ρ x g • g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3)) ∧
      MemLp (fun g => (WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
          EuclideanSpace ℝ (Fin d × Fin d))) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ g, ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
          EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5)) := by
  rcases hK with ⟨hConv, hClosed, hBall1, hBallρ⟩
  rcases hx with ⟨hSelfAdj, hMuBound, hTBounds⟩
  have hTLower (v : EuclideanSpace ℝ (Fin d)) : pgTmin d ρ * ‖v‖ ^ 2 ≤ ⟪(pgOp x) v, v⟫ := (hTBounds v).1
  have hTUpper (v : EuclideanSpace ℝ (Fin d)) : ⟪(pgOp x) v, v⟫ ≤ pgLD ρ * ‖v‖ ^ 2 := (hTBounds v).2
  have hdpos : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdpos' : 0 < (d : ℝ) := by
    have : 0 < (d : ℕ) := Nat.one_pos.trans_le hd
    exact_mod_cast this
  have hρpos : 0 < ρ := by linarith
  have hKappa_pos : 0 < pgKappa := by
    rw [pgKappa]
    norm_num
  have hPB_pos : 0 < pgPB := by
    rw [pgPB]
    norm_num
  have hLam_pos : 0 < pgLam ρ := by
    rw [pgLam]
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hTmin_pos : 0 < pgTmin d ρ := by
    rw [pgTmin]
    refine div_pos (by norm_num) (by nlinarith)
  have hLD_pos : 0 < pgLD ρ := by
    rw [pgLD]
    have h : 0 < pgKappa * pgPB * ρ := by
      positivity
    exact h
  have hDelta_pos : 0 < pgDelta d ρ := by
    rw [pgDelta]
    positivity
  have hEta_pos : 0 < pgEta d ρ := by
    rw [pgEta]
    have h_num : 0 < pgEh d ρ * pgTmin d ρ := by
      have hEh : 0 < pgEh d ρ := by
        rw [pgEh]
        positivity
      positivity
    have h_den : 0 < 7 * pgLD ρ * (1 + Real.sqrt d) * pgDelta d ρ := by
      positivity
    exact div_pos h_num h_den
  have hEta_nonneg : 0 ≤ pgEta d ρ := le_of_lt hEta_pos
  have hEta_sq : (1 + pgEta d ρ) ^ 2 ≤ 5 / 4 := (hEta d ρ (by exact_mod_cast hd) hρ).2
  have hJbound : ρ / (2 ^ pgJb d ρ : ℝ) ≤ pgEta d ρ := by
    have hlogb : Real.logb 2 (ρ / pgEta d ρ) ≤ (pgJb d ρ : ℝ) := by
      have hceil := Nat.le_ceil (Real.logb 2 (ρ / pgEta d ρ))
      simpa [pgJb] using hceil
    have hpos_ratio : 0 < ρ / pgEta d ρ := div_pos hρpos hEta_pos
    have h_rpow : (2 : ℝ) ^ (Real.logb 2 (ρ / pgEta d ρ)) = ρ / pgEta d ρ := by
      refine Real.rpow_logb (by norm_num) (by norm_num) hpos_ratio
    have h_pow_le : (2 : ℝ) ^ (Real.logb 2 (ρ / pgEta d ρ)) ≤ (2 : ℝ) ^ (pgJb d ρ : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogb
    have h_div : ρ / pgEta d ρ ≤ (2 : ℝ) ^ (pgJb d ρ : ℝ) := by linarith
    have h_two_pow_pos : 0 < (2 : ℝ) ^ (pgJb d ρ : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    calc
      ρ / (2 ^ pgJb d ρ : ℝ) = (ρ / pgEta d ρ) * (pgEta d ρ / (2 ^ pgJb d ρ : ℝ)) := by
        field_simp [hEta_pos.ne.symm]
      _ ≤ ((2 : ℝ) ^ (pgJb d ρ : ℝ)) * (pgEta d ρ / (2 ^ pgJb d ρ : ℝ)) := by
        gcongr
      _ = pgEta d ρ := by
        rw [Real.rpow_natCast]
        field_simp [h_two_pow_pos.ne.symm, hEta_pos.ne.symm]
  have hLemmaB := hLB d K ρ hρ hConv hClosed hBall1 hBallρ (pgJb d ρ) (pgEta d ρ) hJbound
  have hLemmaB_x (x' : EuclideanSpace ℝ (Fin d)) :
      gauge K x' ≤ piTilde K ρ (pgJb d ρ) x' ∧
      piTilde K ρ (pgJb d ρ) x' ≤ gauge K x' + ‖x'‖ / (2 ^ pgJb d ρ : ℝ) ∧
      piTilde K ρ (pgJb d ρ) x' ≤ (1 + pgEta d ρ) * gauge K x' :=
    hLemmaB x'
  have hF_le_pgFt (g : EuclideanSpace ℝ (Fin d)) : posF K (pgMu x) (pgOp x) g ≤ pgFt K ρ x g := by
    dsimp [pgFt, posF]
    exact (hLemmaB_x (pgMu x + pgOp x g)).1
  have hpgFt_le_F (g : EuclideanSpace ℝ (Fin d)) : pgFt K ρ x g ≤ (1 + pgEta d ρ) * posF K (pgMu x) (pgOp x) g := by
    dsimp [pgFt, posF]
    have h := hLemmaB_x (pgMu x + pgOp x g)
    exact h.2.2
  have hT0_nonneg : 0 ≤ pgTmin d ρ := le_of_lt hTmin_pos
  have hIsPgDom : IsPgDom (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) := by
    refine ⟨hSelfAdj, hMuBound, ?_⟩
    intro v
    exact ⟨hTLower v, hTUpper v⟩
  have hD4App := hD4 d K (pgTmin d ρ) (pgLD ρ) (pgKappa * ρ) (pgMu x) (pgOp x) hConv hBall1 hT0_nonneg hIsPgDom
  have hF_lip : LipschitzWith (Real.toNNReal (pgLD ρ)) (posF K (pgMu x) (pgOp x)) := hD4App.1
  rcases hD4App with ⟨_, hFBound, hFInt⟩
  have hF_nonneg (g : EuclideanSpace ℝ (Fin d)) : 0 ≤ posF K (pgMu x) (pgOp x) g := (hFBound g).1
  have hF_bound (g : EuclideanSpace ℝ (Fin d)) : posF K (pgMu x) (pgOp x) g ≤ ‖pgMu x‖ + pgLD ρ * ‖g‖ :=
    (hFBound g).2
  have hMu_bound' : ‖pgMu x‖ ≤ pgLD ρ := by
    have h : pgKappa * ρ ≤ pgLD ρ := by
      rw [pgLD]
      have hPB : 1 ≤ pgPB := by
        rw [pgPB]
        norm_num
      calc
        pgKappa * ρ = (pgKappa * ρ) * 1 := by ring
        _ ≤ (pgKappa * ρ) * pgPB := by gcongr
        _ = pgKappa * pgPB * ρ := by ring
        _ = pgLD ρ := by rw [pgLD]
    linarith
  have hF_bound' (g : EuclideanSpace ℝ (Fin d)) : posF K (pgMu x) (pgOp x) g ≤ pgLD ρ * (1 + ‖g‖) := by
    have h := hF_bound g
    linarith
  have hpgFt_nonneg (g : EuclideanSpace ℝ (Fin d)) : 0 ≤ pgFt K ρ x g := by
    have := hF_nonneg g
    have h_le := hF_le_pgFt g
    linarith
  have hpgFt_linear_bound (g : EuclideanSpace ℝ (Fin d)) : pgFt K ρ x g ≤ (1 + pgEta d ρ) * pgLD ρ * (1 + ‖g‖) := by
    calc
      pgFt K ρ x g ≤ (1 + pgEta d ρ) * posF K (pgMu x) (pgOp x) g := hpgFt_le_F g
      _ ≤ (1 + pgEta d ρ) * (pgLD ρ * (1 + ‖g‖)) := by gcongr; exact hF_bound' g
      _ = (1 + pgEta d ρ) * pgLD ρ * (1 + ‖g‖) := by ring
  have hpgFt_sq_bound (g : EuclideanSpace ℝ (Fin d)) : pgFt K ρ x g ^ 2 ≤ 5 / 4 * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
    have h_le := hpgFt_linear_bound g
    have h_sq : ((1 + pgEta d ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 ≤ (5 / 4) * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by
      have h1 : (1 + pgEta d ρ) ^ 2 ≤ 5 / 4 := hEta_sq
      have h2 : (1 + ‖g‖) ^ 2 ≤ 2 * (1 + ‖g‖ ^ 2) := by
        have h := sq_nonneg (‖g‖ - 1)
        nlinarith
      have h_nonneg_L : 0 ≤ pgLD ρ := le_of_lt hLD_pos
      have h_nonneg_eta1 : 0 ≤ 1 + pgEta d ρ := by linarith
      calc
        ((1 + pgEta d ρ) * pgLD ρ * (1 + ‖g‖)) ^ 2 = ((1 + pgEta d ρ) ^ 2) * (pgLD ρ ^ 2) * ((1 + ‖g‖) ^ 2) := by ring
        _ ≤ (5 / 4) * (pgLD ρ ^ 2) * ((1 + ‖g‖) ^ 2) := by gcongr
        _ ≤ (5 / 4) * (pgLD ρ ^ 2) * (2 * (1 + ‖g‖ ^ 2)) := by gcongr
        _ = (5 / 4) * (2 * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) := by ring
    have h_nonneg_pgFt : 0 ≤ pgFt K ρ x g := hpgFt_nonneg g
    have h_nonneg_linear : 0 ≤ (1 + pgEta d ρ) * pgLD ρ * (1 + ‖g‖) := by
      positivity
    nlinarith
  have hMeas_pgFt : Measurable (fun g : EuclideanSpace ℝ (Fin d) => pgFt K ρ x g) := by
    have hMeas_piTilde : Measurable (piTilde K ρ (pgJb d ρ)) := hPT d K ρ hClosed (pgJb d ρ)
    have hMeas_affine : Measurable (fun g : EuclideanSpace ℝ (Fin d) => pgMu x + pgOp x g) := by
      refine (measurable_const.add ?_)
      exact (pgOp x).continuous.measurable
    exact hMeas_piTilde.comp hMeas_affine
  have hAEStrong_pgFt : AEStronglyMeasurable (fun g => pgFt K ρ x g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hMeas_pgFt.aestronglyMeasurable
  have hAEStrong_pgFt_sq : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => (pgFt K ρ x g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hAEStrong_pgFt.pow 2
  let C := 5 / 4 * (2 * pgLD ρ ^ 2)
  have h_int_dom : Integrable (fun g : EuclideanSpace ℝ (Fin d) => C * (1 + ‖g‖ ^ 2)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_int_one : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      integrable_const _
    have h_int_norm_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_mem : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
      have h_ae : AEStronglyMeasurable id (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        continuous_id.aestronglyMeasurable
      rw [memLp_two_iff_integrable_sq_norm h_ae] at h_mem
      simpa using h_mem
    refine (h_int_one.add h_int_norm_sq).const_mul C
  have hAEStrong_pgFt_sq : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => (pgFt K ρ x g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hAEStrong_pgFt.pow 2
  have h_int_pgFt_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (pgFt K ρ x g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine MeasureTheory.Integrable.mono' h_int_dom hAEStrong_pgFt_sq ?_
    filter_upwards with g
    have h := hpgFt_sq_bound g
    have h_nonneg_sq : 0 ≤ pgFt K ρ x g ^ 2 := pow_two_nonneg _
    have h_norm : ‖(pgFt K ρ x g) ^ 2‖ = (pgFt K ρ x g) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_sq]
    rw [h_norm]
    simpa [C, mul_assoc] using h
  have hMemLp_pgFt : MemLp (fun g => pgFt K ρ x g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [memLp_two_iff_integrable_sq_norm hAEStrong_pgFt]
    have h_eq : (fun g => ‖pgFt K ρ x g‖ ^ 2) = (fun g => (pgFt K ρ x g) ^ 2) := by
      ext g
      have h := hpgFt_nonneg g
      simp
    rw [h_eq]
    exact h_int_pgFt_sq
  have h_int_F_sq : Integrable (fun g : EuclideanSpace ℝ (Fin d) => (posF K (pgMu x) (pgOp x) g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_lip : LipschitzWith (Real.toNNReal (pgLD ρ)) (posF K (pgMu x) (pgOp x)) := hF_lip
    have h_meas : AEStronglyMeasurable (fun g => posF K (pgMu x) (pgOp x) g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      h_lip.continuous.aestronglyMeasurable
    have h_bound : ∀ g, |posF K (pgMu x) (pgOp x) g| ≤ pgLD ρ * (1 + ‖g‖) := by
      intro g
      rw [abs_le]
      have h_nonneg := hF_nonneg g
      have h_le := hF_bound' g
      have h_lower : -(pgLD ρ * (1 + ‖g‖)) ≤ posF K (pgMu x) (pgOp x) g := by
        linarith
      exact ⟨h_lower, h_le⟩
    have h_mem_dom : MemLp (fun g : EuclideanSpace ℝ (Fin d) => (1 : ℝ) + ‖g‖) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_id : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
      have h_norm : MemLp (fun g => ‖g‖) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := h_id.norm
      have h_const : MemLp (fun _ => (1 : ℝ)) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        MeasureTheory.memLp_const (1 : ℝ)
      exact h_const.add h_norm
    have h_mem : MemLp (fun g => posF K (pgMu x) (pgOp x) g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      MeasureTheory.MemLp.of_le_mul h_mem_dom h_meas (by
        filter_upwards with g
        have h := hF_bound' g
        have h_nonneg_F : 0 ≤ posF K (pgMu x) (pgOp x) g := hF_nonneg g
        have h_nonneg_dom : 0 ≤ (1 : ℝ) + ‖g‖ := by nlinarith [norm_nonneg g]
        rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_F, Real.norm_eq_abs, abs_of_nonneg h_nonneg_dom]
        exact h)
    have h_ae_sq : AEStronglyMeasurable (fun g => (posF K (pgMu x) (pgOp x) g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (h_lip.continuous.pow 2).aestronglyMeasurable
    have h_int_norm : Integrable (fun g => ‖(posF K (pgMu x) (pgOp x) g)‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      rwa [← memLp_two_iff_integrable_sq_norm h_meas]
    have h_eq : (fun g => ‖(posF K (pgMu x) (pgOp x) g)‖ ^ 2) = (fun g => (posF K (pgMu x) (pgOp x) g) ^ 2) := by
      ext g
      have h_nonneg : 0 ≤ posF K (pgMu x) (pgOp x) g := hF_nonneg g
      simp
    rwa [h_eq] at h_int_norm
  have h_int_pgFt_sq_bound : ∫ g, (pgFt K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2 := by
    have h_int_F_sq_bound : ∫ g, (posF K (pgMu x) (pgOp x) g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        (pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2 := by
      have h_R_le_L : pgKappa * ρ ≤ pgLD ρ := by
        rw [pgLD]
        have hPB : 1 ≤ pgPB := by
          rw [pgPB]
          norm_num
        calc
          pgKappa * ρ = (pgKappa * ρ) * 1 := by ring
          _ ≤ (pgKappa * ρ) * pgPB := by gcongr
          _ = pgKappa * pgPB * ρ := by ring
      have h_sqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have h_bound : ((pgKappa * ρ) + pgLD ρ * Real.sqrt (d : ℝ)) ^ 2 ≤ (pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2 := by
        have hR : pgKappa * ρ ≤ pgLD ρ := h_R_le_L
        have h_sq : (pgKappa * ρ) ^ 2 ≤ (pgLD ρ) ^ 2 := by gcongr
        have h_mul : (pgKappa * ρ) * (pgLD ρ * Real.sqrt (d : ℝ)) ≤ (pgLD ρ) * (pgLD ρ * Real.sqrt (d : ℝ)) := by gcongr
        nlinarith
      linarith [hFInt, h_bound]
    have h_pgFt_sq_le_F_sq : ∀ g, (pgFt K ρ x g) ^ 2 ≤ (1 + pgEta d ρ) ^ 2 * (posF K (pgMu x) (pgOp x) g) ^ 2 := by
      intro g
      have h := hpgFt_le_F g
      have h_nonneg_F : 0 ≤ posF K (pgMu x) (pgOp x) g := hF_nonneg g
      have h_nonneg_pgFt : 0 ≤ pgFt K ρ x g := hpgFt_nonneg g
      have h_nonneg_eta1 : 0 ≤ 1 + pgEta d ρ := by linarith
      calc
        (pgFt K ρ x g) ^ 2 ≤ ((1 + pgEta d ρ) * (posF K (pgMu x) (pgOp x) g)) ^ 2 := by gcongr
        _ = (1 + pgEta d ρ) ^ 2 * (posF K (pgMu x) (pgOp x) g) ^ 2 := by ring
    have h_int_rhs : Integrable (fun g => (1 + pgEta d ρ) ^ 2 * (posF K (pgMu x) (pgOp x) g) ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      h_int_F_sq.const_mul ((1 + pgEta d ρ) ^ 2)
    calc
      ∫ g, (pgFt K ρ x g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, (1 + pgEta d ρ) ^ 2 * (posF K (pgMu x) (pgOp x) g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine MeasureTheory.integral_mono h_int_pgFt_sq h_int_rhs h_pgFt_sq_le_F_sq
      _ = (1 + pgEta d ρ) ^ 2 * ∫ g, (posF K (pgMu x) (pgOp x) g) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 + pgEta d ρ) ^ 2 * ((pgLD ρ * (1 + Real.sqrt (d : ℝ))) ^ 2) := by gcongr
      _ ≤ (5 / 4) * (pgLD ρ ^ 2 * (1 + Real.sqrt (d : ℝ)) ^ 2) := by
        nlinarith [hEta_sq]
      _ = 5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2 := by ring
  -- Part 3: MemLp for pgFt • g
  have h_bound_smul_sq (g : EuclideanSpace ℝ (Fin d)) : ‖pgFt K ρ x g • g‖ ^ 2 ≤ ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) := by
    have h_sq : pgFt K ρ x g ^ 2 ≤ (5/2) * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2) := by
      have h := hpgFt_sq_bound g
      linarith
    calc
      ‖pgFt K ρ x g • g‖ ^ 2 = (pgFt K ρ x g) ^ 2 * ‖g‖ ^ 2 := by
        rw [norm_smul_of_nonneg (hpgFt_nonneg g) g]
        ring
      _ ≤ ((5/2) * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) * ‖g‖ ^ 2 := by gcongr
      _ = ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) := by ring
  have hAEStrong_smul : AEStronglyMeasurable (fun g => pgFt K ρ x g • g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hAEStrong_pgFt.smul continuous_id.aestronglyMeasurable
  have h_int_norm_sq_g : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    have h_ae : AEStronglyMeasurable id (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      continuous_id.aestronglyMeasurable
    have h := (integrable_norm_rpow_iff h_ae (by norm_num) (by norm_num)).mpr h_mem
    simpa [Real.rpow_natCast] using h
  have h_int_norm_four : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 4) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp id 4 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.memLp_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) 4 (by norm_num)
    have h_ae : AEStronglyMeasurable id (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      continuous_id.aestronglyMeasurable
    have h := (integrable_norm_rpow_iff h_ae (by norm_num) (by norm_num)).mpr h_mem
    simpa [Real.rpow_natCast] using h
  have h_int_dom_smul : Integrable (fun g => ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_sum : Integrable (fun g => (1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_sum_eq : ((fun (g : EuclideanSpace ℝ (Fin d)) => (1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) : EuclideanSpace ℝ (Fin d) → ℝ) = (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 2 + ‖g‖ ^ 4) := by
        ext g; ring
      rw [h_sum_eq]
      exact h_int_norm_sq_g.add h_int_norm_four
    exact h_sum.const_mul ((5/2) * pgLD ρ ^ 2)
  have hAEStrong_sq_smul : AEStronglyMeasurable (fun g => ‖pgFt K ρ x g • g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hAEStrong_smul.norm.pow 2
  have h_int_sq_smul : Integrable (fun g => ‖pgFt K ρ x g • g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' h_int_dom_smul hAEStrong_sq_smul ?_
    filter_upwards with g
    have h := h_bound_smul_sq g
    have h_nonneg : 0 ≤ ‖pgFt K ρ x g • g‖ ^ 2 := pow_two_nonneg _
    have h_norm : ‖‖pgFt K ρ x g • g‖ ^ 2‖ = ‖pgFt K ρ x g • g‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    rw [h_norm]
    exact h
  have hMemLp_pgFt_smul_g : MemLp (fun g => pgFt K ρ x g • g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [memLp_two_iff_integrable_sq_norm hAEStrong_smul]
    exact h_int_sq_smul
  -- Part 4: Integral bound for pgFt • g
  have h_int_pgFt_smul_g : ∫ g, ‖pgFt K ρ x g • g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3)) := by
    have h_sum_int : ∫ g, ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (d : ℝ) * (d + 3) := by
      calc
        ∫ g, ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
            ∫ g, (‖g‖ ^ 2 * (1 + ‖g‖ ^ 2)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          refine integral_congr_ae ?_
          filter_upwards with g
          ring
        _ = (d : ℝ) * (d + 3) := (hMom d).1
    have h_dom_int : ∫ g, ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ((5/2) * pgLD ρ ^ 2) * ((d : ℝ) * (d + 3)) := by
      rw [integral_const_mul, h_sum_int]
    calc
      ∫ g, ‖pgFt K ρ x g • g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * ‖g‖ ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine MeasureTheory.integral_mono h_int_sq_smul h_int_dom_smul h_bound_smul_sq
      _ = ((5/2) * pgLD ρ ^ 2) * ((d : ℝ) * (d + 3)) := h_dom_int
      _ = 5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 3)) := by ring
      _ = 5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3)) := by simp
  -- Part 5: MemLp for WithLp.toLp (pgFt * gstat)
  have h_meas_coord (i : Fin d) : Measurable (fun g : EuclideanSpace ℝ (Fin d) => g i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable
  have h_meas_gstat (i j : Fin d) : Measurable (fun g : EuclideanSpace ℝ (Fin d) => gstat g i j) := by
    dsimp [gstat]
    refine ((h_meas_coord i).mul (h_meas_coord j)).sub ?_
    by_cases h : i = j
    · simp [h]
    · simp [h]
  have h_meas_toLp_input : Measurable (fun g : EuclideanSpace ℝ (Fin d) =>
      fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2) := by
    refine measurable_pi_lambda fun p => hMeas_pgFt.mul (h_meas_gstat p.1 p.2)
  have h_meas_toLp_map : Measurable (WithLp.toLp 2 : ((Fin d × Fin d) → ℝ) → EuclideanSpace ℝ (Fin d × Fin d)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d × Fin d => ℝ)).measurable
  have hMeas_toLp : Measurable (fun g : EuclideanSpace ℝ (Fin d) =>
      (WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
        EuclideanSpace ℝ (Fin d × Fin d))) :=
    h_meas_toLp_map.comp h_meas_toLp_input
  have hAEStrong_toLp : AEStronglyMeasurable (fun g => (WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hMeas_toLp.aestronglyMeasurable
  have h_norm_toLp_sq (g : EuclideanSpace ℝ (Fin d)) : ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 = (pgFt K ρ x g) ^ 2 * (∑ p : Fin d × Fin d, gstat g p.1 p.2 ^ 2) := by
    calc
      ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
        EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 =
          ∑ p : Fin d × Fin d, ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
            EuclideanSpace ℝ (Fin d × Fin d)).ofLp p‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      _ = ∑ p : Fin d × Fin d, ‖pgFt K ρ x g * gstat g p.1 p.2‖ ^ 2 := by
        simp
      _ = ∑ p : Fin d × Fin d, (pgFt K ρ x g * gstat g p.1 p.2) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Real.norm_eq_abs, mul_pow, sq_abs, abs_of_nonneg (hpgFt_nonneg g)]
      _ = ∑ p : Fin d × Fin d, (pgFt K ρ x g) ^ 2 * (gstat g p.1 p.2) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      _ = (pgFt K ρ x g) ^ 2 * (∑ p : Fin d × Fin d, gstat g p.1 p.2 ^ 2) := by
        rw [Finset.mul_sum]
  have h_frob (g : EuclideanSpace ℝ (Fin d)) : ∑ p : Fin d × Fin d, gstat g p.1 p.2 ^ 2 = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ) := by
    have h := hFrob d g
    -- h: ∑ i, ∑ j, gstat g i j ^ 2 = ...
    -- goal: ∑ p : Fin d × Fin d, gstat g p.1 p.2 ^ 2 = ...
    calc
      ∑ p : Fin d × Fin d, gstat g p.1 p.2 ^ 2 = ∑ p ∈ (Finset.univ : Finset (Fin d × Fin d)), gstat g p.1 p.2 ^ 2 := by simp
      _ = ∑ p ∈ ((Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset (Fin d))), gstat g p.1 p.2 ^ 2 := by
        rw [Finset.univ_product_univ]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin d)), ∑ j ∈ (Finset.univ : Finset (Fin d)), gstat g i j ^ 2 := by
        rw [Finset.sum_product]
      _ = ∑ i : Fin d, ∑ j : Fin d, gstat g i j ^ 2 := by simp
      _ = ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ) := h
  have h_norm_toLp_sq' (g : EuclideanSpace ℝ (Fin d)) : ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 = (pgFt K ρ x g) ^ 2 * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) := by
    rw [h_norm_toLp_sq g, h_frob g]
  have h_bound_toLp_sq (g : EuclideanSpace ℝ (Fin d)) : ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 ≤ ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) := by
    have h_sq : pgFt K ρ x g ^ 2 ≤ (5/2) * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2) := by
      have h := hpgFt_sq_bound g
      linarith
    have h_frob_nonneg : 0 ≤ ‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ) := by
      have h := h_frob g
      rw [← h]
      refine Finset.sum_nonneg fun p _ => pow_two_nonneg _
    calc
      ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
        EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 = (pgFt K ρ x g) ^ 2 * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) := h_norm_toLp_sq' g
      _ ≤ ((5/2) * pgLD ρ ^ 2 * (1 + ‖g‖ ^ 2)) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) := by gcongr
      _ = ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) := by ring
  have h_int_norm_six : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 6) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_mem : MemLp id 6 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.memLp_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) 6 (by norm_num)
    have h_ae : AEStronglyMeasurable id (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      continuous_id.aestronglyMeasurable
    have h := (integrable_norm_rpow_iff h_ae (by norm_num) (by norm_num)).mpr h_mem
    simpa [Real.rpow_natCast] using h
  have h_int_dom_toLp : Integrable (fun g => ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_poly : Integrable (fun g => (1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have h_expand : ((fun (g : EuclideanSpace ℝ (Fin d)) => (1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) : EuclideanSpace ℝ (Fin d) → ℝ) =
          (fun (g : EuclideanSpace ℝ (Fin d)) => ‖g‖ ^ 6 - ‖g‖ ^ 4 + ((d : ℝ) - 2) * ‖g‖ ^ 2 + (d : ℝ)) := by
        ext g; ring
      rw [h_expand]
      refine ((h_int_norm_six.sub h_int_norm_four).add ((h_int_norm_sq_g.const_mul ((d : ℝ) - 2)))).add ?_
      exact integrable_const _
    exact h_poly.const_mul ((5/2) * pgLD ρ ^ 2)
  have hAEStrong_norm_toLp_sq : AEStronglyMeasurable (fun g =>
      ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
        EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hAEStrong_toLp.norm.pow 2
  have h_int_norm_toLp_sq : Integrable (fun g => ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' h_int_dom_toLp hAEStrong_norm_toLp_sq ?_
    filter_upwards with g
    have h := h_bound_toLp_sq g
    have h_nonneg : 0 ≤ ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 := pow_two_nonneg _
    have h_norm : ‖‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2‖ = ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    rw [h_norm]
    exact h
  have hMemLp_toLp : MemLp (fun g => (WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    rw [memLp_two_iff_integrable_sq_norm hAEStrong_toLp]
    exact h_int_norm_toLp_sq
  -- Part 6: Integral bound for WithLp.toLp
  have h_int_pgFt_toLp : ∫ g, ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
      EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5)) := by
    have h_poly_int : ∫ g, ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        (d : ℝ) * (d + 1) * (d + 5) := by
      calc
        ∫ g, ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
            ∫ g, ((‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ)) * (1 + ‖g‖ ^ 2)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          refine integral_congr_ae ?_
          filter_upwards with g
          ring
        _ = (d : ℝ) * (d + 1) * (d + 5) := (hMom d).2
    have h_dom_int : ∫ g, ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
        ((5/2) * pgLD ρ ^ 2) * ((d : ℝ) * (d + 1) * (d + 5)) := by
      rw [integral_const_mul, h_poly_int]
    calc
      ∫ g, ‖(WithLp.toLp 2 fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2 :
        EuclideanSpace ℝ (Fin d × Fin d))‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          ∫ g, ((5/2) * pgLD ρ ^ 2) * ((1 + ‖g‖ ^ 2) * (‖g‖ ^ 4 - 2 * ‖g‖ ^ 2 + (d : ℝ))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        refine MeasureTheory.integral_mono h_int_norm_toLp_sq h_int_dom_toLp h_bound_toLp_sq
      _ = ((5/2) * pgLD ρ ^ 2) * ((d : ℝ) * (d + 1) * (d + 5)) := h_dom_int
      _ = 5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5)) := by ring
      _ = 5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5)) := by simp
  exact ⟨hMemLp_pgFt, h_int_pgFt_sq_bound, hMemLp_pgFt_smul_g, h_int_pgFt_smul_g, hMemLp_toLp, h_int_pgFt_toLp⟩

theorem pgFt_bias (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq) (hVec : VecCS)
    (hMat : MatCS) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    |∫ g, pgFt K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgKs K x| ≤ pgU d ρ ∧
      ‖∫ g, pgFt K ρ x g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgBs K x‖ ≤ pgU d ρ ∧
      ∑ i, ∑ j, (∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgQs K x i j) ^ 2 ≤
        2 * pgU d ρ ^ 2 := by
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨hε2, hεU⟩ := pgEps_sq hPT hLB hD4 d ρ hd hρ K hK x hx
  have hU : 0 ≤ pgU d ρ := by
    have h1 := (hEta d ρ (by exact_mod_cast hd) hρ).1
    have h2 : 0 ≤ pgLD ρ := by unfold pgLD pgKappa pgPB; positivity
    unfold pgU; positivity
  have hτ0 : 0 ≤ pgTmin d ρ := by unfold pgTmin pgLam; positivity
  obtain ⟨hFL, -, -⟩ := d4_main d K _ _ _ (pgMu x) (pgOp x) hK.1 hK.2.2.1 hτ0 hx
  have hFi : Integrable (posF K (pgMu x) (pgOp x)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integrable_of_lipschitz _ _ hFL
  have hεi : Integrable (pgEps K ρ x) (stdGaussian (EuclideanSpace ℝ (Fin d))) := hε2.integrable one_le_two
  have hFt : ∀ g, pgFt K ρ x g = pgEps K ρ x g + posF K (pgMu x) (pgOp x) g := fun g => by
    unfold pgEps; ring
  have hsq : ∀ a : ℝ, a ^ 2 ≤ pgU d ρ ^ 2 → |a| ≤ pgU d ρ := fun a h => by
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hU] at this
  refine ⟨?_, ?_, ?_⟩
  · have he : ∫ g, pgFt K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgKs K x =
        ∫ g, pgEps K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      simp_rw [hFt]
      rw [integral_add hεi hFi]
      unfold pgKs posK; ring
    rw [he]
    refine hsq _ (le_trans ?_ hεU)
    have hv := ProbabilityTheory.variance_nonneg (pgEps K ρ x) (stdGaussian (EuclideanSpace ℝ (Fin d)))
    rw [ProbabilityTheory.variance_eq_sub hε2] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  · have hgi : MemLp (fun g : EuclideanSpace ℝ (Fin d) => g) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.memLp_two_id
    have hεg : Integrable (fun g => pgEps K ρ x g • g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have := hε2.smul (p := 2) (q := 2) (r := 1) hgi
      exact memLp_one_iff_integrable.1 this
    have hFg : Integrable (fun g => posF K (pgMu x) (pgOp x) g • g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      (integrable_moments _ _ hFL 0 0).2.2
    have he : ∫ g, pgFt K ρ x g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgBs K x =
        ∫ g, pgEps K ρ x g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      simp_rw [hFt, add_smul]
      rw [integral_add hεg hFg]
      unfold pgBs posB; abel
    rw [he]
    have h := hVec d (pgEps K ρ x) hε2
    have := hsq ‖∫ g, pgEps K ρ x g • g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖ (h.trans hεU)
    rwa [abs_norm] at this
  · have he : ∀ i j, ∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgQs K x i j =
        ∫ g, gstat g i j * pgEps K ρ x g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      intro i j
      have hgs : ∀ g : EuclideanSpace ℝ (Fin d),
          ⟪EuclideanSpace.single i (1 : ℝ), g⟫ * ⟪EuclideanSpace.single j (1 : ℝ), g⟫ -
            ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫ = gstat g i j := fun g => by
        simp only [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, gstat]
        simp
      have hFq : Integrable (fun g => gstat g i j * posF K (pgMu x) (pgOp x) g)
          (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        have := (integrable_moments _ _ hFL (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).2.1
        simpa only [hgs] using this
      have hgsm : MemLp (fun g : EuclideanSpace ℝ (Fin d) => gstat g i j) 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        have hm : Measurable (fun g : EuclideanSpace ℝ (Fin d) => gstat g i j) := by
          unfold gstat; fun_prop
        refine memLp_two_iff_integrable_sq hm.aestronglyMeasurable |>.2 ?_
        have hp : ∀ n : ℕ, Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ n)
            (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
          fun n => (IsGaussian.memLp_id _ (n : ENNReal) (by simp)).integrable_norm_pow'
        refine (((hp 4).const_mul 2).add (integrable_const 2)).mono' (hm.pow_const 2).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun g => ?_
        have hi : |g i| ≤ ‖g‖ := by simpa using PiLp.norm_apply_le g i
        have hj : |g j| ≤ ‖g‖ := by simpa using PiLp.norm_apply_le g j
        have hij : (g i * g j) ^ 2 ≤ ‖g‖ ^ 4 := by
          rw [mul_pow, show ‖g‖ ^ 4 = ‖g‖ ^ 2 * ‖g‖ ^ 2 by ring]
          exact mul_le_mul (sq_le_sq' (abs_le.1 hi).1 (abs_le.1 hi).2) (sq_le_sq' (abs_le.1 hj).1 (abs_le.1 hj).2)
            (sq_nonneg _) (sq_nonneg _)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        show (gstat g i j) ^ 2 ≤ 2 * ‖g‖ ^ 4 + 2
        unfold gstat
        split_ifs <;> nlinarith [sq_nonneg (g i * g j + 1)]
      have hεq : Integrable (fun g => gstat g i j * pgEps K ρ x g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        have := hgsm.smul (p := 2) (q := 2) (r := 1) hε2
        refine (memLp_one_iff_integrable.1 this).congr (Filter.Eventually.of_forall fun g => ?_)
        simp [Pi.smul_apply, smul_eq_mul]
      have hq : pgQs K x i j = ∫ g, gstat g i j * posF K (pgMu x) (pgOp x) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        unfold pgQs posQ; simp only [hgs]
      rw [hq]
      have hsplit : (fun g => pgFt K ρ x g * gstat g i j) =
          fun g => gstat g i j * pgEps K ρ x g + gstat g i j * posF K (pgMu x) (pgOp x) g := by
        funext g; rw [hFt]; ring
      rw [hsplit, integral_add hεq hFq]; ring
    simp_rw [he]
    have h := hMat d (pgEps K ρ x) hε2
    nlinarith

theorem pgLemmaT_k (hCheb : ChebAvg) (hBT : PgBiasTest) (hCnt : PgCounts)
    (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hVec : VecCS) (hMat : MatCS) (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {w | pgKappa / 40 < |pgKh K ρ x w - pgKs K x|} ≤ ENNReal.ofReal (1 / 12) := by
  set ν := stdGaussian (EuclideanSpace ℝ (Fin d)) with hν
  set n := pgNT d ρ with hn
  set Φ := pgFt K ρ x with hΦ
  set Φ_int := ∫ g, Φ g ∂ν with hΦ_int
  set Φ_int2 := ∫ g, Φ g ^ 2 ∂ν with hΦ_int2
  set t := pgKappa / 80 with ht
  have hk_pos : 0 < pgKappa := by
    unfold pgKappa
    norm_num
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := mod_cast hd
  have hn_pos : 1 ≤ n := by
    have hpos' : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt (d : ℝ)) ^ 2) / (pgKappa / 80) ^ 2 := by
      have hLDpos : 0 < pgLD ρ := by
        unfold pgLD pgKappa pgPB
        have hρpos : 0 < ρ := by linarith
        positivity
      positivity
    have hle := (hCnt (d : ℝ) ρ hd_real hρ).1
    have hpos_real : 0 < pgNTreal (d : ℝ) ρ := by linarith
    have hceil_pos : 0 < ⌈pgNTreal (d : ℝ) ρ⌉₊ := Nat.ceil_pos.mpr hpos_real
    dsimp [n, pgNT]
    omega
  have hMeas : Measurable Φ := by
    have hmeas_prod := pgFt_measurable hPT d K ρ (hK.2.1)
    have hmeas_diag : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => (x, g)) :=
      Measurable.prodMk measurable_const measurable_id
    exact hmeas_prod.comp hmeas_diag
  have hMemLp : MemLp Φ 2 ν := by
    have hMoments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
    exact hMoments.1
  have hMoments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
  have hΦ_int2_le : Φ_int2 ≤ 5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt (d : ℝ)) ^ 2 := hMoments.2.1
  have hBias := pgFt_bias hPT hLB hD4 hEta hVec hMat d ρ hd hρ K hK x hx
  have hBias_int : |Φ_int - pgKs K x| ≤ pgU (d : ℝ) ρ := hBias.1
  have hU_le_t : pgU (d : ℝ) ρ ≤ t := by
    have hU_le : pgU (d : ℝ) ρ ≤ pgKappa / 80 := by
      unfold pgU
      exact (hBT (d : ℝ) ρ hd_real hρ).2.1
    dsimp [t]
    exact hU_le
  have hChebApp := hCheb ℝ (EuclideanSpace ℝ (Fin d)) ν Φ hMeas hMemLp n t hn_pos ht_pos
  have hChebApp' : (Measure.infinitePi fun _ : ℕ => ν) {w | t ≤ |pgKh K ρ x w - Φ_int|} ≤
      ENNReal.ofReal (Φ_int2 / ((n : ℝ) * t ^ 2)) := by
    simpa [Φ, n, t, ν, pgKh, hΦ, hn, ht, hΦ_int, Φ_int] using hChebApp
  have hSubset : {w | pgKappa / 40 < |pgKh K ρ x w - pgKs K x|} ⊆ {w | t ≤ |pgKh K ρ x w - Φ_int|} := by
    intro w hw
    rw [Set.mem_setOf_eq] at hw ⊢
    have h_tri : |pgKh K ρ x w - Φ_int| ≥ |pgKh K ρ x w - pgKs K x| - |pgKs K x - Φ_int| := by
      have h := abs_sub (pgKh K ρ x w - Φ_int) (pgKs K x - Φ_int)
      have hsub : (pgKh K ρ x w - Φ_int) - (pgKs K x - Φ_int) = pgKh K ρ x w - pgKs K x := by ring
      rw [hsub] at h
      linarith
    have h_abs : |pgKs K x - Φ_int| = |Φ_int - pgKs K x| := by rw [abs_sub_comm]
    have h_lower : |pgKh K ρ x w - pgKs K x| - |pgKs K x - Φ_int| ≥ t := by
      rw [h_abs]
      linarith [h_tri, hBias_int, hU_le_t, hw]
    linarith
  have h_div_le : Φ_int2 / ((n : ℝ) * t ^ 2) ≤ 1/12 := by
    set X_bound := 5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt (d : ℝ)) ^ 2 with hX_bound
    have hX : Φ_int2 ≤ X_bound := hΦ_int2_le
    have hn_bound : 12 * X_bound / t ^ 2 ≤ (n : ℝ) := by
      have h := (hCnt (d : ℝ) ρ hd_real hρ).1
      have hceil : pgNTreal (d : ℝ) ρ ≤ (n : ℝ) := mod_cast Nat.le_ceil (pgNTreal (d : ℝ) ρ)
      linarith
    have hpos_n : 0 < (n : ℝ) := by
      have : 1 ≤ n := hn_pos
      have h' : (1 : ℝ) ≤ (n : ℝ) := mod_cast this
      linarith
    calc
      Φ_int2 / ((n : ℝ) * t ^ 2) ≤ X_bound / ((n : ℝ) * t ^ 2) :=
        div_le_div_of_nonneg_right hX (by positivity)
      _ ≤ 1/12 := by
        have h_div1 : X_bound / ((n : ℝ) * t ^ 2) = (X_bound / t ^ 2) / (n : ℝ) := by ring
        rw [h_div1]
        have h_bound2 : X_bound / t ^ 2 ≤ (n : ℝ) / 12 := by
          calc
            X_bound / t ^ 2 = (12 * X_bound / t ^ 2) / 12 := by field_simp
            _ ≤ (n : ℝ) / 12 := div_le_div_of_nonneg_right hn_bound (by norm_num : 0 ≤ (12 : ℝ))
        have h_div2 : (X_bound / t ^ 2) / (n : ℝ) ≤ ((n : ℝ) / 12) / (n : ℝ) :=
          div_le_div_of_nonneg_right h_bound2 (by positivity)
        have h_div3 : ((n : ℝ) / 12) / (n : ℝ) = 1/12 := by field_simp [hpos_n.ne']
        rw [h_div3] at h_div2
        exact h_div2
  calc
    (Measure.infinitePi fun _ : ℕ => ν) {w | pgKappa / 40 < |pgKh K ρ x w - pgKs K x|} ≤
        (Measure.infinitePi fun _ : ℕ => ν) {w | t ≤ |pgKh K ρ x w - Φ_int|} :=
      measure_mono hSubset
    _ ≤ ENNReal.ofReal (Φ_int2 / ((n : ℝ) * t ^ 2)) := hChebApp'
    _ ≤ ENNReal.ofReal (1 / 12) := ENNReal.ofReal_le_ofReal h_div_le

theorem pgLemmaT_b (hCheb : ChebAvg) (hBT : PgBiasTest) (hCnt : PgCounts)
    (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hVec : VecCS) (hMat : MatCS) (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {w | pgTaub d ρ / 4 < ‖pgBh K ρ x w - pgBs K x‖} ≤ ENNReal.ofReal (1 / 12) := by
  let E := EuclideanSpace ℝ (Fin d)
  -- Φ(g) = pgFt K ρ x g • g
  let Φ : E → E := fun g => pgFt K ρ x g • g
  -- EΦ = ∫ Φ dγ
  let EΦ : E := ∫ g, Φ g ∂(stdGaussian E)
  -- The infinite product measure
  let μ := Measure.infinitePi fun _ : ℕ => stdGaussian E
  -- Get moments from pgFt_moments
  have hMoments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
  rcases hMoments with ⟨hmemΦ, hintΦ_sq, hmemΦg, hintΦg_sq, hmemΦgg, hintΦgg_sq⟩
  -- Get bias from pgFt_bias
  have hBias := pgFt_bias hPT hLB hD4 hEta hVec hMat d ρ hd hρ K hK x hx
  rcases hBias with ⟨hbias_k, hbias_b, hbias_Q⟩
  -- Convert hd from ℕ to ℝ for the hypotheses
  have hd_real : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hBT_d := hBT d ρ hd_real hρ
  rcases hBT_d with ⟨hBT_sqrt2, hBT_kappa, hBT_d'⟩
  have hCnt_d := hCnt d ρ hd_real hρ
  rcases hCnt_d with ⟨hCnt_k, hCnt_b, hCnt_Q⟩
  -- Helper: pgKappa > 0
  have hKappa_pos : 0 < pgKappa := by
    dsimp [pgKappa]; norm_num
  -- Helper: pgPB > 0
  have hPB_pos : 0 < pgPB := by
    dsimp [pgPB]; norm_num
  -- Helper: pgLD > 0
  have hLD_pos : 0 < pgLD ρ := by
    dsimp [pgLD]; positivity
  -- pgTaub > 0 and pgTaub/8 > 0
  have hTaub_pos : 0 < pgTaub d ρ := by
    have hLam_pos : 0 < pgLam ρ := by
      dsimp [pgLam]
      refine Real.sqrt_pos.mpr ?_
      have hlog_pos : 0 < Real.log (1 + ρ) :=
        Real.log_pos (by linarith [hρ] : 1 < 1 + ρ)
      positivity
    have hd_pos : 0 < (d : ℝ) := by
      have : 0 < (d : ℕ) := Nat.pos_of_ne_zero (by omega)
      exact_mod_cast this
    dsimp [pgTaub]
    have h_denom_pos : 0 < 12 * (d : ℝ) * pgLam ρ := by
      have h12 : 0 < (12 : ℝ) := by norm_num
      exact mul_pos (mul_pos h12 hd_pos) hLam_pos
    exact div_pos hKappa_pos h_denom_pos
  have hTaub_div_pos : 0 < pgTaub d ρ / 8 := by linarith
  -- Helper: pgNTreal > 0
  have hNTreal_pos : 0 < (pgNTreal d ρ : ℝ) := by
    have hd_pos : 0 < (d : ℝ) := by
      have : 0 < (d : ℕ) := Nat.pos_of_ne_zero (by omega)
      exact_mod_cast this
    have hpos' : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 3))) / ((pgTaub d ρ / 8) ^ 2) := by
      have hnum : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 3))) := by positivity
      have hden : 0 < (pgTaub d ρ / 8) ^ 2 := by positivity
      exact div_pos hnum hden
    have hle' : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 3))) / ((pgTaub d ρ / 8) ^ 2) ≤ pgNTreal d ρ :=
      hCnt_b
    linarith
  -- Measurability of Φ
  have hΦ_meas : Measurable Φ := by
    have h_ft_meas : Measurable (fun (p : PgSp d × E) => pgFt K ρ p.1 p.2) :=
      pgFt_measurable hPT d K ρ hK.2.1
    have h_map : Measurable (fun (g : E) => (x, g) : E → PgSp d × E) :=
      Measurable.prodMk (measurable_const : Measurable fun (_ : E) => x) measurable_id
    have h_ft_meas_fixed : Measurable (fun (g : E) => pgFt K ρ x g) :=
      h_ft_meas.comp h_map
    exact (h_ft_meas_fixed.smul measurable_id : Measurable (fun g => pgFt K ρ x g • g))
  -- MemLp Φ 2 γ
  have hΦ_memLp : MemLp Φ 2 (stdGaussian E) := hmemΦg
  -- n ≥ 1
  have hn_pos : 1 ≤ pgNT d ρ := by
    have hceil_pos : 0 < pgNT d ρ := Nat.ceil_pos.mpr hNTreal_pos
    omega
  -- Apply Chebyshev's inequality (ChebAvg)
  have hCheb_bound : (Measure.infinitePi fun _ : ℕ => stdGaussian E) {ω : ℕ → E |
      (pgTaub d ρ / 8 : ℝ) ≤ ‖((pgNT d ρ : ℝ)⁻¹ • (∑ i ∈ Finset.range (pgNT d ρ), Φ (ω i))) - EΦ‖} ≤
      ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * ((pgTaub d ρ / 8) ^ 2))) :=
    hCheb (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (stdGaussian (EuclideanSpace ℝ (Fin d)))
      Φ hΦ_meas hΦ_memLp (pgNT d ρ) (pgTaub d ρ / 8) hn_pos hTaub_div_pos
  -- Note that (n : ℝ)⁻¹ • ∑ Φ(ω i) = pgBh K ρ x ω
  have h_pgBh_eq : ∀ ω, ((pgNT d ρ : ℝ)⁻¹ • (∑ i ∈ Finset.range (pgNT d ρ), Φ (ω i))) = pgBh K ρ x ω := by
    intro ω
    dsimp [pgBh, Φ]
  -- Key inclusion: {‖pgBh - pgBs‖ > pgTaub/4} ⊆ {ENNReal.ofReal(pgTaub/8) ≤ ENNReal.ofReal(‖pgBh - EΦ‖)}
  have hInclusion : {w : ℕ → E | pgTaub d ρ / 4 < ‖pgBh K ρ x w - pgBs K x‖} ⊆
      {ω : ℕ → E | ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖} := by
    intro ω hω
    have hω' : pgTaub d ρ / 4 < ‖pgBh K ρ x ω - pgBs K x‖ := hω
    -- ‖pgBh - EΦ‖ ≥ ‖pgBh - pgBs‖ - ‖pgBs - EΦ‖
    have h_bias : ‖pgBs K x - EΦ‖ ≤ pgTaub d ρ / 8 := by
      have hEΦ_eq : EΦ = ∫ g, pgFt K ρ x g • g ∂(stdGaussian E) := rfl
      -- hbias_b : ‖∫ g, pgFt K ρ x g • g ∂(stdGaussian ...) - pgBs K x‖ ≤ pgU d ρ
      -- and from hBT: Real.sqrt 2 * pgU ≤ pgTaub/8
      -- and 1 ≤ Real.sqrt 2, so pgU ≤ Real.sqrt 2 * pgU ≤ pgTaub/8
      have hU_le : pgU d ρ ≤ pgTaub d ρ / 8 := by
        have h_sqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
          have h2 : (1 : ℝ) ^ 2 ≤ 2 := by norm_num
          calc
            (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
            _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
        have h_nonneg : 0 ≤ pgU d ρ := by
          dsimp [pgU]
          have hLam_nonneg : 0 ≤ pgLam ρ := by
            dsimp [pgLam]
            exact Real.sqrt_nonneg _
          have hLD_nonneg : 0 ≤ pgLD ρ := by
            dsimp [pgLD]
            positivity
          have hEta_nonneg : 0 ≤ pgEta d ρ := by
            have hEta_sq := hEta d ρ hd_real hρ
            exact hEta_sq.1
          have h_sqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
          positivity
        calc
          pgU d ρ ≤ Real.sqrt 2 * pgU d ρ := by
            nlinarith
          _ ≤ pgTaub d ρ / 8 := hBT_sqrt2
      simpa [hEΦ_eq, norm_sub_rev] using hbias_b.trans hU_le
    have h_tri : ‖pgBh K ρ x ω - EΦ‖ ≥ ‖pgBh K ρ x ω - pgBs K x‖ - ‖pgBs K x - EΦ‖ := by
      have h_triangle : ‖pgBh K ρ x ω - pgBs K x‖ ≤ ‖pgBh K ρ x ω - EΦ‖ + ‖pgBs K x - EΦ‖ := by
        have h_eq : pgBh K ρ x ω - pgBs K x = (pgBh K ρ x ω - EΦ) + (EΦ - pgBs K x) := by abel
        rw [h_eq]
        calc
          ‖(pgBh K ρ x ω - EΦ) + (EΦ - pgBs K x)‖ ≤ ‖pgBh K ρ x ω - EΦ‖ + ‖EΦ - pgBs K x‖ := norm_add_le _ _
          _ = ‖pgBh K ρ x ω - EΦ‖ + ‖pgBs K x - EΦ‖ := by rw [norm_sub_rev (pgBs K x) (EΦ)]
      linarith
    have h_real : pgTaub d ρ / 8 ≤ ‖pgBh K ρ x ω - EΦ‖ := by
      linarith
    -- Convert to ENNReal
    have h_ennreal : ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖ :=
      ENNReal.ofReal_le_ofReal h_real
    simpa using h_ennreal
  -- Relate hCheb_bound to the set in hInclusion
  have h_measure_le : μ {ω | ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖} ≤
      ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * ((pgTaub d ρ / 8) ^ 2))) := by
    have h_set_eq : {ω : ℕ → E | (pgTaub d ρ / 8 : ℝ) ≤ ‖((pgNT d ρ : ℝ)⁻¹ • (∑ i ∈ Finset.range (pgNT d ρ), Φ (ω i))) - EΦ‖} =
        {ω : ℕ → E | ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖} := by
      ext ω
      have h1 : ((pgNT d ρ : ℝ)⁻¹ • (∑ i ∈ Finset.range (pgNT d ρ), Φ (ω i))) = pgBh K ρ x ω := h_pgBh_eq ω
      have h_norm_nonneg : 0 ≤ ‖pgBh K ρ x ω - EΦ‖ := norm_nonneg _
      have h_equiv : ((pgTaub d ρ / 8 : ℝ) ≤ ‖pgBh K ρ x ω - EΦ‖) ↔
          (ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖) := by
        constructor
        · intro h; exact ENNReal.ofReal_le_ofReal h
        · intro h; exact ((ENNReal.ofReal_le_ofReal_iff h_norm_nonneg).mp h)
      simp [h1, h_equiv]
    simpa [μ, h_set_eq] using hCheb_bound
  -- Now bound the RHS using hintΦg_sq and hCnt_b
  have h_bound : ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * ((pgTaub d ρ / 8) ^ 2))) ≤
      ENNReal.ofReal (1 / 12) := by
    let X := 5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 3))
    let T := (pgTaub d ρ / 8) ^ 2
    have hT_pos : 0 < T := by positivity
    have hX_nonneg : 0 ≤ X := by
      have hLD_nonneg : 0 ≤ pgLD ρ := by
        dsimp [pgLD]
        positivity
      positivity
    have hX_pos : 0 < X := by
      dsimp [X]
      have hd_pos : 0 < (d : ℝ) := by
        have : 0 < (d : ℕ) := Nat.pos_of_ne_zero (by omega)
        exact_mod_cast this
      positivity
    have h_int_bound : (∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) ≤ X := hintΦg_sq
    have h_div_bound : (∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * T) ≤ 1 / 12 := by
      -- Step 1: bound the numerator by X
      have h1 : (∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * T) ≤ X / (((pgNT d ρ : ℕ) : ℝ) * T) :=
        (div_le_div_of_nonneg_right h_int_bound (by positivity))
      -- Step 2: bound X / (n * T) ≤ X / (NTreal * T) because n ≥ NTreal
      have hn_ge_NTreal : (pgNTreal d ρ : ℝ) ≤ (pgNT d ρ : ℝ) := by
        dsimp [pgNT]
        exact mod_cast Nat.le_ceil _
      have h2 : X / (((pgNT d ρ : ℕ) : ℝ) * T) ≤ X / ((pgNTreal d ρ : ℝ) * T) := by
        have h_denom2_pos : 0 < (pgNTreal d ρ : ℝ) * T := by positivity
        have h_le : (pgNTreal d ρ : ℝ) * T ≤ ((pgNT d ρ : ℕ) : ℝ) * T :=
          mul_le_mul_of_nonneg_right hn_ge_NTreal (by positivity)
        exact (div_le_div_of_nonneg_left hX_nonneg h_denom2_pos h_le)
      -- Step 3: bound X / (NTreal * T) ≤ 1/12 using hCnt_b
      have h3 : X / ((pgNTreal d ρ : ℝ) * T) ≤ 1 / 12 := by
        -- hCnt_b: 12 * X / T ≤ pgNTreal
        -- So 12 * X ≤ pgNTreal * T
        -- Then X / (pgNTreal * T) ≤ 1/12
        have hCnt_b' : 12 * X / T ≤ (pgNTreal d ρ : ℝ) := hCnt_b
        have h_mul : 12 * X ≤ (pgNTreal d ρ : ℝ) * T := by
          calc
            12 * X = (12 * X / T) * T := by field_simp [hT_pos.ne.symm]
            _ ≤ (pgNTreal d ρ : ℝ) * T := mul_le_mul_of_nonneg_right hCnt_b' (by positivity)
        have h_pos : 0 < (pgNTreal d ρ : ℝ) * T := by positivity
        have h_pos12 : 0 < (12 : ℝ) := by norm_num
        calc
          X / ((pgNTreal d ρ : ℝ) * T) = (X * 12) / (((pgNTreal d ρ : ℝ) * T) * 12) := by
            field_simp [h_pos.ne.symm, h_pos12.ne.symm]
          _ ≤ ((pgNTreal d ρ : ℝ) * T) / (((pgNTreal d ρ : ℝ) * T) * 12) := by
            refine (div_le_div_of_nonneg_right ?_ (by positivity))
            simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
          _ = 1 / 12 := by
            field_simp [hNTreal_pos.ne.symm, h_pos12.ne.symm]
      linarith
    exact ENNReal.ofReal_le_ofReal h_div_bound
  -- Final chain of inequalities
  calc
    μ {w | pgTaub d ρ / 4 < ‖pgBh K ρ x w - pgBs K x‖} ≤
        μ {ω | ENNReal.ofReal (pgTaub d ρ / 8) ≤ ENNReal.ofReal ‖pgBh K ρ x ω - EΦ‖} :=
      measure_mono hInclusion
    _ ≤ ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian E)) / (((pgNT d ρ : ℕ) : ℝ) * ((pgTaub d ρ / 8) ^ 2))) := h_measure_le
    _ ≤ ENNReal.ofReal (1 / 12) := h_bound

theorem pgLemmaT_Q (hCheb : ChebAvg) (hBT : PgBiasTest) (hCnt : PgCounts)
    (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hVec : VecCS) (hMat : MatCS) (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {w | (pgKappa / (8 * d)) ^ 2 < ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2} ≤ ENNReal.ofReal (1 / 12) := by
  -- Convenient abbreviations
  let n := pgNT d ρ
  let t := pgKappa / (16 * (d : ℝ))
  have hd_pos_nat : 0 < d := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have ht_pos : 0 < t := by
    dsimp [t]
    refine div_pos (by norm_num [pgKappa]) ?_
    nlinarith
  have hn_pos : 1 ≤ n := by
    rcases hCnt (d : ℝ) ρ (by exact_mod_cast hd) hρ with ⟨_, _, hthird⟩
    have hpos : 0 < pgNTreal d ρ := by
      have h_pgLD_pos : 0 < pgLD ρ := by
        dsimp [pgLD, pgKappa, pgPB]
        positivity
      have hpos_num : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) := by
        positivity
      have hpos_den : 0 < (pgKappa / (16 * (d : ℝ))) ^ 2 := by
        have hpos_div : 0 < pgKappa / (16 * (d : ℝ)) :=
          div_pos (by norm_num [pgKappa]) (by nlinarith)
        positivity
      have hpos' : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) /
          (pgKappa / (16 * (d : ℝ))) ^ 2 :=
        div_pos hpos_num hpos_den
      linarith
    have hceil : 0 < ⌈pgNTreal d ρ⌉₊ := Nat.ceil_pos.mpr hpos
    have h_one_le : (1 : ℕ) ≤ ⌈pgNTreal d ρ⌉₊ := Nat.one_le_of_lt hceil
    simpa [n, pgNT] using h_one_le
  -- Measurability of pgFt K ρ x
  have h_pgFt_meas : Measurable (pgFt K ρ x) := by
    have h := pgFt_measurable hPT d K ρ hK.2.1
    exact h.comp (Measurable.prodMk measurable_const measurable_id)
  -- Measurability of each entry of gstat
  have h_gstat_entry_meas : ∀ (i j : Fin d),
      Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => gstat g i j) := by
    intro i j
    have h_gi : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
      have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
        have h_equiv_cont : Continuous (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous
        have h_proj_cont : Continuous (fun (f : Fin d → ℝ) => f i) := continuous_apply i
        have h_eq : (fun (g : EuclideanSpace ℝ (Fin d)) => g i) =
            (fun (f : Fin d → ℝ) => f i) ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) := by
          ext g
          simp [PiLp.continuousLinearEquiv_apply]
        rw [h_eq]
        exact h_proj_cont.comp h_equiv_cont
      exact h_cont.measurable
    have h_gj : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g j) := by
      have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g j) := by
        have h_equiv_cont : Continuous (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous
        have h_proj_cont : Continuous (fun (f : Fin d → ℝ) => f j) := continuous_apply j
        have h_eq : (fun (g : EuclideanSpace ℝ (Fin d)) => g j) =
            (fun (f : Fin d → ℝ) => f j) ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) := by
          ext g
          simp [PiLp.continuousLinearEquiv_apply]
        rw [h_eq]
        exact h_proj_cont.comp h_equiv_cont
      exact h_cont.measurable
    have h_prod : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i * g j) :=
      Measurable.mul h_gi h_gj
    have h_const : Measurable (fun (_ : EuclideanSpace ℝ (Fin d)) => (if i = j then (1 : ℝ) else 0)) :=
      measurable_const
    have h_diff : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
      g i * g j - (if i = j then (1 : ℝ) else 0)) :=
      Measurable.sub h_prod h_const
    simpa [gstat] using h_diff
  -- Define Φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d × Fin d)
  let Φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d × Fin d) :=
    fun g => WithLp.toLp 2 (fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2)
  -- Φ is measurable
  have hΦ_meas : Measurable Φ := by
    have h_toLp_meas : Measurable (WithLp.toLp 2 :
      ((Fin d × Fin d) → ℝ) → EuclideanSpace ℝ (Fin d × Fin d)) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d × Fin d => ℝ)).symm.continuous.measurable
    have h_inner_meas : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
      (fun (p : Fin d × Fin d) => pgFt K ρ x g * gstat g p.1 p.2)) := by
      rw [measurable_pi_iff]
      intro p
      rcases p with ⟨i, j⟩
      exact Measurable.mul h_pgFt_meas (h_gstat_entry_meas i j)
    exact h_toLp_meas.comp h_inner_meas
  -- Φ is in L²
  have hΦ_memLp : MemLp Φ 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_moments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
    simpa [Φ] using h_moments.2.2.2.2.1
  -- Second moment bound from pgFt_moments
  have h_int_bound : ∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5)) := by
    have h_moments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
    simpa [Φ] using h_moments.2.2.2.2.2
  -- Integrability of Φ
  have hΦ_int : Integrable Φ (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hΦ_memLp.integrable (by norm_num : 1 ≤ (2 : ENNReal))
  -- Apply Chebyshev's inequality
  have h_cheb := hCheb (EuclideanSpace ℝ (Fin d × Fin d)) (EuclideanSpace ℝ (Fin d))
    (stdGaussian (EuclideanSpace ℝ (Fin d))) Φ hΦ_meas hΦ_memLp n t hn_pos ht_pos
  -- h_cheb : P(‖avg - EΦ‖ ≥ t) ≤ ENNReal.ofReal ((∫ ‖Φ‖²) / (n * t²))
  -- Bound the RHS using PgCounts
  have h_bound : ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2)) ≤
      ENNReal.ofReal (1 / 12) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rcases hCnt (d : ℝ) ρ (by exact_mod_cast hd) hρ with ⟨_, _, hthird⟩
    have hpos_t_sq : 0 < t ^ 2 := by positivity
    have hn_pos_nat : 0 < n := by omega
    have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    -- From hthird: 12 * num / (pgKappa/(16*d))² ≤ pgNTreal ≤ n
    -- So 12 * num / t² ≤ n, i.e., num / (n * t²) ≤ 1/12
    have hthird' : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / (pgKappa / (16 * (d : ℝ))) ^ 2 ≤
        pgNTreal d ρ := hthird
    have hNTreal_le_n : pgNTreal d ρ ≤ (n : ℝ) := by
      have hceil : (pgNTreal d ρ : ℝ) ≤ (⌈pgNTreal d ρ⌉₊ : ℝ) :=
        Nat.ceil_le.mp (le_refl (⌈pgNTreal d ρ⌉₊))
      simpa [n, pgNT] using hceil
    have h_ineq : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / (pgKappa / (16 * (d : ℝ))) ^ 2 ≤ (n : ℝ) := by
      linarith
    -- From h_ineq: 12*num/t² ≤ n, multiply by t²: 12*num ≤ n*t²
    -- Then divide by 12*n*t²: num/(n*t²) ≤ 1/12
    have h_ineq' : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) ≤ (n : ℝ) * t ^ 2 := by
      have hpos_sq : (pgKappa / (16 * (d : ℝ))) ^ 2 ≠ 0 := by positivity
      have h_eq : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) =
          (12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((pgKappa / (16 * (d : ℝ))) ^ 2)) *
          ((pgKappa / (16 * (d : ℝ))) ^ 2) := by
        exact (div_mul_cancel₀ _ hpos_sq).symm
      rw [h_eq]
      -- Goal: (A / B) * B ≤ (n : ℝ) * t ^ 2
      -- Using h_ineq: A / B ≤ n (where A = 12*..., B = (pgKappa/(16*d))^2)
      -- And t = pgKappa/(16*d), so B = t^2
      -- So (A / B) * B ≤ n * t^2
      have hB_nonneg : 0 ≤ ((pgKappa / (16 * (d : ℝ))) ^ 2) := by positivity
      have hB_eq_t_sq : ((pgKappa / (16 * (d : ℝ))) ^ 2) = t ^ 2 := by
        dsimp [t]
      rw [hB_eq_t_sq]
      exact mul_le_mul_of_nonneg_right h_ineq hB_nonneg
    -- Now combine h_int_bound and h_ineq'
    have h_div_le : (∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2) ≤
        (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((n : ℝ) * t ^ 2) :=
      div_le_div_of_nonneg_right h_int_bound (by positivity)
    have h_goal : (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((n : ℝ) * t ^ 2) ≤ 1 / 12 := by
      field_simp [hn_pos'.ne.symm, hpos_t_sq.ne.symm]
      nlinarith
    exact le_trans h_div_le h_goal
  -- Now the main inclusion: the event in the theorem is contained in the Chebyshev tail event
  have h_inclusion : {ω | (pgKappa / (8 * d)) ^ 2 < ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2} ⊆
      {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) -
        ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖} := by
    intro ω hω
    -- hω : (pgKappa / (8 * d)) ^ 2 < ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2
    -- We need to show: t ≤ ‖avg - EΦ‖
    -- First, relate the coordinates of avg_val to pgQh
    have h_avg_coord : ∀ (i j : Fin d), ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)) (i, j) = pgQh K ρ x ω i j := by
      intro i j
      calc
        ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)) (i, j)
            = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, (Φ (ω k)) (i, j)) := by
          simp [smul_eq_mul, Finset.sum_apply]
        _ = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, pgFt K ρ x (ω k) * gstat (ω k) i j) := by
          simp [Φ]
        _ = ((pgNT d ρ : ℝ)⁻¹ • ∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (ω k) • pgGG (ω k)) i j := by
          rw [Matrix.smul_apply, Matrix.sum_apply]
          simp [pgGG, gstat, Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
          rfl
        _ = pgQh K ρ x ω i j := rfl
    -- From pgFt_bias, we have the bias bound
    have h_bias := pgFt_bias hPT hLB hD4 hEta hVec hMat d ρ hd hρ K hK x hx
    rcases h_bias with ⟨_, _, h_bias_sq⟩
    -- From PgBiasTest, we have: sqrt(2)*pgU ≤ τ_b/8 ≤ κ/(16*d) = t
    have h_bias_test := hBT (d : ℝ) ρ (by exact_mod_cast hd) hρ
    rcases h_bias_test with ⟨h_sqrt2_U_le_taub, _, h_taub_le_t⟩
    have h_sqrt2_U_le_t : Real.sqrt 2 * pgU d ρ ≤ t := by
      dsimp [pgU, t]
      linarith
    -- Convert Matrix to EuclideanSpace
    let matToEuclidean (A : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (Fin d × Fin d) :=
      WithLp.toLp 2 (fun (p : Fin d × Fin d) => A p.1 p.2)
    -- The Frobenius norm squared equals the Euclidean norm squared
    have h_norm_sq_eq (A : Matrix (Fin d) (Fin d) ℝ) : ‖matToEuclidean A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [matToEuclidean, Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
    -- Note that (pgKappa / (8 * d)) = 2 * t
    have h_kappa_over_8d_eq_2t : pgKappa / (8 * (d : ℝ)) = 2 * t := by
      dsimp [t]
      field_simp [show (d : ℝ) ≠ 0 from by linarith]
      ring
    -- The squared Frobenius norm of (pgQh - pgQs) equals the squared Euclidean norm
    have h_frob_sq_eq : ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2 =
        ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ^ 2 := by
      rw [h_norm_sq_eq]
      simp [Matrix.sub_apply]
    -- From hω: 4*t² < ‖matToEuclidean (pgQh - pgQs)‖², so 2t < ‖matToEuclidean (pgQh - pgQs)‖
    have h_norm_avgQ_gt_2t : 2 * t < ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ := by
      have h_sq : (2 * t) ^ 2 < ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ^ 2 := by
        rw [← h_kappa_over_8d_eq_2t, ← h_frob_sq_eq]
        simpa using hω
      have h_nonneg : 0 ≤ ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ := norm_nonneg _
      have h_2t_nonneg : 0 ≤ 2 * t := by nlinarith
      nlinarith
    -- Now we need to bound ‖matToEuclidean (EΦ - Q)‖ ≤ t
    let EΦ_val := ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    -- The key identity: EΦ_val (i, j) = ∫ pgFt * gstat i j
    have h_EΦ_coord : ∀ (i j : Fin d), EΦ_val (i, j) = ∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      intro i j
      calc
        EΦ_val (i, j) = (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (i, j) := rfl
        _ = ∫ g, (Φ g) (i, j) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          -- Use ContinuousLinearMap.integral_comp_comm with the projection
          let L : EuclideanSpace ℝ (Fin d × Fin d) →L[ℝ] ℝ := EuclideanSpace.proj (i, j)
          have h_int_eq : ∫ g, L (Φ g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = L (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
            ContinuousLinearMap.integral_comp_comm L hΦ_int
          calc
            (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (i, j) = L (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
              simp [L, EuclideanSpace.proj]
            _ = ∫ g, L (Φ g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by rw [h_int_eq]
            _ = ∫ g, (Φ g) (i, j) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by simp [L, EuclideanSpace.proj]
        _ = ∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by simp [Φ]
    -- Using h_EΦ_coord, we can bound the norm
    have h_norm_EΦQ_le_t : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ≤ t := by
      have h_sq_sum : ∑ i, ∑ j, (EΦ_val (i, j) - (matToEuclidean (pgQs K x)) (i, j)) ^ 2 ≤ t ^ 2 := by
        calc
          ∑ i, ∑ j, (EΦ_val (i, j) - (matToEuclidean (pgQs K x)) (i, j)) ^ 2
              = ∑ i, ∑ j, (EΦ_val (i, j) - pgQs K x i j) ^ 2 := by
            simp [matToEuclidean]
          _ = ∑ i, ∑ j, (∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgQs K x i j) ^ 2 := by
            simp_rw [h_EΦ_coord]
          _ ≤ 2 * pgU d ρ ^ 2 := h_bias_sq
          _ ≤ t ^ 2 := by
            have h_sq : (Real.sqrt 2 * pgU d ρ) ^ 2 ≤ t ^ 2 := by
              have h_nonneg_sqrt : 0 ≤ Real.sqrt 2 * pgU d ρ := by
                have h_sqrt2 : 0 ≤ Real.sqrt 2 := by positivity
                have h_pgU : 0 ≤ pgU d ρ := by
                  have e1 := (hEta d ρ (by exact_mod_cast hd) hρ).1
                  have e2 : 0 ≤ pgLD ρ := by
                    unfold pgLD pgKappa pgPB; have : (0 : ℝ) ≤ ρ := by linarith
                    positivity
                  unfold pgU; positivity
                nlinarith
              nlinarith
            have h_sqrt_sq : (Real.sqrt 2 * pgU d ρ) ^ 2 = 2 * pgU d ρ ^ 2 := by
              calc
                (Real.sqrt 2 * pgU d ρ) ^ 2 = (Real.sqrt 2) ^ 2 * pgU d ρ ^ 2 := by ring
                _ = 2 * pgU d ρ ^ 2 := by rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
            nlinarith
      -- Now relate the sum of squares to the Euclidean norm squared
      have h_norm_sq_eq' : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ^ 2 = ∑ i, ∑ j, ((EΦ_val - matToEuclidean (pgQs K x)) (i, j)) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        -- Goal: ∑ i, ‖x.ofLp i‖ ^ 2 = ∑ i, ∑ j, x.ofLp (i, j) ^ 2
        -- where x = EΦ_val - matToEuclidean (pgQs K x)
        -- Simplify the left side: ‖x.ofLp i‖ ^ 2 = (x i) ^ 2
        -- and the right side using Fintype.sum_prod_type
        have h_simp (p : Fin d × Fin d) : ‖((EΦ_val - matToEuclidean (pgQs K x))).ofLp p‖ ^ 2 = ((EΦ_val - matToEuclidean (pgQs K x)) p) ^ 2 := by
          simp [Real.norm_eq_abs, sq_abs]
        calc
          ∑ i : Fin d × Fin d, ‖((EΦ_val - matToEuclidean (pgQs K x))).ofLp i‖ ^ 2
              = ∑ i : Fin d × Fin d, ((EΦ_val - matToEuclidean (pgQs K x)) i) ^ 2 := by
            simp_rw [h_simp]
          _ = ∑ i : Fin d, ∑ j : Fin d, ((EΦ_val - matToEuclidean (pgQs K x)) (i, j)) ^ 2 := by
            rw [Fintype.sum_prod_type]
      have h_sub_coord : ∀ (i j : Fin d), (EΦ_val - matToEuclidean (pgQs K x)) (i, j) = EΦ_val (i, j) - pgQs K x i j := by
        intro i j; simp [matToEuclidean]
      have h_norm_sq_le : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ^ 2 ≤ t ^ 2 := by
        rw [h_norm_sq_eq']
        simp_rw [h_sub_coord]
        simpa [matToEuclidean] using h_sq_sum
      nlinarith
    -- Now we can use the triangle inequality
    have h_triangle : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
        ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
      let avg_val := (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)
      have h_avg_sub : matToEuclidean (pgQh K ρ x ω - pgQs K x) = avg_val - matToEuclidean (pgQs K x) := by
        refine PiLp.ext fun p => ?_
        rcases p with ⟨i, j⟩
        unfold matToEuclidean
        rw [PiLp.toLp_apply, PiLp.toLp_apply]
        simp [Matrix.sub_apply]
        rw [← h_avg_coord i j]
      have h_tri := norm_sub_le (avg_val - EΦ_val) (matToEuclidean (pgQs K x) - EΦ_val)
      have h_goal : ‖avg_val - matToEuclidean (pgQs K x)‖ ≤ ‖avg_val - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
        have h_left : (avg_val - EΦ_val) - (matToEuclidean (pgQs K x) - EΦ_val) = avg_val - matToEuclidean (pgQs K x) := by
          calc
            (avg_val - EΦ_val) - (matToEuclidean (pgQs K x) - EΦ_val)
                = avg_val - EΦ_val - matToEuclidean (pgQs K x) + EΦ_val := by abel
            _ = avg_val - matToEuclidean (pgQs K x) := by abel
        have h_right : ‖matToEuclidean (pgQs K x) - EΦ_val‖ = ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by rw [norm_sub_rev]
        rw [h_left, h_right] at h_tri
        exact h_tri
      -- Now combine with h_avg_sub
      have h_target : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
          ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
        -- Using h_avg_sub and h_goal
        have h_target' : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
            ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
          have h_norm_eq : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ = ‖avg_val - matToEuclidean (pgQs K x)‖ :=
            congrArg norm h_avg_sub
          rw [h_norm_eq]
          rw [show ‖avg_val - EΦ_val‖ = ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ by dsimp [avg_val]]
          exact h_goal
        exact h_target'
      exact h_target
    -- Combine the bounds
    have h_result : t ≤ ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ := by
      nlinarith
    -- Return the result
    exact h_result
  -- Combine everything
  calc
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {ω | (pgKappa / (8 * d)) ^ 2 < ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2}
    ≤ (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) -
        ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖} :=
      measure_mono h_inclusion
    _ ≤ ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2)) := h_cheb
    _ ≤ ENNReal.ofReal (1 / 12) := h_bound

theorem pgAmplify (hMH : MajorityHoeffding) (hHo : PgHoeffding) (d : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (x : PgSp d) (B : Set (ℕ → EuclideanSpace ℝ (Fin d))) (hB : MeasurableSet B)
    (hνB : (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) B ≤ ENNReal.ofReal (1 / 4))
    (hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdict K ρ x w}) :
    ((∀ w, pgVerdict K ρ x w → w ∈ B) →
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        {W | pgTest K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ)) ∧
    ((∀ w, ¬ pgVerdict K ρ x w → w ∈ B) →
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        {W | ¬ pgTest K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ)) := by
  classical
  set m := pgMT δ
  set ν_inner := stdGaussian (EuclideanSpace ℝ (Fin d))
  set ν' := Measure.infinitePi fun _ : ℕ => ν_inner
  have hνB' : ν' B ≤ 1 / 4 := by
    -- hνB : ν' B ≤ ENNReal.ofReal (1/4)
    -- ENNReal.ofReal (1/4) = (1/4 : ENNReal)
    simpa using hνB
  have hMHapp := hMH (ℕ → EuclideanSpace ℝ (Fin d)) ν' B hB hνB'
  have hMHapp_m := hMHapp m
  have hJpos : 0 < pgJr δ := by
    have hlog : 0 < Real.logb 2 (4 / δ) :=
      Real.logb_pos (by norm_num) (((one_lt_div (a := 4) hδ0).mpr (by linarith)))
    exact Nat.ceil_pos.mpr hlog
  have hpos_dp : 0 < pgDp δ := by
    have hJpos' : (0 : ℝ) < pgJr δ := Nat.cast_pos.mpr hJpos
    refine div_pos hδ0 (by nlinarith)
  have h_ineq : 8 * Real.log (1 / pgDp δ) ≤ (m : ℝ) := by
    have h_eq : 1 / pgDp δ = 2 * pgJr δ / δ := by
      dsimp [pgDp]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hJpos)]
    rw [h_eq]
    dsimp [m, pgMT]
    have hpos_log : 0 ≤ 8 * Real.log (2 * pgJr δ / δ) := by
      have hpos_arg : 1 < 2 * pgJr δ / δ := by
        have hJr_ge_1 : (1 : ℝ) ≤ pgJr δ := mod_cast Nat.one_le_of_lt hJpos
        have h_one_div_δ_gt_1 : 1 < 1 / δ := one_lt_one_div hδ0 hδ1
        have h_mul : (1 : ℝ) < 2 * (pgJr δ) * (1 / δ) := by
          nlinarith
        simpa [div_eq_mul_inv] using h_mul
      have hlog_pos : 0 < Real.log (2 * pgJr δ / δ) := Real.log_pos hpos_arg
      nlinarith
    have hceil : (⌈8 * Real.log (2 * pgJr δ / δ)⌉₊ : ℝ) = (pgMT δ : ℝ) := by
      dsimp [m, pgMT]
    -- Goal: a ≤ (⌈a⌉₊ : ℝ)
    -- This follows from Nat.ceil_le.mp with n := ⌈a⌉₊
    apply (Nat.ceil_le (a := 8 * Real.log (2 * pgJr δ / δ)) (n := ⌈8 * Real.log (2 * pgJr δ / δ)⌉₊)).mp
    exact le_refl _
  have hPgHo := hHo (pgDp δ) hpos_dp m h_ineq
  have h_bound_dp : ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) ≤ ENNReal.ofReal (pgDp δ) :=
    ENNReal.ofReal_le_ofReal hPgHo
  constructor
  · intro h_accept
    have h_subset : {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | pgTest K ρ δ x W} ⊆
        {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} := by
      intro W hW
      have hmem : pgTest K ρ δ x W := hW
      have hcard_lt : (m : ℝ) / 2 < ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card := hmem
      have hfilter_subset : ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)) ⊆
        ((Finset.range m).filter fun i => W i ∈ B) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        rcases hi with ⟨hi_range, hi_verdict⟩
        exact ⟨hi_range, h_accept (W i) hi_verdict⟩
      have hcard_le : ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card ≤
        ((Finset.range m).filter fun i => W i ∈ B).card :=
        Finset.card_le_card hfilter_subset
      have h_ineq_card : (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card := by
        have hcard_le' : (((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card : ℝ) ≤
          (((Finset.range m).filter fun i => W i ∈ B).card : ℝ) := by exact_mod_cast hcard_le
        linarith
      exact h_ineq_card
    have h_measure_le : (Measure.infinitePi fun _ : ℕ => ν') {W | pgTest K ρ δ x W} ≤
        (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} :=
      measure_mono h_subset
    have h_bound : (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := hMHapp_m
    exact h_measure_le.trans (h_bound.trans h_bound_dp)
  · intro h_reject
    have h_subset : {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | ¬ pgTest K ρ δ x W} ⊆
        {W : ℕ → ℕ → EuclideanSpace ℝ (Fin d) | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} := by
      intro W hW
      have hmem : ¬ pgTest K ρ δ x W := hW
      have h_contra : ∀ w, w ∉ B → pgVerdict K ρ x w := by
        intro w hwB
        by_contra h_not_verdict
        apply hwB
        exact h_reject w h_not_verdict
      have hcard_not_gt : ¬ (m : ℝ) / 2 < ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card := hmem
      have hcard_le_verdict : (((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card : ℝ) ≤ (m : ℝ) / 2 := by
        by_contra h
        apply hcard_not_gt
        push_cast
        linarith
      have h_B_subset : ((Finset.range m).filter fun i => W i ∉ B) ⊆
        ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        rcases hi with ⟨hi_range, hi_not_B⟩
        exact ⟨hi_range, h_contra (W i) hi_not_B⟩
      have h_card_B_le : ((Finset.range m).filter fun i => W i ∉ B).card ≤
        ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card :=
        Finset.card_le_card h_B_subset
      have h_card_notB_le : (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) ≤ (m : ℝ) / 2 := by
        have h : ((Finset.range m).filter fun i => W i ∉ B).card ≤ ((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card :=
          h_card_B_le
        have h' : (((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card : ℝ) ≤ (m : ℝ) / 2 := hcard_le_verdict
        have h_cast : (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) ≤ (((Finset.range m).filter fun i => pgVerdict K ρ x (W i)).card : ℝ) := by
          exact_mod_cast h
        linarith
      have h_card_B_ge : (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card := by
        have h_total : ((Finset.range m).filter fun i => W i ∈ B).card + ((Finset.range m).filter fun i => W i ∉ B).card = m := by
          rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
        have h_total' : (((Finset.range m).filter fun i => W i ∈ B).card : ℝ) + (((Finset.range m).filter fun i => W i ∉ B).card : ℝ) = (m : ℝ) := by
          exact_mod_cast h_total
        push_cast
        linarith
      exact h_card_B_ge
    have h_measure_le : (Measure.infinitePi fun _ : ℕ => ν') {W | ¬ pgTest K ρ δ x W} ≤
        (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} :=
      measure_mono h_subset
    have h_bound : (Measure.infinitePi fun _ : ℕ => ν') {W | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => W i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8)) := hMHapp_m
    exact h_measure_le.trans (h_bound.trans h_bound_dp)

/-! ## Leaves: the conclusion at a sound point -/

theorem posBody_smul {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (a : ℝ) (ha : 0 < a) :
    posBody K μ (a • T) = a⁻¹ • posBody K μ T := by
  ext y
  constructor
  · intro hy
    rw [posBody, Set.mem_ofPred_eq] at hy
    have hz_mem : a • y ∈ posBody K μ T := by
      rw [posBody, Set.mem_ofPred_eq]
      simpa [smul_apply] using hy
    have hy_eq : y = a⁻¹ • (a • y) := (inv_smul_smul₀ ha.ne.symm y).symm
    rw [hy_eq]
    exact Set.mem_smul_set.mpr ⟨a • y, hz_mem, rfl⟩
  · intro hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha.ne.symm) (posBody K μ T) y] at hy
    rw [inv_inv] at hy
    rw [posBody, Set.mem_ofPred_eq] at hy
    simpa [posBody, smul_apply] using hy

theorem pgSound_good (hCaB : PropCaBound) (hCb : PropCb) (hCc : PropCc) (hG : GaussConst) (hNM : NormMeanLower)
    (hConc : PgConclusion) (hQ : PgQtail)
    (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d)
    (hx : x ∈ pgDom d ρ) (hs : PgSound K ρ x) : PgGood d K (36.4 * d * pgLam ρ) (some (pgOut x)) := by
  obtain ⟨hk, hb, hq⟩ := hs
  have hdet : (pgMat x).det ≠ 0 := (pgDom_inv d ρ hd hρ x hx).1
  have hOmu : pgMu (pgOut x) = pgMu x := by unfold pgOut; exact pgMu_pgPack _ _
  have hOmat : pgMat (pgOut x) = pgMat x := by
    unfold pgOut; rw [pgMat_pgPack]; unfold pgA; exact one_smul _ _
  have hOop : pgOp (pgOut x) = pgOp x := by unfold pgOp; rw [hOmat]
  have hPB : IsPosBody K 1 ρ := pgBody_isPosBody K ρ hρ hK
  have hdetT : LinearMap.det (pgOp x : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rw [pgOp_det]; exact hdet
  have hk' : posK K (pgMu x) (pgOp x) ≤ 0.1375 := by
    have h := hk; unfold pgKs pgKappa at h; linarith
  have hk0 : 0 ≤ posK K (pgMu x) (pgOp x) := by
    unfold posK posF; exact integral_nonneg fun g => gauge_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨pgOut x, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hOmat]; exact hdet
  · rw [hOmu, hOop]
    have hQt : (0.1375 : ℝ) ≤ BodySpec.Qtail 1 := by
      have h : (0.1375 : ℝ) ≤ BodySpec.Qtail pgA := hQ
      unfold pgA at h; exact h
    exact hCb d K 1 ρ (pgMu x) (pgOp x) hPB 1 (by linarith)
  · rw [hOmu, hOop]
    obtain ⟨t, ht0, htl, hC⟩ := hG ρ hρ
    have hlam : 0 < pgLam ρ := by
      unfold pgLam
      have := Real.log_pos (by linarith : (1 : ℝ) < 1 + ρ)
      exact Real.sqrt_pos.2 (by linarith)
    have htl' : t ≤ pgLam ρ := htl
    have hC' : bathC ρ t ≤ pgLam ρ := hC
    have hq0 : 0 < pgKappa / (2 * d) := by unfold pgKappa; positivity
    have hb' : ‖posB K (pgMu x) (pgOp x)‖ ≤ pgTaub d ρ := hb
    have h6 : 6 * |t| * ‖posB K (pgMu x) (pgOp x)‖ ≤ pgKappa / (2 * d) := by
      rw [abs_of_nonneg ht0]
      calc 6 * t * ‖posB K (pgMu x) (pgOp x)‖ ≤ 6 * pgLam ρ * pgTaub d ρ := by gcongr
        _ = pgKappa / (2 * d) := by unfold pgTaub; field_simp; ring
    intro y hy
    have hy' := hCaB d K 1 ρ (pgMu x) (pgOp x) hPB hdetT (pgKappa / (2 * d)) t hq0 hq h6 y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine hy'.trans ?_
    rw [div_le_iff₀ hq0]
    have hR : 36.4 * (d : ℝ) * pgLam ρ * (pgKappa / (2 * d)) = 2.275 * pgLam ρ := by
      unfold pgKappa; field_simp; ring
    rw [hR]
    have hkey : (1 + posK K (pgMu x) (pgOp x)) * bathC ρ t ≤ 1.1375 * pgLam ρ := by
      rcases le_total 0 (bathC ρ t) with h | h
      · nlinarith
      · nlinarith
    linarith
  · rw [hOmu, hOop]
    unfold pgMw
    have hc := hCc d K 1 ρ (pgMu x) (pgOp x) hPB (by linarith)
    have hnm := hNM d
    have hsq : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.2 (by linarith)
    have hN : 0 < ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      lt_of_lt_of_le (by positivity) hnm
    have hI : ∫ g, gauge (posBody K (pgMu x) (pgOp x)) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ 1.27 := by
      refine hc.trans ?_
      have h1 : 1 / (1 - posK K (pgMu x) (pgOp x)) ≤ 1 / (1 - 0.1375) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h2 := hConc.2.1
      unfold pgA at h2
      linarith
    rw [div_le_iff₀ hN]
    have hkey : (1.27 : ℝ) ≤ 1.27 * Real.sqrt (d + 1) / d * ∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      calc (1.27 : ℝ) = 1.27 * Real.sqrt (d + 1) / d * (d / Real.sqrt (d + 1)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hnm (by positivity)
    linarith


/-! ## Leaves: the parameters, the domain and the descent -/

theorem pgJr_spec (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ pgJr δ ∧ 4 / δ ≤ 2 ^ pgJr δ ∧ 0 < pgDp δ ∧ pgDp δ ≤ 1 := by
  have h_one_lt_four_div_δ : 1 < 4 / δ := by
    have hδ_lt_4 : δ < 4 := by linarith
    calc
      1 = δ / δ := by field_simp [ne_of_gt hδ0]
      _ < 4 / δ := div_lt_div_of_pos_right hδ_lt_4 hδ0
  have h_one_le_pgJr : 1 ≤ pgJr δ := by
    rw [pgJr, Nat.one_le_ceil_iff]
    exact Real.logb_pos (by norm_num) h_one_lt_four_div_δ
  have h_pgJr_pos : 0 < (pgJr δ : ℝ) := by
    exact_mod_cast Nat.one_pos.trans_le h_one_le_pgJr
  have h_four_div_δ_pos : 0 < 4 / δ := div_pos (by norm_num) hδ0
  have h_logb_le : Real.logb 2 (4 / δ) ≤ (pgJr δ : ℝ) := by
    rw [pgJr]
    exact Nat.le_ceil _
  have h_part2 : 4 / δ ≤ (2 : ℝ) ^ pgJr δ := by
    calc
      4 / δ = (2 : ℝ) ^ Real.logb 2 (4 / δ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) h_four_div_δ_pos]
      _ ≤ (2 : ℝ) ^ (pgJr δ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h_logb_le
      _ = (2 : ℝ) ^ pgJr δ := by rw [Real.rpow_natCast]
  have h_part3 : 0 < pgDp δ := by
    rw [pgDp]
    refine div_pos hδ0 ?_
    nlinarith
  have h_part4 : pgDp δ ≤ 1 := by
    rw [pgDp]
    refine (div_le_one ?_).mpr ?_
    · nlinarith
    · have h_one_le : (1 : ℝ) ≤ (pgJr δ : ℝ) := by exact_mod_cast h_one_le_pgJr
      nlinarith
  exact And.intro h_one_le_pgJr (And.intro h_part2 (And.intro h_part3 h_part4))

theorem pgNs_pos (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 1 ≤ pgNs d ρ := by
  have hdpos : 0 < (d : ℝ) := by
    have hd' : 0 < d := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hd
    exact_mod_cast hd'
  have hlog : 0 < Real.log (1 + ρ) := by
    have h : 1 < 1 + ρ := by linarith
    exact Real.log_pos h
  have hKappa : 0 < pgKappa := by norm_num [pgKappa]
  have hPB : 0 < pgPB := by norm_num [pgPB]
  have hρpos : 0 < ρ := by linarith
  have hLam : 0 < pgLam ρ := by
    dsimp [pgLam]
    have hpos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
    exact Real.sqrt_pos.mpr hpos
  have hLD : 0 < pgLD ρ := by
    dsimp [pgLD]
    positivity
  have hTmin : 0 < pgTmin d ρ := by
    dsimp [pgTmin]
    positivity
  have hDelta : 0 < pgDelta d ρ := by
    dsimp [pgDelta]
    have hsq : 0 < Real.sqrt (4 + pgPB ^ 2 * (d : ℝ)) :=
      Real.sqrt_pos.mpr (by
        have : 0 ≤ pgPB ^ 2 * (d : ℝ) := by positivity
        nlinarith)
    positivity
  have hEh : 0 < pgEh d ρ := by
    dsimp [pgEh]
    positivity
  have hG2 : 0 < pgG2 d ρ := by
    dsimp [pgG2]
    positivity
  have hNreal : 0 < pgNreal d ρ := by
    dsimp [pgNreal]
    positivity
  have hceil : 0 < ⌈pgNreal d ρ⌉₊ := Nat.ceil_pos.mpr hNreal
  simpa [pgNs] using hceil

theorem pgStepSize_pos (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 0 < pgStepSize d ρ := by
  have hκ_pos : 0 < pgKappa := by
    unfold pgKappa
    norm_num
  have hρ_pos : 0 < ρ := by linarith
  have hd_pos : 0 < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hLam_pos : 0 < pgLam ρ := by
    unfold pgLam
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    have hpos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
    exact Real.sqrt_pos.mpr hpos
  have hTmin_pos : 0 < pgTmin (d : ℝ) ρ := by
    unfold pgTmin
    have hden : 0 < 9 * (d : ℝ) * pgLam ρ := by
      have h9 : 0 < (9 : ℝ) := by norm_num
      positivity
    exact div_pos (by norm_num : 0 < (1 : ℝ)) hden
  have hLD_pos : 0 < pgLD ρ := by
    unfold pgLD
    have hPB_pos : 0 < pgPB := by
      unfold pgPB
      norm_num
    positivity
  have hDelta_pos : 0 < pgDelta (d : ℝ) ρ := by
    unfold pgDelta
    have hsqrt : 0 < Real.sqrt (4 + pgPB ^ 2 * (d : ℝ)) :=
      Real.sqrt_pos.mpr (by
        have hsq : 0 ≤ pgPB ^ 2 * (d : ℝ) := by positivity
        nlinarith)
    positivity
  have hG2_pos : 0 < pgG2 (d : ℝ) ρ := by
    unfold pgG2
    have hnum : 0 < 5 * pgLD ρ ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) + 2 * pgKappa ^ 2 / (d : ℝ) := by
      positivity
    have hden : 0 < pgTmin (d : ℝ) ρ ^ 2 := by positivity
    exact div_pos hnum hden
  have hNs_pos : 0 < (pgNs d ρ : ℝ) := by
    have h := pgNs_pos d ρ hd hρ
    have h' : (1 : ℝ) ≤ (pgNs d ρ : ℝ) := by exact_mod_cast h
    linarith
  have hsqrtG2_pos : 0 < Real.sqrt (pgG2 (d : ℝ) ρ) := Real.sqrt_pos.mpr hG2_pos
  have hsqrtNs_pos : 0 < Real.sqrt (pgNs d ρ) := Real.sqrt_pos.mpr hNs_pos
  unfold pgStepSize
  have hden_pos : 0 < Real.sqrt (pgG2 (d : ℝ) ρ) * Real.sqrt (pgNs d ρ) := mul_pos hsqrtG2_pos hsqrtNs_pos
  exact div_pos hDelta_pos hden_pos

theorem pgEh_pos (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 0 < pgEh d ρ := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
  have hρ' : (0 : ℝ) < ρ := by linarith
  have h_log_pos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
  have h_lam_pos : 0 < pgLam ρ := by
    dsimp [pgLam]
    apply Real.sqrt_pos.mpr
    nlinarith
  have h_ld_pos : 0 < pgLD ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    positivity
  have h_num_pos : 0 < pgKappa ^ 2 := by
    dsimp [pgKappa]
    positivity
  have h_denom_pos : 0 < 922 * (d : ℝ) ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by
    positivity
  dsimp [pgEh]
  positivity

theorem pgStep_arith (hStep : PgStep) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgDelta d ρ ^ 2 / (2 * pgStepSize d ρ * pgNs d ρ) + pgStepSize d ρ * pgG2 d ρ / 2 ≤ pgEh d ρ / 4 := by
  set Δ := pgDelta d ρ with hΔ
  set G2 := pgG2 d ρ with hG2
  set e := pgEh d ρ with he
  set N := pgNs d ρ with hN
  set s := pgStepSize d ρ with hs
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
  have hρpos : 0 < ρ := by linarith
  have hKappa_pos : 0 < pgKappa := by
    unfold pgKappa
    norm_num
  have hPB_pos : 0 < pgPB := by
    unfold pgPB
    norm_num
  have hLam_pos : 0 < pgLam ρ := by
    unfold pgLam
    refine Real.sqrt_pos.mpr ?_
    have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith : 1 < 1 + ρ)
    nlinarith
  have hDelta_pos : 0 < Δ := by
    dsimp [Δ, pgDelta]
    positivity
  have hG2_pos : 0 < G2 := by
    dsimp [G2, pgG2, pgLD, pgTmin, pgLam]
    positivity
  have hEh_pos : 0 < e := by
    dsimp [e]
    exact pgEh_pos d ρ hd hρ
  have hNs_one : 1 ≤ N := pgNs_pos d ρ hd hρ
  have hNs_pos : 0 < (N : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hNs_one
  have hNs_nonneg : 0 ≤ (N : ℝ) := by linarith
  have hsqrtG2_pos : 0 < Real.sqrt G2 := Real.sqrt_pos.mpr hG2_pos
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNs_pos
  have hNreal_nonneg : 0 ≤ pgNreal d ρ := by
    unfold pgNreal
    positivity
  have h_left : Δ ^ 2 / (2 * s * (N : ℝ)) + s * G2 / 2 = Δ * Real.sqrt G2 / Real.sqrt (N : ℝ) := by
    dsimp [s, pgStepSize, Δ, G2, N]
    have hrG2 : Real.sqrt (pgG2 d ρ) ^ 2 = pgG2 d ρ := Real.sq_sqrt (by
      dsimp [pgG2, pgLD, pgTmin, pgLam]
      positivity)
    have hrN : Real.sqrt ((pgNs d ρ : ℕ) : ℝ) ^ 2 = (pgNs d ρ : ℝ) := Real.sq_sqrt (by
      have h := pgNs_pos d ρ hd hρ
      exact mod_cast (Nat.one_pos.trans_le h).le)
    have hNs_ne_zero : (pgNs d ρ : ℝ) ≠ 0 := by
      have h := pgNs_pos d ρ hd hρ
      exact mod_cast (Nat.one_pos.trans_le h).ne'
    have hsqrtG2_ne_zero : Real.sqrt (pgG2 d ρ) ≠ 0 := by
      refine Real.sqrt_pos.mpr (by
        dsimp [pgG2, pgLD, pgTmin, pgLam]
        positivity) |>.ne'
    have hsqrtN_ne_zero : Real.sqrt ((pgNs d ρ : ℕ) : ℝ) ≠ 0 := by
      refine Real.sqrt_pos.mpr (by
        have h := pgNs_pos d ρ hd hρ
        exact mod_cast Nat.one_pos.trans_le h) |>.ne'
    field_simp [hsqrtG2_ne_zero, hsqrtN_ne_zero, hNs_ne_zero, hDelta_pos.ne']
    simp [hrG2, hrN]
    ring
  rw [h_left]
  have ha_pos : 0 < Δ * Real.sqrt G2 := by
    exact mul_pos hDelta_pos hsqrtG2_pos
  have hNreal_le_N : pgNreal d ρ ≤ (N : ℝ) := by
    have hceil : (pgNreal d ρ : ℝ) ≤ (⌈pgNreal d ρ⌉₊ : ℝ) := by
      exact mod_cast Nat.le_ceil (pgNreal d ρ)
    dsimp [N, pgNs]
    exact hceil
  have h_cond : 16 * (Δ * Real.sqrt G2) ^ 2 / e ^ 2 ≤ (N : ℝ) := by
    calc
      16 * (Δ * Real.sqrt G2) ^ 2 / e ^ 2 = 16 * (Δ ^ 2 * ((Real.sqrt G2) ^ 2)) / e ^ 2 := by ring
      _ = 16 * (Δ ^ 2 * G2) / e ^ 2 := by rw [Real.sq_sqrt (by linarith : 0 ≤ G2)]
      _ = 16 * pgDelta d ρ ^ 2 * pgG2 d ρ / (pgEh d ρ) ^ 2 := by dsimp [Δ, G2, e]; ring
      _ = pgNreal d ρ := by rfl
      _ ≤ (N : ℝ) := hNreal_le_N
  have h_result := hStep (Δ * Real.sqrt G2) e (N : ℝ) ha_pos hEh_pos h_cond
  -- h_result : (Δ * Real.sqrt G2) / Real.sqrt (N : ℝ) ≤ e / 4
  simpa [Δ, e, N] using h_result

theorem pgProj_continuous (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : Continuous (pgProj d ρ) := by
  have hne : (pgDom d ρ).Nonempty := ⟨pgX1 d ρ, pgX1_mem d ρ hd hρ⟩
  have hcl : IsClosed (pgDom d ρ) := (pgDom_isCompact d ρ).isClosed
  have hcv : Convex ℝ (pgDom d ρ) := pgDom_convex d ρ
  have h := pgProj_spec d ρ hne hcl hcv
  exact h.2.2.continuous

theorem pgDescent_mem (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (a : ℕ → EuclideanSpace ℝ (Fin d)) : pgDescent K ρ a ∈ pgDom d ρ := by
  unfold pgDescent sgdAvg
  let N := pgNs d ρ
  have hNpos : 1 ≤ N := pgNs_pos d ρ hd hρ
  have hNpos' : (N : ℝ) ≠ 0 := by
    intro hzero
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    linarith
  have h_iter_mem : ∀ t ∈ Finset.range N, sgdIter (pgProj d ρ) (pgV K ρ) (pgStepSize d ρ) (pgX1 d ρ) a t ∈ pgDom d ρ := by
    intro t ht
    induction' t with t ih
    · exact pgX1_mem d ρ hd hρ
    · unfold sgdIter
      have h_nonempty : (pgDom d ρ).Nonempty := ⟨pgX1 d ρ, pgX1_mem d ρ hd hρ⟩
      have h_closed : IsClosed (pgDom d ρ) := (pgDom_isCompact d ρ).isClosed
      have h_cvx : Convex ℝ (pgDom d ρ) := pgDom_convex d ρ
      rcases pgProj_spec d ρ h_nonempty h_closed h_cvx with ⟨h_proj_mem, _, _⟩
      apply h_proj_mem
  have h_nonneg : ∀ t ∈ Finset.range N, 0 ≤ (N : ℝ)⁻¹ := by
    intro t ht
    have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    positivity
  have h_sum_one : ∑ t ∈ Finset.range N, (N : ℝ)⁻¹ = 1 := by
    simp [hNpos']
  have h_cvx : Convex ℝ (pgDom d ρ) := pgDom_convex d ρ
  rw [Finset.smul_sum]
  exact Convex.sum_mem h_cvx h_nonneg h_sum_one h_iter_mem

theorem pgH_bdd (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    ∃ C, ∀ x ∈ pgDom d ρ, |pgH K x| ≤ C := by
  have h_compact : IsCompact (pgDom d ρ) := pgDom_isCompact d ρ
  have h_cont : ContinuousOn (pgH K) (pgDom d ρ) := pgH_continuousOn d ρ hd hρ K hK
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn h_compact h_cont
  refine ⟨C, λ x hx => ?_⟩
  have h := hC x hx
  simpa [Real.norm_eq_abs] using h

theorem pgH_desc_measurable (hPT : PiTildeMeasurable) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    Measurable fun a : ℕ → EuclideanSpace ℝ (Fin d) => pgH K (pgDescent K ρ a) := by
  have h_closed : IsClosed K := hK.2.1
  have h_proj_cont : Continuous (pgProj d ρ) := pgProj_continuous d ρ hd hρ
  have h_descent_meas : Measurable (pgDescent K ρ) :=
    pgDescent_measurable hPT d K ρ h_closed h_proj_cont
  have h_mem : ∀ a, pgDescent K ρ a ∈ pgDom d ρ := fun a => pgDescent_mem d ρ hd hρ K a
  have h_cont : ContinuousOn (pgH K) (pgDom d ρ) := pgH_continuousOn d ρ hd hρ K hK
  have h_restrict_cont : Continuous ((pgDom d ρ).domRestrict (pgH K)) := h_cont.domRestrict
  have h_restrict_meas : Measurable ((pgDom d ρ).domRestrict (pgH K)) := h_restrict_cont.measurable
  have h_subtype_meas : Measurable (fun a => (⟨pgDescent K ρ a, h_mem a⟩ : pgDom d ρ)) :=
    Measurable.subtype_mk h_descent_meas (h := h_mem)
  simpa [Set.domRestrict_eq, Function.comp_def] using h_restrict_meas.comp h_subtype_meas

theorem pgH_desc_integrable (hPT : PiTildeMeasurable) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    Integrable (fun a : ℕ → EuclideanSpace ℝ (Fin d) => pgH K (pgDescent K ρ a))
      (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rcases pgH_bdd d ρ hd hρ K hK with ⟨C, hC⟩
  have h_meas : Measurable (fun a : ℕ → EuclideanSpace ℝ (Fin d) => pgH K (pgDescent K ρ a)) :=
    pgH_desc_measurable hPT d ρ hd hρ K hK
  have h_bound : ∀ a, |pgH K (pgDescent K ρ a)| ≤ C := by
    intro a
    apply hC
    exact pgDescent_mem d ρ hd hρ K a
  refine MeasureTheory.Integrable.mono' (integrable_const C) h_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro a
  simpa using h_bound a

theorem pgAccurate_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) (x : PgSp d) : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | PgAccurate K ρ x w} := by
  have hFt_meas (i : ℕ) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgFt K ρ x (w i)) := by
    have h_pair : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (x, w i)) :=
      Measurable.prodMk measurable_const (measurable_pi_apply i)
    have hFt : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgFt K ρ p.1 p.2) :=
      pgFt_measurable hPT d K ρ hK
    exact hFt.comp h_pair
  have h_sumFt : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i)) :=
    Finset.measurable_sum _ (fun i hi => hFt_meas i)
  have h_pgKh : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgKh K ρ x w) := by
    unfold pgKh
    have : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ *
        (∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i))) =
        (fun s : ℝ => (pgNT d ρ : ℝ)⁻¹ * s) ∘
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i)) := rfl
    rw [this]
    exact (measurable_const_mul _).comp h_sumFt
  have h1 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => |pgKh K ρ x w - pgKs K x|) :=
      (h_pgKh.sub measurable_const).abs
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => pgKappa / 40) := measurable_const
    exact measurableSet_le h_meas h_rhs
  have h_pgBh : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgBh K ρ x w) := by
    unfold pgBh
    have h_sum : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i) :=
      Finset.measurable_sum _ (fun i hi => (hFt_meas i).smul (measurable_pi_apply i))
    have : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ •
        (∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i)) =
        (fun s : EuclideanSpace ℝ (Fin d) => (pgNT d ρ : ℝ)⁻¹ • s) ∘
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i) := rfl
    rw [this]
    exact (measurable_const_smul _).comp h_sum
  have h2 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => ‖pgBh K ρ x w - pgBs K x‖) :=
      (h_pgBh.sub measurable_const).norm
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => pgTaub d ρ / 4) := measurable_const
    exact measurableSet_le h_meas h_rhs
  have h_apply (i : Fin d) : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
    have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
      simpa using PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
    exact h_cont.measurable
  have h_meas_pgGG (i j : Fin d) : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => pgGG g i j) := by
    unfold pgGG
    have h_mul : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i * g j) :=
      (h_apply i).mul (h_apply j)
    have h_sub : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
        g i * g j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) :=
      h_mul.sub measurable_const
    simpa [Matrix.vecMulVec_apply, Matrix.one_apply] using h_sub
  have h_pgQh (i j : Fin d) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgQh K ρ x w i j) := by
    unfold pgQh
    have h_meas_entry (k : ℕ) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgFt K ρ x (w k) * pgGG (w k) i j) :=
      (hFt_meas k).mul ((h_meas_pgGG i j).comp (measurable_pi_apply k))
    have h_sum : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) * pgGG (w k) i j) :=
      Finset.measurable_sum _ (fun k hk => h_meas_entry k)
    have h_eq : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => ((pgNT d ρ : ℝ)⁻¹ •
        (∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) • pgGG (w k))) i j) =
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ *
        (∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) * pgGG (w k) i j)) := by
      ext w
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
    rw [h_eq]
    exact (measurable_const_mul _).comp h_sum
  have h3 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) |
      ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2) := by
      refine Finset.measurable_sum Finset.univ (fun i hi => ?_)
      refine Finset.measurable_sum Finset.univ (fun j hj => ?_)
      have h_sub : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgQh K ρ x w i j - pgQs K x i j) :=
        (h_pgQh i j).sub (measurable_const (a := pgQs K x i j))
      have h_mul := h_sub.mul h_sub
      convert h_mul using 1
      ext w
      simp [sq]
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => (pgKappa / (8 * d)) ^ 2) := measurable_const
    exact measurableSet_le h_meas h_rhs
  have h_acc : {w : ℕ → EuclideanSpace ℝ (Fin d) | PgAccurate K ρ x w} =
      ({w | |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40} ∩
      {w | ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4}) ∩
      {ω | ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2 ≤ (pgKappa / (8 * d)) ^ 2} := by
    ext w; simp [PgAccurate, and_assoc]
  rw [h_acc]
  exact (h1.inter h2).inter h3

/-! ## Leaves: generic measure theory -/

theorem markov_half {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (c e : ℝ) (he : 0 < e) (hc : ∀ ω, c ≤ f ω) (hint : ∫ ω, f ω ∂μ ≤ c + e / 2) :
    μ {ω | c + e < f ω} ≤ ENNReal.ofReal (1 / 2) := by
  -- Let g = f - c, which is nonnegative
  have hg_nonneg : 0 ≤ᵐ[μ] (fun ω => f ω - c) := by
    filter_upwards [] with ω
    have h := hc ω
    have : 0 ≤ f ω - c := by linarith
    exact this
  have hg_int : Integrable (fun ω => f ω - c) μ :=
    hf.sub (integrable_const c)
  -- Apply Markov's inequality: e * μ.real {ω | e ≤ f ω - c} ≤ ∫ (f - c) dμ
  have h_markov : e * μ.real {ω | e ≤ f ω - c} ≤ ∫ ω, (f ω - c) ∂μ :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hg_nonneg hg_int e
  -- Compute ∫ (f - c) dμ = ∫ f dμ - c
  have h_int_sub : ∫ ω, (f ω - c) ∂μ = (∫ ω, f ω ∂μ) - c := by
    calc
      ∫ ω, (f ω - c) ∂μ = (∫ ω, f ω ∂μ) - (∫ ω, c ∂μ) := integral_sub hf (integrable_const c)
      _ = (∫ ω, f ω ∂μ) - c := by simp
  -- From hint: ∫ f dμ ≤ c + e/2, so ∫ (f - c) dμ ≤ e/2
  have h_int_bound : ∫ ω, (f ω - c) ∂μ ≤ e / 2 := by
    linarith
  -- Combine: e * μ.real {ω | e ≤ f ω - c} ≤ e/2, so μ.real ≤ 1/2 (since e > 0)
  have h_real_bound : μ.real {ω | e ≤ f ω - c} ≤ 1 / 2 := by
    have h_mul : e * μ.real {ω | e ≤ f ω - c} ≤ e / 2 := by
      linarith
    nlinarith
  -- Set inclusion: {ω | c + e < f ω} ⊆ {ω | e ≤ f ω - c}
  have h_subset : {ω | c + e < f ω} ⊆ {ω | e ≤ f ω - c} := by
    intro ω hω
    have h : c + e < f ω := hω
    have : e ≤ f ω - c := by linarith
    exact this
  -- Use measure_mono for the inclusion
  have h_meas_le : μ {ω | c + e < f ω} ≤ μ {ω | e ≤ f ω - c} :=
    measure_mono h_subset
  -- The measure is finite (probability measure)
  have h_finite : μ {ω | e ≤ f ω - c} ≠ ⊤ :=
    measure_ne_top μ _
  -- Convert to ENNReal.ofReal using ENNReal.ofReal_toReal
  calc
    μ {ω | c + e < f ω} ≤ μ {ω | e ≤ f ω - c} := h_meas_le
    _ = ENNReal.ofReal ((μ {ω | e ≤ f ω - c}).toReal) := by
      rw [ENNReal.ofReal_toReal h_finite]
    _ = ENNReal.ofReal (μ.real {ω | e ≤ f ω - c}) := rfl
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal h_real_bound

theorem prod_small_slices {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set (X × Y)) (hS : MeasurableSet S) (c : ENNReal) :
    (μ.prod ν) {p | p ∈ S ∧ ν (Prod.mk p.1 ⁻¹' S) ≤ c} ≤ c := by
  -- Define the function f(x) = ν(Prod.mk x ⁻¹' S), which is measurable
  let f : X → ENNReal := fun x => ν (Prod.mk x ⁻¹' S)
  have hf : Measurable f := measurable_measure_prodMk_left hS
  -- The set we are measuring is {p | p ∈ S ∧ f(p.1) ≤ c}
  -- Let T be this set
  let T : Set (X × Y) := {p | p ∈ S ∧ f p.1 ≤ c}
  have hT : MeasurableSet T := by
    -- T = S ∩ {p | f p.1 ≤ c}
    -- {p | f p.1 ≤ c} = {p | p.1 ∈ f⁻¹' {y | y ≤ c}}
    -- f⁻¹' {y | y ≤ c} is measurable because f is measurable and {y | y ≤ c} is measurable
    have h_preimage : MeasurableSet {p : X × Y | f p.1 ≤ c} := by
      -- The function p ↦ f p.1 is measurable (composition of measurable f with projection)
      have h_comp : Measurable (fun (p : X × Y) => f p.1) :=
        hf.comp measurable_fst
      -- {p | f p.1 ≤ c} = (fun p => f p.1)⁻¹' {y | y ≤ c}
      -- {y | y ≤ c} is measurable in ENNReal
      exact measurableSet_le h_comp measurable_const
    -- T = S ∩ {p | f p.1 ≤ c}
    exact hS.inter h_preimage
  -- Now use the product measure formula
  rw [MeasureTheory.Measure.prod_apply hT]
  -- Goal: ∫⁻ x, ν (Prod.mk x ⁻¹' T) ∂μ ≤ c
  -- For each x, ν (Prod.mk x ⁻¹' T) ≤ c
  -- Because if f(x) ≤ c, then Prod.mk x ⁻¹' T = Prod.mk x ⁻¹' S, and ν(Prod.mk x ⁻¹' S) = f(x) ≤ c
  -- If f(x) > c, then Prod.mk x ⁻¹' T = ∅, and ν(∅) = 0 ≤ c
  have h_bound : ∀ x, ν (Prod.mk x ⁻¹' T) ≤ c := by
    intro x
    by_cases hx : f x ≤ c
    · -- In this case, Prod.mk x ⁻¹' T = Prod.mk x ⁻¹' S
      have h_slice_eq : Prod.mk x ⁻¹' T = Prod.mk x ⁻¹' S := by
        ext y
        constructor
        · intro hy
          have : (x, y) ∈ T := hy
          -- T = {p | p ∈ S ∧ f p.1 ≤ c}
          -- So (x, y) ∈ T implies (x, y) ∈ S
          rcases this with ⟨hS_mem, _⟩
          exact hS_mem
        · intro hy
          have hS_mem : (x, y) ∈ S := hy
          -- Need to show (x, y) ∈ T, i.e., (x, y) ∈ S ∧ f x ≤ c
          -- We have hS_mem and hx
          refine ⟨hS_mem, hx⟩
      rw [h_slice_eq]
      -- Now ν (Prod.mk x ⁻¹' S) = f x ≤ c
      -- But f x is defined as ν (Prod.mk x ⁻¹' S)
      -- So we need to unfold f
      -- Actually, the goal is ν (Prod.mk x ⁻¹' S) ≤ c, and f x = ν (Prod.mk x ⁻¹' S)
      -- So this is exactly hx
      -- But hx : f x ≤ c, and we need ν (Prod.mk x ⁻¹' S) ≤ c
      -- We need to unfold f
      -- Let me use `show f x ≤ c from hx` after rewriting
      -- Actually, the goal is `ν (Prod.mk x ⁻¹' S) ≤ c`
      -- And `f x` is defined as `ν (Prod.mk x ⁻¹' S)`
      -- So `hx : f x ≤ c` is exactly `ν (Prod.mk x ⁻¹' S) ≤ c` after unfolding
      -- Let me use `simpa [f] using hx`
      simpa [f] using hx
    · -- f x > c, so T contains no point (x, y)
      -- Prod.mk x ⁻¹' T = ∅
      have h_slice_empty : Prod.mk x ⁻¹' T = ∅ := by
        ext y
        constructor
        · intro hy
          have : (x, y) ∈ T := hy
          rcases this with ⟨_, hfy⟩
          -- hfy : f x ≤ c, but we have ¬ f x ≤ c
          exact absurd hfy hx
        · intro hy
          exfalso
          exact hy
      rw [h_slice_empty]
      -- ν ∅ = 0 ≤ c
      rw [measure_empty]
      exact zero_le (a := c)
  -- Now we have ∫⁻ x, ν (Prod.mk x ⁻¹' T) ∂μ ≤ ∫⁻ x, c ∂μ
  -- by lintegral_mono
  -- And ∫⁻ x, c ∂μ = c * μ univ = c * 1 = c
  calc
    ∫⁻ x, ν (Prod.mk x ⁻¹' T) ∂μ ≤ ∫⁻ x, c ∂μ := lintegral_mono h_bound
    _ = c * (μ Set.univ) := by rw [lintegral_const]
    _ = c * 1 := by rw [measure_univ]
    _ = c := by simp

theorem prod_compl_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set (X × Y)) (hS : MeasurableSet S) (G : Set X)
    (hG : MeasurableSet G) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hGS : ∀ x ∈ G, ν {y | (x, y) ∉ S} ≤ ENNReal.ofReal c) (hGc : μ Gᶜ ≤ ENNReal.ofReal (1 / 2)) :
    (μ.prod ν) Sᶜ ≤ ENNReal.ofReal ((1 + c) / 2) := by
  have hprod_compl : (μ.prod ν) Sᶜ = ∫⁻ x, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ := by
    rw [Measure.prod_apply hS.compl]
  rw [hprod_compl]
  have hsplit : (∫⁻ x, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) =
      (∫⁻ x in G, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) + (∫⁻ x in Gᶜ, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) := by
    rw [lintegral_add_compl (fun x => ν (Prod.mk x ⁻¹' Sᶜ)) hG]
  rw [hsplit]
  have hG_meas : Measurable fun (x : X) => ν (Prod.mk x ⁻¹' Sᶜ) :=
    measurable_measure_prodMk_left_finite hS.compl
  have hG_int : (∫⁻ x in G, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) ≤ (∫⁻ _ in G, ENNReal.ofReal c ∂μ) := by
    refine setLIntegral_mono measurable_const (fun x hx => hGS x hx)
  have hGc_int : (∫⁻ x in Gᶜ, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) ≤ (∫⁻ _ in Gᶜ, (1 : ENNReal) ∂μ) := by
    refine setLIntegral_mono measurable_const (fun x hx => ?_)
    calc
      ν (Prod.mk x ⁻¹' Sᶜ) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = (1 : ENNReal) := by simp
  have hG_const : (∫⁻ _ in G, ENNReal.ofReal c ∂μ) = ENNReal.ofReal c * μ G := by
    simp
  have hGc_const : (∫⁻ _ in Gᶜ, (1 : ENNReal) ∂μ) = μ Gᶜ := by
    simp
  have h_total : (∫⁻ x in G, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) + (∫⁻ x in Gᶜ, ν (Prod.mk x ⁻¹' Sᶜ) ∂μ) ≤
      ENNReal.ofReal c * μ G + μ Gᶜ := by
    have h_add := add_le_add hG_int hGc_int
    simpa [hG_const, hGc_const] using h_add
  have h_final : ENNReal.ofReal c * μ G + μ Gᶜ ≤ ENNReal.ofReal ((1 + c) / 2) := by
    have hG_finite : μ G ≠ ⊤ := by
      exact ne_of_lt (measure_lt_top μ G)
    have hGc_finite : μ Gᶜ ≠ ⊤ := by
      exact ne_of_lt (measure_lt_top μ Gᶜ)
    have h_sum : μ G + μ Gᶜ = 1 := by
      have h := measure_add_measure_compl (μ := μ) hG
      simpa [measure_univ] using h
    have h_sum_toReal : (μ G).toReal + (μ Gᶜ).toReal = 1 := by
      simpa [ENNReal.toReal_add hG_finite hGc_finite, ENNReal.toReal_one] using congrArg ENNReal.toReal h_sum
    set p := (μ Gᶜ).toReal with hp_def
    have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
    have hp_le_half : p ≤ 1/2 := by
      have h_toReal := (ENNReal.toReal_le_toReal hGc_finite (by simp)).mpr hGc
      simpa [hp_def, ENNReal.toReal_ofReal] using h_toReal
    have hG_toReal : (μ G).toReal = 1 - p := by
      linarith [h_sum_toReal]
    have h_real : c * (1 - p) + p ≤ (1 + c) / 2 := by
      have h_nonneg : 0 ≤ 1 - c := by linarith
      have h_ineq : (1 - c) * p ≤ (1 - c) * (1/2) := by
        gcongr
      linarith
    have h_left : ENNReal.ofReal c * μ G + μ Gᶜ = ENNReal.ofReal (c * (1 - p) + p) := by
      calc
        ENNReal.ofReal c * μ G + μ Gᶜ
            = ENNReal.ofReal c * ENNReal.ofReal ((μ G).toReal) + ENNReal.ofReal p := by
              simp [hp_def, ENNReal.ofReal_toReal hG_finite]
        _ = ENNReal.ofReal (c * (μ G).toReal) + ENNReal.ofReal p := by
              simp [ENNReal.ofReal_mul hc0]
        _ = ENNReal.ofReal (c * (1 - p)) + ENNReal.ofReal p := by rw [hG_toReal]
        _ = ENNReal.ofReal (c * (1 - p) + p) := by
              rw [ENNReal.ofReal_add (by
                have : 0 ≤ 1 - p := by linarith
                exact mul_nonneg hc0 this
              ) hp_nonneg]
    rw [h_left]
    exact ENNReal.ofReal_le_ofReal h_real
  exact le_trans h_total h_final

theorem slice_resample {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (i : ℕ)
    (C : Set ((ℕ → X) × X)) (hC : MeasurableSet C)
    (hdep : ∀ (ω : ℕ → X) (x x' : X), (Function.update ω i x', x) ∈ C ↔ (ω, x) ∈ C) (ε : ENNReal)
    (hε : ∀ ω, ν {x | (ω, x) ∈ C} ≤ ε) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω | (ω, ω i) ∈ C} ≤ ε := by
  classical
  set P := Measure.infinitePi fun _ : ℕ => ν with hP
  let Φ : (ℕ → X) × X → ℕ → X := fun p => Function.update p.1 i p.2
  have hΦ : Measurable Φ := measurable_update' (a := i)
  have hmap : (P.prod ν).map Φ = P := by
    refine Measure.eq_infinitePi _ ?_
    intro s t ht
    rw [Measure.map_apply hΦ (MeasurableSet.pi s.countable_toSet fun j _ => ht j)]
    have hpre : Φ ⁻¹' Set.pi (↑s) t =
        Set.pi (↑(s.erase i)) t ×ˢ (if i ∈ s then t i else Set.univ) := by
      ext ⟨ω, x⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase, Φ]
      constructor
      · intro h
        refine ⟨fun j ⟨hji, hj⟩ => ?_, ?_⟩
        · have := h j hj
          rwa [Function.update_of_ne hji] at this
        · split_ifs with hi
          · have := h i hi
            rwa [Function.update_self] at this
          · exact Set.mem_univ _
      · rintro ⟨h1, h2⟩ j hj
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          simpa [hj] using h2
        · rw [Function.update_of_ne hji]
          exact h1 j ⟨hji, hj⟩
    rw [hpre, Measure.prod_prod, hP, Measure.infinitePi_pi _ (fun j _ => ht j)]
    split_ifs with hi
    · rw [← Finset.mul_prod_erase s _ hi, mul_comm]
    · simp [Finset.erase_eq_of_notMem hi]
  have hset : MeasurableSet {ω : ℕ → X | (ω, ω i) ∈ C} :=
    hC.preimage (measurable_id.prodMk (measurable_pi_apply i))
  calc P {ω | (ω, ω i) ∈ C} = (P.prod ν).map Φ {ω | (ω, ω i) ∈ C} := by rw [hmap]
    _ = (P.prod ν) (Φ ⁻¹' {ω | (ω, ω i) ∈ C}) := Measure.map_apply hΦ hset
    _ = (P.prod ν) C := by
        congr 1
        ext ⟨ω, x⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Φ, Function.update_self]
        exact hdep ω x x
    _ = ∫⁻ ω, ν (Prod.mk ω ⁻¹' C) ∂P := Measure.prod_apply hC
    _ ≤ ∫⁻ _, ε ∂P := lintegral_mono fun ω => hε ω
    _ = ε := by simp

/-! ## Assemblies: Theorem F.3 -/

/-- The interface statements read by the proof of Theorem F.3. -/
structure PgCoreHyps : Prop where
  hPT : PiTildeMeasurable
  hLB : LemmaB
  hD4 : D4Bounds
  hEta : PgEtaSq
  hVec : VecCS
  hMat : MatCS
  hFrob : FrobStat
  hMom : MomentsE
  hCheb : ChebAvg
  hBT : PgBiasTest
  hCnt : PgCounts
  hMH : MajorityHoeffding
  hHo : PgHoeffding
  hD5 : D5Subgrad
  hL : LemmaLSym
  hD1 : D1Bounds
  hD1i : D1Inv
  hR : LemmaLRadii
  hG : GaussConst
  hAi : PropAi
  hAii : PropAii
  hAiii : PropAiii
  hPAi : PgPropAi
  hCAi : PgCorAi
  hCAii : PgCorAii
  hCAiii : PgCorAiii
  hCaB : PropCaBound
  hCb : PropCb
  hCc : PropCc
  hNM : NormMeanLower
  hConc : PgConclusion
  hQ : PgQtail
  hSgd : SgdExpect
  hStep : PgStep
  hBD : PgBiasDescent
  hFail : PgFailure
  hSome : RoundsSomeHit
  hAll : RoundsAllMiss

theorem pgNotAccurate_le (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) {w | ¬ PgAccurate K ρ x w} ≤
      ENNReal.ofReal (1 / 4) := by
  have hsub : {w | ¬ PgAccurate K ρ x w} ⊆
      {w | pgKappa / 40 < |pgKh K ρ x w - pgKs K x|} ∪ {w | pgTaub d ρ / 4 < ‖pgBh K ρ x w - pgBs K x‖} ∪
        {w | (pgKappa / (8 * d)) ^ 2 < ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2} := by
    intro w hw
    simp only [PgAccurate, Set.mem_ofPred_eq, Set.mem_union] at hw ⊢
    by_contra h
    push Not at h
    exact hw ⟨h.1.1, h.1.2, h.2⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add
    (pgLemmaT_k H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x hx)
    (pgLemmaT_b H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x hx)))
    (pgLemmaT_Q H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x
      hx)).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem pgTest_unsound (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (hns : ¬ PgSound K ρ x) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {W | pgTest K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ) := by
  have hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j := fun v =>
    posQ_eq_sum K hK.1 hK.2.2.1 (pgMu x) (pgOp x) v v
  have hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdict K ρ x w} := by
    have h := (pgVerdict_measurableSet H.hPT d K ρ hK.2.1).preimage (measurable_prodMk_left (x := x))
    exact h
  refine (pgAmplify H.hMH H.hHo d K ρ δ hδ0 hδ1 x {w | ¬ PgAccurate K ρ x w}
    (pgAccurate_measurableSet H.hPT d K ρ hK.2.1 x).compl (pgNotAccurate_le H d ρ hd hρ K hK x hx) hmeas).1 ?_
  intro w hv hacc
  exact hns (pgVerdict_sound d ρ hd K x hQ w hacc hv)

theorem pgTest_complete (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ)
    (hc : PgComplete K ρ x) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {W | ¬ pgTest K ρ δ x W} ≤ ENNReal.ofReal (pgDp δ) := by
  have hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j := fun v =>
    posQ_eq_sum K hK.1 hK.2.2.1 (pgMu x) (pgOp x) v v
  have hmeas : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | pgVerdict K ρ x w} := by
    have h := (pgVerdict_measurableSet H.hPT d K ρ hK.2.1).preimage (measurable_prodMk_left (x := x))
    exact h
  refine (pgAmplify H.hMH H.hHo d K ρ δ hδ0 hδ1 x {w | ¬ PgAccurate K ρ x w}
    (pgAccurate_measurableSet H.hPT d K ρ hK.2.1 x).compl (pgNotAccurate_le H d ρ hd hρ K hK x hx) hmeas).2 ?_
  intro w hv hacc
  exact hv (pgVerdict_complete d ρ hd K x hQ w hacc hc)

theorem pgDescent_expect (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (xs : PgSp d) (hxs : xs ∈ pgDom d ρ)
    (hmin : ∀ y ∈ pgDom d ρ, pgH K xs ≤ pgH K y) :
    ∫ a, pgH K (pgDescent K ρ a) ∂(Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      pgH K xs + pgEh d ρ / 2 := by
  have hne : (pgDom d ρ).Nonempty := ⟨_, pgX1_mem d ρ hd hρ⟩
  have hcpt := pgDom_isCompact d ρ
  have hcv := pgDom_convex d ρ
  obtain ⟨hpm, hpne, -⟩ := pgProj_spec d ρ hne hcpt.isClosed hcv
  have hS := H.hSgd (PgSp d) (EuclideanSpace ℝ (Fin d)) (stdGaussian (EuclideanSpace ℝ (Fin d))) (pgDom d ρ)
    (pgProj d ρ) (pgH K) (pgGam K) (pgV K ρ) xs (pgX1 d ρ) (pgDelta d ρ) (pgStepSize d ρ) (pgG2 d ρ) (pgBeta d ρ)
    (pgNs d ρ) hcpt hcv (pgH_continuousOn d ρ hd hρ K hK) (pgProj_continuous d ρ hd hρ) hpm hpne
    (pgV_measurable H.hPT d K ρ hK.2.1) (pgX1_mem d ρ hd hρ) hxs hmin (pgDom_diam d ρ hd hρ)
    (pgGam_subgrad H.hD5 d ρ hd hρ K hK) (fun x hx => ⟨(pgV_integrable H.hPT H.hLB H.hD4 H.hEta d ρ hd hρ K hK x hx).1,
      (pgV_integrable H.hPT H.hLB H.hD4 H.hEta d ρ hd hρ K hK x hx).2,
      pgV_bias H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat d ρ hd hρ K hK x hx,
      pgV_second_moment H.hPT H.hLB H.hD4 H.hEta H.hFrob H.hMom d ρ hd hρ K hK x hx⟩)
    (pgStepSize_pos d ρ hd hρ) (pgNs_pos d ρ hd hρ)
  have harith := pgStep_arith H.hStep d ρ hd hρ
  have hbias : pgBeta d ρ * pgDelta d ρ ≤ pgEh d ρ / 4 := H.hBD d ρ (by exact_mod_cast hd) hρ
  have hS' : ∫ a, pgH K (pgDescent K ρ a) ∂(Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ pgH K xs + pgDelta d ρ ^ 2 / (2 * pgStepSize d ρ * pgNs d ρ) + pgStepSize d ρ * pgG2 d ρ / 2 +
        pgBeta d ρ * pgDelta d ρ := hS
  linarith

theorem pgDescent_good (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    ∃ G : Set (ℕ → EuclideanSpace ℝ (Fin d)), MeasurableSet G ∧
      (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) Gᶜ ≤ ENNReal.ofReal (1 / 2) ∧
      ∀ a ∈ G, PgComplete K ρ (pgDescent K ρ a) := by
  obtain ⟨xs, hxs, hmin⟩ := pgMin_exists H.hL H.hD1 H.hD1i H.hR H.hG d ρ hd hρ K hK
  have hminD : ∀ y ∈ pgDom d ρ, pgH K xs ≤ pgH K y := fun y hy =>
    hmin (pgMu y) (pgOp y) (by rw [pgOp_det]; exact (pgDom_inv d ρ hd hρ y hy).1)
  refine ⟨{a | pgH K (pgDescent K ρ a) ≤ pgH K xs + pgEh d ρ},
    measurableSet_le (pgH_desc_measurable H.hPT d ρ hd hρ K hK) measurable_const, ?_, ?_⟩
  · have hc : ∀ a, pgH K xs ≤ pgH K (pgDescent K ρ a) := fun a => hminD _ (pgDescent_mem d ρ hd hρ K a)
    have hm := markov_half (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) _
      (pgH_desc_integrable H.hPT d ρ hd hρ K hK) (pgH K xs) (pgEh d ρ) (pgEh_pos d ρ hd hρ) hc
      (pgDescent_expect H d ρ hd hρ K hK xs hxs hminD)
    refine le_trans (le_of_eq ?_) hm
    congr 1
    ext a
    simp [not_le]
  · intro a ha
    exact pgCorA H.hAi H.hAii H.hAiii H.hD4 H.hPAi H.hCAi H.hCAii H.hCAiii d ρ hd hρ K hK _
      (pgDescent_mem d ρ hd hρ K a) (pgH K xs) hmin ha

/-- The acceptance probability of the amplified test at the average of the descent driven by `a`. -/
noncomputable def pgAccProb {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (a : ℕ → EuclideanSpace ℝ (Fin d)) : ENNReal :=
  (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
    {W | pgTest K ρ δ (pgDescent K ρ a) W}

/-- A measurable superset of the failure event of `pgCore`: a repeat accepts whose descent has acceptance probability at
most `δ'`, or no repeat accepts. -/
def pgCoreBad {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) : Set (ℕ → PgRound d) :=
  {ω | (∃ r < pgJr δ, pgTest K ρ δ (pgDescent K ρ (ω r).1) (ω r).2 ∧
      pgAccProb K ρ δ (ω r).1 ≤ ENNReal.ofReal (pgDp δ)) ∨
    ∀ r < pgJr δ, ¬ pgTest K ρ δ (pgDescent K ρ (ω r).1) (ω r).2}

theorem pgCore_good_of_not_bad (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (ω : ℕ → PgRound d)
    (hω : ω ∉ pgCoreBad K ρ δ) : PgGood d K (36.4 * d * pgLam ρ) (pgCore d K ρ δ ω) := by
  have key : ∀ r, r < pgJr δ → pgTest K ρ δ (pgDescent K ρ (ω r).1) (ω r).2 →
      PgGood d K (36.4 * d * pgLam ρ) (some (pgOut (pgDescent K ρ (ω r).1))) := by
    intro r hr hacc
    have hprob : ENNReal.ofReal (pgDp δ) < pgAccProb K ρ δ (ω r).1 := by
      by_contra h
      exact hω (Or.inl ⟨r, hr, hacc, not_lt.mp h⟩)
    have hsound : PgSound K ρ (pgDescent K ρ (ω r).1) := by
      by_contra hns
      exact absurd (pgTest_unsound H d ρ δ hd hρ hδ0 hδ1 K hK _ (pgDescent_mem d ρ hd hρ K _) hns)
        (not_le.mpr hprob)
    exact pgSound_good H.hCaB H.hCb H.hCc H.hG H.hNM H.hConc H.hQ d ρ hd hρ K hK _
      (pgDescent_mem d ρ hd hρ K _) hsound
  classical
  unfold pgCore
  split_ifs with h
  · exact key _ (Nat.find_spec h).1 (Nat.find_spec h).2
  · exact absurd (Or.inr fun r hr hacc => h ⟨r, hr, hacc⟩) hω

theorem pgCoreBad_measure (H : PgCoreHyps) (d : ℕ) (ρ δ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) :
    pgCoreMeasure d (pgCoreBad K ρ δ) ≤ ENNReal.ofReal δ := by
  obtain ⟨hJ1, hJ2, hDp0, hDp1⟩ := pgJr_spec δ hδ0 hδ1
  obtain ⟨Acc, hAccdef⟩ : ∃ Acc : Set (PgRound d), Acc = {p | pgTest K ρ δ (pgDescent K ρ p.1) p.2} := ⟨_, rfl⟩
  have hAcc : MeasurableSet Acc := by
    rw [hAccdef]
    have h := (pgTest_measurableSet H.hPT d K ρ δ hK.2.1).preimage
      (((pgDescent_measurable H.hPT d K ρ hK.2.1 (pgProj_continuous d ρ hd hρ)).comp measurable_fst).prodMk
        measurable_snd)
    exact h
  obtain ⟨B', hB'def⟩ : ∃ B' : Set (PgRound d), B' = {p | p ∈ Acc ∧
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
        (Prod.mk p.1 ⁻¹' Acc) ≤ ENNReal.ofReal (pgDp δ)} := ⟨_, rfl⟩
  have hB' : MeasurableSet B' := by
    rw [hB'def]
    exact hAcc.inter (measurableSet_le ((measurable_measure_prodMk_left hAcc).comp measurable_fst) measurable_const)
  have hB'le : pgRoundMeasure d B' ≤ ENNReal.ofReal (pgDp δ) := by
    rw [hB'def]
    exact prod_small_slices _ _ Acc hAcc _
  obtain ⟨G, hG, hGc, hGcomp⟩ := pgDescent_good H d ρ hd hρ K hK
  have hrej : pgRoundMeasure d Accᶜ ≤ ENNReal.ofReal ((1 + pgDp δ) / 2) := by
    refine prod_compl_le _ _ Acc hAcc G hG (pgDp δ) hDp0.le hDp1 (fun a ha => ?_) hGc
    have h := pgTest_complete H d ρ δ hd hρ hδ0 hδ1 K hK _ (pgDescent_mem d ρ hd hρ K a) (hGcomp a ha)
    rw [hAccdef]
    exact h
  have hsub : pgCoreBad K ρ δ ⊆ {ω | ∃ r < pgJr δ, ω r ∈ B'} ∪ {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} := by
    intro ω hω
    rcases hω with ⟨r, hr, hacc, hp⟩ | hall
    · left
      refine ⟨r, hr, ?_⟩
      rw [hB'def, hAccdef]
      exact ⟨hacc, hp⟩
    · right
      intro r hr
      rw [hAccdef]
      exact hall r hr
  have h1 : pgCoreMeasure d {ω | ∃ r < pgJr δ, ω r ∈ B'} ≤ pgJr δ * ENNReal.ofReal (pgDp δ) :=
    (H.hSome (PgRound d) (pgRoundMeasure d) B' hB' (pgJr δ)).trans (by gcongr)
  have h2 : pgCoreMeasure d {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} ≤ ENNReal.ofReal ((1 + pgDp δ) / 2) ^ pgJr δ :=
    (H.hAll (PgRound d) (pgRoundMeasure d) Accᶜ hAcc.compl (pgJr δ)).le.trans (ENNReal.pow_le_pow_left hrej)
  have hfail := H.hFail δ hδ0 hδ1 (pgJr δ) hJ1 hJ2
  have hDp : pgDp δ = δ / (2 * pgJr δ) := rfl
  have hfin : (pgJr δ : ℝ) * pgDp δ + ((1 + pgDp δ) / 2) ^ pgJr δ ≤ δ := by
    rw [hDp]; linarith
  calc pgCoreMeasure d (pgCoreBad K ρ δ)
      ≤ pgCoreMeasure d ({ω | ∃ r < pgJr δ, ω r ∈ B'} ∪ {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ}) := measure_mono hsub
    _ ≤ pgCoreMeasure d {ω | ∃ r < pgJr δ, ω r ∈ B'} + pgCoreMeasure d {ω | ∀ r < pgJr δ, ω r ∈ Accᶜ} :=
        measure_union_le _ _
    _ ≤ pgJr δ * ENNReal.ofReal (pgDp δ) + ENNReal.ofReal ((1 + pgDp δ) / 2) ^ pgJr δ := add_le_add h1 h2
    _ = ENNReal.ofReal (pgJr δ * pgDp δ + ((1 + pgDp δ) / 2) ^ pgJr δ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hfin

theorem pgCoreThm_of (H : PgCoreHyps) : PgCoreThm := by
  intro d K ρ δ hd hKc hKcl h1 hKρ hρ hδ0 hδ1
  have hK : PgBody K ρ := ⟨hKc, hKcl, h1, hKρ⟩
  refine le_trans (measure_mono ?_) (pgCoreBad_measure H d ρ δ hd hρ hδ0 hδ1 K hK)
  intro ω hω
  by_contra hb
  exact hω (pgCore_good_of_not_bad H d ρ δ hd hρ hδ0 hδ1 K hK ω hb)

/-- The hypotheses of Theorem F.3 from the delivered theorems, except the five statements of `PgProb.lean` whose
proofs are in `PgProbProof.lean`. -/
theorem pgCoreHyps_of (hCheb : ChebAvg) (hSgd : SgdExpect) (hMH : MajorityHoeffding) (hSome : RoundsSomeHit)
    (hAll : RoundsAllMiss) : PgCoreHyps where
  hPT := piTildeMeasurable
  hLB := lemmaB
  hD4 := d4Bounds
  hEta := pgEtaSq
  hVec := vecCS
  hMat := matCS
  hFrob := frobStat
  hMom := momentsE
  hCheb := hCheb
  hBT := pgBiasTest
  hCnt := pgCounts
  hMH := hMH
  hHo := pgHoeffding
  hD5 := d5Subgrad
  hL := lemmaLSym
  hD1 := d1Bounds
  hD1i := d1Inv
  hR := lemmaLRadii
  hG := gaussConst
  hAi := propAi
  hAii := propAii
  hAiii := propAiii
  hPAi := pgPropAi
  hCAi := pgCorAi
  hCAii := pgCorAii
  hCAiii := pgCorAiii
  hCaB := propCaBound
  hCb := propCb
  hCc := propCc
  hNM := normMeanLower
  hConc := pgConclusion
  hQ := pgQtail
  hSgd := hSgd
  hStep := pgStep
  hBD := pgBiasDescent
  hFail := pgFailure
  hSome := hSome
  hAll := hAll

/-! ## Leaves: the stages of Theorem 8.3 -/

theorem pgStage_dep (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ) (i : ℕ)
    (ω ω' : ℕ → ℕ → PgRound d) (h : ∀ j < i, ω j = ω' j) :
    pgStage d K r0 δ' ω i = pgStage d K r0 δ' ω' i := by
  induction' i with i ih
  · rfl
  · simp only [pgStage]
    rw [ih (fun j hj => h j (by omega)), h i (by omega)]

theorem pgStage_eq_pg (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (r0 δ' : ℝ) (hr0 : 0 < r0) (i : ℕ)
    (hi : 1 ≤ i) (ω : ℕ → ℕ → PgRound d) :
    pgStage d K r0 δ' ω i = pg d K r0 (2 ^ i * r0) (i * δ') ω := by
  have hi' : (i : ℝ) ≠ 0 := by
    intro hzero
    have : (i : ℕ) = 0 := by exact_mod_cast hzero
    linarith
  have hlog : Real.logb (2 : ℝ) ((2 : ℝ) ^ (i : ℕ)) = (i : ℝ) := by
    rw [Real.logb_pow]
    rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
    ring
  have hstages : pgStages r0 (2 ^ i * r0) = i := by
    unfold pgStages
    have hdiv : (2 ^ i * r0) / r0 = (2 : ℝ) ^ (i : ℕ) := by
      field_simp [ne_of_gt hr0]
    rw [hdiv, hlog]
    rw [Nat.ceil_natCast i]
    exact max_eq_right hi
  unfold pg
  rw [hstages]
  field_simp [hi']

theorem pgStages_spec (r0 R0 : ℝ) (hr0 : 0 < r0) (hR : r0 ≤ R0) :
    1 ≤ pgStages r0 R0 ∧ R0 ≤ 2 ^ pgStages r0 R0 * r0 := by
  have hRpos : 0 < R0 := hr0.trans_le hR
  have hxpos : 0 < R0 / r0 := div_pos hRpos hr0
  have hlog := Real.rpow_logb (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1) hxpos
  have hceil : Real.logb 2 (R0 / r0) ≤ (⌈Real.logb 2 (R0 / r0)⌉₊ : ℝ) := Nat.le_ceil _
  have hmax : (⌈Real.logb 2 (R0 / r0)⌉₊ : ℝ) ≤ (pgStages r0 R0 : ℝ) := by
    have h := le_max_right (1 : ℕ) ⌈Real.logb 2 (R0 / r0)⌉₊
    exact mod_cast h
  have h_exp : Real.logb 2 (R0 / r0) ≤ (pgStages r0 R0 : ℝ) :=
    le_trans hceil hmax
  have h_rpow : (2 : ℝ) ^ Real.logb 2 (R0 / r0) ≤ (2 : ℝ) ^ (pgStages r0 R0 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) h_exp
  have h_eq : (2 : ℝ) ^ (pgStages r0 R0 : ℝ) = 2 ^ pgStages r0 R0 := by
    simpa using Real.rpow_natCast (2 : ℝ) (pgStages r0 R0)
  have h_div_le : R0 / r0 ≤ 2 ^ pgStages r0 R0 := by
    calc
      R0 / r0 = (2 : ℝ) ^ Real.logb 2 (R0 / r0) := by symm; exact hlog
      _ ≤ (2 : ℝ) ^ (pgStages r0 R0 : ℝ) := h_rpow
      _ = 2 ^ pgStages r0 R0 := h_eq
  have h_main : R0 ≤ 2 ^ pgStages r0 R0 * r0 :=
    (div_le_iff₀ hr0).mp h_div_le
  have h_one : 1 ≤ pgStages r0 R0 := by
    simpa [pgStages] using le_max_left (1 : ℕ) ⌈Real.logb 2 (R0 / r0)⌉₊
  exact And.intro h_one h_main

theorem pgGood_iff (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (o : Option (PgSp d)) :
    PgGood d K R o ↔ o.isSome ∧ PgGood d K R (some (o.getD 0)) := by
  cases o
  · simp [PgGood]
  · rename_i val
    simp [PgGood]

theorem pgGood_mono (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R R' : ℝ) (hR : R ≤ R') (o : Option (PgSp d))
    (h : PgGood d K R o) : PgGood d K R' o := by
  rcases h with ⟨P, ho, hdet, hball1, hballR, hmw⟩
  refine ⟨P, ho, hdet, hball1, ?_, hmw⟩
  exact Set.Subset.trans hballR (Metric.closedBall_subset_closedBall hR)

theorem pgBody_mono {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ ρ' : ℝ) (h : ρ ≤ ρ') (hK : PgBody K ρ) :
    PgBody K ρ' := by
  rcases hK with ⟨hconv, hclosed, hball1, hballρ⟩
  refine ⟨hconv, hclosed, hball1, ?_⟩
  exact hballρ.trans (Metric.closedBall_subset_closedBall h)

theorem posBody_pgComp {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (P P' : PgSp d) :
    posBody (posBody K (pgMu P) (pgOp P)) (pgMu P') (pgOp P') = posBody K (pgMu (pgComp P P')) (pgOp (pgComp P P')) := by
  ext y
  simp only [posBody, Set.mem_setOf_eq]
  have h_mu : pgMu (pgComp P P') = pgMu P + pgOp P (pgMu P') := by
    dsimp [pgComp, pgMu, pgOp, pgPack]
    apply WithLp.toLp_add
  have h_mat : ∀ i j, pgMat (pgComp P P') i j = (pgMat P * pgMat P') i j := by
    intro i j
    dsimp [pgComp, pgMat, pgPack, WithLp.toLp]
  have h_op : pgOp (pgComp P P') = pgOp P ∘ pgOp P' := by
    ext v
    dsimp [pgOp]
    simp [Matrix.mulVec_mulVec]
    have h : pgMat (pgComp P P') = pgMat P * pgMat P' := by
      ext i j; exact h_mat i j
    rw [h]
  have h_mu' : pgMu P + pgOp P (pgMu P' + pgOp P' y) = pgMu (pgComp P P') + pgOp (pgComp P P') y := by
    calc
      pgMu P + pgOp P (pgMu P' + pgOp P' y) = pgMu P + (pgOp P (pgMu P') + pgOp P (pgOp P' y)) := by
        rw [map_add (pgOp P)]
      _ = (pgMu P + pgOp P (pgMu P')) + pgOp P (pgOp P' y) := by abel
      _ = pgMu (pgComp P P') + pgOp (pgComp P P') y := by rw [h_mu, h_op]; rfl
  rw [h_mu']

theorem pgGood_comp (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (P P' : PgSp d) (hP : (pgMat P).det ≠ 0)
    (h : PgGood d (posBody K (pgMu P) (pgOp P)) R (some P')) : PgGood d K R (some (pgComp P P')) := by
  rcases h with ⟨Q, hQ_eq, hQ_det, hQ_ball1, hQ_ball2, hQ_mean⟩
  have hQ_eq' : P' = Q := (Option.some_inj).mp hQ_eq
  have h_det : (pgMat (pgComp P Q)).det ≠ 0 := by
    have h_mat : pgMat (pgComp P Q) = pgMat P * pgMat Q := rfl
    rw [h_mat, Matrix.det_mul]
    exact mul_ne_zero hP hQ_det
  have h_body_eq : posBody (posBody K (pgMu P) (pgOp P)) (pgMu Q) (pgOp Q) =
      posBody K (pgMu (pgComp P Q)) (pgOp (pgComp P Q)) := by
    rw [posBody_pgComp]
  rw [hQ_eq']
  refine ⟨pgComp P Q, rfl, h_det, ?_, ?_, ?_⟩
  · rw [← h_body_eq]; exact hQ_ball1
  · rw [← h_body_eq]; exact hQ_ball2
  · rw [← h_body_eq]; exact hQ_mean

theorem pgStage_body (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K) (r0 R : ℝ) (hr0 : 0 < r0) (i : ℕ) (P : PgSp d)
    (hP : (pgMat P).det ≠ 0)
    (h1 : Metric.closedBall 0 1 ⊆ posBody (K ∩ Metric.closedBall 0 (2 ^ i * r0)) (pgMu P) (pgOp P))
    (hR : posBody (K ∩ Metric.closedBall 0 (2 ^ i * r0)) (pgMu P) (pgOp P) ⊆ Metric.closedBall 0 R) :
    PgBody (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (pgMu P) (pgOp P)) (3 * R) := by
  set μ := pgMu P with hμ
  set A := pgOp P with hA
  set Ki := K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ i * r0) with hKi
  set Ki1 := K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ (i + 1) * r0) with hKi1
  set B := posBody Ki μ A with hB
  set B1 := posBody Ki1 μ A with hB1
  have hKi_cvx : Convex ℝ Ki :=
    hKc.inter (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ i * r0))
  have hKi1_cvx : Convex ℝ Ki1 :=
    hKc.inter (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ (i + 1) * r0))
  have hKi_cl : IsClosed Ki :=
    hKcl.inter (Metric.isClosed_closedBall)
  have hKi1_cl : IsClosed Ki1 :=
    hKcl.inter (Metric.isClosed_closedBall)
  -- The affine map f(y) = μ + A y
  let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
    AffineMap.mk (fun y => μ + A y) (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (by
      intro y v
      simp [add_comm, add_left_comm])
  have hf_cont : Continuous f := by
    have : Continuous (fun y : EuclideanSpace ℝ (Fin d) => μ + A y) := by
      continuity
    simpa [f] using this
  have hB1_eq : B1 = f ⁻¹' Ki1 := by
    ext y; simp [hB1, posBody, Ki1, f]
  -- Convexity of B1
  have hB1_cvx : Convex ℝ B1 := by
    rw [hB1_eq]
    exact hKi1_cvx.affine_preimage f
  -- Closedness of B1
  have hB1_cl : IsClosed B1 := by
    rw [hB1_eq]
    exact hKi1_cl.preimage hf_cont
  -- B̄(0,1) ⊆ B1
  have h_sub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ B1 := by
    have hKi_sub_Ki1 : Ki ⊆ Ki1 := by
      intro z hz
      rcases hz with ⟨hKz, hzball⟩
      refine ⟨hKz, ?_⟩
      rw [Metric.mem_closedBall] at hzball ⊢
      have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (i + 1) := by
        have hpos : 0 < (2 : ℝ) ^ i := pow_pos (by norm_num) i
        calc
          (2 : ℝ) ^ i = ((2 : ℝ) ^ i) * 1 := by ring
          _ ≤ ((2 : ℝ) ^ i) * 2 := by nlinarith
          _ = (2 : ℝ) ^ (i + 1) := by simp [pow_succ]
      nlinarith [hr0]
    have hB_sub_B1 : B ⊆ B1 := by
      intro y hy
      simp [hB, hB1, posBody] at hy ⊢
      rcases hy with ⟨hKy, hyball⟩
      exact ⟨hKy, hKi_sub_Ki1 ⟨hKy, hyball⟩ |>.2⟩
    intro y hy
    exact hB_sub_B1 (h1 hy)
  -- Outer radius: B1 ⊆ closedBall 0 (3*R)
  have hA_inj : Function.Injective A := by
    have h_unit : IsUnit (pgMat P) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      rwa [isUnit_iff_ne_zero]
    have h_mulVec_inj : Function.Injective (pgMat P).mulVec :=
      ((Matrix.mulVec_injective_iff_isUnit (A := pgMat P)).mpr h_unit)
    intro x y h
    have hA_apply : ∀ v, A v = WithLp.toLp 2 ((pgMat P) *ᵥ WithLp.ofLp v) := by
      intro v; rw [hA, AdversarialBco.Poly.pgOp_apply]
    rw [hA_apply x, hA_apply y] at h
    have h_mulVec : (pgMat P) *ᵥ WithLp.ofLp x = (pgMat P) *ᵥ WithLp.ofLp y := by
      apply WithLp.toLp_injective 2
      exact h
    have h_vec : WithLp.ofLp x = WithLp.ofLp y := h_mulVec_inj h_mulVec
    apply WithLp.ofLp_injective 2
    exact h_vec
  have hA_surj : Function.Surjective A := by
    have h_fin : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)) := by
      infer_instance
    have h_inj : Function.Injective (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      hA_inj
    exact ((LinearMap.injective_iff_surjective (f := (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))).mp h_inj)
  have h_outer : B1 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (3 * R) := by
    intro y hy
    rw [hB1, posBody] at hy
    rcases hy with ⟨hKy, hynorm⟩
    set x := μ + A y with hx
    -- hynorm : x ∈ Metric.closedBall 0 (2 ^ (i + 1) * r0)
    have hxnorm : ‖x‖ ≤ 2 ^ (i + 1) * r0 := by
      simpa [dist_eq_norm] using hynorm
    -- Since 0 ∈ B (from h1), we have μ ∈ Ki
    have h0_mem_B : (0 : EuclideanSpace ℝ (Fin d)) ∈ B := by
      have : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall]; simp
      exact h1 this
    simp [hB, posBody] at h0_mem_B
    have hμ_mem_Ki : μ ∈ Ki := by
      simpa [add_zero] using h0_mem_B
    -- 0 ∈ Ki
    have h0_mem_Ki : (0 : EuclideanSpace ℝ (Fin d)) ∈ Ki := by
      refine ⟨h0, ?_⟩
      simp [Metric.mem_closedBall, hr0.le]
    -- x/2 ∈ Ki
    have hx_half_mem_Ki : (1/2 : ℝ) • x ∈ Ki := by
      rcases hμ_mem_Ki with ⟨hμK, hμball⟩
      have hxK : (1/2 : ℝ) • x ∈ K := by
        have hmid := hKc.add_smul_sub_mem h0 hKy (by
          constructor <;> norm_num : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        simpa [sub_zero] using hmid
      have hx_half_norm : ‖(1/2 : ℝ) • x‖ ≤ 2 ^ i * r0 := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
        have hxnorm' : ‖x‖ ≤ 2 ^ (i + 1) * r0 := hxnorm
        have hineq : (1/2 : ℝ) * (2 ^ (i + 1) * r0) ≤ 2 ^ i * r0 := by
          have : (2 : ℝ) ^ i * 2 = (2 : ℝ) ^ (i + 1) := by simp [pow_succ]
          nlinarith [hr0]
        nlinarith
      exact ⟨hxK, by simpa [Metric.mem_closedBall] using hx_half_norm⟩
    -- Since A is surjective, pick y1 with μ + A y1 = x/2
    have hy1_exists : ∃ y1, μ + A y1 = (1/2 : ℝ) • x := by
      have hmem : (1/2 : ℝ) • x - μ ∈ LinearMap.range (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
        hA_surj _
      rcases hmem with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      calc
        μ + A z = μ + ((1/2 : ℝ) • x - μ) := by
          simpa [hA] using congrArg (fun t => μ + t) hz
        _ = (1/2 : ℝ) • x := by abel
    -- Since A is surjective, pick y0 with μ + A y0 = 0
    have hy0_exists : ∃ y0, μ + A y0 = 0 := by
      have hmem : (-μ) ∈ LinearMap.range (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
        hA_surj _
      rcases hmem with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      calc
        μ + A z = μ + (-μ) := by
          simpa [hA] using congrArg (fun t => μ + t) hz
        _ = 0 := by abel
    rcases hy1_exists with ⟨y1, hy1⟩
    rcases hy0_exists with ⟨y0, hy0⟩
    -- y1, y0 ∈ B
    have hy1_mem_B : y1 ∈ B := by
      rw [hB, posBody]
      simpa [hy1] using hx_half_mem_Ki
    have hy0_mem_B : y0 ∈ B := by
      rw [hB, posBody]
      simpa [hy0] using h0_mem_Ki
    -- By hR, y1, y0 ∈ closedBall 0 R
    have hy1_norm : ‖y1‖ ≤ R := by
      have : y1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := hR hy1_mem_B
      simpa [dist_eq_norm] using this
    have hy0_norm : ‖y0‖ ≤ R := by
      have : y0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := hR hy0_mem_B
      simpa [dist_eq_norm] using this
    -- Now: A (2*y1 - y0) = A y, hence 2*y1 - y0 = y by injectivity
    have hAy0 : A y0 = -μ := by
      -- hy0: μ + A y0 = 0
      calc
        A y0 = (μ + A y0) - μ := by abel
        _ = 0 - μ := by rw [hy0]
        _ = -μ := by simp
    have hAy1 : A y1 = (1/2 : ℝ) • x - μ := by
      calc
        A y1 = (μ + A y1) - μ := by abel
        _ = ((1/2 : ℝ) • x) - μ := by rw [hy1]
        _ = (1/2 : ℝ) • x - μ := rfl
    have hy_eq : (2 : ℝ) • y1 - y0 = y := by
      apply hA_inj
      calc
        A ((2 : ℝ) • y1 - y0) = (2 : ℝ) • A y1 - A y0 := by simp
        _ = (2 : ℝ) • ((1/2 : ℝ) • x - μ) - (-μ) := by rw [hAy1, hAy0]
        _ = x - μ := by
          calc
            (2 : ℝ) • ((1/2 : ℝ) • x - μ) - (-μ) = ((2 : ℝ) • ((1/2 : ℝ) • x) - (2 : ℝ) • μ) + μ := by
              simp [sub_eq_add_neg, add_assoc]
            _ = (((2 : ℝ) * (1/2 : ℝ)) • x - (2 : ℝ) • μ) + μ := by rw [smul_smul]
            _ = ((1 : ℝ) • x - (2 : ℝ) • μ) + μ := by norm_num
            _ = (x - (2 : ℝ) • μ) + μ := by simp
            _ = x - μ := by
              calc
                (x - (2 : ℝ) • μ) + μ = x + (-((2 : ℝ) • μ) + μ) := by abel
                _ = x + ((-2 : ℝ) • μ + (1 : ℝ) • μ) := by simp
                _ = x + ((-2 + 1 : ℝ) • μ) := by rw [add_smul]
                _ = x + ((-1 : ℝ) • μ) := by norm_num
                _ = x - μ := by
                  simp [sub_eq_add_neg]
        _ = A y := by
          rw [hx]
          abel
    -- Now ‖y‖ = ‖2*y1 - y0‖ ≤ 2*‖y1‖ + ‖y0‖ ≤ 2*R + R = 3*R
    have hynorm' : ‖y‖ ≤ 3 * R := by
      rw [← hy_eq]
      calc
        ‖(2 : ℝ) • y1 - y0‖ ≤ ‖(2 : ℝ) • y1‖ + ‖y0‖ := norm_sub_le _ _
        _ = ‖(2 : ℝ)‖ * ‖y1‖ + ‖y0‖ := by rw [norm_smul]
        _ = 2 * ‖y1‖ + ‖y0‖ := by norm_num
        _ ≤ 2 * R + R := by nlinarith
        _ = 3 * R := by ring
    simpa [dist_eq_norm, sub_zero] using hynorm'
  exact ⟨hB1_cvx, hB1_cl, h_sub, h_outer⟩

theorem pgStage0_body (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K) (r0 : ℝ)
    (hr0 : 0 < r0) (hK0 : Metric.closedBall 0 r0 ⊆ K) :
    (pgMat (pgPack 0 (r0 • 1) : PgSp d)).det ≠ 0 ∧
      PgBody (posBody (K ∩ Metric.closedBall 0 (2 ^ (0 + 1) * r0)) (pgMu (pgPack 0 (r0 • 1) : PgSp d))
        (pgOp (pgPack 0 (r0 • 1) : PgSp d))) (pgRhoStage d 0) := by
  set P := (pgPack 0 (r0 • 1) : PgSp d) with hP
  have hmat : pgMat P = r0 • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    simp [pgMat, pgPack, hP]
  have hmu : pgMu P = 0 := by
    ext i
    simp [pgMu, pgPack, hP]
  have hop : ∀ y, pgOp P y = r0 • y := by
    intro y
    have h := Matrix.toEuclideanCLM_toLp (𝕜 := ℝ) (n := Fin d) (r0 • (1 : Matrix (Fin d) (Fin d) ℝ)) (y.ofLp)
    calc
      pgOp P y = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (pgMat P)) y := rfl
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) y := by rw [hmat]
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) (WithLp.toLp 2 (y.ofLp)) := by simp
      _ = WithLp.toLp 2 ((r0 • (1 : Matrix (Fin d) (Fin d) ℝ)).mulVec (y.ofLp)) := by simpa using h
      _ = WithLp.toLp 2 (r0 • (y.ofLp)) := by simp [Matrix.smul_mulVec]
      _ = r0 • y := by simp
  have hrho0 : pgRhoStage d 0 = 2 := by
    simp [pgRhoStage]
  have hball : (2 : ℝ) ^ (0 + 1) * r0 = 2 * r0 := by ring
  have hposBody : posBody (K ∩ Metric.closedBall 0 (2 * r0)) (pgMu P) (pgOp P) =
      {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} := by
    ext y
    simp [posBody, hmu, hop, Metric.mem_closedBall]
  rw [hmu, hrho0, hball]
  -- Now the goal is: (pgMat P).det ≠ 0 ∧ PgBody (posBody (K ∩ Metric.closedBall 0 (2 * r0)) 0 (pgOp P)) 2
  -- We need to rewrite posBody using hposBody, but hposBody mentions pgMu P which is now 0
  -- So let's use hposBody differently
  have hposBody' : posBody (K ∩ Metric.closedBall 0 (2 * r0)) 0 (pgOp P) = {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} := by
    simpa [hmu] using hposBody
  rw [hmat, hposBody']
  simp only [PgBody, Metric.mem_closedBall]
  have hconv : Convex ℝ (K ∩ Metric.closedBall 0 (2 * r0)) :=
    hKc.inter (convex_closedBall _ _)
  have hclosed : IsClosed (K ∩ Metric.closedBall 0 (2 * r0)) :=
    hKcl.inter Metric.isClosed_closedBall
  have hcontains_ball : Metric.closedBall 0 1 ⊆ {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hy' : ‖y‖ ≤ 1 := by
      simpa [sub_zero] using hy
    have h1 : r0 • y ∈ K := by
      have hmem : r0 • y ∈ Metric.closedBall 0 r0 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h_norm : ‖r0 • y‖ = r0 * ‖y‖ := by
          simp [norm_smul, abs_of_pos hr0]
        simpa [sub_zero, h_norm] using (by
          have : r0 * ‖y‖ ≤ r0 := by nlinarith
          exact this)
      exact hK0 hmem
    have h2 : ‖r0 • y‖ ≤ 2 * r0 := by
      calc
        ‖r0 • y‖ = r0 * ‖y‖ := by simp [norm_smul, hr0.le]
        _ ≤ r0 * 1 := by gcongr
        _ = r0 := by ring
        _ ≤ 2 * r0 := by nlinarith
    exact ⟨h1, h2⟩
  have hsubset : {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} ⊆ Metric.closedBall 0 2 := by
    intro y hy
    rcases hy with ⟨hKmem, hnorm⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : ‖r0 • y‖ = r0 * ‖y‖ := by simp [norm_smul, hr0.le]
    rw [this] at hnorm
    have hpos : 0 < r0 := hr0
    have hy_norm : ‖y‖ ≤ 2 := by nlinarith
    simpa [sub_zero] using hy_norm
  have hconv_body : Convex ℝ {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} := by
    have h1 : Convex ℝ {y | r0 • y ∈ K} := by
      intro x hx y hy a b ha hb hab
      have h_eq : a • (r0 • x) + b • (r0 • y) = r0 • (a • x + b • y) := by
        simp [smul_add, smul_smul, mul_comm]
      have h_mem : a • (r0 • x) + b • (r0 • y) ∈ K := hKc hx hy ha hb hab
      simpa [h_eq] using h_mem
    have h2 : Convex ℝ {y : EuclideanSpace ℝ (Fin d) | ‖r0 • y‖ ≤ 2 * r0} := by
      intro x hx y hy a b ha hb hab
      rw [Set.mem_setOf_eq] at hx hy
      rw [Set.mem_setOf_eq]
      calc
        ‖r0 • (a • x + b • y)‖ = ‖a • (r0 • x) + b • (r0 • y)‖ := by
          simp [smul_add, smul_smul, mul_comm]
        _ ≤ ‖a • (r0 • x)‖ + ‖b • (r0 • y)‖ := norm_add_le _ _
        _ = a * ‖r0 • x‖ + b * ‖r0 • y‖ := by
          simp [norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * (2 * r0) + b * (2 * r0) := by gcongr
        _ = (a + b) * (2 * r0) := by ring
        _ = 2 * r0 := by rw [hab, one_mul]
    -- The intersection of two convex sets is convex, and {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} = {y | r0 • y ∈ K} ∩ {y | ‖r0 • y‖ ≤ 2 * r0}
    have h_eq : {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} = {y | r0 • y ∈ K} ∩ {y | ‖r0 • y‖ ≤ 2 * r0} := by
      ext y; simp
    rw [h_eq]
    exact Convex.inter h1 h2
  have hclosed_body : IsClosed {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} := by
    have h_eq : {y | r0 • y ∈ K ∧ ‖r0 • y‖ ≤ 2 * r0} = (fun y : EuclideanSpace ℝ (Fin d) => r0 • y) ⁻¹' (K ∩ Metric.closedBall 0 (2 * r0)) := by
      ext y; simp [Metric.mem_closedBall]
    rw [h_eq]
    have h_cont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => r0 • y) := by
      have h_eq : (fun y : EuclideanSpace ℝ (Fin d) => r0 • y) = (r0 • id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) := by
        ext y; simp
      rw [h_eq]
      exact continuous_const.smul continuous_id
    exact hclosed.preimage h_cont
  have hdet : (r0 • (1 : Matrix (Fin d) (Fin d) ℝ)).det ≠ 0 := by
    have hdet_val : (r0 • (1 : Matrix (Fin d) (Fin d) ℝ)).det = r0 ^ (Fintype.card (Fin d)) := by
      simp
    rw [hdet_val]
    have hpos : r0 ^ (Fintype.card (Fin d)) > 0 := pow_pos hr0 _
    linarith
  exact ⟨hdet, hconv_body, hclosed_body, hcontains_ball, hsubset⟩

theorem pgRhoStage_bounds (hGr : PgGrowing) (hConc : PgConclusion) (d : ℕ) (hd : 1 ≤ d) (i : ℕ) :
    1 ≤ pgRhoStage d i ∧ pgRhoStage d i ≤ pgRb d ∧
      3 * (36.4 * d * pgLam (pgRhoStage d i)) ≤ pgRhoStage d (i + 1) ∧
      36.4 * d * pgLam (pgRhoStage d i) ≤ 134 * d * Real.sqrt (Real.log (2 * d + 2)) := by
  have hd_real : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  -- prove Real.log 2 > 1/2, which gives sqrt(log 2) > 1/2
  have h_log2_gt_half : 1/2 < Real.log 2 := by
    have h_exp_half_lt_two : Real.exp (1/2) < 2 := by
      have h_sq : (Real.exp (1/2)) ^ 2 < 3 := by
        calc
          (Real.exp (1/2)) ^ 2 = Real.exp (1/2) * Real.exp (1/2) := by simp [sq]
          _ = Real.exp (1/2 + 1/2) := by rw [Real.exp_add]
          _ = Real.exp 1 := by ring
          _ < 3 := Real.exp_one_lt_three
      have h_pos : 0 < Real.exp (1/2) := Real.exp_pos _
      have h_lt_sqrt3 : Real.exp (1/2) < Real.sqrt 3 := by
        by_contra! hge
        have h_sq_sqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
        have h_nonneg_sqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
        have h_ge_sq : (Real.sqrt 3) ^ 2 ≤ (Real.exp (1/2)) ^ 2 := by
          simpa [sq] using mul_self_le_mul_self h_nonneg_sqrt3 hge
        linarith
      have h_sqrt3_lt_two : Real.sqrt 3 < 2 := by
        have h_lt_four : (3 : ℝ) < 4 := by norm_num
        have h := Real.sqrt_lt_sqrt (by norm_num) h_lt_four
        simpa [show (Real.sqrt 4 : ℝ) = 2 by norm_num] using h
      linarith
    have h := Real.log_lt_log (Real.exp_pos _) h_exp_half_lt_two
    simpa [Real.log_exp] using h
  have h_sqrt_log2_gt_sqrt_half : Real.sqrt (1/2) < Real.sqrt (Real.log 2) :=
    Real.sqrt_lt_sqrt (by norm_num) h_log2_gt_half
  have h_sqrt_half_gt_half : 1/2 < Real.sqrt (1/2) := by
    by_contra! hle
    have h_sq_sqrt : (Real.sqrt (1/2)) ^ 2 = 1/2 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h_nonneg_sqrt_half : 0 ≤ Real.sqrt (1/2) := Real.sqrt_nonneg _
    have h_ge_sq : (Real.sqrt (1/2)) ^ 2 ≤ ((1/2 : ℝ)) ^ 2 := by
      simpa [sq] using mul_self_le_mul_self h_nonneg_sqrt_half hle
    nlinarith
  have h_sqrt_log2_gt_half : 1/2 < Real.sqrt (Real.log 2) := by
    linarith
  -- extract conclusions from hConc
  rcases hConc with ⟨_, _, h_sqrt2, _, _⟩
  -- h_sqrt2 : 36.4 * Real.sqrt 2 ≤ 54
  have h_nonneg_d : 0 ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have h_nonneg_3d : 0 ≤ 3 * (d : ℝ) := by nlinarith
  have h_nonneg_sqrt_log2 : 0 ≤ Real.sqrt (Real.log 2) := Real.sqrt_nonneg _
  have h_nonneg_sqrt_log_ge : ∀ ρ, 0 ≤ ρ → 0 ≤ Real.sqrt (Real.log (1 + ρ)) := by
    intro ρ hρ
    apply Real.sqrt_nonneg
  induction' i with i ih
  · -- base case i = 0
    have h0 : pgRhoStage d 0 = 2 := rfl
    have h1 : 1 ≤ pgRhoStage d 0 := by
      rw [h0]
      norm_num
    have h_log4_gt_one : 1 < Real.log 4 := by
      have h_exp_one_lt_four : Real.exp 1 < 4 := by
        linarith [Real.exp_one_lt_three]
      have h := Real.log_lt_log (Real.exp_pos _) h_exp_one_lt_four
      simpa [Real.log_exp] using h
    have h2 : pgRhoStage d 0 ≤ pgRb (d : ℝ) := by
      rw [h0, pgRb]
      have h_arg : 4 ≤ 2 * (d : ℝ) + 2 := by nlinarith
      have h_log : 1 ≤ Real.log (2 * (d : ℝ) + 2) := by
        have h_log_le : Real.log 4 ≤ Real.log (2 * (d : ℝ) + 2) :=
          Real.log_le_log (by norm_num : 0 < (4 : ℝ)) h_arg
        linarith
      have h_sqrt : 1 ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
        calc
          1 = Real.sqrt (1 : ℝ) := by norm_num
          _ ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := Real.sqrt_le_sqrt h_log
      have h_400d : 400 * (d : ℝ) ≥ 400 := by nlinarith
      nlinarith
    have h3 : 3 * (36.4 * (d : ℝ) * pgLam (pgRhoStage d 0)) ≤ pgRhoStage d 1 := by
      rw [h0]
      have h_pgRhoStage1 : pgRhoStage d 1 = 3 * (54 * (d : ℝ) * Real.sqrt (Real.log 3)) := by
        rw [pgRhoStage, h0]
        norm_num
      rw [h_pgRhoStage1, pgLam]
      -- Goal: 3 * (36.4 * d * Real.sqrt (2 * Real.log (1 + 2))) ≤ 3 * (54 * d * Real.sqrt (Real.log 3))
      -- Simplify Real.log (1 + 2) to Real.log 3
      have h_simplify : Real.log (1 + 2) = Real.log 3 := by norm_num
      rw [h_simplify]
      -- Goal: 3 * (36.4 * d * Real.sqrt (2 * Real.log 3)) ≤ 3 * (54 * d * Real.sqrt (Real.log 3))
      have h_nonneg_sqrt_log3 : 0 ≤ Real.sqrt (Real.log 3) := Real.sqrt_nonneg _
      calc
        3 * (36.4 * (d : ℝ) * Real.sqrt (2 * Real.log 3))
            = 3 * (d : ℝ) * (36.4 * Real.sqrt 2) * Real.sqrt (Real.log 3) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
          ring
        _ ≤ 3 * (d : ℝ) * 54 * Real.sqrt (Real.log 3) := by
          have h_inner : (3 * (d : ℝ)) * (36.4 * Real.sqrt 2) ≤ (3 * (d : ℝ)) * 54 :=
            mul_le_mul_of_nonneg_left h_sqrt2 h_nonneg_3d
          have h_outer : (3 * (d : ℝ) * (36.4 * Real.sqrt 2)) * Real.sqrt (Real.log 3)
              ≤ (3 * (d : ℝ) * 54) * Real.sqrt (Real.log 3) :=
            mul_le_mul_of_nonneg_right h_inner h_nonneg_sqrt_log3
          simpa [mul_assoc] using h_outer
        _ = 3 * (54 * (d : ℝ) * Real.sqrt (Real.log 3)) := by ring
    have h4 : 36.4 * (d : ℝ) * pgLam (pgRhoStage d 0) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      rw [h0]
      have h_gr := hGr (d : ℝ) hd_real
      rcases h_gr with ⟨_, h_gr2⟩
      have h_nonneg_sqrt_log3 : 0 ≤ Real.sqrt (Real.log 3) := Real.sqrt_nonneg _
      calc
        36.4 * (d : ℝ) * pgLam 2
            = 36.4 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + 2)) := by simp [pgLam]
        _ = 36.4 * (d : ℝ) * Real.sqrt (2 * Real.log 3) := by norm_num
        _ = 36.4 * (d : ℝ) * (Real.sqrt 2 * Real.sqrt (Real.log 3)) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
        _ = (d : ℝ) * (36.4 * Real.sqrt 2) * Real.sqrt (Real.log 3) := by ring
        _ ≤ (d : ℝ) * 54 * Real.sqrt (Real.log 3) := by
          have h_inner : (d : ℝ) * (36.4 * Real.sqrt 2) ≤ (d : ℝ) * 54 :=
            mul_le_mul_of_nonneg_left h_sqrt2 h_nonneg_d
          have h_outer : ((d : ℝ) * (36.4 * Real.sqrt 2)) * Real.sqrt (Real.log 3)
              ≤ ((d : ℝ) * 54) * Real.sqrt (Real.log 3) :=
            mul_le_mul_of_nonneg_right h_inner h_nonneg_sqrt_log3
          simpa [mul_assoc] using h_outer
        _ = 54 * (d : ℝ) * Real.sqrt (Real.log 3) := by ring
        _ = 54 * (d : ℝ) * Real.sqrt (Real.log (1 + 2)) := by norm_num
        _ ≤ 54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRb (d : ℝ))) := by
          have h_log : Real.log 3 ≤ Real.log (1 + pgRb (d : ℝ)) := by
            have hpos : 0 < (3 : ℝ) := by norm_num
            have hle : (3 : ℝ) ≤ 1 + pgRb (d : ℝ) := by
              have h2' : (2 : ℝ) ≤ pgRb (d : ℝ) := by
                calc
                  (2 : ℝ) = pgRhoStage d 0 := by rw [h0]
                  _ ≤ pgRb (d : ℝ) := h2
              linarith
            exact Real.log_le_log hpos hle
          have h_sqrt : Real.sqrt (Real.log 3) ≤ Real.sqrt (Real.log (1 + pgRb (d : ℝ))) :=
            Real.sqrt_le_sqrt h_log
          have h_log' : Real.log (1 + 2) ≤ Real.log (1 + pgRb (d : ℝ)) := by
            simpa [show (1 : ℝ) + 2 = (3 : ℝ) by norm_num] using h_log
          have h_sqrt' : Real.sqrt (Real.log (1 + 2)) ≤ Real.sqrt (Real.log (1 + pgRb (d : ℝ))) :=
            Real.sqrt_le_sqrt h_log'
          have h_nonneg : 0 ≤ 54 * (d : ℝ) := by nlinarith
          exact mul_le_mul_of_nonneg_left h_sqrt' h_nonneg
        _ ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
          -- This is exactly h_gr2
          simpa [mul_assoc] using h_gr2
    exact ⟨h1, h2, h3, h4⟩
  · -- inductive step
    rcases ih with ⟨h1_i, h2_i, h3_i, h4_i⟩
    have h_rho_succ_nonneg : 0 ≤ pgRhoStage d (i + 1) := by
      rw [pgRhoStage]
      positivity
    -- Claim 1: 1 ≤ pgRhoStage d (i+1)
    have h1_succ : 1 ≤ pgRhoStage d (i + 1) := by
      rw [pgRhoStage]
      have h_log_ge_log2 : Real.log 2 ≤ Real.log (1 + pgRhoStage d i) :=
        Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by linarith)
      have h_sqrt_log_ge_sqrt_log2 : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log (1 + pgRhoStage d i)) :=
        Real.sqrt_le_sqrt h_log_ge_log2
      have h_nonneg_sqrt_log_rho : 0 ≤ Real.sqrt (Real.log (1 + pgRhoStage d i)) := Real.sqrt_nonneg _
      have h_47_2_pos : 0 < (54 : ℝ) := by norm_num
      have h_3_pos : 0 < (3 : ℝ) := by norm_num
      -- We need: 1 ≤ 3 * (54 * d * Real.sqrt (Real.log (1 + ρ_i)))
      -- Since d ≥ 1, 54 > 0, sqrt(log(1+ρ_i)) ≥ sqrt(log 2) > 1/2
      -- we have: 3 * 54 * d * sqrt(log(1+ρ_i)) ≥ 3 * 54 * 1 * (1/2) = 70.8 > 1
      have h_lower : 1 < 3 * (54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRhoStage d i))) := by
        calc
          1 < 3 * (54 * (1 : ℝ) * Real.sqrt (Real.log 2)) := by
            -- 3 * 54 * 1 * sqrt(log 2) > 3 * 54 * 1 * (1/2) = 70.8 > 1
            have : 1 < 3 * (54 * (1 : ℝ) * (1/2)) := by norm_num
            have h_mid : 3 * (54 * (1 : ℝ) * (1/2)) ≤ 3 * (54 * (1 : ℝ) * Real.sqrt (Real.log 2)) := by
              have h_inner : 54 * (1 : ℝ) * (1/2) ≤ 54 * (1 : ℝ) * Real.sqrt (Real.log 2) := by
                have : 1/2 < Real.sqrt (Real.log 2) := h_sqrt_log2_gt_half
                gcongr
              gcongr
            linarith
          _ ≤ 3 * (54 * (d : ℝ) * Real.sqrt (Real.log 2)) := by
            have h_d_ge_one : (1 : ℝ) ≤ (d : ℝ) := hd_real
            gcongr
          _ ≤ 3 * (54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRhoStage d i))) := by
            gcongr
      exact le_of_lt h_lower
    -- Claim 2: pgRhoStage d (i+1) ≤ pgRb (d : ℝ)
    have h2_succ : pgRhoStage d (i + 1) ≤ pgRb (d : ℝ) := by
      rw [pgRhoStage]
      have h_gr := hGr (d : ℝ) hd_real
      rcases h_gr with ⟨h_gr1, _⟩
      have h_nonneg : 0 ≤ pgRhoStage d i := by linarith
      simpa [mul_assoc] using h_gr1 (pgRhoStage d i) h_nonneg h2_i
    -- Claim 3: 3 * (36.4 * (d : ℝ) * pgLam (pgRhoStage d (i + 1))) ≤ pgRhoStage d (i + 2)
    have h3_succ : 3 * (36.4 * (d : ℝ) * pgLam (pgRhoStage d (i + 1))) ≤ pgRhoStage d (i + 2) := by
      have h_pgRhoStage_succ2 : pgRhoStage d (i + 2) = 3 * (54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1)))) := by
        simp [pgRhoStage]
      rw [h_pgRhoStage_succ2, pgLam]
      -- LHS: 3 * (36.4 * d * Real.sqrt (2 * Real.log (1 + ρ_{i+1})))
      -- RHS: 3 * (54 * d * Real.sqrt (Real.log (1 + ρ_{i+1})))
      have h_nonneg_sqrt_log : 0 ≤ Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := Real.sqrt_nonneg _
      calc
        3 * (36.4 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + pgRhoStage d (i + 1))))
            = 3 * (d : ℝ) * (36.4 * Real.sqrt 2) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
          ring
        _ ≤ 3 * (d : ℝ) * 54 * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := by
          have h_inner : (3 * (d : ℝ)) * (36.4 * Real.sqrt 2) ≤ (3 * (d : ℝ)) * 54 :=
            mul_le_mul_of_nonneg_left h_sqrt2 h_nonneg_3d
          have h_outer : (3 * (d : ℝ) * (36.4 * Real.sqrt 2)) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1)))
              ≤ (3 * (d : ℝ) * 54) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) :=
            mul_le_mul_of_nonneg_right h_inner h_nonneg_sqrt_log
          simpa [mul_assoc] using h_outer
        _ = 3 * (54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1)))) := by ring
    -- Claim 4: 36.4 * (d : ℝ) * pgLam (pgRhoStage d (i + 1)) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))
    have h4_succ : 36.4 * (d : ℝ) * pgLam (pgRhoStage d (i + 1)) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      have h_gr := hGr (d : ℝ) hd_real
      rcases h_gr with ⟨_, h_gr2⟩
      have h_nonneg_sqrt_log_rho : 0 ≤ Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := Real.sqrt_nonneg _
      calc
        36.4 * (d : ℝ) * pgLam (pgRhoStage d (i + 1))
            = 36.4 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + pgRhoStage d (i + 1))) := rfl
        _ = 36.4 * (d : ℝ) * (Real.sqrt 2 * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1)))) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
        _ = (d : ℝ) * (36.4 * Real.sqrt 2) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := by ring
        _ ≤ (d : ℝ) * 54 * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := by
          have h_inner : (d : ℝ) * (36.4 * Real.sqrt 2) ≤ (d : ℝ) * 54 :=
            mul_le_mul_of_nonneg_left h_sqrt2 h_nonneg_d
          have h_outer : ((d : ℝ) * (36.4 * Real.sqrt 2)) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1)))
              ≤ ((d : ℝ) * 54) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) :=
            mul_le_mul_of_nonneg_right h_inner h_nonneg_sqrt_log_rho
          simpa [mul_assoc] using h_outer
        _ = 54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) := by ring
        _ ≤ 54 * (d : ℝ) * Real.sqrt (Real.log (1 + pgRb (d : ℝ))) := by
          have h_log : Real.log (1 + pgRhoStage d (i + 1)) ≤ Real.log (1 + pgRb (d : ℝ)) :=
            Real.log_le_log (by linarith) (by linarith)
          have h_sqrt : Real.sqrt (Real.log (1 + pgRhoStage d (i + 1))) ≤ Real.sqrt (Real.log (1 + pgRb (d : ℝ))) :=
            Real.sqrt_le_sqrt h_log
          gcongr
        _ ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
          simpa [mul_assoc] using h_gr2
    exact ⟨h1_succ, h2_succ, h3_succ, h4_succ⟩

theorem pgStageGood_meas (hM : PgMeas) (hGM : PgGoodMeas) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (r0 δ' : ℝ) (hr0 : 0 < r0) (j : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 j (pgStage d K r0 δ' ω j)} := by
  match j with
  | 0 =>
    have hset : {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 0 (pgStage d K r0 δ' ω 0)} = Set.univ := by
      ext ω; simp [PgStageGood]
    rw [hset]
    exact MeasurableSet.univ
  | j+1 =>
    have hj : 1 ≤ j+1 := Nat.succ_pos j
    have hK'_closed : IsClosed (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) :=
      hKcl.inter Metric.isClosed_closedBall
    have hK'_convex : Convex ℝ (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) :=
      hKc.inter (convex_closedBall 0 (2 ^ (j+1) * r0))
    have hM_res := hM d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') hKcl
    have hGM_res := hGM d (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) (36.4 * d * pgLam (pgRhoStage d j)) (hK'_convex) hK'_closed
    rcases hM_res with ⟨hM_some, hM_getD⟩
    -- Now we need to relate the set to these measurable pieces
    -- The set is {ω | PgStageGood d K r0 (j+1) (pgStage d K r0 δ' ω (j+1))}
    -- = {ω | PgGood d (K ∩ closedBall 0 (2^(j+1)*r0)) (36.4*d*pgLam (pgRhoStage d j)) (pgStage d K r0 δ' ω (j+1))}
    -- = {ω | PgGood d (K ∩ closedBall 0 (2^(j+1)*r0)) (36.4*d*pgLam (pgRhoStage d j)) (pg d K r0 (2^(j+1)*r0) ((j+1)*δ') ω)}
    -- by pgStage_eq_pg and pgGood_iff
    have h_set_eq : {ω : ℕ → ℕ → PgRound d | PgStageGood d K r0 (j+1) (pgStage d K r0 δ' ω (j+1))} =
        {ω : ℕ → ℕ → PgRound d | (pg d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') ω).isSome} ∩
        (fun ω' => (pg d K r0 (2 ^ (j+1) * r0) ((j+1) * δ') ω').getD 0) ⁻¹'
        {Q : PgSp d | PgGood d (K ∩ Metric.closedBall 0 (2 ^ (j+1) * r0)) (36.4 * d * pgLam (pgRhoStage d j)) (some Q)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      rw [PgStageGood, pgStage_eq_pg d K r0 δ' hr0 (j+1) hj ω, pgGood_iff]
      simp only [Option.isSome, Nat.cast_succ]
    rw [h_set_eq]
    exact MeasurableSet.inter hM_some (MeasurableSet.preimage hGM_res hM_getD)

/-! ## Assemblies: Theorem 8.3 -/

theorem pgStage_input (hGr : PgGrowing) (hConc : PgConclusion) (d : ℕ) (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K) (hKcl : IsClosed K) (r0 : ℝ) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall 0 r0 ⊆ K) (δ' : ℝ) (ω : ℕ → ℕ → PgRound d) (j : ℕ) (P : PgSp d)
    (hP : pgStage d K r0 δ' ω j = some P) (hg : PgStageGood d K r0 j (some P)) :
    (pgMat P).det ≠ 0 ∧
      PgBody (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d j) := by
  cases j with
  | zero =>
    have hP0 : P = pgPack 0 (r0 • 1) := by
      simp only [pgStage, Option.some.injEq] at hP
      exact hP.symm
    subst hP0
    exact pgStage0_body d K hKc hKcl r0 hr0 hK0
  | succ i =>
    obtain ⟨P', hP', hdet, h1, hR, -⟩ := hg
    cases hP'
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := hK0 (Metric.mem_closedBall_self hr0.le)
    refine ⟨hdet, pgBody_mono _ _ _ ?_ (pgStage_body d K hKc hKcl h0 r0 _ hr0 (i + 1) P hdet h1 hR)⟩
    exact (pgRhoStage_bounds hGr hConc d hd i).2.2.1

theorem pgThm_of (hC : PgCoreThm) (hM : PgMeas) (hGM : PgGoodMeas) (hGr : PgGrowing) (hConc : PgConclusion) :
    PgThm := by
  intro d K r0 R0 δ hd hKc hKcl hr0 hR hK0 hKR hδ0 hδ1
  obtain ⟨hm1, hmR⟩ := pgStages_spec r0 R0 hr0 hR
  have hm0 : (0 : ℝ) < pgStages r0 R0 := by exact_mod_cast hm1
  have hδ'0 : 0 < δ / pgStages r0 R0 := div_pos hδ0 hm0
  have hδ'1 : δ / pgStages r0 R0 < 1 :=
    (div_le_self hδ0.le (by exact_mod_cast hm1)).trans_lt hδ1
  -- the event of stage `j`: good after `j` stages, not good after `j + 1`
  let C : ℕ → Set ((ℕ → ℕ → PgRound d) × (ℕ → PgRound d)) := fun j =>
    {q | PgStageGood d K r0 j (pgStage d K r0 (δ / pgStages r0 R0) q.1 j) ∧
      ¬ PgStageGood d K r0 (j + 1) (pgStage d K r0 (δ / pgStages r0 R0) (Function.update q.1 j q.2) (j + 1))}
  have hCm : ∀ j, MeasurableSet (C j) := fun j =>
    ((pgStageGood_meas hM hGM d K hKc hKcl r0 _ hr0 j).preimage measurable_fst).inter
      ((pgStageGood_meas hM hGM d K hKc hKcl r0 _ hr0 (j + 1)).preimage measurable_update').compl
  have hE : ∀ j, pgMeasure d {ω | (ω, ω j) ∈ C j} ≤ ENNReal.ofReal (δ / pgStages r0 R0) := by
    intro j
    refine slice_resample (pgCoreMeasure d) j (C j) (hCm j) ?_ _ ?_
    · intro ω x x'
      have hdep : pgStage d K r0 (δ / pgStages r0 R0) (Function.update ω j x') j =
          pgStage d K r0 (δ / pgStages r0 R0) ω j :=
        pgStage_dep d K r0 _ j _ _ fun k hk => Function.update_of_ne (ne_of_lt hk) _ _
      simp only [C, Set.mem_ofPred_eq, Function.update_idem, hdep]
    · intro ω
      by_cases hg : PgStageGood d K r0 j (pgStage d K r0 (δ / pgStages r0 R0) ω j)
      · obtain ⟨P, hP⟩ : ∃ P, pgStage d K r0 (δ / pgStages r0 R0) ω j = some P := by
          cases j with
          | zero => exact ⟨_, rfl⟩
          | succ i =>
            obtain ⟨P, hP, -⟩ := hg
            exact ⟨P, hP⟩
        rw [hP] at hg
        obtain ⟨hdet, hbody⟩ := pgStage_input hGr hConc d hd K hKc hKcl r0 hr0 hK0 _ ω j P hP hg
        refine le_trans (measure_mono ?_) (hC d _ (pgRhoStage d j) _ hd hbody.1 hbody.2.1 hbody.2.2.1 hbody.2.2.2
          (pgRhoStage_bounds hGr hConc d hd j).1 hδ'0 hδ'1)
        intro x hx hgood
        apply hx.2
        have hsj : pgStage d K r0 (δ / pgStages r0 R0) (Function.update ω j x) j = some P := by
          rw [pgStage_dep d K r0 _ j _ ω fun k hk => Function.update_of_ne (ne_of_lt hk) _ _]
          exact hP
        obtain ⟨P', hP', hgood'⟩ : ∃ P', pgCore d (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P)
            (pgOp P)) (pgRhoStage d j) (δ / pgStages r0 R0) x = some P' ∧
            PgGood d (posBody (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P))
              (36.4 * d * pgLam (pgRhoStage d j)) (some P') := by
          obtain ⟨P', hP', h'⟩ := hgood
          exact ⟨P', hP', P', rfl, h'⟩
        show PgGood d (K ∩ Metric.closedBall 0 (2 ^ (j + 1) * r0)) (36.4 * d * pgLam (pgRhoStage d j))
          (pgStage d K r0 (δ / pgStages r0 R0) (Function.update ω j x) (j + 1))
        simp only [pgStage, hsj, Option.bind_some, Function.update_self, hP', Option.map_some]
        exact pgGood_comp d _ _ P P' hdet hgood'
      · have hempty : {x | (ω, x) ∈ C j} = ∅ := by
          ext x
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [hempty, measure_empty]
        exact bot_le
  have hfinal : ∀ ω, PgStageGood d K r0 (pgStages r0 R0) (pgStage d K r0 (δ / pgStages r0 R0) ω (pgStages r0 R0)) →
      PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pg d K r0 R0 δ ω) := by
    intro ω hω
    obtain ⟨k, hk⟩ : ∃ k, pgStages r0 R0 = k + 1 := ⟨pgStages r0 R0 - 1, by omega⟩
    rw [hk] at hω
    have hKm : K ∩ Metric.closedBall 0 (2 ^ (k + 1) * r0) = K := by
      refine Set.inter_eq_left.2 (hKR.trans (Metric.closedBall_subset_closedBall ?_))
      rw [← hk]
      exact hmR
    simp only [PgStageGood, hKm] at hω
    have hpg : pg d K r0 R0 δ ω = pgStage d K r0 (δ / ((k + 1 : ℕ) : ℝ)) ω (k + 1) := by
      unfold pg
      rw [hk]
    rw [hpg]
    exact pgGood_mono d K _ _ (pgRhoStage_bounds hGr hConc d hd k).2.2.2 _ hω
  have hcover : {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pg d K r0 R0 δ ω)} ⊆
      ⋃ j ∈ Finset.range (pgStages r0 R0), {ω | (ω, ω j) ∈ C j} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hnot
    have hall : ∀ i ≤ pgStages r0 R0, PgStageGood d K r0 i (pgStage d K r0 (δ / pgStages r0 R0) ω i) := by
      intro i hi
      induction i with
      | zero => trivial
      | succ i ih =>
        by_contra hb
        refine hnot i (by omega) ?_
        refine ⟨ih (by omega), ?_⟩
        simpa only [Function.update_eq_self] using hb
    exact hω (hfinal ω (hall _ le_rfl))
  calc pgMeasure d {ω | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2))) (pg d K r0 R0 δ ω)}
      ≤ pgMeasure d (⋃ j ∈ Finset.range (pgStages r0 R0), {ω | (ω, ω j) ∈ C j}) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range (pgStages r0 R0), pgMeasure d {ω | (ω, ω j) ∈ C j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (pgStages r0 R0), ENNReal.ofReal (δ / pgStages r0 R0) :=
        Finset.sum_le_sum fun j _ => hE j
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- Theorem 8.3 from Theorem F.3, with the measurability statements of `PgMeasProof.lean` and the arithmetic of `PgArith.lean`. -/
theorem pgThm_of_core (hC : PgCoreThm) : PgThm :=
  pgThm_of hC PgMeas.pgMeas PgMeas.pgGoodMeas pgGrowing pgConclusion

/-- Theorems PG-core and PG from the five statements of `PgProb.lean`. -/
theorem pgCoreThm_pgThm_of (hCheb : ChebAvg) (hSgd : SgdExpect) (hMH : MajorityHoeffding) (hSome : RoundsSomeHit)
    (hAll : RoundsAllMiss) : PgCoreThm ∧ PgThm :=
  ⟨pgCoreThm_of (pgCoreHyps_of hCheb hSgd hMH hSome hAll),
    pgThm_of_core (pgCoreThm_of (pgCoreHyps_of hCheb hSgd hMH hSome hAll))⟩

/-- Theorem F.3. -/
theorem pgCoreThm : PgCoreThm :=
  (pgCoreThm_pgThm_of chebAvg sgdExpect majorityHoeffding roundsSomeHit roundsAllMiss).1

/-- Theorem 8.3. -/
theorem pgThm : PgThm :=
  (pgCoreThm_pgThm_of chebAvg sgdExpect majorityHoeffding roundsSomeHit roundsAllMiss).2

end AdversarialBco.Poly
