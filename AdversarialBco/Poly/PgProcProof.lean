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

@[expose] public section

/-!
Lemmas on Procedure PG of `PgProc.lean`: the hypothesis `PgBody` on the body, the objective `pgH` and the sound and
complete conditions of the test; the domain; the objective and the existence of its minimiser (`pgMin_exists`, from the
interface statements it takes as hypotheses); resampling one coordinate of an i.i.d. stream (`slice_resample`); the
monotonicity of the good positions and the composition of positions (`pgGood_comp`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

namespace AdversarialBco.Poly

/-! ## Auxiliary definitions -/

/-- The hypotheses of the theorem PG-core on the body: closed, convex, `B̄(0, 1) ⊆ K ⊆ B̄(0, ρ)`. -/
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

/-- The sound condition of the test: `k ≤ 1.1 κ`, `|b| ≤ τ_b`, `Q ≥ (κ/(2d)) I`. -/
def PgSound {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) : Prop :=
  pgKs K x ≤ 1.1 * pgKappa ∧ ‖pgBs K x‖ ≤ pgTaub d ρ ∧
    ∀ v, pgKappa / (2 * d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v

/-- The complete condition of the test: `k ≤ 1.05 κ`, `|b| ≤ τ_b/2`, `Q ≥ (3/4)(κ/d) I`. -/
def PgComplete {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) : Prop :=
  pgKs K x ≤ 1.05 * pgKappa ∧ ‖pgBs K x‖ ≤ pgTaub d ρ / 2 ∧
    ∀ v, 3 / 4 * (pgKappa / d) * ‖v‖ ^ 2 ≤ posQ K (pgMu x) (pgOp x) v v

/-! ## The domain -/

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

/-! ## The objective and its minimiser -/

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


/-! ## Generic measure theory -/

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

/-! ## Good positions and their composition -/

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

end AdversarialBco.Poly
