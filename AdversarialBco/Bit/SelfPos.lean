/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Poly.PgProcProof

@[expose] public section

/-!
# Lemmas of the position theorem, the triangular chart and the subgradient descent

* The lemma that the box holds a minimiser: (a) `sp_chol_exists` (the Cholesky factor of a positive definite matrix),
  `sp_gram_posDef`,
  `sp_chol_orth` (`L = T Q` with `Q Qᵀ = 1` when `L Lᵀ = T Tᵀ`), `sp_tri_inv`, `sp_chol_diag_ge` (`L_ii ≥ λ`),
  `sp_chol_entry_le` (`|L_ij| ≤ M`), `sp_tri_min_a`; (b) `sp_map_congr`, `sp_posObj_congr` (the objective depends on
  `A` through `A Aᵀ` only); `sp_tri_min`, the lemma in the package's terms (`pgMin_exists`, `pgPack`).
* The box of the core: `sp_box_par` (the box conditions from the parameter lemma (a)).
* The subgradient lemma: `sp_tril_frob`, `sp_neglog_subgrad`, `sp_V_norm`.
* The descent lemma, the scalar part: `sp_step_rule`.

Each lemma sits in a
namespace `AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/

namespace AdversarialBco.Bit.Aux_sp_tri_inv


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_tri_inv {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hlow : ∀ i j, i < j → L i j = 0)
    (hdiag : ∀ i, L i i ≠ 0) : (∀ i j, i < j → L⁻¹ i j = 0) ∧ ∀ i, L⁻¹ i i * L i i = 1 := by
  have h_lower : L.IsLowerTriangular := by
    unfold Matrix.IsLowerTriangular
    intro i j h
    exact hlow i j h
  have h_det_ne_zero : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L h_lower]
    apply (Finset.prod_ne_zero_iff.mpr ?_)
    intro i _
    exact hdiag i
  have h_unit : IsUnit L.det := by
    apply Ne.isUnit h_det_ne_zero
  have h_inv : Invertible L := Matrix.invertibleOfIsUnitDet L h_unit
  have h_inv_lower : L⁻¹.IsLowerTriangular := by
    have := Matrix.blockTriangular_inv_of_blockTriangular h_lower
    exact this
  have h_inv_mul : L⁻¹ * L = 1 := Matrix.inv_mul_of_invertible L
  have h_first : ∀ i j, i < j → L⁻¹ i j = 0 := by
    intro i j hij
    exact h_inv_lower hij
  have h_second : ∀ i, L⁻¹ i i * L i i = 1 := by
    intro i
    have h_mul : (L⁻¹ * L) i i = 1 := by
      rw [h_inv_mul, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h_mul
    have h_sum_eq : (∑ k : Fin d, L⁻¹ i k * L k i) = L⁻¹ i i * L i i := by
      apply Finset.sum_eq_single i
      · intro k _ hk_ne
        by_cases hik : i < k
        · have hzero : L⁻¹ i k = 0 := h_inv_lower hik
          simp [hzero]
        · by_cases hki : k < i
          · have hzero : L k i = 0 := hlow k i hki
            simp [hzero]
          · have hle1 : k ≤ i := not_lt.mp hik
            have hle2 : i ≤ k := not_lt.mp hki
            have heq : i = k := le_antisymm hle2 hle1
            exfalso; exact hk_ne heq.symm
      · intro hi_not_mem
        exfalso; exact hi_not_mem (Finset.mem_univ i)
    rw [h_sum_eq] at h_mul
    exact h_mul
  exact And.intro h_first h_second

end AdversarialBco.Bit.Aux_sp_tri_inv

namespace AdversarialBco.Bit.Aux_sp_chol_exists


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_chol_exists {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) :
    ∃ L : Matrix (Fin d) (Fin d) ℝ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = S := by
  let L0 := LDL.lower hS
  have hL0_lower : L0.IsLowerTriangular := LDL.isLowerTriangular_lower hS
  have hL0_lower_conj_diag : L0 * LDL.diag hS * L0ᴴ = S := LDL.lower_conj_diag hS
  have h_conjTranspose_eq_transpose : L0ᴴ = L0ᵀ := conjTranspose_eq_transpose_of_trivial _
  -- L0 is invertible (since L0 = (LDL.lowerInv hS)⁻¹ and LDL.lowerInv hS is invertible)
  have hL0_invertible : Invertible L0 := by
    dsimp [L0, LDL.lower]
    infer_instance
  -- Since L0 is invertible and lower triangular, all diagonal entries are nonzero
  have hL0_diag_ne_zero : ∀ i, L0 i i ≠ 0 := by
    have h_det_ne_zero : L0.det ≠ 0 := by
      have h_isUnit : IsUnit L0 := isUnit_of_invertible L0
      rcases (Matrix.isUnit_iff_isUnit_det _).mp h_isUnit with h_det_isUnit
      exact h_det_isUnit.ne_zero
    have h_det_eq_prod : L0.det = ∏ j : Fin d, L0 j j :=
      Matrix.det_of_isLowerTriangular L0 hL0_lower
    rw [h_det_eq_prod] at h_det_ne_zero
    intro i
    contrapose! h_det_ne_zero
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact h_det_ne_zero
  -- LDL.diagEntries hS i > 0 because S is positive definite
  have h_diagEntries_pos : ∀ i, 0 < LDL.diagEntries hS i := by
    intro i
    -- LDL.lowerInv hS is invertible and lower triangular, so its diagonal entries are nonzero
    have h_lowerInv_lower : (LDL.lowerInv hS).IsLowerTriangular :=
      LDL.isLowerTriangular_lowerInv hS
    have h_lowerInv_invertible : Invertible (LDL.lowerInv hS) :=
      LDL.invertibleLowerInv hS
    have h_lowerInv_diag_ne_zero : ∀ i, (LDL.lowerInv hS) i i ≠ 0 := by
      have h_det_ne_zero : (LDL.lowerInv hS).det ≠ 0 := by
        have h_isUnit : IsUnit (LDL.lowerInv hS) := isUnit_of_invertible (LDL.lowerInv hS)
        rcases (Matrix.isUnit_iff_isUnit_det _).mp h_isUnit with h_det_isUnit
        exact h_det_isUnit.ne_zero
      have h_det_eq_prod : (LDL.lowerInv hS).det = ∏ j : Fin d, (LDL.lowerInv hS) j j :=
        Matrix.det_of_isLowerTriangular (LDL.lowerInv hS) h_lowerInv_lower
      rw [h_det_eq_prod] at h_det_ne_zero
      intro i
      contrapose! h_det_ne_zero
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact h_det_ne_zero
    -- Row i of LDL.lowerInv hS is nonzero because its diagonal entry is nonzero
    have h_row_ne_zero : LDL.lowerInv hS i ≠ 0 := by
      intro hzero
      apply h_lowerInv_diag_ne_zero i
      have := congr_fun hzero i
      simpa using this
    -- Use positive definiteness of S
    have h_pos : 0 < star (LDL.lowerInv hS i) ⬝ᵥ (S *ᵥ star (LDL.lowerInv hS i)) :=
      hS.dotProduct_mulVec_pos h_row_ne_zero
    -- LDL.diagEntries hS i = ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ
    -- which for ℝ equals star (LDL.lowerInv hS i) ⬝ᵥ (S *ᵥ star (LDL.lowerInv hS i))
    have h_inner_eq : LDL.diagEntries hS i = star (LDL.lowerInv hS i) ⬝ᵥ (S *ᵥ star (LDL.lowerInv hS i)) := by
      simp [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [h_inner_eq]
    exact h_pos
  -- Now construct the Cholesky factor
  let s (i : Fin d) : ℝ := if 0 < L0 i i then 1 else -1
  have hs_sq : ∀ i, (s i)^2 = 1 := by
    intro i
    unfold s
    split <;> simp
  have h_diagEntries_nonneg : ∀ i, 0 ≤ LDL.diagEntries hS i :=
    fun i => le_of_lt (h_diagEntries_pos i)
  let D' : Matrix (Fin d) (Fin d) ℝ := diagonal (fun i => s i * Real.sqrt (LDL.diagEntries hS i))
  have hD'_mul_D' : D' * D' = diagonal (LDL.diagEntries hS) := by
    calc
      D' * D' = diagonal (fun i =>
        (s i * Real.sqrt (LDL.diagEntries hS i)) * (s i * Real.sqrt (LDL.diagEntries hS i))) := by
        simp [D', diagonal_mul_diagonal]
      _ = diagonal (fun i => ((s i)^2) * ((Real.sqrt (LDL.diagEntries hS i))^2)) := by
        ext i j
        by_cases hij : i = j
        · simp [hij]
          ring
        · simp [hij]
      _ = diagonal (fun i => 1 * (LDL.diagEntries hS i)) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hs_sq i, Real.sq_sqrt (h_diagEntries_nonneg i)]
        · simp [hij]
      _ = diagonal (LDL.diagEntries hS) := by simp
  have hD'_transpose_eq : D'ᵀ = D' := by
    simp [D', diagonal_transpose]
  let L := L0 * D'
  have hL_lower : ∀ i j, i < j → L i j = 0 := by
    intro i j hij
    unfold L
    rw [Matrix.mul_diagonal]
    have hL0_ij : L0 i j = 0 := hL0_lower (OrderDual.toDual_lt_toDual.mpr hij)
    simp [hL0_ij]
  have hL_diag_pos : ∀ i, 0 < L i i := by
    intro i
    unfold L
    rw [Matrix.mul_diagonal]
    have hsqrt_pos : 0 < Real.sqrt (LDL.diagEntries hS i) :=
      Real.sqrt_pos.mpr (h_diagEntries_pos i)
    by_cases hpos : 0 < L0 i i
    · have hs_eq : s i = 1 := by
        unfold s; rw [if_pos hpos]
      rw [hs_eq, one_mul]
      exact mul_pos hpos hsqrt_pos
    · have hs_eq : s i = -1 := by
        unfold s; rw [if_neg hpos]
      rw [hs_eq]
      have hneg : L0 i i < 0 := by
        by_contra! h
        have hzero : L0 i i = 0 := le_antisymm (by linarith) h
        exact hL0_diag_ne_zero i hzero
      have : L0 i i * (-1 * Real.sqrt (LDL.diagEntries hS i)) = (-L0 i i) * Real.sqrt (LDL.diagEntries hS i) := by ring
      rw [this]
      have hpos' : 0 < -L0 i i := by linarith
      exact mul_pos hpos' hsqrt_pos
  have hL_mul_L_transpose : L * Lᵀ = S := by
    calc
      L * Lᵀ = (L0 * D') * (L0 * D')ᵀ := rfl
      _ = (L0 * D') * (D'ᵀ * L0ᵀ) := by simp [Matrix.transpose_mul]
      _ = (L0 * D') * (D' * L0ᵀ) := by simp [hD'_transpose_eq]
      _ = L0 * (D' * D') * L0ᵀ := by
        simp [Matrix.mul_assoc]
      _ = L0 * diagonal (LDL.diagEntries hS) * L0ᵀ := by rw [hD'_mul_D']
      _ = L0 * LDL.diag hS * L0ᵀ := rfl
      _ = L0 * LDL.diag hS * L0ᴴ := by rw [h_conjTranspose_eq_transpose]
      _ = S := hL0_lower_conj_diag
  exact ⟨L, hL_lower, hL_diag_pos, hL_mul_L_transpose⟩

end AdversarialBco.Bit.Aux_sp_chol_exists

namespace AdversarialBco.Bit.Aux_sp_gram_posDef


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_gram_posDef {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) :
    (T * Tᵀ).PosDef := by
  have hT_unit : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  have hinj : Function.Injective fun v => Matrix.vecMul v T :=
    (Matrix.vecMul_injective_iff_isUnit.mpr hT_unit)
  have hpos : (T * T.conjTranspose).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self T hinj
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hpos

end AdversarialBco.Bit.Aux_sp_gram_posDef

namespace AdversarialBco.Bit.Aux_sp_chol_orth


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_chol_orth {d : ℕ} (L T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (h : L * Lᵀ = T * Tᵀ) : (T⁻¹ * L) * (T⁻¹ * L)ᵀ = 1 ∧ L = T * (T⁻¹ * L) := by
  have hT_transpose : IsUnit Tᵀ.det := Matrix.isUnit_det_transpose T hT
  have h1 : (T⁻¹ * L) * (T⁻¹ * L)ᵀ = 1 := by
    calc
      (T⁻¹ * L) * (T⁻¹ * L)ᵀ
          = (T⁻¹ * L) * (Lᵀ * (T⁻¹)ᵀ) := by rw [Matrix.transpose_mul]
      _ = (T⁻¹ * L) * (Lᵀ * T⁻¹ᵀ) := by rfl
      _ = (T⁻¹ * L) * (Lᵀ * (Tᵀ)⁻¹) := by rw [Matrix.transpose_nonsing_inv T]
      _ = T⁻¹ * (L * Lᵀ) * (Tᵀ)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = T⁻¹ * (T * Tᵀ) * (Tᵀ)⁻¹ := by rw [h]
      _ = (T⁻¹ * T) * (Tᵀ * (Tᵀ)⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = 1 * (Tᵀ * (Tᵀ)⁻¹) := by rw [Matrix.nonsing_inv_mul T hT]
      _ = 1 * 1 := by rw [Matrix.mul_nonsing_inv Tᵀ hT_transpose]
      _ = 1 := by simp
  have h2 : L = T * (T⁻¹ * L) := by
    calc
      L = 1 * L := by simp
      _ = (T * T⁻¹) * L := by rw [Matrix.mul_nonsing_inv T hT]
      _ = T * (T⁻¹ * L) := by rw [Matrix.mul_assoc]
  exact And.intro h1 h2

end AdversarialBco.Bit.Aux_sp_chol_orth

namespace AdversarialBco.Bit.Aux_sp_chol_diag_ge


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_chol_diag_ge {d : ℕ} (L T Q : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlow : ∀ i j, i < j → L i j = 0) (hpos : ∀ i, 0 < L i i) (hQ : Q * Qᵀ = 1) (hLTQ : L = T * Q)
    (hT : ∀ v : Fin d → ℝ, lam ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (v ᵥ* T) k ^ 2) (i : Fin d) : lam ≤ L i i := by
  have hL_lower : L.IsLowerTriangular := by
    intro i j h
    apply hlow i j
    simpa using h
  have hdet_ne_zero : L.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular L hL_lower]
    refine (Finset.prod_ne_zero_iff.mpr ?_)
    intro i _
    exact ne_of_gt (hpos i)
  have hdet_unit : IsUnit (L.det) := by
    rwa [isUnit_iff_ne_zero]
  have hQ' : Qᵀ * Q = 1 := ((mul_eq_one_comm (a := Q) (b := Qᵀ)).mp hQ)
  have hT' : T = L * Qᵀ := by
    calc
      T = T * 1 := by simp
      _ = T * (Q * Qᵀ) := by rw [hQ]
      _ = (T * Q) * Qᵀ := by rw [Matrix.mul_assoc]
      _ = L * Qᵀ := by rw [← hLTQ]
  set v : Fin d → ℝ := λ k => L i i * L⁻¹ i k with hv_def
  have hvL : v ᵥ* L = L i i • (λ k => (1 : Matrix (Fin d) (Fin d) ℝ) i k) := by
    ext j
    dsimp [v]
    simp [Matrix.vecMul, dotProduct]
    have h := Matrix.nonsing_inv_mul L hdet_unit
    have h' := congr_fun (congr_fun h i) j
    simp [Matrix.mul_apply] at h'
    calc
      (∑ x : Fin d, (L i i * L⁻¹ i x) * L x j) = (∑ x : Fin d, L i i * (L⁻¹ i x * L x j)) := by
        refine Finset.sum_congr rfl (λ x hx => ?_)
        ring
      _ = L i i * (∑ x : Fin d, L⁻¹ i x * L x j) := by rw [Finset.mul_sum]
      _ = L i i * (1 : Matrix (Fin d) (Fin d) ℝ) i j := by rw [h']
  have h_vT_sq_sum : ∑ k : Fin d, (v ᵥ* T) k ^ 2 = (L i i)^2 := by
    rw [hT']
    have h_vT_component : ∀ k : Fin d, (v ᵥ* (L * Qᵀ)) k = L i i * Q k i := by
      intro k
      rw [← Matrix.vecMul_vecMul v L Qᵀ]
      rw [hvL]
      simp [Matrix.vecMul, dotProduct, Matrix.transpose_apply, Matrix.one_apply]
    rw [Finset.sum_congr rfl (λ k hk => by rw [h_vT_component k])]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    have h_sum_sq : (∑ k : Fin d, (Q k i)^2) = 1 := by
      calc
        (∑ k : Fin d, (Q k i)^2) = (Qᵀ * Q) i i := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
        _ = (1 : Matrix (Fin d) (Fin d) ℝ) i i := by rw [hQ']
        _ = 1 := by simp
    rw [h_sum_sq]
    ring
  have hv_i_eq_one : v i = 1 := by
    dsimp [v]
    have h_inv := (sp_tri_inv L hlow (λ i => (hpos i).ne.symm)).2 i
    -- h_inv : L⁻¹ i i * L i i = 1
    -- So v i = L i i * L⁻¹ i i = 1
    calc
      L i i * L⁻¹ i i = L i i * L⁻¹ i i := rfl
      _ = 1 := by
        -- From h_inv: L⁻¹ i i * L i i = 1
        -- Since ℝ is commutative, L i i * L⁻¹ i i = L⁻¹ i i * L i i = 1
        rw [mul_comm, h_inv]
  have h_sum_v_sq_ge_one : 1 ≤ ∑ k : Fin d, v k ^ 2 := by
    have hvi_sq : v i ^ 2 = 1 := by
      rw [hv_i_eq_one]
      norm_num
    have h_nonneg : ∀ k ∈ (Finset.univ : Finset (Fin d)), 0 ≤ v k ^ 2 := by
      intro k hk
      apply pow_two_nonneg
    calc
      1 = v i ^ 2 := by rw [hvi_sq]
      _ ≤ ∑ k : Fin d, v k ^ 2 := Finset.single_le_sum h_nonneg (Finset.mem_univ i)
  have h_ineq := hT v
  rw [h_vT_sq_sum] at h_ineq
  -- h_ineq : lam ^ 2 * ∑ k, v k ^ 2 ≤ (L i i)^2
  have h_lam_sq_le : lam ^ 2 ≤ (L i i)^2 := by
    -- From h_ineq: lam^2 * ∑ v k^2 ≤ (L i i)^2
    -- And ∑ v k^2 ≥ 1, so lam^2 * 1 ≤ lam^2 * ∑ v k^2 ≤ (L i i)^2
    -- But we need to be careful: lam^2 ≥ 0, so multiplying by lam^2 preserves inequality
    have h_lam_sq_nonneg : 0 ≤ lam ^ 2 := by
      apply pow_two_nonneg
    have h_mul : lam ^ 2 * 1 ≤ lam ^ 2 * ∑ k : Fin d, v k ^ 2 := by
      nlinarith
    nlinarith
  -- Now lam^2 ≤ (L i i)^2, lam ≥ 0, L i i > 0, so lam ≤ L i i
  have h_abs := (sq_le_sq.mp h_lam_sq_le)
  have h_abs_lam : |lam| = lam := abs_of_nonneg hlam
  have h_abs_Li : |L i i| = L i i := abs_of_pos (hpos i)
  rw [h_abs_lam, h_abs_Li] at h_abs
  exact h_abs

end AdversarialBco.Bit.Aux_sp_chol_diag_ge

namespace AdversarialBco.Bit.Aux_sp_chol_entry_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_chol_entry_le {d : ℕ} (L T Q : Matrix (Fin d) (Fin d) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hQ : Q * Qᵀ = 1) (hLTQ : L = T * Q)
    (hT : ∀ v : Fin d → ℝ, ∑ k, (v ᵥ* T) k ^ 2 ≤ M ^ 2 * ∑ k, v k ^ 2) (i j : Fin d) : |L i j| ≤ M := by
  have h_sum_sq_eq : ∑ j : Fin d, L i j ^ 2 = ∑ j : Fin d, T i j ^ 2 := by
    have h_mul_eq : T * (Q * Qᵀ) * Tᵀ = T * Tᵀ := by
      rw [hQ, Matrix.mul_one]
    calc
      ∑ j : Fin d, L i j ^ 2 = (L * Lᵀ) i i := by
        simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
      _ = ((T * Q) * (T * Q)ᵀ) i i := by rw [hLTQ]
      _ = ((T * Q) * (Qᵀ * Tᵀ)) i i := by rw [Matrix.transpose_mul]
      _ = (T * (Q * Qᵀ) * Tᵀ) i i := by
        simp [Matrix.mul_assoc]
      _ = (T * Tᵀ) i i := by rw [h_mul_eq]
      _ = ∑ j : Fin d, T i j ^ 2 := by
        simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
  have hT_bound : ∑ j : Fin d, T i j ^ 2 ≤ M ^ 2 := by
    have h := hT (Pi.single i (1 : ℝ))
    have h_left : ∑ k : Fin d, ((Pi.single i (1 : ℝ)) ᵥ* T) k ^ 2 = ∑ j : Fin d, T i j ^ 2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [Matrix.vecMul_apply, Matrix.col_apply, dotProduct, Pi.single_apply]
    have h_right : ∑ k : Fin d, ((Pi.single i (1 : ℝ)) k) ^ 2 = (1 : ℝ) := by
      simp [Pi.single_apply]
    calc
      ∑ j : Fin d, T i j ^ 2 = ∑ k : Fin d, ((Pi.single i (1 : ℝ)) ᵥ* T) k ^ 2 := by rw [h_left]
      _ ≤ M ^ 2 * (∑ k : Fin d, ((Pi.single i (1 : ℝ)) k) ^ 2) := h
      _ = M ^ 2 := by rw [h_right, mul_one]
  have hL_sq_le : L i j ^ 2 ≤ M ^ 2 := by
    have h_nonneg_sq : ∀ k, 0 ≤ L i k ^ 2 := by
      intro k; apply sq_nonneg
    have h_single_le_sum : L i j ^ 2 ≤ ∑ j : Fin d, L i j ^ 2 :=
      Finset.single_le_sum (by intro k _; exact h_nonneg_sq k) (Finset.mem_univ j)
    calc
      L i j ^ 2 ≤ ∑ j : Fin d, L i j ^ 2 := h_single_le_sum
      _ = ∑ j : Fin d, T i j ^ 2 := h_sum_sq_eq
      _ ≤ M ^ 2 := hT_bound
  exact abs_le_of_sq_le_sq hL_sq_le hM

end AdversarialBco.Bit.Aux_sp_chol_entry_le

namespace AdversarialBco.Bit.Aux_sp_tri_min_a


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_tri_min_a {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (lam M : ℝ) (hlam : 0 ≤ lam)
    (hM : 0 ≤ M) (hdet : IsUnit T.det)
    (hlo : ∀ v : Fin d → ℝ, lam ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (v ᵥ* T) k ^ 2)
    (hhi : ∀ v : Fin d → ℝ, ∑ k, (v ᵥ* T) k ^ 2 ≤ M ^ 2 * ∑ k, v k ^ 2) :
    ∃ L : Matrix (Fin d) (Fin d) ℝ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = T * Tᵀ ∧
      (∀ i, lam ≤ L i i) ∧ ∀ i j, |L i j| ≤ M := by
  have hposdef : (T * Tᵀ).PosDef := sp_gram_posDef T hdet
  rcases sp_chol_exists (T * Tᵀ) hposdef with ⟨L, hL_lower, hL_pos, hL_eq⟩
  rcases sp_chol_orth L T hdet hL_eq with ⟨hQ_orth, hL_eq_TQ⟩
  refine ⟨L, hL_lower, hL_pos, hL_eq, ?_, ?_⟩
  · intro i
    exact sp_chol_diag_ge L T (T⁻¹ * L) lam hlam hL_lower hL_pos hQ_orth hL_eq_TQ hlo i
  · intro i j
    exact sp_chol_entry_le L T (T⁻¹ * L) M hM hQ_orth hL_eq_TQ hhi i j

end AdversarialBco.Bit.Aux_sp_tri_min_a

namespace AdversarialBco.Bit.Aux_sp_tri_min


open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Pointwise Matrix

open AdversarialBco.Poly

/-- The Gaussian image under the operator of a matrix depends only on `M Mᵀ`. -/
theorem _root_.AdversarialBco.Bit.sp_map_congr {d : ℕ} (L T : Matrix (Fin d) (Fin d) ℝ) (h : L * Lᵀ = T * Tᵀ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (Matrix.toEuclideanCLM (𝕜 := ℝ) L) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map (Matrix.toEuclideanCLM (𝕜 := ℝ) T) := by
  apply AdversarialBco.Poly.stdGaussian_map_eq
  have key : ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M).comp
          (ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) M)) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (M * Mᵀ) := by
    intro M
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, map_mul]
    rfl
  rw [key L, key T, h]

theorem _root_.AdversarialBco.Bit.sp_det_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (𝕜 := ℝ) M : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      M.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The lemma that the box holds a minimiser (b): the objective at `(μ, L)` and at `(μ, T)` agree when `L Lᵀ = T Tᵀ`. -/
theorem _root_.AdversarialBco.Bit.sp_posObj_congr {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : K ∈ nhds 0)
    (hKc : Convex ℝ K) (κ : ℝ) (μ : EuclideanSpace ℝ (Fin d)) (L T : Matrix (Fin d) (Fin d) ℝ)
    (h : L * Lᵀ = T * Tᵀ) :
    posObj K κ μ (Matrix.toEuclideanCLM (𝕜 := ℝ) L) = posObj K κ μ (Matrix.toEuclideanCLM (𝕜 := ℝ) T) := by
  unfold posObj
  rw [posK_congr_map K μ _ _ hK hKc (AdversarialBco.Bit.sp_map_congr L T h).symm,
    AdversarialBco.Bit.sp_det_toEuclideanCLM, AdversarialBco.Bit.sp_det_toEuclideanCLM]
  have h2 : L.det ^ 2 = T.det ^ 2 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose] at this
    nlinarith [this]
  have habs : |L.det| = |T.det| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, h2]
  rw [habs]

/-- The squared Euclidean norm of a coordinate vector. -/
theorem _root_.AdversarialBco.Bit.sp_norm_sq_toLp {d : ℕ} (v : Fin d → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ∑ k, v k ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  simp

/-- The lemma that the box holds a minimiser: the triangular box `|μ_i| ≤ r`, `a ≤ L_ii ≤ b`, `|L_ij| ≤ b` (`j < i`),
with `r ≥ κ ρ0`,
`a ≤ t_min(ρ0)` and `b ≥ t_max(ρ0)`, holds a position whose objective is at most the objective at every invertible
position. -/
theorem _root_.AdversarialBco.Bit.sp_tri_min (d : ℕ) (ρ0 : ℝ) (hd : 1 ≤ d) (hρ0 : 1 ≤ ρ0)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ0) (r a b : ℝ) (hr : pgKappa * ρ0 ≤ r)
    (ha : a ≤ pgTmin d ρ0) (hb : pgLD ρ0 ≤ b) :
    ∃ x : PgSp d, (∀ i, |pgMu x i| ≤ r) ∧ (∀ i j, i < j → pgMat x i j = 0) ∧
      (∀ i, a ≤ pgMat x i i ∧ pgMat x i i ≤ b) ∧ (∀ i j, j < i → |pgMat x i j| ≤ b) ∧ (pgMat x).det ≠ 0 ∧
      ∀ (μ' : EuclideanSpace ℝ (Fin d)) (A' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (A' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        pgH K x ≤ posObj K pgKappa μ' A' := by
  obtain ⟨xs, hxs, hmin⟩ := pgMin_exists lemmaLSym d1Bounds d1Inv lemmaLRadii gaussConst d ρ0 hd hρ0 K hK
  have hdom : IsPgDom (pgTmin d ρ0) (pgLD ρ0) (pgKappa * ρ0) (pgMu xs) (pgOp xs) := hxs
  obtain ⟨hsa, hμ, hform⟩ := hdom
  have hdet : (pgMat xs).det ≠ 0 := (pgDom_inv d ρ0 hd hρ0 xs hxs).1
  set T := pgMat xs with hT
  have hτ0 : 0 ≤ pgTmin d ρ0 := by
    unfold pgTmin pgLam; positivity
  have hτ1 : 0 ≤ pgLD ρ0 := by
    unfold pgLD pgKappa pgPB; positivity
  -- `T` is symmetric
  have hsym : Tᵀ = T := by
    have h1 : star (pgOp xs) = pgOp xs := hsa
    have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) (star T) = Matrix.toEuclideanCLM (𝕜 := ℝ) T := by
      rw [map_star]; exact h1
    have h3 := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).injective h2
    simpa [Matrix.star_eq_conjTranspose] using h3
  have hvec : ∀ v : Fin d → ℝ, v ᵥ* T = T *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_transpose, hsym]
  have hop : ∀ v : Fin d → ℝ, pgOp xs (WithLp.toLp 2 v) = WithLp.toLp 2 (T *ᵥ v) := by
    intro v; rw [pgOp_apply]
  have hlo : ∀ v : Fin d → ℝ, pgTmin d ρ0 ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (v ᵥ* T) k ^ 2 := by
    intro v
    set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
    have h1 := (hform w).1
    have h2 : ⟪pgOp xs w, w⟫ ≤ ‖pgOp xs w‖ * ‖w‖ := real_inner_le_norm _ _
    have h3 : pgTmin d ρ0 * ‖w‖ ≤ ‖pgOp xs w‖ := by
      rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
      · rw [← h0, mul_zero]; exact norm_nonneg _
      · have : pgTmin d ρ0 * ‖w‖ * ‖w‖ ≤ ‖pgOp xs w‖ * ‖w‖ := by nlinarith
        exact le_of_mul_le_mul_right this h0
    have h4 : (pgTmin d ρ0 * ‖w‖) ^ 2 ≤ ‖pgOp xs w‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hτ0 (norm_nonneg _)) h3 2
    rw [hvec, ← AdversarialBco.Bit.sp_norm_sq_toLp, ← AdversarialBco.Bit.sp_norm_sq_toLp, ← hop]
    nlinarith [h4]
  have hhi : ∀ v : Fin d → ℝ, ∑ k, (v ᵥ* T) k ^ 2 ≤ pgLD ρ0 ^ 2 * ∑ k, v k ^ 2 := by
    intro v
    set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
    have h1 := AdversarialBco.Poly.opnorm_le_of_form (pgOp xs) (pgLD ρ0) hsa
      (fun u => le_trans (mul_nonneg hτ0 (sq_nonneg _)) (hform u).1) (fun u => (hform u).2) w
    have h2 : ‖pgOp xs w‖ ^ 2 ≤ (pgLD ρ0 * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hvec, ← AdversarialBco.Bit.sp_norm_sq_toLp, ← AdversarialBco.Bit.sp_norm_sq_toLp, ← hop]
    nlinarith [h2]
  obtain ⟨L, hlow, hpos, hLL, hdiag, hent⟩ :=
    AdversarialBco.Bit.sp_tri_min_a T (pgTmin d ρ0) (pgLD ρ0) hτ0 hτ1 (isUnit_iff_ne_zero.2 hdet) hlo hhi
  have hK0 : K ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hK.2.2.1
  have hH : pgH K (pgPack (pgMu xs) L) = pgH K xs := by
    unfold pgH
    rw [pgMu_pgPack]
    exact AdversarialBco.Bit.sp_posObj_congr K hK0 hK.1 pgKappa (pgMu xs) L T hLL
  refine ⟨pgPack (pgMu xs) L, fun i => ?_, ?_, fun i => ⟨?_, ?_⟩, fun i j hij => ?_, ?_, ?_⟩
  · rw [pgMu_pgPack]
    calc |pgMu xs i| ≤ ‖pgMu xs‖ := by
          have := PiLp.norm_apply_le (p := 2) (pgMu xs) i
          simpa [Real.norm_eq_abs] using this
      _ ≤ pgKappa * ρ0 := hμ
      _ ≤ r := hr
  · rw [pgMat_pgPack]; exact hlow
  · rw [pgMat_pgPack]; exact ha.trans (hdiag i)
  · rw [pgMat_pgPack]; exact (le_abs_self _).trans ((hent i i).trans hb)
  · rw [pgMat_pgPack]; exact (hent i j).trans hb
  · rw [pgMat_pgPack]
    intro h0
    have := congrArg Matrix.det hLL
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, h0, zero_mul] at this
    exact hdet (by nlinarith [this])
  · intro μ' A' hA'
    rw [hH]; exact hmin μ' A' hA'

end AdversarialBco.Bit.Aux_sp_tri_min

namespace AdversarialBco.Bit.Aux_sp_box_par


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_box_par (L ja : ℕ) (d s : ℝ) (hL : 10 ≤ L) (hds : 0 < 9 * d * s)
    (hja : 9 * d * s ≤ 2 ^ ja) :
    627 * 1024 < 161 * 4000 ∧ (1 / 8 : ℝ) * (2 ^ L - 1) ≤ 2 ^ (L - 3) ∧
      (627 / 4000 : ℝ) * (2 ^ L - 1) ≤ 161 * 2 ^ (L - 10) ∧ ((2 : ℝ) ^ ja)⁻¹ ≤ 1 / (9 * d * s) ∧
      ((2 : ℝ) ^ ja)⁻¹ ≤ 1 ∧ (1 : ℝ) ≤ 161 * 2 ^ (L - 10) := by
  have hL3 : 3 ≤ L := by omega
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  have hpos_pow_ja : 0 < (2 : ℝ) ^ ja := pow_pos hpos2 ja
  have h_two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  -- (1) numeric inequality
  have h1 : 627 * 1024 < 161 * 4000 := by norm_num
  -- (2) (1/8)(2^L - 1) ≤ 2^(L-3)
  have h2 : (1 / 8 : ℝ) * ((2 : ℝ) ^ L - 1) ≤ (2 : ℝ) ^ (L - 3) := by
    have h_pow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - 3) * (2 : ℝ) ^ 3 := by
      calc
        (2 : ℝ) ^ L = (2 : ℝ) ^ ((L - 3) + 3) := by rw [Nat.sub_add_cancel hL3]
        _ = (2 : ℝ) ^ (L - 3) * (2 : ℝ) ^ 3 := by rw [pow_add]
    have h8 : (2 : ℝ) ^ 3 = (8 : ℝ) := by norm_num
    rw [h8] at h_pow
    calc
      (1 / 8 : ℝ) * ((2 : ℝ) ^ L - 1) = (1 / 8 : ℝ) * (((2 : ℝ) ^ (L - 3) * 8) - 1) := by rw [h_pow]
      _ = (1 / 8 : ℝ) * ((2 : ℝ) ^ (L - 3) * 8) - (1 / 8 : ℝ) * 1 := by ring
      _ = (2 : ℝ) ^ (L - 3) - (1 / 8 : ℝ) := by ring
      _ ≤ (2 : ℝ) ^ (L - 3) := by nlinarith
  -- (3) (627/4000)(2^L - 1) ≤ 161 * 2^(L-10)
  have h3 : (627 / 4000 : ℝ) * ((2 : ℝ) ^ L - 1) ≤ 161 * (2 : ℝ) ^ (L - 10) := by
    have h_pow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - 10) * (2 : ℝ) ^ 10 := by
      calc
        (2 : ℝ) ^ L = (2 : ℝ) ^ ((L - 10) + 10) := by rw [Nat.sub_add_cancel hL]
        _ = (2 : ℝ) ^ (L - 10) * (2 : ℝ) ^ 10 := by rw [pow_add]
    have h1024 : (2 : ℝ) ^ 10 = (1024 : ℝ) := by norm_num
    rw [h1024] at h_pow
    rw [h_pow]
    set X := (2 : ℝ) ^ (L - 10) with hX
    have hX_nonneg : 0 ≤ X := by
      rw [hX]
      exact pow_nonneg h_two_nonneg _
    have h_coeff : (627 : ℝ) * 1024 ≤ 161 * 4000 := by norm_num
    field_simp
    nlinarith
  -- (4) ((2)^ja)⁻¹ ≤ 1/(9*d*s)
  have h4 : ((2 : ℝ) ^ ja)⁻¹ ≤ 1 / (9 * d * s) := by
    rw [one_div]
    simpa [one_div] using (one_div_le_one_div hpos_pow_ja hds).mpr hja
  -- (5) ((2)^ja)⁻¹ ≤ 1
  have h5 : ((2 : ℝ) ^ ja)⁻¹ ≤ 1 := by
    have h_one_le_pow_ja : 1 ≤ (2 : ℝ) ^ ja := by
      by_cases hja0 : ja = 0
      · rw [hja0, pow_zero]
      · exact (one_le_pow_iff_of_nonneg h_two_nonneg hja0).mpr (by norm_num)
    simpa [one_div] using (one_div_le_one_div hpos_pow_ja (by norm_num : 0 < (1 : ℝ))).mpr h_one_le_pow_ja
  -- (6) 1 ≤ 161 * 2^(L-10)
  have h6 : (1 : ℝ) ≤ 161 * (2 : ℝ) ^ (L - 10) := by
    have h_one_le_pow_L10 : 1 ≤ (2 : ℝ) ^ (L - 10) := by
      by_cases hL10 : L - 10 = 0
      · rw [hL10, pow_zero]
      · exact (one_le_pow_iff_of_nonneg h_two_nonneg hL10).mpr (by norm_num)
    nlinarith
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 h6))))

end AdversarialBco.Bit.Aux_sp_box_par

namespace AdversarialBco.Bit.Aux_sp_tril_frob


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_tril_frob {d : ℕ} (u y : Fin d → ℝ) :
    ∑ i, ∑ j, (if j ≤ i then u i * y j else 0) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ j, y j ^ 2) := by
  calc
    ∑ i, ∑ j, (if j ≤ i then u i * y j else 0) ^ 2 ≤ ∑ i, ∑ j, (u i * y j) ^ 2 := by
      refine Finset.sum_le_sum (λ i hi => ?_)
      refine Finset.sum_le_sum (λ j hj => ?_)
      split_ifs with h
      · rfl
      · have h_nonneg := sq_nonneg (u i * y j)
        simpa using h_nonneg
    _ = ∑ i, ∑ j, (u i ^ 2) * (y j ^ 2) := by
      refine Finset.sum_congr rfl (λ i hi => ?_)
      refine Finset.sum_congr rfl (λ j hj => ?_)
      ring
    _ = (∑ i, u i ^ 2) * (∑ j, y j ^ 2) := by
      rw [Finset.sum_mul_sum]

end AdversarialBco.Bit.Aux_sp_tril_frob

namespace AdversarialBco.Bit.Aux_sp_neglog_subgrad


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_neglog_subgrad (x x' : ℝ) (hx : 0 < x) (hx' : 0 < x') :
    -Real.log x - (x' - x) / x ≤ -Real.log x' := by
  have hpos : 0 < x' / x := div_pos hx' hx
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div hx'.ne.symm hx.ne.symm] at hlog
  have hdiv : (x' - x) / x = x' / x - 1 := by
    field_simp [hx.ne.symm]
  rw [hdiv]
  linarith

end AdversarialBco.Bit.Aux_sp_neglog_subgrad

namespace AdversarialBco.Bit.Aux_sp_V_norm


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_V_norm {d : ℕ} (hd : 1 ≤ d) (u y : Fin d → ℝ) (L : Matrix (Fin d) (Fin d) ℝ)
    (κ m : ℝ) (hκ : 0 ≤ κ) (hm : 0 < m) (hLm : ∀ i, m ≤ L i i) (hu : ∑ i, u i ^ 2 ≤ 1) :
    ∑ i, u i ^ 2 + ∑ i, ∑ j, ((if j ≤ i then u i * y j else 0) - (if i = j then κ / d / L i i else 0)) ^ 2 ≤
      1 + (Real.sqrt (∑ j, y j ^ 2) + κ / (Real.sqrt d * m)) ^ 2 := by
  let A : Matrix (Fin d) (Fin d) ℝ := fun i j => if j ≤ i then u i * y j else 0
  let B : Matrix (Fin d) (Fin d) ℝ := fun i j => if i = j then κ / d / L i i else 0
  have hdpos : 0 < (d : ℝ) := by
    have : 1 ≤ (d : ℝ) := by exact mod_cast hd
    linarith
  have h_frob_norm_sq (M : Matrix (Fin d) (Fin d) ℝ) : ‖M‖ ^ 2 = ∑ i, ∑ j, (M i j) ^ 2 := by
    rw [Matrix.frobenius_norm_def M]
    have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
      refine Finset.sum_nonneg fun i _ => ?_
      refine Finset.sum_nonneg fun j _ => ?_
      apply pow_two_nonneg
    have h_sq : ∀ (x : ℝ), 0 ≤ x → ((x ^ (1/2 : ℝ)) ^ 2) = x := by
      intro x hx
      calc
        ((x ^ (1/2 : ℝ)) ^ 2) = ((Real.sqrt x) ^ 2) := by rw [Real.sqrt_eq_rpow]
        _ = x := Real.sq_sqrt hx
    have h := h_sq (∑ i, ∑ j, ‖M i j‖ ^ 2) h_nonneg
    simpa [Real.norm_eq_abs] using h
  have h_tri : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  have h_normA_sq_le : ‖A‖ ^ 2 ≤ ∑ j, y j ^ 2 := by
    rw [h_frob_norm_sq A]
    have h_sp := sp_tril_frob u y
    have h_sum_u_nonneg : 0 ≤ ∑ i, u i ^ 2 := by
      refine Finset.sum_nonneg fun i _ => pow_two_nonneg _
    have h_sum_y_nonneg : 0 ≤ ∑ j, y j ^ 2 := by
      refine Finset.sum_nonneg fun j _ => pow_two_nonneg _
    have h_mul : (∑ i, u i ^ 2) * (∑ j, y j ^ 2) ≤ 1 * (∑ j, y j ^ 2) := by
      nlinarith
    nlinarith
  have h_normB_sq_le : ‖B‖ ^ 2 ≤ (κ / (Real.sqrt d * m)) ^ 2 := by
    rw [h_frob_norm_sq B]
    have hLpos : ∀ i, 0 < L i i := fun i => by linarith [hm, hLm i]
    have h_each_sq : ∀ i, (κ / (d : ℝ) / L i i) ^ 2 ≤ (κ / ((d : ℝ) * m)) ^ 2 := by
      intro i
      have h_nonneg : 0 ≤ κ / (d : ℝ) / L i i := by
        have h_nonneg_div : 0 ≤ κ / (d : ℝ) := by
          have hdpos' : 0 ≤ (d : ℝ) := by linarith
          exact div_nonneg hκ hdpos'
        exact div_nonneg h_nonneg_div (by linarith [hLm i])
      have h_nonneg' : 0 ≤ κ / ((d : ℝ) * m) := by positivity
      have h_le : κ / (d : ℝ) / L i i ≤ κ / ((d : ℝ) * m) := by
        have h_denom : 0 < (d : ℝ) * m := by positivity
        have h_denom_le : (d : ℝ) * m ≤ (d : ℝ) * L i i := by
          nlinarith [hLm i]
        rw [div_div]
        exact div_le_div_of_nonneg_left hκ h_denom h_denom_le
      nlinarith
    have h_sum_eq : ∑ i, ∑ j, (B i j) ^ 2 = ∑ i, (κ / (d : ℝ) / L i i) ^ 2 := by
      calc
        ∑ i, ∑ j, (B i j) ^ 2 = ∑ i, (B i i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          apply Finset.sum_eq_single i
          · intro j hj hne
            dsimp [B]
            simp [hne.symm]
          · intro hi
            exfalso; exact hi (Finset.mem_univ i)
        _ = ∑ i, (κ / (d : ℝ) / L i i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [B]
          simp
    rw [h_sum_eq]
    calc
      ∑ i, (κ / (d : ℝ) / L i i) ^ 2 ≤ ∑ i, (κ / ((d : ℝ) * m)) ^ 2 :=
        Finset.sum_le_sum fun i _ => h_each_sq i
      _ = (Finset.card (Finset.univ : Finset (Fin d)) : ℝ) * (κ / ((d : ℝ) * m)) ^ 2 := by
        simp
      _ = (d : ℝ) * (κ / ((d : ℝ) * m)) ^ 2 := by simp
      _ = (κ / (Real.sqrt d * m)) ^ 2 := by
        have hdpos' : (d : ℝ) ≠ 0 := by linarith
        have hm_ne_zero : m ≠ 0 := by linarith
        have hsqrt_ne_zero : Real.sqrt d ≠ 0 := by linarith [Real.sqrt_pos.mpr hdpos]
        field_simp [hdpos', hm_ne_zero, hsqrt_ne_zero]
        ring_nf
        rw [Real.sq_sqrt (by linarith : 0 ≤ (d : ℝ))]
  have h_final : ∑ i, u i ^ 2 + ‖A - B‖ ^ 2 ≤ 1 + (Real.sqrt (∑ j, y j ^ 2) + κ / (Real.sqrt d * m)) ^ 2 := by
    have h_sq : ‖A - B‖ ^ 2 ≤ (Real.sqrt (∑ j, y j ^ 2) + κ / (Real.sqrt d * m)) ^ 2 := by
      have h_nonneg_ab : 0 ≤ ‖A - B‖ := norm_nonneg _
      have h_nonneg_rhs : 0 ≤ Real.sqrt (∑ j, y j ^ 2) + κ / (Real.sqrt d * m) := by
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (∑ j, y j ^ 2) := Real.sqrt_nonneg _
        have h_kappa_nonneg : 0 ≤ κ / (Real.sqrt d * m) := by
          have h_sqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
          positivity
        positivity
      have h_tri_sq : ‖A - B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by
        nlinarith
      have h_sum_sq' : (‖A‖ + ‖B‖) ^ 2 ≤ (Real.sqrt (∑ j, y j ^ 2) + κ / (Real.sqrt d * m)) ^ 2 := by
        have hA_sq : ‖A‖ ^ 2 ≤ (Real.sqrt (∑ j, y j ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => pow_two_nonneg _)]
          exact h_normA_sq_le
        have hB_sq : ‖B‖ ^ 2 ≤ (κ / (Real.sqrt d * m)) ^ 2 := h_normB_sq_le
        have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
        have hB_nonneg : 0 ≤ ‖B‖ := norm_nonneg _
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (∑ j, y j ^ 2) := Real.sqrt_nonneg _
        have h_kappa_nonneg : 0 ≤ κ / (Real.sqrt d * m) := by
          have h_sqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
          positivity
        have hA_le : ‖A‖ ≤ Real.sqrt (∑ j, y j ^ 2) := by
          nlinarith
        have hB_le : ‖B‖ ≤ κ / (Real.sqrt d * m) := by
          nlinarith
        nlinarith
      exact le_trans h_tri_sq h_sum_sq'
    nlinarith
  have h_goal_eq : (∑ i, ∑ j, ((if j ≤ i then u i * y j else 0) - (if i = j then κ / d / L i i else 0)) ^ 2) = ‖A - B‖ ^ 2 := by
    calc
      _ = ∑ i, ∑ j, ((A - B) i j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [A, B]
        rfl
      _ = ‖A - B‖ ^ 2 := by rw [h_frob_norm_sq (A - B)]
  rw [h_goal_eq]
  exact h_final

end AdversarialBco.Bit.Aux_sp_V_norm

namespace AdversarialBco.Bit.Aux_sp_step_rule


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sp_step_rule (Δ G N s : ℝ) (hΔ : 0 < Δ) (hG : 0 < G) (hN : 0 < N)
    (hs1 : Δ / (G * Real.sqrt N) / 2 < s) (hs2 : s ≤ Δ / (G * Real.sqrt N)) :
    Δ ^ 2 / (2 * s * N) + s / 2 * G ^ 2 ≤ 3 / 2 * Δ * G / Real.sqrt N := by
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsqrtN_sq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have hs_pos : 0 < s := by
    have hpos : 0 < Δ / (G * Real.sqrt N) / 2 := by positivity
    linarith
  have hpos_GsN : 0 < G * Real.sqrt N := by positivity
  -- From hs2: s ≤ Δ/(G*sqrt N). Multiply by G*sqrt N > 0
  have hineq1 : G * Real.sqrt N * s ≤ Δ := by
    have := (le_div_iff₀ hpos_GsN).mp hs2
    nlinarith
  -- From hs1: Δ/(G*sqrt N)/2 < s. Multiply by 2*G*sqrt N > 0
  have hineq2 : Δ < 2 * G * Real.sqrt N * s := by
    have htemp : Δ / (G * Real.sqrt N) < 2 * s := by linarith
    have := (div_lt_iff₀ hpos_GsN).mp htemp
    nlinarith
  -- Now prove the main inequality by clearing denominators
  have hgoal : Δ ^ 2 + s ^ 2 * G ^ 2 * (Real.sqrt N) ^ 2 ≤ 3 * Δ * G * s * Real.sqrt N := by
    nlinarith
  -- Convert back to the original statement
  field_simp [ne_of_gt hsqrtN, ne_of_gt hs_pos]
  nlinarith [hsqrtN_sq, hgoal]

end AdversarialBco.Bit.Aux_sp_step_rule

