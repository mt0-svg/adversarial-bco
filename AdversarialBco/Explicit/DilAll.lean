/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Interface
public import AdversarialBco.Body2.Arith
public import AdversarialBco.Body.Smooth
public import AdversarialBco.Body.Convex
public import AdversarialBco.Body.Cloud
public import AdversarialBco.Body.Inner
public import AdversarialBco.Body.Transfer
public import AdversarialBco.Body.Dil

@[expose] public section

/-!
# Theorem 3.1 for every family from its regular case (Appendix D)

`dilTheorem_of_reg : DilRegExplicit → EcReg → DilTheorem`, the cut of `AdversarialBco/Body2/Interface.lean`:
Theorem 3.1 (`BodySpec.DilTheorem`, `AdversarialBco/StatementBody.lean`) for every convex Lipschitz family from its
case of a regular family (`DilRegExplicit`: class `C^2` with Lipschitz gradients, minimisers over invertible `S`).

- A. Operators and matrices: positive definite operators, the square root of `S S^*` (`exists_sqrt_mul_adjoint`) and
  the strict concavity of `log det` (`det_add_sq`, by the spectral theorem).
- B. Gaussian integrals: `S Z` and `P Z` have the same law when `S S^* = P P^*` (`map_stdGaussian_eq`), the standard
  Gaussian charges every open set, dominated convergence along `b_n + S_n Z`.
- C. Lemma D.2: the entropic Gaussian of a convex coercive Lipschitz function is unique (`entropic_unique`).
- D. Lemma D.3: minimisers over invertible `S` are minimisers over positive definite `S` (`isMinInv_spd`), lie
  in a compact set (`uniform_bounds`), and a limit of them is again one (`limit_isMinInv`).
- E. Lemma D.5: the regular families `F_c + ε_k |· - b*|` smoothed by a bump (`approx_family`), their
  minimisers and gains.
- F. `dilTheorem_of_reg`: conclusions (S3), (S4) and (P3) of the regular families pass to the limit; the hypothesis
  `EcReg` is not used.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.DilAll
open Matrix
open AdversarialBco.BodySpec AdversarialBco.Body2

/-! ## A. Operators and matrices -/

theorem isSPD_iff_posDef {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    IsSPD S ↔ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm S).PosDef := by
  set M := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm S with hM
  have hS : S = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M := by rw [hM, StarAlgEquiv.apply_symm_apply]
  have hsa : IsSelfAdjoint S ↔ M.IsHermitian := by
    rw [hS, IsSelfAdjoint, ← map_star, EmbeddingLike.apply_eq_iff_eq,
      Matrix.IsHermitian, Matrix.star_eq_conjTranspose]
  have hq : ∀ v : EuclideanSpace ℝ (Fin d), ⟪S v, v⟫ = WithLp.ofLp v ⬝ᵥ M *ᵥ WithLp.ofLp v := by
    intro v; rw [real_inner_comm, hS, Matrix.inner_toEuclideanCLM]
  rw [IsSPD, hsa, Matrix.posDef_iff_dotProduct_mulVec]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h v hv => ?_⟩
  · have hx' : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h0; apply hx; simpa using congrArg WithLp.ofLp h0
    have := h _ hx'
    rw [hq] at this
    simpa using this
  · have hv' : WithLp.ofLp v ≠ 0 := by
      intro h0; apply hv; simpa using congrArg (WithLp.toLp 2) h0
    have := h hv'
    rw [hq]
    simpa using this

theorem det_eq_det_symm {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm S).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  rfl

theorem det_pos_of_isSPD {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : IsSPD S) :
    0 < LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
  rw [det_eq_det_symm]
  exact ((isSPD_iff_posDef S).1 hS).det_pos

theorem isSPD_add {d : ℕ} (S T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : IsSPD S)
    (hT : IsSPD T) : IsSPD (S + T) := by
  rw [isSPD_iff_posDef] at hS hT ⊢
  rw [map_add]
  exact hS.add hT

theorem isSPD_smul {d : ℕ} (c : ℝ) (hc : 0 < c) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS : IsSPD S) : IsSPD (c • S) := by
  rw [isSPD_iff_posDef] at hS ⊢
  rw [map_smul]
  exact hS.smul hc

theorem isSPD_of_tendsto {d : ℕ} (S : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (S0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : Tendsto S atTop (𝓝 S0))
    (hspd : ∀ n, IsSPD (S n))
    (hdet : LinearMap.det (S0 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) : IsSPD S0 := by
  have hsa : IsSelfAdjoint S0 := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro v w
    have h1 : Tendsto (fun n => ⟪S n v, w⟫) atTop (𝓝 ⟪S0 v, w⟫) :=
      (((continuous_eval_const v).inner continuous_const).tendsto S0).comp hS
    have h2 : Tendsto (fun n => ⟪v, S n w⟫) atTop (𝓝 ⟪v, S0 w⟫) :=
      ((continuous_const.inner (continuous_eval_const w)).tendsto S0).comp hS
    have e : (fun n => ⟪S n v, w⟫) = fun n => ⟪v, S n w⟫ :=
      funext fun n => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hspd n).1 v w
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  have hnn : ∀ v, 0 ≤ ⟪S0 v, v⟫ := fun v =>
    ge_of_tendsto' ((((continuous_eval_const v).inner continuous_const).tendsto S0).comp hS) fun n => by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((hspd n).2 v hv).le
  have hpos : S0.IsPositive := (ContinuousLinearMap.isPositive_iff' S0).2 ⟨hsa, hnn⟩
  set M := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm S0 with hM
  have hS0 : S0 = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M := by rw [hM, StarAlgEquiv.apply_symm_apply]
  have hMpsd : M.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff]
    have := hpos.toLinearMap
    rw [hS0] at this
    exact this
  rw [isSPD_iff_posDef]
  exact hMpsd.posDef_iff_det_ne_zero.2 (by rwa [← det_eq_det_symm])

open scoped MatrixOrder in
theorem exists_sqrt_mul_adjoint {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hS : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0) :
    ∃ P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSPD P ∧
      P ∘L ContinuousLinearMap.adjoint P = S ∘L ContinuousLinearMap.adjoint S ∧
      LinearMap.det (P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
        |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  set M := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm S with hM
  have hS' : S = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M := by rw [hM, StarAlgEquiv.apply_symm_apply]
  have hMdet : M.det ≠ 0 := by rwa [← det_eq_det_symm]
  have hApsd : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  set R := CFC.sqrt (M * Mᴴ) with hR
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
  have hRR : R * R = M * Mᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.2 hApsd)
  have hRdet : R.det ^ 2 = M.det ^ 2 := by
    rw [sq, ← det_mul, hRR, det_mul, det_conjTranspose, star_trivial, sq]
  have hRdet0 : R.det ≠ 0 := by
    intro h; rw [h] at hRdet; exact hMdet (pow_eq_zero_iff (two_ne_zero) |>.1 (by rw [← hRdet]; ring))
  have hRpd : R.PosDef := hRpsd.posDef_iff_det_ne_zero.2 hRdet0
  have hRpos := hRpd.det_pos
  refine ⟨Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) R, ?_, ?_, ?_⟩
  · rw [isSPD_iff_posDef, StarAlgEquiv.symm_apply_apply]; exact hRpd
  · rw [hS', ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_star,
      ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul, Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose, hRpsd.1.eq, hRR]
  · rw [det_eq_det_symm, det_eq_det_symm, StarAlgEquiv.symm_apply_apply, ← abs_of_pos hRpos]
    exact (sq_eq_sq_iff_abs_eq_abs _ _).1 hRdet

theorem map_stdGaussian_eq {d : ℕ} (S P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : P ∘L ContinuousLinearMap.adjoint P = S ∘L ContinuousLinearMap.adjoint S) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map S = (stdGaussian (EuclideanSpace ℝ (Fin d))).map P := by
  have key : ∀ (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (L : StrongDual ℝ (EuclideanSpace ℝ (Fin d))), ‖L.comp T‖ ^ 2 =
      ⟪(T ∘L ContinuousLinearMap.adjoint T) ((InnerProductSpace.toDual ℝ _).symm L),
        (InnerProductSpace.toDual ℝ _).symm L⟫ := by
    intro T L
    set ℓ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm L with hℓ
    have hL : L.comp T = InnerProductSpace.toDual ℝ _ (ContinuousLinearMap.adjoint T ℓ) := by
      ext x
      rw [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
        ContinuousLinearMap.adjoint_inner_left, ← InnerProductSpace.toDual_apply_apply, hℓ,
        LinearIsometryEquiv.apply_symm_apply]
    rw [hL, LinearIsometryEquiv.norm_map, ← real_inner_self_eq_norm_sq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have hn : ∀ L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)), ‖L.comp S‖ = ‖L.comp P‖ := fun L =>
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [key S L, key P L, h])
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian, hn L]

theorem det_conj_unitary {d : ℕ} (U : unitary (Matrix (Fin d) (Fin d) ℝ)) (X : Matrix (Fin d) (Fin d) ℝ) :
    ((U : Matrix (Fin d) (Fin d) ℝ) * X * star (U : Matrix (Fin d) (Fin d) ℝ)).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (U : Matrix (Fin d) (Fin d) ℝ)), mul_assoc, ← Matrix.det_mul,
    Unitary.mul_star_self_of_mem U.2, Matrix.det_one, mul_one]

theorem det_one_add_sq {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosDef) :
    4 ^ d * C.det ≤ (1 + C).det ^ 2 ∧ (C ≠ 1 → 4 ^ d * C.det < (1 + C).det ^ 2) := by
  set μ := hC.1.eigenvalues with hμ
  set U := hC.1.eigenvectorUnitary
  have hμpos : ∀ i, 0 < μ i := hC.eigenvalues_pos
  have hspec := hC.1.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  have hD : C.det = ∏ i, μ i := by
    rw [hC.1.det_eq_prod_eigenvalues]; simp [hμ]
  have h1C : 1 + C = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal (fun i => 1 + μ i) * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    have h1 : (1 : Matrix (Fin d) (Fin d) ℝ) = (U : Matrix (Fin d) (Fin d) ℝ) * 1 * star (U : Matrix (Fin d) (Fin d) ℝ) := by
      rw [mul_one, Unitary.mul_star_self_of_mem U.2]
    conv_lhs => rw [h1, hspec]
    rw [← add_mul, ← mul_add, ← diagonal_one, diagonal_add]
    rfl
  have hD1 : (1 + C).det = ∏ i, (1 + μ i) := by
    rw [h1C, det_conj_unitary, det_diagonal]
  have hfac : ∀ i, 4 * μ i ≤ (1 + μ i) ^ 2 := fun i => by nlinarith [sq_nonneg (1 - μ i)]
  have hprod : 4 ^ d * C.det = ∏ i, 4 * μ i := by
    rw [hD, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsq : (1 + C).det ^ 2 = ∏ i, (1 + μ i) ^ 2 := by rw [hD1, Finset.prod_pow]
  refine ⟨?_, fun hne => ?_⟩
  · rw [hprod, hsq]
    exact Finset.prod_le_prod₀ (fun i _ => by have := hμpos i; positivity) (fun i _ => hfac i)
  · have hex : ∃ j, μ j ≠ 1 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      apply hne
      rw [hspec]
      have : (RCLike.ofReal ∘ μ : Fin d → ℝ) = fun _ => 1 := funext fun i => by simp [hall i]
      rw [show (RCLike.ofReal ∘ hC.1.eigenvalues : Fin d → ℝ) = fun _ => 1 from this, diagonal_one, mul_one,
        Unitary.mul_star_self_of_mem hC.1.eigenvectorUnitary.2]
    obtain ⟨j, hj⟩ := hex
    rw [hprod, hsq]
    refine Finset.prod_lt_prod₀ (fun i _ => by have := hμpos i; positivity) (fun i _ => hfac i) ⟨j, Finset.mem_univ j, ?_⟩
    have : (1 - μ j) ^ 2 > 0 := by
      have : 1 - μ j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
      positivity
    nlinarith

open scoped MatrixOrder in
theorem det_add_sq_matrix {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    4 ^ d * A.det * B.det ≤ (A + B).det ^ 2 ∧ (A ≠ B → 4 ^ d * A.det * B.det < (A + B).det ^ 2) := by
  set R := CFC.sqrt A with hR
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.2 hA.posSemidef)
  have hAdet := hA.det_pos
  have hRdet : R.det ^ 2 = A.det := by rw [sq, ← det_mul, hRR]
  have hRdet0 : R.det ≠ 0 := by
    intro h; rw [h] at hRdet; linarith [hRdet.symm.le, sq_nonneg (0 : ℝ)]
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 hRdet0
  have hRiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRih : (R⁻¹)ᴴ = R⁻¹ := by rw [conjTranspose_nonsing_inv, hRpsd.1.eq]
  have hRiu : IsUnit R⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det R).2 hRu)
  set C := R⁻¹ * B * R⁻¹ with hCdef
  have hC : C.PosDef := by
    have := hB.conjTranspose_mul_mul_same (B := R⁻¹) (mulVec_injective_iff_isUnit.2 hRiu)
    rwa [hRih] at this
  have hAB : A + B = R * (1 + C) * R := by
    rw [hCdef, mul_add, add_mul, mul_one, hRR, ← mul_assoc, ← mul_assoc, hRRi, one_mul, mul_assoc, hRiR, mul_one]
  have hBC : B = R * C * R := by
    rw [hCdef, ← mul_assoc, ← mul_assoc, hRRi, one_mul, mul_assoc, hRiR, mul_one]
  have hdAB : (A + B).det = A.det * (1 + C).det := by
    rw [hAB, det_mul, det_mul, ← hRdet]; ring
  have hdB : B.det = A.det * C.det := by
    rw [hBC, det_mul, det_mul, ← hRdet]; ring
  obtain ⟨h1, h2⟩ := det_one_add_sq C hC
  have hA2 : 0 < A.det ^ 2 := by positivity
  refine ⟨?_, fun hne => ?_⟩
  · rw [hdAB, hdB]
    calc 4 ^ d * A.det * (A.det * C.det) = A.det ^ 2 * (4 ^ d * C.det) := by ring
      _ ≤ A.det ^ 2 * (1 + C).det ^ 2 := mul_le_mul_of_nonneg_left h1 hA2.le
      _ = (A.det * (1 + C).det) ^ 2 := by ring
  · have hC1 : C ≠ 1 := by
      intro h; apply hne; rw [hBC, h, mul_one, hRR]
    rw [hdAB, hdB]
    calc 4 ^ d * A.det * (A.det * C.det) = A.det ^ 2 * (4 ^ d * C.det) := by ring
      _ < A.det ^ 2 * (1 + C).det ^ 2 := mul_lt_mul_of_pos_left (h2 hC1) hA2
      _ = (A.det * (1 + C).det) ^ 2 := by ring

open AdversarialBco.Body2 AdversarialBco.BodySpec Filter ProbabilityTheory Topology in
open scoped RealInnerProductSpace NNReal in
theorem det_add_sq {d : ℕ} (S T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : IsSPD S)
    (hT : IsSPD T) :
    4 ^ d * LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
        LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≤
      LinearMap.det ((S + T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ^ 2 ∧
    (S ≠ T → 4 ^ d * LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) *
        LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) <
      LinearMap.det ((S + T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ^ 2) := by
  let φ := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm
  have h_add : φ (S + T) = φ S + φ T :=
    φ.map_add S T
  have hA_pos : (φ S).PosDef :=
    ((AdversarialBco.DilAll.isSPD_iff_posDef S).mp hS)
  have hB_pos : (φ T).PosDef :=
    ((AdversarialBco.DilAll.isSPD_iff_posDef T).mp hT)
  have h_detS : LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (φ S).det :=
    AdversarialBco.DilAll.det_eq_det_symm S
  have h_detT : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (φ T).det :=
    AdversarialBco.DilAll.det_eq_det_symm T
  have h_detST : LinearMap.det ((S + T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (φ (S + T)).det :=
    AdversarialBco.DilAll.det_eq_det_symm (S + T)
  rcases AdversarialBco.DilAll.det_add_sq_matrix (φ S) (φ T) hA_pos hB_pos with ⟨h_le, h_lt⟩
  rw [h_add] at h_detST
  rw [h_detS, h_detT, h_detST]
  refine ⟨h_le, ?_⟩
  intro hST_ne
  apply h_lt
  intro hAB_eq
  apply hST_ne
  exact φ.injective hAB_eq

/-! ## B. Gaussian integrals -/

theorem integral_eq_of_map_eq {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : Continuous G)
    (b : EuclideanSpace ℝ (Fin d)) (S P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : (stdGaussian (EuclideanSpace ℝ (Fin d))).map S = (stdGaussian (EuclideanSpace ℝ (Fin d))).map P) :
    ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ z, G (b + P z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hc : Continuous fun y => G (b + y) := hG.comp (continuous_const.add continuous_id)
  rw [← integral_map (f := fun y => G (b + y)) S.continuous.measurable.aemeasurable
      hc.aestronglyMeasurable, h,
    integral_map P.continuous.measurable.aemeasurable hc.aestronglyMeasurable]

theorem isOpenPosMeasure_stdGaussian (d : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).IsOpenPosMeasure := by
  have hg : (gaussianReal 0 1).IsOpenPosMeasure := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
    refine ⟨fun U hU hne => ?_⟩
    rw [withDensity_apply _ hU.measurableSet]
    refine ((setLIntegral_pos_iff (measurable_gaussianPDF 0 1)).2 ?_).ne'
    have hsupp : Function.support (gaussianPDF 0 1) = Set.univ :=
      Set.eq_univ_of_forall fun x => (gaussianPDF_pos 0 one_ne_zero x).ne'
    rw [hsupp, Set.univ_inter]
    exact hU.measure_pos volume hne
  rw [← map_pi_eq_stdGaussian]
  exact (PiLp.continuous_toLp 2 _).isOpenPosMeasure_map (fun x => ⟨WithLp.ofLp x, rfl⟩)

theorem eq_zero_of_integral_eq_zero {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f)
    (h0 : ∀ z, 0 ≤ f z) (hi : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))))
    (h : ∫ z, f z ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = 0) : ∀ z, f z = 0 := by
  have := isOpenPosMeasure_stdGaussian d
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => h0 z) hi).1 h
  have := (Continuous.ae_eq_iff_eq (stdGaussian (EuclideanSpace ℝ (Fin d))) hf continuous_const).1 hae
  exact fun z => congrFun this z

theorem tendsto_of_lipschitz {d : ℕ} (H : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (H0 : EuclideanSpace ℝ (Fin d) → ℝ)
    (K : ℝ≥0) (hH : ∀ n, LipschitzWith K (H n)) (hpt : ∀ y, Tendsto (fun n => H n y) atTop (𝓝 (H0 y)))
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (y0 : EuclideanSpace ℝ (Fin d)) (hy : Tendsto y atTop (𝓝 y0)) :
    Tendsto (fun n => H n (y n)) atTop (𝓝 (H0 y0)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun n => (K : ℝ) * dist (y n) y0) atTop (𝓝 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.1 hy).const_mul (K : ℝ)
  have h2 := tendsto_iff_dist_tendsto_zero.1 (hpt y0)
  refine squeeze_zero (g := fun n => (K : ℝ) * dist (y n) y0 + dist (H n y0) (H0 y0)) (fun n => dist_nonneg)
    (fun n => (dist_triangle _ (H n y0) _).trans (add_le_add ((hH n).dist_le_mul _ _) le_rfl)) ?_
  simpa using h1.add h2

theorem tendsto_integral_cloud {d : ℕ} (H : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (H0 : EuclideanSpace ℝ (Fin d) → ℝ) (b : ℕ → EuclideanSpace ℝ (Fin d))
    (S : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b0 : EuclideanSpace ℝ (Fin d))
    (S0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hb : Tendsto b atTop (𝓝 b0))
    (hS : Tendsto S atTop (𝓝 S0)) (hH : ∀ n, Continuous (H n))
    (hconv : ∀ (y : ℕ → EuclideanSpace ℝ (Fin d)) (y0 : EuclideanSpace ℝ (Fin d)), Tendsto y atTop (𝓝 y0) →
      Tendsto (fun n => H n (y n)) atTop (𝓝 (H0 y0)))
    (C : ℝ) (hC : ∀ n y, |H n y| ≤ C * (1 + ‖y‖ ^ 2)) :
    Tendsto (fun n => ∫ z, H n (b n + S n z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) atTop
      (𝓝 (∫ z, H0 (b0 + S0 z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) := by
  obtain ⟨Bb, hBb⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hb)
  obtain ⟨BS, hBS⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hS)
  set B := max Bb BS with hB
  have hb' : ∀ n, ‖b n‖ ≤ B := fun n => (hBb _ (Set.mem_range_self n)).trans (le_max_left _ _)
  have hS' : ∀ n, ‖S n‖ ≤ B := fun n => (hBS _ (Set.mem_range_self n)).trans (le_max_right _ _)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb' 0)
  have hsq : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (IsGaussian.memLp_two_id).integrable_norm_pow (by norm_num)
  refine tendsto_integral_of_dominated_convergence (fun z => |C| * (1 + 2 * B ^ 2 + 2 * B ^ 2 * ‖z‖ ^ 2))
    (fun n => ((hH n).comp (continuous_const.add (S n).continuous)).aestronglyMeasurable)
    (((integrable_const _).add (hsq.const_mul _)).const_mul _) (fun n => ae_of_all _ fun z => ?_)
    (ae_of_all _ fun z => hconv _ _ (hb.add (((continuous_eval_const z).tendsto S0).comp hS)))
  have h1 : ‖b n + S n z‖ ≤ B + B * ‖z‖ :=
    (norm_add_le _ _).trans (add_le_add (hb' n) ((S n).le_opNorm z |>.trans
      (mul_le_mul_of_nonneg_right (hS' n) (norm_nonneg _))))
  have h2 : ‖b n + S n z‖ ^ 2 ≤ 2 * B ^ 2 + 2 * B ^ 2 * ‖z‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (B - B * ‖z‖)]
  rw [Real.norm_eq_abs]
  calc |H n (b n + S n z)| ≤ C * (1 + ‖b n + S n z‖ ^ 2) := hC n _
    _ ≤ |C| * (1 + ‖b n + S n z‖ ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + 2 * B ^ 2 + 2 * B ^ 2 * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)

theorem integrable_lip {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (hG : LipschitzWith L G)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => G (b + S z)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h := (AdversarialBco.Body.tr_integrable_cloud b S G L hG).1
  have hm : Measurable fun g : EuclideanSpace ℝ (Fin d) => b + S g := (continuous_const.add S.continuous).measurable
  exact (integrable_map_measure hG.continuous.aestronglyMeasurable hm.aemeasurable).1 h

theorem lip_growth {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (hG : LipschitzWith K G) (B : ℝ)
    (hB : |G 0| ≤ B) (x : EuclideanSpace ℝ (Fin d)) : |G x| ≤ (B + K) * (1 + ‖x‖ ^ 2) := by
  have h1 : |G x - G 0| ≤ K * ‖x‖ := by
    have := hG.dist_le_mul x 0
    rwa [Real.dist_eq, dist_zero_right] at this
  have h2 := abs_sub_abs_le_abs_sub (G x) (G 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have ht : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hK : (0 : ℝ) ≤ K := K.2
  nlinarith [mul_le_mul_of_nonneg_left ht hK, mul_nonneg hB0 (sq_nonneg ‖x‖)]

/-! ## C. Uniqueness of the entropic Gaussian (Lemma D.2) -/

open AdversarialBco.Body2 AdversarialBco.BodySpec Filter ProbabilityTheory Topology in
open scoped RealInnerProductSpace NNReal in
theorem int_affine {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (v : EuclideanSpace ℝ (Fin d))
    (h : ∀ x, G (x + v) = (G x + G (x + (2 : ℝ) • v)) / 2) (n : ℤ) :
    G ((n : ℝ) • v) = G 0 + n * (G v - G 0) := by
  set a := fun (n : ℤ) => G ((n : ℝ) • v) with ha
  have ha0 : a 0 = G 0 := by
    simp [a]
  have ha1 : a 1 = G v := by
    simp [a]
  have hrec : ∀ n : ℤ, a (n + 1) = 2 * a n - a (n - 1) := by
    intro n
    have hx := h (((n : ℝ) - 1) • v)
    have h_smul1 : (((n : ℝ) - 1) • v) + v = (n : ℝ) • v := by
      calc
        (((n : ℝ) - 1) • v) + v = (((n : ℝ) - 1) • v) + (1 : ℝ) • v := by simp
        _ = (((n : ℝ) - 1) + 1) • v := by rw [← add_smul]
        _ = (n : ℝ) • v := by norm_num
    have h_smul2 : (((n : ℝ) - 1) • v) + (2 : ℝ) • v = ((n : ℝ) + 1) • v := by
      calc
        (((n : ℝ) - 1) • v) + (2 : ℝ) • v = (((n : ℝ) - 1) + 2) • v := by rw [← add_smul]
        _ = ((n : ℝ) + 1) • v := by congr 1; ring
    rw [h_smul1, h_smul2] at hx
    have ha_left : G ((n : ℝ) • v) = a n := rfl
    have ha_mid : G (((n : ℝ) - 1) • v) = a (n - 1) := by
      dsimp [a]
      have : ((n : ℝ) - 1) = ((n - 1 : ℤ) : ℝ) := by push_cast; ring
      rw [this]
    have ha_right : G (((n : ℝ) + 1) • v) = a (n + 1) := by
      dsimp [a]
      have : ((n : ℝ) + 1) = ((n + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [this]
    rw [ha_left, ha_mid, ha_right] at hx
    linarith
  set P := fun (n : ℤ) => a n = a 0 + (n : ℝ) * (a 1 - a 0) with hP
  have hP0 : P 0 := by
    dsimp [P]
    simp [a]
  have hP1 : P 1 := by
    dsimp [P]
    simp [a]
  have hPpos : ∀ n : ℕ, P (n : ℤ) ∧ P ((n : ℤ) + 1) := by
    intro n
    induction' n with k ih
    · exact ⟨hP0, hP1⟩
    · rcases ih with ⟨hPk, hPk1⟩
      have hPk2 : P ((k : ℤ) + 2) := by
        dsimp [P] at hPk hPk1 ⊢
        have hrec_simp : a ((k : ℤ) + 2) = 2 * a ((k : ℤ) + 1) - a (k : ℤ) := by
          have := hrec ((k : ℤ) + 1)
          simpa [show ((k : ℤ) + 1) + 1 = (k : ℤ) + 2 by ring,
            show ((k : ℤ) + 1) - 1 = (k : ℤ) by ring] using this
        rw [hrec_simp]
        rw [hPk, hPk1]
        push_cast
        ring
      exact ⟨hPk1, hPk2⟩
  have hPnonpos : ∀ n : ℕ, P (-(n : ℤ)) ∧ P (-(n : ℤ) + 1) := by
    intro n
    induction' n with k ih
    · exact ⟨hP0, hP1⟩
    · rcases ih with ⟨hPnegk, hPnegk1⟩
      have hPnegk2 : P (-(k : ℤ) - 1) := by
        dsimp [P] at hPnegk hPnegk1 ⊢
        have hrec_simp : a (-(k : ℤ) - 1) = 2 * a (-(k : ℤ)) - a (-(k : ℤ) + 1) := by
          have := hrec (-(k : ℤ))
          linarith
        rw [hrec_simp]
        rw [hPnegk, hPnegk1]
        push_cast
        ring
      have hPnegk' : P (-(k : ℤ)) := hPnegk
      simpa [show -((k : ℤ) + 1) = -(k : ℤ) - 1 by ring] using And.intro hPnegk2 hPnegk'
  have hPall : ∀ n : ℤ, P n := by
    intro n
    by_cases hn : 0 ≤ n
    · let k : ℕ := Int.toNat n
      have hk_eq : (k : ℤ) = n := by
        dsimp [k]
        exact Int.toNat_of_nonneg hn
      rw [← hk_eq]
      exact (hPpos k).1
    · have hn' : 0 ≤ -n := by linarith
      let k : ℕ := Int.toNat (-n)
      have hk_eq : (k : ℤ) = -n := by
        dsimp [k]
        exact Int.toNat_of_nonneg hn'
      have hn_eq : n = -(k : ℤ) := by linarith
      rw [hn_eq]
      exact (hPnonpos k).1
  dsimp [P, a] at hPall
  simpa using hPall n

open AdversarialBco.Body2 AdversarialBco.BodySpec Filter ProbabilityTheory Topology in
open scoped RealInnerProductSpace NNReal in
theorem eq_zero_of_midpoint {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (a1 a2 : ℝ) (ha : 0 < a1)
    (hcoer : ∀ x, a1 * ‖x‖ - a2 ≤ G x) (v : EuclideanSpace ℝ (Fin d))
    (h : ∀ x, G (x + v) = (G x + G (x + (2 : ℝ) • v)) / 2) : v = 0 := by
  by_contra! hv
  have hnorm_pos : 0 < ‖v‖ := (norm_pos_iff.mpr hv)
  have ha1v_pos : 0 < a1 * ‖v‖ := mul_pos ha hnorm_pos
  set δ := G v - G 0 with hδ
  have h_affine_nat (n : ℕ) : G ((n : ℝ) • v) = G 0 + (n : ℝ) * δ := by
    have h_int := AdversarialBco.DilAll.int_affine G v h (n : ℤ)
    simpa [hδ, Int.cast_ofNat] using h_int
  have h_affine_neg_nat (n : ℕ) : G ((-(n : ℝ)) • v) = G 0 - (n : ℝ) * δ := by
    have h_int := AdversarialBco.DilAll.int_affine G v h (-(n : ℤ))
    simpa [hδ, Int.cast_ofNat, Int.cast_neg, sub_eq_add_neg] using h_int
  have h_sum (n : ℕ) : G ((n : ℝ) • v) + G ((-(n : ℝ)) • v) = 2 * G 0 := by
    rw [h_affine_nat n, h_affine_neg_nat n]
    ring
  have h_ineq (n : ℕ) : a1 * (n : ℝ) * ‖v‖ - a2 ≤ G 0 := by
    have h1 := hcoer ((n : ℝ) • v)
    have h2 := hcoer ((-(n : ℝ)) • v)
    have hnorm1 : ‖(n : ℝ) • v‖ = (n : ℝ) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hnorm2 : ‖(-(n : ℝ)) • v‖ = (n : ℝ) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hnorm1] at h1
    rw [hnorm2] at h2
    have hsum := add_le_add h1 h2
    rw [h_sum n] at hsum
    linarith
  rcases exists_nat_gt ((G 0 + a2) / (a1 * ‖v‖)) with ⟨n, hn⟩
  have h_ineq_n := h_ineq n
  have h_contra : a1 * (n : ℝ) * ‖v‖ - a2 > G 0 := by
    have h_mul' := mul_lt_mul_of_pos_right hn ha1v_pos
    have h_eq : ((G 0 + a2) / (a1 * ‖v‖)) * (a1 * ‖v‖) = G 0 + a2 := by
      field_simp [ha1v_pos.ne.symm]
    have h_mul : G 0 + a2 < (n : ℝ) * (a1 * ‖v‖) := by
      linarith
    have h_comm : a1 * (n : ℝ) * ‖v‖ = (n : ℝ) * (a1 * ‖v‖) := by ring
    rw [h_comm]
    linarith
  linarith

theorem integral_midpoint_le {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hGc : ConvexOn ℝ Set.univ G) (L : ℝ≥0)
    (hGL : LipschitzWith L G) (b1 b2 : EuclideanSpace ℝ (Fin d))
    (S1 S2 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ z, G ((1 / 2 : ℝ) • (b1 + b2) + ((1 / 2 : ℝ) • (S1 + S2)) z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      (∫ z, G (b1 + S1 z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
        ∫ z, G (b2 + S2 z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / 2 := by
  have hm : ∀ z, G ((1 / 2 : ℝ) • (b1 + b2) + ((1 / 2 : ℝ) • (S1 + S2)) z) ≤
      (G (b1 + S1 z) + G (b2 + S2 z)) / 2 := by
    intro z
    have hc := hGc.2 (Set.mem_univ (b1 + S1 z)) (Set.mem_univ (b2 + S2 z)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e : (1 / 2 : ℝ) • (b1 + b2) + ((1 / 2 : ℝ) • (S1 + S2)) z =
        (1 / 2 : ℝ) • (b1 + S1 z) + (1 / 2 : ℝ) • (b2 + S2 z) := by
      simp only [_root_.smul_apply, _root_.add_apply, smul_add]; abel
    rw [e]; simp only [smul_eq_mul] at hc; linarith
  have i1 := integrable_lip G L hGL b1 S1
  have i2 := integrable_lip G L hGL b2 S2
  have i0 := integrable_lip G L hGL ((1 / 2 : ℝ) • (b1 + b2)) ((1 / 2 : ℝ) • (S1 + S2))
  calc _ ≤ ∫ z, (G (b1 + S1 z) + G (b2 + S2 z)) / 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono i0 ((i1.add i2).div_const 2) hm
    _ = _ := by rw [integral_div, integral_add i1 i2]

theorem entropic_unique {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hGc : ConvexOn ℝ Set.univ G) (L : ℝ≥0)
    (hGL : LipschitzWith L G) (a1 a2 : ℝ) (ha : 0 < a1) (hcoer : ∀ x, a1 * ‖x‖ - a2 ≤ G x) (lam : ℝ)
    (hlam : 0 < lam) (b1 b2 : EuclideanSpace ℝ (Fin d))
    (S1 S2 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h1 : IsEntropicGaussian G lam b1 S1) (h2 : IsEntropicGaussian G lam b2 S2) : b1 = b2 ∧ S1 = S2 := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  obtain ⟨hS1, hmin1⟩ := h1
  obtain ⟨hS2, hmin2⟩ := h2
  have hint : ∀ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      Integrable (fun z => G (b + S z)) γ := fun b S => integrable_lip G L hGL b S
  have hd1 := det_pos_of_isSPD S1 hS1
  have hd2 := det_pos_of_isSPD S2 hS2
  have hS12 := isSPD_add S1 S2 hS1 hS2
  have hd12 := det_pos_of_isSPD _ hS12
  have hSm : IsSPD ((1 / 2 : ℝ) • (S1 + S2)) := isSPD_smul _ (by norm_num) _ hS12
  have hdm : LinearMap.det (((1 / 2 : ℝ) • (S1 + S2) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
      (1 / 2 : ℝ) ^ d * LinearMap.det ((S1 + S2 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul, finrank_euclideanSpace_fin]
  have hdmpos : 0 < LinearMap.det (((1 / 2 : ℝ) • (S1 + S2) : EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := det_pos_of_isSPD _ hSm
  obtain ⟨hdet, hdet_lt⟩ := det_add_sq S1 S2 hS1 hS2
  set D1 := LinearMap.det (S1 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  set D2 := LinearMap.det (S2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  set D12 := LinearMap.det ((S1 + S2 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  set Dm := LinearMap.det (((1 / 2 : ℝ) • (S1 + S2) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  have h4 : (4 : ℝ) ^ d * ((1 / 2 : ℝ) ^ d) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm d 2, pow_mul, ← mul_pow]; norm_num
  have hprod : D1 * D2 ≤ Dm ^ 2 := by
    rw [hdm, mul_pow]
    calc D1 * D2 = ((1 / 2 : ℝ) ^ d) ^ 2 * (4 ^ d * D1 * D2) := by linear_combination (-(D1 * D2)) * h4
      _ ≤ ((1 / 2 : ℝ) ^ d) ^ 2 * D12 ^ 2 := mul_le_mul_of_nonneg_left hdet (by positivity)
  have hlogsq : Real.log (Dm ^ 2) = 2 * Real.log Dm := by rw [Real.log_pow]; norm_num
  have hlog : Real.log D1 + Real.log D2 ≤ 2 * Real.log Dm := by
    rw [← Real.log_mul hd1.ne' hd2.ne', ← hlogsq]
    exact Real.log_le_log (mul_pos hd1 hd2) hprod
  have hmid := integral_midpoint_le G hGc L hGL b1 b2 S1 S2
  have e12 := hmin1 b2 S2 hS2
  have e21 := hmin2 b1 S1 hS1
  have em := hmin1 ((1 / 2 : ℝ) • (b1 + b2)) _ hSm
  simp only [entropic] at e12 e21 em
  have hS : S1 = S2 := by
    by_contra hne
    have hprod' : D1 * D2 < Dm ^ 2 := by
      rw [hdm, mul_pow]
      calc D1 * D2 = ((1 / 2 : ℝ) ^ d) ^ 2 * (4 ^ d * D1 * D2) := by linear_combination (-(D1 * D2)) * h4
        _ < ((1 / 2 : ℝ) ^ d) ^ 2 * D12 ^ 2 := mul_lt_mul_of_pos_left (hdet_lt hne) (by positivity)
    have hlog' : Real.log D1 + Real.log D2 < 2 * Real.log Dm := by
      rw [← Real.log_mul hd1.ne' hd2.ne', ← hlogsq]
      exact Real.log_lt_log (mul_pos hd1 hd2) hprod'
    nlinarith
  subst hS
  refine ⟨?_, rfl⟩
  have hhalf : (1 / 2 : ℝ) • (S1 + S1) = S1 := by rw [← two_smul ℝ S1, smul_smul]; norm_num
  rw [hhalf] at hmid em
  have em2 := hmin2 ((1 / 2 : ℝ) • (b1 + b2)) _ hS1
  simp only [entropic] at em2
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    (G (b1 + S1 z) + G (b2 + S1 z)) / 2 - G ((1 / 2 : ℝ) • (b1 + b2) + S1 z) with hf
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    have hc := hGc.2 (Set.mem_univ (b1 + S1 z)) (Set.mem_univ (b2 + S1 z)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have he : (1 / 2 : ℝ) • (b1 + S1 z) + (1 / 2 : ℝ) • (b2 + S1 z) = (1 / 2 : ℝ) • (b1 + b2) + S1 z := by
      rw [← smul_add, add_add_add_comm, ← two_smul ℝ (S1 z), smul_add, smul_smul]; norm_num
    rw [he, smul_eq_mul, smul_eq_mul] at hc
    simp only [hf]; linarith
  have hfc : Continuous f := by
    have hc := hGL.continuous
    simp only [hf]; fun_prop
  have i1 : Integrable (fun z => (G (b1 + S1 z) + G (b2 + S1 z)) / 2) γ :=
    ((hint b1 S1).add (hint b2 S1)).div_const 2
  have i2 : Integrable (fun z => G ((1 / 2 : ℝ) • (b1 + b2) + S1 z)) γ := hint _ S1
  have hfi : Integrable f γ := i1.sub i2
  have hfint : ∫ z, f z ∂γ = 0 := by
    simp only [hf]
    rw [integral_sub i1 i2, integral_div, integral_add (hint b1 S1) (hint b2 S1)]
    linarith
  have hf00 := eq_zero_of_integral_eq_zero f hfc hf0 hfi hfint
  have hsurj : Function.Surjective (S1 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd1.ne'))).2
  have hv := eq_zero_of_midpoint G a1 a2 ha hcoer ((1 / 2 : ℝ) • (b2 - b1)) (fun x => by
    obtain ⟨z, hz⟩ := hsurj (x - b1)
    have hz' : S1 z = x - b1 := hz
    have h0 := hf00 z
    simp only [hf, hz'] at h0
    have e1 : b1 + (x - b1) = x := by abel
    have e2 : (1 / 2 : ℝ) • (b1 + b2) + (x - b1) = x + (1 / 2 : ℝ) • (b2 - b1) := by
      rw [smul_add, smul_sub]; module
    have e3 : b2 + (x - b1) = x + (2 : ℝ) • ((1 / 2 : ℝ) • (b2 - b1)) := by
      rw [smul_smul]; norm_num; abel
    rw [e1, e2, e3] at h0
    linarith)
  have : b2 - b1 = 0 := by
    have h2 := congrArg (fun v => (2 : ℝ) • v) hv
    simpa [smul_smul] using h2
  exact (sub_eq_zero.1 this).symm

/-! ## D. Minimisers over invertible and over positive definite `S`; the limit (Lemma D.3) -/

theorem isEntropicGaussian_of_isMinInv {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (lam : ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hS : IsSPD S)
    (h : IsMinInv G lam b S) : IsEntropicGaussian G lam b S := by
  refine ⟨hS, fun b' S' hS' => ?_⟩
  have h1 := h.2 b' S' (det_pos_of_isSPD S' hS').ne'
  rw [abs_of_pos (det_pos_of_isSPD S hS), abs_of_pos (det_pos_of_isSPD S' hS')] at h1
  exact h1

theorem isMinInv_spd {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (hG : Continuous G) (lam : ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : IsMinInv G lam b S) :
    ∃ P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d), IsSPD P ∧ IsMinInv G lam b P := by
  obtain ⟨P, hP, hPP, hdet⟩ := exists_sqrt_mul_adjoint S h.1
  have hPdet : LinearMap.det (P : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    rw [hdet]; exact abs_ne_zero.2 h.1
  have hint := integral_eq_of_map_eq G hG b S P (map_stdGaussian_eq S P hPP)
  refine ⟨P, hP, hPdet, fun b' S' hS' => ?_⟩
  rw [← hint, hdet, abs_abs]
  exact h.2 b' S' hS'

theorem uniform_bounds {d : ℕ} (a1 a2 lam C : ℝ) (ha : 0 < a1) (ha2 : 0 ≤ a2) (hlam : 0 < lam) :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ (G : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0), LipschitzWith L G →
      (∀ x, a1 * ‖x‖ - a2 ≤ G x) → ∀ lam' : ℝ, lam / 2 ≤ lam' → lam' ≤ 2 * lam →
      ∀ (b : EuclideanSpace ℝ (Fin d)) (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 →
        ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
            lam' * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤ C →
        ‖b‖ ≤ M ∧ ‖S‖ ≤ M ∧ δ ≤ |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  set a := a1 / (2 * lam) with hadef
  set a' := 2 * a2 / lam with ha'def
  have ha0 : 0 < a := div_pos ha (by linarith)
  set G0 : EuclideanSpace ℝ (Fin d) → ℝ := fun x => a * ‖x‖ - a' with hG0def
  have hG0L : LipschitzWith (Real.toNNReal a) G0 := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal _ ha0.le, Real.dist_eq, dist_eq_norm]
    calc |G0 x - G0 y| = a * |‖x‖ - ‖y‖| := by
          rw [show G0 x - G0 y = a * (‖x‖ - ‖y‖) by simp only [hG0def]; ring, abs_mul, abs_of_pos ha0]
      _ ≤ a * ‖x - y‖ := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) ha0.le
  obtain ⟨M, δ, hδ, hbd⟩ := AdversarialBco.Body.entropic_bounded G0 _ hG0L a a' ha0 (fun x => le_rfl) 1 one_pos
    (2 * |C| / lam)
  refine ⟨M, δ, hδ, fun G L hGL hcoer lam' hl1 hl2 b S hS hobj => hbd b S hS ?_⟩
  have hlam' : 0 < lam' := by linarith
  have e1 : a * lam' ≤ a1 := by
    rw [hadef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have e2 : a2 ≤ a' * lam' := by
    rw [ha'def, div_mul_eq_mul_div, le_div_iff₀ hlam]; nlinarith
  have hle : ∀ x, G0 x ≤ G x / lam' := by
    intro x
    rw [le_div_iff₀ hlam']
    have h1 := hcoer x
    have h2 : a * lam' * ‖x‖ ≤ a1 * ‖x‖ := mul_le_mul_of_nonneg_right e1 (norm_nonneg x)
    simp only [hG0def]
    nlinarith
  have hint := integrable_lip G L hGL b S
  have hint0 := integrable_lip G0 _ hG0L b S
  calc ∫ z, G0 (b + S z) ∂γ -
        1 * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|
      ≤ ∫ z, G (b + S z) / lam' ∂γ -
        Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := by
        rw [one_mul]; exact sub_le_sub_right (integral_mono hint0 (hint.div_const _) (fun z => hle _)) _
    _ = (∫ z, G (b + S z) ∂γ -
        lam' * Real.log |LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|) / lam' := by
        rw [integral_div]; field_simp
    _ ≤ C / lam' := div_le_div_of_nonneg_right hobj hlam'.le
    _ ≤ |C| / lam' := div_le_div_of_nonneg_right (le_abs_self C) hlam'.le
    _ ≤ |C| / (lam / 2) := div_le_div_of_nonneg_left (abs_nonneg C) (by linarith) hl1
    _ = 2 * |C| / lam := by field_simp

theorem limit_isMinInv {d : ℕ} (G : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (G0 : EuclideanSpace ℝ (Fin d) → ℝ)
    (L : ℝ≥0) (hL : ∀ n, LipschitzWith L (G n))
    (hpt : ∀ y, Tendsto (fun n => G n y) atTop (𝓝 (G0 y))) (a1 a2 : ℝ) (ha : 0 < a1)
    (hcoer : ∀ n x, a1 * ‖x‖ - a2 ≤ G n x) (lam : ℕ → ℝ) (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hlam : Tendsto lam atTop (𝓝 lam0)) (b : ℕ → EuclideanSpace ℝ (Fin d))
    (S : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hmin : ∀ n, IsMinInv (G n) (lam n) (b n) (S n)) (hspd : ∀ n, IsSPD (S n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (b0 : EuclideanSpace ℝ (Fin d))
      (S0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
      Tendsto (b ∘ φ) atTop (𝓝 b0) ∧ Tendsto (S ∘ φ) atTop (𝓝 S0) ∧ IsSPD S0 ∧ IsMinInv G0 lam0 b0 S0 := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hcoer' : ∀ n x, a1 * ‖x‖ - max a2 0 ≤ G n x := fun n x =>
    le_trans (by linarith [le_max_left a2 0]) (hcoer n x)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hpt 0))
  have hB' : ∀ n, |G n 0| ≤ B := fun n => by simpa using hB _ (Set.mem_range_self n)
  set m1 := ∫ z, ‖z‖ ∂γ
  have hnorm_int : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) γ := IsGaussian.integrable_id.norm
  have hobj : ∀ n, ∫ z, G n (b n + S n z) ∂γ -
      lam n * Real.log |LinearMap.det (S n : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ≤
      B + L * m1 := by
    intro n
    have hid : LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = 1 := by
      rw [ContinuousLinearMap.coe_id, LinearMap.det_id]
    have h := (hmin n).2 0 (ContinuousLinearMap.id ℝ _) (by rw [hid]; exact one_ne_zero)
    rw [hid] at h
    simp only [abs_one, Real.log_one, mul_zero, sub_zero, zero_add, ContinuousLinearMap.id_apply] at h
    refine h.trans ?_
    have hle : ∀ z, G n z ≤ B + L * ‖z‖ := fun z => by
      have := (hL n).dist_le_mul z 0
      rw [Real.dist_eq, dist_zero_right] at this
      linarith [abs_le.1 this, abs_le.1 (hB' n)]
    calc ∫ z, G n z ∂γ ≤ ∫ z, (B + L * ‖z‖) ∂γ :=
          integral_mono (by simpa using integrable_lip (G n) L (hL n) 0 (ContinuousLinearMap.id ℝ _))
            ((integrable_const B).add (hnorm_int.const_mul _)) hle
      _ = B + L * m1 := by
          rw [integral_add (integrable_const B) (hnorm_int.const_mul _), integral_const, integral_const_mul,
            probReal_univ, one_smul]
  have hev : ∀ᶠ n in atTop, lam n ∈ Set.Icc (lam0 / 2) (2 * lam0) :=
    hlam.eventually (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨M, δ, hδ, hbd⟩ := uniform_bounds (d := d) a1 (max a2 0) lam0 (B + L * m1) ha (le_max_right _ _) hlam0
  have hbd' : ∀ n, N ≤ n → ‖b n‖ ≤ M ∧ ‖S n‖ ≤ M ∧
      δ ≤ |LinearMap.det (S n : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := fun n hn =>
    hbd (G n) L (hL n) (hcoer' n) (lam n) (hN n hn).1 (hN n hn).2 (b n) (S n) (hmin n).1 (hobj n)
  have hmem : ∀ n, (b (n + N), S (n + N)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) M := by
    intro n
    obtain ⟨h1, h2, -⟩ := hbd' (n + N) (Nat.le_add_left N n)
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le h1 h2
  obtain ⟨p0, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  set φ : ℕ → ℕ := fun n => ψ n + N with hφdef
  have hφ : StrictMono φ := fun m n hmn => by simp only [hφdef]; exact Nat.add_lt_add_right (hψ hmn) N
  have hφN : ∀ n, N ≤ φ n := fun n => Nat.le_add_left N (ψ n)
  have hblim : Tendsto (b ∘ φ) atTop (𝓝 p0.1) := (continuous_fst.tendsto p0).comp hlim
  have hSlim : Tendsto (S ∘ φ) atTop (𝓝 p0.2) := (continuous_snd.tendsto p0).comp hlim
  have hdetlim : Tendsto (fun n => LinearMap.det (S (φ n) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d))) atTop
      (𝓝 (LinearMap.det (p0.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))) :=
    (AdversarialBco.Body.continuous_det_clm.tendsto p0.2).comp hSlim
  have hdet0 : δ ≤ |LinearMap.det (p0.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| :=
    ge_of_tendsto hdetlim.abs (Eventually.of_forall fun n => (hbd' (φ n) (hφN n)).2.2)
  have hdet0' : LinearMap.det (p0.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 :=
    abs_pos.1 (lt_of_lt_of_le hδ hdet0)
  have hspd0 : IsSPD p0.2 := isSPD_of_tendsto (S ∘ φ) p0.2 hSlim (fun n => hspd _) hdet0'
  refine ⟨φ, hφ, p0.1, p0.2, hblim, hSlim, hspd0, hdet0', fun b' S' hS' => ?_⟩
  have hG' : ∀ n, Continuous (G (φ n)) := fun n => (hL _).continuous
  have hptφ : ∀ y, Tendsto (fun n => G (φ n) y) atTop (𝓝 (G0 y)) := fun y => (hpt y).comp hφ.tendsto_atTop
  have hconv := fun (y : ℕ → EuclideanSpace ℝ (Fin d)) y0 (hy : Tendsto y atTop (𝓝 y0)) =>
    tendsto_of_lipschitz (fun n => G (φ n)) G0 L (fun n => hL _) hptφ y y0 hy
  have hgrowth : ∀ n y, |G (φ n) y| ≤ (B + L) * (1 + ‖y‖ ^ 2) := fun n y => lip_growth _ L (hL _) B (hB' _) y
  have hI := tendsto_integral_cloud (fun n => G (φ n)) G0 (b ∘ φ) (S ∘ φ) p0.1 p0.2 hblim hSlim hG' hconv
    (B + L) hgrowth
  have hI' := tendsto_integral_cloud (fun n => G (φ n)) G0 (fun _ => b') (fun _ => S') b' S'
    tendsto_const_nhds tendsto_const_nhds hG' hconv (B + L) hgrowth
  have hlamφ : Tendsto (lam ∘ φ) atTop (𝓝 lam0) := hlam.comp hφ.tendsto_atTop
  have hlog : Tendsto (fun n => Real.log |LinearMap.det (S (φ n) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d))|) atTop
      (𝓝 (Real.log |LinearMap.det (p0.2 : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|)) :=
    ((Real.continuousAt_log (abs_ne_zero.2 hdet0')).tendsto).comp hdetlim.abs
  exact le_of_tendsto_of_tendsto' (hI.sub (hlamφ.mul hlog)) (hI'.sub (hlamφ.mul tendsto_const_nhds))
    (fun n => (hmin (φ n)).2 b' S' hS')

/-! ## E. The approximating regular families (Lemma D.5) -/

open AdversarialBco.Body2 AdversarialBco.BodySpec Filter ProbabilityTheory Topology in
open scoped RealInnerProductSpace NNReal in
theorem exists_min_of_coercive {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (a a' : ℝ)
    (ha : 0 < a) (hcoer : ∀ x, a * ‖x‖ - a' ≤ f x) : ∃ x0, ∀ y, f x0 ≤ f y := by
  let S : Set (EuclideanSpace ℝ (Fin d)) := {x | f x ≤ f 0}
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [S]
    exact le_refl (f 0)
  have hS_closed : IsClosed S :=
    isClosed_le hf continuous_const
  have hS_bounded : Bornology.IsBounded S := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(f 0 + a') / a, ?_⟩
    intro x hx
    have hxS : f x ≤ f 0 := hx
    have hbound : a * ‖x‖ - a' ≤ f x := hcoer x
    have hineq : a * ‖x‖ ≤ f 0 + a' := by linarith
    have hnorm : ‖x‖ ≤ (f 0 + a') / a := by
      calc
        ‖x‖ = (a * ‖x‖) / a := by field_simp [ha.ne.symm]
        _ ≤ (f 0 + a') / a := by gcongr
    exact hnorm
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have h_cont_on : ContinuousOn f S :=
    hf.continuousOn
  obtain ⟨x0, hx0S, hx0_min⟩ :=
    hS_compact.exists_isMinOn hS_nonempty h_cont_on
  refine ⟨x0, ?_⟩
  intro y
  by_cases hyS : y ∈ S
  · exact hx0_min hyS
  · have hy_not : ¬ (f y ≤ f 0) := hyS
    have hfx0_le_f0 : f x0 ≤ f 0 := hx0S
    linarith

theorem mean_approx {d k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (F Fk : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (bstar : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (h : ∀ c x, |Fk c x - (F c x + ε * ‖x - bstar‖)| ≤ ε ^ 2) (x : EuclideanSpace ℝ (Fin d)) :
    |mean w Fk x - (mean w F x + ε * ‖x - bstar‖)| ≤ ε ^ 2 := by
  unfold mean
  have e : ∑ c, w c * Fk c x - (∑ c, w c * F c x + ε * ‖x - bstar‖) =
      ∑ c, w c * (Fk c x - (F c x + ε * ‖x - bstar‖)) := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
  rw [e]
  calc |∑ c, w c * (Fk c x - (F c x + ε * ‖x - bstar‖))| ≤
        ∑ c, |w c * (Fk c x - (F c x + ε * ‖x - bstar‖))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, w c * ε ^ 2 := Finset.sum_le_sum fun c _ => by
        rw [abs_mul, abs_of_nonneg (hw c)]; exact mul_le_mul_of_nonneg_left (h c x) (hw c)
    _ = ε ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]

open AdversarialBco.Body2 AdversarialBco.BodySpec Filter ProbabilityTheory Topology in
open scoped RealInnerProductSpace NNReal in
theorem argmin_close {d : ℕ} (G Gk : EuclideanSpace ℝ (Fin d) → ℝ) (bstar bk : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (hε : 0 < ε) (h : ∀ x, |Gk x - (G x + ε * ‖x - bstar‖)| ≤ ε ^ 2) (hb : ∀ y, G bstar ≤ G y)
    (hbk : ∀ y, Gk bk ≤ Gk y) : ‖bk - bstar‖ ≤ 2 * ε := by
  have hbk_bound := h bk
  have hbstar_bound := h bstar
  have hbstar_norm : ‖bstar - bstar‖ = 0 := by simp
  have h_gk_bstar_le : Gk bstar ≤ G bstar + ε ^ 2 := by
    have h_abs := abs_le.mp hbstar_bound
    rcases h_abs with ⟨h_low, h_high⟩
    rw [hbstar_norm] at h_high
    linarith
  have h_gk_bk_ge : G bk + ε * ‖bk - bstar‖ - ε ^ 2 ≤ Gk bk := by
    have h_abs := abs_le.mp hbk_bound
    rcases h_abs with ⟨h_low, h_high⟩
    linarith
  have h_chain : G bk + ε * ‖bk - bstar‖ - ε ^ 2 ≤ G bstar + ε ^ 2 := by
    have h_gk_bk_le_gk_bstar : Gk bk ≤ Gk bstar := hbk bstar
    linarith
  have h_ineq : ε * ‖bk - bstar‖ ≤ 2 * ε ^ 2 := by
    have h_gbk_le_gbstar : G bstar ≤ G bk := hb bk
    linarith
  have h_eq : 2 * ε ^ 2 = ε * (2 * ε) := by ring
  rw [h_eq] at h_ineq
  exact le_of_mul_le_mul_left h_ineq hε

theorem min_close {d : ℕ} (G Gk : EuclideanSpace ℝ (Fin d) → ℝ) (bstar x0 xk : EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ∀ x, |Gk x - (G x + ε * ‖x - bstar‖)| ≤ ε ^ 2) (hx0 : ∀ y, G x0 ≤ G y)
    (hxk : ∀ y, Gk xk ≤ Gk y) : |Gk xk - G x0| ≤ ε * ‖x0 - bstar‖ + ε ^ 2 := by
  have h1 := abs_le.1 (h xk)
  have h2 := abs_le.1 (h x0)
  have h3 := hxk x0
  have h4 := hx0 xk
  have h5 : 0 ≤ ε * ‖xk - bstar‖ := mul_nonneg hε (norm_nonneg _)
  have h6 : 0 ≤ ε * ‖x0 - bstar‖ := mul_nonneg hε (norm_nonneg _)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem tendsto_ciSup_fin {k : ℕ} (f : ℕ → Fin k → ℝ) (g : Fin k → ℝ)
    (h : ∀ c, Tendsto (fun n => f n c) atTop (𝓝 (g c))) :
    Tendsto (fun n => ⨆ c, f n c) atTop (𝓝 (⨆ c, g c)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Real.iSup_of_isEmpty]
    exact tendsto_const_nhds
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have := Filter.Tendsto.finset_sup'_nhds_apply (s := Finset.univ) Finset.univ_nonempty
      (f := fun c n => f n c) (fun c _ => h c)
    simpa only [Finset.sup'_univ_eq_ciSup] using this

theorem continuous_lnp : Continuous lnp := by
  have e : lnp = fun x => Real.log (max |x| 1) := by
    funext x
    unfold lnp
    rcases le_total 1 |x| with h | h
    · rw [max_eq_left h, ← Real.log_abs, max_eq_left (Real.log_nonneg h)]
    · rw [max_eq_right h, Real.log_one, ← Real.log_abs]
      exact max_eq_right (Real.log_nonpos (abs_nonneg x) h)
  rw [e]
  exact (continuous_abs.max continuous_const).log fun x => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

theorem KS_pos : 0 < KS := by
  obtain ⟨h1, -, h3, -⟩ := AdversarialBco.Body2.kappa_bounds
  have hk : 0 < kappa := by linarith
  have hk2 : 0 < 13 / 4 + 2 * kappa2 := by linarith
  unfold KS
  exact mul_pos (mul_pos two_pos (pow_pos (div_pos (by norm_num) hk) 2)) hk2

theorem dist_term {d : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (b : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin d) => ε * ‖x - b‖) ∧
      LipschitzWith (Real.toNNReal ε) (fun x : EuclideanSpace ℝ (Fin d) => ε * ‖x - b‖) := by
  constructor
  · refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
    simp only [smul_eq_mul]
    have e : a • x + c • y - b = a • (x - b) + c • (y - b) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hac, one_smul]
    rw [e]
    calc ε * ‖a • (x - b) + c • (y - b)‖ ≤ ε * (a * ‖x - b‖ + c * ‖y - b‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) hε
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
      _ = a * (ε * ‖x - b‖) + c * (ε * ‖y - b‖) := by ring
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.coe_toNNReal ε hε, ← mul_sub, abs_mul, abs_of_nonneg hε, dist_eq_norm]
    refine mul_le_mul_of_nonneg_left ?_ hε
    calc |‖x - b‖ - ‖y - b‖| ≤ ‖(x - b) - (y - b)‖ := abs_norm_sub_norm_le _ _
      _ = ‖x - y‖ := by rw [sub_sub_sub_cancel_right]

theorem tendsto_approx {d : ℕ} (Fn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (F0 : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF0 : Continuous F0) (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0)) (bstar : EuclideanSpace ℝ (Fin d))
    (h : ∀ n x, |Fn n x - (F0 x + eps n * ‖x - bstar‖)| ≤ eps n ^ 2) (y : ℕ → EuclideanSpace ℝ (Fin d))
    (y0 : EuclideanSpace ℝ (Fin d)) (hy : Tendsto y atTop (𝓝 y0)) :
    Tendsto (fun n => Fn n (y n)) atTop (𝓝 (F0 y0)) := by
  have h1 : Tendsto (fun n => Fn n (y n) - (F0 (y n) + eps n * ‖y n - bstar‖)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (Real.norm_eq_abs _).le.trans (h n (y n))) (by simpa using heps.pow 2)
  have h2 : Tendsto (fun n => F0 (y n) + eps n * ‖y n - bstar‖) atTop (𝓝 (F0 y0 + 0 * ‖y0 - bstar‖)) :=
    ((hF0.tendsto y0).comp hy).add (heps.mul (hy.sub_const bstar).norm)
  rw [zero_mul, add_zero] at h2
  simpa using h1.add h2

theorem exists_const_subseq {k : ℕ} (f : ℕ → Fin k) :
    ∃ (c0 : Fin k) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ m, f (φ m) = c0 := by
  obtain ⟨c0, hc0⟩ := Finite.exists_infinite_fiber f
  have hinf : {n | f n = c0}.Infinite := Set.infinite_coe_iff.1 hc0
  exact ⟨c0, Nat.nth (fun n => f n = c0), Nat.nth_strictMono hinf, fun m => Nat.nth_mem_of_infinite hinf m⟩

theorem mean_lipschitz {d k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (hF : ∀ c, LipschitzWith K (F c)) :
    LipschitzWith K (mean w F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  unfold mean
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ c, (w c * F c x - w c * F c y)| ≤ ∑ c, |w c * F c x - w c * F c y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, w c * |F c x - F c y| := by
        congr 1; ext c; rw [← mul_sub, abs_mul, abs_of_nonneg (hw c)]
    _ ≤ ∑ c, w c * (K * dist x y) := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (by rw [← Real.dist_eq]; exact (hF c).dist_le_mul x y) (hw c)
    _ = K * dist x y := by rw [← Finset.sum_mul, hw1, one_mul]

theorem var_growth {d k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (hF : ∀ c, LipschitzWith K (F c)) (B : ℝ)
    (hB : ∀ c, |F c 0 - mean w F 0| ≤ B) (x : EuclideanSpace ℝ (Fin d)) :
    |var w F x| ≤ (2 * B ^ 2 + 8 * (K : ℝ) ^ 2) * (1 + ‖x‖ ^ 2) := by
  have hm := mean_lipschitz w hw hw1 F K hF
  have hsq : ∀ c, (F c x - mean w F x) ^ 2 ≤ (2 * B ^ 2 + 8 * (K : ℝ) ^ 2) * (1 + ‖x‖ ^ 2) := by
    intro c
    have h1 : |F c x - F c 0| ≤ K * ‖x‖ := by
      have := (hF c).dist_le_mul x 0
      rwa [Real.dist_eq, dist_zero_right] at this
    have h2 : |mean w F x - mean w F 0| ≤ K * ‖x‖ := by
      have := hm.dist_le_mul x 0
      rwa [Real.dist_eq, dist_zero_right] at this
    have h3 := hB c
    have e : F c x - mean w F x = (F c 0 - mean w F 0) + ((F c x - F c 0) - (mean w F x - mean w F 0)) := by ring
    have hv : |(F c x - F c 0) - (mean w F x - mean w F 0)| ≤ 2 * K * ‖x‖ := by
      calc _ ≤ |F c x - F c 0| + |mean w F x - mean w F 0| := abs_sub _ _
        _ ≤ 2 * K * ‖x‖ := by linarith
    rw [e]
    set u := F c 0 - mean w F 0
    set v := (F c x - F c 0) - (mean w F x - mean w F 0)
    have hu2 : u ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hv2 : v ^ 2 ≤ (2 * K * ‖x‖) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    nlinarith [sq_nonneg (u - v), mul_nonneg (sq_nonneg B) (sq_nonneg ‖x‖), sq_nonneg (K : ℝ)]
  have hv0 : 0 ≤ var w F x := by
    unfold var
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (sq_nonneg _)
  rw [abs_of_nonneg hv0]
  unfold var
  calc ∑ c, w c * (F c x - mean w F x) ^ 2 ≤
        ∑ c, w c * ((2 * B ^ 2 + 8 * (K : ℝ) ^ 2) * (1 + ‖x‖ ^ 2)) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hsq c) (hw c)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

theorem gmax_ge {k : ℕ} (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (g : Fin k → ℝ) :
    ∑ c, w c * g c ≤ ⨆ c, g c := by
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · simp at hw1
  · calc ∑ c, w c * g c ≤ ∑ c, w c * ⨆ c', g c' := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (le_ciSup (Finite.bddAbove_range g) c) (hw c)
      _ = ⨆ c, g c := by rw [← Finset.sum_mul, hw1, one_mul]

theorem p3_to_scale (d T ℓ h Δs Vs Vb VG : ℝ) (hd : 1 ≤ d) (hT : 0 ≤ T) (hℓ : 0 < ℓ) (hh : 0 < h)
    (hKS : 0 < KS) (hP3 : h * Δs / (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ) ≤ Vs + Vb + VG) :
    Δs / (2 * ℓ) ≤ h * (Δs / (2 * ℓ * h)) ∧
      Δs / (2 * ℓ * h) * h ^ 2 ≤ KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
  have hd0 : 0 < d := by linarith
  have hT1 : 0 < 1 + T := by linarith
  have hC : 0 < KS * (1 + T) ^ 2 * d ^ 2 := by positivity
  have hhne := hh.ne'
  have hℓne := hℓ.ne'
  have hKSne := hKS.ne'
  have hT1ne := hT1.ne'
  have hd0ne := hd0.ne'
  refine ⟨le_of_eq (by field_simp), ?_⟩
  have e : Δs / (2 * ℓ * h) * h ^ 2 =
      KS * (1 + T) ^ 2 * d ^ 2 * (h * Δs / (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ)) := by
    field_simp
  rw [e]
  calc _ ≤ KS * (1 + T) ^ 2 * d ^ 2 * (Vs + Vb + VG) := mul_le_mul_of_nonneg_left hP3 hC.le
    _ = _ := by ring

theorem dil_integrals {d k : ℕ} (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hF : ∀ c, LipschitzWith L (F c)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (bstar b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ x, mean w F x ∂(dilutedLaw q bstar b S) = (1 - q) * mean w F bstar + q / 2 * mean w F b +
        q / 2 * ∫ z, mean w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, var w F x ∂(dilutedLaw q bstar b S) = (1 - q) * var w F bstar + q / 2 * var w F b +
        q / 2 * ∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hprob : IsProbabilityMeasure (gaussLaw b S) := by
    unfold gaussLaw
    exact (Measure.isProbabilityMeasure_map_iff (continuous_const.add S.continuous).measurable.aemeasurable).2
      inferInstance
  have hint := AdversarialBco.Body.tr_integrable_cloud_var b S w F L hF
  have hm : Integrable (mean w F) (gaussLaw b S) := hint.1
  have hv : Integrable (var w F) (gaussLaw b S) := hint.2
  have hmeas : Measurable fun z : EuclideanSpace ℝ (Fin d) => b + S z :=
    (continuous_const.add S.continuous).measurable
  have e : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f (gaussLaw b S) →
      ∫ x, f x ∂(gaussLaw b S) = ∫ z, f (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    fun f hf => integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  unfold dilutedLaw
  rw [(AdversarialBco.Body.integral_diluted bstar b (gaussLaw b S) q hq0 hq1 _ hm).2.2, e _ hm,
    (AdversarialBco.Body.integral_diluted bstar b (gaussLaw b S) q hq0 hq1 _ hv).2.2, e _ hv]
  exact ⟨rfl, rfl⟩

theorem approx_family {d k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hFc : ∀ c, ConvexOn ℝ Set.univ (F c)) (hFL : ∀ c, LipschitzWith L (F c)) (bstar : EuclideanSpace ℝ (Fin d))
    (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n) :
    ∃ (Fk : ℕ → Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (Mp : ℕ → ℝ≥0), ∀ n c,
      ContDiff ℝ 2 (Fk n c) ∧ ConvexOn ℝ Set.univ (Fk n c) ∧ LipschitzWith (L + Real.toNNReal (eps n)) (Fk n c) ∧
      LipschitzWith (Mp n) (fderiv ℝ (Fk n c)) ∧ ∀ x, |Fk n c x - (F c x + eps n * ‖x - bstar‖)| ≤ eps n ^ 2 := by
  have h : ∀ n c, ∃ Fs : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 Fs ∧ ConvexOn ℝ Set.univ Fs ∧
      LipschitzWith (L + Real.toNNReal (eps n)) Fs ∧ (∃ M : ℝ≥0, LipschitzWith M (fderiv ℝ Fs)) ∧
      ∀ x, |Fs x - (F c x + eps n * ‖x - bstar‖)| ≤ eps n ^ 2 := by
    intro n c
    obtain ⟨hc, hl⟩ := dist_term (d := d) (eps n) (heps n).le bstar
    exact AdversarialBco.Body.smooth_convex (fun x => F c x + eps n * ‖x - bstar‖) (L + Real.toNNReal (eps n))
      ((hFL c).add hl) ((hFc c).add hc) (eps n ^ 2) (pow_pos (heps n) 2)
  choose Fk hFk using h
  choose M hM using fun n c => (hFk n c).2.2.2.1
  exact ⟨Fk, fun n => Finset.univ.sup (M n), fun n c => ⟨(hFk n c).1, (hFk n c).2.1, (hFk n c).2.2.1,
    (hM n c).weaken (Finset.le_sup (Finset.mem_univ c)), (hFk n c).2.2.2.2⟩⟩

/-! ## F. Theorem 3.1 for every family -/

theorem dilTheorem_of_reg (hreg : DilRegExplicit) (_hec : EcReg) : DilTheorem := by
  intro d hd k w F L xmin a1 a2 bstar hw hw1 hFc hFL hxmin ha1 hcoer hbstar hΔ
  have hw0 : ∀ c, 0 ≤ w c := fun c => (hw c).le
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have h16 : (0 : ℝ) < 16 * d := by linarith
  set eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hepsdef
  have heps : ∀ n, 0 < eps n := fun n => by simp only [hepsdef]; positivity
  have heps1 : ∀ n, eps n ≤ 1 := fun n => by
    simp only [hepsdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨Fk, Mp, hFk⟩ := approx_family F L hFc hFL bstar eps heps
  have hFkL : ∀ n c, LipschitzWith (L + 1) (Fk n c) := fun n c =>
    (hFk n c).2.2.1.weaken (add_le_add_right (Real.toNNReal_le_one.2 (heps1 n)) L)
  have happ : ∀ n c x, |Fk n c x - (F c x + eps n * ‖x - bstar‖)| ≤ eps n ^ 2 := fun n c => (hFk n c).2.2.2.2
  have happm : ∀ n x, |mean w (Fk n) x - (mean w F x + eps n * ‖x - bstar‖)| ≤ eps n ^ 2 :=
    fun n => mean_approx w hw0 hw1 F (Fk n) bstar (eps n) (happ n)
  have hmeanL : LipschitzWith L (mean w F) := mean_lipschitz w hw0 hw1 F L hFL
  have hmeanLk : ∀ n, LipschitzWith (L + 1) (mean w (Fk n)) := fun n => mean_lipschitz w hw0 hw1 (Fk n) _ (hFkL n)
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ ‖x - bstar‖ + ‖bstar‖ := fun x => by
    have := norm_add_le (x - bstar) bstar
    rwa [sub_add_cancel] at this
  -- minimisers of the members and of the means
  have hxk : ∀ n c, ∃ x0, ∀ y, Fk n c x0 ≤ Fk n c y := by
    intro n c
    refine exists_min_of_coercive _ (hFkL n c).continuous (eps n) (eps n * ‖bstar‖ + eps n ^ 2 - F c (xmin c))
      (heps n) fun x => ?_
    have h1 := (abs_le.1 (happ n c x)).1
    have h2 := hxmin c x
    have h3 : eps n * ‖x‖ ≤ eps n * ‖x - bstar‖ + eps n * ‖bstar‖ := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hnorm x) (heps n).le
    linarith
  choose xk hxk using hxk
  have hcoerk : ∀ n x, a1 * ‖x‖ - (a2 + 1) ≤ mean w (Fk n) x := by
    intro n x
    have h1 := (abs_le.1 (happm n x)).1
    have h2 := hcoer x
    have h3 : 0 ≤ eps n * ‖x - bstar‖ := mul_nonneg (heps n).le (norm_nonneg _)
    have h4 : eps n ^ 2 ≤ 1 := pow_le_one₀ (heps n).le (heps1 n)
    linarith
  have hbk : ∀ n, ∃ b0, ∀ y, mean w (Fk n) b0 ≤ mean w (Fk n) y := fun n =>
    exists_min_of_coercive _ (hmeanLk n).continuous a1 (a2 + 1) ha1 (hcoerk n)
  choose bk hbk using hbk
  -- convergence of the minimisers, the minima, the gains and the floor
  have hbk_lim : Tendsto bk atTop (𝓝 bstar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => argmin_close (mean w F) (mean w (Fk n)) bstar (bk n)
      (eps n) (heps n) (happm n) hbstar (hbk n)) ?_
    simpa using heps0.const_mul 2
  have hconvF : ∀ (ι : ℕ → ℕ), Tendsto ι atTop atTop → ∀ c (y : ℕ → EuclideanSpace ℝ (Fin d)) y0,
      Tendsto y atTop (𝓝 y0) → Tendsto (fun n => Fk (ι n) c (y n)) atTop (𝓝 (F c y0)) :=
    fun ι hι c y y0 hy => tendsto_approx (fun n => Fk (ι n) c) (F c) (hFL c).continuous (eps ∘ ι) (heps0.comp hι)
      bstar (fun n x => happ (ι n) c x) y y0 hy
  have hconvM : ∀ (ι : ℕ → ℕ), Tendsto ι atTop atTop → ∀ (y : ℕ → EuclideanSpace ℝ (Fin d)) y0,
      Tendsto y atTop (𝓝 y0) → Tendsto (fun n => mean w (Fk (ι n)) (y n)) atTop (𝓝 (mean w F y0)) :=
    fun ι hι y y0 hy => tendsto_approx (fun n => mean w (Fk (ι n))) (mean w F) hmeanL.continuous (eps ∘ ι)
      (heps0.comp hι) bstar (fun n x => happm (ι n) x) y y0 hy
  have hconvV : ∀ (ι : ℕ → ℕ), Tendsto ι atTop atTop → ∀ (y : ℕ → EuclideanSpace ℝ (Fin d)) y0,
      Tendsto y atTop (𝓝 y0) → Tendsto (fun n => var w (Fk (ι n)) (y n)) atTop (𝓝 (var w F y0)) := by
    intro ι hι y y0 hy
    exact tendsto_finsetSum _ fun c _ =>
      (((hconvF ι hι c y y0 hy).sub (hconvM ι hι y y0 hy)).pow 2).const_mul (w c)
  have hmin_lim : ∀ c, Tendsto (fun n => Fk n c (xk n c)) atTop (𝓝 (F c (xmin c))) := by
    intro c
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => eps n * ‖xmin c - bstar‖ + eps n ^ 2) (fun n => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]
      exact min_close (F c) (Fk n c) bstar (xmin c) (xk n c) (eps n) (heps n).le (happ n c) (hxmin c) (hxk n c)) ?_
    simpa using (heps0.mul_const ‖xmin c - bstar‖).add (heps0.pow 2)
  set gk : ℕ → Fin k → ℝ := fun n c => Fk n c (bk n) - Fk n c (xk n c) with hgkdef
  set Δk : ℕ → ℝ := fun n => mean w (Fk n) (bk n) - ∑ c, w c * Fk n c (xk n c) with hΔkdef
  have hgk : ∀ c, Tendsto (fun n => gk n c) atTop (𝓝 (F c bstar - F c (xmin c))) := fun c =>
    (hconvF id tendsto_id c bk bstar hbk_lim).sub (hmin_lim c)
  have hΔk : Tendsto Δk atTop (𝓝 (mean w F bstar - ∑ c, w c * F c (xmin c))) :=
    (hconvM id tendsto_id bk bstar hbk_lim).sub (tendsto_finsetSum _ fun c _ => (hmin_lim c).const_mul (w c))
  have hgmax : Tendsto (fun n => ⨆ c, gk n c) atTop (𝓝 (⨆ c, (F c bstar - F c (xmin c)))) :=
    tendsto_ciSup_fin gk _ hgk
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hΔk.eventually (lt_mem_nhds hΔ))
  -- the regular case at every index `n + N`
  have hR : ∀ n, ∃ h : ℝ, Δk (n + N) / 2 ≤ h ∧ h ≤ (⨆ c, gk (n + N) c) ∧ (∃ c, h = gk (n + N) c) ∧
      ∃ (b : EuclideanSpace ℝ (Fin d)) (P : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        IsSPD P ∧ IsMinInv (mean w (Fk (n + N))) (h / (16 * d)) b P ∧
        (∀ y, ∫ z, mean w (Fk (n + N)) (b + P z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
          mean w (Fk (n + N)) y + h / (16 * d) * d) ∧
        h * Δk (n + N) / (2 * KS * (1 + Real.sqrt (2 * lnp (26 * d * ((L + Real.toNNReal (eps (n + N)) : ℝ≥0) : ℝ) *
            ‖P‖ / h))) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * (⨆ c, gk (n + N) c) / Δk (n + N))) ≤
          var w (Fk (n + N)) (bk (n + N)) + var w (Fk (n + N)) b +
            ∫ z, var w (Fk (n + N)) (b + P z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro n
    obtain ⟨h, h1, h2, h3, ⟨b, S, hbS⟩, h5⟩ := hreg d hd k w (Fk (n + N)) (L + Real.toNNReal (eps (n + N)))
      (Mp (n + N)) (xk (n + N)) a1 (a2 + 1) (bk (n + N)) hw0 hw1 (fun c => (hFk _ c).1) (fun c => (hFk _ c).2.1)
      (fun c => (hFk _ c).2.2.1) (fun c => (hFk _ c).2.2.2.1) (hxk (n + N)) ha1 (hcoerk _) (hbk _)
      (hN _ (Nat.le_add_left N n))
    obtain ⟨P, hP, hbP⟩ := isMinInv_spd _ (hmeanLk _).continuous _ b S hbS
    obtain ⟨-, hS3, hP3⟩ := h5 b P hbP
    exact ⟨h, h1, h2, h3, b, P, hP, hbP, hS3, hP3⟩
  choose hs hs1 hs2 hs3 bs Ps hPs hbPs hS3s hP3s using hR
  choose cs hcs using hs3
  -- one gain along a subsequence, then the limit of the Gaussians
  obtain ⟨c0, φ1, hφ1, hc0⟩ := exists_const_subseq cs
  set ι1 : ℕ → ℕ := fun m => φ1 m + N with hι1def
  have hι1 : Tendsto ι1 atTop atTop := (tendsto_add_atTop_nat N).comp hφ1.tendsto_atTop
  set h := F c0 bstar - F c0 (xmin c0) with hhdef
  have hh_lim : Tendsto (fun m => hs (φ1 m)) atTop (𝓝 h) := by
    have : (fun m => hs (φ1 m)) = fun m => gk (ι1 m) c0 := funext fun m => by rw [hcs (φ1 m), hc0 m]
    rw [this]; exact (hgk c0).comp hι1
  have hh1 : (mean w F bstar - ∑ c, w c * F c (xmin c)) / 2 ≤ h :=
    le_of_tendsto_of_tendsto' ((hΔk.comp hι1).div_const 2) hh_lim (fun m => hs1 (φ1 m))
  have hh2 : h ≤ ⨆ c, (F c bstar - F c (xmin c)) :=
    le_of_tendsto_of_tendsto' hh_lim (hgmax.comp hι1) (fun m => hs2 (φ1 m))
  have hhpos : 0 < h := by linarith
  have hlam0 : 0 < h / (16 * d) := div_pos hhpos h16
  obtain ⟨φ2, hφ2, b0, S0, hb0, hS0, hspd0, hmin0⟩ := limit_isMinInv (fun m => mean w (Fk (ι1 m))) (mean w F)
    (L + 1) (fun m => hmeanLk _) (fun y => hconvM ι1 hι1 (fun _ => y) y tendsto_const_nhds) a1 (a2 + 1) ha1
    (fun m => hcoerk _) (fun m => hs (φ1 m) / (16 * d)) (h / (16 * d)) hlam0 (hh_lim.div_const _)
    (fun m => bs (φ1 m)) (fun m => Ps (φ1 m)) (fun m => hbPs (φ1 m)) (fun m => hPs (φ1 m))
  set ι : ℕ → ℕ := fun n => ι1 (φ2 n) with hιdef
  have hι : Tendsto ι atTop atTop := hι1.comp hφ2.tendsto_atTop
  have hbn : Tendsto (fun n => bs (φ1 (φ2 n))) atTop (𝓝 b0) := hb0
  have hSn : Tendsto (fun n => Ps (φ1 (φ2 n))) atTop (𝓝 S0) := hS0
  have hhn : Tendsto (fun n => hs (φ1 (φ2 n))) atTop (𝓝 h) := hh_lim.comp hφ2.tendsto_atTop
  -- growth bounds
  obtain ⟨Bm, hBm⟩ := isBounded_iff_forall_norm_le.1
    (Metric.isBounded_range_of_tendsto _ (hconvM id tendsto_id (fun _ => 0) 0 tendsto_const_nhds))
  have hBm' : ∀ n, |mean w (Fk n) 0| ≤ Bm := fun n => by simpa using hBm _ (Set.mem_range_self n)
  have hBc : ∀ c, ∃ B, ∀ n, |Fk n c 0 - mean w (Fk n) 0| ≤ B := fun c => by
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _
      ((hconvF id tendsto_id c (fun _ => 0) 0 tendsto_const_nhds).sub
        (hconvM id tendsto_id (fun _ => 0) 0 tendsto_const_nhds)))
    exact ⟨B, fun n => by simpa using hB _ (Set.mem_range_self n)⟩
  choose Bc hBc using hBc
  have hBv : ∀ n c, |Fk n c 0 - mean w (Fk n) 0| ≤ ∑ c, |Bc c| := fun n c =>
    (hBc c n).trans ((le_abs_self _).trans (Finset.single_le_sum (fun c _ => abs_nonneg (Bc c)) (Finset.mem_univ c)))
  have hvarc : ∀ n, Continuous (var w (Fk n)) := fun n => by
    have hc : ∀ c, Continuous (Fk n c) := fun c => (hFkL n c).continuous
    exact continuous_finsetSum _ fun c _ => continuous_const.mul
      (((hc c).sub (continuous_finsetSum _ fun c' _ => continuous_const.mul (hc c'))).pow 2)
  -- (S3) in the limit
  have hS3lim : ∀ y, ∫ z, mean w F (b0 + S0 z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      mean w F y + h / (16 * d) * d := by
    intro y
    have hI := tendsto_integral_cloud (fun n => mean w (Fk (ι n))) (mean w F) (fun n => bs (φ1 (φ2 n)))
      (fun n => Ps (φ1 (φ2 n))) b0 S0 hbn hSn (fun n => (hmeanLk _).continuous) (hconvM ι hι)
      (Bm + ((L + 1 : ℝ≥0) : ℝ)) (fun n y => lip_growth _ (L + 1) (hmeanLk _) Bm (hBm' _) y)
    have hRy := (hconvM ι hι (fun _ => y) y tendsto_const_nhds).add ((hhn.div_const (16 * d)).mul_const (d : ℝ))
    exact le_of_tendsto_of_tendsto' hI hRy (fun n => hS3s (φ1 (φ2 n)) y)
  -- (P3) in the limit
  set Δs := mean w F bstar - ∑ c, w c * F c (xmin c) with hΔsdef
  set gmax := ⨆ c, (F c bstar - F c (xmin c)) with hgmaxdef
  have hgmax_ge : Δs ≤ gmax := by
    have e : Δs = ∑ c, w c * (F c bstar - F c (xmin c)) := by
      simp only [hΔsdef, mean, mul_sub, Finset.sum_sub_distrib]
    rw [e]; exact gmax_ge w hw0 hw1 (fun c => F c bstar - F c (xmin c))
  have h2g : 0 < 2 * gmax / Δs := div_pos (by linarith) hΔ
  have hlogpos : 0 < Real.log (2 * gmax / Δs) := Real.log_pos (by rw [lt_div_iff₀ hΔ]; linarith)
  have hKS := KS_pos
  set T := Real.sqrt (2 * lnp (26 * d * (L : ℝ) * ‖S0‖ / h)) with hTdef
  have hLn : Tendsto (fun n => ((L + Real.toNNReal (eps (ι n)) : ℝ≥0) : ℝ)) atTop (𝓝 (L : ℝ)) := by
    have : Tendsto (fun n => (L : ℝ) + eps (ι n)) atTop (𝓝 ((L : ℝ) + 0)) :=
      tendsto_const_nhds.add (heps0.comp hι)
    rw [add_zero] at this
    refine this.congr fun n => ?_
    rw [NNReal.coe_add, Real.coe_toNNReal _ (heps _).le]
  have hTn : Tendsto (fun n => Real.sqrt (2 * lnp (26 * d * ((L + Real.toNNReal (eps (ι n)) : ℝ≥0) : ℝ) *
      ‖Ps (φ1 (φ2 n))‖ / hs (φ1 (φ2 n))))) atTop (𝓝 T) :=
    (Real.continuous_sqrt.tendsto _).comp (((continuous_lnp.tendsto _).comp
      (((tendsto_const_nhds.mul hLn).mul hSn.norm).div hhn hhpos.ne')).const_mul 2)
  have hden : 2 * KS * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs) ≠ 0 := by
    have : 0 < 1 + T := by positivity
    positivity
  have hLHS : Tendsto (fun n => hs (φ1 (φ2 n)) * Δk (ι n) / (2 * KS * (1 + Real.sqrt (2 * lnp (26 * d *
      ((L + Real.toNNReal (eps (ι n)) : ℝ≥0) : ℝ) * ‖Ps (φ1 (φ2 n))‖ / hs (φ1 (φ2 n))))) ^ 2 * (d : ℝ) ^ 2 *
      Real.log (2 * (⨆ c, gk (ι n) c) / Δk (ι n)))) atTop
      (𝓝 (h * Δs / (2 * KS * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs)))) :=
    (hhn.mul (hΔk.comp hι)).div ((((tendsto_const_nhds.mul ((tendsto_const_nhds.add hTn).pow 2)).mul
      tendsto_const_nhds).mul ((Real.continuousAt_log h2g.ne').tendsto.comp
      ((tendsto_const_nhds.mul (hgmax.comp hι)).div (hΔk.comp hι) hΔ.ne')))) hden
  have hRHS : Tendsto (fun n => var w (Fk (ι n)) (bk (ι n)) + var w (Fk (ι n)) (bs (φ1 (φ2 n))) +
      ∫ z, var w (Fk (ι n)) (bs (φ1 (φ2 n)) + Ps (φ1 (φ2 n)) z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) atTop
      (𝓝 (var w F bstar + var w F b0 + ∫ z, var w F (b0 + S0 z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) :=
    ((hconvV ι hι _ _ (hbk_lim.comp hι)).add (hconvV ι hι _ _ hbn)).add
      (tendsto_integral_cloud (fun n => var w (Fk (ι n))) (var w F) _ _ b0 S0 hbn hSn (fun n => hvarc _)
        (hconvV ι hι) _ (fun n y => var_growth w hw0 hw1 (Fk (ι n)) (L + 1) (hFkL _) _ (fun c => hBv _ c) y))
  have hP3lim := le_of_tendsto_of_tendsto' hLHS hRHS (fun n => hP3s (φ1 (φ2 n)))
  -- every entropic Gaussian is the limit one
  have hEG0 : IsEntropicGaussian (mean w F) (h / (16 * d)) b0 S0 :=
    isEntropicGaussian_of_isMinInv _ _ _ _ hspd0 hmin0
  have hconv : ConvexOn ℝ Set.univ (mean w F) := AdversarialBco.Body.convexOn_wsum w hw0 F hFc
  refine ⟨h, hh1, hh2, ⟨c0, rfl⟩, ⟨b0, S0, hEG0⟩, fun b S hbS => ?_⟩
  obtain ⟨rfl, rfl⟩ := entropic_unique (mean w F) hconv L hmeanL a1 a2 ha1 hcoer (h / (16 * d)) hlam0 b b0 S S0
    hbS hEG0
  intro Δs' gmax' T' p Δp
  have hq0 : 0 ≤ Δs / (4 * h) := div_nonneg hΔ.le (by linarith)
  have hq1 : Δs / (4 * h) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  obtain ⟨hpm, hpv⟩ := dil_integrals w F L hFL (Δs / (4 * h)) hq0 hq1 bstar b S
  have hS4 := AdversarialBco.Body.ec_S4 (mean w F) hconv L hmeanL b S
  have hdelta := delta_arith (mean w F bstar) (mean w F b) (∫ z, mean w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
    (∑ c, w c * F c (xmin c)) h d hdR hhpos hΔ hh1 (hbstar b) hS4 (hS3lim bstar)
  have hΔp_eq : Δp = (1 - Δs / (4 * h)) * mean w F bstar + Δs / (4 * h) / 2 * mean w F b +
      Δs / (4 * h) / 2 * ∫ z, mean w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
      ∑ c, w c * F c (xmin c) := by
    show ∫ x, mean w F x ∂(dilutedLaw (Δs / (4 * h)) bstar b S) - _ = _
    rw [hpm]
  have hVs : 0 ≤ var w F bstar := Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (sq_nonneg _)
  have hVb : 0 ≤ var w F b := Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (sq_nonneg _)
  have hVG : 0 ≤ ∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    integral_nonneg fun z => Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (sq_nonneg _)
  obtain ⟨hΛ, hscale⟩ := p3_to_scale d T (Real.log (2 * gmax / Δs)) h Δs (var w F bstar) (var w F b)
    (∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) hdR (Real.sqrt_nonneg _) hlogpos hhpos hKS
    hP3lim
  have hΔp0 : 0 ≤ Δp := by rw [hΔp_eq]; exact hdelta.1
  have hΔp1 : Δp ≤ 65 / 64 * Δs := by rw [hΔp_eq]; exact hdelta.2
  have hKD := (dil_arith2 d T (Real.log (2 * gmax / Δs)) h Δs Δp _ (var w F bstar) (var w F b)
    (∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) hdR (Real.sqrt_nonneg _) hlogpos hhpos hΔ hh1
    hΛ hscale hVs hVb hVG hΔp0 hΔp1).2
  refine ⟨hΔp1, hP3lim, ?_⟩
  show Δp ^ 2 ≤ KD * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs) *
    ∫ x, var w F x ∂(dilutedLaw (Δs / (4 * h)) bstar b S)
  rw [hpv]; exact hKD

end AdversarialBco.DilAll
