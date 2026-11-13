/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2R1

@[expose] public section

/-!
# DF2, the rank-one round lemma: proofs

Proofs of the interface statements `LemmaR1i` to `LemmaR1v` of `AdversarialBco/Poly/Df2R1.lean` (the paper's rank-one
round lemma), as
`lemmaR1i` to `lemmaR1v`.

The route: from `A Aᵀ = S` and `S P = 1`, `A (Aᵀ P) = 1`, so `A⁻¹ = Aᵀ P` and `Aᵀ P A = 1`; then `Aᵀ u = ξ` and the
congruence `Aᵀ P' A = a I + c ξ ξᵀ` (`r1_congr`), which gives the lower bound (with Cauchy-Schwarz, `quad_lower`) and
the determinant (with `det(a I + c ξ ξᵀ) = a^(d-1) (a + c |ξ|²)`, proved for `a ≠ 0` by the matrix determinant lemma
and extended to `a = 0` by continuity in `a`). The inverse, the factor, the Newton step and the traces are direct
expansions of rank-one products (`vecMulVec`).
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly.R1

/-! ## Leaves -/

/-- `A (Aᵀ P) = 1`. -/
theorem r1_mul_AtP {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1) :
    A * (Aᵀ * P) = 1 := by
  rw [← Matrix.mul_assoc, hAS, hSP]

/-- `Aᵀ P A = 1`. -/
theorem r1_AtPA {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1) :
    Aᵀ * P * A = 1 :=
  mul_eq_one_comm.mp (r1_mul_AtP hAS hSP)

/-- `A⁻¹ = Aᵀ P`. -/
theorem r1_inv {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1) :
    A⁻¹ = Aᵀ * P :=
  Matrix.inv_eq_right_inv (r1_mul_AtP hAS hSP)

/-- `Aᵀ u = ξ`. -/
theorem r1_At_u {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1)
    (ξ : Fin d → ℝ) : Aᵀ *ᵥ r1U P A ξ = ξ := by
  rw [r1U, r1W, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, r1_AtPA hAS hSP,
    Matrix.one_mulVec]

/-- `Σ u = w`. -/
theorem r1_S_u {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hSP : S * P = 1) (ξ : Fin d → ℝ) :
    S *ᵥ r1U P A ξ = r1W A ξ := by
  rw [r1U, Matrix.mulVec_mulVec, hSP, Matrix.one_mulVec]

/-- `⟨u, w⟩ = |ξ|²` from `Aᵀ u = ξ`. -/
theorem r1_u_dot_w {d : ℕ} {P A : Matrix (Fin d) (Fin d) ℝ} {ξ : Fin d → ℝ} (h : Aᵀ *ᵥ r1U P A ξ = ξ) :
    r1U P A ξ ⬝ᵥ r1W A ξ = ξ ⬝ᵥ ξ := by
  rw [r1W, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

/-- `Aᵀ P' A = a I + c ξ ξᵀ`. -/
theorem r1_congr {d : ℕ} {P A : Matrix (Fin d) (Fin d) ℝ} (ξ : Fin d → ℝ) (c : ℝ) (hA : Aᵀ * P * A = 1)
    (hu : Aᵀ *ᵥ r1U P A ξ = ξ) :
    Aᵀ * r1P' P A ξ c * A = (1 - c) • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ := by
  simp only [r1P', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hA,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hu]

/-- `(A y)ᵀ M (A y) = yᵀ (Aᵀ M A) y`. -/
theorem dot_conj {d : ℕ} (A M : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    (A *ᵥ y) ⬝ᵥ (M *ᵥ (A *ᵥ y)) = y ⬝ᵥ ((Aᵀ * M * A) *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- `yᵀ (a I + c ξ ξᵀ) y ≥ min(a, a + c |ξ|²) |y|²`. -/
theorem quad_lower {d : ℕ} (a c : ℝ) (ξ y : Fin d → ℝ) :
    min a (a + c * (ξ ⬝ᵥ ξ)) * (y ⬝ᵥ y) ≤
      y ⬝ᵥ ((a • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ) *ᵥ y) := by
  have h1 : y ⬝ᵥ ((a • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ) *ᵥ y) =
      a * (y ⬝ᵥ y) + c * (ξ ⬝ᵥ y) ^ 2 := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, dotProduct_comm y ξ]
    ring
  have hcs : (ξ ⬝ᵥ y) ^ 2 ≤ (ξ ⬝ᵥ ξ) * (y ⬝ᵥ y) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ξ y
    simpa only [dotProduct, sq] using this
  have hY : 0 ≤ y ⬝ᵥ y := by
    simpa using dotProduct_self_star_nonneg y
  rw [h1]
  rcases le_or_gt 0 c with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_right (min_le_left a (a + c * (ξ ⬝ᵥ ξ))) hY,
      mul_nonneg hc (sq_nonneg (ξ ⬝ᵥ y))]
  · nlinarith [mul_le_mul_of_nonneg_right (min_le_right a (a + c * (ξ ⬝ᵥ ξ))) hY,
      mul_le_mul_of_nonpos_left hcs hc.le]

/-- `det(a I + c ξ ξᵀ) = a^(d-1) (a + c |ξ|²)` for `d ≥ 1`, every real `a`. -/
theorem det_smul_one_add_vecMulVec {d : ℕ} (hd : 1 ≤ d) (a c : ℝ) (ξ : Fin d → ℝ) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ).det = a ^ (d - 1) * (a + c * (ξ ⬝ᵥ ξ)) := by
  have key : ∀ b : ℝ, b ≠ 0 →
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ).det = b ^ (d - 1) * (b + c * (ξ ⬝ᵥ ξ)) := by
    intro b hb
    have hM : b • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ =
        b • (1 + replicateCol Unit ((c / b) • ξ) * replicateRow Unit ξ) := by
      rw [← vecMulVec_eq, smul_vecMulVec, smul_add, smul_smul, mul_div_cancel₀ c hb]
    rw [hM, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin,
      dotProduct_smul, smul_eq_mul]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  have hf : Continuous fun b : ℝ => (b • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec ξ ξ).det :=
    ((continuous_id.smul continuous_const).add continuous_const).matrix_det
  have hg : Continuous fun b : ℝ => b ^ (d - 1) * (b + c * (ξ ⬝ᵥ ξ)) := by fun_prop
  exact congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg fun b hb => key b hb) a

/-- `S P' = a I + c w uᵀ`. -/
theorem r1_S_mul_Pp {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hSP : S * P = 1) (ξ : Fin d → ℝ) (c : ℝ) :
    S * r1P' P A ξ c = (1 - c) • (1 : Matrix (Fin d) (Fin d) ℝ) + c • vecMulVec (r1W A ξ) (r1U P A ξ) := by
  rw [r1P', Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hSP, Matrix.mul_vecMulVec, r1_S_u hSP]

/-- `w wᵀ P' = q w uᵀ`. -/
theorem r1_ww_mul_Pp {d : ℕ} {P A : Matrix (Fin d) (Fin d) ℝ} (hPt : Pᵀ = P) (ξ : Fin d → ℝ) (c : ℝ)
    (huw : r1U P A ξ ⬝ᵥ r1W A ξ = ξ ⬝ᵥ ξ) :
    vecMulVec (r1W A ξ) (r1W A ξ) * r1P' P A ξ c = r1Q c ξ • vecMulVec (r1W A ξ) (r1U P A ξ) := by
  have hwP : r1W A ξ ᵥ* P = r1U P A ξ := by rw [← Matrix.mulVec_transpose, hPt]; rfl
  rw [r1P', Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.vecMulVec_mul, hwP,
    Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm, huw, vecMulVec_smul, smul_smul, ← add_smul]
  rfl

/-- The scalar identity of (iii): `c'² |ξ|² - 2 c' + c/q = 0`. -/
theorem r1_quadratic {d : ℕ} (ξ : Fin d → ℝ) (c : ℝ) (ha : 0 < 1 - c) (hq : 0 < r1Q c ξ) :
    r1C' c ξ ^ 2 * (ξ ⬝ᵥ ξ) - 2 * r1C' c ξ + c / r1Q c ξ = 0 := by
  have hs0 : 0 ≤ Real.sqrt ((1 - c) / r1Q c ξ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((1 - c) / r1Q c ξ) ^ 2 = (1 - c) / r1Q c ξ :=
    Real.sq_sqrt (div_nonneg ha.le hq.le)
  have h1s : 1 + Real.sqrt ((1 - c) / r1Q c ξ) ≠ 0 := by positivity
  have key : r1C' c ξ * (1 + Real.sqrt ((1 - c) / r1Q c ξ)) = c / r1Q c ξ := by
    rw [r1C', div_mul_cancel₀ _ h1s]
  have h3 : c / r1Q c ξ * (ξ ⬝ᵥ ξ) = 1 - Real.sqrt ((1 - c) / r1Q c ξ) ^ 2 := by
    rw [hs2]
    have hq' := hq.ne'
    unfold r1Q at hq' ⊢
    field_simp
    ring
  have h2 : r1C' c ξ * (ξ ⬝ᵥ ξ) = 1 - Real.sqrt ((1 - c) / r1Q c ξ) := by
    apply mul_right_cancel₀ h1s
    linear_combination (ξ ⬝ᵥ ξ) * key + h3
  linear_combination r1C' c ξ * h2 - key

/-- `Σ' u = w/q`. -/
theorem r1_Sp_u {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (ξ : Fin d → ℝ) (c : ℝ) (ha : 0 < 1 - c)
    (hq : 0 < r1Q c ξ) (hSu : S *ᵥ r1U P A ξ = r1W A ξ) (huw : r1U P A ξ ⬝ᵥ r1W A ξ = ξ ⬝ᵥ ξ) :
    r1S' S A ξ c *ᵥ r1U P A ξ = (r1Q c ξ)⁻¹ • r1W A ξ := by
  rw [r1S', Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, hSu, dotProduct_comm, huw, smul_smul]
  rw [show r1W A ξ - (c / r1Q c ξ * (ξ ⬝ᵥ ξ)) • r1W A ξ = (1 - c / r1Q c ξ * (ξ ⬝ᵥ ξ)) • r1W A ξ by
    rw [sub_smul, one_smul], smul_smul]
  congr 1
  have hq' := hq.ne'
  have ha' := ha.ne'
  unfold r1Q at hq' ⊢
  field_simp
  ring

/-- `A' A'ᵀ = Σ'`, given the quadratic of `c'`. -/
theorem r1_Ap_mul_Apt {d : ℕ} {S A : Matrix (Fin d) (Fin d) ℝ} (ξ : Fin d → ℝ) (c : ℝ) (ha : 0 < 1 - c)
    (hAS : A * Aᵀ = S) (hquad : r1C' c ξ ^ 2 * (ξ ⬝ᵥ ξ) - 2 * r1C' c ξ + c / r1Q c ξ = 0) :
    r1A' A ξ c * (r1A' A ξ c)ᵀ = r1S' S A ξ c := by
  have hs : (Real.sqrt (1 - c))⁻¹ * (Real.sqrt (1 - c))⁻¹ = (1 - c)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ha.le]
  have hcoef : c / r1Q c ξ = 2 * r1C' c ξ - r1C' c ξ ^ 2 * (ξ ⬝ᵥ ξ) := by linarith
  have hV1 : A * vecMulVec ξ (r1W A ξ) = vecMulVec (r1W A ξ) (r1W A ξ) := by
    rw [Matrix.mul_vecMulVec]; rfl
  have hV2 : vecMulVec (r1W A ξ) ξ * Aᵀ = vecMulVec (r1W A ξ) (r1W A ξ) := by
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]; rfl
  have hV3 : vecMulVec (r1W A ξ) ξ * vecMulVec ξ (r1W A ξ) = (ξ ⬝ᵥ ξ) • vecMulVec (r1W A ξ) (r1W A ξ) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hT : (r1A' A ξ c)ᵀ = (Real.sqrt (1 - c))⁻¹ • (Aᵀ - r1C' c ξ • vecMulVec ξ (r1W A ξ)) := by
    rw [r1A', Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  have hInner : (A - r1C' c ξ • vecMulVec (r1W A ξ) ξ) * (Aᵀ - r1C' c ξ • vecMulVec ξ (r1W A ξ)) =
      S - (c / r1Q c ξ) • vecMulVec (r1W A ξ) (r1W A ξ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hAS, hV1, hV2, hV3, smul_smul,
      hcoef]
    module
  rw [hT, r1A', Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, hInner]
  rfl

/-- The trace of `P'`. -/
theorem r1_trace_Pp {d : ℕ} (P A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ) :
    (r1P' P A ξ c).trace = (1 - c) * P.trace + c * (r1U P A ξ ⬝ᵥ r1U P A ξ) := by
  simp only [r1P', Matrix.trace_add, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]

/-- The trace of `Σ'`. -/
theorem r1_trace_Sp {d : ℕ} (S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ) :
    (r1S' S A ξ c).trace = (S.trace - (c / r1Q c ξ) * (r1W A ξ ⬝ᵥ r1W A ξ)) / (1 - c) := by
  simp only [r1S', Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_vecMulVec, smul_eq_mul]
  ring

/-- `P'` is symmetric when `P` is. -/
theorem r1_Pp_transpose {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (A : Matrix (Fin d) (Fin d) ℝ) (hPt : Pᵀ = P)
    (ξ : Fin d → ℝ) (c : ℝ) : (r1P' P A ξ c)ᵀ = r1P' P A ξ c := by
  simp only [r1P', Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_vecMulVec, hPt]

/-! ## Coupled parts -/

/-- The lower bound of (i). -/
theorem r1_lower {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1)
    (ξ : Fin d → ℝ) (c : ℝ) (x : Fin d → ℝ) :
    min (1 - c) (r1Q c ξ) * ((A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x)) ≤ x ⬝ᵥ (r1P' P A ξ c *ᵥ x) := by
  have hx : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, r1_inv hAS hSP, r1_mul_AtP hAS hSP, Matrix.one_mulVec]
  have h := quad_lower (1 - c) c ξ (A⁻¹ *ᵥ x)
  rw [← r1_congr ξ c (r1_AtPA hAS hSP) (r1_At_u hAS hSP ξ), ← dot_conj, hx] at h
  exact h

/-- The determinant of (i). -/
theorem r1_det {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hAS : A * Aᵀ = S) (hSP : S * P = 1)
    (ξ : Fin d → ℝ) (c : ℝ) (hd : 1 ≤ d) :
    (r1P' P A ξ c).det = (1 - c) ^ (d - 1) * r1Q c ξ * P.det := by
  have h1 := congrArg Matrix.det (r1_congr ξ c (r1_AtPA hAS hSP) (r1_At_u hAS hSP ξ))
  have h2 := congrArg Matrix.det (r1_AtPA hAS hSP)
  rw [det_smul_one_add_vecMulVec hd] at h1
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1 h2
  unfold r1Q
  linear_combination P.det * h1 - (r1P' P A ξ c).det * h2

/-- `Σ' P' = 1`. -/
theorem r1_Sp_mul_Pp {d : ℕ} {P S A : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (hAS : A * Aᵀ = S)
    (hSP : S * P = 1) (ξ : Fin d → ℝ) (c : ℝ) (ha : 0 < 1 - c) (hq : 0 < r1Q c ξ) :
    r1S' S A ξ c * r1P' P A ξ c = 1 := by
  have hPt : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian
  have huw := r1_u_dot_w (r1_At_u hAS hSP ξ)
  rw [r1S', Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, r1_S_mul_Pp hSP, r1_ww_mul_Pp hPt ξ c huw,
    smul_smul, div_mul_cancel₀ c hq.ne', add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

end AdversarialBco.Poly.R1

namespace AdversarialBco.Poly

open R1

/-! ## The five parts -/

theorem lemmaR1i : LemmaR1i := by
  intro d P S A ξ c ⟨hP, hAS, hSP⟩
  have hPt : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian
  have hu := r1_At_u hAS hSP ξ
  refine ⟨hu, r1_S_u hSP ξ, r1_u_dot_w hu, r1_lower hAS hSP ξ c, fun ha hq => ?_, r1_det hAS hSP ξ c⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact r1_Pp_transpose A hPt ξ c
  · have hy : A⁻¹ *ᵥ x ≠ 0 := by
      intro h0
      apply hx
      rw [← Matrix.one_mulVec x, ← r1_mul_AtP hAS hSP, ← r1_inv hAS hSP, ← Matrix.mulVec_mulVec, h0,
        Matrix.mulVec_zero]
    have hpos : 0 < (A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x) := by
      have h := Matrix.dotProduct_self_star_pos_iff.mpr hy
      rwa [star_trivial] at h
    rw [star_trivial]
    exact lt_of_lt_of_le (mul_pos (lt_min ha hq) hpos) (r1_lower hAS hSP ξ c x)

theorem lemmaR1ii : LemmaR1ii := by
  intro d P S A ξ c ⟨hP, hAS, hSP⟩ ha hq
  have h := r1_Sp_mul_Pp hP hAS hSP ξ c ha hq
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem lemmaR1iii : LemmaR1iii := by
  intro d P S A ξ c ⟨hP, hAS, hSP⟩ ha hq
  have hquad := r1_quadratic ξ c ha hq
  have hA' := r1_Ap_mul_Apt ξ c ha hAS hquad
  refine ⟨hquad, hA', fun h0 => ?_⟩
  have h := congrArg Matrix.det (r1_Sp_mul_Pp hP hAS hSP ξ c ha hq)
  rw [← hA', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_one] at h
  simp at h

theorem lemmaR1iv : LemmaR1iv := by
  intro d P S A ξ c Y l ⟨hP, hAS, hSP⟩ ha hq hl
  have huw := r1_u_dot_w (r1_At_u hAS hSP ξ)
  have h1 : r1S' S A ξ c *ᵥ ((Y / (1 - l)) • r1U P A ξ) = (Y / ((1 - l) * r1Q c ξ)) • r1W A ξ := by
    rw [Matrix.mulVec_smul, r1_Sp_u ξ c ha hq (r1_S_u hSP ξ) huw, smul_smul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, smul_dotProduct, dotProduct_smul, huw, smul_eq_mul, smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv, ← inv_pow]
  ring

theorem lemmaR1v : LemmaR1v := by
  intro d P S A ξ c _
  exact ⟨r1_trace_Pp P A ξ c, fun _ _ => r1_trace_Sp S A ξ c⟩

end AdversarialBco.Poly
