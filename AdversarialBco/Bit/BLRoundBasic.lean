/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundIface
public import AdversarialBco.Bit.BLBasic

@[expose] public section

/-!
# Piece C: the matrix and vector tools

Casts of BL's rational data to `ℝ` (`cV`, `cM`), the spectral norm `opN` (the operator norm of `toEuclideanCLM`):
submultiplicative, triangle, transpose, rank one, entrywise bound, `opN A ^ 2 ≤ tr (A Aᵀ)`; the step of the tracking
lemma
(`track_step`, `hTr_step`); the rounding errors in `ℝ`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open Matrix

variable {d : ℕ}

/-! ## Casts -/

theorem cV_add (u v : Fin d → ℚ) : cV (u + v) = cV u + cV v := by ext i; simp [cV]

theorem cV_sub (u v : Fin d → ℚ) : cV (u - v) = cV u - cV v := by ext i; simp [cV]

theorem cV_smul (a : ℚ) (v : Fin d → ℚ) : cV (a • v) = (a : ℝ) • cV v := by ext i; simp [cV]

theorem cV_zero : cV (0 : Fin d → ℚ) = 0 := by ext i; simp [cV]

theorem cM_mulVec (M : Matrix (Fin d) (Fin d) ℚ) (v : Fin d → ℚ) : cV (M *ᵥ v) = cM M *ᵥ cV v := by
  ext i; simp [cV, cM, mulVec, dotProduct]

theorem cM_mul (M N : Matrix (Fin d) (Fin d) ℚ) : cM (M * N) = cM M * cM N := by
  ext i j; simp [cM, Matrix.mul_apply]

theorem cM_add (M N : Matrix (Fin d) (Fin d) ℚ) : cM (M + N) = cM M + cM N := by ext i j; simp [cM]

theorem cM_sub (M N : Matrix (Fin d) (Fin d) ℚ) : cM (M - N) = cM M - cM N := by ext i j; simp [cM]

theorem cM_smul (a : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) : cM (a • M) = (a : ℝ) • cM M := by ext i j; simp [cM]

theorem cM_transpose (M : Matrix (Fin d) (Fin d) ℚ) : cM Mᵀ = (cM M)ᵀ := by ext i j; simp [cM]

theorem cM_vecMulVec (u v : Fin d → ℚ) : cM (vecMulVec u v) = vecMulVec (cV u) (cV v) := by
  ext i j; simp [cM, cV, vecMulVec]

theorem cV_dot (u v : Fin d → ℚ) : ((u ⬝ᵥ v : ℚ) : ℝ) = cV u ⬝ᵥ cV v := by
  simp [cV, dotProduct]

/-! ## The spectral norm -/

/-- `oNorm_eq` under a second name. -/
theorem oNorm_eq_norm (v : Fin d → ℝ) : oNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := oNorm_eq v

theorem oNorm_mulVec_le (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : oNorm (M *ᵥ v) ≤ opN M * oNorm v := by
  rw [oNorm_eq, oNorm_eq, opN, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem opN_nonneg (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ opN M := norm_nonneg _

theorem opN_mul_le (M N : Matrix (Fin d) (Fin d) ℝ) : opN (M * N) ≤ opN M * opN N := by
  simpa [opN, ContinuousLinearMap.mul_def] using
    ContinuousLinearMap.opNorm_comp_le (Matrix.toEuclideanCLM (𝕜 := ℝ) M) (Matrix.toEuclideanCLM (𝕜 := ℝ) N)

theorem opN_add_le (M N : Matrix (Fin d) (Fin d) ℝ) : opN (M + N) ≤ opN M + opN N := by
  unfold opN
  rw [map_add]
  exact norm_add_le _ _

theorem opN_smul (a : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : opN (a • M) = |a| * opN M := by
  unfold opN
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) (a • M) = a • Matrix.toEuclideanCLM (𝕜 := ℝ) M := by
    simpa using map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) a M
  rw [h1]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

theorem opN_one_le : opN (1 : Matrix (Fin d) (Fin d) ℝ) ≤ 1 := by
  unfold opN
  have h : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
    simp [map_one (Matrix.toEuclideanCLM (𝕜 := ℝ))]
  rw [h]
  exact ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))

theorem opN_transpose (M : Matrix (Fin d) (Fin d) ℝ) : opN Mᵀ = opN M := by
  unfold opN
  rw [← Matrix.cstar_norm_def Mᵀ, ← Matrix.cstar_norm_def M]
  rw [(Matrix.conjTranspose_eq_transpose_of_trivial M).symm]
  rw [Matrix.l2_opNorm_conjTranspose]

theorem opN_le_of_abs_le (M : Matrix (Fin d) (Fin d) ℝ) (e : ℝ) (h : ∀ i j, |M i j| ≤ e) : opN M ≤ d * e := by
  have h_nonneg : 0 ≤ (d : ℝ) * e := by
    by_cases hd : d = 0
    · subst hd; simp
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      have hpos := h ⟨0, hd_pos⟩ ⟨0, hd_pos⟩
      have h_abs_nonneg : 0 ≤ |M ⟨0, hd_pos⟩ ⟨0, hd_pos⟩| := abs_nonneg _
      have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
      nlinarith
  have h_bound : ∀ (x : EuclideanSpace ℝ (Fin d)), ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) x‖ ≤ (d : ℝ) * e * ‖x‖ := by
    intro x
    let v := x.ofLp
    have hx_eq : x = WithLp.toLp 2 v := rfl
    rw [hx_eq]
    rw [Matrix.toEuclideanCLM_toLp (𝕜 := ℝ) M v]
    rw [← oNorm_eq_norm, ← oNorm_eq_norm]
    -- Goal: oNorm (M.mulVec v) ≤ (d : ℝ) * e * oNorm v
    have h_sq : oNorm (M.mulVec v) ^ 2 ≤ ((d : ℝ) * e * oNorm v) ^ 2 := by
      calc
        oNorm (M.mulVec v) ^ 2 = (M.mulVec v) ⬝ᵥ (M.mulVec v) := by rw [oNorm_sq]
        _ = ∑ i : Fin d, ((M.mulVec v) i) * ((M.mulVec v) i) := by rw [dotProduct]
        _ = ∑ i : Fin d, ((M.mulVec v) i) ^ 2 := by simp [sq]
        _ = ∑ i : Fin d, (∑ j : Fin d, M i j * v j) ^ 2 := by
          simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ i : Fin d, ((d : ℝ) * e ^ 2 * oNorm v ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _
          have h_term : (∑ j : Fin d, M i j * v j) ^ 2 ≤ (d : ℝ) * e ^ 2 * oNorm v ^ 2 := by
            calc
              (∑ j : Fin d, M i j * v j) ^ 2 = |∑ j : Fin d, M i j * v j| ^ 2 := by
                rw [sq_abs]
              _ ≤ (∑ j : Fin d, |M i j * v j|) ^ 2 := by
                have h_abs_sum : |∑ j : Fin d, M i j * v j| ≤ ∑ j : Fin d, |M i j * v j| :=
                  Finset.abs_sum_le_sum_abs _ _
                have h_nonneg_abs : 0 ≤ |∑ j : Fin d, M i j * v j| := abs_nonneg _
                have h_nonneg_sum : 0 ≤ ∑ j : Fin d, |M i j * v j| :=
                  Finset.sum_nonneg fun j _ => abs_nonneg _
                nlinarith
              _ = (∑ j : Fin d, |M i j| * |v j|) ^ 2 := by
                simp [abs_mul]
              _ ≤ (∑ j : Fin d, e * |v j|) ^ 2 := by
                have h_sum : (∑ j : Fin d, |M i j| * |v j|) ≤ (∑ j : Fin d, e * |v j|) := by
                  refine Finset.sum_le_sum ?_
                  intro j _
                  have h_entry := h i j
                  have h_nonneg_abs_v : 0 ≤ |v j| := abs_nonneg _
                  exact mul_le_mul_of_nonneg_right h_entry h_nonneg_abs_v
                have h_nonneg_sum1 : 0 ≤ ∑ j : Fin d, |M i j| * |v j| :=
                  Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
                simpa [sq] using mul_self_le_mul_self h_nonneg_sum1 h_sum
              _ = (e * ∑ j : Fin d, |v j|) ^ 2 := by
                simp [Finset.mul_sum]
              _ = e ^ 2 * (∑ j : Fin d, |v j|) ^ 2 := by ring
              _ ≤ e ^ 2 * ((∑ j : Fin d, (1 : ℝ) ^ 2) * (∑ j : Fin d, |v j| ^ 2)) := by
                have h_cauchy : (∑ j : Fin d, |v j|) ^ 2 ≤ (∑ j : Fin d, (1 : ℝ) ^ 2) * (∑ j : Fin d, |v j| ^ 2) := by
                  -- Cauchy-Schwarz: (∑ 1 * |v j|)^2 ≤ (∑ 1^2) * (∑ |v j|^2)
                  -- We need to simplify 1 * |v j| = |v j|
                  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ)) (fun j => |v j|)
                  simpa [one_mul] using h
                nlinarith
              _ = e ^ 2 * ((d : ℝ) * (∑ j : Fin d, |v j| ^ 2)) := by simp
              _ = (d : ℝ) * e ^ 2 * (∑ j : Fin d, |v j| ^ 2) := by ring
              _ = (d : ℝ) * e ^ 2 * (v ⬝ᵥ v) := by
                rw [dotProduct]
                refine congrArg (fun t => (d : ℝ) * e ^ 2 * t) ?_
                simp [sq]
              _ = (d : ℝ) * e ^ 2 * (oNorm v ^ 2) := by rw [oNorm_sq]
          exact h_term
        _ = (d : ℝ) * ((d : ℝ) * e ^ 2 * oNorm v ^ 2) := by
          simp [Finset.sum_const]
        _ = ((d : ℝ) * e * oNorm v) ^ 2 := by ring
    have h_nonneg_onorm : 0 ≤ oNorm (M.mulVec v) := oNorm_nonneg _
    have h_nonneg_rhs : 0 ≤ (d : ℝ) * e * oNorm v := by
      have h_de : 0 ≤ (d : ℝ) * e := h_nonneg
      have h_onorm : 0 ≤ oNorm v := oNorm_nonneg _
      nlinarith
    nlinarith
  rw [opN]
  refine ContinuousLinearMap.opNorm_le_bound (Matrix.toEuclideanCLM (𝕜 := ℝ) M) h_nonneg h_bound

theorem opN_sq_le_trace (A : Matrix (Fin d) (Fin d) ℝ) : opN A ^ 2 ≤ (A * Aᵀ).trace := by
  have h_opN_eq : opN A = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := rfl
  rw [h_opN_eq]
  set M := Real.sqrt ((A * Aᵀ).trace) with hM_def
  have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
  have h_trace_nonneg : 0 ≤ (A * Aᵀ).trace := by
    have h_trace_eq : (A * Aᵀ).trace = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
      calc
        (A * Aᵀ).trace = ∑ i : Fin d, ∑ j : Fin d, (A.hadamard A) i j := by
          rw [Matrix.sum_hadamard_eq]
        _ = ∑ i : Fin d, ∑ j : Fin d, (A i j * A i j) := rfl
        _ = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    rw [h_trace_eq]
    refine Finset.sum_nonneg fun i _ => ?_
    refine Finset.sum_nonneg fun j _ => ?_
    apply pow_two_nonneg
  have h_trace_eq : (A * Aᵀ).trace = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
    calc
      (A * Aᵀ).trace = ∑ i : Fin d, ∑ j : Fin d, (A.hadamard A) i j := by
        rw [Matrix.sum_hadamard_eq]
      _ = ∑ i : Fin d, ∑ j : Fin d, (A i j * A i j) := rfl
      _ = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  have h_bound : ∀ (v : EuclideanSpace ℝ (Fin d)),
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) v‖ ≤ M * ‖v‖ := by
    intro v
    -- Work with the underlying Fin d → ℝ function
    let w : Fin d → ℝ := v
    have h_norm_w : ‖v‖ = oNorm w := by
      dsimp [w, oNorm]
      rw [EuclideanSpace.norm_eq, dotProduct]
      refine congrArg Real.sqrt ?_
      simp [sq]
    -- The key inequality: oNorm (A *ᵥ w) ≤ M * oNorm w
    have h_key : oNorm (A *ᵥ w) ≤ M * oNorm w := by
      have h_sq_nonneg_onorm : 0 ≤ oNorm (A *ᵥ w) := oNorm_nonneg _
      have h_sq_nonneg_onorm_w : 0 ≤ oNorm w := oNorm_nonneg _
      have h_sq_le : oNorm (A *ᵥ w) ^ 2 ≤ (M * oNorm w) ^ 2 := by
        -- Cauchy-Schwarz: oNorm (A *ᵥ w) ^ 2 ≤ (A * Aᵀ).trace * (oNorm w) ^ 2
        have h_cauchy : oNorm (A *ᵥ w) ^ 2 ≤ (A * Aᵀ).trace * (oNorm w) ^ 2 := by
          rw [oNorm_sq, dotProduct]
          calc
            (∑ i : Fin d, (A *ᵥ w) i * (A *ᵥ w) i) = ∑ i : Fin d, (∑ j : Fin d, A i j * w j) * (∑ j : Fin d, A i j * w j) := by
              simp [Matrix.mulVec_apply, dotProduct]
            _ = ∑ i : Fin d, (∑ j : Fin d, A i j * w j) ^ 2 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
            _ ≤ ∑ i : Fin d, ((∑ j : Fin d, (A i j) ^ 2) * (∑ j : Fin d, (w j) ^ 2)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have h_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun j => A i j) (fun j => w j)
              simpa [dotProduct] using h_cs
            _ = (∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2) * (∑ j : Fin d, (w j) ^ 2) := by
              rw [← Finset.sum_mul]
            _ = (A * Aᵀ).trace * (∑ j : Fin d, (w j) ^ 2) := by rw [h_trace_eq]
            _ = (A * Aᵀ).trace * (oNorm w) ^ 2 := by
              rw [oNorm_sq, dotProduct]
              simp [sq]
        have h_sq_eq : M ^ 2 = (A * Aᵀ).trace := by
          rw [hM_def, Real.sq_sqrt h_trace_nonneg]
        calc
          oNorm (A *ᵥ w) ^ 2 ≤ (A * Aᵀ).trace * (oNorm w) ^ 2 := h_cauchy
          _ = M ^ 2 * (oNorm w) ^ 2 := by rw [h_sq_eq]
          _ = (M * oNorm w) ^ 2 := by ring
      -- Now from h_sq_le and nonnegativity, we get the desired inequality
      have hM_onorm_nonneg : 0 ≤ M * oNorm w := mul_nonneg hM_nonneg h_sq_nonneg_onorm_w
      nlinarith
    -- Relate the EuclideanSpace norm to oNorm
    have h_norm_mulVec : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) v‖ = oNorm (A *ᵥ w) := by
      dsimp [w]
      rw [oNorm_eq_norm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      -- Both sides are now √(∑ i, ...). Show the radicands are equal.
      refine congrArg Real.sqrt ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      -- Goal: ‖((toEuclideanCLM A) v).ofLp i‖ ^ 2 = ‖(A *ᵥ v.ofLp) i‖ ^ 2
      -- But ((toEuclideanCLM A) v).ofLp i = (A *ᵥ v.ofLp) i
      have h_eq : ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) v).ofLp i = (A *ᵥ v.ofLp) i := by
        rw [Matrix.ofLp_toEuclideanCLM]
      simp [h_eq]
    rw [h_norm_mulVec, h_norm_w]
    exact h_key
  have h_opNorm_le : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M :=
    ContinuousLinearMap.opNorm_le_bound (Matrix.toEuclideanCLM (𝕜 := ℝ) A) hM_nonneg h_bound
  have h_norm_nonneg : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := norm_nonneg _
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ^ 2 ≤ M ^ 2 := by
      have h := mul_self_le_mul_self h_norm_nonneg h_opNorm_le
      simpa [sq] using h
    _ = (A * Aᵀ).trace := by rw [hM_def, Real.sq_sqrt h_trace_nonneg]

theorem oNorm_le_of_abs_le (v : Fin d → ℝ) (e : ℝ) (h : ∀ i, |v i| ≤ e) : oNorm v ≤ Real.sqrt d * e := by
  by_cases hd0 : d = 0
  · subst hd0; simp [oNorm]
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
    have he : 0 ≤ e := by
      have h0 := h ⟨0, hd_pos⟩
      have h_abs_nonneg : 0 ≤ |v ⟨0, hd_pos⟩| := abs_nonneg _
      linarith
    have h_sq : ∀ i, (v i)^2 ≤ e^2 := by
      intro i
      rcases abs_le.mp (h i) with ⟨h_left, h_right⟩
      nlinarith
    have h_sum : v ⬝ᵥ v ≤ (d : ℝ) * e^2 := by
      calc
        v ⬝ᵥ v = ∑ i, (v i)^2 := by
          simp [dotProduct, sq]
        _ ≤ ∑ i : Fin d, e^2 := Finset.sum_le_sum fun i _ => h_sq i
        _ = (d : ℝ) * e^2 := by simp
    calc
      oNorm v = Real.sqrt (v ⬝ᵥ v) := rfl
      _ ≤ Real.sqrt ((d : ℝ) * e^2) := Real.sqrt_le_sqrt h_sum
      _ = Real.sqrt (d : ℝ) * Real.sqrt (e^2) := Real.sqrt_mul (Nat.cast_nonneg _) _
      _ = Real.sqrt (d : ℝ) * |e| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (d : ℝ) * e := by rw [abs_of_nonneg he]

theorem opN_le_of_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (e : ℝ) (he : 0 ≤ e)
    (h : ∀ v, oNorm (M *ᵥ v) ≤ e * oNorm v) : opN M ≤ e := by
  rw [opN]
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  simpa [Matrix.toEuclideanCLM_toLp M (x : Fin d → ℝ), oNorm_eq_norm] using h x

theorem opN_vecMulVec_le (x y : Fin d → ℝ) : opN (vecMulVec x y) ≤ oNorm x * oNorm y := by
  refine opN_le_of_mulVec _ _ (mul_nonneg (oNorm_nonneg _) (oNorm_nonneg _)) fun v => ?_
  have e : vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    ext i; simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [e, oNorm_smul]
  have := abs_dot_le y v
  have h0 := oNorm_nonneg x
  calc |y ⬝ᵥ v| * oNorm x ≤ oNorm y * oNorm v * oNorm x := mul_le_mul_of_nonneg_right this h0
    _ = oNorm x * oNorm y * oNorm v := by ring

theorem opN_one_add_le (H : Matrix (Fin d) (Fin d) ℝ) : opN (1 + H) ≤ 1 + opN H :=
  (opN_add_le 1 H).trans (by linarith [opN_one_le (d := d)])

/-! ## The step of the tracking lemma -/

theorem track_step (A0 A1 Ai N N' ρ H : Matrix (Fin d) (Fin d) ℝ) (h1 : A1 = A0 * N) (hi : A1 * Ai = 1) :
    (1 + H) * A0 * N' + ρ = (1 + (H + ((1 + H) * A0 * (N' - N) + ρ) * Ai)) * A1 := by
  have h_comm : Ai * A1 = 1 :=
    ((Matrix.mul_eq_one_comm_of_equiv (e := Equiv.refl (Fin d))).mp hi)
  rw [h1]
  have h_comm' : Ai * (A0 * N) = 1 := by
    calc
      Ai * (A0 * N) = Ai * A1 := by rw [h1]
      _ = 1 := h_comm
  noncomm_ring
  rw [h_comm']
  simp
  abel

theorem hTr_step (ha x V h : ℝ) (k : ℕ) (hx : 0 ≤ x) (hV : 0 ≤ V) (hh0 : 0 ≤ h)
    (hh : h ≤ (1 + ha + k * V) * (1 + x) ^ k - 1) :
    h + (1 + h) * x + V ≤ (1 + ha + ((k + 1 : ℕ) : ℝ) * V) * (1 + x) ^ (k + 1) - 1 := by
  push_cast
  have hx_nonneg : 0 ≤ 1 + x := by linarith
  have h1 : h + (1 + h) * x + V = (1 + h) * (1 + x) - 1 + V := by ring
  rw [h1]
  have h2 : 1 + h ≤ (1 + ha + (k : ℝ) * V) * (1 + x) ^ k := by linarith
  have h3 : (1 + h) * (1 + x) ≤ (1 + ha + (k : ℝ) * V) * (1 + x) ^ (k + 1) := by
    calc
      (1 + h) * (1 + x) ≤ ((1 + ha + (k : ℝ) * V) * (1 + x) ^ k) * (1 + x) :=
        mul_le_mul_of_nonneg_right h2 hx_nonneg
      _ = (1 + ha + (k : ℝ) * V) * ((1 + x) ^ k * (1 + x)) := by ring
      _ = (1 + ha + (k : ℝ) * V) * (1 + x) ^ (k + 1) := by rw [pow_succ]
  have h4 : V ≤ V * (1 + x) ^ (k + 1) := by
    have hp : 1 ≤ (1 + x) ^ (k + 1) := by
      have : (1 : ℝ) ^ (k + 1) ≤ (1 + x) ^ (k + 1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) (k + 1)
      simpa using this
    nlinarith
  nlinarith

/-- One step of the tracking lemma in norm: if `A1 = A0 N` has the right inverse `Ai`, BL's `(I + H) A0 N' + ρ` is
`(I + H') A1` with `|H'| ≤ |H| + (1 + |H|) |A0| |N' - N| |Ai| + |ρ| |Ai|`. -/
theorem track_norm (A0 A1 Ai N N' ρ H : Matrix (Fin d) (Fin d) ℝ) (h1 : A1 = A0 * N) (hi : A1 * Ai = 1) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, (1 + H) * A0 * N' + ρ = (1 + H') * A1 ∧
      opN H' ≤ opN H + (1 + opN H) * opN A0 * opN (N' - N) * opN Ai + opN ρ * opN Ai := by
  refine ⟨_, track_step A0 A1 Ai N N' ρ H h1 hi, ?_⟩
  have hH := opN_nonneg H; have hA := opN_nonneg A0; have hN := opN_nonneg (N' - N); have hI := opN_nonneg Ai
  have hr := opN_nonneg ρ
  refine (opN_add_le _ _).trans ?_
  have e1 := opN_mul_le ((1 + H) * A0 * (N' - N) + ρ) Ai
  have e2 := opN_add_le ((1 + H) * A0 * (N' - N)) ρ
  have e3 := opN_mul_le ((1 + H) * A0) (N' - N)
  have e4 := opN_mul_le (1 + H) A0
  have e5 := opN_one_add_le H
  have f4 : opN ((1 + H) * A0) ≤ (1 + opN H) * opN A0 := e4.trans (mul_le_mul_of_nonneg_right e5 hA)
  have f3 : opN ((1 + H) * A0 * (N' - N)) ≤ (1 + opN H) * opN A0 * opN (N' - N) :=
    e3.trans (mul_le_mul_of_nonneg_right f4 hN)
  have f2 : opN ((1 + H) * A0 * (N' - N) + ρ) ≤ (1 + opN H) * opN A0 * opN (N' - N) + opN ρ :=
    e2.trans (by linarith)
  have f1 := e1.trans (mul_le_mul_of_nonneg_right f2 hI)
  nlinarith

/-! ## Rounding in `ℝ` -/

theorem rnd_err_real (k : ℕ) (x : ℚ) : |((rnd k x : ℚ) : ℝ) - (x : ℝ)| ≤ 1 / 2 ^ (k + 1) := by
  have := rnd_err k x
  have h : ((|rnd k x - x| : ℚ) : ℝ) ≤ ((1 / 2 ^ (k + 1) : ℚ) : ℝ) := by exact_mod_cast this
  push_cast at h; exact h

theorem sqrtDn_err (k : ℕ) {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtDn k x : ℚ) : ℝ) ≤ Real.sqrt (x : ℝ) ∧ Real.sqrt (x : ℝ) < (sqrtDn k x : ℝ) + 1 / 2 ^ k := by
  have h_sq : sqrtDn k x ^ 2 ≤ x := sqrtDn_sq_le k hx
  have h_nonneg : 0 ≤ sqrtDn k x := sqrtDn_nonneg k x
  have hx' : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have h_sq' : ((sqrtDn k x : ℚ) : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast h_sq
  have h_nonneg' : 0 ≤ ((sqrtDn k x : ℚ) : ℝ) := by exact_mod_cast h_nonneg
  have h1 : ((sqrtDn k x : ℚ) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [Real.le_sqrt h_nonneg' hx']
    exact h_sq'
  have h_lt : x < (sqrtDn k x + 1 / 2 ^ k) ^ 2 := lt_sqrtDn_succ_sq k x
  have h_lt' : (x : ℝ) < (((sqrtDn k x : ℚ) : ℝ) + 1 / ((2 : ℝ) ^ k)) ^ 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr h_lt
    simpa [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h
  have h_sum_nonneg : 0 ≤ ((sqrtDn k x : ℚ) : ℝ) + 1 / ((2 : ℝ) ^ k) := by
    positivity
  have h2 : Real.sqrt (x : ℝ) < ((sqrtDn k x : ℚ) : ℝ) + 1 / ((2 : ℝ) ^ k) := by
    rw [Real.sqrt_lt hx' h_sum_nonneg]
    exact h_lt'
  exact And.intro h1 h2

theorem vecMulVec_diff (x y : Fin d → ℝ) :
    opN (vecMulVec x x - vecMulVec y y) ≤ (oNorm x + oNorm y) * oNorm (x - y) := by
  have h_vecMulVec_mulVec (u v w : Fin d → ℝ) : (vecMulVec u v) *ᵥ w = (v ⬝ᵥ w) • u := by
    ext i
    simp [vecMulVec, mulVec, dotProduct, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]
  have h_opN_vecMulVec_le (u v : Fin d → ℝ) : opN (vecMulVec u v) ≤ oNorm u * oNorm v := by
    rw [opN]
    apply ContinuousLinearMap.opNorm_le_bound
    · have hu := oNorm_nonneg u
      have hv := oNorm_nonneg v
      nlinarith
    · intro w
      have hw : w = WithLp.toLp 2 (fun i => w i) := by
        simp
      rw [hw, Matrix.toEuclideanCLM_toLp, ← oNorm_eq_norm, ← oNorm_eq_norm]
      rw [h_vecMulVec_mulVec u v (fun i => w i)]
      -- oNorm ((v ⬝ᵥ (fun i => w i)) • u) ≤ (oNorm u * oNorm v) * oNorm (fun i => w i)
      have h_oNorm_smul (c : ℝ) (z : Fin d → ℝ) : oNorm (c • z) = |c| * oNorm z := by
        unfold oNorm
        have h_dot : (c • z) ⬝ᵥ (c • z) = c ^ 2 * (z ⬝ᵥ z) := by
          calc
            (c • z) ⬝ᵥ (c • z) = ∑ i, (c • z) i * (c • z) i := rfl
            _ = ∑ i, (c * z i) * (c * z i) := by simp [smul_eq_mul]
            _ = ∑ i, c ^ 2 * (z i * z i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = c ^ 2 * ∑ i, z i * z i := by simp [Finset.mul_sum]
            _ = c ^ 2 * (z ⬝ᵥ z) := rfl
        rw [h_dot, Real.sqrt_mul (show 0 ≤ c ^ 2 from by positivity), Real.sqrt_sq_eq_abs]
      rw [h_oNorm_smul (v ⬝ᵥ (fun i => w i)) u]
      have h_abs : |v ⬝ᵥ (fun i => w i)| ≤ oNorm v * oNorm (fun i => w i) :=
        abs_dot_le v (fun i => w i)
      nlinarith [oNorm_nonneg u, oNorm_nonneg v, oNorm_nonneg (fun i => w i)]
  have h_decomp : vecMulVec x x - vecMulVec y y = vecMulVec x (x - y) + vecMulVec (x - y) y := by
    rw [vecMulVec_sub x x y, sub_vecMulVec x y y, sub_add_sub_cancel]
  rw [h_decomp]
  calc
    opN (vecMulVec x (x - y) + vecMulVec (x - y) y) ≤ opN (vecMulVec x (x - y)) + opN (vecMulVec (x - y) y) := by
      rw [opN, opN, opN]
      -- ‖toEuclideanCLM (A + B)‖ ≤ ‖toEuclideanCLM A‖ + ‖toEuclideanCLM B‖
      have h_add : toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (vecMulVec x (x - y) + vecMulVec (x - y) y) =
          toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (vecMulVec x (x - y)) +
          toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (vecMulVec (x - y) y) := by
        simp
      rw [h_add]
      exact norm_add_le _ _
    _ ≤ oNorm x * oNorm (x - y) + oNorm (x - y) * oNorm y := by
      gcongr
      · exact h_opN_vecMulVec_le x (x - y)
      · exact h_opN_vecMulVec_le (x - y) y
    _ = (oNorm x + oNorm y) * oNorm (x - y) := by ring

end AdversarialBco.Bit.BLP.RC
