/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2
public import AdversarialBco.Poly.PgLemmasProof

@[expose] public section

/-!
# DET, generic lemmas

Matrix and convexity lemmas read by the proof of DET (`Df2DetMain.lean`), stated on their own data: the quadratic
form `df2Sq`, the Loewner order through `PosSemidef`, the quadratic `df2Phi` and its update, the approximate
projection with its Pythagorean defect, the identity of the statistic of the test, the Hessian of a convex `C²`
function, the concavity of `log det`, the lemma of a ball under quadratics with one quadratic, the play inside the body.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The quadratic form -/

theorem sq_add (P Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : df2Sq (P + Q) v = df2Sq P v + df2Sq Q v := by
  simp [df2Sq, Matrix.add_mulVec, dotProduct_add]

theorem sq_sub (P Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : df2Sq (P - Q) v = df2Sq P v - df2Sq Q v := by
  simp [df2Sq, Matrix.sub_mulVec, dotProduct_sub]

theorem sq_smul (a : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : df2Sq (a • P) v = a * df2Sq P v := by
  simp [df2Sq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem sq_one (v : Fin d → ℝ) : df2Sq (1 : Matrix (Fin d) (Fin d) ℝ) v = v ⬝ᵥ v := by
  simp [df2Sq]

theorem sq_zero (v : Fin d → ℝ) : df2Sq (0 : Matrix (Fin d) (Fin d) ℝ) v = 0 := by
  simp [df2Sq]

theorem sq_sum {ι : Type*} (s : Finset ι) (P : ι → Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    df2Sq (∑ i ∈ s, P i) v = ∑ i ∈ s, df2Sq (P i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sq_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sq_add, ih]

theorem sq_smul_arg (P : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) (v : Fin d → ℝ) :
    df2Sq P (a • v) = a ^ 2 * df2Sq P v := by
  simp [df2Sq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

theorem sq_nonneg_of_psd {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (v : Fin d → ℝ) : 0 ≤ df2Sq P v := by
  have := hP.dotProduct_mulVec_nonneg v
  simpa [df2Sq] using this

theorem psd_of_sq {P : Matrix (Fin d) (Fin d) ℝ} (hH : P.IsHermitian) (h : ∀ v, 0 ≤ df2Sq P v) : P.PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun v => by simpa [df2Sq] using h v)

/-- The Loewner order read on the form. -/
theorem sq_le_of_psd {P Q : Matrix (Fin d) (Fin d) ℝ} (h : (Q - P).PosSemidef) (v : Fin d → ℝ) :
    df2Sq P v ≤ df2Sq Q v := by
  have := sq_nonneg_of_psd h v
  rw [sq_sub] at this; linarith

/-! ## The Loewner order -/

theorem psd_smul_one {a : ℝ} (h : 0 ≤ a) : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
  Matrix.PosSemidef.one.smul h

theorem psd_sub_smul_one {a b : ℝ} (h : b ≤ a) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ) - b • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  rw [← sub_smul]; exact psd_smul_one (by linarith)

theorem psd_trans {A B C : Matrix (Fin d) (Fin d) ℝ} (h1 : (A - B).PosSemidef) (h2 : (B - C).PosSemidef) :
    (A - C).PosSemidef := by
  have := h1.add h2
  rwa [sub_add_sub_cancel] at this

theorem psd_of_eq {A B : Matrix (Fin d) (Fin d) ℝ} (h : A.PosSemidef) (e : A = B) : B.PosSemidef := e ▸ h

theorem posDef_of_sub {P : Matrix (Fin d) (Fin d) ℝ} {a : ℝ} (ha : 0 < a)
    (h : (P - a • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) : P.PosDef := by
  have := Matrix.PosDef.posSemidef_add h (Matrix.PosDef.one.smul ha)
  rwa [sub_add_cancel] at this

theorem inv_smul_one {a : ℝ} (ha : a ≠ 0) : (a • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = a⁻¹ • 1 := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul_comm, mul_one, inv_mul_cancel₀ ha, one_smul]

/-! ## Leaves -/

theorem sq_le_trace (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) (v : Fin d → ℝ) :
    df2Sq P v ≤ P.trace * (v ⬝ᵥ v) := by
  dsimp [df2Sq]
  have hP_herm : P.IsHermitian := hP.isHermitian
  have hP_trace_eq : P.trace = ∑ i : Fin d, hP_herm.eigenvalues i :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hP_herm
  have h_eigen_nonneg : ∀ i, 0 ≤ hP_herm.eigenvalues i := hP.eigenvalues_nonneg
  set U := hP_herm.eigenvectorUnitary with hU_def
  set D := diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hP_herm.eigenvalues) with hD_def
  have h_spec : P = (U : Matrix (Fin d) (Fin d) ℝ) * D * (star (U : Matrix (Fin d) (Fin d) ℝ)) := by
    simpa [hU_def, hD_def, Unitary.conjStarAlgAut_star_apply, Unitary.conjStarAlgAut_apply]
      using hP_herm.spectral_theorem
  -- Let w = U^* *ᵥ v
  set w := (star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v with hw_def
  have h_vecMul_eq : ∀ (x : Fin d → ℝ), vecMul x (U : Matrix (Fin d) (Fin d) ℝ) = (star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x := by
    intro x
    ext i
    simp [vecMul, mulVec, dotProduct, mul_comm]
  have h_dot1 : v ⬝ᵥ (P *ᵥ v) = w ⬝ᵥ (D *ᵥ w) := by
    calc
      v ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (((U : Matrix (Fin d) (Fin d) ℝ) * D * (star (U : Matrix (Fin d) (Fin d) ℝ))) *ᵥ v) := by rw [h_spec]
      _ = v ⬝ᵥ ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ (D *ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v))) := by
        simp [Matrix.mulVec_mulVec, mul_assoc]
      _ = (vecMul v (U : Matrix (Fin d) (Fin d) ℝ)) ⬝ᵥ (D *ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v)) := by rw [Matrix.dotProduct_mulVec]
      _ = ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) ⬝ᵥ (D *ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v)) := by rw [h_vecMul_eq v]
      _ = w ⬝ᵥ (D *ᵥ w) := by rw [hw_def]
  have h_dot2 : v ⬝ᵥ v = w ⬝ᵥ w := by
    have hU_mul_star : (U : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      exact Unitary.coe_mul_star_self U
    calc
      v ⬝ᵥ v = v ⬝ᵥ (1 *ᵥ v) := by simp
      _ = v ⬝ᵥ (((U : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) := by rw [hU_mul_star]
      _ = v ⬝ᵥ ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v)) := by simp [Matrix.mulVec_mulVec]
      _ = (vecMul v (U : Matrix (Fin d) (Fin d) ℝ)) ⬝ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) := by rw [Matrix.dotProduct_mulVec]
      _ = ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) ⬝ᵥ ((star (U : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) := by rw [h_vecMul_eq v]
      _ = w ⬝ᵥ w := by rw [hw_def]
  have h_dot3 : w ⬝ᵥ (D *ᵥ w) = ∑ i : Fin d, (hP_herm.eigenvalues i) * (w i * w i) := by
    rw [hD_def]
    simp [Matrix.mulVec_diagonal, dotProduct, mul_left_comm]
  -- Now combine: v^T P v = ∑ λ_i w_i^2 ≤ ∑ λ_i * |w|^2 = tr(P) * |v|^2
  have h_goal : v ⬝ᵥ (P *ᵥ v) ≤ P.trace * (v ⬝ᵥ v) := by
    rw [h_dot1, h_dot3, h_dot2]
    -- Goal: ∑ i, (hP_herm.eigenvalues i) * (w i * w i) ≤ P.trace * (w ⬝ᵥ w)
    -- But P.trace = ∑ i, hP_herm.eigenvalues i
    rw [hP_trace_eq]
    -- Goal: ∑ i, λ_i * w_i^2 ≤ (∑ i, λ_i) * (∑ i, w_i^2)
    -- Since λ_i ≥ 0, this follows from w_i^2 ≤ ∑_j w_j^2 for each i
    calc
      ∑ i : Fin d, (hP_herm.eigenvalues i) * (w i * w i) ≤ ∑ i : Fin d, (hP_herm.eigenvalues i) * (∑ j : Fin d, w j * w j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h_nonneg_eigen : 0 ≤ hP_herm.eigenvalues i := h_eigen_nonneg i
        have h_sq_le : w i * w i ≤ ∑ j : Fin d, w j * w j := by
          -- single term is ≤ sum of nonnegative terms
          calc
            w i * w i = ∑ j : Fin d, (if j = i then w j * w j else 0) := by simp
            _ ≤ ∑ j : Fin d, w j * w j := Finset.sum_le_sum fun j _ => by
              by_cases hji : j = i
              · simp [hji]
              · simp [hji]
                simpa [sq] using sq_nonneg (w j)
        exact mul_le_mul_of_nonneg_left h_sq_le h_nonneg_eigen
      _ = (∑ i : Fin d, hP_herm.eigenvalues i) * (∑ j : Fin d, w j * w j) := by simp [Finset.sum_mul]
      _ = (∑ i : Fin d, hP_herm.eigenvalues i) * (w ⬝ᵥ w) := by simp [dotProduct]
  exact h_goal

theorem pyth_step (Q : Set (Fin d → ℝ)) (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (w m y : Fin d → ℝ) (e : ℝ) (hQ : Convex ℝ Q) (hm : m ∈ Q) (hy : y ∈ Q)
    (hmin : ∀ x ∈ Q, ellF P w m ≤ ellF P w x + e) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    df2Sq P (m - y) ≤ df2Sq P (w - y) + t * df2Sq P (m - y) + 2 * e / t := by
  -- P is symmetric (IsSymm for real matrices)
  have hPsymm : P.IsSymm := hP.1.isSymm
  -- The quadratic form q(v) = df2Sq P v is nonnegative
  have hq_nonneg : ∀ v : Fin d → ℝ, 0 ≤ df2Sq P v := by
    intro v
    dsimp [df2Sq]
    simpa using hP.dotProduct_mulVec_nonneg v
  -- x = m + t • (y - m) is in Q by convexity
  have hx_mem : m + t • (y - m) ∈ Q :=
    hQ.add_smul_sub_mem hm hy ⟨ht0.le, ht1⟩
  have hmin_x := hmin (m + t • (y - m)) hx_mem
  -- hmin_x : ellF P w m ≤ ellF P w (m + t • (y - m)) + e
  -- Multiply by 2: 2 * ellF P w m ≤ 2 * ellF P w (m + t • (y - m)) + 2 * e
  -- And 2 * ellF P w x = df2Sq P (x - w)
  have hellF_eq : ∀ x : Fin d → ℝ, 2 * ellF P w x = df2Sq P (x - w) := by
    intro x
    dsimp [ellF, df2Sq]
    ring
  have h_ineq : df2Sq P (m - w) ≤ df2Sq P ((m + t • (y - m)) - w) + 2 * e := by
    have h2 : 2 * ellF P w m ≤ 2 * ellF P w (m + t • (y - m)) + 2 * e := by linarith
    rw [hellF_eq m, hellF_eq (m + t • (y - m))] at h2
    exact h2
  -- Set a = m - w, b = m - y for cleaner algebra
  set a := m - w with ha
  set b := m - y with hb
  have hy_minus_m : y - m = -b := by
    dsimp [b]
    abel
  have hx_minus_w : (m + t • (y - m)) - w = a - t • b := by
    dsimp [a, b]
    calc
      (m + t • (y - m)) - w = (m - w) + t • (y - m) := by abel
      _ = a + t • (-(m - y)) := by
        dsimp [a]
        rw [hy_minus_m]
      _ = a - t • b := by
        dsimp [b]
        simp [smul_neg, sub_eq_add_neg]
  rw [hx_minus_w] at h_ineq
  -- h_ineq : df2Sq P a ≤ df2Sq P (a - t • b) + 2 * e
  -- Bilinear expansion: df2Sq P (x + s • y) = df2Sq P x + s^2 * df2Sq P y + s*(x⬝ᵥ(P*ᵥy) + y⬝ᵥ(P*ᵥx))
  have h_expand : ∀ (x y : Fin d → ℝ) (s : ℝ),
      df2Sq P (x + s • y) = df2Sq P x + s ^ 2 * df2Sq P y + s * (x ⬝ᵥ (P *ᵥ y) + y ⬝ᵥ (P *ᵥ x)) := by
    intro x y s
    dsimp [df2Sq]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul]
    ring_nf
  -- Expand df2Sq P (a - t • b) = df2Sq P (a + (-t) • b)
  have h_expand_sub : df2Sq P (a - t • b) = df2Sq P a + t ^ 2 * df2Sq P b - 2 * t * (a ⬝ᵥ (P *ᵥ b)) := by
    calc
      df2Sq P (a - t • b) = df2Sq P (a + (-t) • b) := by simp [sub_eq_add_neg]
      _ = df2Sq P a + (-t) ^ 2 * df2Sq P b + (-t) * (a ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ a)) := h_expand a b (-t)
      _ = df2Sq P a + t ^ 2 * df2Sq P b - t * (a ⬝ᵥ (P *ᵥ b) + b ⬝ᵥ (P *ᵥ a)) := by ring
      _ = df2Sq P a + t ^ 2 * df2Sq P b - 2 * t * (a ⬝ᵥ (P *ᵥ b)) := by
        rw [hPsymm.dotProduct_mulVec_comm (x := a) (y := b)]
        ring
  rw [h_expand_sub] at h_ineq
  -- h_ineq : df2Sq P a ≤ df2Sq P a + t ^ 2 * df2Sq P b - 2 * t * (a ⬝ᵥ (P *ᵥ b)) + 2 * e
  -- Cancel df2Sq P a from both sides
  have h_ineq2 : 0 ≤ t ^ 2 * df2Sq P b - 2 * t * (a ⬝ᵥ (P *ᵥ b)) + 2 * e := by
    linarith
  -- Divide by t > 0: 0 ≤ t * df2Sq P b - 2 * (a ⬝ᵥ (P *ᵥ b)) + 2 * e / t
  have h_ineq3 : 0 ≤ t * df2Sq P b - 2 * (a ⬝ᵥ (P *ᵥ b)) + 2 * e / t := by
    have h := h_ineq2
    field_simp [ht0.ne.symm]
    nlinarith
  -- Expand df2Sq P (w - y) = df2Sq P (b - a)
  have hw_minus_y : w - y = b - a := by
    dsimp [a, b]
    abel
  rw [hw_minus_y]
  -- Goal: df2Sq P b ≤ df2Sq P (b - a) + t * df2Sq P b + 2 * e / t
  -- Expand df2Sq P (b - a) = df2Sq P (b + (-a))
  have h_expand_ba : df2Sq P (b - a) = df2Sq P b + df2Sq P a - 2 * (a ⬝ᵥ (P *ᵥ b)) := by
    calc
      df2Sq P (b - a) = df2Sq P (b + (-1) • a) := by simp [sub_eq_add_neg]
      _ = df2Sq P b + (-1) ^ 2 * df2Sq P a + (-1) * (b ⬝ᵥ (P *ᵥ a) + a ⬝ᵥ (P *ᵥ b)) := h_expand b a (-1)
      _ = df2Sq P b + df2Sq P a - (b ⬝ᵥ (P *ᵥ a) + a ⬝ᵥ (P *ᵥ b)) := by ring
      _ = df2Sq P b + df2Sq P a - 2 * (a ⬝ᵥ (P *ᵥ b)) := by
        rw [hPsymm.dotProduct_mulVec_comm (x := a) (y := b)]
        ring
  rw [h_expand_ba]
  -- Goal: df2Sq P b ≤ (df2Sq P b + df2Sq P a - 2 * (a ⬝ᵥ (P *ᵥ b))) + t * df2Sq P b + 2 * e / t
  -- Cancel df2Sq P b from both sides and rearrange
  -- Goal: 0 ≤ df2Sq P a - 2 * (a ⬝ᵥ (P *ᵥ b)) + t * df2Sq P b + 2 * e / t
  -- From h_ineq3: 0 ≤ t * df2Sq P b - 2 * (a ⬝ᵥ (P *ᵥ b)) + 2 * e / t
  -- So it suffices to show: t * df2Sq P b - 2 * (a ⬝ᵥ (P *ᵥ b)) + 2 * e / t ≤
  --   df2Sq P a - 2 * (a ⬝ᵥ (P *ᵥ b)) + t * df2Sq P b + 2 * e / t
  -- i.e., 0 ≤ df2Sq P a, which is true
  have hq_nonneg_a : 0 ≤ df2Sq P a := hq_nonneg a
  nlinarith

theorem pyth_choose (q A D e : ℝ) (hq : q ≤ D ^ 2) (hD : 0 ≤ D) (he : 0 ≤ e) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → q ≤ A + t * D ^ 2 + 2 * e / t) :
    q ≤ A + 2 * D * Real.sqrt (2 * e) + 4 * e := by
  set s := Real.sqrt (2 * e) with hs
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 2 * e := Real.sq_sqrt (by nlinarith)
  by_cases hD0 : D = 0
  · -- Case D = 0
    subst hD0
    have hq0 : q ≤ 0 := by simpa using hq
    nlinarith
  · -- D > 0
    have hDpos : 0 < D := by
      by_contra! hle
      apply hD0
      nlinarith
    by_cases hs_le_D : s ≤ D
    · -- s ≤ D
      by_cases hs_zero : s = 0
      · -- s = 0, so e = 0
        have he0 : e = 0 := by
          rw [hs_zero] at hs_sq
          nlinarith
        subst he0
        have h_simp : ∀ t : ℝ, 0 < t → t ≤ 1 → q ≤ A + t * D ^ 2 := by
          intro t ht1 ht2
          have ht := h t ht1 ht2
          simpa using ht
        by_cases hqA : q ≤ A
        · nlinarith
        · -- q > A, derive contradiction using t = min(1, (q-A)/(2*D^2))
          have hqA' : A < q := by nlinarith
          set t := min 1 ((q - A) / (2 * D ^ 2)) with ht_def
          have ht_pos : 0 < t := by
            rw [ht_def]
            refine lt_min_iff.mpr ⟨by norm_num, ?_⟩
            refine div_pos ?_ ?_
            · nlinarith
            · nlinarith
          have ht_le_one : t ≤ 1 := by
            rw [ht_def]
            exact min_le_left _ _
          have ht_mul : t * D ^ 2 ≤ (q - A) / 2 := by
            rw [ht_def]
            have htmp : min 1 ((q - A) / (2 * D ^ 2)) ≤ (q - A) / (2 * D ^ 2) := min_le_right _ _
            have hpos : 0 ≤ D ^ 2 := by nlinarith
            calc
              min 1 ((q - A) / (2 * D ^ 2)) * D ^ 2 ≤ ((q - A) / (2 * D ^ 2)) * D ^ 2 :=
                mul_le_mul_of_nonneg_right htmp hpos
              _ = (q - A) / 2 := by
                field_simp [hDpos.ne']
          have hineq := h_simp t ht_pos ht_le_one
          nlinarith
      · -- s > 0
        have hs_pos : 0 < s := by
          by_contra! hle
          apply hs_zero
          nlinarith
        set t := s / D with ht_def
        have ht_pos : 0 < t := div_pos hs_pos hDpos
        have ht_le_one : t ≤ 1 := (div_le_one hDpos).mpr hs_le_D
        have hineq := h t ht_pos ht_le_one
        -- hineq: q ≤ A + t * D^2 + 2*e / t
        have h1 : t * D ^ 2 = s * D := by
          dsimp [t]
          field_simp [hDpos.ne']
        have h2 : 2 * e / t = s * D := by
          dsimp [t]
          field_simp [hs_pos.ne', hDpos.ne']
          rw [hs_sq]
        have hcalc : A + t * D ^ 2 + 2 * e / t = A + 2 * s * D := by
          rw [h1, h2]
          ring
        rw [hcalc] at hineq
        nlinarith
    · -- s > D
      have hs_gt_D : D < s := by
        by_contra! hle
        apply hs_le_D
        nlinarith
      have hineq := h 1 (by norm_num) (by norm_num)
      -- hineq: q ≤ A + D^2 + 2*e
      have hcalc : A + (1 : ℝ) * D ^ 2 + 2 * e / (1 : ℝ) = A + D ^ 2 + 2 * e := by ring
      rw [hcalc] at hineq
      -- D^2 < s^2 = 2*e
      have hDsq : D ^ 2 ≤ s ^ 2 := by
        nlinarith
      nlinarith

theorem approx_min_pyth (Q : Set (Fin d → ℝ)) (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (w m y : Fin d → ℝ) (e D : ℝ) (hQ : Convex ℝ Q) (hm : m ∈ Q) (hy : y ∈ Q) (he : 0 ≤ e) (hD : 0 ≤ D)
    (hmin : ∀ x ∈ Q, ellF P w m ≤ ellF P w x + e) (hDb : df2Sq P (m - y) ≤ D ^ 2) :
    df2Sq P (m - y) ≤ df2Sq P (w - y) + 2 * D * Real.sqrt (2 * e) + 4 * e := by
  have hA := sq_nonneg_of_psd hP (w - y)
  refine pyth_choose (df2Sq P (m - y)) (df2Sq P (w - y)) D e hDb hD he hA fun t ht0 ht1 => ?_
  have h := pyth_step Q P hP w m y e hQ hm hy hmin t ht0 ht1
  have : t * df2Sq P (m - y) ≤ t * D ^ 2 := mul_le_mul_of_nonneg_left hDb ht0.le
  linarith

theorem xi_identity (P S : Matrix (Fin d) (Fin d) ℝ) (hP : P.IsHermitian) (hPS : P * S = 1)
    (b G y : Fin d → ℝ) (k l η : ℝ) :
    η * (l - G ⬝ᵥ y) - 2 * df2Phi P b k y =
      (η * (l - G ⬝ᵥ S *ᵥ (b - (η / 2) • G)) - 2 * df2Phi P b k (S *ᵥ (b - (η / 2) • G))) -
        2 * ellF P (S *ᵥ (b - (η / 2) • G)) y := by
  set v := S *ᵥ (b - (η / 2) • G) with hv
  have hPv : P *ᵥ v = b - (η / 2) • G := by
    dsimp [v]
    calc
      P *ᵥ (S *ᵥ (b - (η / 2) • G)) = (P * S) *ᵥ (b - (η / 2) • G) := by rw [mulVec_mulVec]
      _ = 1 *ᵥ (b - (η / 2) • G) := by rw [hPS]
      _ = b - (η / 2) • G := by simp
  have h_sym (x y : Fin d → ℝ) : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
    have hP_trans : Pᵀ = P := by
      simpa using hP.eq
    calc
      x ⬝ᵥ (P *ᵥ y) = (x ᵥ* P) ⬝ᵥ y := by rw [dotProduct_mulVec]
      _ = (Pᵀ *ᵥ x) ⬝ᵥ y := by rw [mulVec_transpose]
      _ = (P *ᵥ x) ⬝ᵥ y := by rw [hP_trans]
      _ = y ⬝ᵥ (P *ᵥ x) := by rw [dotProduct_comm]
  have h_expand : (y - v) ⬝ᵥ (P *ᵥ (y - v)) = y ⬝ᵥ (P *ᵥ y) - 2 * (y ⬝ᵥ (P *ᵥ v)) + v ⬝ᵥ (P *ᵥ v) := by
    calc
      (y - v) ⬝ᵥ (P *ᵥ (y - v)) = (y - v) ⬝ᵥ (P *ᵥ y - P *ᵥ v) := by rw [mulVec_sub]
      _ = (y - v) ⬝ᵥ (P *ᵥ y) - (y - v) ⬝ᵥ (P *ᵥ v) := by rw [dotProduct_sub]
      _ = (y ⬝ᵥ (P *ᵥ y) - v ⬝ᵥ (P *ᵥ y)) - (y ⬝ᵥ (P *ᵥ v) - v ⬝ᵥ (P *ᵥ v)) := by rw [sub_dotProduct, sub_dotProduct]
      _ = y ⬝ᵥ (P *ᵥ y) - v ⬝ᵥ (P *ᵥ y) - y ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ v) := by ring
      _ = y ⬝ᵥ (P *ᵥ y) - y ⬝ᵥ (P *ᵥ v) - y ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ v) := by rw [h_sym v y]
      _ = y ⬝ᵥ (P *ᵥ y) - 2 * (y ⬝ᵥ (P *ᵥ v)) + v ⬝ᵥ (P *ᵥ v) := by ring
  dsimp [df2Phi, ellF]
  ring_nf
  rw [h_expand]
  rw [hPv]
  -- Goal: η*l - η*(G·y) - y·P·y + 2*(b·y) - 2*k = η*l - η*(G·v) - k*2 - v·(b - (η/2)·G) + 2*(b·v) - (y·P·y - 2*(y·(b - (η/2)·G)) + v·(b - (η/2)·G))
  -- Cancel η*l, -y·P·y, -k*2 from both sides
  -- Expand v·(b - (η/2)·G) and y·(b - (η/2)·G)
  have h_dot_expand (w : Fin d → ℝ) : w ⬝ᵥ (b - (η / 2) • G) = w ⬝ᵥ b - (η / 2) * (w ⬝ᵥ G) := by
    rw [dotProduct_sub, dotProduct_smul]
    ring
  rw [h_dot_expand v, h_dot_expand y]
  -- Now the goal is:
  -- η*l - η*(G·y) - y·P·y + 2*(b·y) - 2*k = η*l - η*(G·v) - k*2 - (v·b - (η/2)*(v·G)) + 2*(b·v) - (y·P·y - 2*(y·b - (η/2)*(y·G)) + (v·b - (η/2)*(v·G)))
  ring_nf
  -- After ring_nf: η*(G·y) - 2*(b·y) = η*(G·v) - 2*(b·v) + η*(v·G) - η*(y·G) - 2*(v·b) + 2*(y·b)
  -- Simplify using dotProduct_comm
  rw [dotProduct_comm G y, dotProduct_comm G v, dotProduct_comm b v]
  ring_nf
  rw [dotProduct_comm b y]
  ring

theorem phi_update (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.IsHermitian) (b u μ y : Fin d → ℝ) (k c : ℝ) :
    df2Phi ((1 - c) • P + c • vecMulVec u u) (b + c • ((u ⬝ᵥ μ) • u - P *ᵥ μ))
        (k + c / 2 * ((u ⬝ᵥ μ) ^ 2 - μ ⬝ᵥ (P *ᵥ μ))) y =
      df2Phi P b k y + c / 2 * df2Sq (vecMulVec u u - P) (y - μ) := by
  have hP' : Pᵀ = P := by
    have : Pᴴ = P := hP
    simpa using this
  have h_dot_mulVec {v w : Fin d → ℝ} : (P *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (P *ᵥ w) := by
    calc
      (P *ᵥ v) ⬝ᵥ w = w ⬝ᵥ (P *ᵥ v) := by rw [dotProduct_comm]
      _ = w ᵥ* P ⬝ᵥ v := by rw [Matrix.dotProduct_mulVec]
      _ = (Pᵀ *ᵥ w) ⬝ᵥ v := by
        have h := Matrix.vecMul_transpose Pᵀ w
        simpa [Matrix.transpose_transpose] using congrArg (· ⬝ᵥ v) h
      _ = (P *ᵥ w) ⬝ᵥ v := by rw [hP']
      _ = v ⬝ᵥ (P *ᵥ w) := by rw [dotProduct_comm]
  unfold df2Phi df2Sq
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub,
    dotProduct_add, dotProduct_smul, dotProduct_sub, smul_sub, sub_smul]
  simp
  -- Now we have an equality of real expressions involving dot products
  -- Use dotProduct_comm to normalize and h_dot_mulVec for P terms
  simp only [dotProduct_comm u y, dotProduct_comm u μ, h_dot_mulVec, dotProduct_comm y (P *ᵥ μ)]
  ring

theorem hess_psd (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ Set.univ f)
    (z : EuclideanSpace ℝ (Fin d)) : (df2HessM f z).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hsymm : (df2HessM f z).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    dsimp [df2HessM]
    have h_contdiff_at : ContDiffAt ℝ 2 f z := hf.contDiffAt
    have hsymm' : IsSymmSndFDerivAt ℝ f z := by
      have hmin : minSmoothness ℝ 2 ≤ 2 := by
        simp
      exact h_contdiff_at.isSymmSndFDerivAt hmin
    exact hsymm' _ _
  have hnonneg : ∀ v : Fin d → ℝ, 0 ≤ star v ⬝ᵥ ((df2HessM f z) *ᵥ v) := by
    intro v
    have hstar : star v = v := by
      simp
    rw [hstar]
    let x : EuclideanSpace ℝ (Fin d) := ∑ i, v i • (EuclideanSpace.single i 1)
    have h_eq : v ⬝ᵥ ((df2HessM f z) *ᵥ v) = ((fderiv ℝ (fderiv ℝ f) z) x) x := by
      calc
        v ⬝ᵥ ((df2HessM f z) *ᵥ v) = ∑ i, v i * (((df2HessM f z) *ᵥ v) i) := rfl
        _ = ∑ i, v i * (∑ j, (df2HessM f z) i j * v j) := rfl
        _ = ∑ i, ∑ j, v i * ((df2HessM f z) i j * v j) := by
          simp [Finset.mul_sum]
        _ = ∑ i, ∑ j, v i * (df2HessM f z) i j * v j := by
          ring
        _ = ∑ i, ∑ j, v i * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) * v j := by
          simp [df2HessM]
        _ = ((fderiv ℝ (fderiv ℝ f) z) (∑ i, v i • EuclideanSpace.single i 1)) (∑ j, v j • EuclideanSpace.single j 1) := by
          simp only [map_sum, _root_.sum_apply, ContinuousLinearMap.map_smul, _root_.smul_apply, smul_eq_mul]
          rw [Finset.sum_comm]
          simp [mul_comm, mul_left_comm]
        _ = ((fderiv ℝ (fderiv ℝ f) z) x) x := rfl
    rw [h_eq]
    set g := fun (t : ℝ) => f (z + t • x) with hg_def
    have h_contdiff_g : ContDiff ℝ 2 g := by
      have h_affine : ContDiff ℝ 2 (fun (t : ℝ) => z + t • x) := by
        have h_linear : ContDiff ℝ 2 (fun (t : ℝ) => t • x) :=
          (contDiff_id.smul_const x)
        exact (contDiff_const.add h_linear)
      exact hf.comp h_affine
    have h_conv_g : ConvexOn ℝ Set.univ g := by
      let φ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
        AffineMap.mk (fun t => z + t • x)
          { toFun := fun t => t • x
            map_add' := by intro a b; simp [add_smul]
            map_smul' := by intro r a; simp [smul_smul] }
          (by intro t u; simp [add_smul, add_comm, add_assoc])
      have h_comp := hc.comp_affineMap φ
      have h_preimage : φ ⁻¹' Set.univ = Set.univ := by simp
      rw [h_preimage] at h_comp
      have h_eq_fun : (f ∘ φ) = g := by
        ext t
        simp [g, φ]
      rw [h_eq_fun] at h_comp
      exact h_comp
    have h_diff_g : Differentiable ℝ g :=
      h_contdiff_g.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have h_diff_deriv_g : Differentiable ℝ (deriv g) :=
      ContDiff.differentiable_deriv_two h_contdiff_g
    have h_mono : Monotone (deriv g) := by
      have h_mono_on : MonotoneOn (deriv g) Set.univ :=
        h_conv_g.monotoneOn_deriv (fun x hx => h_diff_g.differentiableAt)
      intro a b hle
      exact h_mono_on (Set.mem_univ a) (Set.mem_univ b) hle
    have h_deriv2_nonneg : ∀ t : ℝ, 0 ≤ deriv (deriv g) t := by
      intro t
      exact h_mono.deriv_nonneg
    have h_deriv2_g : deriv (deriv g) 0 = ((fderiv ℝ (fderiv ℝ f) z) x) x := by
      have h_affine_contdiff : ContDiff ℝ 2 (fun (t : ℝ) => z + t • x) := by
        have h_linear : ContDiff ℝ 2 (fun (t : ℝ) => t • x) := (contDiff_id.smul_const x)
        exact (contDiff_const.add h_linear)
      calc
        deriv (deriv g) 0 = iteratedDeriv 2 g 0 := by
          rw [iteratedDeriv_succ, iteratedDeriv_one]
        _ = iteratedDeriv 2 (f ∘ fun (t : ℝ) => z + t • x) 0 := by
          rfl
        _ = ((iteratedFDeriv ℝ 2 f ((fun (t : ℝ) => z + t • x) 0)) fun _ => deriv (fun (t : ℝ) => z + t • x) 0) +
            (fderiv ℝ f ((fun (t : ℝ) => z + t • x) 0)) (iteratedDeriv 2 (fun (t : ℝ) => z + t • x) 0) := by
          rw [iteratedDeriv_vcomp_two (hf.contDiffAt) (h_affine_contdiff.contDiffAt)]
        _ = ((iteratedFDeriv ℝ 2 f z) fun _ => x) + (fderiv ℝ f z) 0 := by
          have h_deriv_affine : deriv (fun (t : ℝ) => z + t • x) 0 = x := by
            let φ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
              { toFun := fun t => z + t • x
                linear := { toFun := fun t => t • x, map_add' := by intro a b; simp [add_smul], map_smul' := by intro r a; simp [smul_smul] }
                map_vadd' := by intro t u; simp [add_smul, add_comm, add_assoc] }
            have h_hasDeriv : HasDerivAt φ (φ.linear 1) 0 := AffineMap.hasDerivAt φ
            have h_linear_one : φ.linear 1 = x := by
              simp [φ]
            rw [h_linear_one] at h_hasDeriv
            exact h_hasDeriv.deriv
          have h_iteratedDeriv_affine : iteratedDeriv 2 (fun (t : ℝ) => z + t • x) 0 = 0 := by
            rw [iteratedDeriv_succ, iteratedDeriv_one]
            have h_deriv_eq : deriv (fun (t : ℝ) => z + t • x) = fun _ => x := by
              funext t
              have h_hasDeriv_t : HasDerivAt (fun (s : ℝ) => z + s • x) x t := by
                let φ : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
                  { toFun := fun s => z + s • x
                    linear := { toFun := fun s => s • x, map_add' := by intro a b; simp [add_smul], map_smul' := by intro r a; simp [smul_smul] }
                    map_vadd' := by intro s u; simp [add_smul, add_comm, add_assoc] }
                have h := AffineMap.hasDerivAt φ (x := t)
                simpa [φ] using h
              exact h_hasDeriv_t.deriv
            rw [h_deriv_eq]
            simp
          simp [h_deriv_affine, h_iteratedDeriv_affine]
        _ = ((iteratedFDeriv ℝ 2 f z) fun _ => x) := by simp
        _ = ((fderiv ℝ (fderiv ℝ f) z) x) x := by
          rw [iteratedFDeriv_two_apply]
    rw [← h_deriv2_g]
    exact h_deriv2_nonneg 0
  exact And.intro hsymm hnonneg

theorem logdet_le (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det ≤ Real.log A.det + (A⁻¹ * (B - A)).trace := by
  have hA_det_pos : 0 < A.det := hA.det_pos
  have hA_unit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA_det_pos.ne'
  set T := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A with hT_def
  set T' := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) B with hT'_def
  set Ti := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A⁻¹ with hTi_def
  have hT_sadj : IsSelfAdjoint T := by
    rw [hT_def]
    have h_herm : A.IsHermitian := Matrix.PosDef.isHermitian hA
    have h_symm : (Matrix.toEuclideanLin A).IsSymmetric :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr h_herm)
    have h_symm' : IsSelfAdjoint (Matrix.toEuclideanLin A) :=
      ((LinearMap.isSymmetric_iff_isSelfAdjoint (Matrix.toEuclideanLin A)).mp h_symm)
    apply (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A)).mp
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A] using h_symm'
  have hT'_sadj : IsSelfAdjoint T' := by
    rw [hT'_def]
    have h_herm : B.IsHermitian := Matrix.PosDef.isHermitian hB
    have h_symm : (Matrix.toEuclideanLin B).IsSymmetric :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr h_herm)
    have h_symm' : IsSelfAdjoint (Matrix.toEuclideanLin B) :=
      ((LinearMap.isSymmetric_iff_isSelfAdjoint (Matrix.toEuclideanLin B)).mp h_symm)
    apply (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) B)).mp
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin B] using h_symm'
  have hT_pos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v := by
    intro v hv
    rw [hT_def, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM A v]
    have hv' : v.ofLp ≠ 0 := by
      contrapose! hv
      exact (WithLp.ofLp_eq_zero 2).mp hv
    simpa using Matrix.PosDef.dotProduct_mulVec_pos hA hv'
  have hT'_pos : ∀ v, v ≠ 0 → 0 < inner ℝ (T' v) v := by
    intro v hv
    rw [hT'_def, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM B v]
    have hv' : v.ofLp ≠ 0 := by
      contrapose! hv
      exact (WithLp.ofLp_eq_zero 2).mp hv
    simpa using Matrix.PosDef.dotProduct_mulVec_pos hB hv'
  have h_inv : IsInvPair T Ti := by
    rw [hT_def, hTi_def]
    have h_mul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA_unit
    have h_mul' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA_unit
    have h_comp1 : ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A).comp
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A⁻¹) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
      calc
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A).comp
          ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A⁻¹) =
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (A * A⁻¹) := by
          exact ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_mul A A⁻¹).symm
        _ = (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) 1 := by rw [h_mul]
        _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
          exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_one
    have h_comp2 : ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A⁻¹).comp
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
      calc
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A⁻¹).comp
          ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A) =
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (A⁻¹ * A) := by
          exact ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_mul A⁻¹ A).symm
        _ = (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) 1 := by rw [h_mul']
        _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
          exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_one
    exact And.intro h_comp1 h_comp2
  have h_logdet := logDetConcave d T T' Ti hT_sadj hT'_sadj hT_pos hT'_pos h_inv
  -- h_logdet : Real.log (LinearMap.det (T' : _ →ₗ[ℝ] _)) ≤
  --   Real.log (LinearMap.det (T : _ →ₗ[ℝ] _)) +
  --   LinearMap.trace ℝ _ ((Ti.comp (T' - T) : _ →L[ℝ] _) : _ →ₗ[ℝ] _)
  have h_det_T : LinearMap.det (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = A.det := by
    rw [hT_def]
    -- LinearMap.det (↑(toEuclideanCLM A) : _ →ₗ[ℝ] _) = A.det
    -- Use coe_toEuclideanCLM_eq_toEuclideanLin and det_toLin
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.det_toLin]
  have h_det_T' : LinearMap.det (T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = B.det := by
    rw [hT'_def]
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin B]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [LinearMap.det_toLin]
  have h_trace : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d))
      ((Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = (A⁻¹ * (B - A)).trace := by
    -- First, rewrite Ti.comp (T' - T) to toEuclideanCLM (A⁻¹ * (B - A))
    have h_comp : (Ti.comp (T' - T) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) =
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (A⁻¹ * (B - A)) := by
      rw [hTi_def, hT'_def, hT_def]
      have h_sub : ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) B - (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A) =
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (B - A) :=
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_sub B A).symm
      rw [h_sub]
      exact ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).map_mul A⁻¹ (B - A)).symm
    rw [h_comp]
    -- Now: LinearMap.trace ℝ _ (↑(toEuclideanCLM (A⁻¹ * (B - A))) : _ →ₗ[ℝ] _) = (A⁻¹ * (B - A)).trace
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A⁻¹ * (B - A))]
    -- Now: LinearMap.trace ℝ _ (toEuclideanLin (A⁻¹ * (B - A))) = (A⁻¹ * (B - A)).trace
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    -- Now: LinearMap.trace ℝ _ (toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (A⁻¹ * (B - A))) = (A⁻¹ * (B - A)).trace
    rw [Matrix.trace_toLin_eq (A⁻¹ * (B - A)) (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  -- Now rewrite h_logdet using these equalities
  rw [h_det_T, h_det_T', h_trace] at h_logdet
  exact h_logdet

theorem trace_mul_nonneg (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  set U := hA.isHermitian.eigenvectorUnitary with hU_def
  set D := diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues : Fin d → ℝ) with hD_def
  have h_eq : A = U.val * D * star U.val := by
    have h := hA.isHermitian.spectral_theorem
    simpa [hU_def, hD_def] using h
  rw [h_eq]
  -- Goal: 0 ≤ trace ((U.val * D * star U.val) * B)
  -- Using cyclic property: trace ((U * D * Uᴴ) * B) = trace (D * Uᴴ * B * U)
  have h_trace1 : (U.val * D * star U.val * B).trace =
      (D * (star U.val * B * U.val)).trace := by
    calc
      (U.val * D * star U.val * B).trace =
          ((U.val * D) * (star U.val * B)).trace := by simp [Matrix.mul_assoc]
      _ = ((star U.val * B) * (U.val * D)).trace := by rw [Matrix.trace_mul_comm]
      _ = (star U.val * B * U.val * D).trace := by simp [Matrix.mul_assoc]
      _ = (D * (star U.val * B * U.val)).trace := by rw [Matrix.trace_mul_comm]
  rw [h_trace1]
  set C := star U.val * B * U.val with hC_def
  have hC_psd : C.PosSemidef :=
    hB.mul_mul_conjTranspose_same (star U.val)
  have h_trace2 : (D * C).trace = ∑ i : Fin d, (RCLike.ofReal (hA.isHermitian.eigenvalues i)) * (C i i) := by
    rw [hD_def, hC_def]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [h_trace2]
  refine Finset.sum_nonneg fun i _ => ?_
  have h_eigen_nonneg : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
  have h_diag_nonneg : 0 ≤ C i i := hC_psd.diag_nonneg
  have h_ofReal_nonneg : 0 ≤ (RCLike.ofReal (hA.isHermitian.eigenvalues i) : ℝ) := by
    simpa using h_eigen_nonneg
  exact mul_nonneg h_ofReal_nonneg h_diag_nonneg

theorem dot_mulVec_symm {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have hT : Mᵀ = M := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq
  have hv : x ᵥ* M = M *ᵥ x := by
    conv_lhs => rw [← hT]
    exact Matrix.vecMul_transpose M x
  rw [Matrix.dotProduct_mulVec, hv, dotProduct_comm]


theorem inv_antitone (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  have hAu : IsUnit A.det := hA.det_pos.ne'.isUnit
  have hBu : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hAh : A.IsHermitian := hA.isHermitian
  have hBh : B.IsHermitian := hB.isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.inv.isHermitian.sub hB.inv.isHermitian) ?_
  intro x
  simp only [star_trivial]
  set y := B⁻¹ *ᵥ x with hy
  set z := A⁻¹ *ᵥ x with hz
  have hBy : B *ᵥ y = x := by rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hBu, Matrix.one_mulVec]
  have hAz : A *ᵥ z = x := by rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAu, Matrix.one_mulVec]
  have h1 : 0 ≤ (y - z) ⬝ᵥ (A *ᵥ (y - z)) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - z)
  have h2 : 0 ≤ y ⬝ᵥ ((B - A) *ᵥ y) := by simpa using hAB.dotProduct_mulVec_nonneg y
  rw [Matrix.sub_mulVec, dotProduct_sub, hBy] at h2
  rw [Matrix.mulVec_sub, hAz, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h1
  have hsym := dot_mulVec_symm hAh z y
  rw [hAz] at hsym
  rw [Matrix.sub_mulVec, dotProduct_sub, ← hy, ← hz]
  have e1 : x ⬝ᵥ z = z ⬝ᵥ x := dotProduct_comm _ _
  have e2 : x ⬝ᵥ y = y ⬝ᵥ x := dotProduct_comm _ _
  linarith

theorem play_mem (Kt : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (hconv : Convex ℝ Kt) (hcl : IsClosed Kt)
    (hball : Metric.closedBall 0 1 ⊆ Kt) (hε0 : 0 < ε) (hε1 : ε < 1) (x : EuclideanSpace ℝ (Fin d)) :
    (1 - ε)⁻¹ • ((max 1 (gauge Kt x / (1 - ε)))⁻¹ • x) ∈ Kt := by
  have hε0' : 0 < 1 - ε := by linarith
  have hball_mem_nhds : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hKt_mem_nhds : Kt ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset hball_mem_nhds hball
  have hgauge_le_one_iff : gauge Kt ((1 - ε)⁻¹ • ((max 1 (gauge Kt x / (1 - ε)))⁻¹ • x)) ≤ 1 ↔
    ((1 - ε)⁻¹ • ((max 1 (gauge Kt x / (1 - ε)))⁻¹ • x)) ∈ closure Kt :=
    gauge_le_one_iff_mem_closure hconv hKt_mem_nhds
  have hmem_closure : ((1 - ε)⁻¹ • ((max 1 (gauge Kt x / (1 - ε)))⁻¹ • x)) ∈ closure Kt := by
    rw [← hgauge_le_one_iff]
    set p := max 1 (gauge Kt x / (1 - ε)) with hp
    have hp_pos : 0 < p := by
      have h1 : (0 : ℝ) < 1 := by norm_num
      have h_one_le_p : (1 : ℝ) ≤ p := le_max_left _ _
      linarith
    have hgauge_nonneg : 0 ≤ gauge Kt x := gauge_nonneg x
    have h_div_le_p : gauge Kt x / (1 - ε) ≤ p := le_max_right _ _
    have hgauge_le : gauge Kt x ≤ p * (1 - ε) := (div_le_iff₀ hε0').mp h_div_le_p
    calc
      gauge Kt ((1 - ε)⁻¹ • (p⁻¹ • x))
          = (1 - ε)⁻¹ • gauge Kt (p⁻¹ • x) := by
            rw [gauge_smul_of_nonneg (by positivity : 0 ≤ (1 - ε)⁻¹)]
      _ = (1 - ε)⁻¹ • (p⁻¹ • gauge Kt x) := by
            rw [gauge_smul_of_nonneg (by positivity : 0 ≤ p⁻¹)]
      _ = ((1 - ε)⁻¹ * p⁻¹) • gauge Kt x := by rw [smul_smul]
      _ = ((1 - ε)⁻¹ * p⁻¹) * gauge Kt x := by rw [smul_eq_mul]
      _ ≤ ((1 - ε)⁻¹ * p⁻¹) * (p * (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left hgauge_le
        positivity
      _ = 1 := by
        field_simp [hε0'.ne.symm, hp_pos.ne.symm]
  rw [hcl.closure_eq] at hmem_closure
  exact hmem_closure

theorem ib_geo (Q0 : Set (Fin d → ℝ)) (r0 R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (k c m G D s : ℝ) (y : Fin d → ℝ) (hQ : Convex ℝ Q0) (hB : oBall 0 r0 ⊆ Q0) (hR : Q0 ⊆ oBall 0 R)
    (hP : P.IsHermitian) (hr0 : 0 ≤ r0) (hm : 0 < m) (hG : 0 < G) (hD : 0 < D) (hy : y ∈ Q0)
    (hΦ : df2Phi P b k y ≤ c - m) (hgrad : oNorm (P *ᵥ y - b) ≤ G) (hnorm : ∀ v, |df2Sq P v| ≤ D * (v ⬝ᵥ v))
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hsr : s * (R + r0) ≤ min (m / (2 * G)) (Real.sqrt (m / D))) :
    oBall ((1 - s) • y) (s * r0) ⊆ Q0 ∧ ∀ x ∈ oBall ((1 - s) • y) (s * r0), df2Phi P b k x ≤ c := by
  have hs_nonneg : 0 ≤ s := by linarith
  have h_symm : P.IsSymm := hP.isSymm
  have h_dot_comm {u v : Fin d → ℝ} : u ⬝ᵥ P *ᵥ v = v ⬝ᵥ P *ᵥ u :=
    h_symm.dotProduct_mulVec_comm
  have h_mulVec_dot_comm (u v : Fin d → ℝ) : (P *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (P *ᵥ v) := by
    calc
      (P *ᵥ u) ⬝ᵥ v = (u ᵥ* Pᵀ) ⬝ᵥ v := by rw [Matrix.vecMul_transpose]
      _ = u ⬝ᵥ (Pᵀ *ᵥ v) := by rw [← Matrix.dotProduct_mulVec u Pᵀ v]
      _ = u ⬝ᵥ (P *ᵥ v) := by rw [h_symm]
  -- Relate oNorm to the Euclidean norm on PiLp
  have h_onorm_eq_norm (v : Fin d → ℝ) : oNorm v = ‖WithLp.toLp 2 v‖ := by
    unfold oNorm
    have h_dot_nonneg : 0 ≤ v ⬝ᵥ v := by
      rw [dotProduct]
      refine Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have h_norm_sq : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
      calc
        ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 v).ofLp i‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
        _ = ∑ i, ‖v i‖ ^ 2 := by simp
        _ = ∑ i, (v i) ^ 2 := by simp
        _ = v ⬝ᵥ v := by simp [dotProduct, sq]
    have h_sq_eq : (Real.sqrt (v ⬝ᵥ v)) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt h_dot_nonneg
    have h_eq_sq : (Real.sqrt (v ⬝ᵥ v)) ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
      rw [h_sq_eq, h_norm_sq]
    have h_nonneg_norm : 0 ≤ ‖WithLp.toLp 2 v‖ := norm_nonneg _
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (v ⬝ᵥ v) := Real.sqrt_nonneg _
    nlinarith
  have h_onorm_nonneg (v : Fin d → ℝ) : 0 ≤ oNorm v := by
    rw [h_onorm_eq_norm v]
    exact norm_nonneg _
  have h_onorm_smul (c : ℝ) (v : Fin d → ℝ) : oNorm (c • v) = |c| * oNorm v := by
    rw [h_onorm_eq_norm (c • v), h_onorm_eq_norm v]
    simp [norm_smul]
  have h_onorm_add_le (a b : Fin d → ℝ) : oNorm (a + b) ≤ oNorm a + oNorm b := by
    rw [h_onorm_eq_norm (a + b), h_onorm_eq_norm a, h_onorm_eq_norm b]
    simpa using norm_add_le (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  have hy_norm : oNorm y ≤ R := by
    have hy_ball : y ∈ oBall (0 : Fin d → ℝ) R := hR hy
    simpa [oBall] using hy_ball
  have h_cauchy_schwarz (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ oNorm u * oNorm v := by
    rw [h_onorm_eq_norm u, h_onorm_eq_norm v]
    have h_abs_inner : |inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v)| ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ :=
      abs_real_inner_le_norm _ _
    have h_inner_eq : inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
      simp [inner, dotProduct, mul_comm]
    simpa [h_inner_eq] using h_abs_inner
  refine ⟨?_, ?_⟩
  · -- prove oBall ((1 - s) • y) (s * r0) ⊆ Q0
    intro x hx
    have hx_onorm : oNorm (x - ((1 - s) • y)) ≤ s * r0 := hx
    set b' := s⁻¹ • (x - ((1 - s) • y)) with hb'_def
    have hb'_onorm : oNorm b' ≤ r0 := by
      rw [hb'_def, h_onorm_smul]
      have h_abs_inv_s : |s⁻¹| = s⁻¹ := abs_of_pos (by positivity : 0 < s⁻¹)
      rw [h_abs_inv_s]
      calc
        s⁻¹ * oNorm (x - ((1 - s) • y)) ≤ s⁻¹ * (s * r0) :=
          mul_le_mul_of_nonneg_left hx_onorm (by positivity : 0 ≤ s⁻¹)
        _ = r0 := by field_simp [ne_of_gt hs0]
    have hb'_mem_ball : b' ∈ oBall (0 : Fin d → ℝ) r0 := by
      simpa [oBall] using hb'_onorm
    have hb'_mem_Q0 : b' ∈ Q0 := hB hb'_mem_ball
    -- x = (1 - s) • y + s • b'
    have hx_eq : x = (1 - s) • y + s • b' := by
      dsimp [b']
      calc
        x = ((1 - s) • y) + (x - ((1 - s) • y)) := by abel
        _ = ((1 - s) • y) + s • (s⁻¹ • (x - ((1 - s) • y))) := by
          rw [smul_inv_smul₀ (ne_of_gt hs0) (x - ((1 - s) • y))]
        _ = (1 - s) • y + s • b' := rfl
    rw [hx_eq]
    have h_lineMap : (1 - s) • y + s • b' = (AffineMap.lineMap y b') s := by
      rw [AffineMap.lineMap_apply]
      simp [vadd_eq_add, vsub_eq_sub]
      ext i
      simp
      ring
    rw [h_lineMap]
    apply hQ.lineMap_mem hy hb'_mem_Q0
    constructor
    · exact hs_nonneg
    · exact hs1
  · -- prove ∀ x ∈ oBall ((1 - s) • y) (s * r0), df2Phi P b k x ≤ c
    intro x hx
    have hx_onorm : oNorm (x - ((1 - s) • y)) ≤ s * r0 := hx
    set v := x - y with hv_def
    have hx_eq : x = y + v := by
      dsimp [v]
      abel
    rw [hx_eq]
    -- expand df2Phi P b k (y + v)
    have h_expand : df2Phi P b k (y + v) = df2Phi P b k y + (P *ᵥ y - b) ⬝ᵥ v + (1/2) * df2Sq P v := by
      dsimp [df2Phi, df2Sq]
      calc
        1 / 2 * ((y + v) ⬝ᵥ (P *ᵥ (y + v))) - b ⬝ᵥ (y + v) + k
            = 1 / 2 * ((y ⬝ᵥ (P *ᵥ y) + y ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ y) + v ⬝ᵥ (P *ᵥ v))) - (b ⬝ᵥ y + b ⬝ᵥ v) + k := by
          simp [dotProduct_add, mulVec_add, add_assoc, add_comm, add_left_comm]
        _ = 1 / 2 * (y ⬝ᵥ (P *ᵥ y) + y ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ y) + v ⬝ᵥ (P *ᵥ v)) - b ⬝ᵥ y - b ⬝ᵥ v + k := by ring
        _ = 1 / 2 * (y ⬝ᵥ (P *ᵥ y) + (y ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ y)) + v ⬝ᵥ (P *ᵥ v)) - b ⬝ᵥ y - b ⬝ᵥ v + k := by ring
        _ = 1 / 2 * (y ⬝ᵥ (P *ᵥ y) + (v ⬝ᵥ (P *ᵥ y) + y ⬝ᵥ (P *ᵥ v)) + v ⬝ᵥ (P *ᵥ v)) - b ⬝ᵥ y - b ⬝ᵥ v + k := by
          rw [add_comm (y ⬝ᵥ (P *ᵥ v))]
        _ = 1 / 2 * (y ⬝ᵥ (P *ᵥ y) + (y ⬝ᵥ (P *ᵥ v) + y ⬝ᵥ (P *ᵥ v)) + v ⬝ᵥ (P *ᵥ v)) - b ⬝ᵥ y - b ⬝ᵥ v + k := by
          rw [h_dot_comm (u := y) (v := v)]
        _ = 1 / 2 * (y ⬝ᵥ (P *ᵥ y) + 2 * (y ⬝ᵥ (P *ᵥ v)) + v ⬝ᵥ (P *ᵥ v)) - b ⬝ᵥ y - b ⬝ᵥ v + k := by ring
        _ = (1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k) + (y ⬝ᵥ (P *ᵥ v) - b ⬝ᵥ v) + (1 / 2 * (v ⬝ᵥ (P *ᵥ v))) := by ring
        _ = df2Phi P b k y + (P *ᵥ y - b) ⬝ᵥ v + (1/2) * df2Sq P v := by
          simp [df2Phi, df2Sq, h_mulVec_dot_comm]
    rw [h_expand]
    -- Now we need to bound (P *ᵥ y - b) ⬝ᵥ v + (1/2) * df2Sq P v ≤ m
    -- First, bound v's norm
    have hv_onorm_le : oNorm v ≤ s * (R + r0) := by
      have h_second_term : oNorm (((1 - s) • y) - y) ≤ s * R := by
        calc
          oNorm (((1 - s) • y) - y) = oNorm ((-s) • y) := by
            unfold oNorm
            have h : (((1 - s) • y) - y) ⬝ᵥ (((1 - s) • y) - y) = ((-s) • y) ⬝ᵥ ((-s) • y) := by
              simp
              ring
            rw [h]
          _ = |-s| * oNorm y := h_onorm_smul (-s) y
          _ = s * oNorm y := by simp [abs_of_pos hs0]
          _ ≤ s * R := mul_le_mul_of_nonneg_left hy_norm hs_nonneg
      calc
        oNorm v = oNorm ((x - ((1 - s) • y)) + (((1 - s) • y) - y)) := by
          dsimp [v]
          abel
        _ ≤ oNorm (x - ((1 - s) • y)) + oNorm (((1 - s) • y) - y) := h_onorm_add_le _ _
        _ ≤ (s * r0) + (s * R) := add_le_add hx_onorm h_second_term
        _ = s * (R + r0) := by ring
    have h_v_norm_bound1 : oNorm v ≤ m / (2 * G) := by
      have h_le_min : s * (R + r0) ≤ m / (2 * G) :=
        le_of_le_min_left hsr
      linarith
    have h_v_norm_bound2 : oNorm v ≤ Real.sqrt (m / D) := by
      have h_le_min : s * (R + r0) ≤ Real.sqrt (m / D) :=
        le_of_le_min_right hsr
      linarith
    -- Now bound the two terms
    have h_term1 : (P *ᵥ y - b) ⬝ᵥ v ≤ m / 2 := by
      have h_cs : (P *ᵥ y - b) ⬝ᵥ v ≤ |(P *ᵥ y - b) ⬝ᵥ v| := le_abs_self _
      have h_abs_cs : |(P *ᵥ y - b) ⬝ᵥ v| ≤ oNorm (P *ᵥ y - b) * oNorm v := h_cauchy_schwarz _ _
      have h_grad_bound : oNorm (P *ᵥ y - b) * oNorm v ≤ G * oNorm v :=
        mul_le_mul_of_nonneg_right hgrad (h_onorm_nonneg _)
      have h_v_bound : G * oNorm v ≤ G * (m / (2 * G)) :=
        mul_le_mul_of_nonneg_left h_v_norm_bound1 (by linarith)
      have h_G_cancel : G * (m / (2 * G)) = m / 2 := by
        field_simp [hG.ne.symm]
      calc
        (P *ᵥ y - b) ⬝ᵥ v ≤ |(P *ᵥ y - b) ⬝ᵥ v| := h_cs
        _ ≤ oNorm (P *ᵥ y - b) * oNorm v := h_abs_cs
        _ ≤ G * oNorm v := h_grad_bound
        _ ≤ G * (m / (2 * G)) := h_v_bound
        _ = m / 2 := h_G_cancel
    have h_term2 : (1/2) * df2Sq P v ≤ m / 2 := by
      have h_df2Sq_bound : df2Sq P v ≤ D * (v ⬝ᵥ v) := by
        have h_abs := hnorm v
        have h_abs_le : df2Sq P v ≤ |df2Sq P v| := le_abs_self _
        linarith
      have h_onorm_sq_eq : oNorm v ^ 2 = v ⬝ᵥ v := by
        rw [h_onorm_eq_norm v]
        have h := PiLp.norm_sq_eq_of_L2 (β := fun (_ : Fin d) => ℝ) (WithLp.toLp 2 v)
        simpa [dotProduct, sq] using h
      have h_onorm_sq_bound : oNorm v ^ 2 ≤ m / D := by
        have h_nonneg_div : 0 ≤ m / D := by positivity
        calc
          oNorm v ^ 2 ≤ (Real.sqrt (m / D)) ^ 2 := by
            nlinarith [h_onorm_nonneg v, h_v_norm_bound2]
          _ = m / D := Real.sq_sqrt h_nonneg_div
      calc
        (1/2) * df2Sq P v ≤ (1/2) * (D * (v ⬝ᵥ v)) := by nlinarith
        _ = (1/2) * D * (v ⬝ᵥ v) := by ring
        _ = (1/2) * D * (oNorm v ^ 2) := by rw [h_onorm_sq_eq]
        _ ≤ (1/2) * D * (m / D) := by nlinarith
        _ = m / 2 := by
          field_simp [hD.ne.symm]
    -- Combine: df2Phi P b k y + term1 + term2 ≤ (c - m) + m/2 + m/2 = c
    nlinarith

theorem inv_norm_le (P S : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hP : (P - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) (hSP : S * P = 1) (v : Fin d → ℝ) :
    oNorm (S *ᵥ v) ≤ oNorm v / δ := by
  -- Step 1: Get P * S = 1 from S * P = 1
  have hPS : P * S = 1 := by
    have h_inv : Invertible P := invertibleOfLeftInverse P S hSP
    have h_eq : P⁻¹ = S := Matrix.inv_eq_left_inv hSP
    have h_mul_inv : P * P⁻¹ = 1 := by
      have := Matrix.mul_inv_cancel_right_of_invertible (A := P) (B := (1 : Matrix (Fin d) (Fin d) ℝ))
      simpa [Matrix.one_mul] using this
    calc
      P * S = P * P⁻¹ := by rw [h_eq]
      _ = 1 := h_mul_inv
  -- Step 2: PSD inequality: x ⬝ᵥ (P *ᵥ x) ≥ δ * (x ⬝ᵥ x) for all x
  have hP_nonneg : ∀ x : Fin d → ℝ, 0 ≤ star x ⬝ᵥ ((P - δ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hP
  have hP_nonneg' : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ ((P - δ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x) := by
    intro x
    simpa using hP_nonneg x
  have hP_ineq : ∀ x : Fin d → ℝ, x ⬝ᵥ (P *ᵥ x) ≥ δ * (x ⬝ᵥ x) := by
    intro x
    have h := hP_nonneg' x
    have h_expand : (P - δ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x = P *ᵥ x - (δ • x) := by
      calc
        (P - δ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x = P *ᵥ x - (δ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x := by
          rw [Matrix.sub_mulVec]
        _ = P *ᵥ x - δ • ((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ x) := by rw [Matrix.smul_mulVec]
        _ = P *ᵥ x - δ • x := by rw [Matrix.one_mulVec]
    rw [h_expand] at h
    rw [dotProduct_sub] at h
    rw [dotProduct_smul] at h
    -- h : 0 ≤ x ⬝ᵥ (P *ᵥ x) - δ • (x ⬝ᵥ x)
    -- δ • (x ⬝ᵥ x) = δ * (x ⬝ᵥ x)
    simpa [smul_eq_mul] using h
  -- Step 3: Apply the inequality with x = S *ᵥ v
  set x := S *ᵥ v with hx
  have h_apply : x ⬝ᵥ (P *ᵥ x) ≥ δ * (x ⬝ᵥ x) := hP_ineq x
  have h_Px_eq_v : P *ᵥ x = v := by
    calc
      P *ᵥ x = P *ᵥ (S *ᵥ v) := rfl
      _ = (P * S) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ v := by rw [hPS]
      _ = v := by rw [Matrix.one_mulVec]
  rw [h_Px_eq_v] at h_apply
  -- h_apply : (S *ᵥ v) ⬝ᵥ v ≥ δ * ((S *ᵥ v) ⬝ᵥ (S *ᵥ v))
  -- Step 4: Cauchy-Schwarz inequality for dot product
  have h_cauchy_schwarz : (S *ᵥ v) ⬝ᵥ v ≤ oNorm (S *ᵥ v) * oNorm v := by
    have h_sq : ((S *ᵥ v) ⬝ᵥ v) ^ 2 ≤ ((S *ᵥ v) ⬝ᵥ (S *ᵥ v)) * (v ⬝ᵥ v) := by
      rw [dotProduct, dotProduct, dotProduct]
      simpa [sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (S *ᵥ v) v
    have h_nonneg1 : 0 ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by
      rw [dotProduct]
      apply Finset.sum_nonneg
      intro i _
      apply mul_self_nonneg
    have h_nonneg2 : 0 ≤ v ⬝ᵥ v := by
      rw [dotProduct]
      apply Finset.sum_nonneg
      intro i _
      apply mul_self_nonneg
    dsimp [oNorm]
    by_cases h_nonneg_dot : 0 ≤ (S *ᵥ v) ⬝ᵥ v
    · -- Use Real.le_sqrt: x ≤ sqrt(y) ↔ x^2 ≤ y for x, y ≥ 0
      have h_sqrt : (S *ᵥ v) ⬝ᵥ v ≤ Real.sqrt (((S *ᵥ v) ⬝ᵥ (S *ᵥ v)) * (v ⬝ᵥ v)) :=
        (Real.le_sqrt h_nonneg_dot (mul_nonneg h_nonneg1 h_nonneg2)).mpr h_sq
      rw [Real.sqrt_mul h_nonneg1] at h_sqrt
      exact h_sqrt
    · have h_nonneg_sqrt : 0 ≤ Real.sqrt ((S *ᵥ v) ⬝ᵥ (S *ᵥ v)) * Real.sqrt (v ⬝ᵥ v) := by
        apply mul_nonneg
        · apply Real.sqrt_nonneg _
        · apply Real.sqrt_nonneg _
      linarith
  -- Step 5: Combine the inequalities
  have h_main : δ * (oNorm (S *ᵥ v) ^ 2) ≤ oNorm (S *ᵥ v) * oNorm v := by
    have h_sq_eq : oNorm (S *ᵥ v) ^ 2 = (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by
      dsimp [oNorm]
      have h_nonneg : 0 ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by
        rw [dotProduct]
        apply Finset.sum_nonneg
        intro i _
        apply mul_self_nonneg
      rw [Real.sq_sqrt h_nonneg]
    rw [h_sq_eq]
    -- h_apply : (S *ᵥ v) ⬝ᵥ v ≥ δ * ((S *ᵥ v) ⬝ᵥ (S *ᵥ v))
    -- h_cauchy_schwarz : (S *ᵥ v) ⬝ᵥ v ≤ oNorm (S *ᵥ v) * oNorm v
    -- So δ * ((S *ᵥ v) ⬝ᵥ (S *ᵥ v)) ≤ (S *ᵥ v) ⬝ᵥ v ≤ oNorm (S *ᵥ v) * oNorm v
    linarith
  -- Step 6: Divide by oNorm (S *ᵥ v) (handle zero case)
  by_cases h_zero : oNorm (S *ᵥ v) = 0
  · -- If oNorm (S *ᵥ v) = 0, then LHS = 0 ≤ RHS (since oNorm v ≥ 0 and δ > 0)
    rw [h_zero]
    have h_nonneg_v : 0 ≤ oNorm v := by
      dsimp [oNorm]
      apply Real.sqrt_nonneg _
    have h_nonneg_δ : 0 ≤ δ := le_of_lt hδ
    have : 0 ≤ oNorm v / δ := div_nonneg h_nonneg_v h_nonneg_δ
    linarith
  · -- oNorm (S *ᵥ v) > 0, we can divide
    have h_nonneg_a : 0 ≤ oNorm (S *ᵥ v) := by
      dsimp [oNorm]
      apply Real.sqrt_nonneg _
    have h_pos : 0 < oNorm (S *ᵥ v) := by
      by_contra! hle
      apply h_zero
      linarith
    -- From h_main: δ * a^2 ≤ a * b where a = oNorm (S *ᵥ v), b = oNorm v
    -- Since a > 0, we can divide by a: δ * a ≤ b
    have h_div : δ * oNorm (S *ᵥ v) ≤ oNorm v := by
      nlinarith
    -- Now a ≤ b / δ
    -- From δ * a ≤ b, multiply both sides by δ⁻¹ (which is positive)
    have h_inv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
    have h_result : oNorm (S *ᵥ v) ≤ oNorm v * δ⁻¹ := by
      calc
        oNorm (S *ᵥ v) = δ⁻¹ * (δ * oNorm (S *ᵥ v)) := by field_simp [ne_of_gt hδ]
        _ ≤ δ⁻¹ * oNorm v := by gcongr
        _ = oNorm v * δ⁻¹ := mul_comm _ _
    -- Convert to division form
    rw [div_eq_mul_inv]
    exact h_result

theorem keps_basic (Kt : Set (EuclideanSpace ℝ (Fin d))) (ε R : ℝ) (hconv : Convex ℝ Kt) (hcl : IsClosed Kt)
    (hball : Metric.closedBall 0 1 ⊆ Kt) (hR : Kt ⊆ Metric.closedBall 0 R) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Convex ℝ (df2KepsOf Kt ε) ∧ IsClosed (df2KepsOf Kt ε) ∧ oBall 0 (1 - ε) ⊆ df2KepsOf Kt ε ∧
      df2KepsOf Kt ε ⊆ oBall 0 R := by
  have hεpos : 0 < (1 : ℝ) - ε := by linarith
  have hεpos' : (1 : ℝ) - ε ≠ 0 := by linarith
  have hε_nonneg : 0 ≤ (1 : ℝ) - ε := by linarith
  -- Since Metric.closedBall 0 1 ⊆ Kt ⊆ Metric.closedBall 0 R, we have R ≥ 0
  have hR_nonneg : 0 ≤ R := by
    have hmem : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall 0 1 := by
      simp
    have hmem' : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := by
      exact hR (hball hmem)
    rcases Metric.mem_closedBall.mp hmem' with h
    -- Actually, Metric.mem_closedBall gives dist x y ≤ r, and dist 0 0 = 0
    -- So we get 0 ≤ R
    simpa [dist_eq_norm, sub_zero] using h
  -- The linear map φ(y) = WithLp.toLp 2 ((1-ε)⁻¹ • y)
  let φ : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm ∘ₗ
      (((1 : ℝ) - ε)⁻¹ • (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)))
  have hφ_def (y : Fin d → ℝ) : φ y = WithLp.toLp 2 (((1 : ℝ) - ε)⁻¹ • y) := by
    simp [φ, WithLp.toLp_smul]
  have h_df2KepsOf_eq : df2KepsOf Kt ε = φ ⁻¹' Kt := by
    ext y
    simp [df2KepsOf, hφ_def]
  rw [h_df2KepsOf_eq]
  have h_cont : Continuous φ :=
    LinearMap.continuous_of_finiteDimensional φ
  have h_conv : Convex ℝ (φ ⁻¹' Kt) := Convex.linear_preimage hconv φ
  have h_closed : IsClosed (φ ⁻¹' Kt) := hcl.preimage h_cont
  have h_norm_eq (z : Fin d → ℝ) : ‖WithLp.toLp 2 z‖ = oNorm z := by
    dsimp [oNorm]
    rw [norm_eq_sqrt_real_inner]
    simp [inner]
    rfl
  -- Helper lemma: oNorm (c • y) = c * oNorm y for c ≥ 0
  have h_oNorm_smul (c : ℝ) (y : Fin d → ℝ) (hc : 0 ≤ c) : oNorm (c • y) = c * oNorm y := by
    dsimp [oNorm]
    simp [dotProduct]
    have hsum : (∑ i, (c * y i) * (c * y i)) = c ^ 2 * (∑ i, y i * y i) := by
      simp [Finset.mul_sum, mul_comm, mul_left_comm, pow_two]
    rw [hsum, Real.sqrt_mul (by positivity : 0 ≤ c ^ 2), Real.sqrt_sq hc]
  have h_ball1 : oBall 0 ((1 : ℝ) - ε) ⊆ φ ⁻¹' Kt := by
    intro y hy
    rw [Set.mem_preimage, hφ_def]
    -- hy : y ∈ oBall 0 ((1 : ℝ) - ε), i.e., oNorm y ≤ (1 : ℝ) - ε
    have hy' : oNorm y ≤ (1 : ℝ) - ε := by simpa [oBall, sub_zero] using hy
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [h_norm_eq]
    -- Need: oNorm (((1 : ℝ) - ε)⁻¹ • y) ≤ 1
    have h_inv_nonneg : 0 ≤ ((1 : ℝ) - ε)⁻¹ := by positivity
    calc
      oNorm (((1 : ℝ) - ε)⁻¹ • y) = ((1 : ℝ) - ε)⁻¹ * oNorm y := h_oNorm_smul _ _ h_inv_nonneg
      _ ≤ ((1 : ℝ) - ε)⁻¹ * ((1 : ℝ) - ε) := by gcongr
      _ = 1 := by field_simp [hεpos'.symm]
  have h_ball2 : φ ⁻¹' Kt ⊆ oBall 0 R := by
    intro y hy
    rw [Set.mem_preimage, hφ_def] at hy
    -- hy : WithLp.toLp 2 (((1 : ℝ) - ε)⁻¹ • y) ∈ Kt
    have hy' : WithLp.toLp 2 (((1 : ℝ) - ε)⁻¹ • y) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R :=
      hR hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy'
    rw [h_norm_eq] at hy'
    -- hy' : oNorm (((1 : ℝ) - ε)⁻¹ • y) ≤ R
    -- Need: y ∈ oBall 0 R, i.e., oNorm y ≤ R
    have h_inv_nonneg : 0 ≤ ((1 : ℝ) - ε)⁻¹ := by positivity
    have h_ineq : oNorm y ≤ R := by
      calc
        oNorm y = ((1 : ℝ) - ε) * oNorm (((1 : ℝ) - ε)⁻¹ • y) := by
          have := h_oNorm_smul ((1 : ℝ) - ε)⁻¹ y h_inv_nonneg
          field_simp [hεpos'.symm] at this ⊢
          linarith
        _ ≤ ((1 : ℝ) - ε) * R := by gcongr
        _ ≤ 1 * R := by gcongr; linarith
        _ = R := by simp
    simpa [oBall, sub_zero] using h_ineq
  exact ⟨h_conv, h_closed, h_ball1, h_ball2⟩

theorem defect_arith (n : ℕ) (hn : 1 ≤ n) (R T D : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D) (hDb : D ^ 2 ≤ 4 * R ^ 2 * T) :
    D * Real.sqrt (2 * (1 / (16 * n ^ 2 * max 1 (4 * R ^ 2 * T)))) + 2 * (1 / (16 * n ^ 2 * max 1 (4 * R ^ 2 * T))) ≤
      1 / (2 * n) := by
  set m := (n : ℝ) with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact_mod_cast Nat.one_pos.trans_le hn
  have hm_ge_one : (1 : ℝ) ≤ m := by
    rw [hm_def]
    exact_mod_cast hn
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  set M := max 1 (4 * R ^ 2 * T) with hM_def
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM2 : 4 * R ^ 2 * T ≤ M := le_max_right _ _
  have hD2leM : D ^ 2 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  set e := 1 / (16 * m ^ 2 * M) with he_def
  have he_pos : 0 < e := by
    rw [he_def]
    refine div_pos (by norm_num) (by positivity)
  have h2e_nonneg : 0 ≤ 2 * e := by linarith
  -- Key inequality: D^2 * (2*e) ≤ 1/(8*m^2)
  have hDsq_mul : D ^ 2 * (2 * e) ≤ 1 / (8 * m ^ 2) := by
    calc
      D ^ 2 * (2 * e) = D ^ 2 * (2 * (1 / (16 * m ^ 2 * M))) := rfl
      _ = D ^ 2 * (1 / (8 * m ^ 2 * M)) := by ring
      _ = (D ^ 2) / (8 * m ^ 2 * M) := by ring
      _ ≤ M / (8 * m ^ 2 * M) := by
        refine div_le_div_of_nonneg_right hD2leM (by positivity)
      _ = 1 / (8 * m ^ 2) := by
        field_simp [hMpos.ne.symm]
  -- Bound the sqrt term
  have h_sqrt_term : D * Real.sqrt (2 * e) ≤ 1 / (2 * Real.sqrt 2 * m) := by
    calc
      D * Real.sqrt (2 * e) = Real.sqrt (D ^ 2) * Real.sqrt (2 * e) := by
        rw [Real.sqrt_sq hD]
      _ = Real.sqrt (D ^ 2 * (2 * e)) := by rw [Real.sqrt_mul (by positivity : 0 ≤ D ^ 2) (2 * e)]
      _ ≤ Real.sqrt (1 / (8 * m ^ 2)) := Real.sqrt_le_sqrt hDsq_mul
      _ = Real.sqrt 1 / Real.sqrt (8 * m ^ 2) := by rw [Real.sqrt_div (by norm_num : 0 ≤ (1 : ℝ)) _]
      _ = 1 / Real.sqrt (8 * m ^ 2) := by norm_num
      _ = 1 / (Real.sqrt 8 * Real.sqrt (m ^ 2)) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (8 : ℝ)) (m ^ 2)]
      _ = 1 / (Real.sqrt 8 * m) := by rw [Real.sqrt_sq hm_nonneg]
      _ = 1 / ((2 * Real.sqrt 2) * m) := by
        have h_sqrt8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
          calc
            Real.sqrt (8 : ℝ) = Real.sqrt (4 * 2) := by norm_num
            _ = Real.sqrt 4 * Real.sqrt 2 := Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) 2
            _ = 2 * Real.sqrt 2 := by norm_num
        rw [h_sqrt8]
      _ = 1 / (2 * Real.sqrt 2 * m) := by ring
  -- Bound the 2*e term
  have h_e_term : 2 * e ≤ 1 / (8 * m ^ 2) := by
    calc
      2 * e = 2 * (1 / (16 * m ^ 2 * M)) := rfl
      _ = 1 / (8 * m ^ 2 * M) := by ring
      _ ≤ 1 / (8 * m ^ 2) := by
        refine (one_div_le_one_div ?_ ?_).mpr ?_
        · positivity
        · positivity
        · nlinarith
  -- Combine the two bounds
  have h_sum : D * Real.sqrt (2 * e) + 2 * e ≤ 1 / (2 * Real.sqrt 2 * m) + 1 / (8 * m ^ 2) := by
    nlinarith
  -- Final inequality: 1/(2√2*m) + 1/(8*m^2) ≤ 1/(2*m)
  have h_final : 1 / (2 * Real.sqrt 2 * m) + 1 / (8 * m ^ 2) ≤ 1 / (2 * m) := by
    have h_sqrt2_le_two : Real.sqrt 2 ≤ 2 := by
      have h_sq : (Real.sqrt 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        calc
          (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
          _ ≤ 4 := by norm_num
          _ = (2 : ℝ) ^ 2 := by norm_num
      have h_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      nlinarith
    have h_sqrt2_sub_one_pos : 0 < Real.sqrt 2 - 1 := by
      have h : 1 < Real.sqrt 2 := by
        calc
          1 = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
          _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    -- Key identity: √2 / (√2 - 1) = 2 + √2
    have h_id : Real.sqrt 2 / (Real.sqrt 2 - 1) = 2 + Real.sqrt 2 := by
      field_simp [h_sqrt2_sub_one_pos.ne.symm]
      nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    -- Since m ≥ 1, we have 2 + √2 ≤ 4 ≤ 4*m
    have h_key : 2 + Real.sqrt 2 ≤ 4 * m := by
      have h1 : 2 + Real.sqrt 2 ≤ 4 := by linarith
      have h2 : 4 ≤ 4 * m := by nlinarith [hm_ge_one]
      linarith
    -- Therefore √2 / (√2 - 1) ≤ 4*m
    have h_div : Real.sqrt 2 / (Real.sqrt 2 - 1) ≤ 4 * m := by
      rw [h_id]
      exact h_key
    -- Multiply by (√2 - 1) > 0: √2 ≤ 4*m*(√2 - 1)
    have h_mul : Real.sqrt 2 ≤ 4 * m * (Real.sqrt 2 - 1) := by
      calc
        Real.sqrt 2 = (Real.sqrt 2 / (Real.sqrt 2 - 1)) * (Real.sqrt 2 - 1) := by
          field_simp [h_sqrt2_sub_one_pos.ne.symm]
        _ ≤ (4 * m) * (Real.sqrt 2 - 1) := by
          nlinarith
        _ = 4 * m * (Real.sqrt 2 - 1) := by ring
    -- Add 4*m to both sides: 4*m + √2 ≤ 4*m*√2
    have h_add : 4 * m + Real.sqrt 2 ≤ 4 * m * Real.sqrt 2 := by
      nlinarith
    -- Divide by √2 > 0: (4*m)/√2 + 1 ≤ 4*m
    have h_div2 : 4 * m / Real.sqrt 2 + 1 ≤ 4 * m := by
      calc
        4 * m / Real.sqrt 2 + 1 = (4 * m + Real.sqrt 2) / Real.sqrt 2 := by
          field_simp [h_sqrt2_pos.ne.symm]
        _ ≤ (4 * m * Real.sqrt 2) / Real.sqrt 2 := by
          refine div_le_div_of_nonneg_right h_add (by positivity)
        _ = 4 * m := by field_simp [h_sqrt2_pos.ne.symm]
    -- Divide by 8*m^2 > 0: 1/(2*√2*m) + 1/(8*m^2) ≤ 1/(2*m)
    calc
      1 / (2 * Real.sqrt 2 * m) + 1 / (8 * m ^ 2) = (4 * m / Real.sqrt 2 + 1) / (8 * m ^ 2) := by
        field_simp [hm_pos.ne.symm, h_sqrt2_pos.ne.symm]
        ring
      _ ≤ (4 * m) / (8 * m ^ 2) := by
        refine div_le_div_of_nonneg_right h_div2 (by positivity)
      _ = 1 / (2 * m) := by
        field_simp [hm_pos.ne.symm]
        ring
  -- Unfold e and conclude
  rw [he_def]
  linarith

theorem sq_cauchy (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) (a b : Fin d → ℝ) :
    (a ⬝ᵥ (P *ᵥ b)) ^ 2 ≤ df2Sq P a * df2Sq P b := by
  let B := P.toBilin'
  have h_symm_matrix : P.IsSymm := by
    rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, hP.1]
  have h_symm : P.toBilin'.IsSymm :=
    (Matrix.isSymm_toBilin'_iff_isSymm.2 h_symm_matrix)
  have h_nonneg : ∀ x : Fin d → ℝ, 0 ≤ B x x := by
    intro x
    have h := hP.2 (Finsupp.equivFunOnFinite.symm x)
    -- h : 0 ≤ (Finsupp.equivFunOnFinite.symm x).sum ...
    -- goal: 0 ≤ (B x) x = (P.toBilin' x) x
    -- Use Finsupp.sum_fintype to rewrite h, and Matrix.toBilin'_apply to rewrite the goal
    rw [Matrix.toBilin'_apply]
    -- goal: 0 ≤ ∑ i, ∑ j, x i * P i j * x j
    -- Now rewrite h using Finsupp.sum_fintype
    simpa [Finsupp.sum_fintype, Finsupp.coe_equivFunOnFinite_symm] using h
  have h := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le B h_nonneg a b
  -- h : (B a b) * (B b a) ≤ (B a a) * (B b b)
  have h_eq : B a b = B b a := h_symm.eq a b
  rw [← h_eq] at h
  -- h : (B a b) * (B a b) ≤ (B a a) * (B b b)
  have h_sq : (B a b) * (B a b) = (B a b) ^ 2 := by ring
  rw [h_sq] at h
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toBilin'_apply'] at h
  -- h : (a ⬝ᵥ (P *ᵥ b)) ^ 2 ≤ (a ⬝ᵥ (P *ᵥ a)) * (b ⬝ᵥ (P *ᵥ b))
  -- Now unfold df2Sq in the goal, not in h
  unfold df2Sq
  exact h

theorem psd_dot {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ (P *ᵥ v) := by
  simpa using hP.dotProduct_mulVec_nonneg v


theorem mulVec_norm_le (P : Matrix (Fin d) (Fin d) ℝ) (D : ℝ) (hP : P.PosSemidef)
    (hPD : (D • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) (v : Fin d → ℝ) : oNorm (P *ᵥ v) ≤ D * oNorm v := by
  have hD : ∀ x : Fin d → ℝ, x ⬝ᵥ (P *ᵥ x) ≤ D * (x ⬝ᵥ x) := by
    intro x
    have h := psd_dot hPD x
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] at h
    linarith
  have hsym : Pᵀ = P := by
    have h : Pᴴ = P := hP.1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  set w := P *ᵥ v with hw
  have hs : w ⬝ᵥ w = v ⬝ᵥ (P *ᵥ w) := by
    have hvm : v ᵥ* P = P *ᵥ v := by
      conv_lhs => rw [← hsym]
      exact Matrix.vecMul_transpose P v
    rw [Matrix.dotProduct_mulVec v P w, hvm]
  have hq0 : 0 ≤ v ⬝ᵥ (P *ᵥ v) := psd_dot hP v
  have hww0 : 0 ≤ w ⬝ᵥ w := by rw [hs]; exact hs ▸ (dotProduct_self_star_nonneg w).trans_eq (by simp)
  have hvv0 : 0 ≤ v ⬝ᵥ v := by simpa using dotProduct_self_star_nonneg v
  have hc := sq_cauchy P hP v w
  unfold df2Sq at hc
  rw [← hs] at hc
  have h1 := hD w
  have h2 := hD v
  have hss : (w ⬝ᵥ w) ≤ D ^ 2 * (v ⬝ᵥ v) := by
    rcases hww0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : (w ⬝ᵥ w) ^ 2 ≤ (D * (v ⬝ᵥ v)) * (D * (w ⬝ᵥ w)) := by
        calc (w ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ (P *ᵥ v)) * (w ⬝ᵥ (P *ᵥ w)) := hc
          _ ≤ (D * (v ⬝ᵥ v)) * (D * (w ⬝ᵥ w)) := by
            apply mul_le_mul h2 h1 (psd_dot hP w) (hq0.trans h2)
      nlinarith
  have hDv : 0 ≤ D * oNorm v := by
    unfold oNorm
    rcases hvv0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have : 0 ≤ D := by
        by_contra hneg; push Not at hneg; nlinarith
      positivity
  unfold oNorm at hDv ⊢
  exact Real.sqrt_le_iff.mpr ⟨hDv, by rw [mul_pow, Real.sq_sqrt hvv0]; exact hss⟩

theorem phi_convex (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) (b : Fin d → ℝ) (k c : ℝ)
    (Q : Set (Fin d → ℝ)) (hQ : Convex ℝ Q) (hQc : IsClosed Q) :
    ConvexOn ℝ Set.univ (df2Phi P b k) ∧ Continuous (df2Phi P b k) ∧ Convex ℝ {y | y ∈ Q ∧ df2Phi P b k y ≤ c} ∧
      IsClosed {y | y ∈ Q ∧ df2Phi P b k y ≤ c} := by
  have hq : ∀ v, 0 ≤ v ⬝ᵥ (P *ᵥ v) := fun v => sq_nonneg_of_psd hP v
  have hconv : ConvexOn ℝ Set.univ (df2Phi P b k) := by
    refine ⟨convex_univ, fun x _ y _ a a' ha ha' hs => ?_⟩
    obtain rfl : a' = 1 - a := by linarith
    have h := mul_nonneg (mul_nonneg ha ha') (hq (x - y))
    simp only [df2Phi, smul_eq_mul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
    nlinarith [h]
  have hcont : Continuous (df2Phi P b k) := by
    unfold df2Phi
    exact ((continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))).sub
      (continuous_const.dotProduct continuous_id)).add continuous_const
  refine ⟨hconv, hcont, ?_, ?_⟩
  · convert hQ.inter (hconv.convex_le c) using 1
    ext y; simp
  · exact hQc.inter (isClosed_le hcont (continuous_const : Continuous fun _ : Fin d → ℝ => c))

/-! ## Leaves -/

theorem exists_min_on {d : ℕ} (K : Set (Fin d → ℝ)) (R : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hK : IsClosed K) (hKR : K ⊆ oBall 0 R) (hne : K.Nonempty) (hf : Continuous f) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  have h_norm_le_oNorm : ∀ x : Fin d → ℝ, ‖x‖ ≤ oNorm x := by
    intro x
    have h_nonneg : 0 ≤ oNorm x := by
      rw [AdversarialBco.Poly.oNorm]
      exact Real.sqrt_nonneg _
    rw [pi_norm_le_iff_of_nonneg h_nonneg]
    intro i
    have hsq : (x i) ^ 2 ≤ x ⬝ᵥ x := by
      calc
        (x i) ^ 2 ≤ ∑ j : Fin d, (x j) ^ 2 :=
          Finset.single_le_sum (fun j hj => pow_two_nonneg (x j)) (Finset.mem_univ i)
        _ = x ⬝ᵥ x := by
          simp [dotProduct, pow_two]
    have h_abs : |x i| ≤ Real.sqrt (x ⬝ᵥ x) := Real.abs_le_sqrt hsq
    simpa [oNorm, Real.norm_eq_abs] using h_abs
  have h_compact : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded hK
    have h_ball_bounded : Bornology.IsBounded (oBall (d := d) 0 R) := by
      rw [Metric.isBounded_iff_subset_ball 0]
      refine ⟨R + 1, ?_⟩
      intro x hx
      have hx_norm : oNorm x ≤ R := by
        simpa [AdversarialBco.Poly.oBall] using hx
      have h_dist : dist x 0 < R + 1 := by
        calc
          dist x 0 = ‖x‖ := by simp
          _ ≤ oNorm x := h_norm_le_oNorm x
          _ ≤ R := hx_norm
          _ < R + 1 := by linarith
      exact h_dist
    exact Bornology.IsBounded.subset h_ball_bounded hKR
  exact h_compact.exists_isMinOn hne hf.continuousOn

lemma gb_oNorm_add_le {d : ℕ} (a b : Fin d → ℝ) : Real.sqrt ((a + b) ⬝ᵥ (a + b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  set A := a ⬝ᵥ a with hA
  set B := b ⬝ᵥ b with hB
  set C := a ⬝ᵥ b with hC
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [sq_nonneg (a i)]
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [sq_nonneg (b i)]
  have hCauchy : C ≤ Real.sqrt A * Real.sqrt B := by
    rw [hA, hB, hC]
    calc
      a ⬝ᵥ b = ∑ i : Fin d, a i * b i := by simp [dotProduct]
      _ = ∑ i ∈ Finset.univ, a i * b i := by simp
      _ ≤ Real.sqrt (∑ i ∈ Finset.univ, a i ^ 2) * Real.sqrt (∑ i ∈ Finset.univ, b i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d)) a b
      _ = Real.sqrt (∑ i : Fin d, a i ^ 2) * Real.sqrt (∑ i : Fin d, b i ^ 2) := by simp
      _ = Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by simp [dotProduct, sq]
  have h_sq_nonneg : 0 ≤ Real.sqrt A + Real.sqrt B := by
    nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B]
  have h_expand : (a + b) ⬝ᵥ (a + b) = A + 2*C + B := by
    calc
      (a + b) ⬝ᵥ (a + b) = ∑ i : Fin d, (a i + b i) * (a i + b i) := by simp [dotProduct]
      _ = ∑ i : Fin d, (a i * a i + 2 * a i * b i + b i * b i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring_nf
      _ = (∑ i : Fin d, a i * a i) + (∑ i : Fin d, 2 * a i * b i) + (∑ i : Fin d, b i * b i) := by
        simp [Finset.sum_add_distrib]
      _ = (a ⬝ᵥ a) + 2 * (a ⬝ᵥ b) + (b ⬝ᵥ b) := by
        simp [dotProduct, Finset.mul_sum]
        ring_nf
      _ = A + 2*C + B := by rw [hA, hB, hC]
  rw [h_expand]
  have h_sq : A + 2*C + B ≤ (Real.sqrt A + Real.sqrt B)^2 := by
    have h_expand_sq : (Real.sqrt A + Real.sqrt B)^2 = A + B + 2 * Real.sqrt A * Real.sqrt B := by
      calc
        (Real.sqrt A + Real.sqrt B)^2 = (Real.sqrt A)^2 + (Real.sqrt B)^2 + 2 * Real.sqrt A * Real.sqrt B := by ring
        _ = A + (Real.sqrt B)^2 + 2 * Real.sqrt A * Real.sqrt B := by rw [Real.sq_sqrt hA_nonneg]
        _ = A + B + 2 * Real.sqrt A * Real.sqrt B := by rw [Real.sq_sqrt hB_nonneg]
    rw [h_expand_sq]
    nlinarith
  have h_sqrt_sq : Real.sqrt ((Real.sqrt A + Real.sqrt B)^2) = Real.sqrt A + Real.sqrt B :=
    Real.sqrt_sq h_sq_nonneg
  calc
    Real.sqrt (A + 2*C + B) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B)^2) :=
      Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt A + Real.sqrt B := h_sqrt_sq

lemma gb_oNorm_sub_le {d : ℕ} (a b : Fin d → ℝ) : Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  have h_sub_eq_add : a - b = a + (-b) := by
    ext i; simp [sub_eq_add_neg]
  rw [h_sub_eq_add]
  calc
    Real.sqrt ((a + (-b)) ⬝ᵥ (a + (-b))) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt ((-b) ⬝ᵥ (-b)) :=
      gb_oNorm_add_le a (-b)
    _ = Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by simp [dotProduct]

lemma gb_oNorm_sum_le {d : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Fin d → ℝ) : Real.sqrt ((∑ i ∈ s, f i) ⬝ᵥ (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, Real.sqrt (f i ⬝ᵥ f i) := by
  induction' s using Finset.induction with i s his ih
  · simp
  · rw [Finset.sum_insert his]
    calc
      Real.sqrt ((f i + (∑ j ∈ s, f j)) ⬝ᵥ (f i + (∑ j ∈ s, f j))) ≤
          Real.sqrt (f i ⬝ᵥ f i) + Real.sqrt ((∑ j ∈ s, f j) ⬝ᵥ (∑ j ∈ s, f j)) :=
        gb_oNorm_add_le (f i) (∑ j ∈ s, f j)
      _ ≤ Real.sqrt (f i ⬝ᵥ f i) + ∑ j ∈ s, Real.sqrt (f j ⬝ᵥ f j) := by nlinarith
      _ = ∑ j ∈ insert i s, Real.sqrt (f j ⬝ᵥ f j) := by rw [Finset.sum_insert his]


theorem grad_bound {d : ℕ} (T : ℕ) (P0 : Matrix (Fin d) (Fin d) ℝ)
    (M : ℕ → Matrix (Fin d) (Fin d) ℝ) (μ : ℕ → Fin d → ℝ) (y : Fin d → ℝ) (R c0 : ℝ) (m : ℕ → ℝ)
    (hy : oNorm y ≤ R) (hμ : ∀ u < T, oNorm (μ u) ≤ R) (hP0 : ∀ v, oNorm (P0 *ᵥ v) ≤ c0 * oNorm v)
    (hM : ∀ u < T, ∀ v, oNorm (M u *ᵥ v) ≤ m u * oNorm v) (hc0 : 0 ≤ c0) (hm : ∀ u < T, 0 ≤ m u) :
    oNorm ((P0 + ∑ u ∈ Finset.range T, M u) *ᵥ y - ∑ u ∈ Finset.range T, M u *ᵥ μ u) ≤
      c0 * R + 2 * R * ∑ u ∈ Finset.range T, m u := by
  let S := P0 + ∑ u ∈ Finset.range T, M u
  let T_vec := ∑ u ∈ Finset.range T, M u *ᵥ μ u
  have h_expr : S *ᵥ y - T_vec = P0 *ᵥ y + ∑ u ∈ Finset.range T, (M u *ᵥ (y - μ u)) := by
    calc
      S *ᵥ y - T_vec = (P0 + ∑ u ∈ Finset.range T, M u) *ᵥ y - ∑ u ∈ Finset.range T, M u *ᵥ μ u := rfl
      _ = (P0 *ᵥ y + (∑ u ∈ Finset.range T, M u) *ᵥ y) - ∑ u ∈ Finset.range T, M u *ᵥ μ u := by
        rw [add_mulVec]
      _ = (P0 *ᵥ y + ∑ u ∈ Finset.range T, M u *ᵥ y) - ∑ u ∈ Finset.range T, M u *ᵥ μ u := by
        rw [sum_mulVec]
      _ = P0 *ᵥ y + (∑ u ∈ Finset.range T, M u *ᵥ y - ∑ u ∈ Finset.range T, M u *ᵥ μ u) := by
        abel
      _ = P0 *ᵥ y + ∑ u ∈ Finset.range T, (M u *ᵥ y - M u *ᵥ μ u) := by
        rw [Finset.sum_sub_distrib]
      _ = P0 *ᵥ y + ∑ u ∈ Finset.range T, (M u *ᵥ (y - μ u)) := by
        refine congrArg (fun t => P0 *ᵥ y + t) (Finset.sum_congr rfl (fun u hu => ?_))
        rw [mulVec_sub]
  rw [h_expr]
  calc
    oNorm (P0 *ᵥ y + ∑ u ∈ Finset.range T, (M u *ᵥ (y - μ u))) ≤
        oNorm (P0 *ᵥ y) + oNorm (∑ u ∈ Finset.range T, (M u *ᵥ (y - μ u))) :=
      gb_oNorm_add_le (P0 *ᵥ y) (∑ u ∈ Finset.range T, (M u *ᵥ (y - μ u)))
    _ ≤ oNorm (P0 *ᵥ y) + ∑ u ∈ Finset.range T, oNorm (M u *ᵥ (y - μ u)) := by
      have h := gb_oNorm_sum_le (Finset.range T) (fun u => M u *ᵥ (y - μ u))
      simpa [oNorm] using add_le_add_left h (oNorm (P0 *ᵥ y))
    _ ≤ (c0 * oNorm y) + ∑ u ∈ Finset.range T, (m u * oNorm (y - μ u)) := by
      have hP0y : oNorm (P0 *ᵥ y) ≤ c0 * oNorm y := hP0 y
      have hM_bound : ∀ u ∈ Finset.range T, oNorm (M u *ᵥ (y - μ u)) ≤ m u * oNorm (y - μ u) := by
        intro u hu
        rw [Finset.mem_range] at hu
        exact hM u hu (y - μ u)
      have h_sum : ∑ u ∈ Finset.range T, oNorm (M u *ᵥ (y - μ u)) ≤ ∑ u ∈ Finset.range T, (m u * oNorm (y - μ u)) :=
        Finset.sum_le_sum hM_bound
      nlinarith
    _ ≤ c0 * R + ∑ u ∈ Finset.range T, (m u * (oNorm y + oNorm (μ u))) := by
      have h_sub : ∀ u ∈ Finset.range T, oNorm (y - μ u) ≤ oNorm y + oNorm (μ u) := by
        intro u hu
        exact gb_oNorm_sub_le y (μ u)
      have h_sum : ∑ u ∈ Finset.range T, (m u * oNorm (y - μ u)) ≤ ∑ u ∈ Finset.range T, (m u * (oNorm y + oNorm (μ u))) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hm_nonneg : 0 ≤ m u := by
          rw [Finset.mem_range] at hu
          exact hm u hu
        nlinarith [h_sub u hu, hm_nonneg]
      nlinarith
    _ ≤ c0 * R + ∑ u ∈ Finset.range T, (m u * (R + R)) := by
      have h_sum : ∑ u ∈ Finset.range T, (m u * (oNorm y + oNorm (μ u))) ≤ ∑ u ∈ Finset.range T, (m u * (R + R)) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hm_nonneg : 0 ≤ m u := by
          rw [Finset.mem_range] at hu
          exact hm u hu
        have hy_bound : oNorm y ≤ R := hy
        have hμ_bound : oNorm (μ u) ≤ R := by
          rw [Finset.mem_range] at hu
          exact hμ u hu
        nlinarith
      nlinarith
    _ = c0 * R + 2 * R * ∑ u ∈ Finset.range T, m u := by
      rw [show (∑ u ∈ Finset.range T, (m u * (R + R))) = 2 * R * (∑ u ∈ Finset.range T, m u) by
        calc
          (∑ u ∈ Finset.range T, (m u * (R + R))) = (∑ u ∈ Finset.range T, (m u * (2 * R))) := by simp [two_mul]
          _ = (∑ u ∈ Finset.range T, (2 * R * m u)) := by
            refine Finset.sum_congr rfl (fun u _ => ?_)
            ring
          _ = 2 * R * (∑ u ∈ Finset.range T, m u) := by simp [Finset.mul_sum]
      ]

lemma l2_toLp_eq_sum_single {d : ℕ} (v : Fin d → ℝ) :
    WithLp.toLp 2 v = ∑ i : Fin d, v i • (EuclideanSpace.single i 1) := by
  ext j
  simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]


theorem gradM_hessM {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    df2GradM f z ⬝ᵥ v = fderiv ℝ f z (WithLp.toLp 2 v) ∧
      df2Sq (df2HessM f z) v = fderiv ℝ (fderiv ℝ f) z (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  have hgrad : df2GradM f z ⬝ᵥ v = fderiv ℝ f z (WithLp.toLp 2 v) := by
    calc
      df2GradM f z ⬝ᵥ v = (∑ i : Fin d, (df2GradM f z) i * v i) := by
        simp [dotProduct]
      _ = (∑ i : Fin d, (fderiv ℝ f z (EuclideanSpace.single i 1)) * v i) := by
        simp [df2GradM]
      _ = (∑ i : Fin d, v i * (fderiv ℝ f z (EuclideanSpace.single i 1))) := by
        simp [mul_comm]
      _ = (∑ i : Fin d, (fderiv ℝ f z) (v i • EuclideanSpace.single i 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [map_smul, smul_eq_mul]
      _ = (fderiv ℝ f z) (∑ i : Fin d, v i • EuclideanSpace.single i 1) := by
        simp [map_sum]
      _ = fderiv ℝ f z (WithLp.toLp 2 v) := by
        rw [l2_toLp_eq_sum_single v]
  have hhess : df2Sq (df2HessM f z) v = fderiv ℝ (fderiv ℝ f) z (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
    unfold df2Sq
    rw [dotProduct]
    simp [Matrix.mulVec_apply, df2HessM, dotProduct]
    calc
      (∑ i : Fin d, v i * (∑ j : Fin d, ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) * v j))
          = (∑ i : Fin d, ∑ j : Fin d, v i * (((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) * v j)) := by
        simp [Finset.mul_sum]
      _ = (∑ i : Fin d, ∑ j : Fin d, v i * v j * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) := by
        simp [mul_assoc, mul_comm]
      _ = (∑ i : Fin d, v i * (∑ j : Fin d, v j * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1))) := by
        simp [Finset.mul_sum, mul_assoc]
      _ = (∑ i : Fin d, v i * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1) (∑ j : Fin d, v j • EuclideanSpace.single j 1))) := by
        simp [map_sum, smul_eq_mul]
      _ = (∑ i : Fin d, v i * ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1) (WithLp.toLp 2 v))) := by
        rw [l2_toLp_eq_sum_single v]
      _ = (∑ i : Fin d, (v i • ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))) (WithLp.toLp 2 v)) := by
        simp [smul_eq_mul]
      _ = ((∑ i : Fin d, v i • ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i 1))) (WithLp.toLp 2 v)) := by
        rw [_root_.sum_apply]
      _ = ((fderiv ℝ (fderiv ℝ f) z) (∑ i : Fin d, v i • EuclideanSpace.single i 1)) (WithLp.toLp 2 v) := by
        simp [map_sum]
      _ = (fderiv ℝ (fderiv ℝ f) z) (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
        rw [l2_toLp_eq_sum_single v]
  exact And.intro hgrad hhess

theorem ld_core {d : ℕ} (Pb H : ℕ → Matrix (Fin d) (Fin d) ℝ) (T : ℕ)
    (σ2 cm : ℝ) (hσ : 0 < σ2) (hcm : 0 < cm) (hPb0 : Pb 0 = σ2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hstep : ∀ u ≤ T, Pb (u + 1) = Pb u + H u) (hH : ∀ u ≤ T, (H u).PosSemidef)
    (hHle : ∀ u ≤ T, (Pb u - H u).PosSemidef) (htop : (cm • (1 : Matrix (Fin d) (Fin d) ℝ) - Pb (T + 1)).PosSemidef) :
    ∑ u ∈ Finset.range (T + 1), ((Pb u)⁻¹ * H u).trace ≤ 2 * d * Real.log (cm * σ2) := by
  have hσinv_pos : 0 < σ2⁻¹ := inv_pos_of_pos hσ
  -- Step 1: Every Pb u (u ≤ T+1) is positive definite
  have hPb0_posdef : (Pb 0).PosDef := by
    rw [hPb0]
    exact (Matrix.PosDef.one.smul hσinv_pos : ((σ2⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef)
  have hPb_succ_posdef : ∀ u, u ≤ T → (Pb u).PosDef → (Pb (u + 1)).PosDef := by
    intro u hu hPu
    rw [hstep u hu]
    exact hPu.add_posSemidef (hH u hu)
  have hPb_posdef : ∀ u, u ≤ T + 1 → (Pb u).PosDef := by
    intro u hu
    induction' u with u ih
    · exact hPb0_posdef
    · have hu' : u ≤ T := by omega
      have hPu : (Pb u).PosDef := ih (by omega)
      exact hPb_succ_posdef u hu' hPu
  -- Helper: invertibility (use haveI for typeclass instances)
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num : (2 : ℝ) ≠ 0)
  haveI : Invertible cm := invertibleOfNonzero hcm.ne.symm
  have h_det_unit_1 : IsUnit ((1 : Matrix (Fin d) (Fin d) ℝ)).det := by
    simp
  -- Step 2: For each u ≤ T, ((Pb u)⁻¹ * H u).trace ≤ 2 * ((Pb (u+1))⁻¹ * H u).trace
  have h_step_ineq : ∀ u, u ≤ T → ((Pb u)⁻¹ * H u).trace ≤ 2 * ((Pb (u + 1))⁻¹ * H u).trace := by
    intro u hu
    have hPu : (Pb u).PosDef := hPb_posdef u (by omega)
    have hPu1 : (Pb (u + 1)).PosDef := hPb_posdef (u + 1) (by omega)
    have h2Pu_posdef : ((2 : ℝ) • Pb u).PosDef := by
      have hpos : 0 < (2 : ℝ) := by norm_num
      exact (hPu.smul hpos : ((2 : ℝ) • Pb u).PosDef)
    -- (2•Pb u - Pb(u+1)) = Pb u - H u, which is positive semidefinite
    have h_diff : ((2 : ℝ) • Pb u - Pb (u + 1)).PosSemidef := by
      rw [hstep u hu]
      have h_eq : (2 : ℝ) • Pb u - (Pb u + H u) = Pb u - H u := by
        calc
          (2 : ℝ) • Pb u - (Pb u + H u) = ((2 : ℝ) • Pb u - Pb u) - H u := by
            abel
          _ = Pb u - H u := by
            have h : (2 : ℝ) • Pb u - Pb u = Pb u := by
              calc
                (2 : ℝ) • Pb u - Pb u = (2 : ℝ) • Pb u - (1 : ℝ) • Pb u := by simp
                _ = ((2 : ℝ) - (1 : ℝ)) • Pb u := by rw [sub_smul]
                _ = (1 : ℝ) • Pb u := by norm_num
                _ = Pb u := by simp
            rw [h]
      rw [h_eq]
      exact hHle u hu
    -- Apply inv_antitone with A = Pb(u+1), B = 2•Pb u
    have h_inv_anti : ((Pb (u + 1))⁻¹ - ((2 : ℝ) • Pb u)⁻¹).PosSemidef :=
      inv_antitone (Pb (u + 1)) ((2 : ℝ) • Pb u) hPu1 h2Pu_posdef h_diff
    -- (2•Pb u)⁻¹ = (⅟2) • (Pb u)⁻¹ = 2⁻¹ • (Pb u)⁻¹
    have h_inv_smul : ((2 : ℝ) • Pb u)⁻¹ = (2⁻¹ : ℝ) • (Pb u)⁻¹ := by
      have h_det_unit : IsUnit (Pb u).det := by
        rw [← Matrix.isUnit_iff_isUnit_det]
        exact hPu.isUnit
      simpa using Matrix.inv_smul (Pb u) (2 : ℝ) h_det_unit
    have h_inv_diff : ((Pb (u + 1))⁻¹ - ((2⁻¹ : ℝ) • (Pb u)⁻¹)).PosSemidef := by
      simpa [h_inv_smul] using h_inv_anti
    -- Now use trace_mul_nonneg
    have h_trace_nonneg : 0 ≤ (((Pb (u + 1))⁻¹ - ((2⁻¹ : ℝ) • (Pb u)⁻¹)) * (H u)).trace :=
      trace_mul_nonneg _ _ h_inv_diff (hH u hu)
    -- Expand the trace
    have h_trace_expand : (((Pb (u + 1))⁻¹ - ((2⁻¹ : ℝ) • (Pb u)⁻¹)) * (H u)).trace =
        ((Pb (u + 1))⁻¹ * H u).trace - (2⁻¹ : ℝ) * ((Pb u)⁻¹ * H u).trace := by
      calc
        (((Pb (u + 1))⁻¹ - ((2⁻¹ : ℝ) • (Pb u)⁻¹)) * (H u)).trace
            = (((Pb (u + 1))⁻¹) * (H u) - (((2⁻¹ : ℝ) • (Pb u)⁻¹)) * (H u)).trace := by
          rw [Matrix.sub_mul]
        _ = ((Pb (u + 1))⁻¹ * H u).trace - (((2⁻¹ : ℝ) • (Pb u)⁻¹) * H u).trace := by
          rw [Matrix.trace_sub]
        _ = ((Pb (u + 1))⁻¹ * H u).trace - ((2⁻¹ : ℝ) • ((Pb u)⁻¹ * H u)).trace := by
          simp [Algebra.smul_mul_assoc]
        _ = ((Pb (u + 1))⁻¹ * H u).trace - (2⁻¹ : ℝ) * ((Pb u)⁻¹ * H u).trace := by
          rw [Matrix.trace_smul, smul_eq_mul]
    rw [h_trace_expand] at h_trace_nonneg
    -- h_trace_nonneg : 0 ≤ ((Pb (u+1))⁻¹ * H u).trace - (2⁻¹) * ((Pb u)⁻¹ * H u).trace
    -- Rearranging gives the desired inequality
    linarith
  -- Step 3: Use logdet_le to bound each term
  have h_logdet_bound : ∀ u, u ≤ T → ((Pb u)⁻¹ * H u).trace ≤
      2 * (Real.log (Pb (u + 1)).det - Real.log (Pb u).det) := by
    intro u hu
    have hPu : (Pb u).PosDef := hPb_posdef u (by omega)
    have hPu1 : (Pb (u + 1)).PosDef := hPb_posdef (u + 1) (by omega)
    -- logdet_le: Real.log B.det ≤ Real.log A.det + (A⁻¹ * (B - A)).trace
    -- Apply with A = Pb(u+1), B = Pb u
    have h_log := logdet_le (Pb (u + 1)) (Pb u) hPu1 hPu
    -- h_log : Real.log (Pb u).det ≤ Real.log (Pb (u+1)).det + ((Pb (u+1))⁻¹ * (Pb u - Pb (u+1))).trace
    have h_diff : Pb u - Pb (u + 1) = -H u := by
      rw [hstep u hu]
      simp
    rw [h_diff] at h_log
    -- h_log : Real.log (Pb u).det ≤ Real.log (Pb (u+1)).det + ((Pb (u+1))⁻¹ * (-H u)).trace
    have h_trace_neg : ((Pb (u + 1))⁻¹ * (-H u)).trace = -((Pb (u + 1))⁻¹ * H u).trace := by
      simp
    rw [h_trace_neg] at h_log
    -- h_log : Real.log (Pb u).det ≤ Real.log (Pb (u+1)).det - ((Pb (u+1))⁻¹ * H u).trace
    -- Rearranging:
    have h_bound : ((Pb (u + 1))⁻¹ * H u).trace ≤ Real.log (Pb (u + 1)).det - Real.log (Pb u).det := by
      linarith
    -- Combine with step 2
    have h_step := h_step_ineq u hu
    -- h_step : ((Pb u)⁻¹ * H u).trace ≤ 2 * ((Pb (u+1))⁻¹ * H u).trace
    have h_combined : ((Pb u)⁻¹ * H u).trace ≤ 2 * (Real.log (Pb (u + 1)).det - Real.log (Pb u).det) := by
      nlinarith
    exact h_combined
  -- Step 4: Sum over u ≤ T, telescoping sum
  have h_sum_bound : ∑ u ∈ Finset.range (T + 1), ((Pb u)⁻¹ * H u).trace ≤
      2 * (Real.log (Pb (T + 1)).det - Real.log (Pb 0).det) := by
    have h_telescope : ∑ u ∈ Finset.range (T + 1), (Real.log (Pb (u + 1)).det - Real.log (Pb u).det) =
        Real.log (Pb (T + 1)).det - Real.log (Pb 0).det := by
      rw [Finset.sum_range_sub (fun u => Real.log (Pb u).det) (T + 1)]
    calc
      ∑ u ∈ Finset.range (T + 1), ((Pb u)⁻¹ * H u).trace
          ≤ ∑ u ∈ Finset.range (T + 1), (2 * (Real.log (Pb (u + 1)).det - Real.log (Pb u).det)) :=
        Finset.sum_le_sum (fun i hi => h_logdet_bound i (by
          have hi' := Finset.mem_range.1 hi
          omega))
      _ = 2 * ∑ u ∈ Finset.range (T + 1), (Real.log (Pb (u + 1)).det - Real.log (Pb u).det) := by
        rw [Finset.mul_sum]
      _ = 2 * (Real.log (Pb (T + 1)).det - Real.log (Pb 0).det) := by rw [h_telescope]
  -- Step 5: Compute Real.log (Pb 0).det
  have h_log_det0 : Real.log (Pb 0).det = -(d : ℝ) * Real.log σ2 := by
    rw [hPb0]
    have h_det : (σ2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).det = (σ2⁻¹) ^ d * (1 : Matrix (Fin d) (Fin d) ℝ).det := by
      simpa using Matrix.det_smul (1 : Matrix (Fin d) (Fin d) ℝ) (σ2⁻¹)
    rw [h_det, Matrix.det_one]
    rw [Real.log_mul (pow_ne_zero d (inv_ne_zero hσ.ne.symm)) (by norm_num : (1 : ℝ) ≠ 0)]
    simp [Real.log_pow, Real.log_inv]
  -- Step 6: Bound Real.log (Pb (T+1)).det using logdet_le with cm•1
  have h_log_det_top : Real.log (Pb (T + 1)).det ≤ (d : ℝ) * Real.log cm := by
    have h_cm1_posdef : (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
      (Matrix.PosDef.one.smul hcm : (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef)
    have h_log := logdet_le (cm • (1 : Matrix (Fin d) (Fin d) ℝ)) (Pb (T + 1)) h_cm1_posdef (hPb_posdef (T + 1) (by omega))
    -- h_log : Real.log (Pb (T+1)).det ≤ Real.log (cm•1).det + ((cm•1)⁻¹ * (Pb(T+1) - cm•1)).trace
    have h_det_cm1 : (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).det = cm ^ d := by
      simpa [Matrix.det_one] using Matrix.det_smul (1 : Matrix (Fin d) (Fin d) ℝ) cm
    rw [h_det_cm1] at h_log
    have h_log_det_cm1 : Real.log (cm ^ d) = (d : ℝ) * Real.log cm := by
      simp [Real.log_pow]
    rw [h_log_det_cm1] at h_log
    -- Now handle the trace term: ((cm•1)⁻¹ * (Pb(T+1) - cm•1)).trace ≤ 0
    have h_inv_cm1 : (cm • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = (cm⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      calc
        (cm • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = ⅟cm • (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ :=
          Matrix.inv_smul (1 : Matrix (Fin d) (Fin d) ℝ) cm h_det_unit_1
        _ = cm⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by simp
    have h_trace_term : ((cm • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ))).trace ≤ 0 := by
      rw [h_inv_cm1]
      -- (cm⁻¹ • 1) * (Pb(T+1) - cm•1) = cm⁻¹ • (Pb(T+1) - cm•1)
      -- trace of that = cm⁻¹ * trace(Pb(T+1) - cm•1) = cm⁻¹ * (trace(Pb(T+1)) - d*cm)
      -- Since cm•1 - Pb(T+1) is positive semidefinite, trace(cm•1 - Pb(T+1)) ≥ 0
      -- So trace(Pb(T+1)) - d*cm ≤ 0, and cm⁻¹ > 0, so the product ≤ 0
      have h_trace_sub : (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ)).trace =
          (Pb (T + 1)).trace - (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).trace := by
        rw [Matrix.trace_sub]
      have h_trace_cm1 : (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).trace = (d : ℝ) * cm := by
        simp [Matrix.trace_smul, Matrix.trace_one, mul_comm]
      have h_trace_expr : (cm⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ))).trace =
          cm⁻¹ * ((Pb (T + 1)).trace - (d : ℝ) * cm) := by
        calc
          (cm⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ))).trace
              = (cm⁻¹ • ((1 : Matrix (Fin d) (Fin d) ℝ) * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ)))).trace := by
            simp [Algebra.smul_mul_assoc]
          _ = cm⁻¹ * ((1 : Matrix (Fin d) (Fin d) ℝ) * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ))).trace := by
            rw [Matrix.trace_smul, smul_eq_mul]
          _ = cm⁻¹ * (Pb (T + 1) - cm • (1 : Matrix (Fin d) (Fin d) ℝ)).trace := by simp
          _ = cm⁻¹ * ((Pb (T + 1)).trace - (cm • (1 : Matrix (Fin d) (Fin d) ℝ)).trace) := by rw [h_trace_sub]
          _ = cm⁻¹ * ((Pb (T + 1)).trace - (d : ℝ) * cm) := by rw [h_trace_cm1]
      rw [h_trace_expr]
      -- Now we need: cm⁻¹ * ((Pb(T+1)).trace - d*cm) ≤ 0
      -- Since cm > 0, cm⁻¹ > 0, it suffices to show (Pb(T+1)).trace - d*cm ≤ 0
      have h_trace_nonpos : (Pb (T + 1)).trace ≤ (d : ℝ) * cm := by
        have h_psd : (cm • (1 : Matrix (Fin d) (Fin d) ℝ) - Pb (T + 1)).PosSemidef := htop
        have h_trace_psd : 0 ≤ (cm • (1 : Matrix (Fin d) (Fin d) ℝ) - Pb (T + 1)).trace :=
          Matrix.PosSemidef.trace_nonneg h_psd
        have h_trace_diff : (cm • (1 : Matrix (Fin d) (Fin d) ℝ) - Pb (T + 1)).trace =
            (d : ℝ) * cm - (Pb (T + 1)).trace := by
          simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
          ring
        rw [h_trace_diff] at h_trace_psd
        linarith
      have h_cm_inv_pos : 0 < cm⁻¹ := inv_pos_of_pos hcm
      nlinarith
    -- Combine with h_log
    have h_final_bound : Real.log (Pb (T + 1)).det ≤ (d : ℝ) * Real.log cm + 0 := by
      linarith
    simpa using h_final_bound
  -- Step 7: Combine everything
  rw [h_log_det0] at h_sum_bound
  have h_log_mul : Real.log (cm * σ2) = Real.log cm + Real.log σ2 :=
    Real.log_mul hcm.ne.symm hσ.ne.symm
  have h_final : 2 * (Real.log (Pb (T + 1)).det - (-(d : ℝ) * Real.log σ2)) ≤ 2 * (d : ℝ) * Real.log (cm * σ2) := by
    nlinarith
  nlinarith

open scoped MatrixOrder in
theorem mulVec_sq_le {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (D : ℝ)
    (hP : P.PosSemidef) (hPD : (D • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) (x : Fin d → ℝ) :
    (P *ᵥ x) ⬝ᵥ (P *ᵥ x) ≤ D * df2Sq P x := by
  -- Expand df2Sq
  have h_df2Sq : df2Sq P x = x ⬝ᵥ (P *ᵥ x) := rfl
  rw [h_df2Sq]
  have hP_nonneg : 0 ≤ P := (Matrix.nonneg_iff_posSemidef.mpr hP)
  set S := CFC.sqrt P with hS_def
  have hS_sq : S ^ 2 = P := CFC.sq_sqrt P hP_nonneg
  have hS_nonneg : 0 ≤ S := CFC.sqrt_nonneg P
  have hS_psd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS_nonneg
  have hS_herm : S.IsHermitian := hS_psd.isHermitian
  have hS_transpose : S.transpose = S := by
    ext i j
    have h := (Matrix.IsHermitian.ext_iff.mp hS_herm) i j
    simpa using h
  set y := S *ᵥ x with hy_def
  -- (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = y ⬝ᵥ (P *ᵥ y)
  have hLHS : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = y ⬝ᵥ (P *ᵥ y) := by
    calc
      (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = ((S ^ 2) *ᵥ x) ⬝ᵥ ((S ^ 2) *ᵥ x) := by rw [hS_sq]
      _ = ((S * S) *ᵥ x) ⬝ᵥ ((S * S) *ᵥ x) := by rw [sq]
      _ = (S *ᵥ (S *ᵥ x)) ⬝ᵥ (S *ᵥ (S *ᵥ x)) := by simp [Matrix.mulVec_mulVec]
      _ = (S *ᵥ y) ⬝ᵥ (S *ᵥ y) := by rw [hy_def]
      _ = (S.mulVec y) ⬝ᵥ (S.mulVec y) := rfl
      _ = ((S.mulVec y) ᵥ* S) ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
      _ = (y ᵥ* (S.transpose * S)) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
      _ = (y ᵥ* (S * S)) ⬝ᵥ y := by rw [hS_transpose]
      _ = (y ᵥ* (S ^ 2)) ⬝ᵥ y := by rw [sq]
      _ = (y ᵥ* P) ⬝ᵥ y := by rw [hS_sq]
      _ = y ⬝ᵥ (P.mulVec y) := by rw [← Matrix.dotProduct_mulVec]
      _ = y ⬝ᵥ (P *ᵥ y) := rfl
  -- x ⬝ᵥ (P *ᵥ x) = y ⬝ᵥ y
  have hRHS : x ⬝ᵥ (P *ᵥ x) = y ⬝ᵥ y := by
    calc
      x ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ ((S ^ 2) *ᵥ x) := by rw [hS_sq]
      _ = x ⬝ᵥ (S *ᵥ (S *ᵥ x)) := by rw [sq, Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ (S *ᵥ y) := by rw [hy_def]
      _ = x ⬝ᵥ (S.mulVec y) := rfl
      _ = (x ᵥ* S) ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
      _ = (x ᵥ* (S.transpose)) ⬝ᵥ y := by rw [hS_transpose]
      _ = (S.mulVec x) ⬝ᵥ y := by rw [Matrix.vecMul_transpose]
      _ = (S *ᵥ x) ⬝ᵥ y := rfl
      _ = y ⬝ᵥ y := by rw [hy_def]
  rw [hLHS, hRHS]
  -- Need: y ⬝ᵥ (P *ᵥ y) ≤ D * (y ⬝ᵥ y)
  have h := hPD.dotProduct_mulVec_nonneg y
  -- h : 0 ≤ star y ⬝ᵥ ((D • 1 - P) *ᵥ y)
  have h_expand : ((D • (1 : Matrix (Fin d) (Fin d) ℝ) - P) *ᵥ y) = D • y - P *ᵥ y := by
    calc
      ((D • (1 : Matrix (Fin d) (Fin d) ℝ) - P) *ᵥ y) =
        ((D • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ y) - (P *ᵥ y) := by rw [Matrix.sub_mulVec]
      _ = (D • (1 *ᵥ y)) - (P *ᵥ y) := by rw [Matrix.smul_mulVec]
      _ = (D • y) - (P *ᵥ y) := by rw [Matrix.one_mulVec]
  rw [h_expand] at h
  -- h : 0 ≤ star y ⬝ᵥ (D • y - P *ᵥ y)
  have h_dot : star y ⬝ᵥ (D • y - P *ᵥ y) = D * (star y ⬝ᵥ y) - star y ⬝ᵥ (P *ᵥ y) := by
    simp
  rw [h_dot] at h
  -- h : 0 ≤ D * (star y ⬝ᵥ y) - star y ⬝ᵥ (P *ᵥ y)
  have h_star : star y = y := by
    ext i
    simp
  rw [h_star] at h
  -- h : 0 ≤ D * (y ⬝ᵥ y) - y ⬝ᵥ (P *ᵥ y)
  linarith

theorem rank_one_norm {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (a D : ℝ) (hP : P.PosSemidef) (hPD : (D • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) :
    oNorm ((a • (vecMulVec u u - P)) *ᵥ v) ≤ |a| * (u ⬝ᵥ u + D) * oNorm v := by
  have hr : vecMulVec u u *ᵥ v = (u ⬝ᵥ v) • u := by
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have hmv : (a • (vecMulVec u u - P)) *ᵥ v = a • ((u ⬝ᵥ v) • u - P *ᵥ v) := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, hr]
  have hsm : ∀ (c : ℝ) (x : Fin d → ℝ), oNorm (c • x) = |c| * oNorm x := by
    intro c x
    unfold oNorm
    rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have huu0 : 0 ≤ u ⬝ᵥ u := by simpa using dotProduct_self_star_nonneg u
  have huv : |u ⬝ᵥ v| ≤ oNorm u * oNorm v := by
    have h := sq_cauchy (1 : Matrix (Fin d) (Fin d) ℝ) Matrix.PosSemidef.one u v
    simp only [df2Sq, Matrix.one_mulVec] at h
    unfold oNorm
    rw [← Real.sqrt_mul huu0]
    exact Real.abs_le_sqrt h
  have hPv := mulVec_norm_le P D hP hPD v
  have hu0 : 0 ≤ oNorm u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ oNorm v := Real.sqrt_nonneg _
  have huu : oNorm u * oNorm u = u ⬝ᵥ u := Real.mul_self_sqrt huu0
  have hsub : oNorm ((u ⬝ᵥ v) • u - P *ᵥ v) ≤ oNorm ((u ⬝ᵥ v) • u) + oNorm (P *ᵥ v) := gb_oNorm_sub_le _ _
  rw [hsm] at hsub
  have h1 : |u ⬝ᵥ v| * oNorm u ≤ (u ⬝ᵥ u) * oNorm v := by
    rw [← huu]; nlinarith [abs_nonneg (u ⬝ᵥ v)]
  rw [hmv, hsm]
  calc |a| * oNorm ((u ⬝ᵥ v) • u - P *ᵥ v) ≤ |a| * ((u ⬝ᵥ u) * oNorm v + D * oNorm v) := by
        gcongr; linarith
    _ = |a| * (u ⬝ᵥ u + D) * oNorm v := by ring

open Set in
theorem taylor_upper {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContDiff ℝ 2 f) (μ v : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ (fderiv ℝ f) (μ + t • v) v v ≤ M) :
    f (μ + v) ≤ f μ + fderiv ℝ f μ v + M / 2 := by
  set g := fun (t : ℝ) => f (μ + t • v) with hg_def
  set φ := fun (t : ℝ) => μ + t • v with hφ_def
  have hφ_contdiff : ContDiff ℝ 2 φ := by
    have h_const : ContDiff ℝ (2 : ℕ) (fun (_ : ℝ) => μ) := contDiff_const (n := 2)
    have h_id_smul : ContDiff ℝ (2 : ℕ) (fun (t : ℝ) => t • v) :=
      (contDiff_id (n := 2)).smul (contDiff_const (n := 2) (c := v))
    exact h_const.add h_id_smul
  have hg_contdiff : ContDiff ℝ 2 g :=
    hf.comp hφ_contdiff
  have hx_ne : (0 : ℝ) ≠ 1 := by norm_num
  have hg_contdiff_on : ContDiffOn ℝ (1 + 1) g (Set.uIcc (0 : ℝ) 1) :=
    (hg_contdiff.contDiffOn (s := Set.uIcc (0 : ℝ) 1)).of_le (by norm_num)
  rcases taylor_mean_remainder_lagrange_iteratedDeriv hx_ne hg_contdiff_on with ⟨ξ, hξ, h_eq⟩
  -- h_eq: g 1 - taylorWithinEval g 1 (Set.uIcc 0 1) 0 1 = iteratedDeriv 2 g ξ * (1 - 0) ^ 2 / ↑(2).factorial
  have h_taylor_eval : taylorWithinEval g 1 (Set.uIcc (0 : ℝ) 1) 0 1 = g 0 + iteratedDerivWithin 1 g (Set.uIcc (0 : ℝ) 1) 0 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one]
  have h_first_deriv : iteratedDerivWithin 1 g (Set.uIcc (0 : ℝ) 1) 0 = fderiv ℝ f μ v := by
    rw [iteratedDerivWithin_one]
    have h_hasDeriv : HasDerivAt g (fderiv ℝ f μ v) 0 := by
      have h_hasFDeriv : HasFDerivAt f (fderiv ℝ f μ) μ :=
        (hf.differentiable (by norm_num) μ).hasFDerivAt
      have h_φ_deriv : HasDerivAt φ v 0 := by
        have h_const : HasDerivAt (fun (_ : ℝ) => μ) 0 0 := hasDerivAt_const 0 μ
        have h_smul : HasDerivAt (fun (t : ℝ) => t • v) v 0 := by
          have : HasDerivAt (fun (t : ℝ) => t) 1 0 := hasDerivAt_id 0
          simpa using this.smul_const v
        have h_add : HasDerivAt (fun (t : ℝ) => μ + t • v) (0 + v) 0 :=
          HasDerivAt.add h_const h_smul
        simpa [φ, hφ_def, add_zero] using h_add
      have h_eq_pt : μ = φ 0 := by simp [φ, hφ_def]
      have h_comp := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (l := f) (l' := fderiv ℝ f μ)
        (f := φ) (f' := v) (h_eq_pt ▸ h_hasFDeriv) h_φ_deriv
      -- h_comp : HasDerivAt (f ∘ φ) ((fderiv ℝ f μ) v) 0
      -- We need HasDerivAt g (fderiv ℝ f μ v) 0
      -- g = f ∘ φ, and (fderiv ℝ f μ) v = fderiv ℝ f μ v
      have : g = f ∘ φ := by
        ext t; simp [g, hg_def, φ, hφ_def]
      rw [this]
      simpa using h_comp
    have h_hasDerivWithin : HasDerivWithinAt g (fderiv ℝ f μ v) (Set.uIcc (0 : ℝ) 1) 0 :=
      h_hasDeriv.hasDerivWithinAt
    have h_unique_0 : UniqueDiffWithinAt ℝ (Set.uIcc (0 : ℝ) 1) 0 :=
      (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1)) 0 (by
        simp)
    exact h_hasDerivWithin.derivWithin h_unique_0
  have h_second_deriv : iteratedDeriv 2 g ξ = fderiv ℝ (fderiv ℝ f) (μ + ξ • v) v v := by
    -- iteratedDeriv 2 g ξ = iteratedDeriv 2 (f ∘ φ) ξ
    have h_g_eq : g = f ∘ φ := by
      ext t; simp [g, hg_def, φ, hφ_def]
    rw [h_g_eq]
    have h_formula := iteratedDeriv_vcomp_two (g := f) (f := φ) (x := ξ)
    have hf_contdiff_at : ContDiffAt ℝ 2 f (φ ξ) :=
      hf.contDiffAt (𝕜 := ℝ) (x := φ ξ)
    have hφ_contdiff_at : ContDiffAt ℝ 2 φ ξ :=
      hφ_contdiff.contDiffAt (x := ξ)
    rw [h_formula hf_contdiff_at hφ_contdiff_at]
    have h_deriv_φ_all : ∀ t : ℝ, deriv φ t = v := by
      intro t
      have h_hasDeriv : HasDerivAt φ v t := by
        have h_const : HasDerivAt (fun (_ : ℝ) => μ) 0 t := hasDerivAt_const t μ
        have h_smul : HasDerivAt (fun (s : ℝ) => s • v) v t := by
          have : HasDerivAt (fun (s : ℝ) => s) 1 t := hasDerivAt_id t
          simpa using this.smul_const v
        have h_add : HasDerivAt (fun (s : ℝ) => μ + s • v) (0 + v) t :=
          HasDerivAt.add h_const h_smul
        simpa [φ, hφ_def, add_zero] using h_add
      exact h_hasDeriv.deriv
    have h_iter_deriv2_φ : iteratedDeriv 2 φ ξ = 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      have h_deriv_const : deriv φ = fun _ => v :=
        funext h_deriv_φ_all
      rw [h_deriv_const]
      simp
    have h_iterFDeriv_term : ((iteratedFDeriv ℝ 2 f (φ ξ)) fun _ => deriv φ ξ) =
        fderiv ℝ (fderiv ℝ f) (μ + ξ • v) v v := by
      rw [h_deriv_φ_all ξ]
      have h_two_apply := iteratedFDeriv_two_apply (𝕜 := ℝ) f (φ ξ) (fun (_ : Fin 2) => v)
      simpa [φ, hφ_def] using h_two_apply
    have h_fderiv_term : (fderiv ℝ f (φ ξ)) (iteratedDeriv 2 φ ξ) = 0 := by
      rw [h_iter_deriv2_φ]
      simp
    rw [h_iterFDeriv_term, h_fderiv_term]
    simp
  have h_bound : fderiv ℝ (fderiv ℝ f) (μ + ξ • v) v v ≤ M := by
    have hξ_mem : ξ ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hξ with ⟨hξ_left, hξ_right⟩
      have h_min : min (0 : ℝ) 1 = 0 := by simp
      have h_max : max (0 : ℝ) 1 = 1 := by simp
      have h_left : (0 : ℝ) < ξ := by simpa [h_min] using hξ_left
      have h_right : ξ < 1 := by simpa [h_max] using hξ_right
      exact ⟨by linarith, by linarith⟩
    exact hM ξ hξ_mem
  rw [h_taylor_eval, h_first_deriv, h_second_deriv] at h_eq
  have h_simp : g 1 - (g 0 + fderiv ℝ f μ v) = (fderiv ℝ (fderiv ℝ f) (μ + ξ • v) v v) / 2 := by
    simpa [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] using h_eq
  have h_nonpos : g 1 - (g 0 + fderiv ℝ f μ v) ≤ M / 2 := by
    linarith
  have hg1 : g 1 = f (μ + v) := by
    simp [g, hg_def]
  have hg0 : g 0 = f μ := by
    simp [g, hg_def]
  rw [hg1, hg0] at h_nonpos
  linarith

theorem sandwich_lower {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContDiff ℝ 2 f) (μ y : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (hsc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((2 : ℝ) • df2HessM f (WithLp.toLp 2 μ) + δ • P - df2HessM f (WithLp.toLp 2 (μ + t • (y - μ)))).PosSemidef) :
    f (WithLp.toLp 2 μ) - f (WithLp.toLp 2 y) ≥
      df2GradM f (WithLp.toLp 2 μ) ⬝ᵥ (μ - y) - df2Sq (df2HessM f (WithLp.toLp 2 μ)) (y - μ) - δ / 2 * df2Sq P (y - μ) := by
  set v := y - μ with hv
  have hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ (fderiv ℝ f) (WithLp.toLp 2 μ + t • WithLp.toLp 2 v)
      (WithLp.toLp 2 v) (WithLp.toLp 2 v) ≤ 2 * df2Sq (df2HessM f (WithLp.toLp 2 μ)) v + δ * df2Sq P v := by
    intro t ht
    have h := (hsc t ht).dotProduct_mulVec_nonneg v
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_add, dotProduct_smul, smul_eq_mul] at h
    have heq : WithLp.toLp 2 μ + t • WithLp.toLp 2 v = WithLp.toLp 2 (μ + t • v) := by simp
    rw [heq, ← (gradM_hessM f _ v).2]
    unfold df2Sq
    linarith
  have h := taylor_upper f hf (WithLp.toLp 2 μ) (WithLp.toLp 2 v) _ hM
  have hy : WithLp.toLp 2 μ + WithLp.toLp 2 v = WithLp.toLp 2 y := by simp [hv]
  rw [hy, ← (gradM_hessM f _ v).1] at h
  have hgv : df2GradM f (WithLp.toLp 2 μ) ⬝ᵥ (μ - y) = -(df2GradM f (WithLp.toLp 2 μ) ⬝ᵥ v) := by
    rw [hv, ← dotProduct_neg, neg_sub]
  rw [hgv]
  linarith

theorem u_norm {d : ℕ} (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hP : P.PosSemidef) (hAS : A * Aᵀ = S) (hSP : S * P = 1)
    (hPD : (δ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) :
    (P *ᵥ (A *ᵥ ξ)) ⬝ᵥ (P *ᵥ (A *ᵥ ξ)) ≤ (ξ ⬝ᵥ ξ) / δ := by
  -- First, prove the key inequality: for any z, (P*z)⬝ᵥ(P*z) ≤ δ⁻¹ * (z⬝ᵥ(P*z))
  have h_key : ∀ z : Fin d → ℝ, (P *ᵥ z) ⬝ᵥ (P *ᵥ z) ≤ δ⁻¹ * (z ⬝ᵥ (P *ᵥ z)) := by
    intro z
    set B := Matrix.toBilin' P with hB_def
    have hB_nonneg : ∀ x : Fin d → ℝ, 0 ≤ (B x) x := by
      intro x
      rw [hB_def, Matrix.toBilin'_apply']
      have h := hP.dotProduct_mulVec_nonneg x
      simpa using h
    have hB_symm : LinearMap.IsSymm B := by
      have h_symm : P.IsSymm := by simpa using hP.1
      have h : B.IsSymm := by
        refine ⟨λ x y => ?_⟩
        rw [hB_def, Matrix.toBilin'_apply', Matrix.toBilin'_apply']
        calc
          x ⬝ᵥ (P *ᵥ y) = (Matrix.vecMul x P) ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
          _ = (Matrix.vecMul x Pᵀ) ⬝ᵥ y := by rw [h_symm]
          _ = (P *ᵥ x) ⬝ᵥ y := by rw [Matrix.vecMul_transpose]
          _ = y ⬝ᵥ (P *ᵥ x) := by rw [dotProduct_comm]
      exact (LinearMap.BilinForm.isSymm_iff.mp h)
    have h_cs := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm
    have h_bound : ∀ w : Fin d → ℝ, w ⬝ᵥ (P *ᵥ w) ≤ δ⁻¹ * (w ⬝ᵥ w) := by
      intro w
      have h_pd := hPD.dotProduct_mulVec_nonneg w
      have h_pd' : 0 ≤ w ⬝ᵥ ((δ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - P) *ᵥ w) := by simpa using h_pd
      have h_expand : (δ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - P) *ᵥ w = δ⁻¹ • w - P *ᵥ w := by
        calc
          (δ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - P) *ᵥ w = (δ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ w - P *ᵥ w := by
            rw [Matrix.sub_mulVec]
          _ = δ⁻¹ • ((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ w) - P *ᵥ w := by
            rw [Matrix.smul_mulVec]
          _ = δ⁻¹ • w - P *ᵥ w := by simp
      rw [h_expand] at h_pd'
      have h_dot : w ⬝ᵥ (δ⁻¹ • w - P *ᵥ w) = δ⁻¹ * (w ⬝ᵥ w) - w ⬝ᵥ (P *ᵥ w) := by
        calc
          w ⬝ᵥ (δ⁻¹ • w - P *ᵥ w) = w ⬝ᵥ (δ⁻¹ • w) - w ⬝ᵥ (P *ᵥ w) := by
            rw [dotProduct_sub]
          _ = δ⁻¹ • (w ⬝ᵥ w) - w ⬝ᵥ (P *ᵥ w) := by
            rw [dotProduct_smul]
          _ = δ⁻¹ * (w ⬝ᵥ w) - w ⬝ᵥ (P *ᵥ w) := by
            simp
      rw [h_dot] at h_pd'
      linarith
    -- Apply Cauchy-Schwarz with x := z, y := P *ᵥ z
    have h_cs_app := h_cs z (P *ᵥ z)
    rw [hB_def] at h_cs_app
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toBilin'_apply'] at h_cs_app
    -- h_cs_app : (z ⬝ᵥ (P *ᵥ (P *ᵥ z)))^2 ≤ (z ⬝ᵥ (P *ᵥ z)) * ((P *ᵥ z) ⬝ᵥ (P *ᵥ (P *ᵥ z)))
    -- Use symmetry: z ⬝ᵥ (P *ᵥ (P *ᵥ z)) = (P *ᵥ z) ⬝ᵥ (P *ᵥ z)
    have h_symm_dot : z ⬝ᵥ (P *ᵥ (P *ᵥ z)) = (P *ᵥ z) ⬝ᵥ (P *ᵥ z) := by
      have h_symm_P : P.IsSymm := by simpa using hP.1
      calc
        z ⬝ᵥ (P *ᵥ (P *ᵥ z)) = (Matrix.vecMul z P) ⬝ᵥ (P *ᵥ z) := by rw [Matrix.dotProduct_mulVec]
        _ = (Matrix.vecMul z Pᵀ) ⬝ᵥ (P *ᵥ z) := by rw [h_symm_P]
        _ = (P *ᵥ z) ⬝ᵥ (P *ᵥ z) := by rw [Matrix.vecMul_transpose]
    rw [h_symm_dot] at h_cs_app
    -- h_cs_app : ((P *ᵥ z) ⬝ᵥ (P *ᵥ z))^2 ≤ (z ⬝ᵥ (P *ᵥ z)) * ((P *ᵥ z) ⬝ᵥ (P *ᵥ (P *ᵥ z)))
    set a := (P *ᵥ z) ⬝ᵥ (P *ᵥ z) with ha_def
    set b := z ⬝ᵥ (P *ᵥ z) with hb_def
    set c := (P *ᵥ z) ⬝ᵥ (P *ᵥ (P *ᵥ z)) with hc_def
    -- Now h_cs_app : a^2 ≤ b * c
    -- Apply h_bound to P *ᵥ z
    have h_bound_Pz := h_bound (P *ᵥ z)
    -- h_bound_Pz : (P *ᵥ z) ⬝ᵥ (P *ᵥ (P *ᵥ z)) ≤ δ⁻¹ * ((P *ᵥ z) ⬝ᵥ (P *ᵥ z))
    -- This is c ≤ δ⁻¹ * a
    have h_bound_Pz' : c ≤ δ⁻¹ * a := by
      simpa [ha_def, hc_def] using h_bound_Pz
    have ha_nonneg : 0 ≤ a := by
      rw [ha_def]
      have h := dotProduct_star_self_nonneg (P *ᵥ z)
      simpa using h
    have hb_nonneg : 0 ≤ b := by
      rw [hb_def]
      have h := hP.dotProduct_mulVec_nonneg z
      simpa using h
    have h_ineq : a^2 ≤ b * (δ⁻¹ * a) := by
      calc
        a^2 ≤ b * c := h_cs_app
        _ ≤ b * (δ⁻¹ * a) := mul_le_mul_of_nonneg_left h_bound_Pz' hb_nonneg
    -- Now a^2 ≤ δ⁻¹ * a * b
    by_cases ha_zero : a = 0
    · -- If a = 0, then we need 0 ≤ δ⁻¹ * b
      have hpos : 0 ≤ δ⁻¹ * b := by
        have hδinv : 0 ≤ δ⁻¹ := inv_nonneg.mpr (by linarith)
        exact mul_nonneg hδinv hb_nonneg
      simpa [ha_zero, ha_def, hb_def] using hpos
    · -- If a ≠ 0, then a > 0 (since a ≥ 0), and we can divide
      have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
      have hgoal : a ≤ δ⁻¹ * b := by
        nlinarith
      simpa [ha_def, hb_def] using hgoal
  -- Now apply h_key with z := A *ᵥ ξ
  set u := P *ᵥ (A *ᵥ ξ) with hu_def
  -- Goal: u⬝ᵥu ≤ (ξ⬝ᵥξ)/δ
  -- First, show that Aᵀ *ᵥ u = ξ
  have h_AT_u_eq_xi : Aᵀ *ᵥ u = ξ := by
    calc
      Aᵀ *ᵥ u = Aᵀ *ᵥ (P *ᵥ (A *ᵥ ξ)) := by rw [hu_def]
      _ = (Aᵀ * P) *ᵥ (A *ᵥ ξ) := by rw [Matrix.mulVec_mulVec]
      _ = (Aᵀ * P * A) *ᵥ ξ := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ ξ := by
        have h_right_inv : A * (Aᵀ * P) = 1 := by
          calc
            A * (Aᵀ * P) = (A * Aᵀ) * P := by rw [Matrix.mul_assoc]
            _ = S * P := by rw [hAS]
            _ = 1 := hSP
        have h_left_inv : (Aᵀ * P) * A = 1 := mul_eq_one_comm.mp h_right_inv
        simpa [Matrix.mul_assoc] using congrArg (· *ᵥ ξ) h_left_inv
      _ = ξ := by simp
  -- Now compute u ⬝ᵥ (S *ᵥ u) = ξ ⬝ᵥ ξ
  have h_u_S_u_eq_xi_xi : u ⬝ᵥ (S *ᵥ u) = ξ ⬝ᵥ ξ := by
    calc
      u ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ ((A * Aᵀ) *ᵥ u) := by rw [hAS]
      _ = u ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ u)) := by rw [← Matrix.mulVec_mulVec]
      _ = u ⬝ᵥ (A *ᵥ ξ) := by rw [h_AT_u_eq_xi]
      _ = (Aᵀ *ᵥ u) ⬝ᵥ ξ := by
        calc
          u ⬝ᵥ (A *ᵥ ξ) = (u ᵥ* A) ⬝ᵥ ξ := by rw [Matrix.dotProduct_mulVec]
          _ = (u ᵥ* (Aᵀ)ᵀ) ⬝ᵥ ξ := by rw [transpose_transpose]
          _ = (Aᵀ *ᵥ u) ⬝ᵥ ξ := by rw [Matrix.vecMul_transpose]
      _ = ξ ⬝ᵥ ξ := by rw [h_AT_u_eq_xi]
  -- Now set z := S *ᵥ u, then P *ᵥ z = u
  set z := S *ᵥ u with hz_def
  have h_P_z_eq_u : P *ᵥ z = u := by
    calc
      P *ᵥ z = P *ᵥ (S *ᵥ u) := by rw [hz_def]
      _ = (P * S) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ u := by
        have h_PS : P * S = 1 := mul_eq_one_comm.mpr hSP
        rw [h_PS]
      _ = u := by simp
  -- Now z ⬝ᵥ (P *ᵥ z) = u ⬝ᵥ (S *ᵥ u) = ξ ⬝ᵥ ξ
  have h_z_P_z_eq_xi_xi : z ⬝ᵥ (P *ᵥ z) = ξ ⬝ᵥ ξ := by
    rw [h_P_z_eq_u]
    -- z ⬝ᵥ u = u ⬝ᵥ z (by dotProduct_comm)
    -- And z = S *ᵥ u, so u ⬝ᵥ z = u ⬝ᵥ (S *ᵥ u) = ξ ⬝ᵥ ξ
    rw [dotProduct_comm, hz_def]
    exact h_u_S_u_eq_xi_xi
  -- Apply h_key with z := S *ᵥ u
  have h_main := h_key z
  -- h_main : (P *ᵥ z) ⬝ᵥ (P *ᵥ z) ≤ δ⁻¹ * (z ⬝ᵥ (P *ᵥ z))
  have h_left : (P *ᵥ z) ⬝ᵥ (P *ᵥ z) = u ⬝ᵥ u := by rw [h_P_z_eq_u]
  have h_right : z ⬝ᵥ (P *ᵥ z) = ξ ⬝ᵥ ξ := h_z_P_z_eq_xi_xi
  rw [h_left, h_right] at h_main
  -- h_main : u ⬝ᵥ u ≤ δ⁻¹ * (ξ ⬝ᵥ ξ)
  -- Goal: u ⬝ᵥ u ≤ (ξ ⬝ᵥ ξ) / δ
  -- Note: δ⁻¹ * (ξ ⬝ᵥ ξ) = (ξ ⬝ᵥ ξ) / δ
  have h_div : δ⁻¹ * (ξ ⬝ᵥ ξ) = (ξ ⬝ᵥ ξ) / δ := by
    rw [div_eq_inv_mul]
  rw [h_div] at h_main
  -- Now h_main : u ⬝ᵥ u ≤ (ξ ⬝ᵥ ξ) / δ
  -- But u is defined as P *ᵥ (A *ᵥ ξ), so we need to unfold u
  simpa [hu_def] using h_main

private lemma yb_sqrt_ineq_aux (L Lg : ℝ) (hL_nonneg : 0 ≤ L) (hLg_le : Lg ≤ L/27) :
    2 * Real.sqrt L * Real.sqrt Lg ≤ Real.sqrt (8/36) * L := by
  by_cases hLg_nonneg : 0 ≤ Lg
  · have hL_sq_nonneg : 0 ≤ L^2 := pow_two_nonneg L
    have h_sq_ineq : (2 * Real.sqrt L * Real.sqrt Lg)^2 ≤ (Real.sqrt (8/36) * L)^2 := by
      have h1 : (2 * Real.sqrt L * Real.sqrt Lg)^2 = 4 * L * Lg := by
        calc
          (2 * Real.sqrt L * Real.sqrt Lg)^2 = 4 * (Real.sqrt L)^2 * (Real.sqrt Lg)^2 := by ring
          _ = 4 * L * Lg := by rw [Real.sq_sqrt hL_nonneg, Real.sq_sqrt hLg_nonneg]
      have h2 : 4 * L * Lg ≤ 4 * L * (L/27) :=
        mul_le_mul_of_nonneg_left hLg_le (mul_nonneg (by norm_num) hL_nonneg)
      have h3 : 4 * L * (L/27) ≤ (8/36) * L^2 := by
        have h_frac : (4/27 : ℝ) ≤ (8/36 : ℝ) := by norm_num
        calc
          4 * L * (L/27) = (4/27) * L^2 := by ring
          _ ≤ (8/36) * L^2 := mul_le_mul_of_nonneg_right h_frac hL_sq_nonneg
      have h4 : (8/36) * L^2 = (Real.sqrt (8/36) * L)^2 := by
        calc
          (8/36) * L^2 = ((Real.sqrt (8/36))^2) * L^2 := by
            rw [Real.sq_sqrt (by norm_num : 0 ≤ (8/36 : ℝ))]
          _ = (Real.sqrt (8/36) * L)^2 := by ring
      rw [h1, ← h4]
      exact h2.trans h3
    have h_nonneg_left : 0 ≤ 2 * Real.sqrt L * Real.sqrt Lg :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have h_nonneg_right : 0 ≤ Real.sqrt (8/36) * L :=
      mul_nonneg (Real.sqrt_nonneg _) hL_nonneg
    by_contra! h
    have h_sq_gt : (Real.sqrt (8/36) * L)^2 < (2 * Real.sqrt L * Real.sqrt Lg)^2 :=
      (sq_lt_sq₀ h_nonneg_right h_nonneg_left).mpr h
    nlinarith
  · have h_sqrtLg_zero : Real.sqrt Lg = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [h_sqrtLg_zero, mul_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hL_nonneg


theorem ybound (pip G gv e L Lg ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (hpip : pip = max 1 (G / (1 - ε))) (hG0 : 0 ≤ G) (hG : G ≤ Real.sqrt L) (hgv0 : 0 ≤ gv) (hgv1 : gv ≤ 1)
    (he : |e| ≤ Real.sqrt Lg) (hLgL : Lg ≤ 4 / 3 * (L / 36)) (hr4 : 10 * Real.sqrt L + Real.sqrt (8 / 36) * L ≤ L)
    (hL : 1 ≤ L) : |pip * (gv + e) + 2 * (pip - 1) / ε| ≤ L / (2 * ε) := by
  have hL_nonneg : 0 ≤ L := by linarith
  have hsqrtL_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have h_one_minus_ε_pos : 0 < 1 - ε := by linarith
  have h_one_minus_ε_nonneg : 0 ≤ 1 - ε := by linarith
  have hε_nonneg : 0 ≤ ε := by linarith
  -- pip ≥ 1
  have hpip_ge_one : 1 ≤ pip := by
    rw [hpip]
    exact le_max_left _ _
  have hpip_nonneg : 0 ≤ pip := by linarith
  -- pip ≤ 2√L
  have h_one_le_two_sqrtL : (1 : ℝ) ≤ 2 * Real.sqrt L := by
    have h_sqrtL_ge_one : 1 ≤ Real.sqrt L := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    nlinarith
  have hG_div_le_two_sqrtL : G / (1 - ε) ≤ 2 * Real.sqrt L := by
    have h : G ≤ 2 * Real.sqrt L * (1 - ε) := by
      calc
        G ≤ Real.sqrt L := hG
        _ = 2 * Real.sqrt L * (1/2) := by ring
        _ ≤ 2 * Real.sqrt L * (1 - ε) := by
          nlinarith
    have h' : G / (1 - ε) ≤ (2 * Real.sqrt L * (1 - ε)) / (1 - ε) :=
      (div_le_div_iff_of_pos_right h_one_minus_ε_pos).mpr h
    have h'' : (2 * Real.sqrt L * (1 - ε)) / (1 - ε) = 2 * Real.sqrt L := by
      field_simp [h_one_minus_ε_pos.ne']
    rw [h''] at h'
    exact h'
  have hpip_le_two_sqrtL : pip ≤ 2 * Real.sqrt L := by
    rw [hpip]
    exact max_le h_one_le_two_sqrtL hG_div_le_two_sqrtL
  -- |gv + e| ≤ 1 + √Lg
  have h_gv_plus_e_abs_le : |gv + e| ≤ 1 + Real.sqrt Lg := by
    have h_le : gv + e ≤ 1 + Real.sqrt Lg := by
      have he_le : e ≤ Real.sqrt Lg := by
        calc
          e ≤ |e| := le_abs_self e
          _ ≤ Real.sqrt Lg := he
      nlinarith
    have h_neg_le : -(1 + Real.sqrt Lg) ≤ gv + e := by
      have h_neg_e_le : -Real.sqrt Lg ≤ e := by
        calc
          -Real.sqrt Lg ≤ -|e| := by nlinarith
          _ ≤ e := neg_abs_le e
      nlinarith
    exact abs_le.mpr ⟨h_neg_le, h_le⟩
  -- pip - 1 ≥ 0
  have hpip_sub_one_nonneg : 0 ≤ pip - 1 := by nlinarith
  -- 2(pip-1)/ε ≤ 4√L/ε
  have h_term2_le : 2 * (pip - 1) / ε ≤ 4 * Real.sqrt L / ε := by
    apply (div_le_div_iff_of_pos_right hε0).mpr
    nlinarith
  -- Now the main bound
  have h_main : |pip * (gv + e) + 2 * (pip - 1) / ε| ≤ 2 * Real.sqrt L * (1 + Real.sqrt Lg) + 4 * Real.sqrt L / ε := by
    calc
      |pip * (gv + e) + 2 * (pip - 1) / ε| ≤ |pip * (gv + e)| + |2 * (pip - 1) / ε| := abs_add_le _ _
      _ = |pip| * |gv + e| + |2 * (pip - 1) / ε| := by rw [abs_mul]
      _ = pip * |gv + e| + |2 * (pip - 1) / ε| := by rw [abs_of_nonneg hpip_nonneg]
      _ = pip * |gv + e| + |2 * (pip - 1)| / |ε| := by rw [abs_div]
      _ = pip * |gv + e| + |2 * (pip - 1)| / ε := by rw [abs_of_nonneg hε_nonneg]
      _ = pip * |gv + e| + 2 * |pip - 1| / ε := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = pip * |gv + e| + 2 * (pip - 1) / ε := by rw [abs_of_nonneg hpip_sub_one_nonneg]
      _ ≤ pip * (1 + Real.sqrt Lg) + 2 * (pip - 1) / ε := by
        have h_mul : pip * |gv + e| ≤ pip * (1 + Real.sqrt Lg) :=
          mul_le_mul_of_nonneg_left h_gv_plus_e_abs_le hpip_nonneg
        nlinarith
      _ ≤ (2 * Real.sqrt L) * (1 + Real.sqrt Lg) + 2 * (pip - 1) / ε := by
        have h_mul : pip * (1 + Real.sqrt Lg) ≤ (2 * Real.sqrt L) * (1 + Real.sqrt Lg) :=
          mul_le_mul_of_nonneg_right hpip_le_two_sqrtL (by nlinarith [Real.sqrt_nonneg Lg])
        nlinarith
      _ ≤ (2 * Real.sqrt L) * (1 + Real.sqrt Lg) + 4 * Real.sqrt L / ε := by
        nlinarith
  -- Now we need to show: 2√L*(1+√Lg) + 4√L/ε ≤ L/(2ε)
  -- Multiply by 2ε > 0: 4ε√L*(1+√Lg) + 8√L ≤ L
  have h_final : 2 * Real.sqrt L * (1 + Real.sqrt Lg) + 4 * Real.sqrt L / ε ≤ L / (2 * ε) := by
    rw [le_div_iff₀ (by nlinarith : 0 < 2 * ε)]
    have h_mul : (2 * Real.sqrt L * (1 + Real.sqrt Lg) + 4 * Real.sqrt L / ε) * (2 * ε) =
        4 * ε * Real.sqrt L * (1 + Real.sqrt Lg) + 8 * Real.sqrt L := by
      field_simp [hε0.ne']
      ring
    rw [h_mul]
    -- Goal: 4ε√L*(1+√Lg) + 8√L ≤ L
    have hLg_bound : Lg ≤ L/27 := by
      calc
        Lg ≤ 4/3 * (L/36) := hLgL
        _ = L/27 := by ring
    have h_sqrtLg_nonneg : 0 ≤ Real.sqrt Lg := Real.sqrt_nonneg _
    have h4ε_le_2 : 4 * ε ≤ 2 := by nlinarith
    have hε_bound : 4 * ε * Real.sqrt L ≤ 2 * Real.sqrt L := by
      nlinarith
    have hε_bound2 : 4 * ε * Real.sqrt L * Real.sqrt Lg ≤ 2 * Real.sqrt L * Real.sqrt Lg := by
      have h_nonneg_prod : 0 ≤ Real.sqrt L * Real.sqrt Lg :=
        mul_nonneg hsqrtL_nonneg h_sqrtLg_nonneg
      nlinarith
    have h_total : 4 * ε * Real.sqrt L * (1 + Real.sqrt Lg) + 8 * Real.sqrt L ≤
        10 * Real.sqrt L + 2 * Real.sqrt L * Real.sqrt Lg := by
      nlinarith
    have h_key : 2 * Real.sqrt L * Real.sqrt Lg ≤ Real.sqrt (8/36) * L :=
      yb_sqrt_ineq_aux L Lg hL_nonneg hLg_bound
    -- Now: 10√L + 2√L√Lg ≤ 10√L + √(8/36)*L ≤ L
    nlinarith
  -- Combine: |Y| ≤ 2√L*(1+√Lg) + 4√L/ε ≤ L/(2ε)
  nlinarith

/-! ## Leaves -/

theorem closure_level {d : ℕ} (K : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) (a : ℝ)
    (hf : Continuous f) (y : Fin d → ℝ) (hy : y ∈ closure (K \ {x | x ∈ K ∧ f x ≤ a})) : a ≤ f y := by
  have h_subset : K \ {x | x ∈ K ∧ f x ≤ a} ⊆ {x | a ≤ f x} := by
    intro x hx
    rcases hx with ⟨hxK, hx_not⟩
    have h_not_le : ¬ f x ≤ a := by
      intro hle
      apply hx_not
      exact ⟨hxK, hle⟩
    exact le_of_lt (lt_of_not_ge h_not_le)
  have h_closed : IsClosed {x | a ≤ f x} := by
    have := isClosed_le (continuous_const : Continuous fun _ : Fin d → ℝ => a) hf
    simpa using this
  have h_closure_subset : closure (K \ {x | x ∈ K ∧ f x ≤ a}) ⊆ {x | a ≤ f x} :=
    closure_minimal h_subset h_closed
  exact h_closure_subset hy

theorem convexOn_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (K : Set E) (hK : Convex ℝ K)
    (F : Finset ℕ) (f : ℕ → E → ℝ) (hf : ∀ u ∈ F, ConvexOn ℝ K (f u)) :
    ConvexOn ℝ K (fun x => ∑ u ∈ F, f u x) := by
  induction' F using Finset.induction_on with a s ha ih
  · -- empty sum: constant zero function
    simp [convexOn_const (0 : ℝ) hK]
  · -- insert a into s
    have ha_mem : a ∈ insert a s := Finset.mem_insert_self a s
    have ha_conv : ConvexOn ℝ K (f a) := hf a ha_mem
    have h_sum : ConvexOn ℝ K (fun x => ∑ u ∈ s, f u x) := ih fun u hu => hf u (Finset.mem_insert_of_mem hu)
    convert ha_conv.add h_sum using 1
    ext x
    simp [Finset.sum_insert ha]

theorem grad_arith (η κ l k0 L ε d x δ n σ2 : ℝ) (hη : 0 < η) (hκ : κ = 1 / 4)
    (hl : 0 < l) (hk0 : 0 < k0) (hk1 : k0 ≤ 21 / 20) (hL : 504 ≤ L) (hε : 0 < ε) (hd : 1 ≤ d) (hx : x = L / 36)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n) (hσ : 0 < σ2) (r6a : η * l * L / (2 * ε) ≤ 1)
    (c500 : 500 * δ * n ^ ((3 : ℝ) / 2) * d * L ^ 2 ≤ 1) (c4 : 4 * δ / σ2 ≤ 1) :
    n * (η * κ * (l * k0 * (L / (2 * ε)) * (32 / 9 * d * x + 1) / δ)) ≤ 1 / (4 * δ ^ 2) ∧
      σ2⁻¹ + 2 * (n * (η * κ * (l * k0 * (L / (2 * ε)) * (32 / 9 * d * x + 1) / δ))) ≤ 1 / δ ^ 2 := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hnpos : 0 < n := by linarith
  have hdpos : 0 < d := by linarith
  have hδpos : 0 < δ := hδ
  have hσ2pos : 0 < σ2 := hσ
  set M := n * (η * κ * (l * k0 * (L / (2 * ε)) * (32 / 9 * d * x + 1) / δ)) with hM_def
  -- Simplify M using κ = 1/4
  have hM_eq : M = n * η * l * k0 * (L / (2 * ε)) * (32 / 9 * d * x + 1) / (4 * δ) := by
    dsimp [M]
    rw [hκ]
    ring
  -- Bound η * l * (L/(2ε)) ≤ 1
  have h_factor_bound : η * l * (L / (2 * ε)) ≤ 1 := by
    calc
      η * l * (L / (2 * ε)) = (η * l * L) / (2 * ε) := by ring
      _ ≤ 1 := r6a
  -- M ≤ n * k0 * (32/9*d*x + 1) / (4*δ)
  have hM_bound1 : M ≤ n * k0 * (32 / 9 * d * x + 1) / (4 * δ) := by
    rw [hM_eq]
    have h_rearrange : n * η * l * k0 * (L / (2 * ε)) * (32 / 9 * d * x + 1) / (4 * δ) =
        n * k0 * (η * l * (L / (2 * ε))) * (32 / 9 * d * x + 1) / (4 * δ) := by ring
    rw [h_rearrange]
    have h_common_nonneg : 0 ≤ n * k0 * (32 / 9 * d * x + 1) / (4 * δ) := by
      have hx_nonneg : 0 ≤ x := by
        rw [hx]
        have hL_nonneg : 0 ≤ L := by linarith
        nlinarith
      have h_num_nonneg : 0 ≤ 32 / 9 * d * x + 1 := by
        have hdx_nonneg : 0 ≤ d * x := mul_nonneg (by linarith) hx_nonneg
        nlinarith
      refine div_nonneg (mul_nonneg (by nlinarith) h_num_nonneg) (by positivity)
    calc
      n * k0 * (η * l * (L / (2 * ε))) * (32 / 9 * d * x + 1) / (4 * δ) =
          (η * l * (L / (2 * ε))) * (n * k0 * (32 / 9 * d * x + 1) / (4 * δ)) := by ring
      _ ≤ 1 * (n * k0 * (32 / 9 * d * x + 1) / (4 * δ)) :=
        mul_le_mul_of_nonneg_right h_factor_bound h_common_nonneg
      _ = n * k0 * (32 / 9 * d * x + 1) / (4 * δ) := by ring
  -- Substitute x = L/36
  have hx_val : 32 / 9 * d * x + 1 = (8 / 81) * d * L + 1 := by
    rw [hx]
    ring
  -- (8/81)*d*L + 1 ≤ d*L (since d*L ≥ 504)
  have h_extra_bound : (8 / 81) * d * L + 1 ≤ d * L := by
    have h_dL : 504 ≤ d * L := by
      nlinarith
    nlinarith
  -- M ≤ (21/80) * n * d * L / δ
  have hM_bound2 : M ≤ (21 / 80) * n * d * L / δ := by
    rw [hx_val] at hM_bound1
    have h_inner : n * k0 * ((8 / 81) * d * L + 1) / (4 * δ) ≤ n * k0 * (d * L) / (4 * δ) := by
      have h_common_nonneg : 0 ≤ n * k0 / (4 * δ) := by
        refine div_nonneg (by nlinarith) (by positivity)
      calc
        n * k0 * ((8 / 81) * d * L + 1) / (4 * δ) = ((8 / 81) * d * L + 1) * (n * k0 / (4 * δ)) := by ring
        _ ≤ (d * L) * (n * k0 / (4 * δ)) := mul_le_mul_of_nonneg_right h_extra_bound h_common_nonneg
        _ = n * k0 * (d * L) / (4 * δ) := by ring
    have h_k0_bound : n * k0 * (d * L) / (4 * δ) ≤ (21/80) * n * d * L / δ := by
      have h_common_nonneg : 0 ≤ n * (d * L) / (4 * δ) := by
        refine div_nonneg (by nlinarith) (by positivity)
      calc
        n * k0 * (d * L) / (4 * δ) = k0 * (n * (d * L) / (4 * δ)) := by ring
        _ ≤ (21/20) * (n * (d * L) / (4 * δ)) := mul_le_mul_of_nonneg_right hk1 h_common_nonneg
        _ = n * (21/20) * (d * L) / (4 * δ) := by ring
        _ = (21/80) * n * d * L / δ := by ring
    exact le_trans hM_bound1 (le_trans h_inner h_k0_bound)
  -- n ≤ n^(3/2)
  have hn_pow : n ≤ n ^ ((3 : ℝ) / 2) := by
    calc
      n = n ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ n ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1 : ℝ) ≤ (3 : ℝ) / 2)
  -- L ≤ L^2
  have hL_sq : L ≤ L ^ 2 := by
    nlinarith
  -- From c500: 500*δ*n*d*L ≤ 1
  have h_c500' : 500 * δ * n * d * L ≤ 1 := by
    have h_temp : n * d * L ≤ (n ^ ((3 : ℝ) / 2)) * d * (L ^ 2) := by
      have h_step1 : n * d * L ≤ (n ^ ((3 : ℝ) / 2)) * d * L := by
        calc
          n * d * L = n * (d * L) := by ring
          _ ≤ (n ^ ((3 : ℝ) / 2)) * (d * L) :=
            mul_le_mul_of_nonneg_right hn_pow (mul_nonneg (by linarith) (by linarith))
          _ = (n ^ ((3 : ℝ) / 2)) * d * L := by ring
      have h_step2 : (n ^ ((3 : ℝ) / 2)) * d * L ≤ (n ^ ((3 : ℝ) / 2)) * d * (L ^ 2) :=
        mul_le_mul_of_nonneg_left hL_sq (by positivity)
      linarith
    have h_mul : 500 * δ * n * d * L ≤ 500 * δ * (n ^ ((3 : ℝ) / 2)) * d * (L ^ 2) := by
      have h := mul_le_mul_of_nonneg_left h_temp (by positivity : 0 ≤ 500 * δ)
      -- h: 500*δ * (n*d*L) ≤ 500*δ * (n^(3/2)*d*L^2)
      -- Need: 500*δ*n*d*L ≤ 500*δ*n^(3/2)*d*L^2
      simpa [mul_assoc] using h
    exact le_trans h_mul c500
  -- n*d*L ≤ 1/(500*δ)
  have h_ndL_bound : n * d * L ≤ 1 / (500 * δ) := by
    field_simp [hδpos.ne.symm]
    -- Goal: n * d * L * (500 * δ) ≤ 1
    -- h_c500' : 500 * δ * n * d * L ≤ 1
    -- These are equal by commutativity
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_c500'
  -- First goal: M ≤ 1/(4*δ^2)
  have h_first_goal : M ≤ 1 / (4 * δ ^ 2) := by
    have h_intermediate : M ≤ (21/80) * (1 / (500 * δ)) / δ := by
      have h_div_nonneg : 0 ≤ (21/80) / δ := by
        refine div_nonneg (by norm_num) (by positivity)
      calc
        M ≤ (21/80) * n * d * L / δ := hM_bound2
        _ = ((21/80) / δ) * (n * d * L) := by ring
        _ ≤ ((21/80) / δ) * (1 / (500 * δ)) := mul_le_mul_of_nonneg_left h_ndL_bound h_div_nonneg
        _ = (21/80) * (1 / (500 * δ)) / δ := by ring
    have h_final_bound : (21/80) * (1 / (500 * δ)) / δ ≤ 1 / (4 * δ ^ 2) := by
      have hLHS : (21/80) * (1 / (500 * δ)) / δ = 21 / (40000 * δ ^ 2) := by
        field_simp [hδpos.ne.symm]
        ring
      have hRHS : 1 / (4 * δ ^ 2) = 10000 / (40000 * δ ^ 2) := by
        field_simp [hδpos.ne.symm]
        ring
      rw [hLHS, hRHS]
      have hpos_denom : 0 ≤ 40000 * δ ^ 2 := by positivity
      exact div_le_div_of_nonneg_right (by norm_num) hpos_denom
    exact le_trans h_intermediate h_final_bound
  -- Second goal: σ2⁻¹ + 2*M ≤ 1/δ^2
  have h_second_goal : σ2⁻¹ + 2 * M ≤ 1 / δ ^ 2 := by
    -- σ2⁻¹ ≤ 1/(4*δ) from c4
    have hσ2_inv : σ2⁻¹ ≤ 1 / (4 * δ) := by
      have hσ2_ge : 4 * δ ≤ σ2 := (div_le_one hσ2pos).mp c4
      have hpos_4δ : 0 < 4 * δ := by positivity
      rw [inv_eq_one_div]
      exact (one_div_le_one_div hσ2pos hpos_4δ).mpr hσ2_ge
    -- 1/(4*δ) ≤ 1/(4*δ^2) since δ^2 ≤ δ (0 < δ < 1)
    have h_δ_bound : 1 / (4 * δ) ≤ 1 / (4 * δ ^ 2) := by
      have h_δ_sq_le_δ : δ ^ 2 ≤ δ := by
        calc
          δ ^ 2 = δ * δ := by ring
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1.le (by linarith)
          _ = δ := by ring
      have hpos_4δsq : 0 < 4 * δ ^ 2 := by positivity
      have hpos_4δ : 0 < 4 * δ := by positivity
      have h_δ_sq_le_δ' : 4 * δ ^ 2 ≤ 4 * δ := by gcongr
      exact (one_div_le_one_div hpos_4δ hpos_4δsq).mpr h_δ_sq_le_δ'
    -- σ2⁻¹ ≤ 1/(4*δ^2)
    have hσ2_inv' : σ2⁻¹ ≤ 1 / (4 * δ ^ 2) := le_trans hσ2_inv h_δ_bound
    -- 2*M ≤ 1/(2*δ^2) from h_first_goal
    have h_2M_bound : 2 * M ≤ 1 / (2 * δ ^ 2) := by
      have hgoal : 2 * M * (2 * δ ^ 2) ≤ 1 := by
        have hM : M * (4 * δ ^ 2) ≤ 1 := by
          field_simp [hδpos.ne.symm] at h_first_goal
          -- h_first_goal: M * 4 * δ ^ 2 ≤ 1
          -- Need: M * (4 * δ ^ 2) ≤ 1
          simpa [mul_assoc] using h_first_goal
        calc
          2 * M * (2 * δ ^ 2) = M * (4 * δ ^ 2) := by ring
          _ ≤ 1 := hM
      field_simp [hδpos.ne.symm]
      -- Goal: 2 ^ 2 * M * δ ^ 2 ≤ 1
      -- hgoal: 2 * M * (2 * δ ^ 2) ≤ 1
      -- These are equal by ring
      simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using hgoal
    -- Sum bound
    have h_total : σ2⁻¹ + 2 * M ≤ 1 / (4 * δ ^ 2) + 1 / (2 * δ ^ 2) :=
      add_le_add hσ2_inv' h_2M_bound
    have h_calc : 1 / (4 * δ ^ 2) + 1 / (2 * δ ^ 2) = 3 / (4 * δ ^ 2) := by ring
    rw [h_calc] at h_total
    -- 3/(4*δ^2) ≤ 1/δ^2
    have h_final : 3 / (4 * δ ^ 2) ≤ 1 / δ ^ 2 := by
      calc
        3 / (4 * δ ^ 2) = (3/4) * (1 / δ ^ 2) := by
          field_simp [hδpos.ne.symm]
        _ ≤ 1 * (1 / δ ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = 1 / δ ^ 2 := by ring
    exact le_trans h_total h_final
  exact And.intro h_first_goal h_second_goal

open Real Finset in
theorem oNorm_tri {d : ℕ} (u v : Fin d → ℝ) (a : ℝ) (F : Finset ℕ) (w : ℕ → Fin d → ℝ) :
    Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) ∧
      Real.sqrt ((a • u) ⬝ᵥ (a • u)) = |a| * Real.sqrt (u ⬝ᵥ u) ∧
      Real.sqrt ((∑ i ∈ F, w i) ⬝ᵥ (∑ i ∈ F, w i)) ≤ ∑ i ∈ F, Real.sqrt (w i ⬝ᵥ w i) := by
  -- Helper lemma: Real.sqrt (x ⬝ᵥ x) = ‖WithLp.toLp 2 x‖
  have h_norm_eq {x : Fin d → ℝ} : Real.sqrt (x ⬝ᵥ x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    calc
      Real.sqrt (x ⬝ᵥ x) = Real.sqrt (∑ i : Fin d, (x i) ^ 2) := by
        rw [dotProduct]
        simp [pow_two]
      _ = Real.sqrt (∑ i : Fin d, ‖x i‖ ^ 2) := by
        simp [sq_abs]
      _ = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
        rw [PiLp.norm_eq_of_L2 (x := WithLp.toLp 2 x)]
  -- Now prove the three conjuncts
  have h_add : Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
    rw [h_norm_eq (x := u + v), h_norm_eq (x := u), h_norm_eq (x := v)]
    rw [WithLp.toLp_add 2 u v]
    exact norm_add_le _ _
  have h_smul : Real.sqrt ((a • u) ⬝ᵥ (a • u)) = |a| * Real.sqrt (u ⬝ᵥ u) := by
    rw [h_norm_eq (x := a • u), h_norm_eq (x := u)]
    rw [WithLp.toLp_smul 2 a u]
    rw [norm_smul]
    simp [Real.norm_eq_abs]
  have h_sum : Real.sqrt ((∑ i ∈ F, w i) ⬝ᵥ (∑ i ∈ F, w i)) ≤ ∑ i ∈ F, Real.sqrt (w i ⬝ᵥ w i) := by
    rw [h_norm_eq (x := ∑ i ∈ F, w i)]
    rw [WithLp.toLp_sum 2 (Fin d → ℝ) F w]
    have h := norm_sum_le F (fun i => (WithLp.toLp 2 (w i) : EuclideanSpace ℝ (Fin d)))
    apply h.trans
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [h_norm_eq (x := w i)]
  exact And.intro h_add (And.intro h_smul h_sum)

theorem psd_of_sq_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : ∀ v : Fin d → ℝ, v ⬝ᵥ (B *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) : (A - B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hA.sub hB
  · intro v
    have h_nonneg : 0 ≤ v ⬝ᵥ ((A - B) *ᵥ v) := by
      calc
        0 ≤ (v ⬝ᵥ (A *ᵥ v)) - (v ⬝ᵥ (B *ᵥ v)) := by
          linarith [h v]
        _ = v ⬝ᵥ (A *ᵥ v - B *ᵥ v) := by rw [dotProduct_sub]
        _ = v ⬝ᵥ ((A - B) *ᵥ v) := by rw [Matrix.sub_mulVec]
    simpa using h_nonneg

theorem sb_arith (δ R r0 : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 1 ≤ R) (hr0 : 0 ≤ r0)
    (hr1 : r0 ≤ 1) :
    0 < δ ^ 2 / (R * (R + 1)) ∧ δ ^ 2 / (R * (R + 1)) ≤ 1 ∧
      δ ^ 2 / (R * (R + 1)) * (R + r0) ≤ min (2 / (2 * (R / δ ^ 2))) (Real.sqrt (2 / δ⁻¹)) := by
  have hδsq_pos : 0 < δ ^ 2 := pow_pos hδ 2
  have hRpos : 0 < R := by linarith
  have hR1pos : 0 < R + 1 := by linarith
  have h_denom_pos : 0 < R * (R + 1) := mul_pos hRpos hR1pos
  set s := δ ^ 2 / (R * (R + 1)) with hs
  have hs_pos : 0 < s := by
    dsimp [s]
    exact div_pos hδsq_pos h_denom_pos
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hs_le_one : s ≤ 1 := by
    have h_denom_ge_two : 2 ≤ R * (R + 1) := by
      nlinarith
    have hδsq_lt_one : δ ^ 2 < 1 := by
      nlinarith
    have h1 : s ≤ δ ^ 2 / 2 := by
      dsimp [s]
      refine div_le_div_of_nonneg_left (by nlinarith) (by norm_num) h_denom_ge_two
    have h2 : δ ^ 2 / 2 < 1 / 2 :=
      div_lt_div_of_pos_right hδsq_lt_one (by norm_num : (0 : ℝ) < 2)
    have h3 : (1 : ℝ) / 2 ≤ 1 := by norm_num
    linarith
  have h_le_delta_sq_div_R : s * (R + r0) ≤ δ ^ 2 / R := by
    calc
      s * (R + r0) = (δ ^ 2 / (R * (R + 1))) * (R + r0) := rfl
      _ ≤ (δ ^ 2 / (R * (R + 1))) * (R + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hs_nonneg
        nlinarith
      _ = δ ^ 2 / R := by
        field_simp [hRpos.ne.symm, hR1pos.ne.symm]
  have h_bound1 : s * (R + r0) ≤ 2 / (2 * (R / δ ^ 2)) := by
    calc
      s * (R + r0) ≤ δ ^ 2 / R := h_le_delta_sq_div_R
      _ = 2 / (2 * (R / δ ^ 2)) := by
        field_simp [hδsq_pos.ne.symm, hRpos.ne.symm]
  have h_bound2 : s * (R + r0) ≤ Real.sqrt (2 / δ⁻¹) := by
    have h_sqrt_bound : δ ^ 2 / R ≤ Real.sqrt (2 * δ) := by
      have h_nonneg : 0 ≤ δ ^ 2 / R := div_nonneg (by nlinarith) (by nlinarith)
      have h_sq_bound : (δ ^ 2 / R) ^ 2 ≤ 2 * δ := by
        have hδcube_le : δ ^ 3 ≤ 2 * R ^ 2 := by
          have hδcube_lt_one : δ ^ 3 < 1 := by
            nlinarith
          have hR_sq_ge_one : 1 ≤ R ^ 2 := by
            nlinarith
          nlinarith
        calc
          (δ ^ 2 / R) ^ 2 = δ ^ 4 / R ^ 2 := by ring
          _ ≤ 2 * δ := by
            rw [div_le_iff₀ (pow_pos hRpos 2)]
            nlinarith
      calc
        δ ^ 2 / R = Real.sqrt ((δ ^ 2 / R) ^ 2) := by
          rw [Real.sqrt_sq h_nonneg]
        _ ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt h_sq_bound
    calc
      s * (R + r0) ≤ δ ^ 2 / R := h_le_delta_sq_div_R
      _ ≤ Real.sqrt (2 * δ) := h_sqrt_bound
      _ = Real.sqrt (2 / δ⁻¹) := by
        field_simp [hδ.ne.symm]
  have h_min : s * (R + r0) ≤ min (2 / (2 * (R / δ ^ 2))) (Real.sqrt (2 / δ⁻¹)) :=
    le_min h_bound1 h_bound2
  exact ⟨hs_pos, hs_le_one, h_min⟩

theorem t2_arith (δ k0 Y2 X d n L : ℝ) (hδ : 0 < δ) (hk0 : 0 < k0) (hk1 : k0 ≤ 21 / 20)
    (hY0 : 0 ≤ Y2) (hY : Y2 ≤ 22 * n) (hX : X = 32 / 9 * d * (L / 36)) (hd : 0 ≤ d) (hn : 0 ≤ n) (hL : 0 ≤ L) :
    δ⁻¹ * (4 * k0 * Y2 * X) ≤ 16 * d * n * L / δ := by
  have hδinv_nonneg : 0 ≤ δ⁻¹ := by positivity
  have h_mul : 4 * k0 * Y2 * X ≤ 16 * d * n * L := by
    rw [hX]
    have hk0' : 0 ≤ k0 := by linarith
    have h_nonneg_rest : 0 ≤ 4 * Y2 * (32 / 9 * d * (L / 36)) := by positivity
    have h_first : 4 * k0 * Y2 * (32 / 9 * d * (L / 36)) ≤
        4 * (21 / 20) * Y2 * (32 / 9 * d * (L / 36)) := by
      calc
        4 * k0 * Y2 * (32 / 9 * d * (L / 36)) =
            (4 * Y2 * (32 / 9 * d * (L / 36))) * k0 := by ring
        _ ≤ (4 * Y2 * (32 / 9 * d * (L / 36))) * (21 / 20) :=
          mul_le_mul_of_nonneg_left hk1 h_nonneg_rest
        _ = 4 * (21 / 20) * Y2 * (32 / 9 * d * (L / 36)) := by ring
    have h_nonneg_rest2 : 0 ≤ 4 * (21 / 20) * Y2 := by positivity
    have h_second : 4 * (21 / 20) * Y2 * (32 / 9 * d * (L / 36)) ≤
        4 * (21 / 20) * (22 * n) * (32 / 9 * d * (L / 36)) := by
      calc
        4 * (21 / 20) * Y2 * (32 / 9 * d * (L / 36)) =
            (4 * (21 / 20) * (32 / 9 * d * (L / 36))) * Y2 := by ring
        _ ≤ (4 * (21 / 20) * (32 / 9 * d * (L / 36))) * (22 * n) :=
          mul_le_mul_of_nonneg_left hY (by positivity)
        _ = 4 * (21 / 20) * (22 * n) * (32 / 9 * d * (L / 36)) := by ring
    have h_third : 4 * (21 / 20) * (22 * n) * (32 / 9 * d * (L / 36)) ≤ 16 * d * n * L := by
      have h_eq : 4 * (21 / 20) * (22 * n) * (32 / 9 * d * (L / 36)) = (1232/135 : ℝ) * (d * n * L) := by
        field_simp
        ring
      rw [h_eq]
      have h_nonneg_dnL : 0 ≤ d * n * L := by positivity
      nlinarith
    exact le_trans h_first (le_trans h_second h_third)
  calc
    δ⁻¹ * (4 * k0 * Y2 * X) ≤ δ⁻¹ * (16 * d * n * L) :=
      mul_le_mul_of_nonneg_left h_mul hδinv_nonneg
    _ = 16 * d * n * L / δ := by ring

theorem w1_arith (l η d δ σ2 L : ℝ) (hl : 0 < l) (hη : 0 < η) (hd : 0 ≤ d) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hσ : 0 < σ2) (hσ1 : 2 * σ2 ≤ 1) (hσδ : 4 * δ ≤ σ2) (hL : L = 36 * Real.log (1 / δ)) :
    0 ≤ Real.log (1 / (2 * δ) * σ2) ∧
      2 / l * (2 / (η * (1 / 4)) * (2 * d * Real.log (1 / (2 * δ) * σ2))) ≤ d * L / (l * η) := by
  have hpos_arg : 0 < 1 / (2 * δ) * σ2 := by
    have hpos_div : 0 < 1 / (2 * δ) := div_pos (by norm_num) (by nlinarith)
    exact mul_pos hpos_div hσ
  have h_ge_one : 1 ≤ 1 / (2 * δ) * σ2 := by
    have hdivpos : 0 ≤ 2 * δ := by nlinarith
    have h : 4 * δ ≤ σ2 := hσδ
    have h_two : (1 : ℝ) ≤ 2 := by norm_num
    have h_two_eq : (2 : ℝ) = (4 * δ) / (2 * δ) := by field_simp; ring
    have h_div_le : (4 * δ) / (2 * δ) ≤ σ2 / (2 * δ) :=
      div_le_div_of_nonneg_right h hdivpos
    calc
      (1 : ℝ) ≤ 2 := h_two
      _ = (4 * δ) / (2 * δ) := h_two_eq
      _ ≤ σ2 / (2 * δ) := h_div_le
      _ = 1 / (2 * δ) * σ2 := by ring
  have h_log_nonneg : 0 ≤ Real.log (1 / (2 * δ) * σ2) :=
    Real.log_nonneg h_ge_one
  have h_log_bound : Real.log (1 / (2 * δ) * σ2) ≤ Real.log (1 / δ) := by
    apply Real.log_le_log hpos_arg
    have hσ2_half : σ2 ≤ 1/2 := by linarith
    have h_div1 : 1 / (2 * δ) * σ2 ≤ 1 / (4 * δ) := by
      calc
        1 / (2 * δ) * σ2 = σ2 / (2 * δ) := by ring
        _ ≤ (1/2) / (2 * δ) := by
          refine div_le_div_of_nonneg_right hσ2_half ?_
          nlinarith
        _ = 1 / (4 * δ) := by ring
    have h_div2 : 1 / (4 * δ) ≤ 1 / δ := by
      have hpos_4δ : 0 < 4 * δ := by nlinarith
      refine (one_div_le_one_div hpos_4δ hδ).mpr ?_
      nlinarith
    linarith
  have h_log_nonneg' : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (one_le_one_div hδ (by linarith))
  have h_main : 32 * d * Real.log (1 / (2 * δ) * σ2) ≤ d * L := by
    rw [hL]
    by_cases hd0 : d = 0
    · rw [hd0]; simp
    · have hdpos : 0 < d := by
        by_contra! h
        apply hd0
        linarith
      have hdiv : 32 * Real.log (1 / (2 * δ) * σ2) ≤ 36 * Real.log (1 / δ) := by
        nlinarith
      nlinarith
  have h_second : 2 / l * (2 / (η * (1 / 4)) * (2 * d * Real.log (1 / (2 * δ) * σ2))) ≤ d * L / (l * η) := by
    have hpos_lη : 0 ≤ l * η := by nlinarith
    have hcalc : 2 / l * (2 / (η * (1 / 4)) * (2 * d * Real.log (1 / (2 * δ) * σ2))) = 32 * d * Real.log (1 / (2 * δ) * σ2) / (l * η) := by
      field_simp [ne_of_gt hl, ne_of_gt hη]
      ring
    rw [hcalc]
    exact div_le_div_of_nonneg_right h_main hpos_lη
  exact And.intro h_log_nonneg h_second

theorem z_arith (η L ε k0 X δ n d x R : ℝ) (hη0 : 0 < η) (hη : η ≤ 1) (hR : 1 ≤ R)
    (hε : 0 < ε) (hεn : 1 / Real.sqrt n ≤ ε) (hn : 1 ≤ n) (hd : 1 ≤ d) (hx : 1 ≤ x) (hk0 : 0 < k0) (hδ : 0 < δ)
    (hX : X = 32 / 9 * d * x) (hL : L = 36 * x)
    (cz : 1 / 4 * Real.sqrt k0 * 36 * Real.sqrt (32 / 9) * δ ^ ((3 : ℝ) / 2) * n ^ ((3 : ℝ) / 2) * Real.sqrt d *
      x ^ ((3 : ℝ) / 2) ≤ 3 / 4) :
    η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))) ≤ 3 / 4 * R / δ ^ 2 := by
  have hnpos : 0 < n := by linarith
  have hdpos : 0 < d := by linarith
  have hxpos : 0 < x := by linarith
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrt_d_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have hsqrt_x_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsqrt_k0_pos : 0 < Real.sqrt k0 := Real.sqrt_pos.mpr hk0
  have hsqrt_δ_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hXpos : 0 ≤ X := by
    rw [hX]
    positivity
  have h32_9_nonneg : 0 ≤ (32 : ℝ) / 9 := by norm_num
  have h_nonneg_n : 0 ≤ n := by linarith
  have h_nonneg_x : 0 ≤ x := by linarith
  have h_nonneg_d : 0 ≤ d := by linarith
  have h_nonneg_k0 : 0 ≤ k0 := by linarith
  have h_nonneg_δ : 0 ≤ δ := by linarith
  -- 1/ε ≤ √n
  have h_one_div_ε_le_sqrt_n : 1 / ε ≤ Real.sqrt n := by
    have h1 : 1 ≤ ε * Real.sqrt n := by
      calc
        1 = (1 / Real.sqrt n) * Real.sqrt n := by field_simp [hsqrt_n_pos.ne']
        _ ≤ ε * Real.sqrt n := mul_le_mul_of_nonneg_right hεn (by positivity)
    calc
      1 / ε ≤ (ε * Real.sqrt n) / ε := div_le_div_of_nonneg_right h1 (by positivity)
      _ = Real.sqrt n := by field_simp [hε.ne']
  -- Express √(X/δ) in terms of √d, √x, √δ
  have h_sqrt_X_div_δ : Real.sqrt (X / δ) = Real.sqrt (32/9) * Real.sqrt d * Real.sqrt x / Real.sqrt δ := by
    rw [hX]
    calc
      Real.sqrt (((32 : ℝ) / 9 * d * x) / δ) = Real.sqrt (((32 : ℝ) / 9) * (d * x) / δ) := by ring
      _ = Real.sqrt (((32 : ℝ) / 9) * ((d * x) / δ)) := by ring
      _ = Real.sqrt (32/9) * Real.sqrt ((d * x) / δ) := by
        rw [Real.sqrt_mul h32_9_nonneg]
      _ = Real.sqrt (32/9) * (Real.sqrt (d * x) / Real.sqrt δ) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ d * x) _]
      _ = Real.sqrt (32/9) * ((Real.sqrt d * Real.sqrt x) / Real.sqrt δ) := by
        rw [Real.sqrt_mul h_nonneg_d]
      _ = Real.sqrt (32/9) * Real.sqrt d * Real.sqrt x / Real.sqrt δ := by ring
  -- Express n * √n as n^{3/2}
  have hn_pow : n * Real.sqrt n = n ^ ((3 : ℝ) / 2) := by
    calc
      n * Real.sqrt n = n ^ (1 : ℝ) * n ^ ((1 : ℝ) / 2) := by
        simp [Real.sqrt_eq_rpow]
      _ = n ^ ((1 : ℝ) + (1 : ℝ) / 2) := by rw [Real.rpow_add hnpos (1 : ℝ) ((1 : ℝ) / 2)]
      _ = n ^ ((3 : ℝ) / 2) := by ring
  -- Express x * √x as x^{3/2}
  have hx_pow : x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
    calc
      x * Real.sqrt x = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := by
        simp [Real.sqrt_eq_rpow]
      _ = x ^ ((1 : ℝ) + (1 : ℝ) / 2) := by rw [Real.rpow_add hxpos (1 : ℝ) ((1 : ℝ) / 2)]
      _ = x ^ ((3 : ℝ) / 2) := by ring
  -- Express δ^2 / √δ as δ^{3/2}
  have hδ_pow : δ ^ 2 / Real.sqrt δ = δ ^ ((3 : ℝ) / 2) := by
    calc
      δ ^ 2 / Real.sqrt δ = δ ^ (2 : ℝ) / δ ^ ((1 : ℝ) / 2) := by
        simp [Real.sqrt_eq_rpow]
      _ = δ ^ ((2 : ℝ) - (1 : ℝ) / 2) := by
        rw [Real.rpow_sub hδ (2 : ℝ) ((1 : ℝ) / 2)]
      _ = δ ^ ((3 : ℝ) / 2) := by ring
  -- The main inequality: multiply both sides by δ^2 and show ≤ 3/4
  have h_main : δ ^ 2 * (η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ)))) ≤ 3 / 4 := by
    calc
      δ ^ 2 * (η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))))
          = (η / 2) * n * (L / (2 * ε)) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ ≤ (1 / 2) * n * (L / (2 * ε)) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by
        have hpos_common : 0 ≤ n * (L / (2 * ε)) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by
          have hL_nonneg : 0 ≤ L := by rw [hL]; positivity
          have h_div_nonneg : 0 ≤ L / (2 * ε) := div_nonneg hL_nonneg (by positivity)
          have h_sqrt_term_nonneg : 0 ≤ δ ^ 2 * Real.sqrt (X / δ) := by
            positivity
          positivity
        have h_eta_half : η / 2 ≤ 1 / 2 := by linarith
        nlinarith
      _ = n * (L / (2 * ε)) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) / 2 := by ring
      _ = n * L / (4 * ε) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ = n * (36 * x) / (4 * ε) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by rw [hL]
      _ = (9 * n * x / ε) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ = (9 * n * x / ε) * (Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ))) := by ring
      _ ≤ (9 * n * x * Real.sqrt n) * (Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ))) := by
        have hpos_factor : 0 ≤ Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by positivity
        have htemp : 9 * n * x / ε ≤ 9 * n * x * Real.sqrt n := by
          have hpos' : 0 ≤ 9 * n * x := by positivity
          calc
            9 * n * x / ε = (9 * n * x) * (1 / ε) := by ring
            _ ≤ (9 * n * x) * Real.sqrt n := mul_le_mul_of_nonneg_left h_one_div_ε_le_sqrt_n hpos'
            _ = 9 * n * x * Real.sqrt n := by ring
        exact mul_le_mul_of_nonneg_right htemp hpos_factor
      _ = (9 * n * x * Real.sqrt n) * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ = 9 * n * x * Real.sqrt n * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ = 9 * (n * Real.sqrt n) * x * Real.sqrt k0 * (δ ^ 2 * Real.sqrt (X / δ)) := by ring
      _ = 9 * (n * Real.sqrt n) * x * Real.sqrt k0 * (δ ^ 2 * (Real.sqrt (32/9) * Real.sqrt d * Real.sqrt x / Real.sqrt δ)) := by rw [h_sqrt_X_div_δ]
      _ = 9 * (n * Real.sqrt n) * (x * Real.sqrt x) * Real.sqrt k0 * Real.sqrt (32/9) * Real.sqrt d * (δ ^ 2 / Real.sqrt δ) := by
        ring
      _ = (9 * (n * Real.sqrt n) * Real.sqrt k0 * Real.sqrt (32/9) * Real.sqrt d * (δ ^ 2 / Real.sqrt δ)) * (x * Real.sqrt x) := by
        ring
      _ = (9 * (n ^ ((3 : ℝ) / 2)) * Real.sqrt k0 * Real.sqrt (32/9) * Real.sqrt d * (δ ^ ((3 : ℝ) / 2))) * (x ^ ((3 : ℝ) / 2)) := by
        rw [hn_pow, hx_pow, hδ_pow]
      _ = (1 / 4 * Real.sqrt k0 * 36 * Real.sqrt (32/9) * δ ^ ((3 : ℝ) / 2) * n ^ ((3 : ℝ) / 2) * Real.sqrt d * x ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ 3 / 4 := cz
  -- Now divide by δ^2 and use hR
  have h_final : η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))) ≤ 3 / 4 * (1 / δ ^ 2) := by
    have hpos_δsq : 0 < δ ^ 2 := by positivity
    calc
      η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))) = (δ ^ 2 * (η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))))) / δ ^ 2 := by
        field_simp [hpos_δsq.ne']
      _ ≤ (3 / 4) / δ ^ 2 := by
        gcongr
      _ = 3 / 4 * (1 / δ ^ 2) := by ring
  calc
    η / 2 * (n * (L / (2 * ε) * Real.sqrt k0 * Real.sqrt (X / δ))) ≤ 3 / 4 * (1 / δ ^ 2) := h_final
    _ ≤ 3 / 4 * (R / δ ^ 2) := by
      have hpos_34 : 0 ≤ (3/4 : ℝ) := by norm_num
      apply mul_le_mul_of_nonneg_left ?_ hpos_34
      exact div_le_div_of_nonneg_right hR (by positivity)
    _ = 3 / 4 * R / δ ^ 2 := by ring

end AdversarialBco.Poly.Layer2
