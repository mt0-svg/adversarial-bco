/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGCode
public import AdversarialBco.Poly.PgProcProof

@[expose] public section

/-!
# Procedure PG in VL: the linear algebra

* The spectral calculus of a symmetric matrix read off its eigenvectors (`trace_cfc_eq_sum`,
  `dot_cfc_mulVec_eq_sum`, `frob_cfc_eq_sum`), the step function (`trace_step_le_zero_iff`: the trace of
  `1_{(0,∞)}(N)` is `≤ 0` iff `N ≤ 0`) and the clamp (`cfc_clamp_bounds`, `clamp_frob_le`: the variational inequality
  of the clamp on the matrices between `a I` and `b I`).
* Gauss-Jordan without pivoting inverts a positive definite matrix (`gjRun_inv`).
* The nearest point of `D` is the clamp of the symmetric part with the ball clip of `μ` (`pgProj_eq`).
-/

section

open Matrix

theorem AdversarialBco.Poly.PG.trace_cfc_eq_sum {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (f : ℝ → ℝ) : (cfc f S).trace = ∑ i, f (hS.eigenvalues i) := by
  classical
  rw [hS.cfc_eq f, Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.UnitaryGroup.star_mul_self hS.eigenvectorUnitary, Matrix.one_mul]
  rw [Matrix.trace_diagonal]
  simp [RCLike.ofReal_real_eq_id]

end

section

open Matrix

theorem AdversarialBco.Poly.PG.dot_cfc_mulVec_eq_sum {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (f : ℝ → ℝ) (v w : Fin d → ℝ) :
    v ⬝ᵥ (cfc f S *ᵥ w) = ∑ i, f (hS.eigenvalues i) *
      ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ w)) := by
  let U : Matrix (Fin d) (Fin d) ℝ := hS.eigenvectorUnitary
  let D := diagonal (f ∘ hS.eigenvalues)
  have hcfc : cfc f S = U * D * Uᵀ := by
    rw [Matrix.IsHermitian.cfc_eq hS f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp [U, D, RCLike.ofReal_real_eq_id, Matrix.star_eq_conjTranspose]
  rw [hcfc]
  calc
    v ⬝ᵥ ((U * D * Uᵀ) *ᵥ w) = v ⬝ᵥ ((U * D) *ᵥ (Uᵀ *ᵥ w)) := by
      rw [← Matrix.mulVec_mulVec]
    _ = v ⬝ᵥ (U *ᵥ (D *ᵥ (Uᵀ *ᵥ w))) := by
      rw [← Matrix.mulVec_mulVec]
    _ = (v ᵥ* U) ⬝ᵥ (D *ᵥ (Uᵀ *ᵥ w)) := by rw [Matrix.dotProduct_mulVec]
    _ = ((Uᵀ *ᵥ v) ⬝ᵥ (D *ᵥ (Uᵀ *ᵥ w))) := by
      have h : v ᵥ* U = Uᵀ *ᵥ v := by
        simpa using Matrix.vecMul_transpose (A := Uᵀ) (x := v)
      rw [h]
    _ = ∑ i, (Uᵀ *ᵥ v) i * (D *ᵥ (Uᵀ *ᵥ w)) i := rfl
    _ = ∑ i, (Uᵀ *ᵥ v) i * (f (hS.eigenvalues i) * (Uᵀ *ᵥ w) i) := by
      simp [D, Matrix.mulVec_diagonal]
    _ = ∑ i, f (hS.eigenvalues i) * ((Uᵀ *ᵥ v) i * (Uᵀ *ᵥ w) i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ = ∑ i, f (hS.eigenvalues i) * (((hS.eigenvectorBasis i).ofLp ⬝ᵥ v) * ((hS.eigenvectorBasis i).ofLp ⬝ᵥ w)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hUv : (Uᵀ *ᵥ v) i = (hS.eigenvectorBasis i).ofLp ⬝ᵥ v := by
        calc
          (Uᵀ *ᵥ v) i = ∑ k, Uᵀ i k * v k := rfl
          _ = ∑ k, U k i * v k := by simp
          _ = ∑ k, (hS.eigenvectorBasis i) k * v k := by
            simp [U, Matrix.IsHermitian.eigenvectorUnitary_apply]
          _ = (hS.eigenvectorBasis i).ofLp ⬝ᵥ v := rfl
      have hUw : (Uᵀ *ᵥ w) i = (hS.eigenvectorBasis i).ofLp ⬝ᵥ w := by
        calc
          (Uᵀ *ᵥ w) i = ∑ k, Uᵀ i k * w k := rfl
          _ = ∑ k, U k i * w k := by simp
          _ = ∑ k, (hS.eigenvectorBasis i) k * w k := by
            simp [U, Matrix.IsHermitian.eigenvectorUnitary_apply]
          _ = (hS.eigenvectorBasis i).ofLp ⬝ᵥ w := rfl
      rw [hUv, hUw]

end

section

open Matrix

theorem AdversarialBco.Poly.PG.cfc_mulVec_eigenvector {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (f : ℝ → ℝ) (i : Fin d) :
    cfc f S *ᵥ ⇑(hS.eigenvectorBasis i) = f (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i) := by
  have hcfc := Matrix.IsHermitian.cfc_eq hS f
  rw [hcfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  -- Goal: (hS.eigenvectorUnitary * diagonal (RCLike.ofReal ∘ f ∘ hS.eigenvalues) * (star hS.eigenvectorUnitary)) *ᵥ ⇑(hS.eigenvectorBasis i) = ...
  have h1 : (star (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ⇑(hS.eigenvectorBasis i) = Pi.single i 1 := by
    simpa using hS.star_eigenvectorUnitary_mulVec i
  have h2 : diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) *ᵥ Pi.single i 1 = ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) • Pi.single i 1 := by
    calc
      diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) *ᵥ Pi.single i 1 = Pi.single i (((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) * 1) := by
        rw [Matrix.diagonal_mulVec_single ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) i 1]
        simp [Function.comp_apply]
      _ = Pi.single i ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) := by simp
      _ = ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) • Pi.single i 1 := by
        rw [← Pi.single_smul' i ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) 1, smul_eq_mul, mul_one]
  have h3 : (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *ᵥ Pi.single i 1 = ⇑(hS.eigenvectorBasis i) := by
    simp [hS.eigenvectorUnitary_mulVec i]
  calc
    ((hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) * (star (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ))) *ᵥ ⇑(hS.eigenvectorBasis i)
        = (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *ᵥ (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) *ᵥ ((star (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ⇑(hS.eigenvectorBasis i))) := by
      rw [mulVec_mulVec, mulVec_mulVec]
    _ = (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *ᵥ (diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ f ∘ hS.eigenvalues) *ᵥ (Pi.single i 1)) := by rw [h1]
    _ = (hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *ᵥ (((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) • Pi.single i 1) := by rw [h2]
    _ = ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) • ((hS.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *ᵥ Pi.single i 1) := by rw [mulVec_smul]
    _ = ((RCLike.ofReal : ℝ → ℝ) (f (hS.eigenvalues i))) • ⇑(hS.eigenvectorBasis i) := by rw [h3]
    _ = f (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i) := by simp

end

section

open Matrix

theorem AdversarialBco.Poly.PG.sum_eigen_dot_mul {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (v w : Fin d → ℝ) :
    ∑ i, (⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ w) = v ⬝ᵥ w := by
  let b := hS.eigenvectorBasis
  let x := WithLp.toLp 2 v
  let y := WithLp.toLp 2 w
  have hsum := OrthonormalBasis.sum_inner_mul_inner b x y
  have hinner_x_bi (i : Fin d) : inner ℝ x (b i) = (b i : Fin d → ℝ) ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x]
  have hinner_bi_y (i : Fin d) : inner ℝ (b i) y = (b i : Fin d → ℝ) ⬝ᵥ w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [y, dotProduct_comm]
  have hinner_xy : inner ℝ x y = v ⬝ᵥ w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x, y, dotProduct_comm]
  simp [hinner_x_bi, hinner_bi_y, hinner_xy] at hsum
  exact hsum

end

section
open Matrix
theorem AdversarialBco.Poly.PG.frob_cfc_eq_sum {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (f : ℝ → ℝ) (W : Matrix (Fin d) (Fin d) ℝ) :
    ∑ j, ∑ k, cfc f S j k * W j k =
      ∑ i, f (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i))) := by
  have hentry : ∀ j k, cfc f S j k =
      ∑ i, f (hS.eigenvalues i) * (hS.eigenvectorBasis i j * hS.eigenvectorBasis i k) := by
    intro j k
    have h := dot_cfc_mulVec_eq_sum S hS f (Pi.single j 1) (Pi.single k 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  calc ∑ j, ∑ k, cfc f S j k * W j k
      = ∑ j, ∑ k, ∑ i, f (hS.eigenvalues i) * (hS.eigenvectorBasis i j * hS.eigenvectorBasis i k) * W j k := by
        simp_rw [hentry, Finset.sum_mul]
    _ = ∑ j, ∑ i, ∑ k, f (hS.eigenvalues i) * (hS.eigenvectorBasis i j * hS.eigenvectorBasis i k) * W j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, f (hS.eigenvalues i) * (hS.eigenvectorBasis i j * hS.eigenvectorBasis i k) * W j k :=
        Finset.sum_comm
    _ = ∑ i, f (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        ring

end

section

open Matrix

theorem AdversarialBco.Poly.PG.cfc_clamp_bounds {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (a b : ℝ) (hab : a ≤ b) :
    (cfc (fun x : ℝ => max a (min b x)) S).IsHermitian ∧
      ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (cfc (fun x : ℝ => max a (min b x)) S *ᵥ v) ∧
        v ⬝ᵥ (cfc (fun x : ℝ => max a (min b x)) S *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
  have h_cfc_selfadj : IsSelfAdjoint (cfc (fun x : ℝ => max a (min b x)) S) :=
    IsSelfAdjoint.cfc (f := fun x : ℝ => max a (min b x)) (a := S)
  have h_cfc_herm : (cfc (fun x : ℝ => max a (min b x)) S).IsHermitian :=
    h_cfc_selfadj.isHermitian
  refine And.intro h_cfc_herm ?_
  intro v
  set c := fun x : ℝ => max a (min b x) with hc_def
  have hc_lower : ∀ x : ℝ, a ≤ c x := by
    intro x
    dsimp [c]
    exact le_max_left _ _
  have hc_upper : ∀ x : ℝ, c x ≤ b := by
    intro x
    dsimp [c]
    exact max_le hab (min_le_left b x)
  have h_sum_eq : v ⬝ᵥ (cfc c S *ᵥ v) = ∑ i, c (hS.eigenvalues i) *
      ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) :=
    AdversarialBco.Poly.PG.dot_cfc_mulVec_eq_sum S hS c v v
  have h_dot_eq : ∑ i, (hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v) = v ⬝ᵥ v :=
    AdversarialBco.Poly.PG.sum_eigen_dot_mul S hS v v
  have h_nonneg_sq : ∀ i, 0 ≤ (hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v) := by
    intro i
    apply mul_self_nonneg
  have h_lower_sum : a * (v ⬝ᵥ v) ≤ ∑ i, c (hS.eigenvalues i) *
      ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) := by
    calc
      a * (v ⬝ᵥ v) = a * (∑ i, (hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) := by rw [h_dot_eq]
      _ = ∑ i, a * ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, c (hS.eigenvalues i) * ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc_lower (hS.eigenvalues i)) (h_nonneg_sq i))
  have h_upper_sum : ∑ i, c (hS.eigenvalues i) *
      ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) ≤ b * (v ⬝ᵥ v) := by
    calc
      ∑ i, c (hS.eigenvalues i) * ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v))
          ≤ ∑ i, b * ((hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc_upper (hS.eigenvalues i)) (h_nonneg_sq i))
      _ = b * (∑ i, (hS.eigenvectorBasis i ⬝ᵥ v) * (hS.eigenvectorBasis i ⬝ᵥ v)) := by rw [Finset.mul_sum]
      _ = b * (v ⬝ᵥ v) := by rw [h_dot_eq]
  exact And.intro (by rw [h_sum_eq]; exact h_lower_sum) (by rw [h_sum_eq]; exact h_upper_sum)

end

section

open Matrix

theorem AdversarialBco.Poly.PG.trace_step_le_zero_iff {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) (hN : N.IsHermitian) :
    (cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) N).trace ≤ 0 ↔ ∀ v : Fin d → ℝ, v ⬝ᵥ (N *ᵥ v) ≤ 0 := by
  constructor
  · intro h_trace v
    have h_trace_eq : (cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) N).trace = ∑ i : Fin d, (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) :=
      AdversarialBco.Poly.PG.trace_cfc_eq_sum N hN (fun x : ℝ => if 0 < x then (1 : ℝ) else 0)
    rw [h_trace_eq] at h_trace
    have h_nonneg : ∀ i, 0 ≤ (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) := by
      intro i
      split
      · norm_num
      · norm_num
    have h_nonneg' : ∀ i ∈ Finset.univ, 0 ≤ (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) := by
      intro i hi; exact h_nonneg i
    have h_sum_nonneg : 0 ≤ ∑ i : Fin d, (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) :=
      Finset.sum_nonneg h_nonneg'
    have h_sum_zero : ∑ i : Fin d, (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) = 0 := by
      linarith
    have h_each_zero : ∀ i, (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg').mp h_sum_zero
      intro i
      exact this i (Finset.mem_univ i)
    have h_eigenvalues_nonpos : ∀ i, hN.eigenvalues i ≤ 0 := by
      intro i
      by_contra! hpos
      have hpos' : (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) = 1 := by
        split
        · rfl
        · exfalso; linarith
      have hzero := h_each_zero i
      rw [hpos'] at hzero
      norm_num at hzero
    have hN_eq : cfc (id : ℝ → ℝ) N = N := by
      have hsa : IsSelfAdjoint N := hN.isSelfAdjoint
      exact cfc_id ℝ N hsa
    have h_dot : v ⬝ᵥ (cfc (id : ℝ → ℝ) N *ᵥ v) = ∑ i : Fin d, hN.eigenvalues i * ((⇑(hN.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hN.eigenvectorBasis i) ⬝ᵥ v)) :=
      AdversarialBco.Poly.PG.dot_cfc_mulVec_eq_sum N hN (id : ℝ → ℝ) v v
    rw [hN_eq] at h_dot
    rw [h_dot]
    apply Finset.sum_nonpos
    intro i hi
    have h_eig_nonpos : hN.eigenvalues i ≤ 0 := h_eigenvalues_nonpos i
    have h_sq_nonneg : 0 ≤ (⇑(hN.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hN.eigenvectorBasis i) ⬝ᵥ v) :=
      mul_self_nonneg _
    exact mul_nonpos_of_nonpos_of_nonneg h_eig_nonpos h_sq_nonneg
  · intro h
    have h_trace_eq : (cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) N).trace = ∑ i : Fin d, (if 0 < hN.eigenvalues i then (1 : ℝ) else 0) :=
      AdversarialBco.Poly.PG.trace_cfc_eq_sum N hN (fun x : ℝ => if 0 < x then (1 : ℝ) else 0)
    rw [h_trace_eq]
    have h_each_nonpos : ∀ i, hN.eigenvalues i ≤ 0 := by
      intro i
      let b_i := ⇑(hN.eigenvectorBasis i)
      have hb : b_i ⬝ᵥ (N *ᵥ b_i) ≤ 0 := h b_i
      have hN_eq : cfc (id : ℝ → ℝ) N = N := by
        have hsa : IsSelfAdjoint N := hN.isSelfAdjoint
        exact cfc_id ℝ N hsa
      have h_mulvec : cfc (id : ℝ → ℝ) N *ᵥ b_i = hN.eigenvalues i • b_i := by
        simpa [b_i] using AdversarialBco.Poly.PG.cfc_mulVec_eigenvector N hN (id : ℝ → ℝ) i
      rw [hN_eq] at h_mulvec
      rw [h_mulvec] at hb
      rw [dotProduct_smul] at hb
      have h_inner : b_i ⬝ᵥ b_i = 1 := by
        have h_inner_eq_one : inner ℝ (hN.eigenvectorBasis i) (hN.eigenvectorBasis i) = 1 :=
          OrthonormalBasis.inner_eq_one hN.eigenvectorBasis i
        have h_inner_eq_dot : inner ℝ (hN.eigenvectorBasis i) (hN.eigenvectorBasis i) = b_i ⬝ᵥ b_i := by
          calc
            inner ℝ (hN.eigenvectorBasis i) (hN.eigenvectorBasis i) =
              ((hN.eigenvectorBasis i).ofLp) ⬝ᵥ star ((hN.eigenvectorBasis i).ofLp) := by
              simpa using EuclideanSpace.inner_eq_star_dotProduct (hN.eigenvectorBasis i) (hN.eigenvectorBasis i)
            _ = ((hN.eigenvectorBasis i).ofLp) ⬝ᵥ ((hN.eigenvectorBasis i).ofLp) := by simp
            _ = ⇑(hN.eigenvectorBasis i) ⬝ᵥ ⇑(hN.eigenvectorBasis i) := rfl
            _ = b_i ⬝ᵥ b_i := rfl
        rw [h_inner_eq_dot] at h_inner_eq_one
        exact h_inner_eq_one
      rw [h_inner] at hb
      simpa [smul_eq_mul] using hb
    apply Finset.sum_nonpos
    intro i hi
    have h_eig_nonpos : hN.eigenvalues i ≤ 0 := h_each_nonpos i
    split
    · linarith
    · rfl

end

section

open Matrix


set_option maxHeartbeats 400000 in
theorem AdversarialBco.Poly.PG.clamp_frob_le {d : ℕ} (S W : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (a b : ℝ) (hWa : ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (W *ᵥ v))
    (hWb : ∀ v : Fin d → ℝ, v ⬝ᵥ (W *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    ∑ i, ∑ j, (S - cfc (fun x : ℝ => max a (min b x)) S) i j * (W - cfc (fun x : ℝ => max a (min b x)) S) i j
      ≤ 0 := by
  set c := fun x : ℝ => max a (min b x) with hc_def
  set C := cfc c S with hC_def
  set e := fun x : ℝ => x - c x with he_def
  have hS_selfadj : IsSelfAdjoint S := hS.isSelfAdjoint
  have hS_id : S = cfc (id : ℝ → ℝ) S := by
    rw [cfc_id ℝ S]
  have h_sub : S - C = cfc e S := by
    calc
      S - C = (cfc (id : ℝ → ℝ) S) - cfc c S := by
        -- only rewrite LHS
        conv =>
          lhs
          rw [hS_id, hC_def]
      _ = cfc (fun x => id x - c x) S := by
        rw [← cfc_sub (R := ℝ) (f := id) (g := c) (a := S) (hf := by cfc_cont_tac) (hg := by cfc_cont_tac)]
      _ = cfc e S := by simp [e, c]
  rw [h_sub]
  -- Goal: ∑ i, ∑ j, (cfc e S) i j * (W - C) i j ≤ 0
  have h_split : ∑ i, ∑ j, (cfc e S) i j * (W - C) i j =
      (∑ i, ∑ j, (cfc e S) i j * W i j) - (∑ i, ∑ j, (cfc e S) i j * C i j) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [h_split]
  -- Goal: (∑ i, ∑ j, (cfc e S) i j * W i j) - (∑ i, ∑ j, (cfc e S) i j * C i j) ≤ 0
  -- Apply frob_cfc_eq_sum to both sums
  have h_sumW := frob_cfc_eq_sum S hS e W
  have h_sumC := frob_cfc_eq_sum S hS e C
  -- h_sumW: ∑ j, ∑ k, cfc e S j k * W j k = ∑ i, e (hS.eigenvalues i) * (u i ⬝ᵥ (W *ᵥ u i))
  -- h_sumC: ∑ j, ∑ k, cfc e S j k * C j k = ∑ i, e (hS.eigenvalues i) * (u i ⬝ᵥ (C *ᵥ u i))
  rw [h_sumW, h_sumC]
  -- Goal: (∑ i, e (hS.eigenvalues i) * (u i ⬝ᵥ (W *ᵥ u i))) -
  --       (∑ i, e (hS.eigenvalues i) * (u i ⬝ᵥ (C *ᵥ u i))) ≤ 0
  -- Combine the sums
  rw [← Finset.sum_sub_distrib]
  -- Goal: ∑ i, (e (hS.eigenvalues i) * (u i ⬝ᵥ (W *ᵥ u i)) - e (hS.eigenvalues i) * (u i ⬝ᵥ (C *ᵥ u i))) ≤ 0
  -- Simplify each term
  have h_term (i : Fin d) : e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i))) -
      e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (C *ᵥ ⇑(hS.eigenvectorBasis i))) =
      e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) -
        ⇑(hS.eigenvectorBasis i) ⬝ᵥ (C *ᵥ ⇑(hS.eigenvectorBasis i))) := by
    ring
  have h_sum_eq : (∑ i, (e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i))) -
      e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (C *ᵥ ⇑(hS.eigenvectorBasis i))))) =
      (∑ i, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) -
        ⇑(hS.eigenvectorBasis i) ⬝ᵥ (C *ᵥ ⇑(hS.eigenvectorBasis i)))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_term i]
  rw [h_sum_eq]
  -- Now simplify C *ᵥ u i using cfc_mulVec_eigenvector
  have h_C_mulVec (i : Fin d) : C *ᵥ ⇑(hS.eigenvectorBasis i) = c (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i) := by
    rw [hC_def]
    exact cfc_mulVec_eigenvector S hS c i
  have h_sum_eq2 : (∑ i, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) -
      ⇑(hS.eigenvectorBasis i) ⬝ᵥ (C *ᵥ ⇑(hS.eigenvectorBasis i)))) =
      (∑ i, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) -
        ⇑(hS.eigenvectorBasis i) ⬝ᵥ (c (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i)))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_C_mulVec i]
  rw [h_sum_eq2]
  -- Simplify u i ⬝ᵥ (c i • u i) = c i * (u i ⬝ᵥ u i) = c i
  have h_dot_self (i : Fin d) : ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis i) = 1 := by
    have h1 := EuclideanSpace.inner_eq_star_dotProduct (hS.eigenvectorBasis i) (hS.eigenvectorBasis i)
    -- h1 : inner (hS.eigenvectorBasis i) (hS.eigenvectorBasis i) = ofLp (u i) ⬝ᵥ star (ofLp (u i))
    have h3 := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (x := hS.eigenvectorBasis i)
    -- h3 : inner (hS.eigenvectorBasis i) (hS.eigenvectorBasis i) = (‖hS.eigenvectorBasis i‖ ^ 2 : ℝ)
    have h4 : ‖hS.eigenvectorBasis i‖ = 1 := hS.eigenvectorBasis.orthonormal.1 i
    calc
      ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis i) =
          ⇑(hS.eigenvectorBasis i) ⬝ᵥ star (⇑(hS.eigenvectorBasis i)) := by simp
      _ = (@inner ℝ (EuclideanSpace ℝ (Fin d)) _ (hS.eigenvectorBasis i) (hS.eigenvectorBasis i) : ℝ) := by
        rw [← h1]
      _ = (‖hS.eigenvectorBasis i‖ ^ 2 : ℝ) := by
        simpa using h3
      _ = (1 ^ 2 : ℝ) := by rw [h4]
      _ = (1 : ℝ) := by norm_num
      _ = 1 := rfl
  have h_dot_smul (i : Fin d) : ⇑(hS.eigenvectorBasis i) ⬝ᵥ (c (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i)) =
      c (hS.eigenvalues i) := by
    simp [dotProduct_smul, h_dot_self i]
  -- Simplify the goal using h_dot_smul
  have h_sum_eq3 : (∑ i, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) -
      ⇑(hS.eigenvectorBasis i) ⬝ᵥ (c (hS.eigenvalues i) • ⇑(hS.eigenvectorBasis i)))) =
      (∑ i, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) - c (hS.eigenvalues i))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dot_smul i]
  rw [h_sum_eq3]
  -- Goal: ∑ i, e (hS.eigenvalues i) * (u i ⬝ᵥ (W *ᵥ u i) - c (hS.eigenvalues i)) ≤ 0
  -- Let q i := u i ⬝ᵥ (W *ᵥ u i)
  -- From hWa and hWb: a ≤ q i ≤ b (since u i ⬝ᵥ u i = 1)
  have h_qi_lower (i : Fin d) : a ≤ ⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) := by
    have h := hWa (⇑(hS.eigenvectorBasis i))
    simpa [h_dot_self i] using h
  have h_qi_upper (i : Fin d) : ⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) ≤ b := by
    have h := hWb (⇑(hS.eigenvectorBasis i))
    simpa [h_dot_self i] using h
  -- Handle the case where Fin d might be empty
  by_cases h_empty : IsEmpty (Fin d)
  · -- If Fin d is empty, the sum is 0 and 0 ≤ 0 is trivial
    have : (∑ i : Fin d, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) - c (hS.eigenvalues i))) = 0 := by
      simp
    rw [this]
  · -- Fin d is nonempty, so we can prove a ≤ b
    have h_ab : a ≤ b := by
      have h_nonempty : Nonempty (Fin d) := not_isEmpty_iff.mp h_empty
      obtain ⟨i⟩ := h_nonempty
      have h_lower := h_qi_lower i
      have h_upper := h_qi_upper i
      linarith
    -- Now do case analysis on λ i vs a and b
    have h_nonpos (i : Fin d) : e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) - c (hS.eigenvalues i)) ≤ 0 := by
      dsimp [c, e]
      set lami := hS.eigenvalues i
      set qi := ⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i))
      have ha_qi : a ≤ qi := h_qi_lower i
      have hqi_b : qi ≤ b := h_qi_upper i
      by_cases h_le_b : lami ≤ b
      · -- lami ≤ b, so min b (lami) = lami, c = max a (lami)
        have h_min : min b lami = lami := min_eq_right h_le_b
        have h_max : max a (min b lami) = max a lami := by rw [h_min]
        rw [h_max]
        by_cases h_a_le : a ≤ lami
        · -- a ≤ lami, so max a (lami) = lami, c = lami, e = 0
          have h_max2 : max a lami = lami := max_eq_right h_a_le
          rw [h_max2]
          -- e = lami - lami = 0, so product = 0
          simp
        · -- lami < a, so max a (lami) = a, c = a, e = lami - a < 0
          have h_max2 : max a lami = a := max_eq_left (by linarith)
          rw [h_max2]
          -- Need: (lami - a) * (qi - a) ≤ 0
          -- lami - a < 0 and qi - a ≥ 0
          have h_neg : lami - a ≤ 0 := by linarith
          have h_pos : 0 ≤ qi - a := by linarith
          nlinarith
      · -- b < lami, so min b (lami) = b, c = max a b
        have h_min : min b lami = b := min_eq_left (by linarith)
        have h_max : max a (min b lami) = max a b := by rw [h_min]
        rw [h_max]
        -- Since a ≤ b, max a b = b, c = b, e = lami - b > 0
        have h_max2 : max a b = b := max_eq_right h_ab
        rw [h_max2]
        -- Need: (lami - b) * (qi - b) ≤ 0
        -- lami - b > 0 and qi - b ≤ 0
        have h_pos : 0 ≤ lami - b := by linarith
        have h_neg : qi - b ≤ 0 := by linarith
        nlinarith
    -- Now apply Finset.sum_nonpos
    have h_sum : (∑ i : Fin d, e (hS.eigenvalues i) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hS.eigenvectorBasis i)) - c (hS.eigenvalues i))) ≤
        (∑ i : Fin d, (0 : ℝ)) :=
      Finset.sum_le_sum (fun i _ => h_nonpos i)
    simpa using h_sum


end

section

open Matrix

theorem AdversarialBco.Poly.PG.frob_skew_zero {d : ℕ} (Y M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) :
    ∑ i, ∑ j, (Y - (1 / 2 : ℝ) • (Y + Yᵀ)) i j * M i j = 0 := by
  have hM' : ∀ i j, M j i = M i j := by
    intro i j
    calc
      M j i = Mᵀ i j := by rw [Matrix.transpose_apply]
      _ = M i j := by rw [hM]
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.transpose_apply]
  -- Goal: ∑ i, ∑ j, (Y i j - (2⁻¹ * Y i j + 2⁻¹ * Y j i)) * M i j = 0
  -- Rewrite 2⁻¹ * Y i j + 2⁻¹ * Y j i = 2⁻¹ * (Y i j + Y j i)
  have h_eq : (∑ i : Fin d, ∑ j : Fin d, (Y i j - ((2⁻¹ : ℝ) * Y i j + (2⁻¹ : ℝ) * Y j i)) * M i j) =
             (∑ i : Fin d, ∑ j : Fin d, (Y i j - (2⁻¹ : ℝ) * (Y i j + Y j i)) * M i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_eq]
  -- Now: ∑ i, ∑ j, (Y i j - 2⁻¹ * (Y i j + Y j i)) * M i j = 0
  have h : (∑ i : Fin d, ∑ j : Fin d, (Y i j - (2⁻¹ : ℝ) * (Y i j + Y j i)) * M i j) = 0 := by
    calc
      ∑ i, ∑ j, (Y i j - (2⁻¹ : ℝ) * (Y i j + Y j i)) * M i j
          = ∑ i, ∑ j, ((2⁻¹ : ℝ) * (Y i j - Y j i)) * M i j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (2⁻¹ : ℝ) * ∑ i, ∑ j, (Y i j - Y j i) * M i j := by
            simp [Finset.mul_sum, mul_assoc]
      _ = (2⁻¹ : ℝ) * (∑ i, ∑ j, Y i j * M i j - ∑ i, ∑ j, Y j i * M i j) := by
            simp [sub_mul, Finset.sum_sub_distrib]
      _ = (2⁻¹ : ℝ) * (∑ i, ∑ j, Y i j * M i j - ∑ j, ∑ i, Y j i * M i j) := by
            rw [show (∑ i : Fin d, ∑ j : Fin d, Y j i * M i j) = (∑ j : Fin d, ∑ i : Fin d, Y j i * M i j) from Finset.sum_comm]
      _ = (2⁻¹ : ℝ) * (∑ i, ∑ j, Y i j * M i j - ∑ i, ∑ j, Y i j * M j i) := by
            simp
      _ = (2⁻¹ : ℝ) * (∑ i, ∑ j, Y i j * M i j - ∑ i, ∑ j, Y i j * M i j) := by
            simp [hM']
      _ = (2⁻¹ : ℝ) * 0 := by ring
      _ = 0 := by ring
  simpa

end

section

open Matrix

theorem AdversarialBco.Poly.PG.posDef_of_lower {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.IsHermitian) (a : ℝ)
    (ha : 0 < a) (h : ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (T *ᵥ v)) : T.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hT ?_
  intro x hx
  have hdotpos : 0 < star x ⬝ᵥ x := by
    rw [Matrix.dotProduct_star_self_pos_iff]
    exact hx
  have hstar_eq : star x = x := TrivialStar.star_trivial x
  rw [hstar_eq] at hdotpos
  have h_ineq : a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x) := h x
  have ha_mul_pos : 0 < a * (x ⬝ᵥ x) := mul_pos ha hdotpos
  exact lt_of_lt_of_le ha_mul_pos h_ineq

end

section

open Matrix
open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.PG.toEuclideanCLM_bridge {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    (IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) M) ↔ M.IsHermitian) ∧
      ∀ v : EuclideanSpace ℝ (Fin d),
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) M v, v⟫ = WithLp.ofLp v ⬝ᵥ (M *ᵥ WithLp.ofLp v) := by
  have h_inner : ∀ v : EuclideanSpace ℝ (Fin d),
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) M v, v⟫ = WithLp.ofLp v ⬝ᵥ (M *ᵥ WithLp.ofLp v) := by
    intro v
    calc
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) M v, v⟫ = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) M v⟫ := by
        rw [real_inner_comm]
      _ = v.ofLp ⬝ᵥ M *ᵥ v.ofLp := by rw [Matrix.inner_toEuclideanCLM]
      _ = WithLp.ofLp v ⬝ᵥ (M *ᵥ WithLp.ofLp v) := rfl
  have h_adjoint : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) M) ↔ M.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    constructor
    · intro h
      have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℝ) M) = Matrix.toEuclideanCLM (𝕜 := ℝ) M := h
      have h_eq : Matrix.toEuclideanCLM (𝕜 := ℝ) (star M) = Matrix.toEuclideanCLM (𝕜 := ℝ) M := by
        calc
          Matrix.toEuclideanCLM (𝕜 := ℝ) (star M) = star (Matrix.toEuclideanCLM (𝕜 := ℝ) M) := by
            rw [StarRingEquivClass.map_star]
          _ = Matrix.toEuclideanCLM (𝕜 := ℝ) M := hstar
      have hinj : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) :=
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).injective
      exact hinj h_eq
    · intro h
      have hstar : star M = M := h
      have hstar' : star (Matrix.toEuclideanCLM (𝕜 := ℝ) M) = Matrix.toEuclideanCLM (𝕜 := ℝ) M := by
        calc
          star (Matrix.toEuclideanCLM (𝕜 := ℝ) M) = Matrix.toEuclideanCLM (𝕜 := ℝ) (star M) := by
            rw [StarRingEquivClass.map_star]
          _ = Matrix.toEuclideanCLM (𝕜 := ℝ) M := by rw [hstar]
      exact hstar'
  exact And.intro h_adjoint h_inner

end

section

open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.PG.ballClip_norm_le {d : ℕ} (R : ℝ) (hR : 0 ≤ R) (μ : EuclideanSpace ℝ (Fin d)) :
    ‖ballClip R μ‖ ≤ R := by
  by_cases h : R < ‖μ‖
  · rw [ballClip, if_pos h]
    have hpos : 0 < ‖μ‖ := by linarith
    have h_nonneg_div : 0 ≤ R / ‖μ‖ := div_nonneg hR (by linarith)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h_nonneg_div]
    field_simp [hpos.ne']
    exact le_rfl
  · rw [ballClip, if_neg h]
    have hle : ‖μ‖ ≤ R := by linarith
    simpa

end

section

open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.PG.ballClip_varineq {d : ℕ} (R : ℝ) (hR : 0 ≤ R) (μ ν : EuclideanSpace ℝ (Fin d))
    (hν : ‖ν‖ ≤ R) : ⟪μ - ballClip R μ, ν - ballClip R μ⟫ ≤ 0 := by
  unfold ballClip
  split_ifs with h
  · -- case R < ‖μ‖
    have hμ_pos : 0 < ‖μ‖ := by linarith
    have h_one_minus_t_nonneg : 0 ≤ 1 - R / ‖μ‖ := by
      have hdiv : R / ‖μ‖ < 1 := (div_lt_one hμ_pos).mpr h
      linarith
    have h_inner_le : ⟪μ, ν⟫ ≤ R * ‖μ‖ := by
      calc
        ⟪μ, ν⟫ ≤ ‖μ‖ * ‖ν‖ := real_inner_le_norm _ _
        _ ≤ ‖μ‖ * R := mul_le_mul_of_nonneg_left hν (norm_nonneg _)
        _ = R * ‖μ‖ := mul_comm _ _
    have h_second_factor_nonpos : ⟪μ, ν⟫ - (R / ‖μ‖) * ‖μ‖ ^ 2 ≤ 0 := by
      have : (R / ‖μ‖) * ‖μ‖ ^ 2 = R * ‖μ‖ := by
        field_simp [ne_of_gt hμ_pos]
      rw [this]
      linarith
    calc
      ⟪μ - (R / ‖μ‖) • μ, ν - (R / ‖μ‖) • μ⟫
          = ⟪(1 - R / ‖μ‖) • μ, ν - (R / ‖μ‖) • μ⟫ := by
        have : μ - (R / ‖μ‖) • μ = (1 - R / ‖μ‖) • μ := by
          calc
            μ - (R / ‖μ‖) • μ = (1 : ℝ) • μ - (R / ‖μ‖) • μ := by simp
            _ = (1 - R / ‖μ‖) • μ := by rw [sub_smul]
        rw [this]
      _ = (1 - R / ‖μ‖) * ⟪μ, ν - (R / ‖μ‖) • μ⟫ := by
        rw [inner_smul_left]
        simp
      _ = (1 - R / ‖μ‖) * (⟪μ, ν⟫ - ⟪μ, (R / ‖μ‖) • μ⟫) := by rw [inner_sub_right]
      _ = (1 - R / ‖μ‖) * (⟪μ, ν⟫ - (R / ‖μ‖) * ⟪μ, μ⟫) := by rw [inner_smul_right]
      _ = (1 - R / ‖μ‖) * (⟪μ, ν⟫ - (R / ‖μ‖) * ‖μ‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
      _ ≤ (1 - R / ‖μ‖) * 0 :=
        mul_le_mul_of_nonneg_left h_second_factor_nonpos h_one_minus_t_nonneg
      _ = 0 := by ring
  · -- case ¬ R < ‖μ‖, i.e., ‖μ‖ ≤ R
    simp [inner_zero_left]

end

section

open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.PG.nearest_of_varineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (y z : E) (hvi : ∀ w ∈ D, ⟪y - z, w - z⟫ ≤ 0) : ∀ w ∈ D, ‖y - z‖ ≤ ‖y - w‖ := by
  intro w hw
  have h_inner := hvi w hw
  have h_sq_eq : ‖y - w‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (w - z) + ‖w - z‖ ^ 2 := by
    calc
      ‖y - w‖ ^ 2 = ‖(y - z) - (w - z)‖ ^ 2 := by abel
      _ = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (w - z) + ‖w - z‖ ^ 2 := by
        rw [norm_sub_sq_real]
  have hy_nonneg : 0 ≤ ‖y - z‖ := norm_nonneg _
  have hw_nonneg : 0 ≤ ‖y - w‖ := norm_nonneg _
  have h_sq_ineq : ‖y - z‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by
    nlinarith
  have h_abs := (sq_le_sq.mp h_sq_ineq)
  rw [abs_of_nonneg hy_nonneg, abs_of_nonneg hw_nonneg] at h_abs
  exact h_abs

end

section

open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.PG.eq_of_varineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (y z p : E) (hz : z ∈ D) (hvi : ∀ w ∈ D, ⟪y - z, w - z⟫ ≤ 0) (hp : p ∈ D)
    (hmin : ∀ w ∈ D, ‖y - p‖ ≤ ‖y - w‖) : p = z := by
  have hsub : y - p = (y - z) - (p - z) := by
    abel
  have hsq : ‖y - p‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (p - z) + ‖p - z‖ ^ 2 := by
    calc
      ‖y - p‖ ^ 2 = ‖(y - z) - (p - z)‖ ^ 2 := by rw [hsub]
      _ = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (p - z) + ‖p - z‖ ^ 2 := by rw [norm_sub_sq_real]
  have h_inner_nonpos : inner ℝ (y - z) (p - z) ≤ 0 := hvi p hp
  have h_sq_ineq : ‖y - z‖ ^ 2 + ‖p - z‖ ^ 2 ≤ ‖y - p‖ ^ 2 := by
    linarith
  have h_sq_min : ‖y - p‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    have hle : ‖y - p‖ ≤ ‖y - z‖ := hmin z hz
    have h_nonneg : 0 ≤ ‖y - p‖ := norm_nonneg _
    have := mul_self_le_mul_self h_nonneg hle
    -- this gives ‖y-p‖ * ‖y-p‖ ≤ ‖y-z‖ * ‖y-z‖
    simpa [sq] using this
  have h_norm_sq_zero : ‖p - z‖ ^ 2 ≤ 0 := by
    linarith
  have h_norm_zero : ‖p - z‖ = 0 := by
    have h_nonneg : 0 ≤ ‖p - z‖ ^ 2 := sq_nonneg _
    have h_eq_zero : ‖p - z‖ ^ 2 = 0 := by linarith
    nlinarith
  have h_sub_zero : p - z = 0 := by
    rwa [norm_eq_zero] at h_norm_zero
  exact sub_eq_zero.mp h_sub_zero

end

section

open Matrix

theorem AdversarialBco.Poly.PG.gj_pivot_pos {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.PosDef) (k : Fin d)
    (AB : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) (h : GjInv T k AB) : 0 < AB.1 k k := by
  rcases h with ⟨hAB, hA, hB⟩
  set b := AB.2 k with hb_def
  have hT_symm : T.IsHermitian := hT.1
  have hT_symm' (i j : Fin d) : T i j = T j i := by
    have h_eq := congr_fun (congr_fun hT_symm i) j
    simpa [Matrix.conjTranspose_apply] using h_eq.symm
  -- b k = 1
  have hbk : b k = 1 := by
    have := hB k k (le_refl (k : ℕ))
    simpa [b] using this
  -- b ≠ 0
  have hb_ne_zero : b ≠ 0 := by
    intro hzero
    have hbk0 : b k = 0 := by simpa [hzero] using rfl
    rw [hbk] at hbk0
    linarith
  -- AB.1 k j = (T.mulVec b) j for all j
  have h_mulVec_eq (j : Fin d) : AB.1 k j = (T.mulVec b) j := by
    calc
      AB.1 k j = (AB.2 * T) k j := by rw [hAB]
      _ = ∑ l, AB.2 k l * T l j := by rw [Matrix.mul_apply]
      _ = ∑ l, T j l * AB.2 k l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hT_symm' l j, mul_comm (AB.2 k l)]
      _ = ∑ l, T.row j l * b l := by simp [b, Matrix.row_apply]
      _ = T.row j ⬝ᵥ b := rfl
      _ = (T.mulVec b) j := by rw [Matrix.mulVec_apply]
  -- Split the dot product b ⬝ᵥ (T.mulVec b) = ∑_j b j * (T.mulVec b) j
  have h_dotprod_eq : b ⬝ᵥ (T.mulVec b) = AB.1 k k := by
    calc
      b ⬝ᵥ (T.mulVec b) = ∑ j : Fin d, b j * (T.mulVec b) j := rfl
      _ = ∑ j : Fin d, b j * AB.1 k j := by simp [h_mulVec_eq]
      _ = ∑ j : Fin d, b j * (if j = k then AB.1 k k else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases hjk : j = k
        · subst hjk; simp
        · -- j ≠ k, we need to show AB.1 k j = 0
          have hjk' : k ≠ j := Ne.symm hjk
          rcases lt_or_gt_of_ne hjk with (hlt | hlt)
          · -- j < k
            have hA_j := hA k j hlt
            -- hA_j : AB.1 k j = if k = j then 1 else 0
            have hA_j' : AB.1 k j = 0 := by
              simpa [hjk'] using hA_j
            rw [hA_j']
            simp [hjk]
          · -- k < j
            have hB_j := hB k j (le_of_lt hlt)
            -- hB_j : AB.2 k j = if k = j then 1 else 0
            have hb_j : b j = 0 := by
              dsimp [b]
              simpa [hjk'] using hB_j
            rw [hb_j]
            simp
      _ = AB.1 k k := by
        -- ∑ j, b j * (if j = k then AB.1 k k else 0) = b k * AB.1 k k = AB.1 k k
        simp [Finset.sum_ite_eq', Finset.mem_univ, hbk]
  -- Now use positive definiteness
  have h_pos : 0 < star b ⬝ᵥ T.mulVec b := hT.dotProduct_mulVec_pos hb_ne_zero
  -- Over ℝ, star b = b
  have h_pos' : 0 < b ⬝ᵥ (T.mulVec b) := by
    simpa [star_trivial] using h_pos
  rw [h_dotprod_eq] at h_pos'
  exact h_pos'

end

section

open Matrix

theorem AdversarialBco.Poly.PG.gjStep_inv {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    (AB : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) (h : GjInv T k AB) (hp : AB.1 k k ≠ 0) :
    GjInv T ((k : ℕ) + 1) (gjStep k AB) := by
  rcases h with ⟨hAB, hA, hB⟩
  unfold GjInv
  refine ⟨?_, ?_, ?_⟩
  · -- A' = B' * T
    ext i j
    simp [gjStep, Matrix.mul_apply]
    by_cases hik : i = k
    · -- case i = k
      simp [hik, hAB]
      calc
        (AB.2 * T) k j * ((AB.2 * T) k k)⁻¹
            = ((AB.2 * T) k k)⁻¹ * (AB.2 * T) k j := by ring
        _ = ((AB.2 * T) k k)⁻¹ * (∑ x : Fin d, AB.2 k x * T x j) := by
          simp [Matrix.mul_apply]
        _ = ∑ x : Fin d, ((AB.2 * T) k k)⁻¹ * (AB.2 k x * T x j) := by rw [Finset.mul_sum]
        _ = ∑ x : Fin d, AB.2 k x * ((AB.2 * T) k k)⁻¹ * T x j := by
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
    · -- case i ≠ k
      simp [hik, hAB]
      have hRHS : (∑ x : Fin d, (AB.2 i x - (AB.2 * T) i k * (AB.2 k x * ((AB.2 * T) k k)⁻¹)) * T x j) =
          (AB.2 * T) i j - (AB.2 * T) i k * ((AB.2 * T) k k)⁻¹ * (AB.2 * T) k j := by
        calc
          (∑ x : Fin d, (AB.2 i x - (AB.2 * T) i k * (AB.2 k x * ((AB.2 * T) k k)⁻¹)) * T x j)
              = (∑ x : Fin d, (AB.2 i x * T x j - (AB.2 * T) i k * (AB.2 k x * ((AB.2 * T) k k)⁻¹) * T x j)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x : Fin d, AB.2 i x * T x j) - (∑ x : Fin d, (AB.2 * T) i k * (AB.2 k x * ((AB.2 * T) k k)⁻¹) * T x j) := by
            rw [Finset.sum_sub_distrib]
          _ = (AB.2 * T) i j - (∑ x : Fin d, (AB.2 * T) i k * (AB.2 k x * ((AB.2 * T) k k)⁻¹) * T x j) := by
            simp [Matrix.mul_apply]
          _ = (AB.2 * T) i j - (AB.2 * T) i k * ((AB.2 * T) k k)⁻¹ * (∑ x : Fin d, AB.2 k x * T x j) := by
            simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
          _ = (AB.2 * T) i j - (AB.2 * T) i k * ((AB.2 * T) k k)⁻¹ * (AB.2 * T) k j := by
            simp [Matrix.mul_apply]
      rw [hRHS]
      ring
  · -- columns j < k+1 of A'
    intro i j hj
    by_cases hjk : (j : ℕ) < (k : ℕ)
    · -- j < k
      have h_not_keq_j : k ≠ j := by
        intro heq
        have : (j : ℕ) = (k : ℕ) := by simp [heq]
        omega
      have hAij : AB.1 i j = if i = j then 1 else 0 := hA i j hjk
      have hAkj : AB.1 k j = 0 := by
        rw [hA k j hjk]
        simp [h_not_keq_j]
      simp [gjStep, hAij, hAkj]
      by_cases hik : i = k
      · simp [hik, h_not_keq_j]
      · simp [hik]
    · -- j ≥ k, and j < k+1, so j = k
      have h_eq_jk_val : (j : ℕ) = (k : ℕ) := by omega
      have h_eq_jk : j = k := (Fin.val_eq_val j k).mp h_eq_jk_val
      rw [h_eq_jk]
      by_cases hik : i = k
      · rw [hik]
        simp [gjStep]
        field_simp [hp]
      · simp [gjStep, hik]
        field_simp [hp]
        ring
  · -- columns j ≥ k+1 of B'
    intro i j hj
    have hj_ge : (k : ℕ) + 1 ≤ (j : ℕ) := hj
    have h_ge_k : (k : ℕ) ≤ (j : ℕ) := by omega
    have h_not_keq_j : k ≠ j := by
      intro heq
      have : (j : ℕ) = (k : ℕ) := by simp [heq]
      omega
    have hBikj : AB.2 k j = 0 := by
      rw [hB k j h_ge_k]
      simp [h_not_keq_j]
    have hBij : AB.2 i j = if i = j then 1 else 0 := hB i j h_ge_k
    simp [gjStep, hBij, hBikj]
    by_cases hik : i = k
    · simp [hik, h_not_keq_j]
    · simp [hik]

end

section

open Matrix

theorem AdversarialBco.Poly.PG.gjRun_inv {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.PosDef) :
    (gjRun T d).2 = T⁻¹ := by
  have hGjInv_run : ∀ k, AdversarialBco.Poly.PG.GjInv T k (gjRun T k) := by
    intro k
    induction' k with k ih
    · -- k = 0
      unfold gjRun
      refine ⟨?_, ?_, ?_⟩
      · -- (T, 1).1 = (T, 1).2 * T  →  T = 1 * T
        simp
      · -- ∀ i j, (j : ℕ) < 0 → ...
        intro i j hj
        exfalso; exact Nat.not_lt_zero _ hj
      · -- ∀ i j, 0 ≤ (j : ℕ) → 1 i j = if i = j then 1 else 0
        intro i j hj
        simp [Matrix.one_apply]
    · -- k → k+1
      by_cases hk : k < d
      · -- k < d case
        have hstep : gjRun T (k + 1) = gjStep (⟨k, hk⟩ : Fin d) (gjRun T k) := by
          simp [gjRun, hk]
        rw [hstep]
        apply gjStep_inv T (⟨k, hk⟩ : Fin d) (gjRun T k) ih
        have hpos : 0 < (gjRun T k).1 (⟨k, hk⟩ : Fin d) (⟨k, hk⟩ : Fin d) :=
          gj_pivot_pos T hT (⟨k, hk⟩ : Fin d) (gjRun T k) ih
        exact ne_of_gt hpos
      · -- d ≤ k case
        have hrun : gjRun T (k + 1) = gjRun T k := by
          simp [gjRun, hk]
        rw [hrun]
        rcases ih with ⟨h_eq, h_left, h_right⟩
        refine ⟨h_eq, ?_, ?_⟩
        · intro i j hj
          have hj_le_k : (j : ℕ) ≤ k := Nat.le_of_lt_succ hj
          rcases Nat.eq_or_lt_of_le hj_le_k with (hj_eq_k | hj_lt_k)
          · -- (j : ℕ) = k, but k ≥ d and j : Fin d, so (j : ℕ) < d ≤ k, contradiction
            have hj_lt_d : (j : ℕ) < d := j.2
            have : k < d := by
              -- from hj_eq_k: (j : ℕ) = k, and hj_lt_d: (j : ℕ) < d
              -- so k < d, but hk says ¬ k < d
              rw [← hj_eq_k]
              exact hj_lt_d
            exact absurd this hk
          · exact h_left i j hj_lt_k
        · intro i j hj
          have hj_lt_d : (j : ℕ) < d := j.2
          have : k + 1 ≤ (j : ℕ) := hj
          -- k + 1 ≤ (j : ℕ) < d ≤ k, impossible
          omega
  rcases hGjInv_run d with ⟨h_eq, h_left, h_right⟩
  have h_one : (gjRun T d).1 = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    apply h_left i j
    exact j.2
  have h_mul : (gjRun T d).2 * T = 1 := by
    rw [← h_eq, h_one]
  have h_inv : (gjRun T d).2 = T⁻¹ :=
    (Matrix.inv_eq_left_inv h_mul).symm
  exact h_inv

end

section


theorem AdversarialBco.Poly.PG.sgdAvg_congr {E G : Type*} [AddCommGroup E] [Module ℝ E] (proj : E → E)
    (V : E → G → E) (s : ℝ) (x1 : E) (N : ℕ) (a b : ℕ → G) (h : ∀ k < N, a k = b k) :
    AdversarialBco.Poly.sgdAvg proj V s x1 N a = AdversarialBco.Poly.sgdAvg proj V s x1 N b := by
  have h_iter : ∀ t, t ≤ N → AdversarialBco.Poly.sgdIter proj V s x1 a t = AdversarialBco.Poly.sgdIter proj V s x1 b t := by
    intro t
    induction' t with t IH
    · intro _
      rfl
    · intro ht
      have ht' : t < N := Nat.lt_of_succ_le ht
      have h_eq_a : AdversarialBco.Poly.sgdIter proj V s x1 a t = AdversarialBco.Poly.sgdIter proj V s x1 b t :=
        IH (Nat.le_of_succ_le ht)
      have h_eq_ω : a t = b t := h t ht'
      simp [AdversarialBco.Poly.sgdIter, h_eq_a, h_eq_ω]
  unfold AdversarialBco.Poly.sgdAvg
  have hsum : (∑ t ∈ Finset.range N, AdversarialBco.Poly.sgdIter proj V s x1 a t) =
             (∑ t ∈ Finset.range N, AdversarialBco.Poly.sgdIter proj V s x1 b t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    exact h_iter t (Nat.le_of_lt ht)
  rw [hsum]

end

/-! ## The projection on `D` -/

open AdversarialBco AdversarialBco.RealRAM Matrix
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly.PG

/-- The symmetric part is symmetric. -/
theorem symPart_isHermitian {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) : (symPart Y).IsHermitian := by
  unfold symPart
  ext i j
  simp [Matrix.conjTranspose_apply, add_comm]
  ring

/-- The projection on `D` by the formula (D3): the ball clip of `μ`, the spectral clamp of the symmetric part. -/
noncomputable def pgProjF (d : ℕ) (ρ : ℝ) (y : PgSp d) : PgSp d :=
  pgPack (ballClip (pgKappa * ρ) (pgMu y)) (cfc (Spec.fn .clamp (pgTmin d ρ) (pgLD ρ)) (symPart (pgMat y)))

theorem spec_clamp_eq (a b : ℝ) : Spec.fn .clamp a b = fun x => max a (min b x) := rfl

theorem pgMu_sub {d : ℕ} (x y : PgSp d) : pgMu (x - y) = pgMu x - pgMu y := by
  ext i; simp [pgMu]

theorem pgMat_sub {d : ℕ} (x y : PgSp d) : pgMat (x - y) = pgMat x - pgMat y := by
  ext i j; simp [pgMat]

theorem norm_sq_eq_dot {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ^ 2 = WithLp.ofLp v ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

/-- A point of `D` read through its matrix: symmetric, with the quadratic form between `t_min` and `t_max`. -/
theorem pgDom_mat {d : ℕ} {ρ : ℝ} {w : PgSp d} (hw : w ∈ pgDom d ρ) :
    (pgMat w).IsHermitian ∧ ‖pgMu w‖ ≤ pgKappa * ρ ∧
      ∀ v : Fin d → ℝ, pgTmin d ρ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (pgMat w *ᵥ v) ∧
        v ⬝ᵥ (pgMat w *ᵥ v) ≤ pgLD ρ * (v ⬝ᵥ v) := by
  obtain ⟨hsa, hmu, hq⟩ := hw
  have hb := toEuclideanCLM_bridge (pgMat w)
  refine ⟨hb.1.1 hsa, hmu, fun v => ?_⟩
  have h := hq (WithLp.toLp 2 v)
  rw [pgOp, hb.2, norm_sq_eq_dot] at h
  simpa using h

/-- The converse: a symmetric matrix with the quadratic form between `t_min` and `t_max`, and `|μ| ≤ κ ρ`. -/
theorem mem_pgDom_of {d : ℕ} {ρ : ℝ} (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (hmu : ‖μ‖ ≤ pgKappa * ρ)
    (hq : ∀ v : Fin d → ℝ, pgTmin d ρ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v) ∧ v ⬝ᵥ (M *ᵥ v) ≤ pgLD ρ * (v ⬝ᵥ v)) :
    pgPack μ M ∈ pgDom d ρ := by
  have hb := toEuclideanCLM_bridge M
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [pgOp, pgMat_pgPack]; exact hb.1.2 hM
  · rwa [pgMu_pgPack]
  · rw [pgOp, pgMat_pgPack, hb.2, norm_sq_eq_dot]
    exact hq _

theorem pgTmin_le_pgLD {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : pgTmin d ρ ≤ pgLD ρ := by
  have h := (pgDom_mat (pgX1_mem d ρ hd hρ)).2.2 (fun i => if (i : ℕ) = 0 then 1 else 0)
  have hdot : (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0) ⬝ᵥ (fun i => if (i : ℕ) = 0 then 1 else 0) = 1 := by
    have : (⟨0, hd⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
    rw [dotProduct, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  rw [hdot] at h
  linarith [h.1, h.2]

/-- The formula (D3) lands in `D`. -/
theorem pgProjF_mem {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (y : PgSp d) : pgProjF d ρ y ∈ pgDom d ρ := by
  have hab := pgTmin_le_pgLD hd hρ
  have hc := cfc_clamp_bounds (symPart (pgMat y)) (symPart_isHermitian _) _ _ hab
  have hR : 0 ≤ pgKappa * ρ := by unfold pgKappa; linarith
  unfold pgProjF
  rw [spec_clamp_eq]
  exact mem_pgDom_of _ _ hc.1 (ballClip_norm_le _ hR _) hc.2

/-- The formula (D3) satisfies the variational inequality of the nearest point of `D`. -/
theorem pgProjF_varineq {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (y w : PgSp d) (hw : w ∈ pgDom d ρ) :
    ⟪y - pgProjF d ρ y, w - pgProjF d ρ y⟫ ≤ 0 := by
  obtain ⟨hWh, hWmu, hWq⟩ := pgDom_mat hw
  have hR : 0 ≤ pgKappa * ρ := by unfold pgKappa; linarith
  have hab := pgTmin_le_pgLD hd hρ
  set S := symPart (pgMat y) with hS
  set C := cfc (fun x : ℝ => max (pgTmin d ρ) (min (pgLD ρ) x)) S with hC
  have hCh : C.IsHermitian := (cfc_clamp_bounds S (symPart_isHermitian _) (pgTmin d ρ) (pgLD ρ) hab).1
  have hzMu : pgMu (pgProjF d ρ y) = ballClip (pgKappa * ρ) (pgMu y) := by
    unfold pgProjF; rw [pgMu_pgPack]
  have hzMat : pgMat (pgProjF d ρ y) = C := by
    unfold pgProjF; rw [pgMat_pgPack, spec_clamp_eq]
  rw [pgSp_inner, pgMu_sub, pgMu_sub, pgMat_sub, pgMat_sub, hzMu, hzMat]
  have h1 := ballClip_varineq (pgKappa * ρ) hR (pgMu y) (pgMu w) hWmu
  have hWt : (pgMat w)ᵀ = pgMat w := by
    have := hWh.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hCt : Cᵀ = C := by
    have := hCh.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hM : (pgMat w - C)ᵀ = pgMat w - C := by rw [Matrix.transpose_sub, hWt, hCt]
  have h2 := frob_skew_zero (pgMat y) (pgMat w - C) hM
  have h3 := clamp_frob_le S (pgMat w) (symPart_isHermitian _) (pgTmin d ρ) (pgLD ρ)
    (fun v => (hWq v).1) (fun v => (hWq v).2)
  have hsplit : ∑ i, ∑ j, (pgMat y - C) i j * (pgMat w - C) i j =
      ∑ i, ∑ j, (pgMat y - (1 / 2 : ℝ) • (pgMat y + (pgMat y)ᵀ)) i j * (pgMat w - C) i j +
        ∑ i, ∑ j, (S - C) i j * (pgMat w - C) i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hS, symPart]
    simp only [Matrix.sub_apply]
    ring
  rw [hsplit, h2, zero_add]
  linarith

/-- The projection of PgProc.lean is the formula (D3). -/
theorem pgProj_eq {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (y : PgSp d) : pgProj d ρ y = pgProjF d ρ y := by
  have hz := pgProjF_mem hd hρ y
  have hvi := fun w hw => pgProjF_varineq hd hρ y w hw
  have hex : ∃ z ∈ pgDom d ρ, ∀ w ∈ pgDom d ρ, ‖y - z‖ ≤ ‖y - w‖ :=
    ⟨_, hz, nearest_of_varineq _ y _ hvi⟩
  unfold pgProj
  split_ifs
  exact eq_of_varineq _ y _ _ hz hvi hex.choose_spec.1 hex.choose_spec.2

end AdversarialBco.Poly.PG
