/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The frame: the clipped metric

The frame of a law on the ball with covariance `S = Σ_i λ_i e_i e_iᵀ` and floor `w > 0`:

* `clipM w S = Σ_i e_i e_iᵀ / max(λ_i, w²)`, the clipped metric `M` (a function of `S`, `cfc`);
* `clipSqrt w S = M^{1/2}` and `frameA w S`, the same as an operator on `ℝ^d`, so that `|v|_M = ‖frameA w S v‖`
  (the `A` of Dent.lean);
* `frameW w S = S + w² I`, the matrix `W`;
* `dLive w S = #{i : λ_i ≥ w²}` (as the trace of a spectral projection), `DM w S = tr(M S)`.

Statements: (F1) `smul_clipM_le_one`, `norm_frameA_le`, `norm_frameA_apply_le`; (F2) `frameW_inv_le_clipM`,
`clipM_le_two_frameW_inv`, `frameW_le_two_clipM_inv`; (F3) `dLive_le_DM`, `DM_le`; the trace bound of (L4)
`sq_trace_frameW_inv_le`; the metric and its inner product as quadratic forms (`norm_frameA_sq`, `inner_frameA`);
the Lipschitz constant of the dent, `κ r₁ ‖M^{1/2}‖ ≤ κ r₁ / w` (`lipschitz_const_le`).
-/

open Matrix
open scoped MatrixOrder RealInnerProductSpace

namespace AdversarialBco.Lower

/-! ## Definitions -/

/-- The clipped metric `M = Σ_i e_i e_iᵀ / max(λ_i, w²)` of a covariance `S`. -/
noncomputable def clipM {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S

/-- The square root `M^{1/2} = Σ_i e_i e_iᵀ / max(λ_i, w²)^{1/2}`. -/
noncomputable def clipSqrt {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) S

/-- `M^{1/2}` as an operator on `ℝ^d`: `|v|_M = ‖frameA w S v‖`. -/
noncomputable def frameA {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (clipSqrt w S)

/-- `W = S + w² I`. -/
noncomputable def frameW {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The number of live directions, `#{i : λ_i ≥ w²}`, as the trace of the spectral projection. -/
noncomputable def dLive {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  trace (cfc (fun s : ℝ => if w ^ 2 ≤ s then (1 : ℝ) else 0) S)

/-- `D_M = tr(M S)`. -/
noncomputable def DM {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  trace (clipM w S * S)

/-! ## Algebra of the frame -/

theorem clipSqrt_mul_self {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (hw : w ≠ 0) : clipSqrt w S * clipSqrt w S = clipM w S := by
  unfold clipSqrt clipM
  have h_nonneg : ∀ s : ℝ, 0 ≤ max s (w ^ 2) := by
    intro s
    have hw_sq_nonneg : 0 ≤ w ^ 2 := pow_two_nonneg w
    exact le_trans hw_sq_nonneg (le_max_right s (w ^ 2))
  have h_fun_eq : (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) * (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) =
      (fun s : ℝ => (max s (w ^ 2))⁻¹) := by
    ext s
    calc
      (Real.sqrt (max s (w ^ 2)))⁻¹ * (Real.sqrt (max s (w ^ 2)))⁻¹ =
        ((Real.sqrt (max s (w ^ 2))) * (Real.sqrt (max s (w ^ 2))))⁻¹ := by rw [mul_inv]
      _ = (max s (w ^ 2))⁻¹ := by rw [Real.mul_self_sqrt (h_nonneg s)]
  have h_spec_fin : Set.Finite (spectrum ℝ S) := Matrix.finite_spectrum S
  have h_cont : ContinuousOn (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) (spectrum ℝ S) :=
    h_spec_fin.continuousOn _
  rw [← cfc_mul (f := fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹)
    (g := fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) (a := S) (hf := h_cont) (hg := h_cont)]
  exact congrArg (fun f : ℝ → ℝ => cfc f S) h_fun_eq

theorem clipM_isHermitian {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : (clipM w S).IsHermitian := by
  exact (IsSelfAdjoint.cfc (a := S) (f := fun s : ℝ => (max s (w ^ 2))⁻¹)).isHermitian

theorem clipSqrt_isHermitian {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    (clipSqrt w S).IsHermitian := by
  unfold clipSqrt
  exact (IsSelfAdjoint.cfc (a := S) (f := fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹)).isHermitian

theorem clipSqrt_posDef {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0) :
    (clipSqrt w S).PosDef := by
  have hw_sq_pos : w ^ 2 > 0 := sq_pos_iff.mpr hw
  have h_nonneg : 0 ≤ clipSqrt w S := by
    refine cfc_nonneg fun x hx => ?_
    have hx_max : 0 < max x (w ^ 2) := lt_max_of_lt_right hw_sq_pos
    have h_sqrt_pos : 0 < Real.sqrt (max x (w ^ 2)) := Real.sqrt_pos.mpr hx_max
    have h_inv_nonneg : 0 ≤ (Real.sqrt (max x (w ^ 2)))⁻¹ := by
      positivity
    exact h_inv_nonneg
  have h_unit : IsUnit (clipSqrt w S) := by
    dsimp [clipSqrt]
    have h_cont : ContinuousOn (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) (spectrum ℝ S) :=
      (Matrix.finite_real_spectrum (A := S)).continuousOn _
    refine ((isUnit_cfc_iff (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) S h_cont hS).mpr ?_)
    intro x hx
    have hx_max : 0 < max x (w ^ 2) := lt_max_of_lt_right hw_sq_pos
    have h_sqrt_pos : 0 < Real.sqrt (max x (w ^ 2)) := Real.sqrt_pos.mpr hx_max
    exact ne_of_gt (inv_pos.mpr h_sqrt_pos)
  have h_posSemidef : (clipSqrt w S).PosSemidef := h_nonneg.posSemidef
  exact (h_posSemidef.posDef_iff_isUnit.mpr h_unit)

theorem clipM_posDef {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0) :
    (clipM w S).PosDef := by
  have hw_sq_pos : w ^ 2 > 0 := sq_pos_iff.mpr hw
  have hpos : ∀ x : ℝ, 0 ≤ (max x (w ^ 2))⁻¹ := by
    intro x
    have hmax_nonneg : 0 ≤ max x (w ^ 2) := by
      have : 0 ≤ w ^ 2 := pow_two_nonneg w
      exact le_max_of_le_right this
    exact inv_nonneg.mpr hmax_nonneg
  have hnezero : ∀ x : ℝ, (max x (w ^ 2))⁻¹ ≠ 0 := by
    intro x
    refine inv_ne_zero (by
      intro h
      have hmax_ge : max x (w ^ 2) ≥ w ^ 2 := le_max_right _ _
      linarith)
  have hS_selfadjoint : IsSelfAdjoint S := hS
  have h_cont : ContinuousOn (fun s : ℝ => (max s (w ^ 2))⁻¹) (spectrum ℝ S) := by
    have h_cont_f : Continuous (fun s : ℝ => (max s (w ^ 2))⁻¹) := by
      have h_max_cont : Continuous (fun s : ℝ => max s (w ^ 2)) :=
        Continuous.max continuous_id continuous_const
      have h_never_zero : ∀ s : ℝ, max s (w ^ 2) ≠ 0 := by
        intro s
        have hge : max s (w ^ 2) ≥ w ^ 2 := le_max_right _ _
        linarith
      exact h_max_cont.inv₀ h_never_zero
    exact h_cont_f.continuousOn.mono (Set.subset_univ _)
  have h_nonneg_spectrum : ∀ x ∈ spectrum ℝ S, 0 ≤ (max x (w ^ 2))⁻¹ := by
    intro x hx
    exact hpos x
  have h_ne_zero_spectrum : ∀ x ∈ spectrum ℝ S, (max x (w ^ 2))⁻¹ ≠ 0 := by
    intro x hx
    exact hnezero x
  have h_nonneg : 0 ≤ clipM w S := by
    unfold clipM
    exact cfc_nonneg h_nonneg_spectrum
  have h_posSemidef : (clipM w S).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp h_nonneg
  have h_isUnit : IsUnit (clipM w S) := by
    unfold clipM
    exact ((isUnit_cfc_iff (fun s : ℝ => (max s (w ^ 2))⁻¹) S h_cont hS_selfadjoint).mpr h_ne_zero_spectrum)
  exact (Matrix.PosSemidef.posDef_iff_isUnit h_posSemidef).mpr h_isUnit

theorem frameA_injective {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0) :
    Function.Injective (frameA w S) := by
  have hpos : (clipSqrt w S).PosDef := clipSqrt_posDef w S hS hw
  have hisUnit : IsUnit (clipSqrt w S) := Matrix.PosDef.isUnit hpos
  have hinj_mulVec : Function.Injective (clipSqrt w S).mulVec :=
    Matrix.mulVec_injective_of_isUnit hisUnit
  intro x y h
  have h_ofLp : ((frameA w S) x).ofLp = ((frameA w S) y).ofLp := by rw [h]
  dsimp [frameA] at h_ofLp
  have h_ofLp_eq : x.ofLp = y.ofLp := hinj_mulVec h_ofLp
  exact WithLp.ofLp_injective 2 h_ofLp_eq

theorem frameW_eq_cfc {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    frameW w S = cfc (fun s : ℝ => s + w ^ 2) S := by
  haveI hS_selfadj : IsSelfAdjoint S := hS.isSelfAdjoint
  have h_cont_id : ContinuousOn (fun (x : ℝ) => x) (spectrum ℝ S) :=
    continuous_id.continuousOn
  have h_cfc_add := cfc_add_const (R := ℝ) (w ^ 2) (fun (s : ℝ) => s) S h_cont_id (ha := hS_selfadj)
  calc
    frameW w S = S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := rfl
    _ = S + algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) (w ^ 2) := by
      rw [← Algebra.algebraMap_eq_smul_one (R := ℝ) (A := Matrix (Fin d) (Fin d) ℝ) (w ^ 2)]
    _ = (cfc (fun (s : ℝ) => s) S) + algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) (w ^ 2) := by
      rw [cfc_id' (R := ℝ) (ha := hS_selfadj)]
    _ = cfc (fun s : ℝ => s + w ^ 2) S := by
      rw [← h_cfc_add]

theorem frameW_inv_eq_cfc {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hw : w ≠ 0) :
    (frameW w S)⁻¹ = cfc (fun s : ℝ => (s + w ^ 2)⁻¹) S := by
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have hS_nonneg : 0 ≤ S := hS.nonneg
  have hS_selfadj : IsSelfAdjoint S := hS.isHermitian.isSelfAdjoint
  have h_frameW : frameW w S = cfc (fun s : ℝ => s + w ^ 2) S := by
    dsimp [frameW]
    have hS_eq : S = cfc (fun s : ℝ => s) S := (cfc_id ℝ S (ha := hS_selfadj)).symm
    calc
      S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) = cfc (fun s : ℝ => s) S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        nth_rw 1 [hS_eq]
      _ = cfc (fun s : ℝ => s) S + cfc (fun _ : ℝ => w ^ 2) S := by
        rw [cfc_const (w ^ 2) S (ha := hS_selfadj), Algebra.algebraMap_eq_smul_one]
      _ = cfc (fun s : ℝ => s + w ^ 2) S := by
        rw [← cfc_add S (fun s : ℝ => s) (fun _ : ℝ => w ^ 2)]
  rw [h_frameW]
  apply Matrix.inv_eq_left_inv
  have h_cont_add : ContinuousOn (fun s : ℝ => s + w ^ 2) (spectrum ℝ S) :=
    (continuous_id.add continuous_const).continuousOn
  have h_spectrum_nonneg : ∀ x ∈ spectrum ℝ S, 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg hS_nonneg hx
  have h_nonzero : ∀ x ∈ spectrum ℝ S, x + w ^ 2 ≠ 0 := by
    intro x hx
    have hx_nonneg : 0 ≤ x := h_spectrum_nonneg x hx
    linarith
  have h_cont_inv : ContinuousOn (fun s : ℝ => (s + w ^ 2)⁻¹) (spectrum ℝ S) :=
    h_cont_add.inv₀ h_nonzero
  rw [← cfc_mul (fun s : ℝ => (s + w ^ 2)⁻¹) (fun s : ℝ => s + w ^ 2) S h_cont_inv h_cont_add]
  have h_eq_on : ∀ x ∈ spectrum ℝ S, ((x + w ^ 2)⁻¹) * (x + w ^ 2) = (1 : ℝ) := by
    intro x hx
    have h_ne : x + w ^ 2 ≠ 0 := h_nonzero x hx
    field_simp [h_ne]
  rw [cfc_congr' h_eq_on, cfc_const_one ℝ S (ha := hS_selfadj)]

theorem clipM_inv_eq_cfc {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0) :
    (clipM w S)⁻¹ = cfc (fun s : ℝ => max s (w ^ 2)) S := by
  have hw2pos : 0 < w ^ 2 := sq_pos_of_ne_zero hw
  have hfin : (spectrum ℝ S).Finite := Matrix.finite_real_spectrum
  have h_cont_max : ContinuousOn (fun s : ℝ => max s (w ^ 2)) (spectrum ℝ S) :=
    hfin.continuousOn _
  have h_cont_inv : ContinuousOn (fun s : ℝ => (max s (w ^ 2))⁻¹) (spectrum ℝ S) :=
    hfin.continuousOn _
  apply Matrix.inv_eq_left_inv
  dsimp [clipM]
  calc
    cfc (fun s : ℝ => max s (w ^ 2)) S * cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S
        = cfc (fun s : ℝ => max s (w ^ 2) * (max s (w ^ 2))⁻¹) S := by
      rw [cfc_mul _ _ _ h_cont_max h_cont_inv]
    _ = cfc (fun _ : ℝ => (1 : ℝ)) S := by
      refine cfc_congr ?_
      intro s hs
      have hpos : max s (w ^ 2) ≠ 0 := by
        intro hzero
        have hle : w ^ 2 ≤ 0 := by
          have := le_max_right s (w ^ 2)
          linarith
        linarith
      field_simp [hpos]
    _ = 1 := by rw [cfc_const_one ℝ S]

theorem DM_eq_trace_cfc {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    DM w S = trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S) := by
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) :=
    fun f => (Matrix.finite_real_spectrum (A := S)).continuousOn f
  calc
    DM w S = trace (clipM w S * S) := rfl
    _ = trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S * S) := rfl
    _ = trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S * cfc (fun s : ℝ => s) S) := by
      rw [cfc_id' ℝ S]
    _ = trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹ * s) S) := by
      rw [← cfc_mul (fun s => (max s (w ^ 2))⁻¹) (fun s => s) S (hc _) (hc _)]
    _ = trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S) := by
      have h_eq : (fun s : ℝ => (max s (w ^ 2))⁻¹ * s) = (fun s : ℝ => s / max s (w ^ 2)) := by
        ext s
        calc
          (max s (w ^ 2))⁻¹ * s = s * (max s (w ^ 2))⁻¹ := mul_comm _ _
          _ = s / max s (w ^ 2) := by rw [div_eq_mul_inv]
      rw [h_eq]

/-- The trace of `f(S)` is the sum of `f` over the eigenvalues of `S`. -/
theorem trace_cfc_eq_sum {d : ℕ} (f : ℝ → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    trace (cfc f S) = ∑ i, f (hS.eigenvalues i) := by
  rw [hS.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

/-- `d_live` is the number of eigenvalues of `S` at least `w²`. -/
theorem dLive_eq_card {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    dLive w S = ((Finset.univ.filter fun i => w ^ 2 ≤ hS.eigenvalues i).card : ℝ) := by
  unfold dLive
  rw [trace_cfc_eq_sum _ S hS, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- `D_M = Σ_i λ_i / max(λ_i, w²)`. -/
theorem DM_eq_sum {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    DM w S = ∑ i, hS.eigenvalues i / max (hS.eigenvalues i) (w ^ 2) := by
  rw [DM_eq_trace_cfc w S hS, trace_cfc_eq_sum _ S hS]

/-! ## The metric as a quadratic form -/

/-- `⟨u, v⟩_M = uᵀ M v`. -/
theorem inner_frameA {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0)
    (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪frameA w S u, frameA w S v⟫ = (WithLp.ofLp u) ⬝ᵥ (clipM w S *ᵥ WithLp.ofLp v) := by
  set B := clipSqrt w S with hB
  have hB_herm : B.IsHermitian := clipSqrt_isHermitian w S
  have h_mul_self : B * B = clipM w S := clipSqrt_mul_self w S hS hw
  have hB_transpose_eq : B.transpose = B := by
    calc
      B.transpose = B.conjTranspose := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = B := hB_herm.eq
  calc
    ⟪frameA w S u, frameA w S v⟫
        = ((frameA w S v).ofLp) ⬝ᵥ star ((frameA w S u).ofLp) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = ((frameA w S v).ofLp) ⬝ᵥ ((frameA w S u).ofLp) := by simp
    _ = ((B.mulVec (WithLp.ofLp v)) ⬝ᵥ (B.mulVec (WithLp.ofLp u))) := by
      simp [frameA, Matrix.ofLp_toEuclideanCLM, hB]
    _ = (Matrix.vecMul (B.mulVec (WithLp.ofLp v)) B) ⬝ᵥ (WithLp.ofLp u) := by
      rw [Matrix.dotProduct_mulVec]
    _ = ((B.transpose.mulVec (B.mulVec (WithLp.ofLp v))) ⬝ᵥ (WithLp.ofLp u)) := by
      rw [Matrix.mulVec_transpose]
    _ = (((B.transpose * B).mulVec (WithLp.ofLp v)) ⬝ᵥ (WithLp.ofLp u)) := by
      rw [Matrix.mulVec_mulVec]
    _ = (((B * B).mulVec (WithLp.ofLp v)) ⬝ᵥ (WithLp.ofLp u)) := by rw [hB_transpose_eq]
    _ = ((clipM w S).mulVec (WithLp.ofLp v)) ⬝ᵥ (WithLp.ofLp u) := by rw [h_mul_self]
    _ = (WithLp.ofLp u) ⬝ᵥ ((clipM w S).mulVec (WithLp.ofLp v)) := by rw [dotProduct_comm]
    _ = (WithLp.ofLp u) ⬝ᵥ (clipM w S *ᵥ WithLp.ofLp v) := rfl

/-- `|v|_M² = vᵀ M v`. -/
theorem norm_frameA_sq {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖frameA w S v‖ ^ 2 = (WithLp.ofLp v) ⬝ᵥ (clipM w S *ᵥ WithLp.ofLp v) := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_frameA w S hS hw v v

/-! ## (F1) to (F3) -/

/-- (F1): `w² M ≤ I`. -/
theorem smul_clipM_le_one {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : w ≠ 0) :
    (w ^ 2) • clipM w S ≤ 1 := by
  have hw2pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have h_cont_inner : ContinuousOn (fun (s : ℝ) => (max s (w ^ 2))⁻¹) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  have h_cont_mul : ContinuousOn (fun (s : ℝ) => w ^ 2 * (max s (w ^ 2))⁻¹) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  rw [clipM]
  rw [← cfc_smul (w ^ 2) (fun s : ℝ => (max s (w ^ 2))⁻¹) S h_cont_inner]
  have h_one : (1 : Matrix (Fin d) (Fin d) ℝ) = cfc (fun _ : ℝ => (1 : ℝ)) S := by
    rw [cfc_const_one (R := ℝ) (a := S)]
  rw [h_one]
  refine cfc_mono ?_ h_cont_mul continuousOn_const
  intro x hx
  have hmaxpos : 0 < max x (w ^ 2) := lt_max_of_lt_right hw2pos
  have hmaxpos_ne : max x (w ^ 2) ≠ 0 := by linarith
  calc
    w ^ 2 * (max x (w ^ 2))⁻¹ ≤ max x (w ^ 2) * (max x (w ^ 2))⁻¹ := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _) (by
        apply inv_nonneg.mpr (le_of_lt hmaxpos))
    _ = 1 := by field_simp [hmaxpos_ne]

/-- (F1), operator form: `‖M^{1/2}‖ ≤ 1/w`. -/
theorem norm_frameA_le {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : 0 < w) :
    ‖frameA w S‖ ≤ 1 / w := by
  have hw0 : w ≠ 0 := hw.ne'
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := WithLp.ofLp v with hu
  have h1 := norm_frameA_sq w S hS hw0 v
  have h3 := (Matrix.le_iff.1 (smul_clipM_le_one w S hS hw0)).dotProduct_mulVec_nonneg u
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at h3
  have hv : ‖v‖ ^ 2 = u ⬝ᵥ u := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  have hsq : (w * ‖frameA w S v‖) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [mul_pow, h1, hv, ← hu]; linarith
  have hle : w * ‖frameA w S v‖ ≤ ‖v‖ := by
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hw]
  linarith

/-- (F1), pointwise: `|v|_M ≤ ‖v‖/w`. -/
theorem norm_frameA_apply_le {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (hw : 0 < w) (v : EuclideanSpace ℝ (Fin d)) : ‖frameA w S v‖ ≤ ‖v‖ / w := by
  have h := norm_frameA_le w S hS hw
  calc
    ‖frameA w S v‖ ≤ ‖frameA w S‖ * ‖v‖ := ContinuousLinearMap.le_opNorm (frameA w S) v
    _ ≤ (1 / w) * ‖v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖v‖ / w := by ring

/-- (F2): `W⁻¹ ≤ M`. -/
theorem frameW_inv_le_clipM {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hw : w ≠ 0) : (frameW w S)⁻¹ ≤ clipM w S := by
  rw [frameW_inv_eq_cfc w S hS hw]
  have h_cont1 : ContinuousOn (fun s : ℝ => (s + w ^ 2)⁻¹) (spectrum ℝ S) := by
    have h_add : ContinuousOn (fun s : ℝ => s + w ^ 2) (spectrum ℝ S) :=
      (continuous_id.add continuous_const).continuousOn
    have h_ne_zero : ∀ s ∈ spectrum ℝ S, s + w ^ 2 ≠ 0 := by
      intro s hs
      have hs_nonneg : 0 ≤ s := spectrum_nonneg_of_nonneg hS.nonneg hs
      nlinarith [sq_pos_iff.mpr hw]
    exact h_add.inv₀ h_ne_zero
  have h_cont2 : ContinuousOn (fun s : ℝ => (max s (w ^ 2))⁻¹) (spectrum ℝ S) := by
    have h_max : ContinuousOn (fun s : ℝ => max s (w ^ 2)) (spectrum ℝ S) :=
      (continuous_id.max continuous_const).continuousOn
    have h_ne_zero : ∀ s ∈ spectrum ℝ S, max s (w ^ 2) ≠ 0 := by
      intro s hs
      have hs_nonneg : 0 ≤ s := spectrum_nonneg_of_nonneg hS.nonneg hs
      have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
      have h_max_pos : 0 < max s (w ^ 2) := lt_max_of_lt_right hw_sq_pos
      exact ne_of_gt h_max_pos
    exact h_max.inv₀ h_ne_zero
  refine cfc_mono ?_ h_cont1 h_cont2
  · intro x hx
    have hx_nonneg : 0 ≤ x := spectrum_nonneg_of_nonneg hS.nonneg hx
    have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
    have hw_sq_nonneg : 0 ≤ w ^ 2 := by nlinarith
    have h_max_pos : 0 < max x (w ^ 2) := lt_max_of_lt_right hw_sq_pos
    have h_max_le_sum : max x (w ^ 2) ≤ x + w ^ 2 := by
      exact max_le (le_add_of_nonneg_right hw_sq_nonneg) (le_add_of_nonneg_left hx_nonneg)
    exact inv_anti₀ h_max_pos h_max_le_sum

/-- (F2): `M ≤ 2 W⁻¹`. -/
theorem clipM_le_two_frameW_inv {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hw : w ≠ 0) : clipM w S ≤ (2 : ℝ) • (frameW w S)⁻¹ := by
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have hS_nonneg : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS
  have h_spec_nonneg : ∀ x ∈ spectrum ℝ S, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg hS_nonneg hx
  have h_inv_eq : (frameW w S)⁻¹ = cfc (fun s : ℝ => (s + w ^ 2)⁻¹) S :=
    frameW_inv_eq_cfc w S hS hw
  rw [h_inv_eq]
  have h_cont_inv : ContinuousOn (fun s : ℝ => (s + w ^ 2)⁻¹) (spectrum ℝ S) := by
    have h_pos : ∀ x ∈ spectrum ℝ S, x + w ^ 2 ≠ 0 := by
      intro x hx
      have hx_nonneg := h_spec_nonneg x hx
      linarith
    have h_cont_add : ContinuousOn (fun s : ℝ => s + w ^ 2) (spectrum ℝ S) :=
      (continuous_id.add continuous_const).continuousOn
    exact h_cont_add.inv₀ h_pos
  have h_two_smul : (2 : ℝ) • cfc (fun s : ℝ => (s + w ^ 2)⁻¹) S =
      cfc (fun s : ℝ => (2 : ℝ) * (s + w ^ 2)⁻¹) S := by
    rw [cfc_const_mul (2 : ℝ) (fun s : ℝ => (s + w ^ 2)⁻¹) S h_cont_inv]
  rw [h_two_smul]
  have h_cont_max_inv : ContinuousOn (fun s : ℝ => (max s (w ^ 2))⁻¹) (spectrum ℝ S) := by
    have h_pos : ∀ x ∈ spectrum ℝ S, max x (w ^ 2) ≠ 0 := by
      intro x hx
      have hx_nonneg := h_spec_nonneg x hx
      exact ne_of_gt (lt_max_of_lt_right (b := x) hw_sq_pos)
    have h_cont_max : ContinuousOn (fun s : ℝ => max s (w ^ 2)) (spectrum ℝ S) :=
      (continuous_id.max continuous_const).continuousOn
    exact h_cont_max.inv₀ h_pos
  have h_cont_two_mul : ContinuousOn (fun s : ℝ => (2 : ℝ) * (s + w ^ 2)⁻¹) (spectrum ℝ S) := by
    have h_cont_const : ContinuousOn (fun _ : ℝ => (2 : ℝ)) (spectrum ℝ S) :=
      continuous_const.continuousOn
    exact h_cont_const.mul h_cont_inv
  refine cfc_mono (fun x hx => ?_) h_cont_max_inv h_cont_two_mul
  have hx_nonneg : 0 ≤ x := h_spec_nonneg x hx
  have hx_add_w2_pos : 0 < x + w ^ 2 := by linarith
  have hmax_pos : 0 < max x (w ^ 2) := lt_max_of_lt_right (b := x) hw_sq_pos
  have hineq : x + w ^ 2 ≤ 2 * max x (w ^ 2) := by
    nlinarith [le_max_left x (w ^ 2), le_max_right x (w ^ 2)]
  have h_inv_ineq : (2 * max x (w ^ 2))⁻¹ ≤ (x + w ^ 2)⁻¹ :=
    ((inv_le_inv₀ (by nlinarith) hx_add_w2_pos).mpr hineq)
  calc
    (max x (w ^ 2))⁻¹ = (2 : ℝ) * ((2 : ℝ) * max x (w ^ 2))⁻¹ := by ring
    _ ≤ (2 : ℝ) * ((x + w ^ 2)⁻¹) := by
      have hpos : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_left h_inv_ineq hpos

/-- (F2): `W ≤ 2 M⁻¹`. -/
theorem frameW_le_two_clipM_inv {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hw : w ≠ 0) : frameW w S ≤ (2 : ℝ) • (clipM w S)⁻¹ := by
  have hS_herm : S.IsHermitian := hS.isHermitian
  have hS_nonneg : 0 ≤ S := by rwa [Matrix.nonneg_iff_posSemidef]
  have hspec_nonneg : ∀ x ∈ spectrum ℝ S, 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg hS_nonneg hx
  have h_frameW : frameW w S = cfc (fun s : ℝ => s + w ^ 2) S := by
    dsimp [frameW]
    have h_id : cfc (fun s : ℝ => s) S = S := by
      simpa using cfc_id' ℝ S
    have h_const : cfc (fun _ : ℝ => (w : ℝ) ^ 2) S = ((w : ℝ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using cfc_const (R := ℝ) (A := Matrix (Fin d) (Fin d) ℝ) ((w : ℝ) ^ 2) S
    calc
      S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) = cfc (fun s : ℝ => s) S + ((w : ℝ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [h_id]
      _ = cfc (fun s : ℝ => s) S + cfc (fun _ : ℝ => (w : ℝ) ^ 2) S := by rw [h_const]
      _ = cfc (fun s : ℝ => s + (w : ℝ) ^ 2) S :=
        (cfc_add S (fun s : ℝ => s) (fun _ : ℝ => (w : ℝ) ^ 2)
          ((Matrix.finite_real_spectrum (A := S)).continuousOn (fun s : ℝ => s))
          ((Matrix.finite_real_spectrum (A := S)).continuousOn (fun _ : ℝ => (w : ℝ) ^ 2))).symm
  have h_clipM_inv : (clipM w S)⁻¹ = cfc (fun s : ℝ => max s (w ^ 2)) S :=
    clipM_inv_eq_cfc w S hS_herm hw
  have h_cont : ContinuousOn (fun s : ℝ => max s (w ^ 2)) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  have h_cont_id : ContinuousOn (fun s : ℝ => s) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  have h_cont_add : ContinuousOn (fun s : ℝ => s + w ^ 2) (spectrum ℝ S) :=
    h_cont_id.add continuousOn_const
  have h_cont_mul : ContinuousOn (fun s : ℝ => 2 * max s (w ^ 2)) (spectrum ℝ S) :=
    (continuousOn_const.mul h_cont)
  have h_mul : (2 : ℝ) • cfc (fun s : ℝ => max s (w ^ 2)) S = cfc (fun s : ℝ => 2 * max s (w ^ 2)) S := by
    rw [← cfc_const_mul (2 : ℝ) (fun s : ℝ => max s (w ^ 2)) S h_cont]
  have h_ineq : ∀ x ∈ spectrum ℝ S, (fun s : ℝ => s + w ^ 2) x ≤ (fun s : ℝ => 2 * max s (w ^ 2)) x := by
    intro x hx
    dsimp
    have h1 : x ≤ max x (w ^ 2) := le_max_left _ _
    have h2 : w ^ 2 ≤ max x (w ^ 2) := le_max_right _ _
    linarith
  have h_cfc_mono : cfc (fun s : ℝ => s + w ^ 2) S ≤ cfc (fun s : ℝ => 2 * max s (w ^ 2)) S :=
    cfc_mono h_ineq h_cont_add h_cont_mul
  calc
    frameW w S = cfc (fun s : ℝ => s + w ^ 2) S := h_frameW
    _ ≤ cfc (fun s : ℝ => 2 * max s (w ^ 2)) S := h_cfc_mono
    _ = (2 : ℝ) • cfc (fun s : ℝ => max s (w ^ 2)) S := by rw [h_mul]
    _ = (2 : ℝ) • (clipM w S)⁻¹ := by rw [h_clipM_inv]

/-- (F3): `d_live ≤ D_M`. -/
theorem dLive_le_DM {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hw : w ≠ 0) :
    dLive w S ≤ DM w S := by
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have hS_herm : S.IsHermitian := hS.isHermitian
  have h_spec_nonneg : spectrum ℝ S ⊆ {a | 0 ≤ a} :=
    ((Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg).mp hS).2
  have h_dm_eq : DM w S = trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S) := by
    rw [DM_eq_trace_cfc w S hS_herm]
  rw [h_dm_eq]
  dsimp [dLive]
  have h_cont_indicator : ContinuousOn (fun s : ℝ => if w ^ 2 ≤ s then (1 : ℝ) else 0) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  have h_denom_pos : ∀ s : ℝ, 0 < max s (w ^ 2) := by
    intro s
    exact lt_max_of_lt_right hw_sq_pos
  have h_cont_div : ContinuousOn (fun s : ℝ => s / max s (w ^ 2)) (spectrum ℝ S) := by
    refine Continuous.continuousOn ?_
    refine Continuous.div continuous_id ?_ (fun s => (h_denom_pos s).ne')
    exact Continuous.max continuous_id continuous_const
  have h_cfc_le : cfc (fun s : ℝ => if w ^ 2 ≤ s then (1 : ℝ) else 0) S ≤
                  cfc (fun s : ℝ => s / max s (w ^ 2)) S := by
    refine cfc_mono ?_ h_cont_indicator h_cont_div
    intro x hx
    have hx_nonneg : 0 ≤ x := h_spec_nonneg hx
    by_cases h : w ^ 2 ≤ x
    · have hx_pos : 0 < x := by linarith
      simp [h, hx_pos.ne']
    · have h_max : max x (w ^ 2) = w ^ 2 := max_eq_right (by linarith)
      have h_nonneg_div : 0 ≤ x / max x (w ^ 2) := by
        rw [h_max]
        exact div_nonneg hx_nonneg (by linarith)
      simp [h, h_nonneg_div]
  have h_psd : (cfc (fun s : ℝ => s / max s (w ^ 2)) S -
                cfc (fun s : ℝ => if w ^ 2 ≤ s then (1 : ℝ) else 0) S).PosSemidef :=
    (Matrix.le_iff.mp h_cfc_le)
  have h_trace_diff_nonneg : 0 ≤ trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S -
                                        cfc (fun s : ℝ => if w ^ 2 ≤ s then (1 : ℝ) else 0) S) :=
    Matrix.PosSemidef.trace_nonneg h_psd
  rw [Matrix.trace_sub] at h_trace_diff_nonneg
  linarith

/-- (F3): `D_M ≤ d`. -/
theorem DM_le {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hw : w ≠ 0) :
    DM w S ≤ d := by
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have hS_nonneg : 0 ≤ S := hS.nonneg
  have hS_herm : S.IsHermitian := hS.isHermitian
  have h_cont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn f
  have h_mul : clipM w S * S ≤ (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [clipM]
    -- goal: cfc (fun s => (max s (w^2))⁻¹) S * S ≤ 1
    -- rewrite S as cfc id S only on the right factor
    nth_rw 2 [← cfc_id' ℝ S]
    -- goal: cfc (fun s => (max s (w^2))⁻¹) S * cfc (fun x => x) S ≤ 1
    rw [← cfc_mul (fun s : ℝ => (max s (w ^ 2))⁻¹) (fun x : ℝ => x) S (h_cont _) (h_cont _)]
    -- goal: cfc (fun s => (max s (w^2))⁻¹ * x) S ≤ 1
    have h_one : cfc (fun _ : ℝ => (1 : ℝ)) S = (1 : Matrix (Fin d) (Fin d) ℝ) := cfc_const_one ℝ S
    rw [← h_one]
    refine cfc_mono (fun x hx => ?_) (h_cont (fun s : ℝ => (max s (w ^ 2))⁻¹ * s)) (h_cont (fun _ : ℝ => (1 : ℝ)))
    have hx_nonneg : 0 ≤ x := ((StarOrderedRing.nonneg_iff_spectrum_nonneg S).mp hS_nonneg) x hx
    have h_max_pos : 0 < max x (w ^ 2) := lt_max_of_lt_right hw_sq_pos
    calc
      (max x (w ^ 2))⁻¹ * x ≤ (max x (w ^ 2))⁻¹ * max x (w ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = 1 := by field_simp [ne_of_gt h_max_pos]
  have h_sub_nonneg : ((1 : Matrix (Fin d) (Fin d) ℝ) - clipM w S * S).PosSemidef := by
    rwa [Matrix.le_iff] at h_mul
  have h_trace_sub_nonneg : 0 ≤ ((1 : Matrix (Fin d) (Fin d) ℝ) - clipM w S * S).trace :=
    h_sub_nonneg.trace_nonneg
  have h_trace_sub : ((1 : Matrix (Fin d) (Fin d) ℝ) - clipM w S * S).trace =
      (1 : Matrix (Fin d) (Fin d) ℝ).trace - (clipM w S * S).trace := by
    rw [Matrix.trace_sub]
  rw [h_trace_sub] at h_trace_sub_nonneg
  have h_trace_one : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by
    rw [Matrix.trace_one, Fintype.card_fin]
  rw [h_trace_one] at h_trace_sub_nonneg
  rw [DM]
  linarith

/-- `0 ≤ D_M`. -/
theorem DM_nonneg {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hw : w ≠ 0) :
    0 ≤ DM w S := by
  -- From hS, S is Hermitian and has nonnegative spectrum
  rcases (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hS) with ⟨hS_herm, hS_spec⟩
  have hS_selfadj : IsSelfAdjoint S := hS_herm.isSelfAdjoint
  -- w^2 > 0 since w ≠ 0
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  -- Functions are continuous on the finite spectrum
  have h_cont_inv : ContinuousOn (fun s : ℝ => (max s (w ^ 2))⁻¹) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  have h_cont_id : ContinuousOn (fun s : ℝ => s) (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn _
  -- Express DM in terms of cfc
  have hDM_eq : DM w S = trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S) := by
    dsimp [DM, clipM]
    -- Goal: trace (cfc (fun s => (max s (w^2))⁻¹) S * S) = trace (cfc (fun s => s / max s (w^2)) S)
    calc
      trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S * S)
          = trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹) S * cfc (fun x : ℝ => x) S) := by
        rw [cfc_id' (R := ℝ) (ha := hS_selfadj)]
      _ = trace (cfc (fun s : ℝ => (max s (w ^ 2))⁻¹ * s) S) := by
        rw [← cfc_mul (fun s : ℝ => (max s (w ^ 2))⁻¹) (fun s : ℝ => s) S h_cont_inv h_cont_id]
      _ = trace (cfc (fun s : ℝ => s / max s (w ^ 2)) S) := by
        congr
        ext s
        simp [div_eq_mul_inv, mul_comm]
  rw [hDM_eq]
  -- Show cfc (fun s => s / max s (w^2)) S is nonnegative
  have h_cfc_nonneg : 0 ≤ cfc (fun s : ℝ => s / max s (w ^ 2)) S := by
    refine cfc_nonneg fun x hx => ?_
    -- hx : x ∈ spectrum ℝ S, so x ≥ 0
    have hx_nonneg : 0 ≤ x := hS_spec hx
    -- denominator is nonnegative since max x (w^2) ≥ w^2 > 0
    have h_den_nonneg : 0 ≤ max x (w ^ 2) :=
      calc
        0 ≤ w ^ 2 := by positivity
        _ ≤ max x (w ^ 2) := le_max_right _ _
    exact div_nonneg hx_nonneg h_den_nonneg
  -- By Matrix.nonneg_iff_posSemidef, it's PosSemidef
  have h_pos_semidef : (cfc (fun s : ℝ => s / max s (w ^ 2)) S).PosSemidef := by
    rwa [← Matrix.nonneg_iff_posSemidef]
  -- And trace of PosSemidef is nonnegative
  exact Matrix.PosSemidef.trace_nonneg h_pos_semidef

/-- The trace bound of (L4): `w² tr W⁻¹ ≤ d - d_live/2` (at most `1/2` per live direction, `1` per other). -/
theorem sq_trace_frameW_inv_le {d : ℕ} (w : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hw : w ≠ 0) : w ^ 2 * trace (frameW w S)⁻¹ ≤ d - dLive w S / 2 := by
  rw [frameW_inv_eq_cfc w S hS hw, trace_cfc_eq_sum _ S hS.1, dLive_eq_card w S hS.1, Finset.mul_sum,
    Finset.card_filter, Nat.cast_sum, Finset.sum_div]
  have hd : (d : ℝ) = ∑ _i : Fin d, (1 : ℝ) := by simp
  rw [hd, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl := hS.eigenvalues_nonneg i
  have hw2 : 0 < w ^ 2 := by positivity
  have hpos : 0 < hS.1.eigenvalues i + w ^ 2 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  split_ifs with h
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ## The Lipschitz constant of the dent -/

/-- The Lipschitz constant of the dent in the frame (Lemma 9.4): `κ r₁ ‖M^{1/2}‖ ≤ κ r₁ / w`. -/
theorem lipschitz_const_le {d : ℕ} (w κ r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (hw : 0 < w) (hκ : 0 ≤ κ) (hr : 0 ≤ r₁) : κ * r₁ * ‖frameA w S‖ ≤ κ * r₁ / w := by
  have hnr : 0 ≤ κ * r₁ := mul_nonneg hκ hr
  have hnorm := norm_frameA_le w S hS hw
  calc
    κ * r₁ * ‖frameA w S‖ ≤ κ * r₁ * (1 / w) := mul_le_mul_of_nonneg_left hnorm hnr
    _ = κ * r₁ / w := by ring

end AdversarialBco.Lower
