/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Moments
public import AdversarialBco.Conj1Lower.Frame
public import AdversarialBco.Conj1Lower.CellsRound
public import AdversarialBco.Conj1Lower.CellMeas
public import AdversarialBco.Conj1Lower.Bayes
public import AdversarialBco.Conj1Lower.RuleS

@[expose] public section

/-!
# The ledger: Lemma 9.8

`Λ(π) = (1/2) ln det(Σ(π) + w² I)` (`lam`), `W = Σ(π) + w² I` (`frameW` of Frame.lean). For a cell `c` of mass
`p_c = π(c)`: `S_c = p_c⁻¹ ∫_c (θ - m)(θ - m)ᵀ dπ` (`m` the mean of `π`), `U_c = S_c + w² I` (`cellU`), and
`Σ_i ψ(u_{c,i})`, `u_{c,i}` the eigenvalues of `W^{-1/2} U_c W^{-1/2}`, written without eigenvalues as
`psiSum W U_c = tr(W⁻¹U_c) - d - ln det U_c + ln det W`. The payment of a cell is `cellPay = p_c psiSum W U_c / 2`.

Route (S4): every bound comes from one matrix inequality,
`ln det X ≤ ln det U + tr(U⁻¹X) - d` (`logdet_le_logdet_add_trace`), with no matrix Jensen.

* (L1) `ledger_identity`: `∑_c p_c psiSum W U_c = ln det W - ∑_c p_c ln det U_c` (an identity, `∑_c p_c U_c = W`).
* (L2) `ledger_round`: for any finite measurable partition (the answer map `c`) and any signal `s`, with the
  posterior `bayesUpd π (lik c s σ² (c θ) (s θ + σ z))` of BayesRound.lean,
  `E Λ(π') ≤ Λ(π) - (1/2) ∑_c p_c psiSum W U_c`: (S4) pointwise, `Σ(π') ≤ ∫ (θ - m)(θ - m)ᵀ dπ'`, and the
  disintegration `bayes_step`.
* (L3) `pay_tail`, (L4) `pay_inner`, (L5) `pay_outer`: the per-cell bounds in the shapes `cells_leak`
  (CellsRound.lean) consumes, in the frame of `π`.
* (L6) `ledger_game`: `∑_{t < n} E P'_t ≤ (d/2) ln(1 + r₀²/(d w²))`, `P'_t` the payment of the announced cells
  (`payAnn`, `0` on a round whose answer is constant `none`), for any genie rule with answers in `Option Cell`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal NNReal

namespace AdversarialBco.Lower

open Bayes

/-! ## Definitions -/

/-- `ψ(u) = u - 1 - ln u`. -/
noncomputable def psiF (u : ℝ) : ℝ := u - 1 - Real.log u

/-- `Σ_i ψ(u_i)` for the eigenvalues `u_i` of `W^{-1/2} U W^{-1/2}`: `tr(W⁻¹U) - d - ln det U + ln det W`. -/
noncomputable def psiSum {d : ℕ} (W U : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  trace (W⁻¹ * U) - d - Real.log (det U) + Real.log (det W)

variable {d : ℕ}

/-- `Λ(π) = (1/2) ln det(Σ(π) + w² I)`. -/
noncomputable def lam (w : ℝ) (π : Measure (E d)) : ℝ := Real.log (det (frameW w (covM π))) / 2

/-- `U_c = S_c + w² I`, `S_c = π(c)⁻¹ ∫_c (θ - m)(θ - m)ᵀ dπ`, `m` the mean of `π`. -/
noncomputable def cellU (w : ℝ) (π : Measure (E d)) (c : Set (E d)) : Matrix (Fin d) (Fin d) ℝ :=
  (π.real c)⁻¹ • secMom (π.restrict c) (meanV π) + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The payment of the cell `c`: `(1/2) π(c) Σ_i ψ(u_{c,i})`. -/
noncomputable def cellPay (w : ℝ) (π : Measure (E d)) (c : Set (E d)) : ℝ :=
  π.real c * psiSum (frameW w (covM π)) (cellU w π c) / 2

/-- The payment `P'` of the announced cells for an answer map with values in `Option Cell` (`none` is rest). -/
noncomputable def payAnn (w : ℝ) (π : Measure (E d)) (ans : E d → Option Cell) : ℝ :=
  ∑ c : Cell, cellPay w π (ans ⁻¹' {some c})

/-- The ledger's budget at the floor `w`, for the prior on `r₀ B^d`: `(d/2) ln(1 + r₀²/(d w²))`. -/
noncomputable def ledgerBudget (d : ℕ) (r₀ w : ℝ) : ℝ := d / 2 * Real.log (1 + r₀ ^ 2 / (d * w ^ 2))

/-! ## The scalar `ψ` -/

theorem psiF_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ psiF u := by
  rw [psiF]
  have h := Real.log_le_sub_one_of_pos hu
  linarith

theorem psiF_monotoneOn : MonotoneOn psiF (Set.Ici 1) := by
  intro u hu v hv huv
  have hu_pos : 0 < u := by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hv_pos : 0 < v := by
    have : (1 : ℝ) ≤ u := hu
    linarith
  have hdiv_pos : 0 < v / u := div_pos hv_pos hu_pos
  have hlog : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos hdiv_pos
  have h_sub_le : v / u - 1 ≤ v - u := by
    have h_vu_nonneg : 0 ≤ v - u := by linarith
    have h_mul : v - u ≤ u * (v - u) := by
      have hu1 : (1 : ℝ) ≤ u := hu
      nlinarith
    calc
      v / u - 1 = (v - u) / u := by field_simp [hu_pos.ne.symm]
      _ ≤ v - u := by
        field_simp [hu_pos.ne.symm]
        nlinarith
  have hlog_le : Real.log (v / u) ≤ v - u := by linarith
  dsimp [psiF]
  have h_log_div : Real.log (v / u) = Real.log v - Real.log u :=
    Real.log_div (ne_of_gt hv_pos) (ne_of_gt hu_pos)
  rw [h_log_div] at hlog_le
  linarith

theorem psiF_antitoneOn : AntitoneOn psiF (Set.Ioc 0 1) := by
  intro u hu v hv huv
  dsimp [psiF]
  have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).left
  have hv_pos : 0 < v := (Set.mem_Ioc.mp hv).left
  have hv_le_one : v ≤ 1 := (Set.mem_Ioc.mp hv).right
  have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
  have hx_pos : 0 < v / u := div_pos hv_pos hu_pos
  have h_log_ineq : 1 - u / v ≤ Real.log (v / u) := by
    have h := Real.one_sub_inv_le_log_of_pos hx_pos
    simpa [div_div] using h
  have h_sub_ineq : v - u ≤ 1 - u / v := by
    have h_one_div_v_ge_one : 1 ≤ 1 / v := one_le_one_div hv_pos hv_le_one
    calc
      v - u = (v - u) * 1 := by ring
      _ ≤ (v - u) * (1 / v) := mul_le_mul_of_nonneg_left h_one_div_v_ge_one hvu
      _ = (v - u) / v := by ring
      _ = 1 - u / v := by field_simp [hv_pos.ne.symm]
  have h_main : v - u ≤ Real.log (v / u) := le_trans h_sub_ineq h_log_ineq
  have hlog : Real.log (v / u) = Real.log v - Real.log u := Real.log_div hv_pos.ne.symm hu_pos.ne.symm
  rw [hlog] at h_main
  linarith

/-- `ψ(u) ≥ u/2` for `u ≥ 6`. -/
theorem psiF_ge_half {u : ℝ} (hu : 6 ≤ u) : u / 2 ≤ psiF u := by
  have h6pos : 0 < (6 : ℝ) := by norm_num
  have hu_pos : 0 < u := by linarith
  have hu6_pos : 0 < u / 6 := by nlinarith
  have h6_nonzero : (6 : ℝ) ≠ 0 := by norm_num
  have hu6_nonzero : u / 6 ≠ 0 := by nlinarith
  have h_log6_le_2 : Real.log (6 : ℝ) ≤ 2 := by
    have h_exp2_ge_6 : (6 : ℝ) ≤ Real.exp 2 := by
      have htemp : (6 : ℝ) < Real.exp 2 := by
        calc
          (6 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
          _ < (Real.exp 1) ^ 2 := by
            nlinarith [Real.exp_one_gt_d9]
          _ = Real.exp 1 * Real.exp 1 := by ring
          _ = Real.exp (1 + 1) := by rw [Real.exp_add]
          _ = Real.exp 2 := by norm_num
      exact htemp.le
    calc
      Real.log (6 : ℝ) ≤ Real.log (Real.exp 2) := Real.log_le_log h6pos h_exp2_ge_6
      _ = 2 := Real.log_exp 2
  have h_log_u_div_6 : Real.log (u / 6) ≤ u / 6 - 1 :=
    Real.log_le_sub_one_of_pos hu6_pos
  have h_log_u : Real.log u ≤ u / 2 - 1 := by
    calc
      Real.log u = Real.log (6 * (u / 6)) := by field_simp
      _ = Real.log (6 : ℝ) + Real.log (u / 6) :=
        Real.log_mul h6_nonzero hu6_nonzero
      _ ≤ 2 + (u / 6 - 1) := by nlinarith
      _ = u / 6 + 1 := by ring
      _ ≤ u / 2 - 1 := by nlinarith
  dsimp [psiF]
  nlinarith

/-- `ψ(49/64) ≥ 1/31` (it is `0.03269`). -/
theorem psiF_inner : 1 / 31 ≤ psiF (49 / 64) := by
  have hlog49 : Real.log (49 : ℝ) = 2 * Real.log 7 := by
    calc
      Real.log (49 : ℝ) = Real.log ((7:ℝ)^2) := by norm_num
      _ = 2 * Real.log 7 := by rw [Real.log_pow, Nat.cast_ofNat]
  have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    calc
      Real.log (64 : ℝ) = Real.log ((2:ℝ)^6) := by norm_num
      _ = 6 * Real.log 2 := by rw [Real.log_pow, Nat.cast_ofNat]
  have hlog49_64 : Real.log (49/64) = 2 * Real.log 7 - 6 * Real.log 2 := by
    calc
      Real.log (49/64) = Real.log 49 - Real.log 64 :=
        Real.log_div (by norm_num : (49 : ℝ) ≠ 0) (by norm_num : (64 : ℝ) ≠ 0)
      _ = (2 * Real.log 7) - (6 * Real.log 2) := by rw [hlog49, hlog64]
      _ = 2 * Real.log 7 - 6 * Real.log 2 := rfl
  have hpsi_eq : psiF (49/64) = -(15/64 : ℝ) + Real.log (64/49) := by
    dsimp [psiF]
    rw [hlog49_64]
    have hlog64_49 : Real.log (64/49) = 6 * Real.log 2 - 2 * Real.log 7 := by
      calc
        Real.log (64/49) = Real.log 64 - Real.log 49 :=
          Real.log_div (by norm_num : (64 : ℝ) ≠ 0) (by norm_num : (49 : ℝ) ≠ 0)
        _ = (6 * Real.log 2) - (2 * Real.log 7) := by rw [hlog64, hlog49]
        _ = 6 * Real.log 2 - 2 * Real.log 7 := rfl
    rw [hlog64_49]
    ring_nf
  rw [hpsi_eq]
  have hlog_bound : (2 : ℝ)/15 ≤ Real.log (8/7) := by
    have hx : 0 ≤ (1 : ℝ)/7 := by norm_num
    have h := Real.le_log_one_add_of_nonneg hx
    have hcalc : 2 * ((1 : ℝ)/7) / (((1 : ℝ)/7) + 2) = (2 : ℝ)/15 := by ring
    have hone : (1 : ℝ) + (1 : ℝ)/7 = (8 : ℝ)/7 := by ring
    rw [hcalc, hone] at h
    exact h
  have hlog64_49_bound : (4 : ℝ)/15 ≤ Real.log (64/49) := by
    have h : Real.log (64/49) = 2 * Real.log (8/7) := by
      calc
        Real.log (64/49) = Real.log (((8:ℝ)/7)^2) := by norm_num
        _ = 2 * Real.log (8/7) := by rw [Real.log_pow, Nat.cast_ofNat]
    rw [h]
    nlinarith
  have hrational : (1 : ℝ)/31 ≤ -(15/64 : ℝ) + (4/15 : ℝ) := by
    nlinarith
  nlinarith

/-- `ψ(2) ≥ 1/31` (it is `0.3069`). -/
theorem psiF_two : 1 / 31 ≤ psiF 2 := by
  have hlog : Real.log 2 < 30/31 := by
    have h := Real.log_two_lt_d9
    have h' : (0.6931471808 : ℝ) ≤ 30/31 := by norm_num
    linarith
  have hpsi : psiF 2 = 1 - Real.log 2 := by
    unfold psiF
    ring
  rw [hpsi]
  linarith

/-! ## Matrix inequalities, route (S4) -/

/-- `ln det X ≤ tr X - d` for `X` positive definite. -/
theorem logdet_le_trace_sub (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.PosDef) :
    Real.log (det X) ≤ trace X - d := by
  have h_herm : X.IsHermitian := hX.isHermitian
  have h_pos : ∀ i : Fin d, 0 < h_herm.eigenvalues i := hX.eigenvalues_pos
  have h_det : det X = ∏ i : Fin d, (h_herm.eigenvalues i : ℝ) := h_herm.det_eq_prod_eigenvalues
  have h_trace : trace X = ∑ i : Fin d, (h_herm.eigenvalues i : ℝ) := h_herm.trace_eq_sum_eigenvalues
  rw [h_det, h_trace]
  calc
    Real.log (∏ i : Fin d, (h_herm.eigenvalues i : ℝ))
        = ∑ i : Fin d, Real.log (h_herm.eigenvalues i : ℝ) := by
      rw [Real.log_prod]
      intro i hi
      have h := h_pos i
      linarith
    _ ≤ ∑ i : Fin d, ((h_herm.eigenvalues i : ℝ) - 1) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact Real.log_le_sub_one_of_pos (h_pos i)
    _ = (∑ i : Fin d, (h_herm.eigenvalues i : ℝ)) - (∑ i : Fin d, (1 : ℝ)) := by
      simp [Finset.sum_sub_distrib]
    _ = (∑ i : Fin d, (h_herm.eigenvalues i : ℝ)) - (d : ℝ) := by simp

/-- (S4): `ln det X ≤ ln det U + tr(U⁻¹X) - d` for `U, X` positive definite. -/
theorem logdet_le_logdet_add_trace (U X : Matrix (Fin d) (Fin d) ℝ) (hU : U.PosDef) (hX : X.PosDef) :
    Real.log (det X) ≤ Real.log (det U) + trace (U⁻¹ * X) - d := by
  set R := CFC.sqrt (U⁻¹) with hR_def
  have hUinv_posDef : (U⁻¹).PosDef := hU.inv
  have hUinv_nonneg : 0 ≤ (U⁻¹ : Matrix (Fin d) (Fin d) ℝ) :=
    hUinv_posDef.posSemidef.nonneg
  have hR_posDef : R.PosDef :=
    (IsStrictlyPositive.sqrt (U⁻¹) (hUinv_posDef.isStrictlyPositive)).posDef
  have hR_sqrt : R * R = U⁻¹ := by
    rw [hR_def]
    exact CFC.sqrt_mul_sqrt_self (U⁻¹) (ha := hUinv_nonneg)
  have hR_herm : R.IsHermitian := hR_posDef.isHermitian
  have hX_herm : X.IsHermitian := hX.isHermitian
  have hR_conj_eq : R.conjTranspose = R := hR_herm.eq
  have hR_inj : Function.Injective R.mulVec :=
    Matrix.mulVec_injective_of_isUnit (hR_posDef.isUnit)
  have hY_posDef : (R * X * R).PosDef := by
    have h := hX.conjTranspose_mul_mul_same hR_inj
    rw [hR_conj_eq] at h
    exact h
  have h_det_pos_U : 0 < det U := hU.det_pos
  have h_det_pos_X : 0 < det X := hX.det_pos
  have h_det_Y : det (R * X * R) = det X / det U := by
    calc
      det (R * X * R) = det (R * X) * det R := by rw [Matrix.det_mul]
      _ = (det R * det X) * det R := by rw [Matrix.det_mul]
      _ = (det R * det R) * det X := by ring
      _ = det (R * R) * det X := by rw [Matrix.det_mul]
      _ = det (U⁻¹) * det X := by rw [hR_sqrt]
      _ = ((det U)⁻¹) * det X := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      _ = det X / det U := by rw [div_eq_mul_inv, mul_comm]
  have h_trace_Y : trace (R * X * R) = trace (U⁻¹ * X) := by
    calc
      trace (R * X * R) = trace (R * R * X) := by
        rw [Matrix.trace_mul_cycle R X R]
      _ = trace (U⁻¹ * X) := by rw [hR_sqrt]
  have h_log_det_Y : Real.log (det (R * X * R)) = Real.log (det X) - Real.log (det U) := by
    rw [h_det_Y]
    rw [Real.log_div (ne_of_gt h_det_pos_X) (ne_of_gt h_det_pos_U)]
  have h_logdet_le := logdet_le_trace_sub (R * X * R) hY_posDef
  rw [h_log_det_Y, h_trace_Y] at h_logdet_le
  linarith

theorem psiSum_nonneg (W U : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosDef) (hU : U.PosDef) : 0 ≤ psiSum W U := by
  have h := logdet_le_logdet_add_trace W U hW hU
  dsimp [psiSum]
  linarith

/-- Convexity of `ψ` over the eigenvalues: `Σ_i ψ(u_i) ≥ d ψ(mean of the u_i)`. -/
theorem psiSum_ge_mean (W U : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosDef) (hU : U.PosDef) (hd : 0 < d) :
    d * psiF (trace (W⁻¹ * U) / d) ≤ psiSum W U := by
  set τ := trace (W⁻¹ * U) with hτ
  set c := τ / d with hc
  have hτ_pos : 0 < τ := by
    have hWinv_nonneg : 0 ≤ (W⁻¹ : Matrix (Fin d) (Fin d) ℝ) := hW.inv.posSemidef.nonneg
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hWinv_nonneg
    -- hR : W⁻¹ = star R * R
    have hWinv_unit : IsUnit (W⁻¹ : Matrix (Fin d) (Fin d) ℝ) := hW.inv.isUnit
    have hdetWinv_ne_zero : det (W⁻¹ : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := by
      have h := hWinv_unit.map (Matrix.detMonoidHom (n := Fin d) (R := ℝ))
      exact h.ne_zero
    have hdet_star_mul_det : det (star R * R) = det (star R) * det R := Matrix.det_mul _ _
    have hdet_star : det (star R) = det R := by
      simp [Matrix.star_eq_conjTranspose]
    have hdetR_sq_ne_zero : det R * det R ≠ 0 := by
      have h : det (star R * R) = det R * det R := by
        rw [hdet_star_mul_det, hdet_star]
      rw [← h, ← hR]
      exact hdetWinv_ne_zero
    have hdetR_ne_zero : det R ≠ 0 := by
      intro hzero
      apply hdetR_sq_ne_zero
      rw [hzero, zero_mul]
    have hR_unit : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).mpr (isUnit_iff_ne_zero.mpr hdetR_ne_zero)
    have h_pos : 0 < trace (R * U * star R) := by
      have h_pos_def : (R * U * star R).PosDef := by
        rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hR_unit]
        exact hU
      have h_nonempty : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      exact Matrix.PosDef.trace_pos h_pos_def
    -- Now relate trace(W⁻¹ * U) to trace(R * U * star R)
    have h_trace_eq : trace (W⁻¹ * U) = trace (R * U * star R) := by
      rw [hR]
      calc
        trace ((star R * R) * U) = trace (star R * (R * U)) := by rw [Matrix.mul_assoc]
        _ = trace ((R * U) * star R) := by rw [Matrix.trace_mul_comm]
        _ = trace (R * U * star R) := by rw [Matrix.mul_assoc]
    rw [hτ, h_trace_eq]
    exact h_pos
  have hc_pos : 0 < c := div_pos hτ_pos (by exact_mod_cast hd)
  have hU_cW : (c • W).PosDef := hW.smul hc_pos
  have h := logdet_le_logdet_add_trace (c • W) U hU_cW hU
  -- h : Real.log (det U) ≤ Real.log (det (c • W)) + trace ((c • W)⁻¹ * U) - d
  have h_det_smul : det (c • W) = c ^ d * det W := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have h_log_det_smul : Real.log (det (c • W)) = (d : ℝ) * Real.log c + Real.log (det W) := by
    rw [h_det_smul]
    have hc_ne_zero : c ≠ 0 := by linarith
    have hdetW_ne_zero : det W ≠ 0 := by
      have hW_unit : IsUnit W := hW.isUnit
      exact (Matrix.isUnit_iff_isUnit_det W).mp hW_unit |>.ne_zero
    rw [Real.log_mul (by exact pow_ne_zero d hc_ne_zero) hdetW_ne_zero, Real.log_pow]
  have hW_det_unit : IsUnit (det W) := (Matrix.isUnit_iff_isUnit_det W).mp hW.isUnit
  have hc_inv : Invertible (c : ℝ) := invertibleOfNonzero (hc_pos.ne')
  have h_inv_smul : (c • W)⁻¹ = (c⁻¹ : ℝ) • (W⁻¹ : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Matrix.inv_smul W (c : ℝ) hW_det_unit, invOf_eq_inv (c : ℝ)]
  have hd_ne_zero : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h_trace_inv_smul : trace ((c • W)⁻¹ * U) = (d : ℝ) := by
    rw [h_inv_smul]
    -- trace ((c⁻¹ • W⁻¹) * U) = c⁻¹ * trace (W⁻¹ * U)
    rw [smul_mul_assoc, Matrix.trace_smul, ← hτ]
    -- Now: c⁻¹ * τ = d
    -- Since c = τ / d, we have τ = c * d
    have hτ_eq : τ = c * (d : ℝ) := by
      rw [hc]
      field_simp [hd_ne_zero]
    rw [hτ_eq]
    -- Goal: c⁻¹ * (c * (d : ℝ)) = (d : ℝ)
    -- i.e., (c⁻¹ * c) * (d : ℝ) = (d : ℝ)
    -- i.e., 1 * (d : ℝ) = (d : ℝ)
    -- Goal: c⁻¹ • (c * ↑d) = ↑d
    -- In ℝ, • is the same as *
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc_pos.ne', one_mul]
  -- Now use the inequality from logdet_le_logdet_add_trace
  have h_ineq : Real.log (det U) ≤ (d : ℝ) * Real.log c + Real.log (det W) := by
    -- From h: Real.log (det U) ≤ Real.log (det (c • W)) + trace ((c • W)⁻¹ * U) - d
    -- Substitute h_log_det_smul and h_trace_inv_smul
    rw [h_log_det_smul, h_trace_inv_smul] at h
    -- h: Real.log (det U) ≤ ((d : ℝ) * Real.log c + Real.log (det W)) + (d : ℝ) - (d : ℝ)
    -- Simplify: ((d : ℝ) * Real.log c + Real.log (det W)) + (d : ℝ) - (d : ℝ) = (d : ℝ) * Real.log c + Real.log (det W)
    linarith
  -- Now expand psiF and psiSum and use h_ineq
  dsimp [psiF, psiSum]
  -- Goal: d * ((trace (W⁻¹ * U) / d) - 1 - Real.log (trace (W⁻¹ * U) / d)) ≤
  --       trace (W⁻¹ * U) - d - Real.log (det U) + Real.log (det W)
  rw [← hτ]
  -- Goal: d * (c - 1 - Real.log c) ≤ τ - d - Real.log (det U) + Real.log (det W)
  -- (c is definitionally τ / d, so the goal already has c in place of τ / d)
  -- But τ = c * d
  have hτ_eq : τ = c * (d : ℝ) := by
    rw [hc]
    field_simp [hd_ne_zero]
  rw [hτ_eq]
  -- Goal: d * (c - 1 - Real.log c) ≤ c * d - d - Real.log (det U) + Real.log (det W)
  -- LHS: d * (c - 1 - Real.log c) = d*c - d - d*Real.log c
  -- RHS: c*d - d - Real.log (det U) + Real.log (det W)
  -- Using h_ineq: Real.log (det U) ≤ d*Real.log c + Real.log (det W)
  -- So -Real.log (det U) ≥ -d*Real.log c - Real.log (det W)
  -- RHS ≥ c*d - d - d*Real.log c - Real.log (det W) + Real.log (det W) = c*d - d - d*Real.log c = LHS
  nlinarith

/-- Cauchy-Schwarz for a positive semidefinite form: `(zᵀ W x)² ≤ (zᵀ W z)(xᵀ W x)`. -/
theorem sq_dot_mulVec_le (W : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosSemidef) (z x : Fin d → ℝ) :
    (z ⬝ᵥ (W *ᵥ x)) ^ 2 ≤ (z ⬝ᵥ (W *ᵥ z)) * (x ⬝ᵥ (W *ᵥ x)) := by
  have hT : Wᵀ = W := by
    have := hW.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : x ⬝ᵥ (W *ᵥ z) = z ⬝ᵥ (W *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have hq : ∀ t : ℝ, 0 ≤ z ⬝ᵥ (W *ᵥ z) + 2 * t * (z ⬝ᵥ (W *ᵥ x)) + t ^ 2 * (x ⬝ᵥ (W *ᵥ x)) := by
    intro t
    have h := hW.dotProduct_mulVec_nonneg (z + t • x)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym] at h
    nlinarith [h]
  have hC : 0 ≤ x ⬝ᵥ (W *ᵥ x) := by simpa using hW.dotProduct_mulVec_nonneg x
  obtain ⟨A, hA⟩ : ∃ A, A = z ⬝ᵥ (W *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = z ⬝ᵥ (W *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = x ⬝ᵥ (W *ᵥ x) := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hCd] at hq ⊢
  rw [← hCd] at hC
  rcases hC.lt_or_eq with hCpos | hC0
  · have h1 := hq (-B / C)
    have key : C * (A + 2 * (-B / C) * B + (-B / C) ^ 2 * C) = A * C - B ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hCpos.le h1]
  · rw [← hC0] at hq ⊢
    by_contra hneg
    have hB0 : B ≠ 0 := by
      rintro rfl
      simp at hneg
    have h1 := hq (-(A + 1) / (2 * B))
    have key : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
      field_simp
      ring
    linarith

/-- Matrix determinant lemma for the rank-one update along `W z`. -/
theorem quot_det (W : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) (k : ℝ) :
    det (W + k • vecMulVec (W *ᵥ z) (W *ᵥ z)) = det W * (1 + k * (z ⬝ᵥ (W *ᵥ z))) := by
  have h : W + k • vecMulVec (W *ᵥ z) (W *ᵥ z) = W * (1 + vecMulVec (k • z) (W *ᵥ z)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_smul]
    congr 1
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
  rw [h, Matrix.det_mul, Matrix.vecMulVec_eq (ι := Unit), Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul, dotProduct_comm]

/-- Sherman-Morrison for the comparison matrix `V = W + ((q - 1)/b) (W z)(W z)ᵀ`, `b = zᵀ W z`. -/
theorem quot_inv (W : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosDef) (z : Fin d → ℝ) {b q : ℝ}
    (hb : b = z ⬝ᵥ (W *ᵥ z)) (hb0 : 0 < b) (hq : 0 < q) :
    (W + ((q - 1) / b) • vecMulVec (W *ᵥ z) (W *ᵥ z))⁻¹ = W⁻¹ - ((q - 1) / (q * b)) • vecMulVec z z := by
  have hT : Wᵀ = W := by
    have := hW.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hU : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW.isUnit
  have hyW : (W *ᵥ z) ᵥ* W⁻¹ = z := by
    rw [← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv, hT, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  have hyz : (W *ᵥ z) ⬝ᵥ z = b := by rw [dotProduct_comm, hb]
  obtain ⟨k, hk⟩ : ∃ k, k = (q - 1) / b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (q - 1) / (q * b) := ⟨_, rfl⟩
  rw [← hk, ← hc]
  have hcoef : -c + k - k * (c * b) = 0 := by
    rw [hk, hc]
    field_simp
    ring
  have h1 : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have h2 : W * vecMulVec z z = vecMulVec (W *ᵥ z) z := Matrix.mul_vecMulVec _ _ _
  have h3 : vecMulVec (W *ᵥ z) (W *ᵥ z) * W⁻¹ = vecMulVec (W *ᵥ z) z := by
    rw [Matrix.vecMulVec_mul, hyW]
  have h4 : vecMulVec (W *ᵥ z) (W *ᵥ z) * vecMulVec z z = b • vecMulVec (W *ᵥ z) z := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hyz]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  apply Matrix.inv_eq_right_inv
  have key : (W + k • vecMulVec (W *ᵥ z) (W *ᵥ z)) * (W⁻¹ - c • vecMulVec z z) =
      1 + (-c + k - k * (c * b)) • vecMulVec (W *ᵥ z) z := by
    simp only [Matrix.add_mul, Matrix.mul_sub, h1, Matrix.mul_smul, Matrix.smul_mul, h2, h3, h4]
    module
  rw [key, hcoef, zero_smul, add_zero]

/-- The trace against a rank-one correction: `tr((A - c z zᵀ) U) = tr(A U) - c zᵀ U z`. -/
theorem trace_sub_vecMulVec_mul (A U : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) (c : ℝ) :
    trace ((A - c • vecMulVec z z) * U) = trace (A * U) - c * (z ⬝ᵥ (U *ᵥ z)) := by
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The comparison matrix `V = W + ((q - 1)/b) (W z)(W z)ᵀ` is positive definite for `q > 0`. -/
theorem quot_posDef (W : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosDef) (z : Fin d → ℝ) {b q : ℝ}
    (hb : b = z ⬝ᵥ (W *ᵥ z)) (hb0 : 0 < b) (hq : 0 < q) :
    (W + ((q - 1) / b) • vecMulVec (W *ᵥ z) (W *ᵥ z)).PosDef := by
  have hT : Wᵀ = W := by
    have := hW.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_vecMulVec, hT]
  have hvv : ∀ y : Fin d → ℝ, x ⬝ᵥ (vecMulVec y y *ᵥ x) = (y ⬝ᵥ x) ^ 2 := by
    intro y
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hyx : (W *ᵥ z) ⬝ᵥ x = z ⬝ᵥ (W *ᵥ x) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have hC : 0 < x ⬝ᵥ (W *ᵥ x) := by simpa using hW.dotProduct_mulVec_pos hx
  have hCS := sq_dot_mulVec_le W hW.posSemidef z x
  rw [← hb] at hCS
  simp only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    hvv, hyx]
  obtain ⟨B, hB⟩ : ∃ B, B = z ⬝ᵥ (W *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = x ⬝ᵥ (W *ᵥ x) := ⟨_, rfl⟩
  rw [← hB, ← hCd] at hCS ⊢
  rw [← hCd] at hC
  rcases le_or_gt 1 q with h1 | h1
  · have : 0 ≤ (q - 1) / b * B ^ 2 := mul_nonneg (div_nonneg (by linarith) hb0.le) (sq_nonneg _)
    linarith
  · have hk : (q - 1) / b * (b * C) ≤ (q - 1) / b * B ^ 2 :=
      mul_le_mul_of_nonpos_left hCS (div_nonpos_of_nonpos_of_nonneg (by linarith) hb0.le)
    have h2 : (q - 1) / b * (b * C) = (q - 1) * C := by
      field_simp
    nlinarith [mul_pos hq hC]

/-- Rayleigh: `Σ_i ψ(u_i) ≥ ψ(zᵀUz / zᵀWz)` for every `z ≠ 0`. -/
theorem psiSum_ge_quot (W U : Matrix (Fin d) (Fin d) ℝ) (hW : W.PosDef) (hU : U.PosDef) (z : Fin d → ℝ)
    (hz : z ≠ 0) : psiF ((z ⬝ᵥ (U *ᵥ z)) / (z ⬝ᵥ (W *ᵥ z))) ≤ psiSum W U := by
  obtain ⟨a, ha⟩ : ∃ a, a = z ⬝ᵥ (U *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = z ⬝ᵥ (W *ᵥ z) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha0 : 0 < a := by rw [ha]; simpa using hU.dotProduct_mulVec_pos hz
  have hb0 : 0 < b := by rw [hb]; simpa using hW.dotProduct_mulVec_pos hz
  obtain ⟨q, hq⟩ : ∃ q, q = a / b := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 < q := by rw [hq]; exact div_pos ha0 hb0
  have haq : a = q * b := by rw [hq, div_mul_cancel₀ _ hb0.ne']
  have hV := quot_posDef W hW z hb hb0 hq0
  have hlog := logdet_le_logdet_add_trace _ U hV hU
  rw [quot_det W z, quot_inv W hW z hb hb0 hq0, trace_sub_vecMulVec_mul, ← ha, ← hb] at hlog
  have h1 : 1 + (q - 1) / b * b = q := by rw [div_mul_cancel₀ _ hb0.ne']; ring
  rw [h1, Real.log_mul hW.det_pos.ne' hq0.ne'] at hlog
  have h2 : (q - 1) / (q * b) * a = q - 1 := by rw [haq, div_mul_cancel₀ _ (mul_ne_zero hq0.ne' hb0.ne')]
  rw [h2] at hlog
  unfold psiSum psiF
  linarith

/-- AM-GM on the eigenvalues: `ln det X ≤ d ln(tr X / d)` for `X` positive definite. -/
theorem logdet_le_card_log_trace (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.PosDef) (hd : 0 < d) :
    Real.log (det X) ≤ d * Real.log (trace X / d) := by
  haveI : Nonempty (Fin d) := by
    refine ⟨⟨0, hd⟩⟩
  set c := trace X / d with hc_def
  have htrace_pos : 0 < trace X := hX.trace_pos
  have hc_pos : 0 < c := by
    exact div_pos htrace_pos (by exact_mod_cast hd)
  have h_one_posDef : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef :=
    Matrix.PosDef.one
  have hU_posDef : (c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    h_one_posDef.smul hc_pos
  have hineq := logdet_le_logdet_add_trace (c • (1 : Matrix (Fin d) (Fin d) ℝ)) X hU_posDef hX
  have hdet_smul : det (c • (1 : Matrix (Fin d) (Fin d) ℝ)) = c ^ d := by
    calc
      det (c • (1 : Matrix (Fin d) (Fin d) ℝ)) = c ^ (Fintype.card (Fin d)) * det (1 : Matrix (Fin d) (Fin d) ℝ) := by
        rw [Matrix.det_smul]
      _ = c ^ d * 1 := by simp
      _ = c ^ d := by simp
  have htrace_inv_mul : trace ((c • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * X) = trace X / c := by
    haveI : Invertible c := invertibleOfNonzero hc_pos.ne.symm
    have h_det_one_unit : IsUnit (det (1 : Matrix (Fin d) (Fin d) ℝ)) := by
      rw [Matrix.det_one]
      exact isUnit_one
    have h_inv : (c • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = c⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      calc
        (c • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = ⅟c • (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ :=
          Matrix.inv_smul (1 : Matrix (Fin d) (Fin d) ℝ) c h_det_one_unit
        _ = c⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ := by simp
        _ = c⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by simp
    calc
      trace ((c • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * X) = trace ((c⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) * X) := by
        rw [h_inv]
      _ = trace (c⁻¹ • X) := by simp
      _ = c⁻¹ • trace X := by rw [Matrix.trace_smul]
      _ = c⁻¹ * trace X := by rw [smul_eq_mul]
      _ = trace X / c := by ring
  have hlog_det_smul : Real.log (det (c • (1 : Matrix (Fin d) (Fin d) ℝ))) = d * Real.log c := by
    rw [hdet_smul, Real.log_pow]
  rw [hlog_det_smul, htrace_inv_mul] at hineq
  have h_trace_div_c : trace X / c = d := by
    rw [hc_def]
    field_simp [ne_of_gt hd, htrace_pos.ne.symm]
  rw [h_trace_div_c] at hineq
  have h_simp : d * Real.log c + d - d = d * Real.log c := by ring
  rw [h_simp] at hineq
  rw [hc_def] at hineq
  exact hineq

/-- `ln det(S + w² I) ≥ d ln w²` for `S` positive semidefinite. -/
theorem logdet_frameW_ge (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) {w : ℝ} (hw : w ≠ 0) :
    d * Real.log (w ^ 2) ≤ Real.log (det (frameW w S)) := by
  have hS_herm : S.IsHermitian := hS.isHermitian
  have h_eigen_nonneg : ∀ i, 0 ≤ hS_herm.eigenvalues i := hS.eigenvalues_nonneg
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have h_card : Fintype.card (Fin d) = d := by simp
  -- frameW w S is Hermitian
  have h_frame_herm : (frameW w S).IsHermitian := by
    unfold frameW
    have h_one : (1 : Matrix (Fin d) (Fin d) ℝ).IsHermitian := Matrix.isHermitian_one
    have h_smul : ((w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian :=
      h_one.smul (by rw [isSelfAdjoint_iff]; simp : IsSelfAdjoint (w ^ 2))
    exact hS_herm.add h_smul
  -- det(frameW w S) = ∏ eigenvalues_i
  have h_det_eq : det (frameW w S) = ∏ i : Fin d, (h_frame_herm.eigenvalues i : ℝ) :=
    h_frame_herm.det_eq_prod_eigenvalues
  -- spectral theorem: S = U * D * Uᴴ
  have hspec := hS_herm.spectral_theorem
  set U := hS_herm.eigenvectorUnitary with hU
  set D := diagonal ((RCLike.ofReal : ℝ → ℝ) ∘ hS_herm.eigenvalues) with hD
  have hS_eq : S = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) U) D := hspec
  have h_conj_apply : ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) U) D = (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Unitary.conjStarAlgAut_apply]
  have hS_eq' : S = (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hS_eq, h_conj_apply]
  -- U is unitary, so U * star U = 1 and star U * U = 1
  have hU_unitary : IsUnit (U : Matrix (Fin d) (Fin d) ℝ) := by
    have h_mem : (U : Matrix (Fin d) (Fin d) ℝ) ∈ unitaryGroup (Fin d) ℝ := U.property
    rcases h_mem with ⟨h1, h2⟩
    refine ⟨⟨U, star U, ?_, ?_⟩, rfl⟩
    · simpa using h1
    · simpa using h2
  have h_star_eq_inv : star (U : Matrix (Fin d) (Fin d) ℝ) = (U : Matrix (Fin d) (Fin d) ℝ)⁻¹ := by
    have h_mem : (U : Matrix (Fin d) (Fin d) ℝ) ∈ unitaryGroup (Fin d) ℝ := U.property
    rcases h_mem with ⟨h1, h2⟩
    rw [eq_comm, ← Matrix.inv_eq_left_inv h1]
  -- identity: U * D * Uᴴ + w² • I = U * (D + w² • I) * Uᴴ
  have h_frame_eq : frameW w S = (U : Matrix (Fin d) (Fin d) ℝ) * (D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    unfold frameW
    rw [hS_eq']
    have h_unit : (U : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ) = 1 := by
      have h_mem : (U : Matrix (Fin d) (Fin d) ℝ) ∈ unitaryGroup (Fin d) ℝ := U.property
      rcases h_mem with ⟨h1, h2⟩
      exact h2
    calc
      (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
          = (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) + (w ^ 2) • ((U : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ)) := by
        simp [h_unit]
      _ = (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) + (w ^ 2) • ((U : Matrix (Fin d) (Fin d) ℝ) * (1 : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ)) := by
        simp
      _ = (U : Matrix (Fin d) (Fin d) ℝ) * (D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) * star (U : Matrix (Fin d) (Fin d) ℝ) := by
        simp [mul_add, add_mul]
  -- det(frameW w S) = det(D + w² • I)
  have h_det_frame : det (frameW w S) = det (D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    rw [h_frame_eq]
    rw [h_star_eq_inv]
    rw [Matrix.det_conj hU_unitary (D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))]
  -- D is diagonal with entries λ_i
  have hD_diag : D = diagonal fun i : Fin d => (hS_herm.eigenvalues i : ℝ) := by
    ext i j
    simp [D, diagonal]
  -- D + w² • I = diagonal (λ_i + w²)
  have hD_add : D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) = diagonal fun i : Fin d => (hS_herm.eigenvalues i : ℝ) + w ^ 2 := by
    rw [hD_diag]
    ext i j
    simp [diagonal, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  -- det(D + w² • I) = ∏ (λ_i + w²)
  have h_det_diag : det (D + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) = ∏ i : Fin d, ((hS_herm.eigenvalues i : ℝ) + w ^ 2) := by
    rw [hD_add, Matrix.det_diagonal]
  -- Now relate to eigenvalues of frameW
  -- We know det(frameW w S) = ∏ eigenvalues_i(frameW w S)
  -- But we also have det(frameW w S) = ∏ (λ_i + w²)
  -- So we need to show that eigenvalues_i(frameW w S) = λ_i + w²
  -- Actually, we don't need this equality! We just need:
  -- ∏ (λ_i + w²) ≥ (w²)^d
  -- and then take logs.
  -- Each λ_i ≥ 0, w² > 0, so λ_i + w² ≥ w²
  have h_sum_ge : ∀ i, w ^ 2 ≤ (hS_herm.eigenvalues i : ℝ) + w ^ 2 := by
    intro i
    nlinarith [h_eigen_nonneg i]
  -- Product inequality
  have h_prod_ge : (∏ i : Fin d, (w ^ 2 : ℝ)) ≤ ∏ i : Fin d, ((hS_herm.eigenvalues i : ℝ) + w ^ 2) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro i hi
      have : 0 ≤ (w ^ 2 : ℝ) := by linarith
      exact this
    · intro i hi
      exact h_sum_ge i
  -- (w²)^d = ∏ (w²)
  have h_prod_const : (∏ i : Fin d, (w ^ 2 : ℝ)) = (w ^ 2) ^ d := by
    simp
  rw [h_prod_const] at h_prod_ge
  -- Now combine with det equality
  have h_det_val : det (frameW w S) = ∏ i : Fin d, ((hS_herm.eigenvalues i : ℝ) + w ^ 2) := by
    rw [h_det_frame, h_det_diag]
  rw [← h_det_val] at h_prod_ge
  -- h_prod_ge: (w ^ 2) ^ d ≤ det (frameW w S)
  -- We need: d * log(w²) ≤ log(det)
  have h_det_pos : 0 < det (frameW w S) := by
    -- Since det = ∏ (λ_i + w²) and each λ_i + w² ≥ w² > 0
    rw [h_det_val]
    refine Finset.prod_pos fun i hi => ?_
    have : 0 < (hS_herm.eigenvalues i : ℝ) + w ^ 2 := by nlinarith [h_eigen_nonneg i, hw_sq_pos]
    exact this
  have h_w_sq_pow_pos : 0 < (w ^ 2) ^ d := pow_pos hw_sq_pos d
  -- Apply log to both sides of h_prod_ge
  have h_log_ineq : Real.log ((w ^ 2) ^ d) ≤ Real.log (det (frameW w S)) :=
    Real.log_le_log h_w_sq_pow_pos h_prod_ge
  -- Real.log ((w ^ 2) ^ d) = d * Real.log (w ^ 2)
  rw [Real.log_pow] at h_log_ineq
  exact h_log_ineq

theorem frameW_posDef (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) {w : ℝ} (hw : w ≠ 0) :
    (frameW w S).PosDef := by
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_of_ne_zero hw
  have h_one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := Matrix.PosDef.one
  have h_smul : ((w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.smul h_one hw_sq_pos
  have h_add : (S + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.posSemidef_add hS h_smul
  simpa [frameW] using h_add

/-- The Loewner order read on a vector. -/
theorem dotProduct_mulVec_le_of_le {A B : Matrix (Fin d) (Fin d) ℝ} (h : A ≤ B) (v : Fin d → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v) := by
  have hpos : (B - A).PosSemidef := (Matrix.le_iff.mp h)
  have hnonneg : 0 ≤ star v ⬝ᵥ ((B - A) *ᵥ v) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hpos v
  simpa [Matrix.sub_mulVec, dotProduct_sub] using hnonneg

/-- The Loewner order read through a positive semidefinite weight: `tr(Q A) ≤ tr(Q B)`. -/
theorem trace_mul_le_of_le {Q A B : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.PosSemidef) (h : A ≤ B) :
    trace (Q * A) ≤ trace (Q * B) := by
  have hP : (B - A).PosSemidef := by rwa [Matrix.le_iff] at h
  set S := CFC.sqrt Q with hS_def
  have hS : S.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have h_sq : S * S = Q := by
    rw [hS_def, ← pow_two]
    exact CFC.sq_sqrt Q
  have h_trace_sub : trace (Q * B) - trace (Q * A) = trace (Q * (B - A)) := by
    calc
      trace (Q * B) - trace (Q * A) = trace (Q * B - Q * A) := by rw [Matrix.trace_sub]
      _ = trace (Q * (B - A)) := by rw [Matrix.mul_sub]
  have h_nonneg : 0 ≤ trace (Q * (B - A)) := by
    have hPS : PosSemidef (Sᴴ * (B - A) * S) :=
      hP.conjTranspose_mul_mul_same S
    have hPS' : PosSemidef (S * (B - A) * S) := by
      rw [hS.isHermitian.eq] at hPS
      exact hPS
    have h_eq : trace (S * (B - A) * S) = trace (Q * (B - A)) := by
      calc
        trace (S * (B - A) * S) = trace ((S * (B - A)) * S) := rfl
        _ = trace (S * ((B - A) * S)) := by rw [Matrix.mul_assoc]
        _ = trace (((B - A) * S) * S) := by rw [Matrix.trace_mul_comm]
        _ = trace ((B - A) * (S * S)) := by rw [Matrix.mul_assoc]
        _ = trace ((S * S) * (B - A)) := by rw [Matrix.trace_mul_comm]
        _ = trace (Q * (B - A)) := by rw [h_sq]
    rw [← h_eq]
    exact hPS'.trace_nonneg
  linarith

/-! ## The cells' matrices -/

theorem cellU_posDef (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    {w : ℝ} (hw : w ≠ 0) (c : Set (E d)) : (cellU w π c).PosDef := by
  unfold cellU
  have h_secMom_psd : (secMom (π.restrict c) (meanV π)).PosSemidef :=
    secMom_posSemidef (π.restrict c) (h2.restrict) (meanV π)
  have h_inv_nonneg : 0 ≤ (π.real c)⁻¹ :=
    inv_nonneg.mpr measureReal_nonneg
  have h_first_psd : ((π.real c)⁻¹ • secMom (π.restrict c) (meanV π)).PosSemidef :=
    Matrix.PosSemidef.smul h_secMom_psd h_inv_nonneg
  have hw_sq_pos : 0 < w ^ 2 := sq_pos_iff.mpr hw
  have h_second_pd : ((w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
    have : (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) = Matrix.diagonal (fun _ : Fin d => w ^ 2) := by
      ext i j; simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal]
    rw [this]
    exact Matrix.PosDef.diagonal (fun _ => hw_sq_pos)
  exact Matrix.PosDef.posSemidef_add h_first_psd h_second_pd

theorem cellPay_nonneg (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    {w : ℝ} (hw : w ≠ 0) (c : Set (E d)) : 0 ≤ cellPay w π c := by
  unfold cellPay
  have hW : (frameW w (covM π)).PosDef := frameW_posDef (covM π) (covM_posSemidef π h2) hw
  have hU : (cellU w π c).PosDef := cellU_posDef π h2 hw c
  have hpsi : 0 ≤ psiSum (frameW w (covM π)) (cellU w π c) :=
    psiSum_nonneg (frameW w (covM π)) (cellU w π c) hW hU
  have hreal : 0 ≤ π.real c := measureReal_nonneg
  positivity

theorem cellPay_empty (π : Measure (E d)) (w : ℝ) : cellPay w π ∅ = 0 := by
  rw [AdversarialBco.Lower.cellPay, MeasureTheory.measureReal_empty, zero_mul, zero_div]

/-- (L1): `∑_c p_c psiSum W U_c = ln det W - ∑_c p_c ln det U_c` over a finite measurable partition. -/
theorem ledger_identity {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) {w : ℝ} (hw : w ≠ 0)
    {c : E d → α} (hc : Measurable c) :
    ∑ a, π.real (c ⁻¹' {a}) * psiSum (frameW w (covM π)) (cellU w π (c ⁻¹' {a})) =
      Real.log (det (frameW w (covM π))) - ∑ a, π.real (c ⁻¹' {a}) * Real.log (det (cellU w π (c ⁻¹' {a}))) := by
  set W := frameW w (covM π) with hW
  set p := fun (a : α) => π.real (c ⁻¹' {a}) with hp
  set M := fun (a : α) => secMom (π.restrict (c ⁻¹' {a})) (meanV π) with hM
  set U := fun (a : α) => cellU w π (c ⁻¹' {a}) with hU
  have h_sum_p : ∑ a, p a = 1 := by
    calc
      ∑ a, p a = ∑ a ∈ Finset.univ, p a := by simp
      _ = π.real (c ⁻¹' ((Finset.univ : Finset α) : Set α)) := by
        refine MeasureTheory.sum_measureReal_preimage_singleton (Finset.univ : Finset α) ?_ ?_
        · intro a ha
          exact hc (MeasurableSet.singleton a)
        · intro a ha
          exact measure_ne_top π _
      _ = π.real Set.univ := by simp
      _ = 1 := by simp [measureReal_def]
  have hM_zero_of_p_zero (a : α) (hp0 : p a = 0) : M a = 0 := by
    have hmeas : π (c ⁻¹' {a}) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top π (c ⁻¹' {a}))).mp (by rwa [hp] at hp0)
    have hrestrict : π.restrict (c ⁻¹' {a}) = 0 :=
      (Measure.restrict_eq_zero.mpr hmeas)
    dsimp [M]
    rw [hrestrict]
    ext i j
    simp [secMom, integral_zero_measure]
  have hpos : W.PosDef := by
    have hcov : (covM π).PosSemidef := covM_posSemidef π h2
    exact frameW_posDef (covM π) hcov hw
  have hW_inv_mul : W⁻¹ * W = 1 := by
    have h_det_unit : IsUnit W.det := hpos.det_pos.ne'.isUnit
    exact Matrix.nonsing_inv_mul W h_det_unit
  have h_trace_term (a : α) : p a * trace (W⁻¹ * U a) = trace (W⁻¹ * M a) + (p a * w ^ 2) * trace (W⁻¹) := by
    by_cases hp0 : p a = 0
    · have hM0 : M a = 0 := hM_zero_of_p_zero a hp0
      simp [hp0, hM0, U, cellU]
    · dsimp [U, cellU]
      have hcalc : W⁻¹ * (((p a)⁻¹ • M a) + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) =
          ((p a)⁻¹ • (W⁻¹ * M a)) + ((w ^ 2) • (W⁻¹ * (1 : Matrix (Fin d) (Fin d) ℝ))) := by
        simp [Matrix.mul_add]
      rw [hcalc]
      simp [Matrix.trace_add, Matrix.trace_smul]
      field_simp [hp0]
  have h_trace_sum : ∑ a, p a * trace (W⁻¹ * U a) = (d : ℝ) := by
    calc
      ∑ a, p a * trace (W⁻¹ * U a) = ∑ a, (trace (W⁻¹ * M a) + (p a * w ^ 2) * trace (W⁻¹)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [h_trace_term a]
      _ = (∑ a, trace (W⁻¹ * M a)) + (∑ a, (p a * w ^ 2) * trace (W⁻¹)) := by
        simp [Finset.sum_add_distrib]
      _ = trace (W⁻¹ * (∑ a, M a)) + ((∑ a, p a * w ^ 2) * trace (W⁻¹)) := by
        simp [Matrix.trace_sum, Matrix.mul_sum, Finset.sum_mul]
      _ = trace (W⁻¹ * (∑ a, M a)) + ((w ^ 2 * (∑ a, p a)) * trace (W⁻¹)) := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
      _ = trace (W⁻¹ * (∑ a, M a)) + ((w ^ 2 * 1) * trace (W⁻¹)) := by rw [h_sum_p]
      _ = trace (W⁻¹ * (∑ a, M a)) + (w ^ 2 * trace (W⁻¹)) := by ring
      _ = trace (W⁻¹ * (∑ a, M a)) + trace ((w ^ 2) • W⁻¹) := by
        simp [Matrix.trace_smul]
      _ = trace (W⁻¹ * (∑ a, M a) + (w ^ 2) • W⁻¹) := by
        rw [Matrix.trace_add]
      _ = trace (W⁻¹ * ((∑ a, M a) + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
        have : (w ^ 2) • W⁻¹ = W⁻¹ * ((w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
          simp
        rw [this, Matrix.mul_add]
      _ = trace (W⁻¹ * (covM π + (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
        have hsumM : (∑ a, M a) = covM π := by
          simp [hM, sum_secMom_restrict π h2 hc (meanV π), covM]
        rw [hsumM]
      _ = trace (W⁻¹ * W) := by
        dsimp [W, frameW]
      _ = trace (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [hW_inv_mul]
      _ = (d : ℝ) := by simp [Matrix.trace_one]
  calc
    ∑ a, p a * psiSum W (U a)
        = ∑ a, p a * (trace (W⁻¹ * U a) - (d : ℝ) - Real.log (det (U a)) + Real.log (det W)) := by
      dsimp [psiSum, W]
    _ = (∑ a, p a * trace (W⁻¹ * U a)) - (∑ a, p a * (d : ℝ)) - (∑ a, p a * Real.log (det (U a))) + (∑ a, p a * Real.log (det W)) := by
      simp only [Finset.sum_add_distrib, mul_add, sub_eq_add_neg, add_assoc, mul_neg, Finset.sum_neg_distrib]
    _ = (∑ a, p a * trace (W⁻¹ * U a)) - ((∑ a, p a) * (d : ℝ)) - (∑ a, p a * Real.log (det (U a))) + ((∑ a, p a) * Real.log (det W)) := by
      simp [Finset.sum_mul]
    _ = (∑ a, p a * trace (W⁻¹ * U a)) - (1 * (d : ℝ)) - (∑ a, p a * Real.log (det (U a))) + (1 * Real.log (det W)) := by rw [h_sum_p]
    _ = (∑ a, p a * trace (W⁻¹ * U a)) - (d : ℝ) - (∑ a, p a * Real.log (det (U a))) + Real.log (det W) := by ring
    _ = Real.log (det W) - (∑ a, p a * Real.log (det (U a))) := by
      rw [h_trace_sum]
      ring
    _ = Real.log (det (frameW w (covM π))) - ∑ a, π.real (c ⁻¹' {a}) * Real.log (det (cellU w π (c ⁻¹' {a}))) := by
      simp [hW, hp, hU]

/-! ## (L2): one round -/

/-- The posterior of a law on the ball is a probability law on the ball. -/
theorem bayesUpd_isProbabilityMeasure {Θ : Type*} [MeasurableSpace Θ] (π : Measure Θ) [IsProbabilityMeasure π]
    {L : Θ → ℝ≥0∞} (hL : Measurable L) : IsProbabilityMeasure (bayesUpd π L) := by
  unfold bayesUpd
  split_ifs with h
  · infer_instance
  · have hZ_ne_zero : ∫⁻ θ, L θ ∂π ≠ 0 := by
      intro hzero; apply h; left; exact hzero
    have hZ_ne_top : ∫⁻ θ, L θ ∂π ≠ ∞ := by
      intro htop; apply h; right; exact htop
    have h_fin : IsFiniteMeasure (π.withDensity L) :=
      isFiniteMeasure_withDensity hZ_ne_top
    have h_ne_zero : NeZero (π.withDensity L) := by
      refine ⟨?_⟩
      intro hzero
      apply hZ_ne_zero
      have h_ae := (withDensity_eq_zero_iff hL.aemeasurable).mp hzero
      rw [lintegral_eq_zero_iff' hL.aemeasurable]
      exact h_ae
    have h_univ : (π.withDensity L) Set.univ = ∫⁻ θ, L θ ∂π := by
      simp
    have h_prob : IsProbabilityMeasure (((π.withDensity L) Set.univ)⁻¹ • (π.withDensity L)) :=
      inferInstance
    simpa [h_univ] using h_prob

theorem bayesUpd_ae {Θ : Type*} [MeasurableSpace Θ] (π : Measure Θ) {L : Θ → ℝ≥0∞} {P : Θ → Prop}
    (h : ∀ᵐ θ ∂π, P θ) : ∀ᵐ θ ∂bayesUpd π L, P θ := by
  unfold bayesUpd
  split
  · exact h
  · rename_i h_not
    have h_ac : (π.withDensity L).AbsolutelyContinuous π :=
      MeasureTheory.withDensity_absolutelyContinuous π L
    have h_wd : ∀ᵐ θ ∂(π.withDensity L), P θ :=
      h_ac.ae_le h
    exact MeasureTheory.Measure.ae_smul_measure h_wd (∫⁻ θ, L θ ∂π)⁻¹

/-- The quadratic form `(θ - m)ᵀ Q (θ - m)` is integrable when `‖θ‖²` is. -/
theorem integrable_quadForm (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (m : E d) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun θ : E d => (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp)) π := by
  have h : (fun θ : E d => (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp)) =
      fun θ => ∑ i, ∑ j, Q i j * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) := by
    funext θ
    simp only [dotProduct, mulVec, WithLp.ofLp_sub, Pi.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_secMom_entry π h2 m i j).const_mul _

theorem continuous_quadForm (m : E d) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun θ : E d => (θ - m).ofLp ⬝ᵥ (Q *ᵥ (θ - m).ofLp)) := by
  simp only [dotProduct, mulVec]
  fun_prop

/-- (S4) at a law `π'`: `2 Λ(π') ≤ ln det U - d + w² tr U⁻¹ + ∫ (θ - m)ᵀ U⁻¹ (θ - m) dπ'`. -/
theorem two_lam_le (π' : Measure (E d)) [IsProbabilityMeasure π'] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π')
    {w : ℝ} (hw : w ≠ 0) (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.PosDef) (m : E d) :
    2 * lam w π' ≤ Real.log (det U) - d + w ^ 2 * trace U⁻¹ +
      ∫ θ, (θ - m).ofLp ⬝ᵥ (U⁻¹ *ᵥ (θ - m).ofLp) ∂π' := by
  have hX := frameW_posDef (covM π') (covM_posSemidef π' h2) hw
  have h1 := logdet_le_logdet_add_trace U (frameW w (covM π')) hU hX
  have h3 : trace (U⁻¹ * frameW w (covM π')) = trace (U⁻¹ * covM π') + w ^ 2 * trace U⁻¹ := by
    simp [frameW, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  have h4 : trace (U⁻¹ * covM π') ≤ trace (U⁻¹ * secMom π' m) :=
    trace_mul_le_of_le hU.inv.posSemidef (covM_le_secMom π' h2 m)
  rw [trace_mul_secMom π' h2 m] at h4
  unfold lam
  linarith

/-- The cell's quadratic mass: `tr(U_c⁻¹ ∫_c (θ - m)(θ - m)ᵀ dπ) = p_c (d - w² tr U_c⁻¹)`. -/
theorem trace_cellU_inv_secMom (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    {w : ℝ} (hw : w ≠ 0) (c : Set (E d)) :
    trace ((cellU w π c)⁻¹ * secMom (π.restrict c) (meanV π)) =
      π.real c * (d - w ^ 2 * trace (cellU w π c)⁻¹) := by
  set U := cellU w π c with hUdef
  have hU := cellU_posDef π h2 hw c
  have hsec : secMom (π.restrict c) (meanV π) = π.real c • (U - (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    by_cases hp : π.real c = 0
    · have h0 : π c = 0 := (measureReal_eq_zero_iff).1 hp
      have hr : π.restrict c = 0 := Measure.restrict_eq_zero.2 h0
      rw [hp, zero_smul, hr]
      ext i j
      simp [secMom]
    · rw [hUdef, cellU, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hp, one_smul]
  have hinv : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (hU.det_pos.ne').isUnit
  rw [hsec, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, hinv, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]

/-- `∫⁻ f(c θ) dπ = ∑_a f(a) π(c = a)` for a map `c` to a finite type. -/
theorem lintegral_comp_fintype {Θ α : Type*} [MeasurableSpace Θ] [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (π : Measure Θ) {c : Θ → α} (hc : Measurable c) (f : α → ℝ≥0∞) :
    ∫⁻ θ, f (c θ) ∂π = ∑ a, f a * π (c ⁻¹' {a}) := by
  rw [← lintegral_map (measurable_of_finite f) hc, lintegral_fintype]
  simp [Measure.map_apply hc (measurableSet_singleton _)]

/-- (L2), one round, in the `lintegral` form the game sums: the mean ledger after the answer and the observation
falls by the payment of every cell, `E Λ(π') + (1/2) ∑_c p_c psiSum W U_c ≤ Λ(π)` (all shifted by
`(d/2) ln w²`, below which no ledger falls). -/
theorem ledger_round {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (π : Measure (E d)) [IsProbabilityMeasure π] {r : ℝ} (hsupp : ∀ᵐ θ ∂π, θ ∈ Metric.closedBall (0 : E d) r)
    {c : E d → α} (hc : Measurable c) {s : E d → ℝ} (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0) {w : ℝ}
    (hw : w ≠ 0) :
    ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (lam w (bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) -
          d * Real.log (w ^ 2) / 2) ∂gaussianReal 0 1 ∂π +
        ENNReal.ofReal ((∑ a, π.real (c ⁻¹' {a}) * psiSum (frameW w (covM π)) (cellU w π (c ⁻¹' {a}))) / 2) ≤
      ENNReal.ofReal (lam w π - d * Real.log (w ^ 2) / 2) := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : α → Matrix (Fin d) (Fin d) ℝ, ∀ a, U a = cellU w π (c ⁻¹' {a}) := ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : α → ℝ, ∀ a, p a = π.real (c ⁻¹' {a}) := ⟨_, fun _ => rfl⟩
  obtain ⟨Gq, hGq⟩ : ∃ Gq : α → E d → ℝ, ∀ a θ',
      Gq a θ' = (θ' - meanV π).ofLp ⬝ᵥ ((U a)⁻¹ *ᵥ (θ' - meanV π).ofLp) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : α → ℝ, ∀ a, A a = psiSum (U a) ((w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2 :=
    ⟨_, fun _ => rfl⟩
  have hGqf : ∀ a, Gq a = fun θ' => (θ' - meanV π).ofLp ⬝ᵥ ((U a)⁻¹ *ᵥ (θ' - meanV π).ofLp) :=
    fun a => funext (hGq a)
  have h2 : Integrable (fun θ => ‖θ‖ ^ 2) π := integrable_sq_norm_of_ae_mem π hsupp
  have hUpd : ∀ a, (U a).PosDef := fun a => (hU a) ▸ cellU_posDef π h2 hw _
  have hw2 : 0 < w ^ 2 := by positivity
  have hGq0 : ∀ a θ', 0 ≤ Gq a θ' := fun a θ' => by
    have h := (hUpd a).inv.posSemidef.dotProduct_mulVec_nonneg (θ' - meanV π).ofLp
    rw [star_trivial] at h
    rw [hGq]
    exact h
  have hA0 : ∀ a, 0 ≤ A a := fun a => by
    rw [hAdef]
    exact div_nonneg (psiSum_nonneg _ _ (hUpd a) (Matrix.PosDef.one.smul hw2)) zero_le_two
  have hA : ∀ a, A a = (Real.log (det (U a)) - d + w ^ 2 * trace (U a)⁻¹ - d * Real.log (w ^ 2)) / 2 := by
    intro a
    rw [hAdef]
    simp only [psiSum, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.det_smul,
      Matrix.det_one, mul_one, Fintype.card_fin, Real.log_pow]
    ring
  have hlik : ∀ a y, Measurable (lik c s (noiseVar sc) a y) := fun a y =>
    (measurable_lik hc hs (noiseVar sc)).comp (measurable_prodMk_left (x := (a, y)))
  have hGqc : ∀ a, Continuous (Gq a) := fun a => by rw [hGqf]; exact continuous_quadForm _ _
  have hG : Measurable (fun q : E d × α × ℝ => ENNReal.ofReal (Gq q.2.1 q.1)) := by
    have : Measurable (fun q : E d × α => ENNReal.ofReal (Gq q.2 q.1)) :=
      measurable_from_prod_countable_left fun a => ENNReal.measurable_ofReal.comp (hGqc a).measurable
    exact this.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  -- (S4) pointwise in the posterior
  have hpt : ∀ θ y, ENNReal.ofReal (lam w (bayesUpd π (lik c s (noiseVar sc) (c θ) y)) - d * Real.log (w ^ 2) / 2) ≤
      ENNReal.ofReal (A (c θ)) +
        2⁻¹ * ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ') ∂bayesUpd π (lik c s (noiseVar sc) (c θ) y) := by
    intro θ y
    have : IsProbabilityMeasure (bayesUpd π (lik c s (noiseVar sc) (c θ) y)) :=
      bayesUpd_isProbabilityMeasure π (hlik _ _)
    have h2' : Integrable (fun θ => ‖θ‖ ^ 2) (bayesUpd π (lik c s (noiseVar sc) (c θ) y)) :=
      integrable_sq_norm_of_ae_mem _ (bayesUpd_ae π hsupp)
    have hb := two_lam_le _ h2' hw (U (c θ)) (hUpd _) (meanV π)
    have hint : Integrable (Gq (c θ)) (bayesUpd π (lik c s (noiseVar sc) (c θ) y)) := by
      rw [hGqf]; exact integrable_quadForm _ h2' _ _
    rw [← hGqf] at hb
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hGq0 _))]
    have hhalf : ∀ x : ℝ, (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal x = ENNReal.ofReal (x / 2) := fun x => by
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
    rw [hhalf]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
    rw [hA]
    linarith
  -- the disintegration of the posterior means
  have hstep : ∫⁻ θ, ∫⁻ z, 2⁻¹ * ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ')
        ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π =
      2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Gq (c θ) θ) ∂π := by
    have hbs := bayes_step π hc hs (noiseVar_ne_zero hsc) hG
    simp only [lintegral_const, measure_univ, mul_one] at hbs
    rw [hbs, ← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_congr fun θ => ?_
    rw [lintegral_const_mul' _ _ (by simp)]
    congr 1
    have hF : Measurable (fun y => ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ')
        ∂bayesUpd π (lik c s (noiseVar sc) (c θ) y)) :=
      (measurable_lintegral_bayesUpd π hc hs (noiseVar sc) hG).comp (measurable_prodMk_left (x := c θ))
    exact lintegral_gauss_affine (s θ) sc hF
  -- the cells
  have hrI : ∀ a, ∫ θ in c ⁻¹' {a}, Gq a θ ∂π = p a * (d - w ^ 2 * trace (U a)⁻¹) := by
    intro a
    rw [hGqf, ← trace_mul_secMom (π.restrict _) h2.restrict _ _, hU, hp]
    exact trace_cellU_inv_secMom π h2 hw _
  have hr0 : ∀ a, 0 ≤ p a * (d - w ^ 2 * trace (U a)⁻¹) := fun a =>
    hrI a ▸ integral_nonneg fun θ => hGq0 a θ
  have hr : ∀ a, ∫⁻ θ in c ⁻¹' {a}, ENNReal.ofReal (Gq a θ) ∂π =
      ENNReal.ofReal (p a * (d - w ^ 2 * trace (U a)⁻¹)) := by
    intro a
    have hint : Integrable (Gq a) (π.restrict (c ⁻¹' {a})) := by
      rw [hGqf]; exact integrable_quadForm _ h2.restrict _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hGq0 a)), hrI]
  have hcells : ∫⁻ θ, ENNReal.ofReal (Gq (c θ) θ) ∂π =
      ∑ a, ENNReal.ofReal (p a * (d - w ^ 2 * trace (U a)⁻¹)) := by
    have hsplit : ∀ θ, ENNReal.ofReal (Gq (c θ) θ) =
        ∑ a, (c ⁻¹' {a}).indicator (fun θ => ENNReal.ofReal (Gq a θ)) θ := by
      intro θ
      rw [Finset.sum_eq_single (c θ)]
      · simp
      · intro b _ hb
        exact Set.indicator_of_notMem (by simpa [eq_comm] using hb) _
      · simp
    simp_rw [hsplit]
    rw [lintegral_finsetSum _ fun a _ => Measurable.indicator (f := fun θ => ENNReal.ofReal (Gq a θ))
      (ENNReal.measurable_ofReal.comp (hGqc a).measurable) (hc (measurableSet_singleton a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lintegral_indicator (hc (measurableSet_singleton a)), hr a]
  have hAc : ∫⁻ θ, ENNReal.ofReal (A (c θ)) ∂π = ∑ a, ENNReal.ofReal (A a * p a) := by
    rw [lintegral_comp_fintype π hc (fun a => ENNReal.ofReal (A a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_mul (hA0 a), hp, ofReal_measureReal]
  -- the mean ledger
  have hle : ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (lam w (bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) -
        d * Real.log (w ^ 2) / 2) ∂gaussianReal 0 1 ∂π ≤
      ∑ a, ENNReal.ofReal (A a * p a) + 2⁻¹ * ∑ a, ENNReal.ofReal (p a * (d - w ^ 2 * trace (U a)⁻¹)) := by
    calc _ ≤ ∫⁻ θ, ∫⁻ z, (ENNReal.ofReal (A (c θ)) + 2⁻¹ * ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ')
            ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) ∂gaussianReal 0 1 ∂π :=
          lintegral_mono fun θ => lintegral_mono fun z => hpt θ _
      _ = ∫⁻ θ, (ENNReal.ofReal (A (c θ)) + ∫⁻ z, 2⁻¹ * ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ')
            ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1) ∂π := by
          refine lintegral_congr fun θ => ?_
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ θ, ENNReal.ofReal (A (c θ)) ∂π + ∫⁻ θ, ∫⁻ z, 2⁻¹ * ∫⁻ θ', ENNReal.ofReal (Gq (c θ) θ')
            ∂bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z)) ∂gaussianReal 0 1 ∂π :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp ((measurable_of_finite A).comp hc)) _
      _ = _ := by rw [hstep, hcells, hAc]
  -- the accounting, in real numbers
  have hsum1 : ∑ a, p a = 1 := by
    have h := lintegral_comp_fintype π hc (fun _ => (1 : ℝ≥0∞))
    simp only [lintegral_const, measure_univ, one_mul] at h
    have h' : (∑ a, p a) = (∑ a, π (c ⁻¹' {a})).toReal := by
      rw [ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
      exact Finset.sum_congr rfl fun a _ => hp a
    rw [h', ← h]
    simp
  have hid := ledger_identity π h2 hw hc
  simp only [← hp, ← hU] at hid ⊢
  have hreal : ∑ a, A a * p a + (∑ a, p a * (d - w ^ 2 * trace (U a)⁻¹)) / 2 +
      (∑ a, p a * psiSum (frameW w (covM π)) (U a)) / 2 = lam w π - d * Real.log (w ^ 2) / 2 := by
    have hsum : ∑ a, A a * p a + (∑ a, p a * (d - w ^ 2 * trace (U a)⁻¹)) / 2 =
        (∑ a, p a * Real.log (det (U a))) / 2 - d * Real.log (w ^ 2) / 2 * ∑ a, p a := by
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hA a]
      ring
    rw [hsum, hid, hsum1, lam]
    ring
  have hpay0 : 0 ≤ (∑ a, p a * psiSum (frameW w (covM π)) (U a)) / 2 :=
    div_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hp a ▸ measureReal_nonneg)
      (psiSum_nonneg _ _ (frameW_posDef _ (covM_posSemidef π h2) hw) (hUpd a))) zero_le_two
  have hhalf2 : ∀ x : ℝ, ENNReal.ofReal (x / 2) = 2⁻¹ * ENNReal.ofReal x := fun x => by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
  have hAp0 : 0 ≤ ∑ a, A a * p a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hA0 a) (hp a ▸ measureReal_nonneg)
  have hR0 : 0 ≤ (∑ a, p a * (d - w ^ 2 * trace (U a)⁻¹)) / 2 :=
    div_nonneg (Finset.sum_nonneg fun a _ => hr0 a) zero_le_two
  calc _ ≤ ∑ a, ENNReal.ofReal (A a * p a) + 2⁻¹ * ∑ a, ENNReal.ofReal (p a * (d - w ^ 2 * trace (U a)⁻¹)) +
        ENNReal.ofReal ((∑ a, p a * psiSum (frameW w (covM π)) (U a)) / 2) := by gcongr
    _ = ENNReal.ofReal (lam w π - d * Real.log (w ^ 2) / 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hA0 a) (hp a ▸ measureReal_nonneg),
        ← ENNReal.ofReal_sum_of_nonneg fun a _ => hr0 a, ← hreal, ENNReal.ofReal_add (add_nonneg hAp0 hR0) hpay0,
        ENNReal.ofReal_add hAp0 hR0, hhalf2, hhalf2]

/-- (L2) for answers in `Option Cell`, keeping the announced cells only, in the `lintegral` form the game sums. -/
theorem ledger_round_ann (π : Measure (E d)) [IsProbabilityMeasure π] {r : ℝ}
    (hsupp : ∀ᵐ θ ∂π, θ ∈ Metric.closedBall (0 : E d) r) {c : E d → Option Cell} (hc : Measurable c)
    {s : E d → ℝ} (hs : Measurable s) {sc : ℝ} (hsc : sc ≠ 0) {w : ℝ} (hw : w ≠ 0) :
    ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (lam w (bayesUpd π (lik c s (noiseVar sc) (c θ) (s θ + sc * z))) -
          d * Real.log (w ^ 2) / 2) ∂gaussianReal 0 1 ∂π + ENNReal.ofReal (payAnn w π c) ≤
      ENNReal.ofReal (lam w π - d * Real.log (w ^ 2) / 2) := by
  have h2 := integrable_sq_norm_of_ae_mem π hsupp
  refine le_trans ?_ (ledger_round π hsupp hc hs hsc hw)
  gcongr
  have h0 := cellPay_nonneg π h2 hw (c ⁻¹' {none})
  rw [payAnn, Finset.sum_div, Fintype.sum_option]
  simp only [cellPay] at h0 ⊢
  linarith

/-! ## (L3) to (L5): the cells of `S'` in the frame of `π` -/

/-- The direction of the tail cut: `z = ν⁻¹ M u` with `ν = |u|_M` has `zᵀ W z ≤ 2`. -/
theorem tail_dir_W (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) {w : ℝ} (hw : w ≠ 0) (u : E d)
    (hu : 0 < ‖frameA w S u‖) :
    (‖frameA w S u‖⁻¹ • (clipM w S *ᵥ u.ofLp)) ⬝ᵥ (frameW w S *ᵥ (‖frameA w S u‖⁻¹ • (clipM w S *ᵥ u.ofLp))) ≤ 2 := by
  obtain ⟨ν, hν⟩ : ∃ ν, ν = ‖frameA w S u‖ := ⟨_, rfl⟩
  rw [← hν] at hu ⊢
  obtain ⟨y, hy⟩ : ∃ y, y = clipM w S *ᵥ u.ofLp := ⟨_, rfl⟩
  rw [← hy]
  have hM := clipM_posDef w S hS.1 hw
  have hle := dotProduct_mulVec_le_of_le (frameW_le_two_clipM_inv w S hS hw) y
  have hinv : (clipM w S)⁻¹ *ᵥ y = u.ofLp := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit),
      Matrix.one_mulVec]
  have hyy : y ⬝ᵥ ((clipM w S)⁻¹ *ᵥ y) = ν ^ 2 := by
    rw [hinv, hν, norm_frameA_sq w S hS.1 hw, hy, dotProduct_comm]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hyy] at hle
  have hX : ν⁻¹ * (ν⁻¹ * (y ⬝ᵥ (frameW w S *ᵥ y))) ≤ ν⁻¹ * (ν⁻¹ * (2 * ν ^ 2)) := by
    gcongr
  have h2 : ν⁻¹ * (ν⁻¹ * (2 * ν ^ 2)) = 2 := by
    field_simp
  linarith

/-- The direction of the tail cut reads the frame inner product: `z ⬝ v = ⟨A u, A v⟩/‖A u‖`. -/
theorem tail_dir_dot (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) {w : ℝ} (hw : w ≠ 0) (u v : E d) :
    (‖frameA w S u‖⁻¹ • (clipM w S *ᵥ u.ofLp)) ⬝ᵥ v.ofLp = ⟪frameA w S u, frameA w S v⟫ / ‖frameA w S u‖ := by
  rw [smul_dotProduct, smul_eq_mul, div_eq_inv_mul, inner_frameA w S hS hw]
  congr 1
  have hT : (clipM w S)ᵀ = clipM w S := by
    have := (clipM_isHermitian w S).eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.dotProduct_mulVec u.ofLp, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

/-- A linear functional of the centred tip has an integrable square. -/
theorem integrable_dot_sq (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π)
    (z : Fin d → ℝ) (m : E d) : Integrable (fun θ => (z ⬝ᵥ (θ - m).ofLp) ^ 2) π := by
  have h : (fun θ : E d => (z ⬝ᵥ (θ - m).ofLp) ^ 2) =
      fun θ => ∑ i, ∑ j, (z i * z j) * ((θ.ofLp i - m.ofLp i) * (θ.ofLp j - m.ofLp j)) := by
    funext θ
    simp only [dotProduct, WithLp.ofLp_sub, Pi.sub_apply, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_secMom_entry π h2 m i j).const_mul _

/-- The quadratic form of a cell's matrix: `zᵀ U_c z ≥ p_c⁻¹ ∫_c (z ⬝ (θ - m))² dπ`. -/
theorem quad_cellU_ge (π : Measure (E d)) [IsFiniteMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) (w : ℝ)
    (c : Set (E d)) (z : Fin d → ℝ) :
    (π.real c)⁻¹ * ∫ θ in c, (z ⬝ᵥ (θ - meanV π).ofLp) ^ 2 ∂π ≤ z ⬝ᵥ (cellU w π c *ᵥ z) := by
  have hq := quad_secMom (π.restrict c) h2.restrict (meanV π) (WithLp.toLp 2 z)
  have hint : ∫ θ in c, (z ⬝ᵥ (θ - meanV π).ofLp) ^ 2 ∂π =
      z ⬝ᵥ (secMom (π.restrict c) (meanV π) *ᵥ z) := by
    rw [WithLp.ofLp_toLp] at hq
    rw [hq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [dotProduct_comm]
  rw [hint]
  unfold cellU
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  have h0 : 0 ≤ z ⬝ᵥ z := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have := mul_nonneg (sq_nonneg w) h0
  linarith

/-- (L3): a cell inside the tail `{T > (2k)^{1/2}}` pays at least `p k/4` and at least `E[T²; c]/8`. -/
theorem pay_tail (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) {w k : ℝ}
    (hw : 0 < w) (hk : 6 ≤ k) (x : E d) {c : Set (E d)} (hc : MeasurableSet c)
    (htail : ∀ θ ∈ c, Real.sqrt (2 * k) < readT (frameA w (covM π)) (meanV π) θ x) :
    π.real c * k / 4 ≤ cellPay w π c ∧
      (∫ θ in c, readT (frameA w (covM π)) (meanV π) θ x ^ 2 ∂π) / 8 ≤ cellPay w π c := by
  have hw0 : w ≠ 0 := hw.ne'
  have hS := covM_posSemidef π h2
  have hpay0 := cellPay_nonneg π h2 hw0 c
  obtain ⟨ν, hν_def⟩ : ∃ ν, ν = ‖frameA w (covM π) (x - meanV π)‖ := ⟨_, rfl⟩
  obtain ⟨z, hz_def⟩ : ∃ z : Fin d → ℝ, z = ν⁻¹ • (clipM w (covM π) *ᵥ (x - meanV π).ofLp) := ⟨_, rfl⟩
  have hdot : ∀ θ, z ⬝ᵥ (θ - meanV π).ofLp = readT (frameA w (covM π)) (meanV π) θ x := by
    intro θ
    rw [hz_def, hν_def, tail_dir_dot (covM π) hS.1 hw0]
    rfl
  have hTint : Integrable (fun θ => readT (frameA w (covM π)) (meanV π) θ x ^ 2) π := by
    have := integrable_dot_sq π h2 z (meanV π)
    simp only [hdot] at this
    exact this
  by_cases hp : π.real c = 0
  · have hc0 : π c = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hp
      exact hp.resolve_right (measure_ne_top π c)
    have hr : π.restrict c = 0 := Measure.restrict_eq_zero.2 hc0
    rw [hp, hr, integral_zero_measure]
    constructor <;> linarith
  have hp0 : 0 < π.real c := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
  obtain ⟨θ0, hθ0⟩ : c.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp (by simp)
  have hk0 : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.2 (by linarith)
  have hνpos : 0 < ν := by
    rcases (norm_nonneg (frameA w (covM π) (x - meanV π))).lt_or_eq with h | h
    · rw [hν_def]; exact h
    · have := htail θ0 hθ0
      unfold readT at this
      rw [← h, div_zero] at this
      linarith
  have hzW : z ⬝ᵥ (frameW w (covM π) *ᵥ z) ≤ 2 := by
    rw [hz_def, hν_def]
    exact tail_dir_W (covM π) hS hw0 _ (by rw [← hν_def]; exact hνpos)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := htail θ0 hθ0
    rw [← hdot θ0, zero_dotProduct] at this
    linarith
  have hW := frameW_posDef (covM π) hS hw0
  have hU := cellU_posDef π h2 hw0 c
  have hb : 0 < z ⬝ᵥ (frameW w (covM π) *ᵥ z) := by
    have := hW.dotProduct_mulVec_pos hz0
    simpa using this
  have hUq := quad_cellU_ge π h2 w c z
  simp only [hdot] at hUq
  have hle : ∀ θ ∈ c, 2 * k ≤ readT (frameA w (covM π)) (meanV π) θ x ^ 2 := by
    intro θ hθ
    have h1 := htail θ hθ
    have h2k : Real.sqrt (2 * k) ^ 2 = 2 * k := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (2 * k)]
  have hT2 : 2 * k * π.real c ≤ ∫ θ in c, readT (frameA w (covM π)) (meanV π) θ x ^ 2 ∂π := by
    calc 2 * k * π.real c = ∫ θ in c, (2 * k) ∂π := by
          rw [setIntegral_const, smul_eq_mul]; ring
      _ ≤ _ := setIntegral_mono_on (integrable_const (2 * k)).integrableOn hTint.integrableOn hc hle
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ θ in c, readT (frameA w (covM π)) (meanV π) θ x ^ 2 ∂π := ⟨_, rfl⟩
  rw [← hI] at hT2 hUq ⊢
  have hpsi := psiSum_ge_quot _ _ hW hU z hz0
  obtain ⟨a, ha⟩ : ∃ a, a = z ⬝ᵥ (cellU w π c *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, b = z ⬝ᵥ (frameW w (covM π) *ᵥ z) := ⟨_, rfl⟩
  rw [← ha] at hUq hpsi
  rw [← hb'] at hzW hb hpsi
  have hpI : 2 * k ≤ (π.real c)⁻¹ * I := by
    have h1 : (π.real c)⁻¹ * (2 * k * π.real c) ≤ (π.real c)⁻¹ * I :=
      mul_le_mul_of_nonneg_left hT2 (inv_nonneg.2 hp0.le)
    have h2 : (π.real c)⁻¹ * (2 * k * π.real c) = 2 * k := by field_simp
    linarith
  have ha0 : 0 ≤ a := by linarith
  have hq2 : a / 2 ≤ a / b := div_le_div_of_nonneg_left ha0 hb hzW
  have hq6 : 6 ≤ a / b := by linarith
  have hhalf := psiF_ge_half hq6
  unfold cellPay
  have hpp : π.real c * ((π.real c)⁻¹ * I) = I := by field_simp
  constructor
  · nlinarith
  · nlinarith

/-- (L4): on a live round, a cell inside `{R² < D_M/64}` pays at least `p d/62`. -/
theorem pay_inner (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) {w : ℝ}
    (hw : 0 < w) (hd : 0 < d) (hlive : (d : ℝ) / 2 ≤ dLive w (covM π)) {c : Set (E d)} (hc : MeasurableSet c)
    (hin : ∀ θ ∈ c, ‖frameA w (covM π) (θ - meanV π)‖ ^ 2 < DM w (covM π) / 64) :
    π.real c * d / 62 ≤ cellPay w π c := by
  have hw0 : w ≠ 0 := hw.ne'
  have hS := covM_posSemidef π h2
  have hpay0 := cellPay_nonneg π h2 hw0 c
  by_cases hp : π.real c = 0
  · rw [hp, zero_mul, zero_div]
    exact hpay0
  have hp0 : 0 < π.real c := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
  have hW := frameW_posDef (covM π) hS hw0
  have hU := cellU_posDef π h2 hw0 c
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨N, hN⟩ : ∃ N, N = secMom (π.restrict c) (meanV π) := ⟨_, rfl⟩
  have hNpsd : N.PosSemidef := hN ▸ secMom_posSemidef (π.restrict c) h2.restrict (meanV π)
  have hsplit : trace ((frameW w (covM π))⁻¹ * cellU w π c) =
      (π.real c)⁻¹ * trace ((frameW w (covM π))⁻¹ * N) + w ^ 2 * trace (frameW w (covM π))⁻¹ := by
    rw [hN]
    unfold cellU
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  have hi := sq_trace_frameW_inv_le w (covM π) hS hw0
  have hii : trace ((frameW w (covM π))⁻¹ * N) ≤ trace (clipM w (covM π) * N) := by
    rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm (clipM w (covM π))]
    exact trace_mul_le_of_le hNpsd (frameW_inv_le_clipM w (covM π) hS hw0)
  have hiii : trace (clipM w (covM π) * N) ≤ π.real c * (DM w (covM π) / 64) := by
    rw [hN, trace_mul_secMom (π.restrict c) h2.restrict (meanV π)]
    have hint := (integrable_quadForm π h2 (meanV π) (clipM w (covM π))).integrableOn (s := c)
    calc ∫ θ in c, (θ - meanV π).ofLp ⬝ᵥ (clipM w (covM π) *ᵥ (θ - meanV π).ofLp) ∂π
        ≤ ∫ θ in c, DM w (covM π) / 64 ∂π := by
          refine setIntegral_mono_on hint (integrable_const _).integrableOn hc fun θ hθ => ?_
          rw [← norm_frameA_sq w (covM π) hS.1 hw0]
          exact (hin θ hθ).le
      _ = π.real c * (DM w (covM π) / 64) := by rw [setIntegral_const, smul_eq_mul]
  have hDM := DM_le w (covM π) hS hw0
  have hWinv := hW.inv
  have hT0 : 0 ≤ trace ((frameW w (covM π))⁻¹ * N) := by
    rw [Matrix.trace_mul_comm]
    have := trace_mul_le_of_le hNpsd (A := 0) (B := (frameW w (covM π))⁻¹) hWinv.posSemidef.nonneg
    simpa using this
  have htr : 0 < trace (frameW w (covM π))⁻¹ := hWinv.trace_pos
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = trace ((frameW w (covM π))⁻¹ * cellU w π c) := ⟨_, rfl⟩
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hpDM := mul_le_mul_of_nonneg_left hDM hp0.le
  have hA : (π.real c)⁻¹ * trace ((frameW w (covM π))⁻¹ * N) ≤ d / 64 := by
    rw [inv_mul_le_iff₀ hp0]
    linarith
  have hA0 : 0 ≤ (π.real c)⁻¹ * trace ((frameW w (covM π))⁻¹ * N) := mul_nonneg (inv_nonneg.2 hp0.le) hT0
  have hτle : τ ≤ 49 / 64 * d := by
    rw [hτ, hsplit]
    linarith
  have hτpos : 0 < τ := by
    rw [hτ, hsplit]
    have := mul_pos (pow_pos hw 2) htr
    linarith
  have ht0 : 0 < τ / d := div_pos hτpos hdpos
  have ht1 : τ / d ≤ 49 / 64 := by
    rw [div_le_iff₀ hdpos]
    linarith
  have hpsi := psiF_antitoneOn ⟨ht0, by linarith⟩ ⟨by norm_num, by norm_num⟩ ht1
  have hmean := psiSum_ge_mean _ _ hW hU hd
  rw [← hτ] at hmean
  have h31 := psiF_inner
  have hd31 : (d : ℝ) / 31 ≤ psiSum (frameW w (covM π)) (cellU w π c) := by
    have := mul_le_mul_of_nonneg_left (h31.trans hpsi) hdpos.le
    linarith
  unfold cellPay
  have := mul_le_mul_of_nonneg_left hd31 hp0.le
  linarith

/-- (L5): a cell inside `{R² > 4d}` pays at least `p d/62`. -/
theorem pay_outer (π : Measure (E d)) [IsProbabilityMeasure π] (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) {w : ℝ}
    (hw : 0 < w) (hd : 0 < d) {c : Set (E d)} (hc : MeasurableSet c)
    (hout : ∀ θ ∈ c, 4 * (d : ℝ) < ‖frameA w (covM π) (θ - meanV π)‖ ^ 2) :
    π.real c * d / 62 ≤ cellPay w π c := by
  set S := covM π
  set m := meanV π
  set W := frameW w S
  set p := π.real c
  set N := secMom (π.restrict c) m
  set M := clipM w S
  set U := cellU w π c
  have hp_nonneg : 0 ≤ p := MeasureTheory.measureReal_nonneg
  by_cases hp_zero : p = 0
  · -- case p = 0: both sides are 0
    rw [hp_zero]
    have h_cellPay : cellPay w π c = 0 := by
      simp [cellPay, p, hp_zero]
    simp [h_cellPay]
  · have hp_pos : 0 < p := by
      by_contra! hle
      have h_eq : p = 0 := le_antisymm hle hp_nonneg
      exact hp_zero h_eq
    have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd
    have hw_ne : w ≠ 0 := by linarith
    -- W is positive definite
    have hS_psd : S.PosSemidef := covM_posSemidef π h2
    have hW_def : W.PosDef := frameW_posDef S hS_psd hw_ne
    have hW_inv_psd : (W⁻¹).PosSemidef := (hW_def.inv).posSemidef
    have hW_inv_nonneg : 0 ≤ trace (W⁻¹) := Matrix.PosSemidef.trace_nonneg hW_inv_psd
    -- N is positive semidefinite on the restriction
    have h_int_restrict : Integrable (fun θ => ‖θ‖ ^ 2) (π.restrict c) :=
      h2.restrict
    have hN_psd : N.PosSemidef := secMom_posSemidef (π.restrict c) h_int_restrict m
    -- U is positive definite
    have hU_def : U.PosDef := cellU_posDef π h2 hw_ne c
    -- S is Hermitian
    have hS_herm : S.IsHermitian := hS_psd.isHermitian
    -- integrability of ‖frameA w S (θ - m)‖ ^ 2 on c
    have h_int_norm_sq : IntegrableOn (fun θ => ‖frameA w S (θ - m)‖ ^ 2) c π := by
      have h_mem_id : MemLp (fun θ => θ) 2 π := by
        rw [memLp_two_iff_integrable_sq_norm]
        · exact h2
        · exact aestronglyMeasurable_id
      have h_mem_const : MemLp (fun _ => m) 2 π := memLp_const m
      have h_mem_sub : MemLp (fun θ => θ - m) 2 π := MemLp.sub h_mem_id h_mem_const
      have h_mem_comp : MemLp (fun θ => frameA w S (θ - m)) 2 π :=
        ContinuousLinearMap.comp_memLp' (frameA w S) h_mem_sub
      have h_int : Integrable (fun θ => ‖frameA w S (θ - m)‖ ^ 2) π :=
        h_mem_comp.integrable_norm_pow (by norm_num)
      exact h_int.integrableOn
    -- compute trace(W⁻¹ * U) in terms of trace(W⁻¹ * N) and trace(W⁻¹)
    have h_trace_U : trace (W⁻¹ * U) = p⁻¹ * trace (W⁻¹ * N) + w ^ 2 * trace (W⁻¹) := by
      calc
        trace (W⁻¹ * U) = trace (W⁻¹ * (p⁻¹ • N + w ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))) := rfl
        _ = trace (W⁻¹ * (p⁻¹ • N) + W⁻¹ * (w ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
          rw [Matrix.mul_add]
        _ = trace (p⁻¹ • (W⁻¹ * N) + w ^ 2 • (W⁻¹ * (1 : Matrix (Fin d) (Fin d) ℝ))) := by
          simp
        _ = trace (p⁻¹ • (W⁻¹ * N)) + trace (w ^ 2 • (W⁻¹ * (1 : Matrix (Fin d) (Fin d) ℝ))) := by
          rw [Matrix.trace_add]
        _ = p⁻¹ * trace (W⁻¹ * N) + w ^ 2 * trace (W⁻¹ * (1 : Matrix (Fin d) (Fin d) ℝ)) := by
          simp [Matrix.trace_smul]
        _ = p⁻¹ * trace (W⁻¹ * N) + w ^ 2 * trace (W⁻¹) := by simp
    -- trace(W⁻¹) ≥ 0, so trace(W⁻¹ * U) ≥ p⁻¹ * trace(W⁻¹ * N)
    have h_trace_U_ge : p⁻¹ * trace (W⁻¹ * N) ≤ trace (W⁻¹ * U) := by
      have h_nonneg : 0 ≤ w ^ 2 * trace (W⁻¹) := by
        nlinarith [sq_nonneg w, hW_inv_nonneg]
      nlinarith
    -- M ≤ 2 • W⁻¹
    have hM_le : M ≤ (2 : ℝ) • (W⁻¹) := clipM_le_two_frameW_inv w S hS_psd hw_ne
    -- trace(M * N) ≤ 2 * trace(W⁻¹ * N)
    have h_trace_MN_le : trace (M * N) ≤ 2 * trace (W⁻¹ * N) := by
      have h := trace_mul_le_of_le hN_psd hM_le
      -- h : trace (N * M) ≤ trace (N * ((2 : ℝ) • (W⁻¹)))
      -- we need trace (M * N) ≤ 2 * trace (W⁻¹ * N)
      have h_comm : trace (N * M) = trace (M * N) := Matrix.trace_mul_comm _ _
      have h_right : trace (N * ((2 : ℝ) • (W⁻¹))) = (2 : ℝ) * trace (W⁻¹ * N) := by
        simp [Matrix.trace_smul, Matrix.trace_mul_comm N (W⁻¹)]
      rw [h_comm, h_right] at h
      exact h
    -- trace(M * N) = ∫_c ‖frameA w S (θ - m)‖ ^ 2 dπ
    have h_trace_MN_eq : trace (M * N) = ∫ θ in c, ‖frameA w S (θ - m)‖ ^ 2 ∂π := by
      calc
        trace (M * N) = trace (clipM w S * secMom (π.restrict c) m) := rfl
        _ = ∫ θ, (θ - m).ofLp ⬝ᵥ (clipM w S *ᵥ (θ - m).ofLp) ∂(π.restrict c) := by
          rw [trace_mul_secMom (π.restrict c) h_int_restrict m (clipM w S)]
        _ = ∫ θ in c, (θ - m).ofLp ⬝ᵥ (clipM w S *ᵥ (θ - m).ofLp) ∂π := rfl
        _ = ∫ θ in c, ‖frameA w S (θ - m)‖ ^ 2 ∂π := by
          have h_eq_on : Set.EqOn (fun θ => (θ - m).ofLp ⬝ᵥ (clipM w S *ᵥ (θ - m).ofLp))
              (fun θ => ‖frameA w S (θ - m)‖ ^ 2) c := by
            intro θ hθ
            dsimp
            -- goal: (θ.ofLp - m.ofLp) ⬝ᵥ clipM w S *ᵥ (θ.ofLp - m.ofLp) = ‖frameA w S (θ - m)‖ ^ 2
            -- norm_frameA_sq gives: ‖frameA w S (θ - m)‖ ^ 2 = (θ - m).ofLp ⬝ᵥ (clipM w S *ᵥ (θ - m).ofLp)
            -- and (θ - m).ofLp = θ.ofLp - m.ofLp
            simpa [WithLp.ofLp_sub] using (norm_frameA_sq w S hS_herm hw_ne (θ - m)).symm
          rw [setIntegral_congr_fun hc h_eq_on]
    -- ∫_c ‖frameA w S (θ - m)‖ ^ 2 dπ ≥ ∫_c 4*d dπ = 4*d*p
    have h_int_ineq : (∫ θ in c, 4 * (d : ℝ) ∂π) ≤ (∫ θ in c, ‖frameA w S (θ - m)‖ ^ 2 ∂π) := by
      refine setIntegral_mono_on ?_ h_int_norm_sq hc ?_
      · -- integrability of constant
        exact integrableOn_const
      · -- pointwise inequality
        intro θ hθ
        exact le_of_lt (hout θ hθ)
    have h_int_const : (∫ θ in c, 4 * (d : ℝ) ∂π) = 4 * (d : ℝ) * p := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    -- trace(M * N) ≥ 4*d*p
    have h_trace_MN_ge : 4 * (d : ℝ) * p ≤ trace (M * N) := by
      linarith
    -- trace(W⁻¹ * N) ≥ 2*d*p
    have h_trace_WinvN_ge : 2 * (d : ℝ) * p ≤ trace (W⁻¹ * N) := by
      have h : 4 * (d : ℝ) * p ≤ 2 * trace (W⁻¹ * N) := by
        linarith
      nlinarith
    -- trace(W⁻¹ * U) ≥ 2*d
    have h_trace_U_div_d_ge_two : 2 ≤ trace (W⁻¹ * U) / (d : ℝ) := by
      have h : 2 * (d : ℝ) ≤ trace (W⁻¹ * U) := by
        -- from h_trace_U_ge: p⁻¹ * trace(W⁻¹ * N) ≤ trace(W⁻¹ * U)
        -- and h_trace_WinvN_ge: 2*d*p ≤ trace(W⁻¹ * N)
        -- so p⁻¹ * (2*d*p) = 2*d ≤ trace(W⁻¹ * U)
        have h' : p⁻¹ * (2 * (d : ℝ) * p) ≤ trace (W⁻¹ * U) := by
          -- from h_trace_WinvN_ge and h_trace_U_ge
          calc
            p⁻¹ * (2 * (d : ℝ) * p) ≤ p⁻¹ * trace (W⁻¹ * N) :=
              mul_le_mul_of_nonneg_left h_trace_WinvN_ge (by positivity)
            _ ≤ trace (W⁻¹ * U) := h_trace_U_ge
        -- simplify p⁻¹ * (2*d*p) = 2*d
        have h_simp : p⁻¹ * (2 * (d : ℝ) * p) = 2 * (d : ℝ) := by
          field_simp [hp_pos.ne']
        rw [h_simp] at h'
        exact h'
      rw [le_div_iff₀' hd_pos]
      nlinarith
    -- psiF(trace(W⁻¹ * U) / d) ≥ psiF(2) ≥ 1/31
    have h_psi_ge : 1/31 ≤ psiF (trace (W⁻¹ * U) / (d : ℝ)) := by
      have h_two_mem : (2 : ℝ) ∈ Set.Ici (1 : ℝ) := by norm_num
      have h_ratio_mem : trace (W⁻¹ * U) / (d : ℝ) ∈ Set.Ici (1 : ℝ) := by
        have h_one_le_two : (1 : ℝ) ≤ 2 := by norm_num
        have h_le : (1 : ℝ) ≤ trace (W⁻¹ * U) / (d : ℝ) := le_trans h_one_le_two h_trace_U_div_d_ge_two
        exact h_le
      have h_mono : psiF 2 ≤ psiF (trace (W⁻¹ * U) / (d : ℝ)) :=
        psiF_monotoneOn h_two_mem h_ratio_mem h_trace_U_div_d_ge_two
      have h_two : 1/31 ≤ psiF 2 := psiF_two
      linarith
    -- psiSum W U ≥ d * psiF(trace(W⁻¹ * U) / d) ≥ d/31
    have h_psiSum_ge : (d : ℝ) / 31 ≤ psiSum W U := by
      have h := psiSum_ge_mean W U hW_def hU_def hd
      have h' : (d : ℝ) * psiF (trace (W⁻¹ * U) / (d : ℝ)) ≤ psiSum W U := h
      nlinarith
    -- final inequality: cellPay = p * psiSum W U / 2 ≥ p * (d/31) / 2 = p * d / 62
    calc
      π.real c * d / 62 = p * (d : ℝ) / 62 := by ring
      _ = p * ((d : ℝ) / 31) / 2 := by ring
      _ ≤ p * psiSum W U / 2 := by
        nlinarith
      _ = cellPay w π c := by
        simp [cellPay, U, W, S, p]

/-! ## (L6): the game -/

/-- Summation of a ledger that falls in mean by the payments. -/
theorem telescope_lintegral {S : Type*} [MeasurableSpace S] (P : Measure S) (F pay : ℕ → S → ℝ≥0∞) (n : ℕ)
    (h : ∀ t < n, ∫⁻ s, F (t + 1) s ∂P + ∫⁻ s, pay t s ∂P ≤ ∫⁻ s, F t s ∂P) :
    ∑ t ∈ Finset.range n, ∫⁻ s, pay t s ∂P + ∫⁻ s, F n s ∂P ≤ ∫⁻ s, F 0 s ∂P := by
  induction' n with n ih
  · -- n = 0
    simp
  · -- n → n+1
    have hn : ∫⁻ s, F (n + 1) s ∂P + ∫⁻ s, pay n s ∂P ≤ ∫⁻ s, F n s ∂P :=
      h n (Nat.lt_succ_self n)
    have h_restrict : ∀ t < n, ∫⁻ s, F (t + 1) s ∂P + ∫⁻ s, pay t s ∂P ≤ ∫⁻ s, F t s ∂P := by
      intro t ht
      exact h t (Nat.lt_trans ht (Nat.lt_succ_self n))
    have ih_applied := ih h_restrict
    rw [Finset.sum_range_succ]
    calc
      (∑ t ∈ Finset.range n, ∫⁻ s, pay t s ∂P + ∫⁻ s, pay n s ∂P) + ∫⁻ s, F (n + 1) s ∂P
          = (∑ t ∈ Finset.range n, ∫⁻ s, pay t s ∂P) + (∫⁻ s, F (n + 1) s ∂P + ∫⁻ s, pay n s ∂P) := by
        abel
      _ ≤ (∑ t ∈ Finset.range n, ∫⁻ s, pay t s ∂P) + ∫⁻ s, F n s ∂P :=
        add_le_add_right hn _
      _ ≤ ∫⁻ s, F 0 s ∂P := ih_applied

/-- The ledger at the prior: `Λ(π₁) ≤ (d/2) ln(r₀²/d + w²)`. -/
theorem lam_prior_le (hd : 0 < d) {r₀ : ℝ} (hr : 0 < r₀) {w : ℝ} (hw : w ≠ 0) :
    lam w (prior d r₀) ≤ d / 2 * Real.log (r₀ ^ 2 / d + w ^ 2) := by
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  set μ := prior d r₀ with hμ
  set X := frameW w (covM μ) with hX
  have h_prob : IsProbabilityMeasure μ := isProbabilityMeasure_prior d hr
  have h_ae_mem : ∀ᵐ θ ∂μ, θ ∈ Metric.closedBall (0 : E d) r₀ := prior_ae_mem d r₀
  have h_norm_bound : ∀ᵐ θ ∂μ, ‖θ‖ ≤ r₀ := by
    filter_upwards [h_ae_mem] with θ hθ
    have h_dist : dist θ (0 : E d) ≤ r₀ := Metric.mem_closedBall.mp hθ
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
  have h_sq_bound : ∀ᵐ θ ∂μ, ‖θ‖ ^ 2 ≤ r₀ ^ 2 := by
    filter_upwards [h_norm_bound] with θ hθ
    have h_nonneg_norm : 0 ≤ ‖θ‖ := norm_nonneg _
    have h_nonneg_r₀ : 0 ≤ r₀ := by linarith
    have h := mul_self_le_mul_self h_nonneg_norm hθ
    simpa [sq] using h
  have h_int_sq : Integrable (fun θ => ‖θ‖ ^ 2) μ :=
    integrable_sq_norm_of_ae_mem μ h_ae_mem
  have h_int_const : Integrable (fun _ => r₀ ^ 2) μ :=
    integrable_const _
  have h_int_le : ∫ θ, ‖θ‖ ^ 2 ∂μ ≤ ∫ θ, r₀ ^ 2 ∂μ :=
    MeasureTheory.integral_mono_ae h_int_sq h_int_const h_sq_bound
  have h_int_const_val : ∫ θ, r₀ ^ 2 ∂μ = r₀ ^ 2 := by
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  have h_trace_cov_le : Matrix.trace (covM μ) ≤ ∫ θ, ‖θ‖ ^ 2 ∂μ :=
    trace_covM_le μ h_int_sq
  have h_pos_semidef : (covM μ).PosSemidef := covM_posSemidef μ h_int_sq
  have h_pos_def : X.PosDef := frameW_posDef (covM μ) h_pos_semidef hw
  have h_trace_X : Matrix.trace X = Matrix.trace (covM μ) + (d : ℝ) * (w ^ 2) := by
    dsimp [X, frameW]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    ring
  haveI : Nonempty (Fin d) := by
    refine ⟨⟨0, hd⟩⟩
  have h_trace_X_pos : 0 < Matrix.trace X := Matrix.PosDef.trace_pos h_pos_def
  have h_trace_X_div_pos : 0 < Matrix.trace X / (d : ℝ) := div_pos h_trace_X_pos hd_real
  have h_logdet_le : Real.log (det X) ≤ (d : ℝ) * Real.log (Matrix.trace X / (d : ℝ)) :=
    logdet_le_card_log_trace X h_pos_def hd
  have h_trace_bound : Matrix.trace X ≤ r₀ ^ 2 + (d : ℝ) * (w ^ 2) := by
    linarith
  have h_trace_div_bound : Matrix.trace X / (d : ℝ) ≤ (r₀ ^ 2) / (d : ℝ) + w ^ 2 := by
    have h := div_le_div_of_nonneg_right h_trace_bound hd_nonneg
    have h_eq : (r₀ ^ 2 + (d : ℝ) * (w ^ 2)) / (d : ℝ) = (r₀ ^ 2) / (d : ℝ) + w ^ 2 := by
      field_simp [hd_real.ne']
    rw [h_eq] at h
    exact h
  have h_log_le : Real.log (Matrix.trace X / (d : ℝ)) ≤ Real.log ((r₀ ^ 2) / (d : ℝ) + w ^ 2) :=
    Real.log_le_log h_trace_X_div_pos h_trace_div_bound
  have h_mul_le : (d : ℝ) * Real.log (Matrix.trace X / (d : ℝ)) ≤ (d : ℝ) * Real.log ((r₀ ^ 2) / (d : ℝ) + w ^ 2) :=
    mul_le_mul_of_nonneg_left h_log_le hd_nonneg
  have h_logdet_le' : Real.log (det X) ≤ (d : ℝ) * Real.log ((r₀ ^ 2) / (d : ℝ) + w ^ 2) := by
    linarith
  dsimp [lam, X, μ]
  linarith

/-- The ledger is measurable along a measurable family of densities. -/
theorem measurable_lam_dens {H : Type} [MeasurableSpace H] (π0 : Measure (E d)) [SFinite π0]
    {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) (w : ℝ) :
    Measurable (fun h => lam w (π0.withDensity (g h))) := by
  have hcov := measurable_covM_dens π0 hg hfin
  have hW : Continuous (fun S : Matrix (Fin d) (Fin d) ℝ => det (frameW w S)) :=
    (continuous_id.add continuous_const).matrix_det
  exact (Real.measurable_log.comp (hW.measurable.comp hcov)).div_const 2

/-- The payment of a cell is measurable along a measurable family of densities and of cells. -/
theorem measurable_cellPay_dens {H : Type} [MeasurableSpace H] (π0 : Measure (E d)) [SFinite π0]
    {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞)
    {S : Set (H × E d)} (hS : MeasurableSet S) (w : ℝ) :
    Measurable (fun h => cellPay w (π0.withDensity (g h)) {θ | (h, θ) ∈ S}) := by
  have : OpensMeasurableSpace (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace ((Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)))
  set π := fun (h : H) => π0.withDensity (g h) with hπ
  set c := fun (h : H) => {θ | (h, θ) ∈ S} with hc
  have h_real : Measurable (fun h => (π h).real (c h)) :=
    measurable_measureReal_dens π0 hg measurable_id hS
  have h_covM : Measurable (fun h => covM (π h)) :=
    measurable_covM_dens π0 hg hfin
  have h_meanV : Measurable (fun h => meanV (π h)) :=
    measurable_meanV_dens π0 hg hfin
  -- Measurability of the matrix of restricted second moments
  have h_secMom : Measurable (fun h => secMom ((π h).restrict (c h)) (meanV (π h))) := by
    refine measurable_pi_iff.mpr fun i => ?_
    refine measurable_pi_iff.mpr fun j => ?_
    have h_int : Measurable (fun (h : H) => ∫ θ in c h,
      (θ.ofLp i - (meanV (π h)).ofLp i) * (θ.ofLp j - (meanV (π h)).ofLp j) ∂(π h)) := by
      set F : H × E d → ℝ := fun p =>
        (p.2.ofLp i - (meanV (π p.1)).ofLp i) * (p.2.ofLp j - (meanV (π p.1)).ofLp j) with hF
      have hF_meas : Measurable F := by
        dsimp [F]
        refine Measurable.mul (Measurable.sub ?_ ?_) (Measurable.sub ?_ ?_)
        · exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp measurable_snd
        · exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp h_meanV).comp
            measurable_fst
        · exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j).measurable.comp measurable_snd
        · exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j).measurable.comp h_meanV).comp
            measurable_fst
      have h_int' := measurable_setIntegral_dens π0 hg hfin measurable_id hS hF_meas
      simpa [c, hF, π] using h_int'
    simpa [secMom, Matrix.of_apply] using h_int
  -- Now build up to cellPay
  have h_cellU : Measurable (fun h => cellU w (π h) (c h)) := by
    dsimp [cellU]
    have h1 : Measurable (fun h => ((π h).real (c h))⁻¹ • secMom ((π h).restrict (c h)) (meanV (π h))) :=
      h_real.inv.smul h_secMom
    have h2 : Measurable (fun _ : H => (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := measurable_const
    have h_add_cont : Continuous (fun (p : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 + p.2) :=
      continuous_add
    have h_add_meas : Measurable (fun (p : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 + p.2) :=
      h_add_cont.measurable
    exact h_add_meas.comp (Measurable.prodMk h1 h2)
  have h_frameW : Measurable (fun h => frameW w (covM (π h))) := by
    dsimp [frameW]
    have h1 : Measurable (fun h => covM (π h)) := h_covM
    have h2 : Measurable (fun _ : H => (w ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := measurable_const
    have h_add_cont : Continuous (fun (p : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 + p.2) :=
      continuous_add
    have h_add_meas : Measurable (fun (p : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 + p.2) :=
      h_add_cont.measurable
    exact h_add_meas.comp (Measurable.prodMk h1 h2)
  have h_psiSum : Measurable (fun h => psiSum (frameW w (covM (π h))) (cellU w (π h) (c h))) := by
    dsimp [psiSum]
    -- trace (W⁻¹ * U) - d - Real.log (det U) + Real.log (det W)
    have h_Winv : Measurable (fun h => (frameW w (covM (π h)))⁻¹) := by
      have h_det_cont : Continuous (fun (M : Matrix (Fin d) (Fin d) ℝ) => det M) :=
        Continuous.matrix_det (continuous_id : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => M))
      have h_adj_cont : Continuous (fun (M : Matrix (Fin d) (Fin d) ℝ) => adjugate M) :=
        Continuous.matrix_adjugate (continuous_id : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => M))
      have h_det : Measurable (fun h => det (frameW w (covM (π h)))) :=
        h_det_cont.measurable.comp h_frameW
      have h_adj : Measurable (fun h => adjugate (frameW w (covM (π h)))) :=
        h_adj_cont.measurable.comp h_frameW
      have h_inv : Measurable (fun h => (det (frameW w (covM (π h))))⁻¹) :=
        measurable_inv.comp h_det
      have h_eq : (fun h => (frameW w (covM (π h)))⁻¹) =
          (fun h => (det (frameW w (covM (π h))))⁻¹ • adjugate (frameW w (covM (π h)))) := by
        ext h
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [h_eq]
      have h_smul_cont : Continuous (fun (p : ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 • p.2) :=
        continuous_smul
      have h_smul_meas : Measurable (fun (p : ℝ × Matrix (Fin d) (Fin d) ℝ) => p.1 • p.2) :=
        h_smul_cont.measurable
      exact h_smul_meas.comp (Measurable.prodMk h_inv h_adj)
    have h_mul : Measurable (fun h => (frameW w (covM (π h)))⁻¹ * cellU w (π h) (c h)) :=
      continuous_mul.measurable.comp (Measurable.prodMk h_Winv h_cellU)
    have h_trace_cont : Continuous (fun (M : Matrix (Fin d) (Fin d) ℝ) => trace M) :=
      Continuous.matrix_trace (continuous_id : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => M))
    have h_trace : Measurable (fun h => Matrix.trace ((frameW w (covM (π h)))⁻¹ * cellU w (π h) (c h))) :=
      h_trace_cont.measurable.comp h_mul
    have h_det_meas : Measurable (fun (M : Matrix (Fin d) (Fin d) ℝ) => det M) :=
      (Continuous.matrix_det (continuous_id : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => M))).measurable
    have h_log_det_U : Measurable (fun h => Real.log (det (cellU w (π h) (c h)))) :=
      Real.measurable_log.comp (h_det_meas.comp h_cellU)
    have h_log_det_W : Measurable (fun h => Real.log (det (frameW w (covM (π h))))) :=
      Real.measurable_log.comp (h_det_meas.comp h_frameW)
    have h_sub1 : Measurable (fun h =>
      Matrix.trace ((frameW w (covM (π h)))⁻¹ * cellU w (π h) (c h)) - (d : ℝ)) :=
      h_trace.sub measurable_const
    have h_sub2 : Measurable (fun h =>
      Matrix.trace ((frameW w (covM (π h)))⁻¹ * cellU w (π h) (c h)) - (d : ℝ) -
      Real.log (det (cellU w (π h) (c h)))) :=
      h_sub1.sub h_log_det_U
    have h_add_cont' : Continuous (fun (p : ℝ × ℝ) => p.1 + p.2) := continuous_add
    have h_add_meas' : Measurable (fun (p : ℝ × ℝ) => p.1 + p.2) := h_add_cont'.measurable
    exact h_add_meas'.comp (Measurable.prodMk h_sub2 h_log_det_W)
  dsimp [cellPay]
  have h_mul_cont' : Continuous (fun (p : ℝ × ℝ) => p.1 * p.2) := continuous_mul
  have h_mul_meas' : Measurable (fun (p : ℝ × ℝ) => p.1 * p.2) := h_mul_cont'.measurable
  have h_mul : Measurable (fun h => (π h).real (c h) *
    psiSum (frameW w (covM (π h))) (cellU w (π h) (c h))) :=
    h_mul_meas'.comp (Measurable.prodMk h_real h_psiSum)
  refine h_mul.div_const 2

/-- The payment of a round is measurable in the history and the play, for a measurable rule. -/
theorem measurable_payAnn (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell))
    (hR : R.Meas π0) (sc : ℝ) (t : ℕ) (w : ℝ) :
    Measurable (fun p : Hist d (Option Cell) × E d =>
      payAnn w (post π0 R sc t p.1) (R.ans (post π0 R sc t p.1) p.2)) := by
  have hdp := dens_props π0 R hR sc t
  have hg : Measurable (Function.uncurry fun p : Hist d (Option Cell) × E d => dens π0 R sc t p.1) :=
    hdp.1.comp (measurable_fst.fst.prodMk measurable_snd)
  have hans := (measurable_rule_post π0 R hR sc t).1
  unfold payAnn
  refine Finset.measurable_sum _ fun c _ => ?_
  have hS : MeasurableSet {q : (Hist d (Option Cell) × E d) × E d |
      R.ans (post π0 R sc t q.1.1) q.1.2 q.2 = some c} :=
    (hans.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
      (measurableSet_singleton (some c))
  exact measurable_cellPay_dens π0 hg (fun p θ => hdp.2.1 p.1 θ) hS w

/-- (L6), the payment of `GameFacts`: over the game, the announced cells pay at most the ledger's budget. -/
theorem ledger_game {Ω : Type} [MeasurableSpace Ω] (hd : 0 < d) {r₀ : ℝ} (hr : 0 < r₀) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Rule d (Option Cell)) (hR : R.Meas (prior d r₀)) {sc : ℝ} (hsc : sc ≠ 0)
    {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {w : ℝ}
    (hw : w ≠ 0) :
    (∀ t < n, Integrable (fun s => payAnn w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
        (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (play pol t s.2.2 (hist (prior d r₀) R sc pol t s)))) (gameLaw (prior d r₀) μ)) ∧
      ∑ t ∈ Finset.range n, ∫ s, payAnn w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
            (play pol t s.2.2 (hist (prior d r₀) R sc pol t s))) ∂gameLaw (prior d r₀) μ ≤
        ledgerBudget d r₀ w := by
  classical
  haveI := isProbabilityMeasure_prior d hr
  haveI := isProbabilityMeasure_gameLaw (prior d r₀) μ
  have hball := prior_ae_mem d r₀
  obtain ⟨pay, hpay⟩ : ∃ pay : ℕ → Sample d Ω → ℝ, ∀ t s,
      pay t s = payAnn w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
        (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (play pol t s.2.2 (hist (prior d r₀) R sc pol t s))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Sample d Ω → ℝ≥0∞, ∀ t s,
      F t s = ENNReal.ofReal (lam w (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s)) -
        d * Real.log (w ^ 2) / 2) := ⟨_, fun _ _ => rfl⟩
  have hpost : ∀ t h, IsProbabilityMeasure (post (prior d r₀) R sc t h) := fun t h =>
    isProbabilityMeasure_post _ R hR sc t h
  have hpay0 : ∀ t s, 0 ≤ pay t s := by
    intro t s
    rw [hpay]
    haveI := hpost t (hist (prior d r₀) R sc pol t s)
    have h2 := integrable_sq_norm_of_ae_mem _ (post_ae_mem _ R sc t (hist (prior d r₀) R sc pol t s) hball)
    exact Finset.sum_nonneg fun c _ => cellPay_nonneg _ h2 hw _
  have hpaym : ∀ t < n, Measurable (pay t) := by
    intro t ht
    have h := (measurable_payAnn (prior d r₀) R hR sc t w).comp
      ((measurable_hist _ R hR sc hpol ht.le).prodMk
        ((measurable_play (α := Option Cell) (hpol t ht)).comp
          ((measurable_snd.comp measurable_snd).prodMk (measurable_hist _ R hR sc hpol ht.le))))
    exact (funext fun s => hpay t s) ▸ h
  -- one round
  have hstep : ∀ t < n, ∫⁻ s, F (t + 1) s ∂gameLaw (prior d r₀) μ +
      ∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ ≤ ∫⁻ s, F t s ∂gameLaw (prior d r₀) μ := by
    intro t ht
    have hdp := dens_props (prior d r₀) R hR sc (t + 1)
    have hΨ : Measurable (fun q : E d × Hist d (Option Cell) × Ω =>
        ENNReal.ofReal (lam w (post (prior d r₀) R sc (t + 1) q.2.1) - d * Real.log (w ^ 2) / 2)) :=
      ENNReal.measurable_ofReal.comp (((measurable_lam_dens (prior d r₀) hdp.1 hdp.2.1 w).comp
        measurable_snd.fst).sub_const _)
    have hexp := hist_succ_expand (prior d r₀) μ R hR hsc hpol ht hΨ
    have hF1 : ∫⁻ s, F (t + 1) s ∂gameLaw (prior d r₀) μ = ∫⁻ s,
        ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (lam w (bayesUpd (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
          (lik (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
              (play pol t s.2.2 (hist (prior d r₀) R sc pol t s)))
            (R.sig (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
              (play pol t s.2.2 (hist (prior d r₀) R sc pol t s))) (noiseVar sc)
            (R.ans (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
              (play pol t s.2.2 (hist (prior d r₀) R sc pol t s)) θ)
            (R.sig (post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s))
              (play pol t s.2.2 (hist (prior d r₀) R sc pol t s)) θ + sc * z))) -
            d * Real.log (w ^ 2) / 2) ∂gaussianReal 0 1
          ∂post (prior d r₀) R sc t (hist (prior d r₀) R sc pol t s) ∂gameLaw (prior d r₀) μ := by
      simp only [hF]
      rw [hexp]
      simp only [post_succ_push (prior d r₀) R hR sc]
    have hpm : Measurable fun s => ENNReal.ofReal (pay t s) := ENNReal.measurable_ofReal.comp (hpaym t ht)
    rw [hF1, ← lintegral_add_right _ hpm]
    refine lintegral_mono fun s => ?_
    set h := hist (prior d r₀) R sc pol t s
    set x := play pol t s.2.2 h
    haveI := hpost t h
    have hrp := measurable_rule_post (prior d r₀) R hR sc t
    have hm : Measurable (fun θ : E d => (h, x, θ)) := by fun_prop
    have hc0 := hrp.1.comp hm
    have hs0 := hrp.2.comp hm
    have hc : Measurable (R.ans (post (prior d r₀) R sc t h) x) := hc0
    have hs : Measurable (R.sig (post (prior d r₀) R sc t h) x) := hs0
    have hround := ledger_round_ann (post (prior d r₀) R sc t h) (post_ae_mem _ R sc t h hball) hc hs hsc hw
    rw [hpay, hF]
    exact hround
  have htel := telescope_lintegral (gameLaw (prior d r₀) μ) F (fun t s => ENNReal.ofReal (pay t s)) n hstep
  -- the ledger at the prior
  have hF0 : ∫⁻ s, F 0 s ∂gameLaw (prior d r₀) μ ≤ ENNReal.ofReal (ledgerBudget d r₀ w) := by
    have hpost0 : ∀ s, post (prior d r₀) R sc 0 (hist (prior d r₀) R sc pol 0 s) = prior d r₀ := fun s => by
      simp [post, dens, withDensity_one]
    simp only [hF, hpost0, lintegral_const, measure_univ, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hl := lam_prior_le hd hr hw
    have hw2 : 0 < w ^ 2 := by positivity
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hlog : Real.log (r₀ ^ 2 / d + w ^ 2) - Real.log (w ^ 2) = Real.log (1 + r₀ ^ 2 / (d * w ^ 2)) := by
      rw [← Real.log_div (by positivity) hw2.ne']
      congr 1
      field_simp
      ring
    unfold ledgerBudget
    nlinarith [hlog]
  have hbudget0 : 0 ≤ ledgerBudget d r₀ w := by
    unfold ledgerBudget
    have : 1 ≤ 1 + r₀ ^ 2 / (d * w ^ 2) := le_add_of_nonneg_right (by positivity)
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  have hsum_le : ∑ t ∈ Finset.range n, ∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ ≤
      ENNReal.ofReal (ledgerBudget d r₀ w) :=
    le_trans (le_trans le_self_add htel) hF0
  have hfin : ∀ t ∈ Finset.range n, ∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ ≠ ∞ := fun t ht =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans ((Finset.single_le_sum (f := fun t => ∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ)
        (fun _ _ => bot_le) ht)) hsum_le)
  have hint : ∀ t < n, Integrable (pay t) (gameLaw (prior d r₀) μ) := fun t ht =>
    ⟨(hpaym t ht).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpay0 t))).2
      (lt_top_iff_ne_top.2 (hfin t (Finset.mem_range.2 ht)))⟩
  refine ⟨fun t ht => (funext fun s => (hpay t s).symm) ▸ hint t ht, ?_⟩
  simp only [← hpay]
  calc ∑ t ∈ Finset.range n, ∫ s, pay t s ∂gameLaw (prior d r₀) μ
      = ∑ t ∈ Finset.range n, (∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ).toReal :=
        Finset.sum_congr rfl fun t ht => integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hpay0 t))
          (hpaym t (Finset.mem_range.1 ht)).aestronglyMeasurable
    _ = (∑ t ∈ Finset.range n, ∫⁻ s, ENNReal.ofReal (pay t s) ∂gameLaw (prior d r₀) μ).toReal :=
        (ENNReal.toReal_sum hfin).symm
    _ ≤ (ENNReal.ofReal (ledgerBudget d r₀ w)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum_le
    _ = ledgerBudget d r₀ w := ENNReal.toReal_ofReal hbudget0

end AdversarialBco.Lower
