/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIMean
public import AdversarialBco.Poly.Df2EvSIGauss
public import AdversarialBco.Poly.Df2EvVSum

@[expose] public section

/-!
# The states up to the stopping time, for the events LQ, S-DF and DQ

On `DetBase` and at a round `s ≤ τ`: the state satisfies the bound condition `stB (M0 p)` of the increments
(`|μ| ≤ R`, `|A w|² ≤ 2σ² |w|²`, `|P w|² ≤ δ⁻² |w|²`), `δ I ≤ P ≤ I/δ`, `⟨P A z, h⟩ = ⟨z, Aᵀ P h⟩` with
`|Aᵀ P h|² = hᵀ P h`; on the event G, `|Y_s| ≤ L/(2ε)` and `|ξ_s|² ≤ (32/9) d log(1/δ)`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-! ## Matrices -/

theorem transpose_of_psd {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) : Pᵀ = P := by
  have h := hP.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

theorem quad_le_of_psd {P : Matrix (Fin d) (Fin d) ℝ} {a : ℝ}
    (h : (a • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) (w : Fin d → ℝ) : df2Sq P w ≤ a * (w ⬝ᵥ w) := by
  have := sq_le_of_psd h w
  rwa [sq_smul, sq_one] at this

theorem quad_ge_of_psd {P : Matrix (Fin d) (Fin d) ℝ} {a : ℝ}
    (h : (P - a • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) (w : Fin d → ℝ) : a * (w ⬝ᵥ w) ≤ df2Sq P w := by
  have := sq_le_of_psd h w
  rwa [sq_smul, sq_one] at this

/-- `0 ≤ P ≤ a I` gives `|P w|² ≤ a² |w|²`. -/
theorem P_sq_le {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (h : (a • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) (w : Fin d → ℝ) :
    (P *ᵥ w) ⬝ᵥ (P *ᵥ w) ≤ a ^ 2 * (w ⬝ᵥ w) := by
  have hc := sq_cauchy P hP w (P *ᵥ w)
  have hT := transpose_of_psd hP
  have hsym : w ⬝ᵥ (P *ᵥ (P *ᵥ w)) = (P *ᵥ w) ⬝ᵥ (P *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT]
  rw [hsym] at hc
  set N := (P *ᵥ w) ⬝ᵥ (P *ᵥ w)
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have h1 := quad_le_of_psd h w
  have h2 : df2Sq P (P *ᵥ w) ≤ a * N := quad_le_of_psd h _
  have hw := sq_nonneg_of_psd hP w
  have hww : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rcases hN.lt_or_eq with hpos | hzero
  · have h3 : N ^ 2 ≤ (a * (w ⬝ᵥ w)) * (a * N) :=
      hc.trans (mul_le_mul h1 h2 (sq_nonneg_of_psd hP _) (by positivity))
    have h4 : N * N ≤ (a ^ 2 * (w ⬝ᵥ w)) * N := by nlinarith
    exact le_of_mul_le_mul_right h4 hpos
  · rw [← hzero]; positivity

/-- `⟨P A z, h⟩ = ⟨z, Aᵀ P h⟩` for `P` symmetric. -/
theorem lin_eq_dot (st : Df2St d) (hT : st.Pᵀ = st.P) (h z : Fin d → ℝ) :
    lin st h z = z ⬝ᵥ (st.Aᵀ *ᵥ (st.P *ᵥ h)) := by
  unfold lin
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct_comm]

theorem dot_transpose_sq (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) = v ⬝ᵥ ((A * Aᵀ) *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec v A (Aᵀ *ᵥ v), ← mulVec_transpose]

/-- `|Aᵀ P h|² = hᵀ P h` when `A Aᵀ = S` and `S P = 1`. -/
theorem dir_sq (st : Df2St d) (hAA : st.A * st.Aᵀ = st.S) (hSP : st.S * st.P = 1)
    (h : Fin d → ℝ) : (st.Aᵀ *ᵥ (st.P *ᵥ h)) ⬝ᵥ (st.Aᵀ *ᵥ (st.P *ᵥ h)) = df2Sq st.P h := by
  unfold df2Sq
  rw [dot_transpose_sq, hAA, mulVec_mulVec, hSP, one_mulVec, dotProduct_comm]

/-! ## The bound of the states -/

/-- The bound condition of the increments at the parameters `p`: `|μ|² ≤ R²` and the norms of `A`, `P` below
`1/δ`. -/
noncomputable def M0 (p : Df2OPar) : ℝ := p.R ^ 2 + p.δe⁻¹ ^ 2 + 1

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem linv_of (_H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) : EvGY.LInv c π s :=
  ⟨hI.run, hI.pd, hI.SP, hI.AA, hI.pbl, fun v => sq_le_of_psd hI.pb0 v, hI.mu⟩

theorem lpar_of (H : DetBase c δ π m) : EvGY.LPar c π :=
  ⟨H.rows.pos_sig2, H.rows.pos_de, H.kap_pos.le, by linarith [H.heps],
    H.body.2.2.1 (Metric.mem_closedBall_self zero_le_one), rfl⟩

/-- `P ≤ I/δ`. -/
theorem P_upper (_H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) :
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (c.st π s).P).PosSemidef :=
  psd_trans hI.pb2 hI.pbh

/-- `δ I ≤ P`. -/
theorem P_lower (_H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) :
    ((c.st π s).P - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
  psd_trans hI.pbl hI.pbd

theorem P_symm {s : ℕ} (hI : c.StInv π s) : (c.st π s).Pᵀ = (c.st π s).P :=
  transpose_of_psd hI.pd.posSemidef

theorem P_mul_S {s : ℕ} (hI : c.StInv π s) : (c.st π s).P * ((c.st π s).A * (c.st π s).Aᵀ) = 1 := by
  rw [hI.AA]; exact mul_eq_one_comm.1 hI.SP

/-- `|μ|² ≤ R²`. -/
theorem mu_sq_le (H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) :
    (c.st π s).mu ⬝ᵥ (c.st π s).mu ≤ c.p.R ^ 2 := by
  have hm := hI.mu
  have hR := H.body.2.2.2.1 hm
  rw [Metric.mem_closedBall, dist_zero_right, WithLp.toLp_smul, norm_smul, norm_toLp] at hR
  have hε0 := H.rows.pos_eps
  have hε1 : c.p.eps ≤ 1 / 2 := H.heps
  have h1 : 0 < 1 - c.p.eps := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 h1)] at hR
  have h2 : Real.sqrt ((c.st π s).mu ⬝ᵥ (c.st π s).mu) ≤ c.p.R := by
    have h3 : Real.sqrt ((c.st π s).mu ⬝ᵥ (c.st π s).mu) ≤ (1 - c.p.eps) * c.p.R := by
      rw [inv_mul_le_iff₀ h1] at hR; exact hR
    have hR0 : 0 ≤ c.p.R := by linarith [H.rows.one_le_R]
    nlinarith
  have h0 := dot_self_nonneg' (c.st π s).mu
  calc _ = Real.sqrt ((c.st π s).mu ⬝ᵥ (c.st π s).mu) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ c.p.R ^ 2 := by gcongr

/-- `|A w|² ≤ |w|²` (from `2σ² ≤ 1`). -/
theorem A_sq_le (H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) (w : Fin d → ℝ) :
    ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) ≤ w ⬝ᵥ w := by
  have h := EvGY.LInv.A_sq_le c π (lpar_of H) (linv_of H hI) w
  have hr := H.rows.r2
  have hw := dot_self_nonneg' w
  nlinarith

theorem P_sq_le' (H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) (w : Fin d → ℝ) :
    ((c.st π s).P *ᵥ w) ⬝ᵥ ((c.st π s).P *ᵥ w) ≤ c.p.δe⁻¹ ^ 2 * (w ⬝ᵥ w) :=
  P_sq_le hI.pd.posSemidef (inv_nonneg.2 H.rows.pos_de.le) (P_upper H hI) w

/-- The bound condition holds at the states up to `τ`. -/
theorem stB_of (H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) : stB (M0 c.p) (c.st π s) := by
  have hR := mu_sq_le H hI
  have hd := sq_nonneg c.p.δe⁻¹
  have hR2 := sq_nonneg c.p.R
  refine ⟨by unfold M0; linarith, fun w => ?_, fun w => ?_⟩
  · have := A_sq_le H hI w
    have hw := dot_self_nonneg' w
    have : w ⬝ᵥ w ≤ M0 c.p * (w ⬝ᵥ w) := by
      have h1 : 1 ≤ M0 c.p := by unfold M0; linarith
      nlinarith
    linarith
  · have := P_sq_le' H hI w
    have hw := dot_self_nonneg' w
    have : c.p.δe⁻¹ ^ 2 * (w ⬝ᵥ w) ≤ M0 c.p * (w ⬝ᵥ w) := by
      apply mul_le_mul_of_nonneg_right _ hw; unfold M0; linarith
    linarith

theorem M0_nonneg (p : Df2OPar) : 0 ≤ M0 p := by unfold M0; positivity

/-! ## The event G on the path -/

/-- The play is in `K~`. -/
theorem play_mem_Kt (H : DetBase c δ π m) (s : ℕ) : WithLp.toLp 2 (c.play π s) ∈ c.Kt := by
  obtain ⟨hconv, hcl, hball, -, -⟩ := H.body
  have hε0 := H.rows.pos_eps
  have hε1 : c.p.eps < 1 := by have := H.heps; linarith
  have h := play_mem c.Kt c.p.eps hconv hcl hball hε0 hε1 (WithLp.toLp 2 (c.X π s))
  have e1 : WithLp.toLp 2 (c.play π s) = (c.pip π s)⁻¹ • WithLp.toLp 2 (c.X π s) := WithLp.toLp_smul 2 _ _
  have h0 : (0 : E d) ∈ c.Kt := hball (Metric.mem_closedBall_self zero_le_one)
  have := hconv.smul_mem_of_zero_mem h0 h (t := 1 - c.p.eps) ⟨by linarith, by linarith⟩
  rw [smul_smul, mul_inv_cancel₀ (by linarith : (1 - c.p.eps) ≠ 0), one_smul] at this
  rw [e1]; exact this

/-- On G: `|Y_s| ≤ L/(2ε)`. -/
theorem ybd_G (H : DetBase c δ π m) (hG : c.EvG π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    |c.Y π s| ≤ c.p.Le / (2 * c.p.eps) := by
  obtain ⟨he, hg, -⟩ := hG s hs
  have hgv := (H.adm s (H.le_tau_lt hs)).2 _ (play_mem_Kt H s)
  refine ybound (c.pip π s) (gauge c.Kt (WithLp.toLp 2 (c.X π s))) (π.g s (WithLp.toLp 2 (c.play π s))) (π.e s)
    c.p.Le (df2Lg c.p c.n) c.p.eps H.rows.pos_eps H.heps rfl (gauge_nonneg _) hg hgv.1 hgv.2 he ?_ ?_ H.one_le_Le
  · have := H.rows.clg; rw [H.Le_eq]; linarith
  · have := H.rows.r4; simp only [df2C0] at this; exact this

/-- On G: `|ξ_s|² ≤ (32/9) d log(1/δ_e)`. -/
theorem xibd_G (H : DetBase c δ π m) (hG : c.EvG π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * Real.log (1 / c.p.δe) := by
  obtain ⟨-, -, hx⟩ := hG s hs
  have := H.rows.clg
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc _ ≤ 8 * d / 3 * df2Lg c.p c.n := hx
    _ ≤ 8 * d / 3 * (4 / 3 * Real.log (1 / c.p.δe)) := by gcongr
    _ = _ := by ring

end AdversarialBco.Poly.EvSI
