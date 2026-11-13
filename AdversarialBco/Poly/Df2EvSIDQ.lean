/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSILQ

@[expose] public section

/-!
# The event DQ: levels and arithmetic

DF Lemma DQ on setting (E) bounds `μ(G ∩ ¬DQ)` by `δ_e/8`: for a point `c` of a net of `B_R` at scale `δ⁴`, the
increments `Y_s phiH_s - hᵀ s''_s(μ_s) h = hᵀ (ŝ''_s - s''_s(μ_s)) h` with `h = c - μ_s` go to `lemmaU_setE` with the
direction `phiH (· - μ)`; up to `τ` their second moments sum to at most `VD` and they are at most `RD`, and
`|vᵀ (ŝ'' - s'') v| ≤ KD |v|²`. This file holds the levels (`tailD`, `VD`, `RD`, `KD`), the quadratic forms, the
growth of the direction (`phiH_growth`) and the arithmetic of the lemma (`dq_arith`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-! ## The levels -/

/-- The tail term of Lemma TR at `T = (16x)²`. -/
noncomputable def tailD (d n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (WbL d n δ) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * xq d n δ) ^ 2) / 4))

/-- The variance level of DQ. -/
noncomputable def VD (d n : ℕ) (δ : ℝ) : ℝ :=
  ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 *
    (qL d n δ ^ 2 * ((16 * xq d n δ) ^ 2 * (9 * n) + n * tailD d n δ))

/-- The range level of DQ. -/
noncomputable def RD (d n : ℕ) (δ : ℝ) : ℝ :=
  (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) * ((df2oPar d n δ).lam * (df2oPar d n δ).k0) *
      (qL d n δ * (32 / 9 * d * xq d n δ + 1)) +
    (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
      Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ

/-- The bound of `|vᵀ (ŝ''_s - s''_s(μ_s)) v|/|v|²`. -/
noncomputable def KD (d n : ℕ) (δ : ℝ) : ℝ :=
  (df2oPar d n δ).lam * (df2oPar d n δ).k0 * ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) *
      ((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) +
    (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
      Real.sqrt (d / (df2oPar d n δ).δe)

theorem sig2_eq (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).sig2 = 1 / (8 * (36 * xq d n δ)) := rfl

/-! ## Quadratic forms -/

theorem sqrt_dot_add_le (a b : Fin d → ℝ) :
    Real.sqrt ((a + b) ⬝ᵥ (a + b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  rw [← norm_toLp, ← norm_toLp, ← norm_toLp, WithLp.toLp_add]
  exact norm_add_le _ _

theorem df2Sq_sub (A B : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    df2Sq (A - B) v = df2Sq A v - df2Sq B v := by
  unfold df2Sq; rw [sub_mulVec, dotProduct_sub]

/-- For a symmetric `M`, `aᵀ M a - bᵀ M b = (a - b)ᵀ M (a + b)`. -/
theorem sq_sub_sq (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (a b : Fin d → ℝ) :
    df2Sq M a - df2Sq M b = (a - b) ⬝ᵥ (M *ᵥ (a + b)) := by
  have hs : b ⬝ᵥ (M *ᵥ a) = a ⬝ᵥ (M *ᵥ b) := by
    rw [dotProduct_mulVec, ← hM, vecMul_transpose, hM, dotProduct_comm]
  unfold df2Sq
  rw [mulVec_add, dotProduct_add, sub_dotProduct, sub_dotProduct, hs]
  ring

/-- `vᵀ (c (u uᵀ - P)) v = c ((u ⬝ v)² - vᵀ P v)`. -/
theorem df2Sq_rank_one (k : ℝ) (u : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    df2Sq (k • (vecMulVec u u - P)) v = k * ((u ⬝ᵥ v) ^ 2 - df2Sq P v) := by
  unfold df2Sq
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, sub_mulVec, dotProduct_sub, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, smul_eq_mul, dotProduct_comm v u]
  ring

theorem KD_nonneg {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 ≤ KD d n δ := by
  have hx := xq_ge hd hn rows
  have hde := rows.pos_de
  have hl0 := rows.pos_lam
  have hl1 : 0 < 1 - (df2oPar d n δ).lam := by have := rows.lam_le; linarith
  have he := rows.pos_eps
  have hk : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_def]; positivity
  have hLe : 0 ≤ (df2oPar d n δ).Le := by rw [le_eq]; linarith
  have hxq : 0 ≤ xq d n δ := by linarith
  unfold KD
  positivity

/-! ## The growth of the direction -/

/-- The growth constant of `phiH (c - ·)` on the bound condition. -/
noncomputable def KphiH (d n : ℕ) (δ M : ℝ) (y : Fin d → ℝ) : ℝ :=
  (df2oPar d n δ).lam * (df2oPar d n δ).k0 *
    ((M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M)) ^ 2 + Real.sqrt M * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) ^ 2)

theorem KphiH_nonneg {n : ℕ} {δ M : ℝ} (hl0 : 0 ≤ (df2oPar d n δ).lam) (hk0 : 0 ≤ (df2oPar d n δ).k0)
    (y : Fin d → ℝ) : 0 ≤ KphiH d n δ M y := by
  unfold KphiH; positivity

theorem phiH_growth {n : ℕ} {δ M : ℝ} (hM : 0 ≤ M) (hl0 : 0 ≤ (df2oPar d n δ).lam) (hk0 : 0 ≤ (df2oPar d n δ).k0)
    (y : Fin d → ℝ) {st : Df2St d} (hst : stB M st) (z : Fin d → ℝ) :
    |phiH n δ (fun st => y - st.mu) st z| ≤ KphiH d n δ M y * (1 + ‖z‖) ^ 2 := by
  have hA := bdSet_apply hst.2.1 hM z
  have hP := bdSet_apply hst.2.2 hM (st.A *ᵥ z)
  have hz := sqrt_dot_le z
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt hst.1
  have hh := sqrt_dot_sub_le y st.mu
  have hsM := Real.sqrt_nonneg M
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  set a := M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) with ha
  set r := Real.sqrt (y ⬝ᵥ y) + Real.sqrt M with hr
  have hr0 : 0 ≤ r := by positivity
  have hhr : Real.sqrt ((y - st.mu) ⬝ᵥ (y - st.mu)) ≤ r := hh.trans (by linarith)
  have hu : Real.sqrt ((st.P *ᵥ (st.A *ᵥ z)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ z))) ≤ M * (Real.sqrt d * ‖z‖) := by
    calc _ ≤ Real.sqrt M * (Real.sqrt M * Real.sqrt (z ⬝ᵥ z)) := hP.trans (mul_le_mul_of_nonneg_left hA hsM)
      _ = M * Real.sqrt (z ⬝ᵥ z) := by rw [← mul_assoc, hMM]
      _ ≤ M * (Real.sqrt d * ‖z‖) := mul_le_mul_of_nonneg_left hz hM
  have hl : |lin st (y - st.mu) z| ≤ a * ‖z‖ := by
    unfold lin
    refine (abs_dot_le _ _).trans ((mul_le_mul hu hhr (Real.sqrt_nonneg _) (by positivity)).trans (le_of_eq ?_))
    rw [ha, hr]; ring
  have hq : |df2Sq st.P (y - st.mu)| ≤ Real.sqrt M * r ^ 2 := by
    unfold df2Sq
    have h1 := bdSet_apply hst.2.2 hM (y - st.mu)
    calc _ ≤ Real.sqrt ((y - st.mu) ⬝ᵥ (y - st.mu)) *
          Real.sqrt ((st.P *ᵥ (y - st.mu)) ⬝ᵥ (st.P *ᵥ (y - st.mu))) := abs_dot_le _ _
      _ ≤ r * (Real.sqrt M * r) :=
        mul_le_mul hhr (h1.trans (mul_le_mul_of_nonneg_left hhr hsM)) (Real.sqrt_nonneg _) hr0
      _ = Real.sqrt M * r ^ 2 := by ring
  have hz0 := norm_nonneg z
  have hl2 : lin st (y - st.mu) z ^ 2 ≤ a ^ 2 * ‖z‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have hzz : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ hz0 (by linarith) 2
  have h1z : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have hlk : 0 ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 := mul_nonneg hl0 hk0
  unfold phiH KphiH
  rw [← ha, ← hr]
  show |(df2oPar d n δ).lam * (df2oPar d n δ).k0 * (lin st (y - st.mu) z ^ 2 - df2Sq st.P (y - st.mu))| ≤
    (df2oPar d n δ).lam * (df2oPar d n δ).k0 * (a ^ 2 + Real.sqrt M * r ^ 2) * (1 + ‖z‖) ^ 2
  rw [abs_mul, abs_of_nonneg hlk, mul_assoc _ (a ^ 2 + _)]
  refine mul_le_mul_of_nonneg_left ?_ hlk
  have hsq0 := sq_nonneg (lin st (y - st.mu) z)
  have hab : |lin st (y - st.mu) z ^ 2 - df2Sq st.P (y - st.mu)| ≤
      lin st (y - st.mu) z ^ 2 + |df2Sq st.P (y - st.mu)| := by
    have := abs_sub (lin st (y - st.mu) z ^ 2) (df2Sq st.P (y - st.mu))
    rwa [abs_of_nonneg hsq0] at this
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
  have hmr : 0 ≤ Real.sqrt M * r ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hzz ha2, mul_le_mul_of_nonneg_left h1z hmr]


/-! ## The arithmetic -/

theorem qL_pos {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 < qL d n δ := by
  have hx := xq_ge hd hn rows
  have hde := rows.pos_de
  have hl := rows.pos_lam
  unfold qL
  rw [le_eq]
  have : 0 < 36 * xq d n δ := by linarith
  positivity

theorem RD_pos {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 < RD d n δ := by
  have hx := xq_ge hd hn rows
  have hq := qL_pos hd hn rows
  have hl0 := rows.pos_lam
  have hl1 : 0 < 1 - (df2oPar d n δ).lam := by have := rows.lam_le; linarith
  have he := rows.pos_eps
  have hk : 0 < (df2oPar d n δ).k0 := by rw [k0_def]; positivity
  have hLe : 0 < (df2oPar d n δ).Le := by rw [le_eq]; linarith
  have h1 : 0 < (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) * ((df2oPar d n δ).lam * (df2oPar d n δ).k0) *
      (qL d n δ * (32 / 9 * d * xq d n δ + 1)) := by
    have : 0 < 32 / 9 * (d : ℝ) * xq d n δ + 1 := by positivity
    positivity
  have h2 : 0 ≤ (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
      Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ := by positivity
  unfold RD
  linarith

theorem VD_nonneg (d n : ℕ) (δ : ℝ) : 0 ≤ VD d n δ := by
  have ht : 0 ≤ tailD d n δ := by unfold tailD; positivity
  unfold VD
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (add_nonneg (by positivity) (by positivity)))

/-- The arithmetic of DQ: Freedman's level at `VD`, `RD`, a net of `B_R` at scale `δ⁴` and `δ' = δ_e/8`, plus the
discretization, is at most `B_n/(L λ²)`. -/
theorem dq_arith {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) (Cc : ℝ)
    (hC1 : 1 ≤ Cc) (hC : Cc ≤ (1 + 2 * (df2oPar d n δ).R / (df2oPar d n δ).δe ^ 4) ^ d) :
    3 * Real.sqrt (VD d n δ * Real.log (4 * (n * Cc) * max ((RD d n δ)⁻¹ * RD d n δ)
        ((RD d n δ)⁻¹ * Real.sqrt (VD d n δ)) / ((df2oPar d n δ).δe / 8))) +
      2 * RD d n δ * Real.log (4 * (n * Cc) * max ((RD d n δ)⁻¹ * RD d n δ)
        ((RD d n δ)⁻¹ * Real.sqrt (VD d n δ)) / ((df2oPar d n δ).δe / 8)) +
      n * KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) ≤
      df2Bn (df2oPar d n δ) d n / ((df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) := by
  have hRD := RD_pos hd hn rows
  have hV0 := VD_nonneg d n δ
  have hx := xq_ge hd hn rows
  have hl0 := rows.pos_lam
  have hl2 := rows.lam_le
  have ht0 : 0 ≤ tailD d n δ := by unfold tailD; positivity
  have ht1 : tailD d n δ ≤ 1 := dq_tail d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu
  have hV : VD d n δ ≤ n / (df2oPar d n δ).lam ^ 2 := by
    have h := dq_V d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (tailD d n δ) ht0 ht1
    unfold VD qL; rw [le_eq]; exact h
  have hRDe : RD d n δ = 36 * xq d n δ / (2 * (df2oPar d n δ).eps) *
        ((df2oPar d n δ).lam * (df2oPar d n δ).k0) *
        (((1 + (df2oPar d n δ).δe) / (2 * (36 * xq d n δ) * (df2oPar d n δ).lam ^ 2) +
          2 * (df2oPar d n δ).δe ^ 6) * (32 / 9 * d * xq d n δ + 1)) +
      (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (2 * d * (1 / (8 * (36 * xq d n δ)))) *
        ((1 + (df2oPar d n δ).δe) / (2 * (36 * xq d n δ) * (df2oPar d n δ).lam ^ 2) +
          2 * (df2oPar d n δ).δe ^ 6) := by
    unfold RD qL; rw [sig2_eq, le_eq]
  have hsV : Real.sqrt (VD d n δ) ≤ Real.sqrt n * RD d n δ := by
    rw [hRDe]
    exact dq_sqrtV d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (VD d n δ) hV0 hV
  have hn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  set Mx := max ((RD d n δ)⁻¹ * RD d n δ) ((RD d n δ)⁻¹ * Real.sqrt (VD d n δ)) with hMx
  have hM1 : 1 ≤ Mx := by rw [hMx, inv_mul_cancel₀ hRD.ne']; exact le_max_left _ _
  have hMn : Mx ≤ Real.sqrt n := by
    rw [hMx, inv_mul_cancel₀ hRD.ne']
    refine max_le hn1 ?_
    rw [inv_mul_le_iff₀ hRD, mul_comm]
    exact hsV
  have hcard := lq_card d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu Cc hC1 hC
  have hlog := ev_log d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu Cc Mx 8 (by norm_num) (by norm_num) hC1 hcard hM1 hMn
  have hdev := dq_dev d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (VD d n δ) hV0 hV
  rw [← hRDe] at hdev
  have hdisc : n * KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) ≤ 1 := by
    have h := dq_disc d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu
    unfold KD; rw [le_eq]; exact h
  have hB : df2Bn (df2oPar d n δ) d n / ((df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) =
      36 * xq d n δ / (df2oPar d n δ).lam + 36 * xq d n δ / (df2oPar d n δ).lam *
        (Real.sqrt (10 * d * n) + (d : ℝ) ^ 2 * (36 * xq d n δ) / (df2oPar d n δ).eps) := by
    have hL : 0 < 36 * xq d n δ := by linarith
    unfold df2Bn; rw [le_eq]
    field_simp
    ring
  have hL1 : 1 ≤ 36 * xq d n δ / (df2oPar d n δ).lam := by
    rw [le_div_iff₀ hl0]; linarith
  have h1 : Real.sqrt (VD d n δ * Real.log (4 * (n * Cc) * Mx / ((df2oPar d n δ).δe / 8))) ≤
      Real.sqrt (VD d n δ * (7 * d * xq d n δ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hV0)
  have h2 : RD d n δ * Real.log (4 * (n * Cc) * Mx / ((df2oPar d n δ).δe / 8)) ≤ RD d n δ * (7 * d * xq d n δ) :=
    mul_le_mul_of_nonneg_left hlog hRD.le
  rw [hB]
  nlinarith


end AdversarialBco.Poly.EvSI
