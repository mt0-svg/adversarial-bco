/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSILQ

@[expose] public section

/-!
# The event DQ

DF Lemma DQ on setting (E): `μ(G ∩ ¬DQ) ≤ δ_e/8`. For a point `c` of a net of `B_R` at scale `δ⁴`, the increments
`Y_s phiH_s - hᵀ s''_s(μ_s) h = hᵀ (ŝ''_s - s''_s(μ_s)) h` with `h = c - μ_s` are those of `lemmaU_setE` with the
direction `phiH (· - μ)`; up to `τ` and for `y ∈ S_t` within `δ⁴` of `c`, their second moments sum to at most `VD`,
they are at most `RD`, and `G_t(y)` and `G_t(c)` differ by at most `n KD δ⁴ 4R`, since `|vᵀ (ŝ'' - s'') v| ≤ KD |v|²`.
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

/-! ## On the path -/

section path

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ApFun d} {π : Df2Path d} {m : ℕ}

/-- The second moments of the increments at `c` sum to at most `VD`. -/
theorem dq_var (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAt d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
      phiH n δ (fun st => c - st.mu) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤ VD d n δ := by
  have hx := xq_pos H
  set T := (16 * xq d n δ) ^ 2 with hTdef
  have hT : 1 ≤ T := by rw [hTdef]; nlinarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eq H]; positivity
  have hq : 0 ≤ qL d n δ := qL_nonneg H.hd H.hn H.rows
  set τ0 := Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
      phiH n δ (fun st => c - st.mu) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (qL d n δ ^ 2 *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) + Real.sqrt (WbL d n δ) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_H H (hs'.trans ht) (fun st => c - st.mu) T hT
    have hqs := lq_q H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) :=
      integral_nonneg fun z => yR_nonneg n δ Kt (π.g s) _ z
    have hY2 := intY2_le H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) ≤
        Real.sqrt (WbL d n δ) := Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) * τ0 := by
      have : 0 ≤ T := by linarith
      positivity
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef
      (c - ((df2CtxAt d n δ Kt ap).st π s).mu)
    have hq2 : df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (c - ((df2CtxAt d n δ Kt ap).st π s).mu) ^ 2 ≤
        qL d n δ ^ 2 := pow_le_pow_left₀ hP0 hqs 2
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    refine mul_le_mul hq2 ?_ hinner (sq_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hτ0n)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsum := sumY_le H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  have hW : 0 ≤ Real.sqrt (WbL d n δ) * τ0 := by positivity
  unfold VD tailD
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (sq_nonneg _)
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) ≤
      T * (9 * n) := mul_le_mul_of_nonneg_left hsum (by linarith)
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (WbL d n δ) * τ0) ≤ n * (Real.sqrt (WbL d n δ) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

theorem inv_S_eq (_H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hI : (df2CtxAt d n δ Kt ap).StInv π s) :
    (((df2CtxAt d n δ Kt ap).st π s).A * ((df2CtxAt d n δ Kt ap).st π s).Aᵀ)⁻¹ =
      ((df2CtxAt d n δ Kt ap).st π s).P := by
  rw [hI.AA]; exact Matrix.inv_eq_right_inv hI.SP

/-- The increments at `c` are at most `RD` up to `τ`, on G. -/
theorem dq_range (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) (hG : (df2CtxAt d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) {c : Fin d → ℝ}
    (hq : df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (c - ((df2CtxAt d n δ Kt ap).st π s).mu) ≤ qL d n δ) :
    |(df2CtxAt d n δ Kt ap).Y π s * phiH n δ (fun st => c - st.mu) ((df2CtxAt d n δ Kt ap).st π s) (π.xi s) -
      df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) (c - ((df2CtxAt d n δ Kt ap).st π s).mu)| ≤ RD d n δ := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_lt H
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eq H]; positivity
  set st := (df2CtxAt d n δ Kt ap).st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (c - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (c - st.mu) := dir_sq st hI.AA hI.SP _
  have hP0 : 0 ≤ df2Sq st.P (c - st.mu) := sq_nonneg_of_psd hI.pd.posSemidef _
  have hY : |(df2CtxAt d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hlin : lin st (c - st.mu) (π.xi s) = π.xi s ⬝ᵥ b := by
    rw [lin_eq_dot st (P_symm hI), ← hb]
  have hl2 : lin st (c - st.mu) (π.xi s) ^ 2 ≤ 32 / 9 * d * xq d n δ * qL d n δ := by
    rw [hlin]
    have h1 := abs_dot_le (π.xi s) b
    have h2 : |π.xi s ⬝ᵥ b| ^ 2 ≤ (Real.sqrt (π.xi s ⬝ᵥ π.xi s) * Real.sqrt (b ⬝ᵥ b)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (dot_self_nonneg' _), Real.sq_sqrt (dot_self_nonneg' _), hbb] at h2
    exact h2.trans (mul_le_mul hξ hq hP0 (by have := xq_pos H; positivity))
  have hph : |phiH n δ (fun st => c - st.mu) st (π.xi s)| ≤
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 * (qL d n δ * (32 / 9 * d * xq d n δ + 1)) := by
    unfold phiH
    have hlk : 0 ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 := mul_nonneg hl0.le hk0
    rw [abs_mul, abs_of_nonneg hlk]
    refine mul_le_mul_of_nonneg_left ?_ hlk
    have hsq := sq_nonneg (lin st (c - st.mu) (π.xi s))
    rw [abs_le]; constructor <;> nlinarith
  have hH : |df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) (c - st.mu)| ≤
      (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ := by
    have h := hsi.hess2 (WithLp.toLp 2 st.mu) (c - st.mu)
    rw [inv_S_eq H hI] at h
    have hK : 0 ≤ (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (2 * d * (df2oPar d n δ).sig2) := by
      have : 0 < 1 - (df2oPar d n δ).lam := by linarith
      positivity
    exact h.trans (mul_le_mul_of_nonneg_left hq hK)
  have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
  unfold RD
  calc _ ≤ |(df2CtxAt d n δ Kt ap).Y π s * phiH n δ (fun st => c - st.mu) st (π.xi s)| +
        |df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) (c - st.mu)| := abs_sub _ _
    _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) *
          ((df2oPar d n δ).lam * (df2oPar d n δ).k0 * (qL d n δ * (32 / 9 * d * xq d n δ + 1))) +
        (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
          Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hY hph (abs_nonneg _) hLe) hH
    _ = _ := by ring

/-- `|vᵀ (ŝ''_s - s''_s(μ_s)) v| ≤ KD |v|²` up to `τ`, on G. -/
theorem dq_quad (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) (hG : (df2CtxAt d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (v : Fin d → ℝ) :
    |v ⬝ᵥ (((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s) *ᵥ v)| ≤ KD d n δ * (v ⬝ᵥ v) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_lt H
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eq H]; positivity
  have hx := xq_pos H
  set st := (df2CtxAt d n δ Kt ap).st π s with hstdef
  have hY : |(df2CtxAt d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hvv := dot_self_nonneg' v
  have hu : (df2CtxAt d n δ Kt ap).u π s ⬝ᵥ (df2CtxAt d n δ Kt ap).u π s ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe :=
    (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (P_upper H hI)).trans
      (div_le_div_of_nonneg_right hξ hde.le)
  have huv : ((df2CtxAt d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe * (v ⬝ᵥ v) := by
    have h1 := abs_dot_le ((df2CtxAt d n δ Kt ap).u π s) v
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (dot_self_nonneg' _), Real.sq_sqrt hvv] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hu hvv)
  have hPv : df2Sq st.P v ≤ (df2oPar d n δ).δe⁻¹ * (v ⬝ᵥ v) := quad_le_of_psd (P_upper H hI) v
  have hP0 : 0 ≤ df2Sq st.P v := sq_nonneg_of_psd hI.pd.posSemidef v
  have hshh : |df2Sq ((df2CtxAt d n δ Kt ap).shh π s) v| ≤
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 * ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) *
        ((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v) := by
    change |df2Sq (((df2oPar d n δ).lam * (df2oPar d n δ).k0 * (df2CtxAt d n δ Kt ap).Y π s) •
      (vecMulVec ((df2CtxAt d n δ Kt ap).u π s) ((df2CtxAt d n δ Kt ap).u π s) - st.P)) v| ≤ _
    rw [df2Sq_rank_one, abs_mul, abs_mul, abs_mul, abs_of_pos hl0, abs_of_nonneg hk0]
    have hsq := sq_nonneg ((df2CtxAt d n δ Kt ap).u π s ⬝ᵥ v)
    have hab : |((df2CtxAt d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 - df2Sq st.P v| ≤
        ((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v) := by
      rw [abs_le]; constructor <;> nlinarith
    have hlk : 0 ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 := mul_nonneg hl0.le hk0
    calc _ = (df2oPar d n δ).lam * (df2oPar d n δ).k0 * |(df2CtxAt d n δ Kt ap).Y π s| *
          |((df2CtxAt d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 - df2Sq st.P v| := by ring
      _ ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 * ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) *
          (((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hY hlk) hab (abs_nonneg _) (mul_nonneg hlk (by positivity))
      _ = _ := by ring
  have hH : |df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) v| ≤
      (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (d / (df2oPar d n δ).δe) * (v ⬝ᵥ v) := hsi.hess1 (WithLp.toLp 2 st.mu) v
  have e1 : v ⬝ᵥ (((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s) *ᵥ v) =
      df2Sq ((df2CtxAt d n δ Kt ap).shh π s) v - df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) v :=
    df2Sq_sub _ _ v
  rw [e1]
  unfold KD
  calc _ ≤ |df2Sq ((df2CtxAt d n δ Kt ap).shh π s) v| + |df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) v| := abs_sub _ _
    _ ≤ _ := add_le_add hshh hH
    _ = _ := by ring

/-- `ŝ''_s - s''_s(μ_s)` is symmetric up to `τ`. -/
theorem dq_symm (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s)ᵀ =
      (df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have h1 : ((df2CtxAt d n δ Kt ap).sHess π s)ᵀ = (df2CtxAt d n δ Kt ap).sHess π s :=
    hessM_transpose _ hsi.c2 _
  have h2 : ((df2CtxAt d n δ Kt ap).shh π s)ᵀ = (df2CtxAt d n δ Kt ap).shh π s := by
    unfold Df2Ctx.shh
    rw [transpose_smul, transpose_sub, transpose_vecMulVec, P_symm hI]
  rw [transpose_sub, h1, h2]

/-- `G_t(y)` and `G_t(c)` differ by at most `n KD δ⁴ 4R` up to `τ`, on G. -/
theorem dq_disc_path (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) (hG : (df2CtxAt d n δ Kt ap).EvG π m) {t : ℕ}
    (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m) {y c : Fin d → ℝ} (hyR : y ⬝ᵥ y ≤ (df2oPar d n δ).R ^ 2)
    (hcR : c ⬝ᵥ c ≤ (df2oPar d n δ).R ^ 2)
    (hyc : Real.sqrt ((y - c) ⬝ᵥ (y - c)) ≤ (df2oPar d n δ).δe ^ 4) :
    |(df2CtxAt d n δ Kt ap).GG π t y - (df2CtxAt d n δ Kt ap).GG π t c| ≤
      n * KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) := by
  have hR0 : 0 ≤ (df2oPar d n δ).R := by
    have : (1 : ℝ) ≤ (df2oPar d n δ).R := H.rows.one_le_R
    linarith
  have hK0 : 0 ≤ KD d n δ := KD_nonneg H.hd H.hn H.rows
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hterm : ∀ s ≤ t, |df2Sq ((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s)
        (y - ((df2CtxAt d n δ Kt ap).st π s).mu) -
      df2Sq ((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s)
        (c - ((df2CtxAt d n δ Kt ap).st π s).mu)| ≤
      KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := (df2CtxAt d n δ Kt ap).st π s
    rw [sq_sub_sq _ (dq_symm H hs)]
    have h1 := bilin_le_of_quad _ (dq_symm H hs) (KD d n δ) (dq_quad H hG hs) ((y - st.mu) - (c - st.mu))
      ((y - st.mu) + (c - st.mu))
    have e1 : (y - st.mu) - (c - st.mu) = y - c := by abel
    rw [e1] at h1 ⊢
    have hmu := sqrt_dot_le_of hR0 (mu_sq_le H hI)
    have hy1 := sqrt_dot_le_of hR0 hyR
    have hc1 := sqrt_dot_le_of hR0 hcR
    have hy2 := sqrt_dot_sub_le y st.mu
    have hc2 := sqrt_dot_sub_le c st.mu
    have h2 : Real.sqrt (((y - st.mu) + (c - st.mu)) ⬝ᵥ ((y - st.mu) + (c - st.mu))) ≤ 4 * (df2oPar d n δ).R :=
      (sqrt_dot_add_le _ _).trans (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul hyc h2 (Real.sqrt_nonneg _) (by positivity)) hK0)
  unfold Df2Ctx.GG
  rw [← Finset.sum_sub_distrib]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |df2Sq ((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s)
        (y - ((df2CtxAt d n δ Kt ap).st π s).mu) -
      df2Sq ((df2CtxAt d n δ Kt ap).shh π s - (df2CtxAt d n δ Kt ap).sHess π s)
        (c - ((df2CtxAt d n δ Kt ap).st π s).mu)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ n * (KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R))) :=
      mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

end path


/-! ## The budget of DQ -/

/-- DF Lemma DQ on setting (E): `μ(G ∩ ¬DQ) ≤ δ_e/8`. -/
theorem df2EvDQProp_holds : Df2EvDQProp := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hE
  classical
  have rows := df2RowsHold d n δ hd hn hδ0 hδ1 heps
  have hde0 : 0 < (df2oPar d n δ).δe := rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := rows.de_lt
  have he0 : 0 < (df2oPar d n δ).eps := rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := rows.pos_lam
  have hl1 : (df2oPar d n δ).lam < 1 := by have := rows.lam_le; linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_def]; positivity
  have hR1 : 1 ≤ (df2oPar d n δ).R := rows.one_le_R
  have hRD := RD_pos hd hn rows
  have hM0 := M0_nonneg (df2oPar d n δ)
  obtain ⟨C, hCball, -, hCnet, hCcard⟩ := existsNet d (df2oPar d n δ).R ((df2oPar d n δ).δe ^ 4) (by linarith)
    (by positivity)
  have hU := lemmaU_setE (d := d) μ 𝒢 C m n hmn (sig n δ Kθ gθ ap θ ξ e) ξ e
    (fun s hs => measurable_sig n δ Kθ gθ ap θ ξ e 𝒢 hmeas hθ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
    (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
    (fun c s hs => measurable_aOf n δ Kθ gθ ap hmeas hs _ _
      (measurable_phiH n δ _ (measurable_const.sub ApMeas.measurable_st_mu)))
    (fun c s _ => measurable_bOf n δ Kθ gθ ap hmeas _ _
      (measurable_phiH n δ _ (measurable_const.sub ApMeas.measurable_st_mu)))
    (fun c => kF d n δ (M0 (df2oPar d n δ)) * KphiH d n δ (M0 (df2oPar d n δ)) (WithLp.ofLp c)) 3
    (fun c => mul_nonneg (kF_nonneg n δ _ he0) (KphiH_nonneg hl0.le hk0 _))
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiH_nonneg hl0.le hk0 _) (fun st hst z => phiH_growth hM0 hl0.le hk0 _ hst z) x).1)
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiH_nonneg hl0.le hk0 _) (fun st hst z => phiH_growth hM0 hl0.le hk0 _ hst z) x).2)
    (RD d n δ)⁻¹ ((df2oPar d n δ).δe / 8) (inv_pos.2 hRD) (by positivity) (by linarith)
    (fun _ _ _ => VD d n δ) (fun _ _ _ => RD d n δ)
  refine le_trans (measure_mono ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  obtain ⟨hG, hDQ⟩ := hω
  have H : DetBase (df2CtxAt d n δ (Kθ (θ ω)) ap) δ ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ m :=
    EvGY.detBase SIF.df2SIFacts_holds hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ ω)) hap (fun s hs => hadm (θ ω) s hs)
  unfold Df2Ctx.EvDQ at hDQ
  push Not at hDQ
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hDQ
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 (df2oPar d n δ).R := by
    rw [mem_closedBall_zero_iff, norm_toLp]; exact hyR
  have hyR2 : y ⬝ᵥ y ≤ (df2oPar d n δ).R ^ 2 := by
    have h1 : Real.sqrt (y ⬝ᵥ y) ≤ (df2oPar d n δ).R := hyR
    rw [← Real.sq_sqrt (dot_self_nonneg' y)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  obtain ⟨c, hcC, hdist⟩ := hCnet _ hyball
  set c' : Fin d → ℝ := WithLp.ofLp c with hc'
  have hyc : Real.sqrt ((y - c') ⬝ᵥ (y - c')) ≤ (df2oPar d n δ).δe ^ 4 := by
    rw [← norm_toLp, WithLp.toLp_sub, hc', WithLp.toLp_ofLp, ← dist_eq_norm]; exact hdist
  have hc8 : (c' - y) ⬝ᵥ (c' - y) ≤ (df2oPar d n δ).δe ^ 8 := by
    have e1 : (c' - y) ⬝ᵥ (c' - y) = (y - c') ⬝ᵥ (y - c') := by
      rw [← neg_sub y c', neg_dotProduct, dotProduct_neg, neg_neg]
    rw [e1, ← Real.sq_sqrt (dot_self_nonneg' (y - c')), show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hyc 2
  have hcR : c' ⬝ᵥ c' ≤ (df2oPar d n δ).R ^ 2 := by
    have h1 : Real.sqrt (c' ⬝ᵥ c') ≤ (df2oPar d n δ).R := by
      rw [← norm_toLp, hc', WithLp.toLp_ofLp]; exact mem_closedBall_zero_iff.1 (hCball hcC)
    rw [← Real.sq_sqrt (dot_self_nonneg' c')]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have htau := EvGY.tau_lt (df2CtxAt d n δ (Kθ (θ ω)) ap) ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ hm1
  have htm : t < m := lt_of_le_of_lt ht htau
  -- each increment at `c` up to `t`
  have hinc : ∀ s ≤ t, zSeq m
      (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
      (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
      (sig n δ Kθ gθ ap θ ξ e) ξ e c s ω =
      (df2CtxAt d n δ (Kθ (θ ω)) ap).Y ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s *
          phiH n δ (fun st => c' - st.mu)
            ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s) (ξ s ω) -
        df2Sq ((df2CtxAt d n δ (Kθ (θ ω)) ap).sHess ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s)
          (c' - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
    intro s hs
    have hs' := hs.trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    rw [zSeq_eq n δ Kθ gθ ap θ ξ e (M0 (df2oPar d n δ)) (fun c => phiH n δ (fun st => WithLp.ofLp c - st.mu)) c ω
      (lt_of_le_of_lt hs' htau) hst]
    have hm := mean_H H hs' (fun st => c' - st.mu)
    exact congrArg (fun r => _ - r) hm
  rw [Set.mem_ofPred_eq]
  refine ⟨c, hcC, t, htm, VD_nonneg d n δ, by rw [inv_mul_cancel₀ hRD.ne'], ?_, ?_, ?_⟩
  · -- the variance
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (dq_var H ht hyS hc8)
    have hs' := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact sq_aOf_bOf_eq Kθ gθ _ s _ (sig n δ Kθ gθ ap θ ξ e s ω, z) hst
  · -- the range
    intro s hs
    rw [hinc s hs]
    exact dq_range H hG (hs.trans ht) (lq_q H ht hyS hc8 hs)
  · -- the deviation
    have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m
        (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
        (sig n δ Kθ gθ ap θ ξ e) ξ e c s ω =
        (df2CtxAt d n δ (Kθ (θ ω)) ap).GG ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ t c' := by
      unfold Df2Ctx.GG
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hinc s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), df2Sq_sub]
      have hg := shh_sq n δ Kθ gθ ap θ ξ e ω s (fun st => c' - st.mu)
      exact congrArg (fun r => r - _) hg.symm
    rw [hsum]
    have hdisc := dq_disc_path H hG ht hyR2 hcR hyc
    have ha := dq_arith hd hn rows C.card (by
      obtain ⟨c0, hc0⟩ : C.Nonempty := ⟨c, hcC⟩
      exact_mod_cast Finset.card_pos.2 ⟨c0, hc0⟩) hCcard
    have hab := abs_sub_abs_le_abs_sub
      ((df2CtxAt d n δ (Kθ (θ ω)) ap).GG ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ t y)
      ((df2CtxAt d n δ (Kθ (θ ω)) ap).GG ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ t c')
    have hlt' : df2Bn (df2oPar d n δ) d n / ((df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) <
        |(df2CtxAt d n δ (Kθ (θ ω)) ap).GG ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ t y| := hlt
    show _ < _
    linarith

end AdversarialBco.Poly.EvSI
