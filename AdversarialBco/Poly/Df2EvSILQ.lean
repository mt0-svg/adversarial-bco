/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIRound
public import AdversarialBco.Poly.CoverProof
public import AdversarialBco.Poly.Df2EvSIArith
public import AdversarialBco.Poly.Df2SIFactsProof

@[expose] public section

/-!
# The event LQ: levels and arithmetic

Lemma LQ on setting (E) bounds `μ(G ∩ ¬LQ)` by `δ_e/21`: for a point `c` of a net of `B_R` at scale `δ⁴`, the
increments `Y_s ⟨P_s A_s ξ_s, c - μ_s⟩/(1 - λ) - ⟨s'_s(μ_s), c - μ_s⟩ = ⟨ĝ_s - s'_s(μ_s), c - μ_s⟩` go to
`lemmaU_setE` with the direction `phiL c`; up to `τ` their second moments sum to at most `VL`, they are at most `RL`,
and the sums at `y` and at `c` differ by at most `n Gq δ⁴`. This file holds the levels (`xq`, `qL`, `VL`, `RL`, `Gq`),
the parameters in these terms, the arithmetic of the lemma (`lq_arith`) and the growth of the direction
(`phiL_growth`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-! ## The levels -/

/-- `x = log(1/δ_e)`. -/
noncomputable def xq (d n : ℕ) (δ : ℝ) : ℝ := Real.log (1 / (df2oPar d n δ).δe)

/-- The bound of `|c - μ_s|²_{P_s}` for `c` within `δ⁴` of a point of `S_t`. -/
noncomputable def qL (d n : ℕ) (δ : ℝ) : ℝ :=
  (1 + (df2oPar d n δ).δe) / (2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) + 2 * (df2oPar d n δ).δe ^ 6

/-- The bound of the fourth moment of a round. -/
noncomputable def WbL (d n : ℕ) (δ : ℝ) : ℝ :=
  72 + 25600 * ((df2oPar d n δ).R ^ 4 + 3 * (d : ℝ) ^ 2) / (df2oPar d n δ).eps ^ 4

/-- The tail term of Lemma TR at `T = 8x`. -/
noncomputable def tailL (d n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (WbL d n δ) * Real.sqrt (Real.sqrt 105 * Real.exp (-(8 * xq d n δ) / 4))

/-- The variance level of LQ. -/
noncomputable def VL (d n : ℕ) (δ : ℝ) : ℝ :=
  (df2oPar d n δ).k0 * (qL d n δ * (8 * xq d n δ * (9 * n) + n * tailL d n δ))

/-- The range level of LQ. -/
noncomputable def RL (d n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (df2oPar d n δ).k0 * Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ) *
      ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) +
    8 / (df2oPar d n δ).eps * (2 * (df2oPar d n δ).R)

/-- The bound of `|ĝ_s - s'_s(μ_s)|`. -/
noncomputable def Gq (d n : ℕ) (δ : ℝ) : ℝ :=
  (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) * Real.sqrt (df2oPar d n δ).k0 *
      Real.sqrt (32 / 9 * d * xq d n δ / (df2oPar d n δ).δe) +
    8 / (df2oPar d n δ).eps

/-! ## On the path -/

section path

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ApFun d} {π : Df2Path d} {m : ℕ}

theorem sqrt_dot_sub_le (a b : Fin d → ℝ) :
    Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  rw [← norm_toLp, ← norm_toLp, ← norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

end path

/-! ## The parameters -/

theorem le_eq (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).Le = 36 * xq d n δ := rfl

theorem lam_eq (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).lam = 1 / (725 * d * (36 * xq d n δ) ^ 2) := rfl

theorem R_eq (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).R = 134 * d * Real.sqrt (Real.log (2 * d + 2)) := rfl

theorem k0_def (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).k0 = ((1 - (df2oPar d n δ).lam) ^ 2)⁻¹ := rfl

theorem xq_ge {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) : 14 ≤ xq d n δ := by
  have h := rows.cx
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg (by nlinarith)
  unfold xq; linarith

theorem qL_nonneg {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 ≤ qL d n δ := by
  have hx := xq_ge hd hn rows
  have hde := rows.pos_de
  have hl := rows.pos_lam
  unfold qL
  rw [le_eq]
  have : 0 ≤ 36 * xq d n δ := by linarith
  positivity

theorem VL_nonneg {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 ≤ VL d n δ := by
  have hx := xq_ge hd hn rows
  have hq := qL_nonneg hd hn rows
  have hk : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_def]; positivity
  have ht : 0 ≤ tailL d n δ := by unfold tailL; positivity
  unfold VL
  exact mul_nonneg hk (mul_nonneg hq (add_nonneg (mul_nonneg (by linarith) (by positivity))
    (mul_nonneg (by positivity) ht)))

theorem RL_pos {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) :
    0 < RL d n δ := by
  have hx := xq_ge hd hn rows
  have he := rows.pos_eps
  have hR := rows.one_le_R
  have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) :=
    div_nonneg (by rw [le_eq]; linarith) (by linarith)
  have h8 : 0 < 8 / (df2oPar d n δ).eps * (2 * (df2oPar d n δ).R) :=
    mul_pos (div_pos (by norm_num) he) (by linarith)
  have h1 : 0 ≤ Real.sqrt (df2oPar d n δ).k0 * Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ) *
      ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) := mul_nonneg (by positivity) hLe
  unfold RL
  linarith

/-- The arithmetic of LQ: Freedman's level at `VL`, `RL`, a net of `B_R` at scale `δ⁴` and `δ' = δ_e/21`, plus the
discretization, is at most `b₁`. -/
theorem lq_arith {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (rows : Df2Rows (df2oPar d n δ) d n) (Cc : ℝ)
    (hC1 : 1 ≤ Cc) (hC : Cc ≤ (1 + 2 * (df2oPar d n δ).R / (df2oPar d n δ).δe ^ 4) ^ d) :
    3 * Real.sqrt (VL d n δ * Real.log (4 * (n * Cc) * max ((RL d n δ)⁻¹ * RL d n δ)
        ((RL d n δ)⁻¹ * Real.sqrt (VL d n δ)) / ((df2oPar d n δ).δe / 21))) +
      2 * RL d n δ * Real.log (4 * (n * Cc) * max ((RL d n δ)⁻¹ * RL d n δ)
        ((RL d n δ)⁻¹ * Real.sqrt (VL d n δ)) / ((df2oPar d n δ).δe / 21)) +
      n * Gq d n δ * (df2oPar d n δ).δe ^ 4 ≤ df2B1 (df2oPar d n δ) d n := by
  have hRL := RL_pos hd hn rows
  have hV0 := VL_nonneg hd hn rows
  have ht0 : 0 ≤ tailL d n δ := by unfold tailL; positivity
  have ht1 : tailL d n δ ≤ 1 := lq_tail d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu
  have hV : VL d n δ ≤ 11 / 10 * n / (df2oPar d n δ).lam ^ 2 := by
    have h := lq_V d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (tailL d n δ) ht0 ht1
    unfold VL qL; rw [le_eq]; exact h
  have hRLe : RL d n δ = Real.sqrt (df2oPar d n δ).k0 * Real.sqrt (32 / 9 * d * xq d n δ) *
      Real.sqrt ((1 + (df2oPar d n δ).δe) / (2 * (36 * xq d n δ) * (df2oPar d n δ).lam ^ 2) +
        2 * (df2oPar d n δ).δe ^ 6) * (36 * xq d n δ / (2 * (df2oPar d n δ).eps)) +
      8 / (df2oPar d n δ).eps * (2 * (df2oPar d n δ).R) := by
    unfold RL qL; rw [le_eq]
  have hsV : Real.sqrt (VL d n δ) ≤ Real.sqrt n * RL d n δ := by
    rw [hRLe]
    exact lq_sqrtV d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (VL d n δ) hV0 hV
  have hn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  set Mx := max ((RL d n δ)⁻¹ * RL d n δ) ((RL d n δ)⁻¹ * Real.sqrt (VL d n δ)) with hMx
  have hM1 : 1 ≤ Mx := by rw [hMx, inv_mul_cancel₀ hRL.ne']; exact le_max_left _ _
  have hMn : Mx ≤ Real.sqrt n := by
    rw [hMx, inv_mul_cancel₀ hRL.ne']
    refine max_le hn1 ?_
    rw [inv_mul_le_iff₀ hRL, mul_comm]
    exact hsV
  have hcard := lq_card d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu Cc hC1 hC
  have hlog := ev_log d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu Cc Mx 21 (by norm_num) le_rfl hC1 hcard hM1 hMn
  have hdev := lq_dev d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
    (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
    rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu (VL d n δ) hV0 hV
  rw [← hRLe] at hdev
  have hdisc : n * Gq d n δ * (df2oPar d n δ).δe ^ 4 ≤ 1 := by
    have h := lq_disc d n (df2oPar d n δ).δe (xq d n δ) (df2oPar d n δ).lam (df2oPar d n δ).eps
      (df2oPar d n δ).R (df2oPar d n δ).k0 hd hn rows.pos_de rows.de_lt rfl rows.cx (lam_eq d n δ) rows.pos_eps
      rows.eps_le rows.r14 (R_eq d n δ) (k0_def d n δ) rows.cnu
    unfold Gq; rw [le_eq]; exact h
  have hB : df2B1 (df2oPar d n δ) d n = 1 + 1 / (df2oPar d n δ).lam * (11 / 20 * Real.sqrt (10 * d * n * (36 * xq d n δ)) +
      13 / 100 * (d * Real.sqrt d) * (36 * xq d n δ) ^ 2 / (df2oPar d n δ).eps) := by
    unfold df2B1; rw [le_eq]
  have h1 : Real.sqrt (VL d n δ * Real.log (4 * (n * Cc) * Mx / ((df2oPar d n δ).δe / 21))) ≤
      Real.sqrt (VL d n δ * (7 * d * xq d n δ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hV0)
  have h2 : RL d n δ * Real.log (4 * (n * Cc) * Mx / ((df2oPar d n δ).δe / 21)) ≤ RL d n δ * (7 * d * xq d n δ) :=
    mul_le_mul_of_nonneg_left hlog hRL.le
  rw [hB]
  nlinarith

/-! ## The growth of the direction -/

/-- The growth constant of `phiL y` on the bound condition. -/
noncomputable def KphiL (d n : ℕ) (δ M : ℝ) (y : Fin d → ℝ) : ℝ :=
  M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) / (1 - (df2oPar d n δ).lam)

theorem KphiL_nonneg {n : ℕ} {δ M : ℝ} (hM : 0 ≤ M) (hl1 : (df2oPar d n δ).lam < 1) (y : Fin d → ℝ) :
    0 ≤ KphiL d n δ M y := by
  unfold KphiL
  have : 0 < 1 - (df2oPar d n δ).lam := by linarith
  positivity

theorem phiL_growth {n : ℕ} {δ M : ℝ} (hM : 0 ≤ M) (hl1 : (df2oPar d n δ).lam < 1) (y : Fin d → ℝ)
    {st : Df2St d} (hst : stB M st) (z : Fin d → ℝ) : |phiL n δ y st z| ≤ KphiL d n δ M y * (1 + ‖z‖) ^ 2 := by
  have h1 : 0 < 1 - (df2oPar d n δ).lam := by linarith
  have hA := bdSet_apply hst.2.1 hM z
  have hP := bdSet_apply hst.2.2 hM (st.A *ᵥ z)
  have hz := sqrt_dot_le z
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt hst.1
  have hh := sqrt_dot_sub_le y st.mu
  have hsM := Real.sqrt_nonneg M
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have hu : Real.sqrt ((st.P *ᵥ (st.A *ᵥ z)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ z))) ≤ M * (Real.sqrt d * ‖z‖) := by
    calc _ ≤ Real.sqrt M * (Real.sqrt M * Real.sqrt (z ⬝ᵥ z)) := hP.trans (mul_le_mul_of_nonneg_left hA hsM)
      _ = M * Real.sqrt (z ⬝ᵥ z) := by rw [← mul_assoc, hMM]
      _ ≤ M * (Real.sqrt d * ‖z‖) := mul_le_mul_of_nonneg_left hz hM
  have hl : |lin st (y - st.mu) z| ≤ M * (Real.sqrt d * ‖z‖) * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) := by
    unfold lin
    exact (abs_dot_le _ _).trans (mul_le_mul hu (hh.trans (by linarith)) (Real.sqrt_nonneg _) (by positivity))
  have hzz : ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  unfold phiL KphiL
  rw [abs_div, abs_of_pos h1, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ h1.le
  calc |lin st (y - st.mu) z| ≤ M * (Real.sqrt d * ‖z‖) * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) := hl
    _ = M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) * ‖z‖ := by ring
    _ ≤ M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) * (1 + ‖z‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hzz (by positivity)

/-- Under the bound condition, `A² + B² = (fF² + fP²) φ²`. -/
theorem sq_aOf_bOf_eq {n : ℕ} {δ : ℝ} {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (M : ℝ) (s : ℕ)
    (φ : Df2St d → (Fin d → ℝ) → ℝ) (x : (Θ × Df2St d) × (Fin d → ℝ)) (hst : stB M x.1.2) :
    aOf n δ Kθ gθ M s φ x ^ 2 + bOf n δ Kθ M φ x ^ 2 =
      (fF n δ Kθ gθ s x ^ 2 + fP n δ Kθ x ^ 2) * φ x.1.2 x.2 ^ 2 := by
  unfold aOf bOf
  simp only [hst, ↓reduceIte]
  ring

end AdversarialBco.Poly.EvSI
