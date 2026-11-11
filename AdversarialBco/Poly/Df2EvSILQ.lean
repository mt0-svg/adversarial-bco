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
# The event LQ

Lemma LQ on setting (E): `μ(G ∩ ¬LQ) ≤ δ_e/21`. For a point `c` of a net of `B_R` at scale `δ⁴`, the increments
`Y_s ⟨P_s A_s ξ_s, c - μ_s⟩/(1 - λ) - ⟨s'_s(μ_s), c - μ_s⟩ = ⟨ĝ_s - s'_s(μ_s), c - μ_s⟩` are those of `lemmaU_setE`
with the direction `phiL c`; up to `τ` and for `y ∈ S_t` within `δ⁴` of `c`, their second moments sum to at most
`VL`, they are at most `RL`, and the sums at `y` and at `c` differ by at most `n Gq δ⁴`.
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

theorem xq_pos (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) : 14 ≤ xq d n δ := H.x_ge

theorem sqrt_k0 (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) :
    Real.sqrt (df2oPar d n δ).k0 = (1 - (df2oPar d n δ).lam)⁻¹ := by
  have hl1 := lam_lt H
  rw [k0_eq H, Real.sqrt_inv, Real.sqrt_sq (by linarith)]

/-- `|c - μ_s|²_{P_s} ≤ qL` for `c` within `δ⁴` of `y ∈ S_t`. -/
theorem lq_q (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAt d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) {s : ℕ} (hs : s ≤ t) :
    df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (c - ((df2CtxAt d n δ Kt ap).st π s).mu) ≤ qL d n δ := by
  have hI := H.stInv_le_tau s (hs.trans ht)
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := H.rows.de_lt
  have hl : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  set P := ((df2CtxAt d n δ Kt ap).st π s).P
  set mu := ((df2CtxAt d n δ Kt ap).st π s).mu
  have e1 : c - mu = (y - mu) + (c - y) := by abel
  have h1 := psd_expand P hI.pd.posSemidef (y - mu) (c - y) _ hde
  have h2 : (df2oPar d n δ).lam ^ 2 * df2Sq P (y - mu) ≤ 1 / (2 * (df2oPar d n δ).Le) := hy s hs
  have h3 : df2Sq P (c - y) ≤ (df2oPar d n δ).δe⁻¹ * ((c - y) ⬝ᵥ (c - y)) :=
    quad_le_of_psd (P_upper H hI) _
  have hpos : 0 < 2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2 := by positivity
  have h2' : df2Sq P (y - mu) ≤ 1 / (2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) := by
    rw [le_div_iff₀ hpos]
    have : 1 / (2 * (df2oPar d n δ).Le) * (2 * (df2oPar d n δ).Le) = 1 := by field_simp
    nlinarith
  have h3' : df2Sq P (c - y) ≤ (df2oPar d n δ).δe ^ 7 := by
    calc _ ≤ (df2oPar d n δ).δe⁻¹ * (df2oPar d n δ).δe ^ 8 :=
          h3.trans (mul_le_mul_of_nonneg_left hc (by positivity))
      _ = (df2oPar d n δ).δe ^ 7 := by field_simp
  rw [e1]
  unfold qL
  have h7 : (1 + (df2oPar d n δ).δe⁻¹) * (df2oPar d n δ).δe ^ 7 ≤ 2 * (df2oPar d n δ).δe ^ 6 := by
    have : (1 + (df2oPar d n δ).δe⁻¹) * (df2oPar d n δ).δe ^ 7 =
        (df2oPar d n δ).δe ^ 7 + (df2oPar d n δ).δe ^ 6 := by field_simp
    rw [this]
    have : (df2oPar d n δ).δe ^ 7 ≤ (df2oPar d n δ).δe ^ 6 :=
      pow_le_pow_of_le_one hde.le hde1.le (by norm_num)
    linarith
  calc _ ≤ (1 + (df2oPar d n δ).δe) * df2Sq P (y - mu) + (1 + (df2oPar d n δ).δe⁻¹) * df2Sq P (c - y) := h1
    _ ≤ (1 + (df2oPar d n δ).δe) * (1 / (2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2)) +
        (1 + (df2oPar d n δ).δe⁻¹) * (df2oPar d n δ).δe ^ 7 := by
          gcongr
    _ ≤ _ := by
      have : (1 + (df2oPar d n δ).δe) * (1 / (2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2)) =
          (1 + (df2oPar d n δ).δe) / (2 * (df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) := by ring
      linarith

/-- The second moments of the increments at `c` sum to at most `VL`. -/
theorem lq_var (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAt d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
      (lin ((df2CtxAt d n δ Kt ap).st π s) (c - ((df2CtxAt d n δ Kt ap).st π s).mu) z /
        (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤ VL d n δ := by
  have hx := xq_pos H
  set T := 8 * xq d n δ with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eq H]; positivity
  have hq : 0 ≤ qL d n δ := by
    have := H.rows.pos_de; have := H.rows.pos_lam; have := H.one_le_Le
    unfold qL; positivity
  set τ0 := Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
      (lin ((df2CtxAt d n δ Kt ap).st π s) (c - ((df2CtxAt d n δ Kt ap).st π s).mu) z /
        (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤
      (df2oPar d n δ).k0 * (qL d n δ * (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (WbL d n δ) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_L H (hs'.trans ht) (c - ((df2CtxAt d n δ Kt ap).st π s).mu) T hT
    have hqs := lq_q H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) :=
      integral_nonneg fun z => yR_nonneg n δ Kt (π.g s) _ z
    have hY2 := intY2_le H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) ≤
        Real.sqrt (WbL d n δ) := Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) * τ0 := by
      positivity
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef
      (c - ((df2CtxAt d n δ Kt ap).st π s).mu)
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ hk0)
    refine mul_le_mul hqs ?_ hinner hq
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
  unfold VL tailL
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq) hk0
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) ≤
      T * (9 * n) := mul_le_mul_of_nonneg_left hsum hT
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (WbL d n δ) * τ0) ≤ n * (Real.sqrt (WbL d n δ) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

theorem sqrt_dot_sub_le (a b : Fin d → ℝ) :
    Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  rw [← norm_toLp, ← norm_toLp, ← norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem sqrt_dot_le_of {a : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R) (h : a ⬝ᵥ a ≤ R ^ 2) : Real.sqrt (a ⬝ᵥ a) ≤ R := by
  rw [← Real.sqrt_sq hR]; exact Real.sqrt_le_sqrt h

/-- `|⟨s'_s(μ_s), w⟩| ≤ (8/ε) |w|` up to `τ`. -/
theorem sGrad_dot_le (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m)
    (w : Fin d → ℝ) :
    |(df2CtxAt d n δ Kt ap).sGrad π s ⬝ᵥ w| ≤ 8 / (df2oPar d n δ).eps * Real.sqrt (w ⬝ᵥ w) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hK : 0 ≤ 8 / (df2oPar d n δ).eps := by positivity
  have hlip := surr_lip (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hK hsi.ext_lip
    (WithLp.toLp 2 ((df2CtxAt d n δ Kt ap).st π s).mu)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) ((df2CtxAt d n δ Kt ap).st π s).A) _ H.rows.pos_lam
  exact gradM_dot_le _ _ hK hlip _ w

/-- The increments at `c` are at most `RL` up to `τ`, on G. -/
theorem lq_range (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) (hG : (df2CtxAt d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) {c : Fin d → ℝ} (hcR : c ⬝ᵥ c ≤ (df2oPar d n δ).R ^ 2)
    (hq : df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (c - ((df2CtxAt d n δ Kt ap).st π s).mu) ≤ qL d n δ) :
    |(df2CtxAt d n δ Kt ap).Y π s * phiL n δ c ((df2CtxAt d n δ Kt ap).st π s) (π.xi s) -
      (df2CtxAt d n δ Kt ap).sGrad π s ⬝ᵥ (c - ((df2CtxAt d n δ Kt ap).st π s).mu)| ≤ RL d n δ := by
  have hI := H.stInv_le_tau s hs
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hR0 : 0 ≤ (df2oPar d n δ).R := by
    have : (1 : ℝ) ≤ (df2oPar d n δ).R := H.rows.one_le_R
    linarith
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  set st := (df2CtxAt d n δ Kt ap).st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (c - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (c - st.mu) := dir_sq st hI.AA hI.SP _
  have hY : |(df2CtxAt d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hphi : phiL n δ c st (π.xi s) = (π.xi s ⬝ᵥ b) * Real.sqrt (df2oPar d n δ).k0 := by
    unfold phiL; rw [lin_eq_dot st (P_symm hI), sqrt_k0 H, ← hb]; ring
  have h1 : |π.xi s ⬝ᵥ b| ≤ Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ) :=
    (abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hξ) (Real.sqrt_le_sqrt (hbb ▸ hq))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h2 := sGrad_dot_le H hs (c - st.mu)
  have h3 : Real.sqrt ((c - st.mu) ⬝ᵥ (c - st.mu)) ≤ 2 * (df2oPar d n δ).R := by
    have := sqrt_dot_sub_le c st.mu
    have := sqrt_dot_le_of hR0 hcR
    have := sqrt_dot_le_of hR0 (mu_sq_le H hI)
    linarith
  have hk := Real.sqrt_nonneg (df2oPar d n δ).k0
  have hc8 : 0 ≤ 8 / (df2oPar d n δ).eps := by positivity
  have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
  rw [hphi]
  unfold RL
  calc _ ≤ |(df2CtxAt d n δ Kt ap).Y π s * ((π.xi s ⬝ᵥ b) * Real.sqrt (df2oPar d n δ).k0)| +
        |(df2CtxAt d n δ Kt ap).sGrad π s ⬝ᵥ (c - st.mu)| := abs_sub _ _
    _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) *
          ((Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ)) * Real.sqrt (df2oPar d n δ).k0) +
        8 / (df2oPar d n δ).eps * (2 * (df2oPar d n δ).R) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk]
      gcongr
      exact h2.trans (mul_le_mul_of_nonneg_left h3 hc8)
    _ = _ := by ring

/-- The sums at `y` and at `c` differ by at most `n Gq δ⁴` up to `τ`, on G. -/
theorem lq_disc_path (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) (hG : (df2CtxAt d n δ Kt ap).EvG π m) {t : ℕ}
    (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m) {y c : Fin d → ℝ}
    (hyc : Real.sqrt ((y - c) ⬝ᵥ (y - c)) ≤ (df2oPar d n δ).δe ^ 4) :
    |∑ s ∈ Finset.range (t + 1), ((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ
        (y - ((df2CtxAt d n δ Kt ap).st π s).mu) -
      ∑ s ∈ Finset.range (t + 1), ((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ
        (c - ((df2CtxAt d n δ Kt ap).st π s).mu)| ≤ n * Gq d n δ * (df2oPar d n δ).δe ^ 4 := by
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hG0 : 0 ≤ Gq d n δ := by unfold Gq; positivity
  have hterm : ∀ s ≤ t, |((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ (y - c)| ≤
      Gq d n δ * (df2oPar d n δ).δe ^ 4 := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := (df2CtxAt d n δ Kt ap).st π s
    have hY : |(df2CtxAt d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
    have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
    have hu : (st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ π.xi s)) ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe :=
      (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (P_upper H hI)).trans
        (div_le_div_of_nonneg_right hξ hde.le)
    have hgh : (df2CtxAt d n δ Kt ap).ghat π s ⬝ᵥ (y - c) = (df2CtxAt d n δ Kt ap).Y π s *
        Real.sqrt (df2oPar d n δ).k0 * ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c)) := by
      unfold Df2Ctx.ghat Df2Ctx.u Df2Ctx.w
      rw [smul_dotProduct, smul_eq_mul, sqrt_k0 H]
      rfl
    have h1 : |(st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c)| ≤
        Real.sqrt (32 / 9 * d * xq d n δ / (df2oPar d n δ).δe) * (df2oPar d n δ).δe ^ 4 :=
      (abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hu)
        (by rw [show y - c = y - c from rfl]; exact hyc) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h2 := sGrad_dot_le H hs (y - c)
    have hk := Real.sqrt_nonneg (df2oPar d n δ).k0
    have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
    rw [sub_dotProduct, hgh]
    unfold Gq
    calc _ ≤ |(df2CtxAt d n δ Kt ap).Y π s * Real.sqrt (df2oPar d n δ).k0 *
          ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c))| + |(df2CtxAt d n δ Kt ap).sGrad π s ⬝ᵥ (y - c)| := abs_sub _ _
      _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) * Real.sqrt (df2oPar d n δ).k0 *
            (Real.sqrt (32 / 9 * d * xq d n δ / (df2oPar d n δ).δe) * (df2oPar d n δ).δe ^ 4) +
          8 / (df2oPar d n δ).eps * (df2oPar d n δ).δe ^ 4 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk]
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left hyc (by positivity))
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  have e1 : ∀ s ∈ Finset.range (t + 1),
      ((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ
          (y - ((df2CtxAt d n δ Kt ap).st π s).mu) -
        ((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ
          (c - ((df2CtxAt d n δ Kt ap).st π s).mu) =
      ((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ (y - c) := by
    intro s _
    rw [← dotProduct_sub]; congr 1; abel
  rw [Finset.sum_congr rfl e1]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |((df2CtxAt d n δ Kt ap).ghat π s - (df2CtxAt d n δ Kt ap).sGrad π s) ⬝ᵥ
        (y - c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), Gq d n δ * (df2oPar d n δ).δe ^ 4 :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (Gq d n δ * (df2oPar d n δ).δe ^ 4) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ n * (Gq d n δ * (df2oPar d n δ).δe ^ 4) := mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

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

/-! ## The budget of LQ -/

/-- Lemma LQ on setting (E): `μ(G ∩ ¬LQ) ≤ δ_e/21`. -/
theorem df2EvLQProp_holds : Df2EvLQProp := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hE
  classical
  have rows := df2RowsHold d n δ hd hn hδ0 hδ1 heps
  have hde0 : 0 < (df2oPar d n δ).δe := rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := rows.de_lt
  have he0 : 0 < (df2oPar d n δ).eps := rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := rows.pos_lam
  have hl1 : (df2oPar d n δ).lam < 1 := by have := rows.lam_le; linarith
  have hR1 : 1 ≤ (df2oPar d n δ).R := rows.one_le_R
  have hRL := RL_pos hd hn rows
  have hM0 := M0_nonneg (df2oPar d n δ)
  obtain ⟨C, hCball, -, hCnet, hCcard⟩ := existsNet d (df2oPar d n δ).R ((df2oPar d n δ).δe ^ 4) (by linarith)
    (by positivity)
  have hU := lemmaU_setE (d := d) μ 𝒢 C m n hmn (sig n δ Kθ gθ ap θ ξ e) ξ e
    (fun s hs => measurable_sig n δ Kθ gθ ap θ ξ e 𝒢 hmeas hθ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
    (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c)))
    (fun c s hs => measurable_aOf n δ Kθ gθ ap hmeas hs _ _ (measurable_phiL n δ _))
    (fun c s _ => measurable_bOf n δ Kθ gθ ap hmeas _ _ (measurable_phiL n δ _))
    (fun c => kF d n δ (M0 (df2oPar d n δ)) * KphiL d n δ (M0 (df2oPar d n δ)) (WithLp.ofLp c)) 3
    (fun c => mul_nonneg (kF_nonneg n δ _ he0) (KphiL_nonneg hM0 hl1 _))
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiL_nonneg hM0 hl1 _) (fun st hst z => phiL_growth hM0 hl1 _ hst z) x).1)
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiL_nonneg hM0 hl1 _) (fun st hst z => phiL_growth hM0 hl1 _ hst z) x).2)
    (RL d n δ)⁻¹ ((df2oPar d n δ).δe / 21) (inv_pos.2 hRL) (by positivity) (by linarith)
    (fun _ _ _ => VL d n δ) (fun _ _ _ => RL d n δ)
  refine le_trans (measure_mono ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  obtain ⟨hG, hLQ⟩ := hω
  have H : DetBase (df2CtxAt d n δ (Kθ (θ ω)) ap) δ ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ m :=
    EvGY.detBase SIF.df2SIFacts_holds hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ ω)) hap (fun s hs => hadm (θ ω) s hs)
  unfold Df2Ctx.EvLQ at hLQ
  push Not at hLQ
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hLQ
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 (df2oPar d n δ).R := by
    rw [mem_closedBall_zero_iff, norm_toLp]; exact hyR
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
  have hinc : ∀ s ≤ t, zSeq m (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
      (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sig n δ Kθ gθ ap θ ξ e) ξ e c s ω =
      (df2CtxAt d n δ (Kθ (θ ω)) ap).Y ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s *
          phiL n δ c' ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s)
            (ξ s ω) -
        (df2CtxAt d n δ (Kθ (θ ω)) ap).sGrad ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
    intro s hs
    have hs' := hs.trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    rw [zSeq_eq n δ Kθ gθ ap θ ξ e (M0 (df2oPar d n δ)) (fun c => phiL n δ (WithLp.ofLp c)) c ω
      (lt_of_le_of_lt hs' htau) hst]
    have hm := mean_L H hs' c'
    exact congrArg (fun r => _ - r) hm
  rw [Set.mem_ofPred_eq]
  refine ⟨c, hcC, t, htm, VL_nonneg hd hn rows, by rw [inv_mul_cancel₀ hRL.ne'], ?_, ?_, ?_⟩
  · -- the variance
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (lq_var H ht hyS hc8)
    have hs' := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact sq_aOf_bOf_eq Kθ gθ _ s _ (sig n δ Kθ gθ ap θ ξ e s ω, z) hst
  · -- the range
    intro s hs
    rw [hinc s hs]
    exact lq_range H hG (hs.trans ht) hcR (lq_q H ht hyS hc8 hs)
  · -- the deviation
    have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m
        (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sig n δ Kθ gθ ap θ ξ e) ξ e c s ω =
        ∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ ω)) ap).ghat ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ ω)) ap).sGrad ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hinc s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sub_dotProduct]
      have hg := ghat_dot n δ Kθ gθ ap θ ξ e ω s c'
      exact congrArg (fun r => r - _) hg.symm
    rw [hsum]
    have hdisc := lq_disc_path H hG ht hyc
    have ha := lq_arith hd hn rows C.card (by
      obtain ⟨c0, hc0⟩ : C.Nonempty := ⟨c, hcC⟩
      exact_mod_cast Finset.card_pos.2 ⟨c0, hc0⟩) hCcard
    have hab := abs_sub_abs_le_abs_sub
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ ω)) ap).ghat ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ ω)) ap).sGrad ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ ω)) ap).ghat ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ ω)) ap).sGrad ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
    have hlt' : df2B1 (df2oPar d n δ) d n < |∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ ω)) ap).ghat ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ ω)) ap).sGrad ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAt d n δ (Kθ (θ ω)) ap).st ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu)| :=
      hlt
    show _ < _
    linarith

end AdversarialBco.Poly.EvSI
