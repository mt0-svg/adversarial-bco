/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSILQ
public import AdversarialBco.Poly.Df2EvSIRoundV

@[expose] public section

/-!
# The event LQ on a path, with a routine per round

At the context `df2CtxAtF d n δ Kt ap` with a routine `ap s` in round `s` (`ap : ℕ → ApFun d`), on a path with the
hypotheses of DET without the events (`DetBase`), up to `τ`: `|c - μ_s|²_{P_s} ≤ qL` for `c` near a point of `S_t`
(`lq_qV`), the second moments of the increments at `c` sum to at most `VL` (`lq_varV`), `|⟨s'_s(μ_s), w⟩| ≤ (8/ε) |w|`
(`sGrad_dot_leV`), the increments are at most `RL` on G (`lq_rangeV`), and the sums at `y` and at `c` differ by at most
`n Gq δ⁴` on G (`lq_disc_pathV`). The levels are those of Df2EvSILQ.lean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

section path

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}

theorem xq_posV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) : 14 ≤ xq d n δ := H.x_ge

theorem sqrt_k0V (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) :
    Real.sqrt (df2oPar d n δ).k0 = (1 - (df2oPar d n δ).lam)⁻¹ := by
  have hl1 := lam_ltV H
  rw [k0_eqV H, Real.sqrt_inv, Real.sqrt_sq (by linarith)]

/-- `|c - μ_s|²_{P_s} ≤ qL` for `c` within `δ⁴` of `y ∈ S_t`. -/
theorem lq_qV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAtF d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) {s : ℕ} (hs : s ≤ t) :
    df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) ≤ qL d n δ := by
  have hI := H.stInv_le_tau s (hs.trans ht)
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := H.rows.de_lt
  have hl : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  set P := ((df2CtxAtF d n δ Kt ap).st π s).P
  set mu := ((df2CtxAtF d n δ Kt ap).st π s).mu
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
theorem lq_varV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAtF d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
      (lin ((df2CtxAtF d n δ Kt ap).st π s) (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) z /
        (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤ VL d n δ := by
  have hx := xq_posV H
  set T := 8 * xq d n δ with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eqV H]; positivity
  have hq : 0 ≤ qL d n δ := by
    have := H.rows.pos_de; have := H.rows.pos_lam; have := H.one_le_Le
    unfold qL; positivity
  set τ0 := Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
      (lin ((df2CtxAtF d n δ Kt ap).st π s) (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) z /
        (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤
      (df2oPar d n δ).k0 * (qL d n δ * (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (WbL d n δ) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_LV H (hs'.trans ht) (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) T hT
    have hqs := lq_qV H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) :=
      integral_nonneg fun z => yR_nonneg n δ Kt (π.g s) _ z
    have hY2 := intY2_leV H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) ≤
        Real.sqrt (WbL d n δ) := Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) * τ0 := by
      positivity
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef
      (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ hk0)
    refine mul_le_mul hqs ?_ hinner hq
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hτ0n)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsum := sumY_leV H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  have hW : 0 ≤ Real.sqrt (WbL d n δ) * τ0 := by positivity
  unfold VL tailL
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq) hk0
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) ≤
      T * (9 * n) := mul_le_mul_of_nonneg_left hsum hT
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (WbL d n δ) * τ0) ≤ n * (Real.sqrt (WbL d n δ) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

theorem sqrt_dot_sub_leV (a b : Fin d → ℝ) :
    Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  rw [← norm_toLp, ← norm_toLp, ← norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem sqrt_dot_le_ofV {a : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R) (h : a ⬝ᵥ a ≤ R ^ 2) : Real.sqrt (a ⬝ᵥ a) ≤ R := by
  rw [← Real.sqrt_sq hR]; exact Real.sqrt_le_sqrt h

/-- `|⟨s'_s(μ_s), w⟩| ≤ (8/ε) |w|` up to `τ`. -/
theorem sGrad_dot_leV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m)
    (w : Fin d → ℝ) :
    |(df2CtxAtF d n δ Kt ap).sGrad π s ⬝ᵥ w| ≤ 8 / (df2oPar d n δ).eps * Real.sqrt (w ⬝ᵥ w) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hK : 0 ≤ 8 / (df2oPar d n δ).eps := by positivity
  have hlip := surr_lip (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hK hsi.ext_lip
    (WithLp.toLp 2 ((df2CtxAtF d n δ Kt ap).st π s).mu)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) ((df2CtxAtF d n δ Kt ap).st π s).A) _ H.rows.pos_lam
  exact gradM_dot_le _ _ hK hlip _ w

/-- The increments at `c` are at most `RL` up to `τ`, on G. -/
theorem lq_rangeV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) (hG : (df2CtxAtF d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) {c : Fin d → ℝ} (hcR : c ⬝ᵥ c ≤ (df2oPar d n δ).R ^ 2)
    (hq : df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) ≤ qL d n δ) :
    |(df2CtxAtF d n δ Kt ap).Y π s * phiL n δ c ((df2CtxAtF d n δ Kt ap).st π s) (π.xi s) -
      (df2CtxAtF d n δ Kt ap).sGrad π s ⬝ᵥ (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)| ≤ RL d n δ := by
  have hI := H.stInv_le_tau s hs
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hR0 : 0 ≤ (df2oPar d n δ).R := by
    have : (1 : ℝ) ≤ (df2oPar d n δ).R := H.rows.one_le_R
    linarith
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  set st := (df2CtxAtF d n δ Kt ap).st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (c - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (c - st.mu) := dir_sq st hI.AA hI.SP _
  have hY : |(df2CtxAtF d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hphi : phiL n δ c st (π.xi s) = (π.xi s ⬝ᵥ b) * Real.sqrt (df2oPar d n δ).k0 := by
    unfold phiL; rw [lin_eq_dot st (P_symm hI), sqrt_k0V H, ← hb]; ring
  have h1 : |π.xi s ⬝ᵥ b| ≤ Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ) :=
    (abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hξ) (Real.sqrt_le_sqrt (hbb ▸ hq))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h2 := sGrad_dot_leV H hs (c - st.mu)
  have h3 : Real.sqrt ((c - st.mu) ⬝ᵥ (c - st.mu)) ≤ 2 * (df2oPar d n δ).R := by
    have := sqrt_dot_sub_leV c st.mu
    have := sqrt_dot_le_ofV hR0 hcR
    have := sqrt_dot_le_ofV hR0 (mu_sq_le H hI)
    linarith
  have hk := Real.sqrt_nonneg (df2oPar d n δ).k0
  have hc8 : 0 ≤ 8 / (df2oPar d n δ).eps := by positivity
  have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
  rw [hphi]
  unfold RL
  calc _ ≤ |(df2CtxAtF d n δ Kt ap).Y π s * ((π.xi s ⬝ᵥ b) * Real.sqrt (df2oPar d n δ).k0)| +
        |(df2CtxAtF d n δ Kt ap).sGrad π s ⬝ᵥ (c - st.mu)| := abs_sub _ _
    _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) *
          ((Real.sqrt (32 / 9 * d * xq d n δ) * Real.sqrt (qL d n δ)) * Real.sqrt (df2oPar d n δ).k0) +
        8 / (df2oPar d n δ).eps * (2 * (df2oPar d n δ).R) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk]
      gcongr
      exact h2.trans (mul_le_mul_of_nonneg_left h3 hc8)
    _ = _ := by ring

/-- The sums at `y` and at `c` differ by at most `n Gq δ⁴` up to `τ`, on G. -/
theorem lq_disc_pathV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) (hG : (df2CtxAtF d n δ Kt ap).EvG π m) {t : ℕ}
    (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) {y c : Fin d → ℝ}
    (hyc : Real.sqrt ((y - c) ⬝ᵥ (y - c)) ≤ (df2oPar d n δ).δe ^ 4) :
    |∑ s ∈ Finset.range (t + 1), ((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ
        (y - ((df2CtxAtF d n δ Kt ap).st π s).mu) -
      ∑ s ∈ Finset.range (t + 1), ((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ
        (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)| ≤ n * Gq d n δ * (df2oPar d n δ).δe ^ 4 := by
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hG0 : 0 ≤ Gq d n δ := by unfold Gq; positivity
  have hterm : ∀ s ≤ t, |((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ (y - c)| ≤
      Gq d n δ * (df2oPar d n δ).δe ^ 4 := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := (df2CtxAtF d n δ Kt ap).st π s
    have hY : |(df2CtxAtF d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
    have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
    have hu : (st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ π.xi s)) ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe :=
      (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (P_upper H hI)).trans
        (div_le_div_of_nonneg_right hξ hde.le)
    have hgh : (df2CtxAtF d n δ Kt ap).ghat π s ⬝ᵥ (y - c) = (df2CtxAtF d n δ Kt ap).Y π s *
        Real.sqrt (df2oPar d n δ).k0 * ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c)) := by
      unfold Df2Ctx.ghat Df2Ctx.u Df2Ctx.w
      rw [smul_dotProduct, smul_eq_mul, sqrt_k0V H]
      rfl
    have h1 : |(st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c)| ≤
        Real.sqrt (32 / 9 * d * xq d n δ / (df2oPar d n δ).δe) * (df2oPar d n δ).δe ^ 4 :=
      (abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hu)
        (by rw [show y - c = y - c from rfl]; exact hyc) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h2 := sGrad_dot_leV H hs (y - c)
    have hk := Real.sqrt_nonneg (df2oPar d n δ).k0
    have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
    rw [sub_dotProduct, hgh]
    unfold Gq
    calc _ ≤ |(df2CtxAtF d n δ Kt ap).Y π s * Real.sqrt (df2oPar d n δ).k0 *
          ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - c))| + |(df2CtxAtF d n δ Kt ap).sGrad π s ⬝ᵥ (y - c)| := abs_sub _ _
      _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) * Real.sqrt (df2oPar d n δ).k0 *
            (Real.sqrt (32 / 9 * d * xq d n δ / (df2oPar d n δ).δe) * (df2oPar d n δ).δe ^ 4) +
          8 / (df2oPar d n δ).eps * (df2oPar d n δ).δe ^ 4 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk]
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left hyc (by positivity))
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  have e1 : ∀ s ∈ Finset.range (t + 1),
      ((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ
          (y - ((df2CtxAtF d n δ Kt ap).st π s).mu) -
        ((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ
          (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) =
      ((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ (y - c) := by
    intro s _
    rw [← dotProduct_sub]; congr 1; abel
  rw [Finset.sum_congr rfl e1]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |((df2CtxAtF d n δ Kt ap).ghat π s - (df2CtxAtF d n δ Kt ap).sGrad π s) ⬝ᵥ
        (y - c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), Gq d n δ * (df2oPar d n δ).δe ^ 4 :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (Gq d n δ * (df2oPar d n δ).δe ^ 4) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ n * (Gq d n δ * (df2oPar d n δ).δe ^ 4) := mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

end path

end AdversarialBco.Poly.EvSI
