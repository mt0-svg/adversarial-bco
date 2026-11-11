/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIPath
public import AdversarialBco.Poly.Df2EvSIMat

@[expose] public section

/-!
# One round up to the stopping time: means and second moments

At a round `s ≤ τ` of the context at the parameters, with `e_s`, `pip_s` at `X(z) = μ_s + (1 - λ) A_s z`:

* `mean_L`, `mean_H`: the Gaussian means of `e_s φ` for the directions of LQ and of the Hessian are
  `⟨s'_s(μ_s), y - μ_s⟩` and `hᵀ s''_s(μ_s) h` (Lemma D.3);
* `var_L`, `var_H`: the second moments of `(e_s, pip_s) φ` against the truncation `T` (Lemma TR);
* `sumY_le`: `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` (from `vsum_le`); `intY2_le`: `E[(e_s² + pip_s²)²] ≤ Wb`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-! ## The functions of a round -/

/-- The extension of a round at the draw `z` from the state `st`. -/
noncomputable def eR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Ext (df2oPar d n δ) K g (WithLp.toLp 2 (EvGY.xOf n δ st z))

/-- The gauge factor of a round at the draw `z` from the state `st`. -/
noncomputable def pR (n : ℕ) (δ : ℝ) (K : Set (E d)) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Pip (df2oPar d n δ) K (WithLp.toLp 2 (EvGY.xOf n δ st z))

/-- `e² + pip²`. -/
noncomputable def yR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  eR n δ K g st z ^ 2 + pR n δ K st z ^ 2

theorem continuous_xOf (n : ℕ) (δ : ℝ) (st : Df2St d) :
    Continuous fun z => (WithLp.toLp 2 (EvGY.xOf n δ st z) : E d) := by
  unfold EvGY.xOf
  have h : Continuous fun z : Fin d → ℝ => st.A *ᵥ z := (Matrix.mulVecLin st.A).continuous_of_finiteDimensional
  have h2 : Continuous fun z : Fin d → ℝ => st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ z) :=
    continuous_const.add (Continuous.const_smul h (1 - (df2oPar d n δ).lam))
  exact (PiLp.continuous_toLp 2 _).comp h2

theorem continuous_eR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (L : ℝ)
    (hL : ∀ x y, |df2Ext (df2oPar d n δ) K g x - df2Ext (df2oPar d n δ) K g y| ≤ L * ‖x - y‖) (st : Df2St d) :
    Continuous (eR n δ K g st) :=
  (continuous_of_lip _ L hL).comp (continuous_xOf n δ st)

theorem continuous_pR (n : ℕ) (δ : ℝ) (K : Set (E d)) (hK : Convex ℝ K) (hball : Metric.closedBall 0 1 ⊆ K)
    (st : Df2St d) : Continuous (pR n δ K st) := by
  have hn : K ∈ nhds (0 : E d) := Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball
  have hg : Continuous (gauge K) := continuous_gauge hK hn
  unfold pR df2Pip
  exact continuous_const.max ((hg.comp (continuous_xOf n δ st)).div_const _)

/-! ## Integrability -/

theorem integrable_of_poly {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gam d)) (K : ℝ) (k : ℕ)
    (hb : ∀ z, |f z| ≤ K * (1 + ‖z‖) ^ k) : Integrable f (gam d) :=
  ((integrable_poly_gam k).const_mul K).mono' hf
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)

theorem memLp_two_of_poly {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gam d)) (K : ℝ) (k : ℕ)
    (hb : ∀ z, |f z| ≤ K * (1 + ‖z‖) ^ k) : MemLp f 2 (gam d) := by
  rw [memLp_two_iff_integrable_sq hf]
  refine integrable_of_poly (hf.pow 2) (K ^ 2) (k * 2) fun z => ?_
  rw [abs_pow, pow_mul]
  calc |f z| ^ 2 ≤ (K * (1 + ‖z‖) ^ k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb z) 2
    _ = K ^ 2 * ((1 + ‖z‖) ^ k) ^ 2 := by ring

/-! ## Pointwise bounds -/

theorem eR_pR_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) {M : ℝ} (hM : 0 ≤ M) {st : Df2St d}
    (hst : stB M st) (z : Fin d → ℝ) :
    |eR n δ K g st z| ≤ kF d n δ M * (1 + ‖z‖) ∧ |pR n δ K st z| ≤ kF d n δ M * (1 + ‖z‖) :=
  fF_fP_le n δ (fun _ : Unit => K) (fun _ _ => g) (m := 1) (fun _ => hbody) (fun _ _ _ => hg) he0 he1 hl0 hl1 hM
    (s := 0) Nat.zero_lt_one (((), st), z) hst

theorem yR_nonneg (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) :
    0 ≤ yR n δ K g st z := by
  unfold yR; positivity

theorem yR_abs_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) {M : ℝ} (hM : 0 ≤ M) {st : Df2St d}
    (hst : stB M st) (z : Fin d → ℝ) :
    |yR n δ K g st z| ≤ 2 * kF d n δ M ^ 2 * (1 + ‖z‖) ^ 2 := by
  obtain ⟨h1, h2⟩ := eR_pR_le hbody hg he0 he1 hl0 hl1 hM hst z
  rw [abs_of_nonneg (yR_nonneg n δ K g st z)]
  unfold yR
  have a1 : eR n δ K g st z ^ 2 ≤ (kF d n δ M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : pR n δ K st z ^ 2 ≤ (kF d n δ M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith

/-- `e² + pip² ≤ 6 + 10 (pip - 1)²/ε²`. -/
theorem yR_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2) (st : Df2St d)
    (z : Fin d → ℝ) :
    yR n δ K g st z ≤ 6 + 10 * (pR n δ K st z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 := by
  obtain ⟨hF0, hF1, hP1, -⟩ := ext_pip_bounds n δ K hbody g hg he0 he1 (WithLp.toLp 2 (EvGY.xOf n δ st z))
  unfold yR
  change df2Ext (df2oPar d n δ) K g _ ^ 2 + df2Pip (df2oPar d n δ) K _ ^ 2 ≤
    6 + 10 * (df2Pip (df2oPar d n δ) K _ - 1) ^ 2 / (df2oPar d n δ).eps ^ 2
  set ε := (df2oPar d n δ).eps
  set q := df2Pip (df2oPar d n δ) K (WithLp.toLp 2 (EvGY.xOf n δ st z))
  set F := df2Ext (df2oPar d n δ) K g (WithLp.toLp 2 (EvGY.xOf n δ st z))
  set u := (q - 1) / ε with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) he0.le
  have hqu : q - 1 = ε * u := by rw [hu]; field_simp
  have hq : q ≤ 1 + u / 2 := by nlinarith
  have hF : F ≤ 1 + 5 / 2 * u := by
    have : F ≤ q + 2 * u := by rw [hu]; linarith [show 2 * (q - 1) / ε = 2 * ((q - 1) / ε) by ring]
    linarith
  have e10 : 10 * (q - 1) ^ 2 / ε ^ 2 = 10 * u ^ 2 := by rw [hqu]; field_simp
  rw [e10]
  have hF2 : F ^ 2 ≤ (1 + 5 / 2 * u) ^ 2 := pow_le_pow_left₀ hF0 hF 2
  have hq2 : q ^ 2 ≤ (1 + u / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hq 2
  nlinarith [sq_nonneg (3 / 2 * u - 2)]

/-- `pip - 1 ≤ 2 (|μ| + |z|)` when `|A w| ≤ |w|`. -/
theorem pR_sub_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) (st : Df2St d)
    (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    0 ≤ pR n δ K st z - 1 ∧
      pR n δ K st z - 1 ≤ 2 * (Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z)) := by
  obtain ⟨-, -, hP1, hP2⟩ := ext_pip_bounds n δ K hbody g hg he0 he1 (WithLp.toLp 2 (EvGY.xOf n δ st z))
  refine ⟨by unfold pR; linarith, ?_⟩
  have hX : ‖(WithLp.toLp 2 (EvGY.xOf n δ st z) : E d)‖ ≤ Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z) := by
    rw [norm_toLp]
    unfold EvGY.xOf
    have t := (oNorm_tri st.mu ((1 - (df2oPar d n δ).lam) • (st.A *ᵥ z)) 0 ∅ fun _ => 0).1
    have ta := (oNorm_tri (st.A *ᵥ z) 0 (1 - (df2oPar d n δ).lam) ∅ fun _ => 0).2.1
    have hab : |1 - (df2oPar d n δ).lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hAz : Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) ≤ Real.sqrt (z ⬝ᵥ z) := Real.sqrt_le_sqrt (hA z)
    rw [ta] at t
    have h0 := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
    nlinarith [abs_nonneg (1 - (df2oPar d n δ).lam)]
  unfold pR; linarith

/-- `e² + pip² ≤ 6 + 80 (|μ|² + |z|²)/ε²`. -/
theorem yR_le_poly {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) (st : Df2St d)
    (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    yR n δ K g st z ≤ 6 + 80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / (df2oPar d n δ).eps ^ 2 := by
  have h1 := yR_le hbody hg he0 he1 st z
  obtain ⟨h0, h2⟩ := pR_sub_le hbody hg he0 he1 hl0 hl1 st hA z
  have hm := Real.sq_sqrt (dot_self_nonneg' st.mu)
  have hz := Real.sq_sqrt (dot_self_nonneg' z)
  have h3 : (pR n δ K st z - 1) ^ 2 ≤ 8 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) := by
    have := pow_le_pow_left₀ h0 h2 2
    nlinarith [sq_nonneg (Real.sqrt (st.mu ⬝ᵥ st.mu) - Real.sqrt (z ⬝ᵥ z))]
  have he2 : 0 < (df2oPar d n δ).eps ^ 2 := by positivity
  have h4 : 10 * (pR n δ K st z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 ≤
      80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / (df2oPar d n δ).eps ^ 2 := by
    apply div_le_div_of_nonneg_right _ he2.le; linarith
  linarith

/-! ## A round of the context at the parameters, up to `τ` -/

section ctx

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ApFun d} {π : Df2Path d} {m : ℕ}


theorem lam_lt (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) : (df2oPar d n δ).lam < 1 := by
  have : (df2oPar d n δ).lam ≤ 1 / 2 := H.rows.lam_le
  linarith

theorem k0_eq (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) : (df2oPar d n δ).k0 = ((1 - (df2oPar d n δ).lam) ^ 2)⁻¹ := H.k0

theorem continuous_yR (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (st : Df2St d) :
    Continuous (yR n δ Kt (π.g s) st) := by
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv (H.stInv_le_tau s hs))
  have h1 := continuous_eR n δ Kt (π.g s) _ hsi.ext_lip st
  have h2 := continuous_pR n δ Kt H.body.1 H.body.2.2.1 st
  unfold yR
  exact (h1.pow 2).add (h2.pow 2)

theorem memLp_yR (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    MemLp (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s)) 2 (gam d) := by
  have hI := H.stInv_le_tau s hs
  exact memLp_two_of_poly (continuous_yR H hs _).aestronglyMeasurable _ 2
    (yR_abs_le H.body (H.adm s (H.le_tau_lt hs)) H.rows.pos_eps H.heps H.rows.pos_lam.le (lam_lt H).le
      (M0_nonneg _) (stB_of H hI))

theorem integrable_yR (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    Integrable (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s)) (gam d) :=
  (memLp_yR H hs).integrable one_le_two

/-- Lemma D.3 for the direction of LQ. -/
theorem mean_L (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (y : Fin d → ℝ) :
    ∫ z, eR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiL n δ y ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) =
      (df2CtxAt d n δ Kt ap).sGrad π s ⬝ᵥ (y - ((df2CtxAt d n δ Kt ap).st π s).mu) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_lt H
  have hm := mean_lin (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hsi.ext_lip
    ((df2CtxAt d n δ Kt ap).st π s).mu ((df2CtxAt d n δ Kt ap).st π s).A ((df2CtxAt d n δ Kt ap).st π s).P (P_mul_S hI) _ hl0 hl1 (y - ((df2CtxAt d n δ Kt ap).st π s).mu)
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have e1 : (fun z => eR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiL n δ y ((df2CtxAt d n δ Kt ap).st π s) z) = fun z =>
      df2Ext (df2oPar d n δ) Kt (π.g s) (WithLp.toLp 2 (((df2CtxAt d n δ Kt ap).st π s).mu + (1 - (df2oPar d n δ).lam) •
        (((df2CtxAt d n δ Kt ap).st π s).A *ᵥ z))) * ((((df2CtxAt d n δ Kt ap).st π s).P *ᵥ (((df2CtxAt d n δ Kt ap).st π s).A *ᵥ z)) ⬝ᵥ (y - ((df2CtxAt d n δ Kt ap).st π s).mu)) /
        (1 - (df2oPar d n δ).lam) := by
    funext z; unfold eR phiL lin EvGY.xOf; ring
  rw [e1, integral_div, hm, mul_div_cancel_left₀ _ h1]
  rfl

/-- Lemma D.3 for the direction of the Hessian. -/
theorem mean_H (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (hf : Df2St d → Fin d → ℝ) :
    ∫ z, eR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) =
      df2Sq ((df2CtxAt d n δ Kt ap).sHess π s) (hf ((df2CtxAt d n δ Kt ap).st π s)) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_lt H
  have hm := mean_quad (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hsi.ext_lip
    ((df2CtxAt d n δ Kt ap).st π s).mu ((df2CtxAt d n δ Kt ap).st π s).A ((df2CtxAt d n δ Kt ap).st π s).P (P_mul_S hI) _ hl0 hl1 (hf ((df2CtxAt d n δ Kt ap).st π s))
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have e1 : (fun z => eR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAt d n δ Kt ap).st π s) z) = fun z =>
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 *
      (df2Ext (df2oPar d n δ) Kt (π.g s) (WithLp.toLp 2 (((df2CtxAt d n δ Kt ap).st π s).mu + (1 - (df2oPar d n δ).lam) •
        (((df2CtxAt d n δ Kt ap).st π s).A *ᵥ z))) * (((((df2CtxAt d n δ Kt ap).st π s).P *ᵥ (((df2CtxAt d n δ Kt ap).st π s).A *ᵥ z)) ⬝ᵥ hf ((df2CtxAt d n δ Kt ap).st π s)) ^ 2 -
          df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (hf ((df2CtxAt d n δ Kt ap).st π s)))) := by
    funext z; unfold eR phiH lin EvGY.xOf; ring
  rw [e1, integral_const_mul, hm, k0_eq H]
  have key : ∀ X : ℝ, (df2oPar d n δ).lam * ((1 - (df2oPar d n δ).lam) ^ 2)⁻¹ *
      ((1 - (df2oPar d n δ).lam) ^ 2 / (df2oPar d n δ).lam * X) = X := by
    intro X; field_simp
  exact key _

/-- Lemma TR for the direction of LQ: `E[(e² + pip²) (⟨P A z, h⟩/(1 - λ))²]`. -/
theorem var_L (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (h : Fin d → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * (lin ((df2CtxAt d n δ Kt ap).st π s) h z / (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤
      (df2oPar d n δ).k0 * (df2Sq ((df2CtxAt d n δ Kt ap).st π s).P h *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) +
          Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) *
            Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  have hl1 := lam_lt H
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eq H]; positivity
  have e1 : (fun z => yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * (lin ((df2CtxAt d n δ Kt ap).st π s) h z / (1 - (df2oPar d n δ).lam)) ^ 2) =
      fun z => (df2oPar d n δ).k0 * (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
        (z ⬝ᵥ (((df2CtxAt d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAt d n δ Kt ap).st π s).P *ᵥ h))) ^ 2) := by
    funext z; rw [lin_eq_dot _ (P_symm hI), k0_eq H]; field_simp
  rw [e1, integral_const_mul]
  have htr := tr_dot (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s)) (yR_nonneg n δ Kt (π.g s) _) (memLp_yR H hs)
    (((df2CtxAt d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAt d n δ Kt ap).st π s).P *ᵥ h)) T hT
  rw [dir_sq _ hI.AA hI.SP h] at htr
  exact mul_le_mul_of_nonneg_left htr hk0

/-- Lemma TR for the direction of the Hessian. -/
theorem var_H (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) (hf : Df2St d → Fin d → ℝ) (T : ℝ)
    (hT : 1 ≤ T) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (hf ((df2CtxAt d n δ Kt ap).st π s)) ^ 2 *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) +
          Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) *
            Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  set b := ((df2CtxAt d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAt d n δ Kt ap).st π s).P *ᵥ hf ((df2CtxAt d n δ Kt ap).st π s)) with hb
  have hbb : b ⬝ᵥ b = df2Sq ((df2CtxAt d n δ Kt ap).st π s).P (hf ((df2CtxAt d n δ Kt ap).st π s)) := dir_sq _ hI.AA hI.SP _
  have e1 : (fun z => yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAt d n δ Kt ap).st π s) z ^ 2) =
      fun z => ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z *
        ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 2) := by
    funext z; unfold phiH; rw [lin_eq_dot _ (P_symm hI), ← hb, hbb]; ring
  rw [e1, integral_const_mul]
  have htr := tr_quad (yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s)) (yR_nonneg n δ Kt (π.g s) _) (memLp_yR H hs) b T hT
  rw [← hbb]
  exact mul_le_mul_of_nonneg_left htr (sq_nonneg _)

/-- `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` for `t ≤ τ`. -/
theorem sumY_le (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) ≤ 9 * n := by
  have hv := EvGY.vsum_le H.SI d n δ Kt ap π m H.hd H.hn H.hδ0 H.hδ1 H.heps H.hm1 H.hmn H.body H.hap H.adm t ht
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have he2 : 0 < (df2oPar d n δ).eps ^ 2 := by positivity
  have hpt : ∀ s ≤ t, ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) ≤
      6 + 10 / (df2oPar d n δ).eps ^ 2 * ∫ z, (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) := by
    intro s hst
    have hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m := hst.trans ht
    have hI := H.stInv_le_tau s hs
    have hc := continuous_pR n δ Kt H.body.1 H.body.2.2.1 ((df2CtxAt d n δ Kt ap).st π s)
    have hb : ∀ z, |(pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2| ≤
        (kF d n δ (M0 (df2oPar d n δ)) + 1) ^ 2 * (1 + ‖z‖) ^ 2 := by
      intro z
      have h2 : |pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z| ≤ kF d n δ (M0 (df2oPar d n δ)) * (1 + ‖z‖) :=
        (eR_pR_le H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_lt H).le
          (M0_nonneg _) (stB_of H hI) z).2
      have hz : 0 ≤ ‖z‖ := norm_nonneg z
      have hk := kF_nonneg n δ (M0 (df2oPar d n δ)) he0
      rw [abs_of_nonneg (sq_nonneg _)]
      have h3 : |pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1| ≤
          (kF d n δ (M0 (df2oPar d n δ)) + 1) * (1 + ‖z‖) := by
        have := abs_sub (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z) 1
        rw [abs_one] at this
        nlinarith
      calc _ = |pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1| ^ 2 := (sq_abs _).symm
        _ ≤ ((kF d n δ (M0 (df2oPar d n δ)) + 1) * (1 + ‖z‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = _ := by ring
    have hi2 : Integrable (fun z => (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2) (gam d) :=
      integrable_of_poly ((hc.sub continuous_const).pow 2).aestronglyMeasurable _ 2 hb
    have hi3 : Integrable (fun z => 6 + 10 / (df2oPar d n δ).eps ^ 2 *
        (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2) (gam d) :=
      (integrable_const 6).add (hi2.const_mul _)
    have hmono : ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ∂(gam d) ≤
        ∫ z, (6 + 10 / (df2oPar d n δ).eps ^ 2 * (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2)
          ∂(gam d) := by
      refine integral_mono (integrable_yR H hs) hi3 fun z => ?_
      have : yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ≤ 6 + 10 * (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 :=
        yR_le H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps ((df2CtxAt d n δ Kt ap).st π s) z
      show yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ≤
        6 + 10 / (df2oPar d n δ).eps ^ 2 * (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [integral_add (integrable_const 6) (hi2.const_mul _), integral_const_mul, integral_const] at hmono
    simpa using hmono
  have hsum := Finset.sum_le_sum fun s hs => hpt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range] at hsum
  have hv' : ∑ s ∈ Finset.range (t + 1), ∫ z, (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) ≤
      3 / 10 * n * (df2oPar d n δ).eps ^ 2 := hv
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  have h3 : 10 / (df2oPar d n δ).eps ^ 2 * ∑ s ∈ Finset.range (t + 1),
      ∫ z, (pR n δ Kt ((df2CtxAt d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) ≤ 3 * n := by
    calc _ ≤ 10 / (df2oPar d n δ).eps ^ 2 * (3 / 10 * n * (df2oPar d n δ).eps ^ 2) := by gcongr
      _ = 3 * n := by field_simp
  simp only [nsmul_eq_mul] at hsum
  linarith

/-- `E[(e² + pip²)²] ≤ 72 + 25600 (R⁴ + 3 d²)/ε⁴` for `s ≤ τ`. -/
theorem intY2_le (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      72 + 25600 * ((df2oPar d n δ).R ^ 4 + 3 * (d : ℝ) ^ 2) / (df2oPar d n δ).eps ^ 4 := by
  have hI := H.stInv_le_tau s hs
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hR : ((df2CtxAt d n δ Kt ap).st π s).mu ⬝ᵥ ((df2CtxAt d n δ Kt ap).st π s).mu ≤ (df2oPar d n δ).R ^ 2 :=
    mu_sq_le H hI
  set ε := (df2oPar d n δ).eps
  set R := (df2oPar d n δ).R
  have hpt : ∀ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ≤
      (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2 := by
    intro z
    have h1 := yR_le_poly H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_lt H).le
      ((df2CtxAt d n δ Kt ap).st π s) (A_sq_le H hI) z
    have h0 := yR_nonneg n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z
    have hz := dot_self_nonneg' z
    set u := ((df2CtxAt d n δ Kt ap).st π s).mu ⬝ᵥ ((df2CtxAt d n δ Kt ap).st π s).mu
    have hu := dot_self_nonneg' ((df2CtxAt d n δ Kt ap).st π s).mu
    have hc80 : 0 ≤ 80 / ε ^ 2 := by positivity
    have h2 : yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ≤ 6 + 80 / ε ^ 2 * (R ^ 2 + z ⬝ᵥ z) := by
      calc _ ≤ 6 + 80 * (u + z ⬝ᵥ z) / ε ^ 2 := h1
        _ = 6 + 80 / ε ^ 2 * (u + z ⬝ᵥ z) := by ring
        _ ≤ 6 + 80 / ε ^ 2 * (R ^ 2 + z ⬝ᵥ z) := by
          have : u + z ⬝ᵥ z ≤ R ^ 2 + z ⬝ᵥ z := by linarith
          nlinarith [mul_le_mul_of_nonneg_left this hc80]
    have h3 := pow_le_pow_left₀ h0 h2 2
    set a := 80 / ε ^ 2
    have ha : a ^ 2 = 6400 / ε ^ 4 := by rw [show a = 80 / ε ^ 2 from rfl]; ring
    have e1 : 25600 / ε ^ 4 = 4 * a ^ 2 := by rw [ha]; ring
    rw [e1]
    have hR2 := sq_nonneg (R ^ 2 - z ⬝ᵥ z)
    have hb := sq_nonneg (6 - a * (R ^ 2 + z ⬝ᵥ z))
    nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) hR2]
  have hc := continuous_yR H hs ((df2CtxAt d n δ Kt ap).st π s)
  have hzz : Continuous fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2 := by
    have : Continuous fun z : Fin d → ℝ => z ⬝ᵥ z := by
      unfold dotProduct; fun_prop
    exact this.pow 2
  have hbz : ∀ z : Fin d → ℝ, |(z ⬝ᵥ z) ^ 2| ≤ (d : ℝ) ^ 2 * (1 + ‖z‖) ^ 4 := by
    intro z
    have h1 := dot_self_le z
    have hz := dot_self_nonneg' z
    have hn := norm_nonneg z
    rw [abs_of_nonneg (sq_nonneg _)]
    have h2 : z ⬝ᵥ z ≤ d * (1 + ‖z‖) ^ 2 := h1.trans (by gcongr; nlinarith)
    calc (z ⬝ᵥ z) ^ 2 ≤ (d * (1 + ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ hz h2 2
      _ = _ := by ring
  have hi1 : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) (gam d) :=
    integrable_of_poly hzz.aestronglyMeasurable _ 4 hbz
  have hi0 : Integrable (fun z => yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2) (gam d) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).1 (memLp_yR H hs)
  have hi3 : Integrable (fun z : Fin d → ℝ => (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2)
      (gam d) := (integrable_const _).add (hi1.const_mul _)
  have hmono : ∫ z, yR n δ Kt (π.g s) ((df2CtxAt d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ∫ z, ((72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2) ∂(gam d) :=
    integral_mono hi0 hi3 hpt
  rw [integral_add (integrable_const _) (hi1.const_mul _), integral_const_mul, integral_const] at hmono
  have h4 := integral_dot_self_sq_le (d := d)
  have he4 : 0 ≤ 25600 / ε ^ 4 := by positivity
  rw [show (gam d).real Set.univ = 1 by simp, one_smul] at hmono
  have h5 : 25600 / ε ^ 4 * ∫ z, (z ⬝ᵥ z) ^ 2 ∂(gam d) ≤ 25600 / ε ^ 4 * (3 * (d : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left h4 he4
  calc _ ≤ _ := hmono
    _ ≤ 72 + 25600 / ε ^ 4 * R ^ 4 + 25600 / ε ^ 4 * (3 * (d : ℝ) ^ 2) := by linarith
    _ = _ := by ring

end ctx

end AdversarialBco.Poly.EvSI
