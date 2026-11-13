/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIRound
public import AdversarialBco.Poly.Df2EvVSumV

@[expose] public section

/-!
# One round up to the stopping time, with a routine per round

At the context `df2CtxAtF d n δ Kt ap` with a routine `ap s` in round `s` (`ap : ℕ → ApFun d`), on a path with the
hypotheses of DET without the events (`DetBase`), at a round `s ≤ τ`: the continuity, the integrability and the `L²`
membership of `yR = e² + pip²` under the Gaussian; Lemma UB' for the directions of LQ and of the Hessian (`mean_LV`,
`mean_HV`); Lemma TR for the same directions (`var_LV`, `var_HV`); `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` (`sumY_leV`) and
the fourth moment `E[(e² + pip²)²] ≤ 72 + 25600 (R⁴ + 3 d²)/ε⁴` (`intY2_leV`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

section ctx

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}


theorem lam_ltV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) : (df2oPar d n δ).lam < 1 := by
  have : (df2oPar d n δ).lam ≤ 1 / 2 := H.rows.lam_le
  linarith

theorem k0_eqV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) : (df2oPar d n δ).k0 = ((1 - (df2oPar d n δ).lam) ^ 2)⁻¹ := H.k0

theorem continuous_yRV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (st : Df2St d) :
    Continuous (yR n δ Kt (π.g s) st) := by
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv (H.stInv_le_tau s hs))
  have h1 := continuous_eR n δ Kt (π.g s) _ hsi.ext_lip st
  have h2 := continuous_pR n δ Kt H.body.1 H.body.2.2.1 st
  unfold yR
  exact (h1.pow 2).add (h2.pow 2)

theorem memLp_yRV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    MemLp (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s)) 2 (gam d) := by
  have hI := H.stInv_le_tau s hs
  exact memLp_two_of_poly (continuous_yRV H hs _).aestronglyMeasurable _ 2
    (yR_abs_le H.body (H.adm s (H.le_tau_lt hs)) H.rows.pos_eps H.heps H.rows.pos_lam.le (lam_ltV H).le
      (M0_nonneg _) (stB_of H hI))

theorem integrable_yRV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    Integrable (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s)) (gam d) :=
  (memLp_yRV H hs).integrable one_le_two

/-- Lemma UB' for the direction of LQ. -/
theorem mean_LV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (y : Fin d → ℝ) :
    ∫ z, eR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiL n δ y ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) =
      (df2CtxAtF d n δ Kt ap).sGrad π s ⬝ᵥ (y - ((df2CtxAtF d n δ Kt ap).st π s).mu) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_ltV H
  have hm := mean_lin (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hsi.ext_lip
    ((df2CtxAtF d n δ Kt ap).st π s).mu ((df2CtxAtF d n δ Kt ap).st π s).A ((df2CtxAtF d n δ Kt ap).st π s).P (P_mul_S hI) _ hl0 hl1 (y - ((df2CtxAtF d n δ Kt ap).st π s).mu)
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have e1 : (fun z => eR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiL n δ y ((df2CtxAtF d n δ Kt ap).st π s) z) = fun z =>
      df2Ext (df2oPar d n δ) Kt (π.g s) (WithLp.toLp 2 (((df2CtxAtF d n δ Kt ap).st π s).mu + (1 - (df2oPar d n δ).lam) •
        (((df2CtxAtF d n δ Kt ap).st π s).A *ᵥ z))) * ((((df2CtxAtF d n δ Kt ap).st π s).P *ᵥ (((df2CtxAtF d n δ Kt ap).st π s).A *ᵥ z)) ⬝ᵥ (y - ((df2CtxAtF d n δ Kt ap).st π s).mu)) /
        (1 - (df2oPar d n δ).lam) := by
    funext z; unfold eR phiL lin EvGY.xOf; ring
  rw [e1, integral_div, hm, mul_div_cancel_left₀ _ h1]
  rfl

/-- Lemma UB' for the direction of the Hessian. -/
theorem mean_HV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (hf : Df2St d → Fin d → ℝ) :
    ∫ z, eR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) =
      df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) (hf ((df2CtxAtF d n δ Kt ap).st π s)) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_ltV H
  have hm := mean_quad (df2Ext (df2oPar d n δ) Kt (π.g s)) (8 / (df2oPar d n δ).eps) hsi.ext_lip
    ((df2CtxAtF d n δ Kt ap).st π s).mu ((df2CtxAtF d n δ Kt ap).st π s).A ((df2CtxAtF d n δ Kt ap).st π s).P (P_mul_S hI) _ hl0 hl1 (hf ((df2CtxAtF d n δ Kt ap).st π s))
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have e1 : (fun z => eR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAtF d n δ Kt ap).st π s) z) = fun z =>
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 *
      (df2Ext (df2oPar d n δ) Kt (π.g s) (WithLp.toLp 2 (((df2CtxAtF d n δ Kt ap).st π s).mu + (1 - (df2oPar d n δ).lam) •
        (((df2CtxAtF d n δ Kt ap).st π s).A *ᵥ z))) * (((((df2CtxAtF d n δ Kt ap).st π s).P *ᵥ (((df2CtxAtF d n δ Kt ap).st π s).A *ᵥ z)) ⬝ᵥ hf ((df2CtxAtF d n δ Kt ap).st π s)) ^ 2 -
          df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (hf ((df2CtxAtF d n δ Kt ap).st π s)))) := by
    funext z; unfold eR phiH lin EvGY.xOf; ring
  rw [e1, integral_const_mul, hm, k0_eqV H]
  have key : ∀ X : ℝ, (df2oPar d n δ).lam * ((1 - (df2oPar d n δ).lam) ^ 2)⁻¹ *
      ((1 - (df2oPar d n δ).lam) ^ 2 / (df2oPar d n δ).lam * X) = X := by
    intro X; field_simp
  exact key _

/-- Lemma TR for the direction of LQ: `E[(e² + pip²) (⟨P A z, h⟩/(1 - λ))²]`. -/
theorem var_LV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (h : Fin d → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * (lin ((df2CtxAtF d n δ Kt ap).st π s) h z / (1 - (df2oPar d n δ).lam)) ^ 2 ∂(gam d) ≤
      (df2oPar d n δ).k0 * (df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P h *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) +
          Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) *
            Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  have hl1 := lam_ltV H
  have h1 : (1 - (df2oPar d n δ).lam) ≠ 0 := by linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eqV H]; positivity
  have e1 : (fun z => yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * (lin ((df2CtxAtF d n δ Kt ap).st π s) h z / (1 - (df2oPar d n δ).lam)) ^ 2) =
      fun z => (df2oPar d n δ).k0 * (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
        (z ⬝ᵥ (((df2CtxAtF d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAtF d n δ Kt ap).st π s).P *ᵥ h))) ^ 2) := by
    funext z; rw [lin_eq_dot _ (P_symm hI), k0_eqV H]; field_simp
  rw [e1, integral_const_mul]
  have htr := tr_dot (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s)) (yR_nonneg n δ Kt (π.g s) _) (memLp_yRV H hs)
    (((df2CtxAtF d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAtF d n δ Kt ap).st π s).P *ᵥ h)) T hT
  rw [dir_sq _ hI.AA hI.SP h] at htr
  exact mul_le_mul_of_nonneg_left htr hk0

/-- Lemma TR for the direction of the Hessian. -/
theorem var_HV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (hf : Df2St d → Fin d → ℝ) (T : ℝ)
    (hT : 1 ≤ T) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (hf ((df2CtxAtF d n δ Kt ap).st π s)) ^ 2 *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) +
          Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) *
            Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  set b := ((df2CtxAtF d n δ Kt ap).st π s).Aᵀ *ᵥ (((df2CtxAtF d n δ Kt ap).st π s).P *ᵥ hf ((df2CtxAtF d n δ Kt ap).st π s)) with hb
  have hbb : b ⬝ᵥ b = df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (hf ((df2CtxAtF d n δ Kt ap).st π s)) := dir_sq _ hI.AA hI.SP _
  have e1 : (fun z => yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z * phiH n δ hf ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2) =
      fun z => ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
        ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 2) := by
    funext z; unfold phiH; rw [lin_eq_dot _ (P_symm hI), ← hb, hbb]; ring
  rw [e1, integral_const_mul]
  have htr := tr_quad (yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s)) (yR_nonneg n δ Kt (π.g s) _) (memLp_yRV H hs) b T hT
  rw [← hbb]
  exact mul_le_mul_of_nonneg_left htr (sq_nonneg _)

/-- `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` for `t ≤ τ`. -/
theorem sumY_leV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) ≤ 9 * n := by
  have hv := EvGY.vsum_leV H.SI d n δ Kt ap π m H.hd H.hn H.hδ0 H.hδ1 H.heps H.hm1 H.hmn H.body H.hap H.adm t ht
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have he2 : 0 < (df2oPar d n δ).eps ^ 2 := by positivity
  have hpt : ∀ s ≤ t, ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) ≤
      6 + 10 / (df2oPar d n δ).eps ^ 2 * ∫ z, (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) := by
    intro s hst
    have hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m := hst.trans ht
    have hI := H.stInv_le_tau s hs
    have hc := continuous_pR n δ Kt H.body.1 H.body.2.2.1 ((df2CtxAtF d n δ Kt ap).st π s)
    have hb : ∀ z, |(pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2| ≤
        (kF d n δ (M0 (df2oPar d n δ)) + 1) ^ 2 * (1 + ‖z‖) ^ 2 := by
      intro z
      have h2 : |pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z| ≤ kF d n δ (M0 (df2oPar d n δ)) * (1 + ‖z‖) :=
        (eR_pR_le H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_ltV H).le
          (M0_nonneg _) (stB_of H hI) z).2
      have hz : 0 ≤ ‖z‖ := norm_nonneg z
      have hk := kF_nonneg n δ (M0 (df2oPar d n δ)) he0
      rw [abs_of_nonneg (sq_nonneg _)]
      have h3 : |pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1| ≤
          (kF d n δ (M0 (df2oPar d n δ)) + 1) * (1 + ‖z‖) := by
        have := abs_sub (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z) 1
        rw [abs_one] at this
        nlinarith
      calc _ = |pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1| ^ 2 := (sq_abs _).symm
        _ ≤ ((kF d n δ (M0 (df2oPar d n δ)) + 1) * (1 + ‖z‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = _ := by ring
    have hi2 : Integrable (fun z => (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2) (gam d) :=
      integrable_of_poly ((hc.sub continuous_const).pow 2).aestronglyMeasurable _ 2 hb
    have hi3 : Integrable (fun z => 6 + 10 / (df2oPar d n δ).eps ^ 2 *
        (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2) (gam d) :=
      (integrable_const 6).add (hi2.const_mul _)
    have hmono : ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) ≤
        ∫ z, (6 + 10 / (df2oPar d n δ).eps ^ 2 * (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2)
          ∂(gam d) := by
      refine integral_mono (integrable_yRV H hs) hi3 fun z => ?_
      have : yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ≤ 6 + 10 * (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 :=
        yR_le H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps ((df2CtxAtF d n δ Kt ap).st π s) z
      show yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ≤
        6 + 10 / (df2oPar d n δ).eps ^ 2 * (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [integral_add (integrable_const 6) (hi2.const_mul _), integral_const_mul, integral_const] at hmono
    simpa using hmono
  have hsum := Finset.sum_le_sum fun s hs => hpt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range] at hsum
  have hv' : ∑ s ∈ Finset.range (t + 1), ∫ z, (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) ≤
      3 / 10 * n * (df2oPar d n δ).eps ^ 2 := hv
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  have h3 : 10 / (df2oPar d n δ).eps ^ 2 * ∑ s ∈ Finset.range (t + 1),
      ∫ z, (pR n δ Kt ((df2CtxAtF d n δ Kt ap).st π s) z - 1) ^ 2 ∂(gam d) ≤ 3 * n := by
    calc _ ≤ 10 / (df2oPar d n δ).eps ^ 2 * (3 / 10 * n * (df2oPar d n δ).eps ^ 2) := by gcongr
      _ = 3 * n := by field_simp
  simp only [nsmul_eq_mul] at hsum
  linarith

/-- `E[(e² + pip²)²] ≤ 72 + 25600 (R⁴ + 3 d²)/ε⁴` for `s ≤ τ`. -/
theorem intY2_leV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      72 + 25600 * ((df2oPar d n δ).R ^ 4 + 3 * (d : ℝ) ^ 2) / (df2oPar d n δ).eps ^ 4 := by
  have hI := H.stInv_le_tau s hs
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hR : ((df2CtxAtF d n δ Kt ap).st π s).mu ⬝ᵥ ((df2CtxAtF d n δ Kt ap).st π s).mu ≤ (df2oPar d n δ).R ^ 2 :=
    mu_sq_le H hI
  set ε := (df2oPar d n δ).eps
  set R := (df2oPar d n δ).R
  have hpt : ∀ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ≤
      (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2 := by
    intro z
    have h1 := yR_le_poly H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_ltV H).le
      ((df2CtxAtF d n δ Kt ap).st π s) (A_sq_le H hI) z
    have h0 := yR_nonneg n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z
    have hz := dot_self_nonneg' z
    set u := ((df2CtxAtF d n δ Kt ap).st π s).mu ⬝ᵥ ((df2CtxAtF d n δ Kt ap).st π s).mu
    have hu := dot_self_nonneg' ((df2CtxAtF d n δ Kt ap).st π s).mu
    have hc80 : 0 ≤ 80 / ε ^ 2 := by positivity
    have h2 : yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ≤ 6 + 80 / ε ^ 2 * (R ^ 2 + z ⬝ᵥ z) := by
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
  have hc := continuous_yRV H hs ((df2CtxAtF d n δ Kt ap).st π s)
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
  have hi0 : Integrable (fun z => yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2) (gam d) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).1 (memLp_yRV H hs)
  have hi3 : Integrable (fun z : Fin d → ℝ => (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2)
      (gam d) := (integrable_const _).add (hi1.const_mul _)
  have hmono : ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
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
