/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSISDF
public import AdversarialBco.Poly.Df2EvSIRoundV

@[expose] public section

/-!
# The variance cap of S-DF, with a routine per round

At the context `df2CtxAtF d n δ Kt ap` with a routine `ap s` in round `s` (`ap : ℕ → ApFun d`), on a path with the
hypotheses of DET without the events (`DetBase`), with `φ_s = phiH (fun _ => v)` at the state of round `s`: the
integrability of `yR φ_s²` for `s ≤ τ` (`integrable_yR_phiHV`), and the variance cap
`∑_{s ≤ t} E[(e_s² + pip_s²) φ_s²] ≤ (λ κ₀)² q_t(v)² Xv` for `t ≤ τ` (`vsum_phiH_leV`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI.SDF

open Layer2

variable {d : ℕ}

section ctx

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}

theorem integrable_yR_phiHV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (v : Fin d → ℝ) :
    Integrable (fun z => yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
      phiH n δ (fun _ => v) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2) (gam d) := by
  have hI := H.stInv_le_tau s hs
  have hst := stB_of H hI
  have hM := M0_nonneg (df2oPar d n δ)
  have hc := (continuous_yRV H hs ((df2CtxAtF d n δ Kt ap).st π s)).mul
    ((continuous_phiH n δ v ((df2CtxAtF d n δ Kt ap).st π s)).pow 2)
  refine integrable_of_poly hc.aestronglyMeasurable
    (2 * kF d n δ (M0 (df2oPar d n δ)) ^ 2 * kPhi (df2oPar d n δ) d (M0 (df2oPar d n δ)) v ^ 2) 6 fun z => ?_
  have h1 := yR_abs_le H.body (H.adm s (H.le_tau_lt hs)) H.rows.pos_eps H.heps H.rows.pos_lam.le (lam_ltV H).le hM
    hst z
  have h2 := phiH_le n δ _ hM v _ hst z
  have hz : 0 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hk := kPhi_nonneg (df2oPar d n δ) d (M0 (df2oPar d n δ)) v
  have h3 : phiH n δ (fun _ => v) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ≤
      (kPhi (df2oPar d n δ) d (M0 (df2oPar d n δ)) v * (1 + ‖z‖) ^ 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [abs_mul, abs_of_nonneg (sq_nonneg (phiH n δ (fun _ => v) ((df2CtxAtF d n δ Kt ap).st π s) z))]
  calc |yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z| *
        phiH n δ (fun _ => v) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2
      ≤ (2 * kF d n δ (M0 (df2oPar d n δ)) ^ 2 * (1 + ‖z‖) ^ 2) *
          (kPhi (df2oPar d n δ) d (M0 (df2oPar d n δ)) v * (1 + ‖z‖) ^ 2) ^ 2 :=
        mul_le_mul h1 h3 (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- The variance cap: `∑_{s ≤ t} E[(e_s² + pip_s²) φ_s²] ≤ (λ κ₀)² q_t(v)² Xv` for `t ≤ τ`. -/
theorem vsum_phiH_leV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {t : ℕ}
    (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) (v : Fin d → ℝ) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
        phiH n δ (fun _ => v) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 *
        (2 * df2Sq ((df2CtxAtF d n δ Kt ap).PBar π t) v) ^ 2 * xvS (df2oPar d n δ) d n := by
  set c := df2CtxAtF d n δ Kt ap with hc
  set p := df2oPar d n δ with hp
  set T := (16 * Real.log (1 / p.δe)) ^ 2 with hT
  set q := 2 * df2Sq (c.PBar π t) v with hq
  set W := Real.sqrt (72 + 25600 * (p.R ^ 4 + 3 * (d : ℝ) ^ 2) / p.eps ^ 4) *
    Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) with hW
  have hx : 14 ≤ Real.log (1 / p.δe) := H.x_ge
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hW0 : 0 ≤ W := by positivity
  have hlk := sq_nonneg (p.lam * p.k0)
  have hpt : ∀ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) (c.st π s) z *
      phiH n δ (fun _ => v) (c.st π s) z ^ 2 ∂(gam d) ≤
      (p.lam * p.k0) ^ 2 * q ^ 2 * (T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) + W) := by
    intro s hs'
    have hst : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs')
    have hs : s ≤ c.tau π m := hst.trans ht
    have hI := H.stInv_le_tau s hs
    have hv := var_HV H hs (fun _ => v) T hT1
    have hP0 := sq_nonneg_of_psd hI.pd.posSemidef v
    have hPq : df2Sq (c.st π s).P v ≤ q := P_quad_le H hst ht v
    have hP2 : df2Sq (c.st π s).P v ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hP0 hPq 2
    have hY0 : 0 ≤ ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) :=
      integral_nonneg fun z => yR_nonneg n δ Kt (π.g s) _ z
    have hY2 := intY2_leV H hs
    have hsq : Real.sqrt (∫ z, yR n δ Kt (π.g s) (c.st π s) z ^ 2 ∂(gam d)) ≤
        Real.sqrt (72 + 25600 * (p.R ^ 4 + 3 * (d : ℝ) ^ 2) / p.eps ^ 4) := Real.sqrt_le_sqrt hY2
    have hbr : T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) (c.st π s) z ^ 2 ∂(gam d)) *
          Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) ≤
        T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) + W := by
      rw [hW]; gcongr
    have hbr0 : 0 ≤ T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) (c.st π s) z ^ 2 ∂(gam d)) *
          Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) := by positivity
    refine hv.trans ?_
    calc (p.lam * p.k0) ^ 2 * (df2Sq (c.st π s).P v ^ 2 * (T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) +
          Real.sqrt (∫ z, yR n δ Kt (π.g s) (c.st π s) z ^ 2 ∂(gam d)) *
            Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4))))
        ≤ (p.lam * p.k0) ^ 2 * (q ^ 2 * (T * ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) + W)) := by
          gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hpt
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hY := sumY_leV H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have := H.le_tau_lt ht; have : m ≤ n := H.hmn; exact_mod_cast (by omega : t + 1 ≤ n)
  refine hsum.trans ?_
  have hxv : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) +
      ((t + 1 : ℕ) : ℝ) * W ≤ xvS p d n := by
    unfold xvS
    rw [← hT, ← hW]
    have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) ≤ T * (9 * n) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have h2 : ((t + 1 : ℕ) : ℝ) * W ≤ n * W := mul_le_mul_of_nonneg_right htn hW0
    linarith
  calc (p.lam * p.k0) ^ 2 * q ^ 2 * (T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) (c.st π s) z ∂(gam d) +
        ((t + 1 : ℕ) : ℝ) * W) ≤ (p.lam * p.k0) ^ 2 * q ^ 2 * xvS p d n := by gcongr

end ctx

end AdversarialBco.Poly.EvSI.SDF
