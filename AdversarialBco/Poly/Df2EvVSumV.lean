/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvVSum

@[expose] public section

/-!
# The second moments of `v = pip - 1` under the plays, with a routine per round

At the context `df2CtxAtF d n δ Kt ap` with a routine `ap s` in round `s` (`ap : ℕ → ApFun d`): the hypotheses of DET
without the events from the budgets (`detBaseV`); at a round `s ≤ τ`, the spread of the play `‖(1 - λ) A_s‖ ≤ 1/(2 √L)`
(`playT_norm_leV`) and the crude and fine bounds on `E v²` (`vmom_crudeV`, `vmom_fineV`); and the sum of the second
moments up to `t ≤ τ`, at most `n ε²/4` (`vsum_le_quarterV`), so at most `(3/10) n ε²`, the paper's bound (`vsum_leV`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly.EvGY

open Layer2

variable {d : ℕ}

/-- The hypotheses of DET without the events, on the hypotheses of the budgets. -/
theorem detBaseV (hSI : Df2SIFacts) {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ∀ s, ApSpec (ap s)) (hadm : ∀ s < m, AdmLoss Kt (π.g s)) :
    DetBase (df2CtxAtF d n δ Kt ap) δ π m :=
  ⟨layerOne, lemmaW, hSI, hd, hn, hδ0, hδ1, rfl, heps, df2RowsHold d n δ hd hn hδ0 hδ1 heps, hm1, hmn, hbody,
    hap,
    hadm⟩


section Concrete

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}

/-- `‖(1 - λ) A_s‖ ≤ 1/(2 √L)` for `s ≤ τ`: the light invariant gives `|A_s w|² ≤ 2 σ² |w|²`, `σ² = 1/(8 L)`. -/
theorem playT_norm_leV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ‖playT (df2CtxAtF d n δ Kt ap) π s‖ ≤ 1 / (2 * Real.sqrt (df2oPar d n δ).Le) := by
  set c := df2CtxAtF d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  have hp : LPar c π :=
    ⟨H.rows.pos_sig2, H.rows.pos_de, H.kap_pos.le, heps1, H.body.2.2.1 (Metric.mem_closedBall_self zero_le_one),
      rfl⟩
  have hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v := fun u hu v =>
    sHess_nonneg c π u H.body (H.adm u (by have := H.tau_lt; omega)) H.rows.pos_eps heps1 H.rows.pos_lam v
  have hI := linv_le_tau c π hp H.hap hH s hs
  have hA : ∀ w, ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) ≤ 2 * c.p.sig2 * (w ⬝ᵥ w) :=
    fun w => hI.A_sq_le c π hp w
  have hN := toEuclideanCLM_norm_le (c.st π s).A (2 * c.p.sig2) (by have := H.rows.pos_sig2; positivity) hA
  have hsig : c.p.sig2 = 1 / (8 * (df2oPar d n δ).Le) := hP.sig2
  rw [hsig, sqrt_two_sig2 _ (by linarith [hP.L504])] at hN
  have hl0 := H.rows.pos_lam
  have hl1 := H.rows.lam_le
  unfold playT
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h0 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A‖ := norm_nonneg _
  nlinarith

/-- The crude bound at a round `s ≤ τ`: `E v² ≤ 4 ‖(1 - λ) A_s‖² d ≤ d/L`. -/
theorem vmom_crudeV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    vmom (df2CtxAtF d n δ Kt ap) π s ≤ d / (df2oPar d n δ).Le := by
  set c := df2CtxAtF d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, -⟩ := H.body
  have hmu := gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  rw [vmom_eq]
  refine (v_sq_crude c.Kt hK hKc hball c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu _).trans ?_
  have hT := playT_norm_leV H hs
  have hL := hP.L504
  have hsL := Real.sq_sqrt (show (0 : ℝ) ≤ (df2oPar d n δ).Le by linarith)
  have hsp := Real.sqrt_pos.2 (show (0 : ℝ) < (df2oPar d n δ).Le by linarith)
  have hT2 : ‖playT c π s‖ ^ 2 ≤ 1 / (4 * (df2oPar d n δ).Le) := by
    calc ‖playT c π s‖ ^ 2 ≤ (1 / (2 * Real.sqrt (df2oPar d n δ).Le)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ = 1 / (4 * (df2oPar d n δ).Le) := by rw [div_pow, mul_pow, hsL]; norm_num
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc 4 * ‖playT c π s‖ ^ 2 * d ≤ 4 * (1 / (4 * (df2oPar d n δ).Le)) * d := by gcongr
    _ = d / (df2oPar d n δ).Le := by field_simp

/-- The fine bound at a round `s ≤ τ`: `E v² ≤ 2 L ε ((2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ) + e^{-L}`. -/
theorem vmom_fineV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    vmom (df2CtxAtF d n δ Kt ap) π s ≤
      2 * (df2oPar d n δ).Le * ((df2oPar d n δ).eps *
        (2 / (df2oPar d n δ).lam * ((df2CtxAtF d n δ Kt ap).sHess π s *
          (((df2CtxAtF d n δ Kt ap).st π s).A * ((df2CtxAtF d n δ Kt ap).st π s).Aᵀ)).trace +
          2 * (df2oPar d n δ).δe * d / (df2oPar d n δ).lam)) + Real.exp (-(df2oPar d n δ).Le) := by
  set c := df2CtxAtF d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, hMw⟩ := H.body
  have hmu := gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  have hadm := H.adm s (H.le_tau_lt hs)
  have h1 := v_sq_le H.hd c.Kt hK hKc hball hMw c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu (playT c π s)
    (df2oPar d n δ).Le hP.L504 (playT_norm_leV H hs) (par_exp H).1
  have h2 := v_mean_le c.Kt hK hKc hball (π.g s) hadm.1 hadm.2 c.p.eps H.rows.pos_eps heps1 _ hmu (playT c π s)
  have h3 := round_lower H hs
  have he : ∫ g, extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu + playT c π s g)
      ∂(stdGaussian (E d)) = c.ebar π s := by
    unfold Df2Ctx.ebar
    rw [df2Ext_eq]
    rfl
  have he2 : extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu) =
      df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 (c.st π s).mu) := by rw [df2Ext_eq]
  rw [he, he2] at h2
  rw [vmom_eq]
  have hL0 : (0 : ℝ) ≤ 2 * (df2oPar d n δ).Le := by linarith [hP.L504]
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 H.rows.pos_eps.le)
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr; exact h4

/-- The sum of the second moments up to `t ≤ τ` is at most `n ε²/4`. -/
theorem vsum_le_quarterV (hSI : Df2SIFacts) (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ℕ → ApFun d) (π : Df2Path d)
    (m : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hm1 : 1 ≤ m) (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ∀ s, ApSpec (ap s))
    (hadm : ∀ s < m, AdmLoss Kt (π.g s)) (t : ℕ) (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1), vmom (df2CtxAtF d n δ Kt ap) π s ≤ 1 / 4 * n * (df2oPar d n δ).eps ^ 2 := by
  have H := detBaseV (π := π) hSI hd hn hδ0 hδ1 heps hm1 hmn hbody hap hadm
  set c := df2CtxAtF d n δ Kt ap with hc
  set τ := c.tau π m with hτ
  have hP := evGPar d n δ hd hn hδ0
  have hτn : τ < n := lt_of_lt_of_le H.tau_lt hmn
  have hsub : ∑ s ∈ Finset.range (t + 1), vmom c π s ≤ ∑ s ∈ Finset.range (τ + 1), vmom c π s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.succ_le_succ ht))
      (fun s _ _ => vmom_nonneg c π s)
  refine hsub.trans ?_
  rw [Finset.sum_range_succ]
  set L := (df2oPar d n δ).Le with hLdef
  set ε := (df2oPar d n δ).eps with hεdef
  set lam := (df2oPar d n δ).lam with hlamdef
  set de := (df2oPar d n δ).δe with hdedef
  set a : ℕ → ℝ := fun u => 2 / lam * (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace with ha
  set b : ℝ := 2 * de * d / lam with hb
  have hfine : ∑ s ∈ Finset.range τ, vmom c π s ≤ ∑ s ∈ Finset.range τ, (2 * L * (ε * (a s + b)) + Real.exp (-L)) :=
    Finset.sum_le_sum fun s hs => vmom_fineV H (Finset.mem_range.1 hs).le
  have hsum : ∀ k : ℕ, ∑ s ∈ Finset.range k, (2 * L * (ε * (a s + b)) + Real.exp (-L)) =
      2 * L * ε * ∑ s ∈ Finset.range k, a s + k * (2 * L * ε * b + Real.exp (-L)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; push_cast; ring
  have htr : ∑ s ∈ Finset.range τ, a s ≤ d * L / (lam * (df2oPar d n δ).eta) := trace_sum_lt H
  have hcr := vmom_crudeV H (le_refl τ)
  have hL := hP.L504
  have hε0 : 0 < ε := H.rows.pos_eps
  have hl0 : 0 < lam := H.rows.pos_lam
  have hde : 0 < de := H.rows.pos_de
  have hb0 : 0 ≤ 2 * L * ε * b + Real.exp (-L) := by positivity
  have hτn' : (τ : ℝ) ≤ n := by exact_mod_cast hτn.le
  have h2 : ∑ s ∈ Finset.range τ, vmom c π s ≤
      2 * L * ε * (d * L / (lam * (df2oPar d n δ).eta)) + n * (2 * L * ε * b + Real.exp (-L)) := by
    rw [hsum] at hfine
    have h2Le : 0 ≤ 2 * L * ε := by positivity
    calc _ ≤ _ := hfine
      _ ≤ _ := by gcongr
  have hr5p := H.rows.r5p
  rw [show df2C0 = 36 from rfl] at hr5p
  have harith := vsum_arith d n L ε lam (df2oPar d n δ).eta de (by exact_mod_cast hd) (by exact_mod_cast hn) hL
    hε0 H.rows.eps_le hl0 H.rows.pos_eta hde hr5p H.rows.r7 H.rows.r8 H.rows.c2dl (par_exp H).2
  linarith

/-- The sum of the second moments of `pip - 1` under the plays, up to `t ≤ τ`. -/
theorem vsum_leV (hSI : Df2SIFacts) (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ℕ → ApFun d) (π : Df2Path d) (m : ℕ)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ∀ s, ApSpec (ap s)) (hadm : ∀ s < m, AdmLoss Kt (π.g s))
    (t : ℕ) (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1),
        ∫ z, (df2Pip (df2oPar d n δ) Kt (WithLp.toLp 2 (((df2CtxAtF d n δ Kt ap).st π s).mu +
          (1 - (df2oPar d n δ).lam) • (((df2CtxAtF d n δ Kt ap).st π s).A *ᵥ z))) - 1) ^ 2
          ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤
      3 / 10 * n * (df2oPar d n δ).eps ^ 2 := by
  have h := vsum_le_quarterV hSI d n δ Kt ap π m hd hn hδ0 hδ1 heps hm1 hmn hbody hap hadm t ht
  have h0 : (0 : ℝ) ≤ n * (df2oPar d n δ).eps ^ 2 := by positivity
  exact h.trans (by nlinarith)

end Concrete

end AdversarialBco.Poly.EvGY
