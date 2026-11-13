/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeasV
public import AdversarialBco.Poly.Df2EvYProof
public import AdversarialBco.Poly.Df2SIFactsProof
public import AdversarialBco.Poly.Df2EvVSumV

@[expose] public section

/-!
# The budget of Y with an adapted parameter and an advice per round

`EvAd.df2EvYPropAdV_of : Df2SIFacts → Df2EvYPropAdV` and `EvAd.df2EvYPropAdV_holds`, the budget of Y on
`Df2OnSetEAdV`. The frozen point of round `u` is `(θ u, st_u, ξ_u)`, measurable in `𝒢 u ∨ σ(ξ_u)`; the frozen
functions of Df2EvYProof.lean (`pOf`, `jOf`, `aOf`, `fOf`, `zOf`) read the body at `θ u`, the context at `θ 0`, and
`hK` joins them (`Y_eq_frozenAdV`, `zWAd_eq_sqV`, the last step of `condExp_zWAd_leV`). Freedman's inequality
(`freedman_W`), the round bound and the sum of the second moments complete the budget.

The routine of round `s` is `apθ (ψ s ω)` (Df2SetEAdV.lean); no increment reads it, so the proof runs on the context
`ctxWV` with the process lemmas of Df2EvAdMeasV.lean.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly.EvAd

open Layer2 ApMeas EvGY

/-! ## The process on `Ω` -/

section Proc

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
  (gθ : ℕ → Θ → E d → ℝ) {V : Type} [MeasurableSpace V] (apθ : V → ApFun d) {Ω : Type} {m0 : MeasurableSpace Ω} (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V)
  (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)

/-- The state of round `u` at `ω`. -/
noncomputable def stWAdV (u : ℕ) (ω : Ω) : Df2St d := (ctxWV n δ Kθ apθ (θ 0) ψ ω).st (pathWAd gθ θ ξ e ω) u

/-- The frozen point of round `u` at `ω`: the parameter of round `u`, the state, the draw. -/
noncomputable def xWAdV (u : ℕ) (ω : Ω) : Θ × Df2St d × (Fin d → ℝ) :=
  (θ u ω, stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω, ξ u ω)

variable (m) in
/-- `Z_u = 1{π(X_u) ≤ √L} min(Y_u², B)` for `u < m`, and `0` after the horizon. -/
noncomputable def zWAdV (u : ℕ) (ω : Ω) : ℝ :=
  if u < m then zOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω, e u ω) else 0

/-- `W_u = 8 + (10/ε²) E_z v(μ_u + (1 - λ) A_u z)²`. -/
noncomputable def wWAdV (u : ℕ) (ω : Ω) : ℝ :=
  8 + 10 / (df2oPar d n δ).eps ^ 2 * vmom (ctxWV n δ Kθ apθ (θ 0) ψ ω) (pathWAd gθ θ ξ e ω) u

omit [MeasurableSpace Θ] [MeasurableSpace V] in
theorem zWAd_nonnegV (hB : 0 ≤ yB d n δ) (u : ℕ) (ω : Ω) : 0 ≤ zWAdV n δ m Kθ gθ apθ θ ψ ξ e u ω := by
  unfold zWAdV zOf
  split_ifs
  · rcases jOf_mem n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) with h | h <;> rw [h]
    · simp
    · rw [one_mul]; exact le_min (sq_nonneg _) hB
  · exact le_rfl

omit [MeasurableSpace Θ] [MeasurableSpace V] in
theorem zWAd_leV (hB : 0 ≤ yB d n δ) (u : ℕ) (ω : Ω) : zWAdV n δ m Kθ gθ apθ θ ψ ξ e u ω ≤ yB d n δ := by
  unfold zWAdV zOf
  split_ifs
  · rcases jOf_mem n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) with h | h <;> rw [h]
    · simpa using hB
    · rw [one_mul]; exact min_le_right _ _
  · exact hB

theorem measurable_zWAdV (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s))
    (u : ℕ) : StronglyMeasurable[𝒢 (u + 1)] (zWAdV n δ m Kθ gθ apθ θ ψ ξ e u) := by
  by_cases hu : u < m
  · have hfun : zWAdV n δ m Kθ gθ apθ θ ψ ξ e u = fun ω => zOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω, e u ω) :=
      funext fun ω => by simp only [zWAdV, hu, ite_true]
    rw [hfun]
    have hst : Measurable[𝒢 (u + 1)] (stWAdV n δ Kθ gθ apθ θ ψ ξ e u) :=
      (measurable_stAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hξ he hu.le).mono (𝒢.mono (Nat.le_succ u)) le_rfl
    have hθ' : Measurable[𝒢 (u + 1)] (θ u) := (hθ u).mono (𝒢.mono (Nat.le_succ u)) le_rfl
    have hx : Measurable[𝒢 (u + 1)] fun ω => (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω, e u ω) :=
      (hθ'.prodMk (hst.prodMk (hξ u))).prodMk (he u)
    have h := (measurable_zOf n δ Kθ gθ apNone hmeas.none hu).comp hx
    exact h.stronglyMeasurable
  · have hfun : zWAdV n δ m Kθ gθ apθ θ ψ ξ e u = fun _ => 0 := funext fun ω => by simp only [zWAdV, hu, ite_false]
    rw [hfun]
    exact stronglyMeasurable_const

end Proc

/-! ## One round of Y -/

section Round

variable {d : ℕ} {n : ℕ} {δ : ℝ} {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)}
  {gθ : ℕ → Θ → E d → ℝ} {V : Type} [MeasurableSpace V] {apθ : V → ApFun d}

/-- One round: `E[Z_u | 𝒢 u] ≤ W_u` almost surely, adapted parameter. -/
theorem condExp_zWAd_leV (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q))
    (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s)) (hE : Df2SetE d μ 𝒢 ξ e)
    (u : ℕ) :
    μ[zWAdV n δ m Kθ gθ apθ θ ψ ξ e u | 𝒢 u] ≤ᵐ[μ] wWAdV n δ Kθ gθ apθ θ ψ ξ e u := by
  have hP := evGPar d n δ hd hn hδ0
  have hε0 := hP.eps0
  have hε1 : (df2oPar d n δ).eps < 1 := by linarith
  have hL1 : 1 ≤ (df2oPar d n δ).Le := by linarith [hP.L504]
  by_cases hu : u < m
  swap
  · have hfun : zWAdV n δ m Kθ gθ apθ θ ψ ξ e u = 0 :=
      funext fun ω => by simp only [zWAdV, hu, ite_false, Pi.zero_apply]
    rw [hfun, condExp_zero]
    refine ae_of_all _ fun ω => ?_
    have := vmom_nonneg (ctxWV n δ Kθ apθ (θ 0) ψ ω) (pathWAd gθ θ ξ e ω) u
    show (0 : ℝ) ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * vmom (ctxWV n δ Kθ apθ (θ 0) ψ ω) (pathWAd gθ θ ξ e ω) u
    positivity
  have hξm : Measurable[m0] (ξ u) := (hE.xi_meas u).mono (𝒢.le _) le_rfl
  have hH : hOf 𝒢 ξ u ≤ m0 := sup_le (𝒢.le u) hξm.comap_le
  have hst : Measurable[𝒢 u] (stWAdV n δ Kθ gθ apθ θ ψ ξ e u) :=
    measurable_stAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hE.xi_meas hE.e_meas hu.le
  have hθu : Measurable[𝒢 u] (θ u) := hθ u
  have hx : Measurable[𝒢 u] fun ω => (θ u ω, stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) := hθu.prodMk hst
  have hxH : Measurable[hOf 𝒢 ξ u] (xWAdV n δ Kθ gθ apθ θ ψ ξ e u) :=
    (hθu.mono le_sup_left le_rfl).prodMk ((hst.mono le_sup_left le_rfl).prodMk
      ((comap_measurable (ξ u)).mono le_sup_right le_rfl))
  have hJ : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) :=
    ((measurable_jOf n δ Kθ gθ apNone hmeas.none).comp hxH).stronglyMeasurable
  have hPm : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) :=
    ((measurable_pOf n δ Kθ gθ apNone hmeas.none).comp hxH).stronglyMeasurable
  have ham : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) :=
    ((measurable_aOf n δ Kθ gθ apNone hmeas.none hu).comp hxH).stronglyMeasurable
  have hvm : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1 :=
    (((measurable_pOf n δ Kθ gθ apNone hmeas.none).comp hxH).sub_const 1).stronglyMeasurable
  have ha01 : ∀ ω, aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    obtain ⟨hKc, hKcl, hball, -, -⟩ := hbody (θ u ω)
    rw [aOf_eq]
    exact (hadm (θ u ω) u hu).2 _ (play_mem (Kθ (θ u ω)) hKc hKcl hball _ hε0 hε1 _)
  have hB0 : 0 ≤ yB d n δ := by unfold yB; positivity
  have he : Measurable[m0] (e u) := (hE.e_meas u).mono (𝒢.le _) le_rfl
  have h1 := condExp_round_le (hOf 𝒢 ξ u) μ hH (fun ω => jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω))
    (fun ω => pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω)) (fun ω => aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω))
    (fun ω => pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1) hJ (fun ω => jOf_mem n δ Kθ _) hPm ham ha01 hvm
    (2 * Real.sqrt (df2oPar d n δ).Le) (fun ω => (jOf_bounds hL1 hε0 heps _).1)
    (fun ω => (jOf_bounds hL1 hε0 heps _).2.1) (df2oPar d n δ).eps (yB d n δ) hε0 hB0 (e u) he (hE.e_int u)
    (hE.e_mean u) (hE.e_exp u)
  have hzW : zWAdV n δ m Kθ gθ apθ θ ψ ξ e u = fun ω => jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) *
      min ((pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) * (aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) + e u ω) +
        2 * (pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1) / (df2oPar d n δ).eps) ^ 2) (yB d n δ) :=
    funext fun ω => by simp only [zWAdV, hu, ite_true]; rfl
  have h2 : ∀ ω, jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) *
      (4 * pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) ^ 2 +
        8 * (pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1) ^ 2 / (df2oPar d n δ).eps ^ 2) ≤
      fOf n δ Kθ ((θ u ω, stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω), ξ u ω) := by
    intro ω
    show _ ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * (jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) *
      (pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1) ^ 2)
    rcases jOf_mem n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) with h | h <;> rw [h]
    · simp only [zero_mul, mul_zero, add_zero]; norm_num
    · simp only [one_mul]; exact round_arith _ _ hε0 heps
  have hYF : μ[zWAdV n δ m Kθ gθ apθ θ ψ ξ e u | hOf 𝒢 ξ u] ≤ᵐ[μ]
      fun ω => fOf n δ Kθ ((θ u ω, stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω), ξ u ω) := by
    rw [hzW]
    exact h1.trans (ae_of_all _ h2)
  have hint : Integrable (zWAdV n δ m Kθ gθ apθ θ ψ ξ e u) μ := by
    refine Integrable.of_bound ((measurable_zWAdV n δ Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas u).mono
      (𝒢.le _)).aestronglyMeasurable (yB d n δ) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (zWAd_nonnegV n δ Kθ gθ apθ θ ψ ξ e hB0 u ω)]
    exact zWAd_leV n δ Kθ gθ apθ θ ψ ξ e hB0 u ω
  have hF0 : ∀ y, 0 ≤ fOf n δ Kθ y := by
    intro y
    have := (jOf_bounds (Kθ := Kθ) hL1 hε0 heps (y.1.1, y.1.2, y.2)).2.2.1
    unfold fOf; positivity
  have hFC : ∀ y, fOf n δ Kθ y ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * (4 * (df2oPar d n δ).Le) := by
    intro y
    have := (jOf_bounds (Kθ := Kθ) hL1 hε0 heps (y.1.1, y.1.2, y.2)).2.2.2
    unfold fOf
    have : (0 : ℝ) ≤ 10 / (df2oPar d n δ).eps ^ 2 := by positivity
    gcongr
  have h3 := condExp_le_freeze lemmaFR (𝒢 u) (hOf 𝒢 ξ u) μ le_sup_left hH
    (fun ω => (θ u ω, stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω)) (ξ u) hx hξm (hE.xi_indep u) _ hint (fOf n δ Kθ)
    (measurable_fOf n δ Kθ gθ apNone hmeas.none) _ hF0 hFC hYF
  rw [hE.xi_law u] at h3
  refine h3.trans (ae_of_all _ fun ω => ?_)
  obtain ⟨hKc, hKcl, hball, -, -⟩ := hbody (θ u ω)
  refine (integral_fOf_le (gθ := gθ) (ap := apNone) hmeas.none hε0 hε1 (θ u ω) hKc hKcl hball _).trans (le_of_eq ?_)
  simp only [wWAdV, vmom, pOf, hK u ω]
  rfl

end Round

/-! ## The budget -/

section Main

variable {d : ℕ} {n : ℕ} {δ : ℝ} {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)}
  {gθ : ℕ → Θ → E d → ℝ} {V : Type} [MeasurableSpace V] {apθ : V → ApFun d} {Ω : Type} {m0 : MeasurableSpace Ω} {θ : ℕ → Ω → Θ} {ψ : ℕ → Ω → V}
  {ξ : ℕ → Ω → Fin d → ℝ} {e : ℕ → Ω → ℝ}

omit [MeasurableSpace Θ] [MeasurableSpace V] in
/-- `Y_u = P (a + e) + 2 (P - 1)/ε` at the frozen point of round `u`. -/
theorem Y_eq_frozenAdV (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) (u : ℕ) :
    (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) u =
      pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) * (aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) + e u ω) +
        2 * (pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) - 1) / (df2oPar d n δ).eps := by
  rw [aOf_eq]
  simp only [pOf, xWAdV, hK u ω]
  rfl

omit [MeasurableSpace Θ] [MeasurableSpace V] in
/-- On Noise and Pi at round `u < m`, `Z_u = Y_u²`. -/
theorem zWAd_eq_sqV (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q))
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω)
    {u : ℕ} (hu : u < m) (he : |e u ω| ≤ Real.sqrt (df2Lg (df2oPar d n δ) n))
    (hg : gauge (Kθ (θ 0 ω)) (WithLp.toLp 2 (xOf n δ (stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω))) ≤
      Real.sqrt (df2oPar d n δ).Le) :
    zWAdV n δ m Kθ gθ apθ θ ψ ξ e u ω = (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) u ^ 2 := by
  have hP := evGPar d n δ hd hn hδ0
  have hε0 := hP.eps0
  have hε1 : (df2oPar d n δ).eps < 1 := by linarith
  have hg' : gauge (Kθ (θ u ω)) (WithLp.toLp 2 (xOf n δ (stWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω))) ≤
      Real.sqrt (df2oPar d n δ).Le := by
    rw [hK u ω]; exact hg
  have hj : jOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) = 1 := ite_eq_left hg'
  have hP2 : pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) ≤ 2 * Real.sqrt (df2oPar d n δ).Le :=
    pip_le_two_sqrt (df2oPar d n δ) (Kθ (θ u ω)) _ _ (by linarith [hP.L504]) hε0 heps hg'
  have ha : aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω) ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hKc, hKcl, hball, -, -⟩ := hbody (θ u ω)
    rw [aOf_eq]
    exact (hadm (θ u ω) u hu).2 _ (play_mem (Kθ (θ u ω)) hKc hKcl hball _ hε0 hε1 _)
  have hmax := ymax_le (df2oPar d n δ).Le (df2Lg (df2oPar d n δ) n) (df2oPar d n δ).eps
    (pOf n δ Kθ (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω)) (aOf n δ Kθ gθ u (xWAdV n δ Kθ gθ apθ θ ψ ξ e u ω)) (e u ω)
    (by linarith [hP.L504]) hP.LgLe hε0 heps (one_le_pOf n δ Kθ _) hP2 ha he
  rw [Y_eq_frozenAdV hK]
  unfold zWAdV zOf
  rw [ite_eq_left hu, hj, one_mul]
  apply min_eq_left
  refine hmax.trans (le_of_eq ?_)
  unfold yB
  ring

end Main

/-- The budget of Y with an adapted parameter: on every instance, `G` holds and `Y` fails with probability at most
`δ_e/7`. -/
theorem df2EvYPropAdV_of (hSI : Df2SIFacts) : Df2EvYPropAdV := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  have hP := evGPar d n δ hd hn hδ0
  have hB : 0 < yB d n δ := by unfold yB; have := hP.L504; have := hP.eps0; positivity
  have hde7 : 0 < (df2oPar d n δ).δe / 7 := by have := hP.de; positivity
  have hF := freedman_W μ 𝒢 (zWAdV n δ m Kθ gθ apθ θ ψ ξ e) (wWAdV n δ Kθ gθ apθ θ ψ ξ e) (yB d n δ) hB
    (measurable_zWAdV n δ Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas)
    (zWAd_nonnegV n δ Kθ gθ apθ θ ψ ξ e hB.le) (zWAd_leV n δ Kθ gθ apθ θ ψ ξ e hB.le)
    (condExp_zWAd_leV hd hn hδ0 heps hbody hadm hmeas μ 𝒢 θ ψ hK ξ e hθ hψ hE) m ((df2oPar d n δ).δe / 7) hde7
  refine le_trans (measure_mono ?_) (hF.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  intro ω hω
  obtain ⟨hG, hY⟩ := hω
  have H := detBaseV (π := pathWAd gθ θ ξ e ω) hSI hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ 0 ω)) (fun s => hap (ψ s ω))
    (admAd Kθ gθ hadm θ hK ω)
  have hτm : (ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m < m := H.tau_lt
  refine ⟨(ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1, hτm, ?_⟩
  have hZ : ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
      zWAdV n δ m Kθ gθ apθ θ ψ ξ e u ω =
      ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
        (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) u ^ 2 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hut : u ≤ (ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m :=
      Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    exact zWAd_eq_sqV hd hn hδ0 heps hbody hadm hK ω (lt_of_le_of_lt hut hτm) (hG u hut).1 (hG u hut).2.1
  have hY' : 22 * (n : ℝ) < ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
      (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) u ^ 2 := lt_of_not_ge hY
  have hV := vsum_le_quarterV hSI d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω)) (pathWAd gθ θ ξ e ω) m hd hn hδ0 hδ1 heps hm1 hmn
    (hbody (θ 0 ω)) (fun s => hap (ψ s ω)) (admAd Kθ gθ hadm θ hK ω) _ le_rfl
  have hW : ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
      wWAdV n δ Kθ gθ apθ θ ψ ξ e u ω =
      ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1 : ℕ) * 8 + 10 / (df2oPar d n δ).eps ^ 2 *
        ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
          vmom (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) (pathWAd gθ θ ξ e ω) u := by
    unfold wWAdV
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hτn : (((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt hτm).trans hmn
  have hε0 := hP.eps0
  have hεne : (df2oPar d n δ).eps ^ 2 ≠ 0 := by positivity
  have hWb : 10 / (df2oPar d n δ).eps ^ 2 *
      ∑ u ∈ Finset.range ((ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m + 1),
        vmom (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) (pathWAd gθ θ ξ e ω) u ≤ 10 / 4 * n := by
    calc _ ≤ 10 / (df2oPar d n δ).eps ^ 2 * (1 / 4 * n * (df2oPar d n δ).eps ^ 2) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 10 / 4 * n := by field_simp
  have hyb := yb_arith n (df2oPar d n δ).Le (df2oPar d n δ).eps (df2oPar d n δ).δe hP.de H.x_ge H.Le_eq hε0
    H.rows.r7
  have hyb' : yB d n δ * Real.log (1 / ((df2oPar d n δ).δe / 7)) ≤ n := hyb
  rw [hZ, hW]
  linarith

/-- The budget Y with an adapted parameter holds. -/
theorem df2EvYPropAdV_holds : Df2EvYPropAdV :=
  df2EvYPropAdV_of SIF.df2SIFacts_holds

end AdversarialBco.Poly.EvAd
