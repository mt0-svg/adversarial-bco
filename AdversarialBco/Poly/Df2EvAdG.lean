/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeas
public import AdversarialBco.Poly.Df2EvGProof

@[expose] public section

/-!
# The budget of Noise, Pi and Gauss with an adapted parameter

`EvAd.df2EvGPropAd_holds : Df2EvGPropAd`, the proof of `EvGY.df2EvGProp_holds` (Df2EvGProof.lean) on
`Df2OnSetEAd`. Noise and Gauss read no loss. Pi at a round `s ≤ τ` reads the body only: it lies in the event
`piSet` of `(θ 0, mode before round s)`, measurable in `𝒢 s` (`measurable_modeAd`), and of `ξ_s`, independent of
`𝒢 s`; freezing gives the Gaussian bound `pi_round_law` as in the fixed setting.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly.EvAd

open Layer2 ApMeas EvGY

variable {d : ℕ}

section Round

variable {n : ℕ} {δ : ℝ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ}
  {ap : ApFun d}

/-- Pi in one round, adapted parameter: the event of the body parameter, the mode before round `s` and `ξ_s` has
probability at most `exp(-2 L (√L - 2)²)`. -/
theorem pi_roundAd (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) {m : ℕ}
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap)
    {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hE : Df2SetE d μ 𝒢 ξ e) {s : ℕ} (hs : s ≤ m) :
    μ {ω | ((θ 0 ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ≤
      ENNReal.ofReal (Real.exp (-(2 * (df2oPar d n δ).Le * (Real.sqrt (df2oPar d n δ).Le - 2) ^ 2))) := by
  have hP := evGPar d n δ hd hn hδ0
  have hz : Measurable[𝒢 s] fun ω => (θ 0 ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s) :=
    ((hθ 0).mono (𝒢.mono (Nat.zero_le s)) le_rfl).prodMk
      (measurable_modeAd n δ Kθ gθ ap hmeas 𝒢 θ hK ξ e hθ hE.xi_meas hE.e_meas s hs)
  have hx : Measurable[m0] (ξ s) := (hE.xi_meas s).mono (𝒢.le _) le_rfl
  refine freeze_le (𝒢 s) μ (𝒢.le s) _ (ξ s) hz hx (hE.xi_indep s) _ (measurableSet_piSet hmeas) _ ?_
  intro a
  rw [hE.xi_law s]
  by_cases hgood : a.2.code.1 = 2 ∧ gauge (Kθ a.1) (WithLp.toLp 2 a.2.code.2.mu) ≤ 1 ∧
      a.2.code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2)
  · obtain ⟨-, hmu, hA⟩ := hgood
    obtain ⟨hK, hKc, hball, -, hMw⟩ := hbody a.1
    refine (measure_mono fun x hx => hx.2.2.2).trans ?_
    refine pi_round_law hd (Kθ a.1) hK hKc hball hMw a.2.code.2.mu hmu a.2.code.2.A (df2oPar d n δ).lam
      hP.lam0.le hP.lam1.le (df2oPar d n δ).Le hP.L504 ?_
    intro w
    have := hA w
    rwa [hP.sig2] at this
  · have : Prod.mk a ⁻¹' piSet n δ Kθ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hgood ⟨hx.1, hx.2.1, hx.2.2.1⟩
    rw [this, measure_empty]
    exact zero_le

end Round

/-! ## The budget -/

/-- Noise, Pi and Gauss fail with probability at most `3 δ_e/7` on every instance of setting (E) with an adapted
parameter. -/
theorem df2EvGPropAd_holds : Df2EvGPropAd := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hK hE
  have hP := evGPar d n δ hd hn hδ0
  have hx : ∀ s, Measurable[m0] (ξ s) := fun s => (hE.xi_meas s).mono (𝒢.le _) le_rfl
  have hsub : {ω | ¬ (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).EvG
        ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m} ⊆
      ⋃ s ∈ Finset.range m,
        ({ω | Real.sqrt (df2Lg (df2oPar d n δ) n) < |e s ω|} ∪
          {ω | ((θ 0 ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ∪
          {ω | 8 * d / 3 * df2Lg (df2oPar d n δ) n < ξ s ω ⬝ᵥ ξ s ω}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Df2Ctx.EvG, not_forall] at hω
    obtain ⟨s, hs, hfail⟩ := hω
    set c := df2CtxAt d n δ (Kθ (θ 0 ω)) ap with hc
    set π : Df2Path d := ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ with hπ
    have hτ := tau_lt c π hm1
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨s, by omega, ?_⟩
    by_cases h1 : |e s ω| ≤ Real.sqrt (df2Lg (df2oPar d n δ) n)
    · by_cases h3 : ξ s ω ⬝ᵥ ξ s ω ≤ 8 * d / 3 * df2Lg (df2oPar d n δ) n
      · have h2 : ¬ gauge c.Kt (WithLp.toLp 2 (c.X π s)) ≤ Real.sqrt c.p.Le := fun h2 => hfail ⟨h1, h2, h3⟩
        refine Or.inl (Or.inr ?_)
        have hp : LPar c π := by
          refine ⟨?_, hP.de, hP.ek, (by show (df2oPar d n δ).eps < 1; linarith),
            (hbody (θ 0 ω)).2.2.1 (Metric.mem_closedBall_self zero_le_one), rfl⟩
          show 0 < (df2oPar d n δ).sig2
          rw [hP.sig2]
          have := hP.L504
          positivity
        have hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v := fun u hu v =>
          sHess_nonneg c π u (hbody (θ 0 ω)) (admAd Kθ gθ hadm θ hK ω u (by omega)) hP.eps0
            (by show (df2oPar d n δ).eps < 1; linarith) hP.lam0 v
        have hI := linv_le_tau c π hp hap hH s hs
        have hcode : (c.mode π s).code = (2, c.st π s) := by rw [hI.run]; rfl
        show (c.mode π s).code.1 = 2 ∧ gauge (Kθ (θ 0 ω)) (WithLp.toLp 2 (c.mode π s).code.2.mu) ≤ 1 ∧
          (c.mode π s).code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2) ∧
          Real.sqrt (df2oPar d n δ).Le < gauge (Kθ (θ 0 ω)) (WithLp.toLp 2 (xOf n δ (c.mode π s).code.2 (ξ s ω)))
        rw [hcode]
        refine ⟨rfl, gauge_le_one_of_keps _ _ hP.eps0.le (by linarith) _ hI.mu, fun w => hI.A_sq_le c π hp w, ?_⟩
        exact lt_of_not_ge h2
      · exact Or.inr (lt_of_not_ge h3)
    · exact Or.inl (Or.inl (lt_of_not_ge h1))
  have hb : ∀ s ∈ Finset.range m,
      μ ({ω | Real.sqrt (df2Lg (df2oPar d n δ) n) < |e s ω|} ∪
          {ω | ((θ 0 ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ∪
          {ω | 8 * d / 3 * df2Lg (df2oPar d n δ) n < ξ s ω ⬝ᵥ ξ s ω}) ≤
        ENNReal.ofReal (3 * ((df2oPar d n δ).δe / (7 * n))) := by
    intro s hs
    have hsm : s ≤ m := (Finset.mem_range.1 hs).le
    have hle : 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance ≤ m0 := sup_le (𝒢.le s) (hx s).comap_le
    have hN := noise_round μ _ hle (e s) ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.e_int s) (hE.e_exp s) _ hP.Lg0
    have hG := gauss_round hd μ (ξ s) (hx s) (hE.xi_law s) (df2Lg (df2oPar d n δ) n)
    have hPi := (pi_roundAd hd hn hδ0 hbody hmeas μ 𝒢 θ hK ξ e hθ hE hsm).trans
      (ENNReal.ofReal_le_ofReal (pi_le_budget _ _ hP.L504 hP.LgLe))
    rw [two_exp_Lg _ n hn hP.de] at hN hG hPi
    have h3 : ENNReal.ofReal (3 * ((df2oPar d n δ).δe / (7 * n))) =
        ENNReal.ofReal ((df2oPar d n δ).δe / (7 * n)) + ENNReal.ofReal ((df2oPar d n δ).δe / (7 * n)) +
          ENNReal.ofReal ((df2oPar d n δ).δe / (7 * n)) := by
      have h0 : 0 ≤ (df2oPar d n δ).δe / (7 * n) := by have := hP.de; positivity
      rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0]
      ring_nf
    rw [h3]
    exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hN hPi)) hG)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ Finset.range m, ENNReal.ofReal (3 * ((df2oPar d n δ).δe / (7 * n))) := Finset.sum_le_sum hb
    _ = ENNReal.ofReal (m * (3 * ((df2oPar d n δ).δe / (7 * n)))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (3 / 7 * (df2oPar d n δ).δe) := by
      apply ENNReal.ofReal_le_ofReal
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hde := hP.de
      calc (m : ℝ) * (3 * ((df2oPar d n δ).δe / (7 * n))) ≤ n * (3 * ((df2oPar d n δ).δe / (7 * n))) :=
            mul_le_mul_of_nonneg_right hmn' (by positivity)
        _ = 3 / 7 * (df2oPar d n δ).δe := by field_simp

end AdversarialBco.Poly.EvAd
