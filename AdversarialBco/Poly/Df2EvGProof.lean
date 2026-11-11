/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvMeas
public import AdversarialBco.Poly.Df2EvGTools

@[expose] public section

/-!
# The budget of Noise, Pi and Gauss

`df2EvGProp_holds : Df2EvGProp`. A failure of `EvG` is a failure of Noise, Pi or Gauss at a round `s ≤ τ < m`; the
union over the rounds `s < m ≤ n` of the three events, each of probability at most `δ_e/(7n)`, costs `3 δ_e/7`.
Noise and Gauss do not read `τ`. Pi at a round `s ≤ τ` happens at a good state (`π(μ_s) ≤ 1`, `|A_s w|² ≤ 2σ²|w|²`,
from the light invariant `LInv`), so it lies in an event of the mode before round `s`, measurable in `𝒢 s`, and of
`ξ_s`, independent of `𝒢 s`; freezing reduces it to the Gaussian bound `pi_round_law` at a fixed good state.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly

open Layer2 ApMeas

namespace EvGY

variable {d : ℕ}

/-! ## The Hessian forms on the path -/

/-- The surrogate of the extension of an admissible loss is convex. -/
theorem surr_convex {R : ℝ} (Kt : Set (E d)) (hbody : Df2Body d R Kt) (g : E d → ℝ) (hg : AdmLoss Kt g)
    (p : Df2OPar) (hε0 : 0 < p.eps) (hε1 : p.eps < 1) (hlam : 0 < p.lam) (mu : E d) (A : E d →L[ℝ] E d) :
    ConvexOn ℝ Set.univ (df2Surr (df2Ext p Kt g) mu A p.lam) := by
  obtain ⟨hK, hKc, hball, -, -⟩ := hbody
  have hc : (1 - p.eps) / p.eps ≤ 2 / p.eps := div_le_div_of_nonneg_right (by linarith) hε0.le
  have hconv : ConvexOn ℝ Set.univ (df2Ext p Kt g) := by
    rw [df2Ext_eq]
    exact extOf_convex Kt hK hKc hball g hg.1 hg.2 p.eps hε0 hε1 _ hc
  refine df2Surr_convex _ hconv (continuous_of_convexOn_univ _ hconv) (1 + 2 / p.eps)
    ((1 + 2 / p.eps) / (1 - p.eps)) ?_ mu A p.lam hlam
  intro x
  rw [df2Ext_eq]
  exact extOf_abs_le Kt hK hKc hball g hg.2 p.eps hε0 hε1 _ (by positivity) x

/-- The Hessian of the surrogate of round `s` has a nonnegative form. -/
theorem sHess_nonneg {R : ℝ} (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (hbody : Df2Body d R c.Kt)
    (hg : AdmLoss c.Kt (π.g s)) (hε0 : 0 < c.p.eps) (hε1 : c.p.eps < 1) (hlam : 0 < c.p.lam) (v : Fin d → ℝ) :
    0 ≤ df2Sq (c.sHess π s) v := by
  unfold Df2Ctx.sHess
  rw [(gradM_hessM _ _ v).2]
  exact fderiv_fderiv_nonneg_of_convex _ (surr_convex c.Kt hbody (π.g s) hg c.p hε0 hε1 hlam _ _) _ _

/-- A point of `K_ε` has gauge at most `1`. -/
theorem gauge_le_one_of_keps (Kt : Set (E d)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (mu : Fin d → ℝ)
    (hmu : mu ∈ df2KepsOf Kt ε) : gauge Kt (WithLp.toLp 2 mu) ≤ 1 := by
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  have heq : WithLp.toLp 2 mu = (1 - ε) • WithLp.toLp 2 ((1 - ε)⁻¹ • mu) := by
    rw [← WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]
  rw [heq, gauge_smul_of_nonneg h1.le, smul_eq_mul]
  have := gauge_le_one_of_mem (s := Kt) hmu
  have h0 : 0 ≤ gauge Kt (WithLp.toLp 2 ((1 - ε)⁻¹ • mu)) := gauge_nonneg _
  nlinarith

/-! ## The parameters -/

/-- The parameters the budget reads. -/
structure EvGPar (d n : ℕ) (δ : ℝ) : Prop where
  de : 0 < (df2oPar d n δ).δe
  L504 : 504 ≤ (df2oPar d n δ).Le
  Lg0 : 0 ≤ df2Lg (df2oPar d n δ) n
  LgLe : df2Lg (df2oPar d n δ) n ≤ (df2oPar d n δ).Le
  lam0 : 0 < (df2oPar d n δ).lam
  lam1 : (df2oPar d n δ).lam < 1
  eps0 : 0 < (df2oPar d n δ).eps
  sig2 : (df2oPar d n δ).sig2 = 1 / (8 * (df2oPar d n δ).Le)
  ek : 0 ≤ (df2oPar d n δ).eta * (df2oPar d n δ).kap

theorem evGPar (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) : EvGPar d n δ := by
  obtain ⟨hde, -, -⟩ := par_de d n δ hd hn hδ0
  obtain ⟨hL, hLg0, hLgL⟩ := par_Le d n δ hd hn hδ0
  obtain ⟨hl0, hl1, he0, hs, hek⟩ := par_misc d n δ hd hn hδ0
  exact ⟨hde, hL, hLg0, hLgL, hl0, hl1, he0, hs, hek⟩

/-! ## Pi in one round, on setting (E) -/

section Round

variable {n : ℕ} {δ : ℝ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ}
  {ap : ApFun d}

/-- The states of spread at most `k`. -/
def spreadSet (k : ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) := {A | ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)}

variable (n δ Kθ) in
/-- The event of Pi at a good state, as a set of `((θ, mode), ξ)`. -/
def piSet : Set ((Θ × Df2Mode d) × (Fin d → ℝ)) :=
  {x | x.1.2.code.1 = 2 ∧ gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1 ∧
    x.1.2.code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2) ∧
    Real.sqrt (df2oPar d n δ).Le < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2))}

theorem measurableSet_piSet {m : ℕ} (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) :
    MeasurableSet (piSet n δ Kθ) := by
  have hcode : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code :=
    measurable_mode_code.comp (measurable_snd.comp measurable_fst)
  have hst : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code.2 := measurable_snd.comp hcode
  have hq : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.1 := measurable_fst.comp measurable_fst
  have h1 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) | x.1.2.code.1 = 2} :=
    (measurable_fst.comp hcode) (measurableSet_singleton 2)
  have hmu : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => (x.1.1, (WithLp.toLp 2 x.1.2.code.2.mu : E d)) :=
    hq.prodMk ((WithLp.measurable_toLp 2 _).comp (measurable_st_mu.comp hst))
  have hg2 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) := by
    have h := hmeas.1.comp hmu
    exact h
  have h2 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1} := measurableSet_le hg2 measurable_const
  have h3 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      x.1.2.code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2)} :=
    (measurable_st_A.comp hst) (isClosed_spread _).measurableSet
  have hX : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      (x.1.1, (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2) : E d)) := by
    have hx : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => (x.1.2.code.2, x.2) := hst.prodMk measurable_snd
    have h := (measurable_xOf n δ).comp hx
    exact hq.prodMk ((WithLp.measurable_toLp 2 _).comp h)
  have hg4 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2)) := by
    have h := hmeas.1.comp hX
    exact h
  have h4 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      Real.sqrt (df2oPar d n δ).Le < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2))} :=
    measurableSet_lt measurable_const hg4
  exact h1.inter (h2.inter (h3.inter h4))

/-- Pi in one round: the event of the mode before round `s` and of `ξ_s` has probability at most
`exp(-2 L (√L - 2)²)`. -/
theorem pi_round (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) {m : ℕ}
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap)
    {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (θ : Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (hθ : Measurable[𝒢 0] θ) (hE : Df2SetE d μ 𝒢 ξ e)
    {s : ℕ} (hs : s ≤ m) :
    μ {ω | ((θ ω, (ctxW n δ Kθ ap θ ω).mode (pathW gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ≤
      ENNReal.ofReal (Real.exp (-(2 * (df2oPar d n δ).Le * (Real.sqrt (df2oPar d n δ).Le - 2) ^ 2))) := by
  have hP := evGPar d n δ hd hn hδ0
  have hz : Measurable[𝒢 s] fun ω => (θ ω, (ctxW n δ Kθ ap θ ω).mode (pathW gθ θ ξ e ω) s) :=
    (hθ.mono (𝒢.mono (Nat.zero_le s)) le_rfl).prodMk
      (measurable_mode n δ Kθ gθ ap hmeas 𝒢 θ ξ e hθ hE.xi_meas hE.e_meas s hs)
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

/-- Noise, Pi and Gauss fail with probability at most `3 δ_e/7` on every instance of setting (E). -/
theorem df2EvGProp_holds : Df2EvGProp := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hE
  have hP := evGPar d n δ hd hn hδ0
  have hx : ∀ s, Measurable[m0] (ξ s) := fun s => (hE.xi_meas s).mono (𝒢.le _) le_rfl
  have hsub : {ω | ¬ (df2CtxAt d n δ (Kθ (θ ω)) ap).EvG ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ m} ⊆
      ⋃ s ∈ Finset.range m,
        ({ω | Real.sqrt (df2Lg (df2oPar d n δ) n) < |e s ω|} ∪
          {ω | ((θ ω, (ctxW n δ Kθ ap θ ω).mode (pathW gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ∪
          {ω | 8 * d / 3 * df2Lg (df2oPar d n δ) n < ξ s ω ⬝ᵥ ξ s ω}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Df2Ctx.EvG, not_forall] at hω
    obtain ⟨s, hs, hfail⟩ := hω
    set c := df2CtxAt d n δ (Kθ (θ ω)) ap with hc
    set π : Df2Path d := ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ with hπ
    have hτ := tau_lt c π hm1
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨s, by omega, ?_⟩
    by_cases h1 : |e s ω| ≤ Real.sqrt (df2Lg (df2oPar d n δ) n)
    · by_cases h3 : ξ s ω ⬝ᵥ ξ s ω ≤ 8 * d / 3 * df2Lg (df2oPar d n δ) n
      · have h2 : ¬ gauge c.Kt (WithLp.toLp 2 (c.X π s)) ≤ Real.sqrt c.p.Le := fun h2 => hfail ⟨h1, h2, h3⟩
        refine Or.inl (Or.inr ?_)
        have hp : LPar c π := by
          refine ⟨?_, hP.de, hP.ek, (by show (df2oPar d n δ).eps < 1; linarith), (hbody (θ ω)).2.2.1 (Metric.mem_closedBall_self zero_le_one), rfl⟩
          show 0 < (df2oPar d n δ).sig2
          rw [hP.sig2]
          have := hP.L504
          positivity
        have hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v := fun u hu v =>
          sHess_nonneg c π u (hbody (θ ω)) (hadm (θ ω) u (by omega)) hP.eps0 (by show (df2oPar d n δ).eps < 1; linarith)
            hP.lam0 v
        have hI := linv_le_tau c π hp hap hH s hs
        have hcode : (c.mode π s).code = (2, c.st π s) := by rw [hI.run]; rfl
        show (c.mode π s).code.1 = 2 ∧ gauge (Kθ (θ ω)) (WithLp.toLp 2 (c.mode π s).code.2.mu) ≤ 1 ∧
          (c.mode π s).code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2) ∧
          Real.sqrt (df2oPar d n δ).Le < gauge (Kθ (θ ω)) (WithLp.toLp 2 (xOf n δ (c.mode π s).code.2 (ξ s ω)))
        rw [hcode]
        refine ⟨rfl, gauge_le_one_of_keps _ _ hP.eps0.le (by linarith) _ hI.mu, fun w => hI.A_sq_le c π hp w, ?_⟩
        exact lt_of_not_ge h2
      · exact Or.inr (lt_of_not_ge h3)
    · exact Or.inl (Or.inl (lt_of_not_ge h1))
  have hb : ∀ s ∈ Finset.range m,
      μ ({ω | Real.sqrt (df2Lg (df2oPar d n δ) n) < |e s ω|} ∪
          {ω | ((θ ω, (ctxW n δ Kθ ap θ ω).mode (pathW gθ θ ξ e ω) s), ξ s ω) ∈ piSet n δ Kθ} ∪
          {ω | 8 * d / 3 * df2Lg (df2oPar d n δ) n < ξ s ω ⬝ᵥ ξ s ω}) ≤
        ENNReal.ofReal (3 * ((df2oPar d n δ).δe / (7 * n))) := by
    intro s hs
    have hsm : s ≤ m := (Finset.mem_range.1 hs).le
    have hle : 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance ≤ m0 := sup_le (𝒢.le s) (hx s).comap_le
    have hN := noise_round μ _ hle (e s) ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.e_int s) (hE.e_exp s) _ hP.Lg0
    have hG := gauss_round hd μ (ξ s) (hx s) (hE.xi_law s) (df2Lg (df2oPar d n δ) n)
    have hPi := (pi_round hd hn hδ0 hbody hmeas μ 𝒢 θ ξ e hθ hE hsm).trans
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

end EvGY

end AdversarialBco.Poly
