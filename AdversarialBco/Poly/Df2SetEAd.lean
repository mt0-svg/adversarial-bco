/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# Setting (E) with an adapted loss parameter

`Df2OnSetE` (Df2Layer2.lean) reads the losses of an epoch at one parameter `θ` measurable in `𝒢 0`. Against a
strategy the loss of round `s` reads the history before round `s`, hence the draws of the rounds `< s`, which
`Df2SetE.xi_indep` puts outside `𝒢 0`. `Df2OnSetEAd` reads the loss of round `s` at a parameter `θ s` measurable in
`𝒢 s`; the body is read at `θ 0` and every `θ s` gives the same body. The fixed setting is the constant case
(`df2OnSetE_of_ad`, Df2EvAdMeas.lean).

The six adapted Props carry the same events and the same constants as `Df2EvGProp`, `Df2EvYProp`, `Df2EvLQProp`,
`Df2EvSDFProp`, `Df2EvDQProp` and `Df2E1Loc`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

variable {d : ℕ}

/-- `Bad` has probability at most `k δ_e` on every instance of setting (E) at the horizon `m ≤ n`, with a body and
losses that are functions of a parameter, the loss of round `s` read at `θ s`, measurable in `𝒢 s`, and the body at
`θ 0`, every `θ s` giving the same body; a routine with (L1) to (L3), at the parameters of the learner in the
regime. -/
def Df2OnSetEAd (k : ℝ) (Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop) : Prop :=
  ∀ (d n m : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 1 ≤ m → m ≤ n → 0 < δ → δ < 1 → (df2oPar d n δ).eps ≤ 1 / 2 →
  ∀ (Θ : Type) [MeasurableSpace Θ] (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d),
    (∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) → (∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) → ApSpec ap →
    Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap →
  ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (𝒢 : Filtration ℕ m0) (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ),
    (∀ s, Measurable[𝒢 s] (θ s)) → (∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) → Df2SetE d μ 𝒢 ξ e →
    μ {ω | Bad d (df2CtxAt d n δ (Kθ (θ 0 ω)) ap) ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m} ≤
      ENNReal.ofReal (k * (df2oPar d n δ).δe)

/-- Noise, Pi and Gauss fail with probability at most `3 δ_e/7`, adapted parameter. -/
def Df2EvGPropAd : Prop := Df2OnSetEAd (3 / 7) fun _ c π m => ¬ c.EvG π m

/-- The event Y fails on G with probability at most `δ_e/7`, adapted parameter. -/
def Df2EvYPropAd : Prop := Df2OnSetEAd (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvY π m

/-- The event LQ fails on G with probability at most `δ_e/21`, adapted parameter. -/
def Df2EvLQPropAd : Prop := Df2OnSetEAd (1 / 21) fun _ c π m => c.EvG π m ∧ ¬ c.EvLQ π m

/-- The event S-DF fails on G with probability at most `δ_e/7`, adapted parameter. -/
def Df2EvSDFPropAd : Prop := Df2OnSetEAd (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvSDF π m

/-- The event DQ fails on G with probability at most `δ_e/8`, adapted parameter. -/
def Df2EvDQPropAd : Prop := Df2OnSetEAd (1 / 8) fun _ c π m => c.EvG π m ∧ ¬ c.EvDQ π m

/-- Statement E1-loc with an adapted parameter: the epoch fails (a) or (b5') with probability at most
`(149/168) δ_e`. -/
def Df2E1LocAd : Prop := Df2OnSetEAd (149 / 168) fun _ c π m => ¬ c.EpochOK π m

/-- E1-loc with an adapted parameter, from DET and the five adapted budgets (a union bound). -/
def Df2E1LocAdOf : Prop :=
  Df2Det → Df2EvGPropAd → Df2EvYPropAd → Df2EvLQPropAd → Df2EvSDFPropAd → Df2EvDQPropAd → Df2E1LocAd

end AdversarialBco.Poly
