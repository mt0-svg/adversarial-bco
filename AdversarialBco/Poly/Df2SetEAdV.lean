/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# Setting (E) with an adapted parameter and an advice per round

`Df2OnSetEAdV` runs the routine `apθ (ψ s ω)` in round `s` of the epoch, an advice `ψ s` measurable in `𝒢 (s + 1)`:
the context is `df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))`. The round map after the observation is jointly
measurable in the parameter and the advice (`Df2EpochMeasV`), so the mode process stays adapted; the increments of
round `s` never read the routine.

The five Props `Df2EvGPropAdV`, ..., `Df2EvDQPropAdV` carry the events and the constants of the five budgets G, Y, LQ,
S-DF, DQ. At `apNone`, the routine that always fails, `Df2EpochMeasV` gives `Df2EpochMeas` (`Df2EpochMeasV.none`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

variable {d : ℕ}

/-- (L1) with an advice: the gauge and the extensions as in `Df2EpochMeas`, and the round map after the observation
with the routine `apθ v` jointly measurable in the parameter, the advice, the state, the draw and the observation. -/
def Df2EpochMeasV (p : Df2OPar) (n m : ℕ) {Θ : Type} [MeasurableSpace Θ] {V : Type} [MeasurableSpace V]
    (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (apθ : V → ApFun d) : Prop :=
  (Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) ∧
  (∀ s < m, Measurable fun x : Θ × E d => df2Ext p (Kθ x.1) (gθ s x.1) x.2) ∧
  Measurable fun x : (Θ × V) × Df2St d × (Fin d → ℝ) × ℝ =>
    df2NextAP (apθ x.1.2) p n (df2KepsOf (Kθ x.1.1) p.eps) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2

/-- `Bad` has probability at most `k δ_e` on every instance of setting (E) at the horizon `m ≤ n` with an adapted
parameter (the loss of round `s` read at `θ s`, measurable in `𝒢 s`, the body at `θ 0`) and the routine `apθ (ψ s ω)`
in round `s`, the advice `ψ s` measurable in `𝒢 (s + 1)`,
every routine with (L2) and (L3). -/
def Df2OnSetEAdV (k : ℝ) (Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop) : Prop :=
  ∀ (d n m : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 1 ≤ m → m ≤ n → 0 < δ → δ < 1 → (df2oPar d n δ).eps ≤ 1 / 2 →
  ∀ (Θ : Type) [MeasurableSpace Θ] (V : Type) [MeasurableSpace V] (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)
    (apθ : V → ApFun d),
    (∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) → (∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) →
    (∀ v, ApSpec (apθ v)) → Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ →
  ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (𝒢 : Filtration ℕ m0) (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ),
    (∀ s, Measurable[𝒢 s] (θ s)) → (∀ s, Measurable[𝒢 (s + 1)] (ψ s)) → (∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) →
    Df2SetE d μ 𝒢 ξ e →
    μ {ω | Bad d (df2CtxAtF d n δ (Kθ (θ 0 ω)) fun s => apθ (ψ s ω))
      ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m} ≤ ENNReal.ofReal (k * (df2oPar d n δ).δe)

/-- Noise, Pi and Gauss fail with probability at most `3 δ_e/7`, adapted parameter, advice per round. -/
def Df2EvGPropAdV : Prop := Df2OnSetEAdV (3 / 7) fun _ c π m => ¬ c.EvG π m

/-- The event Y fails on G with probability at most `δ_e/7`, adapted parameter, advice per round. -/
def Df2EvYPropAdV : Prop := Df2OnSetEAdV (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvY π m

/-- The event LQ fails on G with probability at most `δ_e/21`, adapted parameter, advice per round. -/
def Df2EvLQPropAdV : Prop := Df2OnSetEAdV (1 / 21) fun _ c π m => c.EvG π m ∧ ¬ c.EvLQ π m

/-- The event S-DF fails on G with probability at most `δ_e/7`, adapted parameter, advice per round. -/
def Df2EvSDFPropAdV : Prop := Df2OnSetEAdV (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvSDF π m

/-- The event DQ fails on G with probability at most `δ_e/8`, adapted parameter, advice per round. -/
def Df2EvDQPropAdV : Prop := Df2OnSetEAdV (1 / 8) fun _ c π m => c.EvG π m ∧ ¬ c.EvDQ π m

/-- The routine that always fails. The round map after the observation is then the constant `guard`, so
`Df2EpochMeasV` gives `Df2EpochMeas` at it (`Df2EpochMeasV.none`); the lemmas of the frozen functions read only
the gauge and the extensions of `Df2EpochMeas`. -/
def apNone : ApFun d := fun _ _ _ _ _ _ _ => none

theorem df2NextAP_none (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) :
    df2NextAP apNone p n Keps st ξ w Y = .guard := by
  unfold df2NextAP apNone
  dsimp only
  split_ifs <;> rfl

theorem Df2EpochMeasV.none {p : Df2OPar} {n m : ℕ} {Θ : Type} [MeasurableSpace Θ] {V : Type} [MeasurableSpace V]
    {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ} {apθ : V → ApFun d}
    (h : Df2EpochMeasV p n m Kθ gθ apθ) : Df2EpochMeas p n m Kθ gθ apNone := by
  refine ⟨h.1, h.2.1, ?_⟩
  have heq : (fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP apNone p n (df2KepsOf (Kθ x.1) p.eps) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2) =
      fun _ => Df2Mode.guard := funext fun x => df2NextAP_none p n _ _ _ _ _
  rw [heq]
  exact measurable_const

end AdversarialBco.Poly
