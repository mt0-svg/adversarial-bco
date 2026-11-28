/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# The events of the reference of Theorem UW on an abstract setting (E)

The cut of `EvProbUW` between the world side (W-SETE, the epoch bound, W-AZ, event (a), event (b), the assembly
`evProbOf`) and the events (c), (d), (e). It is Theorem U's `Df2OnSetEAdV` (Poly/Df2SetEAdV.lean)
with the table T4U in place of `df2oPar d n δ`, the regime `RegimeW` in place of the regime of Theorem U, the failure
`k δc` at the level of the events, and the events read on the weighted path `pathW` of the epoch (UW/Defs.lean).

* `UWOnSetE k Bad`: `Bad` has probability at most `k δc` on every instance of setting (E) at the horizon `m ≤ n`, with
  an adapted parameter `θ s` (the position and the loss parameter of round `s`), an advice `ψ s` measurable after round
  `s`, the context `⟨parW d n ρ.u, n, Kθ (θ 0 ω), fun s => apθ (ψ s ω)⟩` and the unweighted path
  `⟨fun s => gθ s (θ s ω), e · ω, ξ · ω⟩`; `Bad` reads the regime's parameters `ρ` and the context and the path, and
  the events read the weighted path `pathW c ρ.b0 ρ.y0 π`.
* The five Props, with Theorem U's split of the budget `149/168` of an epoch: `EvGPropUW` (event (a) at the level,
  `3/7`), `EvYPropUW` (event (b) under the clip, `1/7`), `EvLQPropUW` (event (c), `1/21`), `EvSDFPropUW` (event (d),
  `1/7`), `EvDQPropUW` (event (e), `1/8`). No event is conditioned on another: the sure ranges replace event (a) in
  the ranges of (b) to (e).

The context `⟨parW d n ρ.u, n, Kθ (θ 0 ω), _⟩` is the one of `ctxU` (UW/Defs.lean) with `Kθ x = kTh n ρ.δc K x.1`, so
the epoch bound of the world instantiates every Prop at P°'s virtual epochs without a rewrite.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World

variable {d : ℕ}

/-- The context of an epoch of the reference of Theorem UW on setting (E): T4U, the horizon `n`, the body at the
parameter of round 0, the routine of round `s` read from the advice. -/
noncomputable def ctxE (d n : ℕ) (ρ : RefW) (Kt : Set (E d)) (ap : ℕ → ApFun d) : Df2Ctx d :=
  ⟨parW d n ρ.u, n, Kt, ap⟩

/-- `Bad` has probability at most `k δc` on every instance of setting (E) for the reference of Theorem UW at the
horizon `m ≤ n`, with an adapted parameter and the routine `apθ (ψ s ω)` in round `s` (`Df2OnSetEAdV` at T4U). -/
def UWOnSetE (k : ℝ) (Bad : (d n : ℕ) → RefW → Df2Ctx d → Df2Path d → ℕ → Prop) : Prop :=
  ∀ (d n m : ℕ) (ρ : RefW), RegimeW d n ρ → 1 ≤ m → m ≤ n →
  ∀ (Θ : Type) [MeasurableSpace Θ] (V : Type) [MeasurableSpace V] (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)
    (apθ : V → ApFun d),
    (∀ q, Df2Body d (parW d n ρ.u).R (Kθ q)) → (∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) →
    (∀ v, ApSpec (apθ v)) → Df2EpochMeasV (parW d n ρ.u) n m Kθ gθ apθ →
  ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (𝒢 : Filtration ℕ m0) (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ),
    (∀ s, Measurable[𝒢 s] (θ s)) → (∀ s, Measurable[𝒢 (s + 1)] (ψ s)) → (∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) →
    Df2SetE d μ 𝒢 ξ e →
    μ {ω | Bad d n ρ (ctxE d n ρ (Kθ (θ 0 ω)) fun s => apθ (ψ s ω))
      ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m} ≤ ENNReal.ofReal (k * ρ.δc)

/-- **Event (a) at the level** fails with probability at most `3 δc/7` (the noise of the unweighted
path, the gauge of the weighted epoch's sample, the draw). -/
def EvGPropUW : Prop :=
  UWOnSetE (3 / 7) fun _ n ρ c π m => ¬ EvGW c π (pathW c ρ.b0 ρ.y0 π) (lgW n ρ.δc) (leW ρ.δc) m

/-- **Event (b) under the clip** fails with probability at most `δc/7`. -/
def EvYPropUW : Prop :=
  UWOnSetE (1 / 7) fun _ n ρ c π m => ¬ EvYW c (pathW c ρ.b0 ρ.y0 π) (sYW n ρ.y0 ρ.δc) m

/-- **Event (c), LQ, at T4U with sure ranges** fails with probability at most `δc/21`. -/
def EvLQPropUW : Prop :=
  UWOnSetE (1 / 21) fun d n ρ c π m => ¬ EvLQW c (pathW c ρ.b0 ρ.y0 π) (b1W c.p d n ρ.u) m

/-- **Event (d), S-DF, at T4U with sure ranges** fails with probability at most `δc/7`. -/
def EvSDFPropUW : Prop :=
  UWOnSetE (1 / 7) fun d n ρ c π m => ¬ EvSDFW c (pathW c ρ.b0 ρ.y0 π) (bnW c.p d n ρ.u) m

/-- **Event (e), DQ, at T4U with sure ranges** fails with probability at most `δc/8`. -/
def EvDQPropUW : Prop :=
  UWOnSetE (1 / 8) fun d n ρ c π m => ¬ EvDQW c (pathW c ρ.b0 ρ.y0 π) (bnW c.p d n ρ.u) m

/-- The five events of P°'s virtual epoch started before round `a`, at its horizon `n - a`: the first clause of
`GoodU` at `a`. -/
def FiveU {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}
    (B : RunW d n K W) (ρ : RefW) (a : ℕ) (ω : Ω) : Prop :=
  EvGW (ctxU B ρ a ω) (pathU B ρ a ω) (epU B ρ a ω) (lgW n ρ.δc) (leW ρ.δc) (n - a) ∧
    EvYW (ctxU B ρ a ω) (epU B ρ a ω) (sYW n ρ.y0 ρ.δc) (n - a) ∧
    EvLQW (ctxU B ρ a ω) (epU B ρ a ω) (b1W (parW d n ρ.u) d n ρ.u) (n - a) ∧
    EvSDFW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a) ∧
    EvDQW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a)

end AdversarialBco.UW
