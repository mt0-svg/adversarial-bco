/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIProc
public import AdversarialBco.Poly.Df2EvSIRound

@[expose] public section

/-!
# The epoch on setting (E) with an adapted parameter: the path

On an instance where the loss of round `s` is read at a parameter `θ s`, measurable in `𝒢 s`, and the body at `θ 0`
(`hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)`): the path of the epoch at `ω` (`pathWAd`), and its losses are admissible on
the body of the context (`admAd`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

namespace EvAd

open ApMeas EvGY Layer2

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
  (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d)

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- The path of the epoch at `ω`, the loss of round `s` read at the parameter of round `s`. -/
def pathWAd (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) : Df2Path d :=
  ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩

omit [MeasurableSpace Θ] in
/-- The losses of the path are admissible on the body of the context. -/
theorem admAd (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) (θ : ℕ → Ω → Θ)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) : ∀ s < m, AdmLoss (Kθ (θ 0 ω)) (gθ s (θ s ω)) :=
  fun s hs => hK s ω ▸ hadm (θ s ω) s hs

end EvAd

end AdversarialBco.Poly
