/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1
public import AdversarialBco.Poly.Df2Run
public import AdversarialBco.Poly.MachLang

@[expose] public section

/-!
# The observations and the losses of a strategy depend on the past only

`obsAd_congr`: the observations of a strategy `σ` up to round `t` read the points of the rounds before `t` only.
`lossAd_congr`: so does the loss the strategy chooses in round `t`.
-/

open MeasureTheory

namespace AdversarialBco.Poly.Conj1

open AdversarialBco.RealRAM

variable {d : ℕ}

theorem obsAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} :
    ∀ t, (∀ i < t, x i = y i) → obsAd σ ε x t = obsAd σ ε y t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := obsAd_congr σ ε t fun i hi => h i (by omega)
    have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i (by omega)
    simp only [obsAd, ih, hx, h t (by omega)]

theorem lossAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (t : ℕ) (h : ∀ i < t, x i = y i) :
    lossAd σ ε x t = lossAd σ ε y t := by
  have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i i.2
  simp only [lossAd, obsAd_congr σ ε t h, hx]

end AdversarialBco.Poly.Conj1
