/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.WorldVEAd
public import AdversarialBco.Poly.Df2WorldAz

@[expose] public section

/-!
# The clean loss of a loss process

The clean loss of round `t` at the parameter `l` is `fL K L t l`: the loss `L t l` on the interior of `K` and `0`
elsewhere. It is jointly measurable in `(l, y)` by the Carathéodory lemma (`measurable_fL`, from
`Conj1.measurable_piecewise_interior`).
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly.Conj1

open Layer2

variable {d : ℕ}

/-! ## The clean round with a loss parameter -/

open Classical in
/-- The clean loss of round `t` at the parameter `l`: `L t l` on the interior of `K`, `0` elsewhere. -/
noncomputable def fL (K : Set (E d)) {Λ : Type} (L : ℕ → Λ → E d → ℝ) (t : ℕ) (l : Λ) : E d → ℝ :=
  (interior K).piecewise (L t l) 0

theorem measurable_fL {K : Set (E d)} {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ} {t : ℕ}
    (hconv : ∀ l, ConvexOn ℝ K (L t l)) (hm : ∀ y ∈ interior K, Measurable fun l => L t l y) :
    Measurable fun p : Λ × E d => fL K L t p.1 p.2 :=
  Conj1.measurable_piecewise_interior K (L t) hconv hm

end AdversarialBco.Poly.Conj1
