/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# BL's bounds: the position, the state and the calls

The data that the magnitude bounds of BL's state and the exponents of its calls are stated with: the position over one
positive denominator (`PosBnd`), the bounds of BL's state in mode `run` on the grid `2^{-p}` (`StBnd`), and the pairs
(radius, accuracy) of BL's three calls (`callRE`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## The magnitudes of the state -/

/-- The position `(μ_S, A_S)` over one positive denominator `D_S ≤ 2^E₀`, numerators at most `2^E₀`. -/
def PosBnd (cfg : Cfg d) (E0 : ℕ) : Prop :=
  ∃ DS : ℤ, 0 < DS ∧ DS ≤ 2 ^ E0 ∧ (∀ j, ∃ x : ℤ, |x| ≤ 2 ^ E0 ∧ (x : ℚ) / DS = cfg.μS j) ∧
    ∀ i j, ∃ x : ℤ, |x| ≤ 2 ^ E0 ∧ (x : ℚ) / DS = cfg.AS i j

/-- BL's state in mode `run`: the numerators of `A', B', b', k', G', l'` on the grid `2^{-p}` at most `2^E`, every
coordinate of `μ'` at most `R` in absolute value. -/
def StBnd (p E R : ℕ) (st : St d) : Prop :=
  (∀ i j, |qn p (st.A i j)| ≤ 2 ^ E) ∧ (∀ i j, |qn p (st.B i j)| ≤ 2 ^ E) ∧ (∀ j, |qn p (st.b j)| ≤ 2 ^ E) ∧
    |qn p st.k| ≤ 2 ^ E ∧ (∀ j, |qn p (st.G j)| ≤ 2 ^ E) ∧ |qn p st.l| ≤ 2 ^ E ∧ ∀ j, |st.mu j| ≤ R

/-- The pairs (radius, accuracy) of BL's three calls: R11 in the first round of an epoch, R11 after it, R14. -/
def callRE (P : Par) (d n : ℕ) : List (ℚ × ℚ) :=
  [(1 - P.eps, (1 - P.eps) ^ 2 / (P.Ne * d * 8)),
   (BLP.rB P / 2, BLP.rB P ^ 2 / (P.Ne * d * 8)), (BLP.rB P / 2, eBL P d n)]

end AdversarialBco.Bit.Transfer.BLM
