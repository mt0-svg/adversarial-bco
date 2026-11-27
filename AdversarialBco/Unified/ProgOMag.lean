/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# The magnitudes of BL-O's run (the statements)

The tail's contract `SpecTail` (ProgOSplit.lean) asks for BL-O's invariant before round `t + 1` with one exponent `E`
for every round. One step does not keep a fixed `E` (`b'`, `k'`, `G'`, `l'` grow by an increment each round), so the
bound comes from two statements on BL-O's run, taken as hypotheses by the tail's proof:

* `MagBLO`: on every input and every world whose position is bounded by `2^E₀`, BL-O's state before every round
  `t ≤ n` in mode `run` has the numerators of `A', B', b', k', G', l'` on the grid `2^{-p}` at most `2^E` with
  `E = C (W + E₀ + 1)^k`, and `μ'` in the box of radius `R_int` (`StBnd` at `parO`);
* `ExpBLO`: for every call of BL-O (`callO`, no row, the radius `R_int`) with the objective `B'B'ᵀ`, `B'` on the grid
  `2^{-p}` with `frob2 B' ≤ 2Λ`, a linear term with coordinates at most `2^E₀` and one of BL's three pairs (radius,
  accuracy) at `parO`, the exponent `ellExpO` of ELL-O's point is at most `C (W + E₀ + 1)^k`, whatever the quadratic
  constraint.

`W = wU d n δ r0 R0 a`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

/-- **BL-O's magnitude contract.** On every input of `TheoremUnified` and every world of the oracle machine whose
position is bounded by `2^E₀` (`PosBnd`), BL-O's state before every round `t ≤ n` in mode `run` has numerators at
most `2^E`, `E = C (W + E₀ + 1)^k`, and `μ'` in the box of radius `R_int` (`StBnd` at `parO`). -/
def MagBLO : Prop :=
  ∃ C k : ℕ, ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 → ∀ w : WorldO d,
    PosBnd (cfgV (cfgW d n δ r0 R0 a w)) E0 → ∀ (t : ℕ) (st : St d), t ≤ n →
      modeO d n δ r0 R0 a w t = .run st →
        StBnd (parO d n δ).p (C * (wU d n δ r0 R0 a + E0 + 1) ^ k) (parO d n δ).Rint st

/-- **BL-O's exponent contract.** For every call of BL-O with the parameters `parO`, the objective `B'B'ᵀ` (`B'` on
the grid `2^{-p}`, `frob2 B' ≤ 2Λ`), a linear term `f` with coordinates at most `2^E₀` and one of BL's three pairs
(radius, accuracy) (`callRE` at `parO`), the exponent of ELL-O's point is at most `C (W + E₀ + 1)^k`, whatever the
quadratic constraint. -/
def ExpBLO : Prop :=
  ∃ C k : ℕ, ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓq : ℚ) (Bp : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (r e : ℚ),
    InU d n δ r0 R0 → c.par = parO d n δ → (∀ i j, OnG (parO d n δ).p (Bp i j)) →
    Bit.BLP.frob2 Bp ≤ 2 * (parO d n δ).Lam → (∀ j, |f j| ≤ 2 ^ E0) → (r, e) ∈ callRE (parO d n δ) d n →
      ellExpO (clearO (callO c H g ℓq r (Bp * Bpᵀ) f e)) ≤ C * (wU d n δ r0 R0 a + E0 + 1) ^ k

end AdversarialBco.Unified.ProgO
