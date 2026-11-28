/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachSplit
public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# The magnitudes of BL-OW's run: the statements

BL-O's `MagBLO` and `ExpBLO` (Unified/ProgOMag.lean) at BL-OW: the run `modeOW` and the parameters `parOW`.

* `MagBLW`: on every input and every world whose position is bounded by `2^E₀`, BL-OW's state before every round
  `t ≤ n` in mode `run` has its numerators at most `2^E`, `E = C (W + E₀ + 1)^k`, and `μ'` in the box of radius
  `R_int` (`StBnd` at `parOW`);
* `ExpBLW`: for every call of BL-OW with the objective `B'B'ᵀ` (`B'` on the grid `2^{-p}`, `frob2 B' ≤ 2Λ`), a linear
  term with coordinates at most `2^E₀` and one of BL's three pairs (radius, accuracy) at `parOW`, the exponent of
  ELL-O's point is at most `C (W + E₀ + 1)^k`.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (parOW cfgWW modeOW)
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

/-- **BL-OW's magnitude contract.** -/
def MagBLW : Prop :=
  ∃ C k : ℕ, ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 → ∀ w : WorldO d,
    PosBnd (cfgV (cfgWW d n δ r0 R0 a w)) E0 → ∀ (t : ℕ) (st : St d), t ≤ n →
      modeOW d n δ r0 R0 a w t = .run st →
        StBnd (parOW d n δ).p (C * (wU d n δ r0 R0 a + E0 + 1) ^ k) (parOW d n δ).Rint st

/-- **BL-OW's exponent contract.** -/
def ExpBLW : Prop :=
  ∃ C k : ℕ, ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓq : ℚ) (Bp : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (r e : ℚ),
    InU d n δ r0 R0 → c.par = parOW d n δ → (∀ i j, OnG (parOW d n δ).p (Bp i j)) →
    Bit.BLP.frob2 Bp ≤ 2 * (parOW d n δ).Lam → (∀ j, |f j| ≤ 2 ^ E0) → (r, e) ∈ callRE (parOW d n δ) d n →
      ellExpO (clearO (callO c H g ℓq r (Bp * Bpᵀ) f e)) ≤ C * (wU d n δ r0 R0 a + E0 + 1) ^ k

end AdversarialBco.UW.ProgW
