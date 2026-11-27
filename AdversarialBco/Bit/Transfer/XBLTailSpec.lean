/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTail
public import AdversarialBco.Bit.Transfer.XBLStep

@[expose] public section

/-!
# The tail of BL's round in mode `run`: the point `w_μ`

`wmuOf`: the point `w_μ = μ - (ŝ5 / 2^p) A (Γ / G)` that R14's call reads, from the state's `μ` and `A`, the slot
value `ŝ5` (`s5 = ŝ5 / 2^p`) and the draw's numerators `Γ` over `G = 2^(2 p_B)`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- `w_μ = μ' - (ŝ5 / 2^p) A' (Γ / G)`, `G = 2^(2 p_B)`. -/
def wmuOf (P : Par) (st : St d) (s5 : ℤ) (Γ : Fin d → ℤ) : Fin d → ℚ :=
  st.mu - ((s5 : ℚ) / 2 ^ P.p) • (st.A *ᵥ fun k => (Γ k : ℚ) / 2 ^ (2 * gsm_prec P.B))

end AdversarialBco.Bit.Transfer.BLM
