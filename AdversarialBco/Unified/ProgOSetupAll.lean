/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetupMode
public import AdversarialBco.Unified.ProgOSetupP0
public import AdversarialBco.Unified.ProgOSetupCoins
public import AdversarialBco.Unified.ProgOSetupParam
public import AdversarialBco.Unified.ProgOSetupCross
public import AdversarialBco.Unified.ProgOTriAll

@[expose] public section

/-!
# BL-O's setup on the oracle bit RAM: `ProgSetupO`

The six sub-block contracts of `xinitO` (Unified/ProgOSetup.lean), each proved: P0 (`p0SpecO`), PARAM at `k_δ`
(`paramSpecO`), TRI-OGD-O (`triSpecO_prog`, on the prologue `triPreSpec_of`), the coin count
(`coinsSpecO`), the cross check (`crossSpecO`), the mode (`modeSpecO`); `progSetupO_of` assembles them.
-/

namespace AdversarialBco.Unified.ProgO

/-- **BL-O's setup on the oracle bit RAM** (`ProgSetupO`, Unified/ProgOBL.lean). -/
theorem progSetupO : ProgSetupO :=
  progSetupO_of ⟨_, _, _, _, _, _, p0SpecO⟩ ⟨_, _, _, _, _, _, paramSpecO⟩ ⟨_, _, _, _, _, _, TriO.triSpecO_prog⟩
    ⟨_, _, _, _, _, _, coinsSpecO⟩ ⟨_, _, _, _, _, _, crossSpecO⟩ ⟨_, _, _, _, _, modeSpecO⟩

end AdversarialBco.Unified.ProgO
