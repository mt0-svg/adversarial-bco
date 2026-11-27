/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStep
public import AdversarialBco.Unified.ProgOTriOut
public import AdversarialBco.Unified.ProgOTriPre

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the program from its prologue

`triSpecO_xstep`: the contract `TriSpecO` (Unified/ProgOSetup.lean) of `xtriO xpre (xstageO xstepO) xoutO` for every
prologue `xpre` meeting `TriPreSpec xpre (KEv TriKX)` at the room `(oT + 340, rT + 72, aT + 29)`: the stages from the
core step `triStepSpec`, the constants `TriKX` (`triKX_stable`), the exponents `triExpO`, the output `triOutSpec_of`,
the magnitudes `triMagO_of`, assembled by `triSpecO_of`. With the prologue `xpreO` (`triPreSpec_of`,
Unified/ProgOTriPre.lean) and `triExpS`: `triSpecO_prog`, the contract of the whole program text.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer
open AdversarialBco.Uni
open AdversarialBco.Unified.ProgO

/-- **TRI-OGD-O on the oracle machine** from a prologue meeting `TriPreSpec`. -/
theorem triSpecO_xstep {xpre : Layout → XCmdO} {Cp kp : ℕ}
    (hp : TriPreSpec xpre (KEv TriKX) Cp kp (oT + 340) (rT + 72) (aT + 29)) :
    TriSpecO (xtriO xpre (xstageO xstepO) xoutO)
      (triCA Cp kp (triCS (2 ^ 920) 105 (2 ^ 1010) 201) (triKS 105 201) (triCO (2 ^ 1010)) (201 + 2)
        (2 ^ 1010 + 2))
      (triKA kp (triKS 105 201) (201 + 2) (201 + 1)) (oT + 340) (rT + 72) (aT + 29) :=
  triSpecO_of hp (triStageSpec_of triStepSpec triExpO triKX_stable (by omega) (by omega) (by omega))
    (triOutSpec_of triExpO (by omega) (by omega) (by omega)) (triMagO_of triExpO) (kCtr_of triKX_stable) (by omega)

theorem TriPreSpec.room {xpre : Layout → XCmdO} {KE : KPred} {C k nS nN nA nS' nN' nA' : ℕ}
    (h : TriPreSpec xpre KE C k nS nN nA) (hs : nS ≤ nS') (hn : nN ≤ nN') (ha : nA ≤ nA') :
    TriPreSpec xpre KE C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ σ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ σ hI hL ⟨hs.trans hR.1, hn.trans hR.2.1, ha.trans hR.2.2⟩

/-- **TRI-OGD-O on the oracle machine**: the program text `xtriO xpreO (xstageO xstepO) xoutO` meets `TriSpecO`. -/
theorem triSpecO_prog :
    TriSpecO (xtriO xpreO (xstageO xstepO) xoutO)
      (triCA (preCf (2 ^ 170)) (preKf 21) (triCS (2 ^ 920) 105 (2 ^ 1010) 201) (triKS 105 201) (triCO (2 ^ 1010))
        (201 + 2) (2 ^ 1010 + 2))
      (triKA (preKf 21) (triKS 105 201) (201 + 2) (201 + 1)) (oT + 340) (rT + 72) (aT + 29) :=
  triSpecO_xstep ((triPreSpec_of triExpS).room (by simp only [oT]; omega) (by simp only [rT]; omega)
    (by simp only [aT]; omega))

end AdversarialBco.Unified.ProgO.TriO
