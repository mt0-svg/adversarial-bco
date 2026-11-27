/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOAsm
public import AdversarialBco.Unified.TailOCall
public import AdversarialBco.Unified.TailOData
public import AdversarialBco.Unified.TailOFire

@[expose] public section

/-!
# The tail of BL-O's round

`progTail_holds : ProgTail`, from `progTail_of'` (TailOAsm.lean) and the four contracts of TailOSpec.lean:
`DataTO`, `DataLO` (TailOData.lean), `FireO` (TailOFire.lean) and `CallO` (TailOCall.lean).
-/

namespace AdversarialBco.Unified.ProgO

/-- **The tail of BL-O's round** (`ProgTail`). -/
theorem progTail_holds : ProgTail :=
  progTail_of' TailD.dataTO_holds TailD.dataLO_holds TailD.fireO_holds callO_holds

end AdversarialBco.Unified.ProgO
