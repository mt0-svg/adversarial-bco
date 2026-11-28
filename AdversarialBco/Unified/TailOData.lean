/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPar
public import AdversarialBco.Bit.Transfer.XBLDataLF

@[expose] public section

/-!
# The data of R11 TEST and R14 LINE at BL-O's PARAM

The data commands `xdt`, `xdl` of R11 TEST and R14 LINE (Bit/Transfer/XBLDataTF.lean, XBLDataL.lean) at
`cfg.par = parN ne d n`, `1 ≤ ne`, with the constants `1024`, `3`. The proofs read PARAM only through `Λ = d N_e`,
`1 ≤ N_e`, `0 < 1/ê`, the rounding of its fields onto the grid `2^{-pF}` and `0 < R'`; each holds at `parN` as at
`par d n = parN (Ne d n) d n`.
-/

namespace AdversarialBco.Unified.ProgO.TailD

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.Bit AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM AdversarialBco.Bit.Transfer.BLM.DataM
open AdversarialBco.Unified.BLO (parN)

variable {d : ℕ}

/-! ## PARAM's fields at `parN` -/

theorem parN_onG_sb (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).sb := onG_dn' _ _

theorem parN_onG_R (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).R := onG_up' _ _

theorem parN_R_pos (ne d n : ℕ) (hd : 1 ≤ d) : 0 < (parN ne d n).R := DataP.up_pos _ _ d _ hd

theorem parN_eHat_pos (ne d n : ℕ) : (0 : ℚ) < (parN ne d n).eHat⁻¹ := by
  rw [tlN_eHat, one_div, inv_inv]; exact_mod_cast tlHN_pos ne d n

end AdversarialBco.Unified.ProgO.TailD
