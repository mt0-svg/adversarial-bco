/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOCallA
public import AdversarialBco.Unified.ProgOR2s
public import AdversarialBco.Bit.Transfer.XBLPrepF

@[expose] public section

/-!
# One ELL-O call of BL-O

`callO_holds : CallO`. The command `xcallC xprep` runs v2.1's preparation `xprep` (`callPrepBL`: the inputs of
`blkBL` for `clearQ` of the rowless call). If `r > 0` and `e > 0` (the numerators in the slots `84` and `86`) it runs
the main branch `xmainC` (TailOCallA.lean), whose answer is ELL-O's on `clearO (callO c H g ℓ r P f e)` for BL-O's
test `tstO` (`pmapC_T`, `scale_eq`, `kC_eq`). Otherwise it writes the failure flag `0` into the slot `oE`, which is
ELL-O's answer since `ellOI` fails at once when `r ≤ 0` or `e ≤ 0`. Constants: `C = C_prep + 10^31`,
`k = k_prep + 24`, room `983, 176, 46`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Bit.Transfer.CallSz (pair_bound)
open AdversarialBco.Uni.EllO (abs_lt_ellOSz ellO_expos)
open AdversarialBco.Bit.RQ (clearQ)
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ callOf)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- The command of one call. -/
def xcallC (xprep : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xprep L)) <|
  xifSO L sZ 84 (xifSO L sZ 86 (xmainC L) (.base (toX (VL.sconst L oE ((0 : ℤ) : ℚ)))))
    (.base (toX (VL.sconst L oE ((0 : ℤ) : ℚ))))

theorem e_num_le_mx (I : EllOI d) : I.e.num.natAbs ≤ ellOMx I := by
  unfold ellOMx
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))

/-- ELL-O fails at once on a call with `r ≤ 0` or `e ≤ 0`. -/
theorem ellOI_none {I : EllOI d} (T : (Fin d → ℚ) → Bool) (h : I.r ≤ 0 ∨ I.e ≤ 0) : ellOI I T = none := by
  unfold ellOI; rw [if_pos (Or.inr h)]

theorem eout_of {r : Option (Fin d → ℤ)} {e : ℕ} {σ : Env d} (h : EllOOut blkC r e σ) : EllOut blkBL r e σ := by
  cases r <;> exact h

theorem tstCK_eq (d : ℕ) : tstCK d = 10 * (d * d) + 55 * d + 83 := by
  unfold tstCK mapCK sdotUnits cmK; ring

end AdversarialBco.Unified.ProgO
