/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOT14

@[expose] public section

/-!
# BL-O's tail, R11 and R12 on the machine

R11 and R12 for BL-O:

* `xT12O`: R12's values (`xR12`) at the test point `x/2^X` that R11's call left in its block, then the test
  `sc 87 < sc 86` (no fire: `xT13O`), else the new epoch. It ends in `RPost` with `m12O`.
* `xT11O`: the data of R11, the ELL-O call, then its flag: `0` leaves for `guard`, `1`
  goes on with `xT12O`. It ends in `RPost` with `m11O`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- R12, then the fire or R13 to R15. -/
def xT12O (xfire xdl : Layout → XCmd) (xcall : Layout → XCmdO) (xcom : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xR12 L)) (xifSO L 87 86 (xT13O xdl xcall xcom L) (.base (xfire L)))

/-- The units of `xT12O`. -/
def u12O (Cf kf Cl kl Ca ka Cc kc d W E E1 X : ℕ) : ℕ :=
  r12Units d X + (u13O Cl kl Ca ka Cc kc d W E E1 + Cf * (d + E + 1) ^ kf + 2)

/-- R11's data, the call, the flag, then R12. -/
def xT11O (xdt : Layout → XCmd) (xcall : Layout → XCmdO) (xfire xdl xcom : Layout → XCmd) (L : Layout) :
    XCmdO :=
  .seq (.base (xdt L)) (.seq (xcall L) (xifSO L sZ oE (xT12O xfire xdl xcall xcom L) (.base (xG L))))

/-- The units of `xT11O`. -/
def u11O (Ct kt Cf kf Cl kl Ca ka Cc kc d W E E1 X : ℕ) : ℕ :=
  Ct * (d + E1 + 1) ^ kt + (Ca * (W + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka +
    (u12O Cf kf Cl kl Ca ka Cc kc d W E E1 X + 2))

end AdversarialBco.Unified.ProgO
