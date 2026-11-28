/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPar

@[expose] public section

/-!
# BL-O's tail, R13 to R15 on the machine

R13 to R15 for BL-O's rowless configuration `cfgV c` and its ELL-O call:

* `xT14O`: the data of R14, the call, then the flag of the block: `0` leaves for `guard`, `1` commits
  the new state (v2.1's R15 with `commitBL`). It ends in `RPost` with the mode `m14O`.
* `xT13O`: R13's values (`xR13`), R13's guard `sc 85 < sc 86`, else `xT14O`. It ends in `RPost` with `m13O`.

`TPostO`: the bounds the caller gives on BL-O's calls when a stage's mode is the new state.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- The bounds the caller gives when the mode `mo` of a stage is the new state. -/
def TPostO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n E : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ)
    (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) (mo : Mode d) : Prop :=
  ∀ mu' : Fin d → ℚ, mo = .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ →
    StBnd c.par.p E c.par.Rint ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ ∧
    ∀ x, apI orc c (callLO c n Bp bp kp wmu) = some x →
      (∀ j, |x j| ≤ 2 ^ E) ∧ ellExpO (clearO (callLO c n Bp bp kp wmu)) ≤ E

/-- R14 and R15: the data, the call, the flag. -/
def xT14O (xdl : Layout → XCmd) (xcall : Layout → XCmdO) (xcom : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xdl L)) (.seq (xcall L) (.base (xifS L sZ oE (xcom L) (xG L))))

/-- The units of `xT14O`. -/
def u14O (Cl kl Ca ka Cc kc d W E E1 G2 : ℕ) : ℕ :=
  Cl * (d + G2 + 1) ^ kl + (Ca * (W + E1 + Cl * (d + G2 + 1) ^ kl + 1) ^ ka + (Cc * (d + E + 1) ^ kc + 3))

/-- R13, then its guard, then R14 and R15. -/
def xT13O (xdl : Layout → XCmd) (xcall : Layout → XCmdO) (xcom : Layout → XCmd) (L : Layout) : XCmdO :=
  .seq (.base (xR13 L)) (xifSO L 85 86 (.base (xG L)) (xT14O xdl xcall xcom L))

/-- The units of `xT13O`. -/
def u13O (Cl kl Ca ka Cc kc d W E E1 : ℕ) : ℕ :=
  r13Units d + (u14O Cl kl Ca ka Cc kc d W E E1 (8 * E1 + 3 * d + 2) + 2)

end AdversarialBco.Unified.ProgO
