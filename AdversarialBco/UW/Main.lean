/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Reduction
public import AdversarialBco.UW.EvProb
public import AdversarialBco.UW.RefReg
public import AdversarialBco.UW.Coup
public import AdversarialBco.UW.WrapIncr
public import AdversarialBco.UW.WrapBias
public import AdversarialBco.UW.BudDom
public import AdversarialBco.UW.Thr
public import AdversarialBco.UW.Rec
public import AdversarialBco.UW.MeasRec
public import AdversarialBco.UW.EngMain
public import AdversarialBco.UW.ProgMachFinal

@[expose] public section

/-!
# Theorem UW

`theoremUW_of_open`: `TheoremUW` (StatementUW.lean) from four bricks of group B as hypotheses, as `theoremUW_of_all`
(UW/Reduction.lean) applied to BL-OW's data `implW P C' k` (UW/ProgRec.lean) and to the proved bricks:

* group A: `rowsUW`, `sifactsUW`, the wrapper `condIncrW`, `condBiasW`, `lemmaUSetW`, Step 2 `coupStepPropUW`, and the
  routes `detOf`, `refRegOf`, `evProbOfUW`;
* group B: `playIntUW`, `posRecUW`, `measRecUW`, `bitsRecUW`, DOM-W `domW`;
* group C: the threshold `thrUW_holds` at `cThr = 10^21`.

The four hypotheses: the cost and space of the program text `P` (`BLOMachOK P C' k`), the program link
(`BLOWLink`), PARAM-W's schedule (`SchedUW`) and the route of the engine (`DomW → EngineRecUW`).

`theoremUW_of_prog`: the same with PARAM-W's schedule (`schedUW`, UW/ParamW.lean) and the engine's route proved from
piece C2 of the round (`Eng.engineOfW`, UW/EngMain.lean); its hypotheses are the program's two clauses
`BLOMachOK P C' k` and `BLOWLink (implW P C' k)`.

`theoremUW`: `TheoremUW`, from `theoremUW_of_prog` and the two clauses of the program text (`ProgW.theoremProgW`).
-/

namespace AdversarialBco.UW

open AdversarialBco.UW.BLOW (implW playIntUW measRecUW schedUW)

/-- **Theorem UW from four bricks of group B as hypotheses.** -/
theorem theoremUW_of_open {P : List BitRAMO.InstrO} {C' : ℝ} {k : ℕ}
    (hmach : Unified.BLO.BLOMachOK P C' k) (hlink : BLOWLink (implW P C' k)) (hsched : SchedUW (implW P C' k))
    (heng : DomW → EngineRecUW (implW P C' k)) : TheoremUW :=
  theoremUW_of_all (I := implW P C' k) (C := cThr)
    { rows := rowsUW
      sifacts := sifactsUW
      condIncr := condIncrW
      condBias := condBiasW
      lemmaUSet := lemmaUSetW
      coup := coupStepPropUW
      detOf := detOf
      refRegOf := refRegOf
      evProbOf := evProbOfUW
      mach := hmach
      link := hlink
      playInt := playIntUW P C' k
      sched := hsched
      pos := posRecUW _
      meas := measRecUW P C' k
      bits := bitsRecUW _
      dom := domW
      engineOf := heng
      thr := thrUW_holds }

/-- **Theorem UW from the program's two clauses** (piece C2 proved: `Eng.engineOfW`). -/
theorem theoremUW_of_prog {P : List BitRAMO.InstrO} {C' : ℝ} {k : ℕ} (hmach : Unified.BLO.BLOMachOK P C' k)
    (hlink : BLOWLink (implW P C' k)) : TheoremUW :=
  theoremUW_of_open hmach hlink (schedUW P C' k) (Eng.engineOfW P C' k)

/-- **Theorem UW** (`TheoremUW`, StatementUW.lean): `theoremUW_of_prog` at BL-OW's program text (`ProgW.theoremProgW`,
UW/ProgMachFinal.lean). -/
theorem theoremUW : TheoremUW := by
  obtain ⟨P, C', k, hlink, hmach⟩ := ProgW.theoremProgW
  exact theoremUW_of_prog hmach hlink

end AdversarialBco.UW
