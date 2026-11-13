/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLPosQ
public import AdversarialBco.Bit.ApQ.FrameB

@[expose] public section

/-!
# `PosTri RoutinesQ` and `PosInst` for BL's routines

The frame inclusion `B̄(frameQ, 1/2) ⊆ K` is `frameQ_ball` of Bit/ApQ/FrameB.lean; with `posTriQ` of
Bit/BLPosQ.lean it gives `PosTri RoutinesQ`, and `posInst_of_posTri` gives `PosInst (blInst P RoutinesQ)` for every
program `P`.
-/

namespace AdversarialBco.Bit.RQ

open AdversarialBco.Bit.BLP (PosTri blInst posInst_of_posTri)

theorem frameQBall : FrameQBall := fun _ _ _ _ _ _ hI => (ApQ.frameQ_ball hI).1

/-- TRI-OGD staged as BL computes it is the position `PosTri` asks for. -/
theorem posTri_routinesQ : PosTri RoutinesQ := posTriQ frameQBall

/-- `PosInst` for BL's routines, every program. -/
theorem posInst_routinesQ (P : List AdversarialBco.BitRAM.Instr) :
    AdversarialBco.Bit.Asm.PosInst (blInst P RoutinesQ) :=
  posInst_of_posTri posTri_routinesQ

end AdversarialBco.Bit.RQ
