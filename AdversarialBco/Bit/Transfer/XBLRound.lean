/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# One round of BL's program (frozen statement)

The program assembly (the driver: `prog_ok_frozenR` to `MachOK`, and `BLLink`) takes this statement as a hypothesis;
the round itself proves it from the three split statements of Bit/Transfer/XBLSplit.lean. The
theorem to prove: `roundBL_of : CallBL → MagBL → ExpBL → RoundBL`.

`RoundBL`: one command `xround L` plays round `t < n` of BL's run against an admissible strategy `σs`: from BL's
invariant before round `t` (`BLInv` with the mode `modeAt .. t`) it ends in BL's invariant before round `t + 1` (with
the mode `modeAt .. (t + 1)`), with BL's play `play .. t` recorded as the point of round `t`. The world's loss of round
`t` is the strategy's loss on BL's history up to round `t` (in the game world of the program it is the loss on the
points the program recorded, which are BL's plays by induction). Work term `W = d + m + size M + size n + E + 1`:
within `C W^k` units, under `C W^k ≤ ℓ` and `C W^k < 2^ℓa`, with the block's room `nS, nN, nA` in the layout, and
`E` at least `Cn (d + m + size M + size n + E₀ + 1)^kn` for a bound `2^E₀` of the position (`PosBnd`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Bit.Asm

/-- **The round contract (frozen).** -/
def RoundBL : Prop :=
  ∃ (xround : Layout → XCmd) (C k Cn kn nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M E0 E ℓa ℓ t : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
      (b : Fin m → ℚ) (σs : Strategy d) (σ : Env d),
      InputOK d n m M A b → AdmStrat (polytope A b) n σs → t < n →
      (∀ x, w.f t x =
        RealRAM.lossAd σs 0 (fun i => BitRAM.toE ((traj RoutinesQ d n m A b σs w.cs (t + 1)).2 i)) t x) →
      LayOK L d ℓa → BLLay L → blkBL.OK L nS nN nA →
      PosBnd (cfgOf RoutinesQ d n m A b w.cs) E0 → Cn * (d + m + M.size + n.size + E0 + 1) ^ kn ≤ E →
      C * (d + m + M.size + n.size + E + 1) ^ k ≤ ℓ → C * (d + m + M.size + n.size + E + 1) ^ k < 2 ^ ℓa →
      BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (modeAt RoutinesQ d n m A b σs w.cs t) t σ →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xround L) σ (C * (d + m + M.size + n.size + E + 1) ^ k) (fun σ' =>
        BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (modeAt RoutinesQ d n m A b σs w.cs (t + 1))
          (t + 1) σ' ∧
        σ'.pts = Function.update σ.pts t (BitRAM.toE (play RoutinesQ d n m A b σs w.cs t)))

end AdversarialBco.Bit.Transfer.BLM
