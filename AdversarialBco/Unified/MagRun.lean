/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.MagStep

@[expose] public section

/-!
# The magnitudes of BL-O's run, part C: the first mode

`mode0O_run`: the first mode `run` of BL-O has `ε' ≤ 1/2` and BL's initial state.
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (Par St Mode init rnd)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (cfgV InU wU)
open AdversarialBco.BitRAMO (WorldO)

variable {d : ℕ}

/-- The first mode `run`: `ε' ≤ 1/2` and BL's initial state. -/
theorem mode0O_run {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {st : St d} (h : mode0O orc c = .run st) :
    c.par.eps ≤ 1 / 2 ∧ st = init c.par d := by
  unfold mode0O at h
  by_cases h1 : 1 / 2 < c.par.eps
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : crossOK orc c
    · rw [if_pos h2] at h; cases h; exact ⟨not_lt.1 h1, rfl⟩
    · rw [if_neg h2] at h; cases h

end AdversarialBco.Unified.MagO
