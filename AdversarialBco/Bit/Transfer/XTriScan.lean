/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriRow

@[expose] public section

/-!
# TRI-M, tactics for the machine rules of a stage

`trimne` (a disequality of indices from the context, in either direction) and `trimenv'` (`trimenv` with the
disequalities from the context).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- A disequality of indices from the context, in either direction. -/
macro "trimne" : tactic => `(tactic| first | assumption | (apply Ne.symm; assumption) | omega)

/-- `trimenv` with the disequalities from the context. -/
macro "trimenv'" : tactic =>
  `(tactic| (simp (disch := trimne) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

end AdversarialBco.Bit.Transfer
