/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.Transfer.XBLR2g

@[expose] public section

/-!
# BL's setup on the machine: P3's count and P5's row test

One pass over the input rows `r < m` (R2's cells): row `r` is read from its cells and cleared (`XV.inRow`:
`â_r = a_r Π_r`, `b̂_r D_S = b_r Π_r D_S`), then `s = â_r·â_r`; when `s > 0` (the row is kept), `rMk += 1`,
`u = b̂_r D_S - â_r·μ̂_S`, and the flag `sBadS` is set when `u ≤ 0`. `XV.s3`: `rMk` ends at the count of the rows with
`s > 0`, the flag at `1` iff some such row has `u ≤ 0`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The slot of P5's flag: some kept row has `β̃ ≤ 0`. -/
abbrev sBadS : ℕ := 29


/-- The cells the rows change. -/
def S3 (y : ℕ) : Prop := y = sBadS ∨ (sGN ≤ y ∧ y ≤ sRQ) ∨ tR ≤ y
def N3 (j : ℕ) : Prop := j = rMk ∨ (rD1 ≤ j ∧ j ≤ rk)
def A3 (a _k : ℕ) : Prop := a = aRw

/-- `omega` after unfolding the cell names (BL's, R2's, the rows'). -/
macro "somega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, sZ, sDS, aMuS, aRw, rD1, rK, rI, rTT, rjj,
  rr, rk, sGN, sGD, sTa, sRB, sRD, sRT, sRN, sRQ, tR, sBadS, oE, rEE, aWE, S3, N3, N3r, A3, ne_eq, not_or, not_and,
  not_not]) <;> omega))


end AdversarialBco.Bit.Transfer.BLM
