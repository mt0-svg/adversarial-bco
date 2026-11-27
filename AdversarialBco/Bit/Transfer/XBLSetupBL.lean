/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupInv
public import AdversarialBco.Bit.Transfer.XBLSetupEpoch
public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# BL's setup on the machine: a tactic

`fomega`: `omega` after unfolding the frames of the setup and the cell names.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The cells changed after the calls. -/
def Sx (y : ℕ) : Prop := S3 y ∨ SE y ∨ y = sMode ∨ y = 124
def Nx (j : ℕ) : Prop := N3 j ∨ NE j
def Ax (a c : ℕ) : Prop := A3 a c ∨ AE (d := d) a c

/-- `omega` after unfolding the frames of the setup and the cell names. -/
macro "fomega" : tactic => `(tactic| ((try simp only [SC, NC, AC, Sx, Nx, Ax, S3, N3, A3, SE, NE, AE, rD, rM, rMk,
  rOne, rP, rPF, rNb, rB, sZ, sMode, sFirst, sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho,
  sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu, sK, sL, sBadS, sGN, sRQ, tR, rD1, rk, aMuS, aAS, aC, aMu,
  aA, aB, ab, aG, aRw, ne_eq, not_or, not_and, not_exists, not_lt, not_le]) <;> omega))

end AdversarialBco.Bit.Transfer.BLM
