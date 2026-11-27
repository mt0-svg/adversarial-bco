/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.Transfer.XTriEnt

@[expose] public section

/-!
# TRI-M in integers

The integers of a stage of TRI-M as pure functions: the rational stage of Bit/RoutQ.lean at its grids.

* The grid of the iterates `2^{-G}`, `G = B_v + j_s + j_a` (`tzG`), the grid of the core output (`tzGc`), the
  precision of a draw (`tzP`); the positions in integers (`PosZ`) and the stage position `(μ̂, T̂) / D` (`StZ`).
* One draw: its numerators (`tzY`), its constants (`DC`), the point `ẑ` (`tzZ`), the entries of the rounded
  subgradient (`tzRMu`, `tzRLow`, `tzRDiag`) and the next iterate (`tzUpd`); the composition at the grids (`tzComp`).
-/

namespace AdversarialBco.Bit.TriM

open AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer Matrix

variable {d : ℕ}

/-- A position in integers: `(μ̂, T̂)`. -/
abbrev PosZ (d : ℕ) := (Fin d → ℤ) × Matrix (Fin d) (Fin d) ℤ

/-! ## Constants -/

/-- `G = B_v + j_s + j_a`, the grid `2^{-G}` of the iterates. -/
def tzG (d ℓ : ℕ) : ℕ := triBvQ d + triJsQ d ℓ + triJaQ d

/-- `G_c = G + n_e`, the grid of the core output (the average of `2^{n_e}` iterates). -/
def tzGc (d ℓ : ℕ) : ℕ := tzG d ℓ + triNeQ d ℓ

/-- `p`, the precision of BM-INT at `B_g` bits: the draws are integers over `2^{2p}`. -/
def tzP (d : ℕ) : ℕ := gsm_prec (triBgQ d)

/-- The constants of one draw: `P_B = 2^{B_v}`, `P_2 = 2^{2p}`, `P_G = 2^G`, `P_j = 2^{j_a}`, the box bounds at the
grid (`r 2^G`, `a 2^G`, `b 2^G`), and `d`. -/
structure DC where
  PB : ℤ
  P2 : ℤ
  PG : ℤ
  Pj : ℤ
  R : ℤ
  Al : ℤ
  Bh : ℤ
  dd : ℤ

/-! ## One draw -/

/-- `ẑ = X̂_μ 2^{2p} + X̂_T Y`, `μ + T y` at the grid `2^{-(G + 2p)}`. -/
def tzZ (X : PosZ d) (Y : Fin d → ℤ) (P2 : ℤ) : Fin d → ℤ := fun i => X.1 i * P2 + ∑ l, X.2 i l * Y l

/-- The entry `μ_i` of the rounded subgradient at the grid `2^{-B_v}`. -/
def tzRMu (A : Fin d → ℤ) (Bb PB : ℤ) (i : Fin d) : ℤ := A i * PB / Bb

/-- The entry `(i, l)`, `l < i`, of the rounded subgradient. -/
def tzRLow (A Y : Fin d → ℤ) (Bb PB P2 : ℤ) (i l : Fin d) : ℤ := A i * Y l * PB / (Bb * P2)

/-- The entry `(i, i)` of the rounded subgradient: `⌊(A_i Y_i / (|β̃| P_2) - P_G / (8 d T̂_ii)) P_B⌋`. -/
def tzRDiag (A Y : Fin d → ℤ) (Bb PB P2 PG dd Tii : ℤ) (i : Fin d) : ℤ :=
  (A i * Y i * (8 * dd * Tii) - PG * Bb * P2) * PB / (Bb * P2 * (8 * dd * Tii))

/-- The next iterate at the grid, from the kept row read in the stage position (`A = T̂ᵀ row`), its `|β̃|` and the draw
`Y`. -/
def tzUpd (c : DC) (X : PosZ d) (A Y : Fin d → ℤ) (Bb : ℤ) : PosZ d :=
  (fun i => clipZ (-c.R) c.R (X.1 i - tzRMu A Bb c.PB i * c.Pj),
   fun i l => if l < i then clipZ (-c.Bh) c.Bh (X.2 i l - tzRLow A Y Bb c.PB c.P2 i l * c.Pj)
     else if l = i then clipZ c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj)
     else 0)

/-! ## The core of a stage -/

/-- Draw `t` of the stage coins `x`: the numerators of `triDrawQ d B x t` over `2^{2 gsm_prec B}`. -/
def tzY (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : Fin d → ℤ := fun i =>
  (gsSpec B (BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat
    (BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat).1

/-! ## The stages -/

/-- A stage position in integers: `(μ̂, T̂) / D`. -/
structure StZ (d : ℕ) where
  D : ℤ
  mu : Fin d → ℤ
  T : Matrix (Fin d) (Fin d) ℤ

/-- `pgComp` at the grids: `P = (μ̂, T̂)/D` and the core output `S/2^{G_c}` give `(μ̂ 2^{G_c} + T̂ Ŝ_μ, T̂ Ŝ_T)/(D 2^{G_c})`. -/
def tzComp (P : StZ d) (S : PosZ d) (Gc : ℕ) : StZ d :=
  ⟨P.D * 2 ^ Gc, fun i => P.mu i * 2 ^ Gc + (P.T *ᵥ S.1) i, P.T * S.2⟩

end AdversarialBco.Bit.TriM
