/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-!
# BL's projection calls on the machine: two frozen contracts

BL calls its projection routine twice per round (R11 TEST, R14 LINE of `step`, Bit/BLPure.lean) through `EllRule`
(Bit/RoutM.lean), on the integer problem `clearQ D` of the call `D = callOf cfg H g ℓ r P f e`. `EllRule` asks for
the inputs of the block (`EllIn`) and for a row command (`RowProv`). This file freezes both as contracts that a
command must meet, so that each can be written apart from the round:

* `RowBL`: the row command. Run with the row index `i` in the register `rE` of the block, it writes row `i` of
  `clearQ D`, that is the `i`-th kept row of the input (P3, `keptIdx`)
  in the position's coordinates, `α̃_i = A_Sᵀ a_i` and `(1 - ε') β̃_i`, `β̃_i = b_i - a_i·μ_S`, each multiplied by the
  product `rowDen` of the reduced denominators of the row (`clr`). It reads the input cells (the rows of `A`, `b`)
  and the cells of `RowCtx` (BL's persistent cells that hold `d`, `m`, `m̃`, `2^pF`, `ε̂`, the position).
* `CallPrepBL`: the preparation of a call. From `H, g, ℓ, r, P, f, e` given as integer pairs `(num, den)`, `den > 0`
  (`PrepIn`), it writes the inputs of the block (`EllIn blkBL (clearQ D)`): the reduced numerators and denominators,
  the products `D_H`, `D_P`, `D_f` and the cleared integers, `R = R_int`.

**BL's layout beyond `BLInv`** (`BLInv` fixes the persistent cells: registers `0..7`, slots `0..25`, arrays `0..7`):

* the inputs of the block `blkBL`: slots `80..87` (`ℓ`, `D_f`, `R`, `r`, `e` as numerator and denominator), arrays
  `8..11` (`H`, `g`, `P`, `f`); the block itself from the slot `768`, the register `64`, the array `32`;
* the row command's own cells (`SRow`, `NRow`, `ARow`): slots `96..255`, registers `32..63`, arrays `12..15`;
* the inputs of the preparation (`PrepIn`): arrays `16..23` (`H`, `g`, `P`, `f`, numerators then denominators),
  slots `64..69` (`ℓ`, `r`, `e`); its own cells: the inputs of the block and the row command's cells.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## The layout of the calls -/

/-- The slots of `ℓ`, `D_f`, `R`, `r`, `e` (numerator and denominator) and the arrays of `H`, `g`, `P`, `f` of the
block. -/
abbrev sEl : ℕ := 80
abbrev aEH : ℕ := 8
abbrev aEg : ℕ := 9
abbrev aEP : ℕ := 10
abbrev aEf : ℕ := 11

/-- The bases of the block of the projection routine. -/
abbrev oE : ℕ := 768
abbrev rEE : ℕ := 64
abbrev aWE : ℕ := 32

/-- The block of BL's projection calls (`EllBlk`, Bit/RoutM.lean): `d` in the register `rD`, the number of kept rows
in `rMk`. -/
def blkBL : EllBlk :=
  { rd := rD, rm := rMk, sl := sEl, sDf := sEl + 1, sRn := sEl + 2, sRd := sEl + 3, srn := sEl + 4, srd := sEl + 5,
    sen := sEl + 6, sed := sEl + 7, aH := aEH, ag := aEg, aP := aEP, af := aEf, o := oE, rE := rEE, aW := aWE }

/-- The row command's own slots, registers and arrays. -/
def SRow (y : ℕ) : Prop := 96 ≤ y ∧ y < 256
def NRow (j : ℕ) : Prop := 32 ≤ j ∧ j < 64
def ARow (a : ℕ) : Prop := 12 ≤ a ∧ a < 16

/-- BL's layout: room for its cells below the bases of the block and for the block's cells that the row command and
the routine's output use (the slots `o, o + 1, o + 2`, the register `rE`, the arrays `aW, aW + 1`). -/
def BLLay (L : Layout) : Prop := oE + 3 ≤ L.NS ∧ rEE + 1 ≤ L.NN ∧ aWE + 2 ≤ L.NA

/-! ## The rows -/

/-- What the row command reads besides the input cells: `d`, `m`, `m̃`, `1`, `pF` in registers, `0`, `2^pF`, `ε̂`
in slots, the position (`PosRep`), every one an integer of absolute value at most `2^E`. -/
structure RowCtx (L : Layout) (m E : ℕ) (cfg : Cfg d) (σ : Env d) : Prop where
  lay : BLLay L
  regs : σ.nat rD = d ∧ σ.nat rM = m ∧ σ.nat rMk = cfg.m ∧ σ.nat rOne = 1 ∧ σ.nat rPF = cfg.par.pF
  consts : σ.sc sZ = 0 ∧ σ.sc s2pF = 2 ^ cfg.par.pF ∧ σ.sc sEps = qn cfg.par.pF cfg.par.eps
  pos : PosRep σ cfg.μS cfg.AS
  bnd : (∀ y ∈ [s2pF, sEps, sDS], ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ E) ∧
    ∀ a ∈ [aMuS, aAS], ∀ k < asz d, ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E

/-- **The row-provider contract (frozen).** One command `xrow L` is a row command (`RowProv`) for every call of BL:
for every input `(A, b)` of height `M`, every frame centre `c` and position `S` (`cfg = mkCfg d n m A b c S`, so its
rows are the kept rows of the input in the position's coordinates), every call data `H, g, ℓ, r, P, f, e`, in every
environment where `RowCtx` holds, with its own cells `SRow`, `NRow`, `ARow`. Work term `W = d + m + size M + E + 1`:
within `C W^k` units, under `C W^k ≤ ℓ` and `C W^k < 2^ℓa`. `ε'` is on the grid `2^{-pF}` and `0 ≤ ε' ≤ 1` (BL's
parameter, `OnG`), so `ε̂ = 2^pF ε'`. -/
def RowBL : Prop :=
  ∃ (xrow : Layout → XCmd) (C k : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M E ℓa ℓ : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
      (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ)
      (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ),
      1 ≤ d → LayOK L d ℓa → RealRAM.HeightLE A b M →
      OnG (par d n).pF (par d n).eps → 0 ≤ (par d n).eps → (par d n).eps ≤ 1 →
      C * (d + m + M.size + E + 1) ^ k ≤ ℓ → C * (d + m + M.size + E + 1) ^ k < 2 ^ ℓa →
      RowProv L (ctxOf w n m A b) ℓa ℓ (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)) blkBL (xrow L)
        (RowCtx L m E (mkCfg d n m A b c S)) SRow NRow ARow (C * (d + m + M.size + E + 1) ^ k)

/-! ## The preparation of a call -/

/-- The arrays of the pairs of `H`, `g`, `P`, `f` (numerators, then denominators) and the slots of the pairs of `ℓ`,
`r`, `e`. -/
abbrev aPHn : ℕ := 16
abbrev aPHd : ℕ := 17
abbrev aPgn : ℕ := 18
abbrev aPgd : ℕ := 19
abbrev aPPn : ℕ := 20
abbrev aPPd : ℕ := 21
abbrev aPfn : ℕ := 22
abbrev aPfd : ℕ := 23
abbrev sPl : ℕ := 64

/-- The rational `x` as a pair of integers `u/v`, `v > 0`, both of absolute value at most `2^s`, in the cell `k` of
the arrays `an`, `ad`. -/
def PairA (σ : Env d) (an ad k s : ℕ) (x : ℚ) : Prop :=
  ∃ u v : ℤ, 0 < v ∧ |u| ≤ 2 ^ s ∧ v ≤ 2 ^ s ∧ σ.arr an k = u ∧ σ.arr ad k = v ∧ (u : ℚ) / v = x

/-- The rational `x` as a pair of integers in the slots `yn`, `yd`. -/
def PairS (σ : Env d) (yn yd s : ℕ) (x : ℚ) : Prop :=
  ∃ u v : ℤ, 0 < v ∧ |u| ≤ 2 ^ s ∧ v ≤ 2 ^ s ∧ σ.sc yn = u ∧ σ.sc yd = v ∧ (u : ℚ) / v = x

/-- The inputs of the preparation: `d`, `m̃`, `R_int`, `0` in their cells of `BLInv`, the call data as pairs below
`2^s` (matrices in the cells `d i + j`). -/
def PrepIn (σ : Env d) (cfg : Cfg d) (s : ℕ) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) : Prop :=
  σ.nat rD = d ∧ σ.nat rMk = cfg.m ∧ σ.nat rOne = 1 ∧ σ.sc sZ = 0 ∧ σ.sc sRint = cfg.par.Rint ∧
    (cfg.par.Rint : ℤ) ≤ 2 ^ s ∧
    (∀ i j : Fin d, PairA σ aPHn aPHd (d * i + j) s (H i j)) ∧ (∀ j : Fin d, PairA σ aPgn aPgd j s (g j)) ∧
    (∀ i j : Fin d, PairA σ aPPn aPPd (d * i + j) s (P i j)) ∧ (∀ j : Fin d, PairA σ aPfn aPfd j s (f j)) ∧
    PairS σ sPl (sPl + 1) s ℓq ∧ PairS σ (sPl + 2) (sPl + 3) s r ∧ PairS σ (sPl + 4) (sPl + 5) s e

/-- The preparation's own cells: the inputs of the block and the row command's cells. -/
def SPrep (y : ℕ) : Prop := (sEl ≤ y ∧ y < sEl + 8) ∨ SRow y
def NPrep (j : ℕ) : Prop := NRow j
def APrep (a : ℕ) : Prop := (aEH ≤ a ∧ a ≤ aEf) ∨ ARow a

/-- **The call-preparation contract (frozen).** One command `xprep L` writes the inputs of the block of the call
`callOf cfg H g ℓ r P f e` (all but the rows) from the call data as pairs (`PrepIn`), for every configuration `cfg`.
Work term `W = d + s + 1`: within `C W^k` units, under `C W^k ≤ ℓ` and `C W^k < 2^ℓa`. It reads no coin and changes
only its own cells. -/
def CallPrepBL : Prop :=
  ∃ (xprep : Layout → XCmd) (C k : ℕ),
    ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ s : ℕ) (cfg : Cfg d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ)
      (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (σ : Env d),
      1 ≤ d → LayOK L d ℓa → BLLay L → PrepIn σ cfg s H g ℓq r P f e →
      C * (d + s + 1) ^ k ≤ ℓ → C * (d + s + 1) ^ k < 2 ^ ℓa →
      XRunsB L X ℓa ℓ (xprep L) σ (C * (d + s + 1) ^ k) (fun σ' =>
        EllIn blkBL (clearQ (callOf cfg H g ℓq r P f e)) σ' ∧ σ'.draws = σ.draws ∧
        FrameA SPrep NPrep (fun a _ => APrep a) σ σ')

/-! ## The contracts fit `EllRule` -/

theorem blkBL_avoid : blkBL.Avoid SRow NRow ARow := by
  simp only [EllBlk.Avoid, blkBL, SRow, NRow, ARow, rD, rMk, sEl, aEH, aEg, aEP, aEf]
  omega

theorem blkBL_ok {L : Layout} {nS nN nA : ℕ} (hS : oE + nS ≤ L.NS) (hN : rEE + nN ≤ L.NN) (hA : aWE + nA ≤ L.NA) :
    blkBL.OK L nS nN nA := by
  simp only [EllBlk.OK, blkBL, rD, rMk, sEl, aEH, aEg, aEP, aEf, oE, rEE, aWE] at *
  omega

end AdversarialBco.Bit.Transfer.BLM
