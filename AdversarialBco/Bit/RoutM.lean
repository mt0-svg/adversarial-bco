/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.Transfer.XDriver
public import AdversarialBco.Bit.Transfer.XEllRow

@[expose] public section

/-!
# Interface II: BL's routines on the machine, as `Prop`s (frozen)

Each rule says that one fixed command, the same for every dimension `d` (the program of the frozen statement is chosen
before `d`), computes on the machine the pure function of Interface I (Bit/RoutQ.lean) that BL's program calls:

* `EllRule`: the projection routine `ellRI` (ELL-R for `d ≥ 2`, BIS-R for `d = 1`) on the integer problem `EllI d`,
  with the rows supplied on demand by a command of the caller (`RowProv`): an environment holds `d² + d` cells per array
  and a fixed number of arrays, so nothing of size `m` is stored.
* `FrameRule`: the frame centre `frameQ`, from the input rows (the input cells of `ctxOf`).
* `TriRule`: the position `posQ` (TRI-OGD staged), from the input rows, the frame centre and the coins.

**Work terms.** Each rule is `∃` a command, a constant `C`, an exponent `k` and the numbers of slots, registers and
arrays the command uses above the bases of its block. For a work parameter `W` (below), the command runs within
`C * W ^ k` units of the extended language, with every value below `2^ℓ` as soon as `C * W ^ k ≤ ℓ` and every register
below `2^ℓa` as soon as `C * W ^ k < 2 ^ ℓa`. A unit costs at most
`xstepCost ℓa ℓ = 40 + 12 ℓa + 4 ℓ + (ℓa + ℓ + 1)²` bit operations (`xtransfer`), so the machine-side totals of
`hBc` and `hBs` (`prog_ok_frozenR`) are sums of these terms:

* `EllRule`: `W = d + m + ellSz I + Kr + 1` for the units (`Kr` the units of one row call), `W = d + m + ellSz I + 1`
  for the magnitudes and the registers; `ellSz I` is the bit length of the largest integer of the problem.
* `FrameRule`: `W = d + m + size M̂ + 1`, `M̂ = frMhat A b`.
* `TriRule`: `W = d + m + size n + size M̂ + s + 1`, `s` the bit length of the frame centre it is given.

**Blocks.** A routine writes the slots from `o`, the registers from `rE` and the arrays from `aW` (its block), and
reads its inputs below these bases. Its outputs are at fixed places of its block. A register holds only numbers
polynomial in `d`, `m` and the bit lengths of the data (`2^ℓa` is polynomial in them under the space bound `hBs`), so
the horizon `n` comes in a slot.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ

/-! ## The projection routine -/

/-- The largest absolute value among the integers of the problem, with the numerators and denominators of `R`, `r`,
`e`. -/
def ellMx {d : ℕ} (I : EllI d) : ℕ :=
  max (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs)
    (max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
      (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))))

/-- The bit length of the largest integer of the problem (`σ`). -/
def ellSz {d : ℕ} (I : EllI d) : ℕ := (ellMx I).size

/-- The block of the projection routine. Inputs below the bases: the registers `rd` (`d`) and `rm` (`m`); the slots
`sl` (`ℓ`), `sDf` (`D_f`), `sRn, sRd`, `srn, srd`, `sen, sed` (the reduced numerators and denominators of `R`, `r`,
`e`); the arrays `aH`, `aP` (`d × d`, entry `(i, j)` in cell `d i + j`), `ag`, `af`. The routine's own: the slots from
`o`, the registers from `rE`, the arrays from `aW`. -/
structure EllBlk where
  rd : ℕ
  rm : ℕ
  sl : ℕ
  sDf : ℕ
  sRn : ℕ
  sRd : ℕ
  srn : ℕ
  srd : ℕ
  sen : ℕ
  sed : ℕ
  aH : ℕ
  ag : ℕ
  aP : ℕ
  af : ℕ
  o : ℕ
  rE : ℕ
  aW : ℕ

/-- The block lies in the layout, with `nS` slots, `nN` registers and `nA` arrays above its bases, and the inputs
below the bases. -/
def EllBlk.OK (L : Layout) (nS nN nA : ℕ) (B : EllBlk) : Prop :=
  B.o + nS ≤ L.NS ∧ B.rE + nN ≤ L.NN ∧ B.aW + nA ≤ L.NA ∧
  B.rd < B.rE ∧ B.rm < B.rE ∧
  B.sl < B.o ∧ B.sDf < B.o ∧ B.sRn < B.o ∧ B.sRd < B.o ∧ B.srn < B.o ∧ B.srd < B.o ∧ B.sen < B.o ∧ B.sed < B.o ∧
  B.aH < B.aW ∧ B.ag < B.aW ∧ B.aP < B.aW ∧ B.af < B.aW

/-- The row command's own cells `SR`, `NR`, `AR` avoid the inputs of the block. -/
def EllBlk.Avoid (B : EllBlk) (SR NR AR : ℕ → Prop) : Prop :=
  ¬ NR B.rd ∧ ¬ NR B.rm ∧ ¬ SR B.sl ∧ ¬ SR B.sDf ∧ ¬ SR B.sRn ∧ ¬ SR B.sRd ∧ ¬ SR B.srn ∧ ¬ SR B.srd ∧ ¬ SR B.sen ∧
    ¬ SR B.sed ∧ ¬ AR B.aH ∧ ¬ AR B.ag ∧ ¬ AR B.aP ∧ ¬ AR B.af

/-- The inputs of the projection routine hold the problem `I` (the rows excepted). -/
def EllIn {d : ℕ} (B : EllBlk) (I : EllI d) (σ : Env d) : Prop :=
  σ.nat B.rd = d ∧ σ.nat B.rm = I.m ∧ σ.sc B.sl = I.ℓ ∧ σ.sc B.sDf = I.Df ∧
  σ.sc B.sRn = I.R.num ∧ σ.sc B.sRd = I.R.den ∧ σ.sc B.srn = I.r.num ∧ σ.sc B.srd = I.r.den ∧
  σ.sc B.sen = I.e.num ∧ σ.sc B.sed = I.e.den ∧
  (∀ i j : Fin d, σ.arr B.aH (d * i + j) = I.H i j) ∧ (∀ j : Fin d, σ.arr B.ag j = I.g j) ∧
  (∀ i j : Fin d, σ.arr B.aP (d * i + j) = I.P i j) ∧ (∀ j : Fin d, σ.arr B.af j = I.f j)

/-- The rows on demand: the command `rowc`, run where `Ctx` holds and the register `rE` holds `i < m`, writes row `i`
of `I` (`α_i` into the cells `0, ..., d - 1` of the array `aW + 1`, `β_i` into the slot `o + 2`) within `Kr` units,
reading no coin, and changes nothing else but its own slots `SR`, registers `NR` and arrays `AR`, all below the bases of
the block. -/
def RowProv {d : ℕ} (L : Layout) (X : XCtx d) (ℓa ℓ : ℕ) (I : EllI d) (B : EllBlk) (rowc : XCmd)
    (Ctx : Env d → Prop) (SR NR AR : ℕ → Prop) (Kr : ℕ) : Prop :=
  (∀ y, SR y → y < B.o) ∧ (∀ j, NR j → j < B.rE) ∧ (∀ b, AR b → b < B.aW) ∧
  ∀ σ : Env d, Ctx σ → ∀ h : σ.nat B.rE < I.m, XRunsB L X ℓa ℓ rowc σ Kr (fun σ' =>
    (∀ j : Fin d, σ'.arr (B.aW + 1) j = I.α ⟨σ.nat B.rE, h⟩ j) ∧ σ'.sc (B.o + 2) = I.β ⟨σ.nat B.rE, h⟩ ∧
    σ'.draws = σ.draws ∧
    FrameA (fun y => y = B.o + 2 ∨ SR y) NR (fun b _ => b = B.aW + 1 ∨ AR b) σ σ')

/-- `Ctx` survives every change of the routine's block and of the row command's own cells. -/
def CtxOK {d : ℕ} (B : EllBlk) (Ctx : Env d → Prop) (SR NR AR : ℕ → Prop) : Prop :=
  ∀ σ σ' : Env d, Ctx σ → σ'.draws = σ.draws →
    FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ' → Ctx σ'

/-- The output of the projection routine: the slot `o` holds `0` on a failure; on a point `x / 2^e`, it holds `1`, the
slot `o + 1` holds `e` and the cells `0, ..., d - 1` of the array `aW` hold `x`. -/
def EllOut {d : ℕ} (B : EllBlk) (r : Option (Fin d → ℤ)) (e : ℕ) (σ : Env d) : Prop :=
  match r with
  | none => σ.sc B.o = 0
  | some x => σ.sc B.o = 1 ∧ σ.sc (B.o + 1) = e ∧ ∀ j : Fin d, σ.arr B.aW j = x j

/-- **Interface II, the projection routine.** One command `xell L B rowc` computes `ellRI I`, the point over
`2^(ellExp I)`, for every `d ≥ 1`, every problem `I` and every row command `rowc` for `I`. Work term: within
`C * (d + m + ellSz I + Kr + 1) ^ k` units, under `C * (d + m + ellSz I + 1) ^ k ≤ ℓ` (magnitudes) and
`C * (d + m + ellSz I + 1) ^ k < 2 ^ ℓa` (registers). It reads no coin and changes only its block and the row
command's own cells. -/
def EllRule : Prop :=
  ∃ (xell : Layout → EllBlk → XCmd → XCmd) (C k nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ : ℕ) (B : EllBlk) (I : EllI d) (rowc : XCmd)
      (Ctx : Env d → Prop) (SR NR AR : ℕ → Prop) (Kr : ℕ) (σ : Env d),
      1 ≤ d → LayOK L d ℓa → B.OK L nS nN nA → B.Avoid SR NR AR →
      RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr → CtxOK B Ctx SR NR AR →
      EllIn B I σ → Ctx σ →
      C * (d + I.m + ellSz I + 1) ^ k ≤ ℓ → C * (d + I.m + ellSz I + 1) ^ k < 2 ^ ℓa →
      XRunsB L X ℓa ℓ (xell L B rowc) σ (C * (d + I.m + ellSz I + Kr + 1) ^ k) (fun σ' =>
        EllOut B (ellRI I) (ellExp I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ')

/-! ## The frame centre and the position -/

/-- The block of a prologue routine: the input registers `rd` (`d`), `rm` (`m`); the input slot `sn` (`n`: a register
holds only numbers polynomial in `d`, `m` and the bit lengths, `n` is not one); an input array `aC` (TRI-OGD's frame
centre); the routine's own slots from `o`, registers from `rE`, arrays from `aW`. -/
structure PrBlk where
  rd : ℕ
  rm : ℕ
  sn : ℕ
  aC : ℕ
  o : ℕ
  rE : ℕ
  aW : ℕ

/-- The block lies in the layout, with `nS` slots, `nN` registers and `nA` arrays above its bases, and the inputs below
the bases. -/
def PrBlk.OK (L : Layout) (nS nN nA : ℕ) (B : PrBlk) : Prop :=
  B.o + nS ≤ L.NS ∧ B.rE + nN ≤ L.NN ∧ B.aW + nA ≤ L.NA ∧ B.rd < B.rE ∧ B.rm < B.rE ∧ B.sn < B.o ∧ B.aC < B.aW

/-- A point `c` in the array `a` as the play leaf reads it: a positive denominator `D` in cell `0`, the numerators in
cells `1, ..., d`, all integers of absolute value below `2^s`. -/
def PtIn {d : ℕ} (σ : Env d) (a s : ℕ) (c : Fin d → ℚ) : Prop :=
  ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ σ.arr a 0 = D ∧
    ∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ σ.arr a (j + 1) = x ∧ (x : ℚ) / D = c j

/-- A position `(μ, A)`: a positive common denominator `D` in the slot `o`, the numerators of `μ` in the cells
`0, ..., d - 1` of the array `a` and those of `A` in the cells `d i + j` of the array `a + 1`, all integers of absolute
value below `2^s`. -/
def PosIn {d : ℕ} (σ : Env d) (o a s : ℕ) (S : PosQ d) : Prop :=
  ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ σ.sc o = D ∧
    (∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ σ.arr a j = x ∧ (x : ℚ) / D = S.1 j) ∧
    ∀ i j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ σ.arr (a + 1) (d * i + j) = x ∧ (x : ℚ) / D = S.2 i j

/-- **Interface II, the frame centre.** One command `xframe L B` computes `frameQ d n m A b` from the input rows (the
input cells of `ctxOf`), into the array `aW` in the form of the play leaf, its integers below `2^(C W^k)`. Work term:
`W = d + m + size M̂ + 1`, `M̂ = frMhat A b`; within `C * W ^ k` units, under `C * W ^ k ≤ ℓ` and `C * W ^ k < 2 ^ ℓa`.
It reads no coin and changes only its block. -/
def FrameRule : Prop :=
  ∃ (xframe : Layout → PrBlk → XCmd) (C k nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
      (ℓa ℓ : ℕ) (B : PrBlk) (σ : Env d),
      1 ≤ d → LayOK L d ℓa → B.OK L nS nN nA → σ.nat B.rd = d → σ.nat B.rm = m →
      C * (d + m + (frMhat A b).size + 1) ^ k ≤ ℓ → C * (d + m + (frMhat A b).size + 1) ^ k < 2 ^ ℓa →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xframe L B) σ (C * (d + m + (frMhat A b).size + 1) ^ k) (fun σ' =>
        PtIn σ' B.aW (C * (d + m + (frMhat A b).size + 1) ^ k) (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ')

/-- **Interface II, the position.** One command `xtri L B` computes `posQ d n m A b` on the coins `cs (draws + k)`,
`k < K0Q d n`, from the input rows, `n` in the slot `sn` and the frame centre in the array `aC` (in the form of the
play leaf, integers below `2^s`), into the slot `o` and the arrays `aW`, `aW + 1` (`PosIn`), its integers below
`2^(C W^k)`, and reads exactly `K0Q d n` coins. Work term: `W = d + m + size n + size M̂ + s + 1`; within `C * W ^ k`
units, under `C * W ^ k ≤ ℓ` and `C * W ^ k < 2 ^ ℓa`. It changes only its block and the count of draws. -/
def TriRule : Prop :=
  ∃ (xtri : Layout → PrBlk → XCmd) (C k nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
      (ℓa ℓ s : ℕ) (B : PrBlk) (σ : Env d),
      1 ≤ d → 1 ≤ n → LayOK L d ℓa → B.OK L nS nN nA → σ.nat B.rd = d → σ.nat B.rm = m →
      σ.sc B.sn = n → PtIn σ B.aC s (frameQ d n m A b) →
      C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k ≤ ℓ →
      C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k < 2 ^ ℓa →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xtri L B) σ (C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k)
        (fun σ' =>
          PosIn σ' B.o B.aW (C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k)
            (posQ d n m A b fun j => w.cs (σ.draws + j)) ∧
          σ'.draws = σ.draws + K0Q d n ∧
          FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ')

end AdversarialBco.Bit.Transfer
