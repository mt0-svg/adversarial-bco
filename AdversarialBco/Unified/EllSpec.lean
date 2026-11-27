/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepSpec
public import AdversarialBco.Bit.RoutQ

@[expose] public section

/-!
# UNI-ELL: Procedures ELL-O and BIS-O and the contract of their block (the interface)

UNI-ELL (the paper's appendix on rational ellipsoid methods). The interface that the program (UNI-PROG) calls; the
proofs are in the modules EllO*.lean; this file
has the definitions and the statements, as `Prop`s.

**The procedures as pure functions** (computable, on `ℤ` and `ℚ`). ELL-O is ELL-R of Bit/RoutQ.lean (`ellTest`,
`ellUpd`, `ellLoop`) with step 2 (the rows) replaced by a membership test `T` and a SEP cut; BIS-O is BIS-R with the same
tests. The call `EllOI d` is the integer problem of ELL-R without rows (the quadratic constraint `Ψ(y) ≤ ℓ`, the
objective `G`, the radius `R`, the radius `r` (the ball of (HQ-O) has radius `2r`), the accuracy `e`), and the data of
the K-part `QK` of the region: a centre `c = Nc/Dc` with `B̄(c, 2^{-erK}) ⊆ QK`.

* `EllOI.base`: the integer problem of ELL-R with no rows and the radius `r`. Its constants `j`, `λ`, `N`, `p`, `q`, `Λ`
  are those of ELL-O: `ρ = 2^{-j} ≤ θ min(r, 1)`, and the ball of (HQ-O) has radius `2r`, so the ball `B' = B̄(p_θ, ρ)`
  of the proof has its `ρ`-neighbourhood `B̄(p_θ, 2ρ) ⊆ B̄(p_θ, 2θr)` in the region (m3: the ball of (HQ-O) has twice
  the radius for which `j` is computed). The block passes `r` to the constants of ELL-R unchanged.
* Step 2 at the centre `a/2^s`: `T (a/2^s)`; on a reject, SEP (`sepE` of SepSpec.lean) on the grid `2^{-E}`,
  `E = s + e₁ + d(2(eL + eτ + 3) + 6 + eτ + eL)`, from `Y₀ = 2^{E-s} a`, with the values of the bisection gauge of
  UNI-GAUGE (`gaugeIt T c x 2^{eH} jg`, the counter `u`, the value `u/2^{eu}`); the cut vector is SEP's integer `G`
  (`g = G/2^{eu+1}`, the same direction), the cut `0` (the kept point is returned) when SEP fails.
* The gauge is that of the K-part about the known centre `c`, not that of the whole region about the unknown centre
  of its ball: the cut keeps every point of depth `ρ` in `QK`, in particular `B'` (EllOCut.lean).

**The constants of step 2** (exponents of `2`): `M = 2^{eM} ≥ 4R̄` bounds the distances; `L = 2^{eL}`, `eL = erK`,
the Lipschitz constant of the gauge; `ℓ₁ = 2^{-e₁}`, `τ = 2^{-eτ}`; `H = 2^{eH} ≥ 4R̄ 2^{erK}` bounds the gauge on
SEP's points; `η_min ≥ 2^{-eη}`; `jg = eη + eH + 1` steps of the gauge; the band of the test must be at most
`2^{-eK}`, `eK = eη + eH + 2` (`EllOAcc`).

**The mathematics** (`Prop`s): `EllOCert` (statement (a): a point returned passed the test `T`, the quadratic test and
the ball test, at the scale of its denominator); `EllOAcc` (statement (b), (HQ-O): under `B̄(a₀, 2r) ⊆ QK ∩ region`, a
test certifying `QK` about `c` with a band at most `2^{-eK}`, `P ≻ 0`, `H ⪰ 0`, the point returned is within `e` of
the minimum of `G` on `QK ∩ region`).

**The block** (`EllOBlockOK`, `EllORule`): the code computes `ellOI I (T k)`, `k = eK + κ`, for every test block `TB`
that answers `T k` when the precision register holds `k`; work term `W = d + ellOSz I + κ + 1`, units
`C (W + Kt)^k₀`.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.RQ (EllI Cut ESt ellUpd ellTest)
open Matrix

variable {d : ℕ}

/-! ## The call -/

/-- A call of ELL-O: the quadratic constraint `yᵀHy/2 - g·y ≤ ℓ`, the objective `yᵀPy/2 - (f/D_f)·y`, the radius `R`
(`|y| ≤ R`), the radius `r` of a ball in the region, the accuracy `e`; the centre `c = Nc/Dc` of the K-part's gauge and
the exponent `erK` of its inner radius. -/
structure EllOI (d : ℕ) where
  H : Matrix (Fin d) (Fin d) ℤ
  g : Fin d → ℤ
  ℓ : ℤ
  P : Matrix (Fin d) (Fin d) ℤ
  f : Fin d → ℤ
  Df : ℕ
  R : ℚ
  r : ℚ
  e : ℚ
  Dc : ℤ
  Nc : Fin d → ℤ
  erK : ℕ

namespace EllOI

variable (I : EllOI d)

/-- The integer problem of ELL-R with no rows and the radius `r` (the ball of (HQ-O) has radius `2r`, m3). -/
def base : EllI d :=
  ⟨0, Fin.elim0, Fin.elim0, I.H, I.g, I.ℓ, I.P, I.f, I.Df, I.R, I.r, I.e⟩

/-- The centre `c` of the K-part's gauge. -/
def c : Fin d → ℚ := ptDN I.Dc I.Nc

/-- `M = 2^{eM} ≥ 4 R̄`. -/
def eM : ℕ := Nat.clog 2 I.base.Rb + 2

/-- `L = 2^{eL}`, the Lipschitz constant of the K-part's gauge: `eL = erK`. -/
def eL : ℕ := I.erK

/-- `ℓ₁ = 2^{-e₁}`. -/
def e1 : ℕ := I.base.j + I.eM + I.erK + 5

/-- `τ = 2^{-eτ}`. -/
def eτ : ℕ := I.base.j + 2 * I.eM + Nat.clog 2 d + 4

/-- `H = 2^{eH}`, the upper end of the gauge's bisection. -/
def eH : ℕ := I.eM + I.erK

/-- `η_min = (τ ℓ₁/1600) 2^{-3d(J+1)} ≥ 2^{-eη}`, `J + 1 = eL + eτ + 4`. -/
def eη : ℕ := I.eτ + I.e1 + 11 + 3 * d * (I.eL + I.eτ + 4)

/-- The steps of the gauge's bisection. -/
def jg : ℕ := I.eη + I.eH + 1

/-- The scale of SEP's values: the value of the counter `u` is `u/2^{eu}`, `eu = jg - eH`. -/
def eu : ℕ := I.eη + 1

/-- The band of the test must be at most `2^{-eK}`. -/
def eK : ℕ := I.eη + I.eH + 2

/-- SEP's grid exponent at the scale `2^s` of the centre. -/
def sepEx (s : ℕ) : ℕ := s + I.e1 + d * (2 * (I.eL + I.eτ + 3) + 6 + I.eτ + I.eL)

/-- SEP's evaluator on the grid `2^{-E}` for the test `T`: the counter of `jg` steps of the gauge of `T` about `c` at
`X/2^E`, on `[0, 2^{eH}]`. -/
def evO (T : (Fin d → ℚ) → Bool) (E : ℕ) (X : Fin d → ℤ) : ℤ :=
  ((gaugeIt T I.c (ptDN (2 ^ E) X) ((2 : ℚ) ^ I.eH) I.jg I.jg).2 : ℤ)

end EllOI

/-! ## Procedures ELL-O and BIS-O -/

/-- Steps 1 to 4 of ELL-O at the scale `2^s`: step 1 (the ball) as ELL-R; step 2 the test `T` at `a/2^s`, on a reject
the SEP cut (the cut `0` when SEP fails); on an accept, `ellTest` of the rowless problem (step 1 again, no row, steps 3
and 4). -/
def ellTestO (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ)) :
    Cut d :=
  if 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2 then .cut a kept
  else if T (ptDN (2 ^ s) a) then ellTest I.base s a kept
  else
    match sepE (I.evO T (I.sepEx s)) ((2 : ℤ) ^ (I.sepEx s - s) • a) (I.sepEx s) I.e1 I.eτ I.eL I.eu with
    | none => .cut 0 kept
    | some (_, G) => .cut G kept

/-- The iterations of ELL-O, `k` of them left (ELL-R's `ellLoop` with `ellTestO`). -/
def ellLoopO (I : EllOI d) (T : (Fin d → ℚ) → Bool) : ℕ → ESt d → Option (Fin d → ℤ)
  | 0, st => st.kept.map Prod.fst
  | k + 1, st =>
    match ellTestO I T I.base.p st.a st.kept with
    | .ret x => some x
    | .cut c kept =>
      if c = 0 then kept.map Prod.fst else
      match ellUpd I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
          ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) st.A st.a c with
      | none => kept.map Prod.fst
      | some (A', a') => ellLoopO I T k ⟨A', a', kept⟩

/-- Procedure ELL-O (`d ≥ 2`): from `Â = 2^p R̄² I`, `â = 0`, `N` iterations; the point `â/2^p`. -/
def ellO (I : EllOI d) (T : (Fin d → ℚ) → Bool) : Option (Fin d → ℤ) :=
  ellLoopO I T I.base.N ⟨((2 : ℤ) ^ I.base.p * I.base.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩

/-- The iterations of BIS-O on `[lo, hi]` (integers over `2^{λ+1}`), `k` of them left. -/
def bisLoopO (I : EllOI d) (T : (Fin d → ℚ) → Bool) : ℕ → ℤ → ℤ → Option ((Fin d → ℤ) × ℤ) → Option (Fin d → ℤ)
  | 0, _, _, kept => kept.map Prod.fst
  | k + 1, lo, hi, kept =>
    let a : ℤ := (lo + hi) / 2
    match ellTestO I T (I.base.lam + 1) (fun _ => a) kept with
    | .ret x => some x
    | .cut c kept' =>
      if c = 0 then kept'.map Prod.fst else
      if 0 < ∑ i, c i then bisLoopO I T k lo a kept' else bisLoopO I T k a hi kept'

/-- Procedure BIS-O (`d = 1`): `λ + 1` halvings of `[-R̄, R̄]`; the point over `2^{λ+1}`. -/
def bisO (I : EllOI d) (T : (Fin d → ℚ) → Bool) : Option (Fin d → ℤ) :=
  bisLoopO I T (I.base.lam + 1) (-((I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1))) ((I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1))
    none

/-- The exponent of the denominator of the returned point: `λ + 1` for `d = 1`, `p` otherwise. -/
def ellExpO (I : EllOI d) : ℕ := if d = 1 then I.base.lam + 1 else I.base.p

/-- ELL-O/BIS-O: fail at once if `R < 1`, `r ≤ 0`, `e ≤ 0` or `d = 0`; BIS-O for `d = 1`; ELL-O for `d ≥ 2`. The
point is `x/2^(ellExpO I)`. -/
def ellOI (I : EllOI d) (T : (Fin d → ℚ) → Bool) : Option (Fin d → ℤ) :=
  if I.R < 1 ∨ I.r ≤ 0 ∨ I.e ≤ 0 then none else
  if d = 0 then none else
  if d = 1 then bisO I T else ellO I T

/-! ## The mathematics -/

/-- The exact part of the region, `{y | yᵀHy/2 - g·y ≤ ℓ, |y| ≤ R}`. -/
def regionO (I : EllOI d) : Set (Fin d → ℝ) :=
  {y | y ⬝ᵥ (I.H.map ((↑) : ℤ → ℝ) *ᵥ y) / 2 - (fun j => (I.g j : ℝ)) ⬝ᵥ y ≤ I.ℓ ∧ oNorm y ≤ I.R}

/-- The objective `G(y) = yᵀPy/2 - (f/D_f)·y`. -/
noncomputable def GO (I : EllOI d) (y : Fin d → ℝ) : ℝ :=
  y ⬝ᵥ (I.P.map ((↑) : ℤ → ℝ) *ᵥ y) / 2 - (fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ y

/-- **Statement (a).** Every point `x/2^s` returned (`s = ellExpO I`) passed the test `T`, the quadratic test and the
ball test: `T` accepts it and it lies in the exact part of the region. -/
def EllOCert : Prop :=
  ∀ (d : ℕ) (I : EllOI d) (T : (Fin d → ℚ) → Bool) (x : Fin d → ℤ), ellOI I T = some x →
    T (ptDN (2 ^ ellExpO I) x) = true ∧ (fun j => (x j : ℝ) / 2 ^ ellExpO I) ∈ regionO I

/-- **Statement (b), (HQ-O).** `QK` closed and convex, bounded, with `B̄(c, 2^{-erK}) ⊆ QK` and `|c| ≤ R`; the test `T`
certifies `QK` about `c` with a band `η ≤ 2^{-eK}`; `P ≻ 0`, `H ⪰ 0`, `D_f > 0`, `R ≥ 1`, `r > 0`, `e > 0`, `d ≥ 1`;
the region `QK ∩ regionO I` contains `B̄(a₀, 2r)`. Then ELL-O/BIS-O returns a point of the region within `e` of the
minimum of `G` on it. -/
def EllOAcc : Prop :=
  ∀ (d : ℕ) (I : EllOI d) (T : (Fin d → ℚ) → Bool) (QK : Set (Fin d → ℝ)) (RK η : ℝ) (a0 : Fin d → ℝ),
    1 ≤ d → 1 ≤ I.R → 0 < I.r → 0 < I.e → 0 < I.Df →
    (I.P.map ((↑) : ℤ → ℝ)).PosDef → (I.H.map ((↑) : ℤ → ℝ)).PosSemidef →
    Convex ℝ QK → IsClosed QK → QK ⊆ oBall 0 RK → oBall (qR I.c) ((2 : ℝ)⁻¹ ^ I.erK) ⊆ QK →
    oNorm (qR I.c) ≤ I.R → TestCert T QK (qR I.c) η → 0 ≤ η → η ≤ (2 : ℝ)⁻¹ ^ I.eK →
    oBall a0 (2 * (I.r : ℝ)) ⊆ QK ∩ regionO I →
    ∃ x, ellOI I T = some x ∧ (fun j => (x j : ℝ) / 2 ^ ellExpO I) ∈ QK ∩ regionO I ∧
      ∀ y ∈ QK ∩ regionO I, GO I (fun j => (x j : ℝ) / 2 ^ ellExpO I) ≤ GO I y + I.e

/-! ## The block -/

/-- The largest absolute value among the integers of the call. -/
def ellOMx (I : EllOI d) : ℕ :=
  max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
    (max (Finset.univ.sup fun j => max (max (I.g j).natAbs (I.f j).natAbs) (I.Nc j).natAbs)
      (max I.ℓ.natAbs (max I.Df (max I.Dc.natAbs (max (max I.R.num.natAbs I.R.den)
        (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))))

/-- The size of the call: the bit length of its largest integer, plus `erK`. -/
def ellOSz (I : EllOI d) : ℕ := (ellOMx I).size + I.erK

/-- The block of ELL-O. Inputs below the bases: the registers `rd` (`d`), `rK` (`erK`), `rκ` (`κ`, the offset of the
test's band); the slots `sl` (`ℓ`), `sDf` (`D_f`), `sRn, sRd`, `srn, srd`, `sen, sed` (the reduced numerators and
denominators of `R`, `r`, `e`); the arrays `aH`, `aP` (`d × d`, entry `(i, j)` in cell `d i + j`), `ag`, `af` and `ac`
(the centre: `Dc` in cell `0`, `Nc` in cells `1, ..., d`). Its own cells: the slots from `o`, the registers from `rE`,
the arrays from `aW` (as for ELL-R's block; the code uses `nS`, `nN`, `nA` of them, `OK`, and the test block's cells lie
below the bases, `TestAvoid`). Fixed places in its own block: the output (`EllOOut`: the
flag in the slot `o`, the exponent in `o + 1`, the point in the array `aW`); the test's point in the array `aW + 1`
(`(D; N)`, cell `0` the denominator) and its answer in the register `rE`; the test's precision `k` in the register
`rE + 1` and `2^k` in the slot `o + 2`. -/
structure EllOBlk where
  rd : ℕ
  rK : ℕ
  rκ : ℕ
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
  ac : ℕ
  o : ℕ
  rE : ℕ
  aW : ℕ

namespace EllOBlk

variable (B : EllOBlk)

/-- The block lies in the layout, with `nS` slots, `nN` registers and `nA` arrays from its bases, and the inputs below
the bases. -/
def OK (L : Layout) (nS nN nA : ℕ) : Prop :=
  B.o + nS ≤ L.NS ∧ B.rE + nN ≤ L.NN ∧ B.aW + nA ≤ L.NA ∧ 3 ≤ nS ∧ 2 ≤ nN ∧ 2 ≤ nA ∧
  B.rd < B.rE ∧ B.rK < B.rE ∧ B.rκ < B.rE ∧
  B.sl < B.o ∧ B.sDf < B.o ∧ B.sRn < B.o ∧ B.sRd < B.o ∧ B.srn < B.o ∧ B.srd < B.o ∧ B.sen < B.o ∧ B.sed < B.o ∧
  B.aH < B.aW ∧ B.ag < B.aW ∧ B.aP < B.aW ∧ B.af < B.aW ∧ B.ac < B.aW

/-- The block's own slots: every slot from its base `o` (as for ELL-R's block, whose frames are unbounded above). -/
def ownS (y : ℕ) : Prop := B.o ≤ y

/-- The block's own registers: every register from its base `rE`. -/
def ownN (j : ℕ) : Prop := B.rE ≤ j

/-- The block's own arrays: every array from its base `aW`. -/
def ownA (b _k : ℕ) : Prop := B.aW ≤ b

/-- The test block's own cells avoid the inputs and the block's own cells (they lie below the bases), the answer
register `rE` excepted. -/
def TestAvoid (St Nt : ℕ → Prop) (Art : ℕ → ℕ → Prop) : Prop :=
  (∀ y, St y → ¬ B.ownS y ∧ y ≠ B.sl ∧ y ≠ B.sDf ∧ y ≠ B.sRn ∧ y ≠ B.sRd ∧ y ≠ B.srn ∧ y ≠ B.srd ∧
    y ≠ B.sen ∧ y ≠ B.sed) ∧
  (∀ j, Nt j → (¬ B.ownN j ∨ j = B.rE) ∧ j ≠ B.rd ∧ j ≠ B.rK ∧ j ≠ B.rκ) ∧
  (∀ b k, Art b k → ¬ B.ownA b k ∧ b ≠ B.aH ∧ b ≠ B.ag ∧ b ≠ B.aP ∧ b ≠ B.af ∧ b ≠ B.ac)

end EllOBlk

/-- The inputs of the block hold the call `I` and the offset `κ`. -/
def EllOIn (B : EllOBlk) (I : EllOI d) (κ : ℕ) (σ : Env d) : Prop :=
  σ.nat B.rd = d ∧ σ.nat B.rK = I.erK ∧ σ.nat B.rκ = κ ∧ σ.sc B.sl = I.ℓ ∧ σ.sc B.sDf = I.Df ∧
  σ.sc B.sRn = I.R.num ∧ σ.sc B.sRd = I.R.den ∧ σ.sc B.srn = I.r.num ∧ σ.sc B.srd = I.r.den ∧
  σ.sc B.sen = I.e.num ∧ σ.sc B.sed = I.e.den ∧
  (∀ i j : Fin d, σ.arr B.aH (d * i + j) = I.H i j) ∧ (∀ j : Fin d, σ.arr B.ag j = I.g j) ∧
  (∀ i j : Fin d, σ.arr B.aP (d * i + j) = I.P i j) ∧ (∀ j : Fin d, σ.arr B.af j = I.f j) ∧
  σ.arr B.ac 0 = I.Dc ∧ ∀ j : Fin d, σ.arr B.ac (1 + (j : ℕ)) = I.Nc j

/-- The output: the slot `o` holds `0` on a failure; on a point `x/2^s`, it holds `1`, the slot `o + 1` holds `s` and
the cells `0, ..., d - 1` of the array `aW` hold `x`. -/
def EllOOut (B : EllOBlk) (r : Option (Fin d → ℤ)) (s : ℕ) (σ : Env d) : Prop :=
  match r with
  | none => σ.sc B.o = 0
  | some x => σ.sc B.o = 1 ∧ σ.sc (B.o + 1) = s ∧ ∀ j : Fin d, σ.arr B.aW j = x j

/-- The test's data at the precision `k`: the caller's data `TDat`, `k` in the register `rE + 1` and `2^k` in the slot
`o + 2`. -/
def TDatK (B : EllOBlk) (TDat : Env d → Prop) (k : ℕ) (σ : Env d) : Prop :=
  TDat σ ∧ σ.nat (B.rE + 1) = k ∧ σ.sc (B.o + 2) = 2 ^ k

/-- **The contract of the ELL-O block** `ellc` (a code for every test block): for every call `I` (with `Dc > 0`; the
early exits of `ellOI` are part of the code), every offset `κ` and every test block `TB` that answers `T k` at
the point of the array `aW + 1` into the register `rE`, for points below `2^bt`, when the caller's data `TDat` holds
and the precision `k = eK + κ` is in its cells (`TDatK`), whose own cells avoid the block (`TestAvoid`) and whose data
survives the writes of the block and of the test (`Stable`): the code writes `ellOI I (T k)` and the exponent
`ellExpO I` (`EllOOut`) within `C (W + Kt)^k₀` units, `W = d + ellOSz I + κ + 1`, when `C W^k₀ ≤ bt`, `bt + 4 ≤ ℓ`
and `C W^k₀ < 2^ℓa`; it keeps the draws and writes only its own cells and the test's. -/
def EllOBlockOK (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (B : EllOBlk) (nS nN nA C k₀ : ℕ)
    (ellc : XCmdO → XCmdO) : Prop :=
  ∀ (I : EllOI d) (κ : ℕ) (TB : XCmdO) (TDat : Env d → Prop) (T : ℕ → (Fin d → ℚ) → Bool) (Kt bt : ℕ)
    (St Nt : ℕ → Prop) (Art : ℕ → ℕ → Prop) (σ : Env d),
    LayOK L d ℓa → B.OK L nS nN nA → 1 ≤ d → 0 < I.Dc →
    TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt (T (I.eK + κ)) Kt St Nt Art →
    B.TestAvoid St Nt Art →
    Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k) →
    TDat σ → EllOIn B I κ σ →
    C * (d + ellOSz I + κ + 1) ^ k₀ ≤ bt → bt + 4 ≤ ℓ → C * (d + ellOSz I + κ + 1) ^ k₀ < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (ellc TB) σ (C * (d + ellOSz I + κ + Kt + 1) ^ k₀) (fun σ' =>
      EllOOut B (ellOI I (T (I.eK + κ))) (ellExpO I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k)
          σ σ')

/-- **Statement (c), the rule of ELL-O on the oracle machine.** One code builder `xellO L B sepc gc` (`sepc` a SEP
block, `gc` a gauge block, at the layouts `sepLayO B`, `gaugeLayO B` inside the block) and constants `C`, `k₀`, `nS`,
`nN`, `nA` such that for every dimension, layout, context and block, every SEP block and every gauge block meeting
their contracts (SepSpec.lean) give an ELL-O block meeting `EllOBlockOK`. -/
def EllORule : Prop :=
  ∃ (xellO : Layout → EllOBlk → (XCmdO → XCmdO) → (XCmdO → XCmdO) → XCmdO → XCmdO)
    (sepLayO : EllOBlk → SepLay) (gaugeLayO : EllOBlk → GaugeLay) (C k₀ nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (B : EllOBlk) (sepc gc : XCmdO → XCmdO),
      SepBlockOK L XO ℓa ℓ (sepLayO B) sepc → GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc →
      EllOBlockOK L XO ℓa ℓ B nS nN nA C k₀ (xellO L B sepc gc)

end AdversarialBco.Uni
