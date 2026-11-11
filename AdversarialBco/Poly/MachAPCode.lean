/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVec
public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# The subroutine AP in VL: the code

Definitions only; the rules are in `MachAP.lean`. The code computes `apCall` of `Df2Oracle.lean`: Procedure ELL-cap
(`ellCapCode`) for `d ≥ 2` and Procedure ELL-1 (`ellOneCode`) for `d = 1`, the membership questions asked of a code
`memQ` given as a parameter (its input the array `V.qv`, its answer `1` or `0` in the scalar `V.qo`).

Variables (`APVars`): the caller's natural variables `dv` (holding `d`) and `one` (holding `1`); the inputs, arrays
`a0` (the centre `a₀`), `P`, `w` and scalars `r`, `R`, `e`; the outputs, the scalar `ok` and the array `out`; the
input `qv` and output `qo` of `memQ`. The internal variables are the naturals `nB + k` (`k < 16`), the scalars
`sB + k` (`k < 128`) and the arrays `aB + k` (`k < 14`), at fixed offsets:

* naturals: `nB + 0, 1, 2` the indices of the vector and matrix macros; `nB + 3, 4` the bisection of the gauge value
  and its number of steps; `nB + 5` the halvings of LINE; `nB + 6` the coordinate of SEP; `nB + 7` the other loops of
  SEP; `nB + 8` the steps of ELL-cap; `nB + 9, 10, 11` the caps `N`, `J`, `B`; `nB + 12` holds `d²`; `nB + 13, 14, 15`
  ELL-1 (the index `0`, the number of bisection steps, the bisection);
* scalars: `sB + 0 .. 19` the gauge value (`sB + 17` the flag, `sB + 18` the value); `sB + 20` the point of a value
  of LINE or SEP; `sB + 21 .. 59` LINE (the window `21 .. 27`, the flag `28`, the state `29`, the result `30, 31`);
  `sB + 60 .. 79` SEP (the length `60`, the flag `61`), and ELL-1; `sB + 80 .. 89` the central cut;
  `sB + 90 .. 99` the step of ELL-cap; `sB + 100 .. 119` ELL-cap (`τ` at `100`, `ℓ₁` at `101`, the state flags at
  `102, 103`, the recorded point's flag and value at `104, 105`);
* arrays: `aB + 0` the difference `x - a₀` of the gauge value; `aB + 1` the point of a value; `aB + 2 .. 6` SEP (the
  point `y`, the scales `δ`, the values `v⁺`, `v⁻`, the vector `g`); `aB + 7, 8` the central cut (`A c`, `b`);
  `aB + 9 .. 13` ELL-cap (`A`, `a`, the recorded point, `a - w`, `P (a - w)`).
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL

/-- The variables of AP given by the caller, and the three bases of its internal variables. -/
structure APVars where
  dv : ℕ
  one : ℕ
  nB : ℕ
  sB : ℕ
  aB : ℕ
  a0 : ℕ
  P : ℕ
  w : ℕ
  out : ℕ
  qv : ℕ
  r : ℕ
  R : ℕ
  e : ℕ
  ok : ℕ
  qo : ℕ

variable (L : Layout) (memQ : Cmd) (V : APVars)

/-! ## The gauge value with its cap -/

/-- One halving of the bisection of the gauge value: `mid := (lo + hi)/2`; if `mid > 0`, ask whether
`a₀ + mid⁻¹ (x - a₀)` (the array `aB` holds `x - a₀`) is in the set and move `hi` or `lo` to `mid`; else `lo := mid`. -/
def gvTurn : Cmd :=
  .seq (sop2 L .add (V.sB + 12) (V.sB + 8) (V.sB + 9)) <|
  .seq (sop2 L .mul (V.sB + 12) (V.sB + 12) (V.sB + 10)) <|
  ifS L (V.sB + 7) (V.sB + 12)
    (.seq (sop2 L .div (V.sB + 13) (V.sB + 11) (V.sB + 12)) <|
     .seq (vcopy L V.dv V.one V.nB V.qv V.a0 (V.sB + 15)) <|
     .seq (vaxpy L V.dv V.one V.nB V.qv V.aB (V.sB + 13) (V.sB + 15) (V.sB + 16)) <|
     .seq memQ <|
     ifS L (V.sB + 7) V.qo (smov L (V.sB + 9) (V.sB + 12)) (smov L (V.sB + 8) (V.sB + 12)))
    (smov L (V.sB + 8) (V.sB + 12))

/-- The value `oGaugeValCap Q a₀ r R B x η` of the gauge (`B` in the natural variable `nB + 11`, `x` an array, `η` a
scalar): `aB := x - a₀`, `nx := |x - a₀|`, `v := log₂ (nx/(r η))`; fail (`sB + 17 := 0`) if `B < v`; else
`sB + 17 := 1` and `sB + 18 :=` the upper end after `⌈v⌉₊` halvings of `[nx/(2R), nx/r]`, or `0` if `nx = 0`. -/
def gvCode (x η : ℕ) : Cmd :=
  .seq (vcopy L V.dv V.one V.nB V.aB x (V.sB + 15)) <|
  .seq (sconst L V.sB (-1)) <|
  .seq (vaxpy L V.dv V.one V.nB V.aB V.a0 V.sB (V.sB + 15) (V.sB + 16)) <|
  .seq (vnorm L V.dv V.one V.nB (V.sB + 1) V.aB (V.sB + 15) (V.sB + 16)) <|
  .seq (sop2 L .mul (V.sB + 2) V.r η) <|
  .seq (sop2 L .div (V.sB + 2) (V.sB + 1) (V.sB + 2)) <|
  .seq (sop1 L .log (V.sB + 2) (V.sB + 2)) <|
  .seq (sconst L (V.sB + 3) 2) <|
  .seq (sop1 L .log (V.sB + 4) (V.sB + 3)) <|
  .seq (sop2 L .div (V.sB + 5) (V.sB + 2) (V.sB + 4)) <|
  .seq (ncast L (V.sB + 6) (V.nB + 11)) <|
  ifS L (V.sB + 6) (V.sB + 5) (sconst L (V.sB + 17) 0) <|
  .seq (sconst L (V.sB + 17) 1) <|
  .seq (sconst L (V.sB + 7) 0) <|
  ifS L (V.sB + 7) (V.sB + 1)
    (.seq (nceil L (V.nB + 4) V.one (V.sB + 5) (V.sB + 14)) <|
     .seq (sop2 L .mul (V.sB + 2) (V.sB + 3) V.R) <|
     .seq (sop2 L .div (V.sB + 8) (V.sB + 1) (V.sB + 2)) <|
     .seq (sop2 L .div (V.sB + 9) (V.sB + 1) V.r) <|
     .seq (sconst L (V.sB + 10) (1 / 2)) <|
     .seq (sconst L (V.sB + 11) 1) <|
     .seq (forN (V.nB + 3) (V.nB + 4) V.one (gvTurn L memQ V)) <|
     smov L (V.sB + 18) (V.sB + 9))
    (smov L (V.sB + 18) (V.sB + 7))

/-- The value of the gauge at `y + s e_i` with error `η` (`y` the array `aB + 2`, `i` the natural variable `idx`,
`s` and `η` scalars): `aB + 1 := y`, its entry `i` plus `s`, then `gvCode`. -/
def ev1Code (idx s η : ℕ) : Cmd :=
  .seq (vcopy L V.dv V.one V.nB (V.aB + 1) (V.aB + 2) (V.sB + 20)) <|
  .seq (aget L (V.sB + 20) (V.aB + 1) idx) <|
  .seq (sop2 L .add (V.sB + 20) (V.sB + 20) s) <|
  .seq (aset L (V.aB + 1) idx (V.sB + 20)) <|
  gvCode L memQ V (V.aB + 1) η

/-! ## Procedure LINE

The window `⟨p₀, λ, v₀, ..., v₄⟩` in the scalars `sB + 21 .. 27`; the flag `sB + 28` (`0` after a failure), the
state `sB + 29` (`1` while running); the result `(s, δ)` in `sB + 30, 31`. The length `ℓ` is the scalar `sB + 60`,
`τ` the scalar `sB + 100`, the cap `J` the natural variable `nB + 10`; the values are asked at `y + s e_i`, `y` the
array `aB + 2`, `i` the natural variable `nB + 6`. -/

/-- The failure of LINE. -/
def lineFail : Cmd := .seq (sconst L (V.sB + 28) 0) (sconst L (V.sB + 29) 0)

/-- A value of LINE at the point `sB + 39` with the error `sB + 38` into `dst`, then `rest`; on a failed value, the
failure of LINE. -/
def lineEv (dst : ℕ) (rest : Cmd) : Cmd :=
  .seq (ev1Code L memQ V (V.nB + 6) (V.sB + 39) (V.sB + 38)) <|
  ifS L (V.sB + 32) (V.sB + 17) (.seq (smov L dst (V.sB + 18)) rest) (lineFail L V)

/-- The first window: `λ := ℓ/4`, the five values at `k λ` with error `τ λ/400`. -/
def lineFirstCode : Cmd :=
  .seq (sconst L (V.sB + 32) 0) <|
  .seq (sconst L (V.sB + 49) 4) <|
  .seq (sop2 L .div (V.sB + 22) (V.sB + 60) (V.sB + 49)) <|
  .seq (sop2 L .mul (V.sB + 38) (V.sB + 100) (V.sB + 22)) <|
  .seq (sconst L (V.sB + 49) 400) <|
  .seq (sop2 L .div (V.sB + 38) (V.sB + 38) (V.sB + 49)) <|
  .seq (sconst L (V.sB + 39) 0) <|
  lineEv L memQ V (V.sB + 23) <|
  .seq (smov L (V.sB + 39) (V.sB + 22)) <|
  lineEv L memQ V (V.sB + 24) <|
  .seq (sconst L (V.sB + 49) 2) <|
  .seq (sop2 L .mul (V.sB + 39) (V.sB + 49) (V.sB + 22)) <|
  lineEv L memQ V (V.sB + 25) <|
  .seq (sconst L (V.sB + 49) 3) <|
  .seq (sop2 L .mul (V.sB + 39) (V.sB + 49) (V.sB + 22)) <|
  lineEv L memQ V (V.sB + 26) <|
  .seq (sconst L (V.sB + 49) 4) <|
  .seq (sop2 L .mul (V.sB + 39) (V.sB + 49) (V.sB + 22)) <|
  lineEv L memQ V (V.sB + 27) <|
  .seq (sconst L (V.sB + 21) 0) <|
  .seq (sconst L (V.sB + 28) 1) <|
  sconst L (V.sB + 29) 1

/-- One halving: `l := λ/4`, `p₁ := p₀ + λ`, `p₂ := p₀ + 2λ`, the six values at `p₁ + k l`, `p₂ + k l` (`k = 1, 2, 3`)
with error `τ λ/1600`, the spreads of the windows `A` (from `p₁`) and `B` (from `p₂`), and the window of smaller
spread (`A` on a tie). -/
def lineHalveCode : Cmd :=
  .seq (sconst L (V.sB + 49) 4) <|
  .seq (sop2 L .div (V.sB + 35) (V.sB + 22) (V.sB + 49)) <|
  .seq (sop2 L .add (V.sB + 36) (V.sB + 21) (V.sB + 22)) <|
  .seq (sconst L (V.sB + 49) 2) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 22)) <|
  .seq (sop2 L .add (V.sB + 37) (V.sB + 21) (V.sB + 48)) <|
  .seq (sop2 L .mul (V.sB + 38) (V.sB + 100) (V.sB + 22)) <|
  .seq (sconst L (V.sB + 49) 1600) <|
  .seq (sop2 L .div (V.sB + 38) (V.sB + 38) (V.sB + 49)) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 36) (V.sB + 35)) <|
  lineEv L memQ V (V.sB + 40) <|
  .seq (sconst L (V.sB + 49) 2) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 35)) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 36) (V.sB + 48)) <|
  lineEv L memQ V (V.sB + 41) <|
  .seq (sconst L (V.sB + 49) 3) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 35)) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 36) (V.sB + 48)) <|
  lineEv L memQ V (V.sB + 42) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 37) (V.sB + 35)) <|
  lineEv L memQ V (V.sB + 43) <|
  .seq (sconst L (V.sB + 49) 2) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 35)) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 37) (V.sB + 48)) <|
  lineEv L memQ V (V.sB + 44) <|
  .seq (sconst L (V.sB + 49) 3) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 35)) <|
  .seq (sop2 L .add (V.sB + 39) (V.sB + 37) (V.sB + 48)) <|
  lineEv L memQ V (V.sB + 45) <|
  .seq (sop2 L .sub (V.sB + 46) (V.sB + 25) (V.sB + 42)) <|
  .seq (sop2 L .sub (V.sB + 48) (V.sB + 40) (V.sB + 24)) <|
  .seq (sop2 L .sub (V.sB + 46) (V.sB + 46) (V.sB + 48)) <|
  .seq (sop2 L .div (V.sB + 46) (V.sB + 46) (V.sB + 35)) <|
  .seq (sop2 L .sub (V.sB + 47) (V.sB + 26) (V.sB + 45)) <|
  .seq (sop2 L .sub (V.sB + 48) (V.sB + 43) (V.sB + 25)) <|
  .seq (sop2 L .sub (V.sB + 47) (V.sB + 47) (V.sB + 48)) <|
  .seq (sop2 L .div (V.sB + 47) (V.sB + 47) (V.sB + 35)) <|
  ifS L (V.sB + 47) (V.sB + 46)
    (.seq (smov L (V.sB + 21) (V.sB + 37)) <| .seq (smov L (V.sB + 22) (V.sB + 35)) <|
     .seq (smov L (V.sB + 23) (V.sB + 25)) <| .seq (smov L (V.sB + 27) (V.sB + 26)) <|
     .seq (smov L (V.sB + 24) (V.sB + 43)) <| .seq (smov L (V.sB + 25) (V.sB + 44)) <|
     smov L (V.sB + 26) (V.sB + 45))
    (.seq (smov L (V.sB + 21) (V.sB + 36)) <| .seq (smov L (V.sB + 22) (V.sB + 35)) <|
     .seq (smov L (V.sB + 23) (V.sB + 24)) <| .seq (smov L (V.sB + 27) (V.sB + 25)) <|
     .seq (smov L (V.sB + 24) (V.sB + 40)) <| .seq (smov L (V.sB + 25) (V.sB + 41)) <|
     smov L (V.sB + 26) (V.sB + 42))

/-- The stop of LINE at the current window: `s := p₀ + 2λ`, `δ := λ`, state `0`. The scalar `sB + 49` holds `2`. -/
def lineDone : Cmd :=
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 22)) <|
  .seq (sop2 L .add (V.sB + 30) (V.sB + 21) (V.sB + 48)) <|
  .seq (smov L (V.sB + 31) (V.sB + 22)) <|
  sconst L (V.sB + 29) 0

/-- The test of the current window: the measured second difference `v₃ + v₁ - 2 v₂` against `τ λ/2`; above it,
`more`, else the stop. -/
def lineCheck (more : Cmd) : Cmd :=
  .seq (sop2 L .add (V.sB + 34) (V.sB + 26) (V.sB + 24)) <|
  .seq (sconst L (V.sB + 49) 2) <|
  .seq (sop2 L .mul (V.sB + 48) (V.sB + 49) (V.sB + 25)) <|
  .seq (sop2 L .sub (V.sB + 34) (V.sB + 34) (V.sB + 48)) <|
  .seq (sop2 L .mul (V.sB + 33) (V.sB + 100) (V.sB + 22)) <|
  .seq (sop2 L .div (V.sB + 33) (V.sB + 33) (V.sB + 49)) <|
  ifS L (V.sB + 33) (V.sB + 34) more (lineDone L V)

/-- Procedure LINE with at most `J` halvings. -/
def lineCode : Cmd :=
  .seq (lineFirstCode L memQ V) <|
  .seq (forN (V.nB + 5) (V.nB + 10) V.one
    (ifS L (V.sB + 32) (V.sB + 29) (lineCheck L V (lineHalveCode L memQ V)) .skip)) <|
  ifS L (V.sB + 32) (V.sB + 29) (lineCheck L V (lineFail L V)) .skip

/-! ## Procedure SEP

On the gauge, from `y⁰` (the array `y0`), with `τ` the scalar `sB + 100`, `ℓ₁` the scalar `sB + 101`, `L = 1/r` and
the cap `J`: the flag `sB + 61`, the vector `g` in the array `aB + 6`. -/

/-- The search along the coordinate `nB + 6`: LINE, then `y_i := y_i + s`, `ℓ := τ δ/(16 L)`, `δ_i := δ`; or the
failure. -/
def sepCoordTurn : Cmd :=
  .seq (lineCode L memQ V) <|
  ifS L (V.sB + 63) (V.sB + 28)
    (.seq (aget L (V.sB + 66) (V.aB + 2) (V.nB + 6)) <|
     .seq (sop2 L .add (V.sB + 66) (V.sB + 66) (V.sB + 30)) <|
     .seq (aset L (V.aB + 2) (V.nB + 6) (V.sB + 66)) <|
     .seq (sop2 L .mul (V.sB + 66) (V.sB + 100) (V.sB + 31)) <|
     .seq (sop2 L .div (V.sB + 60) (V.sB + 66) (V.sB + 62)) <|
     aset L (V.aB + 3) (V.nB + 6) (V.sB + 31))
    (sconst L (V.sB + 61) 0)

/-- The value at `y + δ_i e_i` with error `τ δ_i/400` into `v⁺_i` (`i` the natural variable `nB + 7`). -/
def sepPlusTurn : Cmd :=
  .seq (aget L (V.sB + 69) (V.aB + 3) (V.nB + 7)) <|
  .seq (sop2 L .mul (V.sB + 68) (V.sB + 100) (V.sB + 69)) <|
  .seq (sconst L (V.sB + 65) 400) <|
  .seq (sop2 L .div (V.sB + 68) (V.sB + 68) (V.sB + 65)) <|
  .seq (ev1Code L memQ V (V.nB + 7) (V.sB + 69) (V.sB + 68)) <|
  ifS L (V.sB + 63) (V.sB + 17) (aset L (V.aB + 4) (V.nB + 7) (V.sB + 18)) (sconst L (V.sB + 61) 0)

/-- The value at `y - δ_i e_i` with error `τ δ_i/400` into `v⁻_i`. -/
def sepMinusTurn : Cmd :=
  .seq (aget L (V.sB + 66) (V.aB + 3) (V.nB + 7)) <|
  .seq (sop2 L .sub (V.sB + 69) (V.sB + 63) (V.sB + 66)) <|
  .seq (sop2 L .mul (V.sB + 68) (V.sB + 100) (V.sB + 66)) <|
  .seq (sconst L (V.sB + 65) 400) <|
  .seq (sop2 L .div (V.sB + 68) (V.sB + 68) (V.sB + 65)) <|
  .seq (ev1Code L memQ V (V.nB + 7) (V.sB + 69) (V.sB + 68)) <|
  ifS L (V.sB + 63) (V.sB + 17) (aset L (V.aB + 5) (V.nB + 7) (V.sB + 18)) (sconst L (V.sB + 61) 0)

/-- `g_i := (v⁺_i - v⁻_i)/(2 δ_i)`. -/
def sepGTurn : Cmd :=
  .seq (aget L (V.sB + 66) (V.aB + 4) (V.nB + 7)) <|
  .seq (aget L (V.sB + 70) (V.aB + 5) (V.nB + 7)) <|
  .seq (sop2 L .sub (V.sB + 66) (V.sB + 66) (V.sB + 70)) <|
  .seq (aget L (V.sB + 70) (V.aB + 3) (V.nB + 7)) <|
  .seq (sconst L (V.sB + 65) 2) <|
  .seq (sop2 L .mul (V.sB + 70) (V.sB + 65) (V.sB + 70)) <|
  .seq (sop2 L .div (V.sB + 66) (V.sB + 66) (V.sB + 70)) <|
  aset L (V.aB + 6) (V.nB + 7) (V.sB + 66)

/-- After the searches: `m := min_i δ_i`, the value at `y` with error `τ m/400` (only its failure is read), then the
values `v⁺`, `v⁻` and `g`. -/
def sepTail : Cmd :=
  .seq (nconst (V.nB + 7) 0) <|
  .seq (aget L (V.sB + 67) (V.aB + 3) (V.nB + 7)) <|
  .seq (forN (V.nB + 7) V.dv V.one
    (.seq (aget L (V.sB + 66) (V.aB + 3) (V.nB + 7)) (smin L (V.sB + 67) (V.sB + 67) (V.sB + 66)))) <|
  .seq (sop2 L .mul (V.sB + 68) (V.sB + 100) (V.sB + 67)) <|
  .seq (sconst L (V.sB + 65) 400) <|
  .seq (sop2 L .div (V.sB + 68) (V.sB + 68) (V.sB + 65)) <|
  .seq (gvCode L memQ V (V.aB + 2) (V.sB + 68)) <|
  ifS L (V.sB + 63) (V.sB + 17)
    (.seq (forN (V.nB + 7) V.dv V.one (sepPlusTurn L memQ V)) <|
     .seq (forN (V.nB + 7) V.dv V.one (sepMinusTurn L memQ V)) <|
     forN (V.nB + 7) V.dv V.one (sepGTurn L V))
    (sconst L (V.sB + 61) 0)

/-- Procedure SEP from `y⁰` (the array `y0`). -/
def sepCode (y0 : ℕ) : Cmd :=
  .seq (vcopy L V.dv V.one V.nB (V.aB + 2) y0 (V.sB + 66)) <|
  .seq (sconst L (V.sB + 63) 0) <|
  .seq (vfill L V.dv V.one V.nB (V.aB + 3) (V.sB + 63)) <|
  .seq (smov L (V.sB + 60) (V.sB + 101)) <|
  .seq (sconst L (V.sB + 61) 1) <|
  .seq (sconst L (V.sB + 64) 1) <|
  .seq (sop2 L .div (V.sB + 62) (V.sB + 64) V.r) <|
  .seq (sconst L (V.sB + 65) 16) <|
  .seq (sop2 L .mul (V.sB + 62) (V.sB + 65) (V.sB + 62)) <|
  .seq (forN (V.nB + 6) V.dv V.one (ifS L (V.sB + 63) (V.sB + 61) (sepCoordTurn L memQ V) .skip)) <|
  ifS L (V.sB + 63) (V.sB + 61) (sepTail L memQ V) .skip

/-! ## The central cut -/

/-- The central cut of Lemma E.4 by the array `c` (`c ≠ aB + 7`, `aB + 8`): `Ac := A c`,
`b := (cᵀ A c)^{-1/2} A c`, `A := (d²/(d² - 1)) A - (d²/(d² - 1)) (2/(d + 1)) b bᵀ`, `a := a - b/(d + 1)`, with `A`
the array `aB + 9` and `a` the array `aB + 10`. -/
def cutCode (c : ℕ) : Cmd :=
  .seq (matvec L V.dv V.one V.nB (V.nB + 1) (V.nB + 2) (V.aB + 7) (V.aB + 9) c (V.sB + 80) (V.sB + 87) (V.sB + 88)) <|
  .seq (vdot L V.dv V.one V.nB (V.sB + 80) c (V.aB + 7) (V.sB + 87) (V.sB + 88)) <|
  .seq (sop1 L .sqrt (V.sB + 80) (V.sB + 80)) <|
  .seq (sconst L (V.sB + 81) 1) <|
  .seq (sop2 L .div (V.sB + 80) (V.sB + 81) (V.sB + 80)) <|
  .seq (vcopy L V.dv V.one V.nB (V.aB + 8) (V.aB + 7) (V.sB + 87)) <|
  .seq (vscale L V.dv V.one V.nB (V.aB + 8) (V.sB + 80) (V.sB + 87)) <|
  .seq (ncast L (V.sB + 82) V.dv) <|
  .seq (sop2 L .mul (V.sB + 83) (V.sB + 82) (V.sB + 82)) <|
  .seq (sop2 L .sub (V.sB + 87) (V.sB + 83) (V.sB + 81)) <|
  .seq (sop2 L .div (V.sB + 84) (V.sB + 83) (V.sB + 87)) <|
  .seq (sop2 L .add (V.sB + 87) (V.sB + 82) (V.sB + 81)) <|
  .seq (sconst L (V.sB + 88) 2) <|
  .seq (sop2 L .div (V.sB + 85) (V.sB + 88) (V.sB + 87)) <|
  .seq (sop2 L .mul (V.sB + 85) (V.sB + 84) (V.sB + 85)) <|
  .seq (sconst L (V.sB + 88) 0) <|
  .seq (sop2 L .sub (V.sB + 85) (V.sB + 88) (V.sB + 85)) <|
  .seq (sop2 L .div (V.sB + 86) (V.sB + 81) (V.sB + 87)) <|
  .seq (sop2 L .sub (V.sB + 86) (V.sB + 88) (V.sB + 86)) <|
  .seq (rankOne L V.dv V.one V.nB (V.nB + 1) (V.nB + 2) (V.aB + 9) (V.sB + 84) (V.sB + 85) (V.aB + 8) (V.aB + 8)
    (V.sB + 87) (V.sB + 88) (V.sB + 89)) <|
  vaxpy L V.dv V.one V.nB (V.aB + 10) (V.aB + 8) (V.sB + 86) (V.sB + 87) (V.sB + 88)

/-! ## Procedure ELL-cap

The state: `A` and `a` in the arrays `aB + 9`, `aB + 10`; the recorded point in the array `aB + 11`, its flag in the
scalar `sB + 104` and its value of `F` in `sB + 105`; the flags `sB + 102` (`1` while running) and `sB + 103` (`0`
after a failure); a returned point stays in `aB + 10`. -/

/-- A failed step. -/
def ellFail : Cmd := .seq (sconst L (V.sB + 102) 0) (sconst L (V.sB + 103) 0)

/-- Step 3 of ELL-cap at `a ∈ Q`: record `a`, then return it if `P (a - w) = 0`, else cut by `P (a - w)`. -/
def ellStep3 : Cmd :=
  .seq (vcopy L V.dv V.one V.nB (V.aB + 12) (V.aB + 10) (V.sB + 97)) <|
  .seq (sconst L (V.sB + 92) (-1)) <|
  .seq (vaxpy L V.dv V.one V.nB (V.aB + 12) V.w (V.sB + 92) (V.sB + 97) (V.sB + 98)) <|
  .seq (matvec L V.dv V.one V.nB (V.nB + 1) (V.nB + 2) (V.aB + 13) V.P (V.aB + 12) (V.sB + 96) (V.sB + 97)
    (V.sB + 98)) <|
  .seq (vdot L V.dv V.one V.nB (V.sB + 93) (V.aB + 12) (V.aB + 13) (V.sB + 97) (V.sB + 98)) <|
  .seq (sconst L (V.sB + 95) (1 / 2)) <|
  .seq (sop2 L .mul (V.sB + 93) (V.sB + 95) (V.sB + 93)) <|
  .seq (ifS L (V.sB + 91) (V.sB + 104)
    (ifS L (V.sB + 93) (V.sB + 105)
      (.seq (vcopy L V.dv V.one V.nB (V.aB + 11) (V.aB + 10) (V.sB + 97)) (smov L (V.sB + 105) (V.sB + 93)))
      .skip)
    (.seq (vcopy L V.dv V.one V.nB (V.aB + 11) (V.aB + 10) (V.sB + 97)) <|
     .seq (smov L (V.sB + 105) (V.sB + 93)) <|
     sconst L (V.sB + 104) 1)) <|
  .seq (vdot L V.dv V.one V.nB (V.sB + 94) (V.aB + 13) (V.aB + 13) (V.sB + 97) (V.sB + 98)) <|
  ifS L (V.sB + 91) (V.sB + 94) (cutCode L V (V.aB + 13)) (sconst L (V.sB + 102) 0)

/-- One step of ELL-cap: step 1 (`|a| > R`), step 2 (`a ∉ Q`: SEP on the gauge, the stop (c3) at `g = 0`), step 3. -/
def ellStepCode : Cmd :=
  .seq (vnorm L V.dv V.one V.nB (V.sB + 90) (V.aB + 10) (V.sB + 97) (V.sB + 98)) <|
  ifS L V.R (V.sB + 90)
    (cutCode L V (V.aB + 10))
    (.seq (vcopy L V.dv V.one V.nB V.qv (V.aB + 10) (V.sB + 97)) <|
     .seq memQ <|
     .seq (sconst L (V.sB + 91) 0) <|
     ifS L (V.sB + 91) V.qo
       (ellStep3 L V)
       (.seq (sepCode L memQ V (V.aB + 10)) <|
        ifS L (V.sB + 91) (V.sB + 61)
          (.seq (vdot L V.dv V.one V.nB (V.sB + 99) (V.aB + 6) (V.aB + 6) (V.sB + 97) (V.sB + 98)) <|
           ifS L (V.sB + 91) (V.sB + 99) (cutCode L V (V.aB + 6)) (ellFail L V))
          (ellFail L V)))

/-- The constants of ELL-cap: `τ` (`sB + 100`), `ℓ₁` (`sB + 101`), `N`, `J`, `B` (the natural variables
`nB + 9, 10, 11`). Scratch: `sB + 106 .. 119`. -/
def ellConstsCode : Cmd :=
  .seq (mtrace L V.dv V.one V.nB (V.nB + 2) (V.sB + 107) V.P (V.sB + 110)) <|
  .seq (vnorm L V.dv V.one V.nB (V.sB + 110) V.w (V.sB + 111) (V.sB + 116)) <|
  .seq (sop2 L .add (V.sB + 110) V.R (V.sB + 110)) <|
  .seq (sop2 L .mul (V.sB + 107) (V.sB + 107) (V.sB + 110)) <|
  .seq (sconst L (V.sB + 116) 3) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 116) (V.sB + 107)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 110) V.R) <|
  .seq (sop2 L .div (V.sB + 110) V.e (V.sB + 110)) <|
  .seq (sconst L (V.sB + 117) 1) <|
  .seq (smin L (V.sB + 108) (V.sB + 117) (V.sB + 110)) <|
  .seq (sop2 L .mul (V.sB + 109) (V.sB + 108) V.r) <|
  .seq (sconst L (V.sB + 116) 2) <|
  .seq (sop2 L .div (V.sB + 109) (V.sB + 109) (V.sB + 116)) <|
  .seq (ncast L (V.sB + 112) V.dv) <|
  .seq (sconst L (V.sB + 116) 36) <|
  .seq (sop2 L .mul (V.sB + 110) V.R V.R) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 116) (V.sB + 110)) <|
  .seq (sop1 L .sqrt (V.sB + 111) (V.sB + 112)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 110) (V.sB + 111)) <|
  .seq (sop2 L .div (V.sB + 100) (V.sB + 109) (V.sB + 110)) <|
  .seq (sop2 L .mul (V.sB + 101) V.r (V.sB + 109)) <|
  .seq (sconst L (V.sB + 116) 24) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 116) V.R) <|
  .seq (sop2 L .div (V.sB + 101) (V.sB + 101) (V.sB + 110)) <|
  .seq (sconst L (V.sB + 116) 2) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 116) (V.sB + 112)) <|
  .seq (sop2 L .add (V.sB + 111) (V.sB + 112) (V.sB + 117)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 110) (V.sB + 111)) <|
  .seq (sop2 L .mul (V.sB + 111) (V.sB + 116) V.R) <|
  .seq (sop2 L .mul (V.sB + 114) (V.sB + 108) V.r) <|
  .seq (sop2 L .div (V.sB + 111) (V.sB + 111) (V.sB + 114)) <|
  .seq (sop1 L .log (V.sB + 111) (V.sB + 111)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 110) (V.sB + 111)) <|
  .seq (nceil L (V.nB + 9) V.one (V.sB + 110) (V.sB + 114)) <|
  .seq (nadd (V.nB + 9) (V.nB + 9) V.one) <|
  .seq (sop2 L .mul (V.sB + 110) V.r (V.sB + 100)) <|
  .seq (sconst L (V.sB + 116) 8) <|
  .seq (sop2 L .div (V.sB + 110) (V.sB + 116) (V.sB + 110)) <|
  .seq (sop1 L .log (V.sB + 110) (V.sB + 110)) <|
  .seq (sconst L (V.sB + 116) 2) <|
  .seq (sop1 L .log (V.sB + 113) (V.sB + 116)) <|
  .seq (sop2 L .div (V.sB + 110) (V.sB + 110) (V.sB + 113)) <|
  .seq (nceil L (V.nB + 10) V.one (V.sB + 110) (V.sB + 114)) <|
  .seq (ncast L (V.sB + 110) (V.nB + 10)) <|
  .seq (sop2 L .add (V.sB + 110) (V.sB + 110) (V.sB + 117)) <|
  .seq (sconst L (V.sB + 116) 3) <|
  .seq (sop2 L .mul (V.sB + 111) (V.sB + 116) (V.sB + 112)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 111) (V.sB + 110)) <|
  .seq (sconst L (V.sB + 116) 0) <|
  .seq (sop2 L .sub (V.sB + 110) (V.sB + 116) (V.sB + 110)) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 113) (V.sB + 110)) <|
  .seq (sop1 L .exp (V.sB + 110) (V.sB + 110)) <|
  .seq (sop2 L .mul (V.sB + 115) (V.sB + 100) (V.sB + 101)) <|
  .seq (sconst L (V.sB + 116) 1600) <|
  .seq (sop2 L .div (V.sB + 115) (V.sB + 115) (V.sB + 116)) <|
  .seq (sop2 L .mul (V.sB + 115) (V.sB + 115) (V.sB + 110)) <|
  .seq (sconst L (V.sB + 116) 3) <|
  .seq (sop2 L .mul (V.sB + 110) (V.sB + 116) V.R) <|
  .seq (sop2 L .mul (V.sB + 111) V.r (V.sB + 115)) <|
  .seq (sop2 L .div (V.sB + 110) (V.sB + 110) (V.sB + 111)) <|
  .seq (sop1 L .log (V.sB + 110) (V.sB + 110)) <|
  .seq (sop2 L .div (V.sB + 110) (V.sB + 110) (V.sB + 113)) <|
  nceil L (V.nB + 11) V.one (V.sB + 110) (V.sB + 114)

/-- The start of ELL-cap: `A := R² I`, `a := 0`, no recorded point, running. -/
def ellInitCode : Cmd :=
  .seq (nsq V.dv V.one V.nB (V.nB + 12)) <|
  .seq (sconst L (V.sB + 106) 0) <|
  .seq (mfill L (V.nB + 12) V.one V.nB (V.aB + 9) (V.sB + 106)) <|
  .seq (sop2 L .mul (V.sB + 110) V.R V.R) <|
  .seq (mdiag L V.dv V.one V.nB (V.nB + 2) (V.aB + 9) (V.sB + 110)) <|
  .seq (vfill L V.dv V.one V.nB (V.aB + 10) (V.sB + 106)) <|
  .seq (sconst L (V.sB + 104) 0) <|
  .seq (sconst L (V.sB + 102) 1) <|
  sconst L (V.sB + 103) 1

/-- The end of ELL-cap: the returned point, else the recorded point, else the failure. -/
def ellFinalCode : Cmd :=
  ifS L (V.sB + 106) (V.sB + 103)
    (ifS L (V.sB + 106) (V.sB + 102)
      (ifS L (V.sB + 106) (V.sB + 104)
        (.seq (vcopy L V.dv V.one V.nB V.out (V.aB + 11) (V.sB + 110)) (sconst L V.ok 1))
        (sconst L V.ok 0))
      (.seq (vcopy L V.dv V.one V.nB V.out (V.aB + 10) (V.sB + 110)) (sconst L V.ok 1)))
    (sconst L V.ok 0)

/-- Procedure ELL-cap: the stop (c0) if `R < r`; else the constants, the start, `N` steps, the end. -/
def ellCapCode : Cmd :=
  ifS L V.R V.r (sconst L V.ok 0) <|
  .seq (ellConstsCode L V) <|
  .seq (ellInitCode L V) <|
  .seq (forN (V.nB + 8) (V.nB + 9) V.one (ifS L (V.sB + 106) (V.sB + 102) (ellStepCode L memQ V) .skip)) <|
  ellFinalCode L V

/-! ## Procedure ELL-1 and the dispatch

ELL-1 for `d = 1` on the entries `0` of the arrays (`nB + 13` holds `0`): `a₀` in `sB + 60`, `w` in `sB + 61`, `p`
in `sB + 62`, `|a₀|` in `sB + 63`, the zero `sB + 64`, `w'` in `sB + 65`, `ξ` in `sB + 66`, the bisection `lo`, `hi`,
`mid`, `1/2` in `sB + 67 .. 70`, scratch `sB + 71 .. 74`. -/

/-- One halving of the bisection of ELL-1: `mid := (lo + hi)/2`; the question `mid ∈ Q`; `lo := mid` or
`hi := mid`. -/
def ellOneTurn : Cmd :=
  .seq (sop2 L .add (V.sB + 69) (V.sB + 67) (V.sB + 68)) <|
  .seq (sop2 L .mul (V.sB + 69) (V.sB + 69) (V.sB + 70)) <|
  .seq (aset L V.qv (V.nB + 13) (V.sB + 69)) <|
  .seq memQ <|
  ifS L (V.sB + 64) V.qo (smov L (V.sB + 67) (V.sB + 69)) (smov L (V.sB + 68) (V.sB + 69))

/-- Procedure ELL-1. -/
def ellOneCode : Cmd :=
  .seq (nconst (V.nB + 13) 0) <|
  .seq (aget L (V.sB + 60) V.a0 (V.nB + 13)) <|
  .seq (aget L (V.sB + 61) V.w (V.nB + 13)) <|
  .seq (aget L (V.sB + 62) V.P (V.nB + 13)) <|
  .seq (sconst L (V.sB + 64) 0) <|
  .seq (sop2 L .sub (V.sB + 71) (V.sB + 64) (V.sB + 60)) <|
  .seq (smax L (V.sB + 63) (V.sB + 60) (V.sB + 71)) <|
  ifS L V.R V.r (sconst L V.ok 0) <|
  ifS L V.R (V.sB + 63) (sconst L V.ok 0) <|
  .seq (aset L V.qv (V.nB + 13) (V.sB + 60)) <|
  .seq memQ <|
  ifS L (V.sB + 64) V.qo
    (.seq (smin L (V.sB + 71) V.R (V.sB + 61)) <|
     .seq (sop2 L .sub (V.sB + 72) (V.sB + 64) V.R) <|
     .seq (smax L (V.sB + 65) (V.sB + 72) (V.sB + 71)) <|
     .seq (aset L V.qv (V.nB + 13) (V.sB + 65)) <|
     .seq memQ <|
     ifS L (V.sB + 64) V.qo
       (.seq (aset L V.out (V.nB + 13) (V.sB + 65)) (sconst L V.ok 1))
       (.seq (sop2 L .sub (V.sB + 71) (V.sB + 64) (V.sB + 61)) <|
        .seq (smax L (V.sB + 71) (V.sB + 61) (V.sB + 71)) <|
        .seq (sop2 L .add (V.sB + 71) V.R (V.sB + 71)) <|
        .seq (sop2 L .mul (V.sB + 71) (V.sB + 62) (V.sB + 71)) <|
        .seq (sop2 L .div (V.sB + 66) V.e (V.sB + 71)) <|
        .seq (sop2 L .sub (V.sB + 71) (V.sB + 65) (V.sB + 60)) <|
        .seq (sop2 L .sub (V.sB + 72) (V.sB + 64) (V.sB + 71)) <|
        .seq (smax L (V.sB + 71) (V.sB + 71) (V.sB + 72)) <|
        .seq (sop2 L .div (V.sB + 71) (V.sB + 71) (V.sB + 66)) <|
        .seq (sop1 L .log (V.sB + 71) (V.sB + 71)) <|
        .seq (sconst L (V.sB + 73) 2) <|
        .seq (sop1 L .log (V.sB + 72) (V.sB + 73)) <|
        .seq (sop2 L .div (V.sB + 71) (V.sB + 71) (V.sB + 72)) <|
        .seq (nceil L (V.nB + 14) V.one (V.sB + 71) (V.sB + 74)) <|
        .seq (smov L (V.sB + 67) (V.sB + 60)) <|
        .seq (smov L (V.sB + 68) (V.sB + 65)) <|
        .seq (sconst L (V.sB + 70) (1 / 2)) <|
        .seq (forN (V.nB + 15) (V.nB + 14) V.one (ellOneTurn L memQ V)) <|
        .seq (aset L V.out (V.nB + 13) (V.sB + 67)) (sconst L V.ok 1)))
    (sconst L V.ok 0)

/-- The code of AP: ELL-cap if `1 < d`, else ELL-1. -/
def apCode : Cmd := .ifN V.one V.dv (ellCapCode L memQ V) (ellOneCode L memQ V)

end AdversarialBco.Poly.AP
