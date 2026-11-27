/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.ClampNS
public import AdversarialBco.Poly.MachPGCode

@[expose] public section

/-!
# The code of PG-N with CLAMP-NS

Definitions only. The code of PG-N: the leaves of the code of PG (Poly/MachPGCode.lean) with two of them replaced,
every variable, frame, parameter block and draw unchanged, and the loops over them:

* F1-NS, `pgUpdNS`: the move and the projection of a descent step with CLAMP-NS (`clampNSC`) in place of the `spec`
  clamp. `pgEprL` recomputes `e' = pgEpr d ρ` from the stage variables into `s0 + 36`; `clampNSC` runs the routine
  on array `a0 + 1`: the parameters `m`, `w`, `R₀`, `c₀`, `1/c₀` (`nsParL`), the count
  `k = cnK` and `J = 2k + ⌈log₂ (3k + 3)⌉ = cnsJ` (`nsCountC`), `sym Y - m I` (`nsSymC`), its Frobenius clip at `R₀`
  through `tr (W W)` (`nsClipC`), the two roots `Y^c = M X_J` (`nsRootC`, the loop `nsLoopC` of `J` Newton-Schulz
  steps `nsStepC`) and `m I + (Y^a - Y^b)/2` (`nsOutC`).
* F2, `pgVerdC3P`: the third clause of a basic verdict by the signs of the pivots of Gauss-Jordan elimination on
  `Q̂ - (5/8)(κ/d) I`: one read and one comparison before each `gjPivot` (`gjPivotT`), the verdict cleared at a pivot
  `≤ 0`.
* The loops `pgStepNS` to `pgCodeNS`: the descent, the amplified test, the repeats, the stages and the procedure,
  over these leaves.

Variables of CLAMP-NS (base `nb` for naturals, `sb` for scalars): naturals `nb + 0` to `nb + 5` the indices of the
matrix macros, `nb + 6` the count `k` then the loop index, `nb + 7` the logarithm `⌈log₂ (3k + 3)⌉`, `nb + 8` the
count `J`; scalars `sb +`: `0` `0`, `1` `1/2`, `2` `1`, `3` `m`, `4` `w`, `5` `R₀`, `6` `c₀`, `7` `1/c₀`, `8`, `9`
temporaries, `10` the Frobenius norm, `11` the clip factor, `12` the accumulator of the products, `13` `m - c`, `14`
`3`, `15` `-1/2`, `16` `-1`, `17` the real argument of a ceiling, `18` its temporary. In `pgUpdNS`, `nb = n0`,
`sb = s0`, and the arrays are `a0 + 5` to `a0 + 9` and `a0 + 11` to `a0 + 13`: all inside the frame of the step
`pgStep` of PG.
-/

namespace AdversarialBco.Conj1Arith

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  AdversarialBco.Poly.PG

/-! ## CLAMP-NS -/

open SI in
/-- `0`, `1/2`, `1`, `m = (a + b)/2`, `w = (b - a)/2`, `R₀ = d^{1/2} w`, `c₀ = R₀ + w`, `1/c₀`, `3`, `-1/2`, `-1`. -/
def nsParL (sb a b dR : ℕ) : List SI :=
  [const sb 0, const (sb + 1) (1 / 2), const (sb + 2) 1, op2 .add (sb + 3) a b, op2 .mul (sb + 3) (sb + 3) (sb + 1),
    op2 .sub (sb + 4) b a, op2 .mul (sb + 4) (sb + 4) (sb + 1), op1 .sqrt (sb + 5) dR,
    op2 .mul (sb + 5) (sb + 5) (sb + 4), op2 .add (sb + 6) (sb + 5) (sb + 4), op2 .div (sb + 7) (sb + 2) (sb + 6),
    const (sb + 14) 3, const (sb + 15) (-1 / 2), const (sb + 16) (-1)]

open SI in
/-- `log₂ (c₀/(2e))` into `sb + 17`. -/
def nsKL (sb e : ℕ) : List SI :=
  [op2 .add (sb + 17) e e, op2 .div (sb + 17) (sb + 6) (sb + 17), op1 .log (sb + 17) (sb + 17), const (sb + 18) 2,
    op1 .log (sb + 18) (sb + 18), op2 .div (sb + 17) (sb + 17) (sb + 18)]

open SI in
/-- `log₂ (3k + 3)` into `sb + 17`, `k` the natural `kv`. -/
def nsCL (sb kv : ℕ) : List SI :=
  [cast (sb + 17) kv, const (sb + 18) 3, op2 .mul (sb + 17) (sb + 18) (sb + 17), op2 .add (sb + 17) (sb + 17) (sb + 18),
    op1 .log (sb + 17) (sb + 17), const (sb + 18) 2, op1 .log (sb + 18) (sb + 18),
    op2 .div (sb + 17) (sb + 17) (sb + 18)]

/-- The counts: `k := ⌈log₂ (c₀/(2e))⌉₊` in `nb + 6`, `⌈log₂ (3k + 3)⌉₊` in `nb + 7`, `J := 2k + ⌈log₂ (3k + 3)⌉₊`
in `nb + 8`. -/
def nsCountC (L : Layout) (one nb sb e : ℕ) : Cmd :=
  .seq (sprog L (nsKL sb e)) (.seq (nceil L (nb + 6) one (sb + 17) (sb + 18))
    (.seq (sprog L (nsCL sb (nb + 6))) (.seq (nceil L (nb + 7) one (sb + 17) (sb + 18))
      (.seq (nadd (nb + 8) (nb + 6) (nb + 6)) (nadd (nb + 8) (nb + 8) (nb + 7))))))

/-- `W := sym Y - m I` (`X2`, `I3` work arrays). -/
def nsSymC (L : Layout) (dv one dd nb sb Y W X2 I3 : ℕ) : Cmd :=
  .seq (mtransp L dv one nb (nb + 1) (nb + 2) (nb + 3) X2 Y (sb + 8))
    (.seq (mlin L dd one nb W Y X2 (sb + 1) (sb + 1) (sb + 8) (sb + 9))
      (.seq (mfill L dd one nb I3 sb) (.seq (mdiag L dv one nb (nb + 1) I3 (sb + 3))
        (mlin L dd one nb W W I3 (sb + 2) (sb + 16) (sb + 8) (sb + 9)))))

/-- `W := clip_{R₀} W` in the Frobenius norm, the norm as `(tr (W W))^{1/2}` (`X2` work array). -/
def nsClipC (L : Layout) (dv one dd nb sb W X2 : ℕ) : Cmd :=
  .seq (mmul L dv one nb (nb + 1) (nb + 2) (nb + 3) (nb + 4) (nb + 5) X2 W W (sb + 12) (sb + 8) (sb + 9))
    (.seq (mtrace L dv one nb (nb + 1) (sb + 10) X2 (sb + 8)) (.seq (sop1 L .sqrt (sb + 10) (sb + 10))
      (ifS L (sb + 5) (sb + 10)
        (.seq (sop2 L .div (sb + 11) (sb + 5) (sb + 10)) (mlin L dd one nb W W W (sb + 11) sb (sb + 8) (sb + 9)))
        .skip)))

/-- One Newton-Schulz step `X := X (3 I - X²)/2` (`I3` holds `3 I`; `X2`, `X3` work arrays). -/
def nsStepC (L : Layout) (dv one dd nb sb X X2 X3 I3 : ℕ) : Cmd :=
  .seq (mmul L dv one nb (nb + 1) (nb + 2) (nb + 3) (nb + 4) (nb + 5) X2 X X (sb + 12) (sb + 8) (sb + 9))
    (.seq (mlin L dd one nb X2 I3 X2 (sb + 2) (sb + 16) (sb + 8) (sb + 9))
      (.seq (mmul L dv one nb (nb + 1) (nb + 2) (nb + 3) (nb + 4) (nb + 5) X3 X X2 (sb + 12) (sb + 8) (sb + 9))
        (mlin L dd one nb X X3 X3 (sb + 1) sb (sb + 8) (sb + 9))))

/-- `J` Newton-Schulz steps (`J` in `nb + 8`, index `nb + 6`). -/
def nsLoopC (L : Layout) (dv one dd nb sb X X2 X3 I3 : ℕ) : Cmd :=
  forN (nb + 6) (nb + 8) one (nsStepC L dv one dd nb sb X X2 X3 I3)

/-- One root: `M := W + (m - c) I` (`m - c` in `sb + 13`), `X := M/c₀`, `J` steps, `out := M X`. -/
def nsRootC (L : Layout) (dv one dd nb sb W M X X2 X3 I3 out : ℕ) : Cmd :=
  .seq (mfill L dd one nb I3 sb) (.seq (mdiag L dv one nb (nb + 1) I3 (sb + 13))
    (.seq (mlin L dd one nb M W I3 (sb + 2) (sb + 2) (sb + 8) (sb + 9))
      (.seq (mlin L dd one nb X M M (sb + 7) sb (sb + 8) (sb + 9))
        (.seq (mfill L dd one nb I3 sb) (.seq (mdiag L dv one nb (nb + 1) I3 (sb + 14))
          (.seq (nsLoopC L dv one dd nb sb X X2 X3 I3)
            (mmul L dv one nb (nb + 1) (nb + 2) (nb + 3) (nb + 4) (nb + 5) out M X (sb + 12) (sb + 8) (sb + 9))))))))

/-- `Y := m I + (Y^a - Y^b)/2`. -/
def nsOutC (L : Layout) (dv one dd nb sb Y Ya Yb : ℕ) : Cmd :=
  .seq (mfill L dd one nb Y sb) (.seq (mdiag L dv one nb (nb + 1) Y (sb + 3))
    (.seq (mlin L dd one nb Y Y Ya (sb + 2) (sb + 1) (sb + 8) (sb + 9))
      (mlin L dd one nb Y Y Yb (sb + 2) (sb + 15) (sb + 8) (sb + 9))))

open SI in
/-- CLAMP-NS on the array `Y`, at the bounds `a`, `b`, the tolerance `e` and `d` as a real (`dR`). -/
def clampNSC (L : Layout) (dv one dd nb sb Y W M X X2 X3 I3 Ya Yb a b e dR : ℕ) : Cmd :=
  .seq (sprog L (nsParL sb a b dR)) (.seq (nsCountC L one nb sb e)
    (.seq (nsSymC L dv one dd nb sb Y W X2 I3) (.seq (nsClipC L dv one dd nb sb W X2)
      (.seq (sprog L [op2 .sub (sb + 13) (sb + 3) a, op2 .sub (sb + 13) (sb + 13) e])
        (.seq (nsRootC L dv one dd nb sb W M X X2 X3 I3 Ya)
          (.seq (sprog L [op2 .sub (sb + 13) (sb + 3) b, op2 .add (sb + 13) (sb + 13) e])
            (.seq (nsRootC L dv one dd nb sb W M X X2 X3 I3 Yb) (nsOutC L dv one dd nb sb Y Ya Yb))))))))

/-! ## The step of the descent -/

open SI in
/-- `e' = e_h/(10⁶ G N^{1/2})/(2 d^{1/2})` into `s0 + 36`, from `ρ`, `t_min`, `t_max`, `d` and `N`, with `λ² =
2 log (1 + ρ)`, `e_h = (1/64)/(922 d² λ² L_D)` and `G² = (5 L_D² d (d + 2)(d + 5) + 1/(32 d))/t_min²` as in parts A
and B of the stage parameters. -/
def pgEprL (n0 s0 : ℕ) : List SI :=
  [const (s0 + 3) 1, op2 .add (s0 + 3) (s0 + 3) (s0 + 19), op1 .log (s0 + 3) (s0 + 3), const (s0 + 4) 2,
    op2 .mul (s0 + 3) (s0 + 4) (s0 + 3),
    const (s0 + 4) 922, op2 .mul (s0 + 4) (s0 + 4) (s0 + 48), op2 .mul (s0 + 4) (s0 + 4) (s0 + 48),
    op2 .mul (s0 + 4) (s0 + 4) (s0 + 3), op2 .mul (s0 + 4) (s0 + 4) (s0 + 22), const (s0 + 5) (1 / 64),
    op2 .div (s0 + 4) (s0 + 5) (s0 + 4),
    op2 .mul (s0 + 5) (s0 + 22) (s0 + 22), const (s0 + 6) 5, op2 .mul (s0 + 5) (s0 + 6) (s0 + 5),
    op2 .mul (s0 + 5) (s0 + 5) (s0 + 48), const (s0 + 6) 2, op2 .add (s0 + 6) (s0 + 48) (s0 + 6),
    op2 .mul (s0 + 5) (s0 + 5) (s0 + 6), const (s0 + 6) 5, op2 .add (s0 + 6) (s0 + 48) (s0 + 6),
    op2 .mul (s0 + 5) (s0 + 5) (s0 + 6), const (s0 + 6) (1 / 32), op2 .div (s0 + 6) (s0 + 6) (s0 + 48),
    op2 .add (s0 + 5) (s0 + 5) (s0 + 6), op2 .mul (s0 + 6) (s0 + 21) (s0 + 21), op2 .div (s0 + 5) (s0 + 5) (s0 + 6),
    op1 .sqrt (s0 + 5) (s0 + 5), const (s0 + 6) 1000000, op2 .mul (s0 + 5) (s0 + 6) (s0 + 5), cast (s0 + 6) (n0 + 11),
    op1 .sqrt (s0 + 6) (s0 + 6), op2 .mul (s0 + 5) (s0 + 5) (s0 + 6), op2 .div (s0 + 4) (s0 + 4) (s0 + 5),
    op1 .sqrt (s0 + 6) (s0 + 48), const (s0 + 7) 2, op2 .mul (s0 + 6) (s0 + 7) (s0 + 6),
    op2 .div (s0 + 36) (s0 + 4) (s0 + 6)]

/-- The move and the projection with CLAMP-NS: `pgUpd` with the `spec` clamp replaced by `pgEprL` and `clampNSC`. -/
def pgUpdNS (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (vaxpy L dv one n0 a0 (a0 + 10) (s0 + 30) (s0 + 8) (s0 + 9))
    (.seq (sconst L (s0 + 2) 1)
      (.seq (mlin L (n0 + 9) one n0 (a0 + 1) (a0 + 1) (a0 + 14) (s0 + 2) (s0 + 30) (s0 + 8) (s0 + 9))
        (.seq (vnorm L dv one n0 (s0 + 34) a0 (s0 + 8) (s0 + 9))
          (.seq (ifS L (s0 + 23) (s0 + 34)
              (.seq (sop2 L .div (s0 + 35) (s0 + 23) (s0 + 34)) (vscale L dv one n0 a0 (s0 + 35) (s0 + 8))) .skip)
            (.seq (sprog L (pgEprL n0 s0))
              (clampNSC L dv one (n0 + 9) n0 s0 (a0 + 1) (a0 + 5) (a0 + 6) (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11)
                (a0 + 12) (a0 + 13) (s0 + 21) (s0 + 22) (s0 + 36) (s0 + 48)))))))

/-- One step of the descent, with `pgUpdNS`. -/
def pgStepNS (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L (s0 + 2) 1)
    (.seq (vaxpy L dv one n0 (a0 + 2) a0 (s0 + 2) (s0 + 8) (s0 + 9))
      (.seq (mlin L (n0 + 9) one n0 (a0 + 3) (a0 + 3) (a0 + 1) (s0 + 2) (s0 + 2) (s0 + 8) (s0 + 9))
        (.seq (vgauss L dv one n0 (a0 + 4) (s0 + 8))
          (.seq (pgGauge L dv one n0 s0 a0 muv Av a0 (a0 + 1))
            (.seq (pgVinv L dv one n0 s0 a0) (.seq (pgVmat L dv one n0 s0 a0) (pgUpdNS L dv one n0 s0 a0)))))))

/-- The descent, with `pgStepNS`. -/
def pgDescNS (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L s0 0)
    (.seq (vfill L dv one n0 a0 s0) (.seq (mfill L (n0 + 9) one n0 (a0 + 1) s0)
      (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 1) (s0 + 21))
        (.seq (vfill L dv one n0 (a0 + 2) s0) (.seq (mfill L (n0 + 9) one n0 (a0 + 3) s0)
          (.seq (forN (n0 + 13) (n0 + 11) one (pgStepNS L dv one n0 s0 a0 muv Av))
            (.seq (sconst L (s0 + 2) 1) (.seq (ncast L (s0 + 45) (n0 + 11))
              (.seq (sop2 L .div (s0 + 33) (s0 + 2) (s0 + 45)) (.seq (sconst L s0 0)
                (.seq (vscale L dv one n0 (a0 + 2) (s0 + 33) (s0 + 8))
                  (mlin L (n0 + 9) one n0 (a0 + 3) (a0 + 3) (a0 + 3) (s0 + 33) s0 (s0 + 8) (s0 + 9)))))))))))))

/-! ## The verdict -/

/-- The pivot `k` of Gauss-Jordan elimination with its test: `q := A[d k + k]`, `v := 0` unless `0 < q` (`z` holds
`0`), then `gjPivot`. -/
def gjPivotT (L : Layout) (dv one i j kk ri rk ij kj A B p ip o f t1 t2 z v q : ℕ) : Cmd :=
  .seq (nadd ij rk kk) (.seq (aget L q A ij) (.seq (ifS L z q .skip (sconst L v 0))
    (gjPivot L dv one i j kk ri rk ij kj A B p ip o f t1 t2)))

/-- The third clause of a basic verdict by the pivots: `a0 + 18 := Q̂ - c I` (`c = (5/8) κ/d = (-5/8)(-κ/d)`),
`a0 + 17 := I`, then Gauss-Jordan elimination on the pair with the test of each pivot, which clears the verdict
`s0 + 39` at a pivot `≤ 0`. -/
def pgVerdC3P (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1) (.seq (sconst L (s0 + 47) (-5 / 8))
    (.seq (sop2 L .mul (s0 + 51) (s0 + 47) (s0 + 32))
      (.seq (mfill L (n0 + 9) one n0 (a0 + 17) s0) (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 17) (s0 + 51))
        (.seq (sconst L (s0 + 36) (-1))
          (.seq (mlin L (n0 + 9) one n0 (a0 + 18) (a0 + 16) (a0 + 17) (s0 + 2) (s0 + 36) (s0 + 8) (s0 + 9))
            (.seq (mfill L (n0 + 9) one n0 (a0 + 17) s0) (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 17) (s0 + 2))
              (.seq (nconst (n0 + 5) 0)
                (forN (n0 + 2) dv one (gjPivotT L dv one n0 (n0 + 1) (n0 + 2) (n0 + 4) (n0 + 5) (n0 + 6) (n0 + 7)
                  (a0 + 18) (a0 + 17) (s0 + 12) (s0 + 13) (s0 + 2) (s0 + 14) (s0 + 8) (s0 + 9) s0 (s0 + 39)
                  (s0 + 10)))))))))))))

/-- One basic verdict, with `pgVerdC3P`. -/
def pgVerdNS (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 37) 0) (.seq (vfill L dv one n0 (a0 + 15) s0)
    (.seq (mfill L (n0 + 9) one n0 (a0 + 16) s0)
      (.seq (forN (n0 + 13) (n0 + 12) one (pgSample L dv one n0 s0 a0 muv Av))
        (.seq (pgVerdNorm L dv one n0 s0 a0) (.seq (pgVerdC12 L dv one n0 s0 a0)
          (.seq (pgVerdC3P L dv one n0 s0 a0) (sop2 L .add (s0 + 40) (s0 + 40) (s0 + 39)))))))))

/-- The amplified test, with `pgVerdNS`. -/
def pgTestCNS (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L (s0 + 40) 0) (.seq (forN (n0 + 15) (n0 + 14) one (pgVerdNS L dv one n0 s0 a0 muv Av))
    (.seq (ncast L (s0 + 45) (n0 + 14)) (.seq (sconst L (s0 + 1) (1 / 2))
      (.seq (sop2 L .mul (s0 + 45) (s0 + 45) (s0 + 1))
        (.seq (sconst L (s0 + 49) 0) (ifS L (s0 + 45) (s0 + 40) (sconst L (s0 + 49) 1) .skip))))))

/-! ## The repeats, the stages and the code -/

/-- One repeat, with `pgDescNS` and `pgTestCNS`. -/
def pgRepNS (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (pgDescNS L dv one n0 s0 a0 muv Av) (.seq (pgTestCNS L dv one n0 s0 a0 muv Av)
    (.seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1)
      (ifS L (s0 + 41) (s0 + 2)
        (ifS L s0 (s0 + 49) (.seq (sconst L (s0 + 41) 1)
          (.seq (vcopy L dv one n0 (a0 + 19) (a0 + 2) (s0 + 8)) (mcopy L (n0 + 9) one n0 (a0 + 20) (a0 + 3) (s0 + 8))))
          .skip)
        .skip))))

/-- One stage, with `pgRepNS`. -/
def pgStageCNS (L : Layout) (dv one okv muv Av n0 s0 a0 : ℕ) : Cmd :=
  .seq (pgParA L s0) (.seq (pgParB L s0) (.seq (pgParC1 L one n0 s0) (.seq (pgParC2 L one n0 s0)
    (.seq (sconst L (s0 + 41) 0) (.seq (forN (n0 + 17) (n0 + 16) one (pgRepNS L dv one n0 s0 a0 muv Av))
      (.seq (sconst L s0 0)
        (ifS L s0 (s0 + 41) (pgCompC L dv one n0 s0 a0 muv Av) (sconst L okv 0))))))))

/-- Procedure PG-N with CLAMP-NS: the caps `pgCaps`, the initial centre and matrix, then the stages `pgStageCNS`, each
followed by `pgRho`. -/
def pgCodeNS (L : Layout) (dv one r0v R0v δv okv muv Av n0 s0 a0 : ℕ) : Cmd :=
  .seq (pgCaps L dv one r0v R0v δv n0 s0)
    (.seq (sconst L okv 1) (.seq (sconst L s0 0) (.seq (vfill L dv one n0 muv s0)
      (.seq (mfill L (n0 + 9) one n0 Av s0) (.seq (mdiag L dv one n0 (n0 + 2) Av r0v)
        (.seq (sconst L (s0 + 19) 2) (.seq (sop2 L .add (s0 + 42) r0v r0v)
          (forN (n0 + 19) (n0 + 18) one (.seq (pgStageCNS L dv one okv muv Av n0 s0 a0) (pgRho L s0))))))))))

/-! ## Step counts -/

/-- The step counts of the matrix macros. -/
def kMtransp (d : ℕ) : ℕ := d * (d * 9 + 8) + 4
def kMlin (d : ℕ) : ℕ := d * d * 12 + 3
def kMfill (d : ℕ) : ℕ := d * d * 5 + 3
def kMdiag (d : ℕ) : ℕ := d * 7 + 4
def kMmul (d : ℕ) : ℕ := d * (d * (d * 11 + 12) + 6) + 4
def kMtrace (d : ℕ) : ℕ := d * 8 + 5

/-- `nsCountC` at the counts `k` and `c = ⌈log₂ (3k + 3)⌉₊`. -/
def kNsCount (k c : ℕ) : ℕ := 6 + ((k * 4 + 4) + (8 + ((c * 4 + 4) + (1 + 1))))

def kNsSym (d : ℕ) : ℕ := kMtransp d + (kMlin d + (kMfill d + (kMdiag d + kMlin d)))

def kNsClip (d : ℕ) : ℕ := kMmul d + (kMtrace d + (1 + (kMlin d + 2)))

def kNsStep (d : ℕ) : ℕ := kMmul d + (kMlin d + (kMmul d + kMlin d))

def kNsLoop (d J : ℕ) : ℕ := J * (kNsStep d + 3) + 3

def kNsRoot (d J : ℕ) : ℕ :=
  kMfill d + (kMdiag d + (kMlin d + (kMlin d + (kMfill d + (kMdiag d + (kNsLoop d J + kMmul d))))))

def kNsOut (d : ℕ) : ℕ := kMfill d + (kMdiag d + (kMlin d + kMlin d))

/-- CLAMP-NS at the counts `k`, `c` and `J = 2k + c`. -/
def kClampNS (d k c J : ℕ) : ℕ :=
  14 + (kNsCount k c + (kNsSym d + (kNsClip d + (2 + (kNsRoot d J + (2 + (kNsRoot d J + kNsOut d)))))))

def kUpdNS (d k c J : ℕ) : ℕ := d * 11 + 3 + (1 + (d * d * 12 + 3 + (d * 9 + 5 + (d * 8 + 5 + (38 + kClampNS d k c J)))))

def kStepNS (d jb k c J : ℕ) : ℕ :=
  1 + (d * 11 + 3 + (d * d * 12 + 3 + (d * 6 + 3 + (kGauge d jb + (kVinv d + (kVmat d + kUpdNS d k c J))))))

def kDescNS (d jb N k c J : ℕ) : ℕ :=
  1 + (d * 5 + 3 + (d * d * 5 + 3 + (d * 7 + 4 + (d * 5 + 3 + (d * d * 5 + 3 + (N * (kStepNS d jb k c J + 3) + 3 +
    (1 + (1 + (1 + (1 + (d * 8 + 3 + (d * d * 12 + 3))))))))))))

/-- One pivot with its test. -/
def kPivT (d : ℕ) : ℕ := 1 + (2 + (3 + (d * d * 21 + d * 31 + 14)))

def kVerdC3P (d : ℕ) : ℕ :=
  1 + (1 + (1 + (1 + (kMfill d + (kMdiag d + (1 + (kMlin d + (kMfill d + (kMdiag d + (1 +
    (d * (kPivT d + 3) + 3)))))))))))

def kVerdNS (d jb nT : ℕ) : ℕ :=
  1 + (1 + (d * 5 + 3 + (d * d * 5 + 3 + (nT * (kSample d jb + 3) + 3 + (kVerdNorm d + (kVerdC12 d +
    (kVerdC3P d + 1)))))))

def kTestNS (d jb nT mT : ℕ) : ℕ := 1 + (mT * (kVerdNS d jb nT + 3) + 3 + (1 + (1 + (1 + (1 + 2)))))

def kRepNS (d jb N nT mT k c J : ℕ) : ℕ :=
  kDescNS d jb N k c J + (kTestNS d jb nT mT + (1 + (1 + (1 + (d * 7 + 3 + (d * d * 7 + 3)) + 1 + 1))))

def kStageNS (d jb N nT Jr mT k c J : ℕ) : ℕ :=
  22 + (36 + (nT * 4 + 28 + (N * 4 + jb * 4 + 26 + (1 + (Jr * (kRepNS d jb N nT mT k c J + 3) + 3 +
    (1 + (kCompC d + 1)))))))

/-- The count `k` of CLAMP-NS at the ratio `ρ`. -/
noncomputable def nsK (d : ℕ) (ρ : ℝ) : ℕ := cnK d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ)

/-- The step count of a stage at the ratio `ρ`. -/
noncomputable def kStageAt (d : ℕ) (ρ δ' : ℝ) : ℕ :=
  kStageNS d (pgJb d ρ) (pgNs d ρ) (pgNT d ρ) (pgJr δ') (pgMT δ') (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3))
    (nsCount (nsK d ρ))

/-- The step count of one stage and the next ratio, the largest over the stages. -/
noncomputable def kPGStageNS (d : ℕ) (r0 R0 δ₁ : ℝ) : ℕ :=
  (Finset.range (pgStages r0 R0)).sup fun i => kStageAt d (pgRhoStage d i) (δ₁ / pgStages r0 R0) + 8

/-- The step count of the code of PG-N. -/
noncomputable def kPGNS (d : ℕ) (r0 R0 δ₁ : ℝ) : ℕ :=
  kCaps d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0)) +
    (1 + (1 + (d * 5 + 3 + (d * d * 5 + 3 + (d * 7 + 4 +
      (1 + (1 + (pgStages r0 R0 * (kPGStageNS d r0 R0 δ₁ + 3) + 3))))))))

end AdversarialBco.Conj1Arith
