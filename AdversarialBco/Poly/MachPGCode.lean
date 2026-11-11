/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachSI

@[expose] public section

/-!
# Procedure PG in VL: the code and its mathematical companions

Definitions only; the rules are in `MachPG.lean`.

* Gauss-Jordan elimination without pivoting: `gjStep` (one pivot, on the pair `(A, B)`), `gjRun T k` (the pivots
  `0, ..., k - 1` from `(T, 1)`), `GjInv` (the invariant of the proof that `(gjRun T d).2 = T⁻¹` for a positive
  definite `T`); the code `gjCode` (`B := T⁻¹` through the work array `A`) and its parts `gjScale` (row `k` times the
  inverse pivot), `gjElimRow` (row `i` minus a multiple of row `k`), `gjElim`, `gjElimAll`, `gjPivot`.
* `ballClip R μ`: the radial clip of `μ` to the closed ball of radius `R` (the vector part of the projection on `D`).
-/

namespace AdversarialBco.Poly.PG

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

/-! ## Gauss-Jordan elimination without pivoting -/

/-- One step of Gauss-Jordan elimination without pivoting on the pair `(A, B)` at the pivot `k`: row `k` times
`1 / A k k`, then `A i k` times the new row `k` subtracted from every other row `i`, in `A` and `B` alike. -/
noncomputable def gjStep {d : ℕ} (k : Fin d)
    (AB : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.of fun i j =>
      if i = k then AB.1 k j * (1 / AB.1 k k) else AB.1 i j - AB.1 i k * (AB.1 k j * (1 / AB.1 k k)),
    Matrix.of fun i j =>
      if i = k then AB.2 k j * (1 / AB.1 k k) else AB.2 i j - AB.1 i k * (AB.2 k j * (1 / AB.1 k k)))

/-- The pivots `0, ..., k - 1` of Gauss-Jordan elimination from `(T, 1)`. -/
noncomputable def gjRun {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ
  | 0 => (T, 1)
  | k + 1 => if h : k < d then gjStep ⟨k, h⟩ (gjRun T k) else gjRun T k

/-- The invariant after the pivots `0, ..., k - 1`: `A = B T`, the columns `j < k` of `A` and the columns `j ≥ k` of
`B` are those of the identity. -/
def GjInv {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (AB : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) : Prop :=
  AB.1 = AB.2 * T ∧ (∀ i j : Fin d, (j : ℕ) < k → AB.1 i j = if i = j then 1 else 0) ∧
    (∀ i j : Fin d, k ≤ (j : ℕ) → AB.2 i j = if i = j then 1 else 0)

/-- Row `k` of `A` and of `B` times `ip`: the index `kj` runs from `d k` over the row. -/
def gjScale (L : Layout) (dv one j kj A B ip t : ℕ) : Cmd :=
  forN j dv one (.seq (aget L t A kj) (.seq (sop2 L .mul t t ip) (.seq (aset L A kj t)
    (.seq (aget L t B kj) (.seq (sop2 L .mul t t ip) (.seq (aset L B kj t) (nadd kj kj one)))))))

/-- Row `i` minus `f` times row `k`, in `A` and in `B`: the index `ij` runs from `d i`, `kj` from `d k`. -/
def gjElimRow (L : Layout) (dv one j ij kj A B f t1 t2 : ℕ) : Cmd :=
  forN j dv one (.seq (aget L t1 A kj) (.seq (sop2 L .mul t1 f t1) (.seq (aget L t2 A ij)
    (.seq (sop2 L .sub t2 t2 t1) (.seq (aset L A ij t2) (.seq (aget L t1 B kj) (.seq (sop2 L .mul t1 f t1)
      (.seq (aget L t2 B ij) (.seq (sop2 L .sub t2 t2 t1) (.seq (aset L B ij t2)
        (.seq (nadd ij ij one) (nadd kj kj one))))))))))))

/-- The elimination of row `i` (`ri` holds `d i`) at the pivot `k` (`kk` holds `k`, `rk` holds `d k`):
`f := A[d i + k]`, then `gjElimRow`. -/
def gjElim (L : Layout) (dv one j ri rk kk ij kj A B f t1 t2 : ℕ) : Cmd :=
  .seq (nadd ij ri kk) (.seq (aget L f A ij) (.seq (nconst ij 0) (.seq (nadd ij ij ri) (.seq (nconst kj 0)
    (.seq (nadd kj kj rk) (gjElimRow L dv one j ij kj A B f t1 t2))))))

/-- The elimination of every row `i ≠ k`. -/
def gjElimAll (L : Layout) (dv one i j kk ri rk ij kj A B f t1 t2 : ℕ) : Cmd :=
  .seq (nconst ri 0) (forN i dv one (.seq (.ifN i kk (gjElim L dv one j ri rk kk ij kj A B f t1 t2)
    (.ifN kk i (gjElim L dv one j ri rk kk ij kj A B f t1 t2) .skip)) (nadd ri ri dv)))

/-- The pivot `k` (`kk` holds `k`, `rk` holds `d k`, `o` holds `1`): `p := A[d k + k]`, `ip := 1 / p`, row `k`
scaled, the other rows eliminated, `rk := rk + d`. -/
def gjPivot (L : Layout) (dv one i j kk ri rk ij kj A B p ip o f t1 t2 : ℕ) : Cmd :=
  .seq (nadd ij rk kk) (.seq (aget L p A ij) (.seq (sop2 L .div ip o p) (.seq (nconst kj 0) (.seq (nadd kj kj rk)
    (.seq (gjScale L dv one j kj A B ip t1) (.seq (gjElimAll L dv one i j kk ri rk ij kj A B f t1 t2)
      (nadd rk rk dv)))))))

/-- `B := T⁻¹` by Gauss-Jordan elimination without pivoting (`dd` holds `d²`): `o := 1`, `z := 0`, `A := T`,
`B := 1`, then the pivots `k < d`. -/
def gjCode (L : Layout) (dv one dd i j kk ri rk ij kj T A B p ip o z f t1 t2 : ℕ) : Cmd :=
  .seq (sconst L o 1) (.seq (sconst L z 0) (.seq (mcopy L dd one j A T t1) (.seq (mfill L dd one j B z)
    (.seq (mdiag L dv one i kj B o) (.seq (nconst rk 0)
      (forN kk dv one (gjPivot L dv one i j kk ri rk ij kj A B p ip o f t1 t2)))))))

/-! ## The projection on `D` -/

/-- The radial clip of `μ` to the closed ball of radius `R`. -/
noncomputable def ballClip {d : ℕ} (R : ℝ) (μ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if R < ‖μ‖ then (R / ‖μ‖) • μ else μ

/-! ## The layout of PG

The code of PG takes the caller's variables `dv` (`d`), `one` (`1`), `r0v`, `R0v`, `δv` (`r₀`, `R₀`, `δ₁`), `okv`
(the flag), `muv`, `Av` (the position), and three bases `n0`, `s0`, `a0`: its own variables are `n0 + k` (`k < 20`),
`s0 + k` (`k < 64`), `a0 + k` (`k < 32`).

Naturals `n0 +`: `0` `i`, `1` `j`, `2` `k`, `3` `l`, `4` `ri`, `5` `rk`, `6` `ij`, `7` `kj` (the indices of the
macros), `8` `jj` (bisection), `9` `dd` (`d²`), `10` `jb` (`pgJb`), `11` `N` (`pgNs`), `12` `nT` (`pgNT`), `13` the
descent and sample index, `14` `mT` (`pgMT`), `15` the verdict index, `16` `J` (`pgJr`), `17` the repeat index,
`18` `m` (`pgStages`), `19` the stage index.

Scalars `s0 +`: `0` `0`, `1` `1/2`, `2` `1`, `3` to `7` the bisection (`nx`, `sl`, `su`, `mid`, `inv`), `8` to
`10` temporaries, `11` `s` of the products, `12` `p`, `13` `ip`, `14` `f` (Gauss-Jordan), `15` `qo` (the answer of
the body), `16` `c`, `17` `nt` (the body), `18` `F` (the gauge), `19` `ρ`, `20` `λ`, `21` `t_min`, `22` `t_max`,
`23` `κρ`, `24` `Δ`, `25` `G²`, `26` `e_h`, `27` `η`, `28` `τ_b`, `29` `s` (the step), `30` `-s`, `31` `F/2`,
`32` `-κ/d`, `33` `1/N`, `34` `|μ|`, `35` the clip factor, `36` `-1`, `37` `k̂`, `38` `|b̂|`, `39` the verdict,
`40` the count of verdicts, `41` the flag of a found repeat, `42` the radius `2^{i+1} r₀`, `43` `δ' = δ₁/m`,
`44` the trace, `45` to `47` temporaries, `48` `d` as a real, `49` the test, `50` a temporary, `51` `(5/8) κ/d`.

Arrays `a0 +`: `0` `μ`, `1` `T` (the iterate), `2`, `3` the sums, then the average, `4` `g`, `5` `μ + T g`, `6` the
point asked to the body, `7` `μ_P + A y`, `8` `T⁻¹`, `9` the work array of Gauss-Jordan, `10` the `μ` part of `V`,
`11` `g gᵀ - I`, `12` `T⁻¹ (g gᵀ - I)`, `13` its transpose, `14` the `T` part of `V`, `15` `b̂`, `16` `Q̂`,
`17` `c I - Q̂`, `18` its step, `19`, `20` the kept average, `21`, `22` the composed position.
-/

/-- The body of the current stage, `posBody (K ∩ B̄(0, rad)) μ A` (`μ`, `A` in `muv`, `Av`): `qo := 1` if
`μ + A y ∈ K` and `|μ + A y| ≤ rad` (`y` the array `a0 + 6`), else `0`. -/
def pgMemQ (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (memAff L dv one n0 (n0 + 1) (n0 + 2) (s0 + 15) muv Av (a0 + 6) (a0 + 7) (s0 + 16) (s0 + 11) (s0 + 8)
      (s0 + 9))
    (.seq (vnorm L dv one n0 (s0 + 17) (a0 + 7) (s0 + 8) (s0 + 9))
      (ifS L (s0 + 42) (s0 + 17) (sconst L (s0 + 15) 0) .skip))

/-- The gauge `F := π̃(μ + T g)` of the body of the stage, at the point `(μ, T)` held in `xm`, `xT`, with `g` in
`a0 + 4`: `a0 + 5 := T g + μ`, then the bisection of `gaugeBis` with `jb` steps. -/
def pgGauge (L : Layout) (dv one n0 s0 a0 muv Av xm xT : ℕ) : Cmd :=
  .seq (matvec L dv one n0 (n0 + 1) (n0 + 2) (a0 + 5) xT (a0 + 4) (s0 + 11) (s0 + 8) (s0 + 9))
    (.seq (sconst L (s0 + 2) 1) (.seq (vaxpy L dv one n0 (a0 + 5) xm (s0 + 2) (s0 + 8) (s0 + 9))
      (gaugeBis L (pgMemQ L dv one n0 s0 a0 muv Av) dv one n0 (n0 + 8) (n0 + 10) (a0 + 5) (a0 + 6) (s0 + 19)
        (s0 + 15) (s0 + 18) (s0 + 3) (s0 + 4) (s0 + 5) (s0 + 6) (s0 + 7) s0 (s0 + 1) (s0 + 2) (s0 + 8)
        (s0 + 9))))

/-- `a0 + 11 := g gᵀ - I`. -/
def pgGGcode (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1) (.seq (sconst L (s0 + 36) (-1))
    (.seq (mfill L (n0 + 9) one n0 (a0 + 11) s0) (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 11) (s0 + 36))
      (rankOne L dv one n0 (n0 + 1) (n0 + 2) (a0 + 11) (s0 + 2) (s0 + 2) (a0 + 4) (a0 + 4) (s0 + 8) (s0 + 9)
        (s0 + 10))))))

/-- `a0 + 8 := T⁻¹` (Gauss-Jordan on the iterate `a0 + 1`), then the `μ` part of `V`: `a0 + 10 := F T⁻¹ g`. -/
def pgVinv (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (gjCode L dv one (n0 + 9) n0 (n0 + 1) (n0 + 2) (n0 + 4) (n0 + 5) (n0 + 6) (n0 + 7) (a0 + 1) (a0 + 9) (a0 + 8)
      (s0 + 12) (s0 + 13) (s0 + 2) s0 (s0 + 14) (s0 + 8) (s0 + 9))
    (.seq (matvec L dv one n0 (n0 + 1) (n0 + 2) (a0 + 10) (a0 + 8) (a0 + 4) (s0 + 11) (s0 + 8) (s0 + 9))
      (vscale L dv one n0 (a0 + 10) (s0 + 18) (s0 + 8)))

/-- The `T` part of `V`: `a0 + 14 := (F/2) (M + Mᵀ) + (-κ/d) T⁻¹` with `M = T⁻¹ (g gᵀ - I)`. -/
def pgVmat (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (pgGGcode L dv one n0 s0 a0)
    (.seq (mmul L dv one n0 (n0 + 1) (n0 + 3) (n0 + 4) (n0 + 5) (n0 + 6) (a0 + 12) (a0 + 8) (a0 + 11) (s0 + 11)
        (s0 + 8) (s0 + 9))
      (.seq (mtransp L dv one n0 (n0 + 1) (n0 + 4) (n0 + 5) (a0 + 13) (a0 + 12) (s0 + 8))
        (.seq (sconst L (s0 + 1) (1 / 2)) (.seq (sop2 L .mul (s0 + 31) (s0 + 18) (s0 + 1))
          (.seq (mlin L (n0 + 9) one n0 (a0 + 14) (a0 + 12) (a0 + 13) (s0 + 31) (s0 + 31) (s0 + 8) (s0 + 9))
            (mlin L (n0 + 9) one n0 (a0 + 14) (a0 + 14) (a0 + 8) (s0 + 2) (s0 + 32) (s0 + 8) (s0 + 9)))))))

/-- The descent move and the projection on `D`: `μ := μ - s V_μ`, `T := T - s V_T`, then `μ` clipped to the ball
of radius `κρ` and `T := clamp_{[t_min, t_max]} (sym T)` (one `spec` instruction). -/
def pgUpd (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (vaxpy L dv one n0 a0 (a0 + 10) (s0 + 30) (s0 + 8) (s0 + 9))
    (.seq (sconst L (s0 + 2) 1)
      (.seq (mlin L (n0 + 9) one n0 (a0 + 1) (a0 + 1) (a0 + 14) (s0 + 2) (s0 + 30) (s0 + 8) (s0 + 9))
        (.seq (vnorm L dv one n0 (s0 + 34) a0 (s0 + 8) (s0 + 9))
          (.seq (ifS L (s0 + 23) (s0 + 34)
              (.seq (sop2 L .div (s0 + 35) (s0 + 23) (s0 + 34)) (vscale L dv one n0 a0 (s0 + 35) (s0 + 8))) .skip)
            (mspec L .clamp (a0 + 1) (a0 + 1) (s0 + 21) (s0 + 22))))))

/-- One step of the descent: the sums `+= x`, a sample `g` (`d` draws), the gauge, `V`, the move. -/
def pgStep (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L (s0 + 2) 1)
    (.seq (vaxpy L dv one n0 (a0 + 2) a0 (s0 + 2) (s0 + 8) (s0 + 9))
      (.seq (mlin L (n0 + 9) one n0 (a0 + 3) (a0 + 3) (a0 + 1) (s0 + 2) (s0 + 2) (s0 + 8) (s0 + 9))
        (.seq (vgauss L dv one n0 (a0 + 4) (s0 + 8))
          (.seq (pgGauge L dv one n0 s0 a0 muv Av a0 (a0 + 1))
            (.seq (pgVinv L dv one n0 s0 a0) (.seq (pgVmat L dv one n0 s0 a0) (pgUpd L dv one n0 s0 a0)))))))

/-- The descent: `x := x_1 = (0, t_min I)`, the sums `:= 0`, `N` steps, then the average `x̄` in `a0 + 2`, `a0 + 3`. -/
def pgDesc (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L s0 0)
    (.seq (vfill L dv one n0 a0 s0) (.seq (mfill L (n0 + 9) one n0 (a0 + 1) s0)
      (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 1) (s0 + 21))
        (.seq (vfill L dv one n0 (a0 + 2) s0) (.seq (mfill L (n0 + 9) one n0 (a0 + 3) s0)
          (.seq (forN (n0 + 13) (n0 + 11) one (pgStep L dv one n0 s0 a0 muv Av))
            (.seq (sconst L (s0 + 2) 1) (.seq (ncast L (s0 + 45) (n0 + 11))
              (.seq (sop2 L .div (s0 + 33) (s0 + 2) (s0 + 45)) (.seq (sconst L s0 0)
                (.seq (vscale L dv one n0 (a0 + 2) (s0 + 33) (s0 + 8))
                  (mlin L (n0 + 9) one n0 (a0 + 3) (a0 + 3) (a0 + 3) (s0 + 33) s0 (s0 + 8) (s0 + 9)))))))))))))

/-- One sample of a basic verdict at `x̄` (in `a0 + 2`, `a0 + 3`): `g` (`d` draws), `F`, then `k̂ += F`,
`b̂ += F g`, `Q̂ += F (g gᵀ - I)`. -/
def pgSample (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (vgauss L dv one n0 (a0 + 4) (s0 + 8))
    (.seq (pgGauge L dv one n0 s0 a0 muv Av (a0 + 2) (a0 + 3))
      (.seq (sop2 L .add (s0 + 37) (s0 + 37) (s0 + 18))
        (.seq (vaxpy L dv one n0 (a0 + 15) (a0 + 4) (s0 + 18) (s0 + 8) (s0 + 9))
          (.seq (pgGGcode L dv one n0 s0 a0)
            (mlin L (n0 + 9) one n0 (a0 + 16) (a0 + 16) (a0 + 11) (s0 + 2) (s0 + 18) (s0 + 8) (s0 + 9))))))

/-- The averages of a basic verdict: `k̂`, `b̂`, `Q̂` times `1/n_T`. -/
def pgVerdNorm (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1) (.seq (ncast L (s0 + 45) (n0 + 12))
    (.seq (sop2 L .div (s0 + 46) (s0 + 2) (s0 + 45)) (.seq (sop2 L .mul (s0 + 37) (s0 + 46) (s0 + 37))
      (.seq (vscale L dv one n0 (a0 + 15) (s0 + 46) (s0 + 8))
        (mlin L (n0 + 9) one n0 (a0 + 16) (a0 + 16) (a0 + 16) (s0 + 46) s0 (s0 + 8) (s0 + 9)))))))

/-- The first two clauses of a basic verdict: `v := 1`, cleared if `k̂ > 1.075 κ` or `|b̂| > (3/4) τ_b`. -/
def pgVerdC12 (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (sconst L (s0 + 39) 1) (.seq (sconst L (s0 + 47) (43 / 320))
    (.seq (ifS L (s0 + 47) (s0 + 37) (sconst L (s0 + 39) 0) .skip)
      (.seq (vnorm L dv one n0 (s0 + 38) (a0 + 15) (s0 + 8) (s0 + 9))
        (.seq (sconst L (s0 + 47) (3 / 4)) (.seq (sop2 L .mul (s0 + 47) (s0 + 47) (s0 + 28))
          (ifS L (s0 + 47) (s0 + 38) (sconst L (s0 + 39) 0) .skip))))))

/-- The third clause of a basic verdict: `N := c I - Q̂` (`c = (5/8) κ/d = (-5/8) (-κ/d)`), cleared if the trace of
`1_{(0,∞)}(N)` is positive. -/
def pgVerdC3 (L : Layout) (dv one n0 s0 a0 : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1) (.seq (sconst L (s0 + 47) (-5 / 8))
    (.seq (sop2 L .mul (s0 + 51) (s0 + 47) (s0 + 32))
      (.seq (mfill L (n0 + 9) one n0 (a0 + 17) s0) (.seq (mdiag L dv one n0 (n0 + 2) (a0 + 17) (s0 + 51))
        (.seq (sconst L (s0 + 36) (-1))
          (.seq (mlin L (n0 + 9) one n0 (a0 + 17) (a0 + 17) (a0 + 16) (s0 + 2) (s0 + 36) (s0 + 8) (s0 + 9))
            (.seq (mspec L .step (a0 + 18) (a0 + 17) s0 s0)
              (.seq (mtrace L dv one n0 (n0 + 2) (s0 + 44) (a0 + 18) (s0 + 8))
                (ifS L s0 (s0 + 44) (sconst L (s0 + 39) 0) .skip))))))))))

/-- One basic verdict at `x̄`: the accumulators `:= 0`, `n_T` samples, the averages, the three clauses, and the
count of accepting verdicts `+=` the verdict. -/
def pgVerd (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L s0 0) (.seq (sconst L (s0 + 37) 0) (.seq (vfill L dv one n0 (a0 + 15) s0)
    (.seq (mfill L (n0 + 9) one n0 (a0 + 16) s0)
      (.seq (forN (n0 + 13) (n0 + 12) one (pgSample L dv one n0 s0 a0 muv Av))
        (.seq (pgVerdNorm L dv one n0 s0 a0) (.seq (pgVerdC12 L dv one n0 s0 a0)
          (.seq (pgVerdC3 L dv one n0 s0 a0) (sop2 L .add (s0 + 40) (s0 + 40) (s0 + 39)))))))))

/-- The amplified test at `x̄`: `m_T` basic verdicts, then `pass := 1` if more than `m_T/2` accept, else `0`. -/
def pgTestC (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (sconst L (s0 + 40) 0) (.seq (forN (n0 + 15) (n0 + 14) one (pgVerd L dv one n0 s0 a0 muv Av))
    (.seq (ncast L (s0 + 45) (n0 + 14)) (.seq (sconst L (s0 + 1) (1 / 2))
      (.seq (sop2 L .mul (s0 + 45) (s0 + 45) (s0 + 1))
        (.seq (sconst L (s0 + 49) 0) (ifS L (s0 + 45) (s0 + 40) (sconst L (s0 + 49) 1) .skip))))))

/-- One repeat: the descent, the test, and if no earlier repeat was kept and the test passes, `x̄` kept in
`a0 + 19`, `a0 + 20` with the flag `found := 1`. -/
def pgRep (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (pgDesc L dv one n0 s0 a0 muv Av) (.seq (pgTestC L dv one n0 s0 a0 muv Av)
    (.seq (sconst L s0 0) (.seq (sconst L (s0 + 2) 1)
      (ifS L (s0 + 41) (s0 + 2)
        (ifS L s0 (s0 + 49) (.seq (sconst L (s0 + 41) 1)
          (.seq (vcopy L dv one n0 (a0 + 19) (a0 + 2) (s0 + 8)) (mcopy L (n0 + 9) one n0 (a0 + 20) (a0 + 3) (s0 + 8))))
          .skip)
        .skip))))

/-! ### The parameters of a stage, as straight-line scalar code

The parameters of a stage from `ρ` (in `s0 + 19`) and `d` (in `s0 + 48`), in blocks of scalar instructions (`SI`),
each block computing one parameter from the earlier ones with the scratch scalars `s0 + 45`, `s0 + 46`,
`s0 + 47`, `s0 + 50`. -/

open SI in
/-- `o := 1`, `λ := (2 log (1 + ρ))^{1/2}` into `s0 + 20`. -/
def pgA1 (s0 : ℕ) : List SI :=
  [const (s0 + 2) 1, op2 .add (s0 + 45) (s0 + 2) (s0 + 19), op1 .log (s0 + 45) (s0 + 45), const (s0 + 46) 2,
    op2 .mul (s0 + 45) (s0 + 46) (s0 + 45), op1 .sqrt (s0 + 20) (s0 + 45)]

open SI in
/-- `t_max := L_D = (627/4000) ρ` into `s0 + 22`. -/
def pgA2 (s0 : ℕ) : List SI := [const (s0 + 46) (627 / 4000), op2 .mul (s0 + 22) (s0 + 46) (s0 + 19)]

open SI in
/-- `t_min := 1/(9 d λ)` into `s0 + 21`. -/
def pgA3 (s0 : ℕ) : List SI :=
  [const (s0 + 46) 9, op2 .mul (s0 + 45) (s0 + 46) (s0 + 48), op2 .mul (s0 + 45) (s0 + 45) (s0 + 20),
    op2 .div (s0 + 21) (s0 + 2) (s0 + 45)]

open SI in
/-- `κρ := ρ/8` into `s0 + 23`. -/
def pgA4 (s0 : ℕ) : List SI := [const (s0 + 46) (1 / 8), op2 .mul (s0 + 23) (s0 + 46) (s0 + 19)]

open SI in
/-- `Δ := κρ (4 + p_B² d)^{1/2}` into `s0 + 24`. -/
def pgA5 (s0 : ℕ) : List SI :=
  [const (s0 + 46) (393129 / 250000), op2 .mul (s0 + 45) (s0 + 46) (s0 + 48), const (s0 + 46) 4,
    op2 .add (s0 + 45) (s0 + 46) (s0 + 45), op1 .sqrt (s0 + 45) (s0 + 45), op2 .mul (s0 + 24) (s0 + 23) (s0 + 45)]

open SI in
/-- `-κ/d` into `s0 + 32`. -/
def pgA6 (s0 : ℕ) : List SI := [const (s0 + 46) (-1 / 8), op2 .div (s0 + 32) (s0 + 46) (s0 + 48)]

/-- Part A: `λ`, `t_max`, `t_min`, `κρ`, `Δ`, `-κ/d`. -/
def pgParAL (s0 : ℕ) : List SI := pgA1 s0 ++ pgA2 s0 ++ pgA3 s0 ++ pgA4 s0 ++ pgA5 s0 ++ pgA6 s0

/-- The parameters of a stage, part A. -/
def pgParA (L : Layout) (s0 : ℕ) : Cmd := sprog L (pgParAL s0)

open SI in
/-- `5 L_D² d (d + 2)(d + 5)` into `s0 + 45`. -/
def pgB1 (s0 : ℕ) : List SI :=
  [op2 .mul (s0 + 45) (s0 + 22) (s0 + 22), const (s0 + 46) 5, op2 .mul (s0 + 45) (s0 + 46) (s0 + 45),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 48), const (s0 + 46) 2, op2 .add (s0 + 46) (s0 + 48) (s0 + 46),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 46), const (s0 + 46) 5, op2 .add (s0 + 46) (s0 + 48) (s0 + 46),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 46)]

open SI in
/-- `G² := (5 L_D² d (d + 2)(d + 5) + 1/(32 d))/t_min²` into `s0 + 25`. -/
def pgB2 (s0 : ℕ) : List SI :=
  [const (s0 + 46) (1 / 32), op2 .div (s0 + 46) (s0 + 46) (s0 + 48), op2 .add (s0 + 45) (s0 + 45) (s0 + 46),
    op2 .mul (s0 + 46) (s0 + 21) (s0 + 21), op2 .div (s0 + 25) (s0 + 45) (s0 + 46)]

open SI in
/-- `e_h := (1/64)/(922 d² λ² L_D)` into `s0 + 26`. -/
def pgB3 (s0 : ℕ) : List SI :=
  [const (s0 + 46) 922, op2 .mul (s0 + 45) (s0 + 46) (s0 + 48), op2 .mul (s0 + 45) (s0 + 45) (s0 + 48),
    op2 .mul (s0 + 46) (s0 + 20) (s0 + 20), op2 .mul (s0 + 45) (s0 + 45) (s0 + 46),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 22), const (s0 + 46) (1 / 64), op2 .div (s0 + 26) (s0 + 46) (s0 + 45)]

open SI in
/-- `η := e_h t_min/(7 L_D (1 + d^{1/2}) Δ)` into `s0 + 27`. -/
def pgB4 (s0 : ℕ) : List SI :=
  [op2 .mul (s0 + 45) (s0 + 26) (s0 + 21), op1 .sqrt (s0 + 46) (s0 + 48), op2 .add (s0 + 46) (s0 + 2) (s0 + 46),
    const (s0 + 47) 7, op2 .mul (s0 + 47) (s0 + 47) (s0 + 22), op2 .mul (s0 + 47) (s0 + 47) (s0 + 46),
    op2 .mul (s0 + 47) (s0 + 47) (s0 + 24), op2 .div (s0 + 27) (s0 + 45) (s0 + 47)]

open SI in
/-- `τ_b := (1/8)/(12 d λ)` into `s0 + 28`. -/
def pgB5 (s0 : ℕ) : List SI :=
  [const (s0 + 46) 12, op2 .mul (s0 + 45) (s0 + 46) (s0 + 48), op2 .mul (s0 + 45) (s0 + 45) (s0 + 20),
    const (s0 + 46) (1 / 8), op2 .div (s0 + 28) (s0 + 46) (s0 + 45)]

/-- Part B: `G²`, `e_h`, `η`, `τ_b`. -/
def pgParBL (s0 : ℕ) : List SI := pgB1 s0 ++ pgB2 s0 ++ pgB3 s0 ++ pgB4 s0 ++ pgB5 s0

/-- The parameters of a stage, part B. -/
def pgParB (L : Layout) (s0 : ℕ) : Cmd := sprog L (pgParBL s0)

open SI in
/-- `(5/4) L_D² d³` into `s0 + 45`. -/
def pgC1 (s0 : ℕ) : List SI :=
  [op2 .mul (s0 + 45) (s0 + 22) (s0 + 22), const (s0 + 46) (5 / 4), op2 .mul (s0 + 45) (s0 + 46) (s0 + 45),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 48), op2 .mul (s0 + 45) (s0 + 45) (s0 + 48),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 48)]

open SI in
/-- `6144 (d + 1)(d + 5)` into `s0 + 46`. -/
def pgC2 (s0 : ℕ) : List SI :=
  [const (s0 + 46) 6144, op2 .add (s0 + 47) (s0 + 48) (s0 + 2), op2 .mul (s0 + 46) (s0 + 46) (s0 + 47),
    const (s0 + 47) 5, op2 .add (s0 + 47) (s0 + 48) (s0 + 47), op2 .mul (s0 + 46) (s0 + 46) (s0 + 47)]

open SI in
/-- `221184 (d + 3) λ²` into `s0 + 47`. -/
def pgC3 (s0 : ℕ) : List SI :=
  [const (s0 + 47) 221184, const (s0 + 50) 3, op2 .add (s0 + 50) (s0 + 48) (s0 + 50),
    op2 .mul (s0 + 47) (s0 + 47) (s0 + 50), op2 .mul (s0 + 50) (s0 + 20) (s0 + 20),
    op2 .mul (s0 + 47) (s0 + 47) (s0 + 50)]

open SI in
/-- `n_T^real := (5/4) L_D² d³ max(..)/(1/64)` into `s0 + 45`. -/
def pgC4 (s0 : ℕ) : List SI :=
  [smax (s0 + 50) (s0 + 46) (s0 + 47), op2 .mul (s0 + 45) (s0 + 45) (s0 + 50), const (s0 + 46) (1 / 64),
    op2 .div (s0 + 45) (s0 + 45) (s0 + 46)]

/-- Part C before the ceiling: `n_T^real` into `s0 + 45`. -/
def pgParC1L (s0 : ℕ) : List SI := pgC1 s0 ++ pgC2 s0 ++ pgC3 s0 ++ pgC4 s0

/-- The parameters of a stage, part C: `n_T := ⌈n_T^real⌉₊`. -/
def pgParC1 (L : Layout) (one n0 s0 : ℕ) : Cmd :=
  .seq (sprog L (pgParC1L s0)) (nceil L (n0 + 12) one (s0 + 45) (s0 + 46))

open SI in
/-- `N^real := 16 Δ² G²/e_h²` into `s0 + 45`. -/
def pgD1 (s0 : ℕ) : List SI :=
  [op2 .mul (s0 + 45) (s0 + 24) (s0 + 24), const (s0 + 46) 16, op2 .mul (s0 + 45) (s0 + 46) (s0 + 45),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 25), op2 .mul (s0 + 46) (s0 + 26) (s0 + 26),
    op2 .div (s0 + 45) (s0 + 45) (s0 + 46)]

open SI in
/-- `log₂ (ρ/η)` into `s0 + 45`. -/
def pgD2 (s0 : ℕ) : List SI :=
  [op2 .div (s0 + 45) (s0 + 19) (s0 + 27), op1 .log (s0 + 45) (s0 + 45), const (s0 + 46) 2,
    op1 .log (s0 + 46) (s0 + 46), op2 .div (s0 + 45) (s0 + 45) (s0 + 46)]

open SI in
/-- The step `s := Δ/(G N^{1/2})` into `s0 + 29` and `-s` into `s0 + 30`. -/
def pgD3 (s0 n0 : ℕ) : List SI :=
  [op1 .sqrt (s0 + 45) (s0 + 25), cast (s0 + 46) (n0 + 11), op1 .sqrt (s0 + 46) (s0 + 46),
    op2 .mul (s0 + 45) (s0 + 45) (s0 + 46), op2 .div (s0 + 29) (s0 + 24) (s0 + 45), const s0 0,
    op2 .sub (s0 + 30) s0 (s0 + 29)]

/-- The parameters of a stage, part D: `N := ⌈N^real⌉₊`, `j := ⌈log₂ (ρ/η)⌉₊`, the step `s` and `-s`. -/
def pgParC2 (L : Layout) (one n0 s0 : ℕ) : Cmd :=
  .seq (sprog L (pgD1 s0)) (.seq (nceil L (n0 + 11) one (s0 + 45) (s0 + 46))
    (.seq (sprog L (pgD2 s0)) (.seq (nceil L (n0 + 10) one (s0 + 45) (s0 + 46)) (sprog L (pgD3 s0 n0)))))

/-- The composition of the position with the kept point `x̄ = (μ', T')`: `μ := μ + A μ'`, `A := A T'`. -/
def pgCompC (L : Layout) (dv one n0 s0 a0 muv Av : ℕ) : Cmd :=
  .seq (matvec L dv one n0 (n0 + 1) (n0 + 2) (a0 + 22) Av (a0 + 19) (s0 + 11) (s0 + 8) (s0 + 9))
    (.seq (sconst L (s0 + 2) 1) (.seq (vaxpy L dv one n0 muv (a0 + 22) (s0 + 2) (s0 + 8) (s0 + 9))
      (.seq (mmul L dv one n0 (n0 + 1) (n0 + 3) (n0 + 4) (n0 + 5) (n0 + 6) (a0 + 21) Av (a0 + 20) (s0 + 11) (s0 + 8)
          (s0 + 9))
        (mcopy L (n0 + 9) one n0 Av (a0 + 21) (s0 + 8)))))

/-- One stage: the parameters from `ρ`, `found := 0`, the `J` repeats, then the composition if a repeat was kept,
else `ok := 0`. -/
def pgStageC (L : Layout) (dv one okv muv Av n0 s0 a0 : ℕ) : Cmd :=
  .seq (pgParA L s0) (.seq (pgParB L s0) (.seq (pgParC1 L one n0 s0) (.seq (pgParC2 L one n0 s0)
    (.seq (sconst L (s0 + 41) 0) (.seq (forN (n0 + 17) (n0 + 16) one (pgRep L dv one n0 s0 a0 muv Av))
      (.seq (sconst L s0 0)
        (ifS L s0 (s0 + 41) (pgCompC L dv one n0 s0 a0 muv Av) (sconst L okv 0))))))))

open SI in
/-- The next ratio and radius as scalar instructions. -/
def pgRhoL (s0 : ℕ) : List SI :=
  [const (s0 + 2) 1, op2 .add (s0 + 45) (s0 + 2) (s0 + 19), op1 .log (s0 + 45) (s0 + 45),
    op1 .sqrt (s0 + 45) (s0 + 45), const (s0 + 46) 162, op2 .mul (s0 + 46) (s0 + 46) (s0 + 48),
    op2 .mul (s0 + 19) (s0 + 46) (s0 + 45), op2 .add (s0 + 42) (s0 + 42) (s0 + 42)]

/-- The next ratio and radius: `ρ := 3 · 54 d (log (1 + ρ))^{1/2}`, `rad := 2 rad`. -/
def pgRho (L : Layout) (s0 : ℕ) : Cmd := sprog L (pgRhoL s0)

open SI in
/-- `d` as a real into `s0 + 48`, `o := 1`, `log₂ (R₀/r₀)` into `s0 + 45`. -/
def pgK1 (dv r0v R0v s0 : ℕ) : List SI :=
  [cast (s0 + 48) dv, const (s0 + 2) 1, op2 .div (s0 + 45) R0v r0v, op1 .log (s0 + 45) (s0 + 45),
    const (s0 + 46) 2, op1 .log (s0 + 46) (s0 + 46), op2 .div (s0 + 45) (s0 + 45) (s0 + 46)]

open SI in
/-- `δ' := δ₁/m` into `s0 + 43`, `log₂ (4/δ')` into `s0 + 45`. -/
def pgK2 (δv n0 s0 : ℕ) : List SI :=
  [cast (s0 + 45) (n0 + 18), op2 .div (s0 + 43) δv (s0 + 45), const (s0 + 45) 4,
    op2 .div (s0 + 45) (s0 + 45) (s0 + 43), op1 .log (s0 + 45) (s0 + 45), const (s0 + 46) 2,
    op1 .log (s0 + 46) (s0 + 46), op2 .div (s0 + 45) (s0 + 45) (s0 + 46)]

open SI in
/-- `8 log (2J/δ')` into `s0 + 45`. -/
def pgK3 (n0 s0 : ℕ) : List SI :=
  [cast (s0 + 45) (n0 + 16), const (s0 + 46) 2, op2 .mul (s0 + 45) (s0 + 46) (s0 + 45),
    op2 .div (s0 + 45) (s0 + 45) (s0 + 43), op1 .log (s0 + 45) (s0 + 45), const (s0 + 46) 8,
    op2 .mul (s0 + 45) (s0 + 46) (s0 + 45)]

/-- The caps, once: `dd := d²`, `d` as a real, `m := max 1 ⌈log₂ (R₀/r₀)⌉₊`, `δ' := δ₁/m`,
`J := ⌈log₂ (4/δ')⌉₊`, `m_T := ⌈8 log (2J/δ')⌉₊`. -/
def pgCaps (L : Layout) (dv one r0v R0v δv n0 s0 : ℕ) : Cmd :=
  .seq (nsq dv one n0 (n0 + 9)) (.seq (sprog L (pgK1 dv r0v R0v s0))
    (.seq (nceil L (n0 + 18) one (s0 + 45) (s0 + 46)) (.seq (.ifN (n0 + 18) one (nconst (n0 + 18) 1) .skip)
      (.seq (sprog L (pgK2 δv n0 s0)) (.seq (nceil L (n0 + 16) one (s0 + 45) (s0 + 46))
        (.seq (sprog L (pgK3 n0 s0)) (nceil L (n0 + 14) one (s0 + 45) (s0 + 46))))))))

/-- Procedure PG: the caps, the start `ok := 1`, `μ := 0`, `A := r₀ I`, `ρ := 2`, `rad := 2 r₀`, then the `m`
stages, each followed by the next ratio and radius. -/
def pgCode (L : Layout) (dv one r0v R0v δv okv muv Av n0 s0 a0 : ℕ) : Cmd :=
  .seq (pgCaps L dv one r0v R0v δv n0 s0)
    (.seq (sconst L okv 1) (.seq (sconst L s0 0) (.seq (vfill L dv one n0 muv s0)
      (.seq (mfill L (n0 + 9) one n0 Av s0) (.seq (mdiag L dv one n0 (n0 + 2) Av r0v)
        (.seq (sconst L (s0 + 19) 2) (.seq (sop2 L .add (s0 + 42) r0v r0v)
          (forN (n0 + 19) (n0 + 18) one (.seq (pgStageC L dv one okv muv Av n0 s0 a0) (pgRho L s0))))))))))


/-! ## The sets, frames and step counts of the rules -/

/-- The body of a stage read off the arrays: the points `y` with `A y + μ ∈ K` and `|A y + μ| ≤ R`. -/
def pgBodySet {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (μ : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y | WithLp.toLp 2 (A *ᵥ WithLp.ofLp y + μ) ∈ K ∧ ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp y + μ)‖ ≤ R}

/-- The natural temporaries `n0 + 0, ..., n0 + 8`. -/
def pgTmpN (n0 : ℕ) : List ℕ := [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8]

/-- The scalar temporaries `s0 + 0, ..., s0 + 18`. -/
def pgTmpS (s0 : ℕ) : List ℕ :=
  [s0, s0 + 1, s0 + 2, s0 + 3, s0 + 4, s0 + 5, s0 + 6, s0 + 7, s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13,
    s0 + 14, s0 + 15, s0 + 16, s0 + 17, s0 + 18]

def kMemQ (d : ℕ) : ℕ := d * (d * 10 + 9) + d * 11 + 9 + (d * 9 + 5 + 2)

def kGauge (d jb : ℕ) : ℕ := d * (d * 10 + 9) + 4 + (1 + (d * 11 + 3 + (jb * (d * 15 + kMemQ d + 16) + d * 9 + 15)))

def kGG (d : ℕ) : ℕ := 1 + (1 + (1 + (d * d * 5 + 3 + (d * 7 + 4 + (d * (d * 16 + 6) + 4)))))

def kGJ (d : ℕ) : ℕ := d * (d * d * 21 + d * 31 + 17) + d * d * 12 + d * 7 + 16

def kVinv (d : ℕ) : ℕ := kGJ d + (d * (d * 10 + 9) + 4 + (d * 8 + 3))

def kVmat (d : ℕ) : ℕ :=
  kGG d + (d * (d * (d * 11 + 12) + 6) + 4 + (d * (d * 9 + 8) + 4 + (1 + (1 + (d * d * 12 + 3 + (d * d * 12 + 3))))))

def kUpd (d : ℕ) : ℕ := d * 11 + 3 + (1 + (d * d * 12 + 3 + (d * 9 + 5 + (d * 8 + 5 + 1))))

def kStep (d jb : ℕ) : ℕ :=
  1 + (d * 11 + 3 + (d * d * 12 + 3 + (d * 6 + 3 + (kGauge d jb + (kVinv d + (kVmat d + kUpd d))))))

def kDesc (d jb N : ℕ) : ℕ :=
  1 + (d * 5 + 3 + (d * d * 5 + 3 + (d * 7 + 4 + (d * 5 + 3 + (d * d * 5 + 3 + (N * (kStep d jb + 3) + 3 +
    (1 + (1 + (1 + (1 + (d * 8 + 3 + (d * d * 12 + 3))))))))))))

def kSample (d jb : ℕ) : ℕ := d * 6 + 3 + (kGauge d jb + (1 + (d * 11 + 3 + (kGG d + (d * d * 12 + 3)))))

def kVerdNorm (d : ℕ) : ℕ := 1 + (1 + (1 + (1 + (1 + (d * 8 + 3 + (d * d * 12 + 3))))))

def kVerdC12 (d : ℕ) : ℕ := 1 + (1 + (2 + (d * 9 + 5 + (1 + (1 + 2)))))

def kVerdC3 (d : ℕ) : ℕ :=
  1 + (1 + (1 + (1 + (d * d * 5 + 3 + (d * 7 + 4 + (1 + (d * d * 12 + 3 + (1 + (d * 8 + 5 + 2)))))))))

def kVerd (d jb nT : ℕ) : ℕ :=
  1 + (1 + (d * 5 + 3 + (d * d * 5 + 3 + (nT * (kSample d jb + 3) + 3 + (kVerdNorm d + (kVerdC12 d +
    (kVerdC3 d + 1)))))))

def kTest (d jb nT mT : ℕ) : ℕ := 1 + (mT * (kVerd d jb nT + 3) + 3 + (1 + (1 + (1 + (1 + 2)))))

def kRep (d jb N nT mT : ℕ) : ℕ :=
  kDesc d jb N + (kTest d jb nT mT + (1 + (1 + (1 + (d * 7 + 3 + (d * d * 7 + 3)) + 1 + 1))))

def kCompC (d : ℕ) : ℕ :=
  d * (d * 10 + 9) + 4 + (1 + (d * 11 + 3 + (d * (d * (d * 11 + 12) + 6) + 4 + (d * d * 7 + 3))))

def kStage (d jb N nT J mT : ℕ) : ℕ :=
  22 + (36 + (nT * 4 + 28 + (N * 4 + jb * 4 + 26 + (1 + (J * (kRep d jb N nT mT + 3) + 3 + (1 + (kCompC d + 1)))))))

def kCaps (d m0 J mT : ℕ) : ℕ := d * 4 + 4 + 7 + (m0 * 4 + 4) + 2 + 8 + (J * 4 + 4) + 7 + (mT * 4 + 4)

end AdversarialBco.Poly.PG
