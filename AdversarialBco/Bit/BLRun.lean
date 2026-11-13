/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLLink

@[expose] public section

/-!
# BL's run record and the frozen interfaces of `RunOK`

This file builds BL's run record `blRun R` (`Run` of Bit/ShadowIface.lean) from the pure function of Bit/BLPure.lean,
the instance `blInst P R` of `BLInst`, and freezes the statements that the proof of `RunOK (blInst P R)` is cut into
:

* piece A (`BudA`): the enclosure lemma and the precision theorem, the real inequalities `BudOK d n` on
  the constants of the lemma of the errors of a round (namespace `Bud`);
* piece B (`BitsB`, `MeasDrawB`): the probability of BL's unsound draws and the measurability of the draw of a round;
* piece C (`RoundC`): one round of BL against one round of P°'s virtual epoch (Lemmas TRACK, TRACK-2, SEL, VAL,
  GUARD with E1 to E18), deterministic;
* the requirement `PosTri R` on BL's position routine, for the brick `PosInst`.

Piece D proves `RunOK (blInst P R)` from `BLLink P R`, `O3SpecQ R.ap`, `PosLocal R` and these
statements: the record's `BLMeas`, `BitsHyp`, `EngineHyp` (the induction `IND(t)` over P°'s run,
through the horizon lemma), and the losses and plays of `RunSpec`.

Two choices of the record, both invisible to `RunOK`:

* the loss parameter of round `t` is BL's history before round `t` in the type `HistQ d` with the discrete
  sigma-field; it is the history itself when that history is measurable at `cσ d t` (which piece B's prefix lemma gives)
  and `0` otherwise, so that the record is defined with no proof obligation;
* the losses are those of the strategy when it is admissible (`AdmStrat`), `0` otherwise.

The shift and the advice are read at P°'s mode before the round; they are not
trivial only when both learners are in mode `run`.
-/

namespace AdversarialBco.Bit.BLP

open MeasureTheory
open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ)
open AdversarialBco.Poly.Conj1 (fL)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm
open Matrix

variable {d : ℕ}

/-! ## Casts and norms -/

/-- A rational vector as a real one. -/
def cV (v : Fin d → ℚ) : Fin d → ℝ := fun i => (v i : ℝ)

/-- A rational matrix as a real one. -/
def cM (M : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℝ := M.map ((↑) : ℚ → ℝ)

/-- The spectral norm of a real matrix (the operator norm on `E d`). -/
noncomputable def opN (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-! ## The record -/

/-- BL's history: the points played in the rounds before the current one, `0` from it on. The discrete sigma-field. -/
def HistQ (d : ℕ) : Type := ℕ → Fin d → ℚ

instance : MeasurableSpace (HistQ d) := ⊤

/-- The empty history. -/
def histZero : HistQ d := fun _ _ => 0

/-- BL's digit map at `(d, n)`: `BLInst.β` of the instance `blInst`. -/
noncomputable def betaR (R : Routines) (d n : ℕ) : (ℕ → ℝ) → ℕ → Bool := Sched.beta d (R.K0 d n) (par d n).B

/-- The noiseless worlds `Z_n`. -/
def Zn (n : ℕ) : Set WΩ := {ω | ∀ t < n, ω.2 t = 0}

open Classical in
/-- The loss of round `t` at the history `l`: the strategy's if it is admissible, else `0`. -/
noncomputable def lossL (K : Set (E d)) (n : ℕ) (σ : Strategy d) (t : ℕ) (l : HistQ d) : E d → ℝ :=
  if AdmStrat K n σ then lossAd σ 0 (fun i => toE (l i)) t else 0

/-- BL's history before round `t` on the world `ω`. -/
noncomputable def lamRaw (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : HistQ d :=
  (traj R d n m A b σ (betaR R d n ω.1) t).2

open Classical in
/-- The loss parameter of round `t`: BL's history when it is `cσ d t`-measurable (always, by piece B), else `0`. -/
noncomputable def lamR (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) : WΩ → HistQ d :=
  if Measurable[cσ d t] (lamRaw R d n m A b σ t) then lamRaw R d n m A b σ t else fun _ => histZero

theorem admLoss_zero {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    AdmLoss (polytope A b) (0 : E d → ℝ) :=
  ⟨convexOn_const 0 (Conj1Poly.convex_polytope A b), fun _ _ => ⟨le_refl 0, zero_le_one⟩⟩

/-- The loss process of the record. -/
noncomputable def blF (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d) :
    Df2LossProcF d n (polytope A b) (cσ d) where
  Λ := HistQ d
  L := lossL (polytope A b) n σ
  lam := lamR R d n m A b σ
  adm t ht l := by
    classical
    unfold lossL
    split_ifs with h
    · exact h t ht l
    · exact admLoss_zero A b
  meas _ _ _ _ := measurable_from_top
  lam_meas t _ := by
    classical
    unfold lamR
    by_cases h : Measurable[cσ d t] (lamRaw R d n m A b σ t)
    · rw [ite_eq_left h]; exact h
    · rw [ite_eq_right h]; exact measurable_const

/-- BL's position on the coins `cs`: `(μ_S, A_S)` of the prologue, as a point of `PgSp d`. -/
noncomputable def posR (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool) :
    PgSp d :=
  pgPack (toE (R.pos d n m A b cs).1) (cM (R.pos d n m A b cs).2)

/-- BL's configuration on the world `ω`. -/
noncomputable def cfgW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ω : WΩ) : Cfg d :=
  cfgOf R d n m A b (betaR R d n ω.1)

/-- BL's mode before round `t` on the world `ω`. -/
noncomputable def modeW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : Mode d :=
  modeAt R d n m A b σ (betaR R d n ω.1) t

/-- BL's draw `(ξ'_t, ζ'_t)` of round `t` on the world `ω`. -/
noncomputable def drawW (R : Routines) (d n : ℕ) (t : ℕ) (ω : WΩ) : (Fin d → ℚ) × ℚ :=
  drawAt R d n (betaR R d n ω.1) t

/-- BL's play of round `t` on the world `ω` (rational). -/
noncomputable def playW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : Fin d → ℚ :=
  play R d n m A b σ (betaR R d n ω.1) t

/-- BL's reading of round `t` on the world `ω`, `⌊2^p f_t(x'_t)⌋`, as in `traj`. -/
noncomputable def obsW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : ℤ :=
  ⌊(2 : ℝ) ^ (par d n).p * lossAd σ 0 (fun i => toE (Function.update (lamRaw R d n m A b σ t ω) t
      (playW R d n m A b σ t ω) i)) t (toE (playW R d n m A b σ t ω))⌋

/-- The loss of round `t` that the record reads at the world `ω` (`Run.loss`). -/
noncomputable def lossW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : E d → ℝ :=
  lossL (polytope A b) n σ t (lamR R d n m A b σ t ω)

open Classical in
/-- The loss of round `t` that P° reads at the world `ω` (`Run.lossR`). -/
noncomputable def lossRW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) : E d → ℝ :=
  if t < n then fL (polytope A b) (lossL (polytope A b) n σ) t (lamR R d n m A b σ t ω) else 0

/-! ### BL's draws: the soundness event -/

/-- The bound `e_ξ` on each coordinate of `ξ'_t - ξ_t` on `E_bits`, `2^{2 - B/2}` (E1). -/
noncomputable def eXi0 (d n : ℕ) : ℝ := 4 / 2 ^ ((par d n).B / 2)

/-- The bound `e_ζ` on `ζ'_t - Z̃_t/2` on `E_bits`, `2^{1 - B/2}`. -/
noncomputable def eZt0 (d n : ℕ) : ℝ := 2 / 2 ^ ((par d n).B / 2)

/-- `E_bits` (the lemma of the draws): BL's draws of the rounds `t < n` are within `e_ξ`, `e_ζ` of
the world's draw `ξc d t ω` and half its dither coordinate `zc d t ω 0`. -/
noncomputable def Ebits (R : Routines) (d n : ℕ) : Set WΩ :=
  {ω | ∀ t < n, (∀ i, |((drawW R d n t ω).1 i : ℝ) - ξc d t ω i| ≤ eXi0 d n) ∧
    |((drawW R d n t ω).2 : ℝ) - zc d t ω 0 / 2| ≤ eZt0 d n}

/-! ### The shift -/

/-- P°'s parameters at BL's confidence. -/
noncomputable def po (d n : ℕ) : Df2OPar := df2oPar d n (deltaBL d n)

/-- P°'s body at BL's position (positioned coordinates). -/
noncomputable def kW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ω : WΩ) : Set (E d) :=
  kTh n (deltaBL d n) (polytope A b) (posR R d n m A b (betaR R d n ω.1))

/-- P°'s point `X°_t = μ° + (1 - λ) A° ξ_t` from the state `so`. -/
noncomputable def refX (p : Df2OPar) (so : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ := so.mu + (1 - p.lam) • (so.A *ᵥ ξ)

/-- P°'s `pt°(X) = max(1, gauge(X)/(1 - ε))` for the body `Kt`. -/
noncomputable def refPt (p : Df2OPar) (Kt : Set (E d)) (X : Fin d → ℝ) : ℝ :=
  max 1 (gauge Kt (WithLp.toLp 2 X) / (1 - p.eps))

/-- The shift `(m_t, r_t)` of round `t` at P°'s mode `mo` before round `t`:
`r = pt'/pt°` and `m = (r - 1) ε_t + (pt' f(x') - pt° f°(x°) + 4 (pt' - 1)/ε' - 4 (pt° - 1)/ε)/pt°`, with `f` the loss
of the round at BL's play `x'` and `f°` the loss P° reads at its play `x°`; `(0, 1)` unless both learners are in mode
`run`. On the coupling event `ζ°_t = m_t + r_t Z̃_t/2`, P°'s observation is BL's exact observation
`pt'(f(x') + ε_t + Z̃_t/2)/2 + 2(pt' - 1)/ε'`. -/
noncomputable def shW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) (mo : Df2Mode d) : ℝ × ℝ :=
  match mo, modeW R d n m A b σ t ω with
  | .run so, .run st =>
    let cfg := cfgW R d n m A b ω
    let q := posR R d n m A b (betaR R d n ω.1)
    let Xo := refX (po d n) so (ξc d t ω)
    let pto := refPt (po d n) (kW R d n m A b ω) Xo
    let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
    let pt' : ℝ := ptQ cfg (XQ cfg st (drawW R d n t ω).1)
    let x' : E d := toE (playW R d n m A b σ t ω)
    let r := pt' / pto
    ((r - 1) * ω.2 t + (pt' * lossW R d n m A b σ t ω x' - pto * lossRW R d n m A b σ t ω xo +
        4 * (pt' - 1) / (cfg.par.eps : ℝ) - 4 * (pto - 1) / (po d n).eps) / pto, r)
  | _, _ => (0, 1)

/-! ### The advice -/

/-- BL's test call of a round in mode `run` and its decision: the point `p'` and whether BL fires; `none` when BL acts
its guard before the test or the call fails. The lines R5 to R12 of `step`, verbatim. -/
def testQ (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Option ((Fin d → ℚ) × Bool) :=
  let P := cfg.par
  let w := st.A *ᵥ ξ
  let X := XQ cfg st ξ
  let pt := ptQ cfg X
  let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let c := P.kapc * Y
  let a := 1 - c
  let q := a + c * (ξ ⬝ᵥ ξ)
  if a < 1 / 2 ∨ q < 1 / 2 then none else
  let s1 := sqrtDn P.p (1 / a)
  let s3 := sqrtDn P.p a
  let rq := sqrtDn P.p q
  let s2 := rnd P.p (c / (s3 * rq * (s3 + rq)))
  let s4 := rnd P.p (c / (s3 + rq))
  let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
  let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
  let u := st.B *ᵥ ξ
  let v := st.Bᵀ *ᵥ st.mu
  let b' := st.b + rndV P.p (c • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
  let k' := st.k + rnd P.p (c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
  let g := rndV P.p ((Y * P.nu) • u)
  let G' := st.G + g
  let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
  if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then none else
  let Pp := B' * B'ᵀ
  let wp := b' - (P.eta / 2) • G'
  let callT : CallQ d :=
    if st.first then callOf cfg 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
    else callOf cfg (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
  match ap callT with
  | none => none
  | some p' =>
    some (p', decide (P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat))

/-- P°'s test function after the update of a round, `Xi(y) = η(l' - G'·y) - 2 Φ'(y)`, written as
`κ + h·y - yᵀP'y`: the triple `(κ, h, P') = (η l' - 2k', 2b' - η G', P')` with the values of `df2NextAP`. -/
noncomputable def refTest (p : Df2OPar) (so : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) :
    ℝ × (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ :=
  let w := so.A *ᵥ ξ
  let u := so.P *ᵥ w
  let g := (Y / (1 - p.lam)) • u
  let c := p.eta * p.kap * p.lam * p.k0 * Y
  let a := 1 - c
  let P' := a • so.P + c • vecMulVec u u
  let b' := so.b + c • ((u ⬝ᵥ so.mu) • u - so.P *ᵥ so.mu)
  let k' := so.k + c / 2 * ((u ⬝ᵥ so.mu) ^ 2 - so.mu ⬝ᵥ (so.P *ᵥ so.mu))
  let G' := so.G + g
  let l' := so.l + g ⬝ᵥ so.mu
  (p.eta * l' - 2 * k', 2 • b' - p.eta • G', P')

open Classical in
/-- The selection of the selection lemma for the concave quadratic `F y = κ + h·y - yᵀPy`, the threshold
`T` and the ball `(c0, r)`: BL's point `p` unless BL fires and `F p > T`; then the point of the segment from `p` to
`c0 + r v` (`v = -∇F(c0)/|∇F(c0)|`, the first basis vector if the gradient vanishes) where `F = T` first, the root
`t* = 2α₀/((α₁² + 4α₀α₂)^{1/2} - α₁)` of `α₀ + α₁ t - α₂ t² = F(p + t (q - p)) - T`. -/
noncomputable def selT (κ : ℝ) (h : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) (c0 : Fin d → ℝ) (r : ℝ)
    (p : Fin d → ℝ) (fire : Bool) : Fin d → ℝ :=
  let F := fun y : Fin d → ℝ => κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y)
  if fire = true ∧ T < F p then
    let gr := h - (P + Pᵀ) *ᵥ c0
    let v : Fin d → ℝ := if gr = 0 then fun i => if (i : ℕ) = 0 then 1 else 0 else (oNorm gr)⁻¹ • (-gr)
    let dv := (c0 + r • v) - p
    let α0 := F p - T
    let α1 := (h - (P + Pᵀ) *ᵥ p) ⬝ᵥ dv
    let α2 := dv ⬝ᵥ (P *ᵥ dv)
    p + (2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1)) • dv
  else p

/-- BL's line μ answer, read off the mode after the round: the mean of a continued state, else `0`. -/
def muOf : Mode d → Fin d → ℚ
  | .run st => if st.first then 0 else st.mu
  | _ => 0

/-- The advice of a round: for the test call, the selection `selT` of BL's test point for
P°'s test function at P°'s state `so`, draw `ξ` and observation `Y`, threshold `-θρ` and ball `(ctr°, r°)`; for line
μ, BL's answer. -/
noncomputable def advQ (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ)
    (obs : ℤ) (p : Df2OPar) (so : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) : Adv d :=
  (match testQ ap cfg st ξ' ζ' obs with
    | none => 0
    | some (pq, fire) =>
      selT (refTest p so ξ Y).1 (refTest p so ξ Y).2.1 (refTest p so ξ Y).2.2 (-(p.theta * p.rho)) so.ctr so.r
        (cV pq) fire,
   cV (muOf (step ap cfg n (.run st) ξ' ζ' obs)))

/-- P°'s observation of round `t` at its mode `.run so` on the world `ω` (the `Y` of `df2RoundGa`), with the coupled
dither `coupMax` of the record's shift. -/
noncomputable def refYW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) (so : Df2St d) : ℝ :=
  let q := posR R d n m A b (betaR R d n ω.1)
  let Xo := refX (po d n) so (ξc d t ω)
  let pto := refPt (po d n) (kW R d n m A b ω) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shW R d n m A b σ t ω (.run so)
  pto * (lossRW R d n m A b σ t ω xo + ω.2 t + coupMax sh.1 sh.2 (zc d t ω)) / 2 + 2 * (pto - 1) / (po d n).eps

/-- The advice of round `t` at P°'s mode `mo` before round `t`; `(0, 0)` unless both learners are in mode `run`. -/
noncomputable def advW (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (t : ℕ) (ω : WΩ) (mo : Df2Mode d) : Adv d :=
  match mo, modeW R d n m A b σ t ω with
  | .run so, .run st =>
    advQ R.ap (cfgW R d n m A b ω) n st (drawW R d n t ω).1 (drawW R d n t ω).2 (obsW R d n m A b σ t ω) (po d n) so
      (ξc d t ω) (refYW R d n m A b σ t ω so)
  | _, _ => (0, 0)

/-- BL's run record on the input `(d, n, m, A, b)` against the strategy `σ`. -/
noncomputable def blRun (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d) :
    Run d n (polytope A b) where
  F := blF R d n m A b σ
  pos ω := posR R d n m A b (betaR R d n ω.1)
  sh := shW R d n m A b σ
  adv := advW R d n m A b σ
  play t ω := toE (playW R d n m A b σ t ω)
  bits := Ebits R d n ∩ Zn n
  Coup := coupMax

/-- The instance of `BLInst`: the program `P`, the prologue length and block length of BL at `(d, n)`, the record. -/
noncomputable def blInst (P : List Instr) (R : Routines) : BLInst where
  P := P
  K0 := R.K0
  B d n := (par d n).B
  B_pos d n := by unfold par; simp only; omega
  run := blRun R


/-! ## Piece A: the constants and the precision theorem

At BL's `p = (par d n).p`, `B = (par d n).B`, with the
reference values of `po d n = df2oPar d n (deltaBL d n)` (equal to the reference values: `δe = 1/N_e`,
`Le = 36 ln N_e`, `κ_c = η κ λ k0`, part of piece A). Norms of matrices are spectral (`opN`). -/

namespace Bud

/-- `N_e = 1/δe`. -/
noncomputable def Ne (d n : ℕ) : ℝ := (BLP.Ne d n : ℝ)
/-- `δe`. -/
noncomputable def de (d n : ℕ) : ℝ := (po d n).δe
/-- `Le`. -/
noncomputable def Le (d n : ℕ) : ℝ := (po d n).Le
/-- `Λ = d N_e`. -/
noncomputable def Lam (d n : ℕ) : ℝ := d * Ne d n
/-- `λ`. -/
noncomputable def lam (d n : ℕ) : ℝ := (po d n).lam
/-- `η`. -/
noncomputable def eta (d n : ℕ) : ℝ := (po d n).eta
/-- `ε`. -/
noncomputable def eps (d n : ℕ) : ℝ := (po d n).eps
/-- `ρ`. -/
noncomputable def rho (d n : ℕ) : ℝ := (po d n).rho
/-- `R`. -/
noncomputable def R (d n : ℕ) : ℝ := (po d n).R
/-- `κ_c = η κ λ k0`, so that `c = κ_c Y`. -/
noncomputable def kc (d n : ℕ) : ℝ := (po d n).eta * (po d n).kap * (po d n).lam * (po d n).k0
/-- `Lgb = ln 14 + 5 Le/144`. -/
noncomputable def Lgb (d n : ℕ) : ℝ := Real.log 14 + 5 * Le d n / 144
/-- `Ξ = ((8d/3) Lgb)^{1/2}`. -/
noncomputable def Xi (d n : ℕ) : ℝ := Real.sqrt (8 * d / 3 * Lgb d n)
/-- `Ξ₁ = Ξ + 1`. -/
noncomputable def Xi1 (d n : ℕ) : ℝ := Xi d n + 1
/-- `P̄ = 2 Le^{1/2} + 1`. -/
noncomputable def Pb (d n : ℕ) : ℝ := 2 * Real.sqrt (Le d n) + 1
/-- `π̄ = Le^{1/2} + 1/8`. -/
noncomputable def pib (d n : ℕ) : ℝ := Real.sqrt (Le d n) + 1 / 8
/-- `Ȳ = 2 Le^{1/2}(1/2 + Lgb^{1/2}) + 4 Le^{1/2}/ε`. -/
noncomputable def Yb (d n : ℕ) : ℝ :=
  2 * Real.sqrt (Le d n) * (1 / 2 + Real.sqrt (Lgb d n)) + 4 * Real.sqrt (Le d n) / eps d n
/-- `c̄ = κ_c Ȳ`. -/
noncomputable def cb (d n : ℕ) : ℝ := kc d n * Yb d n
/-- `W° = R + 4d (N_e/Le)^{1/2}`. -/
noncomputable def W0 (d n : ℕ) : ℝ := R d n + 4 * d * Real.sqrt (Ne d n / Le d n)
/-- `u = 2^{-p}`. -/
noncomputable def tp (d n : ℕ) : ℝ := 1 / 2 ^ (par d n).p
/-- `ê = 2^{-p + 3ℓe + 6ℓd + 64}`. -/
noncomputable def eh (d n : ℕ) : ℝ := ((par d n).eHat : ℝ)
/-- E1: `e_ξ = d^{1/2} 2^{2 - B/2}` (in norm). -/
noncomputable def exi (d n : ℕ) : ℝ := Real.sqrt d * (4 / 2 ^ ((par d n).B / 2))
/-- E1: `e_ζ = 2^{1 - B/2}`. -/
noncomputable def ezt (d n : ℕ) : ℝ := 2 / 2 ^ ((par d n).B / 2)
/-- E2: `e_Y`. -/
noncomputable def eY (d n : ℕ) : ℝ := tp d n / 2 + Pb d n / 2 * (tp d n + ezt d n)
/-- E3: `Δ_c`. -/
noncomputable def Dc (d n : ℕ) : ℝ := cb d n * tp d n * (11 / 10 * (Pb d n + 1) / Yb d n + 1 / 16)
/-- E3: `e_N`. -/
noncomputable def eN (d n : ℕ) : ℝ :=
  tp d n * (1001 / 1000 + 51 / 100 * Xi1 d n ^ 2) + 143 / 100 * (1 + Xi1 d n ^ 2) * Dc d n +
    285 / 100 * cb d n * Xi1 d n * exi d n
/-- E4: `ν = d 2^{-p-1}`. -/
noncomputable def nu (d n : ℕ) : ℝ := d * tp d n / 2
/-- E5: `h_a`. -/
noncomputable def ha (d n : ℕ) : ℝ := tp d n * (Real.sqrt (8 * Le d n) + 1) + tp d n / 16
/-- E5: `x = n Λ e_N`. -/
noncomputable def x (d n : ℕ) : ℝ := n * Lam d n * eN d n
/-- E5: `V = n Λ^{1/2} ν`. -/
noncomputable def V (d n : ℕ) : ℝ := n * Real.sqrt (Lam d n) * nu d n
/-- E5: `ℏ = h_a + V + 2x(2 + h_a)`. -/
noncomputable def hb (d n : ℕ) : ℝ := ha d n + V d n + 2 * x d n * (2 + ha d n)
/-- The bound of the tracking lemma after `k` rounds of an epoch, `(1 + h_a + k Λ^{1/2} ν)(1 + Λ e_N)^k - 1`. -/
noncomputable def hTr (d n k : ℕ) : ℝ :=
  (1 + ha d n + k * Real.sqrt (Lam d n) * nu d n) * (1 + Lam d n * eN d n) ^ k - 1
/-- E6: `X̄`. -/
noncomputable def Xb (d n : ℕ) : ℝ :=
  Real.sqrt (Lam d n) * (hb d n * Xi1 d n + exi d n) +
    tp d n / 16 * lam d n * (1 + hb d n) * Real.sqrt (Lam d n) * Xi1 d n
/-- E7: `Δ_u`. -/
noncomputable def Du (d n : ℕ) : ℝ := Real.sqrt (Lam d n) * (hb d n * Xi1 d n + exi d n)
/-- E8: `Δ_P`. -/
noncomputable def DP (d n : ℕ) : ℝ := (2 * hb d n + hb d n ^ 2) * Lam d n
/-- E9: `e_b`. -/
noncomputable def eb (d n : ℕ) : ℝ :=
  Real.sqrt d * tp d n / 2 + Dc d n * R d n * (103 / 100) * Lam d n * (Xi1 d n ^ 2 + 1) +
    cb d n * R d n * (203 / 100 * Real.sqrt (Lam d n) * Xi1 d n * Du d n + DP d n)
/-- E9: `e_k`. -/
noncomputable def ek (d n : ℕ) : ℝ :=
  tp d n / 2 + Dc d n * R d n ^ 2 * (103 / 100) * Lam d n * (Xi1 d n ^ 2 + 1) / 2 +
    cb d n / 2 * R d n ^ 2 * (203 / 100 * Real.sqrt (Lam d n) * Xi1 d n * Du d n + DP d n)
/-- E11: `e_g`. -/
noncomputable def eg (d n : ℕ) : ℝ :=
  Real.sqrt d * tp d n / 2 + 101 / 100 * (eY d n + Yb d n * tp d n / 16) * (101 / 100) * Real.sqrt (Lam d n) * Xi1 d n +
    101 / 100 * Yb d n * Du d n
/-- E11: `e_l`. -/
noncomputable def el (d n : ℕ) : ℝ := tp d n / 2 + R d n * eg d n
/-- E11: `Ḡ`. -/
noncomputable def Gb (d n : ℕ) : ℝ := n * (101 / 100) * Yb d n * Real.sqrt (Lam d n) * Xi d n
/-- E12: `e_Φ`. -/
noncomputable def ePhi (d n : ℕ) : ℝ := R d n ^ 2 / 2 * DP d n + R d n * n * eb d n + n * ek d n
/-- E13: `e_X`. -/
noncomputable def eX (d n : ℕ) : ℝ :=
  eta d n * (101 / 100) * (n * el d n + R d n * n * eg d n) + eta d n * tp d n / 16 * (21 / 10) * R d n * Gb d n +
    2 * ePhi d n
/-- `w_ρ = 2^{-p-4} ρ`. -/
noncomputable def wr (d n : ℕ) : ℝ := tp d n / 16 * rho d n
/-- `w_ε = 2^{-p-4} ε`. -/
noncomputable def we (d n : ℕ) : ℝ := tp d n / 16 * eps d n
/-- E14: the Hausdorff gap `h`. -/
noncomputable def h (d n : ℕ) : ℝ :=
  R d n * (ePhi d n + eh d n + 8 * wr d n) + 2 * R d n ^ 3 * we d n / de d n ^ 2 + 2 * R d n * we d n
/-- `r_min = δe²/(2R(R + 1))`. -/
noncomputable def rmin (d n : ℕ) : ℝ := de d n ^ 2 / (2 * R d n * (R d n + 1))
/-- `Lip_F = 4R/δe²`. -/
noncomputable def LipF (d n : ℕ) : ℝ := 4 * R d n / de d n ^ 2
/-- E15: the left side of SEL. -/
noncomputable def sel (d n : ℕ) : ℝ := 4 * eh d n + LipF d n * h d n + wr d n
/-- E15: the right side of SEL, `(3/4)(δe/d) r_min²`. -/
noncomputable def selR (d n : ℕ) : ℝ := 3 / 4 * de d n / d * rmin d n ^ 2
/-- E16: `Δ_q`. -/
noncomputable def Dq (d n : ℕ) : ℝ := Dc d n * (1 + Xi1 d n ^ 2) + 202 / 100 * cb d n * Xi1 d n * exi d n
/-- E16: `Δs_5`. -/
noncomputable def Ds5 (d n : ℕ) : ℝ :=
  tp d n / 2 + 103 / 100 * eta d n * (eY d n + 3 * tp d n / 16 * Yb d n + Yb d n * Dq d n)
/-- E16: `Δ_w`. -/
noncomputable def Dw (d n : ℕ) : ℝ := Ds5 d n * Real.sqrt (Lam d n) * Xi d n + 103 / 100 * eta d n * Yb d n * Du d n
/-- E16: `Δ_F`. -/
noncomputable def DF (d n : ℕ) : ℝ :=
  (R d n + W0 d n + Dw d n) ^ 2 / 2 * DP d n + Lam d n * Dw d n * (2 * R d n + 2 * W0 d n + Dw d n) / 2
/-- E16: `L_F`. -/
noncomputable def LF (d n : ℕ) : ℝ := Lam d n * (R d n + W0 d n)
/-- E16: the left side of VAL. -/
noncomputable def val (d n : ℕ) : ℝ := 2 * DF d n + LF d n * h d n
/-- E16: the right side of VAL, `δe/(128 n² R² d)`. -/
noncomputable def valR (d n : ℕ) : ℝ := de d n / (128 * n ^ 2 * R d n ^ 2 * d)
/-- E17: `m_par`. -/
noncomputable def mpar (d n : ℕ) : ℝ := tp d n / 4 * pib d n * (R d n + 10) / eps d n
/-- E17: the regret transfer term. -/
noncomputable def reg (d n : ℕ) : ℝ := n / eps d n * ((1 + 2 * R d n) * Xb d n + 4 * R d n * pib d n * we d n)
/-- E17: `κ0 = (4/3)((2 + 16/ε) X̄ + m_par)` (`κ1 = 0`). -/
noncomputable def kap0 (d n : ℕ) : ℝ := 4 / 3 * ((2 + 16 / eps d n) * Xb d n + mpar d n)
/-- `δbits = 2^{-p-2}` (the lemma of the draws). -/
noncomputable def dbits (d n : ℕ) : ℝ := tp d n / 4

/-- The enclosures of the enclosure lemma: BL's rational parameters `par d n` against P°'s `po d n`,
relative error `2^{-p-4}` and the stated directions. -/
structure EncOK (d n : ℕ) : Prop where
  de_eq : de d n = 1 / Ne d n
  Le_eq : Le d n = 36 * Real.log (Ne d n)
  Le_le : ((par d n).Le : ℝ) ≤ Le d n
  Le_rel : |((par d n).Le : ℝ) / Le d n - 1| ≤ tp d n / 16
  eps_le : eps d n ≤ (par d n).eps
  eps_rel : ((par d n).eps : ℝ) ≤ eps d n * (1 + tp d n / 16)
  lam_rel : |((par d n).lam : ℝ) / lam d n - 1| ≤ tp d n / 16
  eta_rel : |((par d n).eta : ℝ) / eta d n - 1| ≤ tp d n / 16
  sig2_rel : |((par d n).sig2 : ℝ) / (po d n).sig2 - 1| ≤ tp d n / 16
  rho_le : ((par d n).rho : ℝ) ≤ rho d n
  rho_rel : |((par d n).rho : ℝ) / rho d n - 1| ≤ tp d n / 16
  kapc_rel : |((par d n).kapc : ℝ) / kc d n - 1| ≤ tp d n / 16
  nu_rel : |((par d n).nu : ℝ) * (1 - lam d n) - 1| ≤ tp d n / 16
  R_le : R d n ≤ (par d n).R
  R_rel : |((par d n).R : ℝ) / R d n - 1| ≤ tp d n / 16
  sb_le : ((par d n).sb : ℝ) ≤ (po d n).sb
  sb_rel : |((par d n).sb : ℝ) / (po d n).sb - 1| ≤ tp d n / 16
  W_le : W0 d n ≤ (par d n).W
  W_rel : |((par d n).W : ℝ) / W0 d n - 1| ≤ tp d n / 16
  A0 : |((par d n).A0 : ℝ) / Real.sqrt (po d n).sig2 - 1| ≤ tp d n * Real.sqrt (8 * Le d n) + tp d n / 16
  B0 : |((par d n).B0 : ℝ) * Real.sqrt (po d n).sig2 - 1| ≤ tp d n + tp d n / 16
  Lam_eq : ((par d n).Lam : ℝ) = Lam d n
  Ne_eq : ((par d n).Ne : ℝ) = Ne d n
  kap : (po d n).kap = 1 / 4
  k0 : (po d n).k0 = 1 / (1 - lam d n) ^ 2
  theta : (po d n).theta = 1
  alpha : (po d n).alpha = 1 / 4
  c1 : (po d n).c1 = 8
  gam : (po d n).gam = 1 / 100

/-- The precision theorem at `(d, n)`, with the enclosure lemma and the regime facts that the
proofs of pieces C and D read. Fields may be added on request of pieces C or D (then proved by piece A); none is
removed or weakened. -/
structure BudOK (d n : ℕ) : Prop where
  enc : EncOK d n
  /-- Regime: `Le ≥ 17467` (5.1 (F1)). -/
  Le_ge : 17467 ≤ Le d n
  /-- Regime: `log(14 n/δe) ≤ Lgb`. -/
  Lg_le : df2Lg (po d n) n ≤ Lgb d n
  /-- Regime: Lemma DOM at the bound `c̄`: `c̄ (1 + Ξ₁²) ≤ 10^{-30}`. -/
  cb_le : cb d n * (1 + Xi1 d n ^ 2) ≤ 1 / 10 ^ 30
  /-- (P1). -/
  x_le : x d n ≤ 1
  V_le : V d n ≤ 1
  hb_le : hb d n ≤ 1 / 100
  /-- The tracking lemma's bound stays below `ℏ` over an epoch. -/
  hTr_le : ∀ k ≤ n, hTr d n k ≤ hb d n
  /-- (P2) SEL. -/
  sel_le : sel d n ≤ selR d n
  /-- (P5). -/
  h_le : h d n ≤ rmin d n / 4
  /-- (P3) VAL. -/
  val_le : val d n ≤ valR d n
  /-- (P4). -/
  Xb_le : Xb d n ≤ 1 / 16
  reg_le : reg d n ≤ 1
  /-- The slack `ê`. -/
  ePhi_le : ePhi d n ≤ eh d n
  eX_le : eX d n ≤ eh d n
  /-- GUARD (E18). -/
  gT : d * DP d n ≤ Lam d n
  gW : Dw d n ≤ W0 d n
  gA : 11 / 10 ^ 35 + Dc d n * (1 + Xi1 d n ^ 2) ≤ 1 / 2
  /-- The coins: `n (⌈d/2⌉ + 1) 2^{-B/2} ≤ 2^{-p-2}`. -/
  coins : n * ((d + 1) / 2 + 1 : ℕ) * (1 / 2 ^ ((par d n).B / 2) : ℝ) ≤ dbits d n
  /-- The budget of `RunSpec.engine` with `δbits = 2^{-p-2}`, `κ0`, `κ1 = 0`. -/
  budget : n * (dbits d n + n * kap0 d n) ≤ 1 / 4
  /-- `κ0 ≥ 0` (asked by piece D: `RunSpec.engine`). -/
  kap0_nonneg : 0 ≤ kap0 d n

end Bud

/-- Piece A: the enclosure lemma and the precision theorem at every `(d, n)` of the case `RunCase`. -/
def BudA : Prop := ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → RunCase d n → Bud.BudOK d n

/-! ## Piece B: BL's draws -/

/-- Piece B, the probability (the lemma of the draws (b)): BL's draws of the rounds `< n` are unsound with
probability at most `2^{-p-2}` under the Gaussian stream. -/
def BitsB : Prop :=
  ∀ (R : Routines) (d n : ℕ), 1 ≤ d → 1 ≤ n → RunCase d n →
    μs (Measure.dirac 0) (Ebits R d n)ᶜ ≤ ENNReal.ofReal (Bud.dbits d n)

/-- Piece B, the measurability: BL's draw `ξ'_t` is a function of the draw group `ξg d t`. -/
def MeasDrawB : Prop :=
  ∀ (R : Routines) (d n t : ℕ),
    Measurable[MeasurableSpace.comap (ξg d t) inferInstance] fun ω : WΩ => (drawW R d n t ω).1

/-! ## Piece C: one round of BL against one round of P°'s epoch -/

/-- The tracking relation (the tracking lemma) between BL's state `st` and P°'s
state `so` after `k` rounds of their common epoch: the same epoch position and mean; P°'s exact invariants
`S° = A°A°ᵀ`, `P° S° = I`; BL's pair `A' = (I + H) A°`, `B' = (I + H^B) B°` with `B° = P° A° = (A°)^{-T}` and both
right relative errors within `hTr k`; the fields `b, k, G, l` within `k` times their error per round. -/
structure Track (d n : ℕ) (st : St d) (so : Df2St d) (k : ℕ) : Prop where
  first : st.first = so.first
  mu : cV st.mu = so.mu
  S_eq : so.S = so.A * so.Aᵀ
  PS : so.P * so.S = 1
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.A = (1 + H) * so.A ∧ opN H ≤ Bud.hTr d n k
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.B = (1 + H) * (so.P * so.A) ∧ opN H ≤ Bud.hTr d n k
  errb : oNorm (cV st.b - so.b) ≤ k * Bud.eb d n
  errk : |(st.k : ℝ) - so.k| ≤ k * Bud.ek d n
  errG : oNorm (cV st.G - so.G) ≤ k * Bud.eg d n
  errl : |(st.l : ℝ) - so.l| ≤ k * Bud.el d n

/-- Piece C, the play (the tracking lemma and E6): in the setting of `RoundC`, before the round is
observed, BL's point `X' = μ' + (1 - λ') A' ξ'` is within `X̄` of P°'s `X°_s`. It reads neither the loss nor the
observation nor the routine of the round, so it holds at every round before the first decoupling (the shift clause of
`EngineHyp`). -/
def PlayC : Prop :=
  ∀ (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ),
    1 ≤ d → 1 ≤ n → RunCase d n → Bud.BudOK d n →
    PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs)) →
    s < n →
    DetHyp (df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap)
      (deltaBL d n) π (s + 1) →
    (df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap).tau π (s + 1) = s →
    Track d n st ((df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap).st π s)
      s →
    (∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ eXi0 d n) →
    oNorm (cV (XQ (cfgOf R d n m A b cs) st ξ') -
      (df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap).X π s) ≤ Bud.Xb d n

/-- Piece C, the round: one round. Let BL be in mode `run st` before a round and P°'s virtual epoch (context `c`, path `π`, on
P°'s body `kTh` at BL's position, with the routines `ap`) be at its round `s < n`, with `DetHyp` at the horizon
`s + 1` and `τ(s + 1) = s` (the horizon lemma (c)), and `Track` at `s`. The round's loss `f` is admissible
and is the path's loss; BL's draws are within `e_ξ`, `e_ζ` of the path's draw and of `Z/2`; P°'s observation is BL's
exact observation (the coupled, noiseless round); P°'s routine of round `s` is the checked advice `advQ` of the round.
Then either both fire (both restart) or both continue with `Track` at
`s + 1`. The hypotheses `hrows`, `hpos`, `hgauge` are the rows lemma of BL on `Case` (proved in piece D). -/
def RoundC : Prop :=
  ∀ (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z : ℝ) (f : E d → ℝ),
    1 ≤ d → 1 ≤ n → RunCase d n → Bud.BudOK d n → O3SpecQ R.ap →
    PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs)) →
    (∀ y : Fin d → ℝ, (∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (cfgOf R d n m A b cs).β i) ↔
      pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs) (WithLp.toLp 2 y) ∈ polytope A b) →
    (∀ i, 0 < (cfgOf R d n m A b cs).β i) →
    (∀ X : Fin d → ℚ, (gaugeQ (cfgOf R d n m A b cs) X : ℝ) =
      gauge (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) (WithLp.toLp 2 (cV X))) →
    s < n →
    DetHyp (df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap)
      (deltaBL d n) π (s + 1) →
    (df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap).tau π (s + 1) = s →
    Track d n st ((df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap).st π s)
      s →
    AdmLoss (polytope A b) f →
    (∀ y, π.g s y = f (pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs) y) / 2) →
    (∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ eXi0 d n) → |(ζ' : ℝ) - Z / 2| ≤ eZt0 d n →
    let c := df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap
    let cfg := cfgOf R d n m A b cs
    let pt' : ℝ := ptQ cfg (XQ cfg st ξ')
    let fx : ℝ := f (toE (playPt cfg (.run st) ξ'))
    let obs : ℤ := ⌊(2 : ℝ) ^ cfg.par.p * fx⌋
    c.Y π s = pt' * (fx + Z / 2) / 2 + 2 * (pt' - 1) / (cfg.par.eps : ℝ) →
    ap s = apAdv (advQ R.ap cfg n st ξ' ζ' obs c.p (c.st π s) (π.xi s) (c.Y π s)) →
    (step R.ap cfg n (.run st) ξ' ζ' obs = .run (init cfg.par d) ∧ c.fire π s) ∨
      ∃ st' : St d, step R.ap cfg n (.run st) ξ' ζ' obs = .run st' ∧ c.cont π s ∧
        Track d n st' (c.st π (s + 1)) (s + 1)

/-! ## The position routine: the requirement of `PosInst` -/

/-- What `PosInst (blInst P R)` asks of BL's position routine (for the routine that provides `R.pos`): TRI-OGD staged
(`triPos` of Bit/TriStage.lean) on rows of `K`, at a frame centre `c` with `B̄(c, 1/2) ⊆ K`, with an integer
`ℓ ≥ log (m_st/δpos)` for some `δpos` with `n δpos ≤ 1/4`, reading the first `m_st L ≤ K0 d n` coins, and
`posR R` equal to its output on every coin sequence. -/
def PosTri (R : Routines) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b → RunCase d n →
    ∃ (m' : ℕ) (α : Fin m' → E d) (β' : Fin m' → ℝ) (c : E d) (ℓ : ℕ) (δpos : ℝ),
      polytope A b = {y | ∀ k, inner ℝ (α k) y ≤ β' k} ∧ Metric.closedBall c (1 / 2) ⊆ polytope A b ∧
      0 < δpos ∧ (n : ℝ) * δpos ≤ 1 / 4 ∧ Real.log (triMst (1 / 2) n / δpos) ≤ ℓ ∧
      triMst (1 / 2) n * triL d ℓ ≤ R.K0 d n ∧
      ∀ cs : ℕ → Bool, posR R d n m A b cs = triPos α β' c (1 / 2) n ℓ cs

end AdversarialBco.Bit.BLP
