/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly
public import AdversarialBco.Poly.PgProc
public import AdversarialBco.Poly.Df2Oracle
public import AdversarialBco.Poly.Df2

@[expose] public section

/-!
# DF2-O: the learner as a function of its inputs, and the split of Theorem POLY32-O

The learner DF2-O[AP], with AP = `apCall` of `Df2Oracle.lean` (ELL-cap for `d ≥ 2`, ELL-1
for `d = 1`), written as a function of the inputs `d, n, r₀, R₀, δ`, the body `K` (read through membership only),
the losses, the noise and the Gaussian stream: the world `w : World d` of the frozen machine
(`AdversarialBco/StatementPoly.lean`). It is the object that the machine layer proves a program equal to
(`Df2OMachine`), and that the analysis proves the regret of (`Df2ORegretMeas`); `theoremPoly32O_of_df2oMeas` composes
the two. The clause "every point played is in `K`" holds by the definition of the learner (`df2oPlay_mem`), so
`Df2ORegret`, the regret with that clause, follows from `Df2ORegretMeas` (`df2oRegret_of_meas`).

The analysis takes two inputs from other files: Theorem 8.3 (Theorem 8.3 of the paper; its Lean parts in
`PgLemmas.lean` and `PosGauss.lean`) for the position, and `PropAP` of `Df2Oracle.lean` ((SPEC-AP) for `apCall`) at
the arguments of the two calls of `df2Next`, the test call on `R⁻_t` and line `μ` on `R_{t+1}`: the regret of part
A of Theorem POLY32-DF2-O is stated for every AP that meets (SPEC-AP).

## The learner

1. Positioning: `pg d K r₀ R₀ δ₁` on a fixed block
   of the stream (below). If it returns no position, the learner plays `o = 0` in every round.
2. The regime: if `ε > 1/2` it plays `o` in every round.
3. Otherwise it runs DF2 on `K' = K~ ∩ B_R`, `K~ = posBody K μ_S A_S` the positioned body,
   `R = 134 d (log (2d + 2))^{1/2}`, in the positioned coordinates (`Fin d → ℝ` and matrices, as `Df2R1.lean`),
   with the changes: the gauge `pt` with `j` bisection steps (`piTilde` on `K'`), the dither, the play
   test, the two calls of AP (the test call on `R⁻_t` with accuracy `min (1, αρ/2)`, line `μ` on `R_{t+1}` with accuracy
   `e_t^val`), the ball `(ctr_t, r_t)`, and the guard of four tests (T1') `a_t ≤ 0`, `q_t ≤ 0`, `tr P_{t+1} > d/δ_e`,
   `tr Σ_{t+1} > d/δ_e`; (T2) `|w_t| > R + η (16 d n L_e/δ_e)^{1/2}`; (T2z) `|z_t| > R/δ_e³`; (T4) a call of AP
   fails. After an act of the guard the learner plays `S⁻¹(0) = μ_S` (after the play test) in every later round; a
   play test that fails makes it play `o` in this round and every later one. A fire of the restart test
   `Ξ_t(p_t) ≤ -θρ` starts a new epoch at the next round. The order inside a round is that of Algorithm 8.2.

The state of an epoch (`Df2St`): `μ_t`, `P_t`, `Σ_t`, the factor `A_t`, the quadratic
`Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`, `Ĝ_{t-1}`, `l_{t-1}`, the ball `(ctr_t, r_t)`, and whether `t` is
the first round of its epoch (then `R⁻_t = K_ε`). `Df2Mode`: off (`o` played), guard (`μ_S` played), or a state.
`df2oFrom a m s` is the mode before round `a + s` of the run started in the mode `m` before round `a`; the run of the
learner is `df2oFrom 0 (df2oMode0 ..)`, and an epoch started at round `a` is `df2oFrom a (.run (df2Init ..))`.

## Parameters

`δ₁ = min (δ/3, e^{-14} (d n)^{-3})` (the confidence of the learner: Theorem POLY32-DF2 asks `δ ≤ e^{-14} (dn)^{-3}`,
and part A of Theorem POLY32-DF2-O spends `3 δ₁`), `δ_e = 4 δ₁/(5n)`, `L_e = C₀ log (1/δ_e)` (`C₀ = df2C0 = 36`),
`C_λ = 725`, `C_σ = 8`, `C_ε = 20 C_λ`, `λ = 1/(C_λ d L_e²)`, `η = d^{1/2}/(L_e n^{1/2})`, `σ² = 1/(C_σ L_e)`,
`ρ = 2 C_λ d² L_e³`, `ε = C_ε d^{3/2} L_e⁵/n^{1/2}`, `κ = 1/4`, `θ = 1`, `α = 1/4`, `c₁ = 8`, `γ = 1/100`,
`κ₀ = (1 - λ)^{-2}`, `R = 134 d (log (2d + 2))^{1/2}`, `j = ⌈log₂ (n R (R + 7)/(δ₁ ε))⌉`, `s_b = δ_e²/(R (R + 1))`.

## The draws

The stream `gs` is read in fixed blocks: first the block of PG, `N₀` terms
(`df2oN0`): for each stage `i < m`, each repeat `r < J`, the `N_i` descent vectors and then the `m_T` verdicts of
`n_{T,i}` test vectors, `d` terms each, in this order (`df2oIdxA`, `df2oIdxT`); then `d + 1` terms per round `t`:
`ξ_t` (`d` terms) and the dither `ζ_t = g/2` (`df2oXi`, `df2oZeta`). PG's stream `ω` (`df2oOmega`) takes every entry
outside these ranges (`i ≥ m`, `r ≥ J`, `k ≥ N_i`, `v ≥ m_T`, `k ≥ n_{T,i}`) from its own term at or after
`N₀ + n (d + 1)` (`df2oSpare`, through `Nat.pair`); an entry inside them that `pg` never reads (the descent vector
`N_i - 1` of a repeat) keeps its term in the block. So the index maps
`df2oIdxA` and `df2oIdxT` are injective with disjoint images, and these images miss the terms of the rounds `t < n`:
the image of `gaussStream` under the map to `ω` is `pgMeasure`, independent of the draws of the rounds `t < n` (to be
proved in the analysis).

## Junk values

`x / 0 = 0`, `Real.sqrt` of a negative number is `0`, `Real.log` and `Real.logb` read `|x|`, `⌈x⌉₊ = 0` for `x ≤ 0`.
For `d, n ≥ 1` and `0 < δ`: `δ₁, δ_e > 0`, `δ_e < 1`, so `L_e > 0` and `λ, η, σ², ρ, ε, R > 0`; `λ < 1`. The divisions
of a round: by `1 - ε` only when `ε ≤ 1/2`; by `pt ≥ 1`; by `1 - λ`; by `a_t`, `q_t` and the square roots of `a_t`
and `a_t/q_t` only after (T1') has checked `a_t > 0` and `q_t > 0`. `piTilde` returns `0` at `0`, so `pt = 1` there.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM

variable {d : ℕ}

/-! ## Parameters -/

/-- The parameters of the learner at `(d, n, δ)`. -/
structure Df2OPar where
  δ1 : ℝ
  δe : ℝ
  Le : ℝ
  lam : ℝ
  eta : ℝ
  sig2 : ℝ
  rho : ℝ
  eps : ℝ
  kap : ℝ
  theta : ℝ
  alpha : ℝ
  c1 : ℝ
  gam : ℝ
  k0 : ℝ
  R : ℝ
  sb : ℝ
  j : ℕ

/-- `C_λ = 725`. -/
noncomputable def df2oClam : ℝ := 725

/-- The parameters of the module docstring. -/
noncomputable def df2oPar (d n : ℕ) (δ : ℝ) : Df2OPar :=
  let δ1 := min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)
  let δe := 4 * δ1 / (5 * n)
  let Le := df2C0 * Real.log (1 / δe)
  let lam := 1 / (df2oClam * d * Le ^ 2)
  let eps := 20 * df2oClam * (d * Real.sqrt d) * Le ^ 5 / Real.sqrt n
  let R := 134 * d * Real.sqrt (Real.log (2 * d + 2))
  { δ1 := δ1, δe := δe, Le := Le, lam := lam, eta := Real.sqrt d / (Le * Real.sqrt n), sig2 := 1 / (8 * Le),
    rho := 2 * df2oClam * d ^ 2 * Le ^ 3, eps := eps, kap := 1 / 4, theta := 1, alpha := 1 / 4, c1 := 8,
    gam := 1 / 100, k0 := ((1 - lam) ^ 2)⁻¹, R := R, sb := δe ^ 2 / (R * (R + 1)),
    j := ⌈Real.logb 2 (n * R * (R + 7) / (δ1 * eps))⌉₊ }

/-! ## The block of the positioning -/

/-- The confidence of each stage of PG, `δ₁/m`. -/
noncomputable def df2oPgDelta (r0 R0 δ1 : ℝ) : ℝ := δ1 / pgStages r0 R0

/-- The vectors of one repeat of stage `i`: `N_i + m_T n_{T,i}`. -/
noncomputable def df2oPgW (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ :=
  pgNs d (pgRhoStage d i) + pgMT δ' * pgNT d (pgRhoStage d i)

/-- The terms of stage `i`: `J (N_i + m_T n_{T,i}) d`. -/
noncomputable def df2oPgBlock (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ := pgJr δ' * df2oPgW d δ' i * d

/-- The first term of stage `i`. -/
noncomputable def df2oPgOff (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ := ∑ i' ∈ Finset.range i, df2oPgBlock d δ' i'

/-- `N₀`, the terms of the block of PG. -/
noncomputable def df2oN0 (d : ℕ) (r0 R0 δ1 : ℝ) : ℕ := df2oPgOff d (df2oPgDelta r0 R0 δ1) (pgStages r0 R0)

/-- The first term not read by the rounds `t < n`: `N₀ + n (d + 1)`. The spare entries of `ω` live from there on, and a
round `t ≥ n` reads them: a lemma on the positioning and the rounds holds below round `n` only. -/
noncomputable def df2oSpare (d n : ℕ) (r0 R0 δ1 : ℝ) : ℕ := df2oN0 d r0 R0 δ1 + n * (d + 1)

open Classical in
/-- The term of the stream that holds coordinate `c` of descent vector `k` of repeat `r` of stage `i`. -/
noncomputable def df2oIdxA (d n : ℕ) (r0 R0 δ1 : ℝ) (i r k : ℕ) (c : Fin d) : ℕ :=
  let δ' := df2oPgDelta r0 R0 δ1
  if i < pgStages r0 R0 ∧ r < pgJr δ' ∧ k < pgNs d (pgRhoStage d i) then
    df2oPgOff d δ' i + (r * df2oPgW d δ' i + k) * d + c
  else df2oSpare d n r0 R0 δ1 + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c)

open Classical in
/-- The term of the stream that holds coordinate `c` of test vector `k` of verdict `v` of repeat `r` of stage `i`. -/
noncomputable def df2oIdxT (d n : ℕ) (r0 R0 δ1 : ℝ) (i r v k : ℕ) (c : Fin d) : ℕ :=
  let δ' := df2oPgDelta r0 R0 δ1
  if i < pgStages r0 R0 ∧ r < pgJr δ' ∧ v < pgMT δ' ∧ k < pgNT d (pgRhoStage d i) then
    df2oPgOff d δ' i + (r * df2oPgW d δ' i + pgNs d (pgRhoStage d i) + v * pgNT d (pgRhoStage d i) + k) * d + c
  else df2oSpare d n r0 R0 δ1 + Nat.pair (Nat.pair i r) (Nat.pair (2 * Nat.pair v k + 1) c)

/-- The stream of PG read off the Gaussian stream. -/
noncomputable def df2oOmega (d n : ℕ) (r0 R0 δ1 : ℝ) (gs : ℕ → ℝ) : ℕ → ℕ → PgRound d :=
  fun i r => (fun k => WithLp.toLp 2 fun c => gs (df2oIdxA d n r0 R0 δ1 i r k c),
    fun v k => WithLp.toLp 2 fun c => gs (df2oIdxT d n r0 R0 δ1 i r v k c))

/-- The position `(μ_S, A_S)` returned by PG, else `none`. -/
noncomputable def df2oPos (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Option (PgSp d) :=
  pg d w.K r0 R0 (df2oPar d n δ).δ1 (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 w.gs)

/-- `ξ_t`, the `d` terms of round `t`. -/
def df2oXi (N0 : ℕ) (gs : ℕ → ℝ) (t : ℕ) : Fin d → ℝ := fun c => gs (N0 + t * (d + 1) + c)

/-- The dither `ζ_t = g/2`, `g` the last term of round `t`. -/
noncomputable def df2oZeta (d N0 : ℕ) (gs : ℕ → ℝ) (t : ℕ) : ℝ := gs (N0 + t * (d + 1) + d) / 2

/-! ## One round -/

/-- The state of an epoch before round `t`. -/
structure Df2St (d : ℕ) where
  /-- `t` is the first round of its epoch. -/
  first : Bool
  mu : Fin d → ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  S : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  b : Fin d → ℝ
  k : ℝ
  G : Fin d → ℝ
  l : ℝ
  ctr : Fin d → ℝ
  r : ℝ

/-- The mode of the learner before a round. -/
inductive Df2Mode (d : ℕ)
  /-- `o = 0` is played: no position, the regime `ε > 1/2`, or a failed play test. -/
  | off
  /-- The guard has acted: `S⁻¹(0) = μ_S` is played after the play test. -/
  | guard
  /-- A round of DF2 from this state. -/
  | run (st : Df2St d)

/-- The start of an epoch: `μ₁ = 0`, `P₁ = I/σ²`, `Σ₁ = σ² I`, `A₁ = σ I`, `Φ₀ = |·|²/(2σ²)`, `Ĝ₀ = 0`, `l₀ = 0`,
the ball `(0, 1 - ε)`. -/
noncomputable def df2Init (p : Df2OPar) (d : ℕ) : Df2St d :=
  ⟨true, 0, p.sig2⁻¹ • 1, p.sig2 • 1, Real.sqrt p.sig2 • 1, 0, 0, 0, 0, 0, 1 - p.eps⟩

/-- `Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`. -/
noncomputable def df2Phi (P : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (k : ℝ) (y : Fin d → ℝ) : ℝ :=
  1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k

/-- The positioned body cut by `B_R`, `K' = K~ ∩ B_R`, in `E d`. -/
def df2Kp (K : Set (E d)) (Ps : PgSp d) (R : ℝ) : Set (E d) := {y | pgMu Ps + pgOp Ps y ∈ K ∧ ‖y‖ ≤ R}

/-- `K_ε = (1 - ε) K'`, in the coordinates `Fin d → ℝ`: `y/(1 - ε) ∈ K'`. -/
noncomputable def df2Keps (K : Set (E d)) (Ps : PgSp d) (R eps : ℝ) : Set (Fin d → ℝ) :=
  {y | WithLp.toLp 2 ((1 - eps)⁻¹ • y) ∈ df2Kp K Ps R}

open Classical in
/-- The rest of a round of DF2 after the observation `Y_t`, from the state `st`, the draw `ξ_t` and `w_t = A_t ξ_t`:
the scalars and (T1'); the updates and (T1') on the traces; `z_t` and (T2z); the test call and (T4); the restart test;
the ball, (T2), line `μ` and (T4). -/
noncomputable def df2Next (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) :
    Df2Mode d :=
  let u := st.P *ᵥ w
  let g := (Y / (1 - p.lam)) • u
  let c := p.eta * p.kap * p.lam * p.k0 * Y
  let a := 1 - c
  let q := a + c * (ξ ⬝ᵥ ξ)
  if a ≤ 0 ∨ q ≤ 0 then .guard else
  let P' := a • st.P + c • vecMulVec u u
  let S' := a⁻¹ • (st.S - (c / q) • vecMulVec w w)
  let c' := c / q / (1 + Real.sqrt (a / q))
  let A' := (Real.sqrt a)⁻¹ • (st.A - c' • vecMulVec w ξ)
  let b' := st.b + c • ((u ⬝ᵥ st.mu) • u - st.P *ᵥ st.mu)
  let k' := st.k + c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - st.mu ⬝ᵥ (st.P *ᵥ st.mu))
  let G' := st.G + g
  let l' := st.l + g ⬝ᵥ st.mu
  if d / p.δe < P'.trace ∨ d / p.δe < S'.trace then .guard else
  let z := S' *ᵥ (b' - (p.eta / 2) • G')
  if p.R / p.δe ^ 3 < oNorm z then .guard else
  let Rm : Set (Fin d → ℝ) :=
    if st.first then Keps else {y | y ∈ Keps ∧ df2Phi st.P st.b st.k y ≤ (p.c1 - p.gam) * p.rho}
  match apCall Rm st.ctr st.r p.R P' z (min 1 (p.alpha * p.rho / 2)) with
  | none => .guard
  | some pt =>
    if p.eta * (l' - G' ⬝ᵥ pt) - 2 * df2Phi P' b' k' pt ≤ -(p.theta * p.rho) then .run (df2Init p d) else
    let ctr' := (1 - p.sb) • pt
    let r' := p.sb * (1 - p.eps)
    let wmu := st.mu - (p.eta * Y / ((1 - p.lam) * q)) • w
    if p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm wmu then .guard else
    let Rp : Set (Fin d → ℝ) := {y | y ∈ Keps ∧ df2Phi P' b' k' y ≤ p.c1 * p.rho}
    match apCall Rp ctr' r' p.R P' wmu (1 / (16 * n ^ 2 * max 1 (4 * p.R ^ 2 * P'.trace))) with
    | none => .guard
    | some mu' => .run ⟨false, mu', P', S', A', b', k', G', l', ctr', r'⟩

open Classical in
/-- One round: the point played and the mode after it, from the position `Ps`, the loss `ft`, the noise `nt`, the
draws `ξ_t`, `ζ_t`, and the mode before it. In a round of DF2: the sample `X_t = μ_t + (1 - λ) A_t ξ_t`, the gauge
`pt(X_t) = max (1, π̃(X_t)/(1 - ε))`, the point `S⁻¹(X_t/pt(X_t)) = μ_S + A_S (X_t/pt(X_t))`, the play test, the
observation `O_t = f_t(x) + ε_t` and `Y_t = pt(X_t) (O_t + ζ_t)/2 + 2 (pt(X_t) - 1)/ε`, then `df2Next`. -/
noncomputable def df2Round (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) : Df2Mode d → E d × Df2Mode d
  | .off => (0, .off)
  | .guard => if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, .guard) else (0, .off)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - p.lam) • w
    let pt := max 1 (piTilde (df2Kp K Ps p.R) p.R p.j (WithLp.toLp 2 X) / (1 - p.eps))
    let x := pgMu Ps + pgOp Ps (WithLp.toLp 2 (pt⁻¹ • X))
    if x ∈ K then
      (x, df2Next p n (df2Keps K Ps p.R p.eps) st ξ w (pt * (ft x + nt + ζ) / 2 + 2 * (pt - 1) / p.eps))
    else (0, .off)

/-! ## The run -/

open Classical in
/-- The mode before round `0`: off if PG returns no position or `ε > 1/2`, else the start of an epoch. -/
noncomputable def df2oMode0 (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Df2Mode d :=
  match df2oPos d n r0 R0 δ w with
  | none => .off
  | some _ => if 1 / 2 < (df2oPar d n δ).eps then .off else .run (df2Init (df2oPar d n δ) d)

/-- Round `t` of the learner from the mode `m`. -/
noncomputable def df2oRoundAt (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2Round (df2oPar d n δ) n w.K ((df2oPos d n r0 R0 δ w).getD 0) (w.f t) (w.noise t)
    (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) m

/-- The mode before round `a + s` of the run started in the mode `m` before round `a`. -/
noncomputable def df2oFrom (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (df2oRoundAt d n r0 R0 δ w (a + s) (df2oFrom d n r0 R0 δ w a m s)).2

/-- The mode of the learner before round `t`. -/
noncomputable def df2oMode (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : Df2Mode d :=
  df2oFrom d n r0 R0 δ w 0 (df2oMode0 d n r0 R0 δ w) t

/-- The point played by the learner in round `t`. -/
noncomputable def df2oPlay (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : E d :=
  (df2oRoundAt d n r0 R0 δ w t (df2oMode d n r0 R0 δ w t)).1

/-- A run read from a later round: the run started in the mode `m` before round `a`, after `s` rounds, is the run
started in the mode it has reached before round `a + s`. -/
theorem df2oFrom_add (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) (m : Df2Mode d) (s s' : ℕ) :
    df2oFrom d n r0 R0 δ w a m (s + s') = df2oFrom d n r0 R0 δ w (a + s) (df2oFrom d n r0 R0 δ w a m s) s' := by
  induction s' with
  | zero => rfl
  | succ s' ih => rw [← Nat.add_assoc, df2oFrom, df2oFrom, ih, Nat.add_assoc]

/-- One round plays `0` or a point that passed the membership test of `K`. -/
theorem df2Round_mem (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (m : Df2Mode d) :
    (df2Round p n K Ps ft nt ξ ζ m).1 = 0 ∨ (df2Round p n K Ps ft nt ξ ζ m).1 ∈ K := by
  cases m with
  | off => exact Or.inl rfl
  | guard =>
    unfold df2Round
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl
  | run st =>
    unfold df2Round
    simp only
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl

/-- Every point played is in `K`, on every world whose body contains the ball `B(0, r₀)`, `r₀ > 0`. -/
theorem df2oPlay_mem (d n : ℕ) (r0 R0 δ : ℝ) (hr0 : 0 < r0) (K : Set (E d)) (hball : Metric.closedBall 0 r0 ⊆ K)
    (f : ℕ → E d → ℝ) (gs noise : ℕ → ℝ) (t : ℕ) : df2oPlay d n r0 R0 δ ⟨K, f, noise, gs⟩ t ∈ K := by
  have h0 : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self hr0.le)
  unfold df2oPlay df2oRoundAt
  rcases df2Round_mem (df2oPar d n δ) n K _ (f t) (noise t) _ _ _ with h | h
  · simp only at h ⊢; rw [h]; exact h0
  · exact h

/-! ## The split of Theorem POLY32-O -/

/-- The regret clause of `TheoremPoly32O` and its clause "every point played is in `K`", for the learner `df2oPlay`.
The second clause holds by definition (`df2oPlay_mem`); the analysis proves `Df2ORegretMeas`. -/
def Df2ORegret : Prop :=
  ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ f ∈ Advs K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ, ∀ t < n, df2oPlay d n r0 R0 δ ⟨K, f, noise, gs⟩ t ∈ K) ∧
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts K f (df2oPlay d n r0 R0 δ ⟨K, f, ω.2, ω.1⟩) n} ≤
        ENNReal.ofReal δ

/-- The analysis: the regret clause of `TheoremPoly32O` for the learner `df2oPlay`, the measure of the worlds of
regret above the bound. -/
def Df2ORegretMeas : Prop :=
  ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ f ∈ Advs K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts K f (df2oPlay d n r0 R0 δ ⟨K, f, ω.2, ω.1⟩) n} ≤
        ENNReal.ofReal δ

/-- The clause "every point played is in `K`" costs the analysis nothing. -/
theorem df2oRegret_of_meas (h : Df2ORegretMeas) : Df2ORegret := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf ν hν =>
    ⟨fun gs noise t _ => df2oPlay_mem d n r0 R0 δ hr0 K hball f gs noise t,
      hC d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf ν hν⟩⟩

/-- The machine layer: one program of the frozen machine whose points played are those of `df2oPlay` in the rounds
`t < n`, and which meets the cost clause of `TheoremPoly32O`, on every run. -/
def Df2OMachine : Prop :=
  ∃ (P : List Instr) (C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ f ∈ Advs K n, ∀ gs noise : ℕ → ℝ,
      CostOK P ⟨K, f, noise, gs⟩ (init d n r0 R0 δ) n
          (C' * ((d : ℝ) * n * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k)
          (C' * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k) ∧
        ∀ t < n, played P ⟨K, f, noise, gs⟩ (init d n r0 R0 δ) t = df2oPlay d n r0 R0 δ ⟨K, f, noise, gs⟩ t

/-- The regret reads the points of the rounds `t < n` only. -/
theorem regretPts_congr (K : Set (E d)) (f : ℕ → E d → ℝ) {x y : ℕ → E d} (n : ℕ) (h : ∀ t < n, x t = y t) :
    regretPts K f x n = regretPts K f y n := by
  unfold regretPts
  congr 1
  exact Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]

/-- Theorem POLY32-O from the analysis of DF2-O and its machine layer. -/
theorem theoremPoly32O_of_df2o (hR : Df2ORegret) (hM : Df2OMachine) : TheoremPoly32O := by
  obtain ⟨C, hC⟩ := hR
  obtain ⟨P, C', k, hP⟩ := hM
  refine ⟨P, C, C', k, fun d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf ν hν => ?_⟩
  obtain ⟨hK, hreg⟩ := hC d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf ν hν
  have hM' := hP d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf
  refine ⟨fun gs noise => ⟨(hM' gs noise).1, fun t ht => ?_⟩, ?_⟩
  · rw [(hM' gs noise).2 t ht]; exact hK gs noise t ht
  · refine le_of_eq_of_le ?_ hreg
    congr 1
    ext ω
    show (_ : ℝ) < _ ↔ (_ : ℝ) < _
    rw [regretPts_congr K f n (hM' ω.1 ω.2).2]

/-- Theorem POLY32-O from the regret clause of the analysis and the machine layer. -/
theorem theoremPoly32O_of_df2oMeas (hR : Df2ORegretMeas) (hM : Df2OMachine) : TheoremPoly32O :=
  theoremPoly32O_of_df2o (df2oRegret_of_meas hR) hM

end AdversarialBco.Poly
