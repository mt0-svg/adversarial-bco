/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Run
public import AdversarialBco.Poly.Df2R1
public import AdversarialBco.Poly.Wrapper
public import AdversarialBco.Poly.Df2Azuma

@[expose] public section

/-!
# DF2-O: the interface of the analysis, second layer

Interface statements for `Df2ORegretMeas` of `Df2Run.lean`, the regret clause of Theorem POLY32-O for the learner
`df2oPlay`. No proof here except definitional checks (`rfl`). The proofs go in `Df2Layer2Proof.lean`.

## The route

* DJ is `df2oPlay` (bisection gauge `piTilde`). D0 is the same learner with the exact gauge of `K'` (`df2zPlay`,
  through `df2RoundGa`): the learner E(A) on the instance `(f_t/2, (ε_t + ζ_t)/2)`. There is no
  reference learner: the one-epoch theorem is stated for every projection routine `ap` that meets
  `ApSpec` (the two clauses of `PropAP`), and D0 is the instance `ap = apCall`.
* One epoch, pathwise (`Df2Det`): the losses are any
  admissible functions, the projections are any `ap` with `ApSpec`, the five events are hypotheses
  on the path, and the conclusion is (a) and (b5') of the one-epoch statement (Appendix D.1 of the paper).
* One epoch, probability (`Df2E1Loc`, Statement E1-loc): on every instance of the setting (E) of Appendix D.1,
  with a body that is a function of the first sigma-field, the epoch fails (a) or (b5') with probability at most
  `(149/168) δ_e`. The class of the round map: (L1) `Df2EpochMeas`, (L2) and (L3) `ApSpec`. It follows from `Df2Det`
  and the five event budgets (`Df2EvGProp` to `Df2EvDQProp`) by a union bound.
* The run (Lemma 8.8): the virtual epoch of D0 started at each round `a < n` is an instance of (E) on the world,
  with the filtration of the run (Lemma NZ, `LemmaNZProd`); `Df2VEWorld` is the budget per start round on the
  world. The Azuma event of the run is `Df2AzWorld` (from `Df2AzumaEvent` and Lemma FR, `LemmaFR`). `Df2WorldDet`
  is the gluing with the regret: on every world of the case of the analysis where every virtual epoch meets (a) and
  (b5') and the Azuma event holds, the regret of D0 is at most `2 ρ/η + n ε + (2 n log(7/δ_e))^{1/2}`.
* DJ against D0 (`Df2PropG`): Lemma TV and Proposition G, at the `j` of the learner.
* The composition (`Df2Layer2Comp`): the leaves imply `Df2ORegretMeas`, with Theorem 8.3 for the positioning and
  the trivial bound outside the regime (`Df2Trivial`).

## Indices

Rounds are `0, 1, ...`; round `s` here is round `s + 1` of DF2. In an epoch, `c.mode π s` is the mode before
round `s` (`c.mode π 0` is the fresh state), `c.st π s` its state: `μ_s`, `P_s`, `A_s` here are `μ_{s+1}`,
`P_{s+1}`, `A_{s+1}` of DF2. The quantities computed in round `s` (`Y_s`, `a_s`, `q_s`, `ĝ_s`, `ŝ''_s`, the update
`P'`, `b'`, `k'`) carry the index `s`. `PBar k` is `P̄` after `k` rounds (`P̄_{k+1}` of DF2). `c.Phi π k` is the
quadratic before round `k` (`Φ_k` of DF2), and `c.PhiN π s` the one computed in round `s` (`Φ_{s+1}` of DF2). The
lower region of the test of round `s` is `{y ∈ K_ε : Φ_s(y) ≤ (c₁ - γ) ρ}` (`K_ε` at the first round of the epoch),
the region of line `μ` of round `s` is `{y ∈ K_ε : c.PhiN π s y ≤ c₁ ρ}`, as in `df2Next`. The ellipsoid set `S_t`
of DF2 (rounds `1, ..., t`) is `c.SS π (t - 1)` (rounds `0, ..., t - 1`). The stopping time `τ` and the events
read the rounds `s ≤ τ ≤ m - 1`, `m` the horizon of the epoch.

## Junk values

`x / 0 = 0`, `Real.sqrt` of a negative number is `0`, `Real.log` reads `|x|`. `gauge` is `0` on the empty set; on
the bodies of the analysis (`Df2Body`: `B̄(0, 1) ⊆ K ⊆ B̄(0, R)`, closed and convex) it is the Minkowski functional,
finite, with `|x|/R ≤ gauge K x ≤ |x|`. A mode other than `.run` has no state: `c.st` reads the fresh state there
(`Df2Mode.stOr`); every statement reads the state at rounds `s ≤ τ`, where the mode is `.run` (condition 4 of
`Df2Ctx.Cond`). `fderiv` of a function not differentiable at the point is `0`: the surrogates are of class `C²`
(`Df2SIFacts`, item X7). `τ = m - 1` when no condition fails before round `m`. A conditional expectation on a
sigma-field not below the ambient one is `0`: in `Df2SetE` the sigma-fields are below it (`Filtration`, and the
draw is measurable). The measure of a set that is not measurable is its outer measure: the budgets bound outer
measures, and a measurable event of the same measure exists (`exists_measurable_superset`). The parameters are
those of `df2oPar` and every statement is in the regime `ε ≤ 1/2`; there `L_e ≥ 504`, `δ_e ≤ e^{-14} (d n)^{-3}`,
`0 < λ < 1`.

## Inputs beyond Df2.lean, Lemma D.14, PropAP, Theorem 8.3 and the events

`Df2SIFacts` (the analytic facts on the extension and the surrogate),
`Df2PropG` (PO Lemma TV and Proposition G), `Df2ApCallMeas` (the measurability of the round map of DF2-O, (L1)),
`PgMeas` and `PgGoodMeas` (measurability of the positioning), `Df2AzumaEvent` (proved in `Df2AzumaProof.lean`).
`LemmaFR` and `LemmaNZProd` are standard facts proved in `Df2Layer2Proof.lean`. Condition 1 of the stopping time is taken
in this form: some minimiser of the cumulative surrogate over `K_ε` lies in the
next lower region; Lemma D.14 reads `xs` as any minimiser, so no measurable selection (Lemma MS) is asked for.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM

variable {d : ℕ}

/-! ## The levels and the rows -/

/-- `C_g = 4`. -/
noncomputable def df2Cg : ℝ := 4

/-- `log (14 n/δ_e)`, the level of the per-round events. -/
noncomputable def df2Lg (p : Df2OPar) (n : ℕ) : ℝ := Real.log (14 * n / p.δe)

/-- `B_n = λ L² [1 + (10 d n)^{1/2} + d² L/ε]`. -/
noncomputable def df2Bn (p : Df2OPar) (d n : ℕ) : ℝ :=
  p.lam * p.Le ^ 2 * (1 + Real.sqrt (10 * d * n) + (d : ℝ) ^ 2 * p.Le / p.eps)

/-- The level of Lemma LQ, `b₁ = 1 + (1/λ) [(11/20) (10 d n L)^{1/2} + (13/100) d^{3/2} L²/ε]`. -/
noncomputable def df2B1 (p : Df2OPar) (d n : ℕ) : ℝ :=
  1 + 1 / p.lam * (11 / 20 * Real.sqrt (10 * d * n * p.Le) + 13 / 100 * (d * Real.sqrt d) * p.Le ^ 2 / p.eps)

/-- `θ_n = 2 η B_n`. -/
noncomputable def df2ThN (p : Df2OPar) (d n : ℕ) : ℝ := 2 * p.eta * df2Bn p d n

/-- `dev' = η κ B_n/(2 L λ²)`. -/
noncomputable def df2DevP (p : Df2OPar) (d n : ℕ) : ℝ := p.eta * p.kap * df2Bn p d n / (2 * p.Le * p.lam ^ 2)

/-- `dev = b₁ + B_n/(4 L λ²)`. -/
noncomputable def df2Dev (p : Df2OPar) (d n : ℕ) : ℝ := df2B1 p d n + df2Bn p d n / (4 * p.Le * p.lam ^ 2)

/-- `dev_κ = b₁ + B_n/(8 L λ²)`. -/
noncomputable def df2DevK (p : Df2OPar) (d n : ℕ) : ℝ := df2B1 p d n + df2Bn p d n / (8 * p.Le * p.lam ^ 2)

/-- `stab = 2 C_g η² d n L`. -/
noncomputable def df2Stab (p : Df2OPar) (d n : ℕ) : ℝ := 2 * df2Cg * p.eta ^ 2 * d * n * p.Le

/-- `pri = R²/(2 σ²)`. -/
noncomputable def df2Pri (p : Df2OPar) : ℝ := p.R ^ 2 / (2 * p.sig2)

/-- The bound `M(K) ≤ 1.27 (d + 1)^{1/2}/d` of `PgGood` on the positioned body. -/
noncomputable def df2Mw (d : ℕ) : ℝ := 1.27 * Real.sqrt (d + 1) / d

/-- The rows in their oracle form, at the constants, and the
conditions on `δ_e` that the pathwise assembly reads, with `L = L_e`, `δ = δ_e`, `C₀ = 36`. The event Props are
stated at the parameters of `df2oPar` in the regime and carry their own conditions on `δ` inside their proofs. -/
structure Df2Rows (p : Df2OPar) (d n : ℕ) : Prop where
  pos_de : 0 < p.δe
  de_lt : p.δe < 1
  pos_lam : 0 < p.lam
  lam_le : p.lam ≤ 1 / 2
  pos_eta : 0 < p.eta
  eta_le : p.eta ≤ 1
  pos_sig2 : 0 < p.sig2
  pos_rho : 0 < p.rho
  pos_eps : 0 < p.eps
  eps_le : p.eps ≤ 1 / 2
  one_le_R : 1 ≤ p.R
  k0_le : p.k0 ≤ 21 / 20
  /-- R1 (on the positioned body, `M ≤ 1.27 (d + 1)^{1/2}/d`). -/
  r1 : 2 * d * p.sig2 * df2Mw d ^ 2 ≤ 1
  r2 : 2 * p.sig2 ≤ 1
  r3 : 8 / df2C0 * p.sig2 * p.Le ≤ 1
  r4 : 10 * Real.sqrt p.Le + Real.sqrt (8 / df2C0) * p.Le ≤ p.Le
  /-- R5p, with 352. -/
  r5p : 352 / df2C0 * d * p.Le ^ 2 / (p.lam * p.eta * p.eps) ≤ n
  /-- R6, with 8 (`Lip(e_t) ≤ 8/ε`). -/
  r6 : 8 * p.eta * p.lam * Real.sqrt (2 * d * p.sig2) / p.eps ≤ 1
  r6a : p.eta * p.lam * p.Le / (2 * p.eps) ≤ 1
  r6b : 2 / df2C0 * p.eta * p.lam * d * p.Le ^ 2 / p.eps ≤ 1
  r7 : p.Le ^ 3 / p.eps ^ 2 ≤ n
  r8 : (d : ℝ) ^ 2 * p.Le / p.eps ≤ Real.sqrt (d * n)
  r11 : p.lam ≤ 1 / (d * p.Le ^ 2)
  r12 : df2ThN p d n ≤ 1
  r14 : 1 / Real.sqrt n ≤ p.eps
  r15p : 84 / df2C0 ≤ df2Cg
  r17 : 8 / (p.kap * df2C0) ≤ 1
  /-- R19o, the row main with the defects. -/
  r19o : 2 * p.eta + d * p.Le / p.lam + df2Pri p + df2Stab p d n + p.eta * df2DevK p d n + 1 ≤ p.rho
  /-- R20, the margin. -/
  r20 : 2 * df2DevP p d n ≤ p.gam * p.rho
  /-- R21, the inclusion, strict. -/
  r21 : 16 * p.c1 * p.rho * p.Le * p.lam ^ 2 + 2 * df2ThN p d n < 1
  /-- R22, the row negative. -/
  r22 : 3 * p.eta + d * p.Le / p.lam + 10 * p.eta / (p.eps * p.lam) + 2 * df2Pri p + p.eta * df2Dev p d n ≤
    (p.theta - p.alpha) * p.rho
  /-- R24o, the row bonus with the defects. -/
  r24o : 2 * p.eta + 8 * df2Pri p + 7 * df2Stab p d n + 7 * (p.eta * df2DevK p d n) + 7 * (p.eta * df2Dev p d n) +
    df2DevP p d n + 7 * p.theta * p.rho + 7 ≤ (p.c1 - p.gam) * p.rho
  /-- R24b, the row of the ball (Lemma D.17). -/
  r24b : 3 + 2 * df2Pri p + df2Stab p d n + p.eta * df2DevK p d n + p.eta * df2Dev p d n + df2DevP p d n +
    p.theta * p.rho ≤ (p.c1 - p.gam) * p.rho
  /-- The condition. -/
  c22 : 22 * p.Le * p.δe / p.eps ^ 2 ≤ 1
  /-- The two conditions. -/
  c8 : 8 * p.δe / p.eps ≤ 1
  c16 : 16 * p.eta * p.lam * n * Real.sqrt (d * p.δe) / p.eps ≤ 1
  c4 : 4 * p.δe / p.sig2 ≤ 1
  /-- `ν = n δ/λ² ≤ 1`. -/
  cnu : n * p.δe / p.lam ^ 2 ≤ 1
  /-- The sum over the rounds of `2 δ d/λ` is at most 1 (W1). -/
  c2dl : 2 * p.δe * d * n / p.lam ≤ 1
  c500 : 500 * p.δe * (n : ℝ) ^ ((3 : ℝ) / 2) * d * p.Le ^ 2 ≤ 1
  cx : 14 + 3 * Real.log (d * n) ≤ Real.log (1 / p.δe)
  clg : df2Lg p n ≤ 4 / 3 * Real.log (1 / p.δe)
  /-- The row of Lemma D.18 at `x = log (1/δ_e)` (`Df2RowZ`). -/
  cz : 1 / 4 * Real.sqrt p.k0 * df2C0 * Real.sqrt (32 / 9) * p.δe ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
    Real.sqrt d * Real.log (1 / p.δe) ^ ((3 : ℝ) / 2) ≤ 3 / 4

/-- The rows hold at the parameters of the learner in the regime `ε ≤ 1/2` (Lemma D.15 of
the paper). -/
def Df2RowsHold : Prop :=
  ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → (df2oPar d n δ).eps ≤ 1 / 2 →
    Df2Rows (df2oPar d n δ) d n

/-! ## Round maps with a general gauge and a general projection routine -/

/-- The signature of a projection routine, that of `apCall`: region, centre and radius of the ball, outer radius,
the matrix and the point of the objective, the accuracy. -/
abbrev ApFun (d : ℕ) : Type :=
  Set (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) → ℝ → Option (Fin d → ℝ)

/-- (L2) and (L3): the two clauses of `PropAP` for the routine `ap`. (a) Under its hypotheses the
call returns a point of `Q` within `e` of the infimum of `ellF P w` over `Q`; (b) on every input it fails or returns
a point of `Q` of norm at most `R`. `PropAP` gives `ApSpec apCall` for `d ≥ 1`. -/
def ApSpec (ap : ApFun d) : Prop :=
  ∀ (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (e : ℝ),
    (Convex ℝ Q → IsClosed Q → 0 < r → oBall a0 r ⊆ Q → Q ⊆ oBall 0 R → P.PosDef → 0 < e →
      ∃ μ, ap Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, ellF P w μ ≤ ellF P w x + e) ∧
    (ap Q a0 r R P w e = none ∨ ∃ μ, ap Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ oNorm μ ≤ R)

open Classical in
/-- `df2Next` with the routine `ap` in place of `apCall`, line by line. -/
noncomputable def df2NextAP (ap : ApFun d) (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d)
    (ξ w : Fin d → ℝ) (Y : ℝ) : Df2Mode d :=
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
  match ap Rm st.ctr st.r p.R P' z (min 1 (p.alpha * p.rho / 2)) with
  | none => .guard
  | some pt =>
    if p.eta * (l' - G' ⬝ᵥ pt) - 2 * df2Phi P' b' k' pt ≤ -(p.theta * p.rho) then .run (df2Init p d) else
    let ctr' := (1 - p.sb) • pt
    let r' := p.sb * (1 - p.eps)
    let wmu := st.mu - (p.eta * Y / ((1 - p.lam) * q)) • w
    if p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm wmu then .guard else
    let Rp : Set (Fin d → ℝ) := {y | y ∈ Keps ∧ df2Phi P' b' k' y ≤ p.c1 * p.rho}
    match ap Rp ctr' r' p.R P' wmu (1 / (16 * n ^ 2 * max 1 (4 * p.R ^ 2 * P'.trace))) with
    | none => .guard
    | some mu' => .run ⟨false, mu', P', S', A', b', k', G', l', ctr', r'⟩

/-- Definitional check: `df2Next` is `df2NextAP apCall`. -/
theorem df2Next_eq_AP (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) :
    df2Next p n Keps st ξ w Y = df2NextAP apCall p n Keps st ξ w Y := rfl

open Classical in
/-- `df2Round` with the gauge `ga` in place of `piTilde (df2Kp K Ps p.R) p.R p.j` and the routine `ap` in place of
`apCall`. -/
noncomputable def df2RoundGa (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) : Df2Mode d → E d × Df2Mode d
  | .off => (0, .off)
  | .guard => if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, .guard) else (0, .off)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - p.lam) • w
    let pt := max 1 (ga (WithLp.toLp 2 X) / (1 - p.eps))
    let x := pgMu Ps + pgOp Ps (WithLp.toLp 2 (pt⁻¹ • X))
    if x ∈ K then
      (x, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ w (pt * (ft x + nt + ζ) / 2 + 2 * (pt - 1) / p.eps))
    else (0, .off)

/-- Definitional check: `df2Round` is `df2RoundGa` at the bisection gauge and `apCall`. -/
theorem df2Round_eq_Ga (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2Round p n K Ps ft nt ξ ζ m = df2RoundGa p n K Ps (piTilde (df2Kp K Ps p.R) p.R p.j) apCall ft nt ξ ζ m := by
  cases m <;> rfl

/-! ## D0: the learner with the exact gauge, on the world -/

/-- The position read off the world, `0` when PG returns none. -/
noncomputable def df2oPs (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : PgSp d := (df2oPos d n r0 R0 δ w).getD 0

/-- Round `t` of D0 from the mode `m`: `df2oRoundAt` with the exact gauge `gauge K'` of `K' = df2Kp K Ps R`. -/
noncomputable def df2zRoundAt (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa (df2oPar d n δ) n w.K (df2oPs d n r0 R0 δ w)
    (gauge (df2Kp w.K (df2oPs d n r0 R0 δ w) (df2oPar d n δ).R)) apCall (w.f t) (w.noise t)
    (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) m

/-- The mode of D0 before round `a + s`, started in the mode `m` before round `a`. -/
noncomputable def df2zFrom (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (df2zRoundAt d n r0 R0 δ w (a + s) (df2zFrom d n r0 R0 δ w a m s)).2

/-- The mode of D0 before round `t`. -/
noncomputable def df2zMode (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : Df2Mode d :=
  df2zFrom d n r0 R0 δ w 0 (df2oMode0 d n r0 R0 δ w) t

/-- The point played by D0 in round `t`. -/
noncomputable def df2zPlay (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : E d :=
  (df2zRoundAt d n r0 R0 δ w t (df2zMode d n r0 R0 δ w t)).1

/-! ## One epoch on a path (setting (E), pathwise) -/

/-- The context of an epoch: the parameters, the horizon `n` of the thresholds, the body `K~` (positioned), the
projection routine. -/
structure Df2Ctx (d : ℕ) where
  p : Df2OPar
  n : ℕ
  Kt : Set (E d)
  ap : ApFun d

/-- The context at the parameters of the learner. -/
noncomputable def df2CtxAt (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ApFun d) : Df2Ctx d :=
  ⟨df2oPar d n δ, n, Kt, ap⟩

/-- A path of the data of an epoch: the losses `g s` (on `E d`, positioned), the noise `e s` of the observation, the
draws `ξ s`. -/
structure Df2Path (d : ℕ) where
  g : ℕ → E d → ℝ
  e : ℕ → ℝ
  xi : ℕ → Fin d → ℝ

/-- `K_ε = (1 - ε) K~` in the coordinates `Fin d → ℝ`; `df2Keps K Ps R ε = df2KepsOf (df2Kp K Ps R) ε`. -/
def df2KepsOf (Kt : Set (E d)) (eps : ℝ) : Set (Fin d → ℝ) := {y | WithLp.toLp 2 ((1 - eps)⁻¹ • y) ∈ Kt}

/-- Definitional check. -/
theorem df2Keps_eq (K : Set (E d)) (Ps : PgSp d) (R eps : ℝ) : df2Keps K Ps R eps = df2KepsOf (df2Kp K Ps R) eps :=
  rfl

/-- The exact gauge `pip(x) = max (1, π(x)/(1 - ε))`. -/
noncomputable def df2Pip (p : Df2OPar) (Kt : Set (E d)) (x : E d) : ℝ := max 1 (gauge Kt x / (1 - p.eps))

/-- The extension: `e(x) = pip(x) g(x/pip(x)) + 2 (pip(x) - 1)/ε`. -/
noncomputable def df2Ext (p : Df2OPar) (Kt : Set (E d)) (g : E d → ℝ) (x : E d) : ℝ :=
  df2Pip p Kt x * g ((df2Pip p Kt x)⁻¹ • x) + 2 * (df2Pip p Kt x - 1) / p.eps

/-- One round of the epoch learner from a mode: the point played (positioned coordinates) and the next mode. In a
round of DF2: `X = μ + (1 - λ) A ξ`, the play `X/pip(X)`, `Y = pip(X) (g(X/pip(X)) + e) + 2 (pip(X) - 1)/ε`, then
`df2NextAP`. D0 on a world with a position of `G_pos` is this map at `g y = f_t(S⁻¹ y)/2`, `e = (ε_t + ζ_t)/2`. -/
noncomputable def df2RoundE (c : Df2Ctx d) (g : E d → ℝ) (e : ℝ) (ξ : Fin d → ℝ) :
    Df2Mode d → (Fin d → ℝ) × Df2Mode d
  | .off => (0, .off)
  | .guard => (0, .guard)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - c.p.lam) • w
    let pt := df2Pip c.p c.Kt (WithLp.toLp 2 X)
    (pt⁻¹ • X, df2NextAP c.ap c.p c.n (df2KepsOf c.Kt c.p.eps) st ξ w
      (pt * (g (WithLp.toLp 2 (pt⁻¹ • X)) + e) + 2 * (pt - 1) / c.p.eps))

/-- The state of a mode, the default `dflt` when the mode is not `.run`. -/
def Df2Mode.stOr : Df2Mode d → Df2St d → Df2St d
  | .run st, _ => st
  | _, dflt => dflt

namespace Df2Ctx

variable (c : Df2Ctx d) (π : Df2Path d)

/-- `K_ε` of the context. -/
def Keps : Set (Fin d → ℝ) := df2KepsOf c.Kt c.p.eps

/-- The mode before round `s` of the epoch started fresh before round `0`. -/
noncomputable def mode : ℕ → Df2Mode d
  | 0 => .run (df2Init c.p d)
  | s + 1 => (df2RoundE c (π.g s) (π.e s) (π.xi s) (mode s)).2

/-- The state before round `s` (`μ_s`, `P_s`, `A_s`, ...). -/
noncomputable def st (s : ℕ) : Df2St d := (c.mode π s).stOr (df2Init c.p d)

/-- `w_s = A_s ξ_s`. -/
noncomputable def w (s : ℕ) : Fin d → ℝ := (c.st π s).A *ᵥ π.xi s

/-- `X_s = μ_s + (1 - λ) w_s`. -/
noncomputable def X (s : ℕ) : Fin d → ℝ := (c.st π s).mu + (1 - c.p.lam) • c.w π s

/-- `pip(X_s)`. -/
noncomputable def pip (s : ℕ) : ℝ := df2Pip c.p c.Kt (WithLp.toLp 2 (c.X π s))

/-- The point played, `X_s/pip(X_s)`. -/
noncomputable def play (s : ℕ) : Fin d → ℝ := (c.pip π s)⁻¹ • c.X π s

/-- `Y_s = pip(X_s) (g_s(X_s/pip(X_s)) + e_s) + 2 (pip(X_s) - 1)/ε`. -/
noncomputable def Y (s : ℕ) : ℝ :=
  c.pip π s * (π.g s (WithLp.toLp 2 (c.play π s)) + π.e s) + 2 * (c.pip π s - 1) / c.p.eps

/-- `u_s = P_s w_s`. -/
noncomputable def u (s : ℕ) : Fin d → ℝ := (c.st π s).P *ᵥ c.w π s

/-- `c_s = η κ λ κ₀ Y_s`. -/
noncomputable def cc (s : ℕ) : ℝ := c.p.eta * c.p.kap * c.p.lam * c.p.k0 * c.Y π s

/-- `a_s = 1 - c_s`. -/
noncomputable def aa (s : ℕ) : ℝ := 1 - c.cc π s

/-- `q_s = a_s + c_s |ξ_s|²`. -/
noncomputable def qq (s : ℕ) : ℝ := c.aa π s + c.cc π s * (π.xi s ⬝ᵥ π.xi s)

/-- The update computed in round `s`, `P' = a_s P_s + c_s u_s u_sᵀ`. -/
noncomputable def Pn (s : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  c.aa π s • (c.st π s).P + c.cc π s • vecMulVec (c.u π s) (c.u π s)

/-- `b' = b + c_s (⟨u_s, μ_s⟩ u_s - P_s μ_s)`. -/
noncomputable def bn (s : ℕ) : Fin d → ℝ :=
  (c.st π s).b + c.cc π s • ((c.u π s ⬝ᵥ (c.st π s).mu) • c.u π s - (c.st π s).P *ᵥ (c.st π s).mu)

/-- `k' = k + (c_s/2) (⟨u_s, μ_s⟩² - μ_sᵀ P_s μ_s)`. -/
noncomputable def kn (s : ℕ) : ℝ :=
  (c.st π s).k + c.cc π s / 2 * ((c.u π s ⬝ᵥ (c.st π s).mu) ^ 2 - (c.st π s).mu ⬝ᵥ ((c.st π s).P *ᵥ (c.st π s).mu))

/-- The quadratic before round `k`, `Φ_k(y) = ½ yᵀ P y - bᵀ y + k` of the state before round `k`. -/
noncomputable def Phi (k : ℕ) (y : Fin d → ℝ) : ℝ := df2Phi (c.st π k).P (c.st π k).b (c.st π k).k y

/-- The quadratic computed in round `s` (`Φ_{s+1}` of DF2). -/
noncomputable def PhiN (s : ℕ) (y : Fin d → ℝ) : ℝ := df2Phi (c.Pn π s) (c.bn π s) (c.kn π s) y

/-- `ĝ_s = (Y_s/(1 - λ)) u_s`. -/
noncomputable def ghat (s : ℕ) : Fin d → ℝ := (c.Y π s / (1 - c.p.lam)) • c.u π s

/-- `ŝ''_s = λ κ₀ Y_s (u_s u_sᵀ - P_s)`; `P' = P_s + η κ ŝ''_s`. -/
noncomputable def shh (s : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (c.p.lam * c.p.k0 * c.Y π s) • (vecMulVec (c.u π s) (c.u π s) - (c.st π s).P)

/-- The surrogate of round `s`, at the law `N(μ_s, A_s A_sᵀ)`. -/
noncomputable def surr (s : ℕ) : E d → ℝ :=
  df2Surr (df2Ext c.p c.Kt (π.g s)) (WithLp.toLp 2 (c.st π s).mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A)
    c.p.lam

end Df2Ctx

/-- The gradient of `f` at `z` in the coordinates `Fin d → ℝ`. -/
noncomputable def df2GradM (f : E d → ℝ) (z : E d) : Fin d → ℝ :=
  fun i => fderiv ℝ f z (EuclideanSpace.single i 1)

/-- The Hessian of `f` at `z` as a matrix. -/
noncomputable def df2HessM (f : E d → ℝ) (z : E d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

namespace Df2Ctx

variable (c : Df2Ctx d) (π : Df2Path d)

/-- `s'_s(μ_s)`. -/
noncomputable def sGrad (s : ℕ) : Fin d → ℝ := df2GradM (c.surr π s) (WithLp.toLp 2 (c.st π s).mu)

/-- `s''_s(μ_s)`. -/
noncomputable def sHess (s : ℕ) : Matrix (Fin d) (Fin d) ℝ := df2HessM (c.surr π s) (WithLp.toLp 2 (c.st π s).mu)

/-- `ē_s`, the mean of the extension under the play `p'_s = N(μ_s, (1 - λ)² A_s A_sᵀ)`: what the paper writes
`E_{s-1}[e_s(X_s)]` (Lemma FR). -/
noncomputable def ebar (s : ℕ) : ℝ :=
  ∫ z, df2Ext c.p c.Kt (π.g s)
      (WithLp.toLp 2 (c.st π s).mu + (1 - c.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A z)
    ∂(stdGaussian (E d))

/-- `eReg_r(x) = ∑_{s ≤ r} (ē_s - e_s(x))`. -/
noncomputable def eReg (r : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (r + 1), (c.ebar π s - df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 x))

/-- `S_t(y) = ∑_{u ≤ t} s_u(y)`. -/
noncomputable def SumS (t : ℕ) (y : Fin d → ℝ) : ℝ := ∑ u ∈ Finset.range (t + 1), c.surr π u (WithLp.toLp 2 y)

/-- `P̄` after `k` rounds: `P̄ 0 = P_0`, `P̄ (s + 1) = P̄ s + η κ s''_s(μ_s)`. -/
noncomputable def PBar : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => (c.st π 0).P
  | s + 1 => PBar s + (c.p.eta * c.p.kap) • c.sHess π s

/-- `S_t` of DF2 over the rounds `0, ..., t`: `λ² |y - μ_u|²_{P_u} ≤ 1/(2L)` for `u ≤ t`. -/
def SS (t : ℕ) : Set (Fin d → ℝ) :=
  {y | ∀ u ≤ t, c.p.lam ^ 2 * df2Sq (c.st π u).P (y - (c.st π u).mu) ≤ 1 / (2 * c.p.Le)}

/-- `G_t(y) = ∑_{u ≤ t} (y - μ_u)ᵀ (ŝ''_u - s''_u(μ_u)) (y - μ_u)`. -/
noncomputable def GG (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range (t + 1), df2Sq (c.shh π u - c.sHess π u) (y - (c.st π u).mu)

/-- Round `s` continues the epoch: the next mode is a state that is not the first of an epoch. -/
def cont (s : ℕ) : Prop := ∃ st : Df2St d, c.mode π (s + 1) = .run st ∧ st.first = false

/-- The test fires at the end of round `s`: the next mode is the fresh state. -/
def fire (s : ℕ) : Prop := c.mode π (s + 1) = .run (df2Init c.p d)

/-- The four conditions of the stopping time at round `s`: (1) in the form NO-MS, some
minimiser of `S_s` over `K_ε` lies in the next lower region `{Φ_{s+1} ≤ (c₁ - γ) ρ}`; (2) `a_s > 0`, `q_s > 0`;
(3) `δ I ≤ ½ P̄ ≤ P' ≤ 2 P̄ ≤ I/δ` with `P̄ = PBar (s + 1)`, `P'` the update; (4) the round continues the epoch
(neither a fire nor an act of the guard). -/
def Cond (s : ℕ) : Prop :=
  (∃ x ∈ c.Keps, (∀ y ∈ c.Keps, c.SumS π s x ≤ c.SumS π s y) ∧ c.PhiN π s x ≤ (c.p.c1 - c.p.gam) * c.p.rho) ∧
  (0 < c.aa π s ∧ 0 < c.qq π s) ∧
  (((1 / 2 : ℝ) • c.PBar π (s + 1) - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (c.Pn π s - (1 / 2 : ℝ) • c.PBar π (s + 1)).PosSemidef ∧
    ((2 : ℝ) • c.PBar π (s + 1) - c.Pn π s).PosSemidef ∧
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (2 : ℝ) • c.PBar π (s + 1)).PosSemidef) ∧
  c.cont π s

open Classical in
/-- The stopping time at the horizon `m`: the first round `s < m` at which a condition fails, else `m - 1`. -/
noncomputable def tau (m : ℕ) : ℕ := if h : ∃ s, s < m ∧ ¬ c.Cond π s then Nat.find h else m - 1

/-! ### The events, on the path, at the levels of the epoch -/

/-- Noise and Pi and Gauss: for `s ≤ τ`, `|e_s| ≤ log(14n/δ)^{1/2}`, `π(X_s) ≤ L^{1/2}`,
`|ξ_s|² ≤ (8d/3) log(14n/δ)`. Budget `3δ/7`. -/
def EvG (m : ℕ) : Prop :=
  ∀ s ≤ c.tau π m, |π.e s| ≤ Real.sqrt (df2Lg c.p c.n) ∧ gauge c.Kt (WithLp.toLp 2 (c.X π s)) ≤ Real.sqrt c.p.Le ∧
    π.xi s ⬝ᵥ π.xi s ≤ 8 * d / 3 * df2Lg c.p c.n

/-- Y: `∑_{s ≤ τ} Y_s² ≤ 22 n`. Budget `δ/7`. -/
def EvY (m : ℕ) : Prop := ∑ s ∈ Finset.range (c.tau π m + 1), c.Y π s ^ 2 ≤ 22 * c.n

/-- LQ (Lemma LQ): for `t ≤ τ` and `y` in `B_R` and in `S_t`,
`|∑_{u ≤ t} ⟨ĝ_u - s'_u(μ_u), y - μ_u⟩| ≤ b₁`. Budget `δ/21`. -/
def EvLQ (m : ℕ) : Prop :=
  ∀ t ≤ c.tau π m, ∀ y : Fin d → ℝ, oNorm y ≤ c.p.R → y ∈ c.SS π t →
    |∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu)| ≤ df2B1 c.p d c.n

/-- S-DF (DF Lemma S-DF): for `t ≤ τ` and every `v`, `|vᵀ (P' - P̄) v| ≤ 4 κ η B_n |v|²_{P̄}` with `P'` the update
of round `t`, `P̄ = PBar (t + 1)` on the left and `PBar t` on the right (`N_{t+1}` and `P̄_t` of DF). Budget `δ/7`. -/
def EvSDF (m : ℕ) : Prop :=
  ∀ t ≤ c.tau π m, ∀ v : Fin d → ℝ,
    |df2Sq (c.Pn π t - c.PBar π (t + 1)) v| ≤ 4 * c.p.kap * c.p.eta * df2Bn c.p d c.n * df2Sq (c.PBar π t) v

/-- DQ (DF Lemma DQ, on `B_R`): for `t ≤ τ` and `y` in `B_R` and in `S_t`, `|G_t(y)| ≤ B_n/(L λ²)`. Budget `δ/8`. -/
def EvDQ (m : ℕ) : Prop :=
  ∀ t ≤ c.tau π m, ∀ y : Fin d → ℝ, oNorm y ≤ c.p.R → y ∈ c.SS π t →
    |c.GG π t y| ≤ df2Bn c.p d c.n / (c.p.Le * c.p.lam ^ 2)

/-- (a) and (b5') of Statement E1-loc at the horizon `m`: either (F) the
epoch continues through the rounds `s < r`, the test fires at the end of round `r < m`, and `eReg_r(x) ≤ 0` on
`K_ε`; or (N) it continues through every round `s < m` and `eReg_{m-1}(x) ≤ ρ/η` on `K_ε`. In both cases no mode of
the epoch is `guard` or `off`. -/
def EpochOK (m : ℕ) : Prop :=
  (∃ r < m, (∀ s < r, c.cont π s) ∧ c.fire π r ∧ ∀ x ∈ c.Keps, c.eReg π r x ≤ 0) ∨
    ((∀ s < m, c.cont π s) ∧ ∀ x ∈ c.Keps, c.eReg π (m - 1) x ≤ c.p.rho / c.p.eta)

end Df2Ctx

/-- The bodies of the analysis: closed, convex, `B̄(0, 1) ⊆ K~ ⊆ B̄(0, R)`, and `M(K~) ≤ 1.27 (d + 1)^{1/2}/d`, the
conclusion of `PgGood` on the positioned body (`K' = K~` when `K~ ⊆ B̄(0, R)`). -/
def Df2Body (d : ℕ) (R : ℝ) (Kt : Set (E d)) : Prop :=
  Convex ℝ Kt ∧ IsClosed Kt ∧ Metric.closedBall 0 1 ⊆ Kt ∧ Kt ⊆ Metric.closedBall 0 R ∧ pgMw Kt ≤ df2Mw d

/-! ## The analytic inputs -/

/-- The surrogate of `g` on `Kt` at the law `N(μ, A Aᵀ)`. -/
noncomputable def df2SurrOf (p : Df2OPar) (Kt : Set (E d)) (g : E d → ℝ) (mu : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : E d → ℝ :=
  df2Surr (df2Ext p Kt g) (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A) p.lam

/-- (A5) at a state: `μ ∈ K_ε`, `A` invertible, `‖A Aᵀ‖ ≤ 2 σ²`, `δ I ≤ (A Aᵀ)⁻¹ ≤ I/δ`. -/
def Df2StateOK (p : Df2OPar) (Kt : Set (E d)) (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  mu ∈ df2KepsOf Kt p.eps ∧ A.det ≠ 0 ∧ ((2 * p.sig2) • (1 : Matrix (Fin d) (Fin d) ℝ) - A * Aᵀ).PosSemidef ∧
    ((A * Aᵀ)⁻¹ - p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (A * Aᵀ)⁻¹).PosSemidef

/-- The analytic facts on the extension and the surrogate, at the parameters of the learner in the regime,
on a body of the analysis and an admissible loss; `P = (A Aᵀ)⁻¹`.
* X1: `e` is convex, nonnegative, `(8/ε)`-Lipschitz, and `e = g` on `K_ε`.
* X7 (lem:basic): the surrogate is of class `C²`, convex and below `e`.
* X2 (lem:ons-adv:s-bound): `-10/(λ ε) ≤ s ≤ 1` on `K_ε`.
* X3 (prop:lower): `E_p e - s(μ) ≤ (2/λ) tr(s''(μ) A Aᵀ) + 2 δ d/λ`.
* X6 (prop:opt:H-upper part 2): `|vᵀ s''(z) v| ≤ (λ (8/ε)/(1 - λ)) (2 d σ²)^{1/2} |v|²_P`.
* X8 (prop:opt:H-upper part 1, proved in the source):
  `|vᵀ s''(z) v| ≤ (λ (8/ε)/(1 - λ)) (d/δ)^{1/2} |v|²`, the bound `(λ Lip/(1 - λ)) (d ‖P‖)^{1/2}` with `‖P‖ ≤ 1/δ`;
  condition (d) of the epoch reads it for `2 ‖P̄_{τ+1}‖ ≤ 1/δ`.
* X4 (prop:s-sc): `λ² |x - y|²_P ≤ 1/L` gives `s''(x) ≤ 2 s''(y) + δ P`.
* X5 (prop:ons:q-lower): `λ² |y - μ|²_P ≤ 1/L` gives
  `s(μ) - s(y) ≤ ⟨s'(μ), μ - y⟩ - ¼ |y - μ|²_{s''(μ)} + δ/λ²`. -/
def Df2SIFacts : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (g : E d → ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 →
    (df2oPar d n δ).eps ≤ 1 / 2 → Df2Body d (df2oPar d n δ).R Kt → AdmLoss Kt g →
    (ConvexOn ℝ Set.univ (df2Ext (df2oPar d n δ) Kt g) ∧ (∀ x, 0 ≤ df2Ext (df2oPar d n δ) Kt g x) ∧
      (∀ x y, |df2Ext (df2oPar d n δ) Kt g x - df2Ext (df2oPar d n δ) Kt g y| ≤ 8 / (df2oPar d n δ).eps * ‖x - y‖) ∧
      ∀ y ∈ df2KepsOf Kt (df2oPar d n δ).eps, df2Ext (df2oPar d n δ) Kt g (WithLp.toLp 2 y) = g (WithLp.toLp 2 y)) ∧
    ∀ (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ), Df2StateOK (df2oPar d n δ) Kt mu A →
      (ContDiff ℝ 2 (df2SurrOf (df2oPar d n δ) Kt g mu A) ∧
        ConvexOn ℝ Set.univ (df2SurrOf (df2oPar d n δ) Kt g mu A) ∧
        ∀ z, df2SurrOf (df2oPar d n δ) Kt g mu A z ≤ df2Ext (df2oPar d n δ) Kt g z) ∧
      (∀ z ∈ df2KepsOf Kt (df2oPar d n δ).eps,
        -(10 / ((df2oPar d n δ).lam * (df2oPar d n δ).eps)) ≤ df2SurrOf (df2oPar d n δ) Kt g mu A (WithLp.toLp 2 z) ∧
          df2SurrOf (df2oPar d n δ) Kt g mu A (WithLp.toLp 2 z) ≤ 1) ∧
      ((∫ z, df2Ext (df2oPar d n δ) Kt g (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A z)
            ∂(stdGaussian (E d))) - df2SurrOf (df2oPar d n δ) Kt g mu A (WithLp.toLp 2 mu) ≤
        2 / (df2oPar d n δ).lam * (df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) (WithLp.toLp 2 mu) * (A * Aᵀ)).trace +
          2 * (df2oPar d n δ).δe * d / (df2oPar d n δ).lam) ∧
      (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) z) v| ≤
        (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
          Real.sqrt (2 * d * (df2oPar d n δ).sig2) * df2Sq (A * Aᵀ)⁻¹ v) ∧
      (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) z) v| ≤
        (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
          Real.sqrt (d / (df2oPar d n δ).δe) * (v ⬝ᵥ v)) ∧
      (∀ x y : Fin d → ℝ, (df2oPar d n δ).lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (x - y) ≤ 1 / (df2oPar d n δ).Le →
        ((2 : ℝ) • df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) (WithLp.toLp 2 y) + (df2oPar d n δ).δe • (A * Aᵀ)⁻¹ -
          df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) (WithLp.toLp 2 x)).PosSemidef) ∧
      (∀ y : Fin d → ℝ, (df2oPar d n δ).lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (y - mu) ≤ 1 / (df2oPar d n δ).Le →
        df2SurrOf (df2oPar d n δ) Kt g mu A (WithLp.toLp 2 mu) - df2SurrOf (df2oPar d n δ) Kt g mu A (WithLp.toLp 2 y) ≤
          df2GradM (df2SurrOf (df2oPar d n δ) Kt g mu A) (WithLp.toLp 2 mu) ⬝ᵥ (mu - y) -
            1 / 4 * df2Sq (df2HessM (df2SurrOf (df2oPar d n δ) Kt g mu A) (WithLp.toLp 2 mu)) (y - mu) +
            (df2oPar d n δ).δe / (df2oPar d n δ).lam ^ 2)

/-! ## The pathwise epoch theorem (DET) -/

/-- The layer-1 Props (`Df2.lean`, `Df2R1.lean`), all proved in `Df2DetProof.lean`, `Df2PlayProof.lean` and
`Df2R1Proof.lean`. -/
def Df2LayerOne : Prop :=
  LemmaDFI ∧ LemmaMON ∧ PropINC2 ∧ LemmaD2 ∧ LemmaONS2Core ∧ LemmaZCore ∧ Df2RowZ ∧ PlayShift ∧ LemmaUBPrime ∧
    PlayHess ∧ Df2Trivial ∧ Df2Carriers ∧ LemmaR1i ∧ LemmaR1ii ∧ LemmaR1iii ∧ LemmaR1iv ∧ LemmaR1v

/-- DET, one epoch on every path. The
losses are any admissible functions on the body, the routine is any `ap` with `ApSpec`, the five events are
hypotheses; the conclusion is (a) and (b5'). The proof is the induction on the rounds: the closure,
Lemma D.7, Proposition D.8, Lemma D.13 with the defects, Lemma D.10, Lemma D.14, Lemma D.17, Lemma D.18. -/
def Df2Det : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ApFun d) (π : Df2Path d) (m : ℕ),
    1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → (df2oPar d n δ).eps ≤ 1 / 2 → 1 ≤ m → m ≤ n →
    Df2Body d (df2oPar d n δ).R Kt → ApSpec ap → (∀ s < m, AdmLoss Kt (π.g s)) →
    (df2CtxAt d n δ Kt ap).EvG π m → (df2CtxAt d n δ Kt ap).EvY π m → (df2CtxAt d n δ Kt ap).EvLQ π m →
    (df2CtxAt d n δ Kt ap).EvSDF π m → (df2CtxAt d n δ Kt ap).EvDQ π m →
    (df2CtxAt d n δ Kt ap).EpochOK π m

/-- DET from its inputs. -/
def Df2DetOf : Prop := Df2LayerOne → LemmaW → Df2SIFacts → Df2RowsHold → Df2Det

/-! ## Setting (E) and the event budgets -/

/-- The fields of a state, as a point of a product of Borel spaces. -/
def Df2St.code (st : Df2St d) :
    Bool × (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ ×
      (Fin d → ℝ) × ℝ × (Fin d → ℝ) × ℝ × (Fin d → ℝ) × ℝ :=
  (st.first, st.mu, st.P, st.S, st.A, st.b, st.k, st.G, st.l, st.ctr, st.r)

instance : MeasurableSpace (Df2St d) := MeasurableSpace.comap Df2St.code inferInstance

/-- A state with every field `0`, the second component of the code of `off` and `guard`. -/
def df2StZero : Df2St d := ⟨true, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The code of a mode: its tag and its state. -/
def Df2Mode.code : Df2Mode d → Fin 3 × Df2St d
  | .off => (0, df2StZero)
  | .guard => (1, df2StZero)
  | .run st => (2, st)

instance : MeasurableSpace (Df2Mode d) := MeasurableSpace.comap Df2Mode.code inferInstance

/-- (L1) for a family of contexts indexed by a parameter `q ∈ Θ` (the position): the gauge, the extensions and the
rest of a round after the observation are jointly measurable in the parameter and their arguments; the extensions at
the rounds `s < m` of the horizon only (for `t ≥ n` the adversary class leaves `f_t` unconstrained). -/
def Df2EpochMeas (p : Df2OPar) (n m : ℕ) {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
    (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d) : Prop :=
  (Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) ∧
  (∀ s < m, Measurable fun x : Θ × E d => df2Ext p (Kθ x.1) (gθ s x.1) x.2) ∧
  Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
    df2NextAP ap p n (df2KepsOf (Kθ x.1) p.eps) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2

/-- Setting (E): the draw `ξ s` is measurable in `𝒢 (s + 1)`, standard Gaussian and
independent of `𝒢 s` (E1); the noise `e s` is measurable in `𝒢 (s + 1)`, centred, with `E exp(e²) ≤ 2`, given
`𝒢 s` and `ξ s` (E3). The losses (E2) are fixed functions of the parameter (`Df2OnSetE`). -/
structure Df2SetE (d : ℕ) {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  xi_meas : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)
  xi_law : ∀ s, μ.map (ξ s) = Measure.pi fun _ : Fin d => gaussianReal 0 1
  xi_indep : ∀ s, Indep (MeasurableSpace.comap (ξ s) inferInstance) (𝒢 s) μ
  e_meas : ∀ s, Measurable[𝒢 (s + 1)] (e s)
  e_int : ∀ s, Integrable (fun ω => Real.exp (e s ω ^ 2)) μ
  e_mean : ∀ s, μ[e s | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] =ᵐ[μ] 0
  e_exp : ∀ s, μ[fun ω => Real.exp (e s ω ^ 2) | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] ≤ᵐ[μ] fun _ => 2

/-- `Bad` has probability at most `k δ_e` on every instance of setting (E) at the horizon `m ≤ n`, with a body and
losses that are functions of a parameter `θ` measurable in `𝒢 0` (the position, in the instance of the world), a
routine with (L1) to (L3), at the parameters of the learner in the regime. -/
def Df2OnSetE (k : ℝ) (Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop) : Prop :=
  ∀ (d n m : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 1 ≤ m → m ≤ n → 0 < δ → δ < 1 → (df2oPar d n δ).eps ≤ 1 / 2 →
  ∀ (Θ : Type) [MeasurableSpace Θ] (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d),
    (∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) → (∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) → ApSpec ap →
    Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap →
  ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
  ∀ (𝒢 : Filtration ℕ m0) (θ : Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ),
    Measurable[𝒢 0] θ → Df2SetE d μ 𝒢 ξ e →
    μ {ω | Bad d (df2CtxAt d n δ (Kθ (θ ω)) ap) ⟨fun s => gθ s (θ ω), fun s => e s ω, fun s => ξ s ω⟩ m} ≤
      ENNReal.ofReal (k * (df2oPar d n δ).δe)

/-- Noise and Pi and Gauss fail with probability at most `3 δ_e/7` (the Gaussian tails (T1), (T2), NoiseTail;
lem:ons:mink with R1 to R3). -/
def Df2EvGProp : Prop := Df2OnSetE (3 / 7) fun _ c π m => ¬ c.EvG π m

/-- The event Y fails on G with probability at most `δ_e/7` (as in the source, with `V_τ ≤ 10 n`;
rows R5p and R7). -/
def Df2EvYProp : Prop := Df2OnSetE (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvY π m

/-- The event LQ fails on G with probability at most `δ_e/21` (Lemma LQ). -/
def Df2EvLQProp : Prop := Df2OnSetE (1 / 21) fun _ c π m => c.EvG π m ∧ ¬ c.EvLQ π m

/-- The event S-DF fails on G with probability at most `δ_e/7` (DF Lemma S-DF). -/
def Df2EvSDFProp : Prop := Df2OnSetE (1 / 7) fun _ c π m => c.EvG π m ∧ ¬ c.EvSDF π m

/-- The event DQ fails on G with probability at most `δ_e/8` (DF Lemma DQ on `B_R`). -/
def Df2EvDQProp : Prop := Df2OnSetE (1 / 8) fun _ c π m => c.EvG π m ∧ ¬ c.EvDQ π m

/-- Statement E1-loc: on every instance of setting (E) the epoch fails
(a) or (b5') with probability at most `(3/7 + 1/7 + 1/21 + 1/7 + 1/8) δ_e = (149/168) δ_e`. -/
def Df2E1Loc : Prop := Df2OnSetE (149 / 168) fun _ c π m => ¬ c.EpochOK π m

/-- E1-loc from DET and the five budgets (a union bound). -/
def Df2E1LocOf : Prop :=
  Df2Det → Df2EvGProp → Df2EvYProp → Df2EvLQProp → Df2EvSDFProp → Df2EvDQProp → Df2E1Loc

/-! ## Tools: the freezing lemma and the noise on a product -/

/-- Lemma FR: if `x` is `𝒢`-measurable and `ζ` is independent of `𝒢` with law `γ`, then
`E[F(x, ζ) | 𝒢] = ∫ F(x, z) dγ(z)` almost surely. -/
def LemmaFR : Prop :=
  ∀ (Ω X Z : Type) (𝒢 : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] (μ : Measure[m0] Ω) [IsProbabilityMeasure μ] (x : Ω → X) (ζ : Ω → Z)
    (F : X × Z → ℝ), 𝒢 ≤ m0 → Measurable[𝒢] x → Measurable[m0] ζ →
    @Indep Ω (MeasurableSpace.comap ζ inferInstance) 𝒢 m0 μ → Measurable F →
    Integrable (fun ω => F (x ω, ζ ω)) μ →
    μ[fun ω => F (x ω, ζ ω) | 𝒢] =ᵐ[μ] fun ω => ∫ z, F (x ω, z) ∂(@Measure.map Ω Z m0 _ ζ μ)

/-- Lemma NZ (b) on a product: for probability measures `γ`, `ν`, a sub-sigma-field
`m` of the second factor and `h` integrable for `ν`, the conditional expectation of `h(ω₂)` given the product of
the whole first sigma-field and `m` is `ν[h | m](ω₂)`. -/
def LemmaNZProd : Prop :=
  ∀ (X Y : Type) [mX : MeasurableSpace X] (m : MeasurableSpace Y) [mY : MeasurableSpace Y] (γ : Measure X)
    (ν : Measure[mY] Y) [IsProbabilityMeasure γ] [IsProbabilityMeasure ν] (h : Y → ℝ), m ≤ mY →
    Integrable h ν →
    (γ.prod ν)[fun ω => h ω.2 | MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m] =ᵐ[γ.prod ν]
      fun ω => (ν[h | m]) ω.2

/-! ## The run of D0 on the world -/

/-- The world of the frozen statement at `ω = (gs, noise)`. -/
def df2World (K : Set (E d)) (f : ℕ → E d → ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : World d := ⟨K, f, ω.2, ω.1⟩

/-- The case of the analysis: PG returned a position of `G_pos` (`PgGood` at the radius `R` of the learner) and
`ε ≤ 1/2`. -/
def Df2Case (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Prop :=
  PgGood d w.K (df2oPar d n δ).R (df2oPos d n r0 R0 δ w) ∧ (df2oPar d n δ).eps ≤ 1 / 2

/-- The context of the epochs of D0 on the world. -/
noncomputable def df2zCtx (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Df2Ctx d :=
  df2CtxAt d n δ (df2Kp w.K (df2oPs d n r0 R0 δ w) (df2oPar d n δ).R) apCall

/-- The path of the virtual epoch of D0 started before round `a`: the losses
`g_s(y) = f_{a+s}(S⁻¹ y)/2`, the noise `(ε_{a+s} + ζ_{a+s})/2`, the draws `ξ_{a+s}`. It is read at the rounds
`s < n - a` only. -/
noncomputable def df2zPath (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) : Df2Path d :=
  ⟨fun s y => w.f (a + s) (pgMu (df2oPs d n r0 R0 δ w) + pgOp (df2oPs d n r0 R0 δ w) y) / 2,
    fun s => (w.noise (a + s) + df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs (a + s)) / 2,
    fun s => df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs (a + s)⟩

/-- The mean of the loss of round `t` of D0 given the past: the integral over the draw of round `t` of the loss at
the point played from the mode before round `t` (the point does not read the loss, the noise or the dither). -/
noncomputable def df2zMean (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : ℝ :=
  ∫ z, w.f t (df2RoundGa (df2oPar d n δ) n w.K (df2oPs d n r0 R0 δ w)
      (gauge (df2Kp w.K (df2oPs d n r0 R0 δ w) (df2oPar d n δ).R)) apCall (w.f t) 0 z 0 (df2zMode d n r0 R0 δ w t)).1
    ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)

/-- The Azuma event of the run of D0. -/
def Df2AzPath (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Prop :=
  ∑ t ∈ Finset.range n, w.f t (df2zPlay d n r0 R0 δ w t) ≤
    ∑ t ∈ Finset.range n, df2zMean d n r0 R0 δ w t + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe))

/-- The quantifier block of the world statements: the hypotheses of `Df2ORegretMeas`. -/
def Df2WorldHyp (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ) : Prop :=
  1 ≤ d ∧ 1 ≤ n ∧ 0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
    K ⊆ Metric.closedBall 0 R0 ∧ f ∈ Advs K n

/-- Lemma 8.8 on the world: for each start round `a < n`, the virtual epoch of D0
started before round `a` fails (a) or (b5') at the horizon `n - a`, in the case of the analysis, with probability
at most `(149/168) δ_e`. These are the five event budgets on the world, summed. -/
def Df2VEWorld : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ), Df2WorldHyp d n r0 R0 δ K f →
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν → ∀ a < n,
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
          ¬ (df2zCtx d n r0 R0 δ (df2World K f ω)).EpochOK (df2zPath d n r0 R0 δ (df2World K f ω) a) (n - a)} ≤
        ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe)

/-- The Azuma event of the run of D0 fails, in the case of the analysis, with probability at most `δ_e/7`. -/
def Df2AzWorld : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ), Df2WorldHyp d n r0 R0 δ K f →
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧ ¬ Df2AzPath d n r0 R0 δ (df2World K f ω)} ≤
        ENNReal.ofReal ((df2oPar d n δ).δe / 7)

/-- The measurability (L1) of the round map of DF2-O after the observation, jointly in the position. -/
def Df2ApCallMeas : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (K : Set (E d)), 1 ≤ d → IsClosed K → Convex ℝ K →
    Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP apCall (df2oPar d n δ) n (df2KepsOf (df2Kp K x.1 (df2oPar d n δ).R) (df2oPar d n δ).eps) x.2.1 x.2.2.1
        (x.2.1.A *ᵥ x.2.2.1) x.2.2.2

/-- Lemma 8.8 on the world from E1-loc: the world with the filtration of the run is an instance of setting (E)
for each start round (Lemma NZ), with the position as parameter; `PropAP` gives `ApSpec apCall`, which E1-loc reads. -/
def Df2VEWorldOf : Prop := Df2E1Loc → PropAP → PgMeas → PgGoodMeas → Df2ApCallMeas → Df2VEWorld

/-- The Azuma event on the world from `Df2AzumaEvent` on the filtration of the run (Lemma FR for the means). -/
def Df2AzWorldOf : Prop := Df2AzumaEvent.{0} → PgMeas → PgGoodMeas → Df2ApCallMeas → Df2AzWorld

/-- Lemma 8.10 with the regret, on every world: in the
case of the analysis, if every virtual epoch of D0 meets (a) and (b5') and the Azuma event holds, the regret of D0
is at most `2 ρ/η + n ε + (2 n log(7/δ_e))^{1/2}` (the factor 2 is that of the losses `f/2`). -/
def Df2WorldDet : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ), Df2WorldHyp d n r0 R0 δ K f →
    ∀ w : World d, w.K = K → w.f = f → Df2Case d n r0 R0 δ w →
      (∀ a < n, (df2zCtx d n r0 R0 δ w).EpochOK (df2zPath d n r0 R0 δ w a) (n - a)) → Df2AzPath d n r0 R0 δ w →
      regretPts K f (df2zPlay d n r0 R0 δ w) n ≤
        2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) + n * (df2oPar d n δ).eps +
          Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe))

/-- Lemma TV and Proposition G for DF2-O: the bisection gauge with `j` steps against the exact gauge.
In the case of the analysis, the regret of DJ exceeds `B + 1` with probability at most that of D0 exceeding `B`,
plus `n η_g (R + 7)/ε ≤ δ₁`. -/
def Df2PropG : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ), Df2WorldHyp d n r0 R0 δ K f →
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν → ∀ B : ℝ,
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
          B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n} ≤
        (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
          B < regretPts K f (df2zPlay d n r0 R0 δ (df2World K f ω)) n} + ENNReal.ofReal (df2oPar d n δ).δ1

/-- The last step: the union over the start rounds and the Azuma event, Proposition G, Theorem 8.3 for the
positioning (with the law of the positioning block, `PgMeas` and `PgGoodMeas`), and the trivial bound outside the
regime give the measure clause. -/
def Df2CompOf : Prop :=
  Df2VEWorld → Df2AzWorld → Df2WorldDet → Df2PropG → PgThm → PgMeas → PgGoodMeas → Df2Trivial → Df2ORegretMeas

/-! ## The composition -/

/-- The composition: the layer-1 Props, Lemma D.14, `PropAP`, Theorem 8.3 with the measurability of the positioning,
the SI facts, the five event budgets, the Azuma event, Proposition G and (L1) for `apCall` imply the measure clause
of `Df2ORegret`. Its proof chains `Df2DetOf`, `Df2E1LocOf`, `Df2VEWorldOf`, `Df2AzWorldOf`, `Df2WorldDet` and
`Df2CompOf`, with `Df2RowsHold`, `LemmaFR` and `LemmaNZProd` proved in `Df2Layer2Proof.lean`. -/
def Df2Layer2Comp : Prop :=
  Df2LayerOne → LemmaW → PropAP → PgThm → PgMeas → PgGoodMeas → Df2SIFacts →
    Df2EvGProp → Df2EvYProp → Df2EvLQProp → Df2EvSDFProp → Df2EvDQProp →
    Df2AzumaEvent.{0} → Df2PropG → Df2ApCallMeas → Df2ORegretMeas

end AdversarialBco.Poly
