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

Definitions and interface statements for the analysis of one epoch of the learner DF2-O. No proof here except
definitional checks (`rfl`).

* The levels and the rows: the constants of the epoch (`df2Cg`, `df2Lg`, `df2Bn`, ...) and the rows `Df2Rows`, which
  hold at the parameters of the learner in the regime `ε ≤ 1/2` (`Df2RowsHold`).
* Round maps with a general gauge and a general projection routine: a routine `ap : ApFun d` that meets `ApSpec`
  (the two clauses of `PropAP`, which give `ApSpec apCall`), the line `df2NextAP` and the round map `df2RoundGa` with
  a gauge `ga`. D0 is the learner with the exact gauge of `K'` and `ap = apCall`.
* One epoch on a path (`Df2Ctx`, `Df2Path`): the losses are any admissible functions, the projections any `ap` with
  `ApSpec`; the stopping time `tau`, the five events `EvG`, `EvY`, `EvLQ`, `EvSDF`, `EvDQ` on the path, and (a) and
  (b5') of the one-epoch statement (`EpochOK`).
* The analytic inputs: the bodies of the analysis (`Df2Body`), `Df2SIFacts` (the analytic facts on the extension and
  the surrogate) and the layer-1 statements (`Df2LayerOne`).
* Setting (E) (`Df2SetE`) and (L1), the joint measurability of a round in a parameter (`Df2EpochMeas`).
* Lemma FR (`LemmaFR`) and Lemma NZ on a product (`LemmaNZProd`), standard facts proved in `Df2Layer2Proof.lean`.

Condition 1 of the stopping time is taken in this form: some minimiser of the cumulative surrogate over `K_ε` lies in
the next lower region; the restart-wrapper lemma reads `xs` as any minimiser, so no measurable selection (Lemma MS) is
asked for.

## Indices

Rounds are `0, 1, ...`; round `s` here is round `s + 1` of DF2. In an epoch, `c.mode π s` is the mode before
round `s` (`c.mode π 0` is the fresh state), `c.st π s` its state: `μ_s`, `P_s`, `A_s` here are `μ_{s+1}`,
`P_{s+1}`, `A_{s+1}` of DF2. The quantities computed in round `s` (`Y_s`, `a_s`, `q_s`, `ĝ_s`, `ŝ''_s`, the update
`P'`, `b'`, `k'`) carry the index `s`. `PBar k` is `P̄` after `k` rounds (`P̄_{k+1}` of DF2). `c.Phi π k` is the
quadratic before round `k` (`Φ_k` of DF2), and `c.PhiN π s` the one computed in round `s` (`Φ_{s+1}` of DF2). The
lower region of the test of round `s` is `{y ∈ K_ε : Φ_s(y) ≤ (c₁ - γ) ρ}` (`K_ε` at the first round of the epoch),
the region of line `μ` of round `s` is `{y ∈ K_ε : c.PhiN π s y ≤ c₁ ρ}`, as in `df2NextAP`. The ellipsoid set `S_t`
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
  /-- R24b, the row of the ball (the inner-ball lemma). -/
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
  /-- The row of the lemma of the centre of the test at `x = log (1/δ_e)` (`Df2RowZ`). -/
  cz : 1 / 4 * Real.sqrt p.k0 * df2C0 * Real.sqrt (32 / 9) * p.δe ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
    Real.sqrt d * Real.log (1 / p.δe) ^ ((3 : ℝ) / 2) ≤ 3 / 4

/-- The rows hold at the parameters of the learner in the regime `ε ≤ 1/2` (the rows lemma of the epoch of
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
/-- The line of DF2-O with the routine `ap` in place of `apCall`. -/
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

open Classical in
/-- The round map of DF2-O with the gauge `ga` in place of the bisection gauge of `df2Kp K Ps p.R` and the routine `ap`
in place of `apCall`. -/
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

/-! ## One epoch on a path (setting (E), pathwise) -/

/-- The context of an epoch: the parameters, the horizon `n` of the thresholds, the body `K~` (positioned), the
projection routine of each round (`ap s` in round `s`; (O7)). -/
structure Df2Ctx (d : ℕ) where
  p : Df2OPar
  n : ℕ
  Kt : Set (E d)
  ap : ℕ → ApFun d

/-- The context at the parameters of the learner, with the routine `ap` in every round. -/
noncomputable def df2CtxAt (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ApFun d) : Df2Ctx d :=
  ⟨df2oPar d n δ, n, Kt, fun _ => ap⟩

/-- The context at the parameters of the learner, with the routine `ap s` in round `s`. -/
noncomputable def df2CtxAtF (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ℕ → ApFun d) : Df2Ctx d :=
  ⟨df2oPar d n δ, n, Kt, ap⟩

/-- A path of the data of an epoch: the losses `g s` (on `E d`, positioned), the noise `e s` of the observation, the
draws `ξ s`. -/
structure Df2Path (d : ℕ) where
  g : ℕ → E d → ℝ
  e : ℕ → ℝ
  xi : ℕ → Fin d → ℝ

/-- `K_ε = (1 - ε) K~` in the coordinates `Fin d → ℝ`; `df2Keps K Ps R ε = df2KepsOf (df2Kp K Ps R) ε`. -/
def df2KepsOf (Kt : Set (E d)) (eps : ℝ) : Set (Fin d → ℝ) := {y | WithLp.toLp 2 ((1 - eps)⁻¹ • y) ∈ Kt}

/-- The exact gauge `pip(x) = max (1, π(x)/(1 - ε))`. -/
noncomputable def df2Pip (p : Df2OPar) (Kt : Set (E d)) (x : E d) : ℝ := max 1 (gauge Kt x / (1 - p.eps))

/-- The extension: `e(x) = pip(x) g(x/pip(x)) + 2 (pip(x) - 1)/ε`. -/
noncomputable def df2Ext (p : Df2OPar) (Kt : Set (E d)) (g : E d → ℝ) (x : E d) : ℝ :=
  df2Pip p Kt x * g ((df2Pip p Kt x)⁻¹ • x) + 2 * (df2Pip p Kt x - 1) / p.eps

/-- One round of the epoch learner from a mode: the point played (positioned coordinates) and the next mode. In a
round of DF2: `X = μ + (1 - λ) A ξ`, the play `X/pip(X)`, `Y = pip(X) (g(X/pip(X)) + e) + 2 (pip(X) - 1)/ε`, then
`df2NextAP` with the routine `ap` of the round. D0 on a world with a position of `G_pos` is this map at
`g y = f_t(S⁻¹ y)/2`, `e = (ε_t + ζ_t)/2`. -/
noncomputable def df2RoundE (c : Df2Ctx d) (ap : ApFun d) (g : E d → ℝ) (e : ℝ) (ξ : Fin d → ℝ) :
    Df2Mode d → (Fin d → ℝ) × Df2Mode d
  | .off => (0, .off)
  | .guard => (0, .guard)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - c.p.lam) • w
    let pt := df2Pip c.p c.Kt (WithLp.toLp 2 X)
    (pt⁻¹ • X, df2NextAP ap c.p c.n (df2KepsOf c.Kt c.p.eps) st ξ w
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
  | s + 1 => (df2RoundE c (c.ap s) (π.g s) (π.e s) (π.xi s) (mode s)).2

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

/-! ## The layer-1 statements -/

/-- The layer-1 Props (`Df2.lean`, `Df2R1.lean`), all proved in `Df2DetProof.lean`, `Df2PlayProof.lean` and
`Df2R1Proof.lean`. -/
def Df2LayerOne : Prop :=
  LemmaDFI ∧ LemmaMON ∧ PropINC2 ∧ LemmaD2 ∧ LemmaONS2Core ∧ LemmaZCore ∧ Df2RowZ ∧ PlayShift ∧ LemmaUBPrime ∧
    PlayHess ∧ Df2Trivial ∧ Df2Carriers ∧ LemmaR1i ∧ LemmaR1ii ∧ LemmaR1iii ∧ LemmaR1iv ∧ LemmaR1v

/-! ## Setting (E) and the measurability of a round -/

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
`𝒢 s` and `ξ s` (E3). The losses (E2) are fixed functions of the parameter. -/
structure Df2SetE (d : ℕ) {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  xi_meas : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)
  xi_law : ∀ s, μ.map (ξ s) = Measure.pi fun _ : Fin d => gaussianReal 0 1
  xi_indep : ∀ s, Indep (MeasurableSpace.comap (ξ s) inferInstance) (𝒢 s) μ
  e_meas : ∀ s, Measurable[𝒢 (s + 1)] (e s)
  e_int : ∀ s, Integrable (fun ω => Real.exp (e s ω ^ 2)) μ
  e_mean : ∀ s, μ[e s | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] =ᵐ[μ] 0
  e_exp : ∀ s, μ[fun ω => Real.exp (e s ω ^ 2) | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] ≤ᵐ[μ] fun _ => 2

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

end AdversarialBco.Poly
