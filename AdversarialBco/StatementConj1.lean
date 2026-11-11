/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly

@[expose] public section

/-!
# The frozen statement of Remark 1.2: Conjecture 1 of Bubeck, Eldan and Lee, upper half, against a strategy

The machine, the body, the noise and the regret
are those of `TheoremPoly32O` (StatementPoly.lean), reused unchanged. Two things change: the adversary is a
strategy, and `n` leaves the cost bounds except inside the logarithm.

## The statement (`TheoremConj1Upper`)

There are one program `P` of the machine of StatementPoly.lean, constants `C`, `C'` and an exponent `k` such that for
all `d ≥ 1`, `n ≥ 1`, `0 < r₀ ≤ R₀`, `δ ∈ (0, 1)`, every compact convex `K` with `closedBall 0 r₀ ⊆ K ⊆
closedBall 0 R₀`, every strategy `σ ∈ Strats K n` and every noise law `ν` with `NoiseOK ν`, with `L = log (2 d n / δ)`:

* on every run (every Gaussian stream and every noise sequence) the first play comes within
  `C' (d L (2 + log (R₀/r₀)))^k` steps, every later round within `C' (d L)^k` steps of the round before, and every
  point played is in `K`;
* the outer measure of the runs whose regret exceeds `C d^{3/2} n^{1/2} L^5` is at most `δ`, the regret being taken
  against the losses that the strategy chose on that run.

It implies `TheoremPoly32O` (`theoremPoly32O_of_conj1`, AdversarialBco/Conj1/Poly32O.lean): a fixed sequence is a
constant strategy, whose run is the run of `TheoremPoly32O` step by step, and `(d L)^k ≤ (d n L)^k`.

## The adversary (`Strategy`, `Strats`)

A strategy is a function `σ t x o y`: the loss of round `t` at the point `y`, given the points `x 0, ..., x (t - 1)`
played and the observations `o 0, ..., o (t - 1)` received in the rounds before `t`. The machine is that of
StatementPoly.lean; at each step it runs in the world whose loss of round `t` is `σ t x o`, with `x` the points that
the state records as played (`pts`, each written once, when its round is played) and `o` the observations rebuilt from
them by the recursion `obsAd`, `o u = σ u (x 0, ..., x (u - 1)) (o 0, ..., o (u - 1)) (x u) + ε_u`, which is what
`play` wrote in round `u`. The step `step` reads the loss of the current round only, and that loss reads the points of
the earlier rounds only (`lossAd`), so the strategy is non-anticipating by the semantics, with no side condition.

* What it reads: the transcript of the game before round `t`, plays and observations. A fixed sequence is the strategy
  that reads nothing (`fun t _ _ => f t`). The game of Bubeck, Eldan and Lee (no noise, the loss of round `t`
  chosen with the knowledge of the plays before `t`) is a strategy that reads the plays only. This is the class of
  Proposition 8.5 of the paper, which is proved for the strategies of the plays and the observations and for no wider
  class.
* What it does not read: the Gaussian stream, neither the draws of round `t` nor those of the earlier rounds. An
  adversary that reads the current draw, or the current play, forces an expected regret `n/4` on every learner: here `σ` sees no draw, and the loss of round `t` is fixed by the earlier
  rounds before the point of round `t` exists. The learner's past draws are withheld as well: the machine marks no
  boundary between the draws that serve one round and those that serve the next (a program may draw ahead), and
  Proposition 8.5 is not proved against an adversary that reads them.
* Deterministic: the statement bounds the probability for each strategy. A randomised adversary (a seed drawn
  independently of the game, and a strategy for each value of the seed) is a mixture of these. Its bound would be
  the average over the seed, which needs the event of the regret clause to be measurable jointly in the seed and the
  run; the statement does not carry the seed.
* Measurability: for `t < n` and each point `y ∈ K`, the map `(x, o) ↦ σ t x o y` is measurable for the Borel
  σ-algebras, the hypothesis of Proposition 8.5. A constant strategy
  meets it whatever `f` is, so the fixed sequences need no measurability, as in `TheoremPoly32O`.
* Admissibility: for `t < n` every value `σ t x o` is an `AdmLoss K`, for every history, including the ones no run
  reaches: Proposition 8.5 asks the same. For the histories with a point outside `K` the requirement costs nothing: setting a strategy to `0`
  there changes no run whose points are in `K`, and keeps the measurability since `K` is closed.
* Order of quantifiers: the strategy comes after the program and the instance, so it may depend on `P`, `d`, `n`, `δ`,
  `r₀`, `R₀` and `K`, as the adversary of Bubeck, Eldan and Lee knows the algorithm.

## The noise

`NoiseOK ν` and the law `gaussStream.prod ν`, as in `TheoremPoly32O`: the noise sequence is drawn independently of
the Gaussian stream and, given the past noise, `ε_t` is centred with `E exp(ε_t²) ≤ 2`. The strategy reads the past
observations, hence the past noise, and nothing of `ε_t` before round `t` is played. The noiseless game of Bubeck, Eldan and Lee is
`ν = dirac 0`. Not covered: a noise whose law depends on the plays or on the strategy (a kernel at the history, as
hypothesis (N) allows); its law would have to be built round by round in the
statement, and the game of the conjecture has no noise.

## The cost clause

The machine and its step count are those of `TheoremPoly32O`, and so is the clause (`CostOKAd` is `CostOK` read on the
run against the strategy). The bounds are those of Proposition 8.4: `C' (d L (2 + log (R₀/r₀)))^k`
steps for the first play, which includes the positioning, and `C' (d L)^k` steps for each later round, restarts
included. Since `L = log 2 + log d + log (n/δ)` and `log d ≤ d`, both are polynomial in `d` and `log (n/δ)`, the first
also in `log (R₀/r₀)`: `n` enters only inside the logarithm. `TheoremPoly32O` has the same bounds with `d n L` in place
of `d L`.

## Junk values

Those of `TheoremPoly32O`, and three more. `playedAd` is `0` for a round that never comes, and the cost clause makes
every round `t < n` come on every run. The losses of the regret are `lossAd σ ε (playedAd ...)`: the loss of round `t`
reads the points of the rounds before `t`, which are the points the run had played when it played round `t`, so the
regret is taken against the losses that produced the feedback (the run against a strategy is the run in the world of
its realised losses). The values of the strategy for `t ≥ n`,
and off `K`, are never read by the regret.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace RealRAM

/-- A strategy of the adversary: `σ t x o` is the loss of round `t`, given the points `x` played and the observations
`o` received in the rounds `0, ..., t - 1`. -/
abbrev Strategy (d : ℕ) : Type := (t : ℕ) → (Fin t → E d) → (Fin t → ℝ) → E d → ℝ

/-- The strategies of the class over `n` rounds: for `t < n`, every value is a convex loss `K → [0, 1]`, and at each
point of `K` the loss is a measurable function of the history. -/
def Strats {d : ℕ} (K : Set (E d)) (n : ℕ) : Set (Strategy d) :=
  {σ | ∀ t < n, (∀ x o, AdmLoss K (σ t x o)) ∧
    ∀ y ∈ K, Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => σ t h.1 h.2 y}

/-- The observations of the rounds `0, ..., t - 1` when the points played are `x` and the noise is `ε`:
`o u = σ u (x 0, ..., x (u - 1)) (o 0, ..., o (u - 1)) (x u) + ε u`. -/
def obsAd {d : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (x : ℕ → E d) : (t : ℕ) → Fin t → ℝ
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => ℝ) (obsAd σ ε x t) (σ t (fun i => x i) (obsAd σ ε x t) (x t) + ε t)

/-- The loss of round `t` when the points played are `x`; it reads `x 0, ..., x (t - 1)` only. -/
def lossAd {d : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (x : ℕ → E d) (t : ℕ) : E d → ℝ :=
  σ t (fun i : Fin t => x i) (obsAd σ ε x t)

/-- What the program interacts with against a strategy: the body, the strategy, the noise and the Gaussian stream. -/
structure GameAd (d : ℕ) where
  /-- The body. -/
  K : Set (E d)
  /-- The strategy. -/
  σ : Strategy d
  /-- The noise of the observations. -/
  noise : ℕ → ℝ
  /-- The Gaussian stream. -/
  gs : ℕ → ℝ

/-- The world of the machine when the points played so far are `x`: its losses are those the strategy gives. -/
def GameAd.world {d : ℕ} (g : GameAd d) (x : ℕ → E d) : World d :=
  ⟨g.K, lossAd g.σ g.noise x, g.noise, g.gs⟩

/-- One step against a strategy: the step of the machine in the world of the points the state records as played. -/
noncomputable def stepAd {d : ℕ} (P : List Instr) (g : GameAd d) (s : State d) : State d :=
  step P (g.world s.pts) s

/-- The state after `k` steps against a strategy. -/
noncomputable def runAd {d : ℕ} (P : List Instr) (g : GameAd d) (s0 : State d) (k : ℕ) : State d :=
  (stepAd P g)^[k] s0

open Classical in
/-- The point played in round `t` against a strategy (`0` if that round never comes). -/
noncomputable def playedAd {d : ℕ} (P : List Instr) (g : GameAd d) (s0 : State d) (t : ℕ) : E d :=
  if h : ∃ k, t < (runAd P g s0 k).rounds then (runAd P g s0 (Nat.find h)).pts t else 0

/-- The cost clause against a strategy, as `CostOK`: the first play within `B0` steps, and every later round `t < n`
within `B` steps of the step at which round `t - 1` was played. -/
def CostOKAd {d : ℕ} (P : List Instr) (g : GameAd d) (s0 : State d) (n : ℕ) (B0 B : ℝ) : Prop :=
  1 ≤ (runAd P g s0 ⌈B0⌉₊).rounds ∧
    ∀ k t : ℕ, 1 ≤ t → t < n → (runAd P g s0 k).rounds = t → t + 1 ≤ (runAd P g s0 (k + ⌈B⌉₊)).rounds

end RealRAM

open RealRAM in
/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee against a non-anticipating adversary: a
single real-RAM program with a membership oracle and Gaussian draws, with regret `C d^{3/2} n^{1/2} log^5 (2 d n / δ)`
with probability at least `1 - δ` against every strategy of the class, every point played in `K`, and a number of
steps per round polynomial in `d` and `log (2 d n / δ)`, the first round also in `log (R₀/r₀)`. -/
def TheoremConj1Upper : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ σ ∈ Strats K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ,
        CostOKAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 δ) n
            (C' * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k)
            (C' * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k) ∧
          ∀ t < n, playedAd P ⟨K, σ, noise, gs⟩ (init d n r0 R0 δ) t ∈ K) ∧
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts K (lossAd σ ω.2 (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 δ)))
                (playedAd P ⟨K, σ, ω.2, ω.1⟩ (init d n r0 R0 δ)) n} ≤
        ENNReal.ofReal δ

end AdversarialBco
