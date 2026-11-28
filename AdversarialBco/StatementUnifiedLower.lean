/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnified
public import AdversarialBco.StatementConj1Lower

@[expose] public section

/-!
# Statement: the lower bound in the generality of Theorem U (release v2.3)

`TheoremLowerU` and `TheoremLowerUProg` are the lower half of release v2.3, Theorem LU of the paper with Lemmas
SMALL, BRIDGE and REAL. They follow the upper
theorem `TheoremUnified` (StatementUnified.lean, frozen and imported unchanged) in the same generality: the same class
of bodies, the same game of adversary, noise and observation, a form in expectation and a form with probability.
Every object they share with `TheoremUnified` is its own: the body class, the weak membership oracle `WeakMemOracle`,
the oracle machine (`InstrO`, `playedO`, `CostOKO`, `CoinWindowsOK`, `initU`), the environments `NoisyAdv`, the
world `envWorld`, the regret `regretU` and the coins `coinStream`. The learners, the strategies and the regret of the
noiseless game are those of the frozen lower statement of v2.1 (StatementConj1Lower.lean: `Learner`, `IsLearnerAd`,
`regretAd`; StatementConj1.lean: `Strategy`, `Strats`).

## The claims

`TheoremLowerU` (every learner). For every `d ≥ 1`, `n ≥ 1`, every centre `a ∈ ℝ^d`, radii `0 < r0 ≤ R0`, every
compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` (`BodyU`) and every measurable randomised learner on `K`
(`IsLearnerAd`, on any probability space):

* (a) if `d ≥ 4·10^6` and `n ≥ d^10`, there is a strategy of `StratsLowU K n r0` against which the regret is
  integrable with mean at least `7·10^-9 d^{3/2} n^{1/2} / log d` (`LowerMean`);
* (b) if `d ≥ 4·10^6` and `n ≥ d^10`, there is a strategy of `StratsLowU K n r0` against which the regret is
  measurable and at least `2.8·10^-9 d^{3/2} n^{1/2} / log d` with probability at least `1/2` (`LowerProb`);
* (c) for every `d ≥ 1` and `n ≥ 1`, there is a strategy of `StratsLowU K n r0` with mean regret at least
  `n^{1/2} / (4 √3)`, and one with regret at least `n^{1/2} / (8 √3)` with probability at least `1/48`.

(a) is Theorem LU (a) (the lower bound on the unit ball, carried to every body of the class by an affine map, Lemmas
AFF, POS and R0-EXT), (b) is Theorem LU (b) (Proposition STOP and Corollary LU-P), (c) is Lemma SMALL (random-sign
linear losses along one direction, oblivious, made deterministic). No constant depends on `a`, `r0`,
`R0` or `K`. Each clause has its own strategy: the strategy of (b) need not be that of (a).

`TheoremLowerUProg` (every program, in Theorem U's own objects). For every program `P` of the oracle machine and every
input of `TheoremUnified`'s class (`d, n ≥ 1`, rationals `0 < δ < 1`, `0 < r0 ≤ R0`, a rational centre `a`, a compact
convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, a weak membership oracle `orc` of `K`), if `P` meets on that input, on
every world, three of the four machine clauses of `TheoremUnified` (`MachineOK`: every round within cost `B`, plays
in `K`, the coin windows `D`, `D'`), then the clauses (a), (b), (c) hold for `P` in the objects of
`TheoremUnified`: there is an environment of `TheoremUnified` with the windows `D`, `D'` of the program, namely
a strategy of `StratsLowU K n r0` played in closed loop with `P` (`ClosedLoop`) with zero noise, on the program's own
coin space `(ℕ → Bool, coinStream)`, against which `regretU`, the regret of `TheoremUnified`, is integrable with the
mean of (a) (`ProgMean`), or measurable and at least the threshold of (b) with probability `1/2` (`ProgProb`), and
likewise for (c).

So the lower bound is stated twice: once for every measurable learner, which contains every program and every
algorithm, whatever its computational model, whose plays exist, lie in `K` and are jointly measurable on every history
(for a program of the oracle machine, one that meets the machine clauses, by Lemma BRIDGE), and once for
the programs of the bit RAM in exactly the environments, the regret and the probability space of `TheoremUnified`, so
that the two theorems combine with no translation (`CorollaryMatch`).

## The bodies (`BodyU`)

`BodyU K a r0 R0`: `0 < r0 ≤ R0`, `K` compact and convex, `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, with a real centre and real
radii. Every body of `TheoremUnified` (rational `a`, `r0`, `R0`, through `toE` and the casts) is one
(`bodyU_of_unified` in the sanity module). `TheoremLowerUProg` takes the rational data of `TheoremUnified`, which the
program reads (`initU`).

## The adversary (`StratsLowU`)

`StratsLowU K n r0` is the part of `Strats K n` (the strategies of StatementConj1.lean: for `t < n` and every history,
a loss convex with values in `[0, 1]` on `K`, measurable in the history at each point of `K`; so an admissible loss of
`TheoremUnified` on every history, `AdmLoss`) whose losses, for `t < n` and every history,

* read the past points and ignore the past observations;
* take values in `[1/8, 7/8]` on `K`;
* are `1/(4 r0)`-Lipschitz on all of `ℝ^d`.

The strategy is existential, so each restriction strengthens the claim. The Lipschitz constant scales with the inner
radius as a loss pulled back by an affine map does: in the normalisation of Bubeck, Eldan and Lee (a unit ball inside
`K`) it is `1/4`, the constant of `StratsLip` (StatementConj1Lower.lean). The strategy is deterministic: it reads no
seed, no coin of the program and no noise. Its loss of round `t` is one that the environments of `TheoremUnified`
allow: the earlier points are functions of the observations of the earlier rounds and of the coins read before the
play of round `t - 1`, at most `D t` of them by the coin clause, so the loss is independent of the later coins.

## The learner, the game and the regret (`Learner`, `IsLearnerAd`, `regretAd`)

As in StatementConj1Lower.lean: a seed `ω` drawn from a probability measure `μ` on any measurable space `Ω`, and a play
rule `pol t ω x o` (the point of round `t` from the seed, the earlier points `x` and the earlier observations `o`),
jointly measurable, with values in `K`, for the rounds `t < n`. The game is noiseless: the learner observes the loss of
its point exactly. `regretAd K σ p n` is the realised regret `Σ_{t < n} f_t(x_t) - inf_{y ∈ K} Σ_{t < n} f_t(y)`
against the losses `f_t` that `σ` chose on that run.

This learner class contains the programs of `TheoremUnified`. A program reads the feedback `f_t(x_t) + ε_t` through
`obsR` (or `obs`) to a precision it chooses, a function of the exact observation; with the noise `0` its play of round
`t` is a function of its coins and of the exact observations of the earlier rounds (Lemma BRIDGE). That
inclusion is what `TheoremLowerUProg` asks the proof to carry into the objects of `TheoremUnified`; it is not a separate
statement here.

## The program form (`MachineOK`, `ClosedLoop`, `ProgMean`, `ProgProb`)

`MachineOK P K orc s0 n B D D'` asks, for every world (losses admissible on `K` in the rounds `t < n`, any real noise,
any coins, the oracle `orc`), the cost clause `CostOKO` with the bound `B`, the plays of the rounds `t < n` in `K`, and
the coin clause `CoinWindowsOK` with the windows `D`, `D'`: three of the four machine clauses of `TheoremUnified`,
word for word. The space clause `SpaceOKO` is not asked, and `B` is any real: the hypothesis is weaker than the machine
clauses of `TheoremUnified` (with its `B = C' (d log(2dn/δ) S)^k`), so the claim is stronger, and the program of
`TheoremUnified` meets it with its own `B`, `D`, `D'` (a corollary in the sanity module of
release v2.3).

`ClosedLoop P s0 orc n σ loss`: on every coin sequence `cs` and in every round `t < n`, the loss `loss t cs` is the
loss that `σ` chooses from the points that `P` played in the rounds before `t` in the world of these losses, the noise
`0`, the coins `cs` and the oracle `orc`. The condition refers to the run it defines; the run reads the loss of round
`s` only after the play of round `s`, so on the rounds `t < n` it has exactly one solution, built round by round
(Lemma REAL). The losses of the rounds `t ≥ n` are free and never read.

`ProgMean P K orc s0 n r0 D D' c`: there are a strategy `σ` of `StratsLowU K n r0` and losses `loss` on the coin space
in closed loop with `P`, such that `(coinStream, id, loss, 0)` is a `NoisyAdv` with the windows `D`, `D'` (an
environment of `TheoremUnified`: the coins are the program's own fair coins, the losses are admissible and measurable,
the coins after each window are independent of the past, the noise is `0`), the regret `regretU` of the run is
integrable on the coin space, and its mean is at least `c`. `ProgProb` is the same with the regret measurable and at
least `c` with probability at least `p`. The noise `0` is a member of the class (BJLR26 l.181: "This includes noiseless
feedback").

## Corollary MATCH (`CorollaryMatch`)

`CorollaryMatch` is the two-sided statement for one program: there are a program `P`, constants `C`, `C'`, `k` and
windows `D`, `D'` such that, on every input of `TheoremUnified`'s class with every weak membership oracle, `P` meets the
machine clauses of `TheoremUnified` and its two regret clauses against every environment of the class, and, in the same
environments (a `NoisyAdv` with the same windows), (a) and (b) when `d ≥ 4·10^6` and `n ≥ d^10`, and (c). With
`U = C d^{3/2} n^{1/2} log^5 (2 d n / δ)`, `d ≥ 4·10^6`, `n ≥ d^10` and the program run at `δ ∈ (0, 1/2)`: the worst
case over the environments of the class of the `(1 - δ)`-quantile of the regret lies between
`2.8·10^-9 d^{3/2} n^{1/2} / log d` and `U`, and the worst case of its mean lies between
`7·10^-9 d^{3/2} n^{1/2} / log d` and `U + n δ`; at `δ = 1/n` the two means are within a factor of order
`log d log^5 (2 d n^2)`. It is the conjunction of the two theorems for the program of `TheoremUnified`:
`TheoremUnified → TheoremLowerUProg → CorollaryMatch` and `CorollaryMatch → TheoremUnified` are proved in the sanity
module. The two sides are separate theorems on the same game; no minimax identity is claimed.

## What is not claimed

* The rate `d^{3/2} n^{1/2} / log d` for `d < 4·10^6` or `n < d^10`. For `n < c^2 d^3 / log^2 d` a lower bound
  `c d^{3/2} n^{1/2} / log d` is false, since the regret is at most `n`. Between about `d^3 / log^2 d` and about
  `d^5 R0'^2`, with `R0' = 67 d (log (2 d + 2))^{1/2}` the outer radius of the position with inner radius `1/2` that
  the proof uses (Lemma POS), it is open for the class: the construction of (a) needs `n` of
  order `d^5 R0'^2` up to logarithms. From `e^4 d^5 R0'^2` to `d^10` the same construction reaches it by a derivation
  that is not part of this release (LOW-MID); that range is left out of the claim. For every `d` and `n`, clause
  (c) gives the rate `n^{1/2}` only; the form `c d^{3/2} n^{1/2} / log (d + 2)`, for every `n` when `d < 4·10^6` and
  for `n ≥ d^10` when `d ≥ 4·10^6`, which follows from (a), (b) and (c) by arithmetic (Corollary ALL-D), is
  not stated.
* A lower bound that depends on `δ`: the program reads `δ`, and the lower bound is the same for every `δ`; whether some
  dependence of the upper bound on `δ` is necessary is not settled.
* The noisy game: the lower bound uses the noise `0`, which `TheoremUnified`'s class contains; a lower bound larger by
  `(log n)^{1/2}` with a Gaussian noise (LOW-NOISY) is not stated.
* The oblivious and the stochastic settings at the rate `d^{3/2}`: the strategies of (a) and (b) read the earlier
  points. The strategies that the proof gives for (c) are oblivious; the statement does not assert it.
* One strategy for (a) and (b) together.

## Junk values

`Real.log d > 0` since `d ≥ 4·10^6` where it is used, and `(d : ℝ) ^ (3/2 : ℝ)` is the ordinary power since `d > 0`.
`dist y z / (4 * r0)` has `r0 > 0` in both theorems (`BodyU`; the rational `r0 > 0`). The integrals are compared only
where integrability is asserted, and the measures of `{c ≤ Reg}` only where measurability is asserted, so neither is
Mathlib's junk value. `regretAd` and `regretU` take the infimum of `Σ_{t < n} f_t` over `K`, nonempty (it contains
`B̄(a, r0)`) and bounded below by `n / 8` for the losses of a strategy of `StratsLowU`. `playedO` is `0` for a round
that never comes; the cost clause of `MachineOK` makes every round `t < n` come on every world whose losses are
admissible in the rounds `t < n`, and the closed-loop losses of these rounds are those of a strategy of `Strats K n`,
admissible, so every round comes. A negative `B` makes `MachineOK` false (the cost never decreases), so the claim asks
nothing for it; the program of `TheoremUnified` meets `MachineOK` with its own `B`. `Strats K n`, `StratsLowU K n r0`,
`IsLearnerAd K n`, `ClosedLoop` and `NoisyAdv` bind the rounds `t < n` only, and nothing reads a later round. The coin
space is `ℕ → Bool` with the product σ-algebra; `id` is measurable with law `coinStream`.

## Non-vacuity (AdversarialBco/UnifiedLower/Sanity.lean)

The hypotheses of `TheoremLowerU` hold for every `d`, `n` at the closed unit ball about `0` (`r0 = R0 = 1`) with the
constant learner on `Unit` (`lowerU_hyps_satisfiable`); those of `TheoremLowerUProg` hold at the closed unit ball about
the rational centre `0` with its exact membership oracle and the program of three instructions that plays the point
`0`, the centre, in every round and reads no coin, with the windows `D = D' = 0`, for every `d`, `n`, `δ` and oracle
(`progU_hyps_satisfiable`). The Comparator configurations config-minimax-q.json and config-matched.json certify these
two witnesses.
-/

open MeasureTheory

namespace AdversarialBco

namespace UnifiedLower

open BitRAM BitRAMO Unified
open RealRAM (Strategy Strats)
open Lower (Learner IsLearnerAd regretAd)

/-- The body class: `0 < r0 ≤ R0`, a compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`. -/
def BodyU {d : ℕ} (K : Set (E d)) (a : E d) (r0 R0 : ℝ) : Prop :=
  0 < r0 ∧ r0 ≤ R0 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall a r0 ⊆ K ∧ K ⊆ Metric.closedBall a R0

/-- The strategies of the lower bound on `K` for `n` rounds at the inner radius `r0`: those of `Strats K n` whose loss,
for `t < n` and every history, reads the past points only, takes values in `[1/8, 7/8]` on `K` and is
`1/(4 r0)`-Lipschitz on `E d`. -/
def StratsLowU {d : ℕ} (K : Set (E d)) (n : ℕ) (r0 : ℝ) : Set (Strategy d) :=
  {σ | σ ∈ Strats K n ∧ ∀ t < n, ∀ (x : Fin t → E d) (o o' : Fin t → ℝ),
    σ t x o = σ t x o' ∧ (∀ y ∈ K, 1 / 8 ≤ σ t x o y ∧ σ t x o y ≤ 7 / 8) ∧
      ∀ y z : E d, |σ t x o y - σ t x o z| ≤ dist y z / (4 * r0)}

/-- A strategy of `StratsLowU K n r0` against which the regret of the learner `(μ, pol)` in the noiseless game is
integrable with mean at least `c`. -/
def LowerMean {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (K : Set (E d)) (n : ℕ) (r0 : ℝ) (μ : Measure Ω)
    (pol : Learner Ω d) (c : ℝ) : Prop :=
  ∃ σ ∈ StratsLowU K n r0, Integrable (fun ω => regretAd K σ (fun t => pol t ω) n) μ ∧
    c ≤ ∫ ω, regretAd K σ (fun t => pol t ω) n ∂μ

/-- A strategy of `StratsLowU K n r0` against which the regret of the learner `(μ, pol)` in the noiseless game is
measurable and at least `c` with probability at least `p`. -/
def LowerProb {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (K : Set (E d)) (n : ℕ) (r0 : ℝ) (μ : Measure Ω)
    (pol : Learner Ω d) (c : ℝ) (p : ENNReal) : Prop :=
  ∃ σ ∈ StratsLowU K n r0, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
    p ≤ μ {ω | c ≤ regretAd K σ (fun t => pol t ω) n}

/-- The losses `loss` on the coin space are the closed loop of the strategy `σ` with the program `P` from `s0` with the
oracle `orc` and the noise `0`: in every round `t < n` and on every coin sequence `cs`, the loss of round `t` is the
loss that `σ` chooses from the points that `P` played in the rounds before `t` in the world of these losses. -/
def ClosedLoop {d : ℕ} (P : List InstrO) (s0 : State d) (orc : (Fin d → ℚ) → ℕ → Bool) (n : ℕ) (σ : Strategy d)
    (loss : ℕ → (ℕ → Bool) → E d → ℝ) : Prop :=
  ∀ t < n, ∀ cs : ℕ → Bool, loss t cs =
    σ t (fun s : Fin t => playedO P (envWorld orc id loss (fun _ _ => 0) cs) s0 s) (fun _ => 0)

/-- The machine clauses of `TheoremUnified` that the lower bound reads, for `P` from `s0` with the oracle `orc`, on
every world whose losses are admissible on `K` in the rounds `t < n`: every round within cost `B` (`CostOKO`), the
plays of the rounds `t < n` in `K`, and the coin windows `D`, `D'` (`CoinWindowsOK`). -/
def MachineOK {d : ℕ} (P : List InstrO) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (B : ℝ) (D D' : ℕ → ℕ) : Prop :=
  ∀ (f : ℕ → E d → ℝ) (noise : ℕ → ℝ) (cs : ℕ → Bool), (∀ t < n, AdmLoss K (f t)) →
    CostOKO P ⟨f, noise, cs, orc⟩ s0 n B ∧ (∀ t < n, playedO P ⟨f, noise, cs, orc⟩ s0 t ∈ K) ∧
      CoinWindowsOK P ⟨f, noise, cs, orc⟩ s0 n D D'

/-- A strategy of `StratsLowU K n r0` in closed loop with `P`, with the noise `0`, on the program's coin space, which is
an environment of `TheoremUnified` with the windows `D`, `D'` and against which the regret `regretU` of `P` is
integrable with mean at least `c`. -/
def ProgMean {d : ℕ} (P : List InstrO) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (r0 : ℝ) (D D' : ℕ → ℕ) (c : ℝ) : Prop :=
  ∃ (σ : Strategy d) (loss : ℕ → (ℕ → Bool) → E d → ℝ), σ ∈ StratsLowU K n r0 ∧ ClosedLoop P s0 orc n σ loss ∧
    NoisyAdv K n D D' coinStream id loss (fun _ _ => 0) ∧
    Integrable (fun cs => regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)) coinStream ∧
    c ≤ ∫ cs, regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs) ∂coinStream

/-- A strategy of `StratsLowU K n r0` in closed loop with `P`, with the noise `0`, on the program's coin space, which is
an environment of `TheoremUnified` with the windows `D`, `D'` and against which the regret `regretU` of `P` is
measurable and at least `c` with probability at least `p`. -/
def ProgProb {d : ℕ} (P : List InstrO) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (r0 : ℝ) (D D' : ℕ → ℕ) (c : ℝ) (p : ENNReal) : Prop :=
  ∃ (σ : Strategy d) (loss : ℕ → (ℕ → Bool) → E d → ℝ), σ ∈ StratsLowU K n r0 ∧ ClosedLoop P s0 orc n σ loss ∧
    NoisyAdv K n D D' coinStream id loss (fun _ _ => 0) ∧
    Measurable (fun cs => regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)) ∧
    p ≤ coinStream {cs | c ≤ regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)}

end UnifiedLower

open Lower UnifiedLower in
/-- **Theorem LU, with Lemma SMALL.** For every `d, n ≥ 1`, every compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`,
`0 < r0 ≤ R0`, and every measurable randomised learner on `K`: (a) if `d ≥ 4·10^6` and `n ≥ d^10`, a strategy of
`StratsLowU K n r0` (convex, values in `[1/8, 7/8]` on `K`, `1/(4 r0)`-Lipschitz, reading the earlier points) against
which the regret is integrable with mean at least `7·10^-9 d^{3/2} n^{1/2} / log d`; (b) if `d ≥ 4·10^6` and
`n ≥ d^10`, a strategy of the class against which the regret is at least `2.8·10^-9 d^{3/2} n^{1/2} / log d` with
probability at least `1/2`; (c) a strategy of the class with mean regret at least `n^{1/2} / (4 √3)`, and one with
regret at least `n^{1/2} / (8 √3)` with probability at least `1/48`. -/
def TheoremLowerU : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol →
      (4000000 ≤ d → d ^ 10 ≤ n →
        LowerMean K n r0 μ pol (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ∧
          LowerProb K n r0 μ pol (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2)) ∧
      LowerMean K n r0 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      LowerProb K n r0 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified UnifiedLower in
/-- **Theorem LU for the programs of the oracle machine, in the objects of `TheoremUnified`.** For every program `P`,
every input of `TheoremUnified`'s class and every weak membership oracle of `K`, if `P` meets on every world the cost
clause with some bound `B`, plays in `K` and has the coin windows `D`, `D'` (`MachineOK`), then there is, for each of
the clauses (a), (b), (c) of `TheoremLowerU`, a strategy of `StratsLowU K n r0` in closed loop with `P` with the noise
`0`, an environment of `TheoremUnified` with the windows `D`, `D'` on the program's coin space, against which the regret
`regretU` of `P` satisfies that clause. -/
def TheoremLowerUProg : Prop :=
  ∀ (P : List InstrO) (d : ℕ), 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
  ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
  ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
  ∀ (B : ℝ) (D D' : ℕ → ℕ), MachineOK P K orc (initU d n δ r0 R0 a) n B D D' →
    (4000000 ≤ d → d ^ 10 ≤ n →
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D'
          (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ∧
        ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D'
          (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2)) ∧
    ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (4 * Real.sqrt 3)) ∧
    ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified UnifiedLower in
/-- **Corollary MATCH.** One program `P` with constants `C, C', k` and windows `D, D'` such that, on every input of
`TheoremUnified`'s class with every weak membership oracle, `P` meets the machine clauses and the two regret clauses of
`TheoremUnified` (word for word), and, in environments of the same class (`NoisyAdv` with the same windows), the lower
clauses (a) and (b) of `TheoremLowerUProg` when `d ≥ 4·10^6` and `n ≥ d^10`, and (c). Not a theorem to prove on its own:
it follows from `TheoremUnified` and `TheoremLowerUProg` (sanity module). -/
def CorollaryMatch : Prop :=
  ∃ (P : List InstrO) (C C' : ℝ) (k : ℕ) (D D' : (d n : ℕ) → ℚ → ℚ → ℚ → (Fin d → ℚ) → ℕ → ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∀ (f : ℕ → E d → ℝ) (noise : ℕ → ℝ) (cs : ℕ → Bool), (∀ t < n, AdmLoss K (f t)) →
        CostOKO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n
            (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
          SpaceOKO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n
            (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
          (∀ t < n, playedO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) t ∈ K) ∧
          CoinWindowsOK P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n (D d n δ r0 R0 a) (D' d n δ r0 R0 a)) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
        (noise : ℕ → Ω → ℝ), NoisyAdv K n (D d n δ r0 R0 a) (D' d n δ r0 R0 a) μ coin loss noise →
        Measurable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) ∧
        Integrable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) μ ∧
        μ {ω | C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 <
            regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤ ENNReal.ofReal (δ : ℝ) ∧
        ∫ ω, max (regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) 0 ∂μ ≤
          C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ)) ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        ProgMean P K orc (initU d n δ r0 R0 a) n r0 (D d n δ r0 R0 a) (D' d n δ r0 R0 a)
            (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ∧
          ProgProb P K orc (initU d n δ r0 R0 a) n r0 (D d n δ r0 R0 a) (D' d n δ r0 R0 a)
            (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2)) ∧
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 (D d n δ r0 R0 a) (D' d n δ r0 R0 a)
          (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      ProgProb P K orc (initU d n δ r0 R0 a) n r0 (D d n δ r0 R0 a) (D' d n δ r0 R0 a)
          (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

end AdversarialBco
