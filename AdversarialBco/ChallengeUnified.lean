/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-unified.json: AdversarialBco/StatementUnified.lean verbatim over the first and seventh
-- modules, its theorem and five non-vacuity witnesses, each proved by `sorry` (code/formal-proof/challenges.sh).
-- Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementPoly
public import AdversarialBco.ChallengeBase.StatementBitRAMO
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Statement: Theorem U, one program for every body given by an oracle, every δ, BJLR26's adversary and noise (release v2.3)

`TheoremUnified` is Theorem U, the upper bound of the paper: one program of the bit RAM with a weak membership
oracle (StatementBitRAMO.lean), and one theorem covering at once every convex body given by a weak membership oracle
with a known centre and radii, every confidence `δ` read by the program, and every environment of Bakhtiari, Jamieson,
Lattimore and Ratliff (BJLR26, arXiv 2611.33531v1, Section 3, advcvx.tex l.158 to 186): losses chosen adaptively from
the whole past, the program's past coins included, and a noise conditionally centred and subgaussian given the past and
the program's current draw. The regret is bounded by `C d^{3/2} n^{1/2} log^5 (2 d n / δ)` with probability at least
`1 - δ`, and in expectation up to `n δ`; every round costs a number of bit operations polynomial in `d`, `log n` and
the bit length of `δ`, the centre and the radii.

## The claim (`TheoremUnified`)

There are one program `P` of the oracle machine, constants `C`, `C'`, an exponent `k` and two coin schedules `D`, `D'`
(functions of the input) such that for all `d ≥ 1`, `n ≥ 1`, rationals `δ`, `r0`, `R0` with `0 < δ < 1` and
`0 < r0 ≤ R0`, every rational centre `a ∈ ℚ^d`, every compact convex `K ⊆ ℝ^d` with
`B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` and every weak membership oracle `orc` for `K` (`WeakMemOracle`), the run of `P` on the
input `d, n, δ, r0, R0, a` (`initU`) with the oracle `orc` satisfies, with `L = log (2 d n / δ)`,
`S = sizeU δ r0 R0 a` the total bit length of the numerators and denominators of `δ`, `r0`, `R0` and the coordinates
of `a`, and `B = C' (d L S)^k`:

* (machine, on every world) against every sequence of losses that are convex with values in `[0, 1]` on `K` in the
  rounds `t < n`, every real noise sequence and every coin sequence:
  (i) each round `t < n`, the first included, is played within cost `B` of the state from which it is awaited
  (`CostOKO`); (ii) at every step before the play of round `n - 1` the cells in use have total bit length at most `B`
  (`SpaceOKO`); (iii) every point played in a round `t < n` lies in `K`; (iv) the program has read exactly `D' t` coins
  when it plays round `t`, and at most `D t` coins when it plays round `t - 1` (`CoinWindowsOK`);
* (regret, for every environment) for every noisy adversary (`NoisyAdv`) with the windows `D`, `D'` on a probability
  space `(Ω, μ)`, the regret `Reg` of the run (on `K`, against the losses chosen on that run) is a measurable and
  integrable function on `Ω`, `μ (Reg > C d^{3/2} n^{1/2} L^5) ≤ δ`, and
  `∫ max (Reg, 0) dμ ≤ C d^{3/2} n^{1/2} L^5 + n δ`.

The schedules `D`, `D'` are part of the claim, chosen with the program and depending on the input only; clause (iv)
ties them to the run: the noise of round `t` may read every coin read up to the play of round `t`, and the loss of
round `t` every coin read up to the play of round `t - 1` and possibly more (the program of the route lets it read the
coins drawn after the observation of round `t - 1` too).

## The input (`inputU`, `initU`, `sizeU`)

The program reads integers: the cells `0`, `1` hold `d`, `n`; the cells `2`, `3` the numerator and the denominator in
lowest terms of `δ`, `4`, `5` those of `r0`, `6`, `7` those of `R0`; the cells `8 + 2 i`, `9 + 2 i` those of the
coordinate `a i`, `i < d`; every other cell is `0`. The body `K` itself is not in the memory: the program learns it
through the oracle only. `S` is the bit length of the data `δ, r0, R0, a`, which a program must read; together with
`d` and `log (2 d n / δ)` it makes the cost bound polynomial in `d`, `log n` and the bit length of `δ`, `a`, `r0` and
`R0` (`log (1/δ)` is at most the bit length of `δ` and can be much smaller), the centre and the radii being the
parameters of a well-bounded centred convex body of Grötschel, Lovász and Schrijver (Geometric Algorithms and
Combinatorial Optimization, 2nd ed. 1993, (2.1.16) and (2.1.17)). `log (R0 / r0)` is at most `S`.

## The machine clauses (`CostOKO`, `SpaceOKO`, `CoinWindowsOK`)

They are asserted for every world: every sequence of losses admissible on `K` in the rounds `t < n` (`AdmLoss`), every
real noise sequence, every coin sequence, and the oracle `orc`; so they hold on every run against every environment,
whatever its probability space. The cost clause: for every step `k` at which fewer than `n` rounds have been played,
some later step plays one more round, and the cost spent between the two is at most `B`; so every round, the first
included, costs at most `B`, nothing is amortised, and all `n` rounds are played on every run. The space clause bounds
the cells in use at every step of every round up to the play of round `n - 1`; with the cost clause it bounds the time
of a Turing machine that simulates a round (StatementBitRAM.lean, "Why this is a bit-cost model"). The noise can be
any real number, so the cost clause asks the program to read the feedback within a bounded number of digits; `obsR`
reads it clipped (StatementBitRAMO.lean). The coin clause: for every round `t < n` and every step, a state with at most
`t` rounds played has read at most `D' t` coins, a state with more than `t` rounds played at least `D' t` coins (so the
program has read exactly `D' t` coins when it plays round `t`, on every run), and a state with fewer than `t` rounds
played at most `D t` coins (so `D t` is at least the number of coins read when round `t - 1` is played).

## The environment (`NoisyAdv`)

A noisy adversary on `K` for `n` rounds with the windows `D`, `D'` is a probability space `(Ω, μ)`, any type with any
σ-algebra, carrying the program's coins `coin : Ω → (ℕ → Bool)`, the losses `loss t : Ω → (ℝ^d → ℝ)` and the noises
`noise t : Ω → ℝ`; on `ω` the program runs in the world of the losses `loss t ω`, the noises `noise t ω`, the coins
`coin ω` and the oracle (`envWorld`). The same `ω` drives the losses, the noise and the coins, so they may be
correlated in every way that the following conditions allow, for every round `t < n`:

* the coins are fair and independent: `coin` is measurable and its law is `coinStream` (StatementBitRAM.lean);
* `loss t ω` is convex with values in `[0, 1]` on `K` for every `ω`, its value at each point of `K` is a measurable
  function of `ω`, and `noise t` is measurable;
* (the loss of round `t` does not read the coins after its window) the coins of index at least `D t` are independent of
  the σ-algebra generated by the losses of the rounds `0, ..., t`, the noises of the rounds `0, ..., t - 1` and the coins
  of index below `D t` (`fresh_loss`);
* (the noise of round `t` does not read the coins after the play of round `t`) the coins of index at least `D' t` are
  independent of the σ-algebra generated by the losses and the noises of the rounds `0, ..., t` and the coins of index
  below `D' t` (`fresh_noise`);
* (the noise is centred and subgaussian given everything before it) `exp (noise t ^ 2)` is integrable, and, given the
  σ-algebra `G_t` generated by the losses of the rounds `0, ..., t`, the noises of the rounds `0, ..., t - 1` and the
  coins of index below `D' t`, the conditional expectation of `noise t` is `0` and that of `exp (noise t ^ 2)` is at
  most `2`, almost everywhere (`noise_mean`, `noise_exp`).

The σ-algebra of a loss is generated by its values at the points of `K` (`lossσ`), that of a set of coins by those
coins (`coinsBelow`, `coinsFrom`), and `histσ L M N` is generated by the losses of the rounds below `L`, the noises of
the rounds below `M` and the coins of index below `N`.

**Conditional expectations.** The noise clauses are written with Mathlib's conditional expectation
`μ[f | G_t]` (`MeasureTheory.condExp`), which is BJLR26's `E_t[· | ζ_t]` given a σ-algebra contained in theirs, and
equal to it when the σ-algebra of a loss is that of its values on `K`; their two conditions pass to `G_t` by the tower
property (below). A kernel form (the noise of round `t` drawn from a Markov kernel of the past, the law of the game
built by the Ionescu-Tulcea theorem, or the noise a function of the past and a fresh seed) would fix the
joint law of the noise and of the adversary's future choices given the past, which BJLR26 do not fix: their noise of
round `t` may be correlated with randomness that the adversary uses later. The class here contains the route's class
(an argument, not proved in Lean: a noise `η(θ, past, u_t)` centred in a fresh seed `u_t` for every value of the rest
is centred given `G_t`, by the freezing lemma and the tower property). The clauses are not vacuous: `G_t` is a
sub-σ-algebra of the σ-algebra of `Ω` (its generators are measurable, sanity module `histσ_le`), so the conditional
expectation is not Mathlib's junk value `0`, and `exp (noise t ^ 2)` is asserted integrable, so neither clause holds
by non-integrability.

**Why windows.** The loss of round `t` must not read the coins with which the program draws its point of round `t`: an
adversary that reads the current draw forces regret `n/4`. The noise of
round `t` may read that draw (BJLR26 condition on it) but not the coins drawn after the observation, which the program
of the route uses to dither its estimate (a noise reading them breaks the
analysis; such a noise reads coins drawn after its own play, see the grouping below). A larger window only
enlarges the class (the coins being fair and independent), so clause (iv) fixes `D' t` to the number of coins read
when round `t` is played and asks `D t` to be at least the number read when round `t - 1` is played.

## Against BJLR26 Section 3, line by line (advcvx.tex l.158 to 186)

Their rounds are `t = 1, ..., n`, ours `t = 0, ..., n - 1`; their dimension is `d`, as ours.

**The grouping of the coins into rounds.** For the program here, BJLR26's `ζ_t` ("the randomness of the algorithm in
round t which it uses to make decisions", l.167) is the block of coins that the program reads after the play of round
`t - 1` and up to the play of round `t`: the coins of index in `[D' (t - 1), D' t)` (`D' (-1) = 0`), by clause (iv).
The program of the route reads no coin between a play and the observation of that round, so this block is the coins
read after the observation of round `t - 1` and up to the play of round `t`; it contains the coins drawn after that
observation (the dither of round `t - 1`) and the draw of round `t`, and not the
dither of round `t`, which belongs to `ζ_{t+1}`. The reason for this grouping: a noise generated at the play of round
`t` cannot depend on coins drawn after it, and in BJLR26's own algorithm all the randomness of round `t`, the Gaussian
draw `X_t` (l.321), precedes the play `A_t = X_t / π_ε(X_t)`. With `ζ_t` the whole randomness of round `t` including
the dither drawn after the observation, their conditions would admit a noise correlated with that later dither, which
breaks the coupling of the route; no noise generated at the play has that correlation. The block ends at
the play and not at the observation because on this machine the feedback of a round can be read any number of times,
so its observation is not one event, while its play is.

* l.158 to 160 "Let K be a convex body that is known to the learner." Here `K` is any compact convex set with
  `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, known to the program through a weak membership oracle and the input `a, r0, R0`.
  BJLR26 Theorem 3.1 (l.495) assumes `B_1 ⊆ K ⊆ B_{2d}` and an exact evaluation of the gauge of `K` (l.488); that is
  the case `a = 0`, `r0 = 1`, `R0 = 2 d` here, and the exact membership answer `[y ∈ K]`, which a gauge evaluation
  gives, is a weak membership oracle at every precision (sanity module, `weakMemOracle_exact`).
* l.161 to 163 "an adversary chooses a convex loss f_t : K → [0,1], the learner chooses an action A_t ∈ K, and it
  observes f_t(A_t) + ξ_t". Here the loss of round `t` is `loss t ω`, convex with values in `[0, 1]` on `K`
  (`NoisyAdv.adm`); the action is the point `playedO P w s0 t`, in `K` on every run (clause (iii)); the feedback is
  `loss t ω (x_t) + noise t ω` (`WorldO.toW`), which the program reads through `obsR` (or `obs`) at the precision it
  chooses. A bit machine cannot read a real number exactly; it reads any finite number of its digits, paying for each.
* l.164 to 166 "The adversary is adaptive: f_t may depend on everything that happened before round t, including the
  earlier actions of the learner, but not on the randomness that the learner uses in round t." Here `fresh_loss`: the
  coins of index at least `D t` are independent of the losses up to round `t`, the earlier noises and the coins of
  index below `D t`; the earlier actions and observations are functions of these, and the loss may depend on anything
  else on `Ω`. In particular the loss of round `t` may depend on every coin of index below `D t`: clause (iv) puts
  `D t` at least at `D' (t - 1)`, so these include `ζ_0, ..., ζ_{t-1}`, and for the program of the route, whose
  window `D t` ends after the dither of round `t - 1`, the loss of round `t` may
  also read that dither, which lies in their `ζ_t` and which their `f_t` may not read.
* l.167 to 169 "let ζ_t be the randomness of the algorithm in round t which it uses to make decisions, let
  F_t = σ(f_1, ζ_1, ξ_1, ..., f_t, ζ_t, ξ_t, f_{t+1})". With `ζ_t` grouped as above, the σ-algebra
  `G_t = histσ K loss noise coin (t + 1) t (D' t)` in our indices, generated by the values on `K` of the losses of the
  rounds `≤ t`, the noises of the rounds `< t` and the coins of index below `D' t`, is contained in
  `F_{t-1} ∨ σ(ζ_t)`, and equal to it when the σ-algebra of a loss is that of its values on `K`; and `F_t` contains
  `histσ K loss noise coin (t + 1) (t + 1) (D' t)`.
* l.170 to 173 "E_t[·] = E[· | F_{t-1}] ... Thus F_{t-1} contains the history up to the end of round t-1 together with
  the loss f_t, so that under E_t the loss of round t is fixed and only the randomness of the learner and the noise in
  that round remain." This presupposes that `ζ_t` is independent of `F_{t-1}` and has the law of the learner's
  randomness (here fair coins), as l.164 to 166 say in words; nothing more is assumed of the joint law.
* l.174 to 178 "E_t[ξ_t | ζ_t] = 0, E_t[exp(ξ_t²) | ζ_t] ≤ 2". Here `noise_mean` and `noise_exp`: the same two
  conditional expectations, given `G_t`, written `μ[· | G_t]`; `G_t` is `F_{t-1} ∨ σ(ζ_t)` when the σ-algebra of a loss
  is that of its values on `K`, and in general a sub-σ-algebra of it, to which their two conditions pass by the tower
  property; `noise_int` is the integrability that makes the second one a Bochner conditional expectation (it follows
  from theirs: `E exp(ξ_t²) = E E_t[exp(ξ_t²) | ζ_t] ≤ 2`).
* l.181 "This includes noiseless feedback." The zero noise is a member (sanity module, `hyps_satisfiable`).
* l.182 to 186 the realized regret `Reg_n = Σ_t f_t(A_t) - inf_{x ∈ K} Σ_t f_t(x)` against the losses of the run:
  `regretU`, built on `regretPts` (StatementPoly.lean), the same expression. Their bound holds with probability
  `1 - δ`, as the probability clause here; the expectation clause is added.

**Their environment is one of ours.** Take an environment of BJLR26 played by the program here, with `ζ_t` grouped as
above, independent of `F_{t-1}` and fair, and give the coins that the program never reads in the `n` rounds (their
model has none) a fair law independent of everything (a product extension of their space, which changes no loss,
noise or action). Then, condition by condition:

* `coin_law`, `coin_meas`: the coins are fair and independent (their l.164 to 173, as read above, and the product
  extension).
* `adm`, `loss_meas`, `noise_meas`: their `f_t : K → [0, 1]` convex, and `f_t`, `ξ_t` random variables.
* `fresh_loss`: by induction over the blocks `ζ_t, ζ_{t+1}, ...`, each independent of the σ-algebra before it, and the
  fresh coins, the coins of index at least `D' (t - 1)` are independent of `F_{t-1}`; being fair and independent among
  themselves, those of index at least `N` are then independent of `F_{t-1} ∨ σ(coins of index in [D' (t - 1), N))` for
  every `N ≥ D' (t - 1)`. At `N = D t`, which is at least `D' (t - 1)` by clause (iv), that σ-algebra contains
  `histσ K loss noise coin (t + 1) t (D t)`.
* `fresh_noise`: the same argument with `F_t` in place of `F_{t-1}` and `N = D' t`; `F_t` contains
  `histσ K loss noise coin (t + 1) (t + 1) (D' t)`.
* `noise_mean`, `noise_exp`, `noise_int`: their l.174 to 178, passed to `G_t ⊆ F_{t-1} ∨ σ(ζ_t)` by the tower
  property, as said.

So the class `NoisyAdv` contains their adversary and their noise for the program, with no restriction, and contains
more: the loss of round `t` may also read the coins of index in `[D' (t - 1), D t)`.

## The regret, the probability and the expectation

`regretU P K n s0 w = Σ_{t < n} w.f t (x_t) - inf_{y ∈ K} Σ_{t < n} w.f t y`, `x_t` the points played in the world
`w`. The regret of the environment at `ω` is that of the world `envWorld orc coin loss noise ω`. Its measurability on
`Ω` is asserted, so the event `{Reg > C d^{3/2} n^{1/2} L^5}` is measurable and the probability clause bounds its
measure; its integrability is asserted, so `max (Reg, 0)` is integrable and its Bochner integral is its expectation.
The confidence `δ` is the program's input: the same program meets the two regret clauses for every `δ`. At
`δ = 1/(n+1)` the expectation clause gives `E max (Reg, 0) ≤ C d^{3/2} n^{1/2} log^5 (2 d n (n + 1)) + 1`.

## Non-vacuity (AdversarialBco/Unified/Sanity.lean)

The hypotheses hold together at `d = n = 1`, `δ = 1/2`, `a = 0`, `r0 = R0 = 1`, the ball `B̄(0, 1)`, its exact
membership oracle, the zero losses with zero noise on the coin space (`hyps_satisfiable`, for all windows); the class
has members with nonzero noise in every round (`noisyAdv_signNoise`, for every `K`, `n` and windows); the conditional
expectations are taken given a sub-σ-algebra (`histσ_le`); and the empty program fails the cost clause
(`nil_not_costOKO`). The Comparator configuration config-unified.json certifies them next to the theorem, from its
solution module `AdversarialBco.Unified.Main`.

## What is not claimed

An oracle whose ambiguous answers change from run to run (a random or adversarial oracle): the oracle is a fixed
function, for every such function. Plays in the interior of `K` (the program of the route plays interior points; the
statement asks `K`). A body without a known centre and radii: Conjecture 1 of Bubeck, Eldan and Lee on their
polytopes, where the program finds a centre itself, is `TheoremConj1UpperBitHP` (StatementConj1BitHP.lean), and its
derivation from `TheoremUnified` is left to the proof lanes as an implication between the two frozen statements. A
noise that reads the coins drawn after the play of its round, or a loss that reads the coins of the current draw (see
"Why windows"). A real `δ` (a real `δ` is served by a rational in `[δ/2, δ]`, at the price of a constant inside `L`).
The lower bound (a separate statement).

## Junk values

`log (2 d n / δ) > log 2 > 0` for `d, n ≥ 1` and `0 < δ < 1`. `S ≥ 3 + d > 0`: every denominator is at least `1`,
of length at least `1`. A negative `C'` makes `B` negative, and the cost clause then fails at step `0` (the cost never
decreases), as does the space clause (`SpaceLE s B` is false for `B < 0`); a negative `C` lowers the threshold of both
regret clauses, which only makes them harder. `ENNReal.ofReal δ` is `δ` since `δ > 0`. `playedO` is `0` for a round
that never comes, and the cost clause makes every round `t < n` come on every run. `regretPts` takes the infimum of a
set of reals bounded below by `0` on the nonempty `K`. `inputU` reads the coordinate `(c - 8) / 2` only when it is
below `d`. `μ.map coin` is the law of a measurable map. The conditional expectations and the independences are
between sub-σ-algebras of the σ-algebra of `Ω` (`histσ_le`). The machine's junk values are listed in
StatementBitRAM.lean and StatementBitRAMO.lean; `coinStream` is a probability measure
(AdversarialBco/Conj1Bit/Sanity.lean).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace Unified

open BitRAM BitRAMO
open RealRAM (regretPts)

/-- The input in the memory: `d`, `n` in the cells `0`, `1`; the numerators and the denominators in lowest terms of
`δ`, `r0`, `R0` in the cells `2` to `7`; those of the coordinate `a i` in the cells `8 + 2 i` and `9 + 2 i`, `i < d`;
every other cell `0`. -/
def inputU (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℤ → ℤ :=
  fun c =>
    if c = 0 then d
    else if c = 1 then n
    else if c = 2 then δ.num
    else if c = 3 then δ.den
    else if c = 4 then r0.num
    else if c = 5 then r0.den
    else if c = 6 then R0.num
    else if c = 7 then R0.den
    else if h : 8 ≤ c ∧ (c - 8).toNat / 2 < d then
      (if (c - 8).toNat % 2 = 0 then (a ⟨(c - 8).toNat / 2, h.2⟩).num
       else ((a ⟨(c - 8).toNat / 2, h.2⟩).den : ℤ))
    else 0

/-- The initial state on the input: the memory `inputU d n δ r0 R0 a`, the counter, the coins used, the rounds and the
cost at `0`. -/
def initU (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : State d where
  pc := 0
  mem := inputU d n δ r0 R0 a
  coins := 0
  rounds := 0
  pts := fun _ _ => 0
  cost := 0

/-- The bit length of the data `δ`, `r0`, `R0`, `a`: the lengths of their numerators and denominators. -/
noncomputable def sizeU {d : ℕ} (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℝ :=
  ((len δ.num + len δ.den + len r0.num + len r0.den + len R0.num + len R0.den +
    ∑ i, (len (a i).num + len (a i).den) : ℕ) : ℝ)

/-- The world of the environment at `ω`: its losses, its noises and its coins at `ω`, and the oracle. -/
def envWorld {d : ℕ} {Ω : Type} (orc : (Fin d → ℚ) → ℕ → Bool) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
    (noise : ℕ → Ω → ℝ) (ω : Ω) : WorldO d :=
  ⟨fun t => loss t ω, fun t => noise t ω, coin ω, orc⟩

/-- The σ-algebra of the coins of index below `N`. -/
abbrev coinsBelow {Ω : Type} (coin : Ω → ℕ → Bool) (N : ℕ) : MeasurableSpace Ω :=
  ⨆ (j : ℕ) (_ : j < N), MeasurableSpace.comap (fun ω => coin ω j) inferInstance

/-- The σ-algebra of the coins of index at least `N`. -/
abbrev coinsFrom {Ω : Type} (coin : Ω → ℕ → Bool) (N : ℕ) : MeasurableSpace Ω :=
  ⨆ (j : ℕ) (_ : N ≤ j), MeasurableSpace.comap (fun ω => coin ω j) inferInstance

/-- The σ-algebra of the loss of round `t`: generated by its values at the points of `K`. -/
abbrev lossσ {d : ℕ} {Ω : Type} (K : Set (E d)) (loss : ℕ → Ω → E d → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ (y : E d) (_ : y ∈ K), MeasurableSpace.comap (fun ω => loss t ω y) inferInstance

/-- The σ-algebra of the noise of round `t`. -/
abbrev noiseσ {Ω : Type} (noise : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (noise t) inferInstance

/-- The σ-algebra generated by the losses of the rounds below `L`, the noises of the rounds below `M` and the coins of
index below `N`. -/
abbrev histσ {d : ℕ} {Ω : Type} (K : Set (E d)) (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) (coin : Ω → ℕ → Bool)
    (L M N : ℕ) : MeasurableSpace Ω :=
  (⨆ (s : ℕ) (_ : s < L), lossσ K loss s) ⊔ (⨆ (s : ℕ) (_ : s < M), noiseσ noise s) ⊔ coinsBelow coin N

/-- A noisy adversary on `K` for `n` rounds with the windows `D` (losses) and `D'` (noises), on the probability space
`(Ω, μ)` that carries the program's coins, the losses and the noises: the coins are fair and independent; each loss is
convex with values in `[0, 1]` on `K`, with measurable values; the coins from the window of a loss on are independent
of that loss, the earlier losses and noises and the coins in the window; the coins from the window of a noise on are
independent of that noise, the losses up to its round, the earlier noises and the coins in the window; and the noise of
round `t` has conditional mean `0` and conditional `E exp(noise²) ≤ 2` given the losses up to round `t`, the earlier
noises and the coins in its window. -/
structure NoisyAdv {d : ℕ} (K : Set (E d)) (n : ℕ) (D D' : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) : Prop where
  /-- `μ` is a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- The coins are a measurable function on `Ω`. -/
  coin_meas : Measurable coin
  /-- The coins are fair and independent. -/
  coin_law : μ.map coin = coinStream
  /-- Each loss of the rounds `t < n` is convex with values in `[0, 1]` on `K`, on every `ω`. -/
  adm : ∀ t < n, ∀ ω, AdmLoss K (loss t ω)
  /-- The value of each loss of the rounds `t < n` at each point of `K` is measurable. -/
  loss_meas : ∀ t < n, ∀ y ∈ K, Measurable fun ω => loss t ω y
  /-- The noise of each round `t < n` is measurable. -/
  noise_meas : ∀ t < n, Measurable (noise t)
  /-- The coins of index at least `D t` are independent of the losses of the rounds `≤ t`, the noises of the rounds
  `< t` and the coins of index below `D t`. -/
  fresh_loss : ∀ t < n, Indep (coinsFrom coin (D t)) (histσ K loss noise coin (t + 1) t (D t)) μ
  /-- The coins of index at least `D' t` are independent of the losses and the noises of the rounds `≤ t` and the coins
  of index below `D' t`. -/
  fresh_noise : ∀ t < n, Indep (coinsFrom coin (D' t)) (histσ K loss noise coin (t + 1) (t + 1) (D' t)) μ
  /-- `exp (noise t ^ 2)` is integrable. -/
  noise_int : ∀ t < n, Integrable (fun ω => Real.exp (noise t ω ^ 2)) μ
  /-- The noise of round `t` is centred given the losses of the rounds `≤ t`, the noises of the rounds `< t` and the
  coins of index below `D' t`. -/
  noise_mean : ∀ t < n, μ[noise t | histσ K loss noise coin (t + 1) t (D' t)] =ᵐ[μ] 0
  /-- Given the same σ-algebra, the conditional expectation of `exp (noise t ^ 2)` is at most `2`. -/
  noise_exp : ∀ t < n,
    μ[fun ω => Real.exp (noise t ω ^ 2) | histσ K loss noise coin (t + 1) t (D' t)] ≤ᵐ[μ] fun _ => 2

/-- The coin clause: for every round `t < n` and every step, a state with at most `t` rounds played has read at most
`D' t` coins and a state with more than `t` rounds played at least `D' t` coins (so exactly `D' t` coins are read when
round `t` is played), and a state with fewer than `t` rounds played has read at most `D t` coins. -/
def CoinWindowsOK {d : ℕ} (P : List InstrO) (w : WorldO d) (s0 : State d) (n : ℕ) (D D' : ℕ → ℕ) : Prop :=
  ∀ t < n, ∀ k : ℕ,
    ((runO P w s0 k).rounds ≤ t → (runO P w s0 k).coins ≤ D' t) ∧
      (t < (runO P w s0 k).rounds → D' t ≤ (runO P w s0 k).coins) ∧
      ((runO P w s0 k).rounds < t → (runO P w s0 k).coins ≤ D t)

/-- The regret of the run of `P` from `s0` in the world `w` over `n` rounds, on `K`, against the losses of `w`. -/
noncomputable def regretU {d : ℕ} (P : List InstrO) (K : Set (E d)) (n : ℕ) (s0 : State d) (w : WorldO d) : ℝ :=
  regretPts K w.f (playedO P w s0) n

end Unified

open BitRAM BitRAMO Unified in
/-- **Theorem U.** One program `P` of the bit RAM with a weak membership oracle, constants `C, C', k` and coin
schedules `D, D'` such that, for every `d, n ≥ 1`, every rational `δ ∈ (0, 1)`, every rational centre `a` and radii
`0 < r0 ≤ R0`, every compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` and every weak membership oracle of `K`:
on every world (admissible losses, any noise, any coins) `P` plays `n` rounds, each within cost
`C' (d log(2dn/δ) S)^k` with its cells in use within the same bound, at points of `K`, reading exactly `D' t` coins
before the play of round `t` and at most `D t` before the play of round `t - 1`; and for every noisy adversary with
these windows (BJLR26's adversary and noise) the regret is measurable and integrable, exceeds
`C d^{3/2} √n log(2dn/δ)^5` with probability at most `δ`, and its positive part has mean at most that plus `n δ`. -/
def TheoremUnified : Prop :=
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
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
        (noise : ℕ → Ω → ℝ), NoisyAdv K n (D d n δ r0 R0 a) (D' d n δ r0 R0 a) μ coin loss noise →
        Measurable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) ∧
        Integrable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) μ ∧
        μ {ω | C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 <
            regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤ ENNReal.ofReal (δ : ℝ) ∧
        ∫ ω, max (regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) 0 ∂μ ≤
          C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ)

/-- Theorem U: the theorem that a solution module proves. -/
theorem theoremUnified : TheoremUnified := by
  sorry

namespace Unified.UnifiedSanity

open BitRAM BitRAMO

/-- The exact membership answer is a weak membership oracle for `K` at every precision. -/
theorem weakMemOracle_exact {d : ℕ} (K : Set (E d)) [DecidablePred (· ∈ K)] :
    WeakMemOracle K (fun y _ => decide (toE y ∈ K)) := by
  sorry

/-- Under `NoisyAdv`, the σ-algebra generated by the losses of the rounds below `L ≤ n`, the noises of the rounds below
`M ≤ n` and the coins below any index, and that of the coins from any index on, are sub-σ-algebras of the σ-algebra
of `Ω`. -/
theorem histσ_le {d n : ℕ} {K : Set (E d)} {D D' : ℕ → ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
    (h : NoisyAdv K n D D' μ coin loss noise) {L M : ℕ} (hL : L ≤ n) (hM : M ≤ n) (N : ℕ) :
    histσ K loss noise coin L M N ≤ mΩ ∧ coinsFrom coin N ≤ mΩ := by
  sorry

/-- The hypotheses of `TheoremUnified` hold together: `d = n = 1`, `δ = 1/2`, the centre `0`, `r0 = R0 = 1`, the closed
unit ball with its exact membership oracle, and the zero losses with zero noise on the coin space, for all windows. -/
theorem hyps_satisfiable (D D' : ℕ → ℕ) :
    (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) < 1 ∧ (0 : ℚ) < 1 ∧ (1 : ℚ) ≤ 1 ∧
      IsCompact (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin 1 → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin 1 → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin 1 → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      NoisyAdv (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) 1 D D' coinStream (fun ω => ω)
        (fun _ _ _ => 0) (fun _ _ => 0) := by
  sorry

/-- The class has members with a nonzero noise in every round: on the fair coins indexed by `ℕ ⊕ ℕ`, the program's
coins at the indices `inl j`, the noise of round `t` equal to `1/2` or `-1/2` according to the coin at `inr t`, and the
zero losses, for every convex `K`, every `n` and all windows. -/
theorem noisyAdv_signNoise {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (n : ℕ) (D D' : ℕ → ℕ) :
    NoisyAdv K n D D' (Measure.infinitePi fun _ : ℕ ⊕ ℕ => coinLaw) (fun ω j => ω (Sum.inl j))
        (fun _ _ _ => 0) (fun t ω => if ω (Sum.inr t) then 1 / 2 else -1 / 2) ∧
      ∀ (t : ℕ) (ω : ℕ ⊕ ℕ → Bool), (if ω (Sum.inr t) then (1 / 2 : ℝ) else -1 / 2) ≠ 0 := by
  sorry

/-- The empty program never plays, so it fails the cost clause on every input with `n ≥ 1`. -/
theorem nil_not_costOKO {d : ℕ} (w : WorldO d) (s0 : State d) (n : ℕ) (B : ℝ) (h0 : s0.rounds < n) :
    ¬ CostOKO [] w s0 n B := by
  sorry

end Unified.UnifiedSanity

end AdversarialBco
