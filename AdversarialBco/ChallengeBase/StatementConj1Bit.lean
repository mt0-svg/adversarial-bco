/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenges, fifth module: AdversarialBco/StatementConj1Bit.lean verbatim over the third and fourth
-- modules (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1Poly
public import AdversarialBco.ChallengeBase.StatementBitRAM

@[expose] public section

/-!
# Statement: Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in a bit-cost model

Conjecture 1 of Bubeck, Eldan and Lee (arXiv 1607.03084, BEL16.tex l.86 to 88; J. ACM 68 (2021), Conjecture 1):
"There exists an algorithm such that each step takes poly(n log(T))-time (under the same assumption on K as in
Theorem 1) and which achieves E R_T = Õ(n^{1.5} √T)." The assumption of their Theorem 1 (l.82): "K is a polytope
described by poly(n) constraints whose coefficients are rational numbers with absolute values of numerators and
denominators bounded by poly(T)"; their normalisation (l.76): K contains a unit ball and has diameter at most T.
Their game (l.69 to 73): in each round the player selects `x_t ∈ K` and simultaneously an adversary selects a convex
loss `l_t : K → [0, 1]`; the feedback is `l_t(x_t)`; the player has external randomness and selects `x_t` from the
history `(x_s, l_s(x_s))_{s<t}`; `R_T = Σ_t l_t(x_t) - min_{x ∈ K} Σ_t l_t(x)`. Their analysis (l.656) takes the
filtration `F_t = σ(l_1, x_1, ..., l_t, x_t, l_{t+1})`: the losses are random variables, `l_{t+1}` is chosen with the
knowledge of the rounds up to `t`.

`TheoremConj1UpperBit` is that sentence, with time counted in bit operations: in their letters `n` is the dimension
and `T` the horizon, here `d` and `n`.

## The claim (`TheoremConj1UpperBit`)

There are one program `P` of the logarithmic-cost RAM of StatementBitRAM.lean, constants `C`, `C'` and an exponent
`k` such that for all `d ≥ 1`, `n ≥ 1`, `m`, `M`, every `A ∈ ℚ^{m × d}` and `b ∈ ℚ^m` whose entries have numerators
and denominators at most `M` in absolute value, whose polytope `K = {x : A x ≤ b}` contains a closed ball of radius `1`
and has diameter at most `n`, every probability space `(Θ, ρ)` of the adversary's seed and every randomised adaptive
adversary `σ` on `K` for `n` rounds (`RandAdv`), the run of `P` on the input `d, n, m, A, b` (`initBit`) satisfies,
with `L = log (2 d n)`:

* on every run (every seed `θ` and every coin sequence) each round `t < n`, the first included, is played within cost
  `C' (d m L log (2 M))^k` of the state from which it is awaited, at every step before the play of round `n - 1` the
  cells in use have total bit length at most `C' (d m L log (2 M))^k`, and every point played in a round `t < n` lies
  in `K`;
* the upper expectation of the positive part of the regret over the seed and the coins is at most
  `C d^{3/2} n^{1/2} L^5`: there is a measurable `R : Θ × (ℕ → Bool) → ℝ≥0` with `Reg ≤ R` on every run and
  `∫ R d(ρ ⊗ coinStream) ≤ C d^{3/2} n^{1/2} L^5`, the regret being taken on `K` against the losses that the adversary
  chose on that run.

In BEL's letters: for `m` at most a power of the dimension and `M` at most a power of the horizon, every step has a
cost, on the logarithmic-cost RAM, polynomial in `n log T`, a Turing machine simulates every step in time polynomial in
`n log T` (StatementBitRAM.lean, "Why this is a bit-cost model"), and `E R_T ≤ C n^{3/2} T^{1/2} log^5 (2 n T)`,
which is `Õ(n^{1.5} √T)`. For every `m` and `M` the cost and the space of a step are polynomial in `d`, `m`, `log n`
and `log M`.

## The input (`inputMem`, `initBit`)

The polytope and the bound `M` are those of StatementConj1Poly.lean (`polytope`, `HeightLE`),
reused unchanged: every `m` (no bound on the number of facets), every `M`, and BEL's two normalisations as hypotheses,
the ball of radius `1` centred anywhere (the centre is not given to the program) and the diameter bound written with
`dist`. The program reads integers: the cells `0`, `1`, `2` hold `d`, `n`, `m`; the entry `e = (d + 1) i + j` of the
rows `(A i 0, ..., A i (d - 1), b i)`, `i < m`, `j ≤ d`, has its numerator in lowest terms in the cell `3 + 2 e` and its
denominator in the cell `4 + 2 e`; every other cell is `0`. The program is not told `M`; the lengths of the data are
what the program pays to read. `M` stays in the statement as BEL's height bound: the cost bound is polynomial in
`log M`, and a height polynomial in the horizon makes it polynomial in `d`, `m` and `log n`.

## The game (`GameBit`, `stepBit`, `runBit`, `playedBit`)

The adversary is a strategy `σ θ` for each seed `θ` (`Strategy`, StatementConj1.lean): the loss of round `t` is
`σ θ t x o`, a function of the points `x 0, ..., x (t - 1)` played and the feedbacks `o 0, ..., o (t - 1)` of the
rounds before `t`. The game has no noise, as BEL's: the feedback of round `u` is `l_u (x_u)` exactly, rebuilt by
`obsAd σ 0` and read by the program through `obs`, binary digit by binary digit. At each step the machine runs in the
world whose loss of round `t` is `lossAd (σ θ) 0 x t`, `x` the points the state records as played; the coins
are the run's coin sequence. So the loss of round `t` is
fixed by the seed and the rounds before `t`, before the point of round `t` exists: the adversary moves simultaneously
with the player, and is adaptive.

## The feedback interface

The program reads the feedback `o` of the last round played through `obs dst prec`: the integer `⌊2^p o⌋`, its first
`p` binary digits (`o ∈ [0, 1]` on the plays in `K`), at a cost of `p` plus the length of the result, `p` chosen by the
program at run time, as often as it likes until its next play. Every reading is a function of `l_t(x_t)`, so the
program learns nothing BEL's player does not; it can read any finite number of digits, paying one per digit, which is
all a bit machine can do with a real number. Alternatives not taken: a reading rounded by an adversary within
`2^{-p}` (the oracle of computable analysis), a fixed precision, an exact rational feedback (which would restrict the
losses), a one-bit randomised feedback.

## The adversary (`RandAdv`)

A seed `θ` is drawn from a probability measure `ρ` on any measurable space `Θ`, independently of the program's coins,
and the adversary plays the strategy `σ θ`. It reads the points and the exact feedbacks of the earlier rounds, never
the program's coins: BEL's player "has access to external randomness", and their filtration `F_t` is generated by
the plays and the losses alone. An adversary of BEL's game whose randomness is independent of the player's is of this
form, with `θ` all of its randomness. The deterministic strategies are the case `Θ = Unit`, and the oblivious
sequences the strategies that read nothing. `(Θ, σ)` comes after the program and the instance, so it may depend on
`P`, `d`, `n`, `A`, `b`.

What `RandAdv` asks, for every round `t < n` and every rational history `q` of points (a sequence of `ℚ^d`, of which
the loss of round `t` reads the first `t` terms):

* the loss of round `t` on that history, `lossAd (σ θ) 0 q t`, is a convex function `K → [0, 1]` (`AdmLoss`), for every
  seed;
* at each point `y ∈ K`, that loss is a measurable function of the seed.

The second is exactly what BEL's filtration presupposes, and no more: it says that `l_t(y)` is a random variable for
every player that plays rational points. Since the points played are rational and take countably many values, the
loss of round `t` at `y` on a run is the countable sum over the histories `q` of the indicator of `{x_{<t} = q}` times
the loss on `q`, measurable as soon as each term is; conversely, the player that plays a fixed rational sequence `q`
makes the loss on `q` the random variable `l_t(y)` itself. So the condition is necessary and sufficient for the losses
to be random variables in every game against a player of rational points. A deterministic strategy needs no
measurability at all: its losses on a rational history do not depend on the seed. This is weaker than the condition
`Strats` of StatementConj1.lean (Borel in the real history), which the real-RAM statements need because there the
points played have continuous laws; a one-round example shows that some measurability cannot be dropped there. Here
it can for deterministic strategies, and is kept in the seed only. Both
conditions are asked on every rational history, also on those with a point outside `K`, which no run of a program that
plays in `K` reaches: there the loss can be set to `0` (whether a history has a point outside `K` does not depend on the
seed), which changes no such run and keeps both conditions.

## The regret and the expectation

The regret of a run is `regretPts K (lossAd (σ θ) 0 x) x n`, `x` the points played: `Σ_{t < n} l_t (x_t)` minus the
infimum over `K` of `Σ_{t < n} l_t`, against the losses chosen on that run (StatementConj1.lean). The infimum is BEL's
minimum when it is attained, and is at most every value, so this regret is at least `R_T`. The expectation is over the
product `ρ ⊗ coinStream`, the seed independent of the coins, which are fair and independent (`coinStream`,
StatementBitRAM.lean). The statement bounds the upper expectation of the positive part of the regret: a
measurable `R ≥ 0` above the regret on every run, with `∫ R` at most the bound,
asks nothing of the regret itself, and gives `E R_T ≤` the bound whenever `R_T` is measurable and integrable. Under
`RandAdv` the regret is measurable in the seed and the coins (proved in Lean for every program, in the proof of the
corollary in expectation of StatementConj1BitExp.lean): the points played take countably many values, each on an
event measurable in the seed and the coins, and a convex function on `K` has the
same infimum over `K` as over a countable dense subset of the interior of `K` (it is continuous on the interior, and at
a boundary point `y`, `g ((1 - s) y + s z) ≤ (1 - s) g y + s g z` for `z` interior); so `max (Reg, 0)` is a measurable
majorant, and the clause amounts to `E max (Reg, 0) ≤` the bound.

## The cost clause (`CostOKBit`)

For every step `k` at which fewer than `n` rounds have been played, some later step plays one more round, and the cost
spent between the two is at most `B = C' (d m L log (2 M))^k`. Applied at the step after the play of round `t - 1` (at
step `0` for `t = 0`), it bounds the cost of round `t` by `B`: every round, the first included, costs at most `B`, and
nothing is amortised. Since `cost` never decreases and a halted machine never plays, it also forces all `n` rounds to
be played on every run. Besides the digits of `d`, `n` and `m`, the input has at most `2 m (d + 1) (1 + log₂ M)` binary
digits, polynomially many in the quantities of `B`, so a program can read all of it within one round.

## The space clause (`SpaceOKBit`)

At every step at which fewer than `n` rounds have been played, so at every step of every round up to the play of
round `n - 1`, the cells in use (`SpaceLE`, StatementBitRAM.lean: the cells with a nonzero content, their addresses and
contents) have total bit length at most the same `B`. Together with the cost clause, it bounds the time of a Turing
machine that simulates a round by a polynomial in `d`, `m`, `log n` and `log M` (StatementBitRAM.lean, "Why this is a
bit-cost model"). Without it, a program could keep a cell for each past round and reach any of them at cost
`O(log n)`, while on a Turing machine these cells fill a tape of length of order `t` in round `t`. The input is in the
memory and is counted: its cells in use, addresses and contents, have total bit length at most
`N (len N + len d + len n + len m + len M)` with `N = 3 + 2 (d + 1) m` (`input_space_nat`,
AdversarialBco/Conj1Bit/Sanity.lean). The points played are output and are
not counted; the machine stores nothing for the program outside its cells.

## What is not claimed

The second sentence of the conjecture (StatementConj1Lower.lean); a noisy feedback (the conjecture's game has none,
and an unbounded noise would make the digits before the point unbounded too); an adversary that reads the program's
coins (an adversary that reads the current draw forces regret `n/4`).

## Junk values

`log (2 d n) ≥ log 2 > 0` for `d, n ≥ 1`. `log (2 M)`: the hypotheses force `m ≥ 1` (with no row the polytope is the
whole space, of unbounded diameter) and then `M ≥ 1` (a denominator is at least `1`), so `log (2 M) ≥ log 2 > 0`. A
negative `C'` makes `B` negative, and the cost clause then fails at step `0` (the cost never decreases), as does the
space clause (`SpaceLE s B` is false for `B < 0`), so it cannot help; a negative `C` makes the bound `0`
(`ENNReal.ofReal`), which only makes the claim harder. `playedBit` is `0` for a round that never comes, and the cost
clause makes every round `t < n` come on every run. `inputMem` reads the row `e / (d + 1)` and the column
`e % (d + 1)` of the entry `e` only when the row is below `m`, with `d + 1 ≥ 1`. The junk values of the machine are
listed in StatementBitRAM.lean; `coinStream` is a probability measure (`isProbabilityMeasure_coinStream`,
AdversarialBco/Conj1Bit/Sanity.lean), so `ρ ⊗ coinStream` is one
when `ρ` is.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace AdversarialBco

namespace BitRAM

open RealRAM (Strategy lossAd regretPts polytope HeightLE)

/-- The entry `j` of the row `i` of the input: `A i j` for `j < d`, `b i` for `j = d`. -/
def entry {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i : Fin m) (j : ℕ) : ℚ :=
  if hj : j < d then A i ⟨j, hj⟩ else b i

/-- The input in the memory: `d`, `n`, `m` in the cells `0`, `1`, `2`; the entry `e = (d + 1) i + j` of the rows
`(A i 0, ..., A i (d - 1), b i)` with its numerator (in lowest terms) in the cell `3 + 2 e` and its denominator in the
cell `4 + 2 e`; every other cell `0`. -/
def inputMem (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℤ → ℤ :=
  fun c =>
    if c = 0 then d
    else if c = 1 then n
    else if c = 2 then m
    else if h : 3 ≤ c ∧ (c - 3).toNat / 2 / (d + 1) < m then
      (if (c - 3).toNat % 2 = 0 then (entry A b ⟨(c - 3).toNat / 2 / (d + 1), h.2⟩ ((c - 3).toNat / 2 % (d + 1))).num
       else ((entry A b ⟨(c - 3).toNat / 2 / (d + 1), h.2⟩ ((c - 3).toNat / 2 % (d + 1))).den : ℤ))
    else 0

/-- The initial state on BEL's input: the memory `inputMem d n m A b`, the counter, the coins used, the rounds and the
cost at `0`. -/
def initBit (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : State d where
  pc := 0
  mem := inputMem d n m A b
  coins := 0
  rounds := 0
  pts := fun _ _ => 0
  cost := 0

/-- What the program plays against: a strategy of the adversary (its seed fixed) and the coin sequence. -/
structure GameBit (d : ℕ) where
  /-- The strategy. -/
  σ : Strategy d
  /-- The coin sequence, `true` for heads. -/
  cs : ℕ → Bool

/-- The world of the machine when the points played so far are `x`: the losses that the strategy gives on them, in the
game without noise. -/
noncomputable def GameBit.world {d : ℕ} (g : GameBit d) (x : ℕ → Fin d → ℚ) : World d :=
  ⟨lossAd g.σ 0 (fun i => toE (x i)), g.cs⟩

/-- One step against a strategy: the step of the machine in the world of the points the state records as played. -/
noncomputable def stepBit {d : ℕ} (P : List Instr) (g : GameBit d) (s : State d) : State d :=
  step P (g.world s.pts) s

/-- The state after `k` steps against a strategy. -/
noncomputable def runBit {d : ℕ} (P : List Instr) (g : GameBit d) (s0 : State d) (k : ℕ) : State d :=
  (stepBit P g)^[k] s0

open Classical in
/-- The point played in round `t` against a strategy, as a point of `E d` (`0` if that round never comes). -/
noncomputable def playedBit {d : ℕ} (P : List Instr) (g : GameBit d) (s0 : State d) (t : ℕ) : E d :=
  if h : ∃ k, t < (runBit P g s0 k).rounds then toE ((runBit P g s0 (Nat.find h)).pts t) else 0

/-- The cost clause: from every step at which fewer than `n` rounds have been played, one more round is played within
cost `B`. -/
def CostOKBit {d : ℕ} (P : List Instr) (g : GameBit d) (s0 : State d) (n : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, (runBit P g s0 k).rounds < n →
    ∃ j : ℕ, (runBit P g s0 k).rounds < (runBit P g s0 (k + j)).rounds ∧
      ((runBit P g s0 (k + j)).cost : ℝ) ≤ (runBit P g s0 k).cost + B

/-- The space clause: at every step at which fewer than `n` rounds have been played, the cells in use have total bit
length at most `B`. -/
def SpaceOKBit {d : ℕ} (P : List Instr) (g : GameBit d) (s0 : State d) (n : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, (runBit P g s0 k).rounds < n → SpaceLE (runBit P g s0 k) B

/-- A randomised adaptive adversary on `K` for `n` rounds, a strategy `σ θ` for each seed `θ`: for every round
`t < n` and every rational history `q` of points, the loss of round `t` on `q` is a convex function `K → [0, 1]` for
every seed, and at each point of `K` it is a measurable function of the seed. -/
def RandAdv {d : ℕ} (K : Set (E d)) (n : ℕ) {Θ : Type} [MeasurableSpace Θ] (σ : Θ → Strategy d) : Prop :=
  ∀ t < n, ∀ q : ℕ → Fin d → ℚ,
    (∀ θ, AdmLoss K (lossAd (σ θ) 0 (fun i => toE (q i)) t)) ∧
      ∀ y ∈ K, Measurable fun θ => lossAd (σ θ) 0 (fun i => toE (q i)) t y

end BitRAM

open BitRAM in
open RealRAM (Strategy lossAd regretPts polytope HeightLE) in
/-- The first sentence of Conjecture 1 of Bubeck, Eldan and Lee, with time counted in bit operations: one program of
the logarithmic-cost RAM with fair coins, which reads the dimension, the horizon, the number of constraints and the
rational constraints of a polytope that contains a unit ball and has diameter at most `n`, and is told nothing else,
plays rational points of the polytope, each round within cost polynomial in `d`, `m`, `log (2 d n)` and `log (2 M)`
with its cells in use of total bit length within the same bound, and has an upper expected regret at most
`C d^{3/2} n^{1/2} log^5 (2 d n)` against every randomised adaptive adversary: a measurable `R ≥ 0` above the regret
on every run, with that integral over the seed and the coins. -/
def TheoremConj1UpperBit : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ,
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), HeightLE A b M →
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) →
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) →
    ∀ (Θ : Type) [MeasurableSpace Θ] (ρ : Measure Θ), IsProbabilityMeasure ρ →
    ∀ σ : Θ → Strategy d, RandAdv (polytope A b) n σ →
      (∀ (θ : Θ) (cs : ℕ → Bool),
        CostOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
          SpaceOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
          ∀ t < n, playedBit P ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b) ∧
      ∃ R : Θ × (ℕ → Bool) → ℝ≥0, Measurable R ∧
        (∀ ω : Θ × (ℕ → Bool),
          regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
              (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n ≤ R ω) ∧
        ∫⁻ ω, (R ω : ENNReal) ∂(ρ.prod coinStream) ≤
          ENNReal.ofReal (C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5)

end AdversarialBco
