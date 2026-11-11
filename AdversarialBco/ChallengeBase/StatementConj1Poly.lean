/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenges, third module: AdversarialBco/StatementConj1Poly.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1

@[expose] public section

/-!
# The frozen statement of Theorem 1.3: Conjecture 1 of Bubeck, Eldan and Lee, upper half, on their polytopes

The input is that of Theorem 1 of Bubeck, Eldan and Lee (arXiv 1607.03084) and nothing else. The machine, its step function, the strategies, the noise, the run against a strategy,
the cost clause and the regret are those of `TheoremConj1Upper` (StatementConj1.lean) and `TheoremPoly32O`
(StatementPoly.lean), reused unchanged. What changes: the program has no `query` instruction, and the body is a
polytope whose rational data the program reads in its real memory.

## The statement (`TheoremConj1UpperPoly`)

There are one program `P` of the machine of StatementPoly.lean with no `query` instruction, constants `C`, `C'` and an
exponent `k` such that for all `d ≥ 1`, `n ≥ 1`, `m`, `M`, `δ ∈ (0, 1)`, every `A ∈ ℚ^{m × d}` and `b ∈ ℚ^m` whose
entries have numerators and denominators at most `M` in absolute value, whose polytope `K = {x : A x ≤ b}` contains a
closed ball of radius `1` and has diameter at most `n`, every strategy `σ ∈ Strats K n` and every noise law `ν` with
`NoiseOK ν`, with `L = log (2 d n / δ)`, the run of `P` from `initPoly d n m δ A b` satisfies:

* on every run (every Gaussian stream and every noise sequence) the first play comes within
  `C' (d m L log (2 M))^k` steps, every later round within `C' (d m L)^k` steps of the round before, and every point
  played in a round `t < n` is in `K`;
* the outer measure of the runs whose regret exceeds `C d^{3/2} n^{1/2} L^5` is at most `δ`, the regret being taken
  against the losses that the strategy chose on that run.

The hypotheses have no instance for `n < 2`, nor for `n = 2` when `d ≥ 2`: two points of a unit ball lie at distance
`2`, and a polytope in dimension `d ≥ 2` is not a ball, so it has two points more than `2` apart. This is faithful to
Bubeck, Eldan and Lee, whose normalisation puts the horizon above the diameter of `K`; the claim is about large horizons.

`n` enters the cost only inside `L`, and `M` only inside the logarithm of the first bound; `d` and `m` enter
polynomially. The regret bound has the shape of `TheoremConj1Upper`'s. In their letters (`n` their dimension, `T` their
horizon; here `d` and `n`): for `m` at most a power of the dimension, `M` at most a power of the horizon and
`δ = 1/(2T)`, every step, the first included, takes a number of machine steps polynomial in `n` and `log T`, and the
upper expectation of the regret (its expectation when it is measurable) is at most
`C n^{3/2} T^{1/2} log^5 (4 n T^2) + 1/2` (the regret is at most `T` on every run, the plays being in `K` and the
losses in `[0, 1]` on `K`).

## The input (`polytope`, `HeightLE`, `initPoly`)

* `polytope A b = {x ∈ ℝ^d : ∀ i, Σ_j A i j x_j ≤ b i}`, the polytope of Bubeck, Eldan and Lee ("K is a polytope described by poly(n)
  constraints whose coefficients are rational numbers with absolute values of numerators and denominators bounded by
  poly(T)").
* `HeightLE A b M`: every entry of `A` and of `b`, in lowest terms (`Rat.num`, `Rat.den`), has a numerator and a
  denominator of absolute value at most `M`. `M` is bound by this hypothesis alone: the program is not told `M`, and the
  claim holds for every `M` that bounds the heights, so the first bound may be read at the least one.
* Their two normalisations are hypotheses: `K` contains a closed ball of radius `1` (centred anywhere), and any
  two points of `K` are at distance at most `n` ("for normalization purposes we assume that the diameter of K is at most
  T"). The second is written with `dist`, since `Metric.diam` is `0` on an unbounded set; it makes `K` bounded.
* `initPoly d n m δ A b`, the initial state: `N 0 = d`, `N 1 = n`, `N 2 = m`, every other natural register `0`;
  `M 2 = δ`; for each row `i < m` the cells `3 + (d + 1) i + j`, `j < d`, hold `A i j` and the cell
  `3 + (d + 1) i + d` holds `b i`, as real numbers; every other cell `0`. The registers `0`, `1` and the cell `2` are
  those of `init` (StatementPoly.lean); the cells `0` and `1`, which hold `r₀` and `R₀` there, are `0`: no radius is
  given. The data cannot sit in the natural registers: a program names finitely many of them, while the data has
  `m (d + 1)` entries; the real memory is addressed indirectly.
* A rational held in a cell does not show its numerator to the machine (it has no floor), so the heights reach the
  program only through the geometry they force (the polytope lies in the ball of radius `(d m M^{2(d+1)})^{d+1}` about `0`,
  Lemma 8.12 of the paper), which the program meets by trying radii `2^{2^j}`, `j = 0, 1, ...`.

## The model (`QueryFree`)

The program is a program of the frozen machine with no `query` instruction (`QueryFree`). The field `K` of the world
is read by `query` only, so it is inert for such a program: the polytope reaches the program through `initPoly` alone
(`runAd_K_irrel` in the sanity module). Without `QueryFree` a program could test membership in one step, through the
oracle, instead of reading the constraints (a centre search and a translation would still be needed to run the program
of `TheoremConj1Upper`, which is given a ball about `0` and the radii `r₀`, `R₀`). The remaining primitives are those of StatementPoly.lean: unit-cost exact real arithmetic
with rational constants, `sqrt`, `exp`, `log`, the comparison of reals, natural counters with `+`, truncated `-` and
comparison, the cast of a natural to a real, exact Gaussian draws, and the two spectral functions (the clamp of the
eigenvalues to an interval and the indicator of a half line), each one step. The docstring of StatementPoly.lean says
what this model leaves out (the bit cost of exact real arithmetic, the cost of exact eigenprojections). Not claimed: the
bit model; the second sentence of the conjecture (StatementConj1Lower.lean); an adversary beyond the class `Strats`
(StatementConj1.lean says which, and why a deterministic strategy covers a randomised one).

## Junk values

Those of `TheoremConj1Upper`, and these. `HeightLE` is about the entries in lowest terms (`Rat` is normalised), so
`Rat.den ≥ 1` gives `M ≥ 1` as soon as `m ≥ 1`, and `m ≥ 1` follows from the hypotheses for `d ≥ 1` (with no row the
polytope is the whole space, of unbounded diameter); so `log (2 M) ≥ log 2 > 0`, and the first bound is not `0` by a
junk `log 0`. `initPoly` reads the row `(c - 3) / (d + 1)` and the column `(c - 3) % (d + 1)` of the cell `c` only when
`3 ≤ c` and the row is below `m`, so the truncated subtraction and the division by `d + 1 ≥ 1` are exact there. The
regret and the plays-in-`K` clause are on `polytope A b`, the set of the strategy's class.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace RealRAM

/-- The polytope `{x : ∀ i, Σ_j A i j x_j ≤ b i}` of `ℝ^d`. -/
def polytope {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Set (E d) :=
  {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)}

/-- Every entry of `A` and of `b`, in lowest terms, has a numerator and a denominator of absolute value at most `M`. -/
def HeightLE {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (M : ℕ) : Prop :=
  (∀ i j, (A i j).num.natAbs ≤ M ∧ (A i j).den ≤ M) ∧ ∀ i, (b i).num.natAbs ≤ M ∧ (b i).den ≤ M

/-- The initial state on a polytope: `N 0 = d`, `N 1 = n`, `N 2 = m`, `M 2 = δ`, and the row
`(A i 0, ..., A i (d - 1), b i)` in the cells `3 + (d + 1) i, ..., 3 + (d + 1) i + d`; every other register and cell
`0`. -/
noncomputable def initPoly (d n m : ℕ) (δ : ℝ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : State d where
  pc := 0
  nreg := fun i => if i = 0 then d else if i = 1 then n else if i = 2 then m else 0
  mem := fun c =>
    if c = 2 then δ
    else if h : 3 ≤ c ∧ (c - 3) / (d + 1) < m then
      (if hj : (c - 3) % (d + 1) < d then ((A ⟨(c - 3) / (d + 1), h.2⟩ ⟨(c - 3) % (d + 1), hj⟩ : ℚ) : ℝ)
       else ((b ⟨(c - 3) / (d + 1), h.2⟩ : ℚ) : ℝ))
    else 0
  draws := 0
  rounds := 0
  pts := fun _ => 0

/-- The program has no membership query. -/
def QueryFree (P : List Instr) : Prop := ∀ dst src : ℕ, Instr.query dst src ∉ P

end RealRAM

open RealRAM in
/-- The upper half of Conjecture 1 of Bubeck, Eldan and Lee on their polytopes (Theorem 1.3 of the paper): a single
real-RAM program with Gaussian draws and no membership oracle, which reads the dimension, the horizon, the number
of constraints, `δ` and the rational constraints, and is told nothing else, with regret
`C d^{3/2} n^{1/2} log^5 (2 d n / δ)` with probability at least `1 - δ` against every strategy of the class on every
polytope that contains a unit ball and has diameter at most `n`, every point played in the polytope, and a
number of steps per round polynomial in `d`, `m` and `log (2 d n / δ)`, the first round also in `log (2 M)`. -/
def TheoremConj1UpperPoly : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ), QueryFree P ∧
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), HeightLE A b M →
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) →
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) →
    ∀ σ ∈ Strats (polytope A b) n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ,
        CostOKAd P ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m δ A b) n
            (C' * ((d : ℝ) * m * Real.log (2 * d * n / δ) * Real.log (2 * M)) ^ k)
            (C' * ((d : ℝ) * m * Real.log (2 * d * n / δ)) ^ k) ∧
          ∀ t < n, playedAd P ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m δ A b) t ∈ polytope A b) ∧
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts (polytope A b)
                (lossAd σ ω.2 (playedAd P ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)))
                (playedAd P ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)) n} ≤
        ENNReal.ofReal δ

end AdversarialBco
