/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import AdversarialBco.Statement

@[expose] public section

/-!
# The frozen statement of Corollary 8.6 (POLY), the membership-oracle form

A polynomial-time learner for adversarial
bandit convex optimisation on a convex body given by a membership oracle: regret `C d^{3/2} n^{1/2} log^5 (2 d n / δ)`
with probability at least `1 - δ` against every oblivious sequence of convex losses `K → [0, 1]` with noisy feedback,
and on every run a number of primitive steps per round polynomial in `d`, `n` and `log (1/δ)`, independent of
`R₀/r₀` after the first round.

## The machine (`RealRAM`)

The learner is one finite program `P : List Instr`, the same for every `d`, `n`, `K`: a machine of Blum, Shub and
Smale with rational constants only, extended by `sqrt`, `exp`, `log` and two spectral functions, with a membership
oracle, a Gaussian source and a play instruction. Each executed instruction is one step; the cost of a round is the
number of steps between two plays.

* State: a program counter, natural registers `N : ℕ → ℕ`, a real memory `M : ℕ → ℝ`, the number of Gaussian draws
  used, the number of rounds played and the points played. Real operands are addressed indirectly: operand `i`
  denotes the cell `M (N i)`. A point of `ℝ^d` is the block `M (a), ..., M (a + d - 1)`; a `d × d` matrix is the
  block `M (a + d i + j)`.
* Instructions: rational constants; `+ - × /` on reals; `sqrt`, `exp`, `log`; the jump on `<` between reals;
  natural constants, `+` and truncated `-` on naturals, the jump on `<` between naturals; the cast of a natural to a
  real; the unconditional jump; a spectral function of a symmetric matrix (below); one membership query; one draw
  from the Gaussian stream; one play.
* Inputs: `N 0 = d`, `N 1 = n`, `M 0 = r₀`, `M 1 = R₀`, `M 2 = δ`, every other cell `0`. The program halts when the
  counter leaves the code; a halted state does not change.
* `query dst src`: `M (N dst) := 1` if the point at `N src` is in `K`, else `0`.
* `gauss dst`: `M (N dst) := g_k`, the next unused term of the Gaussian stream.
* `play dst src`: the point `x` at `N src` is played in round `t` (the number of rounds played so far), and the
  observation `f_t x + ε_t` is written to `M (N dst)`.
* `spec s dst src a b`: the `d × d` block at `N dst` receives `φ(S)`, `S` the symmetric part of the block at `N src`
  and `φ` applied to its eigenvalues (`cfc`), with `φ = clamp to [M (N a), M (N b)]` (the projection of Procedure
  PG) or `φ = 1_{(M (N a), ∞)}` (a spectral projection). Each is a
  function of the matrix, so no choice of eigenvectors enters the semantics.

Choices of the model.

* One program for all inputs, finite code, rational constants only: a family of programs indexed by `(d, n)`, or real
  constants in the code, would carry advice; a family of decision trees reads `k` bits of the history in depth `k`,
  so it computes any function of what it has read at no cost, and its depth measures query complexity only.
* No conversion from reals to naturals (no floor) and no multiplication or division on naturals: unit-cost floor or
  unit-cost multiplication with bit extraction makes a RAM decide PSPACE-hard problems in polynomially many steps
  (Hartmanis and Simon; Schönhage).
* The residual of the model, which the steps do not measure: unit-cost real arithmetic is not known to be
  polynomially simulable by a Turing machine (with `+ - × / <` and rational constants it decides PosSLP in linear
  time, and its polynomial-time Boolean class is `P^PosSLP`: Allender, Bürgisser, Kjeldgaard-Pedersen and Miltersen,
  2009); with `exp`, the sign of an exp-log constant is known to be decidable only under Schanuel's conjecture
  (Macintyre and Wilkie); and `spec` gives exact eigenprojections at unit cost, whose true arithmetic cost is about
  `d^3`. None of these is known to run an exponential-work learner in polynomially many steps.
* A free monad over the same primitives (a program `prim p (fun r => ...)` with Lean functions as continuations) is
  not used: the continuations would compute any function of the values read at no cost.
* A uniform draw is not a primitive: `exp (-(g₁² + g₂²)/2)` is uniform on `(0, 1)` for two Gaussian draws.
* The eigendecomposition is not a primitive: its eigenvectors are not a function of the matrix, so its semantics
  would range over all eigensolvers and would have to ask them to be measurable, with the existence of a measurable
  one as a proof obligation of non-vacuity. The two spectral functions above are what the learners use.

## The game

* `K` compact convex with `closedBall 0 r₀ ⊆ K ⊆ closedBall 0 R₀`, `0 < r₀ ≤ R₀`, accessed only through `query`.
* The losses: `f ∈ Advs K n`, convex on `K` with values in `[0, 1]` on `K` (Statement.lean), fixed in advance.
* The noise: a sequence `ε : ℕ → ℝ` with law `ν`, independent of the Gaussian stream, such that for every `t`,
  conditionally on `ε_0, ..., ε_{t-1}`, `ε_t` has mean `0` and `E exp(ε_t²) ≤ 2` (`NoiseOK`). The noiseless game is
  `ν = dirac 0`. Since `ν` is independent of the stream, this is the hypothesis (N)
  for an oblivious adversary.
* The probability space: the Gaussian stream (`Measure.infinitePi` of `gaussianReal 0 1`) times `ν`.
* Regret: `Σ_{t < n} f_t(X_t) - inf_{x ∈ K} Σ_{t < n} f_t(x)`, `X_t` the point of round `t` (`played`).

## The statement (`TheoremPoly32O`)

There are a program `P`, constants `C`, `C'` and an exponent `k` such that for all `d ≥ 1`, `n ≥ 1`, `r₀`, `R₀`,
`δ ∈ (0, 1)`, `K`, `f` and `ν` as above, with `L = log (2 d n / δ)`:

* on every run (every Gaussian stream and every noise sequence) the first play comes within
  `C' (d n L (2 + log (R₀/r₀)))^k` steps (the positioning, Procedure PG, and the first round), every later round
  within `C' (d n L)^k` steps, and every point played is in `K`;
* the outer measure of the runs with regret above `C d^{3/2} n^{1/2} L^5` is at most `δ`.

Junk values. `x / 0 = 0`, `sqrt x = 0` for `x < 0` and `log x = log |x|`, `log 0 = 0` are total functions the program
can compute with one comparison more, so they give it nothing. `played` is `0` for a round that never comes, but the
cost clause makes every round `t < n` come on every run. The event of the regret clause may fail to be measurable (a
convex loss can be non-measurable on the boundary of `K`); the measure of a set is its outer measure, so the clause
asks for a measurable superset of measure at most `δ`, the strong reading. `condExp` is `0` for a non-integrable
function; `NoiseOK` asks `exp (ε_t²)` to be integrable, which gives `ε_t` integrable, and the σ-algebra of the past is
a sub-σ-algebra of the product one, so neither junk case occurs. `L > 0` since `2 d n / δ > 2`. `log (R₀/r₀) ≥ 0`. A
negative `C'` gives the bound `0` and the cost clause fails at the first play, so it cannot help. The `sInf` is over
the nonempty set of values on `K`, bounded below by `0`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace RealRAM

/-- Binary real operations. -/
inductive Op2
  | add
  | sub
  | mul
  | div

/-- Unary real operations. -/
inductive Op1
  | sqrt
  | exp
  | log

/-- Spectral functions: the clamp to `[a, b]`, and the indicator of `(a, ∞)`. -/
inductive Spec
  | clamp
  | step

/-- The instructions. Real operands are natural register indices `i`, denoting the cell `M (N i)`. -/
inductive Instr
  /-- `M (N dst) := q`. -/
  | rconst (dst : ℕ) (q : ℚ)
  /-- `M (N dst) := M (N a) o M (N b)`. -/
  | op2 (o : Op2) (dst a b : ℕ)
  /-- `M (N dst) := o (M (N a))`. -/
  | op1 (o : Op1) (dst a : ℕ)
  /-- Jump to `target` if `M (N a) < M (N b)`. -/
  | rjlt (a b target : ℕ)
  /-- `N dst := c`. -/
  | nconst (dst c : ℕ)
  /-- `N dst := N a + N b`. -/
  | nadd (dst a b : ℕ)
  /-- `N dst := N a - N b` (truncated). -/
  | nsub (dst a b : ℕ)
  /-- Jump to `target` if `N a < N b`. -/
  | njlt (a b target : ℕ)
  /-- `M (N dst) := N a`. -/
  | ncast (dst a : ℕ)
  /-- Jump to `target`. -/
  | jmp (target : ℕ)
  /-- The `d × d` block at `N dst` receives the spectral function `s` with parameters `M (N a)`, `M (N b)` of the
  symmetric part of the block at `N src`. -/
  | spec (s : Spec) (dst src a b : ℕ)
  /-- `M (N dst) := 1` if the point at `N src` is in `K`, else `0`. -/
  | query (dst src : ℕ)
  /-- `M (N dst) :=` the next unused term of the Gaussian stream. -/
  | gauss (dst : ℕ)
  /-- Play the point at `N src`; `M (N dst) :=` the observation. -/
  | play (dst src : ℕ)

/-- The value of a binary operation (`x / 0 = 0`). -/
noncomputable def Op2.eval : Op2 → ℝ → ℝ → ℝ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y

/-- The value of a unary operation (`sqrt x = 0` for `x < 0`, `log x = log |x|`). -/
noncomputable def Op1.eval : Op1 → ℝ → ℝ
  | .sqrt, x => Real.sqrt x
  | .exp, x => Real.exp x
  | .log, x => Real.log x

/-- The function of the eigenvalues of a spectral instruction, with parameters `a`, `b`. -/
noncomputable def Spec.fn : Spec → ℝ → ℝ → ℝ → ℝ
  | .clamp, a, b, x => max a (min b x)
  | .step, a, _, x => if a < x then 1 else 0

/-- The state of the machine. -/
structure State (d : ℕ) where
  /-- The program counter. -/
  pc : ℕ
  /-- The natural registers. -/
  nreg : ℕ → ℕ
  /-- The real memory. -/
  mem : ℕ → ℝ
  /-- The number of Gaussian draws made. -/
  draws : ℕ
  /-- The number of rounds played. -/
  rounds : ℕ
  /-- `pts t`: the point played in round `t`, for `t < rounds`. -/
  pts : ℕ → E d

/-- What the program interacts with: the body (through `query`), the losses and the noise (through `play`), and the
Gaussian stream (through `gauss`). -/
structure World (d : ℕ) where
  /-- The body. -/
  K : Set (E d)
  /-- The losses. -/
  f : ℕ → E d → ℝ
  /-- The noise of the observations. -/
  noise : ℕ → ℝ
  /-- The Gaussian stream. -/
  gs : ℕ → ℝ

/-- The point stored at `a, ..., a + d - 1`. -/
def vecAt {d : ℕ} (m : ℕ → ℝ) (a : ℕ) : E d :=
  WithLp.toLp 2 fun i : Fin d => m (a + i)

/-- The `d × d` matrix stored at `a + d i + j`. -/
def matAt (d : ℕ) (m : ℕ → ℝ) (a : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => m (a + d * i + j)

/-- The entry `(i, j)` of a matrix, `0` outside the range. -/
def matEntry {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : ℕ) : ℝ :=
  if h : i < d ∧ j < d then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The memory `m` with the matrix `A` written at `a + d i + j`. -/
def writeMat {d : ℕ} (m : ℕ → ℝ) (a : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) : ℕ → ℝ :=
  fun k => if a ≤ k ∧ k < a + d * d then matEntry A ((k - a) / d) ((k - a) % d) else m k

/-- The symmetric part `(A + Aᵀ)/2`. -/
noncomputable def symPart {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (A + A.transpose)

open Classical in
/-- One step of the machine. -/
noncomputable def step {d : ℕ} (P : List Instr) (w : World d) (s : State d) : State d :=
  match P[s.pc]? with
  | none => s
  | some ins =>
    match ins with
    | .rconst dst q => { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) q }
    | .op2 o dst a b =>
      { s with pc := s.pc + 1,
               mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a)) (s.mem (s.nreg b))) }
    | .op1 o dst a =>
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a))) }
    | .rjlt a b target =>
      if s.mem (s.nreg a) < s.mem (s.nreg b) then { s with pc := target } else { s with pc := s.pc + 1 }
    | .nconst dst c => { s with pc := s.pc + 1, nreg := Function.update s.nreg dst c }
    | .nadd dst a b => { s with pc := s.pc + 1, nreg := Function.update s.nreg dst (s.nreg a + s.nreg b) }
    | .nsub dst a b => { s with pc := s.pc + 1, nreg := Function.update s.nreg dst (s.nreg a - s.nreg b) }
    | .njlt a b target =>
      if s.nreg a < s.nreg b then { s with pc := target } else { s with pc := s.pc + 1 }
    | .ncast dst a => { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (s.nreg a : ℝ) }
    | .jmp target => { s with pc := target }
    | .spec sp dst src a b =>
      { s with pc := s.pc + 1,
               mem := writeMat s.mem (s.nreg dst)
                 (cfc (sp.fn (s.mem (s.nreg a)) (s.mem (s.nreg b))) (symPart (matAt d s.mem (s.nreg src)))) }
    | .query dst src =>
      { s with pc := s.pc + 1,
               mem := Function.update s.mem (s.nreg dst) (if vecAt s.mem (s.nreg src) ∈ w.K then 1 else 0) }
    | .gauss dst =>
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (w.gs s.draws), draws := s.draws + 1 }
    | .play dst src =>
      { s with pc := s.pc + 1,
               mem := Function.update s.mem (s.nreg dst)
                 (w.f s.rounds (vecAt s.mem (s.nreg src)) + w.noise s.rounds),
               rounds := s.rounds + 1,
               pts := Function.update s.pts s.rounds (vecAt s.mem (s.nreg src)) }

/-- The initial state on the inputs `d, n, r₀, R₀, δ`. -/
noncomputable def init (d n : ℕ) (r0 R0 δ : ℝ) : State d where
  pc := 0
  nreg := fun i => if i = 0 then d else if i = 1 then n else 0
  mem := fun i => if i = 0 then r0 else if i = 1 then R0 else if i = 2 then δ else 0
  draws := 0
  rounds := 0
  pts := fun _ => 0

/-- The state after `k` steps. -/
noncomputable def run {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) (k : ℕ) : State d :=
  (step P w)^[k] s0

open Classical in
/-- The point played in round `t` (`0` if that round never comes). -/
noncomputable def played {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) (t : ℕ) : E d :=
  if h : ∃ k, t < (run P w s0 k).rounds then (run P w s0 (Nat.find h)).pts t else 0

/-- The cost clause: the first play within `B0` steps, and every later round `t < n` within `B` steps of the step at
which round `t - 1` was played. -/
def CostOK {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) (n : ℕ) (B0 B : ℝ) : Prop :=
  1 ≤ (run P w s0 ⌈B0⌉₊).rounds ∧
    ∀ k t : ℕ, 1 ≤ t → t < n → (run P w s0 k).rounds = t → t + 1 ≤ (run P w s0 (k + ⌈B⌉₊)).rounds

/-- Regret of the points `x 0, ..., x (n - 1)` against the best fixed action of `K`. -/
noncomputable def regretPts {d : ℕ} (K : Set (E d)) (f : ℕ → E d → ℝ) (x : ℕ → E d) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, f t (x t) - sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K)

/-- The σ-algebra of the first `t` terms of the noise. -/
abbrev pastNoise (t : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun ε : ℕ → ℝ => fun i : Fin t => ε i) inferInstance

/-- The noise hypothesis: a probability law of the noise sequence under which, conditionally on the past noise,
`ε_t` has mean `0` and `E exp(ε_t²) ≤ 2`. -/
def NoiseOK (ν : Measure (ℕ → ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ t : ℕ,
    Integrable (fun ε : ℕ → ℝ => Real.exp (ε t ^ 2)) ν ∧
      ν[fun ε => ε t | pastNoise t] =ᵐ[ν] 0 ∧
      ν[fun ε => Real.exp (ε t ^ 2) | pastNoise t] ≤ᵐ[ν] fun _ => 2

/-- The Gaussian stream: independent standard Gaussian terms. -/
noncomputable def gaussStream : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

end RealRAM

open RealRAM in
/-- Corollary 8.6 (POLY): a single real-RAM program with a membership oracle and Gaussian draws, with regret
`C d^{3/2} n^{1/2} log^5 (2 d n / δ)` with probability at least `1 - δ`, every point played in `K`, and a number of
steps per round polynomial in `d`, `n`, `log (1/δ)`, the first round also in `log (R₀/r₀)`. -/
def TheoremPoly32O : Prop :=
  ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
    ∀ f ∈ Advs K n, ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (∀ gs noise : ℕ → ℝ,
        CostOK P ⟨K, f, noise, gs⟩ (init d n r0 R0 δ) n
            (C' * ((d : ℝ) * n * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k)
            (C' * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k) ∧
          ∀ t < n, played P ⟨K, f, noise, gs⟩ (init d n r0 R0 δ) t ∈ K) ∧
      (gaussStream.prod ν)
          {ω : (ℕ → ℝ) × (ℕ → ℝ) |
            C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
              regretPts K f (played P ⟨K, f, ω.2, ω.1⟩ (init d n r0 R0 δ)) n} ≤
        ENNReal.ofReal δ

end AdversarialBco
