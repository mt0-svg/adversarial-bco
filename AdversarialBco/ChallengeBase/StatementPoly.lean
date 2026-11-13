/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenges, first module, importing Mathlib only: the definitions `E`, `AdmLoss` of
-- AdversarialBco/Statement.lean and AdversarialBco/StatementPoly.lean verbatim (code/formal-proof/challenges.sh).
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure

@[expose] public section

section

open MeasureTheory Real

namespace AdversarialBco

/-- The ambient space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A loss of the class: convex on `K`, with values in `[0, 1]` on `K`. -/
def AdmLoss {d : ℕ} (K : Set (E d)) (f : E d → ℝ) : Prop :=
  ConvexOn ℝ K f ∧ ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1

end AdversarialBco

end

/-!
# Machine data, the regret of the points played, the noise and the Gaussian stream

Definitions that the later statement files and the proofs reuse.

* `RealRAM.Op2`, `Op1` and `Spec`, with their values `Op2.eval`, `Op1.eval` and `Spec.fn`: the operations of a
  machine of Blum, Shub and Smale extended by `sqrt`, `exp`, `log` and two spectral functions (the clamp to `[a, b]`
  and the indicator of `(a, ∞)`, applied to the eigenvalues of a symmetric matrix).
* `State d`: a program counter, natural registers `N : ℕ → ℕ`, a real memory `M : ℕ → ℝ`, the number of Gaussian
  draws used, the number of rounds played and the points played. `World d`: the body, the losses, the noise and the
  Gaussian stream.
* The memory layout: a point of `ℝ^d` is the block `M a, ..., M (a + d - 1)` (`vecAt`); a `d × d` matrix is the
  block `M (a + d i + j)` (`matAt`, `matEntry`, `writeMat`); `symPart A = (A + Aᵀ)/2`.
* `regretPts K f x n = Σ_{t < n} f_t(x_t) - inf_{y ∈ K} Σ_{t < n} f_t(y)`, the regret of the points `x`.
* `NoiseOK ν`: `ν` is a probability law of the noise sequence `ε` under which, for every `t`, conditionally on
  `ε_0, ..., ε_{t-1}` (`pastNoise t`), `ε_t` has mean `0` and `E exp(ε_t²) ≤ 2`.
* `gaussStream`: independent standard Gaussian terms (`Measure.infinitePi` of `gaussianReal 0 1`).

Junk values. `x / 0 = 0`, `sqrt x = 0` for `x < 0` and `log x = log |x|` in `Op2.eval` and `Op1.eval`. `condExp` is
`0` for a non-integrable function; `NoiseOK` asks `exp (ε_t²)` to be integrable, which gives `ε_t` integrable, and the
σ-algebra of the past is a sub-σ-algebra of the product one, so neither junk case occurs. For a nonempty `K` and
losses with values in `[0, 1]` on `K`, the `sInf` of `regretPts` is over a nonempty set bounded below by `0`.
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

/-- The world of a run: the body, the losses, the noise of the observations and the Gaussian stream. -/
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

end AdversarialBco
