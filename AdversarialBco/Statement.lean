/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# The frozen statement: Corollary 1.6

Adversarial bandit convex optimisation with an oblivious adversary and noiseless bandit feedback: the definitions of
the statement of Corollary 1.6 of the paper, in the form of its Section 11.1. The statement with a `sorry` proof is
`AdversarialBco/Challenge.lean`, which repeats these definitions.

* `E d = EuclideanSpace ℝ (Fin d)`. The action set `K ⊆ E d` is a convex body containing a unit ball: compact,
  convex, `closedBall c 1 ⊆ K` for some `c` (so `K` has nonempty interior).
* `AdmLoss K f`: `f` is convex on `K` with values in `[0, 1]` on `K` (values off `K` play no role).
* The adversary is oblivious: it fixes a whole sequence `f : ℕ → E d → ℝ` before the game, with `f t` admissible for
  every round `t < n` (`Advs K n`); the terms of index `≥ n` play no role.
* A learner (`IsLearner K pol`): a seed `ω` drawn from a probability measure `μ` on any measurable space `Ω`, and for
  each round `t` a jointly measurable map `pol t : Ω → (Fin t → ℝ) → E d` with values in `K`. In round `t` the
  learner plays `X_t = pol t ω (Y_0, ..., Y_{t-1})` and observes only `Y_t = f t X_t` (`obs`). This is the class
  of all randomised learners: the seed carries all the randomisation, and the learner remembers its own past actions
  since they are functions of `ω` and the past observations.
* Regret against the best fixed action: `Σ_{t < n} f t X_t - inf_{x ∈ K} Σ_{t < n} f t x` (`regret`); its
  expectation over the seed is `expReg`.
* `minimaxRegret K n`: the infimum over learners whose regret is integrable against every admissible sequence of
  the supremum over admissible sequences of the expected regret.
* `CorollaryADV`: there is an absolute constant `C` such that for every `d ≥ 1`, `n ≥ 2` and every convex body
  `K ⊆ E d` containing a unit ball, `minimaxRegret K n ≤ C d^{3/2} n^{1/2} (log (n diam K))^{3/2}`.

Junk values. A convex function on a compact convex set can be discontinuous, even non-measurable, at the boundary
(on the closed disc, `0` inside and the indicator of any subset of the circle on it), so the regret of a learner whose
actions have a continuous law on the boundary need not be measurable, and its Bochner integral would be the junk
value `0`. The infimum of `minimaxRegret` therefore runs over the learners whose regret is integrable against every
admissible sequence. This only removes learners, which can only raise the infimum: the statement is at least as
strong as the claim with any convention for those learners. The class is nonempty (a constant learner) and every
member has expected regret in `[0, n]` at the zero sequence and at most `n` everywhere, so the supremum is over a
nonempty set bounded above by `n` and the infimum over a nonempty set bounded below by `0`; neither takes the junk
value. The comparator `sInf` is over the nonempty set of values on `K`, bounded below by `0`. `Metric.diam K` is the
true diameter since `K` is bounded, and it is at least `2`, so `log (n diam K) ≥ log 4 > 0` and the real power is the
ordinary one.
-/

open MeasureTheory Real

namespace AdversarialBco

/-- The ambient space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A loss of the class: convex on `K`, with values in `[0, 1]` on `K`. -/
def AdmLoss {d : ℕ} (K : Set (E d)) (f : E d → ℝ) : Prop :=
  ConvexOn ℝ K f ∧ ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1

/-- The oblivious adversary's choices over `n` rounds: sequences whose first `n` terms are admissible. -/
def Advs {d : ℕ} (K : Set (E d)) (n : ℕ) : Set (ℕ → E d → ℝ) :=
  {f | ∀ t < n, AdmLoss K (f t)}

/-- Observations `Y_0, ..., Y_{t-1}` of a deterministic policy `pol` (the learner with its seed fixed) against the
sequence `f`: `Y_s = f s (pol s (Y_0, ..., Y_{s-1}))`. -/
def obs {d : ℕ} (f : ℕ → E d → ℝ) (pol : (t : ℕ) → (Fin t → ℝ) → E d) : (t : ℕ) → Fin t → ℝ
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => ℝ) (obs f pol t) (f t (pol t (obs f pol t)))

/-- Regret over the rounds `0, ..., n - 1` against the best fixed action of `K`. -/
noncomputable def regret {d : ℕ} (K : Set (E d)) (f : ℕ → E d → ℝ) (pol : (t : ℕ) → (Fin t → ℝ) → E d)
    (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, f t (pol t (obs f pol t)) - sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K)

/-- A learner on `K`: jointly measurable policies of the seed and the observations, with values in `K`. -/
def IsLearner {d : ℕ} (K : Set (E d)) {Ω : Type} [MeasurableSpace Ω] (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d) :
    Prop :=
  (∀ t, Measurable fun p : Ω × (Fin t → ℝ) => pol t p.1 p.2) ∧ ∀ t ω y, pol t ω y ∈ K

/-- Expected regret of the learner `(μ, pol)` against the sequence `f`. -/
noncomputable def expReg {d : ℕ} (K : Set (E d)) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d) (f : ℕ → E d → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, regret K f (fun t => pol t ω) n ∂μ

/-- The minimax regret over `n` rounds: infimum over the learners (with integrable regret against every admissible
sequence) of the supremum over admissible sequences of the expected regret. -/
noncomputable def minimaxRegret {d : ℕ} (K : Set (E d)) (n : ℕ) : ℝ :=
  sInf {r | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (pol : (t : ℕ) → Ω → (Fin t → ℝ) → E d), IsLearner K pol ∧
      (∀ f ∈ Advs K n, Integrable (fun ω => regret K f (fun t => pol t ω) n) μ) ∧
      r = sSup ((fun f => expReg K μ pol f n) '' Advs K n)}

/-- Corollary 1.6 of the paper, in the form of its Section 11.1. -/
def CorollaryADV : Prop :=
  ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (E d), IsCompact K → Convex ℝ K →
    (∃ c : E d, Metric.closedBall c 1 ⊆ K) →
      minimaxRegret K n ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * Metric.diam K) ^ (3 / 2 : ℝ)

end AdversarialBco
