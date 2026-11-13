/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1

@[expose] public section

/-!
# The lower bound: the learners, the run, the regret and the adversaries

Definitions of the frozen lower bound on a polytope (StatementConj1LowerPoly.lean). The game is that of
StatementConj1.lean: the strategy type `Strategy` and its class `Strats`, the observations `obsAd` and the losses
`lossAd` are reused unchanged, with the regret `regretPts` of StatementPoly.lean, in the noiseless game. What is new
is the learner side, which quantifies over every randomised learner, and the sub-class of strategies that the lower
bound produces.

## The learner (`Learner`, `IsLearnerAd`)

A learner is a seed `ω`, drawn from a probability measure `μ` on any measurable space `Ω`, and a play rule
`pol t ω x o`: the point played in round `t`, given the seed, the points `x 0, ..., x (t - 1)` it played and the
observations `o 0, ..., o (t - 1)` it received. This is every randomised algorithm, with no computational restriction:
the seed carries all the randomisation, and the rule is any function. Two conditions:

* the play is in `K` (the player selects `x_t ∈ K`);
* the rule is jointly measurable in `(ω, x, o)` for the Borel σ-algebras: the hypothesis
  that makes the regret a random variable and which the proof uses
  (the law of the hidden minimiser given the seed and the history, the paper's posterior lemma). Both conditions bind
  the rounds
  `t < n` only: the rule after round `n` is never read.

The learner reads its own past points. A rule reading the observations only is a rule
of this form, and a rule of this form gives the same run as one reading the observations only (its points are
measurable functions of the seed and the observations), so the two classes have the same runs; the form here is the
transcript of the game. The real RAM of StatementPoly.lean is not mentioned: a program whose plays are measurable
functions of its Gaussian stream and its observations would be a learner of this class with `Ω = ℕ → ℝ` and
`μ = gaussStream`; that measurability is not proved here, and the claim does not need it.

## The run (`transcript`, `plays`)

Against a strategy `σ`, with the noise `ε`, the transcript of the rounds `0, ..., t - 1` is built round by round: in
round `t` the learner plays `y = p t x o` from the transcript `(x, o)` so far, and observes `σ t x o y + ε t`, the loss
that `σ` chose from the transcript before round `t`, read at `y`. `plays σ ε p t` is the point of round `t`. The
observations of the transcript are those of `obsAd σ ε (plays σ ε p)` and its losses are `lossAd σ ε (plays σ ε p)`
(`transcript_snd`, `lossAd_plays` in AdversarialBco/Conj1Lower/Sanity.lean), so the regret below is `regretPts`
(StatementPoly.lean) against the losses that produced the feedback. The statement uses the noise `0`: the learner
sees `f_t(x_t)`, the game of Bubeck, Eldan and Lee, with the noise law `dirac 0`. The device of the proof (the
Gaussian game of the paper's section on the strategy and the genie) is not part of the statement; the bounded
perturbation of the proof is in the losses, chosen by the adversary, and fixed with its other draws when the
strategy is made deterministic.

## The adversary (`StratsLip`)

`StratsLip K n` is the part of `Strats K n` (the class of StatementConj1.lean: for `t < n` and every history, a
convex loss `K → [0, 1]`, measurable in the history at each point of `K`) whose losses, for `t < n` and every history,

* read the past points only and not the past observations, as in the game of Bubeck, Eldan and Lee (the loss of round
  `t` is chosen knowing the plays before `t`), and
* are `1/4`-Lipschitz on `K` (the losses of the proof are even `σ`-Lipschitz with `σ = 1/(8 (6 log n)^{1/2})`).

Both restrict the strategy, which is existential, so both strengthen the claim. The strategy is deterministic and
non-anticipating: the loss of round `t` is `σ t x o`, a function of the transcript before round `t`. The order of
quantifiers is that of a lower bound: the strategy comes after the learner, so it may depend on `d`, `n`, `μ` and the
rule `pol`; the seed `ω` reaches it only through the points played.
The proof gives more: one randomised strategy, the same for every learner; the paper's proof of the lower bound turns it
into a
deterministic strategy for each learner, the form stated here, which keeps the adversaries in the class `Strats`.

## The regret and its mean (`regretAd`)

`regretAd K σ p n = regretPts K (lossAd σ 0 (plays σ 0 p)) (plays σ 0 p) n`: the realised regret
`Σ_{t < n} f_t(x_t) - inf_{y ∈ K} Σ_{t < n} f_t(y)` against the losses `f_t` that `σ` chose on that run. The claim
asks that it be integrable in the seed, and bounds its Bochner integral from below.

## Junk values

`Real.log d > 0` since `d ≥ 4·10^6`, and `(d : ℝ) ^ (3/2 : ℝ)` is the ordinary power since `d > 0`. The Bochner
integral of a non-integrable function is `0`; the claim asserts integrability, so the integral is the mean. The
conjunct costs the claim nothing: for every strategy of `StratsLip K n` and every learner of the class the regret is
integrable. The argument, which is not formalized: the transcript is measurable in the seed (by induction on the
rounds), the loss at the point played is measurable because a strategy of the class is measurable in the history at
each point of `K` and Lipschitz on `K` while the points played are in `K`, the comparator `sInf` over `K` of a function
continuous on `K` is an infimum over a countable dense subset, and `|regret| ≤ n` since the losses lie in `[0, 1]` on
`K`. The `sInf` of `regretPts` is over the values of `Σ_{t < n} f_t` on `K`, a nonempty set bounded below by `0`
for a strategy of the class. The regret reads the losses at the points played and on `K` only, and the points of the
rounds `t < n` are in `K`, so the values of a strategy off `K` and for `t ≥ n` are never read. `plays` is defined for
every rule and every strategy, and the losses of the learner's rounds `t < n` are admissible on every history, so no
junk enters the run.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace Lower

open RealRAM

/-- A deterministic play rule: `p t x o` is the point played in round `t`, given the points `x` played and the
observations `o` received in the rounds `0, ..., t - 1`. A learner with its seed fixed is one. -/
abbrev Policy (d : ℕ) : Type := (t : ℕ) → (Fin t → E d) → (Fin t → ℝ) → E d

/-- A randomised learner with seeds in `Ω`: `pol t ω x o` is the point played in round `t` with the seed `ω`, given
the points `x` played and the observations `o` received in the rounds `0, ..., t - 1`. -/
abbrev Learner (Ω : Type) (d : ℕ) : Type := (t : ℕ) → Ω → (Fin t → E d) → (Fin t → ℝ) → E d

/-- The learners of the class over `n` rounds: for `t < n`, the play is a jointly measurable function of the seed,
the past points and the past observations, with values in `K`. -/
def IsLearnerAd {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (K : Set (E d)) (n : ℕ) (pol : Learner Ω d) : Prop :=
  ∀ t < n, (Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) ∧
    ∀ ω x o, pol t ω x o ∈ K

/-- The transcript of the rounds `0, ..., t - 1` of the play rule `p` against the strategy `σ` with the noise `ε`: the
points played and the observations received. In round `t` the point is `y = p t x o`, from the transcript `(x, o)`
so far, and the observation is `σ t x o y + ε t`. -/
def transcript {d : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) : (t : ℕ) → (Fin t → E d) × (Fin t → ℝ)
  | 0 => (Fin.elim0, Fin.elim0)
  | t + 1 =>
    let h := transcript σ ε p t
    let y := p t h.1 h.2
    (Fin.snoc (α := fun _ => E d) h.1 y, Fin.snoc (α := fun _ => ℝ) h.2 (σ t h.1 h.2 y + ε t))

/-- The point played in round `t` by the play rule `p` against the strategy `σ` with the noise `ε`. -/
def plays {d : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) : E d :=
  p t (transcript σ ε p t).1 (transcript σ ε p t).2

/-- The regret over `n` rounds of the play rule `p` against the strategy `σ` in the noiseless game, against the losses
that `σ` chose on that run: `regretPts` of the losses `lossAd` with the noise `0`. -/
noncomputable def regretAd {d : ℕ} (K : Set (E d)) (σ : Strategy d) (p : Policy d) (n : ℕ) : ℝ :=
  regretPts K (lossAd σ (fun _ => 0) (plays σ (fun _ => 0) p)) (plays σ (fun _ => 0) p) n

/-- The strategies of the lower bound over `n` rounds: those of `Strats K n` whose loss, for `t < n` and every
history, reads the past points only and is `1/4`-Lipschitz on `K`. -/
def StratsLip {d : ℕ} (K : Set (E d)) (n : ℕ) : Set (Strategy d) :=
  {σ | σ ∈ Strats K n ∧
    ∀ t < n, ∀ (x : Fin t → E d) (o o' : Fin t → ℝ), σ t x o = σ t x o' ∧
      ∀ y ∈ K, ∀ z ∈ K, |σ t x o y - σ t x o z| ≤ dist y z / 4}

end Lower

end AdversarialBco
