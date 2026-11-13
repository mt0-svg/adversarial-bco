/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly

@[expose] public section

/-!
# The adversary against a strategy: definitions of the frozen statements

The adversary of the frozen statements is a strategy (`Strategy`, its class `Strats`), which chooses the loss of each
round from the transcript of the rounds before it (`obsAd`, `lossAd`).

A strategy is a function `σ t x o y`: the loss of round `t` at the point `y`, given the points `x 0, ..., x (t - 1)`
played and the observations `o 0, ..., o (t - 1)` received in the rounds before `t`. Against the points `x` and the
noise `ε`, the observations are rebuilt by the recursion `obsAd`,
`o u = σ u (x 0, ..., x (u - 1)) (o 0, ..., o (u - 1)) (x u) + ε_u`, and the loss of round `t` is
`lossAd σ ε x t = σ t (x 0, ..., x (t - 1)) (o 0, ..., o (t - 1))`: it reads the points of the earlier rounds only, so
the strategy is non-anticipating by construction, with no side condition.

* What it reads: the transcript of the game before round `t`, plays and observations. A fixed sequence is the strategy
  that reads nothing (`fun t _ _ => f t`). The game of Bubeck, Eldan and Lee (no noise, the loss of round `t` chosen
  with the knowledge of the plays before `t`) is a strategy that reads the plays only.
* What it does not read: the learner's random draws, neither those of round `t` nor those of the earlier rounds. An
  adversary that reads the current draw, or the current play, forces an expected regret `n/4` on every learner: here
  `σ` sees no draw, and the loss of round `t` is fixed by the earlier rounds before the point of round `t` exists.
* Deterministic: a strategy has no seed. A randomised adversary (a seed drawn independently of the game, and a
  strategy for each value of the seed) is a mixture of strategies.
* Measurability (`Strats`): for `t < n` and each point `y ∈ K`, the map `(x, o) ↦ σ t x o y` is measurable for the
  Borel σ-algebras. A constant strategy meets it whatever `f` is, so the fixed sequences need no measurability.
* Admissibility (`Strats`): for `t < n` every value `σ t x o` is an `AdmLoss K`, for every history, including the ones
  no run reaches. For the histories with a point outside `K` the requirement costs nothing: setting a strategy to `0`
  there changes no run whose points are in `K`, and keeps the measurability since `K` is closed.

Junk values: none in this file. The values of a strategy for `t ≥ n`, and off `K`, are never read by a regret over
`n` rounds on `K`.
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

end RealRAM

end AdversarialBco
