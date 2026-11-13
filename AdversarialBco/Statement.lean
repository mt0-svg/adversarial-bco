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
# The ambient space and the class of losses

The two definitions that the statement files build on, repeated verbatim by the challenges.

* `E d = EuclideanSpace ℝ (Fin d)`, the ambient space `ℝ^d`.
* `AdmLoss K f`: `f` is convex on `K` with values in `[0, 1]` on `K` (values off `K` play no role).
-/

open MeasureTheory Real

namespace AdversarialBco

/-- The ambient space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A loss of the class: convex on `K`, with values in `[0, 1]` on `K`. -/
def AdmLoss {d : ℕ} (K : Set (E d)) (f : E d → ℝ) : Prop :=
  ConvexOn ℝ K f ∧ ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1

end AdversarialBco
