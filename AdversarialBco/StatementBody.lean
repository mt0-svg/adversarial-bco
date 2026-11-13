/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The standard Gaussian density and its upper tail

`phi` is the standard Gaussian density on `ℝ` and `Qtail t = ∫_t^∞ phi` its upper tail, which the Gaussian estimates
of the proofs use. The file imports only Mathlib.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.BodySpec

/-- The standard Gaussian density on `ℝ`. -/
noncomputable def phi (t : ℝ) : ℝ := Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- The upper tail `Q t = ∫_t^∞ phi` of the standard Gaussian law. -/
noncomputable def Qtail (t : ℝ) : ℝ := ∫ s in Set.Ioi t, phi s

end AdversarialBco.BodySpec
