/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnified
public import AdversarialBco.StatementConj1BitHP
public import AdversarialBco.Unified.PolyRS
public import AdversarialBco.Unified.RunFacts
public import AdversarialBco.Unified.Sanity
public import AdversarialBco.Bit.Assembly
public import AdversarialBco.Bit.RegMeas
public import AdversarialBco.Bit.Transfer.XDriver
public import AdversarialBco.Bit.ApQ.FrameB

@[expose] public section

/-!
# UNI-POLY: the instance of Theorem U (`s0U`, `worldO`, `orcK`, `δK`)
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UniPoly

open BitRAM BitRAMO Unified
open RealRAM (Strategy lossAd regretPts polytope HeightLE)

variable {d : ℕ}

/-- The exact membership answer for the polytope. -/
noncomputable def orcK {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : (Fin d → ℚ) → ℕ → Bool :=
  fun y _ => @decide (toE y ∈ polytope A b) (Classical.dec _)

/-- The confidence handed to Theorem U. -/
def δK (n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)

/-- The input of Theorem U. -/
noncomputable def s0U (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : State d :=
  initU d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b)

/-- The oracle world of a bit world: the same losses and coins, no noise, the exact oracle. -/
noncomputable def worldO {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (w : World d) : WorldO d :=
  ⟨w.f, fun _ => 0, w.cs, orcK A b⟩

/-- The feedback of the bit state is in `[0, 1]`. -/
def FbOK (w : World d) (t : State d) : Prop := 0 ≤ feedback w t ∧ feedback w t ≤ 1

theorem worldO_toW {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (w : World d) : (worldO A b w).toW = w := by
  cases w; simp [WorldO.toW, worldO]

end AdversarialBco.UniPoly
