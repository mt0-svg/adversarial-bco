/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLPure
public import AdversarialBco.Bit.Assembly

@[expose] public section

/-!
# The objective of BL's call

`CallQ.obj`: the objective `yᵀPy/2 - f·y` of a call of BL's class (`CallQ`, Bit/BLPure.lean).
-/

namespace AdversarialBco.Bit.BLP

open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Poly (oNorm oBall)
open AdversarialBco.Bit.Asm
open Matrix

variable {d : ℕ}

/-- The region of a call: `{y | α_i·y ≤ β_i (i < m), yᵀHy/2 - g·y ≤ ℓ, |y| ≤ R}`, in `ℝ^d`. -/
def CallQ.region (D : CallQ d) : Set (Fin d → ℝ) :=
  {y | (∀ i, (fun j => (D.α i j : ℝ)) ⬝ᵥ y ≤ D.β i) ∧
    y ⬝ᵥ (D.H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (D.g j : ℝ)) ⬝ᵥ y ≤ D.ℓ ∧ oNorm y ≤ D.R}

/-- The objective of a call, `yᵀPy/2 - f·y`. -/
noncomputable def CallQ.obj (D : CallQ d) (y : Fin d → ℝ) : ℝ :=
  y ⬝ᵥ (D.P.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (D.f j : ℝ)) ⬝ᵥ y

/-- (O3) = (B4) on BL's call data (the projection theorem, part (b)): if the
region holds a ball of radius `r > 0` (centre not passed), `P` is positive definite, `H` positive semidefinite,
`R ≥ 1` and `e > 0`, the routine returns a point of the region within `e` of the infimum of the objective there. -/
def O3SpecQ (ap : ∀ {d : ℕ}, CallQ d → Option (Fin d → ℚ)) : Prop :=
  ∀ (d : ℕ) (D : CallQ d) (a0 : Fin d → ℝ), 1 ≤ D.R → 0 < D.r → oBall a0 D.r ⊆ D.region →
    (D.P.map ((↑) : ℚ → ℝ)).PosDef → (D.H.map ((↑) : ℚ → ℝ)).PosSemidef → 0 < D.e →
      ∃ μ, ap D = some μ ∧ (fun j => (μ j : ℝ)) ∈ D.region ∧
        ∀ x ∈ D.region, D.obj (fun j => (μ j : ℝ)) ≤ D.obj x + D.e

end AdversarialBco.Bit.BLP
