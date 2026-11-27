/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosRow
public import AdversarialBco.Unified.SepSpec

@[expose] public section

/-!
# UNI-POS part 3: the hypothesis on the SEP field of the stages, as a consequence of SepSpec's (SEP0)

UNI-POS (the paper's section on the position), part 2. Stage `j` of TRI-OGD-O runs on the body
`K ∩ triCube c (2^{j+1} r0)` read in the position `P` of the previous stage; at the base point `z = μ + L w` of a step
the program runs SEP on the gauge of that body and takes the vector `g` it returns, `gs j P z` (a total function: the
program sets `g = 0` when SEP fails, or any other measurable rule).

* `IsQ`, `IsRatE`, `IsRatPg`: rational reals, vectors and points of `PgSp d` (the oracle answers rational queries, so
  the program's field is read at rational points only).
* `triRz`: a radius of the base points `μ + L w`, `x` in the box of dimension `d`, `‖w‖ ≤ M_d`.
* `PosSepHyp`: the hypothesis the stage chain reads: at every rational position `P` whose stage body is a `PgBody`
  at the radius `ρ_a` (the good event of the earlier stages), at every rational base point of norm at most `triRz d`,
  the program's vector satisfies (SEP0) (`Sep0`, Unified/PosCore.lean) for the gauge of the stage body.
* `sep0_of_fin`, `sep0_of_sepOut`: (SEP0) in the form of `SepZero` (Unified/SepSpec.lean, on `Fin d → ℝ` with
  `oNorm` and `⬝ᵥ`) gives `Sep0`; from a SEP output (`SepAcc`'s conclusion: a `τ`-subgradient in the `ℓ_1` form at a
  point within `ρ` of the base point) and `SepZero` at `L = 1`, `Sep0` holds with slope `τ √d` and offset
  `(2 + 2 τ √d) ρ`.
* `posSepHyp_of_sepOut`: `PosSepHyp` from SEP outputs at the good positions, through `SepZero`.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

variable {d : ℕ}

/-- A rational real. -/
def IsQ (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℚ → ℝ)

/-- A vector with rational coordinates. -/
def IsRatE (z : EuclideanSpace ℝ (Fin d)) : Prop := ∀ i, IsQ (z i)

/-- A point of `PgSp d` with rational coordinates. -/
def IsRatPg (x : PgSp d) : Prop := ∀ k, IsQ (x k)

/-- A radius of the base points `μ + L w` of the steps: `√d r + b (d (d + 1)/2)^{1/2} M_d`, `M_d = (8 d k_g)^{1/2}`. -/
noncomputable def triRz (d : ℕ) : ℝ :=
  Real.sqrt d * triR d + triB d * Real.sqrt (d * (d + 1) / 2) * Real.sqrt (8 * d * triKg d)

/-- **The SEP field of the stages** (UNI-POS part 2): at every rational position `P` whose stage body
`posBody (K ∩ triCube c (2^{j+1} r0)) P` is a `PgBody` at the radius `ρ_a` (what the good event of the stages before
`j` gives, `triStage_inputK`), at every rational base point `z` with `‖z‖ ≤ triRz d`, the program's vector
`gs j P z` satisfies (SEP0) for the gauge of the stage body with slope `as` and offset `cs`. Nothing is asked at the
other positions (off the good event the program's rule when SEP fails is free). -/
def PosSepHyp (K : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ)
    (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (as cs : ℝ) : Prop :=
  ∀ (j : ℕ) (P : PgSp d), IsRatPg P → (pgMat P).det ≠ 0 →
    PgBody (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (triRa d) →
    ∀ z, IsRatE z → ‖z‖ ≤ triRz d →
      Sep0 (gauge (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P))) z (gs j P z) as cs

theorem upos_oNorm (v : Fin d → ℝ) : oNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold oNorm
  congr 1
  simp [dotProduct, sq]

theorem upos_inner (g v : Fin d → ℝ) :
    inner ℝ (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 v) = g ⬝ᵥ v := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- (SEP0) in the coordinates of `SepZero` gives `Sep0`. -/
theorem sep0_of_fin (h : (Fin d → ℝ) → ℝ) (y0 g : Fin d → ℝ) (a c : ℝ)
    (H : ∀ z, h y0 + g ⬝ᵥ (z - y0) - a * oNorm (z - y0) - c ≤ h z) :
    Sep0 (fun v : EuclideanSpace ℝ (Fin d) => h (WithLp.ofLp v)) (WithLp.toLp 2 y0) (WithLp.toLp 2 g) a c := by
  intro z
  have H1 := H (WithLp.ofLp z)
  have e1 : z - WithLp.toLp 2 y0 = WithLp.toLp 2 (WithLp.ofLp z - y0) := by ext i; simp
  rw [e1, upos_inner, ← upos_oNorm]
  simpa using H1

/-- **(SEP0) from a SEP output**: a `τ`-subgradient in the `ℓ_1` form (the conclusion of `SepAcc`) of a `1`-Lipschitz
`π` at a point `y` with `oNorm (y - y0) ≤ ρ` gives `Sep0 π y0 g (τ √d) ((2 + 2 τ √d) ρ)`, through `SepZero` at `L = 1`. -/
theorem sep0_of_sepOut (hZ : AdversarialBco.Uni.SepZero) (π : EuclideanSpace ℝ (Fin d) → ℝ) (hπ : LipschitzWith 1 π)
    (y0 y g : Fin d → ℝ) (τ ρ : ℝ) (hτ : 0 ≤ τ) (hy : oNorm (y - y0) ≤ ρ)
    (hsub : ∀ z, π (WithLp.toLp 2 y) + g ⬝ᵥ (z - y) - τ * ∑ i, |z i - y i| ≤ π (WithLp.toLp 2 z)) :
    Sep0 π (WithLp.toLp 2 y0) (WithLp.toLp 2 g) (τ * Real.sqrt d) ((2 * 1 + 2 * τ * Real.sqrt d) * ρ) := by
  have hlip : ∀ x y : Fin d → ℝ, |π (WithLp.toLp 2 x) - π (WithLp.toLp 2 y)| ≤ 1 * oNorm (x - y) := by
    intro x y
    have h := hπ.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    rw [Real.dist_eq, dist_eq_norm] at h
    simp only [NNReal.coe_one] at h
    rw [upos_oNorm]
    simpa using h
  unfold AdversarialBco.Uni.SepZero at hZ
  obtain ⟨-, h2⟩ := hZ d (fun x => π (WithLp.toLp 2 x)) 1 τ ρ y0 y g hlip zero_le_one hτ hy hsub
  have h3 := sep0_of_fin (fun x => π (WithLp.toLp 2 x)) y0 g (τ * Real.sqrt d) ((2 * 1 + 2 * τ * Real.sqrt d) * ρ)
    fun z => by simpa only [mul_assoc] using h2 z
  simpa using h3

/-- **`PosSepHyp` from SEP outputs** (the consequence of `SepAcc` and `SepZero` the stage chain reads): if at every
good rational position and rational base point `z` in range the program's vector `gs j P z` is the `g` of a point
`y` within `ρ` of `z` at which it is a `τ`-subgradient of the gauge of the stage body in the `ℓ_1` form, then
`PosSepHyp` holds with slope `τ √d` and offset `(2 + 2 τ √d) ρ`. -/
theorem posSepHyp_of_sepOut (hZ : AdversarialBco.Uni.SepZero) (K : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d))
    (r0 : ℝ) (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (τ ρ : ℝ) (hτ : 0 ≤ τ)
    (hout : ∀ (j : ℕ) (P : PgSp d), IsRatPg P → (pgMat P).det ≠ 0 →
      PgBody (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (triRa d) →
      ∀ z, IsRatE z → ‖z‖ ≤ triRz d → ∃ y : Fin d → ℝ, oNorm (y - WithLp.ofLp z) ≤ ρ ∧
        ∀ w : Fin d → ℝ, gauge (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (WithLp.toLp 2 y) +
          WithLp.ofLp (gs j P z) ⬝ᵥ (w - y) - τ * ∑ i, |w i - y i| ≤
            gauge (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (WithLp.toLp 2 w)) :
    PosSepHyp K c r0 gs (τ * Real.sqrt d) ((2 * 1 + 2 * τ * Real.sqrt d) * ρ) := by
  intro j P hPq hdet hbody z hzq hz
  obtain ⟨y, hy, hsub⟩ := hout j P hPq hdet hbody z hzq hz
  have hlip := (tri_gauge _ hbody.1 hbody.2.2.1).1
  have h := sep0_of_sepOut hZ _ hlip (WithLp.ofLp z) y (WithLp.ofLp (gs j P z)) τ ρ hτ hy hsub
  simpa using h

end AdversarialBco.UniPos
