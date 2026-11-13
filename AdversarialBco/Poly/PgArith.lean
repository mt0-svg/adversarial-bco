/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The arithmetic of the theorem of Procedure PG: definitions and interface statements

Interface: inequalities between the constants of the procedure PG (the paper's appendix on the position), for all
`d ≥ 1` and `ρ ≥ 1`. The parameters: `κ = 1/8`, the rational `PB = 1.254 ≥ (π/2)^{1/2}` in `L_D = t_max = κ PB ρ`,
every other parameter by the formulas of the appendix on the position. The dimension `d` is a real number `≥ 1` here
(a statement for every real `d ≥ 1` contains the one for integers).

The statements: Proposition A (i) at the accuracy of the descent (`PgPropAi`), the three thresholds of Corollary A
(`PgCorAi`, `PgCorAii`, `PgCorAiii`), the constants of the conclusion (`PgConclusion`) and the Gaussian tail at the
inner radius (`PgQtail`).

Every statement is a `Prop`, proved in `AdversarialBco/Poly/PgArithProof.lean` (theorems named after the `Prop` in
lower camel case, `pgCorAi : PgCorAi`).
-/

namespace AdversarialBco.Poly

/-- `κ = 1/8`, the mean of the gauge in the Gaussian position. -/
noncomputable def pgKappa : ℝ := 1 / 8

/-- `PB = 1.254`, a rational upper bound of `(π/2)^{1/2} = 1.25331...`. -/
noncomputable def pgPB : ℝ := 1254 / 1000

/-- `a = 1`, the scale of the returned position `(μ, a T)`: no dilation, the position returned is `(μ, T)`, and
the certificate proposition (b) is read at radius 1, where `Q(1) ≥ 1.1 κ` (`PgQtail`). -/
noncomputable def pgA : ℝ := 1

/-- `λ = (2 log (1 + ρ))^{1/2}`. -/
noncomputable def pgLam (ρ : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 + ρ))

/-- `L_D = t_max = κ PB ρ`, the Lipschitz constant on the domain and the largest eigenvalue allowed there. -/
noncomputable def pgLD (ρ : ℝ) : ℝ := pgKappa * pgPB * ρ

/-- `t_min = 1/(9 d λ)`. -/
noncomputable def pgTmin (d ρ : ℝ) : ℝ := 1 / (9 * d * pgLam ρ)

/-- `e_h = κ²/(922 d² λ² L_D)`, the accuracy of the descent. -/
noncomputable def pgEh (d ρ : ℝ) : ℝ := pgKappa ^ 2 / (922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ)

/-- `τ_b = κ/(12 d λ)`, the threshold of the test on `b`. -/
noncomputable def pgTaub (d ρ : ℝ) : ℝ := pgKappa / (12 * d * pgLam ρ)

/-- `c_2 = 8 φ(2^{1/2}) = 8 e^{-1}/(2π)^{1/2}` (Proposition A (ii)). -/
noncomputable def pgC2 : ℝ := 8 * Real.exp (-1) / Real.sqrt (2 * Real.pi)

/-- Proposition A (i) read at `e_h < 0.0012 κ`: `x - 1 - log x < 0.0012` gives `x ≤ 1.05`. -/
def PgPropAi : Prop := ∀ x : ℝ, 0 < x → x - 1 - Real.log x < 0.0012 → x ≤ 1.05

/-- Corollary A, the threshold of (i): `e_h < 0.0012 κ`. -/
def PgCorAi : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgEh d ρ < 0.0012 * pgKappa

/-- Corollary A, the threshold of (ii) at `t = 1/4`: `e_h < κ²/(32 d² (c_2 L_D + κ/d))`. -/
def PgCorAii : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgEh d ρ < pgKappa ^ 2 / (32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d))

/-- Corollary A, the threshold of (iii) for `|b| ≤ τ_b/2`: `1.6 L_D e_h ≤ (τ_b/2)²`. -/
def PgCorAiii : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → 1.6 * pgLD ρ * pgEh d ρ ≤ (pgTaub d ρ / 2) ^ 2

/-- The constants of the conclusion of Theorems PG-core and PG: `36.4/a ≤ 36.4` and `a l ≤ 1.27` at `a = 1`,
`l = 1/(1 - 0.1375)`; `36.4 · 2^{1/2} ≤ 54`; `54 · 5.5^{1/2} ≤ 134`; `134 · 1.27 ≤ 180`. -/
def PgConclusion : Prop :=
  36.4 / pgA ≤ (36.4 : ℝ) ∧ pgA * (1 / (1 - 0.1375)) ≤ (1.27 : ℝ) ∧ 36.4 * Real.sqrt 2 ≤ 54 ∧
    54 * Real.sqrt 5.5 ≤ 134 ∧ 134 * 1.27 ≤ (180 : ℝ)

/-- The inner radius of the theorem PG-core: `Q(a) ≥ 1.1 κ = 0.1375` at `a = 1`, where `Q(a) = ∫_a^∞ φ` is the Gaussian
tail
(`BodySpec.Qtail a`, written out). The true value is `Q(1) = 0.158655`, the room 15 per cent; it follows from
`Body2.Qtail_one_bounds`. -/
def PgQtail : Prop :=
  (0.1375 : ℝ) ≤ ∫ s in Set.Ioi pgA, Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi)

end AdversarialBco.Poly
