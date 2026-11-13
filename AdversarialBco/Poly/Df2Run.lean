/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly
public import AdversarialBco.Poly.PgProc
public import AdversarialBco.Poly.Df2Oracle
public import AdversarialBco.Poly.Df2
public import AdversarialBco.Poly.MachVL
public import AdversarialBco.Poly.PgProcProof

@[expose] public section

/-!
# DF2-O: the parameters and the state of an epoch

The parameters of the learner DF2-O at `(d, n, δ)` (`df2oPar`), the state of an epoch (`Df2St`), the mode of the
learner before a round (`Df2Mode`), the start of an epoch (`df2Init`), the quadratic `df2Phi`, and the positioned
body cut by `B_R`, `K' = K~ ∩ B_R` (`df2Kp`), with `K_ε = (1 - ε) K'` (`df2Keps`). DF2-O runs DF2 on `K'`,
`K~ = posBody K μ_S A_S` the body in the position returned by Procedure PG, `R = 134 d (log (2d + 2))^{1/2}`, in the
positioned coordinates (`Fin d → ℝ` and matrices, as `Df2R1.lean`).

The state of an epoch (`Df2St`): `μ_t`, `P_t`, `Σ_t`, the factor `A_t`, the quadratic
`Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`, `Ĝ_{t-1}`, `l_{t-1}`, the ball `(ctr_t, r_t)`, and whether `t` is
the first round of its epoch (then `R⁻_t = K_ε`). `Df2Mode`: off (`o` played), guard (`μ_S` played), or a state.

## Parameters

`δ₁ = min (δ/3, e^{-14} (d n)^{-3})` (the confidence of the learner: Theorem POLY32-DF2 asks `δ ≤ e^{-14} (dn)^{-3}`,
and part A of Theorem POLY32-DF2-O spends `3 δ₁`), `δ_e = 4 δ₁/(5n)`, `L_e = C₀ log (1/δ_e)` (`C₀ = df2C0 = 36`),
`C_λ = 725`, `C_σ = 8`, `C_ε = 20 C_λ`, `λ = 1/(C_λ d L_e²)`, `η = d^{1/2}/(L_e n^{1/2})`, `σ² = 1/(C_σ L_e)`,
`ρ = 2 C_λ d² L_e³`, `ε = C_ε d^{3/2} L_e⁵/n^{1/2}`, `κ = 1/4`, `θ = 1`, `α = 1/4`, `c₁ = 8`, `γ = 1/100`,
`κ₀ = (1 - λ)^{-2}`, `R = 134 d (log (2d + 2))^{1/2}`, `j = ⌈log₂ (n R (R + 7)/(δ₁ ε))⌉`, `s_b = δ_e²/(R (R + 1))`.

## Junk values

`x / 0 = 0`, `Real.sqrt` of a negative number is `0`, `Real.log` and `Real.logb` read `|x|`, `⌈x⌉₊ = 0` for `x ≤ 0`.
For `d, n ≥ 1` and `0 < δ`: `δ₁, δ_e > 0`, `δ_e < 1`, so `L_e > 0` and `λ, η, σ², ρ, ε, R > 0`; `λ < 1`. `K_ε`
divides by `1 - ε`, read only when `ε ≤ 1/2`.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM

variable {d : ℕ}

/-! ## Parameters -/

/-- The parameters of the learner at `(d, n, δ)`. -/
structure Df2OPar where
  δ1 : ℝ
  δe : ℝ
  Le : ℝ
  lam : ℝ
  eta : ℝ
  sig2 : ℝ
  rho : ℝ
  eps : ℝ
  kap : ℝ
  theta : ℝ
  alpha : ℝ
  c1 : ℝ
  gam : ℝ
  k0 : ℝ
  R : ℝ
  sb : ℝ
  j : ℕ

/-- `C_λ = 725`. -/
noncomputable def df2oClam : ℝ := 725

/-- The parameters of the module docstring. -/
noncomputable def df2oPar (d n : ℕ) (δ : ℝ) : Df2OPar :=
  let δ1 := min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)
  let δe := 4 * δ1 / (5 * n)
  let Le := df2C0 * Real.log (1 / δe)
  let lam := 1 / (df2oClam * d * Le ^ 2)
  let eps := 20 * df2oClam * (d * Real.sqrt d) * Le ^ 5 / Real.sqrt n
  let R := 134 * d * Real.sqrt (Real.log (2 * d + 2))
  { δ1 := δ1, δe := δe, Le := Le, lam := lam, eta := Real.sqrt d / (Le * Real.sqrt n), sig2 := 1 / (8 * Le),
    rho := 2 * df2oClam * d ^ 2 * Le ^ 3, eps := eps, kap := 1 / 4, theta := 1, alpha := 1 / 4, c1 := 8,
    gam := 1 / 100, k0 := ((1 - lam) ^ 2)⁻¹, R := R, sb := δe ^ 2 / (R * (R + 1)),
    j := ⌈Real.logb 2 (n * R * (R + 7) / (δ1 * eps))⌉₊ }

/-! ## The state of an epoch -/

/-- The state of an epoch before round `t`. -/
structure Df2St (d : ℕ) where
  /-- `t` is the first round of its epoch. -/
  first : Bool
  mu : Fin d → ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  S : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  b : Fin d → ℝ
  k : ℝ
  G : Fin d → ℝ
  l : ℝ
  ctr : Fin d → ℝ
  r : ℝ

/-- The mode of the learner before a round. -/
inductive Df2Mode (d : ℕ)
  /-- `o = 0` is played: no position, the regime `ε > 1/2`, or a failed play test. -/
  | off
  /-- The guard has acted: `S⁻¹(0) = μ_S` is played after the play test. -/
  | guard
  /-- A round of DF2 from this state. -/
  | run (st : Df2St d)

/-- The start of an epoch: `μ₁ = 0`, `P₁ = I/σ²`, `Σ₁ = σ² I`, `A₁ = σ I`, `Φ₀ = |·|²/(2σ²)`, `Ĝ₀ = 0`, `l₀ = 0`,
the ball `(0, 1 - ε)`. -/
noncomputable def df2Init (p : Df2OPar) (d : ℕ) : Df2St d :=
  ⟨true, 0, p.sig2⁻¹ • 1, p.sig2 • 1, Real.sqrt p.sig2 • 1, 0, 0, 0, 0, 0, 1 - p.eps⟩

/-- `Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`. -/
noncomputable def df2Phi (P : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (k : ℝ) (y : Fin d → ℝ) : ℝ :=
  1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k

/-- The positioned body cut by `B_R`, `K' = K~ ∩ B_R`, in `E d`. -/
def df2Kp (K : Set (E d)) (Ps : PgSp d) (R : ℝ) : Set (E d) := {y | pgMu Ps + pgOp Ps y ∈ K ∧ ‖y‖ ≤ R}

/-- `K_ε = (1 - ε) K'`, in the coordinates `Fin d → ℝ`: `y/(1 - ε) ∈ K'`. -/
noncomputable def df2Keps (K : Set (E d)) (Ps : PgSp d) (R eps : ℝ) : Set (Fin d → ℝ) :=
  {y | WithLp.toLp 2 ((1 - eps)⁻¹ • y) ∈ df2Kp K Ps R}

end AdversarialBco.Poly
