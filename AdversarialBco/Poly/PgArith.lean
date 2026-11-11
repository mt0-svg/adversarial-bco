/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The arithmetic of Theorem 8.3: definitions and interface statements

Interface: the inequalities between the constants of the procedure PG
(Appendix F of the paper), for all `d ≥ 1` and `ρ ≥ 1`. The parameters: `κ = 1/8`, the rational `PB = 1.254 ≥ (π/2)^{1/2}` in `L_D = t_max = κ PB ρ` and in
`Δ = κ ρ (4 + PB² d)^{1/2}`, every other parameter by the formulas of Appendix F. The dimension `d` is a real number
`≥ 1` here (a statement for every real `d ≥ 1` contains the one for integers). The integers of the procedure
(`N`, `n_T`, `j`, `J`, `m_T`) enter through the real numbers they are the ceilings of, as in Appendix F ("at least
x", "at most x + 1").

Every statement is a `Prop`, proved in `AdversarialBco/Poly/PgArithProof.lean` (theorems named after the `Prop` in
lower camel case, `pgNSize : PgNSize`).
-/

namespace AdversarialBco.Poly

/-- `κ = 1/8`, the mean of the gauge in the Gaussian position. -/
noncomputable def pgKappa : ℝ := 1 / 8

/-- `PB = 1.254`, a rational upper bound of `(π/2)^{1/2} = 1.25331...`. -/
noncomputable def pgPB : ℝ := 1254 / 1000

/-- `a = 1`, the scale of the returned position `(μ, a T)` (`pgOut`): no dilation, the position returned is `(μ, T)`, and
Proposition F.2 (b) is read at radius 1, where `Q(1) ≥ 1.1 κ` (`PgQtail`). -/
noncomputable def pgA : ℝ := 1

/-- `λ = (2 log (1 + ρ))^{1/2}`. -/
noncomputable def pgLam (ρ : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 + ρ))

/-- `L_D = t_max = κ PB ρ`, the Lipschitz constant on the domain and the largest eigenvalue allowed there. -/
noncomputable def pgLD (ρ : ℝ) : ℝ := pgKappa * pgPB * ρ

/-- `t_min = 1/(9 d λ)`. -/
noncomputable def pgTmin (d ρ : ℝ) : ℝ := 1 / (9 * d * pgLam ρ)

/-- `Δ = κ ρ (4 + PB² d)^{1/2}`, the diameter bound of the domain. -/
noncomputable def pgDelta (d ρ : ℝ) : ℝ := pgKappa * ρ * Real.sqrt (4 + pgPB ^ 2 * d)

/-- `G² = (5 L_D² d (d + 2)(d + 5) + 2 κ²/d)/t_min²`, the second moment bound of the estimates (Lemma E (b)). -/
noncomputable def pgG2 (d ρ : ℝ) : ℝ :=
  (5 * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * pgKappa ^ 2 / d) / pgTmin d ρ ^ 2

/-- `e_h = κ²/(922 d² λ² L_D)`, the accuracy of the descent. -/
noncomputable def pgEh (d ρ : ℝ) : ℝ := pgKappa ^ 2 / (922 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ)

/-- `η = e_h t_min/(7 L_D (1 + d^{1/2}) Δ)`, the relative error of the gauge by bisection. -/
noncomputable def pgEta (d ρ : ℝ) : ℝ :=
  pgEh d ρ * pgTmin d ρ / (7 * pgLD ρ * (1 + Real.sqrt d) * pgDelta d ρ)

/-- `τ_b = κ/(12 d λ)`, the threshold of the test on `b`. -/
noncomputable def pgTaub (d ρ : ℝ) : ℝ := pgKappa / (12 * d * pgLam ρ)

/-- The real number whose ceiling is `n_T`: `1.25 L_D² d³ max(6144 (d + 1)(d + 5), 221184 (d + 3) λ²)/κ²`. -/
noncomputable def pgNTreal (d ρ : ℝ) : ℝ :=
  5 / 4 * pgLD ρ ^ 2 * d ^ 3 * max (6144 * (d + 1) * (d + 5)) (221184 * (d + 3) * pgLam ρ ^ 2) / pgKappa ^ 2

/-- The real number whose ceiling is `N`: `16 Δ² G²/e_h²`. -/
noncomputable def pgNreal (d ρ : ℝ) : ℝ := 16 * pgDelta d ρ ^ 2 * pgG2 d ρ / pgEh d ρ ^ 2

/-- `c_2 = 8 φ(2^{1/2}) = 8 e^{-1}/(2π)^{1/2}` (Proposition A (ii)). -/
noncomputable def pgC2 : ℝ := 8 * Real.exp (-1) / Real.sqrt (2 * Real.pi)

/-- `rb_d = 400 d (log (2d + 2))^{1/2}`, the bound on the radius ratios of the growing balls. -/
noncomputable def pgRb (d : ℝ) : ℝ := 400 * d * Real.sqrt (Real.log (2 * d + 2))

/-- Proposition A (i) read at `e_h < 0.0012 κ`: `x - 1 - log x < 0.0012` gives `x ≤ 1.05`. -/
def PgPropAi : Prop := ∀ x : ℝ, 0 < x → x - 1 - Real.log x < 0.0012 → x ≤ 1.05

/-- `c_2 ≤ 1.1742`. -/
def PgC2Bound : Prop := 0 < pgC2 ∧ pgC2 ≤ 1.1742

/-- Corollary A, the threshold of (i): `e_h < 0.0012 κ`. -/
def PgCorAi : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgEh d ρ < 0.0012 * pgKappa

/-- Corollary A, the threshold of (ii) at `t = 1/4`: `e_h < κ²/(32 d² (c_2 L_D + κ/d))`. -/
def PgCorAii : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgEh d ρ < pgKappa ^ 2 / (32 * d ^ 2 * (pgC2 * pgLD ρ + pgKappa / d))

/-- Corollary A, the threshold of (iii) for `|b| ≤ τ_b/2`: `1.6 L_D e_h ≤ (τ_b/2)²`. -/
def PgCorAiii : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → 1.6 * pgLD ρ * pgEh d ρ ≤ (pgTaub d ρ / 2) ^ 2

/-- The bias bound of Lemma E and Lemma T: `u = η L_D (1 + d^{1/2}) ≤ 1/(145600 d³ λ³ ρ²)`. -/
def PgBiasU : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ →
    pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ 1 / (145600 * d ^ 3 * pgLam ρ ^ 3 * ρ ^ 2)

/-- The bias of the test (Lemma T): `2^{1/2} u ≤ τ_b/8`, `u ≤ κ/80` and `τ_b/8 ≤ κ/(16 d)`. -/
def PgBiasTest : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ →
    Real.sqrt 2 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) ≤ pgTaub d ρ / 8 ∧
      pgEta d ρ * pgLD ρ * (1 + Real.sqrt d) ≤ pgKappa / 80 ∧ pgTaub d ρ / 8 ≤ pgKappa / (16 * d)

/-- Lemma E (b): `0 ≤ η` and `(1 + η)² ≤ 5/4`. -/
def PgEtaSq : Prop := ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → 0 ≤ pgEta d ρ ∧ (1 + pgEta d ρ) ^ 2 ≤ 5 / 4

/-- The bias of the descent (Theorem F.3, one round): `β Δ ≤ e_h/4`, `β = 3^{1/2} u/t_min`. -/
def PgBiasDescent : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ →
    Real.sqrt 3 * (pgEta d ρ * pgLD ρ * (1 + Real.sqrt d)) / pgTmin d ρ * pgDelta d ρ ≤ pgEh d ρ / 4

/-- The sample counts of Lemma T (Chebyshev at probability `1/12` with the moments of Lemma E (b) and `5/4` for
`(1 + η)²`), for `k`, `b` and `Q` at the tolerances `κ/80`, `τ_b/8`, `κ/(16 d)`, are at most the real `n_T`. -/
def PgCounts : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ →
    12 * (5 / 4 * pgLD ρ ^ 2 * (1 + Real.sqrt d) ^ 2) / (pgKappa / 80) ^ 2 ≤ pgNTreal d ρ ∧
      12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 3))) / (pgTaub d ρ / 8) ^ 2 ≤ pgNTreal d ρ ∧
      12 * (5 / 4 * pgLD ρ ^ 2 * (2 * d * (d + 1) * (d + 5))) / (pgKappa / (16 * d)) ^ 2 ≤ pgNTreal d ρ

/-- The size of `N` (Theorem F.3, sizes): `N ≤ 16 Δ² G²/e_h² + 1 ≤ 1.8e11 d^{10} ρ^6 log³(1 + ρ)`. -/
def PgNSize : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgNreal d ρ + 1 ≤ 1.8e11 * d ^ 10 * ρ ^ 6 * Real.log (1 + ρ) ^ 3

/-- The size of `n_T`: `n_T ≤ n_T(real) + 1 ≤ 3.7e6 d^5 ρ² log(1 + ρ)`. -/
def PgNTSize : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → pgNTreal d ρ + 1 ≤ 3.7e6 * d ^ 5 * ρ ^ 2 * Real.log (1 + ρ)

/-- The ratio of the bisection: `ρ/η ≤ 152468 d⁴ ρ^{5.5}`. -/
def PgRhoEta : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ → ρ / pgEta d ρ ≤ 152468 * d ^ 4 * ρ ^ (11 / 2 : ℝ)

/-- The number of bisection steps: `j ≤ log₂(ρ/η) + 1 ≤ 19 + 4 log₂ d + 5.5 log₂ ρ`. -/
def PgBisectSteps : Prop :=
  ∀ d ρ : ℝ, 1 ≤ d → 1 ≤ ρ →
    Real.logb 2 (ρ / pgEta d ρ) + 1 ≤ 19 + 4 * Real.logb 2 d + 5.5 * Real.logb 2 ρ

/-- The failure probability of Theorem F.3: with `2^J ≥ 4/δ` and `δ' = δ/(2J)`,
`J δ' + ((1 + δ')/2)^J ≤ 0.92 δ`. -/
def PgFailure : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ J : ℕ, 1 ≤ J → 4 / δ ≤ 2 ^ J →
    J * (δ / (2 * J)) + ((1 + δ / (2 * J)) / 2) ^ J ≤ 0.92 * δ

/-- The amplification of Lemma T: `m ≥ 8 log(1/δ')` gives `exp(-m/8) ≤ δ'`. -/
def PgHoeffding : Prop :=
  ∀ δ' : ℝ, 0 < δ' → ∀ m : ℕ, 8 * Real.log (1 / δ') ≤ m → Real.exp (-(m : ℝ) / 8) ≤ δ'

/-- The step size of the descent: `N ≥ 16 Δ² G²/e_h²` gives `Δ G/N^{1/2} ≤ e_h/4`. -/
def PgStep : Prop :=
  ∀ a e N : ℝ, 0 < a → 0 < e → 16 * a ^ 2 / e ^ 2 ≤ N → a / Real.sqrt N ≤ e / 4

/-- The constants of the conclusion of Theorems PG-core and PG: `36.4/a ≤ 36.4` and `a l ≤ 1.27` at `a = 1`,
`l = 1/(1 - 0.1375)`; `36.4 · 2^{1/2} ≤ 54`; `54 · 5.5^{1/2} ≤ 134`; `134 · 1.27 ≤ 180`. -/
def PgConclusion : Prop :=
  36.4 / pgA ≤ (36.4 : ℝ) ∧ pgA * (1 / (1 - 0.1375)) ≤ (1.27 : ℝ) ∧ 36.4 * Real.sqrt 2 ≤ 54 ∧
    54 * Real.sqrt 5.5 ≤ 134 ∧ 134 * 1.27 ≤ (180 : ℝ)

/-- The inner radius of Theorem F.3: `Q(a) ≥ 1.1 κ = 0.1375` at `a = 1`, where `Q(a) = ∫_a^∞ φ` is the Gaussian tail
(`BodySpec.Qtail a`, written out). The true value is `Q(1) = 0.158655`, the room 15 per cent; it follows from
`Body2.Qtail_one_bounds`. -/
def PgQtail : Prop :=
  (0.1375 : ℝ) ≤ ∫ s in Set.Ioi pgA, Real.exp (-(s ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- (G3) of Theorem 8.3, the hand bound: `log (1 + rb_d) ≤ 5.5 log (2d + 2)`. -/
def PgRbLog : Prop := ∀ d : ℝ, 1 ≤ d → Real.log (1 + pgRb d) ≤ 5.5 * Real.log (2 * d + 2)

/-- (G3) of Theorem 8.3: the map `ρ ↦ 3 · 54 d (log (1 + ρ))^{1/2}` sends `[0, rb_d]` into itself, and the final radius
`54 d (log (1 + rb_d))^{1/2}` is at most `134 d (log (2d + 2))^{1/2}`. -/
def PgGrowing : Prop :=
  ∀ d : ℝ, 1 ≤ d →
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ pgRb d → 3 * 54 * d * Real.sqrt (Real.log (1 + ρ)) ≤ pgRb d) ∧
      54 * d * Real.sqrt (Real.log (1 + pgRb d)) ≤ 134 * d * Real.sqrt (Real.log (2 * d + 2))

/-- The chi-square moments of Lemma E (b), as identities: with `E|g|² = d`, `E|g|⁴ = d (d + 2)`,
`E|g|⁶ = d (d + 2)(d + 4)`, `E[|g|² (1 + |g|²)] = d (d + 3)`, `E[(|g|⁴ - 2|g|² + d)(1 + |g|²)] = d (d + 1)(d + 5)`,
and `2 d (d + 3) + 4 d (d + 1)(d + 5) ≤ 4 d (d + 2)(d + 5)` for `d ≥ 0`. -/
def PgMoments : Prop :=
  ∀ d : ℝ, 0 ≤ d →
    d + d * (d + 2) = d * (d + 3) ∧
      d * (d + 2) * (d + 4) - d * (d + 2) + (d - 2) * d + d = d * (d + 1) * (d + 5) ∧
      2 * d * (d + 3) + 4 * d * (d + 1) * (d + 5) ≤ 4 * d * (d + 2) * (d + 5)

end AdversarialBco.Poly
