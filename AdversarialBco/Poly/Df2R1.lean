/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# DF2, Lemma D.2: the rank-one updates of one round (interface)

Interface of Lemma D.2: the update `P' = a P + c u uᵀ` of the precision, its inverse
`Σ' = (Σ - (c/q) w wᵀ)/a` and its factor `A' = a^{-1/2} (A - c' w ξᵀ)`, written in coordinates (`Matrix (Fin d) (Fin d) ℝ`,
vectors `Fin d → ℝ`). Pure algebra: no probability, no other file of the project.

Notation of Appendix D: `P` positive definite, `A Aᵀ = Σ = P⁻¹`, `ξ ∈ ℝ^d`, `w = A ξ`, `u = P w`, `c ∈ ℝ`, `a = 1 - c`,
`q = a + c |ξ|²`, `P' = a P + c u uᵀ`, `c' = (c/q)/(1 + (a/q)^{1/2})`, `κ₀ = (1 - λ)^{-2}`, `ĝ = Y u/(1 - λ)`.

* `LemmaR1i`: `Aᵀ u = ξ` (that is `u = A^{-T} ξ`), `Σ u = w`, `⟨u, w⟩ = |ξ|²`,
  `xᵀ P' x ≥ min(a, q) |A⁻¹ x|²`, `a > 0 ∧ q > 0 → P'` positive definite, `det P' = a^{d-1} q det P` for `d ≥ 1`.
* `LemmaR1ii`: for `a > 0`, `q > 0`: `Σ' P' = 1` and `P' Σ' = 1`.
* `LemmaR1iii`: for `a > 0`, `q > 0`: `c'² |ξ|² - 2 c' + c/q = 0`, `A' A'ᵀ = Σ'`, `det A' ≠ 0`.
* `LemmaR1iv`: for `a > 0`, `q > 0`, `λ ≠ 1` (`l` in Lean): `Σ' ĝ = (Y/((1 - λ) q)) w` and `ĝᵀ Σ' ĝ = κ₀ Y² |ξ|²/q`.
* `LemmaR1v`: `tr P' = a tr P + c |u|²`, and for `a > 0`, `q > 0`: `tr Σ' = (tr Σ - (c/q) |w|²)/a`.

Junk values. `Σ'`, `c'` and `A'` divide by `a` and `q` and take `√a`, `√(a/q)`: every statement that reads them assumes
`a > 0` and `q > 0`. `ĝ` and `κ₀` divide by `1 - λ`: `LemmaR1iv` assumes `λ ≠ 1`. `A⁻¹` is the inverse of an invertible
matrix under `R1Hyp` (`A (Aᵀ P) = 1`).

The converse of the positivity in (i) (for `d ≥ 2`, `P'` positive definite gives `a > 0` and `q > 0`) is not stated: the
route reads only the direct implication (the first clause of the guard).
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

/-- `w = A ξ`. -/
def r1W {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : Fin d → ℝ := A *ᵥ ξ

/-- `u = P w = P A ξ`. -/
def r1U {d : ℕ} (P A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) : Fin d → ℝ := P *ᵥ r1W A ξ

/-- `q = a + c |ξ|²` with `a = 1 - c`. -/
def r1Q {d : ℕ} (c : ℝ) (ξ : Fin d → ℝ) : ℝ := (1 - c) + c * (ξ ⬝ᵥ ξ)

/-- `P' = a P + c u uᵀ`. -/
def r1P' {d : ℕ} (P A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - c) • P + c • vecMulVec (r1U P A ξ) (r1U P A ξ)

/-- `Σ' = (Σ - (c/q) w wᵀ)/a`. -/
noncomputable def r1S' {d : ℕ} (S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - c)⁻¹ • (S - (c / r1Q c ξ) • vecMulVec (r1W A ξ) (r1W A ξ))

/-- `c' = (c/q)/(1 + (a/q)^{1/2})`. -/
noncomputable def r1C' {d : ℕ} (c : ℝ) (ξ : Fin d → ℝ) : ℝ :=
  (c / r1Q c ξ) / (1 + Real.sqrt ((1 - c) / r1Q c ξ))

/-- `A' = a^{-1/2} (A - c' w ξᵀ)`. -/
noncomputable def r1A' {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (Real.sqrt (1 - c))⁻¹ • (A - r1C' c ξ • vecMulVec (r1W A ξ) ξ)

/-- The standing hypotheses of Lemma D.2: `P` positive definite and `A Aᵀ = Σ = P⁻¹`. -/
def R1Hyp {d : ℕ} (P S A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  P.PosDef ∧ A * Aᵀ = S ∧ S * P = 1

/-- Lemma D.2 (i). -/
def LemmaR1i : Prop :=
  ∀ (d : ℕ) (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ), R1Hyp P S A →
    Aᵀ *ᵥ r1U P A ξ = ξ ∧ S *ᵥ r1U P A ξ = r1W A ξ ∧ r1U P A ξ ⬝ᵥ r1W A ξ = ξ ⬝ᵥ ξ ∧
      (∀ x : Fin d → ℝ, min (1 - c) (r1Q c ξ) * ((A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x)) ≤ x ⬝ᵥ (r1P' P A ξ c *ᵥ x)) ∧
      (0 < 1 - c → 0 < r1Q c ξ → (r1P' P A ξ c).PosDef) ∧
      (1 ≤ d → (r1P' P A ξ c).det = (1 - c) ^ (d - 1) * r1Q c ξ * P.det)

/-- Lemma D.2 (ii): `Σ'` is the inverse of `P'`. -/
def LemmaR1ii : Prop :=
  ∀ (d : ℕ) (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ), R1Hyp P S A →
    0 < 1 - c → 0 < r1Q c ξ → r1S' S A ξ c * r1P' P A ξ c = 1 ∧ r1P' P A ξ c * r1S' S A ξ c = 1

/-- Lemma D.2 (iii): `c'` solves `c'² |ξ|² - 2 c' + c/q = 0`, and `A'` is an invertible factor of `Σ'`. -/
def LemmaR1iii : Prop :=
  ∀ (d : ℕ) (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ), R1Hyp P S A →
    0 < 1 - c → 0 < r1Q c ξ →
      r1C' c ξ ^ 2 * (ξ ⬝ᵥ ξ) - 2 * r1C' c ξ + c / r1Q c ξ = 0 ∧
        r1A' A ξ c * (r1A' A ξ c)ᵀ = r1S' S A ξ c ∧ (r1A' A ξ c).det ≠ 0

/-- Lemma D.2 (iv): the Newton step and the size of the gradient estimate `ĝ = Y u/(1 - λ)` in `Σ'`. -/
def LemmaR1iv : Prop :=
  ∀ (d : ℕ) (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c Y l : ℝ), R1Hyp P S A →
    0 < 1 - c → 0 < r1Q c ξ → l ≠ 1 →
      r1S' S A ξ c *ᵥ ((Y / (1 - l)) • r1U P A ξ) = (Y / ((1 - l) * r1Q c ξ)) • r1W A ξ ∧
        ((Y / (1 - l)) • r1U P A ξ) ⬝ᵥ (r1S' S A ξ c *ᵥ ((Y / (1 - l)) • r1U P A ξ)) =
          ((1 - l) ^ 2)⁻¹ * Y ^ 2 * (ξ ⬝ᵥ ξ) / r1Q c ξ

/-- Lemma D.2 (v): the traces. -/
def LemmaR1v : Prop :=
  ∀ (d : ℕ) (P S A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (c : ℝ), R1Hyp P S A →
    (r1P' P A ξ c).trace = (1 - c) * P.trace + c * (r1U P A ξ ⬝ᵥ r1U P A ξ) ∧
      (0 < 1 - c → 0 < r1Q c ξ →
        (r1S' S A ξ c).trace = (S.trace - (c / r1Q c ξ) * (r1W A ξ ⬝ᵥ r1W A ξ)) / (1 - c))

end AdversarialBco.Poly
