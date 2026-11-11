/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The truncation and the compensator of Lemmas S# and QM: definitions and interface statements

Interface: the steps of Lemma S# and Lemma QM
that are about the estimator, its truncation and its compensator, for any truncation event `G` and any
sub-σ-algebra `m` (the past `F_{s-1}`): the centred truncated increment `ζ = X 1_G - E[X 1_G | m]` (S# step 3,
QM step 4), the decomposition `X - E[X | m] = ζ - b` on `G` with the compensator `b = E[X 1_{Gᶜ} | m]` and its
conditional Cauchy-Schwarz bound (S# step 5, QM step 6), the density ratio and the size of the estimator at the mean
(QM steps 1 and 3), the change of variables behind its unbiasedness (QM step 2), and the arithmetic of S# steps 1, 4
to 6 and QM steps 5 and 6. Nothing here reads the guard, the projections or the stopping rule of the learner.

Every statement is a `Prop`; the theorems that prove them are in
`AdversarialBco/Poly/TruncProof.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

universe u

/-- The centred truncated increment `ζ = X 1_G - E[X 1_G | m]`. -/
noncomputable def truncCentred {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (m : MeasurableSpace Ω)
    (G : Set Ω) (X : Ω → ℝ) : Ω → ℝ :=
  G.indicator X - μ[G.indicator X | m]

/-- The compensator `b = E[X 1_{Gᶜ} | m]`. -/
noncomputable def truncComp {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (m : MeasurableSpace Ω)
    (G : Set Ω) (X : Ω → ℝ) : Ω → ℝ :=
  μ[Gᶜ.indicator X | m]

/-- `E[ζ | m] = 0`. -/
def TruncCentredMean : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω),
    m ≤ m0 → ∀ (G : Set Ω) (X : Ω → ℝ), MeasurableSet G → Integrable X μ →
    μ[truncCentred μ m G X | m] =ᵐ[μ] 0

/-- `|X| ≤ B` on `G` gives `|ζ| ≤ 2 B`. -/
def TruncCentredBound : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω),
    m ≤ m0 → ∀ (G : Set Ω) (X : Ω → ℝ) (B : ℝ), 0 ≤ B → (∀ᵐ ω ∂μ, ω ∈ G → |X ω| ≤ B) →
    ∀ᵐ ω ∂μ, |truncCentred μ m G X ω| ≤ 2 * B

/-- `E[ζ² | m] ≤ E[X² 1_G | m] ≤ E[X² | m]`. -/
def TruncCentredVar : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω),
    m ≤ m0 → ∀ (G : Set Ω) (X : Ω → ℝ), MeasurableSet G → MemLp X 2 μ →
    (μ[fun ω => truncCentred μ m G X ω ^ 2 | m] ≤ᵐ[μ] μ[G.indicator (fun ω => X ω ^ 2) | m]) ∧
      μ[G.indicator (fun ω => X ω ^ 2) | m] ≤ᵐ[μ] μ[fun ω => X ω ^ 2 | m]

/-- On `G`: `X - E[X | m] = ζ - b`. -/
def TruncDecomp : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω),
    m ≤ m0 → ∀ (G : Set Ω) (X : Ω → ℝ), MeasurableSet G → Integrable X μ →
    ∀ᵐ ω ∂μ, ω ∈ G → X ω - μ[X | m] ω = truncCentred μ m G X ω - truncComp μ m G X ω

/-- The conditional Cauchy-Schwarz bound of the compensator: `|E[X 1_A | m]| ≤ E[X² | m]^{1/2} P(A | m)^{1/2}`. -/
def CondExpCauchySchwarz : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω),
    m ≤ m0 → ∀ (A : Set Ω) (X : Ω → ℝ), MeasurableSet A → MemLp X 2 μ →
    ∀ᵐ ω ∂μ, |μ[A.indicator X | m] ω| ≤
      Real.sqrt (μ[fun ω => X ω ^ 2 | m] ω) * Real.sqrt (μ[A.indicator (fun _ => (1 : ℝ)) | m] ω)

/-- Lemma QM step 1: the density ratio at the mean, `(1 - λ)^{-d} exp(-(w/2)(1/(1 - λ)² - 1))` with `w = |W|²`,
lies in `[0, e²]` for `0 < λ ≤ 1/2` and `λ d ≤ 1`. -/
def RatioAtMean : Prop :=
  ∀ (d : ℕ) (lam w : ℝ), 0 < lam → lam ≤ 1 / 2 → lam * d ≤ 1 → 0 ≤ w →
    0 ≤ ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ∧
      ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ≤ Real.exp 2

/-- Lemma QM step 3: for `r ∈ [0, e²]` and `0 < λ ≤ 1`, `|1 + (r - 1)/λ| ≤ e²/λ`. -/
def EstimatorSize : Prop :=
  ∀ lam r : ℝ, 0 < lam → lam ≤ 1 → 0 ≤ r → r ≤ Real.exp 2 → |1 + (r - 1) / lam| ≤ Real.exp 2 / lam

/-- Lemma QM step 2, the change of variables `X = (1 - λ) X' + λ x`: for a positive density `p` of `X` on `ℝ^d`
and the ratio `r(x)(y) = p((y - λ x)/(1 - λ))/((1 - λ)^d p(y))`, `E[r(x)(X) f(X)] = E[f((1 - λ) X + λ x)]`. -/
def EstimatorUnbiased : Prop :=
  ∀ (d : ℕ) (p f : (Fin d → ℝ) → ℝ) (lam : ℝ) (x : Fin d → ℝ), 0 < lam → lam < 1 → (∀ y, 0 < p y) →
    ∫ y, p y * (p ((1 - lam)⁻¹ • (y - lam • x)) / ((1 - lam) ^ d * p y)) * f y =
      ∫ z, p z * f ((1 - lam) • z + lam • x)

/-- Lemma QM step 5, the arithmetic: with `v = 10 e⁴ n/λ²`, `B₁ = e² L/(2 λ ε)` and `l ≤ L`,
`(2 v l)^{1/2} + (4 B₁/3) l ≤ (1/λ)(e² (20 n L)^{1/2} + (2 e²/3) L²/ε)`. -/
def QMFreedmanArith : Prop :=
  ∀ n L lam eps l : ℝ, 0 < lam → 0 < eps → 0 ≤ n → 0 ≤ l → l ≤ L →
    Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l) + 4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l ≤
      1 / lam * (Real.exp 2 * Real.sqrt (20 * n * L) + 2 * Real.exp 2 / 3 * L ^ 2 / eps)

/-- Lemma QM step 6, the arithmetic: `n (e²/λ)(72 d/ε)(3δ/(7n))^{1/2} ≤ 1/λ` when `1/ε ≤ n^{1/2}`,
`δ ≤ c₀ (dn)^{-3}` and `c₀ ≤ e^{-14}`. -/
def QMCompensatorArith : Prop :=
  ∀ (d n : ℕ) (lam eps δ c0 : ℝ), 1 ≤ d → 1 ≤ n → 0 < lam → 0 < eps → 1 / eps ≤ Real.sqrt n → 0 < δ →
    δ ≤ c0 / ((d : ℝ) * n) ^ 3 → c0 ≤ Real.exp (-14) →
    n * (Real.exp 2 / lam * (72 * d / eps) * Real.sqrt (3 * δ / (7 * n))) ≤ 1 / lam

/-- Lemma S# steps 1 and 4, the arithmetic: on `G_s`, with `|Y| ≤ L/(2ε)`, `|W|² ≤ (8d/3) ℓ` and `ℓ ≤ L`, the range
`2 e² a |Y| · 2 (4|W|² + 1)` is at most `B₀ = 24 e² a d L²/ε`, and `(4 B₀/3) l ≤ 32 e² a d L³/ε` for `l ≤ L`
(`a = ηλ`). -/
def SSharpRangeArith : Prop :=
  ∀ (d L a eps y w ell : ℝ), 1 ≤ d → 1 ≤ L → 0 ≤ a → 0 < eps → |y| ≤ L / (2 * eps) → 0 ≤ w →
    w ≤ 8 * d / 3 * ell → ell ≤ L →
    2 * Real.exp 2 * a * |y| * (2 * (4 * w + 1)) ≤ 24 * Real.exp 2 * a * d * L ^ 2 / eps ∧
      ∀ l : ℝ, 0 ≤ l → l ≤ L →
        4 * (24 * Real.exp 2 * a * d * L ^ 2 / eps) / 3 * l ≤ 32 * Real.exp 2 * a * d * L ^ 3 / eps

/-- Lemma S# step 5, the arithmetic: `n · 4 e² a (72 d/ε)(29 d)(3δ/(7n))^{1/2} ≤ a (dn)^{1/2}` when `1/ε ≤ n^{1/2}`,
`δ ≤ c₀ (dn)^{-3}` and `c₀ ≤ 7/(3 (8352 e²)²)` (`8352 = 4 · 72 · 29`). -/
def SSharpCompensatorArith : Prop :=
  ∀ (d n : ℕ) (a eps δ c0 : ℝ), 1 ≤ d → 1 ≤ n → 0 ≤ a → 0 < eps → 1 / eps ≤ Real.sqrt n → 0 < δ →
    δ ≤ c0 / ((d : ℝ) * n) ^ 3 → c0 ≤ 7 / (3 * (8352 * Real.exp 2) ^ 2) →
    n * (4 * Real.exp 2 * a * (72 * d / eps) * (29 * d) * Real.sqrt (3 * δ / (7 * n))) ≤ a * Real.sqrt (d * n)

/-- Lemma S# step 6, the arithmetic: `(2 C_W d (1 + 10 L² n) L)^{1/2} a + 32 e² a d L³/ε + a (dn)^{1/2}
≤ C_# a (L^{3/2} (dn)^{1/2} + d L³/ε)` with `C_# = max((22 C_W)^{1/2} + 1, 32 e²)`. -/
def SSharpSumArith : Prop :=
  ∀ (d n L CW a eps : ℝ), 1 ≤ d → 1 ≤ n → 1 ≤ L → 0 ≤ CW → 0 ≤ a → 0 < eps →
    Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + 32 * Real.exp 2 * a * d * L ^ 3 / eps +
        a * Real.sqrt (d * n) ≤
      max (Real.sqrt (22 * CW) + 1) (32 * Real.exp 2) * a *
        (L ^ (3 / 2 : ℝ) * Real.sqrt (d * n) + d * L ^ 3 / eps)

/-- Lemma S# steps 2 and 5, the moment arithmetic: `d (d + 2)(d + 4)(d + 6) ≤ (d + 6)⁴` (`E|W|⁸ ≤ (d + 6)⁴`) and
`4 (d + 6) + 1 ≤ 29 d` for `d ≥ 1`. -/
def SSharpMomentArith : Prop :=
  ∀ d : ℝ, 1 ≤ d → d * (d + 2) * (d + 4) * (d + 6) ≤ (d + 6) ^ 4 ∧ 4 * (d + 6) + 1 ≤ 29 * d

/-- Lemma QM step 7 and Lemma S# step 6: `D_s = ζ_s - b_s` for `s < t` gives
`|Σ_{s < t} D_s| ≤ |Σ_{s < t} ζ_s| + Σ_{s < t} |b_s|`. -/
def SumDecomp : Prop :=
  ∀ (t : ℕ) (D z b : ℕ → ℝ), (∀ s, s < t → D s = z s - b s) →
    |∑ s ∈ Finset.range t, D s| ≤ |∑ s ∈ Finset.range t, z s| + ∑ s ∈ Finset.range t, |b s|

end AdversarialBco.Poly
