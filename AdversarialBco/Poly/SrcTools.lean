/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Freedman

@[expose] public section

/-!
# Probabilistic tools: definitions and interface statements

Interface of generic probabilistic bricks: the Gaussian tails, the tail of the noise, and Lemma U, Freedman's
inequality over a finite family, on top of `FreedmanFK` (`AdversarialBco/Poly/Freedman.lean`) and the union bound
(`AdversarialBco/Poly/Cover.lean`).

* `GaussTailT1`: `P(g ≥ b) ≤ e^{-b²/2}/2` and `P(|g| ≥ b) ≤ e^{-b²/2}` for `b ≥ 0`.
* `GaussTailT2`: `P(|W|² ≥ t) ≤ 2 e^{-3t/(8d)}` for a standard Gaussian vector `W` of `ℝ^d`, `d ≥ 1`.
* `NoiseTail`: `E exp(ε²) ≤ 2` gives `P(|ε| ≥ b) ≤ 2 e^{-b²}` for `b ≥ 0`.
* `LemmaU`: for a finite set `C` and martingale differences `Z c t` (`ℱ (t + 1)`-measurable, centred given `ℱ t`), with
  probability at least `1 - δ`, for all `c ∈ C` and `t ∈ [1, n]`, `|∑_{s < t} Z c s| ≤ fkBound`, the bound of Lemma FK
  with `l = log (4 n |C| max(1, κ R, κ V^{1/2}) / δ)`.

Indexing as in `Freedman.lean`: `Z c t` is the increment of round `t + 1`; the rounds `1, ..., t` are the indices
`s < t`, so `V_t(c) = predVar μ ℱ (Z c) t` and `R_t(c) = max_{s < t} |Z c s|`.

Junk values. The integrals are Bochner integrals, so every statement carries the integrability it reads (`Integrable`
of `exp (ε²)` for `NoiseTail`). `Real.log` is read at positive arguments (`δ > 0`, `n |C| ≥ 1` on the event,
`max 1 _ ≥ 1`); `3 / (8 d)` at `d ≥ 1`.

Every statement is a `Prop`; the theorems that prove them are in `SrcToolsProof.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

universe u

/-- The bound of Lemma FK at round `t`, with the logarithm `l = log (4 N max(1, κ R, κ V^{1/2}) / δ)`:
`3 (V l)^{1/2} + 2 max(1/κ, R) l`, where `V = predVar μ ℱ X t` and `max(1, κ R) = absMax (κ X) t`. -/
noncomputable def fkBound {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (κ N δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  3 * Real.sqrt (predVar μ ℱ X t ω * Real.log (4 * N * max (absMax (fun s ω => κ * X s ω) t ω)
      (κ * Real.sqrt (predVar μ ℱ X t ω)) / δ))
    + 2 * (absMax (fun s ω => κ * X s ω) t ω / κ) * Real.log (4 * N * max (absMax (fun s ω => κ * X s ω) t ω)
      (κ * Real.sqrt (predVar μ ℱ X t ω)) / δ)

/-- (T1) -/
def GaussTailT1 : Prop :=
  ∀ b : ℝ, 0 ≤ b →
    gaussianReal 0 1 (Set.Ici b) ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2) / 2) ∧
      gaussianReal 0 1 {x | b ≤ |x|} ≤ ENNReal.ofReal (Real.exp (-b ^ 2 / 2))

/-- (T2) -/
def GaussTailT2 : Prop :=
  ∀ (d : ℕ) (t : ℝ), 1 ≤ d →
    stdGaussian (EuclideanSpace ℝ (Fin d)) {W | t ≤ ‖W‖ ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-(3 * t / (8 * d))))

/-- The tail of the noise (the conditional hypothesis `E[exp(ε²) | X] ≤ 2` gives the
unconditional one by the tower property). -/
def NoiseTail : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Ω → ℝ),
    AEMeasurable ε μ → Integrable (fun ω => Real.exp (ε ω ^ 2)) μ → ∫ ω, Real.exp (ε ω ^ 2) ∂μ ≤ 2 →
    ∀ b : ℝ, 0 ≤ b → μ {ω | b ≤ |ε ω|} ≤ ENNReal.ofReal (2 * Real.exp (-b ^ 2))

/-- Lemma U: Lemma FK for each `c ∈ C` and each `t ∈ [1, n]`, with the union. -/
def LemmaU : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {ι : Type} (C : Finset ι) (Z : ι → ℕ → Ω → ℝ),
    (∀ c ∈ C, ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z c t)) → (∀ c ∈ C, ∀ t, Integrable (Z c t) μ) →
    (∀ c ∈ C, ∀ t, Integrable (fun ω => Z c t ω ^ 2) μ) → (∀ c ∈ C, ∀ t, μ[Z c t | ℱ t] =ᵐ[μ] 0) →
    ∀ (n : ℕ) (κ δ : ℝ), 0 < κ → 0 < δ → δ ≤ 1 →
    μ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
      fkBound μ ℱ (Z c) κ (n * C.card) δ t ω < |∑ s ∈ Finset.range t, Z c s ω|} ≤ ENNReal.ofReal δ

end AdversarialBco.Poly
