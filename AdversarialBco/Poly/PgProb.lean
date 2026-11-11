/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The probability of Procedure PG: definitions and generic interface statements

Interface of the generic probabilistic steps, which the analysis of
Procedure PG-core reads: the descent in expectation (Lemma SGD), the sampling bound of Lemma T (Chebyshev for an
average of independent copies of a vector), its amplification (Hoeffding for a majority vote), and the independence of
the rounds. The randomness is a sequence of independent samples of a probability measure `ν` (`Measure.infinitePi`;
a step that uses `n` samples reads the first `n` coordinates): this is how the procedure draws its Gaussian vectors,
one fresh sample per use.

* `sgdIter proj V s x1 ω t`: the iterates of projected stochastic descent driven by the samples `ω t`: `x_0 = x1`,
  `x_{t+1} = proj (x_t - s V(x_t, ω t))`; `sgdAvg` the average of `x_0, ..., x_{N-1}`.
* `SgdExpect` (Lemma SGD): on a compact convex set `D` of diameter at most `Δ`, with a nonexpansive projection
  `proj` onto `D`, `γ x` a subgradient of `h` at `x ∈ D`, an estimate `V x g` with `|E V(x, ·) - γ x| ≤ β` and
  `E |V(x, ·)|² ≤ G²` at every `x ∈ D`, and a minimiser `xs` of `h` on `D`:
  `E h(x̄) ≤ h(xs) + Δ²/(2 s N) + s G²/2 + β Δ`.
* `ChebAvg`: for `n` independent copies of a square-integrable vector `Φ(g)`, `P(|avg - E Φ| ≥ t) ≤ E|Φ|²/(n t²)`.
* `MajorityHoeffding`: if `ν(B) ≤ 1/4`, then among `m` independent samples, `P(#{i : ω i ∈ B} ≥ m/2) ≤ e^{-m/8}`.
* `RoundsAllMiss`: for independent rounds, `P(ω r ∈ A for all r < J) = ν(A)^J`.
* `RoundsSomeHit`: for independent rounds, `P(ω r ∈ B for some r < J) ≤ J ν(B)`.

Junk values. `sgdAvg` divides by `N`, read at `N ≥ 1`; `ChebAvg` divides by `n t²`, read at `n ≥ 1`, `t > 0`. The
integrals carry their integrability: `h` is continuous on the compact `D` (hence bounded there), `V x` and
`|V x|²` are integrable for `x ∈ D`, `Φ` is in `L²`.

Every statement is a `Prop`; the theorems that prove them are in `PgProbProof.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly

/-- The iterates of projected stochastic descent driven by the samples `ω t`: `x_0 = x1`,
`x_{t+1} = proj (x_t - s V(x_t, ω t))`. -/
def sgdIter {E G : Type*} [AddCommGroup E] [Module ℝ E] (proj : E → E) (V : E → G → E) (s : ℝ) (x1 : E)
    (ω : ℕ → G) : ℕ → E
  | 0 => x1
  | t + 1 => proj (sgdIter proj V s x1 ω t - s • V (sgdIter proj V s x1 ω t) (ω t))

/-- The average `x̄ = (1/N) ∑_{t < N} x_t` of the first `N` iterates. -/
noncomputable def sgdAvg {E G : Type*} [AddCommGroup E] [Module ℝ E] (proj : E → E) (V : E → G → E) (s : ℝ)
    (x1 : E) (N : ℕ) (ω : ℕ → G) : E :=
  (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, sgdIter proj V s x1 ω t

/-- Lemma SGD, in expectation over independent samples. -/
def SgdExpect : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    (D : Set E) (proj : E → E) (h : E → ℝ) (γ : E → E) (V : E → G → E) (xs x1 : E) (Δ s G2 β : ℝ) (N : ℕ),
    IsCompact D → Convex ℝ D → ContinuousOn h D → Continuous proj → (∀ y, proj y ∈ D) →
    (∀ y, ∀ z ∈ D, ‖proj y - z‖ ≤ ‖y - z‖) → Measurable (Function.uncurry V) → x1 ∈ D → xs ∈ D →
    (∀ y ∈ D, h xs ≤ h y) → (∀ y ∈ D, ∀ z ∈ D, ‖y - z‖ ≤ Δ) →
    (∀ x ∈ D, ∀ y ∈ D, h x + ⟪γ x, y - x⟫ ≤ h y) →
    (∀ x ∈ D, Integrable (V x) ν ∧ Integrable (fun g => ‖V x g‖ ^ 2) ν ∧ ‖∫ g, V x g ∂ν - γ x‖ ≤ β ∧
      ∫ g, ‖V x g‖ ^ 2 ∂ν ≤ G2) →
    0 < s → 1 ≤ N →
    ∫ ω, h (sgdAvg proj V s x1 N ω) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      h xs + Δ ^ 2 / (2 * s * N) + s * G2 / 2 + β * Δ

/-- Chebyshev's inequality for the average of `n` independent copies of a vector (Lemma T, sampling). -/
def ChebAvg : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (Φ : G → E),
    Measurable Φ → MemLp Φ 2 ν → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
    (Measure.infinitePi fun _ : ℕ => ν) {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) - ∫ g, Φ g ∂ν‖} ≤
      ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂ν) / (n * t ^ 2))

open Classical in
/-- Hoeffding's inequality for a majority vote (Lemma T, amplification). -/
def MajorityHoeffding : Prop :=
  ∀ (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (B : Set G), MeasurableSet B →
    ν B ≤ 1 / 4 → ∀ m : ℕ,
    (Measure.infinitePi fun _ : ℕ => ν) {ω | (m : ℝ) / 2 ≤ ((Finset.range m).filter fun i => ω i ∈ B).card} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) / 8))

/-- Independent rounds that all miss a set. -/
def RoundsAllMiss : Prop :=
  ∀ (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (A : Set G), MeasurableSet A →
    ∀ J : ℕ, (Measure.infinitePi fun _ : ℕ => ν) {ω | ∀ r < J, ω r ∈ A} = ν A ^ J

/-- Independent rounds, one of which hits a set. -/
def RoundsSomeHit : Prop :=
  ∀ (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (B : Set G), MeasurableSet B →
    ∀ J : ℕ, (Measure.infinitePi fun _ : ℕ => ν) {ω | ∃ r < J, ω r ∈ B} ≤ J * ν B

end AdversarialBco.Poly
