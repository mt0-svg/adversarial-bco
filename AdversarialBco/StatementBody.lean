/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Frozen statements: Theorem 3.1 for every family, Proposition 2.2 with its constant

The statements of the paper formalized here, as `Prop` definitions; the theorems proving them live in
other modules, and the Comparator challenge `AdversarialBco.ChallengeBody` copies this file with the three theorems
`dilTheorem`, `bodyExplicit` and `bodyHExplicit` stated with `sorry`. The file imports only Mathlib.

* `E d = EuclideanSpace ℝ (Fin d)`, written out (the abbreviation `AdversarialBco.E` of `Statement.lean` is not
  imported, so that this file stands alone).
* Gaussian constants of Section 3: `phi` is the standard Gaussian density, `Qtail t = ∫_t^∞ phi` its upper tail,
  `kappa = phi 0 - phi 1 + Qtail 1`, `kappa2 = 1 - Qtail 1 - phi 1`, `KS = 2 (32/kappa)^2 (13/4 + 2 kappa2)` and
  `KD = 1.6 * 10^6`, the constants of Theorem 3.1.
* A family (Section 3.1): weights `w c > 0` with sum `1`, convex `L`-Lipschitz functions `F c` on `ℝ^d`, each
  attaining its minimum at `xmin c`, whose mean `Fbar = ∑ w c F c` is coercive (`Fbar x ≥ a1 ‖x‖ - a2`, `a1 > 0`).
  `V x = ∑ w c (F c x - Fbar x)^2`; the floor is `Δ* = min Fbar - ∑ w c min F c`, with `min Fbar = Fbar bstar` for a
  minimiser `bstar`; for a law `p`, `Δ p = ∫ Fbar dp - ∑ w c min F c` and `I p = ∫ V dp`.
* The entropic objective `E_λ(b, S) = E Fbar(b + S Z) - λ log det S`, `Z` a standard Gaussian vector of `ℝ^d`, over
  `b ∈ ℝ^d` and `S` symmetric positive definite (`IsSPD`: self-adjoint with `⟪S v, v⟫ > 0` for `v ≠ 0`). An entropic
  Gaussian of `Fbar` at temperature `λ` is a minimiser (`IsEntropicGaussian`); Lemma 3.2 says it exists and is unique,
  and `DilTheorem` asserts the existence at the temperature it uses and its conclusions for every minimiser.
* `N(b, S^2)` is the law of `b + S Z` (`gaussLaw`), and `p_h = (1 - q) δ_{b*} + (q/2) δ_{b_h} + (q/2) N(b_h, A_h)`
  (`dilutedLaw`).
* The largest eigenvalue `s_h` of the symmetric positive definite `S_h` is its operator norm `‖S_h‖`.
* `lnp x = max (log x) 0`.
* `HypH J L lo hi α β`: hypothesis (H)[α, β] (Section 2) on the class of convex functions `J → [lo, hi]` with
  `|f x - f y| ≤ L |x - y|` on `J`; `F(J, n)` is the case `L = n`, `lo = 0`, `hi = 1`. Its body is that of
  `AdversarialBco.HypH` (`Lemmas.lean`) word for word, so the two are equivalent by `Iff.rfl`.

Junk values. Every division has a positive denominator under the hypotheses: `h ≥ Δ*/2 > 0`, `Δ* > 0`, and
`gmax = ⨆ c, g c ≥ ∑ w c g c = Δ*` (the index type is nonempty and finite since the weights sum to `1`), so the
logarithm `log (2 gmax / Δ*)` is at least `log 2 > 0`. `det S > 0` for `S` positive definite. `q = Δ*/(4h)` lies in
`(0, 1/2]`, so the weights of `dilutedLaw` are the real ones. In Proposition 2.2, `diam J ≥ 1` since `J` contains a
closed ball of radius `1/2` and is bounded, so `log (n d diam J) ≥ log 2`; in the interface `D ≥ diam K ≥ 2`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.BodySpec

/-- The standard Gaussian density on `ℝ`. -/
noncomputable def phi (t : ℝ) : ℝ := Real.exp (-(t ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- The upper tail `Q t = ∫_t^∞ phi` of the standard Gaussian law. -/
noncomputable def Qtail (t : ℝ) : ℝ := ∫ s in Set.Ioi t, phi s

/-- `κ = φ(0) - φ(1) + Q(1)` (Section 3.2; it equals `E min(Z_1^+, 1)`). -/
noncomputable def kappa : ℝ := phi 0 - phi 1 + Qtail 1

/-- `κ_2 = 1 - Q(1) - φ(1)` (Lemma 3.3). -/
noncomputable def kappa2 : ℝ := 1 - Qtail 1 - phi 1

/-- `K_S = 2 (32/κ)^2 (13/4 + 2 κ_2)` (Theorem 3.1). -/
noncomputable def KS : ℝ := 2 * (32 / kappa) ^ 2 * (13 / 4 + 2 * kappa2)

/-- `K_D = 1.6 * 10^6` (Theorem 3.1). -/
noncomputable def KD : ℝ := 16 * 10 ^ 5

/-- `ln⁺ x = max (ln x) 0`. -/
noncomputable def lnp (x : ℝ) : ℝ := max (Real.log x) 0

/-- The mean `Fbar x = ∑ w c F c x` of a family. -/
def mean {d k : ℕ} (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  ∑ c, w c * F c x

/-- The variance `V x = ∑ w c (F c x - Fbar x)^2` of a family at `x`. -/
def var {d k : ℕ} (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  ∑ c, w c * (F c x - mean w F x) ^ 2

/-- `S` is symmetric positive definite. -/
def IsSPD {d : ℕ} (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  IsSelfAdjoint S ∧ ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 → 0 < ⟪S v, v⟫

/-- The entropic objective `E_λ(b, S) = E G(b + S Z) - λ log det S`, `Z` a standard Gaussian vector of `ℝ^d`. -/
noncomputable def entropic {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, G (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) -
    lam * Real.log (LinearMap.det (S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))

/-- `(b, S)` is an entropic Gaussian of `G` at temperature `lam`: a minimiser of `E_lam` over `b ∈ ℝ^d` and `S`
symmetric positive definite. -/
def IsEntropicGaussian {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ) (lam : ℝ) (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  IsSPD S ∧ ∀ (b' : EuclideanSpace ℝ (Fin d)) (S' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    IsSPD S' → entropic G lam b S ≤ entropic G lam b' S'

/-- The Gaussian law `N(b, S^2)`: the law of `b + S Z`. -/
noncomputable def gaussLaw {d : ℕ} (b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => b + S z)

/-- The diluted law `(1 - q) δ_{bstar} + (q/2) δ_b + (q/2) N(b, S^2)`. -/
noncomputable def dilutedLaw {d : ℕ} (q : ℝ) (bstar b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ENNReal.ofReal (1 - q) • Measure.dirac bstar + ENNReal.ofReal (q / 2) • Measure.dirac b +
    ENNReal.ofReal (q / 2) • gaussLaw b S

/-- **Theorem 3.1**, for every family. For a family with floor `Δ* > 0` and a minimiser `bstar` of its
mean, with gains `g c = F c bstar - min F c` and `gmax = max g c`, there is a scale `h ∈ [Δ*/2, gmax]`, one of the
gains, such that the entropic Gaussian of the mean at temperature `h/(16 d)` exists and every such `(b_h, S_h)`, with
`T_h = (2 ln⁺(26 d L s_h / h))^{1/2}`, `q = Δ*/(4h)` and `p_h` the diluted law, has `Δ(p_h) ≤ (65/64) Δ*`, the bound
(P3) and `Δ(p_h)^2 ≤ K_D (1 + T_h)^2 d^2 ln(2 gmax/Δ*) I(p_h)`. -/
def DilTheorem : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (k : ℕ) (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (xmin : Fin k → EuclideanSpace ℝ (Fin d)) (a1 a2 : ℝ) (bstar : EuclideanSpace ℝ (Fin d)),
    (∀ c, 0 < w c) → ∑ c, w c = 1 →
    (∀ c, ConvexOn ℝ Set.univ (F c)) → (∀ c, LipschitzWith L (F c)) →
    (∀ c y, F c (xmin c) ≤ F c y) →
    0 < a1 → (∀ x, a1 * ‖x‖ - a2 ≤ mean w F x) →
    (∀ y, mean w F bstar ≤ mean w F y) →
    0 < mean w F bstar - ∑ c, w c * F c (xmin c) →
    ∃ h : ℝ, (mean w F bstar - ∑ c, w c * F c (xmin c)) / 2 ≤ h ∧ h ≤ ⨆ c, (F c bstar - F c (xmin c)) ∧
      (∃ c, h = F c bstar - F c (xmin c)) ∧
      (∃ b S, IsEntropicGaussian (mean w F) (h / (16 * d)) b S) ∧
      ∀ b S, IsEntropicGaussian (mean w F) (h / (16 * d)) b S →
        let Δs := mean w F bstar - ∑ c, w c * F c (xmin c)
        let gmax := ⨆ c, (F c bstar - F c (xmin c))
        let T := Real.sqrt (2 * lnp (26 * d * L * ‖S‖ / h))
        let p := dilutedLaw (Δs / (4 * h)) bstar b S
        let Δp := ∫ x, mean w F x ∂p - ∑ c, w c * F c (xmin c)
        Δp ≤ 65 / 64 * Δs ∧
        h * Δs / (2 * KS * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs)) ≤
          var w F bstar + var w F b + ∫ z, var w F (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
        Δp ^ 2 ≤ KD * (1 + T) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * gmax / Δs) * ∫ x, var w F x ∂p

/-- Hypothesis (H)[α, β] on the class of convex functions `J → [lo, hi]` that are `L`-Lipschitz on `J`: for every
finitely supported law on the class (weights `w`, functions `F`) some probability law `ρ` carried by `J`, under which
the functions are integrable, has `E_ρ Fbar - E_w min_J F ≤ α + (β E_ρ E_w (Fbar - F)^2)^{1/2}`. -/
def HypH {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (L lo hi α β : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → ℝ) (F : Fin k → EuclideanSpace ℝ (Fin d) → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
    (∀ i, ConvexOn ℝ J (F i) ∧ (∀ x ∈ J, ∀ y ∈ J, |F i x - F i y| ≤ L * dist x y) ∧
      ∀ x ∈ J, F i x ∈ Set.Icc lo hi) →
    ∃ ρ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure ρ ∧ ρ Jᶜ = 0 ∧ (∀ i, Integrable (F i) ρ) ∧
      ∫ x, ∑ i, w i * F i x ∂ρ - ∑ i, w i * sInf (F i '' J) ≤
        α + √(β * ∫ x, ∑ i, w i * ((∑ j, w j * F j x) - F i x) ^ 2 ∂ρ)

/-- **Proposition 2.2** with `C_0 = 1.2 * 10^9`: for `n ≥ 2` and a convex body `J ⊆ ℝ^d` containing a
ball of radius `1/2`, the class `F(J, n)` satisfies (H)[1/n, β] with `β = C_0 d^2 ln(n d diam J) ln(2n)`. -/
def BodyExplicit : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ J : Set (EuclideanSpace ℝ (Fin d)), IsCompact J → Convex ℝ J →
    (∃ c, Metric.closedBall c (1 / 2) ⊆ J) →
      HypH J n 0 1 (1 / n) (1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * Metric.diam J) * Real.log (2 * n))

/-- The form that Theorem 1.5 and Corollary 1.6 use: (H)[1/n, 1.2 * 10^9 d^2 ln(n d D) ln(2n)] on the inner body
`{y | closedBall y (1/n) ⊆ K}` of a convex body `K` containing a unit ball, for every `D ≥ diam K` (Proposition 2.2
on the body `J` of Lemma 2.1). -/
def BodyHExplicit : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
    ∀ c : EuclideanSpace ℝ (Fin d), Metric.closedBall c 1 ⊆ K → ∀ D : ℝ, Metric.diam K ≤ D →
      HypH {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} n 0 1 (1 / n)
        (1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n))

end AdversarialBco.BodySpec
