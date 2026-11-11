/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# DF2: the interface of the analysis, first layer

Interface statements of the lemmas that read the run only through quantities given as hypotheses: the
deterministic lemmas, the lemmas "on the events" with the events written as hypotheses on arbitrary data, the
identities of the play `p'`, and the assembly with the trivial bound outside the regime. Lemma D.2 is in `Df2R1.lean`;
Lemma D.14 (Lemma DF2-W is its instance) is `LemmaW` of `Wrapper.lean`. The learner itself, its events and the readings
of the source (Lemmas S-DF, DQ, LQ, LD, the closure, the guard, Lemma D.17 with Lemma D.16) form the second layer,
the machine layer.

Carriers. The region, the test and the online Newton inequality (`df2Sq` to `LemmaONS2Core`) work on `Fin d → ℝ` with
matrices and `|v|²_P = v ⬝ᵥ (P *ᵥ v)` (`df2Sq`), as `Df2R1.lean`; the centre of the test and the play (`LemmaZCore`,
`df2Surr` to `PlayHess`) work on `EuclideanSpace ℝ (Fin d)` with continuous linear maps, as the frozen statement
(`E d`) and `PosGauss.lean`. `Df2Carriers` states the passage. The Gaussian laws are images of `stdGaussian` on
`EuclideanSpace ℝ (Fin d)` by an affine map with the factor `A` (`A Aᵀ = Σ`: no matrix square root).

* `df2C0`: the constant `C₀` of `L = C₀ log (1/δ)`, a single definition read by `Df2RowZ`; the other constants are
  defined in the second layer, next to the statements that read them. The lemmas below are stated for general levels.
* `LemmaDFI`: the midpoint identity of a quadratic and its two-level consequence.
* `LemmaMON`: `Φ_u ≤ Φ_t + 2 dev'` on `S_t ∩ B_R`, `u ≤ t ≤ τ`, on the event of Lemma DQ.
* `PropINC2`: the single region lies in every past ellipsoid, by the segment argument.
* `LemmaD2`: the dichotomy at general levels.
* `LemmaONS2Core`: the online Newton inequality without the last projection, telescoped, with the defects of
  the projection of DF2-O (Lemma RB2).
* `LemmaZCore`: the centre of the test from the three bounds of its proof; `Df2RowZ` its numerical row.
* `PlayShift`, `LemmaUBPrime`, `PlayHess`: the identities of the play `p'`; the gradient and the
  Hessian of the surrogate at every point.
* `Df2Trivial` (Step result item 8): outside the regime `n ≥ 4 C_ε² d³ L^10` the trivial bound `n` is at most
  `2 C_ε d^{3/2} L^5 n^{1/2}`.
* `Df2Carriers`: the two carriers, through `WithLp.toLp 2` and `Matrix.toEuclideanCLM`.

Deterministic pieces of the route stated in the second layer, next to the quantities they read: the identity of the
test (`Ξ_t = η T̂_t - 2 Φ₀` at `κ = 1/4`, `Ξ_t(y) = Ξ_t(z_t) - |y - z_t|²_{P_{t+1}}`, and the passage from
the accuracy `min (1, αρ/2) = 1` of AP to `αρ` on `Ξ_t`); the scalar facts `a_t ≥ 1/2` and `q_t ≥ 1/4`, with Lemma D.2; the
reduction in Lemma D.13 (`R⁻_t ⊆ R_{s+1}` for `s < t`, by `LemmaMON` and the margin row); the two halves of (W3);
the rows at the constants `κ`, `θ`, `α`, `c₁`, `γ`, `C_g`, `C_ε/C_λ`, and the conditions on `δ`,
under the regime hypothesis, `Df2Trivial` covering its complement. The smoothing limit `s_ϱ'' → s''`, uniform in `z`, is in the second layer; it reads `LemmaUBPrime`
for `e_t` and for `e_ϱ` and `PlayHess` for `e_ϱ`.

Junk values. `df2Sq` has no division. `LemmaD2` divides by nothing (`r` is given with its defining identity).
`PlayShift`, `LemmaUBPrime`, `PlayHess` divide by `λ` and `1 - λ`: they assume `0 < λ < 1`. The integrals are Bochner
integrals: `LemmaUBPrime` takes `e` measurable of linear growth, `PlayHess` takes `e` of class `C²` with bounded second
derivative; both conclude that the surrogate is of class `C²`, so that their `fderiv` are the true derivatives.
`Df2Trivial` reads `Real.sqrt` of nonnegative numbers only.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix RealInnerProductSpace

namespace AdversarialBco.Poly

/-! ## Constants -/

/-- `C₀ = 36`, `L = C₀ log (1/δ)`. -/
noncomputable def df2C0 : ℝ := 36

/-! ## Quadratics -/

/-- `|v|²_P = vᵀ P v`. -/
def df2Sq {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ := v ⬝ᵥ (P *ᵥ v)

/-- The quadratic `k + ⟨b, y⟩ + ½ yᵀ P y`, of Hessian `P`. -/
noncomputable def df2Quad {d : ℕ} (k : ℝ) (b : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) : ℝ :=
  k + b ⬝ᵥ y + (1 / 2) * df2Sq P y

/-- Lemma DF-I: `Φ(y) + Φ(y') - 2 Φ((y + y')/2) = |y - y'|²_P / 4`, so `Φ(y) ≤ c`, `Φ(y') ≤ c'` and
`Φ((y + y')/2) ≥ -e` give `|y - y'|²_P ≤ 4 (c + c' + 2 e)`. -/
def LemmaDFI : Prop :=
  ∀ (d : ℕ) (k : ℝ) (b : Fin d → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (y y' : Fin d → ℝ),
    df2Quad k b P y + df2Quad k b P y' - 2 * df2Quad k b P ((1 / 2 : ℝ) • (y + y')) = df2Sq P (y - y') / 4 ∧
      ∀ c c' e : ℝ, df2Quad k b P y ≤ c → df2Quad k b P y' ≤ c' → -e ≤ df2Quad k b P ((1 / 2 : ℝ) • (y + y')) →
        df2Sq P (y - y') ≤ 4 * (c + c' + 2 * e)

/-! ## The region -/

/-- Lemma D.7. `Φ_t = Φ₀ + Ω̂_t`; the true bonus `Ω_t` is nondecreasing in `t`; the event of Lemma DQ:
`|Ω̂_t - Ω_t| ≤ dev'` on `S_t ∩ B_R` for `t ≤ τ`; the sets `S_t` decrease. Then `Φ_u ≤ Φ_t + 2 dev'` on `S_t ∩ B_R`
for `u ≤ t ≤ τ`. -/
def LemmaMON : Prop :=
  ∀ (d : ℕ) (Φ0 : (Fin d → ℝ) → ℝ) (Ω Ωh : ℕ → (Fin d → ℝ) → ℝ) (S : ℕ → Set (Fin d → ℝ))
    (BR : Set (Fin d → ℝ)) (τ : ℕ) (dev' : ℝ),
    (∀ u t, u ≤ t → S t ⊆ S u) → (∀ u t y, u ≤ t → Ω u y ≤ Ω t y) →
    (∀ t ≤ τ, ∀ y ∈ S t ∩ BR, |Ωh t y - Ω t y| ≤ dev') →
    ∀ u t, u ≤ t → t ≤ τ → ∀ y ∈ S t ∩ BR, Φ0 y + Ωh u y ≤ Φ0 y + Ωh t y + 2 * dev'

/-- The past ellipsoids `S_t = ⋂_{1 ≤ s ≤ t} {y : |y - μ_s|²_{P_s} ≤ r}` (`r = 1/(2 L λ²)`). -/
def df2S {d : ℕ} (μ : ℕ → Fin d → ℝ) (P : ℕ → Matrix (Fin d) (Fin d) ℝ) (r : ℝ) (t : ℕ) : Set (Fin d → ℝ) :=
  {y | ∀ s, 1 ≤ s → s ≤ t → df2Sq (P s) (y - μ s) ≤ r}

/-- The region `R_u = {y ∈ K_ε : Φ_{u-1}(y) ≤ c}` (`c = c₁ ρ`). -/
def df2R {d : ℕ} (Keps : Set (Fin d → ℝ)) (Φ : ℕ → (Fin d → ℝ) → ℝ) (c : ℝ) (u : ℕ) : Set (Fin d → ℝ) :=
  {y | y ∈ Keps ∧ Φ (u - 1) y ≤ c}

/-- Proposition D.8. The data of the rounds `1, ..., τ`: centres `μ_s`, precisions `P_s` (positive definite,
`s ≤ τ`), quadratics `Φ_t = Φ₀ + Ω̂_t` of Hessian `P_{t+1}` (`t + 1 ≤ τ`) whose new term vanishes at `μ_t`
(`Φ_t(μ_t) = Φ_{t-1}(μ_t)`),
`Φ₀ ≥ 0`, `Φ₀ ≤ pri` on `K_ε` and `|y - μ₁|²_{P₁} ≤ 2 pri` there, `μ₁ ∈ K_ε` with `(Φ₀ + Ω̂₀)(μ₁) = 0`; `μ_u ∈ R_u` whenever
`R_u` is nonempty (the projection); the true bonus `Ω_t ≥ 0`, nondecreasing; the event of Lemma DQ on `S_t ∩ B_R`; the
strict row `8 (c₁ ρ + 2 dev') < r` and `pri ≤ ρ`. Then for `1 ≤ u ≤ τ`: (a_u) `μ_u ∈ R_u`; (b_u) every `y ∈ R_u` has
`|y - μ_s|²_{P_s} ≤ 8 (c₁ ρ + 2 dev')` for `1 ≤ s ≤ u`. -/
def PropINC2 : Prop :=
  ∀ (d : ℕ) (Keps BR : Set (Fin d → ℝ)) (μ : ℕ → Fin d → ℝ) (P : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (Φ0 : (Fin d → ℝ) → ℝ) (Ω Ωh : ℕ → (Fin d → ℝ) → ℝ) (τ : ℕ) (c1 ρ dev' pri r : ℝ),
    Convex ℝ Keps → IsClosed Keps → Keps ⊆ BR →
    (∀ s, 1 ≤ s → s ≤ τ → (P s).PosDef) →
    (∀ t, t + 1 ≤ τ → ∃ k b, (fun y => Φ0 y + Ωh t y) = df2Quad k b (P (t + 1))) →
    (∀ t, 1 ≤ t → t ≤ τ → Φ0 (μ t) + Ωh t (μ t) = Φ0 (μ t) + Ωh (t - 1) (μ t)) →
    (∀ y, 0 ≤ Φ0 y) → (∀ y ∈ Keps, Φ0 y ≤ pri ∧ df2Sq (P 1) (y - μ 1) ≤ 2 * pri) →
    μ 1 ∈ Keps → Φ0 (μ 1) + Ωh 0 (μ 1) = 0 →
    (∀ u, 2 ≤ u → u ≤ τ → (df2R Keps (fun t y => Φ0 y + Ωh t y) (c1 * ρ) u).Nonempty →
      μ u ∈ df2R Keps (fun t y => Φ0 y + Ωh t y) (c1 * ρ) u) →
    (∀ t y, 0 ≤ Ω t y) → (∀ u t y, u ≤ t → Ω u y ≤ Ω t y) →
    (∀ t ≤ τ, ∀ y ∈ df2S μ P r t ∩ BR, |Ωh t y - Ω t y| ≤ dev') →
    0 ≤ dev' → 0 ≤ ρ → 1 ≤ c1 → pri ≤ ρ → 8 * (c1 * ρ + 2 * dev') < r →
    ∀ u, 1 ≤ u → u ≤ τ →
      μ u ∈ df2R Keps (fun t y => Φ0 y + Ωh t y) (c1 * ρ) u ∧
        ∀ y ∈ df2R Keps (fun t y => Φ0 y + Ωh t y) (c1 * ρ) u, ∀ s, 1 ≤ s → s ≤ u →
          df2Sq (P s) (y - μ s) ≤ 8 * (c1 * ρ + 2 * dev')

/-! ## The test -/

/-- Lemma D.10, the dichotomy at general levels. `m` is a number with `sup_Q Ξ - e ≤ m ≤ sup_Q Ξ`, written as
`Ξ ≤ m + e` on `Q` and `m ≤ b` for every upper bound `b` of `Ξ` on `Q`; the test fires when `m ≤ -h`.
(s) A fire gives `η sReg ≤ -(h - e) + π₀ + η dev + η ν` on `Q`. (c) `η sReg ≤ -k_c` on `Q`, with
`k_c = (1 + r) h + r ρ'' + (1 + r) η dev + η ν`, gives a fire. -/
def LemmaD2 : Prop :=
  ∀ (α : Type) (Q : Set α) (sReg T Th W Ξ : α → ℝ) (κ a cup r η ν dev ρ'' π0 h e m : ℝ),
    κ < a → a < cup → r * (a - κ) = cup - a → 0 < η → 0 < h → 0 ≤ e →
    (∀ y ∈ Q, sReg y ≤ T y + ν) →
    (∀ y ∈ Q, T y ≤ sReg y + (cup - a) / 2 * W y + ν) →
    (∀ y ∈ Q, η * T y ≤ ρ'' - (a - κ) / 2 * η * W y) →
    (∀ y ∈ Q, |Th y - T y| ≤ dev) →
    (∀ y ∈ Q, η * Th y - π0 ≤ Ξ y ∧ Ξ y ≤ η * Th y) →
    (∀ y ∈ Q, Ξ y ≤ m + e) → (∀ b, (∀ y ∈ Q, Ξ y ≤ b) → m ≤ b) →
    (m ≤ -h → ∀ y ∈ Q, η * sReg y ≤ -(h - e) + π0 + η * dev + η * ν) ∧
      ((∀ y ∈ Q, η * sReg y ≤ -((1 + r) * h + r * ρ'' + (1 + r) * η * dev + η * ν)) → m ≤ -h)

/-! ## The online Newton inequality -/

/-- Lemma D.13, the deterministic core. Rounds `s = 1, ..., t`, `t ≥ 1`: `P_{s+1} = P_s + η H_s` with `P_{s+1}`
positive definite and `Σ_{s+1} P_{s+1} = 1`; `w_s = μ_s - η Σ_{s+1} ĝ_s`; the comparator `y` satisfies the Pythagorean
inequality with defect `e_s` (`ep s`), `½ |μ_{s+1} - y|²_{P_{s+1}} ≤ ½ |w_s - y|²_{P_{s+1}} + e_s` for `s < t` (the projection
with defects of DF2-O on a convex set containing `y`; `e = 0` is the exact projection). Then, with
`q̂_s(y) = ⟨ĝ_s, y - μ_s⟩ + ½ |y - μ_s|²_{H_s}`,
`η Σ_{s ≤ t} (q̂_s(μ_s) - q̂_s(y)) ≤ ½ |μ₁ - y|²_{P₁} + Σ_{s < t} e_s + (η²/2) Σ_{s ≤ t} |ĝ_s|²_{Σ_{s+1}}`. -/
def LemmaONS2Core : Prop :=
  ∀ (d : ℕ) (P S H : ℕ → Matrix (Fin d) (Fin d) ℝ) (μ g : ℕ → Fin d → ℝ) (ep : ℕ → ℝ) (η : ℝ) (t : ℕ)
    (y : Fin d → ℝ), 1 ≤ t →
    (∀ s, 1 ≤ s → s ≤ t → P (s + 1) = P s + η • H s) →
    (∀ s, 1 ≤ s → s ≤ t → (P (s + 1)).PosDef ∧ S (s + 1) * P (s + 1) = 1) →
    (∀ s, 1 ≤ s → s < t →
      df2Sq (P (s + 1)) (μ (s + 1) - y) ≤ df2Sq (P (s + 1)) (μ s - η • (S (s + 1) *ᵥ g s) - y) + 2 * ep s) →
    η * ∑ s ∈ Finset.Icc 1 t, (g s ⬝ᵥ (μ s - y) - (1 / 2) * df2Sq (H s) (y - μ s)) ≤
      (1 / 2) * df2Sq (P 1) (μ 1 - y) + ∑ s ∈ Finset.Ico 1 t, ep s +
        η ^ 2 / 2 * ∑ s ∈ Finset.Icc 1 t, df2Sq (S (s + 1)) (g s)

/-! ## The centre of the test -/

/-- Lemma D.18, the step that closes it: `z = Σ (b - (η/2) Ĝ)` with `‖Σ v‖ ≤ ‖v‖/δ`, `‖b‖ ≤ R/(4 δ²)` and
`(η/2) ‖Ĝ‖ ≤ (3/4) R/δ²` has `‖z‖ ≤ R/δ³`. Norms are Euclidean (`EuclideanSpace`). -/
def LemmaZCore : Prop :=
  ∀ (d : ℕ) (Sg : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (b G : EuclideanSpace ℝ (Fin d))
    (η R δ : ℝ), 0 < δ → (∀ v, ‖Sg v‖ ≤ ‖v‖ / δ) → ‖b‖ ≤ R / (4 * δ ^ 2) → η / 2 * ‖G‖ ≤ 3 / 4 * R / δ ^ 2 →
    0 ≤ η → ‖Sg (b - (η / 2) • G)‖ ≤ R / δ ^ 3

/-- The row of Lemma D.18: `(1/4) κ₀^{1/2} C₀ (32/9)^{1/2} δ^{3/2} n^{3/2} d^{1/2} x^{3/2} ≤ 3/4` at `δ = e^{-x}`,
`x ≥ 14 + 3 log (d n)` (`δ ≤ e^{-14} (d n)^{-3}`), `κ₀ ≤ 4`. -/
def Df2RowZ : Prop :=
  ∀ (d n : ℕ) (x κ0 : ℝ), 1 ≤ d → 1 ≤ n → 14 + 3 * Real.log (d * n) ≤ x → 0 ≤ κ0 → κ0 ≤ 4 →
    1 / 4 * Real.sqrt κ0 * df2C0 * Real.sqrt (32 / 9) * Real.exp (-x) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
      Real.sqrt d * x ^ ((3 : ℝ) / 2) ≤ 3 / 4

/-! ## The play `p'` -/

/-- The surrogate at the law `p = N(μ, A Aᵀ)`, as an integral over the standard Gaussian:
`s(z) = (1 - 1/λ) E e(μ + A g) + (1/λ) E e((1 - λ)(μ + A g) + λ z)`. -/
noncomputable def df2Surr {d : ℕ} (e : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 - 1 / lam) * ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) +
    1 / lam * ∫ g, e ((1 - lam) • (μ + A g) + lam • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The play `p' = N(μ, (1 - λ)² A Aᵀ)` and the identity
`E_{p'} e - s(μ) = (1 - λ)(E_p e - s(μ))`, with `E_{p'} e = E e(μ + (1 - λ) A g)`. -/
def PlayShift : Prop :=
  ∀ (d : ℕ) (e : EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam : ℝ), 0 < lam → lam < 1 →
    ∫ g, e (μ + (1 - lam) • A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - df2Surr e μ A lam μ =
      (1 - lam) * (∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - df2Surr e μ A lam μ)

/-- Lemma D.3, at every point. For `e` measurable of linear growth, `|e y| ≤ B (1 + ‖y‖)` (the class of the
extension `e_t`), `A` invertible with `P = (A Aᵀ)⁻¹` (`Pm`, as a continuous linear map,
`Pm ∘ A ∘ Aᵀ = 1`), `κ₀ = (1 - λ)^{-2}` and `X_z = (1 - λ)(μ + A g) + λ z`: the surrogate is of class `C²`, and at
every `z` its gradient is `v ↦ E[κ₀ e(X_z) ⟨P (1 - λ) A g, v⟩]` and its Hessian is
`(w, v) ↦ λ E[κ₀ e(X_z) (κ₀ ⟨P (1 - λ) A g, v⟩ ⟨P (1 - λ) A g, w⟩ - ⟨P v, w⟩)]`. Here `X_z - m_z = (1 - λ) A g` with
`m_z = (1 - λ) μ + λ z`, the mean of `X_z`; Lemma D.3 (Lemma D.3 of the paper) is the case `z = μ`, where `X_μ = μ + (1 - λ) A g`. -/
def LemmaUBPrime : Prop :=
  ∀ (d : ℕ) (e : EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A Pm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam B : ℝ),
    0 < lam → lam < 1 → Measurable e → (∀ y, |e y| ≤ B * (1 + ‖y‖)) →
    Pm.comp (A.comp (ContinuousLinearMap.adjoint A)) = ContinuousLinearMap.id ℝ _ →
    ContDiff ℝ 2 (df2Surr e μ A lam) ∧
      ∀ z v w : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (df2Surr e μ A lam) z v =
            ∫ g, ((1 - lam) ^ 2)⁻¹ * e ((1 - lam) • (μ + A g) + lam • z) * ⟪Pm ((1 - lam) • A g), v⟫
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
          fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) z w v =
            lam * ∫ g, ((1 - lam) ^ 2)⁻¹ * e ((1 - lam) • (μ + A g) + lam • z) *
                (((1 - lam) ^ 2)⁻¹ * ⟪Pm ((1 - lam) • A g), v⟫ * ⟪Pm ((1 - lam) • A g), w⟫ - ⟪Pm v, w⟫)
              ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The Hessian identity, at every point: for `e` of class `C²` with bounded second derivative (and so of at
most quadratic growth), the surrogate is of class `C²` and `s''(z) = λ E e''(X_z)`, `X_z = (1 - λ)(μ + A g) + λ z`; at
`z = μ` this is `s''(μ) = λ E_{p'} e''`. -/
def PlayHess : Prop :=
  ∀ (d : ℕ) (e : EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (lam B : ℝ),
    0 < lam → lam < 1 → ContDiff ℝ 2 e → (∀ y, ‖fderiv ℝ (fderiv ℝ e) y‖ ≤ B) →
    ContDiff ℝ 2 (df2Surr e μ A lam) ∧
      ∀ z v w : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) z w v =
          lam * ∫ g, fderiv ℝ (fderiv ℝ e) ((1 - lam) • (μ + A g) + lam • z) w v
            ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-! ## The regime (Step result item 8) -/

/-- Outside the regime: `n < 4 C_ε² d³ L^{10}` gives `n ≤ 2 C_ε d^{3/2} L^5 n^{1/2}`, so the trivial bound `Reg_n ≤ n`
(losses in `[0, 1]`) is within the bound of the theorem there. -/
def Df2Trivial : Prop :=
  ∀ (d n Ceps L : ℝ), 1 ≤ d → 1 ≤ n → 0 < Ceps → 0 < L → n < 4 * Ceps ^ 2 * d ^ 3 * L ^ 10 →
    n ≤ 2 * Ceps * d ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n

/-! ## The two carriers -/

/-- The passage between the carriers `Fin d → ℝ` with matrices and `EuclideanSpace ℝ (Fin d)` with continuous linear
maps, through `WithLp.toLp 2` and `Matrix.toEuclideanCLM`: the form `df2Sq`, the action, the product, the transpose
(the adjoint), the norm, and the convexity and the closedness of the preimage of a set. -/
def Df2Carriers : Prop :=
  ∀ (d : ℕ) (P Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (K : Set (EuclideanSpace ℝ (Fin d))),
    df2Sq P v = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P (WithLp.toLp 2 v), WithLp.toLp 2 v⟫ ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) P (WithLp.toLp 2 v) = WithLp.toLp 2 (P *ᵥ v) ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) (P * Q) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) P).comp (Matrix.toEuclideanCLM (𝕜 := ℝ) Q) ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) Pᵀ = ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) P) ∧
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = v ⬝ᵥ v ∧
      (Convex ℝ (WithLp.toLp 2 ⁻¹' K) ↔ Convex ℝ K) ∧ (IsClosed (WithLp.toLp 2 ⁻¹' K) ↔ IsClosed K)

end AdversarialBco.Poly
