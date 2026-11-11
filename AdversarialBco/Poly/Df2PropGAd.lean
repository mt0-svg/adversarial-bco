/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1
public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# Proposition G against a strategy

The statement `Df2PropGAd`: Lemma TV and Proposition G for DF2-O when the losses are chosen by a
strategy `σ ∈ Strats K n` (StatementConj1.lean), in the comparison design of Proposition 8.11 of the paper.

* Left side, DJ (DF2-O with the bisection gauge): its points `x`, given as any solution of the fixed-point equation
  `x t = df2oPlay ... ⟨K, lossAd σ ε x, ε, gs⟩ t` for `t < n` (the points of `df2oPlayAd` are one, by
  `df2oPlayAd_fix`), and the losses `lossAd σ ε x` that the strategy chose on that run.
* Right side, the comparison run: D0 (the exact gauge, `df2zPlay`) in the world `cmpWorld` whose loss of round `t`
  is `cmpLoss t = σ t x̃_{<t} õ_{<t}`, where `x̃_s` is the point that DJ's bisection map gives from the mode of D0
  before round `s` and the draw of round `s` (`cmpPts`), and `õ_s = σ s x̃_{<s} õ_{<s} (x̃_s) + ε_s`, with no dither
  (`obsAd`). The history fed to the strategy is thus the same function of (mode, draw, noise) in every hybrid of the
  proof, and it never reads the dither.

The joint measurability of the strategy on the interior of `K` is the Carathéodory lemma of A2, taken here as the
named hypothesis `CaraInterior` (`Df2PropGAdOf`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM

variable {d : ℕ}

/-- The Carathéodory lemma on the interior of a convex set: a family of convex functions on `K`, measurable in the
parameter at each interior point, is jointly measurable on `X × E d` once extended by `0` off the interior. -/
def CaraInterior : Prop :=
  ∀ (d : ℕ) (X : Type) [MeasurableSpace X] (K : Set (E d)) (F : X → E d → ℝ),
    (∀ x, ConvexOn ℝ K (F x)) → (∀ y ∈ interior K, Measurable fun x => F x y) →
      Measurable fun q : X × E d => (interior K).indicator (F q.1) q.2

/-- The quantifier block of the world statements against a strategy: the hypotheses of `TheoremConj1Upper`. -/
def Df2WorldHypAd (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) : Prop :=
  1 ≤ d ∧ 1 ≤ n ∧ 0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
    K ⊆ Metric.closedBall 0 R0 ∧ σ ∈ Strats K n

/-- The points `x̃_0, ..., x̃_{t-1}` of the comparison run (`0` from round `t` on): `x̃_t` is the point that DJ's round
map (`df2oRoundAt`, the bisection gauge) gives from the mode of D0 before round `t`, D0 being run in the world whose
losses the strategy gives at the points `x̃` of the earlier rounds. -/
noncomputable def cmpPref (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    ℕ → ℕ → E d
  | 0 => fun _ => 0
  | t + 1 => Function.update (cmpPref d n r0 R0 δ K σ ω t) t
      (df2oRoundAt d n r0 R0 δ (df2World K (lossAd σ ω.2 (cmpPref d n r0 R0 δ K σ ω t)) ω) t
        (df2zMode d n r0 R0 δ (df2World K (lossAd σ ω.2 (cmpPref d n r0 R0 δ K σ ω t)) ω) t)).1

/-- The point `x̃_t` of the comparison run. -/
noncomputable def cmpPts (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ω : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℕ) :
    E d :=
  cmpPref d n r0 R0 δ K σ ω (t + 1) t

/-- The loss of round `t` of the comparison run: `σ t x̃_{<t} õ_{<t}`, with `õ_s = σ s x̃_{<s} õ_{<s} (x̃_s) + ε_s`. -/
noncomputable def cmpLoss (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (t : ℕ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) : E d → ℝ :=
  lossAd σ ω.2 (cmpPts d n r0 R0 δ K σ ω) t

/-- The world of the comparison run: the body, the comparison losses, the noise and the Gaussian stream of `ω`. -/
noncomputable def cmpWorld (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    World d :=
  df2World K (fun t => cmpLoss d n r0 R0 δ K σ t ω) ω

/-- Lemma TV and Proposition 8.11 for DF2-O against a strategy. In the case of the analysis, the regret of DJ
against the losses the strategy chose on the run exceeds `B + 1` with probability at most that of D0 exceeding `B`
in the comparison world, plus `δ₁`. -/
def Df2PropGAd : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d), Df2WorldHypAd d n r0 R0 δ K σ →
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν → ∀ B : ℝ, ∀ x : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → E d,
      (∀ ω, ∀ t < n, x ω t = df2oPlay d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) t) →
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
          B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} ≤
        (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) ∧
          B < regretPts K (fun t => cmpLoss d n r0 R0 δ K σ t ω)
            (df2zPlay d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω)) n} + ENNReal.ofReal (df2oPar d n δ).δ1

/-- Proposition 8.11 from the Carathéodory lemma on the interior. -/
def Df2PropGAdOf : Prop := CaraInterior → Df2PropGAd

end AdversarialBco.Poly
