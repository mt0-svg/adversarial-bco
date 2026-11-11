/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SetEAd
public import AdversarialBco.Conj1.Prefix

@[expose] public section

/-!
# The world layer with an adapted loss process: statements

`Df2VEWorld` and `Df2AzWorld` (Df2Layer2.lean) bound two events of the run of D0 on the world `df2World K f ω` for
one fixed sequence `f`. Against a strategy the comparison run of Proposition 8.11 (Poly/Df2PropGAd.lean) has losses
that read the run before their round. `Df2LossProc` is such a process: the loss of round `t` on the world `ω` is
`L t (lam t ω)`, a family of admissible losses indexed by a parameter `l : Λ`, measurable in `l` at each point of the
interior of `K`, read at a parameter `lam t ω` measurable for the sigma-field `prefixσ … t` of the run before round
`t` (Conj1/Prefix.lean, with the first term of the rounds `N0` and the spare index `S` of the learner). A fixed
sequence is the constant process.

* `Df2VEWorldAd`: Lemma 8.8 on the world of a loss process, the same event and constant as `Df2VEWorld`.
* `Df2AzWorldAd`: the Azuma event of the run of D0 on the world of a loss process, as `Df2AzWorld`.
* `Df2VEWorldAdOf`, `Df2AzWorldAdOf`: the same inputs as `Df2VEWorldOf` and `Df2AzWorldOf`, with E1-loc in its
  adapted form `Df2E1LocAd` (Poly/Df2SetEAd.lean).

`Df2WorldDet` (Lemma 8.10) is pathwise and applies at each `ω` to the sequence `F.loss ω`, which is in
`Advs K n` (`Df2LossProc.loss_mem`).
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

variable {d : ℕ}

/-- A loss process adapted to the run of the learner over `n` rounds, on the body `K`, for the layout of the Gaussian
stream with first round term `N0` and spare index `S`: the loss of round `t` on the world `ω` is `L t (lam t ω)`. -/
structure Df2LossProc (d n N0 S : ℕ) (K : Set (E d)) where
  /-- The parameter space of the losses. -/
  Λ : Type
  /-- Its sigma-field. -/
  [mΛ : MeasurableSpace Λ]
  /-- The loss of round `t` at the parameter `l`. -/
  L : ℕ → Λ → E d → ℝ
  /-- The parameter of round `t` on the world `ω = (gs, noise)`. -/
  lam : ℕ → (ℕ → ℝ) × (ℕ → ℝ) → Λ
  /-- Every loss of the rounds `t < n` is admissible. -/
  adm : ∀ t < n, ∀ l, AdmLoss K (L t l)
  /-- At each point of the interior of `K`, the loss of a round `t < n` is measurable in the parameter. -/
  meas : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y
  /-- The parameter of a round `t < n` is known before round `t`. -/
  lam_meas : ∀ t < n, Measurable[Conj1.prefixσ N0 S n d t] (lam t)

attribute [instance] Df2LossProc.mΛ

/-- The losses of a loss process on the world `ω`. -/
def Df2LossProc.loss {n N0 S : ℕ} {K : Set (E d)} (F : Df2LossProc d n N0 S K) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    ℕ → E d → ℝ :=
  fun t => F.L t (F.lam t ω)

theorem Df2LossProc.loss_mem {n N0 S : ℕ} {K : Set (E d)} (F : Df2LossProc d n N0 S K) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    F.loss ω ∈ Advs K n :=
  fun t ht => F.adm t ht _

/-- The loss processes of the learner at `(d, n, r₀, R₀, δ)` on `K`: the layout of its Gaussian stream. -/
abbrev Df2LossProcOf (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) : Type 1 :=
  Df2LossProc d n (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) K

/-- The quantifier block of the world statements without the losses: the hypotheses of `TheoremConj1Upper` on the
dimension, the horizon, the radii, the confidence and the body. -/
def Df2BodyHyp (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) : Prop :=
  1 ≤ d ∧ 1 ≤ n ∧ 0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
    K ⊆ Metric.closedBall 0 R0

/-- Lemma 8.8 on the world of a loss process: for each start round `a < n`, the virtual epoch of D0 started
before round `a` fails (a) or (b5') at the horizon `n - a`, in the case of the analysis, with probability at most
`(149/168) δ_e`. -/
def Df2VEWorldAd : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)), Df2BodyHyp d n r0 R0 δ K → ∀ F : Df2LossProcOf d n r0 R0 δ K,
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν → ∀ a < n,
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧
          ¬ (df2zCtx d n r0 R0 δ (df2World K (F.loss ω) ω)).EpochOK
            (df2zPath d n r0 R0 δ (df2World K (F.loss ω) ω) a) (n - a)} ≤
        ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe)

/-- The Azuma event of the run of D0 on the world of a loss process fails, in the case of the analysis, with
probability at most `δ_e/7`. -/
def Df2AzWorldAd : Prop :=
  ∀ (d n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)), Df2BodyHyp d n r0 R0 δ K → ∀ F : Df2LossProcOf d n r0 R0 δ K,
    ∀ ν : Measure (ℕ → ℝ), NoiseOK ν →
      (gaussStream.prod ν) {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧
          ¬ Df2AzPath d n r0 R0 δ (df2World K (F.loss ω) ω)} ≤
        ENNReal.ofReal ((df2oPar d n δ).δe / 7)

/-- Lemma 8.8 on the world of a loss process from E1-loc in its adapted form: the instance at the start round `a`
reads the loss of its round `s` at the parameter (position, `lam (a + s)`), measurable before round `s`. -/
def Df2VEWorldAdOf : Prop := Df2E1LocAd → PropAP → PgMeas → PgGoodMeas → Df2ApCallMeas → Df2VEWorldAd

/-- The Azuma event on the world of a loss process from `Df2AzumaEvent` on the filtration of the run. -/
def Df2AzWorldAdOf : Prop := Df2AzumaEvent.{0} → PgMeas → PgGoodMeas → Df2ApCallMeas → Df2AzWorldAd

end AdversarialBco.Poly
