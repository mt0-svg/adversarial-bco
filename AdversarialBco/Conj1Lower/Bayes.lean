/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower
public import AdversarialBco.Conj1Lower.BayesRound

@[expose] public section

/-!
# The Bayes core: Lemma 9.5 over the whole game

Route (S7): the Gaussian game lives on an explicit product, the sample
`s = (x°, Z, ω) : Sample d Ω` with the law `gameLaw π0 μ = π0 ⊗ gaussStream ⊗ μ` (the tip, the Gaussian stream of
StatementPoly.lean, the seed of the learner). The history with the genie's answers and the posterior are functions on
it; no conditional expectation, no Ionescu-Tulcea.

* `Hist d α`: points played, observations and answers of every round, indexed by `ℕ`; the rounds not yet played hold
  `0` and `default`. One type for every round, in place of fixed-length histories.
* `Rule d α`: a genie rule, which gives, from the law `π` of the tip before a round and the play `x`, the answer
  `ans π x θ` and the signal `sig π x θ` (the loss without its noise) at each tip `θ`. The strategy S' of Section 9 is
  one (its dead rounds have a constant answer and a constant signal, so that the posterior does not move).
  `Rule.Meas`: the rule is measurable along every measurable family of probability densities on `π0` (Lemma 9.3); the only hypothesis of the core on the rule.
* `dens t h`: the density, on the prior `π0`, of the law `post t h` of the tip before round `t` given the history `h`
  (its rounds `0, ..., t - 1`): the recursion `π_{t+1} ∝ π_t 1[θ in the cell A_t] φ_σ(Y_t - s(θ))`, with
  `π_{t+1} = π_t` where the normaliser is `0` (the null-normaliser convention; `∞` never occurs).
* `hist t s`: the history after `t` rounds on the sample `s`: in round `t` the learner plays `x = pol t ω (...)` from
  the points and observations before `t`, the genie answers `ans (post t h) x x°`, the learner observes
  `sig (post t h) x x° + sc Z_t`.
* Lemma 9.5 (`post_disintegrates`): for `t ≤ n` and every measurable `F ≥ 0`,
  `E F(x°, Z_t, G_t, ω) = E ∫ post t G_t (dθ) ∫ N(0, 1)(dz) F(θ, z, G_t, ω)`: given the history and the seed, the tip
  has the law `post t`, and `Z_t` is a standard Gaussian independent of both. Proof by induction on `t` with
  `bayes_step` (BayesRound.lean) for the round.
* For the modules that use it (Ledger.lean, Info.lean, Top.lean): the tower form `post_disintegrates'`, the expansion of
  round `t` (`hist_succ_expand`), the posterior after a round as a Bayes update (`post_succ_push`), the Bochner form
  for bounded `F` (`post_disintegrates_integral`), and the measurability of what they integrate
  (`measurable_lintegral_post`, `measurable_hist`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Bayes

open RealRAM

/-! ## The objects -/

/-- A history with the genie's answers: the points played, the observations and the answers, indexed by the
rounds; the rounds not yet played hold `0` and `default`. -/
abbrev Hist (d : ℕ) (α : Type) : Type := (ℕ → E d) × (ℕ → ℝ) × (ℕ → α)

/-- The sample of the Gaussian game: the tip `x°`, the Gaussian stream `Z`, the seed of the learner. -/
abbrev Sample (d : ℕ) (Ω : Type) : Type := E d × (ℕ → ℝ) × Ω

/-- The law of the sample: `π0 ⊗ gaussStream ⊗ μ`. -/
noncomputable def gameLaw {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (π0 : Measure (E d)) (μ : Measure Ω) :
    Measure (Sample d Ω) :=
  π0.prod (gaussStream.prod μ)

/-- A genie rule: from the law `π` of the tip before a round and the play `x`, the answer `ans π x θ` and the signal
`sig π x θ` at the tip `θ`. -/
structure Rule (d : ℕ) (α : Type) where
  /-- The genie's answer at the tip. -/
  ans : Measure (E d) → E d → E d → α
  /-- The signal (the loss without its noise) at the tip. -/
  sig : Measure (E d) → E d → E d → ℝ

/-- Measurability of a rule along every measurable family `g` of finite probability densities on `π0`. -/
def Rule.Meas {d : ℕ} {α : Type} [MeasurableSpace α] (R : Rule d α) (π0 : Measure (E d)) : Prop :=
  ∀ (H : Type) [MeasurableSpace H] (g : H → E d → ℝ≥0∞), Measurable (Function.uncurry g) →
    (∀ h θ, g h θ ≠ ∞) → (∀ h, ∫⁻ θ, g h θ ∂π0 = 1) →
    Measurable (fun p : H × E d × E d => R.ans (π0.withDensity (g p.1)) p.2.1 p.2.2) ∧
      Measurable (fun p : H × E d × E d => R.sig (π0.withDensity (g p.1)) p.2.1 p.2.2)

section Defs

variable {d : ℕ} {α Ω : Type} [MeasurableSpace α]

/-- The likelihood of round `t` of the history `h`, for the law `π` of the tip before that round. -/
noncomputable def roundLik (R : Rule d α) (sc : ℝ) (π : Measure (E d)) (t : ℕ) (h : Hist d α) : E d → ℝ≥0∞ :=
  lik (R.ans π (h.1 t)) (R.sig π (h.1 t)) (noiseVar sc) (h.2.2 t) (h.2.1 t)

/-- The density on the prior `π0` of the law of the tip before round `t`, given the history `h`. -/
noncomputable def dens (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) : ℕ → Hist d α → E d → ℝ≥0∞
  | 0 => fun _ _ => 1
  | t + 1 => fun h =>
    if ∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0 = 0 ∨
        ∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0 = ∞
      then dens π0 R sc t h
      else fun θ => (∫⁻ θ', dens π0 R sc t h θ' *
          roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ' ∂π0)⁻¹ *
        (dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ)

/-- The law of the tip before round `t` given the history `h`: `π0` with the density `dens t h`. -/
noncomputable def post (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) : Measure (E d) :=
  π0.withDensity (dens π0 R sc t h)

/-- The point played in round `t` with the seed `ω`, from the points and observations of the rounds before `t`. -/
def play (pol : Learner Ω d) (t : ℕ) (ω : Ω) (h : Hist d α) : E d :=
  pol t ω (fun i : Fin t => h.1 i) (fun i : Fin t => h.2.1 i)

/-- The history `h` with round `t` set to the play `x`, the observation `y` and the answer `a`. -/
def Hist.push (h : Hist d α) (t : ℕ) (x : E d) (y : ℝ) (a : α) : Hist d α :=
  (Function.update h.1 t x, Function.update h.2.1 t y, Function.update h.2.2 t a)

/-- The history before the first round. -/
def Hist.empty [Inhabited α] : Hist d α :=
  (fun _ => 0, fun _ => 0, fun _ => default)

/-- The history after `t` rounds of the Gaussian game on the sample `s = (x°, Z, ω)`. -/
noncomputable def hist [Inhabited α] (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) :
    ℕ → Sample d Ω → Hist d α
  | 0 => fun _ => Hist.empty
  | t + 1 => fun s =>
    Hist.push (hist π0 R sc pol t s) t (play pol t s.2.2 (hist π0 R sc pol t s))
      (R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1 + sc * s.2.1 t)
      (R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1)

end Defs

/-! ## The posterior: densities, measurability, the update of a round -/

section Post

variable {d : ℕ} {α : Type} [MeasurableSpace α]

omit [MeasurableSpace α] in
theorem dens_succ (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) :
    dens π0 R sc (t + 1) h =
      if ∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0 = 0 ∨
          ∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0 = ∞
        then dens π0 R sc t h
        else fun θ => (∫⁻ θ', dens π0 R sc t h θ' *
            roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ' ∂π0)⁻¹ *
          (dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ) := rfl

/-- The densities are jointly measurable in the history and the tip, finite, and of mass one. -/
theorem dens_props [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) :
    Measurable (Function.uncurry (dens π0 R sc t)) ∧ (∀ h θ, dens π0 R sc t h θ ≠ ∞) ∧
      ∀ h, ∫⁻ θ, dens π0 R sc t h θ ∂π0 = 1 := by
  induction t with
  | zero =>
    refine ⟨measurable_const, fun _ _ => ENNReal.one_ne_top, fun h => ?_⟩
    simp [dens]
  | succ t ih =>
    obtain ⟨hm, hfin, hone⟩ := ih
    obtain ⟨hA, hS⟩ := hR (Hist d α) (dens π0 R sc t) hm hfin hone
    have hm' : Measurable (fun q : Hist d α × E d => dens π0 R sc t q.1 q.2) := hm
    have hpt : Measurable (fun q : Hist d α × E d => (q.1, q.1.1 t, q.2)) :=
      measurable_fst.prodMk (((measurable_pi_apply t).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd)
    have hc : Measurable (fun q : Hist d α × E d =>
        R.ans (π0.withDensity (dens π0 R sc t q.1)) (q.1.1 t) q.2) := by
      have := hA.comp hpt
      exact this
    have hs : Measurable (fun q : Hist d α × E d =>
        R.sig (π0.withDensity (dens π0 R sc t q.1)) (q.1.1 t) q.2) := by
      have := hS.comp hpt
      exact this
    have hL : Measurable (fun q : Hist d α × E d =>
        roundLik R sc (π0.withDensity (dens π0 R sc t q.1)) t q.1 q.2) :=
      measurable_lik_param (P := Hist d α) (c := fun h => R.ans (π0.withDensity (dens π0 R sc t h)) (h.1 t))
        (s := fun h => R.sig (π0.withDensity (dens π0 R sc t h)) (h.1 t)) hc hs
        (noiseVar sc) (a := fun h => h.2.2 t) (y := fun h => h.2.1 t)
        ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
        ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))
    have hgL := hm'.mul hL
    have hN : Measurable (fun h : Hist d α => ∫⁻ θ, dens π0 R sc t h θ *
        roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0) := hgL.lintegral_prod_right'
    have hLfin : ∀ h θ, roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ≠ ∞ := fun h θ =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lik_le _ _ _ _ _ θ)
    refine ⟨?_, ?_, ?_⟩
    · have heq : Function.uncurry (dens π0 R sc (t + 1)) = fun q : Hist d α × E d =>
          if ∫⁻ θ, dens π0 R sc t q.1 θ * roundLik R sc (π0.withDensity (dens π0 R sc t q.1)) t q.1 θ ∂π0 = 0 ∨
              ∫⁻ θ, dens π0 R sc t q.1 θ * roundLik R sc (π0.withDensity (dens π0 R sc t q.1)) t q.1 θ ∂π0 = ∞
            then dens π0 R sc t q.1 q.2
            else (∫⁻ θ, dens π0 R sc t q.1 θ *
                roundLik R sc (π0.withDensity (dens π0 R sc t q.1)) t q.1 θ ∂π0)⁻¹ *
              (dens π0 R sc t q.1 q.2 * roundLik R sc (π0.withDensity (dens π0 R sc t q.1)) t q.1 q.2) := by
        funext q
        simp only [Function.uncurry, dens_succ]
        split_ifs <;> rfl
      rw [heq]
      refine Measurable.ite ?_ hm' ((hN.comp measurable_fst).inv.mul hgL)
      exact ((hN.comp measurable_fst) (measurableSet_singleton 0)).union
        ((hN.comp measurable_fst) (measurableSet_singleton ∞))
    · intro h θ
      rw [dens_succ]
      split_ifs with hc
      · exact hfin h θ
      · push Not at hc
        exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc.1) (ENNReal.mul_ne_top (hfin h θ) (hLfin h θ))
    · intro h
      rw [dens_succ]
      split_ifs with hc
      · exact hone h
      · push Not at hc
        have hθ : Measurable (fun θ => dens π0 R sc t h θ *
            roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ) := hgL.comp (measurable_prodMk_left (x := h))
        beta_reduce
        rw [lintegral_const_mul _ hθ, ENNReal.inv_mul_cancel hc.1 hc.2]

theorem measurable_dens [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) :
    Measurable (Function.uncurry (dens π0 R sc t)) :=
  (dens_props π0 R hR sc t).1

theorem isProbabilityMeasure_post [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d))
    [IsProbabilityMeasure π0] (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) (h : Hist d α) :
    IsProbabilityMeasure (post π0 R sc t h) := by
  have hdens := (dens_props π0 R hR sc t).2.2 h
  have hpost : post π0 R sc t h = π0.withDensity (dens π0 R sc t h) := rfl
  rw [hpost]
  refine ⟨?h⟩
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hdens

/-- The posterior integral of a measurable function of a parameter and the tip is measurable in the parameter. -/
theorem measurable_lintegral_post [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d))
    [IsProbabilityMeasure π0] (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) {P : Type} [MeasurableSpace P]
    {hp : P → Hist d α} (hhp : Measurable hp) {f : P × E d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p => ∫⁻ θ, f (p, θ) ∂post π0 R sc t (hp p)) := by
  have hmeas_dens : Measurable (Function.uncurry (dens π0 R sc t)) :=
    measurable_dens π0 R hR sc t
  have hmeas_g : Measurable (fun (q : P × E d) => dens π0 R sc t (hp q.1) q.2 * f q) := by
    have h1 : Measurable (fun (q : P × E d) => dens π0 R sc t (hp q.1) q.2) :=
      hmeas_dens.comp ((hhp.comp measurable_fst).prodMk measurable_snd)
    exact h1.mul hf
  have h_eq : (fun p => ∫⁻ θ, f (p, θ) ∂post π0 R sc t (hp p)) =
      (fun p => ∫⁻ θ, dens π0 R sc t (hp p) θ * f (p, θ) ∂π0) := by
    ext p
    simpa [post] using MeasureTheory.lintegral_withDensity_eq_lintegral_mul π0
      (f := dens π0 R sc t (hp p))
      (hmeas_dens.comp (measurable_prodMk_left (x := hp p)))
      (g := fun θ => f (p, θ))
      (hf.comp (measurable_prodMk_left (x := p)))
  rw [h_eq]
  exact hmeas_g.lintegral_prod_right'

/-- The answer and the signal of round `t` are measurable in the history, the play and the tip. -/
theorem measurable_rule_post [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d))
    [IsProbabilityMeasure π0] (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) :
    Measurable (fun p : Hist d α × E d × E d => R.ans (post π0 R sc t p.1) p.2.1 p.2.2) ∧
      Measurable (fun p : Hist d α × E d × E d => R.sig (post π0 R sc t p.1) p.2.1 p.2.2) := by
  exact hR (Hist d α) (dens π0 R sc t) (dens_props π0 R hR sc t).1 (dens_props π0 R hR sc t).2.1 (dens_props π0 R hR sc t).2.2

/-- The density of round `t` reads the rounds before `t` only. -/
theorem dens_congr (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h h' : Hist d α)
    (hh : ∀ i < t, h.1 i = h'.1 i ∧ h.2.1 i = h'.2.1 i ∧ h.2.2 i = h'.2.2 i) :
    dens π0 R sc t h = dens π0 R sc t h' := by
  induction t generalizing h h' with
  | zero => rfl
  | succ t ih =>
      have hh_t : h.1 t = h'.1 t ∧ h.2.1 t = h'.2.1 t ∧ h.2.2 t = h'.2.2 t :=
        hh t (Nat.lt_succ_self t)
      rcases hh_t with ⟨h1, h2, h3⟩
      have hh_restrict : ∀ i < t, h.1 i = h'.1 i ∧ h.2.1 i = h'.2.1 i ∧ h.2.2 i = h'.2.2 i := by
        intro i hi
        exact hh i (Nat.lt_of_lt_of_le hi (Nat.le_succ _))
      simp [dens, roundLik, ih h h' hh_restrict, h1, h2, h3]
      split_ifs with hcond
      · simp [hcond]
      · simp [hcond]

/-- Setting round `t` does not change the law before round `t`. -/
theorem post_push (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) (x : E d) (y : ℝ)
    (a : α) : post π0 R sc t (Hist.push h t x y a) = post π0 R sc t h := by
  unfold post
  rw [dens_congr π0 R sc t (Hist.push h t x y a) h ?_]
  intro i hi
  simp [Hist.push, Function.update_of_ne (Nat.ne_of_lt hi)]

/-- The density recursion is the Bayes update of `BayesRound.lean`. -/
theorem withDensity_upd {Θ : Type} [MeasurableSpace Θ] (π0 : Measure Θ) {g L : Θ → ℝ≥0∞} (hg : Measurable g)
    (hL : Measurable L) :
    π0.withDensity (if ∫⁻ θ, g θ * L θ ∂π0 = 0 ∨ ∫⁻ θ, g θ * L θ ∂π0 = ∞ then g
        else fun θ => (∫⁻ θ', g θ' * L θ' ∂π0)⁻¹ * (g θ * L θ)) =
      bayesUpd (π0.withDensity g) L := by
  have hlintegral : ∫⁻ θ, L θ ∂(π0.withDensity g) = ∫⁻ θ, g θ * L θ ∂π0 := by
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable hL.aemeasurable]
    refine lintegral_congr fun θ => ?_
    simp [Pi.mul_apply]
  unfold bayesUpd
  rw [hlintegral]
  split_ifs with h
  · rfl
  · have hN0 : ∫⁻ θ, g θ * L θ ∂π0 ≠ 0 := by
      intro h0
      apply h
      left
      exact h0
    have hNtop : ∫⁻ θ, g θ * L θ ∂π0 ≠ ∞ := by
      intro htop
      apply h
      right
      exact htop
    have h_eq_fun : (fun θ => (∫⁻ θ', g θ' * L θ' ∂π0)⁻¹ * (g θ * L θ)) =
        ((∫⁻ θ', g θ' * L θ' ∂π0)⁻¹ • (g * L)) := by
      ext θ
      simp [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [h_eq_fun]
    rw [MeasureTheory.withDensity_smul _ (hg.mul hL)]
    rw [MeasureTheory.withDensity_mul π0 hg hL]

/-- The law after round `t` is the Bayes update of the law before it by the likelihood of round `t`. -/
theorem post_succ [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) (h : Hist d α) :
    post π0 R sc (t + 1) h = bayesUpd (post π0 R sc t h) (roundLik R sc (post π0 R sc t h) t h) := by
  have hg : Measurable (dens π0 R sc t h) :=
    (measurable_dens π0 R hR sc t).comp (measurable_prodMk_left (x := h))
  obtain ⟨hA, hS⟩ := measurable_rule_post π0 R hR sc t
  have hpt : Measurable (fun θ : E d => (h, h.1 t, θ)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hc : Measurable (R.ans (post π0 R sc t h) (h.1 t)) := by
    have := hA.comp hpt
    exact this
  have hs : Measurable (R.sig (post π0 R sc t h) (h.1 t)) := by
    have := hS.comp hpt
    exact this
  have hL : Measurable (roundLik R sc (post π0 R sc t h) t h) := by
    have := (measurable_lik hc hs (noiseVar sc)).comp
      (measurable_const.prodMk measurable_id : Measurable fun θ : E d => ((h.2.2 t, h.2.1 t), θ))
    exact this
  rw [post, post, dens_succ]
  exact withDensity_upd π0 hg hL

/-- The law after a round with the play `x`, the observation `y` and the answer `a`. -/
theorem post_succ_push [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (t : ℕ) (h : Hist d α) (x : E d) (y : ℝ) (a : α) :
    post π0 R sc (t + 1) (Hist.push h t x y a) =
      bayesUpd (post π0 R sc t h)
        (lik (R.ans (post π0 R sc t h) x) (R.sig (post π0 R sc t h) x) (noiseVar sc) a y) := by
  calc
  post π0 R sc (t + 1) (Hist.push h t x y a)
      = bayesUpd (post π0 R sc t (Hist.push h t x y a)) (roundLik R sc (post π0 R sc t (Hist.push h t x y a)) t (Hist.push h t x y a)) := by
    rw [post_succ π0 R hR sc t (Hist.push h t x y a)]
  _ = bayesUpd (post π0 R sc t h) (roundLik R sc (post π0 R sc t h) t (Hist.push h t x y a)) := by
    rw [post_push π0 R sc t h x y a]
  _ = bayesUpd (post π0 R sc t h) (lik (R.ans (post π0 R sc t h) x) (R.sig (post π0 R sc t h) x) (noiseVar sc) a y) := by
    simp [roundLik, Hist.push, Function.update_self]

/-- A round whose likelihood is a constant in `(0, ∞)` (a dead round, on its path) leaves the law unchanged. -/
theorem bayesUpd_const {Θ : Type} [MeasurableSpace Θ] (π : Measure Θ) [IsProbabilityMeasure π] {L : Θ → ℝ≥0∞}
    {c : ℝ≥0∞} (hL : ∀ θ, L θ = c) (hc0 : c ≠ 0) (hc : c ≠ ∞) : bayesUpd π L = π := by
  have hL' : L = fun _ => c := funext hL
  have hint : ∫⁻ θ, L θ ∂π = c := by
    rw [hL', lintegral_const, measure_univ, mul_one]
  have h_not : ¬ (c = 0 ∨ c = ∞) := by
    rintro (h0 | htop)
    · exact hc0 h0
    · exact hc htop
  unfold bayesUpd
  rw [hint]
  by_cases hcond : c = 0 ∨ c = ∞
  · exfalso; exact h_not hcond
  · rw [ite_eq_right hcond, hL', MeasureTheory.withDensity_const, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]

end Post

/-! ## The history -/

section History

variable {d : ℕ} {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω] [Inhabited α]

omit [MeasurableSpace α] [MeasurableSpace Ω] in
theorem hist_zero (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (s : Sample d Ω) :
    hist π0 R sc pol 0 s = Hist.empty := rfl

omit [MeasurableSpace α] [MeasurableSpace Ω] in
theorem hist_succ (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) :
    hist π0 R sc pol (t + 1) s =
      Hist.push (hist π0 R sc pol t s) t (play pol t s.2.2 (hist π0 R sc pol t s))
        (R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1 +
          sc * s.2.1 t)
        (R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1) := rfl

/-- The history after `t` rounds reads the stream before `t` only. -/
theorem hist_congr (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (t : ℕ) (s s' : Sample d Ω)
    (h1 : s.1 = s'.1) (h2 : ∀ i < t, s.2.1 i = s'.2.1 i) (h3 : s.2.2 = s'.2.2) :
    hist π0 R sc pol t s = hist π0 R sc pol t s' := by
  rcases s with ⟨θ, Z, ω⟩
  rcases s' with ⟨θ', Z', ω'⟩
  subst h1
  subst h3
  dsimp at h2
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [hist_succ π0 R sc pol t (θ, Z, ω), hist_succ π0 R sc pol t (θ, Z', ω)]
      rw [ih (fun i hi => h2 i (Nat.lt_of_lt_of_le hi (Nat.le_succ _)))]
      have hZt : Z t = Z' t := h2 t (Nat.lt_succ_self t)
      dsimp
      rw [hZt]

/-- Later rounds do not change round `i`. -/
theorem hist_stable (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (s : Sample d Ω) {i t : ℕ}
    (hi : i < t) :
    (hist π0 R sc pol t s).1 i = (hist π0 R sc pol (i + 1) s).1 i ∧
      (hist π0 R sc pol t s).2.1 i = (hist π0 R sc pol (i + 1) s).2.1 i ∧
      (hist π0 R sc pol t s).2.2 i = (hist π0 R sc pol (i + 1) s).2.2 i := by
  have hle : i + 1 ≤ t := Nat.succ_le_of_lt hi
  refine Nat.le_induction ?base ?step t hle
  · -- base: t = i + 1
    exact ⟨rfl, rfl, rfl⟩
  · -- step: from k to k+1, where i+1 ≤ k
    intro k hk hih
    have hik : i < k := by
      omega
    have hne : i ≠ k := by omega
    rw [hist_succ π0 R sc pol k s]
    simp [Hist.push, Function.update_of_ne hne]
    exact hih

/-- Round `i` of the history after round `i`: the play, the observation and the answer of that round. -/
theorem hist_succ_self (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (s : Sample d Ω) (i : ℕ) :
    (hist π0 R sc pol (i + 1) s).1 i = play pol i s.2.2 (hist π0 R sc pol i s) ∧
      (hist π0 R sc pol (i + 1) s).2.1 i =
        R.sig (post π0 R sc i (hist π0 R sc pol i s)) (play pol i s.2.2 (hist π0 R sc pol i s)) s.1 +
          sc * s.2.1 i ∧
      (hist π0 R sc pol (i + 1) s).2.2 i =
        R.ans (post π0 R sc i (hist π0 R sc pol i s)) (play pol i s.2.2 (hist π0 R sc pol i s)) s.1 := by
  rw [hist_succ]
  simp [Hist.push]

omit [Inhabited α] in
theorem measurable_play {pol : Learner Ω d} {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (fun p : Ω × Hist d α => play pol t p.1 p.2) := by
  have h_proj : Measurable (fun p : Ω × Hist d α => (p.1, (fun i : Fin t => p.2.1 i), (fun i : Fin t => p.2.2.1 i))) := by
    fun_prop
  have h_eq : (fun p : Ω × Hist d α => play pol t p.1 p.2) =
      (fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) ∘
      (fun p : Ω × Hist d α => (p.1, (fun i : Fin t => p.2.1 i), (fun i : Fin t => p.2.2.1 i))) := by
    ext p
    rfl
  rw [h_eq]
  exact hpol.comp h_proj

omit [Inhabited α] in
theorem measurable_push (t : ℕ) :
    Measurable (fun p : Hist d α × E d × ℝ × α => Hist.push p.1 t p.2.1 p.2.2.1 p.2.2.2) := by
  unfold Hist.push; fun_prop

/-- The history is measurable in the sample for `t ≤ n` when the learner is measurable for `t < n`. -/
theorem measurable_hist [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    {t : ℕ} (ht : t ≤ n) : Measurable (hist π0 R sc pol t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hm := ih (Nat.le_of_succ_le ht)
    obtain ⟨hA, hS⟩ := measurable_rule_post π0 R hR sc t
    have hxp : Measurable (fun s : Sample d Ω => play pol t s.2.2 (hist π0 R sc pol t s)) := by
      have h1 := measurable_play (α := α) (hpol t (Nat.lt_of_succ_le ht))
      exact h1.comp ((measurable_snd.comp measurable_snd).prodMk hm)
    have ha : Measurable (fun s : Sample d Ω =>
        R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1) := by
      have h2 := hA.comp (hm.prodMk (hxp.prodMk measurable_fst))
      exact h2
    have hy : Measurable (fun s : Sample d Ω =>
        R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1 +
          sc * s.2.1 t) := by
      have h3 := hS.comp (hm.prodMk (hxp.prodMk measurable_fst))
      exact h3.add (measurable_const.mul ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)))
    have htup : Measurable (fun s : Sample d Ω => (hist π0 R sc pol t s, play pol t s.2.2 (hist π0 R sc pol t s),
        R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1 +
          sc * s.2.1 t,
        R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1)) :=
      hm.prodMk (hxp.prodMk (hy.prodMk ha))
    have hfun : hist π0 R sc pol (t + 1) =
        (fun q : Hist d α × E d × ℝ × α => Hist.push q.1 t q.2.1 q.2.2.1 q.2.2.2) ∘
          (fun s : Sample d Ω => (hist π0 R sc pol t s, play pol t s.2.2 (hist π0 R sc pol t s),
            R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1 +
              sc * s.2.1 t,
            R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) s.1)) := rfl
    rw [hfun]
    exact (measurable_push t).comp htup

end History

/-! ## The stream and the law of the sample -/

section Stream

instance : IsProbabilityMeasure gaussStream := by
  unfold gaussStream
  infer_instance

/-- A coordinate of a product of probability measures is independent of the others: a function of the coordinate
`i` and of a point that it does not read through its coordinate `i`. -/
theorem lintegral_infinitePi_coord {ι : Type} [DecidableEq ι] {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (i : ι) {F : X × (ι → X) → ℝ≥0∞} (hF : Measurable F)
    (hupd : ∀ a Z b, F (a, Function.update Z i b) = F (a, Z)) :
    ∫⁻ Z, F (Z i, Z) ∂Measure.infinitePi (fun _ : ι => ν) =
      ∫⁻ Z, ∫⁻ a, F (a, Z) ∂ν ∂Measure.infinitePi (fun _ : ι => ν) := by
  have hΦ : Measurable (fun p : (ι → X) × X => Function.update p.1 i p.2) :=
    measurable_update'
  have hmp : MeasurePreserving (fun p : (ι → X) × X => Function.update p.1 i p.2)
      ((Measure.infinitePi fun _ : ι => ν).prod ν) (Measure.infinitePi fun _ : ι => ν) := by
    refine ⟨hΦ, ?_⟩
    apply Measure.eq_infinitePi
    intro s t ht
    rw [Measure.map_apply hΦ (MeasurableSet.pi s.countable_toSet fun j _ => ht j)]
    have hpre : (fun p : (ι → X) × X => Function.update p.1 i p.2) ⁻¹' Set.pi (↑s) t =
        Set.pi (↑(s.erase i)) t ×ˢ (if i ∈ s then t i else Set.univ) := by
      ext ⟨Z, b⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have := h j hj.2
          rwa [Function.update_of_ne hj.1] at this
        · split_ifs with hi
          · have := h i hi
            rwa [Function.update_self] at this
          · trivial
      · rintro ⟨h1, h2⟩ j hj
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          rwa [if_pos hj] at h2
        · rw [Function.update_of_ne hji]
          exact h1 j ⟨hji, hj⟩
    rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun j _ => ht j)]
    split_ifs with hi
    · rw [Finset.prod_erase_mul _ _ hi]
    · rw [measure_univ, mul_one, Finset.erase_eq_of_notMem hi]
  have hf : Measurable (fun Z : ι → X => F (Z i, Z)) := hF.comp ((measurable_pi_apply i).prodMk measurable_id)
  calc ∫⁻ Z, F (Z i, Z) ∂Measure.infinitePi (fun _ : ι => ν)
      = ∫⁻ p, F ((Function.update p.1 i p.2) i, Function.update p.1 i p.2)
          ∂((Measure.infinitePi fun _ : ι => ν).prod ν) := (hmp.lintegral_comp hf).symm
    _ = ∫⁻ p, F (p.2, p.1) ∂((Measure.infinitePi fun _ : ι => ν).prod ν) := by
        refine lintegral_congr fun p => ?_
        rw [Function.update_self, hupd]
    _ = ∫⁻ Z, ∫⁻ a, F (a, Z) ∂ν ∂Measure.infinitePi (fun _ : ι => ν) :=
        lintegral_prod _ (hF.comp measurable_swap).aemeasurable

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

theorem isProbabilityMeasure_gameLaw (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (gameLaw π0 μ) := by
  unfold gameLaw gaussStream
  infer_instance

/-- Coordinate `t` of the stream is independent of what does not read it, under the law of the sample. -/
theorem lintegral_gameLaw_coord (π0 : Measure (E d)) [SFinite π0] (μ : Measure Ω) [SFinite μ] (t : ℕ)
    {F : ℝ × Sample d Ω → ℝ≥0∞} (hF : Measurable F)
    (hupd : ∀ a θ Z b ω, F (a, (θ, Function.update Z t b, ω)) = F (a, (θ, Z, ω))) :
    ∫⁻ s, F (s.2.1 t, s) ∂gameLaw π0 μ = ∫⁻ s, ∫⁻ z, F (z, s) ∂gaussianReal 0 1 ∂gameLaw π0 μ := by
  have hG : Measurable (fun s : Sample d Ω => ∫⁻ z, F (z, s) ∂gaussianReal 0 1) := hF.lintegral_prod_left'
  have hF1 : Measurable (fun s : Sample d Ω => F (s.2.1 t, s)) :=
    hF.comp (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk measurable_id)
  unfold gameLaw
  rw [lintegral_prod _ hF1.aemeasurable, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun θ => ?_
  have hF1' : Measurable (fun q : (ℕ → ℝ) × Ω => F (q.1 t, (θ, q))) :=
    hF1.comp (measurable_prodMk_left (x := θ))
  have hG' : Measurable (fun q : (ℕ → ℝ) × Ω => ∫⁻ z, F (z, (θ, q)) ∂gaussianReal 0 1) :=
    hG.comp (measurable_prodMk_left (x := θ))
  rw [lintegral_prod_symm _ hF1'.aemeasurable, lintegral_prod_symm _ hG'.aemeasurable]
  refine lintegral_congr fun ω => ?_
  unfold gaussStream
  exact lintegral_infinitePi_coord (gaussianReal 0 1) t (F := fun p : ℝ × (ℕ → ℝ) => F (p.1, (θ, p.2, ω)))
    (hF.comp (measurable_fst.prodMk (measurable_const.prodMk (measurable_snd.prodMk measurable_const))))
    (fun a Z b => hupd a θ Z b ω)

end Stream

/-! ## Lemma 9.5 -/

section POST

variable {d : ℕ} {α Ω : Type} [MeasurableSpace α] [MeasurableSpace Ω] [Inhabited α] [Fintype α]
  [MeasurableSingletonClass α]

/-- Round `t` pushed onto the history `h` at the tip `θ`, the noise `z` and the seed `ω`, `p = (θ, z, h, ω)`. -/
noncomputable def roundPush (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (t : ℕ)
    (p : E d × ℝ × Hist d α × Ω) : Hist d α :=
  Hist.push p.2.2.1 t (play pol t p.2.2.2 p.2.2.1)
    (R.sig (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1 + sc * p.2.1)
    (R.ans (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1)

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSpace α] [MeasurableSpace Ω] in
theorem hist_succ_roundPush (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (pol : Learner Ω d) (t : ℕ)
    (s : Sample d Ω) :
    hist π0 R sc pol (t + 1) s = roundPush π0 R sc pol t (s.1, s.2.1 t, hist π0 R sc pol t s, s.2.2) := rfl

omit [Inhabited α] in
theorem measurable_roundPush (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d α) (hR : R.Meas π0)
    (sc : ℝ) {pol : Learner Ω d} {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (roundPush π0 R sc pol t) := by
  obtain ⟨hA, hS⟩ := measurable_rule_post π0 R hR sc t
  have hh : Measurable (fun p : E d × ℝ × Hist d α × Ω => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hxp : Measurable (fun p : E d × ℝ × Hist d α × Ω => play pol t p.2.2.2 p.2.2.1) := by
    have h1 := measurable_play (α := α) hpol
    exact h1.comp ((measurable_snd.comp (measurable_snd.comp measurable_snd)).prodMk hh)
  have ha : Measurable (fun p : E d × ℝ × Hist d α × Ω =>
      R.ans (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1) := by
    have h2 := hA.comp (hh.prodMk (hxp.prodMk measurable_fst))
    exact h2
  have hy : Measurable (fun p : E d × ℝ × Hist d α × Ω =>
      R.sig (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1 + sc * p.2.1) := by
    have h3 := hS.comp (hh.prodMk (hxp.prodMk measurable_fst))
    exact h3.add (measurable_const.mul (measurable_fst.comp measurable_snd))
  have htup : Measurable (fun p : E d × ℝ × Hist d α × Ω => (p.2.2.1, play pol t p.2.2.2 p.2.2.1,
      R.sig (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1 + sc * p.2.1,
      R.ans (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1)) := hh.prodMk (hxp.prodMk (hy.prodMk ha))
  have hfun : roundPush π0 R sc pol t = (fun q : Hist d α × E d × ℝ × α => Hist.push q.1 t q.2.1 q.2.2.1 q.2.2.2) ∘
      (fun p : E d × ℝ × Hist d α × Ω => (p.2.2.1, play pol t p.2.2.2 p.2.2.1,
        R.sig (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1 + sc * p.2.1,
        R.ans (post π0 R sc t p.2.2.1) (play pol t p.2.2.2 p.2.2.1) p.1)) := rfl
  rw [hfun]
  exact (measurable_push t).comp htup

omit [Inhabited α] [Fintype α] [MeasurableSingletonClass α] [MeasurableSpace α] in
/-- The tip is independent of the seed under the law of the sample. -/
theorem lintegral_gameLaw_tip (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [SFinite μ]
    {Φ : E d × Ω → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ s, Φ (s.1, s.2.2) ∂gameLaw π0 μ = ∫⁻ s, ∫⁻ θ, Φ (θ, s.2.2) ∂π0 ∂gameLaw π0 μ := by
  have h1 : Measurable (fun s : Sample d Ω => Φ (s.1, s.2.2)) :=
    hΦ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable (fun s : Sample d Ω => ∫⁻ θ, Φ (θ, s.2.2) ∂π0) :=
    (hΦ.comp (measurable_snd.prodMk ((measurable_snd.comp measurable_snd).comp measurable_fst))).lintegral_prod_right'
  unfold gameLaw
  rw [lintegral_prod3 _ _ _ h1, lintegral_prod3 _ _ _ h2]
  refine lintegral_congr fun ω => ?_
  simp only [lintegral_const, measure_univ, mul_one]

/-- One round, for a fixed history and seed: the tip of law `post t h` and the noise `z`, read through the answer and
the observation of round `t`, disintegrate along the law after the round. -/
theorem post_step (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d α) (hR : R.Meas π0) {sc : ℝ}
    (hsc : sc ≠ 0) (t : ℕ) (h : Hist d α) (x : E d) {G : E d × α × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ, ∫⁻ z, G (θ, R.ans (post π0 R sc t h) x θ, R.sig (post π0 R sc t h) x θ + sc * z)
        ∂gaussianReal 0 1 ∂post π0 R sc t h =
      ∫⁻ θ, ∫⁻ z, ∫⁻ θ', G (θ', R.ans (post π0 R sc t h) x θ, R.sig (post π0 R sc t h) x θ + sc * z)
        ∂post π0 R sc (t + 1)
          (Hist.push h t x (R.sig (post π0 R sc t h) x θ + sc * z) (R.ans (post π0 R sc t h) x θ))
        ∂gaussianReal 0 1 ∂post π0 R sc t h := by
  haveI : IsProbabilityMeasure (post π0 R sc t h) := isProbabilityMeasure_post π0 R hR sc t h
  obtain ⟨hA, hS⟩ := measurable_rule_post π0 R hR sc t
  have hpt : Measurable (fun θ : E d => (h, x, θ)) := measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hcx : Measurable (R.ans (post π0 R sc t h) x) := by
    have := hA.comp hpt
    exact this
  have hsx : Measurable (R.sig (post π0 R sc t h) x) := by
    have := hS.comp hpt
    exact this
  have hpush : ∀ θ z, post π0 R sc (t + 1)
      (Hist.push h t x (R.sig (post π0 R sc t h) x θ + sc * z) (R.ans (post π0 R sc t h) x θ)) =
      bayesUpd (post π0 R sc t h) (lik (R.ans (post π0 R sc t h) x) (R.sig (post π0 R sc t h) x) (noiseVar sc)
        (R.ans (post π0 R sc t h) x θ) (R.sig (post π0 R sc t h) x θ + sc * z)) :=
    fun θ z => post_succ_push π0 R hR sc t h x _ _
  calc ∫⁻ θ, ∫⁻ z, G (θ, R.ans (post π0 R sc t h) x θ, R.sig (post π0 R sc t h) x θ + sc * z)
        ∂gaussianReal 0 1 ∂post π0 R sc t h
      = ∫⁻ θ, ∫⁻ y, G (θ, R.ans (post π0 R sc t h) x θ, y)
          ∂gaussianReal (R.sig (post π0 R sc t h) x θ) (noiseVar sc) ∂post π0 R sc t h :=
        lintegral_congr fun θ => lintegral_gauss_affine _ _
          (f := fun y => G (θ, R.ans (post π0 R sc t h) x θ, y))
          (hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ θ, ∫⁻ y, ∫⁻ θ', G (θ', R.ans (post π0 R sc t h) x θ, y)
          ∂bayesUpd (post π0 R sc t h) (lik (R.ans (post π0 R sc t h) x) (R.sig (post π0 R sc t h) x)
            (noiseVar sc) (R.ans (post π0 R sc t h) x θ) y)
          ∂gaussianReal (R.sig (post π0 R sc t h) x θ) (noiseVar sc) ∂post π0 R sc t h :=
        bayes_step (post π0 R sc t h) hcx hsx (noiseVar_ne_zero hsc) hG
    _ = _ := by
        refine lintegral_congr fun θ => ?_
        rw [← lintegral_gauss_affine _ _ ?_]
        · refine lintegral_congr fun z => ?_
          rw [hpush θ z]
        · exact measurable_lintegral_bayesUpd_param (post π0 R sc t h) (P := ℝ)
            (c := fun _ => R.ans (post π0 R sc t h) x) (s := fun _ => R.sig (post π0 R sc t h) x)
            (hcx.comp measurable_snd) (hsx.comp measurable_snd) (noiseVar sc)
            (a := fun _ => R.ans (post π0 R sc t h) x θ) (y := id) measurable_const measurable_id
            (G := fun q => G (q.2, R.ans (post π0 R sc t h) x θ, q.1))
            (hG.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))

/-- Lemma 9.5: given the history after `t` rounds and the seed, the tip has the law `post t` and the noise of round
`t` is a standard Gaussian independent of both. -/
theorem post_disintegrates (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [SFinite μ]
    (R : Rule d α) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    {t : ℕ} (ht : t ≤ n) {F : E d × ℝ × Hist d α × Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s, F (s.1, s.2.1 t, hist π0 R sc pol t s, s.2.2) ∂gameLaw π0 μ =
      ∫⁻ s, ∫⁻ θ, ∫⁻ z, F (θ, z, hist π0 R sc pol t s, s.2.2) ∂gaussianReal 0 1
        ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
  induction t generalizing F with
  | zero =>
    have hF1 : Measurable (fun q : ℝ × Sample d Ω => F (q.2.1, q.1, Hist.empty, q.2.2.2)) :=
      hF.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk
        (measurable_const.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
    have h1 := lintegral_gameLaw_coord π0 μ 0 hF1 (fun _ _ _ _ _ => rfl)
    have hΦ : Measurable (fun q : E d × Ω => ∫⁻ z, F (q.1, z, Hist.empty, q.2) ∂gaussianReal 0 1) :=
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_fst))))).lintegral_prod_right'
    have h2 := lintegral_gameLaw_tip π0 μ hΦ
    have hp0 : ∀ h : Hist d α, post π0 R sc 0 h = π0 := fun h => by
      show π0.withDensity (fun _ => 1) = π0
      exact withDensity_one
    simp only [hist_zero, hp0]
    exact h1.trans h2
  | succ t ih =>
    have htn : t < n := ht
    have hH : Measurable (hist π0 R sc pol t) := measurable_hist π0 R hR sc hpol htn.le
    have hH1 : Measurable (hist π0 R sc pol (t + 1)) := measurable_hist π0 R hR sc hpol ht
    have hRP : Measurable (roundPush π0 R sc pol t) := measurable_roundPush π0 R hR sc (hpol t htn)
    -- the noise of round `t + 1` is independent of the history after round `t + 1`
    have hF1 : Measurable (fun q : ℝ × Sample d Ω => F (q.2.1, q.1, hist π0 R sc pol (t + 1) q.2, q.2.2.2)) :=
      hF.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk
        ((hH1.comp measurable_snd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
    have e1 := lintegral_gameLaw_coord π0 μ (t + 1) hF1 (fun a θ Z b ω => by
      simp only
      rw [hist_congr π0 R sc pol (t + 1) (θ, Function.update Z (t + 1) b, ω) (θ, Z, ω) rfl
        (fun i hi => Function.update_of_ne (Nat.ne_of_lt hi) b Z) rfl])
    -- POST at `t` for the round pushed
    have hF2 : Measurable (fun p : E d × ℝ × Hist d α × Ω =>
        ∫⁻ z', F (p.1, z', roundPush π0 R sc pol t p, p.2.2.2) ∂gaussianReal 0 1) :=
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
        ((hRP.comp measurable_fst).prodMk
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))))))).lintegral_prod_right'
    have e2 := ih htn.le hF2
    have hF3 : Measurable (fun p : E d × ℝ × Hist d α × Ω =>
        ∫⁻ θ', ∫⁻ z', F (θ', z', roundPush π0 R sc pol t p, p.2.2.2) ∂gaussianReal 0 1
          ∂post π0 R sc (t + 1) (roundPush π0 R sc pol t p)) := by
      refine measurable_lintegral_post π0 R hR sc (t + 1) hRP
        (f := fun q => ∫⁻ z', F (q.2, z', roundPush π0 R sc pol t q.1, q.1.2.2.2) ∂gaussianReal 0 1) ?_
      exact (hF.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk
        ((hRP.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_fst.comp measurable_fst)))))))).lintegral_prod_right'
    have e4 := ih htn.le hF3
    -- the round at each history: Bayes' formula
    have e3 : ∀ s : Sample d Ω,
        ∫⁻ θ, ∫⁻ z, ∫⁻ z', F (θ, z', roundPush π0 R sc pol t (θ, z, hist π0 R sc pol t s, s.2.2), s.2.2)
            ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂post π0 R sc t (hist π0 R sc pol t s) =
          ∫⁻ θ, ∫⁻ z, ∫⁻ θ', ∫⁻ z', F (θ', z', roundPush π0 R sc pol t (θ, z, hist π0 R sc pol t s, s.2.2),
              s.2.2) ∂gaussianReal 0 1 ∂post π0 R sc (t + 1) (roundPush π0 R sc pol t (θ, z, hist π0 R sc pol t s, s.2.2))
            ∂gaussianReal 0 1 ∂post π0 R sc t (hist π0 R sc pol t s) := by
      intro s
      have hG : Measurable (fun q : E d × α × ℝ => ∫⁻ z', F (q.1, z', Hist.push (hist π0 R sc pol t s) t
          (play pol t s.2.2 (hist π0 R sc pol t s)) q.2.2 q.2.1, s.2.2) ∂gaussianReal 0 1) :=
        (hF.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
          (((measurable_push t).comp (measurable_const.prodMk (measurable_const.prodMk
            ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
              (measurable_fst.comp (measurable_snd.comp measurable_fst)))))).prodMk measurable_const)))).lintegral_prod_right'
      exact post_step π0 R hR hsc t (hist π0 R sc pol t s) (play pol t s.2.2 (hist π0 R sc pol t s)) hG
    calc ∫⁻ s, F (s.1, s.2.1 (t + 1), hist π0 R sc pol (t + 1) s, s.2.2) ∂gameLaw π0 μ
        = ∫⁻ s, ∫⁻ z', F (s.1, z', hist π0 R sc pol (t + 1) s, s.2.2) ∂gaussianReal 0 1 ∂gameLaw π0 μ := e1
      _ = _ := e2
      _ = _ := lintegral_congr e3
      _ = _ := e4.symm

/-- Lemma 9.5 without the noise: given the history after `t` rounds and the seed, the tip has the law `post t`. -/
theorem post_disintegrates' (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [SFinite μ]
    (R : Rule d α) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    {t : ℕ} (ht : t ≤ n) {F : E d × Hist d α × Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s, F (s.1, hist π0 R sc pol t s, s.2.2) ∂gameLaw π0 μ =
      ∫⁻ s, ∫⁻ θ, F (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
  have hF' : Measurable (fun (x : E d × ℝ × Hist d α × Ω) => F (x.1, x.2.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h_eq := post_disintegrates π0 μ R hR hsc hpol ht hF'
  calc
    ∫⁻ s, F (s.1, hist π0 R sc pol t s, s.2.2) ∂gameLaw π0 μ
        = ∫⁻ s, (fun (x : E d × ℝ × Hist d α × Ω) => F (x.1, x.2.2)) (s.1, s.2.1 t, hist π0 R sc pol t s, s.2.2) ∂gameLaw π0 μ := rfl
    _ = ∫⁻ s, ∫⁻ θ, ∫⁻ z, (fun (x : E d × ℝ × Hist d α × Ω) => F (x.1, x.2.2)) (θ, z, hist π0 R sc pol t s, s.2.2) ∂gaussianReal 0 1 ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
      rw [h_eq]
    _ = ∫⁻ s, ∫⁻ θ, ∫⁻ z, F (θ, hist π0 R sc pol t s, s.2.2) ∂gaussianReal 0 1 ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := rfl
    _ = ∫⁻ s, ∫⁻ θ, (F (θ, hist π0 R sc pol t s, s.2.2) * ∫⁻ z, (1 : ℝ≥0∞) ∂gaussianReal 0 1) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
      refine lintegral_congr fun s => ?_
      refine lintegral_congr fun θ => ?_
      rw [lintegral_const, measure_univ]
      simp
    _ = ∫⁻ s, ∫⁻ θ, F (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
      simp

/-- The expansion of round `t`: a function of the tip, the history after round `t` and the seed, integrated over the
law before round `t` and the noise of round `t`. -/
theorem hist_succ_expand (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [SFinite μ]
    (R : Rule d α) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    {t : ℕ} (ht : t < n) {Ψ : E d × Hist d α × Ω → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ s, Ψ (s.1, hist π0 R sc pol (t + 1) s, s.2.2) ∂gameLaw π0 μ =
      ∫⁻ s, ∫⁻ θ, ∫⁻ z, Ψ (θ, Hist.push (hist π0 R sc pol t s) t (play pol t s.2.2 (hist π0 R sc pol t s))
          (R.sig (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) θ + sc * z)
          (R.ans (post π0 R sc t (hist π0 R sc pol t s)) (play pol t s.2.2 (hist π0 R sc pol t s)) θ), s.2.2)
        ∂gaussianReal 0 1 ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
  have hF : Measurable (fun p : E d × ℝ × Hist d α × Ω => Ψ (p.1, roundPush π0 R sc pol t p, p.2.2.2)) :=
    hΨ.comp (measurable_fst.prodMk ((measurable_roundPush π0 R hR sc (hpol t ht)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have h := post_disintegrates π0 μ R hR hsc hpol ht.le hF
  exact h

/-- Lemma 9.5, Bochner form, for a bounded measurable real function. -/
theorem post_disintegrates_integral (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Rule d α) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2)
    {t : ℕ} (ht : t ≤ n) {F : E d × Hist d α × Ω → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) :
    ∫ s, F (s.1, hist π0 R sc pol t s, s.2.2) ∂gameLaw π0 μ =
      ∫ s, ∫ θ, F (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
  -- Decompose F = F⁺ - F⁻ with F⁺, F⁻ ≥ 0, bounded by C, measurable
  set Fpos := fun p : E d × Hist d α × Ω => max (F p) 0 with hFpos_def
  set Fneg := fun p : E d × Hist d α × Ω => max (-F p) 0 with hFneg_def
  have hFpos_nonneg : ∀ p, 0 ≤ Fpos p := by
    intro p; dsimp [Fpos]; exact le_max_right _ _
  have hFneg_nonneg : ∀ p, 0 ≤ Fneg p := by
    intro p; dsimp [Fneg]; exact le_max_right _ _
  have hFpos_meas : Measurable Fpos :=
    hF.max measurable_const
  have hFneg_meas : Measurable Fneg :=
    (hF.neg).max measurable_const
  have hFpos_bound : ∀ p, |Fpos p| ≤ C := by
    intro p
    have h := hC p
    dsimp [Fpos]
    by_cases hp : 0 ≤ F p
    · rw [max_eq_left hp, abs_of_nonneg hp]
      rwa [abs_of_nonneg hp] at h
    · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]
      have : 0 ≤ |F p| := abs_nonneg _
      linarith
  have hFneg_bound : ∀ p, |Fneg p| ≤ C := by
    intro p
    have h := hC p
    dsimp [Fneg]
    by_cases hp : 0 ≤ -F p
    · rw [max_eq_left hp, abs_of_nonneg hp]
      rwa [← abs_neg (F p), abs_of_nonneg hp] at h
    · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]
      have : 0 ≤ |F p| := abs_nonneg _
      linarith
  have hF_eq : ∀ p, F p = Fpos p - Fneg p := by
    intro p; dsimp [Fpos, Fneg]; rw [max_zero_sub_max_neg_zero_eq_self]
  -- The map s ↦ (s.1, hist ..., s.2.2) is measurable
  let φ : Sample d Ω → E d × Hist d α × Ω := fun s => (s.1, hist π0 R sc pol t s, s.2.2)
  have hφ_meas : Measurable φ :=
    measurable_fst.prodMk ((measurable_hist π0 R hR sc hpol ht).prodMk
      (measurable_snd.comp measurable_snd))
  have hFpos_meas' : Measurable (fun s : Sample d Ω => Fpos (φ s)) :=
    hFpos_meas.comp hφ_meas
  have hFneg_meas' : Measurable (fun s : Sample d Ω => Fneg (φ s)) :=
    hFneg_meas.comp hφ_meas
  -- Make probability measure instances available for Integrable.of_bound
  haveI : IsProbabilityMeasure (gameLaw π0 μ) := isProbabilityMeasure_gameLaw π0 μ
  haveI (s : Sample d Ω) : IsProbabilityMeasure (post π0 R sc t (hist π0 R sc pol t s)) :=
    isProbabilityMeasure_post π0 R hR sc t (hist π0 R sc pol t s)
  -- Helper lemma: inner Bochner integral is AEStronglyMeasurable and bounded
  have h_inner_meas_and_bound (G : E d × Hist d α × Ω → ℝ) (hG_meas : Measurable G) (hG_nonneg : ∀ p, 0 ≤ G p) (hG_bound : ∀ p, |G p| ≤ C) :
    AEStronglyMeasurable (fun s : Sample d Ω => ∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) (gameLaw π0 μ) ∧
    (∀ᵐ s ∂gameLaw π0 μ, ‖(∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s))‖ ≤ C) := by
    have h_lintegral_meas : Measurable (fun s : Sample d Ω => ∫⁻ θ, ENNReal.ofReal (G (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s)) := by
      have hf : Measurable (fun (p : Sample d Ω × E d) => ENNReal.ofReal (G (p.2, hist π0 R sc pol t p.1, p.1.2.2))) := by
        refine ENNReal.measurable_ofReal.comp ?_
        refine hG_meas.comp ?_
        -- map (s, θ) ↦ (θ, hist ... s, s.2.2)
        have h1 : Measurable (fun (p : Sample d Ω × E d) => (p.2 : E d)) := measurable_snd
        have h2 : Measurable (fun (p : Sample d Ω × E d) => hist π0 R sc pol t p.1) :=
          (measurable_hist π0 R hR sc hpol ht).comp measurable_fst
        have h3 : Measurable (fun (p : Sample d Ω × E d) => p.1.2.2) :=
          measurable_snd.comp (measurable_snd.comp measurable_fst)
        exact (h1.prodMk (h2.prodMk h3))
      exact measurable_lintegral_post π0 R hR sc t (hhp := measurable_hist π0 R hR sc hpol ht) (hf := hf)
    have h_meas : AEStronglyMeasurable (fun s : Sample d Ω => ∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) (gameLaw π0 μ) := by
      have h_eq : (fun s : Sample d Ω => ∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) =ᵐ[gameLaw π0 μ]
        (fun s => (∫⁻ θ, ENNReal.ofReal (G (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s)).toReal) := by
        refine ae_of_all _ (fun s => ?_)
        simp [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun θ => hG_nonneg (θ, hist π0 R sc pol t s, s.2.2)))
          (hG_meas.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const)) |>.aestronglyMeasurable)]
      have h_toReal_meas : Measurable (fun s => (∫⁻ θ, ENNReal.ofReal (G (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s)).toReal) :=
        ENNReal.measurable_toReal.comp h_lintegral_meas
      exact h_toReal_meas.aestronglyMeasurable.congr h_eq.symm
    have h_bound : ∀ᵐ s ∂gameLaw π0 μ, ‖(∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s))‖ ≤ C := by
      refine ae_of_all _ (fun s => ?_)
      rw [Real.norm_eq_abs]
      have h_int_bound : |∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)| ≤ C := by
        calc
          |∫ θ, G (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)|
              ≤ ∫ θ, |G (θ, hist π0 R sc pol t s, s.2.2)| ∂post π0 R sc t (hist π0 R sc pol t s) := by
            apply abs_integral_le_integral_abs
          _ ≤ ∫ θ, C ∂post π0 R sc t (hist π0 R sc pol t s) := by
            have h_int_G : Integrable (fun θ : E d => G (θ, hist π0 R sc pol t s, s.2.2))
                (post π0 R sc t (hist π0 R sc pol t s)) :=
              Integrable.of_bound (C := C)
                (hG_meas.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))).aestronglyMeasurable
                (ae_of_all _ (fun θ => hG_bound (θ, hist π0 R sc pol t s, s.2.2)))
            refine integral_mono h_int_G.abs (integrable_const C) (fun θ => hG_bound (θ, hist π0 R sc pol t s, s.2.2))
          _ = C := by
            have h_prob : IsProbabilityMeasure (post π0 R sc t (hist π0 R sc pol t s)) :=
              isProbabilityMeasure_post π0 R hR sc t (hist π0 R sc pol t s)
            have h_real_univ : (post π0 R sc t (hist π0 R sc pol t s)).real Set.univ = 1 := by
              rw [Measure.real, h_prob.measure_univ]
              simp
            rw [integral_const, h_real_univ, one_smul]
      exact h_int_bound
    exact And.intro h_meas h_bound
  -- Get the results for Fpos and Fneg
  have h_inner_pos := h_inner_meas_and_bound Fpos hFpos_meas hFpos_nonneg hFpos_bound
  have h_inner_neg := h_inner_meas_and_bound Fneg hFneg_meas hFneg_nonneg hFneg_bound
  have h_inner_pos_meas := h_inner_pos.1
  have h_inner_neg_meas := h_inner_neg.1
  have h_inner_pos_bound := h_inner_pos.2
  have h_inner_neg_bound := h_inner_neg.2
  -- Integrability of the inner integrals
  have h_inner_pos_int : Integrable (fun s : Sample d Ω => ∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) (gameLaw π0 μ) :=
    Integrable.of_bound h_inner_pos_meas C h_inner_pos_bound
  have h_inner_neg_int : Integrable (fun s : Sample d Ω => ∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) (gameLaw π0 μ) :=
    Integrable.of_bound h_inner_neg_meas C h_inner_neg_bound
  -- Fpos and Fneg composed with φ are integrable
  have hFpos_int : Integrable (fun s : Sample d Ω => Fpos (φ s)) (gameLaw π0 μ) :=
    Integrable.of_bound (hFpos_meas'.aestronglyMeasurable) C (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs]; exact hFpos_bound (φ s)))
  have hFneg_int : Integrable (fun s : Sample d Ω => Fneg (φ s)) (gameLaw π0 μ) :=
    Integrable.of_bound (hFneg_meas'.aestronglyMeasurable) C (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs]; exact hFneg_bound (φ s)))
  -- Inner integrals for each s
  have hFpos_int_inner (s : Sample d Ω) : Integrable (fun θ : E d => Fpos (θ, hist π0 R sc pol t s, s.2.2))
      (post π0 R sc t (hist π0 R sc pol t s)) :=
    Integrable.of_bound (C := C) (hFpos_meas.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))).aestronglyMeasurable
      (ae_of_all _ (fun θ => by rw [Real.norm_eq_abs]; exact hFpos_bound (θ, hist π0 R sc pol t s, s.2.2)))
  have hFneg_int_inner (s : Sample d Ω) : Integrable (fun θ : E d => Fneg (θ, hist π0 R sc pol t s, s.2.2))
      (post π0 R sc t (hist π0 R sc pol t s)) :=
    Integrable.of_bound (C := C) (hFneg_meas.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))).aestronglyMeasurable
      (ae_of_all _ (fun θ => by rw [Real.norm_eq_abs]; exact hFneg_bound (θ, hist π0 R sc pol t s, s.2.2)))
  -- Apply post_disintegrates' to ENNReal.ofReal ∘ Fpos and ENNReal.ofReal ∘ Fneg
  have hpos := post_disintegrates' π0 μ R hR hsc hpol ht (F := ENNReal.ofReal ∘ Fpos) (hF := ENNReal.measurable_ofReal.comp hFpos_meas)
  have hneg := post_disintegrates' π0 μ R hR hsc hpol ht (F := ENNReal.ofReal ∘ Fneg) (hF := ENNReal.measurable_ofReal.comp hFneg_meas)
  -- Now convert between Bochner and ENNReal integrals
  have hpos_bochner : ∫ s, Fpos (φ s) ∂gameLaw π0 μ = ∫ s, (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
    have h_eq_lintegral : ENNReal.ofReal (∫ s, Fpos (φ s) ∂gameLaw π0 μ) = ENNReal.ofReal (∫ s, (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) := by
      calc
        ENNReal.ofReal (∫ s, Fpos (φ s) ∂gameLaw π0 μ) = ∫⁻ s, ENNReal.ofReal (Fpos (φ s)) ∂gameLaw π0 μ :=
          ofReal_integral_eq_lintegral_ofReal hFpos_int (ae_of_all _ (fun s => hFpos_nonneg (φ s)))
        _ = ∫⁻ s, ∫⁻ θ, ENNReal.ofReal (Fpos (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
          simpa [φ] using hpos
        _ = ∫⁻ s, ENNReal.ofReal (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
          refine lintegral_congr (fun s => ?_)
          rw [ofReal_integral_eq_lintegral_ofReal (hFpos_int_inner s) (ae_of_all _ (fun θ => hFpos_nonneg (θ, hist π0 R sc pol t s, s.2.2)))]
        _ = ENNReal.ofReal (∫ s, (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) :=
          (ofReal_integral_eq_lintegral_ofReal h_inner_pos_int (ae_of_all _ (fun s => integral_nonneg (fun θ => hFpos_nonneg (θ, hist π0 R sc pol t s, s.2.2))))).symm
    have h_eq' := congrArg ENNReal.toReal h_eq_lintegral
    have h_nonneg_A : 0 ≤ ∫ s, Fpos (φ s) ∂gameLaw π0 μ :=
      integral_nonneg (fun s => hFpos_nonneg (φ s))
    have h_nonneg_B : 0 ≤ ∫ s, (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ :=
      integral_nonneg (fun s => integral_nonneg (fun θ => hFpos_nonneg (θ, hist π0 R sc pol t s, s.2.2)))
    simpa [ENNReal.toReal_ofReal h_nonneg_A, ENNReal.toReal_ofReal h_nonneg_B] using h_eq'
  have hneg_bochner : ∫ s, Fneg (φ s) ∂gameLaw π0 μ = ∫ s, (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
    have h_eq_lintegral : ENNReal.ofReal (∫ s, Fneg (φ s) ∂gameLaw π0 μ) = ENNReal.ofReal (∫ s, (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) := by
      calc
        ENNReal.ofReal (∫ s, Fneg (φ s) ∂gameLaw π0 μ) = ∫⁻ s, ENNReal.ofReal (Fneg (φ s)) ∂gameLaw π0 μ :=
          ofReal_integral_eq_lintegral_ofReal hFneg_int (ae_of_all _ (fun s => hFneg_nonneg (φ s)))
        _ = ∫⁻ s, ∫⁻ θ, ENNReal.ofReal (Fneg (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
          simpa [φ] using hneg
        _ = ∫⁻ s, ENNReal.ofReal (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
          refine lintegral_congr (fun s => ?_)
          rw [ofReal_integral_eq_lintegral_ofReal (hFneg_int_inner s) (ae_of_all _ (fun θ => hFneg_nonneg (θ, hist π0 R sc pol t s, s.2.2)))]
        _ = ENNReal.ofReal (∫ s, (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) :=
          (ofReal_integral_eq_lintegral_ofReal h_inner_neg_int (ae_of_all _ (fun s => integral_nonneg (fun θ => hFneg_nonneg (θ, hist π0 R sc pol t s, s.2.2))))).symm
    have h_eq' := congrArg ENNReal.toReal h_eq_lintegral
    have h_nonneg_A : 0 ≤ ∫ s, Fneg (φ s) ∂gameLaw π0 μ :=
      integral_nonneg (fun s => hFneg_nonneg (φ s))
    have h_nonneg_B : 0 ≤ ∫ s, (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ :=
      integral_nonneg (fun s => integral_nonneg (fun θ => hFneg_nonneg (θ, hist π0 R sc pol t s, s.2.2)))
    simpa [ENNReal.toReal_ofReal h_nonneg_A, ENNReal.toReal_ofReal h_nonneg_B] using h_eq'
  -- Combine using F = Fpos - Fneg
  calc
    ∫ s, F (φ s) ∂gameLaw π0 μ = ∫ s, (Fpos (φ s) - Fneg (φ s)) ∂gameLaw π0 μ := by
      refine integral_congr_ae (ae_of_all _ (fun s => ?_))
      dsimp
      rw [hF_eq (φ s)]
    _ = (∫ s, Fpos (φ s) ∂gameLaw π0 μ) - (∫ s, Fneg (φ s) ∂gameLaw π0 μ) := by
      rw [integral_sub hFpos_int hFneg_int]
    _ = (∫ s, (∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) -
        (∫ s, (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ) := by
      rw [hpos_bochner, hneg_bochner]
    _ = ∫ s, ((∫ θ, Fpos (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) -
             (∫ θ, Fneg (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s))) ∂gameLaw π0 μ := by
      rw [integral_sub h_inner_pos_int h_inner_neg_int]
    _ = ∫ s, (∫ θ, (Fpos (θ, hist π0 R sc pol t s, s.2.2) - Fneg (θ, hist π0 R sc pol t s, s.2.2)) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
      refine integral_congr_ae (ae_of_all _ (fun s => ?_))
      dsimp
      rw [integral_sub (hFpos_int_inner s) (hFneg_int_inner s)]
    _ = ∫ s, (∫ θ, F (θ, hist π0 R sc pol t s, s.2.2) ∂post π0 R sc t (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
      refine integral_congr_ae (ae_of_all _ (fun s => ?_))
      refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
      dsimp
      rw [hF_eq (θ, hist π0 R sc pol t s, s.2.2)]


end POST

end AdversarialBco.Lower.Bayes
